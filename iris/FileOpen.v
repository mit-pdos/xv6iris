(* ===================================================================== *)
(* FileOpen.v -- THE FILE APPLICATION'S OPEN AND READ SUPPLIERS: the AU   *)
(* bundles a program derives FROM THE DEED (lane F-OPEN).                 *)
(*                                                                       *)
(* Design of record: claude-notes/design/app-file.md sections 2 and 3.    *)
(* [TreeMove.v] is the mould at the tree claim and [UInitCons.v] at       *)
(* init's mknod; this file is the two of them at [AppFile]'s deed.        *)
(*                                                                       *)
(*   section 1  THE FRACTION.  A move needs the deed's whole half         *)
(*              ([AppFile.file_step_park] joins it with the claim's to    *)
(*              make the in-flight arm); a READ needs only a positive     *)
(*              fraction -- agreement settles the exact arm and validity  *)
(*              refutes the in-flight one.  That is what lets ONE deed    *)
(*              answer the two independent pieces a read-only open owes   *)
(*              (the walk's hops and the terminal observation), which is  *)
(*              the wall [PinnedObs.v] section 12 records for a live      *)
(*              claim.                                                    *)
(*   section 2  the claim read at the era's record, and the FREE step.    *)
(*   section 3  open(O_CREATE)'s bundle at `f`, at a length-0 parent      *)
(*              prefix: the arm, the unarm and the dlookup free, the      *)
(*              parent leg the two-phase move.                            *)
(*   section 4  the read commit at `f`'s inum, and its arms.              *)
(*                                                                       *)
(* WHAT IS NOT HERE, and section 5 says exactly why: the O_TRUNC leg of   *)
(* the create bundle.  It is a SECOND claim-moving piece in one syscall   *)
(* and the deed pays for one.                                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var mono_nat invariants.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import Xv6Cameras.       (* [bioslotG] *)
Require Import Xv6G.             (* [xv6G] *)
Require Import FdSlots.          (* [fdslotG] *)
Require Import IrefSlots.        (* [irefslotG] *)
Require Import ProcAvail.        (* [pavG] *)
Require Import FileInvDefs.      (* [fileG], and its [appcfg] field [file_app] *)
Require Import FsCfg.            (* [fsc_fs] *)
Require Import PathElems.        (* [path_elems] *)
Require Import FsTree.           (* [fname] *)
Require Import FsImgCheck.       (* [fname_f] *)
Require Import FsBlocks.         (* [fs_names] *)
Require Import FsBytesGamma.     (* [fs_gamma_L] *)
Require Import OffGv.            (* [off_gv] *)
Require Import AppCfg.           (* [app_pred] / [app_run] / [MkAppcfg] *)
Require Import AppInv.           (* [app_inv], [app_body], [app_step], [appE] *)
Require Import FsAbsDelta.       (* [cre_pre], the legs *)
Require Import PieceFam.         (* [pfam] / [pf_at] *)
Require Import FsAbsCreateFire.  (* create's four commits, [cre_arm_fired] *)
Require Import UserPtTree.       (* [uptd] / [uva_wmapped]: the read's -1 arm's
                                    table and its reason *)
Require Import FsAbsReadFire.    (* [aread_commit_at] / [read_arms] *)
Require Import FsAbsEra.         (* [ep_start], [np_elems], [um_start_of] *)
Require Import SysMknodDefs.     (* [npar_cur], [npar_elems] *)
Require Import FsAbsCreateNm.    (* [npar_nm], [acre_commit_at_gen_nm_of] *)
Require Import ArgPath.          (* [arg_path_of], [arg_path_of_uniq] *)
Require Import SysOpenDefs.      (* [open_au_create_at], [open_trunc_piece] *)
Require Import UserOff.     (* [foff_pub]: what the publish hands the caller *)
Require Import SpecSysOpen.      (* [open_receipt_plain] *)
Require Import PinnedObs.        (* the pinned walk and the linear cursor *)
Require Import PinnedOpen.       (* [pinned_open_bundle_dead_lin] (lane F-OPEN-2) *)
Require Import SysReadDefs.      (* [ard_count] / [ard_pre] *)
Require Import InodeInv.         (* [MAXFILE] *)
Require Import BioDefs.          (* [BSIZE] *)
Require Import UmodeArith.       (* [moi_small] *)
Require Import FsImg.            (* re-IMPORTED last: the three leaves above
                                    carry a [ROOTINO] of their own *)
Require Import FsConsPin.        (* [cons_absent], [cons_present_at] *)
Require Import FileFsPure.
Require Import EchoDisc.         (* [line_ok] *)
Require Import EchoOut.          (* [echoOutG] *)
Require Import AppEcho.          (* [echo_taint] at the projection *)
Require Import AppFile.          (* the claim, the deed, the two phases *)
Require FileDisc.                (* the class [FileDisc.uname] *)
Require Import FileDeltas.       (* the pure legs *)
Require Import AppFileCons.      (* [cons_fact], [file_cons_cred] and its law *)
Require Import FsAbsDefs.        (* [aview] / [anode] / [arow_at] *)
Import Defs.

Local Open Scope Z_scope.

Section FileOpen.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.

  (* =================================================================== *)
  (*  1.  THE DEED AT A FRACTION                                          *)
  (* =================================================================== *)

  (* [AppFile.fdeed] is the holder's HALF; this is the same ghost at any
     fraction.  A MOVE needs the half on the nose ([file_step_park] joins
     it with the claim's to make [fdeed_whole]); a READ needs only a
     positive fraction, and that is the whole content of this section. *)
  Definition fdq (r : file_names) (q : Qp) (s : dst) : iProp Σ :=
    ghost_var (fn_deed r) q s.

  Global Instance fdq_timeless r q s : Timeless (fdq r q s).
  Proof using . rewrite /fdq. apply _. Qed.

  Lemma fdq_deed (r : file_names) (s : dst) : fdeed r s ⊣⊢ fdq r (1/2) s.
  Proof using . reflexivity. Qed.

  Lemma fdq_split (r : file_names) (q1 q2 : Qp) (s : dst) :
    fdq r (q1 + q2) s -∗ fdq r q1 s ∗ fdq r q2 s.
  Proof using . rewrite /fdq. iIntros "H". by iApply ghost_var_split. Qed.

  Lemma fdq_join (r : file_names) (q1 q2 : Qp) (s s' : dst) :
    fdq r q1 s -∗ fdq r q2 s' -∗ fdq r (q1 + q2) s.
  Proof using .
    rewrite /fdq. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %<-.
    iCombine "H1 H2" as "H". iExact "H".
  Qed.

  (* the two readings a fraction buys *)
  Lemma fdq_agree (r : file_names) (q q' : Qp) (s s' : dst) :
    fdq r q s -∗ fdq r q' s' -∗ ⌜s = s'⌝.
  Proof using .
    rewrite /fdq. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %Heq. by iPureIntro.
  Qed.

  Lemma fdq_whole_excl (r : file_names) (q : Qp) (s s' : dst) :
    fdq r q s -∗ fdeed_whole r s' -∗ False.
  Proof using .
    rewrite /fdq /fdeed_whole. iIntros "H1 H2".
    iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hq _].
    iPureIntro. rewrite Qp.add_comm in Hq. exact (Qp.not_add_le_l _ _ Hq).
  Qed.

  (* THE READING LAW AT A FRACTION: [AppFile.file_deed_law] with the half
     weakened to any [q].  A holder of a fraction meets no in-flight arm
     ([fdq_whole_excl]) and agrees with the exact one. *)
  Lemma file_deed_law_q (c : file_fixed) (r : file_names) (q : Qp) :
    ⊢ □ (∀ (v : aview) (s : dst),
           fdq r q s -∗ file_pred c r v -∗
           file_pred c r v ∗ fdq r q s ∗
           ((⌜f_ok v s /\ file_fs_pure v⌝) ∨ file_taint c)).
  Proof using .
    iIntros "!>" (v s) "Hd Hp". rewrite /file_pred.
    iDestruct "Hp" as "[#Ht | (%Hpins & Hc & Hf)]".
    { iSplitR; [ by iLeft |]. iFrame "Hd". by iRight. }
    rewrite /f_state.
    iDestruct "Hf" as "[[Hw Hf] | Hf]"; last first.
    { (* THE ESCROW ARM: the deed is WHOLE in the claim, and a fraction
         meets it exactly as it meets the in-flight arm (lane F-OPEN-5) *)
      rewrite /f_esc_live.
      iDestruct "Hf" as (h0 s0 g) "(_ & _ & Hwh & _ & _ & _)".
      iDestruct (fdq_whole_excl with "Hd Hwh") as %[]. }
    rewrite /f_core.
    iDestruct "Hf" as "[Hf | Hf]"; last first.
    { iDestruct "Hf" as (s0 s1) "(Hwh & _ & _ & _)".
      iDestruct (fdq_whole_excl with "Hd Hwh") as %[]. }
    iDestruct "Hf" as (s') "(Hd' & Ht & #Hty & %Hok)".
    iDestruct (fdq_agree r q (1/2) s s' with "Hd Hd'") as %<-.
    iSplitL "Hc Hw Hd' Ht".
    { iRight. iSplitR; [ by iPureIntro |]. iFrame "Hc".
      iApply (f_state_of_core with "Hw").
      iApply (f_core_exact c r v s Hok with "Hd' Ht Hty"). }
    iFrame "Hd". iLeft. by iPureIntro.
  Qed.

  (* ...and the same at the HALF, which is what a mover holds *)
  Lemma file_deed_law_pins (c : file_fixed) (r : file_names) :
    ⊢ □ (∀ (v : aview) (s : dst),
           fdeed r s -∗ file_pred c r v -∗
           file_pred c r v ∗ fdeed r s ∗
           ((⌜f_ok v s /\ file_fs_pure v⌝) ∨ file_taint c)).
  Proof using . iApply (file_deed_law_q c r (1/2)). Qed.

  (* =================================================================== *)
  (*  2.  THE CLAIM READ AT THE ERA'S RECORD, AND THE FREE STEP           *)
  (* =================================================================== *)

  (* THE CONSOLE'S PIN, AT THE FILE CLAIM.  [AppEcho.echo_cons_law] read
     through [AppFile.file_pred_cons]: the era's FLAG -- persistent, minted
     by /init's own mknod and carried down the process chain -- says the
     console is at a FIXED inum at every view the claim admits.  It is what
     the create's UNARM leg spends: a row [ialloc] just armed is not the
     console's, and nothing in the FILE deed says so (the deed is about
     `f`). *)
  (* ...the landed statement, now the made-arm corollary of
     [AppFileCons.file_cons_cred_law]; the create's legs below read the
     claim at the option-indexed credential directly. *)
  Lemma file_cons_law (c : file_fixed) (r : file_names) (jc : Z) :
    cons_made (fn_cons r) jc -∗
    □ (∀ v : aview, file_pred c r v -∗
         file_pred c r v ∗ (⌜cons_present_at jc v⌝ ∨ file_taint c)).
  Proof using .
    iIntros "#Hm".
    iDestruct (file_cons_cred_law c r (Some jc) with "[]") as "#Hl";
      [ iApply (file_cons_cred_of_made with "Hm") | ].
    iIntros "!>" (v) "Hp". iDestruct ("Hl" $! v with "Hp") as "[Hp Hc]".
    iFrame "Hp". cbn [cons_fact]. iExact "Hc".
  Qed.

  (* everything a leg of the create reads off the claim at one view *)
  Definition fclaim_facts (jo : option Z) (s : dst) (v : aview) : Prop :=
    f_ok v s /\ file_fs_pure v /\ cons_fact jo v.

  Lemma file_claim_read (γfs : fs_names) (c : file_fixed) (r : file_names)
      (jo : option Z) (s : dst) (q : Qp) (I : gmap Z fs_node) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ file_cons_cred c r jo -∗ fdq r q s -∗
    ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
      ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ∗ fdq r q s ∗
      (⌜fclaim_facts jo s (abs_view I)⌝ ∨ file_taint c).
  Proof using .
    intros Heq. iIntros "#Hinv #Hm Hd Hka".
    iDestruct (file_deed_law_q c r q) as "#Hlaw".
    iDestruct (file_cons_cred_law c r jo with "Hm") as "#Hcl".
    iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I') "(>Hh & Hp & >%Hdom & #Hx)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iAssert (▷ (file_pred c r (abs_view I) ∗ fdq r q s
                ∗ (⌜f_ok (abs_view I) s /\ file_fs_pure (abs_view I)⌝
                   ∨ file_taint c)))%I with "[Hp Hd]" as "Hpc".
    { iNext. iApply ("Hlaw" with "Hd Hp"). }
    iDestruct "Hpc" as "[Hp [Hd Hc1]]". iMod "Hc1". iMod "Hd".
    iAssert (▷ (file_pred c r (abs_view I)
                ∗ (⌜cons_fact jo (abs_view I)⌝ ∨ file_taint c)))%I
      with "[Hp]" as "Hpd".
    { iNext. iApply ("Hcl" with "Hp"). }
    iDestruct "Hpd" as "[Hp Hc2]". iMod "Hc2".
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hx".
      iSplitL; [| by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names]. iExact "Hp". }
    iModIntro. iFrame "Hka Hd".
    iDestruct "Hc1" as "[%H1 | #HT]"; [| by iRight ].
    iDestruct "Hc2" as "[%H2 | #HT]"; [| by iRight ].
    iLeft. iPureIntro. rewrite /fclaim_facts. split_and!;
      [ exact (proj1 H1) | exact (proj2 H1) | exact H2 ].
  Qed.

  (* ---- 2a.  THE CLAIM READ THROUGH AN ESCROW (lane F-OPEN-5) ----

     [file_claim_read]'s twin for a caller whose deed is PARKED IN THE
     CLAIM ([AppFile.file_escrow_park]).  What it holds is the escrow's
     UNSPENT TOKEN beside a persistent witness of the ledger entry, and
     what it reads is the same three facts -- so every leg of the create
     reads its claim exactly as it did before, at a deed it no longer
     holds. *)
  Lemma file_claim_read_esc (γfs : fs_names) (c : file_fixed) (r : file_names)
      (jo : option Z) (n : nat) (s : dst) (g : gname) (I : gmap Z fs_node) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ file_cons_cred c r jo -∗ esc_key c r n s g -∗
    esc_tok g -∗
    ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
      ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ∗ esc_tok g ∗
      ((⌜fclaim_facts jo s (abs_view I)⌝ ∗ f_typed c s) ∨ file_taint c).
  Proof using .
    intros Heq. iIntros "#Hinv #Hm #Hwit Htok Hka".
    iDestruct (file_escrow_law c r) as "#Hlaw".
    iDestruct (file_cons_cred_law c r jo with "Hm") as "#Hcl".
    iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I') "(>Hh & Hp & >%Hdom & #Hx)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iAssert (▷ (file_pred c r (abs_view I) ∗ esc_tok g
                ∗ ((⌜f_ok (abs_view I) s /\ file_fs_pure (abs_view I)⌝
                    ∗ f_typed c s) ∨ file_taint c)))%I
      with "[Hp Htok]" as "Hpc".
    { iNext. iApply ("Hlaw" with "Hwit Htok Hp"). }
    iDestruct "Hpc" as "[Hp [Htok Hc1]]". iMod "Hc1". iMod "Htok".
    iAssert (▷ (file_pred c r (abs_view I)
                ∗ (⌜cons_fact jo (abs_view I)⌝ ∨ file_taint c)))%I
      with "[Hp]" as "Hpd".
    { iNext. iApply ("Hcl" with "Hp"). }
    iDestruct "Hpd" as "[Hp Hc2]". iMod "Hc2".
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hx".
      iSplitL; [| by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names]. iExact "Hp". }
    iModIntro. iFrame "Hka Htok".
    iDestruct "Hc1" as "[[%H1 #Hty] | #HT]"; [| by iRight ].
    iDestruct "Hc2" as "[%H2 | #HT]"; [| by iRight ].
    iLeft. iFrame "Hty". iPureIntro. rewrite /fclaim_facts. split_and!;
      [ exact (proj1 H1) | exact (proj2 H1) | exact H2 ].
  Qed.

  (* ...AND WITH NOTHING IN HAND AT ALL: the persistent witness alone,
     which is what the create's [dirlookup] observation carries.  The
     answer is the DISJUNCTION, and the holder of the unspent token is
     what refutes its second half downstream ([file_trunc_of_exists]). *)
  Lemma file_escrow_read_at (γfs : fs_names) (c : file_fixed) (r : file_names)
      (n : nat) (s : dst) (g : gname) (I : gmap Z fs_node) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ esc_key c r n s g -∗
    ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
      ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ∗
      (⌜f_ok (abs_view I) s⌝ ∨ esc_spent g ∨ file_taint c).
  Proof using .
    intros Heq. iIntros "#Hinv #Hwit Hka".
    iDestruct (file_escrow_read c r) as "#Hlaw".
    iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I') "(>Hh & Hp & >%Hdom & #Hx)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iAssert (▷ (file_pred c r (abs_view I)
                ∗ ((⌜f_ok (abs_view I) s /\ file_fs_pure (abs_view I)⌝
                    ∗ f_typed c s) ∨ esc_spent g ∨ file_taint c)))%I
      with "[Hp]" as "Hpc".
    { iNext. iApply ("Hlaw" with "Hwit Hp"). }
    iDestruct "Hpc" as "[Hp Hc]". iMod "Hc".
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hx".
      iSplitL; [| by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names]. iExact "Hp". }
    iModIntro. iFrame "Hka".
    iDestruct "Hc" as "[[%H1 _] | [#Hsp | #HT]]".
    - iLeft. iPureIntro. exact (proj1 H1).
    - iRight. by iLeft.
    - iRight. by iRight.
  Qed.

  (* THE FREE STEP at the era's record: [AppFile.file_step_free] wrapped in
     [AppInv.app_step]'s shape.  [file_app_step_park]'s twin, with no
     resource at all. *)
  Lemma file_app_step_free_at (c : file_fixed) (r : file_names)
      (i : Z) (I : gmap Z fs_node) (av' : aview) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (file_fs_pure (abs_view I) -> file_fs_pure av') ->
    (cons_absent (abs_view I) -> cons_absent av') ->
    (forall j, cons_present_at j (abs_view I) -> cons_present_at j av') ->
    (forall s : dst, f_ok (abs_view I) s -> f_ok av' s) ->
    ⊢ app_step i I av'.
  Proof using .
    intros Heq Hpins Hab Hpr Hok. rewrite /app_step.
    iIntros (n') "%Hav Hp". rewrite Heq. cbn [app_pred app_run app_names].
    rewrite Hav. iModIntro. iNext.
    iApply (file_step_free c r _ _ Hpins Hab Hpr Hok with "Hp").
  Qed.

  (* =================================================================== *)
  (*  3.  open(O_CREATE)'s BUNDLE AT `f`                                  *)
  (*                                                                      *)
  (*  [TreeMove.tree_open_create_au]'s mould at the FILE deed, and         *)
  (*  [UInitCons.init_cons_mknod_bundle]'s at a FILE child: the parent     *)
  (*  prefix of `f` is EMPTY, so the walk is the start cursor alone and    *)
  (*  the cursor is the pure [⌜d = ROOTINO⌝]; the ARM and the UNARM and    *)
  (*  the dlookup observation are FREE; and the deed goes into exactly one *)
  (*  leg -- the ARM's -- and comes out through whichever of the parent    *)
  (*  leg and the unarm actually fired (the permit's own discipline,       *)
  (*  [FsAbsCreateFire.acre_commit_at_gen]'s note).                        *)
  (* =================================================================== *)

  (* ---- 3a.  THE FAMILIES, AT AN ESCROWED DEED (lane F-OPEN-5) ----

     The deed itself is no longer in any of them: it is PARKED IN THE
     CLAIM before the call ([AppFile.file_escrow_park]).  What travels is
     [fesc_res] -- the holder's TICKET, which is what [AppFile.file_resync]
     keys on and which the create's own legs need for phase 2, beside the
     escrow's UNSPENT TOKEN, which is what says the escrow has not fired.
     The ledger witness is PERSISTENT and rides as a premise of every
     lemma, never in a family: that is what makes the lookup piece free,
     and it is the whole reason the escrow lives in the claim's ledger
     rather than in a second fraction (see [AppFile] section 2a). *)
  Definition fesc_res (r : file_names) (s : dst) (g : gname) : iProp Σ :=
    (ftkt r s ∗ esc_tok g)%I.

  Definition file_arm_fam (c : file_fixed) (r : file_names) (jo : option Z) (s : dst)
      (g : gname) : pfam Σ (aview -> Z -> iProp Σ) :=
    MkPfam (fun (av : aview) (_ : Z) =>
              ((⌜fclaim_facts jo s av⌝ ∗ fesc_res r s g) ∨ file_taint c)%I)
           (fesc_res r s g).

  Definition file_unarm_fam (c : file_fixed) (r : file_names) (s : dst)
      (g : gname) : pfam Σ (aview -> Z -> iProp Σ) :=
    MkPfam (fun (_ : aview) (_ : Z) => (fesc_res r s g ∨ file_taint c)%I)
           True%I.

  (* the parent leg's receipt: the deed AT THE NEW STATE -- the line's
     file [N] present, empty, at the inum the arm chose, every other file
     as it was, and OUT OF THE ESCROW, because the leg fires it and phase 2
     hands both halves back -- or the taint.  EVERY create the claim
     absorbs is at the line's own name in the root (cut W2: the name
     predicate the kernel threads is the tie to the path's last element,
     and the class is where it lives), so there is no arm at another
     name. *)
  Definition file_cre_recv (c : file_fixed) (r : file_names) (jo : option Z)
      (N : fname) (s : dst) (g : gname) : aview -> Z -> fname -> Z -> iProp Σ :=
    fun (av : aview) (d : Z) (nm : fname) (i : Z) =>
      ((⌜s !! N = None /\ d = ROOTINO /\ nm = N⌝ ∗ fown r (<[N := (i, [])]> s))
       ∨ file_taint c)%I.

  Definition file_cre_fam (c : file_fixed) (r : file_names) (jo : option Z)
      (N : fname) (s : dst) (g : gname)
      : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ) :=
    MkPfam (file_cre_recv c r jo N s g) True%I.

  (* ---- 3b.  THE ARM LEG: free, and it MINTS THE PERMIT ---- *)

  Lemma file_arm_commit (γfs : fs_names) (c : file_fixed) (r : file_names)
      (jo : option Z) (n : nat) (s : dst) (g : gname) (bsc : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ file_cons_cred c r jo -∗ esc_key c r n s g -∗
    fesc_res r s g -∗
    aarm_commit_at (fs_gamma_L γfs) appE (AFile bsc)
      (file_arm_fam c r jo s g).(pf_recv).
  Proof using .
    intros Heq. iIntros "#Hinv #Hm #Hwit [Htk Htok]".
    assert (Hnd : forall e : gmap fname Z, AFile bsc <> ADir e)
      by (intros e Hc; discriminate Hc).
    rewrite /aarm_commit_at. iIntros (I i) "%Hnone %Hsome Hka".
    iMod (file_claim_read_esc γfs c r jo n s g I Heq
            with "Hinv Hm Hwit Htok Hka") as "(Hka & Htok & [[%Hf #Hty] | #HT])";
      last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". cbn [pf_recv].
      by iRight. }
    destruct Hf as (Hok & Hpure & Hcons).
    iModIntro. iFrame "Hka". iSplitR "Htk Htok".
    { iApply (file_app_step_free_at c r i I _ Heq).
      - intros _. exact (file_fs_pure_arm i (AFile bsc) (abs_view I) Hnone Hpure).
      - exact (cons_absent_arm_nd i (AFile bsc) (abs_view I) Hnd).
      - intros j. exact (cons_present_arm_nd j i (AFile bsc) (abs_view I) Hnone).
      - intros s'. exact (f_ok_arm i (AFile bsc) (abs_view I) s' Hnone Hnd). }
    iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". cbn [pf_recv].
    iLeft. rewrite /fesc_res. iFrame "Htk Htok". iPureIntro.
    by rewrite /fclaim_facts.
  Qed.

  (* ---- 3c.  THE UNARM LEG: free, and it SPENDS THE PERMIT ----

     The two inequalities [FsConsPin]'s unarm lemmas ask -- the armed inum
     is neither the root nor the pinned row's -- come off the ARM's own
     receipt: [FsAbsCreateFire.cre_arm_fired] says the row was ABSENT at
     the arm's view, and the receipt says what the claim held THERE.  The
     console's is the flag's ([file_cons_law]); `f`'s is the DEED'S OWN
     INUM, which is why the deed's state carries it. *)
  Lemma file_unarm_commit (γfs : fs_names) (c : file_fixed) (r : file_names)
      (jo : option Z) (n : nat) (s : dst) (g : gname) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ file_cons_cred c r jo -∗ esc_key c r n s g -∗
    aunarm_of_arm (fs_gamma_L γfs) appE (file_arm_fam c r jo s g)
      (file_unarm_fam c r s g).(pf_recv).
  Proof using .
    intros Heq. iIntros "#Hinv #Hm #Hwit". rewrite /aunarm_of_arm.
    iIntros (i) "Harm". rewrite /cre_arm_fired.
    iDestruct "Harm" as (av0) "[%Hfree Hrec]". cbn [pf_recv].
    rewrite /aunarm_commit_at. iIntros (I c0) "%Hrow Hka".
    iDestruct "Hrec" as "[[%Hf0 [Htk Htok]] | #HT]"; last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". cbn [pf_recv].
      by iRight. }
    destruct Hf0 as (Hok0 & Hpure0 & Hcons0).
    iMod (file_claim_read_esc γfs c r jo n s g I Heq
            with "Hinv Hm Hwit Htok Hka") as "(Hka & Htok & [[%Hf #Hty] | #HT])";
      last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". cbn [pf_recv].
      by iRight. }
    destruct Hf as (Hok & Hpure & Hcons).
    iModIntro. iFrame "Hka". iSplitR "Htk Htok".
    { iApply (file_app_step_free_at c r i I _ Heq).
      - intros _.
        exact (file_fs_pure_unarm_fresh i av0 (abs_view I) Hfree Hpure0 Hpure).
      - exact (cons_absent_unarm i (abs_view I)).
      - intros j Hj.
        (* the console is at ONE inum, so [j] is the flag's -- and at the
           sealed flag there is no [j] at all ([cons_fact_present]) *)
        pose proof (cons_fact_present jo (abs_view I) j Hcons Hj) as Hjo.
        subst jo. cbn [cons_fact] in Hcons0.
        exact (cons_present_unarm_fresh_nd j i av0 (abs_view I) Hfree
                 Hcons0 Hj).
      - intros s' Hs'. rewrite (f_ok_det (abs_view I) s' s Hs' Hok).
        exact (f_ok_unarm_fresh i av0 (abs_view I) s Hfree Hok0 Hok). }
    iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". cbn [pf_recv].
    iLeft. rewrite /fesc_res. iFrame "Htk Htok".
  Qed.

  (* ---- 3d.  THE PARENT LEG: the two-phase move, at the line's file ---- *)

  (* THE NAME PREDICATE the create is threaded with: the path's last
     element, which the redirect child tied to its line's file [N] *)
  Definition redir_at (N : fname) (nm : fname) : Prop := nm = N.

  (* The create reached [N] in the root, so the claim moves [N] ABSENT ->
     present-and-empty, every other file carried -- and THE ESCROW IS WHAT
     PAYS FOR IT: phase 1 is [AppFile.file_app_step_escrow], which moves
     the content of the deed the claim already holds WHOLE and spends the
     one-shot, and phase 2 is [AppFile.file_resync] exactly as before, on
     the ticket the holder kept.  [cre_pre] says [N] was ABSENT when the
     leg fired, so the deed's entry at [N] is [None] ([cre_pre_none]), and
     the arm's own receipt says the child's inum was FREE at the arm's
     view, so no other file holds it ([f_ok_fresh]). *)
  Lemma file_acre_commit (γfs : fs_names) (c : file_fixed) (r : file_names)
      (jo : option Z) (n : nat) (N : fname) (s : dst) (g : gname)
      (ls : list fwline) (ws : wordline) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    FileDisc.uname N ->
    (N, ws) ∈ ls -> EchoDisc.line_ok ws ->
    app_inv γfs -∗ file_cons_cred c r jo -∗ esc_key c r n s g -∗
    fl_lb c ls -∗
    acre_commit_at_gen_nm (fs_gamma_L γfs) appE (fun _ _ => AFile [])
      (redir_at N)
      (fun d : Z => ⌜d = ROOTINO⌝%I)
      (file_arm_fam c r jo s g) (file_cre_fam c r jo N s g).(pf_recv).
  Proof using .
    intros Heq HN Hin Hok. iIntros "#Hinv #Hm #Hwit #Hlb".
    rewrite /acre_commit_at_gen_nm.
    iIntros (I d i nm ents nl) "%Hpre %Hdots %HNm Harm %Hd Hka". subst d.
    rewrite /redir_at in HNm. subst nm.
    rewrite /cre_arm_fired. iDestruct "Harm" as (av0) "[%Hfree Hrec]".
    cbn [pf_recv].
    iDestruct "Hrec" as "[[%Hf0 [Htk Htok]] | #HT]"; last first.
    { iModIntro. iFrame "Hka". iSplitR; [ done |]. iSplitR.
      { iApply (file_app_step_taint c r ROOTINO I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      rewrite /file_cre_fam /file_cre_recv. cbn [pf_recv].
      iRight. iExact "HT". }
    iMod (file_claim_read_esc γfs c r jo n s g I Heq
            with "Hinv Hm Hwit Htok Hka") as "(Hka & Htok & [[%Hf #Hty] | #HT])";
      last first.
    { iModIntro. iFrame "Hka". iSplitR; [ done |]. iSplitR.
      { iApply (file_app_step_taint c r ROOTINO I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      rewrite /file_cre_fam /file_cre_recv. cbn [pf_recv].
      iRight. iExact "HT". }
    destruct Hf as (Hokv & Hpure & Hcons).
    destruct Hf0 as (Hok0 & _ & _).
    pose proof (cre_pre_none (abs_view I) s N ents nl i (AFile []) Hpre Hokv)
      as HsN.
    pose proof (f_ok_fresh av0 s i Hok0 Hfree) as Hfresh.
    destruct (file_create_at N (abs_view I) ents nl i s HN Hpre Hfresh Hpure Hokv)
      as (Hp1 & Hp2 & Hp3 & Hp4).
    iModIntro. iFrame "Hka". iSplitR; [ done |]. iSplitL "Htok".
    { iApply (file_app_step_escrow c r ROOTINO I _ n s (<[N := (i, [])]> s) g
                Heq (fun _ => Hp1) Hp2 Hp3 (fun _ => Hp4)
                with "Hwit Htok []").
      rewrite -(subseq_nil (echo_chunks ws)).
      iApply (f_typed_some c s ls N ws [] i HN Hin Hok
                (sel_ok_nil (echo_chunks ws)) with "Hty Hlb"). }
    iIntros (I') "%Hav Hka'".
    assert (Hne : s <> <[N := (i, [])]> s).
    { intros He. apply (f_equal (fun m : dst => m !! N)) in He.
      rewrite lookup_insert HsN in He. discriminate He. }
    iMod (file_resync γfs c r s (<[N := (i, [])]> s) I' appE
            ltac:(set_solver) Heq
            ltac:(rewrite -(f_ok_fcontent (abs_view I') (<[N := (i, [])]> s));
                  [ reflexivity | rewrite Hav; exact Hp4 ])
            Hne with "Hinv Htk Hka'") as "(Hka' & Hres)".
    iModIntro. iFrame "Hka'".
    rewrite /file_cre_fam /file_cre_recv. cbn [pf_recv].
    iDestruct "Hres" as "[Hown | [_ #HT]]".
    + iLeft. iFrame "Hown". iPureIntro. split_and!; [ exact HsN | reflexivity | reflexivity ].
    + iRight. iExact "HT".
  Qed.


  (* ---- 3e'.  WHAT THE CLAIM SAYS AT A VIEW NOBODY HOLDS A FRACTION AT

     The truncate's EXISTS disjunct has to identify a row at the view
     create's own [dirlookup] read, which is EARLIER than the [itrunc]'s
     own instant and which no deed fraction reaches: the deed's half is in
     the ARM's piece, where the create leg needs it WHOLE (its park at `f`
     joins it with the claim's), and the pieces of a bundle are
     [∗]-separated.  What IS readable there costs no fraction at all:
     [file_pred]'s non-taint arm carries [⌜file_fs_pure av⌝] and, in BOTH
     arms of [f_state], the TYPED witness of whatever state the claim is
     at ([AppFile.f_typed]'s pure part).  Together they say: if the root
     has an `f` at this view, its row is a file of FEWER THAN
     [EchoDisc.line_max] bytes -- which is exactly the premise
     [FileDeltas.f_inum_not_pinned] wants, so the truncate at that inum
     cannot be one of the four era-0 binaries.  That is the whole content
     of the dlookup family below, and it is why nothing LINEAR rides in
     it. *)

  Definition fclaim_free (v : aview) : Prop :=
    file_fs_pure v /\
    forall (N : fname) (i : Z), FileDisc.uname N ->
      astep v FsImg.ROOTINO N = Some i ->
      exists bs : list (bv 8),
        v !! i = Some (MkAnode (AFile bs) 1%nat)
        /\ (length bs < EchoDisc.line_max)%nat.

  (* the whole pure reading, off ONE arm's typed witness: this is what
     every arm of [f_state] -- the exact one, the in-flight one and the
     ESCROW -- gives, and the only thing that differs between them is
     which state the witness is at. *)
  Lemma fclaim_free_of (c : file_fixed) (v : aview) (s : dst) :
    file_fs_pure v -> f_ok v s -> f_typed c s -∗ ⌜fclaim_free v⌝.
  Proof using .
    intros Hpins Hok. iIntros "#Hty".
    iAssert (⌜forall (N : fname) (i : Z) (bs : list (bv 8)),
               s !! N = Some (i, bs) -> (length bs < EchoDisc.line_max)%nat⌝)%I
      as %Hshort.
    { iIntros (N i bs Hs).
      iDestruct (f_typed_lookup c s N i bs Hs with "Hty") as (ls) "[_ %Hbt]".
      iPureIntro. exact (f_bytes_typed_short ls N bs Hbt). }
    iPureIntro. split; [ exact Hpins |]. intros N i HN Hst.
    destruct (s !! N) as [[i0 bs0] |] eqn:Hs.
    - destruct (f_ok_pin v s N i0 bs0 Hok Hs) as (Hst0 & Hrow0).
      rewrite Hst0 in Hst. injection Hst as <-. exists bs0.
      split; [ exact Hrow0 | exact (Hshort N i0 bs0 Hs) ].
    - pose proof (f_ok_absent v s N Hok HN Hs) as Hab.
      rewrite /name_absent in Hab. rewrite Hab in Hst. discriminate.
  Qed.

  Lemma file_claim_read_free (γfs : fs_names) (c : file_fixed) (r : file_names)
      (I : gmap Z fs_node) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗
    ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
      ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ∗
      (⌜fclaim_free (abs_view I)⌝ ∨ file_taint c).
  Proof using .
    intros Heq. iIntros "#Hinv Hka".
    iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I') "(>Hh & Hp & >%Hdom & #Hx)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iDestruct "Hp" as ">Hp".
    iAssert (file_pred c r (abs_view I)
             ∗ (⌜fclaim_free (abs_view I)⌝ ∨ file_taint c))%I
      with "[Hp]" as "[Hp Hres]".
    { rewrite /file_pred.
      iDestruct "Hp" as "[#Ht | (%Hpins & Hc & Hf)]".
      { iSplitR; [ by iLeft |]. by iRight. }
      iAssert (f_state c r (abs_view I)
               ∗ ⌜fclaim_free (abs_view I)⌝)%I with "[Hf]" as "[Hf %Hfree]".
      { rewrite /f_state.
        iDestruct "Hf" as "[[Hw Hf] | Hf]"; last first.
        - (* THE ESCROW ARM carries the typed witness of the escrowed
             content exactly as the exact arm does (lane F-OPEN-5) *)
          rewrite /f_esc_live.
          iDestruct "Hf" as (h0 s0 g) "(Ha & #Hrec & Hwh & Htk & #Hty & %Hok)".
          iDestruct (fclaim_free_of c (abs_view I) s0 Hpins Hok with "Hty")
            as "%Hfree".
          iSplitL; [| by iPureIntro ].
          iRight. iExists h0, s0, g. iFrame "Ha Hrec Hwh Htk Hty".
          by iPureIntro.
        - rewrite /f_core. iDestruct "Hf" as "[Hf | Hf]".
          + iDestruct "Hf" as (s') "(Hd & Htk & #Hty & %Hok)".
            iDestruct (fclaim_free_of c (abs_view I) s' Hpins Hok with "Hty")
              as "%Hfree".
            iSplitL; [| by iPureIntro ].
            iLeft. iFrame "Hw". iLeft. iExists s'. iFrame "Hd Htk Hty".
            by iPureIntro.
          + iDestruct "Hf" as (s0 s1) "(Hwh & Htk & #Hty & %Hok)".
            iDestruct (fclaim_free_of c (abs_view I) s1 Hpins Hok with "Hty")
              as "%Hfree".
            iSplitL; [| by iPureIntro ].
            iLeft. iFrame "Hw". iRight. iExists s0, s1.
            iFrame "Hwh Htk Hty". by iPureIntro. }
      iSplitL "Hc Hf".
      - iRight. iSplitR; [ by iPureIntro |]. iFrame "Hc Hf".
      - iLeft. by iPureIntro. }
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hx".
      iSplitL; [| by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names]. iExact "Hp". }
    iModIntro. iFrame "Hka Hres".
  Qed.

  (* THE EXISTS OBSERVATION'S FAMILY: the pure reading above, at the view
     create's [dirlookup] fired at, AND THE ESCROW READ AT THAT SAME VIEW
     (lane F-OPEN-5).  Still nothing linear: the escrow's tie is the
     PERSISTENT ledger witness, which is exactly what this piece needs,
     because the syscall's fold DROPS this receipt on the arm where the
     permit was never paid ([SpecSysOpen.cre_rcpt_kept] is [emp] at a
     truncating create) -- a fraction handed to this piece would be a
     fraction the deed could never get back. *)
  Definition file_dlk_recv (c : file_fixed) (r : file_names) (n : nat)
      (s : dst) (g : gname)
      : aview -> Z -> fname -> Z -> iProp Σ :=
    fun (av : aview) (_ : Z) (_ : fname) (_ : Z) =>
      ((⌜fclaim_free av⌝ ∗ (⌜f_ok av s⌝ ∨ esc_spent g)) ∨ file_taint c)%I.

  Definition file_dlk_fam (c : file_fixed) (r : file_names) (n : nat)
      (s : dst) (g : gname)
      : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ) :=
    MkPfam (file_dlk_recv c r n s g) True%I.

  Lemma file_dlk_piece (γfs : fs_names) (c : file_fixed) (r : file_names)
      (n : nat) (s : dst) (g : gname) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ esc_key c r n s g -∗
    pf_at (dlookup_commit_at (fs_gamma_L γfs) appE) (file_dlk_fam c r n s g).
  Proof using .
    intros Heq. iIntros "#Hinv #Hwit". rewrite /pf_at. cbn [pf_recv pf_refund].
    iSplit; [| done ].
    rewrite /dlookup_commit_at. iIntros (I d i nm ents nl) "%Hd %Hnm Hka".
    iMod (file_claim_read_free γfs c r I Heq with "Hinv Hka") as "[Hka Hfree]".
    iMod (file_escrow_read_at γfs c r n s g I Heq with "Hinv Hwit Hka")
      as "[Hka Hesc]".
    iModIntro. iFrame "Hka". rewrite /file_dlk_fam /file_dlk_recv.
    cbn [pf_recv].
    iDestruct "Hfree" as "[%Hfree | #HT]"; [| by iRight ].
    iDestruct "Hesc" as "[%Hok | [#Hsp | #HT]]".
    - iLeft. iSplitR; [ by iPureIntro |]. iLeft. by iPureIntro.
    - iLeft. iSplitR; [ by iPureIntro |]. by iRight.
    - by iRight.
  Qed.

  (* THE OPEN OBSERVATION'S FAMILY: the same escrow read at the instant
     the kernel reports the FOUND NODE'S TYPE.  That instant is later than
     the lookup's, which is why the claim must be read AGAIN here -- and
     it is what refutes create's F-OK's found DEVICE (lane F-OPEN-5): at
     the deed's own inum the claim says the row is an [AFile]. *)
  Definition file_odlk_recv (c : file_fixed) (r : file_names) (n : nat)
      (s : dst) (g : gname) : aview -> Z -> anode -> iProp Σ :=
    fun (av : aview) (_ : Z) (_ : anode) =>
      ((⌜f_ok av s⌝ ∨ esc_spent g) ∨ file_taint c)%I.

  Definition file_odlk_fam (c : file_fixed) (r : file_names) (n : nat)
      (s : dst) (g : gname) : pfam Σ (aview -> Z -> anode -> iProp Σ) :=
    MkPfam (file_odlk_recv c r n s g) True%I.

  Lemma file_odlk_piece (γfs : fs_names) (c : file_fixed) (r : file_names)
      (n : nat) (s : dst) (g : gname) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ esc_key c r n s g -∗
    pf_at (aopen_commit_at (fs_gamma_L γfs) appE) (file_odlk_fam c r n s g).
  Proof using .
    intros Heq. iIntros "#Hinv #Hwit". rewrite /pf_at. cbn [pf_recv pf_refund].
    iSplit; [| done ].
    rewrite /aopen_commit_at. iIntros (I i a) "%Hrow Hka".
    iMod (file_escrow_read_at γfs c r n s g I Heq with "Hinv Hwit Hka")
      as "[Hka Hesc]".
    iModIntro. iFrame "Hka". rewrite /file_odlk_fam /file_odlk_recv.
    cbn [pf_recv].
    iDestruct "Hesc" as "[%Hok | [#Hsp | #HT]]".
    - iLeft. iLeft. by iPureIntro.
    - iLeft. by iRight.
    - by iRight.
  Qed.

  (* ---- 3f.  THE O_TRUNC LEG, KEYED TO THE CREATE'S OWN RECEIPT ----

     Lane F-OPEN stopped here and priced the seam; this is its
     APPLICATION half, landed.  [SysOpenDefs.atrunc_of_permit] is the
     shape -- the truncate's commit AT ONE INUM, produced from a PERMIT
     naming that inum, on [FsAbsCreateFire.aunarm_of_arm]'s mould -- and
     [SysOpenDefs.trunc_permit_cre] is the permit the FRESH arm holds: the
     create's own fired receipt, which for this claim carries the deed.

     THE TRUNCATE IS THEN FREE ON THE FRESH RUN, and that is the whole
     content: the row the call reached is the CHILD the create just made,
     so [cre_pre] says it is [AFile []] at nlink 1, the tie says the name
     was `f`, and the deed is at [Some (i, [])] where the parent leg put
     it -- so the truncate at that row is the identity
     ([FileDeltas.f_ok_trunc_nil]) and the deed comes back unmoved. *)

  (* THE RECEIPT.  TWO arms (lane F-OPEN-5, and this is the deliverable):
     THE LINE'S FILE [N] IS PRESENT AND EMPTY AT THE ROW THE TRUNCATE
     REACHED, every other file as the deed had it -- create's own child on
     the FRESH run, [N]'s own row on the EXISTS one -- or the taint.  The
     old first arm ("the deed did not move") is GONE: on the fresh run the
     create leg moved it, and on the exists run the escrow's reading at the
     lookup's view identifies the row and refutes an absent entry
     outright. *)
  Definition file_trunc_recv (c : file_fixed) (r : file_names) (N : fname)
      (s : dst) : aview -> Z -> list (bv 8) -> iProp Σ :=
    fun (_ : aview) (i : Z) (_ : list (bv 8)) =>
      (fown r (<[N := (i, [])]> s) ∨ file_taint c)%I.

  Definition file_trunc_fam (c : file_fixed) (r : file_names) (N : fname)
      (s : dst) : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ) :=
    MkPfam (file_trunc_recv c r N s) True%I.

  Lemma file_trunc_free (av0 av : aview) (i : Z) (s : dst) :
    av0 !! i = Some (MkAnode (AFile []) 1%nat) ->
    file_fs_pure av0 ->
    f_ok av0 s ->
    file_fs_pure av -> f_ok av s ->
    file_fs_pure (delta_trunc i av)
    /\ (cons_absent av -> cons_absent (delta_trunc i av))
    /\ (forall j, cons_present_at j av -> cons_present_at j (delta_trunc i av))
    /\ f_ok (delta_trunc i av) s.
  Proof using .
    intros Hrow0 Hpure0 Hok0 Hpure Hok.
    destruct (f_inum_not_pinned av0 i [] Hpure0 Hrow0
                ltac:(rewrite /EchoDisc.line_max; cbn [length]; lia))
      as (N1 & N2 & N3 & N4 & N5 & N6).
    split_and!.
    - exact (file_fs_pure_trunc_ne i av N1 N2 N3 N4 N5 N6 Hpure).
    - exact (cons_absent_trunc_any i av).
    - intros j. exact (cons_present_trunc_any j i av).
    - apply (f_ok_trunc_keep i av s); [| exact Hok].
      (* a file at the create's child IS empty: its row at [av0] is
         [AFile []] *)
      intros N j bs Hs ->.
      destruct (f_ok_pin av0 s N i bs Hok0 Hs) as (_ & Hrowf).
      rewrite Hrow0 in Hrowf. congruence.
  Qed.

  Lemma file_trunc_of_cre (γfs : fs_names) (c : file_fixed) (r : file_names)
      (jo : option Z) (n : nat) (N : fname) (s : dst) (g : gname) (i : Z) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ file_cons_cred c r jo -∗
    (∃ (av0 : aview) (ents : gmap fname Z) (nl0 : nat),
       ⌜cre_pre av0 ROOTINO N ents nl0 i (AFile [])⌝ ∗
       (file_cre_fam c r jo N s g).(pf_recv) av0 ROOTINO N i) -∗
    atrunc_commit_i (fs_gamma_L γfs) appE i (file_trunc_recv c r N s).
  Proof using .
    intros Heq. iIntros "#Hinv #Hm Hperm".
    iDestruct "Hperm" as (av0 ents nl0) "[%Hpre Hrec]".
    rewrite /file_cre_fam /file_cre_recv. cbn [pf_recv].
    rewrite /atrunc_commit_i. iIntros (I bs0 nl) "%Hrow Hka".
    iDestruct "Hrec" as "[Hfb | #HT]"; last first.
    { (* the taint: the step is free and the receipt is the taint *)
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      rewrite /file_trunc_recv. iRight. iExact "HT". }
    (* THE CREATE AT [N]: the deed is at [<[N := (i, [])]> s] and the
       truncate is the identity there *)
    iDestruct "Hfb" as "[_ [Hd Ht]]".
    iMod (file_claim_read γfs c r jo (<[N := (i, [])]> s) (1/2) I Heq
            with "Hinv Hm Hd Hka") as "(Hka & Hd & [%Hf | #HT])"; last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      rewrite /file_trunc_recv. iRight. iExact "HT". }
    destruct Hf as (Hok & Hpure & Hcons).
    pose proof (proj2 (f_ok_pin (abs_view I) _ N i [] Hok (lookup_insert _ _ _)))
      as HrowI.
    destruct (file_trunc_free (abs_view I) (abs_view I) i (<[N := (i, [])]> s)
                HrowI Hpure Hok Hpure Hok)
      as (Hp1 & Hp2 & Hp3 & Hp4).
    iModIntro. iFrame "Hka". iSplitR "Hd Ht".
    { iApply (file_app_step_free_at c r i I _ Heq).
      - intros _. exact Hp1.
      - exact Hp2.
      - exact Hp3.
      - intros s' Hs'.
        rewrite (f_ok_det (abs_view I) s' _ Hs' Hok). exact Hp4. }
    iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
    rewrite /file_trunc_recv. iLeft. rewrite /fown. iFrame "Hd Ht".
  Qed.

  (* ...AND THE PIECE, as a bundle would carry it: the keyed AU beside a
     refund of [True] -- a create that fired and then failed past the
     truncate hands the deed back through the CREATE's receipt
     ([SpecSysOpen.open_post_fail_create] arm (a)), so this piece owes
     nothing on that path. *)
  (* ---- 3f'.  THE EXISTS DISJUNCT: [N] WAS THERE AND THE TRUNCATE MOVES IT

     What the permit hands on this run is the exists observation's receipt
     -- the pure reading of section 3e' and THE ESCROW'S OWN READING, both
     at the view create's [dirlookup] fired at -- BESIDE THE ARM PIECE THE
     RUN NEVER FIRED (create found the name, so [ialloc] never ran), and
     [pf_at] is a conjunction, so the piece's REFUND is the escrow's
     UNSPENT TOKEN.  The token refutes the receipt's [esc_spent] disjunct,
     so what is left is [f_ok avx s] -- the claim's own value AT THE
     LOOKUP'S VIEW, which is what F-OPEN-3 could not have and what
     F-OPEN-4 could not reach through a second invariant.  At an absent
     entry it contradicts the found entry at the tie (REFUTED, the name
     being in the class); at [s !! N = Some (i, bs)] it IDENTIFIES the
     row, and the move [(i, bs) -> (i, [])] at [N] is the escrow's fire
     and resync. *)
  Lemma file_trunc_of_exists (γfs : fs_names) (c : file_fixed) (r : file_names)
      (jo : option Z) (n : nat) (N : fname) (s : dst) (g : gname)
      (ls : list fwline) (ws : wordline)
      (i : Z) (avx : aview) (entsx : gmap fname Z) (nlx : nat) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    FileDisc.uname N ->
    avx !! FsImg.ROOTINO = Some (MkAnode (ADir entsx) nlx) ->
    entsx !! N = Some i ->
    (N, ws) ∈ ls -> EchoDisc.line_ok ws ->
    app_inv γfs -∗ file_cons_cred c r jo -∗ esc_key c r n s g -∗
    fl_lb c ls -∗
    ((⌜fclaim_free avx⌝ ∗ (⌜f_ok avx s⌝ ∨ esc_spent g)) ∨ file_taint c) -∗
    fesc_res r s g -∗
    atrunc_commit_i (fs_gamma_L γfs) appE i (file_trunc_recv c r N s).
  Proof using .
    intros Heq HN Hrowx Hentx Hin Hokw.
    iIntros "#Hinv #Hm #Hwit #Hlb Hfree [Htk Htok]".
    rewrite /atrunc_commit_i. iIntros (I bs0 nl) "%Hrow Hka".
    (* the lookup's view, read: the root's [N] is [i], and its row is a
       SHORT file, so [i] is none of the four pinned binaries *)
    iDestruct "Hfree" as "[[%Hfree Hval] | #HT]"; last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      rewrite /file_trunc_recv. iRight. iExact "HT". }
    (* THE REFUTATION: the token says the escrow never fired *)
    iDestruct "Hval" as "[%Hokx | #Hsp]"; last first.
    { iDestruct (esc_tok_spent g with "Htok Hsp") as %[]. }
    assert (Hstx : astep avx FsImg.ROOTINO N = Some i)
      by (rewrite /astep /aents Hrowx /= /anode_ents /=; exact Hentx).
    destruct Hfree as (Hpurex & Hrowf).
    destruct (Hrowf N i HN Hstx) as (bsx & Hrowi & Hlenx).
    destruct (f_inum_not_pinned avx i bsx Hpurex Hrowi Hlenx)
      as (N1 & N2 & N3 & N4 & N5 & N6).
    (* AND THE IDENTIFICATION: the deed's entry at the lookup's own view
       names the row the truncate reached *)
    destruct (s !! N) as [[j bs] |] eqn:HsN; last first.
    { (* AN ABSENT ENTRY IS REFUTED: the root had no [N] at [avx], and
         the lookup found one *)
      exfalso.
      pose proof (f_ok_absent avx s N Hokx HN HsN) as Hab.
      rewrite /name_absent in Hab. rewrite Hab in Hstx. discriminate. }
    assert (Hji : j = i).
    { destruct (f_ok_pin avx s N j bs Hokx HsN) as (Hstj & _).
      rewrite Hstj in Hstx. by injection Hstx. }
    subst j.
    iMod (file_claim_read_esc γfs c r jo n s g I Heq
            with "Hinv Hm Hwit Htok Hka") as "(Hka & Htok & [[%Hf #Hty] | #HT])";
      last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      rewrite /file_trunc_recv. iRight. iExact "HT". }
    destruct Hf as (Hok & Hpure & Hcons).
    (* the three legs the truncate at a NON-PINNED row always carries *)
    assert (Hp1 : file_fs_pure (delta_trunc i (abs_view I)))
      by exact (file_fs_pure_trunc_ne i (abs_view I) N1 N2 N3 N4 N5 N6 Hpure).
    assert (Hp2 : cons_absent (abs_view I) ->
                  cons_absent (delta_trunc i (abs_view I)))
      by exact (cons_absent_trunc_any i (abs_view I)).
    assert (Hp3 : forall j, cons_present_at j (abs_view I) ->
                  cons_present_at j (delta_trunc i (abs_view I)))
      by (intros j; exact (cons_present_trunc_any j i (abs_view I))).
    destruct (decide (bs = [])) as [-> | Hbs].
    { (* it was empty already: the delta is the identity on the claim, and
         the escrow comes home UNSPENT in phase 2 *)
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_free_at c r i I _ Heq).
        - intros _. exact Hp1.
        - exact Hp2.
        - exact Hp3.
        - intros s' Hs'.
          rewrite (f_ok_det (abs_view I) s' s Hs' Hok).
          apply (f_ok_trunc_nil i N i (abs_view I) s HsN); [| exact Hok].
          intros M j bs' Hne HsM Hij. subst j.
          exact (f_ok_inum_ne (abs_view I) s N M i i [] bs' Hok HsN Hne HsM eq_refl). }
      iIntros (I') "%Hav Hka'".
      iMod (file_escrow_return γfs c r n s g appE
              ltac:(set_solver) Heq with "Hinv Hwit Htok Htk") as "Hres".
      iModIntro. iFrame "Hka'". rewrite /file_trunc_recv.
      rewrite (insert_id s N (i, []) HsN).
      iDestruct "Hres" as "[Hown | #HT]".
      - iLeft. iExact "Hown".
      - iRight. iExact "HT". }
    assert (Hp4 : f_ok (delta_trunc i (abs_view I)) (<[N := (i, [])]> s))
      by exact (f_ok_trunc_at N i bs (abs_view I) s HsN Hok).
    iModIntro. iFrame "Hka". iSplitL "Htok".
    { iApply (file_app_step_escrow c r i I _ n s (<[N := (i, [])]> s) g
                Heq (fun _ => Hp1) Hp2 Hp3 (fun _ => Hp4) with "Hwit Htok []").
      rewrite -(subseq_nil (echo_chunks ws)).
      iApply (f_typed_some c s ls N ws [] i HN Hin Hokw
                (sel_ok_nil (echo_chunks ws)) with "Hty Hlb"). }
    iIntros (I') "%Hav Hka'".
    assert (Hne : s <> <[N := (i, [])]> s).
    { intros He. apply (f_equal (fun m : dst => m !! N)) in He.
      rewrite lookup_insert HsN in He. congruence. }
    iMod (file_resync γfs c r s (<[N := (i, [])]> s) I' appE
            ltac:(set_solver) Heq
            ltac:(rewrite -(f_ok_fcontent (abs_view I') (<[N := (i, [])]> s));
                  [ reflexivity | rewrite Hav; exact Hp4 ])
            Hne
            with "Hinv Htk Hka'") as "(Hka' & Hres)".
    iModIntro. iFrame "Hka'".
    rewrite /file_trunc_recv.
    iDestruct "Hres" as "[Hown | [_ #HT]]".
    + iLeft. iExact "Hown".
    + iRight. iExact "HT".
  Qed.

  Lemma file_trunc_piece (γfs : fs_names) (c : file_fixed) (r : file_names)
      (jo : option Z) (n : nat) (N : fname) (s : dst) (g : gname)
      (ls : list fwline) (ws : wordline)
      (M : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    FileDisc.uname N ->
    arg_path_of M pv pl ->
    list_basics.last (path_elems pl) = Some N ->
    (N, ws) ∈ ls -> EchoDisc.line_ok ws ->
    app_inv γfs -∗ file_cons_cred c r jo -∗ esc_key c r n s g -∗
    fl_lb c ls -∗
    pf_at (atrunc_of_permit (fs_gamma_L γfs) appE
             (trunc_permit_of (fs_gamma_L γfs)
                (trunc_tie_arg M pv (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I))
                (file_arm_fam c r jo s g) (file_cre_fam c r jo N s g)
                (file_dlk_fam c r n s g)))
      (file_trunc_fam c r N s).
  Proof using .
    intros Heq HN Hpath Hlast Hin Hokw. iIntros "#Hinv #Hm #Hwit #Hlb".
    rewrite /pf_at. cbn [pf_recv pf_refund].
    iSplit; [| done ].
    rewrite /atrunc_of_permit. iIntros (i) "Hperm".
    rewrite /trunc_permit_of.
    iDestruct "Hperm" as (d nm) "[Htie Hrest]".
    iEval (rewrite /trunc_tie_arg) in "Htie".
    iDestruct "Htie" as "[Hnm Hcur]".
    (* THE TIE, READ: the name is [N] and the parent is the root *)
    iDestruct ("Hnm" $! pl with "[%]") as "%Hl"; [ exact Hpath |].
    assert (Hnmf : nm = N) by (rewrite Hlast in Hl; by injection Hl).
    subst nm.
    iDestruct (npar_cur_elim M pv pl
                 (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I) d Hpath
                 with "Hcur") as "%Hd". subst d.
    iDestruct "Hrest" as "[Hfresh | [Hex Harm]]".
    - (* THE FRESH RUN: create's own receipt AT THE TIED NAME *)
      iApply (file_trunc_of_cre γfs c r jo n N s g i Heq with "Hinv Hm [Hfresh]").
      rewrite /cre_acre_fired. iExact "Hfresh".
    - (* THE EXISTS RUN: the observation's reading -- pure AND ESCROWED --
         beside the arm piece's refund, which is the escrow's token *)
      rewrite /cre_ex_fired.
      iDestruct "Hex" as (avx entsx nlx) "(%Hrx & %Hex & Hrec)".
      rewrite /file_dlk_fam. cbn [pf_recv].
      rewrite /pf_at. iDestruct "Harm" as "[_ Harm]".
      rewrite /file_arm_fam. cbn [pf_refund].
      iApply (file_trunc_of_exists γfs c r jo n N s g ls ws i avx entsx nlx
                Heq HN Hrx Hex Hin Hokw with "Hinv Hm Hwit Hlb Hrec Harm").
  Qed.

  (* ---- 3e.  ...AND THE WHOLE BUNDLE, FROM ONE ESCROWED DEED ---- *)

  (* [SysOpenDefs.open_au_create_at] at the path [N], whose parent prefix
     is EMPTY: the walk is the start cursor alone ([ep_hops_done] over the
     empty list) and the cursor is the pure [⌜d = ROOTINO⌝], which is
     duplicable and returns itself in phase 1 -- [TreeMove.tree_mknod_au]'s
     reason, at this path.

     THE TRUNCATION PIECE IS THE CLAIM'S OWN (lane F-OPEN-3), at ANY mode:
     the bundle carries it at the permit create pays, and section 3f''
     supplies it.  The path's LAST ELEMENT is a premise because the tie is
     what identifies the truncated row -- the redirect child opens its
     line's file [N], and that is the sentence saying so.

     WHAT GOES IN IS NO LONGER THE DEED (lane F-OPEN-5) but the ESCROW:
     the caller parks its half in the claim with
     [AppFile.file_escrow_park] before the call and hands in the ticket,
     the one-shot token and the ledger witness.  The OPEN OBSERVATION is
     no longer trivial either: it reads the claim at the instant the
     kernel reports the found node's type, which is what refutes create's
     F-OK's found DEVICE. *)
  Lemma file_open_create_au (γfs : fs_names) (c : file_fixed) (r : file_names)
      (jo : option Z) (n : nat) (N : fname) (s : dst) (g : gname)
      (ls : list fwline) (ws : wordline)
      (cw : Z) (M : gmap Z (bv 8)) (pv vom : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    FileDisc.uname N ->
    arg_path_of M pv pl ->
    np_elems pl = [] ->
    um_start_of cw pl = ROOTINO ->
    list_basics.last (path_elems pl) = Some N ->
    (N, ws) ∈ ls -> EchoDisc.line_ok ws ->
    app_inv γfs -∗ file_cons_cred c r jo -∗ fl_lb c ls -∗
    esc_key c r n s g -∗ fesc_res r s g -∗
    open_au_create_at (fs_gamma_L γfs) γfs cw M pv vom
      (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I)
      (fun _ _ => True%I)
      (file_arm_fam c r jo s g) (file_unarm_fam c r s g)
      (file_cre_fam c r jo N s g)
      (file_dlk_fam c r n s g)
      (file_odlk_fam c r n s g)
      (file_trunc_fam c r N s).
  Proof using .
    intros Heq HN Hpath Hnp Hstart Hlast Hin Hok.
    iIntros "#Hinv #Hm #Hlb #Hwit Hres".
    rewrite /open_au_create_at. iSplitR.
    { (* THE WALK: no hops at all, and the start cursor is pure *)
      iIntros (pl0) "%Hpath0".
      rewrite (arg_path_of_uniq M pv pl0 pl Hpath0 Hpath).
      rewrite /ep_start. iIntros (r0) "%Hr0". iModIntro. iSplitR.
      - iPureIntro. rewrite Hr0 Hstart //.
      - iApply (ep_hops_done γfs _ _ pl 0%nat). rewrite Hnp /=. lia. }
    iSplitR "Hres"; last first.
    { iSplitR.
      { iApply (file_dlk_piece γfs c r n s g Heq with "Hinv Hwit"). }
      iSplitR.
      { (* THE OPEN OBSERVATION, at the escrow's reading *)
        iApply (file_odlk_piece γfs c r n s g Heq with "Hinv Hwit"). }
      iSplitR.
      { (* THE TRUNCATE, at the permit create pays (section 3f'') *)
        rewrite /open_trunc_piece. destruct (om_trunc vom); [| done].
        iApply (file_trunc_piece γfs c r jo n N s g ls ws M pv pl
                  Heq HN Hpath Hlast Hin Hok with "Hinv Hm Hwit Hlb"). }
      (* THE CHILD'S TWO LEGS: the escrow goes in HERE and comes back out
         through whichever of the parent leg and the unarm fired *)
      rewrite /cre_child_unfired. iSplitL "Hres".
      - rewrite /pf_at /file_arm_fam /=. iSplit; [| iExact "Hres"].
        iApply (file_arm_commit γfs c r jo n s g [] Heq
                  with "Hinv Hm Hwit Hres").
      - rewrite /pf_at /file_unarm_fam /=. iSplit; [| done].
        iApply (file_unarm_commit γfs c r jo n s g Heq with "Hinv Hm Hwit"). }
    (* THE PARENT LEG, at the guarded cursor: the move between the two
       readings is the ISO, and it costs nothing at this prefix *)
    rewrite /pf_at /file_cre_fam /=. iSplit; [| done].
    rewrite /acre_commit_at_nm.
    (* THE NAME: the kernel pins it at argument 0's last element, which
       is the line's file [N] here *)
    iApply (acre_commit_at_gen_nm_mono (fs_gamma_L γfs) appE
              (fun _ _ => AFile []) (redir_at N) (npar_nm M pv)).
    { intros nm Hnm.
      pose proof (npar_nm_elim M pv pl nm Hpath Hnm) as Hn.
      rewrite /nlast_elem Hlast in Hn. injection Hn as <-.
      reflexivity. }
    iApply (acre_commit_at_gen_nm_cur_mono (fs_gamma_L γfs) appE
              (fun _ _ => AFile []) (redir_at N)
              (fun d : Z => ⌜d = ROOTINO⌝%I)
              (npar_cur M pv (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I))
              (file_arm_fam c r jo s g)
              (file_cre_fam c r jo N s g).(pf_recv)
              with "[] [] []").
    - iIntros "!>" (d) "H". rewrite /npar_cur.
      iApply ("H" $! pl). iPureIntro. exact Hpath.
    - iIntros "!>" (d) "%Hd". rewrite /npar_cur. iIntros (pl0) "_".
      by iPureIntro.
    - iApply (file_acre_commit γfs c r jo n N s g ls ws Heq HN Hin Hok
                with "Hinv Hm Hwit Hlb").
  Qed.

  (* ...and at [om_trunc vom = false], where the truncate is never owed.
     SUBSUMED by the lemma above (lane F-OPEN-3): the bundle supplies its
     own piece at every mode, so this is the same statement under one more
     premise, kept only so a caller at 0x201 need not read the guard. *)
  Lemma file_open_create_au_notrunc (γfs : fs_names) (c : file_fixed)
      (r : file_names) (jo : option Z) (n : nat) (N : fname) (s : dst) (g : gname)
      (ls : list fwline) (ws : wordline)
      (cw : Z) (M : gmap Z (bv 8)) (pv vom : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    FileDisc.uname N ->
    arg_path_of M pv pl ->
    np_elems pl = [] ->
    um_start_of cw pl = ROOTINO ->
    list_basics.last (path_elems pl) = Some N ->
    om_trunc vom = false ->
    (N, ws) ∈ ls -> EchoDisc.line_ok ws ->
    app_inv γfs -∗ file_cons_cred c r jo -∗ fl_lb c ls -∗
    esc_key c r n s g -∗ fesc_res r s g -∗
    open_au_create_at (fs_gamma_L γfs) γfs cw M pv vom
      (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I)
      (fun _ _ => True%I)
      (file_arm_fam c r jo s g) (file_unarm_fam c r s g)
      (file_cre_fam c r jo N s g)
      (file_dlk_fam c r n s g)
      (file_odlk_fam c r n s g)
      (file_trunc_fam c r N s).
  Proof using .
    intros Heq HN Hpath Hnp Hstart Hlast Htr Hin Hok.
    iIntros "#Hinv #Hm #Hlb #Hwit Hres".
    iApply (file_open_create_au γfs c r jo n N s g ls ws cw M pv vom pl
              Heq HN Hpath Hnp Hstart Hlast Hin Hok with "Hinv Hm Hlb Hwit Hres").
  Qed.

  (* ---- 3g.  THE RECEIPT, READ: WHAT THE REDIRECT CHILD GETS BACK ----

     [SpecSysOpen.open_receipt_create] at the families above, folded into
     the payloads lane SH-ROUND instantiates [UkShRedirAns.ush_open_call2]
     with.  Every arm hands the deed back and the lemma says through
     WHICH: a fired truncate through its own receipt, a create that fired
     and then failed through the KEYED PIECE'S REFUND (the permit,
     [SysOpenDefs.cre_ft_kept] -- this is F-OPEN's "third arm"), and
     everything else through the arm piece's refund, WHICH IS NOW THE
     ESCROW and comes home through [AppFile.file_escrow_return].

     THE FD ARM IS [fown r (Some (i, []))] ALONE (lane F-OPEN-5): the
     escrow's reading at the LOOKUP's own view refutes an absent deed at
     the found entry and identifies the row at a present one, so
     F-OPEN-3's unreachable [fown r s] disjunct is gone. *)

  (* what the deed is worth on an arm that did not settle at `f`: F-OPEN-2's
     [Kf], with the taint *)
  (* THE CREATED ARM SAYS [N] WAS ABSENT (the PROGRAM STREAM, stretch 9).
     Its one producer is the create leg's own receipt
     ([file_cre_recv]'s first arm), which holds [s !! N = None]; dropping it
     left a payload the model cannot file -- [FileDisc.fsm]'s [RFOpenM] is
     guarded at an absent file (xv6 truncates only after [filealloc] has
     succeeded), so "present, non-empty, and now empty" after a FAILED
     open is no alternative of the line. *)
  Definition file_open_pay (c : file_fixed) (r : file_names) (N : fname)
      (s : dst) : iProp Σ :=
    (fown r s ∨ (⌜s !! N = None⌝ ∗ ∃ i : Z, fown r (<[N := (i, [])]> s))
     ∨ file_taint c)%I.

  (* ...and the same BEFORE the escrow comes home: this is what every
     payer below produces, and [file_esc_pay_home] is the one fupd that
     turns it into the deed. *)
  Definition file_esc_pay (c : file_fixed) (r : file_names) (N : fname)
      (s : dst) (g : gname) : iProp Σ :=
    (fesc_res r s g ∨ (⌜s !! N = None⌝ ∗ ∃ i : Z, fown r (<[N := (i, [])]> s))
     ∨ file_taint c)%I.

  Lemma file_esc_pay_home (γfs : fs_names) (c : file_fixed) (r : file_names)
      (n : nat) (N : fname) (s : dst) (g : gname) (E : coPset) :
    ↑appN ⊆ E ->
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ esc_key c r n s g -∗ file_esc_pay c r N s g ={E}=∗
      file_open_pay c r N s.
  Proof using .
    intros HE Heq. iIntros "#Hinv #Hwit [[Htk Htok] | [Hd | #HT]]".
    - iMod (file_escrow_return γfs c r n s g E HE Heq
              with "Hinv Hwit Htok Htk") as "[Hown | #HT]".
      + iModIntro. rewrite /file_open_pay. by iLeft.
      + iModIntro. rewrite /file_open_pay. iRight. by iRight.
    - iModIntro. rewrite /file_open_pay. iRight. by iLeft.
    - iModIntro. rewrite /file_open_pay. iRight. by iRight.
  Qed.

  (* the permit, read back off a piece that never fired.  THE TIE IS NOT
     READ here -- identifying the row is the truncate's business, and an
     unfired permit is worth only what was parked in it -- so the lemma is
     at any tie. *)
  Lemma file_permit_pay (c : file_fixed) (r : file_names) (jo : option Z) (n : nat)
      (N : fname) (s : dst) (g : gname) (T : Z -> fname -> iProp Σ) (i : Z)
      (Γ : fs_view_names Σ) :
    trunc_permit_of Γ T
      (file_arm_fam c r jo s g) (file_cre_fam c r jo N s g)
      (file_dlk_fam c r n s g) i -∗
    file_esc_pay c r N s g.
  Proof using .
    iIntros "H". rewrite /trunc_permit_of.
    iDestruct "H" as (d nm) "[_ [Hfresh | [_ Harm]]]".
    - rewrite /cre_acre_fired.
      iDestruct "Hfresh" as (av ents nl) "[_ Hrec]".
      rewrite /file_cre_fam /file_cre_recv. cbn [pf_recv].
      iDestruct "Hrec" as "[[%Hnone Hown] | #HT]".
      + rewrite /file_esc_pay. iRight. iLeft.
        iSplitR; [ iPureIntro; exact (proj1 Hnone) | ].
        iExists i. iExact "Hown".
      + rewrite /file_esc_pay. iRight. iRight. iExact "HT".
    - rewrite /pf_at. iDestruct "Harm" as "[_ Hres]".
      rewrite /file_arm_fam. cbn [pf_refund].
      rewrite /file_esc_pay. by iLeft.
  Qed.

  (* ...AND AT THE TIE, which is what the DEVICE sub-arm needs: the
     escrow's token is in hand beside the lookup's reading AT THE LOOKUP'S
     VIEW.  ONE ARM AND THE TAINT (lane F-OPEN-6): the permit this reads
     is the EXISTS branch, which the arm that paid it now names
     ([SysOpenDefs.trunc_permit_ex]) -- create's [dirlookup] found the
     name, so the create leg never fired and no "the deed is back at the
     row" disjunct is left to report. *)
  Definition file_permit_read (c : file_fixed) (r : file_names) (N : fname)
      (s : dst) (g : gname) (i : Z) : iProp Σ :=
    ((∃ avx : aview,
        ⌜astep avx FsImg.ROOTINO N = Some i⌝ ∗ ⌜f_ok avx s⌝
        ∗ fesc_res r s g)
     ∨ file_taint c)%I.

  Lemma file_permit_tied (c : file_fixed) (r : file_names) (n : nat)
      (N : fname) (s : dst) (g : gname) (jo : option Z) (pl : list (bv 8)) (i : Z)
      (Γ : fs_view_names Σ) :
    list_basics.last (path_elems pl) = Some N ->
    trunc_permit_ex Γ
      (trunc_tie_at pl (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I))
      (file_arm_fam c r jo s g) (file_dlk_fam c r n s g) i -∗
    file_permit_read c r N s g i.
  Proof using .
    intros Hlast. iIntros "H". rewrite /trunc_permit_ex.
    iDestruct "H" as (d nm) "(Htie & Hex & Harm)".
    iEval (rewrite /trunc_tie_at) in "Htie".
    iDestruct "Htie" as "[%Hl %Hd]".
    assert (Hnmf : nm = N) by (rewrite Hlast in Hl; by injection Hl).
    subst nm d.
    rewrite /cre_ex_fired.
    iDestruct "Hex" as (avx entsx nlx) "(%Hrx & %Hex & Hrec)".
    rewrite /file_dlk_fam /file_dlk_recv. cbn [pf_recv].
    rewrite /pf_at. iDestruct "Harm" as "[_ Harm]".
    rewrite /file_arm_fam. cbn [pf_refund].
    assert (Hstx : astep avx FsImg.ROOTINO N = Some i)
      by (rewrite /astep /aents Hrx /= /anode_ents /=; exact Hex).
    iDestruct "Hrec" as "[[_ Hval] | #HT]"; last first.
    { rewrite /file_permit_read. iRight. iExact "HT". }
    iDestruct "Harm" as "[Htk Htok]".
    iDestruct "Hval" as "[%Hokx | #Hsp]"; last first.
    { iDestruct (esc_tok_spent g with "Htok Hsp") as %[]. }
    rewrite /file_permit_read. iLeft. iExists avx.
    rewrite /fesc_res. iFrame "Htk Htok". iPureIntro. by split.
  Qed.

  Lemma file_permit_read_pay (c : file_fixed) (r : file_names) (N : fname)
      (s : dst) (g : gname) (i : Z) :
    file_permit_read c r N s g i -∗ file_esc_pay c r N s g.
  Proof using .
    rewrite /file_permit_read /file_esc_pay.
    iIntros "[Hex | #HT]".
    - iDestruct "Hex" as (avx) "(_ & _ & Hres)". by iLeft.
    - iRight. iRight. iExact "HT".
  Qed.

  (* THE DEVICE SUB-ARM, REFUTED (lanes F-OPEN-5 and F-OPEN-6).  create's
     F-OK admits a found DEVICE; the claim says otherwise AT THE OPEN'S
     OWN OBSERVATION INSTANT, which is what the open observation's family
     reads.  The permit is the EXISTS branch and the arm that paid it now
     says so, so the token refutes the spent disjunct, the tie identifies
     `f`'s row with the row the call reached, and the claim's own [AFile]
     contradicts the [ADev] on the nose.  WHAT IS LEFT IS THE TAINT ALONE
     -- the one state in which the application's claim says nothing about
     the file system, and in which a device at `f` is a real outcome; it
     is the same escape every other arm of this file carries. *)
  Lemma file_dev_refute (c : file_fixed) (r : file_names) (N : fname) (s : dst)
      (g : gname) (i ma mi : Z) (nl : nat) (av : aview) :
    FileDisc.uname N ->
    arow_at av i (MkAnode (ADev ma mi) nl) ->
    file_permit_read c r N s g i -∗
    ((⌜f_ok av s⌝ ∨ esc_spent g) ∨ file_taint c) -∗
    file_taint c.
  Proof using .
    intros HN Hrow. iIntros "Hperm Hobs".
    rewrite /file_permit_read.
    iDestruct "Hperm" as "[Hex | #HT]"; [| by iFrame "HT" ].
    iDestruct "Hex" as (avx) "(%Hstx & %Hokx & [Htk Htok])".
    iDestruct "Hobs" as "[[%Hoka | #Hsp] | #HT]"; [| | by iFrame "HT" ]; last first.
    { iDestruct (esc_tok_spent g with "Htok Hsp") as %[]. }
    exfalso. destruct (s !! N) as [[j bs] |] eqn:HsN; last first.
    { (* an ABSENT entry contradicts the found entry at the tie *)
      pose proof (f_ok_absent avx s N Hokx HN HsN) as Hab.
      rewrite /name_absent in Hab. rewrite Hab in Hstx. discriminate. }
    assert (Hji : j = i).
    { destruct (f_ok_pin avx s N j bs Hokx HsN) as (Hstj & _).
      rewrite Hstj in Hstx. by injection Hstx. }
    subst j. destruct (f_ok_pin av s N i bs Hoka HsN) as (_ & Hrowf).
    rewrite /arow_at in Hrow. cbn [an_nlink] in Hrow.
    destruct (decide (nl = 0%nat)); simpl in Hrow; congruence.
  Qed.

  (* ...and off the keyed piece, whose refund carries it *)
  Lemma file_kept_pay (c : file_fixed) (r : file_names) (jo : option Z) (n : nat)
      (N : fname) (s : dst) (g : gname)
      (γfs : fs_names) (vom : mword 64) (pl : list (bv 8)) (i : Z) :
    om_trunc vom = true ->
    cre_trunc_kept (fs_gamma_L γfs) vom pl
      (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I)
      (file_arm_fam c r jo s g) (file_cre_fam c r jo N s g)
      (file_dlk_fam c r n s g)
      i (file_trunc_fam c r N s) -∗
    file_esc_pay c r N s g.
  Proof using .
    intros Htr. iIntros "H".
    rewrite /cre_trunc_kept /open_trunc_at Htr /pf_at /cre_ft_kept.
    cbn [pf_refund]. iDestruct "H" as "[_ [_ Hk]]".
    rewrite /cre_permit.
    iApply (file_permit_pay c r jo n N s g _ i (fs_gamma_L γfs) with "Hk").
  Qed.

  (* ...and the same piece read AT THE TIE, which the device arm wants *)
  Lemma file_kept_tied (c : file_fixed) (r : file_names) (jo : option Z) (n : nat)
      (N : fname) (s : dst) (g : gname)
      (γfs : fs_names) (vom : mword 64) (pl : list (bv 8)) (i : Z) :
    om_trunc vom = true ->
    list_basics.last (path_elems pl) = Some N ->
    cre_trunc_kept_ex (fs_gamma_L γfs) vom pl
      (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I)
      (file_arm_fam c r jo s g) (file_dlk_fam c r n s g)
      i (file_trunc_fam c r N s) -∗
    file_permit_read c r N s g i.
  Proof using .
    intros Htr Hlast. iIntros "H".
    rewrite /cre_trunc_kept_ex /open_trunc_at Htr /pf_at /cre_ft_kept.
    cbn [pf_refund]. iDestruct "H" as "[_ [_ Hk]]".
    rewrite /cre_permit_ex.
    iApply (file_permit_tied c r n N s g jo pl i (fs_gamma_L γfs) Hlast with "Hk").
  Qed.

  (* the escrow off create's own child legs, which every arm that fired
     nothing hands back *)
  Lemma file_legs_pay (c : file_fixed) (r : file_names) (jo : option Z) (n : nat)
      (N : fname) (s : dst) (g : gname) (Γ : fs_view_names Σ) :
    (cre_child_unfired Γ (AFile []) (file_arm_fam c r jo s g)
       (file_unarm_fam c r s g)
     ∨ ∃ ic : Z, cre_child_pair (file_arm_fam c r jo s g)
                   (file_unarm_fam c r s g) ic) -∗
    file_esc_pay c r N s g.
  Proof using .
    iIntros "[Hch | Hp]".
    - rewrite /cre_child_unfired. iDestruct "Hch" as "[Harm _]".
      iDestruct (pf_at_refund with "Harm") as "Hres".
      rewrite /file_arm_fam. cbn [pf_refund]. rewrite /file_esc_pay.
      by iLeft.
    - iDestruct "Hp" as (ic) "Hp". rewrite /cre_child_pair /cre_unarm_fired.
      iDestruct "Hp" as (av0 c0) "[_ Hrec]".
      rewrite /file_unarm_fam. cbn [pf_recv].
      iDestruct "Hrec" as "[Hres | #HT]"; rewrite /file_esc_pay.
      + by iLeft.
      + iRight. iRight. iExact "HT".
  Qed.

  (* ---- THE FAILURE FOLD, PAID.  Five shapes and every one of them hands
     the escrow or the deed back: through the arm piece's refund where
     nothing fired, and through the KEYED PIECE'S REFUND -- the permit --
     where the create fired and the call failed past it. *)
  Lemma file_open_create_fail_pay (γfs : fs_names) (c : file_fixed)
      (r : file_names) (jo : option Z) (n : nat) (N : fname) (s : dst) (g : gname)
      (cw : Z) (M : gmap Z (bv 8)) (pv vom : mword 64) :
    om_trunc vom = true ->
    open_post_fail_create (fs_gamma_L γfs) γfs cw M pv vom
      (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I)
      (fun _ _ => True%I)
      (file_arm_fam c r jo s g) (file_unarm_fam c r s g)
      (file_cre_fam c r jo N s g) (file_dlk_fam c r n s g)
      (file_odlk_fam c r n s g)
      (file_trunc_fam c r N s) -∗
    file_esc_pay c r N s g.
  Proof using .
    intros Htr. rewrite /open_post_fail_create /open_au_create_at.
    iIntros "[Hau | H]".
    - iDestruct "Hau" as "(_ & _ & _ & _ & _ & Hch)".
      iApply (file_legs_pay c r jo n N s g _ with "[Hch]"). by iLeft.
    - iDestruct "H" as (pl0) "[_ [Hd | Hc]]".
      + iDestruct "Hd" as "(_ & _ & _ & _ & _ & Hch)".
        iApply (file_legs_pay c r jo n N s g _ with "[Hch]"). by iLeft.
      + iDestruct "Hc" as (d) "[_ [Ha | [Hb | Hc]]]".
        * (* (a) the create FIRED and the open failed past it: the deed is
               in the permit, which the keyed piece's refund carries *)
          iDestruct "Ha" as (av i nm ents nl)
            "(_ & _ & _ & _ & _ & _ & Hkept & _)".
          iApply (file_kept_pay c r jo n N s g γfs vom pl0 i Htr with "Hkept").
        * (* (b) the name existed *)
          iDestruct "Hb" as (av i nm ents nl) "(_ & _ & _ & _ & _ & Hfk & _)".
          rewrite /cre_fail_kept Htr.
          iDestruct "Hfk" as "[[Hkept _] | [_ Hlegs]]".
          { iApply (file_kept_pay c r jo n N s g γfs vom pl0 i Htr with "Hkept"). }
          iApply (file_legs_pay c r jo n N s g _ with "Hlegs").
        * (* (c) nothing was observed at all *)
          iDestruct "Hc" as "(_ & _ & _ & _ & Hlegs)".
          iApply (file_legs_pay c r jo n N s g _ with "Hlegs").
  Qed.

  (* ---- WHAT THE FD ARM HANDS THE ROUND, AT THE DESCRIPTOR'S TYPE.  This
     is [UkShRedirAns.ush_open_call2]'s [K], one sentence: the descriptor
     is on an INODE and `f` is present and EMPTY at that inode -- or the
     claim is TAINTED, the one state in which the application promises
     nothing about the file system and in which the kernel's own
     [FdDevice] arm is a real outcome.  That is why the disjunction sits
     OUTSIDE the type equation and not inside it: a tainted claim cannot
     refute a device, and nothing below this line can either.
     [UkFileOpen.redir_K] is this, and it is the name lane SH-ROUND
     instantiates. *)
  Definition file_open_fd_K (omo : offmode) (c : file_fixed) (r : file_names)
      (N : fname) (s : dst) (ty : fdtype) : iProp Σ :=
    ((∃ (i : Z) (γo : gname),
        ⌜ty = FdInode i γo omo⌝ ∗ fown r (<[N := (i, [])]> s)
        (* ...AND THE HALF THE PUBLISH HANDED OUT (lane OFF-LINK-6's L4):
           nothing at mode PARK, [UserOff.uoff γo 0] at mode HAND, which is
           what [UShRound]'s [redir_K] and K1's entry ask for. *)
        ∗ foff_pub omo γo)
     ∨ file_taint c)%I.

  (* ---- THE WHOLE RECEIPT, at the redirect child's own mode.  TWO
     outcomes (lane F-OPEN-6): the [-1] fold, and A DESCRIPTOR ON AN
     INODE with `f` present and empty at it.  F-OPEN-3's "the deed
     unmoved" disjunct is gone (the escrow refutes it), and the DEVICE
     outcome is gone as an arm of its own:
     [SpecSysOpen.open_post_ok_create]'s EXISTS arm now says WHICH BRANCH
     of the truncate permit it paid, so [file_dev_refute] contradicts the
     [ADev] on the nose, and the FRESH arm never had a device sub-arm at
     all -- [sys_open] type-checks the inode [create] returned, STILL
     LOCKED, so its observation is that child's own [AFile []].  What
     survives of the device is the TAINT, which rides
     [file_open_fd_K]'s right disjunct like every other arm's.  See
     section 6. *)
  Lemma file_open_create_recv (γfs : fs_names) (c : file_fixed)
      (omo : offmode)
      (r : file_names) (jo : option Z) (n : nat) (N : fname) (s : dst) (g : gname)
      (cw : Z) (M : gmap Z (bv 8)) (pv vom : mword 64) (pl : list (bv 8))
      (sts : list fdstate) (rv : mword 64) (fdv' : list fdstate)
      (E : coPset) :
    ↑appN ⊆ E ->
    om_trunc vom = true ->
    FileDisc.uname N ->
    arg_path_of M pv pl ->
    list_basics.last (path_elems pl) = Some N ->
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ esc_key c r n s g -∗
    open_receipt_create omo (fs_gamma_L γfs) γfs cw M pv vom
      (fun (_ : nat) (d : Z) => ⌜d = ROOTINO⌝%I)
      (fun _ _ => True%I)
      (file_arm_fam c r jo s g) (file_unarm_fam c r s g)
      (file_cre_fam c r jo N s g) (file_dlk_fam c r n s g)
      (file_odlk_fam c r n s g)
      (file_trunc_fam c r N s) sts rv fdv' ={E}=∗
      ((⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ⌜fdv' = sts⌝
        ∗ file_open_pay c r N s)
       ∨ (∃ ty : fdtype,
            ⌜open_fd_rcpt (om_readable vom) (om_writable vom) ty sts rv fdv'⌝
            ∗ file_open_fd_K omo c r N s ty)).
  Proof using .
    intros HE Htr HN Hpath Hlast Heq. rewrite /open_receipt_create.
    iIntros "#Hinv #Hwit [(%Hr & %Hfdv & Hf) | Hok]".
    { iMod (file_esc_pay_home γfs c r n N s g E HE Heq with "Hinv Hwit [Hf]")
        as "Hpay".
      { iApply (file_open_create_fail_pay γfs c r jo n N s g cw M pv vom Htr
                  with "Hf"). }
      iModIntro. iLeft. iSplitR; [ by iPureIntro |].
      iSplitR; [ by iPureIntro |]. iExact "Hpay". }
    iDestruct "Hok" as (pl0 d i nm) "(%Hpath0 & _ & _ & [Hfresh | Hex])".
    - (* FRESH: create made `f` and the truncate fired at the empty child *)
      iDestruct "Hfresh" as (av ents nl)
        "(_ & _ & _ & _ & _ & Htrc & _ & Hfd)".
      iEval (rewrite Htr) in "Htrc".
      iDestruct "Htrc" as (av' nl') "[_ Hrec]".
      rewrite /file_trunc_fam /file_trunc_recv. cbn [pf_recv].
      iDestruct "Hfd" as (γo) "[%Hrcpt Hpub]".
      iModIntro. iRight. iExists (FdInode i γo omo).
      iSplitR; [ by iPureIntro |]. rewrite /file_open_fd_K.
      iDestruct "Hrec" as "[Hown | #HT]"; [| by iRight ].
      iLeft. iExists i, γo. iSplitR; [ by iPureIntro |]. iFrame "Hown Hpub".
    - (* THE NAME WAS THERE *)
      rewrite (arg_path_of_uniq M pv pl0 pl Hpath0 Hpath).
      iDestruct "Hex" as (avx entsx nlx) "(_ & _ & _ & _ & _ & Hrest)".
      iDestruct "Hrest" as (av nl) "[Hfile | Hdev]".
      + (* ...on a FILE: the truncate fired there *)
        iDestruct "Hfile" as (bs0) "(_ & _ & Htrc & Hfd)".
        iEval (rewrite Htr) in "Htrc".
        iDestruct "Htrc" as (av') "[_ Hrec]".
        rewrite /file_trunc_fam /file_trunc_recv. cbn [pf_recv].
        iDestruct "Hfd" as (γo) "[%Hrcpt Hpub]".
        iModIntro. iRight. iExists (FdInode i γo omo).
        iSplitR; [ by iPureIntro |]. rewrite /file_open_fd_K.
        iDestruct "Hrec" as "[Hown | #HT]"; [| by iRight ].
        iLeft. iExists i, γo. iSplitR; [ by iPureIntro |]. iFrame "Hown Hpub".
      + (* ...or on a DEVICE, WHICH THE CLAIM REFUTES: the permit is the
             EXISTS branch and the arm says so, so all that is left is the
             taint *)
        iDestruct "Hdev" as (ma mi) "(%Hrow & _ & Hobs & Hkept & %Hrcpt)".
        rewrite /file_odlk_fam /file_odlk_recv. cbn [pf_recv].
        iDestruct (file_kept_tied c r jo n N s g γfs vom pl i Htr Hlast
                     with "Hkept") as "Hperm".
        iDestruct (file_dev_refute c r N s g i ma mi nl av HN Hrow
                     with "Hperm Hobs") as "#HT".
        iModIntro. iRight. iExists (FdDevice ma).
        iSplitR; [ by iPureIntro |]. rewrite /file_open_fd_K. by iRight.
  Qed.

  (* =================================================================== *)
  (*  4.  THE READ AT `f`'s INUM                                          *)
  (*                                                                      *)
  (*  [UkTreeRead.tree_read_piece] at the FILE deed, and its arms.  The    *)
  (*  tree's supplier runs on a [□] claim law (a FROZEN deed); this one    *)
  (*  runs on a FRACTION of the live deed, which is all a READ needs --    *)
  (*  the fraction goes into the commit's fupd and comes back out through  *)
  (*  the receipt, and through the piece's own refund if the read never    *)
  (*  fires.                                                              *)
  (* =================================================================== *)

  Definition file_read_recv (c : file_fixed) (r : file_names) (q : Qp)
      (jo : option Z) (s : dst) : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ) :=
    MkPfam (fun (av : aview) (_ : nat) (_ : anode) (_ : nat) =>
              ((⌜fclaim_facts jo s av⌝ ∗ fdq r q s)
               ∨ (fdq r q s ∗ file_taint c))%I)
           (fdq r q s).

  Lemma file_read_piece (γfs : fs_names) (c : file_fixed) (r : file_names)
      (q : Qp) (jo : option Z) (s : dst) (i : Z) (γo : gname) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ file_cons_cred c r jo -∗ fdq r q s -∗
    pf_at (aread_commit_at (fs_gamma_L γfs) appE i γo)
      (file_read_recv c r q jo s).
  Proof using .
    intros Heq. iIntros "#Hinv #Hm Hd". rewrite /pf_at. cbn [pf_recv pf_refund].
    iSplit; [| iExact "Hd" ].
    rewrite /aread_commit_at. iIntros (I off a d) "%Hpre Hka Hoff".
    iMod (file_claim_read γfs c r jo s q I Heq with "Hinv Hm Hd Hka")
      as "(Hka & Hd & Hc)".
    iModIntro. iFrame "Hka".
    iSplitL "Hoff"; [iApply (off_ret_of_link with "Hoff") |].
    iDestruct "Hc" as "[%Hf | #HT]".
    - iLeft. iFrame "Hd". by iPureIntro.
    - iRight. iFrame "Hd". iExact "HT".
  Qed.

  (* =================================================================== *)
  (*  THE HELD READ'S PIECE (kernel stream, item 2)                       *)
  (* =================================================================== *)
  (* [file_read_piece]'s twin at a HELD row, and it is
     [FsAbsWriteFire.awrite_full_adv]'s shape at the read: the program's
     own half of the offset shadow sits in the PIECE'S CLOSURE, the node
     reads the offset it is fired at off it ([UserOff.uoff_agree_k] against
     the arm it was lent) INSIDE its own [forall off], moves both halves
     ([UserOff.uoff_advance]) and hands the box's arm back ADVANCED -- so
     the kernel's fire answers no supplier ([FsAbsReadFire.arf_read_fire_adv]).

     THREE THINGS CHANGE AND NO MORE, which is why this is a twin and not a
     second design:
       * the RECEIPT carries the advanced half, [uoff γo (off + d)], beside
         the claim's own facts.  That is where the write side puts its
         client cursor too: a receipt is indexed by [off] and [d], so the
         position is nameable exactly there and nowhere else;
       * the REFUND carries the half back UNFIRED.  A piece that took
         [uoff γo p] in must return it if it is never spent, and [pf_at]'s
         [∧] is what makes the two halves of that statement one resource;
       * the TAINT arm of the lent link is the one case with no half to
         agree against, and it hands the taint straight back
         ([OffGv.off_link_taint] is good at any value). *)
  Definition file_read_recv_hand (c : file_fixed) (r : file_names) (q : Qp)
      (jo : option Z) (s : dst) (γo : gname) (p : nat)
      : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ) :=
    (* [PipeQueue.pipe_wpost]'s shape at this coupling, and ONE disjunction
       rather than two: FIRED, with the offset the read ran at reported and
       the half advanced by what it read; or the object was disconnected
       under the caller -- which is the SAME EVENT as the claim coming back
       tainted, because the node declines to move a shadow it can no longer
       say anything about -- and the half comes back UNMOVED beside the
       taint that says why. *)
    MkPfam (fun (av : aview) (off : nat) (_ : anode) (d : nat) =>
              ((⌜off = p⌝ ∗ ⌜fclaim_facts jo s av⌝ ∗ fdq r q s
                ∗ uoff γo (p + d)%nat)
               ∨ (fdq r q s ∗ uoff γo p ∗ file_taint c))%I)
           (fdq r q s ∗ uoff γo p).

  Lemma file_read_piece_adv (γfs : fs_names) (c : file_fixed) (r : file_names)
      (q : Qp) (jo : option Z) (s : dst) (i : Z) (γo : gname) (p : nat) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (* THE ONE BRIDGE THIS PIECE NEEDS, and it is the application's own
       equation rather than a fact about the file: the box's disconnect is
       [app_taint] and the claim's is [file_taint c], and only the program
       that owns the claim knows they are the same credential
       ([UShRound]'s [Hkill]).  The caller supplies it; the kernel does not
       invent it. *)
    (* THE ONE BRIDGE THIS PIECE NEEDS, and it is the application's own
       equation rather than a fact about the file: the box's disconnect is
       [app_taint] and the claim's is [file_taint c], and only the program
       that owns the claim knows they are the same credential
       ([UShRound]'s [Hkill] is that equation).  BOTH DIRECTIONS are used
       -- the link's taint becomes the claim's on the receipt, and the
       claim's becomes the link's when the node declines to move a shadow
       it can no longer say anything about. *)
    □ (app_taint -∗ file_taint c) -∗ □ (file_taint c -∗ app_taint) -∗
    app_inv γfs -∗ file_cons_cred c r jo -∗ fdq r q s -∗ uoff γo p -∗
    pf_at (aread_commit_adv (fs_gamma_L γfs) appE i γo)
      (file_read_recv_hand c r q jo s γo p).
  Proof using .
    intros Heq. iIntros "#Hbr #Hrb #Hinv #Hm Hd Hu".
    rewrite /pf_at. cbn [pf_recv pf_refund].
    iSplit; [| iFrame "Hd Hu" ].
    rewrite /aread_commit_adv /file_read_recv_hand. cbn [pf_recv].
    iIntros (I off a d) "%Hpre Hka Hoff".
    iDestruct "Hoff" as "[Hk | #HT]"; last first.
    { (* the object was disconnected under the caller: the taint is the
         advanced arm, the node moves nothing, and the receipt takes its
         own right disjunct *)
      iMod (file_claim_read γfs c r jo s q I Heq with "Hinv Hm Hd Hka")
        as "(Hka & Hd & _)".
      iModIntro. iFrame "Hka".
      iSplitR; [ iApply (off_link_taint with "HT") | ].
      iRight. iFrame "Hd Hu". iApply ("Hbr" with "HT"). }
    (* THE THREE MOVES.  Agree first: the half the piece holds PINS the
       offset the kernel is firing at. *)
    iDestruct (uoff_agree_k γo p (Z.of_nat off) with "Hu Hk") as %Hzp.
    assert (Hoffp : off = p) by lia. subst off.
    iMod (file_claim_read γfs c r jo s q I Heq with "Hinv Hm Hd Hka")
      as "(Hka & Hd & Hc)".
    iDestruct "Hc" as "[%Hf | #HT2]"; last first.
    { (* THE CLAIM CAME BACK TAINTED, so the node DECLINES TO MOVE: it can
         no longer say which row the count was against, and a half advanced
         past the claim's own content is a position nothing bounds.  The
         arm goes back as the taint -- the claim's credential IS the box's
         ([Hrb]) -- and the half comes back UNMOVED, which is
         [PipeQueue.pipe_wpost]'s right arm exactly. *)
      iModIntro. iFrame "Hka".
      iDestruct ("Hrb" with "HT2") as "#HTa".
      iSplitR; [ iApply (off_link_taint with "HTa") | ].
      iRight. iFrame "Hd Hu". iExact "HT2". }
    (* ...then the advance, both halves inside the one update... *)
    iMod (uoff_advance γo p d with "Hu Hk") as "[Hk Hu]".
    (* ...and the arm goes back at the advanced value. *)
    iModIntro. iFrame "Hka".
    iSplitL "Hk"; [ by iApply off_link_of | ].
    iLeft. iFrame "Hd Hu". iSplitR; by iPureIntro.
  Qed.

  (* ...AND THE ARMS, READ: [UkTreeRead.read_arms_tree_learn] with the
     frozen pin replaced by the deed's own reading -- the observed row is
     `f`'s because the CLAIM says so at the very view the kernel read it
     in, and the deed's state names both the inum and the bytes. *)
  (* THE OK ARM ON ITS OWN, so the mapped corollary below -- which REFUTES
     the other one -- does not have to re-prove it. *)
  (* THE COUNT NEVER EXCEEDS THE ONE ASKED FOR, and it is ARM-INDEPENDENT
     (lane OFF-LINK, for CAT-ENTRY-2): [SysReadDefs.ard_ret_tie] answers
     [ard_count] on a file row and a value in [0 .. n] on every other, so
     whatever the receipt's own arm turns out to be -- content or taint --
     the return sits inside the caller's count.  [bv_unsigned] of a
     [mword_of_int] is a [mod], which only ever DECREASES a non-negative
     value, so the bound needs no width side condition. *)
  Lemma moi_le (z : Z) :
    0 <= z -> bv_unsigned (mword_of_int z : mword 64) <= z.
  Proof using .
    intro Hz. rewrite moi_unsigned. apply Z.mod_le; [ exact Hz | ].
    unfold Z64. lia.
  Qed.

  Lemma file_read_post_ok_learn (c : file_fixed) (r : file_names) (q : Qp)
      (jo : option Z) (i : Z) (bs : list (bv 8)) (N : fname) (s : dst) (n : Z)
      (rv : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64)
      (k : nat) (g : nat -> bv 8) :
    s !! N = Some (i, bs) ->
    (forall j : nat, (j < k)%nat ->
       uint (add_vec_int addr (Z.of_nat j)) = (uint addr + Z.of_nat j)%Z) ->
    (forall j : nat, (j < k)%nat ->
       M' !! uint (add_vec_int addr (Z.of_nat j)) = Some (g j)) ->
    (Z.to_nat n <= k)%nat ->
    read_post_ok (fs_gamma_L fsc_fs) i n
      (file_read_recv c r q jo s) rv M' addr -∗
    (⌜(Z.to_nat (bv_unsigned rv) <= Z.to_nat n)%nat⌝ ∗
     (((∃ off : nat,
            ⌜Z.to_nat (bv_unsigned rv)
             = ard_count (Z.to_nat n) off (length bs)⌝ ∗
            ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
               g j = bs !!! (off + j)%nat⌝)
       ∗ fdq r q s)
      ∨ (fdq r q s ∗ file_taint c))).
  Proof using .
    intros HsN Hlin Himg Hnk.
    rewrite /read_post_ok.
    iIntros "Hok".
    iDestruct "Hok" as (av off a d) "(%Hpre & %Hn & %Htie & %Hdr & %Hbytes & Hc)".
    (* THE BOUND, off the tie alone and BEFORE the receipt's arms *)
    assert (Hbnd : (Z.to_nat (bv_unsigned rv) <= Z.to_nat n)%nat).
    { rewrite /ard_ret_tie in Htie.
      destruct (an_node a) as [bs' | ents | ma mi] eqn:Han;
        try rewrite Han in Htie; try cbn in Htie.
      - rewrite Htie.
        pose proof (moi_le (Z.of_nat (ard_count (Z.to_nat n) off (length bs')))
                      ltac:(lia)) as Hle.
        pose proof (ard_count_le (Z.to_nat n) off (length bs')) as Hcl. lia.
      - destruct Htie as (rv' & Hrv & Hlo & Hhi). rewrite Hrv.
        pose proof (moi_le rv' Hlo) as Hle. lia.
      - destruct Htie as (rv' & Hrv & Hlo & Hhi). rewrite Hrv.
        pose proof (moi_le rv' Hlo) as Hle. lia. }
    iSplitR; [ by iPureIntro | ].
    rewrite /file_read_recv. cbn [pf_recv].
    iDestruct "Hc" as "[[%Hf Hd] | [Hd #HT]]"; last first.
    { iRight. iFrame "Hd". iExact "HT". }
    destruct Hf as (Hok & _ & _). destruct (f_ok_pin _ s N i bs Hok HsN) as (_ & Hav).
    destruct Hpre as (Hrow & _ & Hsz).
    assert (Hab : a = MkAnode (AFile bs) 1%nat)
      by exact (arow_at_pinned _ _ _ _ Hrow Hav).
    subst a. cbn [an_node] in Htie, Hbytes.
    cbn [anode_size_ok an_node] in Hsz.
    apply Nat2Z.inj_le in Hsz. rewrite Nat2Z.inj_mul in Hsz.
    change (Z.of_nat InodeInv.MAXFILE) with 268 in Hsz.
    change (Z.of_nat BioDefs.BSIZE) with 1024 in Hsz.
    iLeft. iFrame "Hd". iExists off.
    assert (Hdc : d = ard_count (Z.to_nat n) off (length bs)).
    { assert (Hbu : bv_unsigned rv
                    = Z.of_nat (ard_count (Z.to_nat n) off (length bs))).
      { rewrite Htie. apply moi_small.
        pose proof (ard_count_sub (Z.to_nat n) off (length bs)) as Hle.
        unfold Z64. lia. }
      lia. }
    iPureIntro. split.
    { rewrite -Hdr Nat2Z.id. exact Hdc. }
    intros j Hj.
    assert (Hjd : (j < d)%nat) by (rewrite -Hdr Nat2Z.id in Hj; lia).
    assert (Hdk : (d <= k)%nat).
    { pose proof (ard_count_le (Z.to_nat n) off (length bs)) as Hle. lia. }
    pose proof (Hbytes ltac:(intros i0 Hi0; apply Hlin; lia) j Hjd) as HM.
    pose proof (Himg j ltac:(lia)) as HG.
    rewrite HM in HG. by injection HG.
  Qed.

  (* ...AND THE SAME AT THE HELD PIECE (kernel stream, item 2).  Two things
     the parked reading cannot say come out here, and both come off the
     receipt's second conjunct rather than off any new fact about the file:
     the offset the read RAN AT is the one the caller lent
     ([⌜off = p⌝], the node's own agreement, reported), and the half comes
     back ADVANCED BY WHAT WAS READ.  On the taint arm the half comes back
     SOMEWHERE -- the object was disconnected under the caller, so the only
     honest statement is the existential, which is exactly what
     [UCatKernel.cat_held_read]'s taint arm asks for. *)
  Lemma file_read_post_ok_learn_hand (c : file_fixed) (r : file_names) (q : Qp)
      (jo : option Z) (i : Z) (bs : list (bv 8)) (N : fname) (s : dst) (n : Z) (γo : gname) (p : nat)
      (rv : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64)
      (k : nat) (g : nat -> bv 8) :
    s !! N = Some (i, bs) ->
    (forall j : nat, (j < k)%nat ->
       uint (add_vec_int addr (Z.of_nat j)) = (uint addr + Z.of_nat j)%Z) ->
    (forall j : nat, (j < k)%nat ->
       M' !! uint (add_vec_int addr (Z.of_nat j)) = Some (g j)) ->
    (Z.to_nat n <= k)%nat ->
    read_post_ok (fs_gamma_L fsc_fs) i n
      (file_read_recv_hand c r q jo s γo p) rv M' addr -∗
    (⌜(Z.to_nat (bv_unsigned rv) <= Z.to_nat n)%nat⌝ ∗
     ((⌜Z.to_nat (bv_unsigned rv)
        = ard_count (Z.to_nat n) p (length bs)⌝ ∗
       ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
          g j = bs !!! (p + j)%nat⌝ ∗
       uoff γo (p + Z.to_nat (bv_unsigned rv))%nat ∗
       fdq r q s)
      ∨ (uoff γo p ∗ fdq r q s ∗ file_taint c))).
  Proof using .
    intros HsN Hlin Himg Hnk.
    rewrite /read_post_ok.
    iIntros "Hok".
    iDestruct "Hok" as (av off a d) "(%Hpre & %Hn & %Htie & %Hdr & %Hbytes & Hc)".
    assert (Hbnd : (Z.to_nat (bv_unsigned rv) <= Z.to_nat n)%nat).
    { rewrite /ard_ret_tie in Htie.
      destruct (an_node a) as [bs' | ents | ma mi] eqn:Han;
        try rewrite Han in Htie; try cbn in Htie.
      - rewrite Htie.
        pose proof (moi_le (Z.of_nat (ard_count (Z.to_nat n) off (length bs')))
                      ltac:(lia)) as Hle.
        pose proof (ard_count_le (Z.to_nat n) off (length bs')) as Hcl. lia.
      - destruct Htie as (rv' & Hrv & Hlo & Hhi). rewrite Hrv.
        pose proof (moi_le rv' Hlo) as Hle. lia.
      - destruct Htie as (rv' & Hrv & Hlo & Hhi). rewrite Hrv.
        pose proof (moi_le rv' Hlo) as Hle. lia. }
    iSplitR; [ by iPureIntro | ].
    rewrite /file_read_recv_hand. cbn [pf_recv].
    iDestruct "Hc" as "[(%Hop & %Hf & Hd & Hu) | (Hd & Hu & #HT)]"; last first.
    { iRight. iFrame "Hu Hd". iExact "HT". }
    subst off.
    destruct Hf as (Hok & _ & _). destruct (f_ok_pin _ s N i bs Hok HsN) as (_ & Hav).
    destruct Hpre as (Hrow & _ & Hsz).
    assert (Hab : a = MkAnode (AFile bs) 1%nat)
      by exact (arow_at_pinned _ _ _ _ Hrow Hav).
    subst a. cbn [an_node] in Htie, Hbytes.
    cbn [anode_size_ok an_node] in Hsz.
    apply Nat2Z.inj_le in Hsz. rewrite Nat2Z.inj_mul in Hsz.
    change (Z.of_nat InodeInv.MAXFILE) with 268 in Hsz.
    change (Z.of_nat BioDefs.BSIZE) with 1024 in Hsz.
    assert (Hdc : d = ard_count (Z.to_nat n) p (length bs)).
    { assert (Hbu : bv_unsigned rv
                    = Z.of_nat (ard_count (Z.to_nat n) p (length bs))).
      { rewrite Htie. apply moi_small.
        pose proof (ard_count_sub (Z.to_nat n) p (length bs)) as Hle.
        unfold Z64. lia. }
      lia. }
    assert (Hrvd : Z.to_nat (bv_unsigned rv) = d)
      by (rewrite -Hdr Nat2Z.id; reflexivity).
    iLeft. iFrame "Hd". rewrite Hrvd. iFrame "Hu".
    iPureIntro. split; [ exact Hdc | ].
    intros j Hj.
    assert (Hjd : (j < d)%nat) by lia.
    assert (Hdk : (d <= k)%nat).
    { pose proof (ard_count_le (Z.to_nat n) p (length bs)) as Hle. lia. }
    pose proof (Hbytes ltac:(intros i0 Hi0; apply Hlin; lia) j Hjd) as HM.
    pose proof (Himg j ltac:(lia)) as HG.
    rewrite HM in HG. by injection HG.
  Qed.

  Lemma file_read_arms_learn (c : file_fixed) (r : file_names) (q : Qp)
      (jo : option Z) (i : Z) (bs : list (bv 8)) (N : fname) (s : dst) (γo : gname) (P : uptd) (n : Z)
      (rv : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64)
      (k : nat) (g : nat -> bv 8) :
    s !! N = Some (i, bs) ->
    (forall j : nat, (j < k)%nat ->
       uint (add_vec_int addr (Z.of_nat j)) = (uint addr + Z.of_nat j)%Z) ->
    (forall j : nat, (j < k)%nat ->
       M' !! uint (add_vec_int addr (Z.of_nat j)) = Some (g j)) ->
    (Z.to_nat n <= k)%nat ->
    read_arms (fs_gamma_L fsc_fs) i γo P n
      (file_read_recv c r q jo s) rv M' addr -∗
    (((⌜rv = (mword_of_int (-1) : mword 64)⌝
       ∨ (∃ off : nat,
            ⌜Z.to_nat (bv_unsigned rv)
             = ard_count (Z.to_nat n) off (length bs)⌝ ∗
            ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
               g j = bs !!! (off + j)%nat⌝))
      ∗ fdq r q s)
     ∨ (fdq r q s ∗ file_taint c)).
  Proof using .
    intros HsN Hlin Himg Hnk.
    rewrite /read_arms /read_post_fail.
    iIntros "[Hok | [%Hm1 Hf]]"; last first.
    { (* the sign guard hands the piece back whole; the copyout-fault arm
         hands the FIRED receipt.  Either way the fraction comes home. *)
      iDestruct "Hf" as "[[_ Hpf] | [_ [_ Hfired]]]".
      - iDestruct (pf_at_refund with "Hpf") as "Hd".
        rewrite /file_read_recv. cbn [pf_refund].
        iLeft. iFrame "Hd". iLeft. by iPureIntro.
      - iDestruct "Hfired" as (av off a) "(_ & Hc)".
        rewrite /file_read_recv. cbn [pf_recv].
        iDestruct "Hc" as "[[_ Hd] | [Hd #HT]]".
        + iLeft. iFrame "Hd". iLeft. by iPureIntro.
        + iRight. iFrame "Hd". iExact "HT". }
    iDestruct (file_read_post_ok_learn c r q jo i bs N s n rv M' addr k g
                 HsN Hlin Himg Hnk with "Hok") as "[_ [[H Hd] | [Hd HT]]]".
    - iLeft. iFrame "Hd". iRight. iExact "H".
    - iRight. iFrame "Hd". iExact "HT".
  Qed.

  (* ...AND AT A MAPPED DESTINATION BUFFER THE -1 ARM IS GONE (lane
     READ-RELAY, deliverable 2).  One line: the relay carried the copyout's
     reason from [SpecCopyout] to [FsAbsReadFire.read_post_fail], and a
     program that owns its destination run refutes it there. *)
  Lemma file_read_arms_learn_mapped (c : file_fixed) (r : file_names) (q : Qp)
      (jo : option Z) (i : Z) (bs : list (bv 8)) (N : fname) (s : dst) (γo : gname) (P : uptd) (n : Z)
      (rv : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64)
      (k : nat) (g : nat -> bv 8) :
    s !! N = Some (i, bs) ->
    (forall j : nat, (j < k)%nat ->
       uint (add_vec_int addr (Z.of_nat j)) = (uint addr + Z.of_nat j)%Z) ->
    (forall j : nat, (j < k)%nat ->
       M' !! uint (add_vec_int addr (Z.of_nat j)) = Some (g j)) ->
    (0 <= n)%Z ->
    (Z.to_nat n <= k)%nat ->
    (forall j : nat, (j < k)%nat ->
       uva_wmapped P (uint (add_vec_int addr (Z.of_nat j)))) ->
    read_arms (fs_gamma_L fsc_fs) i γo P n
      (file_read_recv c r q jo s) rv M' addr -∗
    (* ...AND THE COUNT'S BOUND RIDES OUT BESIDE THE ARMS (lane OFF-LINK,
       for CAT-ENTRY-2): a read of [n] bytes returns at most [n] whichever
       arm the receipt took, which is what a caller needs to refute a short
       write at the cursor on the TAINT arm, where the deed says nothing. *)
    (⌜(Z.to_nat (bv_unsigned rv) <= Z.to_nat n)%nat⌝ ∗
     (((∃ off : nat,
          ⌜Z.to_nat (bv_unsigned rv)
           = ard_count (Z.to_nat n) off (length bs)⌝ ∗
          ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
             g j = bs !!! (off + j)%nat⌝)
       ∗ fdq r q s)
      ∨ (fdq r q s ∗ file_taint c))).
  Proof using .
    intros HsN Hlin Himg Hn Hnk Hmap. iIntros "H".
    iApply (file_read_post_ok_learn c r q jo i bs N s n rv M' addr k g
              HsN Hlin Himg Hnk).
    iApply (read_arms_mapped (fs_gamma_L fsc_fs) i γo P n
              (file_read_recv c r q jo s) rv M' addr k
              Hn Hnk Hmap with "H").
  Qed.

  (* ...AND THE HELD PIECE'S MAPPED READING, which is what cat applies: at
     a destination buffer the caller owns there is no [-1] arm at all, so
     the two arms are the content and the taint and both carry the half. *)
  Lemma file_read_arms_learn_mapped_hand (c : file_fixed) (r : file_names)
      (q : Qp) (jo : option Z) (i : Z) (bs : list (bv 8)) (N : fname) (s : dst) (γo : gname) (p : nat)
      (P : uptd) (n : Z)
      (rv : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64)
      (k : nat) (g : nat -> bv 8) :
    s !! N = Some (i, bs) ->
    (forall j : nat, (j < k)%nat ->
       uint (add_vec_int addr (Z.of_nat j)) = (uint addr + Z.of_nat j)%Z) ->
    (forall j : nat, (j < k)%nat ->
       M' !! uint (add_vec_int addr (Z.of_nat j)) = Some (g j)) ->
    (0 <= n)%Z ->
    (Z.to_nat n <= k)%nat ->
    (forall j : nat, (j < k)%nat ->
       uva_wmapped P (uint (add_vec_int addr (Z.of_nat j)))) ->
    read_arms (fs_gamma_L fsc_fs) i γo P n
      (file_read_recv_hand c r q jo s γo p) rv M' addr -∗
    (⌜(Z.to_nat (bv_unsigned rv) <= Z.to_nat n)%nat⌝ ∗
     ((⌜Z.to_nat (bv_unsigned rv)
        = ard_count (Z.to_nat n) p (length bs)⌝ ∗
       ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
          g j = bs !!! (p + j)%nat⌝ ∗
       uoff γo (p + Z.to_nat (bv_unsigned rv))%nat ∗
       fdq r q s)
      ∨ (uoff γo p ∗ fdq r q s ∗ file_taint c))).
  Proof using .
    intros HsN Hlin Himg Hn Hnk Hmap. iIntros "H".
    iApply (file_read_post_ok_learn_hand c r q jo i bs N s n γo p rv M' addr k g
              HsN Hlin Himg Hnk).
    iApply (read_arms_mapped (fs_gamma_L fsc_fs) i γo P n
              (file_read_recv_hand c r q jo s γo p) rv M' addr k
              Hn Hnk Hmap with "H").
  Qed.

  (* =================================================================== *)
  (*  5.  THE O_RDONLY OPEN AT `f` (cat's)                                *)
  (*                                                                      *)
  (*  [PinnedObs.v] section 12 records the wall a LIVE claim meets here:   *)
  (*  a read-only open owes TWO independent pieces that must each read the *)
  (*  claim -- the walk's hops and the terminal observation -- and a       *)
  (*  linear deed sits in only one.  THE FILE DEED WALKS ROUND IT: a READ  *)
  (*  needs no move, so the holder SPLITS its half in two and pays each    *)
  (*  piece with a fraction (section 1).  Both come home -- the walk's     *)
  (*  through the terminal cursor, the observation's through its own       *)
  (*  receipt -- and [fdq_join] puts them back together.                   *)
  (* =================================================================== *)

  (* ---- 5a.  THE PIN, AT THE DEED'S OWN INUM ---- *)

  Lemma f_pin_walks (i : Z) (bs : list (bv 8)) (N : fname) (s : dst) (cw : Z) (pl : list (bv 8)) :
    s !! N = Some (i, bs) ->
    path_elems pl = [N] ->
    um_start_of cw pl = ROOTINO ->
    pin_walks_at (fun v : aview => f_ok v s) cw pl
      [ROOTINO; i] i.
  Proof using .
    intros HsN Hel Hst. rewrite /pin_walks_at Hel. cbn [length].
    split_and!; [ exact Hst | reflexivity |].
    intros v Hv. destruct (f_ok_pin v s N i bs Hv HsN) as (Hstep & _).
    cbn [list_lookup_total].
    eapply ARun_cons; [ exact Hstep | apply ARun_nil ].
  Qed.

  Lemma f_pin_resolves (i : Z) (bs : list (bv 8)) (N : fname) (s : dst) (cw : Z) (pl : list (bv 8)) :
    s !! N = Some (i, bs) ->
    path_elems pl = [N] ->
    um_start_of cw pl = ROOTINO ->
    pin_resolves_abs (fun v : aview => f_ok v s) cw pl
      [ROOTINO; i] i (AFile bs).
  Proof using .
    intros HsN Hel Hst. split; [ exact (f_pin_walks i bs N s cw pl HsN Hel Hst) |].
    intros v Hv. destruct (f_ok_pin v s N i bs Hv HsN) as (_ & Hrow).
    by exists 1%nat.
  Qed.

  (* ---- 5b.  THE CLAIM LAW AT THE ERA'S RECORD, LINEAR IN A FRACTION -- *)

  Lemma file_pin_law_q (c : file_fixed) (r : file_names) (q : Qp) (s : dst) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    ⊢ □ (∀ v : aview, fdq r q s -∗ app_pred app_run v -∗
           app_pred app_run v ∗ fdq r q s ∗ (⌜f_ok v s⌝ ∨ file_taint c)).
  Proof using .
    intros Heq. iDestruct (file_deed_law_q c r q) as "#Hlaw".
    iIntros "!>" (v) "Hd Hp".
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iDestruct ("Hlaw" $! v s with "Hd Hp") as "(Hp & Hd & Hc)".
    iSplitL "Hp".
    { rewrite Heq. cbn [app_pred app_run app_names]. iExact "Hp". }
    iFrame "Hd". iDestruct "Hc" as "[%Hf | #HT]";
      [ iLeft; iPureIntro; exact (proj1 Hf) | by iRight ].
  Qed.

  (* ---- 5c.  THE OBSERVATION, WITH THE FRACTION IN THE RECEIPT -------- *)

  (* [PinnedObs.pobs_aopen_lin]'s three lines, with [K] put in the RECEIPT
     as well as in the refund: the caller must have its fraction back on
     BOTH paths, and a fired observation returns it only through [Φ]. *)
  Definition file_open_recv (c : file_fixed) (r : file_names) (q : Qp)
      (s : dst) : pfam Σ (aview -> Z -> anode -> iProp Σ) :=
    MkPfam (fun (av : aview) (i : Z) (a : anode) =>
              (⌜arow_at av i a⌝ ∗ fdq r q s
               ∗ (⌜f_ok av s⌝ ∨ file_taint c))%I)
           (fdq r q s).

  Lemma file_aopen_piece (γfs : fs_names) (c : file_fixed) (r : file_names)
      (q : Qp) (s : dst) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    app_inv γfs -∗ fdq r q s -∗
    pf_at (aopen_commit_at (fs_gamma_L γfs) appE) (file_open_recv c r q s).
  Proof using .
    intros Heq. iIntros "#Hinv Hd".
    iDestruct (file_deed_law_q c r q) as "#Hlaw".
    rewrite /pf_at. cbn [pf_recv pf_refund]. iSplit; [| iExact "Hd" ].
    rewrite /aopen_commit_at. iIntros (I i a) "%Hrow Hka".
    iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I') "(>Hh & Hp & >%Hdom & #Hx)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iAssert (▷ (file_pred c r (abs_view I) ∗ fdq r q s
                ∗ (⌜f_ok (abs_view I) s /\ file_fs_pure (abs_view I)⌝
                   ∨ file_taint c)))%I with "[Hp Hd]" as "Hpc".
    { iNext. iApply ("Hlaw" with "Hd Hp"). }
    iDestruct "Hpc" as "[Hp [Hd Hc]]". iMod "Hc". iMod "Hd".
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hx".
      iSplitL; [| by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names]. iExact "Hp". }
    iModIntro. iFrame "Hka Hd". iSplitR; [ by iPureIntro |].
    iDestruct "Hc" as "[%Hf | #HT]";
      [ iLeft; iPureIntro; exact (proj1 Hf) | by iRight ].
  Qed.

  (* ---- 5d.  THE BUNDLE ---- *)

  Lemma file_open_plain_au (γfs : fs_names) (c : file_fixed) (r : file_names)
      (q1 q2 : Qp) (i : Z) (bs : list (bv 8)) (N : fname) (s : dst)
      (cw : Z) (M : gmap Z (bv 8)) (pv vom : mword 64) (pl : list (bv 8))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    s !! N = Some (i, bs) ->
    file_app = MkAppcfg file_names (file_pred c) r ->
    arg_path_of M pv pl ->
    path_elems pl = [N] ->
    um_start_of cw pl = ROOTINO ->
    om_trunc vom = false ->
    app_inv γfs -∗
    fdq r q1 s -∗ fdq r q2 s -∗
    open_au_plain_at (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P_lin (file_taint c) [ROOTINO; i] (fdq r q1 s))
      (pobs_Pmiss (file_taint c))
      (file_open_recv c r q2 s) Ft.
  Proof using .
    intros HsN Heq Hpath Hel Hst Htr. iIntros "#Hinv Hd1 Hd2".
    iDestruct (file_pin_law_q c r q1 s Heq) as "#Hcl1".
    rewrite /open_au_plain_at. iSplitL "Hd1".
    { iIntros (pl0) "%Hpath0".
      rewrite (arg_path_of_uniq M pv pl0 pl Hpath0 Hpath).
      iApply (pobs_walk_w_lin γfs (fun v : aview => f_ok v s)
                (file_taint c) (fdq r q1 s)
                (pobs_Pmiss (file_taint c)) cw pl [ROOTINO; i] i
                (f_pin_walks i bs N s cw pl HsN Hel Hst)
                with "[] Hcl1 Hinv Hd1").
      iApply pobs_miss_taint_Pmiss. }
    iSplitL "Hd2".
    { iApply (file_aopen_piece γfs c r q2 s Heq with "Hinv Hd2"). }
    iApply (open_trunc_piece_none _ vom _ Ft Htr).
  Qed.

  (* ---- 5e.  THE RECEIPT, READ AT THE DEED ----

     [UkTreeRead.tree_open_recv_file]'s three-way collapse at the file
     claim: the device and directory arms are refuted by the terminal
     identification, and the file arm's descriptor is on THE DEED'S OWN
     INUM.  BOTH fractions come home. *)
  Lemma file_open_recv_file (γfs : fs_names) (c : file_fixed) (r : file_names)
      (omo : offmode)
      (q1 q2 : Qp) (i : Z) (bs : list (bv 8)) (N : fname) (s : dst)
      (cw : Z) (M : gmap Z (bv 8)) (pv vom : mword 64) (pl : list (bv 8))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (sts : list fdstate) (rv : mword 64) (fdv' : list fdstate) :
    s !! N = Some (i, bs) ->
    arg_path_of M pv pl ->
    path_elems pl = [N] ->
    um_start_of cw pl = ROOTINO ->
    (* no O_TRUNC: the fraction rides the terminal cursor, which a
       truncating open spends into its permit ([SpecSysOpen.cur_kept]) *)
    om_trunc vom = false ->
    open_receipt_plain omo (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P_lin (file_taint c) [ROOTINO; i] (fdq r q1 s))
      (pobs_Pmiss (file_taint c))
      (file_open_recv c r q2 s) Ft sts rv fdv' ={⊤}=∗
      ((* THE FAILED CALL REFUNDS BOTH FRACTIONS (PROGRAM-STREAM stretch 9,
          item 3 (i)): the receipt's failure fold carries the whole bundle
          back ([SpecSysOpen.open_post_fail_plain]) and each of its three
          arms holds the walk's cursor and the observation piece's refund.
          The one [={⊤}=>] is the fold's first arm, as in
          [PinnedOpen.pinned_open_dead_lin]. *)
       (⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ⌜fdv' = sts⌝
        ∗ fdq r q1 s ∗ fdq r q2 s)
       ∨ (∃ γo : gname,
            ⌜open_fd_rcpt (om_readable vom) (om_writable vom)
               (FdInode i γo omo) sts rv fdv'⌝
            (* ...AND THE HALF THE PUBLISH HANDED OUT (lane OFF-LINK-6's
               L4): nothing at mode PARK, [UserOff.uoff γo 0] at mode
               HAND. *)
            ∗ foff_pub omo γo
            ∗ fdq r q1 s ∗ fdq r q2 s)
       ∨ file_taint c).
  Proof using .
    intros HsN Hpath Hel Hst Htr. iIntros "Hrc".
    pose proof (f_pin_resolves i bs N s cw pl HsN Hel Hst) as Hres.
    pose proof Hres as [(_ & Hfin & _) Hpinr].
    rewrite /open_receipt_plain.
    iDestruct "Hrc" as "[(%Hr & %Hfd & Hfail) | Hok]".
    { rewrite /open_post_fail_plain.
      iAssert (|={⊤}=> (fdq r q1 s ∗ fdq r q2 s)
                       ∨ file_taint c)%I with "[Hfail]" as ">Hc".
      { iDestruct "Hfail" as "[Hpre | Hrest]".
        - (* the AU never fired: the walk one-shot at its own start, and
             the observation piece's refund *)
          rewrite /open_au_plain_at. iDestruct "Hpre" as "(Hw & Hpf & _)".
          iDestruct ("Hw" $! pl with "[%]") as "Hst0"; [ exact Hpath | ].
          rewrite /ex_start.
          iMod ("Hst0" $! (um_start_of cw pl) with "[//]") as "[HP _]".
          iModIntro. rewrite /pobs_P_lin.
          iDestruct "HP" as "[[_ Hd1] | #HT]"; [ | by iRight ].
          rewrite /pf_at. iDestruct "Hpf" as "[_ Hd2]".
          rewrite /file_open_recv. cbn [pf_refund]. iLeft. iFrame "Hd1 Hd2".
        - iDestruct "Hrest" as (pl') "(%Hpath' & Hr2)". iModIntro.
          iDestruct "Hr2" as "[Hdead | Hpost]".
          + (* the walk died: the cursor at the hop it died at (a MISS at a
               present [f] is the taint), the piece unfired *)
            iDestruct "Hdead" as "(Hde & Hpf & _)".
            rewrite /namei_walk_dead_era.
            iDestruct "Hde" as (k d) "(_ & Harm)".
            iDestruct "Harm" as "[[HP _] | [HPm _]]"; last first.
            { iRight. rewrite /pobs_Pmiss. iExact "HPm". }
            rewrite /pobs_P_lin.
            iDestruct "HP" as "[[_ Hd1] | #HT]"; [ | by iRight ].
            rewrite /pf_at. iDestruct "Hpf" as "[_ Hd2]".
            rewrite /file_open_recv. cbn [pf_refund]. iLeft.
            iFrame "Hd1 Hd2".
          + (* the inode was reached: the terminal cursor and the piece's
               RECEIPT *)
            iDestruct "Hpost" as (i0) "(HP & Hrv & _)".
            iEval (rewrite /cur_kept Htr) in "HP".
            rewrite /pobs_P_lin.
            iDestruct "HP" as "[[_ Hd1] | #HT]"; [ | by iRight ].
            iDestruct "Hrv" as (av a) "[_ Hrecv]".
            rewrite /file_open_recv. cbn [pf_recv].
            iDestruct "Hrecv" as "(_ & Hd2 & _)". iLeft. iFrame "Hd1 Hd2". }
      iModIntro. iDestruct "Hc" as "[[Hd1 Hd2] | #HT]"; [ | by iRight; iRight ].
      iLeft. iFrame "Hd1 Hd2". iPureIntro. exact (conj Hr Hfd). }
    iModIntro.
    iDestruct "Hok" as (pl' av j) "(%Hpath' & HP & Harm)".
    rewrite (arg_path_of_uniq M pv pl' pl Hpath' Hpath).
    (* the terminal cursor names the deed's inum and hands the walk's
       fraction back *)
    iEval (rewrite /cur_kept Htr) in "HP".
    rewrite /pobs_P_lin Hel. cbn [length].
    iDestruct "HP" as "[[%Hj Hd1] | #HT]"; last first.
    { iRight. iRight. iExact "HT". }
    cbn [list_lookup_total] in Hj. subst j.
    iDestruct "Harm" as "[Hdev | [Hfile | Hdir]]".
    - (* DEVICE: refuted -- the deed says the row is a FILE *)
      iDestruct "Hdev" as (ma mi nl) "(%Hrow & _ & Hrecv & _ & _)".
      rewrite /file_open_recv. cbn [pf_recv].
      iDestruct "Hrecv" as "(%Hra & Hd2 & [%Hf | #HT])"; last first.
      { iRight. iRight. iExact "HT". }
      exfalso. destruct (f_ok_pin _ s N i bs Hf HsN) as (_ & Hav).
      pose proof (arow_at_pinned _ _ _ _ Hra Hav) as Hab. discriminate Hab.
    - (* FILE: the descriptor is on the deed's own inum *)
      iDestruct "Hfile" as (bs0 nl) "(%Hrow & Hrecv & _ & Hfdr)".
      rewrite /file_open_recv. cbn [pf_recv].
      iDestruct "Hrecv" as "(%Hra & Hd2 & [%Hf | #HT])"; last first.
      { iRight. iRight. iExact "HT". }
      iDestruct "Hfdr" as (γo) "[%Hfdr Hpub]".
      iRight. iLeft. iExists γo. iFrame "Hpub Hd1 Hd2". by iPureIntro.
    - (* DIRECTORY: refuted the same way *)
      iDestruct "Hdir" as (ents nl) "(%Hrow & _ & Hrecv & _ & _)".
      rewrite /file_open_recv. cbn [pf_recv].
      iDestruct "Hrecv" as "(%Hra & Hd2 & [%Hf | #HT])"; last first.
      { iRight. iRight. iExact "HT". }
      exfalso. destruct (f_ok_pin _ s N i bs Hf HsN) as (_ & Hav).
      pose proof (arow_at_pinned _ _ _ _ Hra Hav) as Hab. discriminate Hab.
  Qed.

  (* ---- 3h.  THE ESCROW THAT WOULD CLOSE THE `s = None` EXISTS ARM, AND
     THE MASK THAT REFUTES IT (lane F-OPEN-4).

     Lane F-OPEN-3 left the EXISTS disjunct at [s = None] DISCHARGED and
     not REFUTED (section 6 (a)) and named two ways out; way (ii) was
     ruled: put the deed's half in an INVARIANT OF THE CLAIM'S OWN with a
     one-shot in the arm piece, so the LOOKUP piece may open it, read
     [fdeed r None] against [file_pred] through [file_deed_law], conclude
     [f_ok avx None] and refute [Fex]'s found entry at the tie.

     THAT SHAPE IS REFUTED, and by a MASK and not by a fraction.  The
     refutation needs TWO resources at ONE instant -- [file_pred c r avx],
     which lives only inside [AppInv.app_inv] at the namespace
     [AppInv.appN], and the deed's half, which by hypothesis lives inside
     an escrow invariant at some namespace [N].  The lookup piece is
     [FsAbsCreateFire.dlookup_commit_at Gamma appE], whose body is a fancy
     update AT THE MASK [AppInv.appE], and the kernel fixes that mask:
     [SysOpenDefs.open_au_create_at] (SysOpenDefs.v line 864) asks the
     application for [pf_at (dlookup_commit_at Gamma appE) Fex] and for
     nothing else.  [AppInv.appE] is [nclose appN] (AppInv.v line 85), so
     opening [app_inv] with [inv_acc appE appN] leaves the mask
     [appE ∖ nclose appN], which is EMPTY -- and no namespace's closure
     is empty.  The two lemmas below are that argument, machine-checked;
     [file_escrow_mask_blocked] is the whole obstruction.

     So an escrow invariant may be opened at a fire point -- AppInv.v's
     own mask note says so, and [OffGv.foffN] is the landed example -- but
     never AT THE SAME TIME as the claim, which is exactly what the
     refutation wants.  The remaining ways are unchanged in number: lane
     F-OPEN-2's restatement 3 (kernel-tier), or a THIRD one this lane
     names, (iii): move the escrow INSIDE the claim, i.e. give
     [AppFile.f_state] an arm in which the holder's half is parked beside
     a one-shot the holder keeps, so that ONE invariant carries both and
     the mask question never arises.  (iii) is an [AppFile.v] restatement
     of [file_pred] and therefore moves the transports, the boot resource,
     the era-0 mint and every landed consumer of the claim; it is not a
     [FileOpen.v] change, which is what the ruling assumed way (ii) was. *)

  Lemma app_commit_mask_full : appE ∖ ↑appN = ∅.
  Proof using . rewrite /appE. set_solver. Qed.

  (* NO invariant at all can be opened inside a commit that has the claim
     open: the mask left over is empty, and a namespace's closure is
     infinite. *)
  Lemma file_escrow_mask_blocked (N : namespace) :
    (↑N : coPset) ⊆ appE ∖ ↑appN -> False.
  Proof using .
    intros HN. apply (nclose_infinite N). exists nil. intros x Hx.
    exfalso. apply HN in Hx. rewrite /appE in Hx.
    assert (Hem : x ∈ (∅ : coPset)) by (revert Hx; set_solver).
    revert Hem. set_solver.
  Qed.

End FileOpen.

(* ===================================================================== *)
(*  6.  WHAT IS *NOT* HERE, AND EXACTLY WHY (the lane's STOP rule)        *)
(*                                                                       *)
(*  (a) THE O_TRUNC LEG OF THE CREATE BUNDLE -- CLOSED (lane F-OPEN-3),   *)
(*      WITH ONE HOLE NAMED AT THE END.                                   *)
(*                                                                       *)
(*      WHAT LANDED.  [SysOpenDefs.open_trunc_piece] now carries the      *)
(*      permit [SysOpenDefs.trunc_permit_of]: the WALK'S TIE (the arg     *)
(*      path's last element is [nm], and the walk's terminal directory is *)
(*      [d] -- the two facts [SysMknodDefs.npar_cur] carries, guarded the *)
(*      same way) beside the DISJUNCTION the kernel pays from whichever   *)
(*      of create's arms ran: the create leg's fired receipt on the FRESH *)
(*      run, the exists observation's receipt BESIDE THE UNFIRED ARM      *)
(*      PIECE on the EXISTS one.  [file_trunc_piece] supplies it at both  *)
(*      ([file_trunc_of_cre] and [file_trunc_of_exists]), and             *)
(*      [file_open_create_au] no longer takes the truncate as a premise   *)
(*      at any mode -- the 0x601 bundle is one deed.                      *)
(*                                                                       *)
(*      THE RULING SAID THE EXISTS DISJUNCT NEEDS A DEED FRACTION INSIDE  *)
(*      [Fex]'s RECEIPT (lane F-OPEN-2's finding 2) AND IT DOES NOT.      *)
(*      What the disjunct must establish at the truncate is that the row  *)
(*      the call reached is not one of the four era-0 binaries, and the   *)
(*      claim says that at the LOOKUP's view with NOTHING LINEAR: its     *)
(*      non-taint arm carries [⌜file_fs_pure av⌝], and both arms of       *)
(*      [AppFile.f_state] carry the TYPED witness of whatever state the   *)
(*      claim is at, whose pure part bounds the content by               *)
(*      [EchoDisc.line_max].  That is [fclaim_free] and                   *)
(*      [file_claim_read_free], and it is why [file_dlk_fam]'s receipt    *)
(*      holds no fraction at all -- which is what makes the whole half    *)
(*      available in the ARM piece, where the create leg needs it.        *)
(*      Lane F-OPEN-2's finding 3 (the split is impossible at             *)
(*      [s = None]) was therefore never on the critical path, and no      *)
(*      third kernel seam was needed.                                     *)
(*                                                                       *)
(*      WHAT IS STILL OPEN, and it is the ONE thing a redirect round      *)
(*      needs next: THE EXISTS DISJUNCT AT [s = None] IS DISCHARGED AND   *)
(*      NOT REFUTED.  At an absent deed a run in which create's           *)
(*      [dirlookup] FINDS `f` is unreachable, but the SUPPLY must still   *)
(*      cover it; [file_trunc_of_exists] covers it by stepping FREELY     *)
(*      (the row is not pinned, [f_ok av None] is preserved) and handing  *)
(*      the deed back UNMOVED, so [file_trunc_recv]'s first arm           *)
(*      ([fown r s]) is reachable in the statement though not on any run. *)
(*      REFUTING it needs the claim read AT THE LOOKUP'S VIEW -- the      *)
(*      entry fact [ents !! f = Some i] is at [avx], and between [avx]    *)
(*      and the [itrunc] the parent is unlocked, so no later view carries *)
(*      it -- and reading the claim's OWN VALUE there (rather than the    *)
(*      determined one) needs a positive deed fraction inside the [Fex]   *)
(*      piece, which at [s = None] the create's parent leg has already    *)
(*      claimed in full ([AppFile.file_step_park] at `f` wants            *)
(*      [fdeed_whole], and the bundle's pieces are [∗]-separated).  So    *)
(*      the choice was priced as two: (i) lane F-OPEN-2's restatement 3   *)
(*      -- [FsAbsCreateFire.acre_commit_at_gen] takes the UNFIRED [Fex]   *)
(*      piece beside the arm's receipt, making the two exclusive in the   *)
(*      logic and letting the parent leg reassemble [q1 + q2]; or (ii) an *)
(*      APPLICATION-SIDE ESCROW -- the deed's half in an invariant of the *)
(*      claim's own, with the arm's piece holding the one-shot that says  *)
(*      it has not fired, so [Fex] may read it and the arm may take it.   *)
(*                                                                       *)
(*      (ii) IS REFUTED (lane F-OPEN-4), AND BY THE MASK.  Section 3h     *)
(*      above carries the argument and its two machine-checked lemmas     *)
(*      ([app_commit_mask_full], [file_escrow_mask_blocked]): the lookup  *)
(*      piece's commit is a fancy update at [AppInv.appE], the kernel     *)
(*      fixes that mask ([SysOpenDefs.open_au_create_at]), [appE] is      *)
(*      [nclose appN], and reading the claim opens [appN] -- so the mask  *)
(*      left over is EMPTY and no escrow invariant, at any namespace,     *)
(*      can be open at the same instant as the claim.  The deed's half    *)
(*      and [file_pred] must meet, and there is no place for them to.     *)
(*      What replaces (ii) is (iii): move the escrow INSIDE the claim --  *)
(*      an arm of [AppFile.f_state] in which the holder's half is parked  *)
(*      beside a one-shot the holder keeps -- so that ONE invariant       *)
(*      carries both.  That is an [AppFile.v] restatement of [file_pred], *)
(*      not a [FileOpen.v] one, and it moves the transports, the boot     *)
(*      resource, the era-0 mint and every landed consumer of the claim.  *)
(*      (iii) LANDED (lane F-OPEN-5), and the fd arm is                   *)
(*      [fown r (Some (i, [])) ∨ file_taint c].                           *)
(*                                                                       *)
(*      THE SAME SHAPE ONCE MORE, SMALLER, AND ALSO CLOSED: create's      *)
(*      F-OK admits a found DEVICE, and the row's type is reported at the *)
(*      OPEN's observation instant while the tie is at the lookup's.      *)
(*      What closes it is not a wider reading but the ARM SAYING WHICH    *)
(*      BRANCH OF THE TRUNCATE PERMIT IT PAID (lane F-OPEN-6,             *)
(*      [SysOpenDefs.trunc_permit_ex]): the device is reported on the     *)
(*      EXISTS run alone, the escrow's token is in hand there, and        *)
(*      [file_dev_refute] contradicts the [ADev] on the nose.  The FRESH  *)
(*      run needs nothing: [sys_open] type-checks the inode [create]      *)
(*      returned, still locked, so its observation is that child's own    *)
(*      [AFile []] and the arm has no device sub-arm.  WHAT SURVIVES IS   *)
(*      THE TAINT, and it survives everywhere: a tainted claim promises   *)
(*      nothing about the file system, so the kernel's [FdDevice] is a    *)
(*      real outcome there and no reading of the claim can refute it.     *)
(*      That is why [file_open_fd_K] puts the taint OUTSIDE the type      *)
(*      equation -- the fd arm is one arm, not two, and the type is       *)
(*      pinned on every branch but the taint.                             *)
(*                                                                       *)
(*  (b) THE O_RDONLY OPEN AT AN ABSENT `f` -- CLOSED (lane F-OPEN-2,      *)
(*      seam 2).  [file_open_miss_au] / [file_open_miss_recv] below are    *)
(*      the bundle and its receipt at [f_pin_misses], and the fraction     *)
(*      comes home.  What F-OPEN priced as two fixes turned out to be      *)
(*      one: put [K] ON THE CURSOR ([PinnedObs.pobs_P_dead_lin], section   *)
(*      11a's construction one list shorter) and BOTH arms of              *)
(*      [SysOpenDefs.namei_walk_dead_era] refund without that definition   *)
(*      moving -- the `hop never fired` arm hands back [P k d] and the     *)
(*      `fired and missed` arm hands back [Pmiss k d], and at              *)
(*      [pobs_Pmiss_ref] both carry [K].  The walk piece did NOT have to   *)
(*      become a [pf_at].                                                  *)
(* ===================================================================== *)

Section FileOpenMiss.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.

  (* the pin an ABSENT class name gives the walk: the first hop misses *)
  Lemma f_pin_misses (N : fname) (s : dst) (cw : Z) (pl : list (bv 8)) :
    FileDisc.uname N -> s !! N = None ->
    path_elems pl = [N] ->
    um_start_of cw pl = ROOTINO ->
    pin_misses_at (fun v : aview => f_ok v s) cw pl ROOTINO.
  Proof using .
    intros HN HsN Hel Hst. split; [ exact Hst |].
    intros v nm Hp Hs. rewrite Hel in Hs. cbn in Hs.
    injection Hs as <-. exact (f_ok_absent v s N Hp HN HsN).
  Qed.
  (* the taint answers for every view: [AppFile.file_sup_of_taint] at the
     application the instance names *)
  Lemma file_taint_sup (c : file_fixed) (r : file_names) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    ⊢ □ (file_taint c -∗ app_sup).
  Proof using .
    intros Heq. rewrite /app_sup Heq.
    cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
    iIntros "!> #Ht". iApply (file_sup_of_taint c r with "Ht").
  Qed.

  (* ---- THE BUNDLE, AND IT REFUNDS THE FRACTION ----

     [PinnedOpen.pinned_open_bundle_dead_lin] at the ABSENT pin: the walk
     dies at its first hop, the success fold collapses to the taint, and
     the deed fraction the hop was paid with rides the CURSOR and comes
     home through whichever arm of the failure fold the receipt hands
     back ([PinnedObs] section 8a).  That is the whole of what lane
     F-OPEN's STOP item (b) was waiting on.

     AT ANY MODE THAT DOES NOT CREATE (lane TRUNC-PERMIT): the truncate's
     permit is the walk's terminal cursor, which at this dead pin is the
     taint, and the taint pays the step out of the supply -- so the piece
     is owed at the family whose receipt is the taint, and the miss
     receipt below collects it there. *)
  Lemma file_open_miss_au (γfs : fs_names) (c : file_fixed) (r : file_names)
      (q : Qp) (N : fname) (s : dst) (cw : Z) (M : gmap Z (bv 8)) (pv vom : mword 64)
      (pl : list (bv 8))
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    FileDisc.uname N -> s !! N = None ->
    arg_path_of M pv pl ->
    path_elems pl = [N] ->
    um_start_of cw pl = ROOTINO ->
    om_create vom = false ->
    app_inv γfs -∗
    fdq r q s -∗
    open_in (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P_dead_lin (file_taint c) (fdq r q s) ROOTINO)
      (pobs_Pmiss_ref (file_taint c) (fdq r q s))
      Farm Fun Fok Fex
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : anode) => True%I))
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : list (bv 8)) => file_taint c)).
  Proof using .
    intros Heq HN HsN Hpath Hel Hst Hcr. iIntros "#Hinv Hd".
    iApply (pinned_open_bundle_dead_lin γfs
              (fun v : aview => f_ok v s) (file_taint c)
              (fdq r q s)
              (pobs_Pmiss_ref (file_taint c) (fdq r q s))
              cw pl ROOTINO M pv vom Farm Fun Fok Fex
              Hcr (f_pin_misses N s cw pl HN HsN Hel Hst) Hpath
              ltac:(rewrite Hel; discriminate)
              with "[] [] [] Hinv [] Hd").
    - iApply (file_pin_law_q c r q s Heq).
    - iApply pobs_miss_taint_ref.
    - iApply pobs_miss_hold_ref.
    - iApply (file_taint_sup c r Heq).
  Qed.

  (* ...AND THE RECEIPT: the open failed and the table did not move AND
     THE FRACTION IS BACK, or the application is tainted.  There is no
     third arm -- cat's `cannot open` branch is a THEOREM at an absent
     deed, not an arm it has to carry. *)
  Lemma file_open_miss_recv (γfs : fs_names) (c : file_fixed) (r : file_names)
      (omo : offmode)
      (q : Qp) (N : fname) (s : dst) (cw : Z) (M : gmap Z (bv 8)) (pv vom : mword 64)
      (pl : list (bv 8))
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (sts : list fdstate) (rv : mword 64) (fdv' : list fdstate) :
    arg_path_of M pv pl ->
    path_elems pl = [N] ->
    open_receipt_plain omo (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P_dead_lin (file_taint c) (fdq r q s) ROOTINO)
      (pobs_Pmiss_ref (file_taint c) (fdq r q s)) Fo
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : list (bv 8)) => file_taint c))
      sts rv fdv'
    ={⊤}=∗ ((⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ⌜fdv' = sts⌝
             ∗ fdq r q s)
            ∨ file_taint c).
  Proof using .
    intros Hpath Hel. iIntros "Hrc".
    iApply (pinned_open_dead_lin γfs (file_taint c) (fdq r q s) omo
              cw pl ROOTINO M pv vom Fo
              (pfam_triv (fun (_ : aview) (_ : Z) (_ : list (bv 8)) => file_taint c))
              sts rv fdv' Hpath
              ltac:(rewrite Hel; discriminate)
              ltac:(intros _ av i bs; cbn [pfam_triv pf_recv]; reflexivity)
              with "Hrc").
  Qed.

End FileOpenMiss.
