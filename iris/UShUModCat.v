(* ===================================================================== *)
(*  UShUModCat.v -- THE [cat f] LINE'S SHAPE MODULE (shape-modules S1,    *)
(*  step 3; design: claude-notes/design/shape-modules.md sections 2 and  *)
(*  5).                                                                   *)
(*                                                                        *)
(*  Everything the round needs of the [cat f] line, in one file: its     *)
(*  argument words and exec-failed bytes (moved from [UShUModBase]; the  *)
(*  rows [ucat_rows] stay there, the sync and seccomp supplies read      *)
(*  them), the cat child's exec supply and law at the union's credential *)
(*  [uHchild_cat] (moved from [UShURound]'s S2), the module [mod_cat]    *)
(*  ([UkShShape.shape_mod]: the family [LCat _], the line predicate      *)
(*  [UkShRedirBody.ushs_lp_cat], first bytes 'c' 'a', room 68) and the   *)
(*  body law at the cat line [ucat_body_law], the generic                *)
(*  [UkShShape.ushf_body_law_of_mod]'s instance.  The out-of-memory law  *)
(*  with the deed opened is [UShURoundDefs.uoom_law_deed] (the redirect  *)
(*  child reads it too).                                                  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserChildren.
Require Import UexecRet.
Require Import ExecEntry.
Require Import UkRun.
Require Import UexecExecInst.
Require Import WpUart.
Require Import FsImg.
Require Import FsCatPin.
Require Import AppCfg.
Require Import AppFileCons.
Require Import UserPerm.
Require Import UserPtTree.
Require Import LineWords.
Require Import EchoDisc.
Require Import EchoOut.
Require Import FileDisc.
Require Import FileState.
Require Import AppEcho.
Require Import AppFile.
Require UNamePath.                (* the path/argv facts off the class laws *)
Require Import UNameBytes.        (* the diagnostic windows *)
Require Import FileOut.
Require Import FileOpen.
Require Import UkShRedirBody.
Require Import ExecWords.
Require Import UkShDiagAt.
Require Import UShCat.
Require Import UShCatPay.
Require Import ElfUser.
Require Import UkSh.
Require Import UkShDiag.
Require Import UkShEcho.
Require Import UkShFork.
Require Import LinkRec.
Require Import FileLinkGen.
Require Import FileHooks.
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenLinksLine.
Require Import UShPanic.
Require Import UkConsOut.
Require Import PipeOut.
Require Import UnionDisc.
Require Import UnionDiscDec.
Require Import UnionOut.
Require Import UnionLinks.
Require Import UnionLinkInstAt.
Require Import UkUnionEntries.
Require Import UShURoundDefs.
Require UkFileIface.
Require FileDeltas.
Require UShExecPin.
Require Import CtxIdDefs.
Require Import UShUModBase.       (* the pure preamble, shared with the shape modules *)
Require Import UkShShape.
Local Open Scope Z_scope.
Import Defs.

Local Notation U := ulmG.
Local Notation K := ulmG_hooks.

(* ---- cat's argument words at the line's name, positionally over its
        length (seam (d); cut W3) ---- *)
Definition ucat_ws (nm : list (bv 8)) : list (list (bv 8)) := FileDisc.uline_ws (LCat nm).

Lemma ucat_ws_exec_ok (nm : list (bv 8)) : FileDisc.uname nm -> exec_ok (ucat_ws nm).
Proof using. exact (UNamePath.cat_words_exec_ok nm). Qed.
Lemma ucat_ws_len (nm : list (bv 8)) : length (ucat_ws nm) = 2%nat.
Proof using. reflexivity. Qed.
Lemma ucat_ws_alen (nm : list (bv 8)) : UkShEcho.echo_alen (ucat_ws nm) 1%nat = length nm.
Proof using. reflexivity. Qed.
Lemma ucat_ws_fname (nm : list (bv 8)) (j : nat) :
  (j < length nm)%nat ->
  LineWords.wl_line (ucat_ws nm) !!! (UkShEcho.echo_off (ucat_ws nm) 1%nat + j)%nat
  = nm !!! j.
Proof using.
  intro Hj. unfold UkShEcho.echo_off.
  exact (LineWords.wl_line_word (ucat_ws nm) 1%nat nm j eq_refl Hj).
Qed.
Lemma ucat_ws_head (nm : list (bv 8)) : ucat_ws nm !!! 0%nat = UShCatPay.cat_pl.
Proof using. exact (UNamePath.cat_words_head nm). Qed.
Lemma ucat_ws_line (nm : list (bv 8)) :
  LineWords.wl_line (ucat_ws nm) = FileDisc.line_bytes (LCat nm).
Proof using. reflexivity. Qed.

Lemma ucat_xline (nm : list (bv 8)) (gb : nat -> bv 8) (len : nat) :
  UkSh.ush_line_at (LCat nm) gb 0%nat len ->
  UkShEcho.ush_xline_is (ucat_ws nm) gb 0%nat len.
Proof using.
  intros (Hu & Hlen & Hby). split; [exact (ucat_ws_exec_ok nm Hu) |].
  rewrite ucat_ws_line. exact (conj Hlen Hby).
Qed.

(* cat's exec-failed alternative, around its name (the command word, not
   the file's: the same at every name) *)
Lemma ucat_execfail_bytes0 :
  UkShDiagAt.ush_execfail_bytes FileDisc.alt_execcat UShCatPay.cat_pl.
Proof using.
  rewrite /UkShDiagAt.ush_execfail_bytes. split_and!.
  - vm_compute. lia.
  - intros p Hp.
    assert (Hl : (p < length FileDisc.alt_execcat)%nat)
      by (vm_compute in Hp |- *; lia).
    exact (list_lookup_lookup_total_lt FileDisc.alt_execcat p Hl).
  - intros p Hp.
    apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x1298)
             (fun q : nat => FileDisc.alt_execcat !!! q) 0%nat 5%nat);
      [vm_compute; reflexivity | lia].
  - intros j Hj.
    assert (Hj3 : (j < 3)%nat) by (vm_compute in Hj; lia).
    destruct j as [| [| [| j]]]; try lia; vm_compute; reflexivity.
  - intros p Hp.
    apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x1298)
             (fun q : nat => FileDisc.alt_execcat !!! (q + 1)%nat)
             7%nat 8%nat);
      [vm_compute; reflexivity | lia].
Qed.

Lemma ucat_execfail_bytes (nm : list (bv 8)) :
  UkShDiagAt.ush_execfail_bytes FileDisc.alt_execcat (ucat_ws nm !!! 0%nat).
Proof using. rewrite ucat_ws_head. exact ucat_execfail_bytes0. Qed.
(* ---- THE MODULE: the cat line as the round sees it ---- *)
(* its first bytes are 'c' 'a', and it is at least two long *)
Lemma ucat_lp0 (ws : list (list (bv 8))) (g : nat -> bv 8) (k len : nat) :
  UkShRedirBody.ushs_lp_cat ws g k len -> head_ok HeadCA g k len.
Proof using .
  intros (nm & _ & Hline). cbn [head_ok].
  assert (Hb0 : bv_unsigned (g k) = 99%Z).
  { pose proof (UkShRedirBody.ushs_cat_byte nm g k len 0%nat Hline ltac:(lia)) as H0.
    rewrite Nat.add_0_r in H0. rewrite H0. by vm_compute. }
  assert (Hb1 : bv_unsigned (g (k + 1)%nat) = 97%Z).
  { pose proof (UkShRedirBody.ushs_cat_byte nm g k len 1%nat Hline ltac:(lia)) as H1.
    rewrite H1. by vm_compute. }
  assert (Hlen2 : (2 <= len)%nat).
  { destruct Hline as (_ & Hl & _). rewrite Hl UNameBytes.cat_line_len. lia. }
  split_and!; [exact Hb0 | exact Hb1 | exact Hlen2].
Qed.

Lemma ucat_lp_at (lu : FileDisc.uline) (f : nat -> bv 8) (k len : nat) :
  (exists nm : list (bv 8), lu = LCat nm) -> UkSh.ush_line_at lu f k len ->
  UkShRedirBody.ushs_lp_cat (FileDisc.uline_ws lu) (fun j : nat => f (k + j)%nat) 0%nat len.
Proof using .
  intros [nm ->] (Hok & Hlen & Hby). exists nm. split; [reflexivity |].
  split_and!; [exact Hok | exact Hlen |]. intros j Hj. rewrite Nat.add_0_l. exact (Hby j Hj).
Qed.

Lemma ucat_Dc_le : (68 <= 68 + UkSh.ush_Dpipe)%nat.
Proof using . lia. Qed.

Definition mod_cat : shape_mod :=
  {| sm_D := fun l => exists nm : list (bv 8), l = LCat nm; sm_Lp := UkShRedirBody.ushs_lp_cat;
     sm_head := HeadCA; sm_Dc := 68%nat; sm_Dc_le := ucat_Dc_le; sm_lp0 := ucat_lp0;
     sm_lp_at := ucat_lp_at |}.

Section UShUModCat.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  (* NO [ghost_varG Σ Z] BINDER ([UShRound]'s header): the redirect child's
     pins name [Xv6Cameras.offbox_offG] *)
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context `{HfifR : !UkFileIface.fifRegG Σ}.

  Context (ug : union_gn) (r : file_names).
  Local Notation gf := (ugn_file ug).
  Context (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl gf)) r).
  Context (s0 : fstate).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ _) = ucl ug).
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ _) = file_taint (fgn_cl gf)).
  (* the era credential at the union IS the era's wild token ([union_ifc]),
     and the reader-side one is the open premise (seccomp design 10.12) *)
  Context (Hwild : @riscv_wild Σ (@riscv_fixedGS Σ _) = usecc_tok ug).
  Context (Hrdw : ush_rdwild_of_shape ug).
  (* THE RECORD'S SYNC-HOOK FAMILY IS THE UNION'S (sync SY3-A4): the seam
     through which /sync's lend carries the hook sh mints *)
  Context (Hhk : @riscv_sync_hook Σ (@riscv_fixedGS Σ _) = union_hk file_pred (fgn_cl gf)).

  Local Notation T := (file_taint (fgn_cl gf)).
  Local Notation FI := (union_link_inst_at ug s0).
  Local Notation PA := (union_params_at ug s0).

  (* the pipeline's two shapes: parameters until C9f2 names them *)
  Context (PT : list (bv 8) -> nat -> iProp Σ) (PD : list (bv 8) -> iProp Σ).

  Local Notation Wcl := (uWcl ug s0).
  Local Notation Wcf := (uWcf ug r s0).
  Local Notation Wcu := (uWcu ug r s0 PT PD).
  Local Notation Wbu := (uWbf ug r s0).
  Local Notation PRE := (ush_pre_at ug r s0).
  Local Notation DONE := (ush_done_at ug r s0).

  #[local] Instance usr_T_pers0 : Persistent T | 0.
  Proof using . rewrite /file_taint /echo_taint. apply _. Qed.
  #[local] Instance usr_links_pers0 : Persistent (union_links ug) | 0
    := union_links_persistent ug.

  Local Notation uHktaint' := (UShURoundDefs.uHktaint ug Hkill).
  Local Notation uWcu_taint' := (UShURoundDefs.uWcu_taint ug r s0 PT PD).

  (* ---- THE EXEC SUPPLY: [exec /cat] at the union's cat entry ---- *)
  Lemma ucat_exec_sup (I : list (bv 8)) (nm : list (bv 8)) (s : dst) (v' : era_pins)
      (cs' : list nat) (jo : option Z) :
    FileDisc.uname nm ->
    ul I = LCat nm ->
    upre_tie cs' s0 I (dst_content s) -> (0 < nlines I)%nat ->
    ⊢ udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShCatPay.sh_cat_slot T -∗
      file_cons_cred (fgn_cl gf) r jo -∗
      era_pin (fgn_echo gf) (S gen_id) v' -∗ cs_lb v' cs' -∗
      f_typed (fgn_cl gf) s -∗
      UkShEcho.sh_exec_sup_echo_at (SG := uexecSG_xv6)
        (ghost_varG0 := offbox_offG)
        ucat_rows (ucat_ws nm)
        (fun _ : Z => UkShFork.ushf_wq Wcu I)
        (Wcl I 3%nat ∗ (fown r s ∗ urpos ug r I)).
  Proof using Heq Hkill Hcons HfifR.
    intros Hu Hul Htie Hpos. pose proof Htie as [Hlen Hcon].
    assert (Hnp : uline_nopipe (ul I)) by (rewrite Hul; exact (uline_nopipe_cat nm)).
    iIntros "#Hdep #Hslot #Hmade #Hpin' #Hcs' #Hty".
    iPoseProof "Hslot" as "(#Hinv & #Hcl & #Hgen)".
    iAssert (□ (T -∗ UkShFork.ushf_wq Wcu I))%I as "#HQt".
    { iIntros "!> #HT". rewrite /UkShFork.ushf_wq.
      iApply (uWcu_taint' I 0%nat v' with "Hpin' HT"). }
    iAssert (□ (app_taint -∗ UkShFork.ushf_wq Wcu I))%I as "#Hkt".
    { iIntros "!> #Hk". iApply "HQt". iApply uHktaint'. iExact "Hk". }
    iAssert (∀ sts, image_entry_taint T sts ProcDefs.secc_all
               (fun _ : Z => UkShFork.ushf_wq Wcu I) uslot)%I as "#Hgen'".
    { iIntros (sts). iApply image_entry_taint_intro. iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! (UkShFork.ushf_wq Wcu I) W' with "HT Hmp Hkt"). }
    iApply (UShExecPin.sh_exec_sup_x_of_entry (ghost_varG0 := offbox_offG)
              ucat_rows (ucat_ws nm) UShCatPay.cat_pl FsCatPin.era0_cat_pins
              [FsImg.ROOTINO; FsCatPin.CAT_INO] FsCatPin.CAT_INO ElfUser.cat_elf T
              (UkShFork.ushf_wq Wcu I) (Wcl I 3%nat ∗ (fown r s ∗ urpos ug r I))%I
              (ucat_ws_exec_ok nm Hu) (ucat_ws_head nm) UShCat.cat_elf_loadable
              UShCatPay.sh_cat_pin_resolves with "[] Hkt [Hslot]");
      [| iApply (UShExecPin.sh_pin_slot_cat with "Hslot")].
    iIntros "!>" (M sa t gb fdv chs pidv) "%Himg %Hbytes %Hflen %Hrows #Hnp0".
    rewrite /image_entry. iModIntro.
    iIntros (na alen afun W') "%Hok %Hcwd0 %Hlzf %Hscw %Hch0 %Hpid0 %Hargs Hmp
                               (Hc & Hd & Hup)".
    (* ---- the lend, OPENED into the round's cursor ---- *)
    rewrite {1}/uWcl /lk_lcred.
    iDestruct "Hc" as (v) "[#Hpin Hc]".
    cbn [lk_pin lk_lpr union_link_inst_at gen_link_inst gwc_lpr].
    rewrite /gwc_blk.
    iDestruct "Hc" as "[Hc | #HT]"; last first.
    { iApply ("Hgen'" $! (UexecSlot.uvis_fd W') W' with "HT [//] [%] Hmp"); exact Hscw. }
    iDestruct "Hc" as (ps cs sw P) "(%Hw & Htn & #Hps & #Hcs & #HE & #HW & _)".
    iAssert (⌜sw = s0⌝)%I as %->.
    { cbn [gW union_params_at]. rewrite /f0w_at. iDestruct "HW" as "[_ %Hs]". done. }
    iDestruct (era_pin_agree (fgn_echo gf) (S gen_id) v v' with "Hpin Hpin'")
      as %<-.
    pose proof Hw as [(Hpin0 & Hr & Hn & HP) Htail].
    iDestruct (ucs_lb_agree_len v cs cs' ltac:(lia) with "Hcs Hcs'") as %<-.
    destruct Hrows as ([wr0 Hr0] & [rb1 Hr1] & [rb2 Hr2]).
    (* the content's C-int bound, off the claim's typing of it *)
    iAssert (⌜forall (i : Z) (bs : list (bv 8)), s !! nm = Some (i, bs) ->
               (Z.of_nat (length bs) < 2 ^ 31)%Z⌝)%I as %Hshort.
    { iIntros (i bs Hs).
      iDestruct (f_typed_lookup (fgn_cl gf) s nm i bs Hs with "Hty") as (ls0) "[_ %Hbt]".
      iPureIntro. pose proof (FileDeltas.f_bytes_typed_short _ nm bs Hbt) as Hb.
      unfold EchoDisc.line_max in Hb. lia. }
    iPoseProof (ucat_image_entry (PS := uprogSG_free)
                  ug Hcons nm (ucat_ws nm) M sa t gb fdv
                  FsImg.ROOTINO chs pidv v ps cs s0 I P r
                  (1/2)%Qp s rb1 rb2 jo
                  (fun _ : Z => UkShFork.ushf_wq Wcu I) (ftkt r s ∗ urpos ug r I)%I
                  (fun _ _ => eq_refl) Heq Hw Hu Hul (eq_sym Hcon) Hshort
                  (ucat_ws_exec_ok nm Hu) Himg Hbytes Hflen
                  (ucat_ws_len nm) (ucat_ws_alen nm) (ucat_ws_fname nm) eq_refl
                  Hr1 Hr2
                  with "[] [] [] HQt Hmade Hinv Hpin Hnp0 Hdep") as "#He".
    { iIntros "!> Hk". iApply uHktaint'. iExact "Hk". }
    { iIntros "!> HT". rewrite Hkill. iExact "HT". }
    { (* WHAT cat PRODUCES, AND THE TICKET, PAY THE ROUND *)
      iIntros "!>" (a) "%Ha Hpost Hdq [Htk Hup]". rewrite /UkShFork.ushf_wq.
      iApply (uWcu_of ug r s0 PT PD I 0%nat).
      iAssert (fown r s) with "[Hdq Htk]" as "Hown".
      { rewrite /fown /fdeed /FileOpen.fdq. iFrame "Hdq Htk". }
      assert (Hc' : dst_content s = lm_step U (ust cs s0 I) (ul I) (lm_dec U a))
        by (rewrite Hul (ustep_id_cat _ nm); exact Hcon).
      apply elem_of_cons in Ha as [-> | Ha]; [| apply list_elem_of_singleton in Ha as ->].
      - iApply (uWcf0_of_posts_alt ug r s0 I (ualt_code (UR RCRan)) v v cs s
                  (ulm_aprs_R I RCRan Hnp ltac:(rewrite Hul; exact Logic.I) eq_refl)
                  ltac:(rewrite Hul; reflexivity) ltac:(by vm_compute) Hlen Hpos Hc' with "[] Hpost Hown Hup Hty Hpin Hcs").
        cbn [lk_pin union_link_inst_at gen_link_inst]. iExact "Hpin".
      - iApply (uWcf0_of_posts_alt ug r s0 I (ualt_code (UR RCNoOpen)) v v cs s
                  (ulm_aprs_R I RCNoOpen Hnp ltac:(rewrite Hul; exact Logic.I) eq_refl)
                  ltac:(rewrite Hul; reflexivity) ltac:(by vm_compute) Hlen Hpos Hc' with "[] Hpost Hown Hup Hty Hpin Hcs").
        cbn [lk_pin union_link_inst_at gen_link_inst]. iExact "Hpin". }
    rewrite /image_entry.
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] [%] Hmp
                                          [Htn Hd Hup]");
      [ exact Hok | exact Hcwd0 | exact Hlzf | exact Hscw | exact Hch0 | exact Hpid0
      | exact Hargs | ].
    rewrite /fown /fdeed /FileOpen.fdq.
    iDestruct "Hd" as "[Hdq Htk]". iFrame "Hdq Htk Hup".
    rewrite /cons_cur. iFrame "Htn Hps Hcs HE HW".
  Qed.

  (* ---- THE OUT-OF-MEMORY DIAGNOSTIC WITH THE DEED OPENED (the cat and
          redirect children open the lend before the parse) ---- *)
  Lemma ur_fupd_mwp (e : expr riscv_lang) : (|={⊤}=> mWP e) ⊢ mWP e.
  Proof using . rewrite /wp_triv. iIntros "H". iApply fupd_wp. iExact "H". Qed.

  (* THE ROUND POSITION BACK TOGETHER: the half a call returns and the
     witness quarter the round kept agree, and the era's pin bounds them *)
  Lemma urpos_of_halves (I : list (bv 8)) (vf : file_era) (n n' : nat) :
    (n' <= length (fe_base vf) + nlines I)%nat ->
    file_era_pin gf (S gen_id) vf -∗ fpos r n -∗ fposq r n' -∗
    run_reg (fgn_cl gf) (S gen_id) (fn_pos r) (fn_deed r) -∗ urpos ug r I.
  Proof using .
    intros Hle. iIntros "#Hp [%Hr H1] [_ H2] #Hrr".
    iDestruct (fposf_agree with "H1 H2") as %->.
    iExists vf, n'. iFrame "Hp Hrr". rewrite /fposh /fpos /fposq.
    iSplitL; [| iPureIntro; exact Hle].
    iSplitL "H1"; (iSplitR; [iPureIntro; exact Hr |]); [iExact "H1" | iExact "H2"].
  Qed.

  (* an exec-failure law read at a stronger hold and a weaker residue *)
  Lemma uexecfail_law_at_conv (dg : list (bv 8)) (n : nat)
      (Cr Cr2 Cd Cd' : iProp Σ) :
    UkShDiag.ush_execfail_law_at (PS := uprogSG_free)
      (ghost_varG0 := offbox_offG) dg n Cr Cd -∗
    □ (Cr2 -∗ Cr) -∗ □ (Cd -∗ Cd') -∗
    UkShDiag.ush_execfail_law_at (PS := uprogSG_free)
      (ghost_varG0 := offbox_offG) dg n Cr2 Cd'.
  Proof using .
    iIntros "#Hl #Hc #Hw". rewrite /UkShDiag.ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd Hh". iDestruct ("Hc" with "Hh") as "Hh".
    iDestruct ("Hl" $! N l with "[%] Hh") as (Pf) "(H0 & #Hs & #He)";
      [exact Hfd |].
    iExists Pf. iFrame "H0 Hs". iIntros "!> Hp". iApply "Hw". iApply "He".
    iExact "Hp".
  Qed.

  (* ...at any carried position [X] that reads back as the round's *)
  Lemma uoom_law_deed (I : list (bv 8)) (cs : list nat) (s : dst) (v' : era_pins)
      (X : iProp Σ) :
    uwild (ul I) = false -> upre_tie cs s0 I (dst_content s) -> (0 < nlines I)%nat ->
    ⊢ union_links ug -∗ f_typed (fgn_cl gf) s -∗
      era_pin (fgn_echo gf) (S gen_id) v' -∗ cs_lb v' cs -∗
      □ (X -∗ urpos ug r I) -∗
      UkShDiag.ush_execfail_law_at (PS := uprogSG_free) (ghost_varG0 := offbox_offG)
        alt_oom 14 (Wcl I 3%nat ∗ (fown r s ∗ X)) (Wcu I 0%nat).
  Proof using .
    intros Hnw [Hlen Hc] Hpos. iIntros "#Hlk #Hty #Hpin' #Hcs #HX".
    iPoseProof (UShPanic.ush_diag_law_hold_at_alt (PS := uprogSG_free)
                  (ghost_varG0 := offbox_offG) FI (fown r s ∗ X) I uoom
                  with "[] [] []") as "#Hx".
    { iLeft. iPureIntro. rewrite ufi_wild Hnw. discriminate. }
    { iApply ufi_rnd_free. intros Hq. vm_compute in Hq. discriminate Hq. }
    { cbn [lk_links union_link_inst_at gen_link_inst]. iExact "Hlk". }
    assert (Hab : lk_ab FI I uoom = alt_oom).
    { change (lk_ab FI I uoom) with (lm_ab U K I uoom). exact (ulm_ab_oom I). }
    assert (Hn : (length alt_oom - 2 = 14)%nat) by (vm_compute; reflexivity).
    iEval (rewrite Hab Hn) in "Hx".
    rewrite /UkShDiag.ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd Hc".
    iDestruct ("Hx" $! N l with "[%] Hc") as (Pf) "(H0 & #Hs & #He)"; [exact Hfd |].
    iExists Pf. iFrame "H0 Hs". iIntros "!> Hp".
    iDestruct ("He" with "Hp") as (v) "(#Hp & Hblk & Hd & Hup)".
    iDestruct ("HX" with "Hup") as "Hup".
    iApply (uWcu_of ug r s0 PT PD I 0%nat).
    iApply (uWcf0_of_post_alt ug r s0 I uoom v v' cs s (ulm_apr_oom I) Hnw ltac:(by vm_compute) Hlen Hpos
              ltac:(rewrite ulm_step_oom; exact Hc) with "Hp Hblk Hd Hup Hty Hpin' Hcs").
  Qed.

  (* ---- THE cat CHILD'S LAW ---- *)
  Lemma uHchild_cat :
    ⊢ union_links ug -∗
      udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShCatPay.sh_cat_slot T -∗
      (∃ jo : option Z, file_cons_cred (fgn_cl gf) r jo) -∗
      UkShFork.ushf_child_law_at (PS := uprogSG_free) (SG := uexecSG_xv6)
        (ghost_varG0 := offbox_offG) T Wcu UkShRedirBody.ushs_lp_cat 68.
  Proof using Heq Hkill Hcons HfifR.
    iIntros "#Hlk #Hdep #Hslot #Hmade". iDestruct "Hmade" as (jo) "#Hmade".
    iPoseProof "Hslot" as "(#Hinv & _ & #Hgen)".
    rewrite /UkShFork.ushf_child_law_at.
    iIntros "!>" (N' h m dw dv sa len ws gb sz ld n I)
      "%Hpeq %Hs1 %Hline %Hlws %Hfok %Hsa %Hs64 %Hs38 %Hszlo %Hszal %Hszok
       %Hrows #Hcode #Hpcode #Hpro #Hjt Hstr Hwsp Hsy Hstd Hcwd Hch _ HM Hcr
       Hrun".
    iDestruct (UkSh.ush_std_ustd with "Hstd") as "Hstd".
    iDestruct (UserChildren.uch_any_of with "Hch") as "Hch".
    destruct Hline as (nm & -> & Hlat).
    pose proof (proj1 Hlat) as Hu.
    (* ---- the line, off the fork's words ---- *)
    assert (Hpos : (0 < nlines I)%nat).
    { destruct (nlines I) as [| k] eqn:Hn; [| lia]. exfalso.
      rewrite /last_ws in Hlws. rewrite /nlines in Hn.
      apply nil_length_inv in Hn. rewrite Hn in Hlws. cbn in Hlws.
      revert Hlws. vm_compute. discriminate. }
    assert (Hfl : fline I = LCat nm).
    { apply (FileDisc.fline_ok_cat_words (UkSh.ush_lastbody I) nm Hfok).
      rewrite -(last_ws_lastbody I). symmetry. exact Hlws. }
    assert (Hul : ul I = LCat nm).
    { rewrite ul_lastbody. apply uline_of_u_eq; [exact Hfl | discriminate]. }
    assert (Hnp : uline_nopipe (ul I)) by (rewrite Hul; exact (uline_nopipe_cat nm)).
    (* ---- the lend, opened ---- *)
    iDestruct (uWcu_3_nw ug r s0 PT PD I ltac:(rewrite Hul; reflexivity) with "Hcr")
      as "Hcr".
    rewrite uWcf_S3. iDestruct "Hcr" as "[Hc [Hpre #Hwit]]".
    iAssert (∃ v0 : era_pins, era_pin (fgn_echo gf) (S gen_id) v0)%I
      as (v0) "#Hpin0".
    { rewrite /uWcl /lk_lcred.
      iDestruct "Hc" as (v0) "[#Hp _]". iExists v0.
      cbn [lk_pin union_link_inst_at gen_link_inst]. iExact "Hp". }
    iAssert (□ (app_taint -∗ UkShFork.ushf_wq Wcu I))%I as "#Hkillq".
    { iIntros "!> #Hk". rewrite /UkShFork.ushf_wq.
      iApply (uWcu_taint' I 0%nat v0 with "Hpin0"). iApply uHktaint'.
      iExact "Hk". }
    iAssert (□ (∀ W : UexecSlot.uvis,
                  T -∗ ChildTok.my_pay (UexecSlot.uvis_gen W) (ukn_pay N') -∗
                  UexecRet.uslot (SG := uexecSG_xv6) W))%I
      as "#Hgenw".
    { iIntros "!>" (W) "#HT' #Hmy". rewrite Hpeq.
      iApply ("Hgen" $! (UkShFork.ushf_wq Wcu I) W with "HT' Hmy Hkillq"). }
    rewrite {1}/ush_deed_at. iDestruct "Hpre" as "[Hpre | #HT]"; last first.
    { iApply (urun_gen (PS := uprogSG_free) (SG := uexecSG_xv6)
                (ghost_varG0 := offbox_offG) N' T h m
                (mword_of_int 0x99c) _ ltac:(vm_compute; reflexivity)
                with "Hgenw HT Hrun"). }
    iDestruct "Hpre" as (cs s v') "(Hd & %Htie & #Hty & #Hpin' & #Hcs & %Hnw & Hup)".
    pose proof Htie as [Hlen Hcon].
    (* ---- THE WALK, at 8 more steps of budget than it needs ---- *)
    assert (Hbud : (68 + (8 + (UkShDiag.ush_Dg + n)))%nat
                   = (60 + (8 + (UkShDiag.ush_Dg + (n + 8))))%nat) by lia.
    rewrite Hbud.
    iApply (UkShEcho.wp_kshm_child_x_holds (PS := uprogSG_free)
              (SG := uexecSG_xv6) (ghost_varG0 := offbox_offG)
              (fun k H => H) ucat_rows (ucat_ws nm) FileDisc.alt_execcat
              (fun _ : Z => UkShFork.ushf_wq Wcu I)
              (Wcl I 3%nat ∗ (fown r s ∗ urpos ug r I))%I
              (∃ v : era_pins,
                 lk_pin FI (S gen_id) v
                 ∗ lk_post FI (S gen_id) v I (ualt_code (UR RCExec))
                 ∗ (fown r s ∗ urpos ug r I))%I
              N' (ukn_const_of_eq N' _ Hpeq (fun _ _ => eq_refl))
              h m dw dv sa len gb sz ld (n + 8)%nat
              Hpeq Hs1 (ucat_xline nm gb len Hlat) (ucat_execfail_bytes nm)
              Hsa Hs64 Hs38 Hszlo Hszal Hszok Hrows (proj2 (proj2 Hrows))
              with "Hcode [] [] [] [] Hpcode Hpro Hjt Hstr Hwsp Hsy Hstd Hcwd
                    Hch HM [Hc Hd Hup] Hrun").
    - (* exec /cat *)
      iApply (ucat_exec_sup I nm s v' cs jo Hu Hul Htie Hpos
                with "Hdep Hslot Hmade Hpin' Hcs Hty").
    - (* the parse ran out of memory: "out of memory", the deed as found *)
      pose proof (ukn_const_of_eq N' _ Hpeq (fun _ _ => eq_refl)) as Hcst.
      iApply (UkShEcho.ushp_oom_of_diag (PS := uprogSG_free)
                (ghost_varG0 := offbox_offG) N' (Wcl I 3%nat ∗ (fown r s ∗ urpos ug r I))
                (Wcu I 0%nat) ld
                (18 + (8 + (UkShDiag.ush_Dg + (n + 8))))%nat ltac:(lia)
                (proj2 (proj2 Hrows)) with "[] [] Hcode []").
      + iApply (uoom_law_deed I cs s v' (urpos ug r I) ltac:(rewrite Hul; reflexivity)
                  Htie Hpos with "Hlk Hty Hpin' Hcs []"). iIntros "!> $".
      + iIntros "!> H". rewrite Hpeq /UkShFork.ushf_wq. iExact "H".
      + iApply (UkSh.ush_jtab_ro with "Hjt").
    - (* exec failed: the diagnostic at [RCExec] *)
      iPoseProof (UShPanic.ush_diag_law_hold_at_alt (PS := uprogSG_free)
                    (ghost_varG0 := offbox_offG) FI (fown r s ∗ urpos ug r I) I
                    (ualt_code (UR RCExec)) with "[] [] []") as "#Hx".
      { iLeft. iPureIntro. rewrite ufi_wild Hnw. discriminate. }
      { iApply ufi_rnd_free. intros Hq. vm_compute in Hq. discriminate Hq. }
      { cbn [lk_links union_link_inst_at gen_link_inst]. iExact "Hlk". }
      assert (Hab : lk_ab FI I (ualt_code (UR RCExec)) = FileDisc.alt_execcat).
      { change (lk_ab FI I (ualt_code (UR RCExec))) with (lm_ab U K I (ualt_code (UR RCExec))).
        rewrite (ulm_ab_R I RCExec Hnp ltac:(rewrite Hul; exact Logic.I) eq_refl) Hul.
        reflexivity. }
      rewrite Hab. iExact "Hx".
    - iIntros "!> H". rewrite /UkShFork.ushf_wq.
      iApply (uWcu_of ug r s0 PT PD I 0%nat).
      iDestruct "H" as (v) "(#Hp & Hblk & Hd & Hup)".
      iApply (uWcf0_of_post_alt ug r s0 I (ualt_code (UR RCExec)) v v' cs s
                (ulm_apr_R I RCExec Hnp ltac:(rewrite Hul; exact Logic.I) eq_refl eq_refl)
                ltac:(rewrite Hul; reflexivity) ltac:(by vm_compute) Hlen Hpos ltac:(rewrite ulm_step_R Hul; exact Hcon)
                with "Hp Hblk Hd Hup Hty Hpin' Hcs").
    - iFrame "Hc Hd Hup".
  Qed.

  (* THE BODY LAW at the cat line, from its child law: the generic
     wrapper's instance *)
  Lemma ucat_body_law (N : uk_names Σ) `{Hp : !ukn_const N} (γp : gname)
      (Pm : list (bv 8) -> iProp Σ) (sz : Z) :
    8344 <= sz -> UserPtTree.pgroundup sz = sz -> usz_ok (sz + 65536) ->
    UkShFork.ushf_kill_law Wcu -∗
    UkShFork.ushf_child_law_at (PS := uprogSG_free) (SG := uexecSG_xv6)
      (ghost_varG0 := offbox_offG) T Wcu UkShRedirBody.ushs_lp_cat 68 -∗
    UkShDiag.ush_panic_law (PS := uprogSG_free) Wcu Wbu -∗
    UkShFork.ushf_body_law (PS := uprogSG_free) (SG := uexecSG_xv6)
      (ghost_varG0 := offbox_offG) N γp T Wcu Wbu Pm (sm_D mod_cat) sz.
  Proof using .
    intros Hszlo Hszal Hszok. iIntros "#Hkl #Hchl #Hplaw".
    iApply (UkShShape.ushf_body_law_of_mod (PS := uprogSG_free) (SG := uexecSG_xv6)
              (ghost_varG0 := offbox_offG) N γp T Wcu Wbu Pm (fun k H => H)
              mod_cat sz Hszlo Hszal Hszok with "Hkl [] Hplaw").
    rewrite /UkShShape.sm_law. cbn [sm_Lp sm_Dc mod_cat]. iExact "Hchl".
  Qed.

End UShUModCat.
