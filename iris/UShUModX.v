(* ===================================================================== *)
(*  UShUModX.v -- THE WHOLE-LEND CHILD LAWS' SHARED PROLOGUE              *)
(*  (shape-modules stage 1b, S5; design: claude-notes/design/            *)
(*  shape-modules.md section 3, "The child laws stay hand-written").     *)
(*                                                                        *)
(*  [ushf_child_law_of_x]: the child law at the union's credential for   *)
(*  an EXEC line whose lend goes to the program whole, from the shape's   *)
(*  pure line facts and ONE persistent per-shape law: at the line, the   *)
(*  lend opens into the taint or into the walk's [Cr] with the supply,   *)
(*  the two diagnostic laws from [Cr] to [Cd], and the exit paying the   *)
(*  round from [Cd].  The prologue it owns: the line fact off the fork's *)
(*  words, the era pin off the lend (the taint's payload), the view off  *)
(*  the table, the budget, the walk at the named view and its four arms. *)
(*  Instances: [UShUModSync.uHchild_sync], [UShUModSecc.uHchild_secc].   *)
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
Require Import UkRun.
Require Import UexecExecInst.
Require Import WpUart.
Require Import AppCfg.
Require Import LineWords.
Require Import EchoOut.
Require Import FileDisc.
Require Import FileState.
Require Import AppEcho.
Require Import AppFile.
Require Import FileOut.
Require Import FsAbsDefs.
Require Import UkShDiagAt.
Require Import UkSh.
Require Import UkShDiag.
Require Import UkShEcho.
Require Import UkShFork.
Require Import LinkRec.
Require Import GenLinksLine.
Require Import PipeOut.
Require Import UnionDisc.
Require Import UnionDiscDec.
Require Import UnionOut.
Require Import UnionLinks.
Require Import UnionLinkInstAt.
Require Import UShURoundDefs.
Require UkFileIface.
Require UShExecPin.
Require Import CtxIdDefs.
Require Import UShUModBase.       (* the pure preamble, shared with the shape modules *)
Local Open Scope Z_scope.
Import Defs.

Local Notation U := ulmG.
Local Notation K := ulmG_hooks.

Section UShUModX.
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

  (* THE SHARED PROLOGUE: the per-shape law [Hx] is asked at the line [l]
     the fork's words name, with the taint's payload in hand; it answers
     the taint, or the walk's [Cr] with what the walk's four arms need *)
  Lemma ushf_child_law_of_x
      (Lp : list (list (bv 8)) -> (nat -> bv 8) -> nat -> nat -> Prop)
      (D : FileDisc.uline -> Prop) (pins : aview -> Prop) :
    (forall ws g len, Lp ws g 0%nat len ->
       exists l, D l /\ ws = FileDisc.uline_ws l /\ UkSh.ush_line_at l g 0%nat len) ->
    (forall l g len, D l -> UkSh.ush_line_at l g 0%nat len ->
       UkShEcho.ush_xline_is (FileDisc.uline_ws l) g 0%nat len) ->
    (forall l b, D l -> FileDisc.uline_ok l -> FileDisc.fline_ok b ->
       wl_words b = FileDisc.uline_ws l -> uline_of_u b = l) ->
    ⊢ □ (∀ (I : list (bv 8)) (l : FileDisc.uline),
           ⌜D l⌝ -∗ ⌜FileDisc.uline_ok l⌝ -∗ ⌜ul I = l⌝ -∗ ⌜(0 < nlines I)%nat⌝ -∗
           □ (app_taint -∗ UkShFork.ushf_wq Wcu I) -∗ Wcu I 3%nat -∗
           T ∨ ∃ (Cr Cd : iProp Σ) (dg : list (bv 8)),
             ⌜UkShDiagAt.ush_execfail_bytes dg (FileDisc.uline_ws l !!! 0%nat)⌝ ∗ Cr ∗
             □ (∀ vw, ⌜ush_view_ok vw⌝ -∗
                  UkShEcho.sh_exec_sup_echo_at_v (SG := uexecSG_xv6)
                    (ghost_varG0 := offbox_offG) ucat_rows (FileDisc.uline_ws l)
                    (fun _ : Z => UkShFork.ushf_wq Wcu I) Cr vw) ∗
             UkShDiag.ush_execfail_law_at (PS := uprogSG_free)
               (ghost_varG0 := offbox_offG) FileDisc.alt_oom 14 Cr Cd ∗
             UkShDiag.ush_execfail_law_at (PS := uprogSG_free)
               (ghost_varG0 := offbox_offG) dg
               (13 + length (FileDisc.uline_ws l !!! 0%nat))%nat Cr Cd ∗
             □ (Cd -∗ UkShFork.ushf_wq Wcu I)) -∗
      UShExecPin.sh_pin_slot pins T -∗
      UkShFork.ushf_child_law_at (PS := uprogSG_free) (SG := uexecSG_xv6)
        (ghost_varG0 := offbox_offG) T Wcu Lp 68.
  Proof using Hkill.
    intros HLp Hxl Hul0. iIntros "#Hx #Hslot".
    iPoseProof "Hslot" as "(_ & _ & #Hgen)".
    rewrite /UkShFork.ushf_child_law_at.
    iIntros "!>" (N' h m dw dv sa len ws gb sz ld n I)
      "%Hpeq %Hs1 %Hline %Hlws %Hfok %Hsa %Hs64 %Hs38 %Hszlo %Hszal %Hszok
       %Hrows #Hcode #Hpcode #Hpro #Hjt Hstr Hwsp Hsy Hstd Hcwd Hch _ HM Hcr
       Hrun".
    iDestruct (UserChildren.uch_any_of with "Hch") as "Hch".
    destruct (HLp _ _ _ Hline) as (l & HDl & -> & Hlat).
    pose proof (Hxl l gb len HDl Hlat) as Hxline.
    (* ---- the line, off the fork's words ---- *)
    assert (Hpos : (0 < nlines I)%nat).
    { destruct (nlines I) as [| k] eqn:Hn; [| lia]. exfalso.
      apply nil_length_inv in Hn. rewrite /last_ws Hn /= in Hlws.
      destruct Hxline as [(_ & Hl0 & _) _]. rewrite Hlws in Hl0. cbn in Hl0. lia. }
    assert (Hul : ul I = l).
    { rewrite ul_lastbody. apply (Hul0 l _ HDl (proj1 Hlat) Hfok).
      rewrite -(last_ws_lastbody I). symmetry. exact Hlws. }
    (* the era's pin, off the lend, for the taint's payload *)
    iAssert (∃ v0 : era_pins, era_pin (fgn_echo gf) (S gen_id) v0)%I
      as (v0) "#Hpin0".
    { iDestruct (uWcu_3 ug r s0 PT PD I with "Hcr") as "[Hc | (_ & _ & %v0 & #Hp & _)]";
        [| by iExists v0].
      rewrite uWcf_S3 /uWcl /lk_lcred. iDestruct "Hc" as "[Hc _]".
      iDestruct "Hc" as (v0) "[#Hp _]". iExists v0.
      cbn [lk_pin union_link_inst_at gen_link_inst]. iExact "Hp". }
    iAssert (□ (app_taint -∗ UkShFork.ushf_wq Wcu I))%I as "#Hkillq".
    { iIntros "!> #Hk". rewrite /UkShFork.ushf_wq.
      iApply (uWcu_taint' I 0%nat v0 with "Hpin0"). iApply uHktaint'. iExact "Hk". }
    iAssert (□ (∀ W : UexecSlot.uvis,
                  T -∗ ChildTok.my_pay (UexecSlot.uvis_gen W) (ukn_pay N') -∗
                  UexecRet.uslot (SG := uexecSG_xv6) W))%I as "#Hgenw".
    { iIntros "!>" (W) "#HT' #Hmy". rewrite Hpeq.
      iApply ("Hgen" $! (UkShFork.ushf_wq Wcu I) W with "HT' Hmy Hkillq"). }
    rewrite /UkSh.ush_std /UserFd.ustd_ok.
    iDestruct "Hstd" as (vw) "[[%Hvok | #HT] Hstd]";
      [| iApply (urun_gen (PS := uprogSG_free) (SG := uexecSG_xv6) (ghost_varG0 := offbox_offG)
               N' T h m (mword_of_int 0x99c) _ ltac:(vm_compute; reflexivity) with "Hgenw HT Hrun")].
    iDestruct ("Hx" $! I l HDl (proj1 Hlat) Hul Hpos with "Hkillq Hcr")
      as "[#HT | (%Cr & %Cd & %dg & %Hdg & Hcr & #Hsup & #Hoom & #Hxf & #Hpay)]";
      [iApply (urun_gen (PS := uprogSG_free) (SG := uexecSG_xv6) (ghost_varG0 := offbox_offG)
               N' T h m (mword_of_int 0x99c) _ ltac:(vm_compute; reflexivity) with "Hgenw HT Hrun") |].
    (* ---- THE WALK, at 8 more steps of budget than it needs ---- *)
    assert (Hbud : (68 + (8 + (UkShDiag.ush_Dg + n)))%nat
                   = (60 + (8 + (UkShDiag.ush_Dg + (n + 8))))%nat) by lia.
    rewrite Hbud.
    iApply (UkShEcho.wp_kshm_child_x_v_holds (PS := uprogSG_free)
              (SG := uexecSG_xv6) (ghost_varG0 := offbox_offG)
              (fun k H => H) ucat_rows (FileDisc.uline_ws l) dg
              (fun _ : Z => UkShFork.ushf_wq Wcu I) Cr Cd
              N' (ukn_const_of_eq N' _ Hpeq (fun _ _ => eq_refl))
              h m dw dv sa len gb sz ld vw (n + 8)%nat
              Hpeq Hs1 Hxline Hdg
              Hsa Hs64 Hs38 Hszlo Hszal Hszok Hrows (proj2 (proj2 Hrows))
              with "Hcode [] [] [] [] Hpcode Hpro Hjt Hstr Hwsp Hsy Hstd Hcwd
                    Hch HM Hcr Hrun").
    - iApply ("Hsup" $! vw Hvok).
    - (* the parse ran out of memory: "out of memory" *)
      pose proof (ukn_const_of_eq N' _ Hpeq (fun _ _ => eq_refl)) as Hcst.
      iApply (UkShEcho.ushp_oom_of_diag (PS := uprogSG_free)
                (ghost_varG0 := offbox_offG) N' Cr Cd ld
                (18 + (8 + (UkShDiag.ush_Dg + (n + 8))))%nat ltac:(lia)
                (proj2 (proj2 Hrows)) with "Hoom [] Hcode []").
      + iIntros "!> H". rewrite Hpeq. iApply ("Hpay" with "H").
      + iApply (UkSh.ush_jtab_ro with "Hjt").
    - iExact "Hxf".
    - iIntros "!> H". iApply ("Hpay" with "H").
  Qed.

End UShUModX.
