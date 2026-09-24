(* ===================================================================== *)
(*  FileLinkInst.v -- [LinkRec.LinkRec] AT THE FILE APPLICATION.          *)
(*                                                                       *)
(*  Since app-both M2c the record is [FileLinkGen.file_link_gen], the     *)
(*  generic [GenLinksLine.gen_link_inst] at the file model's parameters, *)
(*  and the record at a named boot state (RULING H') is the same generic *)
(*  section at the witness [f0w ∗ ⌜s = s0⌝].  What this file adds is      *)
(*  what [UShRound] instantiates its two families at ([file_Wcl] /        *)
(*  [file_Wbl]), the cursor and stage records ([StageRec]) at the file    *)
(*  era, and the packing between the two readings of the record.        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import LineWords.
Require Import EchoDisc.
Require Import FileState.
Require Import FileDisc.
Require Import LineModel.
Require Import LineModelLinks.
Require Import EchoOut.
Require Import AppFile.
Require Import FileOut.
Require Import FileHooks.         (* S0 of [FileLinksLine], moved *)
Require Import LinkRec.
Require Import StageRec.   (* the cursor / stage record *)
Require Import GenLinksLine.
Require Import FileLinkGen.
Require Import RiscvPtsto.
Require Import WpUart.
Local Open Scope list_scope.

Section file_link_inst.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.

  Definition file_link_inst : LinkRec Σ := file_link_gen g.
End file_link_inst.

(* ===================================================================== *)
(*  THE [UShRound]-FACING LEMMAS.                                         *)
(*                                                                       *)
(*  Lane SKELETON's obligation table, discharged by NAME at the file      *)
(*  instance.  [Wcl]/[Wbl] below are what [UShRound.v] must instantiate  *)
(*  its two parameters at; [Wcf I p = Wcl I p ∗ sh_hold I] is then the    *)
(*  family the loop carries, and the two framed laws admit that linear    *)
(*  conjunct.                                                            *)
(* ===================================================================== *)
Section sh_round_facing.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.

  Local Notation FI := (file_link_inst g).

  (* the two families [UShRound]'s [Wcl] / [Wbl] are instantiated at *)
  Definition file_Wcl (I : list (bv 8)) (p : nat) : iProp Σ :=
    lk_lcred FI (S gen_id) I p.

  Definition file_Wbl (I : list (bv 8)) : iProp Σ :=
    (∃ v : era_pins,
       lk_pin FI (S gen_id) v ∗ lk_ban FI (S gen_id) v I 0%nat)%I.

  Global Instance file_Wcl_timeless I p : Timeless (file_Wcl I p).
  Proof using . rewrite /file_Wcl. apply lk_lcred_timeless. Qed.

  (* ---- [UShRound]'s [Hwbl] ---- *)
  Lemma file_Hwbl (I : list (bv 8)) : ⊢ file_Wcl I 3%nat -∗ file_Wcl I 0%nat.
  Proof using . rewrite /file_Wcl. iApply (lk_lcred_blk_line FI (S gen_id) I). Qed.

  (* ---- [UShRound]'s [Hwbwc] ---- *)
  Lemma file_Hwbwc (I : list (bv 8)) : ⊢ file_Wbl I -∗ file_Wcl I 0%nat.
  Proof using . rewrite /file_Wcl /file_Wbl. iApply (lk_lcred_of_ban FI (S gen_id) I). Qed.

  (* ---- [UShRound]'s [Hcltaint], AT THE TWO-PIN SHAPE ---- *)
  Lemma file_Hcltaint (I : list (bv 8)) (p : nat) (v : era_pins) :
    ⊢ era_pin (fgn_echo g) (S gen_id) v -∗
      file_taint (fgn_cl g) -∗ file_Wcl I p.
  Proof using .
    rewrite /file_Wcl. iApply (lk_lcred_taint FI (S gen_id) I p v).
  Qed.

  (* ---- [UShRound]'s [Hwc]: the read that completed a line ---- *)
  Lemma file_Hwc (I l : list (bv 8)) (v : era_pins) :
    wl_nl ∉ l ->
    ⊢ era_pin (fgn_echo g) (S gen_id) v -∗
      inp_lb v (I ++ l ++ [wl_nl]) -∗
      file_Wcl I 2%nat -∗ file_Wcl (I ++ l ++ [wl_nl]) 3%nat.
  Proof using .
    intros Hl. rewrite /file_Wcl.
    iApply (lk_lcred_read FI (S gen_id) I l v Hl).
  Qed.

  (* ---- [UShRound]'s [Hwbr]: a read past a banner-owed boundary ---- *)
  Lemma file_Hwbr (I l : list (bv 8)) (v : era_pins) :
    wl_nl ∉ l ->
    ⊢ era_pin (fgn_echo g) (S gen_id) v -∗
      lk_rres FI v (I ++ l ++ [wl_nl]) -∗
      file_Wbl I -∗ file_taint (fgn_cl g).
  Proof using .
    intros Hl. iIntros "#Hpin #Hres Hb". rewrite /file_Wbl.
    iDestruct "Hb" as (v') "[#Hpin' Hb]".
    iDestruct (lk_pin_agr FI (S gen_id) v v' with "Hpin Hpin'") as %<-.
    iApply (lk_ban_read_taint FI (S gen_id) v I l Hl with "Hb Hres").
  Qed.

  (* =================================================================== *)
  (*  THE STAGE, AT THE FILE ERA (the program stream, (c))                *)
  (*                                                                     *)
  (*  echo's instance ([StageRec.echo_stage_inst]) opens the era's lend    *)
  (*  into a bundle and names the cursor itself; the file era's is         *)
  (*  SHORTER, because the generic families already have both halves:     *)
  (*  the block family at index 0 IS the cursor and the block step IS its *)
  (*  step.                                                               *)
  (*                                                                     *)
  (*  WHAT IT IS ABOUT: the lines whose block is the LINE's own            *)
  (*  alternative, i.e. the [LEcho] ones.  At an [LEchoF] line the child   *)
  (*  writes to the FILE and the console block is the prompt; at an        *)
  (*  [LCat] line it is cat's.  [ck_lineok] is where that is said, and it  *)
  (*  is the record field the program stream added for exactly this.       *)
  (* =================================================================== *)
  Record file_stg := MkFileStg { fs_I : list (bv 8) }.

  Definition file_lineok (I : list (bv 8)) : Prop :=
    fline I = LEcho (last_ws I).

  (* the model's alternative 0 at an echo line IS echo's own output *)
  Lemma file_ralt0 : ralt_dec 0%nat = REcho 0%nat.
  Proof using . reflexivity. Qed.

  Lemma file_ralt0_ok (I : list (bv 8)) :
    file_lineok I -> ralt_ok (fline I) (ralt_dec 0%nat).
  Proof using .
    intro Hl. rewrite Hl file_ralt0. cbn [ralt_ok]. lia.
  Qed.

  Lemma file_ralt0_free : fstate_free (ralt_dec 0%nat) = true.
  Proof using . reflexivity. Qed.

  Lemma file_fab0 (I : list (bv 8)) :
    file_lineok I -> fab I 0%nat = line_alts_of (last_ws I) !!! 0%nat.
  Proof using .
    intro Hl.
    rewrite (fab_is I 0%nat (file_ralt0_ok I Hl) file_ralt0_free) Hl.
    reflexivity.
  Qed.

  Lemma file_fab0_len (I : list (bv 8)) :
    file_lineok I ->
    (length (fab I 0%nat) - 2)%nat
    = length (wl_line (drop 1 (last_ws I))).
  Proof using .
    intro Hl. rewrite (file_fab0 I Hl) (line_alts_of_0_length (last_ws I)).
    lia.
  Qed.

  (* ...and at the record's own block ([lm_ab]), which is [fab] *)
  Lemma file_lmab0 (I : list (bv 8)) :
    file_lineok I ->
    lm_ab file_lm file_hooks I 0%nat = line_alts_of (last_ws I) !!! 0%nat.
  Proof using . intro Hl. rewrite -fab_lm. exact (file_fab0 I Hl). Qed.

  Lemma file_lmab0_len (I : list (bv 8)) :
    file_lineok I ->
    (length (lm_ab file_lm file_hooks I 0%nat) - 2)%nat
    = length (wl_line (drop 1 (last_ws I))).
  Proof using . intro Hl. rewrite -fab_lm. exact (file_fab0_len I Hl). Qed.

  Lemma file_apr0 (I : list (bv 8)) :
    file_lineok I -> lm_apr file_lm file_hooks I 0%nat.
  Proof using .
    intro Hl. apply fapr_lm. rewrite /fapr.
    split_and!;
      [ exact (file_ralt0_ok I Hl) | exact file_ralt0_free | reflexivity ].
  Qed.

  Local Lemma fi_cur_tl (k : nat) (v : era_pins) (st : file_stg) (p : nat) :
    Timeless (lk_blk FI k v (fs_I st) 0%nat p).
  Proof using . apply lk_blk_tl. Qed.

  Local Lemma fi_step (k : nat) (v : era_pins) (st : file_stg)
      (ws : list (list (bv 8))) (i : nat) (b : bv 8) (Φ : iProp Σ) :
    (fline (fs_I st) = LEcho ws /\ last_ws (fs_I st) = ws) ->
    line_alts_of ws !!! 0%nat !! i = Some b ->
    ⊢ lk_pin FI k v -∗ lk_links FI -∗ lk_blk FI k v (fs_I st) 0%nat i -∗
      (lk_blk FI k v (fs_I st) 0%nat (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros [ Hln Hlast ] Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iApply (lk_blk_step FI k v (fs_I st) 0%nat i b Φ with "Hpin Hlk Hc HΦ").
    cbn [lk_ab FI file_link_gen gen_link_inst].
    rewrite (file_lmab0 (fs_I st) ltac:(rewrite /file_lineok Hlast; exact Hln)).
    rewrite Hlast. exact Hb.
  Qed.

  Definition file_cur_inst : CurRec FI :=
    MkCurRec FI file_stg
      (fun st ws => fline (fs_I st) = LEcho ws /\ last_ws (fs_I st) = ws)
      (fun ws => line_alts_of ws !!! 0%nat)
      file_lineok
      (fun k v st p => lk_blk FI k v (fs_I st) 0%nat p)
      fi_cur_tl fi_step.

  (* THE LEND, OPENED.  The lend and the block family at [0 0] are the
     same proposition, and what the block's END pays is [lk_post FI],
     which is that family at [length (lk_ab I 0) - 2]. *)
  Local Lemma fi_lend_stage (k : nat) (v : era_pins) (I : list (bv 8)) :
    file_lineok I ->
    ⊢ lk_lend FI k v I -∗
      (∃ st : file_stg,
         ⌜fline (fs_I st) = LEcho (last_ws I) /\ last_ws (fs_I st) = last_ws I⌝
         ∗ ⌜line_alts_of (last_ws I) !!! 0%nat
            = line_alts_of (last_ws I) !!! 0%nat⌝
         ∗ lk_blk FI k v (fs_I st) 0%nat 0%nat
         ∗ □ (lk_blk FI k v (fs_I st) 0%nat
                (length (wl_line (drop 1 (last_ws I)))) -∗
              lk_post FI k v I 0%nat))
      ∨ lk_T FI.
  Proof using .
    intro Hlok.
    cbn [lk_lend lk_blk lk_T FI file_link_gen gen_link_inst].
    rewrite /gwc_lend. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    iLeft. iExists (MkFileStg I). cbn [fs_I].
    iSplitR; [ iPureIntro; split; [ exact Hlok | reflexivity ] | ].
    iSplitR; [ by iPureIntro | ].
    iSplitL "Htn".
    - rewrite /gwc_blk. iLeft. iExists ps, cs, s0, P.
      cbn [lm_blkcs]. rewrite Nat.add_0_r.
      iFrame "Htn Hps Hcs HE Hf". by iPureIntro.
    - iIntros "!> Hc". rewrite /lk_post.
      cbn [lk_blk lk_ab FI file_link_gen gen_link_inst].
      rewrite (file_lmab0_len I Hlok). iExact "Hc".
  Qed.

  Local Lemma fi_apr0 (I : list (bv 8)) :
    file_lineok I -> lk_apr FI I 0%nat.
  Proof using .
    intro Hl. cbn [lk_apr FI file_link_gen gen_link_inst]. exact (file_apr0 I Hl).
  Qed.

  Definition file_stage_inst : StageRec FI :=
    MkStageRec FI file_cur_inst (fun _ => 0%nat) fi_lend_stage fi_apr0.
End sh_round_facing.

(* ===================================================================== *)
(*  THE RECORD AT A NAMED BOOT STATE (lane INIT-FILE, ruling H')          *)
(*                                                                       *)
(*  [file_link_inst] above hides the era's boot state under each family's *)
(*  own existential, so a holder of a credential knows the state is SOME  *)
(*  value and never WHICH -- and sh's round needs exactly that            *)
(*  ([UCatOut.cat_tie] is [dst_content s = cat_st cs0 s0 I]).  This is    *)
(*  the SAME generic record at the witness [f0w ∗ ⌜s = s0⌝]: one [s0]     *)
(*  shared by every field, so /init names its deed's content once and    *)
(*  reads the same name back off the banner's own credential.            *)
(* ===================================================================== *)
Section file_link_inst_at.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.
  Context (s0 : fstate).

  Definition file_link_inst_at : LinkRec Σ := file_link_gen_at g s0.

  Local Notation FIs := file_link_inst_at.

  (* ---- THE TWO FAMILIES THE ROUND INSTANTIATES, at the index ----
     [file_Wcl] / [file_Wbl] are what [UShRound] takes its [Wcl] / [Wbl]
     at; these are the same two at the record above, and they are what
     lets the round read [Wcf I p := exists s0, Wcl_at s0 I p * hold s0 I]
     with the credential and the deed at ONE state. *)
  Definition file_Wcl_at (I : list (bv 8)) (p : nat) : iProp Σ :=
    lk_lcred FIs (S gen_id) I p.

  Definition file_Wbl_at (I : list (bv 8)) : iProp Σ :=
    (∃ v : era_pins,
       lk_pin FIs (S gen_id) v ∗ lk_ban FIs (S gen_id) v I 0%nat)%I.

  Global Instance file_Wcl_at_timeless I p : Timeless (file_Wcl_at I p).
  Proof using . rewrite /file_Wcl_at. apply lk_lcred_timeless. Qed.

  Global Instance file_Wbl_at_timeless I : Timeless (file_Wbl_at I).
  Proof using .
    rewrite /file_Wbl_at. apply bi.exist_timeless; intro.
    apply bi.sep_timeless; [apply lk_pin_tl | apply lk_ban_tl].
  Qed.

  Lemma file_Wcl_at_pack (I : list (bv 8)) (p : nat) :
    file_Wcl_at I p -∗ file_Wcl g I p.
  Proof using .
    rewrite /file_Wcl_at /file_Wcl /lk_lcred.
    iIntros "H". iDestruct "H" as (v) "[#Hpin Hc]". iExists v.
    cbn [lk_pin lk_lpr file_link_inst file_link_inst_at file_link_gen
         file_link_gen_at gen_link_inst] in *.
    iFrame "Hpin". iApply (gwc_lpr_at_pack with "Hc").
  Qed.

  Lemma file_Wbl_at_pack (I : list (bv 8)) :
    file_Wbl_at I -∗ file_Wbl g I.
  Proof using .
    rewrite /file_Wbl_at /file_Wbl.
    iIntros "H". iDestruct "H" as (v) "[#Hpin Hc]". iExists v.
    cbn [lk_pin lk_ban file_link_inst file_link_inst_at file_link_gen
         file_link_gen_at gen_link_inst] in *.
    iFrame "Hpin". iApply (gwc_ban_at_pack with "Hc").
  Qed.

  (* =================================================================== *)
  (*  THE STAGE, AT THE INDEXED RECORD (the PROGRAM STREAM)               *)
  (* =================================================================== *)
  Local Lemma fi_cur_tl_at (k : nat) (v : era_pins) (st : file_stg)
      (p : nat) :
    Timeless (lk_blk FIs k v (fs_I st) 0%nat p).
  Proof using . apply lk_blk_tl. Qed.

  Local Lemma fi_step_at (k : nat) (v : era_pins) (st : file_stg)
      (ws : list (list (bv 8))) (i : nat) (b : bv 8) (Φ : iProp Σ) :
    (fline (fs_I st) = LEcho ws /\ last_ws (fs_I st) = ws) ->
    line_alts_of ws !!! 0%nat !! i = Some b ->
    ⊢ lk_pin FIs k v -∗ lk_links FIs -∗ lk_blk FIs k v (fs_I st) 0%nat i -∗
      (lk_blk FIs k v (fs_I st) 0%nat (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros [ Hln Hlast ] Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iApply (lk_blk_step FIs k v (fs_I st) 0%nat i b Φ with "Hpin Hlk Hc HΦ").
    cbn [lk_ab FIs file_link_gen_at gen_link_inst].
    rewrite (file_lmab0 (fs_I st) ltac:(rewrite /file_lineok Hlast; exact Hln)).
    rewrite Hlast. exact Hb.
  Qed.

  Definition file_cur_inst_at : CurRec FIs :=
    MkCurRec FIs file_stg
      (fun st ws => fline (fs_I st) = LEcho ws /\ last_ws (fs_I st) = ws)
      (fun ws => line_alts_of ws !!! 0%nat)
      file_lineok
      (fun k v st p => lk_blk FIs k v (fs_I st) 0%nat p)
      fi_cur_tl_at fi_step_at.

  Local Lemma fi_lend_stage_at (k : nat) (v : era_pins) (I : list (bv 8)) :
    file_lineok I ->
    ⊢ lk_lend FIs k v I -∗
      (∃ st : file_stg,
         ⌜fline (fs_I st) = LEcho (last_ws I)
          /\ last_ws (fs_I st) = last_ws I⌝
         ∗ ⌜line_alts_of (last_ws I) !!! 0%nat
            = line_alts_of (last_ws I) !!! 0%nat⌝
         ∗ lk_blk FIs k v (fs_I st) 0%nat 0%nat
         ∗ □ (lk_blk FIs k v (fs_I st) 0%nat
                (length (wl_line (drop 1 (last_ws I)))) -∗
              lk_post FIs k v I 0%nat))
      ∨ lk_T FIs.
  Proof using .
    intro Hlok.
    cbn [lk_lend lk_blk lk_T FIs file_link_gen_at gen_link_inst].
    rewrite /gwc_lend. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs s P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    iLeft. iExists (MkFileStg I). cbn [fs_I].
    iSplitR; [ iPureIntro; split; [ exact Hlok | reflexivity ] | ].
    iSplitR; [ by iPureIntro | ].
    iSplitL "Htn".
    - rewrite /gwc_blk. iLeft. iExists ps, cs, s, P.
      cbn [lm_blkcs]. rewrite Nat.add_0_r.
      iFrame "Htn Hps Hcs HE Hf". by iPureIntro.
    - iIntros "!> Hc". rewrite /lk_post.
      cbn [lk_blk lk_ab FIs file_link_gen_at gen_link_inst].
      rewrite (file_lmab0_len I Hlok). iExact "Hc".
  Qed.

  Local Lemma fi_apr0_at (I : list (bv 8)) :
    file_lineok I -> lk_apr FIs I 0%nat.
  Proof using .
    intro Hl. cbn [lk_apr FIs file_link_gen_at gen_link_inst]. exact (file_apr0 I Hl).
  Qed.

  Definition file_stage_inst_at : StageRec FIs :=
    MkStageRec FIs file_cur_inst_at (fun _ => 0%nat) fi_lend_stage_at fi_apr0_at.
End file_link_inst_at.

(* ...and the converse: the unindexed families ARE the existential
   closures of the indexed ones, which is what makes [file_link_inst] and
   [file_link_inst_at] two readings of one record rather than two
   records. *)
Section file_W_unpack.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.

  Lemma file_Wcl_unpack (I : list (bv 8)) (p : nat) :
    file_Wcl g I p -∗ ∃ s0 : fstate, file_Wcl_at g s0 I p.
  Proof using .
    rewrite /file_Wcl /lk_lcred.
    iIntros "H". iDestruct "H" as (v) "[#Hpin Hc]".
    cbn [lk_pin lk_lpr file_link_inst file_link_gen gen_link_inst] in *.
    iDestruct (gwc_lpr_unpack with "Hc") as (s0) "Hc".
    iExists s0. rewrite /file_Wcl_at /lk_lcred. iExists v.
    cbn [lk_pin lk_lpr file_link_inst_at file_link_gen_at gen_link_inst].
    iFrame "Hpin Hc".
  Qed.

  Lemma file_Wbl_unpack (I : list (bv 8)) :
    file_Wbl g I -∗ ∃ s0 : fstate, file_Wbl_at g s0 I.
  Proof using .
    rewrite /file_Wbl.
    iIntros "H". iDestruct "H" as (v) "[#Hpin Hc]".
    cbn [lk_pin lk_ban file_link_inst file_link_gen gen_link_inst] in *.
    iDestruct (gwc_ban_unpack with "Hc") as (s0) "Hc".
    iExists s0. rewrite /file_Wbl_at. iExists v.
    cbn [lk_pin lk_ban file_link_inst_at file_link_gen_at gen_link_inst].
    iFrame "Hpin Hc".
  Qed.
End file_W_unpack.
