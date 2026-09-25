(* ===================================================================== *)
(*  UCatOut.v -- cat's CONSOLE OUTPUT AT THE FILE STAGE.                  *)
(*                                                                       *)
(*  [UEchoOut.v] is echo's share of a completed line at the ECHO stage;   *)
(*  this file is cat's at the FILE stage.  cat's round is the [LCat_f]      *)
(*  line, and the alternative it takes is decided by THE DEED and not by  *)
(*  the return value of its own open:                                    *)
(*                                                                       *)
(*    a PRESENT deed whose open succeeded   [FileDisc.RCRan]  -- the      *)
(*        content, then the shell's prompt;                              *)
(*    an ABSENT deed                        [FileDisc.RCRan]  -- at       *)
(*        [s = None] the continuation IS the diagnostic                   *)
(*        ([FileDisc.alt_catopen]), which is what cat's                   *)
(*        [fprintf(2, ...)] prints;                                      *)
(*    a PRESENT deed whose open returned -1 [FileDisc.RCNoOpen] -- the    *)
(*        same bytes at a file that is still there.                      *)
(*                                                                       *)
(*  So the two alternatives print the SAME diagnostic and differ only in  *)
(*  what the file holds; which one is filed is read off the deed, exactly *)
(*  as [RFOpenU] / [RFOpenM] are on the redirect side.  That corrects the *)
(*  lane brief, which paired [RCNoOpen] with the -1 return.               *)
(*                                                                       *)
(*  THE EMPTY CONTENT COSTS NOTHING.  At [s = Some []] the round's whole  *)
(*  continuation is the prompt ([cat_cont_ran_nil]), so cat writes no     *)
(*  byte, files no alternative and hands the turn back where it found it; *)
(*  the block's FIRST byte is then the prompt's, and the shell files      *)
(*  [RCRan] at it through [FileLinks.file_write_link_blk] with no help    *)
(*  from cat.  No second exit-payload shape is needed on the stage's side *)
(*  -- only on cat's own, which is [catq_unfiled] below.                  *)
(*                                                                       *)
(*  WHAT IS NOT HERE, and why (lane CAT-ENTRY's STOP): the conversion of  *)
(*  cat's WALK into these links.  [UEchoOut]'s S4-S7 turn                 *)
(*  [UkEcho.kecho_pay_all] -- a chain of per-CALL obligations at an       *)
(*  abstract cursor -- into the era's link.  cat's landed walk has no     *)
(*  such chain: [UkCat.wp_kcat_write] routes write(16) through the QUIET  *)
(*  row at [UkCat.cat_deps]' [UkRun.udepw_law 16], the key-free FREE      *)
(*  write law, and discards the post; and [UkCat.cat_deps] is a premise   *)
(*  of every lemma of the walk.  At the file application that law is      *)
(*  payable only from [AppInv.app_sup], which is                          *)
(*  [AppFile.file_taint_of_sup] -- the taint.  So the sections below are  *)
(*  the payment a walk RESTATED over a per-call chain would consume, and  *)
(*  they are stated so that such a walk plugs into them unchanged.        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import RiscvPtsto.
Require Import LineWords.
Require Import EchoDisc.
Require Import FileState.
Require Import FileDisc.
Require Import FileOutPure.
Require Import EchoOut.
Require Import AppEcho.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinks.
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import WpUart.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  1.  cat's STAGE: THE PURE PART OF WHAT SH's FORK LENDS IT             *)
(* ===================================================================== *)

(* WHERE THE ERA STANDS WHEN cat RUNS.  [UEchoOut.echo_stage] with the
   line NAMED BY ITS SHAPE rather than by its words: cat's round is the
   [LCat_f] line the shell parsed, the era's input has no partial line, and
   every line below this one is resolved.  The boot state [s0] is the one
   [FileOut.f0_lb] pins and the state at cat's own round is a FUNCTION of
   it ([FileDisc.fstate_upto]), so the stage names no history. *)
Definition cat_stage (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8))
    (P : nat) : Prop :=
  rest_of I0 = []
  /\ nlines I0 = S (length cs0)
  /\ uline_of (bodies_of I0 !!! (nlines I0 - 1)%nat) = LCat_f
  /\ P = length (proc_before_f ps0 cs0 (Some s0) I0)
  /\ pro_pin_f ps0 cs0 I0.

(* THE STATE cat's ROUND STARTS AT -- the whole of what the file adds to a
   writer's obligation. *)
Definition cat_st (cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) : fstate :=
  fstate_upto cs0 s0 (bodies_of I0) (nlines I0 - 1)%nat.

(* THE PURE TIE cat RECEIVES FROM SH AND CARRIES: the value its deed
   FRACTION agrees on IS the model's state at its own round.  It is what
   turns [FileOpen.fdq_agree] into a fact about [FileDisc.cont], and it is
   all the stage ever needs of the claim. *)
Definition cat_tie (cs0 : list nat) (s0 : fstate) (I0 : list (bv 8))
    (s : dst) : Prop :=
  dst_content s = cat_st cs0 s0 I0.

Lemma cat_stage_nonnil ps0 cs0 s0 I0 P :
  cat_stage ps0 cs0 s0 I0 P -> I0 <> [].
Proof using.
  intros (_ & Hn & _) ->. rewrite nlines_nil in Hn. discriminate.
Qed.

Lemma cat_stage_last ps0 cs0 s0 I0 P :
  cat_stage ps0 cs0 s0 I0 P -> (nlines I0 - 1)%nat = length cs0.
Proof using. intros (_ & Hn & _). lia. Qed.

Lemma cat_stage_nstarted ps0 cs0 s0 I0 P :
  cat_stage ps0 cs0 s0 I0 P -> nstarted I0 = S (length cs0).
Proof using.
  intros Hst. pose proof Hst as (Hr & Hn & _).
  by rewrite (fop_nstarted_rest_nil I0 Hr) Hn.
Qed.

(* filing an alternative reads no round below the boundary *)
Lemma cat_stage_pin_snoc ps0 cs0 s0 I0 P a :
  cat_stage ps0 cs0 s0 I0 P -> pro_pin_f ps0 (cs0 ++ [a]) I0.
Proof using.
  intros Hst. pose proof (cat_stage_nstarted ps0 cs0 s0 I0 P Hst) as Hns.
  pose proof Hst as (_ & _ & _ & _ & Hpin).
  intros q Hq. rewrite Hns in Hq.
  rewrite (pro_idx_f_ext (cs0 ++ [a]) cs0 q
             ltac:(intros j Hj; rewrite list_lookup_total_alt lookup_app_l;
                   [by rewrite -list_lookup_total_alt | lia])
             q ltac:(lia)).
  apply Hpin. rewrite Hns. exact Hq.
Qed.

(* ...and it moves no byte of what is already out *)
Lemma cat_blk_low ps0 cs0 s0 I0 P a :
  cat_stage ps0 cs0 s0 I0 P ->
  proc_before_f ps0 (cs0 ++ [a]) (Some s0) I0
  = proc_before_f ps0 cs0 (Some s0) I0.
Proof using.
  intros Hst. pose proof Hst as (Hr & Hn & _ & _ & Hpin). symmetry.
  apply (proc_before_f_cs_prefix ps0 ps0 cs0 (cs0 ++ [a]) (Some s0) I0
           ltac:(reflexivity) ltac:(by eexists) Hpin).
  rewrite (fop_nlines_removelast I0 Hr). lia.
Qed.

(* THE BLOCK cat's ROUND OWES, once alternative [a] is filed: at a
   NON-PANIC alternative it is exactly that alternative's own output at
   the state the file is in.  ([RCRan] and [RCNoOpen] are both
   non-panic -- only sh's [fork1] diagnostic re-enters the prologue.) *)
Lemma cat_blk_pending ps0 cs0 s0 I0 P a :
  cat_stage ps0 cs0 s0 I0 P ->
  ralt_panic (ralt_dec a) = false ->
  pending_at_f ps0 (cs0 ++ [a]) (Some s0) I0
  = cont (cat_st cs0 s0 I0) LCat_f (ralt_dec a).
Proof using.
  intros Hst Hnp.
  pose proof (cat_stage_nonnil ps0 cs0 s0 I0 P Hst) as Hne.
  pose proof (cat_stage_last ps0 cs0 s0 I0 P Hst) as Hlast.
  pose proof Hst as (Hr & Hn & Hl & _ & _).
  assert (Hat : ralt_at (cs0 ++ [a]) (nlines I0 - 1)%nat = ralt_dec a).
  { rewrite /ralt_at Hlast list_lookup_total_alt lookup_app_r;
      [| lia].
    by rewrite Nat.sub_diag. }
  assert (Hup : fstate_upto (cs0 ++ [a]) s0 (bodies_of I0) (nlines I0 - 1)%nat
                = cat_st cs0 s0 I0).
  { rewrite /cat_st.
    apply (fstate_upto_ext (cs0 ++ [a]) cs0 s0 (bodies_of I0) (bodies_of I0));
      [| intros j _; reflexivity ].
    intros j Hj. rewrite list_lookup_total_alt lookup_app_l; [| lia].
    by rewrite -list_lookup_total_alt. }
  rewrite /pending_at_f decide_False; [| exact Hne].
  rewrite decide_True; [| exact Hr].
  rewrite /alt_cont_f f0_st_some Hat Hup Hl Hnp. by rewrite app_nil_r.
Qed.

(* THE STREAM BYTE THE WRITE LINK ASKS FOR: byte [j] of cat's alternative
   is byte [P + j] of the era's process stream. *)
Lemma cat_blk_byte ps0 cs0 s0 I0 P a j b :
  cat_stage ps0 cs0 s0 I0 P ->
  ralt_panic (ralt_dec a) = false ->
  cont (cat_st cs0 s0 I0) LCat_f (ralt_dec a) !! j = Some b ->
  proc_stream_f ps0 (cs0 ++ [a]) (Some s0) I0 !! (P + j)%nat = Some b.
Proof using.
  intros Hst Hnp Hb. pose proof Hst as (_ & _ & _ & HP & _).
  rewrite /proc_stream_f (cat_blk_low ps0 cs0 s0 I0 P a Hst)
          lookup_app_r; [| lia].
  replace (P + j - length (proc_before_f ps0 cs0 (Some s0) I0))%nat
    with j by lia.
  by rewrite (cat_blk_pending ps0 cs0 s0 I0 P a Hst Hnp).
Qed.

(* ===================================================================== *)
(*  2.  THE TWO ALTERNATIVES, AND WHAT EACH PRINTS                        *)
(* ===================================================================== *)

Lemma cat_ralt_ok_ran : ralt_ok LCat_f RCRan.
Proof using. exact I. Qed.

Lemma cat_ralt_ok_noopen : ralt_ok LCat_f RCNoOpen.
Proof using. exact I. Qed.

Lemma cat_ralt_panic_ran : ralt_panic (ralt_dec (ralt_enc RCRan)) = false.
Proof using. by rewrite ralt_dec_enc. Qed.

Lemma cat_ralt_panic_noopen :
  ralt_panic (ralt_dec (ralt_enc RCNoOpen)) = false.
Proof using. by rewrite ralt_dec_enc. Qed.

(* the CONTENT arm: what cat reads is what it prints, and the prompt is
   the shell's *)
Lemma cat_cont_ran_some (s : fstate) (bs : list (bv 8)) :
  s !! fname_f = Some bs -> cont s LCat_f RCRan = bs ++ u_prompt.
Proof using. intros Hs. cbn [cont lname line_file default]. by rewrite Hs. Qed.

(* THE EMPTY CONTENT: the block's whole continuation is the prompt, so cat
   writes nothing and the shell's own prompt byte is the block's first. *)
Lemma cat_cont_ran_nil : cont {[fname_f := []]} LCat_f RCRan = u_prompt.
Proof using. apply (cat_cont_ran_some _ []). apply lookup_singleton. Qed.

(* the ABSENT arm: at an absent [f] the round's continuation IS cat's
   diagnostic -- so an absent deed is [RCRan], not [RCNoOpen] *)
Lemma cat_cont_ran_absent (s : fstate) :
  s !! fname_f = None -> cont s LCat_f RCRan = alt_catopen.
Proof using. intros Hs. cbn [cont lname line_file default]. by rewrite Hs. Qed.

Lemma cat_cont_ran_none : cont ∅ LCat_f RCRan = alt_catopen.
Proof using. apply cat_cont_ran_absent. apply lookup_empty. Qed.

(* ...and the PRESENT-but-unopenable one prints the same bytes *)
Lemma cat_cont_noopen (s : fstate) : cont s LCat_f RCNoOpen = alt_catopen.
Proof using. reflexivity. Qed.

(* the two are byte-identical at an absent file, which is why the
   observer cannot tell them apart and the DEED is what decides which is
   filed ([FileOpen.fdq_agree] at cat's fraction) *)
Lemma cat_cont_none_eq : cont ∅ LCat_f RCRan = cont ∅ LCat_f RCNoOpen.
Proof using. by rewrite cat_cont_ran_none cat_cont_noopen. Qed.

(* WHAT THE DEED BUYS: the fraction agrees on [s], the tie says [s] is the
   model's state, and the two together name cat's own output. *)
Lemma cat_out_of_tie (cs0 : list nat) (s0 : fstate) (I0 : list (bv 8))
    (s : dst) (i : Z) (bs : list (bv 8)) :
  cat_tie cs0 s0 I0 s -> s = Some (i, bs) ->
  cont (cat_st cs0 s0 I0) LCat_f RCRan = bs ++ u_prompt.
Proof using.
  intros Htie Hs. rewrite /cat_tie Hs /dst_content in Htie.
  cbn [fmap option_fmap option_map fst_of snd] in Htie.
  rewrite -Htie. apply cat_cont_ran_some. apply lookup_singleton.
Qed.

Lemma cat_out_of_tie_none (cs0 : list nat) (s0 : fstate) (I0 : list (bv 8))
    (s : dst) :
  cat_tie cs0 s0 I0 s -> s = None ->
  cont (cat_st cs0 s0 I0) LCat_f RCRan = alt_catopen.
Proof using.
  intros Htie Hs. rewrite /cat_tie Hs /dst_content in Htie.
  cbn [fmap option_fmap option_map fst_of snd] in Htie.
  rewrite -Htie. apply cat_cont_ran_none.
Qed.

(* ===================================================================== *)
(*  CAT'S OWN END CURSOR (lane CAT-GEOM-2).                               *)
(*                                                                       *)
(*  Every alternative cat's round can take is `<cat's own output> ++      *)
(*  u_prompt`, and THE PROMPT IS THE SHELL'S -- cat exits before it is    *)
(*  written.  So the cursor cat leaves the era at is the round's length   *)
(*  MINUS the prompt's two bytes: [|bs|] on the content arm and NINETEEN  *)
(*  on the diagnostic.  [UEchoOut.echo_uexec_slot_at] has had the right   *)
(*  shape all along -- it files at [length (wl_line (drop 1 ws))], the    *)
(*  PROGRAM's own output length -- and [catq_filed] below is restated at  *)
(*  this.                                                                *)
(* ===================================================================== *)
Definition cat_out_len (cs0 : list nat) (s0 : fstate) (I0 : list (bv 8))
    (a : nat) : nat :=
  (length (cont (cat_st cs0 s0 I0) LCat_f (ralt_dec a)) - length u_prompt)%nat.

Lemma cat_prompt_len : length u_prompt = 2%nat.
Proof using. vm_compute. reflexivity. Qed.

Lemma cat_out_len_ran_some (cs0 : list nat) (s0 : fstate) (I0 : list (bv 8))
    (s : dst) (i : Z) (bs : list (bv 8)) :
  cat_tie cs0 s0 I0 s -> s = Some (i, bs) ->
  cat_out_len cs0 s0 I0 (ralt_enc RCRan) = length bs.
Proof using.
  intros Htie Hs. rewrite /cat_out_len ralt_dec_enc.
  rewrite (cat_out_of_tie cs0 s0 I0 s i bs Htie Hs).
  rewrite length_app cat_prompt_len. lia.
Qed.

Lemma cat_out_len_ran_none (cs0 : list nat) (s0 : fstate) (I0 : list (bv 8))
    (s : dst) :
  cat_tie cs0 s0 I0 s -> s = None ->
  cat_out_len cs0 s0 I0 (ralt_enc RCRan) = 19%nat.
Proof using.
  intros Htie Hs. rewrite /cat_out_len ralt_dec_enc.
  rewrite (cat_out_of_tie_none cs0 s0 I0 s Htie Hs).
  vm_compute. reflexivity.
Qed.

(* ...and at [RCNoOpen] it is NINETEEN at EVERY state: the alternative's
   continuation is the diagnostic whatever the file holds
   ([cat_cont_noopen]). *)
Lemma cat_out_len_noopen (cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) :
  cat_out_len cs0 s0 I0 (ralt_enc RCNoOpen) = 19%nat.
Proof using.
  rewrite /cat_out_len ralt_dec_enc.
  rewrite (cat_cont_noopen (cat_st cs0 s0 I0)).
  vm_compute. reflexivity.
Qed.


(* ===================================================================== *)
(*  3.  THE CURSOR FAMILY, AND ONE BYTE THROUGH THE ERA'S WRITE LINK      *)
(*                                                                       *)
(*  [UEchoOut]'s S1-S3 at the FILE stage.  [p] of cat's output bytes are  *)
(*  out and the era's cursor says so -- or the era is TAINTED.  The       *)
(*  choice list grows at the FIRST byte and not before, which is the      *)
(*  whole content of [catcs]; at [p = 0] the family does not mention the  *)
(*  alternative at all ([cch_0_alt]), which is what lets cat hand the     *)
(*  turn back UNFILED when its content is empty.                         *)
(* ===================================================================== *)
Section UCatOut.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = fecl g).

  Definition catcs (cs0 : list nat) (a p : nat) : list nat :=
    match p with O => cs0 | S _ => cs0 ++ [a] end.

  Lemma catcs_pos (cs0 : list nat) (a p : nat) :
    (0 < p)%nat -> catcs cs0 a p = cs0 ++ [a].
  Proof using . intro Hp. destruct p as [| p']; [lia | reflexivity]. Qed.

  Definition cch (v : era_pins) (vf : file_era) (ps0 cs0 : list nat)
      (s0 : fstate) (I0 : list (bv 8)) (a P p : nat) : iProp Σ :=
    ((turn v (P + p)%nat ∗ ps_lb v ps0 ∗ cs_lb v (catcs cs0 a p)
      ∗ inp_lb v I0 ∗ f0_lb vf s0) ∨ file_taint (fgn_cl g))%I.

  Global Instance cch_timeless v vf ps0 cs0 s0 I0 a P p :
    Timeless (cch v vf ps0 cs0 s0 I0 a P p).
  Proof using . rewrite /cch /file_taint /echo_taint. apply _. Qed.

  (* AT THE CURSOR'S START THE ALTERNATIVE IS NOT YET NAMED.  This is the
     EMPTY-CONTENT case's whole content: cat returns the credential it was
     lent, at the choice list it was lent it at, and the shell's own
     prompt byte opens the block. *)
  Lemma cch_0_alt (v : era_pins) (vf : file_era) (ps0 cs0 : list nat)
      (s0 : fstate) (I0 : list (bv 8)) (a a' P : nat) :
    cch v vf ps0 cs0 s0 I0 a P 0%nat ⊣⊢ cch v vf ps0 cs0 s0 I0 a' P 0%nat.
  Proof using . rewrite /cch /catcs. reflexivity. Qed.

  (* ONE BYTE.  The block-first byte FILES the alternative
     ([FileLinks.file_write_link_blk]); every byte after it goes through
     the ordinary link at the choice list the first one extended. *)
  Lemma cch_step (k : nat) (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8))
      (a P p : nat) (b : bv 8) (Φ : iProp Σ) :
    cat_stage ps0 cs0 s0 I0 P ->
    ralt_ok LCat_f (ralt_dec a) ->
    ralt_panic (ralt_dec a) = false ->
    cont (cat_st cs0 s0 I0) LCat_f (ralt_dec a) !! p = Some b ->
    era_pin (fgn_echo g) k v -∗ file_era_pin g k vf -∗
    cch v vf ps0 cs0 s0 I0 a P p -∗
    (cch v vf ps0 cs0 s0 I0 a P (S p) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hst Hok Hnp Hb.
    pose proof (cat_stage_nonnil ps0 cs0 s0 I0 P Hst) as Hne.
    pose proof (cat_stage_pin_snoc ps0 cs0 s0 I0 P a Hst) as Hpin1.
    pose proof Hst as (Hr & Hn & Hl & HP & Hpin).
    iIntros "#Hpin #Hfp Hc HΦ".
    rewrite /cch.
    iDestruct "Hc" as "[(Htn & #Hps & #Hcs & #Hilb & #Hf0) | #HT]".
    - destruct p as [| p']; cbn [catcs].
      + (* THE BLOCK-FIRST BYTE *)
        rewrite Nat.add_0_r.
        iApply (file_write_link_blk g Hcons k v vf P a b ps0 cs0 s0 I0 Φ
                  Hne Hr ltac:(lia) Hpin HP
                  ltac:(rewrite Hl; exact Hok)
                  ltac:(rewrite Hl; exact Hb)
                  with "Hpin Hfp Htn Hps Hcs Hilb Hf0 [HΦ]").
        iIntros "Hres". iApply "HΦ". cbn [catcs].
        replace (P + 1)%nat with (S P) by lia. iExact "Hres".
      + (* every byte after it *)
        iApply (file_write_link g Hcons k v vf (P + S p')%nat b ps0
                  (cs0 ++ [a]) s0 I0 Φ
                  ltac:(rewrite length_app; cbn [length]; lia)
                  Hpin1
                  (cat_blk_byte ps0 cs0 s0 I0 P a (S p') b Hst Hnp Hb)
                  with "Hpin Hfp Htn Hps Hcs Hilb Hf0 [HΦ]").
        iIntros "Hres". iApply "HΦ". cbn [catcs].
        replace (P + S (S p'))%nat with (S (P + S p')) by lia.
        iExact "Hres".
    - (* THE TAINT ARM continues the tower on its own *)
      iApply (file_write_link_taint g Hcons k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iRight.
  Qed.

  (* A RUN OF BYTES, AS THE CONSOLE CHAIN.  [UEchoOut.ech_chain] verbatim
     at cat's cursor: the node is ADDITIVE -- the cursor at [i] AND the
     step for the byte the image holds there -- so one copy of the era's
     bundle answers both. *)
  Lemma cch_chain (k : nat) (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8))
      (a P p : nat) (M : gmap Z (bv 8)) (ua : mword 64)
      (fb : nat -> bv 8) :
    cat_stage ps0 cs0 s0 I0 P ->
    ralt_ok LCat_f (ralt_dec a) ->
    ralt_panic (ralt_dec a) = false ->
    forall (c i : nat),
    (forall j : nat, (i <= j)%nat -> (j < i + c)%nat ->
       cont (cat_st cs0 s0 I0) LCat_f (ralt_dec a) !! (p + j)%nat
       = Some (fb j)) ->
    (forall j : nat, (i <= j)%nat -> (j < i + c)%nat ->
       M !! uint (add_vec_int ua (Z.of_nat j)) = Some (fb j)) ->
    era_pin (fgn_echo g) k v -∗ file_era_pin g k vf -∗
    cch v vf ps0 cs0 s0 I0 a P (p + i)%nat -∗
    cons_out_chain k M ua
      (fun j : nat => cch v vf ps0 cs0 s0 I0 a P (p + j)%nat) i c.
  Proof using Hcons.
    intros Hst Hok Hnp c. induction c as [| c IH]; intros i Hline HM.
    - iIntros "_ _ Hc". cbn [cons_out_chain]. iExact "Hc".
    - iIntros "#Hpin #Hfp Hc". cbn [cons_out_chain]. iSplit.
      + iExact "Hc".
      + iIntros (b) "%Hbm".
        assert (Hbb : b = fb i).
        { rewrite (HM i ltac:(lia) ltac:(lia)) in Hbm. by injection Hbm. }
        subst b.
        iApply (cch_step k v vf ps0 cs0 s0 I0 a P (p + i)%nat (fb i) _
                  Hst Hok Hnp (Hline i ltac:(lia) ltac:(lia))
                  with "Hpin Hfp Hc").
        iIntros "Hc".
        replace (S (p + i))%nat with (p + S i)%nat by lia.
        iApply (IH (S i) ltac:(intros j H1 H2; apply Hline; lia)
                  ltac:(intros j H1 H2; apply HM; lia) with "Hpin Hfp Hc").
  Qed.

  (* ...AND THE SAME RUN AT A TAINTED ERA, with no row at all (lane
     CAT-ENTRY-2).  [cch_chain] asks for the model's byte at every
     position because its non-taint arm files them; at a tainted era the
     tower continues on its own ([FileLinks.file_write_link_taint]) and
     the cursor is the right disjunct at EVERY position, so a writer that
     holds the taint funds a run of ANY length and claims nothing.  This
     is what lets cat's round be built at a turn whose justification is
     the taint. *)
  Lemma cch_chain_taint (k : nat) (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8))
      (a P p : nat) (M : gmap Z (bv 8)) (ua : mword 64) :
    forall (c i : nat),
    file_taint (fgn_cl g) -∗
    cons_out_chain k M ua
      (fun j : nat => cch v vf ps0 cs0 s0 I0 a P (p + j)%nat) i c.
  Proof using Hcons.
    intros c. induction c as [| c IH]; intros i.
    - iIntros "#HT". cbn [cons_out_chain]. rewrite /cch. by iRight.
    - iIntros "#HT". cbn [cons_out_chain]. iSplit.
      + rewrite /cch. by iRight.
      + iIntros (b) "_".
        iApply (file_write_link_taint g Hcons k b _ with "HT").
        iIntros "_". iApply (IH (S i) with "HT").
  Qed.

  (* ===================================================================== *)
  (*  4.  cat's TWO EXIT-PAYLOAD SHAPES                                     *)
  (*                                                                       *)
  (*  What the shell is owed when cat exits.  On the FILED shape the        *)
  (*  alternative is in the choice list and the cursor is at the end of     *)
  (*  cat's own run; on the UNFILED one nothing moved.  Both are            *)
  (*  STATUS-INDEPENDENT ([UkRun.ukn_const]'s shape): cat exits 0 on the    *)
  (*  content arm and 1 on the diagnostic arm, and what the parent is owed  *)
  (*  is the same either way.                                              *)
  (* ===================================================================== *)
  (* ...AT CAT'S OWN END CURSOR and not at the round's (lane CAT-GEOM-2;
     see [cat_out_len] above).  The two bytes between them are the
     SHELL's prompt: cat exits before they are written, so what SH-ROUND
     files at them is its OWN prompt write -- through
     [FileLinks.file_write_link] at the choice list cat's first byte
     already extended, and through [file_write_link_blk] only in the
     EMPTY-CONTENT case, where cat wrote nothing and the prompt's first
     byte IS the block's ([cch_empty_unfiled], CAT-ENTRY's ruling (b)). *)
  Definition catq_filed (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (a P : nat)
    : Z -> iProp Σ :=
    fun _ => cch v vf ps0 cs0 s0 I0 a P (cat_out_len cs0 s0 I0 a).

  Definition catq_unfiled (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (P : nat)
    : Z -> iProp Σ :=
    fun _ => cch v vf ps0 cs0 s0 I0 0%nat P 0%nat.

  Lemma catq_filed_const (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (a P : nat)
      (x y : Z) :
    catq_filed v vf ps0 cs0 s0 I0 a P x
    = catq_filed v vf ps0 cs0 s0 I0 a P y.
  Proof using . reflexivity. Qed.

  Lemma catq_unfiled_const (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (P : nat)
      (x y : Z) :
    catq_unfiled v vf ps0 cs0 s0 I0 P x
    = catq_unfiled v vf ps0 cs0 s0 I0 P y.
  Proof using . reflexivity. Qed.

  (* THE EMPTY CONTENT, IN THE LOGIC: cat is handed the era's credential at
     the cursor its round opens and gives it back unchanged, because the
     round's whole continuation is the shell's prompt. *)
  Lemma cch_empty_unfiled (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (a P : nat) :
    (cat_st cs0 s0 I0 : fstate) !! fname_f = Some [] ->
    cch v vf ps0 cs0 s0 I0 a P 0%nat -∗
    catq_unfiled v vf ps0 cs0 s0 I0 P (-1).
  Proof using .
    intros _. rewrite /catq_unfiled /cch /catcs. by iIntros "$".
  Qed.

End UCatOut.
