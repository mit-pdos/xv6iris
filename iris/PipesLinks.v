(* ===================================================================== *)
(*  PipesLinks.v -- THE PIPELINE APPLICATION'S CONSOLE LINKS AT THE       *)
(*  N-STAGE CLAIM (cut C8).                                              *)
(*                                                                       *)
(*  [PipeOutNEv.peclE] -- the generic claim between rounds, the open     *)
(*  N-writer round while one is open -- wrapped onto the kernel's own    *)
(*  console contracts: the taint route, the single writer's three write  *)
(*  links ([PipesOut.pecl'_step_write] and its block and prologue        *)
(*  twins), the FILING link of an N-writer round (the prompt's first     *)
(*  byte files the block the family handed back, [PipeOutN.             *)
(*  pwc_blkN_file] / [PipeOutNEv.pwc_blkN_file_empty]), the read link,   *)
(*  the close and the byte, and [App.al_echo] as a closed entailment.    *)
(*                                                                       *)
(*  THE BUNDLE a program holds is the record equation itself, as a pure  *)
(*  persistent fact, and the links are read off it where they are spent  *)
(*  (as at [PipeLinks]).                                                 *)
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
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import EchoOut.
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenOutPure.
Require Import GenOutHist.
Require Import GenOut.
Require Import AppEcho.
Require Import PipeOut.
Require Import ProgTree.
Require Import PipesDisc.
Require Import PipesDiscDec.
Require Import PipeOutN.
Require Import PipeOutNEv.
Require Import PipesOut.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
Require Import SpecConsoleintr.
From stdpp Require Import list.
Local Open Scope list_scope.

Section pipes_links.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.

  Notation T := (echo_taint γ).
  Local Notation PME := (pipes_lm (fun _ => None) adm_echo).
  Local Notation PBE := (pipes_lm_byte_laws (fun _ => None) adm_echo).
  Local Notation LwE := pipes_lm_echo_laws.

  (* the record equations, as section parameters *)
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = peclE g).
  Context (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HRg) = ptagE g).

  Lemma pschist_at0 (kk : nat) (hh : list mobs) (HH : LogEntryDefs.cons_hist) :
    chist_at Uart0 kk hh HH = peclE g kk hh HH.
  Proof using Hcons. rewrite /chist_at. by rewrite Hcons. Qed.

  Lemma peclE_taint (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    T -∗ peclE g k ho H.
  Proof using . rewrite /peclE. iApply pecl'_taint. Qed.

  (* ---- the taint route ---- *)
  Lemma pipes_cons_link_of_taint (k : nat) (ev : ConsLog.cons_ev) (Φ : iProp Σ) :
    T -∗ Φ -∗ cons_link Uart0 k ev Φ.
  Proof using Hcons.
    iIntros "#HT HΦ" (o H) "#Hlb Hres _ _".
    iModIntro. iExists o.
    iSplitR; [iExact "Hlb" |].
    iSplitR "HΦ"; [| iExact "HΦ"].
    rewrite !pschist_at0. by iApply peclE_taint.
  Qed.

  Lemma pipes_write_link_taint (k : nat) (b : bv 8) (Φ : iProp Σ) :
    T -∗ (T -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using Hcons.
    iIntros "#HT HΦ" (o H) "#Hlb Hres".
    iModIntro. iExists o.
    iSplitR; [iExact "Hlb" |].
    iSplitR "HΦ"; [| by iApply "HΦ"].
    rewrite !pschist_at0. by iApply peclE_taint.
  Qed.

  (* (W) THE WRITE LINK, inside a block or a prologue round *)
  Lemma pipes_write_link (k : nat) (v : era_pins) (P : nat) (b : bv 8)
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (Φ : iProp Σ) :
    (nlines I0 <= length cs0)%nat ->
    lm_pro_pin PME ps0 cs0 I0 ->
    lm_proc_stream PME ps0 cs0 tt I0 !! P = Some b ->
    era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0) ∨ T) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hn Hpin0 Hb.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb HΦ" (o H) "#Hlb Hres".
    rewrite !pschist_at0.
    iMod (pecl'_step_write g (fun _ => None) adm_echo LwE k v P b ps0 cs0 I0
            (default [] o) H Hn Hpin0 Hb with "Hpin Ht Hpslb Hcslb Hilb Hres")
      as "(Hres & Hret)".
    iModIntro. iExists o. rewrite pschist_at0. iFrame "Hlb Hres".
    by iApply "HΦ".
  Qed.

  (* (W') THE WRITE LINK AT A BLOCK'S FIRST BYTE: the program names the
     alternative its round takes and the line admits it *)
  Lemma pipes_write_link_blk (k : nat) (v : era_pins) (P a : nat)
      (b : bv 8) (ps0 cs0 : list nat) (I0 : list (bv 8)) (Φ : iProp Σ) :
    I0 <> [] ->
    rest_of I0 = [] ->
    (nlines I0 <= S (length cs0))%nat ->
    lm_pro_pin PME ps0 cs0 I0 ->
    P = length (lm_proc_before PME ps0 cs0 tt I0) ->
    lm_ok PME (lm_line_at PME I0) (lm_dec PME a) ->
    lm_term PME (lm_dec PME a) = false ->
    lm_abs PME tt cs0 I0 a !! 0%nat = Some b ->
    era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0)
      ∨ T) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hne0 Hr0 Hdiv Hpin0 HPeq Halt Hterm Hhead.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb HΦ" (o H) "#Hlb Hres".
    rewrite !pschist_at0.
    iMod (pecl'_step_write_blk g (fun _ => None) adm_echo LwE k v P a b ps0 cs0 I0
            (default [] o) H Hne0 Hr0 Hdiv Hpin0 HPeq Halt Hterm Hhead
            with "Hpin Ht Hpslb Hcslb Hilb Hres") as "(Hres & Hret)".
    iModIntro. iExists o. rewrite pschist_at0. iFrame "Hlb Hres".
    by iApply "HΦ".
  Qed.

  (* (W-pro) THE WRITE LINK AT A PROLOGUE ROUND'S CHOICE BYTE *)
  Lemma pipes_write_link_pro (k : nat) (v : era_pins) (P a : nat)
      (b : bv 8) (ps0 cs0 : list nat) (I0 : list (bv 8)) (Φ : iProp Σ) :
    rest_of I0 = [] ->
    (I0 = [] \/ lm_panic PME (lm_at PME cs0 (nlines I0 - 1)%nat) = true) ->
    (nlines I0 <= length cs0)%nat ->
    lm_pro_pin PME ps0 cs0 I0 ->
    ~ pro_done (pro_from (lm_pro_idx PME cs0 (nlines I0)) ps0) ->
    P = length (lm_proc_stream PME ps0 cs0 tt I0) ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    (((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0)
      ∨ T) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb HΦ" (o H) "#Hlb Hres".
    rewrite !pschist_at0.
    iMod (pecl'_step_write_pro g (fun _ => None) adm_echo LwE k v P a b ps0 cs0 I0
            (default [] o) H Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead
            with "Hpin Ht Hpslb Hcslb Hilb Hres") as "(Hres & Hret)".
    iModIntro. iExists o. rewrite pschist_at0. iFrame "Hlb Hres".
    by iApply "HΦ".
  Qed.

  (* (F) THE FILING LINK OF AN N-WRITER ROUND: the prompt's first byte,
     once the family has handed the block back ([PipeOutN.pipesN_file]) *)
  Lemma pipes_file_link (k : nat) (v : era_pins) (I pre : list (bv 8)) (b : bv 8)
      (Φ : iProp Σ) :
    adm_echo (lineN (fun _ => None) adm_echo I) = true ->
    line_blocks (fun _ => None) (lineN (fun _ => None) adm_echo I) pre ->
    b = u_prompt !!! 0%nat ->
    pwc_blkN g (fun _ => None) adm_echo v I k pre false -∗
    (((∃ (ps cs : list nat) (P : nat),
         ⌜wr_blkN (fun _ => None) adm_echo ps cs I P⌝
         ∗ turn v (S (P + length pre))%nat ∗ ps_lb v ps
         ∗ cs_lb v (cs ++ [plalt_code (PLRun pre)]) ∗ inp_lb v I) ∨ T) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Ha Hbl Hbv. iIntros "Hpw HΦ" (o H) "#Hlb Hres".
    rewrite !pschist_at0.
    destruct (decide (pre = [])) as [-> | Hne].
    - iMod (pwc_blkN_file_empty g (fun _ => None) adm_echo LwE v I k (default [] o) H b
              Ha Hbl Hbv with "Hpw Hres") as "(Hres & Hret)".
      iModIntro. iExists o. rewrite pschist_at0. iFrame "Hlb Hres".
      iApply "HΦ". iDestruct "Hret" as "[Hx | HT]"; [| by iRight].
      iLeft. iDestruct "Hx" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE)".
      iExists ps, cs, P. cbn [length]. rewrite Nat.add_0_r.
      iFrame "Htn Hps Hcs HE". by iPureIntro.
    - iMod (pwc_blkN_file g (fun _ => None) adm_echo LwE v I k (default [] o) H pre b
              Ha Hbl Hne Hbv with "Hpw Hres") as "(Hres & Hret)".
      iModIntro. iExists o. rewrite pschist_at0. iFrame "Hlb Hres".
      by iApply "HΦ".
  Qed.

  (* (R) THE READ LINK *)
  Definition preadE_ret (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) : iProp Σ :=
    ((T ∗ dl_cnt v (1/2) n)
     ∨ dl_cnt v (1/2) (n + length ws)%nat
       ∗ ∃ (pops : list log_entry) (dl : list (list mobs * bv 8)),
           ⌜read_ok pops dl ws⌝ ∗ ⌜length dl = n⌝
           ∗ ⌜(dl ++ ws) `prefix_of` echoed pops⌝
           ∗ ⌜E_index (seg_of (echoed pops))⌝
           ∗ ⌜lm_E_disc PME (seg_of (echoed pops))⌝
           ∗ inp_lb v (snd <$> (dl ++ ws))
           ∗ ⌜lm_disc_input PME (snd <$> (dl ++ ws))⌝
           ∗ (⌜ws = []⌝
              ∨ ∃ cs0 ps0 : list nat,
                  cs_lb v cs0 ∗ ps_lb v ps0
                  ∗ ⌜(nlines (snd <$> (dl ++ ws)) <= S (length cs0))%nat⌝
                  ∗ turn_lb v (length (lm_proc_before PME ps0 cs0 tt
                                 (snd <$> (dl ++ ws))))
                  ∗ ⌜lm_rd_stage PME ps0 cs0 (snd <$> (dl ++ ws))⌝))%I.

  Lemma pipes_read_link (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
    era_pin γ k v -∗ dl_cnt v (1/2) n -∗ (preadE_ret k v n ws -∗ Φ) -∗
    cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using Hcons.
    iIntros "#Hpin Hdlr HΦ" (o H) "#Hlb Hres _ %Hread".
    rewrite !pschist_at0.
    iMod (pecl'_step_read g (fun _ => None) adm_echo LwE k v n (default [] o) H ws Hread
            with "Hpin Hdlr Hres") as "(Hres & Hret)".
    iModIntro. iExists o. rewrite pschist_at0. iFrame "Hlb Hres".
    iApply "HΦ". rewrite /preadE_ret /rd_retN.
    iDestruct "Hret" as "[Ht | (Hdlr & %Hdl & %Hpref & %Hidx & %Hbyte & _
                               & Hilb & %Hdi & Hrest)]"; [by iLeft |].
    iRight. iFrame "Hdlr".
    iExists (LogEntryDefs.ch_log H), (LogEntryDefs.ch_dl H).
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iSplitL "Hilb"; [iExact "Hilb" |].
    iSplitR; [by iPureIntro |].
    iDestruct "Hrest" as "[%Hws | Hb]"; [by iLeft |].
    iDestruct "Hb" as (cs0 ps0 s0) "(Hcs & Hps & _ & %Hnl & Htl & %Hrs)".
    iRight. iExists cs0, ps0. iFrame "Hcs Hps". iSplitR; [by iPureIntro |].
    destruct s0. iFrame "Htl". by iPureIntro.
  Qed.

  (* ---- the arm's close and its bytes, both free ---- *)
  Lemma pipes_close_link (k : nat) (Φ : iProp Σ) :
    Φ -∗ cons_link Uart0 k ConsLog.EvClose Φ.
  Proof using Hcons.
    iIntros "HΦ" (o H) "#Hlb Hres %Hok %Hev".
    rewrite pschist_at0.
    iDestruct (pecl'_close g (fun _ => None) adm_echo LwE k (default [] o) H Hok Hev
                 with "Hres") as "Hres".
    iModIntro. iExists o. rewrite pschist_at0. by iFrame "Hlb Hres HΦ".
  Qed.

  Lemma pipes_byte_link (k : nat) (b : bv 8) (Φ : iProp Σ) :
    Φ -∗ cons_link Uart0 k (ConsLog.EvByte b) Φ.
  Proof using Hcons.
    iIntros "HΦ" (o H) "#Hlb Hres %Hok %Hev".
    rewrite pschist_at0.
    iMod (pecl'_step_byte g (fun _ => None) adm_echo LwE k (default [] o) H b Hok Hev
            with "Hres") as "Hres".
    iModIntro. iExists o. rewrite pschist_at0. by iFrame "Hlb Hres HΦ".
  Qed.

  Lemma pipes_cons_run (k : nat) (cs : list (bv 8)) (Φ : iProp Σ) :
    Φ -∗ cons_run k cs Φ.
  Proof using Hcons.
    iIntros "HΦ". iInduction cs as [| b cs] "IH" forall (Φ); cbn [cons_run].
    - by iApply pipes_close_link.
    - iSplit.
      + by iApply pipes_close_link.
      + iApply pipes_byte_link. by iApply "IH".
  Qed.

  (* THE ECHO SHIFT -- [App.al_echo], a CLOSED entailment *)
  Lemma pipes_happ_echo :
    ⊢ ∀ (GEN : GenId) (XI : CurCtx),
        @SpecConsoleintr.cons_echo_shift Σ HRg GEN XI.
  Proof using Hcons Htag.
    iIntros (GEN XI).
    rewrite /SpecConsoleintr.cons_echo_shift Htag.
    iIntros "!>" (h c cs Φ) "%Hends %Hk %Hcs #Htg #Hlbh HΦ".
    iDestruct "Htg" as "[%Hsh [%Hdisc | #HT]]"; last first.
    { iApply (pipes_cons_link_of_taint with "HT [HΦ]").
      by iApply pipes_cons_run. }
    iIntros (o H) "#Hlb Hres %Hok %Hev".
    rewrite pschist_at0.
    destruct (lm_disc_open_seg PME h Hsh Hdisc) as (s & _ & Hseg).
    iDestruct (pecl'_open g (fun _ => None) adm_echo LwE (S gen_id) (default [] o) H h c cs
                 Hok Hev (proj1 Hseg) Hk Hdisc Hsh with "Hres") as "Hres".
    iModIntro. iExists (Some h). cbn [obs_hist_lb_o from_option id].
    rewrite pschist_at0. iFrame "Hlbh Hres".
    by iApply pipes_cons_run.
  Qed.
End pipes_links.

(* ===================================================================== *)
(*  THE BUNDLE: the record equation, as a pure persistent fact            *)
(* ===================================================================== *)
Section pipes_links_bundle.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.

  Notation T := (echo_taint γ).

  Definition pipes_link_taint : iProp Σ :=
    (□ ∀ (k : nat) (b : bv 8) (Φ : iProp Σ),
        T -∗ (T -∗ Φ) -∗ out_link Uart0 k b Φ)%I.

  Definition pipes_link_rd : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (n : nat)
         (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
        era_pin γ k v -∗ dl_cnt v (1/2) n -∗
        (preadE_ret g k v n ws -∗ Φ) -∗
        cons_link Uart0 k (ConsLog.EvRead ws) Φ)%I.

  Definition pipes_link_rd_taint : iProp Σ :=
    (□ ∀ (k : nat) (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
        T -∗ (T -∗ Φ) -∗ cons_link Uart0 k (ConsLog.EvRead ws) Φ)%I.

  Definition pipes_links : iProp Σ :=
    ⌜@riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = peclE g⌝%I.

  Global Instance pipes_link_taint_persistent : Persistent pipes_link_taint | 0.
  Proof using . rewrite /pipes_link_taint. apply bi.intuitionistically_persistent. Qed.
  Global Instance pipes_link_rd_persistent : Persistent pipes_link_rd | 0.
  Proof using . rewrite /pipes_link_rd. apply bi.intuitionistically_persistent. Qed.
  Global Instance pipes_link_rd_taint_persistent :
    Persistent pipes_link_rd_taint | 0.
  Proof using . rewrite /pipes_link_rd_taint. apply bi.intuitionistically_persistent. Qed.
  Global Instance pipes_links_persistent : Persistent pipes_links | 0.
  Proof using . rewrite /pipes_links. apply bi.pure_persistent. Qed.

  Lemma pipes_links_eq :
    pipes_links -∗ ⌜@riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = peclE g⌝.
  Proof using . rewrite /pipes_links. by iIntros "%Hc". Qed.

  Lemma pipes_links_taint : pipes_links -∗ pipes_link_taint.
  Proof using .
    iIntros "Hlk". iDestruct (pipes_links_eq with "Hlk") as %Hc.
    rewrite /pipes_link_taint. iIntros "!>" (k b Φ) "HT HΦ".
    iApply (pipes_write_link_taint g Hc with "HT HΦ").
  Qed.

  Lemma pipes_links_rd : pipes_links -∗ pipes_link_rd.
  Proof using .
    iIntros "Hlk". iDestruct (pipes_links_eq with "Hlk") as %Hc.
    rewrite /pipes_link_rd. iIntros "!>" (k v n ws Φ) "Hpin Hdl HΦ".
    iApply (pipes_read_link g Hc with "Hpin Hdl HΦ").
  Qed.

  Lemma pipes_links_rd_taint : pipes_links -∗ pipes_link_rd_taint.
  Proof using .
    iIntros "Hlk". iDestruct (pipes_links_eq with "Hlk") as %Hc.
    rewrite /pipes_link_rd_taint. iIntros "!>" (k ws Φ) "#HT HΦ".
    iApply (pipes_cons_link_of_taint g Hc with "HT [HΦ]").
    by iApply "HΦ".
  Qed.

  Lemma pipes_links_holds
      (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = peclE g) :
    ⊢ pipes_links.
  Proof using . by iPureIntro. Qed.
End pipes_links_bundle.

(* THE BUNDLE IS OPAQUE TO THE INSTANCE SEARCH ([PipeLinks]'s measured
   rule): a [Persistent (pipes_links _)] goal is settled by its own
   instance and nothing else is tried. *)
#[global] Typeclasses Opaque pipes_links.
