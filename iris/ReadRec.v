(* ===================================================================== *)
(*  ReadRec.v -- THE READ RECORD: what the SHELL'S READ takes of an era.  *)
(*                                                                       *)
(*  Lane LINK-GEN-4 (lane LINK-GEN-3's findings, section 6.1).            *)
(*  [LinkRec.v] carries the read's RETURN as a single field [lk_rr], which *)
(*  is right for the two places that only PASS it; [UShLine]'s read LEAF  *)
(*  needs three things more, and [LinkRec] is frozen, so they are a       *)
(*  record of their own:                                                 *)
(*                                                                       *)
(*   - [rk_disc], the INPUT'S DISCIPLINE ([EchoDisc.disc_input] at echo,  *)
(*     [FileDisc.disc_input_f] at the file).  It is the parameter         *)
(*     [UkSh.ush_read_ans_at] takes.                                      *)
(*   - [rk_rd] / [rk_rd_taint], the era's READ LINK and its taint route   *)
(*     ([EchoLinks.echo_link_rd] / [echo_link_rd_taint] -- projections of *)
(*     [lk_links] that [LinkRec] does not expose).                        *)
(*   - [rk_arms], THE WINDOW ARM: the whole of what [UShLine.             *)
(*     ush_read_recv_era] reads out of the receipt, packaged at the rows  *)
(*     the console member hands it.  Opening [EchoOut.read_ret]'s body is *)
(*     what that lemma did by hand three times; this is the one law it    *)
(*     does it through now.                                              *)
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
Require Import EchoDisc.
Require Import LogEntryDefs.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import RiscvPtsto.
Require Import ConsoleInv.
Require Import WpUart.
Require Import EchoOut.
Require Import EchoLinks.
Require Import LinkRec.
Require Import UserConsole.       (* [ucons_swallow] / [ucons_stored_lb]: the swallowed byte's tag *)
Local Open Scope list_scope.

(* ===================================================================== *)
(*  THE RING'S TRANSLATION IS THE IDENTITY ON A DISCIPLINED INPUT         *)
(*  (lane IO-LEAF, M5; it moves here from [UShLine] because the echo      *)
(*  instance below is what needs it).                                     *)
(* ===================================================================== *)
Lemma disc_input_no_cr (I : list (bv 8)) (j : nat) :
  disc_input I -> (j < length I)%nat -> cons_xlate (I !!! j) = I !!! j.
Proof using.
  intros Hd Hj. pose proof (disc_input_byte_ncr I j Hd Hj) as Hv.
  rewrite /cons_xlate. rewrite decide_False; [reflexivity |].
  intro Hq. apply (f_equal bv_unsigned) in Hq.
  rewrite (_ : bv_unsigned (mword_of_int 13 : mword 8) = 13%Z) in Hq;
    [lia | by vm_compute].
Qed.

(* THE BYTE THE READ DELIVERED IS THE INPUT'S, AT THE READER'S OWN COUNT.
   Three rows of one receipt meet here: the WINDOW row says the [j]th byte
   the call delivered is the ring's stored entry at [cur + j] and the
   caller's buffer byte is its translation; the BOUNDARY row says the
   window the call CONSUMED is that same stored run; and
   [EchoOut.ein_read_byte] places that byte in the ERA'S INPUT at the
   reader's own delivered count.  Stated at index 0, which is the only one
   the era's law reaches and the only one sh's [gets] copies. *)
Lemma rr_byte_of_rows (D : list (bv 8) -> Prop)
    (sl sl' ws dl : list (list mobs * bv 8)) (hs : list (list mobs))
    (pops : list LogEntryDefs.log_entry)
    (I J : list (bv 8)) (dd dc : nat) (g : nat -> bv 8) :
  (* THE DISCIPLINE'S ONE READING (lane LINK-GEN-5): the ring's
     translation is the identity on it, which is the whole of what the
     byte's identity needs.  echo passes [disc_input_no_cr]; the file its
     own twin. *)
  (forall (I0 : list (bv 8)) (j : nat),
     D I0 -> (j < length I0)%nat -> cons_xlate (I0 !!! j) = I0 !!! j) ->
  (0 < dd)%nat -> (dd <= dc)%nat ->
  cons_window sl (length I) dd g hs ->
  sl `prefix_of` sl' ->
  (forall j : nat, (j < dc)%nat -> ws !! j = sl' !! (length I + j)%nat) ->
  (dl ++ ws) `prefix_of` echoed pops ->
  length dl = length I ->
  (snd <$> (dl ++ ws)) = I ++ J ->
  D (I ++ J) ->
  (0 < length J)%nat ->
  g 0%nat = J !!! 0%nat.
Proof using.
  intros Hncr Hdd Hdc Hwin Hpre Hws Hpr Hdl Hcat Hdisc HJ.
  destruct Hwin as (_ & _ & Hwj).
  destruct (Hwj 0%nat Hdd) as (hh & b & Hsl & _ & _ & Hg).
  assert (Hsl' : sl' !! (length I + 0)%nat = Some (hh, b))
    by (eapply prefix_lookup_Some; [ exact Hsl | exact Hpre ]).
  assert (Hw0 : ws !! 0%nat = Some (hh, b))
    by (rewrite (Hws 0%nat ltac:(lia)); exact Hsl').
  pose proof (ein_read_byte pops dl ws (length I) (hh, b) Hpr Hdl Hw0) as Hb.
  cbn [snd] in Hb.
  assert (Hidx : (I ++ J) !!! (length I)%nat = J !!! 0%nat).
  { rewrite !list_lookup_total_alt.
    rewrite (lookup_app_r I J (length I) ltac:(lia)) Nat.sub_diag.
    reflexivity. }
  rewrite Hg Hb Hcat. rewrite <- Hidx.
  apply (Hncr (I ++ J) (length I) Hdisc).
  rewrite length_app. lia.
Qed.

(* ===================================================================== *)
(*  THE RECORD                                                            *)
(* ===================================================================== *)
Section readrec.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context `{HRg : !riscvGS Σ}.
  Context `{!uartGhostG Σ}.
  (* the era's own generation, which is where [rk_arms] is pinned: a
     reader's residue names the era's FILE state at [S gen_id]
     ([FileLinksLine.f0w]), so the window arm is stated there and not at an
     arbitrary [k].  The two LINK fields stay generic in [k]. *)
  Context `{GEN : GenId}.

  Record ReadRec (L : LinkRec Σ) := MkReadRec {
    (* the INPUT's discipline -- [UkSh.ush_read_ans_at]'s parameter *)
    rk_disc : list (bv 8) -> Prop;

    (* the era's READ LINK: one answer to [WpUart.cons_link]'s atomic
       update at the ring's [EvRead] event *)
    rk_rd : forall (k n : nat) (v : era_pins)
                   (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
      ⊢ lk_links L -∗ lk_pin L k v -∗ dl_cnt v (1/2) n -∗
        (lk_rr L k v n ws -∗ Φ) -∗
        cons_link Uart0 k (ConsLog.EvRead ws) Φ;

    (* ...and its TAINT route: on a tainted turn the reader holds no half
       of the delivered count and the link is free.  AT THE ERA'S OWN
       NUMBER: the taint may license one era only (the union's wild token,
       seccomp design 10.7), and a tainted lease holds no pin to name it *)
    rk_rd_taint : forall (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
      ⊢ lk_links L -∗ lk_T L -∗ (lk_T L -∗ Φ) -∗
        cons_link Uart0 (S gen_id) (ConsLog.EvRead ws) Φ;

    (* THE WINDOW ARM, at exactly what [UShLine.ush_read_recv_era]
       consumes: the call moved the era's input on by the [dc] bytes [J],
       the byte it DELIVERED is the first of them, the input so far is
       DISCIPLINED, and the reader's residue is at the far end. *)
    (* ...AND IT IS HANDED THE CONSUMED BYTES' TAGS (the PROGRAM STREAM,
       stretch 9).  The residue is the ONLY thing of an era's that rides in
       the shell's mid-line pieces, and an input byte's tag
       ([RiscvPtsto.riscv_rx_tag]) is the only place an era's RX-side
       ledger ever speaks to a program -- the file era's tag carries the
       lower bound of the typed line list ([FileOut.ftag]), which is how a
       line reaches the child that writes it to `f`.  The window names the
       DELIVERED bytes' tags ([hs]); a SWALLOWED byte extends the input
       too, and its tag is inside [UserConsole.ucons_swallow], so the arm
       takes both rows as the console member hands them over.  An era with
       nothing to read off a tag ignores all three. *)
    rk_arms : forall (cn : cons_names) (v : era_pins) (I : list (bv 8))
                (ws sl sl' : list (list mobs * bv 8))
                (hs : list (list mobs)) (dd dc : nat) (g : nat -> bv 8),
      (dd <= dc)%nat -> length ws = dc ->
      cons_window sl (length I) dd g hs ->
      sl `prefix_of` sl' ->
      (forall j : nat, (j < dc)%nat -> ws !! j = sl' !! (length I + j)%nat) ->
      ⊢ lk_epin L (S gen_id) v -∗ inp_lb v I -∗ lk_rres L v I -∗
        lk_rr L (S gen_id) v (length I) ws -∗
        ([∗ list] hh ∈ hs, riscv_rx_tag hh) -∗
        ucons_swallow cn False sl dd dc -∗
        ucons_stored_lb cn sl' -∗
        (dl_cnt v (1/2) (length I + dc)%nat
         ∗ ∃ J : list (bv 8),
             ⌜length J = dc⌝ ∗ ⌜rk_disc (I ++ J)⌝
             ∗ ⌜(0 < dd)%nat -> g 0%nat = J !!! 0%nat⌝
             ∗ inp_lb v (I ++ J) ∗ lk_rres L v (I ++ J))
        ∨ lk_T L;
  }.

End readrec.

(* NO [Global Arguments] HERE: the record's parameter [L] stays EXPLICIT on
   every projection, as [LinkRec]'s own fields keep theirs ([lk_pin L k v]),
   so a reader never has to guess which era a law is at. *)

(* ===================================================================== *)
(*  THE ECHO INSTANCE, DEFINITIONALLY (LinkRec's pattern).                *)
(* ===================================================================== *)
Section echo_read_inst.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{HPT : !Persistent T} `{HTT : !Timeless T}.
  Context `{HRg : !riscvGS Σ}.
  Context `{!uartGhostG Σ}.
  Context `{GEN : GenId}.

  Local Notation LE := (echo_link_inst T γ).

  Local Lemma eri_rd (k n : nat) (v : era_pins)
      (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
    ⊢ EchoLinks.echo_links T γ -∗ era_pin γ k v -∗ dl_cnt v (1/2) n -∗
      (read_ret T k v n ws -∗ Φ) -∗
      cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using .
    iIntros "#Hlk #Hpin Hdl HΦ".
    iDestruct (EchoLinks.echo_links_rd with "Hlk") as "#Hrdl".
    iApply ("Hrdl" $! k v n ws with "Hpin Hdl HΦ").
  Qed.

  Local Lemma eri_rd_taint (ws : list (list mobs * bv 8))
      (Φ : iProp Σ) :
    ⊢ EchoLinks.echo_links T γ -∗ T -∗ (T -∗ Φ) -∗
      cons_link Uart0 (S gen_id) (ConsLog.EvRead ws) Φ.
  Proof using .
    iIntros "#Hlk HT HΦ".
    iDestruct (EchoLinks.echo_links_rd_taint with "Hlk") as "#Hrdt".
    iApply ("Hrdt" $! (S gen_id) ws with "HT HΦ").
  Qed.

  (* [UShLine.ush_read_recv_era]'s own era block, as a law.  The input at
     the window's far end EXTENDS the lease's, because both are lower
     bounds of one echoed list ([EchoOut.inp_lb_cmp]) and the lease's is
     the shorter; the residue comes off the receipt where a byte was
     delivered and off the lease where the count did not move. *)
  Local Lemma eri_arms (cn : cons_names) (v : era_pins) (I : list (bv 8))
      (ws sl sl' : list (list mobs * bv 8))
      (hs : list (list mobs)) (dd dc : nat) (g : nat -> bv 8) :
    (dd <= dc)%nat -> length ws = dc ->
    cons_window sl (length I) dd g hs ->
    sl `prefix_of` sl' ->
    (forall j : nat, (j < dc)%nat -> ws !! j = sl' !! (length I + j)%nat) ->
    ⊢ era_pin γ (S gen_id) v -∗ inp_lb v I -∗ echo_rres v I -∗
      read_ret T (S gen_id) v (length I) ws -∗
      ([∗ list] hh ∈ hs, riscv_rx_tag hh) -∗
      ucons_swallow cn False sl dd dc -∗
      ucons_stored_lb cn sl' -∗
      (dl_cnt v (1/2) (length I + dc)%nat
       ∗ ∃ J : list (bv 8),
           ⌜length J = dc⌝ ∗ ⌜disc_input (I ++ J)⌝
           ∗ ⌜(0 < dd)%nat -> g 0%nat = J !!! 0%nat⌝
           ∗ inp_lb v (I ++ J) ∗ echo_rres v (I ++ J))
      ∨ T.
  Proof using HPT.
    intros Hddc Hlws Hwinf Hpre2 Hwsj.
    iIntros "#Hpin #HE0 #Hres0 Hret _ _ _".
    rewrite /read_ret.
    iDestruct "Hret" as "[[#HT _] | [Hdlr Hfacts]]"; [ by iRight | ].
    iDestruct "Hfacts" as (pops dl)
      "(%Hrok & %Hdl & %Hpref & %Hidx & %Hdsce & #HEin & %Hdinp & Hrest)".
    iEval (rewrite Hlws) in "Hdlr".
    (* THE INPUT AT THE FAR END EXTENDS THE LEASE'S *)
    iDestruct (inp_lb_cmp v I (snd <$> (dl ++ ws)) with "HE0 HEin") as %Hcmp.
    assert (Hlen' : length (snd <$> (dl ++ ws)) = (length I + dc)%nat).
    { rewrite length_fmap length_app Hdl Hlws. reflexivity. }
    assert (Hpre' : I `prefix_of` (snd <$> (dl ++ ws))).
    { destruct Hcmp as [Hc | Hc]; [ exact Hc | ].
      pose proof (prefix_length _ _ Hc) as Hle.
      assert (Hdc0 : dc = 0%nat) by lia.
      assert (Heq : (snd <$> (dl ++ ws)) = I).
      { apply (list_eq_same_length _ _ (length I)); [ lia | lia | ].
        intros i x y Hi Hx Hy.
        pose proof (prefix_lookup_Some _ _ i x Hx Hc) as Hxy.
        rewrite Hxy in Hy. by injection Hy as <-. }
      rewrite Heq. done. }
    destruct Hpre' as [J HJ].
    assert (HJlen : length J = dc)
      by (rewrite HJ length_app in Hlen'; lia).
    assert (HJdisc : disc_input (I ++ J)) by (rewrite <- HJ; exact Hdinp).
    iDestruct "Hrest" as "#Hrest".
    iAssert (echo_rres v (I ++ J)) as "#Hresn".
    { iDestruct "Hrest" as "[%Hws0 | Hbb]".
      - assert (Hdc0 : dc = 0%nat)
          by (rewrite <- Hlws, Hws0; reflexivity).
        assert (HJnil : J = []) by (apply nil_length_inv; lia).
        rewrite HJnil app_nil_r. iExact "Hres0".
      - iDestruct "Hbb" as (cs0 ps0) "(#Hcs & #Hps & _ & #Htlb & %Hrds)".
        rewrite /echo_rres. iExists ps0, cs0.
        rewrite <- HJ. iFrame "Htlb Hps Hcs". by iPureIntro. }
    iAssert (inp_lb v (I ++ J)) as "#HEn";
      [ rewrite <- HJ; iExact "HEin" | ].
    iLeft. iFrame "Hdlr". iExists J.
    iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
    iSplitR; [ | iFrame "HEn Hresn" ].
    iPureIntro. intro Hdd0.
    exact (rr_byte_of_rows disc_input sl sl' ws dl hs pops I J dd dc g
             disc_input_no_cr
             Hdd0 Hddc Hwinf Hpre2 Hwsj Hpref Hdl HJ HJdisc ltac:(lia)).
  Qed.

  Definition echo_read_inst : ReadRec LE :=
    MkReadRec LE disc_input eri_rd eri_rd_taint eri_arms.

  (* ---- the definitional checks ---- *)
  Lemma echo_read_inst_disc : rk_disc LE echo_read_inst = disc_input.
  Proof using . reflexivity. Qed.

End echo_read_inst.
