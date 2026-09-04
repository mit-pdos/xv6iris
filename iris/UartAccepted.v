(* UartAccepted.v -- THE SAFETY TIE between the observable trace and the
   ACCEPTED-BYTE HISTORY the console specs are stated over.

   [ObsTrace.v] proves the trace's SHAPE a step invariant of the semantics
   and ties the current cycle's output projection to the device's [u_wire]
   ([obs_wf]'s third conjunct).  This file adds the other half of the
   sentence a console spec needs, in the direction the owner ruled for
   [claude-notes/projects/uart-trace.md] -- SAFETY, "no unaccepted byte
   ever appears":

     every [ObsUartOut] byte of the current power cycle is a byte the
     kernel ACCEPTED into the UART, in order, and nothing else is there:

       obs_wire (open_seg h)  `sublist_of`  uart_acc (duart (gdev g))

   [uart_acc] ([DevModel.v]) is precisely the object the campaign's
   receipts are lower bounds of: [WpUart.uart_sent γ tr] is
   [own _ (◯ML tr)] against [uart_sent_auth γ u = own _ (●ML (uart_acc u))],
   and [UartSentLoc.uart_sent_from γ tr0 bs] is a located refinement of the
   same list.  So this theorem is what turns a receipt about [uart_acc]
   into a statement about what the HOST SAW -- see [run_out_accepted_from]
   at the end, which is that composition at the pure level.

   WHY IT IS A SUBLIST AND NOT A PREFIX.  A byte accepted into the transmit
   FIFO reaches the wire on the device thread's own later step, and under
   LOOP ([uart_loopback], MCR bit 4) it never reaches the wire at all -- it
   goes back into this UART's own receiver with SOUT held marking.  An FCR
   write can also CLEAR the transmit FIFO, dropping bytes that were accepted
   and never sent.  So the wire is a SUBLIST of the accepted history, and
   the invariant that carries this is stated one step below, on the device:

       out_wire_ok u  :=  u_wire u `sublist_of` u_out u

   ([u_out] is what the transmitter has finished with; [uart_acc = u_out ++
   u_tx], so [u_out] is a prefix of it).  That form is what survives an FCR
   clear, which shortens [u_tx] and touches neither of these two.

   WHY THERE IS NO LEDGER HERE.  The trace ledger's per-event wands
   ([WpUart.uart_obs_permit_ledger]) are quantified over an ARBITRARY
   [γ : uart_names] and an ARBITRARY [u : uart_state], so a client's [R]
   can learn nothing about the era's acceptance at an event that it did not
   already know; the acceptance content of the trace is a PURE step
   invariant of the language, and that is where it belongs -- exactly as
   [obs_wf] is.  What the ledger is needed for is an ERA-ATTACHED fact (a
   receipt at a particular [γ]), and that waits on uart-trace.md's open
   "identification gate".  See the header of [run_out_accepted_from].

   A LEAF below the Iris layer, like [ObsTrace.v]: nothing rebuilds under
   it. *)

From stdpp Require Import gmap finite relations list bitvector.definitions.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import RiscvLang.
Require Import ObsTrace.

(* ---------------------------------------------------------------------- *)
(* 1. [u_out] is carried by everything that is not the drain, exactly as    *)
(*    [u_wire] is ([ObsTrace.v] section 1).  The two lists move TOGETHER,   *)
(*    which is what makes the sublist below an invariant.                   *)
(* ---------------------------------------------------------------------- *)

(* the per-register facts are DevModel's own ([uart_read_stable]'s second
   projection and [uart_write_out]); only the bus lift is new *)
Lemma dev_read_u_out (d : dev_state) (pa : Arch.pa) (n : N)
    (w : bv (8 * n)) (d' : dev_state) :
  dev_read d pa n = Some (w, d') -> u_out (duart d') = u_out (duart d).
Proof.
  unfold dev_read, uart_dev_read. intros H.
  repeat (case_match; try discriminate); simplify_eq; cbn;
    first [ reflexivity
          | by match goal with
               | H : uart_read _ _ = Some _ |- _ =>
                   destruct (uart_read_stable _ _ _ _ H) as (_ & ? & _)
               end ].
Qed.

Lemma dev_write_u_out (d : dev_state) (pa : Arch.pa) (n : N)
    (v : bv (8 * n)) (d' : dev_state) :
  dev_write d pa n v = Some d' -> u_out (duart d') = u_out (duart d).
Proof.
  unfold dev_write, uart_dev_write. intros H.
  repeat (case_match; try discriminate); simplify_eq; cbn;
    first [ reflexivity | by eapply uart_write_out ].
Qed.

(* the twin of [ObsTrace.mnode_step_u_out]'s [u_wire] version: a hart node
   reaches the UART only through the bus *)
Lemma mnode_step_u_out oth h img s log tv itv r m m' s' log' tv' itv' r' :
  mnode_step oth h img s log tv itv r m m' s' log' tv' itv' r' ->
  u_out (duart (mdev s')) = u_out (duart (mdev s)).
Proof.
  rewrite /mnode_step. destruct m as [y|T oc k].
  { by intros (tick & _ & -> & _). }
  destruct oc; simpl;
    try (by intros (_ & -> & _)); try (by intros []).
  - (* MemRead *)
    destruct (dev_addr _).
    + intros (w & d' & Hdr & _ & -> & _). cbn.
      exact (dev_read_u_out _ _ _ _ _ Hdr).
    + by intros [(_ & tvn & w & _ & _ & _ & _ & -> & _)
                |[(_ & _ & tvn & w & _ & _ & _ & _ & -> & _)
                 |(_ & [(_ & _ & -> & _) | (_ & w & _ & _ & -> & _)])]].
  - (* MemWrite *)
    destruct (dev_addr _).
    + intros (d' & Hdw & _ & -> & _). cbn.
      exact (dev_write_u_out _ _ _ _ _ Hdw).
    + by intros [(_ & _ & -> & _) | (_ & _ & -> & _)].
  - (* Choose *) by intros (ch & _ & -> & _).
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE DEVICE INVARIANT: nothing reaches the wire that the transmitter   *)
(*    did not finish with, in order.                                       *)
(* ---------------------------------------------------------------------- *)

Definition out_wire_ok (u : uart_state) : Prop :=
  u_wire u `sublist_of` u_out u.

(* a fresh UART has neither *)
Lemma out_wire_ok_uart0 : out_wire_ok uart0_state.
Proof. rewrite /out_wire_ok /=. apply stdpp.list_relations.sublist_nil_l. Qed.

(* THE DRAIN, the one transition that moves either list: the popped byte is
   appended to [u_out] always and to [u_wire] only when it really left the
   chip, so the sublist survives both arms. *)
Lemma uart_tx_pop_out_wire_ok (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_tx_pop u = Some (b, u') -> out_wire_ok u -> out_wire_ok u'.
Proof.
  intros Hpop Hok.
  pose proof (uart_tx_pop_wire _ _ _ Hpop) as Hw.
  pose proof (uart_tx_pop_out _ _ _ Hpop) as Ho.
  rewrite /out_wire_ok Hw Ho.
  destruct (uart_loopback u).
  - (* under LOOP the wire stands still while [u_out] grows *)
    by apply stdpp.list_relations.sublist_inserts_r.
  - apply stdpp.list_relations.sublist_app; [exact Hok | reflexivity].
Qed.

(* ...and what it says about the ACCEPTED history, which is [u_out] followed
   by whatever is still queued *)
Lemma out_wire_ok_acc (u : uart_state) :
  out_wire_ok u -> u_wire u `sublist_of` uart_acc u.
Proof.
  intros Hok. rewrite /uart_acc. etrans; [exact Hok|].
  by apply stdpp.list_relations.sublist_inserts_r.
Qed.

Lemma uart_step_out_wire_ok (d : dev_state) (κ : list mobs) (d' : dev_state) :
  uart_step d κ d' -> out_wire_ok (duart d) -> out_wire_ok (duart d').
Proof.
  intros H Hok. destruct H as [b u' Htx | b u' Hrx | p' _ _ |].
  - cbn [duart set_duart]. exact (uart_tx_pop_out_wire_ok _ _ _ Htx Hok).
  - cbn [duart set_duart]. rewrite /out_wire_ok.
    rewrite (uart_rx_push_wire _ _ _ Hrx).
    by rewrite (uart_rx_push_out _ _ _ Hrx).
  - by cbn [duart set_dplic].
  - exact Hok.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. ...AS A STEP INVARIANT OF THE MACHINE.  Conditioned on the power,     *)
(*    exactly like [obs_wf]'s wire tie: a powered-off machine's UART is     *)
(*    whatever the last cycle left (and its wire is not observed), and a    *)
(*    PowerOn resets it to [uart0_state].                                   *)
(* ---------------------------------------------------------------------- *)

Definition gout_wire_ok (g : gstate) : Prop :=
  g.(gpow) = true -> out_wire_ok (duart g.(gdev)).

Lemma gout_wire_ok_off (g : gstate) : g.(gpow) = false -> gout_wire_ok g.
Proof. intros Hpw Hon. by rewrite Hpw in Hon. Qed.

Lemma prim_step_gout_wire_ok e g κ e' g' efs :
  prim_step e g κ e' g' efs -> gout_wire_ok g -> gout_wire_ok g'.
Proof.
  intros Hstep Hok.
  destruct Hstep as
    [ (gen & cpu & m & -> & -> & _ & [ (_ & Hn) | (_ & _ & ->) ])
    | [ (gen & -> & _ & _ & [ ([Hpw Hgen] & d' & Hu & ->) | (_ & -> & ->) ])
    | [ (gen & -> & _ & -> & _ & [ (_ & d' & W & log' & Hd & _ & _ & ->) | (_ & ->) ])
    | [ (gen & -> & _ & -> & _ & [ (_ & gr' & _ & ->) | (_ & ->) ])
    | (-> & _ & [ (Hpw & -> & _ & ->) | (Hpw & -> & _ & Hboot) ]) ] ] ] ];
    try exact Hok.
  - (* a hart node: it reaches the UART through the bus only, and the bus
       moves neither list *)
    destruct Hn as (m' & s' & log' & tv' & itv' & r' & Hn & _ & ->). cbn.
    intros Hon. rewrite /out_wire_ok.
    rewrite (mnode_step_u_wire _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hn)
            (mnode_step_u_out _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hn).
    exact (Hok Hon).
  - (* the UART thread: the one mover *)
    cbn. intros _. exact (uart_step_out_wire_ok _ _ _ Hu (Hok Hpw)).
  - (* the disk: it never touches the UART *)
    cbn. intros Hon. rewrite /out_wire_ok (disk_step_duart _ _ _ _ Hd).
    exact (Hok Hon).
  - (* PowerOff: nothing is observed while the power is off *)
    by intros Hon.
  - (* PowerOn: a reset UART *)
    destruct Hboot as (_ & _ & Hbf).
    destruct Hbf as (_ & _ & _ & _ & Huart & _).
    intros _. rewrite /out_wire_ok Huart. exact out_wire_ok_uart0.
Qed.

Lemma step_gout_wire_ok (ρ1 ρ2 : cfg riscv_lang) (κ : list mobs) :
  step ρ1 κ ρ2 -> gout_wire_ok ρ1.2 -> gout_wire_ok ρ2.2.
Proof.
  intros [e1 σ1 e2 σ2 efs t1 t2 -> -> Hstep] Hok. cbn.
  exact (prim_step_gout_wire_ok _ _ _ _ _ _ Hstep Hok).
Qed.

Lemma nsteps_gout_wire_ok (n : nat) (ρ1 ρ2 : cfg riscv_lang) (κs : list mobs) :
  nsteps n ρ1 κs ρ2 -> gout_wire_ok ρ1.2 -> gout_wire_ok ρ2.2.
Proof.
  intros Hn.
  induction Hn as [ρ|n ρ1 ρ2 ρ3 κ κs Hstep _ IH]; intros Hok; [exact Hok|].
  apply IH. exact (step_gout_wire_ok _ _ _ Hstep Hok).
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. THE OPEN SEGMENT OF A POWERED-OFF HISTORY IS EMPTY, which is what     *)
(*    makes the tie below unconditional: with the power off there is no     *)
(*    current cycle to talk about.                                         *)
(* ---------------------------------------------------------------------- *)

Lemma trace_shape_off_open_seg (h : list mobs) :
  trace_shape h false -> open_seg h = [].
Proof.
  rewrite /trace_shape. induction h as [|e h IH] using rev_ind; [done|].
  rewrite foldl_app. intros Hsh.
  destruct (foldl obs_step (Some false) h) as [on|] eqn:Hs; [|discriminate Hsh].
  (* only [PowerOff from on] lands in [Some false] *)
  destruct on, e; cbn in Hsh; try discriminate Hsh.
  by apply (open_seg_power h ObsPowerOff).
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. THE TIE.  Every byte the machine has put on the console wire in the   *)
(*    CURRENT power cycle was accepted by the kernel, in order -- for every *)
(*    run of the machine, under every schedule, with no logic involved.     *)
(*                                                                         *)
(*    It is a statement about a REACHED STATE, so it holds at every point   *)
(*    of every run: every prefix of an [nsteps] is an [nsteps].  That is    *)
(*    how the completed cycles are covered -- each satisfied it while it    *)
(*    was the open one.                                                    *)
(* ---------------------------------------------------------------------- *)

Theorem run_out_accepted (n : nat) (t t2 : list (expr riscv_lang))
    (g g2 : gstate) (κs : list mobs) :
  g.(gpow) = false -> g.(ggen) = 0%nat ->
  nsteps (Λ := riscv_lang) n (t, g) κs (t2, g2) ->
  obs_wire (open_seg κs) `sublist_of` uart_acc (duart g2.(gdev)).
Proof.
  intros Hpw Hgen Hn.
  pose proof (run_obs_wf n t t2 g g2 κs Hpw Hgen Hn) as (Hsh & _ & Hwire).
  pose proof (nsteps_gout_wire_ok n (t, g) (t2, g2) κs Hn
                (gout_wire_ok_off g Hpw)) as Hok.
  destruct (g2.(gpow)) eqn:Hpw2.
  - rewrite (Hwire eq_refl). exact (out_wire_ok_acc _ (Hok Hpw2)).
  - rewrite (trace_shape_off_open_seg κs Hsh) /=.
    apply stdpp.list_relations.sublist_nil_l.
Qed.

(* ---------------------------------------------------------------------- *)
(* 6. COMPOSING WITH A LOCATED RECEIPT.                                     *)
(*                                                                          *)
(*    [UartSentLoc.uart_sent_from γ tr0 bs] says: the bytes [bs] were        *)
(*    accepted, in order, at positions strictly after an accepted trace      *)
(*    that had [tr0] as a prefix.  Its PURE RESIDUE at a state -- what it    *)
(*    yields once agreed against [uart_sent_auth γ u] -- is exactly the two  *)
(*    hypotheses below, about [uart_acc u].  This lemma is what the residue  *)
(*    then buys ON THE TRACE:                                               *)
(*                                                                          *)
(*      the cycle's observable output splits at the receipt's seed, and the  *)
(*      part after the seed is a sublist of what was accepted AFTER the seed *)
(*      -- the same window [bs] lives in.                                    *)
(*                                                                          *)
(*    SAFETY ONLY (ruling 5), and deliberately so: nothing here says the     *)
(*    bytes of [bs] APPEAR on the wire -- they may still be sitting in the   *)
(*    transmit FIFO, and an FCR clear or a LOOP setting can destroy them.    *)
(*    What it says is that NO OTHER BYTE can appear in that window: any      *)
(*    output the host sees after the receipt's seed was accepted after the   *)
(*    seed, and in the accepted order.                                       *)
(*                                                                          *)
(*    THE OPEN LINK is the Iris-to-pure step that produces the two           *)
(*    hypotheses at the END of a run: it needs the era's [uart_sent_auth]    *)
(*    agreed against a receipt for THAT era's [γ], and no client resource    *)
(*    can name an era's ghosts today -- the trace ledger's wands and the     *)
(*    permit premise are quantified over an arbitrary [γ : uart_names].      *)
(*    That is uart-trace.md's open "identification gate" (the [P_era]        *)
(*    chain's), in its UART instance; see this lane's report.                *)
(* ---------------------------------------------------------------------- *)

Lemma out_accepted_split (w tr0 rest : list (bv 8)) :
  w `sublist_of` (tr0 ++ rest) ->
  exists w1 w2, w = w1 ++ w2 /\ w1 `sublist_of` tr0 /\ w2 `sublist_of` rest.
Proof. by rewrite stdpp.list_relations.sublist_app_r. Qed.

(* THE LOCATING STEP, at a single accepted history: an observed output that
   is a sublist of [acc] splits at any prefix [tr0] of [acc], and the part
   after the split lives in the receipt's own window.  Stated at a bare
   [acc] so the era side can use it at the device state an event leaves
   ([uart_acc u], out of the wand's [uart_ghosts γ u]) exactly as the run
   theorem below uses it at the reached state. *)
Lemma out_accepted_locate (w acc tr0 : list (bv 8)) :
  w `sublist_of` acc -> tr0 `prefix_of` acc ->
  exists w1 w2,
    w = w1 ++ w2 /\ w1 `sublist_of` tr0 /\ w2 `sublist_of` drop (length tr0) acc.
Proof.
  intros Hsub Hpre.
  assert (Hsplit : acc = tr0 ++ drop (length tr0) acc).
  { destruct Hpre as [k ->]. by rewrite drop_app_length. }
  rewrite Hsplit in Hsub.
  destruct (out_accepted_split _ _ _ Hsub) as (w1 & w2 & Hw & Hw1 & Hw2).
  by exists w1, w2.
Qed.

Theorem run_out_accepted_from (n : nat) (t t2 : list (expr riscv_lang))
    (g g2 : gstate) (κs : list mobs) (tr0 bs : list (bv 8)) :
  g.(gpow) = false -> g.(ggen) = 0%nat ->
  nsteps (Λ := riscv_lang) n (t, g) κs (t2, g2) ->
  (* the receipt's pure residue at the reached state *)
  tr0 `prefix_of` uart_acc (duart g2.(gdev)) ->
  bs `sublist_of` drop (length tr0) (uart_acc (duart g2.(gdev))) ->
  exists w1 w2,
    obs_wire (open_seg κs) = w1 ++ w2
    /\ w1 `sublist_of` tr0
    /\ w2 `sublist_of` drop (length tr0) (uart_acc (duart g2.(gdev)))
    /\ bs `sublist_of` drop (length tr0) (uart_acc (duart g2.(gdev))).
Proof.
  intros Hpw Hgen Hn Hpre Hbs.
  pose proof (run_out_accepted n t t2 g g2 κs Hpw Hgen Hn) as Hsub.
  destruct (out_accepted_locate _ _ _ Hsub Hpre) as (w1 & w2 & Hw & Hw1 & Hw2).
  exists w1, w2. done.
Qed.
