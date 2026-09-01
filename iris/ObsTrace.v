(* ObsTrace.v -- the PURE vocabulary of the observable trace.                *)
(*                                                                          *)
(*  The language emits four observation events (RiscvLang.mobs, §3b'):      *)
(*  ObsUartOut/ObsUartIn on the UART thread's drain/rx arms, ObsPowerOff/   *)
(*  ObsPowerOn on the power thread.  This file says what a WELL-FORMED      *)
(*  history of them looks like and proves it a STEP INVARIANT of the        *)
(*  semantics, with no Iris in it:                                          *)
(*                                                                          *)
(*    obs_wf h g  :=  trace_shape h (gpow g)                 -- alternation  *)
(*                 /\ obs_boots h = start_count g             -- boot count  *)
(*                 /\ (gpow g -> obs_wire (open_seg h) = u_wire (duart g))   *)
(*                                                            -- WIRE TIE    *)
(*                                                                          *)
(*  [prim_step_obs_wf] re-establishes it across every arm of [prim_step],   *)
(*  and [nsteps_obs_wf] lifts that to a whole run.  The Iris side           *)
(*  (claude-notes/projects/uart-trace.md) carries [obs_wf h g] as a pure     *)
(*  conjunct of [state_interp] beside [resv_ok], where [h] is the history    *)
(*  so far: the alternation is what lets a client segment [h] into power     *)
(*  cycles, and the wire tie is how a client that owns the UART's state      *)
(*  ([uart_frag u]) learns which bytes of the interleaved current cycle are  *)
(*  the ones the host actually saw.                                          *)
(*                                                                          *)
(*  [obs_wire] and the three wire lemmas were introduced with the events    *)
(*  (746c265c4) and swept as dead code before anything consumed them         *)
(*  (c1b3a6670, bdefa96e3); they are restored here, where they are used.     *)
(*  A LEAF below RiscvPtsto on purpose: nothing rebuilds under it.          *)

From stdpp Require Import gmap finite relations bitvector.definitions.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang.

(* ---------------------------------------------------------------------- *)
(* 1. The output projection, and the wire lemmas.                          *)
(*                                                                          *)
(*    [obs_wire] is a PROOF-SIDE projection only: it is what ties the        *)
(*    interleaved history to the device's [u_wire], which records outputs   *)
(*    alone.  Trace PROPERTIES are stated over the interleaved list, never   *)
(*    over the two directions separately (uart-trace.md, ruling 1).         *)
(* ---------------------------------------------------------------------- *)

(* the OUTPUT bytes of an observation list.  A direct Fixpoint (not stdpp's
   [omap]) so [cbn] reduces it on literal lists without unfolding through
   the typeclass. *)
Fixpoint obs_wire (κ : list mobs) : list (bv 8) :=
  match κ with
  | [] => []
  | ObsUartOut b :: κ' => b :: obs_wire κ'
  | _ :: κ' => obs_wire κ'
  end.

Lemma obs_wire_app (κ1 κ2 : list mobs) :
  obs_wire (κ1 ++ κ2) = obs_wire κ1 ++ obs_wire κ2.
Proof.
  induction κ1 as [|e κ1 IH]; [reflexivity|].
  destruct e; cbn; by rewrite IH.
Qed.

(* the receiver never touches SOUT *)
Lemma uart_recv_wire (u : uart_state) (b : bv 8) :
  u_wire (uart_recv u b) = u_wire u.
Proof. reflexivity. Qed.

(* What the drain step puts ON THE WIRE: the popped byte in normal mode,
   nothing under LOOP (the byte goes back into this UART's own receiver,
   with SOUT held marking).  This is the pure fact behind the language's
   UART OUTPUT OBSERVATION (RiscvLang.uart_step): the observation list of a
   drain step is exactly the wire's growth. *)
Lemma uart_tx_pop_wire (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_tx_pop u = Some (b, u') ->
  u_wire u' = if uart_loopback u then u_wire u else u_wire u ++ [b].
Proof.
  unfold uart_tx_pop. destruct (u_tx u) as [| b0 tx'] eqn:Htx; [discriminate|].
  destruct (uart_loopback u); intro H; injection H as <- <-.
  - by rewrite uart_recv_wire.
  - reflexivity.
Qed.

(* ... and a byte ARRIVING never touches the wire *)
Lemma uart_rx_push_wire (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_rx_push u b = Some u' -> u_wire u' = u_wire u.
Proof.
  unfold uart_rx_push.
  destruct (length (u_rx u) <? uart_fifo_depth)%nat; [| discriminate].
  intro H. injection H as <-. by rewrite uart_recv_wire.
Qed.

(* no MMIO access transmits anything: every [uart_read] branch and every
   [uart_write] branch carries [u_wire] through untouched (a THR write only
   QUEUES; the wire event is the device's own later drain) *)
Lemma uart_read_wire (u : uart_state) (off : Z) (b : bv 8) (u' : uart_state) :
  uart_read u off = Some (b, u') -> u_wire u' = u_wire u.
Proof.
  unfold uart_read. intros H.
  repeat (case_match; try discriminate); simplify_eq; reflexivity.
Qed.

Lemma uart_write_wire (u : uart_state) (off : Z) (b : bv 8) (u' : uart_state) :
  uart_write u off b = Some u' -> u_wire u' = u_wire u.
Proof.
  unfold uart_write. intros H.
  repeat (case_match; try discriminate); simplify_eq; reflexivity.
Qed.

(* the bus: an MMIO transaction of any width reaches the UART through
   [uart_read]/[uart_write] and the other two devices through setters that
   keep [duart] verbatim *)
Lemma dev_read_u_wire (d : dev_state) (pa : Arch.pa) (n : N)
    (w : bv (8 * n)) (d' : dev_state) :
  dev_read d pa n = Some (w, d') ->
  u_wire (duart d') = u_wire (duart d).
Proof.
  unfold dev_read, uart_dev_read. intros H.
  repeat (case_match; try discriminate); simplify_eq; cbn;
    first [ reflexivity | by eapply uart_read_wire ].
Qed.

Lemma dev_write_u_wire (d : dev_state) (pa : Arch.pa) (n : N)
    (v : bv (8 * n)) (d' : dev_state) :
  dev_write d pa n v = Some d' ->
  u_wire (duart d') = u_wire (duart d).
Proof.
  unfold dev_write, uart_dev_write. intros H.
  repeat (case_match; try discriminate); simplify_eq; cbn;
    first [ reflexivity | by eapply uart_write_wire ].
Qed.

(* THE OBSERVATIONS ARE FAITHFUL: a UART step's output observations are
   exactly the wire's growth, so the cumulative ObsUartOut trace of any
   execution IS [u_wire] -- what a console spec talks about, and what
   [VTest.serial_of] compares against QEMU.  (The input side needs no
   counterpart: an accepted byte is recorded nowhere cumulative -- the rx
   FIFO is consumed -- so [ObsUartIn] is DEFINED as the acceptance event
   rather than mirrored from state.) *)
Lemma uart_step_wire (d : dev_state) (κ : list mobs) (d' : dev_state) :
  uart_step d κ d' ->
  u_wire (duart d') = u_wire (duart d) ++ obs_wire κ.
Proof.
  intros H. destruct H as [b u' Htx | b u' Hrx | p' _ _ |].
  - cbn [duart set_duart]. rewrite (uart_tx_pop_wire _ _ _ Htx).
    destruct (uart_loopback d.(duart)); cbn [obs_wire];
      by rewrite ?app_nil_r.
  - cbn [duart set_duart]. rewrite (uart_rx_push_wire _ _ _ Hrx).
    cbn [obs_wire]. by rewrite app_nil_r.
  - cbn [duart set_dplic obs_wire]. by rewrite app_nil_r.
  - cbn [obs_wire]. by rewrite app_nil_r.
Qed.

(* a UART step's events are console I/O and nothing else *)
Definition is_io (e : mobs) : bool :=
  match e with ObsUartIn _ | ObsUartOut _ => true | _ => false end.

Lemma uart_step_io (d : dev_state) (κ : list mobs) (d' : dev_state) :
  uart_step d κ d' -> Forall (fun e => is_io e = true) κ.
Proof.
  intros H. destruct H as [b u' _ | b u' _ | p' _ _ |].
  - destruct (uart_loopback (duart d)); repeat constructor.
  - repeat constructor.
  - constructor.
  - constructor.
Qed.

(* A hart node never moves the wire: register effects and RAM accesses do
   not touch the device fabric, and an MMIO transaction goes through
   [dev_read]/[dev_write].  The twin of [RiscvLang.mnode_step_v_disk]. *)
Lemma mnode_step_u_wire oth h img s log tv r m m' s' log' tv' r' :
  mnode_step oth h img s log tv r m m' s' log' tv' r' ->
  u_wire (duart (mdev s')) = u_wire (duart (mdev s)).
Proof.
  rewrite /mnode_step. destruct m as [y|T oc k].
  { by intros (tick & _ & -> & _). }
  destruct oc; simpl;
    try (by intros (_ & -> & _)); try (by intros []).
  - (* MemRead *)
    destruct (dev_addr _).
    + intros (w & d' & Hdr & _ & -> & _). cbn.
      exact (dev_read_u_wire _ _ _ _ _ Hdr).
    + by intros [(_ & tvn & w & _ & _ & _ & _ & -> & _)
                |(_ & [(_ & _ & -> & _) | (_ & w & _ & _ & -> & _)])].
  - (* MemWrite *)
    destruct (dev_addr _).
    + intros (d' & Hdw & _ & -> & _). cbn.
      exact (dev_write_u_wire _ _ _ _ _ Hdw).
    + by intros [(_ & _ & -> & _) | (_ & _ & -> & _)].
  - (* Choose *) by intros (ch & _ & -> & _).
Qed.

(* a disk step never touches the UART: every arm rebuilds the fabric with
   [set_dvirtio]/[set_dplic], which keep [duart] verbatim *)
Lemma disk_step_duart (d : dev_state) (m : gmap Arch.pa (bv 8))
    (d' : dev_state) (m' : gmap Arch.pa (bv 8)) :
  disk_step d m d' m' -> duart d' = duart d.
Proof. intros H. destruct H; reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The shape of a history.                                               *)
(*                                                                          *)
(*    A machine starts POWERED OFF (the top-level theorems' [gpow g =        *)
(*    false]).  From there the only legal histories alternate PowerOn,       *)
(*    console I/O, PowerOff, PowerOn, ...: [obs_step] is the automaton,      *)
(*    [None] its error state, and [trace_shape h on] says the history        *)
(*    parses and leaves the power at [on].  Snoc-oriented, since the         *)
(*    machine extends the history at the right.                              *)
(* ---------------------------------------------------------------------- *)

Definition obs_step (s : option bool) (e : mobs) : option bool :=
  match s, e with
  | Some false, ObsPowerOn => Some true
  | Some true, ObsPowerOff => Some false
  | Some true, ObsUartIn _ => Some true
  | Some true, ObsUartOut _ => Some true
  | _, _ => None
  end.

Definition trace_shape (h : list mobs) (on : bool) : Prop :=
  foldl obs_step (Some false) h = Some on.

Lemma trace_shape_nil : trace_shape [] false.
Proof. reflexivity. Qed.

Lemma trace_shape_snoc (h : list mobs) (e : mobs) (on on' : bool) :
  trace_shape h on -> obs_step (Some on) e = Some on' ->
  trace_shape (h ++ [e]) on'.
Proof. rewrite /trace_shape foldl_app => -> /=. done. Qed.

Lemma trace_shape_io (h κ : list mobs) :
  trace_shape h true -> Forall (fun e => is_io e = true) κ ->
  trace_shape (h ++ κ) true.
Proof.
  intros Hh Hκ. revert h Hh.
  induction Hκ as [|e κ He _ IH]; intros h Hh; [by rewrite app_nil_r|].
  rewrite cons_middle app_assoc. apply IH.
  eapply trace_shape_snoc; [exact Hh|]. by destruct e.
Qed.

(* the boot count: how many times the power came on *)
Fixpoint obs_boots (h : list mobs) : nat :=
  match h with
  | [] => 0
  | ObsPowerOn :: h' => S (obs_boots h')
  | _ :: h' => obs_boots h'
  end.

Lemma obs_boots_app (h1 h2 : list mobs) :
  obs_boots (h1 ++ h2) = (obs_boots h1 + obs_boots h2)%nat.
Proof.
  induction h1 as [|e h1 IH]; [reflexivity|].
  destruct e; cbn; rewrite IH; lia.
Qed.

Lemma obs_boots_io (κ : list mobs) :
  Forall (fun e => is_io e = true) κ -> obs_boots κ = 0%nat.
Proof. induction 1 as [|e κ He _ IH]; [reflexivity|]. by destruct e. Qed.

(* the CURRENT power cycle's I/O: the events since the last power event.
   A power event resets it, so with the power off it is empty. *)
Definition seg_step (seg : list mobs) (e : mobs) : list mobs :=
  match e with
  | ObsPowerOn | ObsPowerOff => []
  | _ => seg ++ [e]
  end.

Definition open_seg (h : list mobs) : list mobs := foldl seg_step [] h.

Lemma open_seg_app (h κ : list mobs) :
  open_seg (h ++ κ) = foldl seg_step (open_seg h) κ.
Proof. by rewrite /open_seg foldl_app. Qed.

Lemma foldl_seg_io (seg κ : list mobs) :
  Forall (fun e => is_io e = true) κ ->
  foldl seg_step seg κ = seg ++ κ.
Proof.
  intros Hκ. revert seg.
  induction Hκ as [|e κ He _ IH]; intros seg; [by rewrite app_nil_r|].
  cbn. destruct e; try discriminate He; cbn; rewrite IH; by rewrite -app_assoc.
Qed.

Lemma open_seg_io (h κ : list mobs) :
  Forall (fun e => is_io e = true) κ ->
  open_seg (h ++ κ) = open_seg h ++ κ.
Proof. intros Hκ. rewrite open_seg_app. by apply foldl_seg_io. Qed.

Lemma open_seg_power (h : list mobs) (e : mobs) :
  is_io e = false -> open_seg (h ++ [e]) = [].
Proof. intros He. rewrite open_seg_app. by destruct e. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. THE STEP INVARIANT.  [start_count g] (RiscvPtsto) is spelled out      *)
(*    here so that this file stays below the Iris layer.                    *)
(* ---------------------------------------------------------------------- *)

Definition obs_wf (h : list mobs) (g : gstate) : Prop :=
  trace_shape h g.(gpow)
  /\ obs_boots h = (g.(ggen) + (if g.(gpow) then 1 else 0))%nat
  /\ (g.(gpow) = true -> obs_wire (open_seg h) = u_wire (duart g.(gdev))).

(* the powered-off, never-booted machine every top-level theorem starts at *)
Lemma obs_wf_init (g : gstate) :
  g.(gpow) = false -> g.(ggen) = 0%nat -> obs_wf [] g.
Proof.
  intros Hpw Hgen. split_and!.
  - rewrite Hpw. exact trace_shape_nil.
  - by rewrite Hpw Hgen.
  - by rewrite Hpw.
Qed.

Lemma prim_step_obs_wf e g κ e' g' efs (h : list mobs) :
  prim_step e g κ e' g' efs -> obs_wf h g -> obs_wf (h ++ κ) g'.
Proof.
  intros Hstep (Hsh & Hbt & Hwire).
  destruct Hstep as
    [ (gen & cpu & m & -> & -> & _ & [ (_ & Hn) | (_ & _ & ->) ])
    | [ (gen & -> & _ & _ & [ ([Hpw Hgen] & d' & Hu & ->) | (_ & -> & ->) ])
    | [ (gen & -> & _ & -> & _ & [ (_ & d' & W & log' & Hd & _ & _ & ->) | (_ & ->) ])
    | [ (gen & -> & _ & -> & _ & [ (_ & gr' & _ & ->) | (_ & ->) ])
    | (-> & _ & [ (Hpw & -> & _ & ->) | (Hpw & -> & _ & Hboot) ]) ] ] ] ];
    try (rewrite app_nil_r; by split_and!).
  - (* a hart node: silent, and it never moves the wire *)
    rewrite app_nil_r. destruct Hn as (m' & s' & log' & tv' & r' & Hn & _ & ->). cbn.
    split_and!; [exact Hsh|exact Hbt|].
    intros Hpw. rewrite (Hwire Hpw). symmetry.
    exact (mnode_step_u_wire _ _ _ _ _ _ _ _ _ _ _ _ _ Hn).
  - (* the UART: its events extend the open cycle, and by exactly what
       reached the wire *)
    pose proof (uart_step_io _ _ _ Hu) as Hio. cbn.
    rewrite Hpw in Hsh Hbt Hwire. cbn in Hbt.
    split_and!.
    + rewrite Hpw. by apply trace_shape_io.
    + rewrite Hpw obs_boots_app (obs_boots_io _ Hio). cbn. lia.
    + intros _. rewrite (open_seg_io _ _ Hio) obs_wire_app (Hwire eq_refl).
      symmetry. exact (uart_step_wire _ _ _ Hu).
  - (* the disk: silent, and it never touches the UART *)
    rewrite app_nil_r. cbn. split_and!; [exact Hsh|exact Hbt|].
    intros Hpw. rewrite (Hwire Hpw). by rewrite (disk_step_duart _ _ _ _ Hd).
  - (* PowerOff *)
    cbn. rewrite Hpw in Hsh Hbt. cbn in Hbt. split_and!.
    + eapply trace_shape_snoc; [exact Hsh|reflexivity].
    + rewrite obs_boots_app. cbn. lia.
    + discriminate.
  - (* PowerOn: the next cycle opens empty, over a reset UART *)
    destruct Hboot as (Hgen & _ & Hbf).
    destruct Hbf as (Hpw' & _ & _ & _ & Huart & _).
    rewrite Hpw in Hsh Hbt. cbn in Hbt. rewrite /obs_wf Hpw' Hgen. split_and!.
    + eapply trace_shape_snoc; [exact Hsh|reflexivity].
    + rewrite obs_boots_app. cbn. lia.
    + intros _. rewrite (open_seg_power _ ObsPowerOn eq_refl) Huart.
      reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. THE WHOLE RUN, with no Iris: a machine that starts powered off emits *)
(*    a well-formed history, whatever the schedule.  What the adequacy      *)
(*    theorem adds is the per-cycle CONTENT, which only the logic can       *)
(*    supply; the shape is the semantics' own.                             *)
(* ---------------------------------------------------------------------- *)

Lemma step_obs_wf (ρ1 ρ2 : cfg riscv_lang) (κ : list mobs) (h : list mobs) :
  step ρ1 κ ρ2 -> obs_wf h ρ1.2 -> obs_wf (h ++ κ) ρ2.2.
Proof.
  intros [e1 σ1 e2 σ2 efs t1 t2 -> -> Hstep] Hwf. cbn.
  exact (prim_step_obs_wf _ _ _ _ _ _ _ Hstep Hwf).
Qed.

Lemma nsteps_obs_wf (n : nat) (ρ1 ρ2 : cfg riscv_lang) (κs : list mobs)
    (h : list mobs) :
  nsteps n ρ1 κs ρ2 -> obs_wf h ρ1.2 -> obs_wf (h ++ κs) ρ2.2.
Proof.
  intros Hn. revert h.
  induction Hn as [ρ|n ρ1 ρ2 ρ3 κ κs Hstep _ IH]; intros h Hwf.
  - by rewrite app_nil_r.
  - rewrite app_assoc. apply IH. exact (step_obs_wf _ _ _ _ Hstep Hwf).
Qed.

Theorem run_obs_wf (n : nat) (t t2 : list (expr riscv_lang)) (g g2 : gstate)
    (κs : list mobs) :
  g.(gpow) = false -> g.(ggen) = 0%nat ->
  nsteps (Λ := riscv_lang) n (t, g) κs (t2, g2) ->
  obs_wf κs g2.
Proof.
  intros Hpw Hgen Hn.
  exact (nsteps_obs_wf _ _ _ _ [] Hn (obs_wf_init _ Hpw Hgen)).
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. THE PER-CYCLE VIEW.  A trace property is stated over the WHOLE       *)
(*    interleaved history (uart-trace.md, ruling 1); this is the derived    *)
(*    reading a client uses when its property happens to be per power      *)
(*    cycle: [cycles_of h] is the console I/O of every cycle so far, in     *)
(*    order, the current (open) one last.  Kept as a fold in REVERSE (most  *)
(*    recent cycle first, so extending the open cycle is a [cons] case) and *)
(*    reversed for reading.                                                 *)
(* ---------------------------------------------------------------------- *)

Definition cyc_step (cs : list (list mobs)) (e : mobs) : list (list mobs) :=
  match e with
  | ObsPowerOn => [] :: cs
  | ObsPowerOff => cs
  | _ => match cs with [] => [[e]] | c :: cs' => (c ++ [e]) :: cs' end
  end.

Definition cycles_rev (h : list mobs) : list (list mobs) := foldl cyc_step [] h.
Definition cycles_of (h : list mobs) : list (list mobs) := rev (cycles_rev h).

Lemma cycles_rev_app (h κ : list mobs) :
  cycles_rev (h ++ κ) = foldl cyc_step (cycles_rev h) κ.
Proof. by rewrite /cycles_rev foldl_app. Qed.

(* while the power is on, the most recent cycle IS the open segment *)
Lemma trace_shape_cycles (h : list mobs) :
  trace_shape h true -> exists cs, cycles_rev h = open_seg h :: cs.
Proof.
  rewrite /trace_shape /cycles_rev /open_seg.
  induction h as [|e h IH] using rev_ind; [discriminate|].
  rewrite !foldl_app. intros Hsh.
  destruct (foldl obs_step (Some false) h) as [on|] eqn:Hs;
    [|discriminate Hsh].
  destruct on.
  - destruct (IH eq_refl) as (cs & Hcs). rewrite Hcs.
    destruct e; cbn in Hsh |- *; try discriminate Hsh; by eexists.
  - destruct e; cbn in Hsh |- *; try discriminate Hsh. by eexists.
Qed.

Lemma cycles_of_on (h : list mobs) :
  cycles_of (h ++ [ObsPowerOn]) = cycles_of h ++ [[]].
Proof. by rewrite /cycles_of cycles_rev_app /=. Qed.

Lemma cycles_of_off (h : list mobs) :
  cycles_of (h ++ [ObsPowerOff]) = cycles_of h.
Proof. by rewrite /cycles_of cycles_rev_app. Qed.

(* a console event extends the open cycle, and only it *)
Lemma cycles_of_io (h κ : list mobs) :
  trace_shape h true -> Forall (fun e => is_io e = true) κ ->
  exists cs, cycles_of h = cs ++ [open_seg h] /\
             cycles_of (h ++ κ) = cs ++ [open_seg h ++ κ].
Proof.
  intros Hsh Hκ. destruct (trace_shape_cycles _ Hsh) as (cs & Hcs).
  exists (rev cs). rewrite /cycles_of cycles_rev_app Hcs. split.
  { done. }
  assert (Hf : forall c κ', Forall (fun e => is_io e = true) κ' ->
                foldl cyc_step (c :: cs) κ' = (c ++ κ') :: cs).
  { intros c κ' Hκ'. revert c.
    induction Hκ' as [|e κ' He _ IH]; intros c; [by rewrite app_nil_r|].
    destruct e; try discriminate He; cbn; rewrite IH; by rewrite -app_assoc. }
  rewrite (Hf _ _ Hκ). done.
Qed.
