(* ConsLog: the console UART's accepted-input log, the pure vocabulary of
   E5's boundary contract (claude-notes/projects/app-echo.md, "E5 -- THE
   CONSOLE I/O CLAIM").  An entry is (h, c, cs): the history the byte was
   received at (obs_ends_in Uart0 h c), the byte, and what the kernel put on
   the wire for it.  Nothing of the kernel's ring is here. *)

(* ---------------------------------------------------------------------- *)
(*  THE DEFINITIONS BELOW ARE THE COORDINATOR'S CANONICAL TEXT (names,     *)
(*  argument order, clause order) and are shared with lane CONS-IO, which  *)
(*  writes this same file in another checkout; the coordinator merges.     *)
(*  ANY LEMMA GOES BELOW THEM.  [echo_of] and [cons_erase] MOVE here from  *)
(*  SpecConsoleintr.v (CONS-IO makes that file import this one and deletes  *)
(*  its copies); this file never mentions SpecConsoleintr.                 *)
(* ---------------------------------------------------------------------- *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
(* the Sail machine-word vocabulary [echo_of]/[cons_erase] are spelled in
   ([mword], [eq_vec], [mword_of_int]); the same four lines ConsoleInv.v
   takes for [cons_xlate]. *)
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.        (* [mobs], [Uart0] (via DevModel) *)
Require Import ObsTrace.         (* [obs_ends_in], [hist_ext] *)
Require Export LogEntryDefs. (* [log_entry], [le_hist], [le_byte],
                                [le_echo] -- this file's own entry type,
                                split out for [RiscvPtsto].  EXPORT: every
                                existing importer reads them here.     *)
(* after the imports, before any definition -- the Sail imports leave
   string_scope on top and `++` would elaborate as String.append (CONS-IO, F1) *)
Local Open Scope list_scope.

Definition echo_of (c : bv 8) : bv 8 :=
  if eq_vec (c : mword 8) (mword_of_int 13 : mword 8)
  then (mword_of_int 10 : mword 8) else c.

Definition cons_erase (c : bv 8) : bool :=
  eq_vec (c : mword 8) (mword_of_int 21 : mword 8)
  || eq_vec (c : mword 8) (mword_of_int 8 : mword 8)
  || eq_vec (c : mword 8) (mword_of_int 127 : mword 8).

(* MOVED here from SpecConsputc.v:118 (CONS-IO makes SpecConsputc import
   ConsLog and deletes its copy): the BACKSPACE arm's three bytes *)
Definition consputc_bs : list (bv 8) :=
  [(mword_of_int 8 : mword 8); (mword_of_int 32 : mword 8);
   (mword_of_int 8 : mword 8)].

(* MOVED here from SpecConsoleintr.v:169 (ruling on CONS-IO's F10): the
   shape of what one consoleintr call echoes for [c], per arm *)
Definition cons_echo (c : bv 8) (cs : list (bv 8)) : Prop :=
  cs = [] \/ cs = [echo_of c]
  \/ (cons_erase c = true /\ exists n : nat, cs = mjoin (replicate n consputc_bs)).

(* [log_entry] and its projections MOVED DOWN to [LogEntryDefs.v]
   (re-exported above): [RiscvPtsto] names the type and nothing else
   of this file's theory. *)

(* the entries a read hands out: the echoed ones *)
Definition log_echoed (e : log_entry) : Prop := le_echo e = [echo_of (le_byte e)].

(* consecutive histories strictly increase *)
Definition hist_chain (l : list (list mobs * bv 8)) : Prop :=
  forall i h1 c1 h2 c2,
    l !! i = Some (h1, c1) -> l !! S i = Some (h2, c2) -> hist_ext h1 h2.

(* THE GAP CLAUSE: between two consecutive delivered inputs, every logged
   input either got no echo, or an erase character was logged in (h1, h2]. *)
Definition gap_ok (pops : list log_entry) (h1 h2 : list mobs) : Prop :=
  (forall e, e ∈ pops -> hist_ext h1 (le_hist e) -> hist_ext (le_hist e) h2 ->
             le_echo e = [])
  \/ (exists e, e ∈ pops /\ hist_ext h1 (le_hist e)
                /\ (le_hist e = h2 \/ hist_ext (le_hist e) h2)
                /\ cons_erase (le_byte e) = true).

(* the kernel's pure fact at a read: [ws] delivered after [dl] *)
Definition read_ok (pops : list log_entry) (dl ws : list (list mobs * bv 8)) : Prop :=
  (forall p, p ∈ ws -> exists e, e ∈ pops /\ (le_hist e, le_byte e) = p /\ log_echoed e)
  /\ hist_chain (dl ++ ws)
  /\ (forall h c, (dl ++ ws) !! 0%nat = Some (h, c) -> gap_ok pops [] h)
  /\ (forall i h1 c1 h2 c2,
        (dl ++ ws) !! i = Some (h1, c1) -> (dl ++ ws) !! S i = Some (h2, c2) ->
        gap_ok pops h1 h2).

(* the log is in arrival order and every entry is an input *)
Definition log_ok (pops : list log_entry) : Prop :=
  (forall e, e ∈ pops -> obs_ends_in Uart0 (le_hist e) (le_byte e)
                         /\ cons_echo (le_byte e) (le_echo e))
  /\ (forall i e1 e2, pops !! i = Some e1 -> pops !! S i = Some e2 ->
                     hist_ext (le_hist e1) (le_hist e2)).

(* ====================================================================== *)
(*  LEMMAS (below the canonical definitions, as the merge protocol asks)   *)
(* ====================================================================== *)

(* [log_echoed] is a list equality, so a filter may be taken over it *)
Global Instance log_echoed_dec (e : log_entry) : Decision (log_echoed e).
Proof. unfold log_echoed. apply _. Defined.

(* HOW MANY OF THE LOG'S ENTRIES WERE ECHOED -- what [cons_drop_ok]'s
   full-ring disjunct counts, AS A NAME.  Every file that consumes that
   clause takes the Sail imports, which re-export [Stdlib.List] and shadow
   stdpp's [filter] with a bool-valued one that does not typecheck at the
   [Prop]-valued [log_echoed]; naming the quantity here, where the shadow is
   already lifted, is what keeps those files from having to fight it. *)
Definition echoed_count (L : list log_entry) : nat :=
  length (base.filter log_echoed L).

Lemma echoed_count_eq (L : list log_entry) :
  echoed_count L = length (base.filter log_echoed L).
Proof. reflexivity. Qed.

(* THE ERASE RUN IS NEVER ONE GLYPH (relax-d2, K3).  An erase arm's echo is
   a whole number of [consputc_bs] triples, so it is never the single byte
   [echo_of c] a STORE arm sends -- which is what lets the store arm's
   [ca_sent = 1] clause be stated over every arm and discharged vacuously on
   the erase ones, the kill loop's early stop included. *)
Lemma cons_bs_join_length (n : nat) :
  length (mjoin (replicate n consputc_bs)) = (3 * n)%nat.
Proof.
  induction n as [| k IH]; [reflexivity |].
  assert (Hc : mjoin (replicate (S k) consputc_bs)
               = (consputc_bs ++ mjoin (replicate k consputc_bs))%list)
    by reflexivity.
  rewrite Hc, length_app, IH. cbn [length consputc_bs]. lia.
Qed.

Lemma cons_bs_join_not_single (n : nat) (x : bv 8) :
  mjoin (replicate n consputc_bs) <> [x].
Proof.
  intro He. apply (f_equal (@length (bv 8))) in He.
  rewrite cons_bs_join_length in He. cbn [length] in He. lia.
Qed.

(* ...and the same for a run SPLIT at the arm's position, which is the shape
   the kill loop's early stop is in *)
Lemma cons_bs_join_app_not_single (i n : nat) (x : bv 8) :
  ((mjoin (replicate i consputc_bs)) ++ mjoin (replicate n consputc_bs))%list
  <> [x].
Proof.
  intro He. apply (f_equal (@length (bv 8))) in He.
  rewrite length_app, !cons_bs_join_length in He. cbn [length] in He. lia.
Qed.

(* an echoed entry has a nonempty echo -- the one step that turns the gap
   clause's left disjunct into "not an echoed entry" *)
Lemma log_echoed_nonnil (e : log_entry) : log_echoed e -> le_echo e <> [].
Proof. unfold log_echoed. intros ->. discriminate. Qed.

(* the log's order is transitive, not merely consecutive *)
Lemma log_ok_lt (pops : list log_entry) (i j : nat) (e1 e2 : log_entry) :
  log_ok pops -> (i < j)%nat ->
  pops !! i = Some e1 -> pops !! j = Some e2 -> hist_ext (le_hist e1) (le_hist e2).
Proof.
  intros [_ Hstep] Hij. revert e2. induction Hij as [|j Hij IH]; intros e2 H1 H2.
  - by eapply Hstep.
  - destruct (pops !! j) as [e|] eqn:Hj.
    + eapply hist_ext_trans; [by apply IH | by eapply Hstep].
    + exfalso. apply lookup_ge_None_1 in Hj.
      apply lookup_lt_Some in H2. lia.
Qed.

(* ...and so is a read window's, which is the same fact at [hist_chain]'s
   pair shape *)
Lemma hist_chain_lt (l : list (list mobs * bv 8)) (i j : nat)
      (h1 : list mobs) (c1 : bv 8) (h2 : list mobs) (c2 : bv 8) :
  hist_chain l -> (i < j)%nat ->
  l !! i = Some (h1, c1) -> l !! j = Some (h2, c2) -> hist_ext h1 h2.
Proof.
  intros Hchain Hij. revert h2 c2. induction Hij as [|j Hij IH]; intros h2 c2 H1 H2.
  - by eapply Hchain.
  - destruct (l !! j) as [[hm cm]|] eqn:Hj.
    + eapply hist_ext_trans; [by apply (IH hm cm) | by eapply Hchain].
    + exfalso. apply lookup_ge_None_1 in Hj.
      apply lookup_lt_Some in H2. lia.
Qed.

(* CONS-IO bridge lemmas *)
(* ====================================================================== *)
(*  ONE CONTIGUOUS BLOCK, every name prefixed [cl_], so the merge with     *)
(*  ECHO-PURE's copy of everything above is an append.  These are the      *)
(*  three facts the KERNEL side of the boundary needs and nothing else:    *)
(*  what the log's high-water half buys the shift, where that mark sits    *)
(*  after an append, and that the log stays well-formed across one.        *)
(*                                                                        *)
(*  THE LOG'S TOP IS SPELLED BY INDEX, never with [last]: the Sail imports *)
(*  above bring in [Stdlib.List.last], which takes a default and shadows   *)
(*  stdpp's -- the same dodge [ObsTrace.obs_ends_in_inj] documents.        *)
(* ====================================================================== *)

(* EVERY LOGGED HISTORY IS STRICTLY BELOW [h] once the LAST one is.  This is
   exactly what [WpUart.uart_log_hi]'s two halves buy consoleintr's shift:
   the mark IS the log's top, so one comparison against the byte being
   accepted orders it against the WHOLE log -- which is the premise
   the arm's order premise asks for ([arm_ok]'s fourth clause, which
   [WpUart.in_append] used to carry per byte), and hence why a byte can be
   logged only
   once and the log is in arrival order. *)
Lemma cl_log_ok_last_ext (pops : list log_entry) (h : list mobs) :
  log_ok pops ->
  (forall el, pops !! (length pops - 1)%nat = Some el -> hist_ext (le_hist el) h) ->
  forall e, e ∈ pops -> hist_ext (le_hist e) h.
Proof.
  intros Hok Htop e He.
  apply elem_of_list_lookup_1 in He as [i Hi].
  assert (Hlen : (i < length pops)%nat) by (apply lookup_lt_Some in Hi; lia).
  destruct (lookup_lt_is_Some_2 pops (length pops - 1)%nat ltac:(lia)) as [el Hel].
  destruct (decide (i = length pops - 1)%nat) as [-> | Hne].
  - rewrite Hel in Hi. injection Hi as <-. exact (Htop el Hel).
  - apply (hist_ext_trans _ (le_hist el)); [| exact (Htop el Hel)].
    exact (log_ok_lt pops i (length pops - 1)%nat e el Hok ltac:(lia) Hi Hel).
Qed.

(* the top entry after an append IS the appended one *)
Lemma cl_top_snoc (pops : list log_entry) (e : log_entry) :
  (pops ++ [e]) !! (length (pops ++ [e]) - 1)%nat = Some e.
Proof.
  rewrite length_app. cbn [length].
  replace (length pops + 1 - 1)%nat with (length pops) by lia.
  rewrite lookup_app_r; [| lia]. by rewrite Nat.sub_diag.
Qed.

(* ...and the log stays well-formed when one such entry is appended *)
Lemma cl_log_ok_snoc (pops : list log_entry) (e : log_entry) :
  log_ok pops ->
  obs_ends_in Uart0 (le_hist e) (le_byte e) ->
  cons_echo (le_byte e) (le_echo e) ->
  (forall e', e' ∈ pops -> hist_ext (le_hist e') (le_hist e)) ->
  log_ok (pops ++ [e]).
Proof.
  intros [Hin Hch] Hends Hecho Hbelow. split.
  - intros e' He'. apply elem_of_app in He' as [He' | He'].
    + exact (Hin e' He').
    + apply elem_of_list_singleton in He' as ->. split; assumption.
  - intros i e1 e2 H1 H2.
    assert (Hi : (i < length pops)%nat).
    { apply lookup_lt_Some in H1. rewrite length_app in H1. cbn [length] in H1.
      destruct (decide (i < length pops)%nat) as [Hy | Hn]; [exact Hy | exfalso].
      assert (i = length pops) by lia. subst i.
      rewrite lookup_app_r in H2; [| lia].
      replace (S (length pops) - length pops)%nat with 1%nat in H2 by lia.
      cbn in H2. discriminate. }
    rewrite lookup_app_l in H1; [| lia].
    destruct (decide (S i < length pops)%nat) as [Hs | Hs].
    + rewrite lookup_app_l in H2; [| lia]. exact (Hch i e1 e2 H1 H2).
    + assert (S i = length pops) by lia.
      rewrite lookup_app_r in H2; [| lia].
      replace (S i - length pops)%nat with 0%nat in H2 by lia.
      cbn in H2. injection H2 as <-.
      apply Hbelow. by eapply elem_of_list_lookup_2.
Qed.

(* ====================================================================== *)
(*  THE CONSOLE HISTORY, AND THE EVENTS THAT MOVE IT  (redesign lane R1)   *)
(*                                                                        *)
(*  PURPOSE.  Today the console boundary is THREE resources -- an output   *)
(*  claim over the accepted bytes, an input claim over the log and the     *)
(*  delivered inputs, and a kernel-lent window token whose only job was to *)
(*  refute interleavings [cons.lock] already forbids.  The redesign        *)
(*  replaced them by ONE resource over the record below, and the token by  *)
(*  the record's own [ch_arm] field -- which consoleintr arm is in         *)
(*  progress, and how much of its echo has gone out.                      *)
(*                                                                        *)
(*  THIS SECTION IS THE PURE HALF, and it was wired to nothing when it     *)
(*  landed (lane R1): the three claims, their links and the token were     *)
(*  untouched, so the expensive kernel lane could be attempted against a   *)
(*  pure layer that was already proved.  Lane R2 wired it, and the three   *)
(*  claims and the token are gone.                                        *)
(*                                                                        *)
(*  THE OPEN QUESTION it was independent of -- persistent-and-split with   *)
(*  the arm in a kernel ghost, versus linear and justified by              *)
(*  [cons.lock]'s own resource -- was settled the first way                *)
(*  ([WpUart.uart_arm]).  It decided WHO PROVES [cons_ev_ok] and how; it   *)
(*  did not change what the events are or what they do to the history.     *)
(* ====================================================================== *)

(* The consoleintr arm in progress: the byte [c] was accepted at history
   [h], the echo [cs] was chosen for it, and [j] of [cs]'s bytes have
   already reached the wire.  [None] between arms. *)
(* [cons_arm] and its four projections are in [LogEntryDefs.v], which this
   file re-exports -- the ghost camera and the port ghost name the type. *)

(* [cons_hist] is in [LogEntryDefs.v], which this file re-exports: the
   fixed record's field names the type. *)

(* One ghost event per boundary step.  [EvOut] is a process byte reaching
   the wire (write(2)); [EvOpen]/[EvByte]/[EvClose] are one consoleintr
   arm -- a store arm is [EvOpen; EvByte; EvClose], a drop arm is
   [EvOpen; EvClose] at [cs = []], a kill-line arm is [EvOpen; EvByte*;
   EvClose]; [EvRead] is a consoleread handing inputs to a process. *)
Inductive cons_ev :=
  | EvOut  (b : bv 8)
  | EvOpen (h : list mobs) (c : bv 8) (cs : list (bv 8))
  | EvByte (b : bv 8)
  | EvClose
  | EvRead (ws : list (list mobs * bv 8)).

(* THE PROCESS EVENTS (seccomp design §10.2): the two a PROCESS steps the
   claim by -- a byte it writes ([EvOut]) and a read it takes ([EvRead]).
   The echo arm's [EvOpen]/[EvByte]/[EvClose] are the interrupt's.  The
   per-era WILD licence ([RiscvPtsto.ai_wild_lic]) covers these two only. *)
Definition wild_ev (ev : cons_ev) : Prop :=
  match ev with EvOut _ | EvRead _ => True | _ => False end.

Definition cons_step (H : cons_hist) (ev : cons_ev) : cons_hist :=
  match ev with
  | EvOut b => MkCH (ch_acc H ++ [b]) (ch_log H) (ch_dl H) (ch_arm H)
  | EvOpen h c cs => MkCH (ch_acc H) (ch_log H) (ch_dl H) (Some (h, c, cs, 0%nat))
  | EvByte b =>
      match ch_arm H with
      | Some (h, c, cs, j) =>
          MkCH (ch_acc H ++ [b]) (ch_log H) (ch_dl H) (Some (h, c, cs, S j))
      | None => H
      end
  | EvClose =>
      match ch_arm H with
      | Some (h, c, cs, j) =>
          MkCH (ch_acc H) (ch_log H ++ [(h, c, take j cs)]) (ch_dl H) None
      | None => H
      end
  | EvRead ws => MkCH (ch_acc H) (ch_log H) (ch_dl H ++ ws) (ch_arm H)
  end.

(* WHAT A DROP ARM ([cs = []]) OWES (relaxed discipline, D2 deleted).  A
   [consoleintr] arm that echoes nothing is one of four: a NUL byte, ^P
   (procdump), an erase byte with nothing to erase, or a FULL RING.  The
   fourth is the one the application must be able to refute from its own
   discipline, and it can only do so if the kernel says what a full ring
   MEANS in the boundary's own terms: the ring's 128 live bytes are echoed
   log entries no read has delivered, so the log has at least 128 echoed
   entries beyond the delivered ones.  (The kernel proves it from the ring's
   [cons_logged]/[cons_chain] clauses and the consumed cursor, which bounds
   the delivered count from above.) *)
Definition cons_drop_ok (c : bv 8) (L : list log_entry)
    (dl : list (list mobs * bv 8)) : Prop :=
  bv_unsigned c = 0%Z \/ bv_unsigned c = 16%Z \/ cons_erase c = true
  \/ (128 + length dl <= length (base.filter log_echoed L))%nat.

(* WHAT THE RECEIVER MAY HAVE LOST (relaxed discipline).  The log is complete
   up to ONE exception the hardware forces: uartinit's FCR write clears the
   receive FIFO, so bytes the environment pushed before the console was
   initialised are discarded and no arm ever files them.  The kernel cannot
   refute that input; it can say WHEN it happened -- before any byte reached
   the console's wire -- and how many bytes it was.  [flush_lost h f]: [f]
   inputs of this era were lost, and if any were, some prefix of the era's
   segment holds exactly those [f] inputs and NO console output.  The
   application refutes [f > 0] from its own discipline: a disciplined user
   types nothing before the first prompt, so no input precedes the first
   output. *)
Definition flush_lost (h : list mobs) (f : nat) : Prop :=
  f = 0%nat
  \/ exists sf : list mobs,
       sf `prefix_of` open_seg h /\ obs_wire Uart0 sf = []
       /\ length (obs_ins Uart0 sf) = f.

(* THE KERNEL'S PURE PREMISE at each event -- what the kernel proves from
   its own state before firing the application's link.

   [EvClose]'s [cons_echo] CLAUSE IS LOAD-BEARING AND IS NOT [j <= length
   cs].  The entry records what actually went out, [take j cs], and
   [log_ok] asks every entry's echo to be a LEGAL echo of its byte; but a
   legal echo is not prefix-closed -- the erase arm's [cs] is a multiple of
   the three bytes [consputc_bs], and stopping one or two bytes into an
   erase leaves something that is no echo of anything.  So the arm is
   stoppable exactly where its partial echo is itself legal, which is what
   the live contract already demands ([WpUart.in_claim_append] and
   [uart_inv_append] both take [ConsLog.cons_echo c cs] for the [cs] they
   file).  Stating it as [j <= length cs] would make [cons_hist_ok_step]
   below UNPROVABLE at [EvClose]. *)
Definition cons_ev_ok (H : cons_hist) (ev : cons_ev) : Prop :=
  match ev with
  | EvOut _ => True
  | EvOpen h c cs =>
      ch_arm H = None
      /\ obs_ends_in Uart0 h c
      /\ cons_echo c cs
      /\ (forall e, e ∈ ch_log H -> hist_ext (le_hist e) h)
      (* the WIRE RIDER: what the application has accounted for is already
         on the wire the kernel is about to extend *)
      /\ obs_wire Uart0 (open_seg h) `prefix_of` ch_acc H
      (* THE LOG IS COMPLETE (relaxed discipline): every input of this era
         before [c] has been popped and FILED -- the receive FIFO is drained
         in arrival order and each popped byte's arm closes before the next
         pop -- so the entry this arm will file is input number [length
         (ch_log H) + 1], up to the [f] bytes uartinit's flush lost
         ([flush_lost]).  This is what lets the application know, without
         waiting for echoes, that the echoed list is a PREFIX of the input. *)
      /\ (exists f : nat, flush_lost h f
            /\ (length (ch_log H) + 1 + f)%nat = length (obs_ins Uart0 (open_seg h)))
      (* ...AND A DROP SAYS WHY ([cons_drop_ok]) *)
      /\ (cs = [] -> cons_drop_ok c (ch_log H) (ch_dl H))
  | EvByte b => exists a, ch_arm H = Some a /\ ca_echo a !! ca_sent a = Some b
  | EvClose =>
      exists a, ch_arm H = Some a
                /\ cons_echo (ca_byte a) (take (ca_sent a) (ca_echo a))
                (* A STORE ARM SENDS ITS BYTE (relaxed discipline): the arm
                   whose echo is the byte itself closes only after that
                   byte went out, so the entry it files is ECHOED.  The
                   erase arms are stoppable early and owe nothing here. *)
                /\ (ca_echo a = [echo_of (ca_byte a)] -> ca_sent a = 1%nat)
  | EvRead ws => read_ok (ch_log H) (ch_dl H) ws
  end.

(* The arm's own well-formedness, against the log it will be filed into AND
   the accepted bytes it is echoing into.

   THE WIRE CLAUSE IS WHY [acc] IS AN ARGUMENT.  [EvOpen] takes "what the
   application has accounted for is already on the wire the kernel is about
   to extend" as a premise; the application needs it again at EVERY byte of
   the arm, and between two bytes an unrelated writer's [EvOut] may have
   grown [acc].  Carrying it here is what makes it survive: every event
   either leaves [acc] alone or appends to it, and a prefix of a list is a
   prefix of its extension. *)
Definition arm_ok (L : list log_entry) (acc : list (bv 8))
    (a : cons_arm) : Prop :=
  obs_ends_in Uart0 (ca_hist a) (ca_byte a)
  /\ cons_echo (ca_byte a) (ca_echo a)
  /\ (ca_sent a <= length (ca_echo a))%nat
  /\ (forall e, e ∈ L -> hist_ext (le_hist e) (ca_hist a))
  /\ obs_wire Uart0 (open_seg (ca_hist a)) `prefix_of` acc.

(* THE INVARIANT the port carries.  [ConsoleInv.cons_ok] is a different
   thing (the ring's three counters), hence the name. *)
Definition cons_hist_ok (H : cons_hist) : Prop :=
  log_ok (ch_log H)
  /\ from_option (arm_ok (ch_log H) (ch_acc H)) True (ch_arm H).

(* ---------------------------------------------------------------------- *)
(*  THE ONE THEOREM: the events preserve the invariant.                    *)
(* ---------------------------------------------------------------------- *)

Lemma cons_hist_ok_step (H : cons_hist) (ev : cons_ev) :
  cons_hist_ok H -> cons_ev_ok H ev -> cons_hist_ok (cons_step H ev).
Proof.
  unfold cons_hist_ok, cons_ev_ok, cons_step, arm_ok,
         ca_hist, ca_byte, ca_echo, ca_sent.
  intros [Hlog Harm] Hev. destruct ev.
  - (* EvOut: only [ch_acc] moves, and it GROWS -- which is what the arm's
       wire clause needs *)
    simpl in *. split; [exact Hlog |].
    destruct (ch_arm H) as [[[[h c] cs] j] |]; [| exact I].
    simpl in *. destruct Harm as (Hends & Hecho & Hle & Hbelow & Hwire).
    split; [exact Hends |]. split; [exact Hecho |].
    split; [exact Hle |]. split; [exact Hbelow |].
    etrans; [exact Hwire | by apply prefix_app_r].
  - (* EvOpen: the arm is founded, and its facts ARE the premises *)
    destruct Hev as (Hnone & Hends & Hecho & Hbelow & Hwire & _ & _).
    simpl in *. split; [exact Hlog |].
    split; [exact Hends |]. split; [exact Hecho |].
    split; [apply Nat.le_0_l |]. split; [exact Hbelow | exact Hwire].
  - (* EvByte: the counter advances into a byte the echo really has, so it
       stays within the echo; [ch_acc] grows, as at [EvOut] *)
    destruct Hev as (a & Ha & Hlk). destruct a as [[[h c] cs] j].
    rewrite Ha in Harm. rewrite Ha. simpl in *.
    destruct Harm as (Hends & Hecho & _ & Hbelow & Hwire).
    apply lookup_lt_Some in Hlk.
    split; [exact Hlog |].
    split; [exact Hends |]. split; [exact Hecho |].
    split; [exact Hlk |]. split; [exact Hbelow |].
    etrans; [exact Hwire | by apply prefix_app_r].
  - (* EvClose: the entry is filed, and the arm's facts are exactly
       [cl_log_ok_snoc]'s premises *)
    destruct Hev as (a & Ha & Hpre & _). destruct a as [[[h c] cs] j].
    rewrite Ha in Harm. rewrite Ha. simpl in *.
    destruct Harm as (Hends & _ & _ & Hbelow & _).
    split; [| exact I].
    exact (cl_log_ok_snoc (ch_log H) (h, c, take j cs) Hlog Hends Hpre Hbelow).
  - (* EvRead: only [ch_dl] moves *)
    simpl in *. split; [exact Hlog |].
    destruct (ch_arm H) as [[[[h c] cs] j] |]; [| exact I]. exact Harm.
Qed.

(* The log only ever grows, and only at [EvClose]. *)
Lemma cons_step_log (H : cons_hist) (ev : cons_ev) :
  exists suf, ch_log (cons_step H ev) = ch_log H ++ suf.
Proof.
  destruct ev; simpl.
  - exists nil. rewrite app_nil_r. reflexivity.
  - exists nil. rewrite app_nil_r. reflexivity.
  - destruct (ch_arm H) as [[[[h c] cs] j] |];
      (exists nil; rewrite app_nil_r; reflexivity).
  - destruct (ch_arm H) as [[[[h c] cs] j] |].
    + exists (cons (h, c, take j cs) nil). reflexivity.
    + exists nil. rewrite app_nil_r. reflexivity.
  - exists nil. rewrite app_nil_r. reflexivity.
Qed.
