(* ZZFloorProbe.v -- THE FLOOR PROBE (tso-machine-flip.md A6.82).

   THIS IS THE STANDALONE FORM OF WHAT LANDED AS [TsoMemPa.v] §12d, kept
   here (beside ZZRacyProbe / ZZWinProbe / ZZPinProbe) so the ruling's
   pure argument can be re-run against a bare [TsoMemPa.vo] without the
   rest of the tree.

   The coordinator's ruling on A6.81 §(4): the window payload gains a
   FLOOR [Bm] -- the position of the MINT STORE itself -- and [wpin] /
   [own_last] constrain only messages AT OR ABOVE it, so a kalloc'd
   page's pre-mint garbage is unconstrained.  The reader pays with the
   stable pair [hart_view_lb K ∗ ⌜Bm ≤ K⌝].

   WHAT IT SHOWS, and it is the ruling's claim: a reader whose view has
   passed the floor cannot see below it -- the mint store TOUCHED the
   window and is visible at every such view, so [read_down] settles at or
   above [Bm] and every candidate it could settle on is gate-mediated.

   AND WHAT IT ADDS TO THE SKETCH: [win_ok] has to be relativised too.
   xv6's [memset] is a byte loop, so [kfree]'s [memset(pa, 1, PGSIZE)]
   appends PGSIZE ONE-BYTE messages and each writes a proper subset of
   the window -- so the whole-window-or-none property is FALSE below the
   floor at exactly the cell this ruling exists for, and the REASSEMBLY
   ([read_down_win]) takes it at every timestamp.  [read_down_win_fl]
   below is that re-proof: same induction, base case moved to the floor.

   TO RE-RUN it needs a [TsoMemPa] WITHOUT §12d (every name below is
   exported from there now, so against the current one it clashes):

     git show <pre-A6.82>:iris/TsoMemPa.v  -- or any tree at A6.81 --
     then, in that tree's iris/:
     coqc -w -notation-overridden -R . xv6iris -R ../model-xv6iris Riscv \
          -R ../kernel-rocq Kernel -R ../user-rocq User ZZFloorProbe.v
     # then rm the .v/.vo/.vos/.vok/.glob/.aux out of iris/

   Against the CURRENT tree the same audit is one line per name:
   [Print Assumptions TsoMemPa.read_down_win_fl.] and its eleven
   siblings, which is what the numbers below were taken from.

   All twelve results print [Closed under the global context]; no
   [Admitted], no [admit], no [Axiom]. *)
From Stdlib Require Import ZArith Lia List.
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap list bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import TsoMemPa.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* §12d.1  AT ONE BYTE.                                                  *)
(* ===================================================================== *)

Section floor_byte.
  Variable img : gmap Arch.pa (bv 8).
  Variable log : list pwmsg.

  (* "among the messages AT OR ABOVE the floor, h's last write to [a] is
     at most [t]".  [own_last] is the [Bm = 0] case -- every timestamp is
     at or above 0 -- so nothing below this file has to move. *)
  Definition own_last_fl (Bm : nat) (h : agent) (a : Arch.pa) (t : nat) : Prop :=
    forall i m, (Bm <= S i)%nat -> log !! i = Some m -> pm_tid m = h ->
      is_Some (msg_byte m a) -> (S i <= t)%nat.

  Definition writer_pin_fl (Bm : nat) (a : Arch.pa)
      (Sf : agent -> bv 8 -> Prop) : Prop :=
    forall i m c, (Bm <= S i)%nat -> log !! i = Some m ->
      msg_byte m a = Some c -> Sf (pm_tid m) c.

  (* the unrelativised forms ARE the floor-0 instances *)
  Lemma own_last_fl_0 (h : agent) (a : Arch.pa) (t : nat) :
    own_last log h a t <-> own_last_fl 0 h a t.
  Proof.
    split.
    - move => Ho i m _ Hlk Htid Hs. exact (Ho i m Hlk Htid Hs).
    - move => Ho i m Hlk Htid Hs. exact (Ho i m ltac:(lia) Hlk Htid Hs).
  Qed.

  Lemma writer_pin_fl_0 (a : Arch.pa) (Sf : agent -> bv 8 -> Prop) :
    writer_pin log a Sf <-> writer_pin_fl 0 a Sf.
  Proof.
    split.
    - move => Hw i m c _ Hlk Hb. exact (Hw i m c Hlk Hb).
    - move => Hw i m c Hlk Hb. exact (Hw i m c ltac:(lia) Hlk Hb).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* (1) THE SHADOW.  A view past the floor cannot resolve below it --    *)
  (* the floor message is visible there ([visibleb_below]) and it WRITES  *)
  (* the byte, so [read_down]'s scan is stopped at or above it.  This is  *)
  (* the whole content of the ruling, and it is [read_down_latest] at     *)
  (* [t' := Bm].                                                          *)
  (* ------------------------------------------------------------------ *)
  Lemma read_down_shadow (h : agent) (tv Bm : nat) (a : Arch.pa) (bm : bv 8) :
    (Bm <= tv)%nat -> (Bm <= length log)%nat ->
    log_byte img log Bm a = Some bm ->
    exists (T : nat) (v : bv 8),
      (Bm <= T)%nat
      /\ tso_read img log h tv a = Some v
      /\ visibleb h tv log T = true
      /\ log_byte img log T a = Some v.
  Proof.
    move => Htv Hlen Hbm.
    have Hvis : visibleb h tv log Bm = true by (apply visibleb_below; lia).
    have [T [v [Hge [Hrd [Hv Hb]]]]] :=
      read_down_latest img log h tv a (length log) Bm bm Hlen Hvis Hbm.
    exists T, v. by rewrite /tso_read.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* (2) [racy_read_split] RELATIVISED.  Same statement, same proof, one  *)
  (* extra [lia] at each of the two uses: the timestamp the read settles  *)
  (* on is >= the ANCHOR [t], and the anchor is >= the floor, so both     *)
  (* gates apply to it.                                                   *)
  (* ------------------------------------------------------------------ *)
  Lemma racy_read_split_fl (h : agent) (a : Arch.pa) (tv Bm t : nat)
      (v b : bv 8) (Sf : agent -> bv 8 -> Prop) :
    (Bm <= t)%nat ->
    (t <= length log)%nat ->
    visibleb h tv log t = true ->
    log_byte img log t a = Some v ->
    own_last_fl Bm h a t ->
    writer_pin_fl Bm a Sf ->
    tso_read img log h tv a = Some b ->
    b = v \/ exists h', h' <> h /\ Sf h' b.
  Proof.
    move => Hfl Hlen Hvis Hb Ho Hw Hrd.
    destruct (read_down_latest img log h tv a (length log) t v Hlen Hvis Hb)
      as (t'' & v'' & Hle & Hrd'' & Hvis'' & Hb'').
    rewrite /tso_read Hrd'' in Hrd. injection Hrd as <-.
    destruct (decide (t'' = t)) as [->|Hne].
    { left. rewrite Hb'' in Hb. by injection Hb as <-. }
    right.
    destruct t'' as [|i]; first lia.
    rewrite /log_byte in Hb''.
    destruct (log !! i) as [m|] eqn:Hlk; last done.
    exists (pm_tid m). split.
    - move => Htid.
      have := Ho i m ltac:(lia) Hlk Htid ltac:(by eexists). lia.
    - exact (Hw i m _ ltac:(lia) Hlk Hb'').
  Qed.

  (* the ANCHOR a non-writer supplies: it never wrote at or above the
     floor, so its own-last IS the floor.  This is the premise the
     [notheld] reader can actually hold, and the one the unrelativised
     kit could not give it (A6.81 §(4)). *)
  Lemma own_last_fl_anchor (Bm : nat) (h : agent) (a : Arch.pa) :
    (forall i m, (Bm <= S i)%nat -> log !! i = Some m -> pm_tid m = h ->
       msg_byte m a = None) ->
    own_last_fl Bm h a Bm.
  Proof.
    move => Hno i m Hge Hlk Htid Hs.
    rewrite /is_Some (Hno i m Hge Hlk Htid) in Hs. by destruct Hs as [? ?].
  Qed.

  (* ---- MAINTENANCE: the frame arms are the unrelativised ones with a
     hypothesis DROPPED, which is why nothing above this file moves. ---- *)
  Lemma own_last_fl_app_frame (Bm : nat) (m : pwmsg) (h : agent)
      (a : Arch.pa) (t : nat) :
    own_last_fl Bm h a t ->
    (pm_tid m = h -> msg_byte m a = None) ->
    (forall i m0, (Bm <= S i)%nat -> (log ++ [m]) !! i = Some m0 ->
       pm_tid m0 = h -> is_Some (msg_byte m0 a) -> (S i <= t)%nat).
  Proof.
    move => Ho Hfr i m0 Hge Hlk Htid Hs.
    apply lookup_app_Some in Hlk. destruct Hlk as [Hlk | [Hge2 Hlk]].
    - exact (Ho i m0 Hge Hlk Htid Hs).
    - destruct (i - length log)%nat as [|k] eqn:Hk; cbn in Hlk; last done.
      injection Hlk as <-. rewrite /is_Some (Hfr Htid) in Hs.
      by destruct Hs as [? ?].
  Qed.

  Lemma writer_pin_fl_app (Bm : nat) (m : pwmsg) (a : Arch.pa)
      (Sf : agent -> bv 8 -> Prop) :
    writer_pin_fl Bm a Sf ->
    (forall c, msg_byte m a = Some c -> Sf (pm_tid m) c) ->
    (forall i m0 c, (Bm <= S i)%nat -> (log ++ [m]) !! i = Some m0 ->
       msg_byte m0 a = Some c -> Sf (pm_tid m0) c).
  Proof.
    move => Hw Hm i m0 c Hge Hlk Hb.
    apply lookup_app_Some in Hlk. destruct Hlk as [Hlk | [Hge2 Hlk]].
    - exact (Hw i m0 c Hge Hlk Hb).
    - destruct (i - length log)%nat as [|k] eqn:Hk; cbn in Hlk;
        [ injection Hlk as <-; by apply Hm | done ].
  Qed.

End floor_byte.

(* ===================================================================== *)
(* §12d.2  AT THE WINDOW -- the shape the lock's owner cell needs.        *)
(* ===================================================================== *)

Section floor_window.
  Variable img : gmap Arch.pa (bv 8).
  Variable log : list pwmsg.
  Variable a : Arch.pa.
  Variable n : nat.
  Hypothesis Hn : (0 < n)%nat.

  Local Notation find_top := (find_top img log a).

  (* ================================================================== *)
  (* [win_ok] MUST BE RELATIVISED TOO, AND THAT IS THE PART THE RULING's *)
  (* SKETCH DOES NOT COVER.                                             *)
  (*                                                                    *)
  (* [TsoMemPa.read_down_win] -- the reassembly that makes ONE timestamp *)
  (* serve every byte of the window -- takes [win_ok] at EVERY           *)
  (* timestamp, and below the floor that is FALSE for exactly the cell   *)
  (* this whole ruling exists for: xv6's [memset] is a BYTE LOOP         *)
  (* ([string.c]: [for (i = 0; i < n; i++) cdst[i] = c;]), so [kfree]'s  *)
  (* [memset(pa, 1, PGSIZE)] appends PGSIZE one-byte messages and every  *)
  (* one of them writes a PROPER SUBSET of the window.  A floor that     *)
  (* relativised only [wpin] and [own_last] would leave the reassembly   *)
  (* unprovable, so the floor has to reach [win_ok] as well.             *)
  (*                                                                    *)
  (* THAT IT STILL GOES THROUGH IS THE SECOND HALF OF THIS PROBE, and    *)
  (* the reason is the same shadow: the scan never descends below the    *)
  (* floor, so it only ever compares timestamps the relativised          *)
  (* [win_ok_fl] speaks about.                                           *)
  (* ================================================================== *)
  Definition win_ok_fl (Bm : nat) : Prop :=
    forall t : nat, (Bm <= t)%nat ->
      (forall j, (j < n)%nat -> is_Some (log_byte img log t (pa_add a j)))
      \/ (forall j, (j < n)%nat -> log_byte img log t (pa_add a j) = None).

  Lemma win_ok_fl_0 : win_ok img log a n <-> win_ok_fl 0.
  Proof.
    split.
    - move => Hw t _. exact (Hw t).
    - move => Hw t. exact (Hw t ltac:(lia)).
  Qed.

  (* THE RELATIVISED REASSEMBLY.  [read_down_win]'s proof, with the
     induction stopped at the floor: at [t = Bm] the floor message is
     visible ([Bm <= tv]) and writes every byte, so the scan halts there
     and never asks [win_ok] about anything below. *)
  Lemma read_down_win_fl (h : agent) (tv Bm t j : nat) :
    win_ok_fl Bm -> (j < n)%nat -> (Bm <= tv)%nat -> (Bm <= t)%nat ->
    (forall k, (k < n)%nat -> is_Some (log_byte img log Bm (pa_add a k))) ->
    read_down img log h tv (pa_add a j) t
    = match find_top h tv t with
      | Some T => log_byte img log T (pa_add a j)
      | None => None
      end.
  Proof.
    move => Hw Hj Htv. elim: t => [|t IH] Hge Hfl.
    - (* t = 0, so the floor is 0 and the image writes the window *)
      have HB : Bm = 0%nat by lia.
      rewrite HB in Hfl.
      rewrite read_down_0 find_top_0.
      have Hv : visibleb h tv log 0 = true by (apply visibleb_below; lia).
      rewrite Hv.
      have [b0 Hb0] := Hfl 0%nat ltac:(lia).
      rewrite Hb0. move: Hb0. rewrite /log_byte. by move => _.
    - case: (decide (Bm = S t)) => [HB|Hne].
      + (* the floor itself: it is visible and it writes every byte *)
        rewrite read_down_S find_top_S.
        have Hv : visibleb h tv log (S t) = true
          by (apply visibleb_below; lia).
        rewrite Hv.
        rewrite HB in Hfl.
        have [b0 Hb0] := Hfl 0%nat ltac:(lia).
        have [bj Hbj] := Hfl j Hj.
        by rewrite Hb0 Hbj.
      + (* above the floor: [read_down_win]'s step, verbatim *)
        have Hge' : (Bm <= t)%nat by lia.
        rewrite read_down_S find_top_S.
        case Ev : (visibleb h tv log (S t)); last by rewrite (IH Hge' Hfl).
        case E0 : (log_byte img log (S t) (pa_add a 0)) => [b0|].
        * case: (Hw (S t) ltac:(lia)) => Hall.
          -- have [bj Hbj] := Hall j Hj. by rewrite Hbj.
          -- have := Hall 0%nat ltac:(lia). by rewrite E0.
        * case: (Hw (S t) ltac:(lia)) => Hall.
          -- have := Hall 0%nat ltac:(lia). rewrite E0. by move => [? ?].
          -- have := Hall j Hj => ->. by rewrite (IH Hge' Hfl).
  Qed.

  Definition wpin_fl (Bm : nat)
      (Wf : agent -> (nat -> option (bv 8)) -> Prop) : Prop :=
    forall i m, (Bm <= S i)%nat -> log !! i = Some m ->
      is_Some (msg_byte m (pa_add a 0)) ->
      Wf (pm_tid m) (fun j => msg_byte m (pa_add a j)).

  (* ------------------------------------------------------------------ *)
  (* THE THEOREM, RELATIVISED.  [racy_read_window]'s proof verbatim, with *)
  (* the [own_last] use carrying the floor bound the anchor supplies.     *)
  (* ------------------------------------------------------------------ *)
  Lemma racy_read_window_fl (h : agent) (tv Bm t : nat) :
    win_ok_fl Bm ->
    (Bm <= tv)%nat ->
    (forall k, (k < n)%nat -> is_Some (log_byte img log Bm (pa_add a k))) ->
    (Bm <= t)%nat ->
    (t <= length log)%nat ->
    visibleb h tv log t = true ->
    (forall j, (j < n)%nat -> is_Some (log_byte img log t (pa_add a j))) ->
    (forall j, (j < n)%nat -> own_last_fl log Bm h (pa_add a j) t) ->
    exists T : nat,
      (t <= T)%nat
      /\ (forall j, (j < n)%nat ->
            tso_read img log h tv (pa_add a j) = log_byte img log T (pa_add a j))
      /\ (T = t \/ exists i m, T = S i /\ log !! i = Some m /\ pm_tid m <> h
                            /\ (Bm <= S i)%nat
                            /\ is_Some (msg_byte m (pa_add a 0))).
  Proof.
    move => Hw Htv Hcov Hfl Hlen Hvis Hsome Ho.
    have [T [HT Hge]] :=
      find_top_max img log a n Hn h tv (length log) t Hlen Hvis (Hsome 0%nat ltac:(lia)).
    exists T. split; first done.
    split.
    { move => j Hj.
      rewrite /tso_read
        (read_down_win_fl h tv Bm (length log) j Hw Hj Htv ltac:(lia) Hcov) HT //. }
    case: (decide (T = t)) => [->|Hne]; first by left.
    right.
    have [Hle [Hv [b0 Hb0]]] := find_top_spec img log a n Hn h tv (length log) T HT.
    case ET : T => [|i]; first lia.
    move: Hb0. rewrite ET /log_byte.
    case El : (log !! i) => [m|]; last by [].
    move => Hb0. exists i, m. split_and!; [done|done| |lia|by eexists].
    move => Htid.
    have := Ho 0%nat ltac:(lia) i m ltac:(lia) El Htid ltac:(by eexists).
    lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE READER'S OWN ANCHOR IS THE FLOOR ITSELF, and this is the step    *)
  (* the ruling turns on: the MINT STORE wrote the whole window at [Bm],  *)
  (* a reader whose view has passed [Bm] sees it, and a reader that never *)
  (* wrote at or above the floor therefore resolves EXACTLY at [Bm]       *)
  (* unless someone else wrote above it.  No premise about the cell's     *)
  (* history BELOW the floor appears anywhere.                            *)
  (* ------------------------------------------------------------------ *)
  Lemma racy_read_window_floor (h : agent) (tv Bm : nat) :
    win_ok_fl Bm ->
    (Bm <= tv)%nat ->
    (Bm <= length log)%nat ->
    (forall j, (j < n)%nat -> is_Some (log_byte img log Bm (pa_add a j))) ->
    (forall i m, (Bm <= S i)%nat -> log !! i = Some m -> pm_tid m = h ->
       msg_byte m (pa_add a 0) = None) ->
    exists T : nat,
      (Bm <= T)%nat
      /\ (forall j, (j < n)%nat ->
            tso_read img log h tv (pa_add a j) = log_byte img log T (pa_add a j))
      /\ (T = Bm \/ exists i m, T = S i /\ log !! i = Some m /\ pm_tid m <> h
                             /\ (Bm <= S i)%nat
                             /\ is_Some (msg_byte m (pa_add a 0))).
  Proof.
    move => Hw Htv Hlen Hsome Hno.
    apply (racy_read_window_fl h tv Bm Bm Hw Htv Hsome ltac:(lia) Hlen
             ltac:(apply visibleb_below; lia) Hsome).
    (* the anchor: [own_last_fl] at [Bm] for every byte of the window.
       [win_ok] carries "writes byte 0" to "writes byte j", so the ONE
       hypothesis about byte 0 serves the whole window. *)
    move => j Hj i m Hge Hlk Htid Hs.
    exfalso.
    have Hb0 : msg_byte m (pa_add a 0) = None by exact (Hno i m Hge Hlk Htid).
    case: (Hw (S i) ltac:(lia)) => Hall.
    - have := Hall 0%nat ltac:(lia). rewrite /log_byte Hlk Hb0. by move => [? ?].
    - have := Hall j Hj. rewrite /log_byte Hlk.
      move => Heq. rewrite Heq in Hs. by destruct Hs as [? ?].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE GATE-MEDIATED FORM, at the floor: whatever the read settles on is *)
  (* either the MINT STORE's own word or a message by someone else that    *)
  (* the RELATIVISED [wpin] speaks about.  Nothing below [Bm] appears.     *)
  (* ------------------------------------------------------------------ *)
  Lemma racy_read_window_pin_fl (h : agent) (tv Bm : nat)
      (Wf : agent -> (nat -> option (bv 8)) -> Prop) :
    win_ok_fl Bm -> wpin_fl Bm Wf ->
    (Bm <= tv)%nat ->
    (Bm <= length log)%nat ->
    (forall j, (j < n)%nat -> is_Some (log_byte img log Bm (pa_add a j))) ->
    (forall i m, (Bm <= S i)%nat -> log !! i = Some m -> pm_tid m = h ->
       msg_byte m (pa_add a 0) = None) ->
    (forall j, (j < n)%nat ->
       tso_read img log h tv (pa_add a j) = log_byte img log Bm (pa_add a j))
    \/ (exists (h' : agent) (m : pwmsg),
          h' <> h /\ pm_tid m = h'
          /\ Wf h' (fun j => msg_byte m (pa_add a j))
          /\ forall j, (j < n)%nat ->
               tso_read img log h tv (pa_add a j) = msg_byte m (pa_add a j)).
  Proof.
    move => Hw Hp Htv Hlen Hsome Hno.
    have [T [Hge [Hrd Harm]]] :=
      racy_read_window_floor h tv Bm Hw Htv Hlen Hsome Hno.
    case: Harm => [HTeq|[i [m [HTeq [El [Htid [Hge2 Hb0]]]]]]].
    - left. move => j Hj. rewrite (Hrd j Hj) HTeq //.
    - right. exists (pm_tid m), m. split_and!.
      + by move => ?; apply Htid.
      + done.
      + exact (Hp i m Hge2 El Hb0).
      + move => j Hj. rewrite (Hrd j Hj) HTeq /log_byte El //.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE CONSUMER: [lkcpu_not_mine] AT A FLOOR.  A hart that has not      *)
  (* touched the lock since the mint, and whose view has passed the mint, *)
  (* provably does not read its OWN cpus_ptr -- the answer [holding()]    *)
  (* answer and the whole reason the racy kit exists.  Compare the        *)
  (* unrelativised [TsoMemPa.lkcpu_not_mine]: the premise                 *)
  (* [log_byte img log t] is the clear word at an anchor [t] the reader   *)
  (* itself wrote -- is replaced by: the MINT STORE wrote it at [Bm], plus *)
  (* the receipt [Bm <= tv] -- and THAT is the premise a hart which has   *)
  (* never touched the lock can hold.                                    *)
  (* ------------------------------------------------------------------ *)
  Lemma lkcpu_not_mine_fl (h : agent) (tv Bm : nat)
      (z : nat -> bv 8) (cp : agent -> nat -> bv 8) :
    win_ok_fl Bm ->
    wpin_fl Bm
      (fun j f => (forall k, (k < n)%nat -> f k = Some (z k))
               \/ (forall k, (k < n)%nat -> f k = Some (cp j k))) ->
    (Bm <= tv)%nat ->
    (Bm <= length log)%nat ->
    (* the MINT STORE wrote the clear word over the whole window *)
    (forall j, (j < n)%nat -> log_byte img log Bm (pa_add a j) = Some (z j)) ->
    (* the reader has not written the cell since *)
    (forall i m, (Bm <= S i)%nat -> log !! i = Some m -> pm_tid m = h ->
       msg_byte m (pa_add a 0) = None) ->
    (exists k, (k < n)%nat /\ z k <> cp h k) ->
    (forall h', h' <> h -> exists k, (k < n)%nat /\ cp h' k <> cp h k) ->
    exists k, (k < n)%nat /\ tso_read img log h tv (pa_add a k) <> Some (cp h k).
  Proof.
    move => Hw Hp Htv Hlen Hz Hno [k0 [Hk0 Hzk]] Hinj.
    have Hsome : forall j, (j < n)%nat -> is_Some (log_byte img log Bm (pa_add a j))
      by move => j Hj; rewrite (Hz j Hj); by eexists.
    destruct (racy_read_window_pin_fl h tv Bm _ Hw Hp Htv Hlen Hsome Hno)
      as [Hown | (h' & m & Hne & Htid & HW & Hrd)].
    - exists k0. split; first done.
      rewrite (Hown k0 Hk0) (Hz k0 Hk0). move => [Heq]. exact (Hzk Heq).
    - case: HW => [Hcl | Hme].
      + exists k0. split; first done.
        rewrite (Hrd k0 Hk0) (Hcl k0 Hk0). move => [Heq]. exact (Hzk Heq).
      + have [k [Hk Hd]] := Hinj h' Hne.
        exists k. split; first done.
        rewrite (Hrd k Hk) (Hme k Hk). move => [Heq]. exact (Hd Heq).
  Qed.

End floor_window.

(* ===================================================================== *)
(* §12d.3 THE DEGENERATE CASE: the floor-0 instance IS the boot mint, and *)
(* its receipt is free ([TsoGhost.view_lb_0] in Iris; [0 <= tv] here).    *)
(* So the eight .bss callers pay nothing for the relativisation.          *)
(* ===================================================================== *)

Lemma lkcpu_not_mine_floor0 (img : gmap Arch.pa (bv 8)) (log : list pwmsg)
    (a : Arch.pa) (n : nat) (h : agent) (tv : nat)
    (z : nat -> bv 8) (cp : agent -> nat -> bv 8) :
  (0 < n)%nat ->
  win_ok img log a n ->
  wpin_fl log a 0
    (fun j f => (forall k, (k < n)%nat -> f k = Some (z k))
             \/ (forall k, (k < n)%nat -> f k = Some (cp j k))) ->
  (forall j, (j < n)%nat -> img !! (pa_add a j) = Some (z j)) ->
  (forall i m, log !! i = Some m -> pm_tid m = h ->
     msg_byte m (pa_add a 0) = None) ->
  (exists k, (k < n)%nat /\ z k <> cp h k) ->
  (forall h', h' <> h -> exists k, (k < n)%nat /\ cp h' k <> cp h k) ->
  exists k, (k < n)%nat /\ tso_read img log h tv (pa_add a k) <> Some (cp h k).
Proof.
  move => Hn Hw Hp Hz Hno Hzk Hinj.
  apply (lkcpu_not_mine_fl img log a n Hn h tv 0 z cp
           ltac:(by apply (win_ok_fl_0 img log a n)) Hp
           ltac:(lia) ltac:(lia)
           ltac:(move => j Hj; rewrite /log_byte; exact (Hz j Hj))
           ltac:(move => i m _ Hlk Htid; exact (Hno i m Hlk Htid))
           Hzk Hinj).
Qed.

(* ===================================================================== *)
(* THE AUDIT.                                                            *)
(* ===================================================================== *)
Print Assumptions read_down_shadow.
Print Assumptions win_ok_fl_0.
Print Assumptions read_down_win_fl.
Print Assumptions racy_read_split_fl.
Print Assumptions own_last_fl_anchor.
Print Assumptions own_last_fl_app_frame.
Print Assumptions writer_pin_fl_app.
Print Assumptions racy_read_window_fl.
Print Assumptions racy_read_window_floor.
Print Assumptions racy_read_window_pin_fl.
Print Assumptions lkcpu_not_mine_fl.
Print Assumptions lkcpu_not_mine_floor0.
