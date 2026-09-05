(** * TsoLitmus.v — executable litmus programs over the relaxed view machine

    A tiny hart-program language (NOT Sail) on top of [TsoMem]'s two-log
    view machine, plus the litmus suite that is a standing obligation of the
    memory model: every verdict here is the model's answer, and a change
    to [TsoMem] that flips one is a design change.

    THE VERDICTS, after the R→R relaxation
    (claude-notes/completed/relaxed-rr.md) and the W→W relaxation
    (claude-notes/projects/relaxed-ww.md §1.2).  The machine keeps R→W
    order and a single drain order (multi-copy atomicity), and relaxes
    load–load and store–store order; so among the classical shapes:

      SB                       allowed      (store buffering)
      SB + fence rw,rw both    forbidden    (the drain: a W-fence waits)
      MP, no fences            ALLOWED      (the reader reorders)
      MP + writer w,w only     ALLOWED      (the reader reorders)
      MP + reader r,r only     ALLOWED      (flipped: the WRITER reorders)
      MP + w,w / r,r fences    forbidden    (the release and the acquire)
      MP + addr dependency     ALLOWED      (dependencies are NOT modelled)
      CoRR                     forbidden    (the per-byte coherence floor)
      CoWW                     forbidden    (per-byte FIFO drain)
      LB                       forbidden    (R→W kept — stronger than RVWMO)
      IRIW, no fences          ALLOWED
      IRIW + r,r both readers  forbidden    (one drain log: multi-copy atomic)
      n6                       allowed      (the buffer drains late)
      2+2W                     ALLOWED      (flipped: stores drain out of order)
      S                        ALLOWED      (flipped)
      store; amoswap.aq /
        amoswap.aq; load       ALLOWED      (flipped: no .rl, no fence)
      store; fence rw,w; store /
        amoswap.aq; load       forbidden    (the xv6 lock handoff)
      pending store vs AMO     the store lands AFTER the AMO
      AMO plain (no .aq)       ALLOWED      (the floor does not move)

    Every FORBIDDEN verdict comes with a reachability witness (the shape it
    quantifies over is reached with the verdict's hypotheses satisfied), so
    none is vacuous.  Like [TsoMem.v] this file imports only stdpp. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite relations list.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import TsoMem.

(* ------------------------------------------------------------------ *)
(** ** Bytes, addresses, registers

    Everything is a literal so that the concrete side conditions reduce by
    computation. *)

Definition b0 : bv 8 := Z_to_bv 8 0.
Definition b1 : bv 8 := Z_to_bv 8 1.
Definition b2 : bv 8 := Z_to_bv 8 2.

Lemma b0_ne_b1 : b0 ≠ b1.
Proof. intros H. apply (f_equal bv_unsigned) in H. by vm_compute in H. Qed.
Lemma b0_ne_b2 : b0 ≠ b2.
Proof. intros H. apply (f_equal bv_unsigned) in H. by vm_compute in H. Qed.
Lemma b1_ne_b2 : b1 ≠ b2.
Proof. intros H. apply (f_equal bv_unsigned) in H. by vm_compute in H. Qed.

(** The three litmus addresses and the four litmus registers.  [az] sits at
    address 1 so that the BYTE [b1] read out of a pointer cell IS its
    address — what the MP+addr test needs. *)
Local Notation ax := (0%Z).
Local Notation az := (1%Z).
Local Notation ay := (8%Z).
Local Notation rg1 := (1%nat).
Local Notation rg2 := (2%nat).
Local Notation rg3 := (3%nat).
Local Notation rg4 := (4%nat).

(** The era-initial image: all three litmus bytes read as 0 at timestamp 0. *)
Definition img0m : gmap Z (bv 8) := <[ax := b0]> (<[az := b0]> {[ay := b0]}).
(** [TsoMem.image] is a partial FUNCTION on [Z] (the [gmap Arch.pa _]
    Countable trap); the litmus image is still built as a map. *)
Definition img0 : image := λ a, img0m !! a.

Lemma img0_x : img0 ax = Some b0.
Proof. rewrite /img0 /img0m lookup_insert //. Qed.
Lemma img0_z : img0 az = Some b0.
Proof. rewrite /img0 /img0m lookup_insert_ne // lookup_insert //. Qed.
Lemma img0_y : img0 ay = Some b0.
Proof.
  rewrite /img0 /img0m lookup_insert_ne // lookup_insert_ne // lookup_singleton //.
Qed.
Lemma img0_x_nb1 : img0 ax ≠ Some b1.
Proof. rewrite img0_x. intros H. apply b0_ne_b1. congruence. Qed.
Lemma img0_x_nb2 : img0 ax ≠ Some b2.
Proof. rewrite img0_x. intros H. apply b0_ne_b2. congruence. Qed.
Lemma img0_y_nb1 : img0 ay ≠ Some b1.
Proof. rewrite img0_y. intros H. apply b0_ne_b1. congruence. Qed.

(* ------------------------------------------------------------------ *)
(** ** Single-byte messages *)

Lemma msg_byte_single a v tid a' :
  msg_byte (WMsg a [v] tid) a' = if bool_decide (a' = a) then Some v else None.
Proof.
  rewrite /msg_byte /=.
  destruct (decide (a' = a)) as [->|Hne].
  - rewrite (bool_decide_eq_true_2 (a ≤ a)%Z); [lia|].
    rewrite (bool_decide_eq_true_2 (a = a :> Z)); [reflexivity|].
    rewrite Z.sub_diag //.
  - rewrite (bool_decide_eq_false_2 (a' = a :> Z)); [exact Hne|].
    destruct (decide (a ≤ a')%Z) as [Hle|Hgt].
    + rewrite (bool_decide_eq_true_2 (a ≤ a')%Z); [exact Hle|].
      assert (Z.to_nat (a' - a) = S (Z.to_nat (a' - a - 1))) as Heq by lia.
      rewrite Heq //.
    + rewrite (bool_decide_eq_false_2 (a ≤ a')%Z); [exact Hgt|]. done.
Qed.


(* ------------------------------------------------------------------ *)
(** ** The hart-program language

    Loads and stores carry no annotations (the machine has no acquire/
    release bit on a plain access); [ILoadInd] reads through a register —
    the address is the byte in [ra] — so an address dependency can be
    written down. *)

Inductive instr :=
| ILoad (reg : nat) (a : Z)
| ILoadInd (ra reg : nat)
| IStore (a : Z) (v : bv 8)
| IFence (pr pw sr sw : bool)
(** [amoswap]: the read half takes MEMORY (the drain log's flat) and the
    write half appends to both logs, in one step.  With [aq] the floor
    lands past the append (RVWMO's acquire annotation); without it only the
    read watermark moves — a plain AMO orders nothing after itself.  With
    [rl] the AMO waits for every own store to drain; without it only for
    the own stores to ITS byte (same-address order).  Sail puts the acquire
    strength on the read kind and the language layer carries it to the
    paired write as [RiscvLang.hr_acq]; here the pair is one step, so the
    bits sit on the instruction. *)
| IAmoSwap (aq rl : bool) (reg : nat) (a : Z) (v : bv 8).

(** the AMO's floor: past its own append iff it acquires *)
Definition amo_post (aq : bool) (tv : nat) (dl : list nat) : nat :=
  if aq then S (length dl) else tv.

(** The WHOLE per-hart memory state, beside the program and registers: the
    floor, the read watermark, the per-byte coherence floor — all drain
    positions. *)
Record hart := Hart {
  h_prog : list instr;               (* the remaining program IS the pc *)
  h_regs : gmap nat (bv 8);
  h_tv   : nat;
  h_rv   : nat;
  h_coh  : cohmap;
}.

Record config := Cfg {
  c_img   : image;
  c_log   : list wmsg;               (* the issue log *)
  c_dl    : list nat;                (* the drain log *)
  c_harts : list hart;
}.

(** The address held in register [ra] (0 if unset). *)
Definition reg_addr (regs : gmap nat (bv 8)) (ra : nat) : Z :=
  match regs !! ra with Some b => bv_unsigned b | None => 0%Z end.

(** One small step: EITHER pick a hart and execute its next instruction
    (the hart's INDEX is its agent id, so forwarding keys on it), OR let
    the memory system drain one pending store. *)
Definition hstep (c c' : config) : Prop :=
  ∃ (i : nat) (h : hart),
    c_harts c !! i = Some h ∧ c_img c' = c_img c ∧
    match h_prog h with
    | [] => False
    | ILoad r a :: rest => ∃ (tv' : nat) (v : bv 8),
        load_ok (c_img c) (c_log c) (c_dl c) i (h_tv h) (h_coh h a) tv' a v ∧
        c_log c' = c_log c ∧ c_dl c' = c_dl c ∧
        c_harts c' =
          <[i := Hart rest (<[r := v]> (h_regs h)) (h_tv h)
                   (Nat.max (h_rv h) tv') (coh_upd (h_coh h) a tv')]> (c_harts c)
    | ILoadInd ra r :: rest => ∃ (tv' : nat) (v : bv 8),
        load_ok (c_img c) (c_log c) (c_dl c) i (h_tv h)
          (h_coh h (reg_addr (h_regs h) ra)) tv' (reg_addr (h_regs h) ra) v ∧
        c_log c' = c_log c ∧ c_dl c' = c_dl c ∧
        c_harts c' =
          <[i := Hart rest (<[r := v]> (h_regs h)) (h_tv h)
                   (Nat.max (h_rv h) tv')
                   (coh_upd (h_coh h) (reg_addr (h_regs h) ra) tv')]> (c_harts c)
    | IStore a v :: rest =>
        c_log c' = store_log (c_log c) i a [v] ∧ c_dl c' = c_dl c ∧
        c_harts c' = <[i := Hart rest (h_regs h) (h_tv h) (h_rv h) (h_coh h)]> (c_harts c)
    | IFence pr pw sr sw :: rest =>
        fence_ok i (c_log c) (c_dl c) pw ∧
        c_log c' = c_log c ∧ c_dl c' = c_dl c ∧
        c_harts c' =
          <[i := Hart rest (h_regs h)
                   (fence_post i (c_log c) (c_dl c) pr pw sr sw (h_tv h) (h_rv h))
                   (h_rv h) (h_coh h)]> (c_harts c)
    | IAmoSwap aq rl r a v :: rest => ∃ (v_old : bv 8),
        excl_read_ok (c_img c) (c_log c) (c_dl c) i rl a v_old ∧
        c_log c' = store_log (c_log c) i a [v] ∧
        c_dl c' = c_dl c ++ [length (c_log c)] ∧
        c_harts c' =
          <[i := Hart rest (<[r := v_old]> (h_regs h))
                   (amo_post aq (h_tv h) (c_dl c)) (S (length (c_dl c))) (h_coh h)]>
            (c_harts c)
    end.

Definition dstep (c c' : config) : Prop :=
  ∃ i : nat,
    drain_ok (c_log c) (c_dl c) i ∧
    c_img c' = c_img c ∧ c_log c' = c_log c ∧
    c_dl c' = drain_log (c_dl c) i ∧ c_harts c' = c_harts c.

Definition lstep (c c' : config) : Prop := hstep c c' ∨ dstep c c'.

(* ------------------------------------------------------------------ *)
(** ** Step constructors (used to exhibit interleavings) *)

Lemma step_load c i r a rest regs tv rv coh tv' v :
  c_harts c !! i = Some (Hart (ILoad r a :: rest) regs tv rv coh) →
  load_ok (c_img c) (c_log c) (c_dl c) i tv (coh a) tv' a v →
  lstep c (Cfg (c_img c) (c_log c) (c_dl c)
               (<[i := Hart rest (<[r := v]> regs) tv (Nat.max rv tv')
                        (coh_upd coh a tv')]> (c_harts c))).
Proof.
  intros Hlk Hok. left. exists i, (Hart (ILoad r a :: rest) regs tv rv coh).
  split_and!; [done|done|]. simpl. exists tv', v. by split_and!.
Qed.

Lemma step_load_ind c i ra r rest regs tv rv coh tv' v :
  c_harts c !! i = Some (Hart (ILoadInd ra r :: rest) regs tv rv coh) →
  load_ok (c_img c) (c_log c) (c_dl c) i tv (coh (reg_addr regs ra)) tv'
    (reg_addr regs ra) v →
  lstep c (Cfg (c_img c) (c_log c) (c_dl c)
               (<[i := Hart rest (<[r := v]> regs) tv (Nat.max rv tv')
                        (coh_upd coh (reg_addr regs ra) tv')]> (c_harts c))).
Proof.
  intros Hlk Hok. left. exists i, (Hart (ILoadInd ra r :: rest) regs tv rv coh).
  split_and!; [done|done|]. simpl. exists tv', v. by split_and!.
Qed.

Lemma step_store c i a v rest regs tv rv coh :
  c_harts c !! i = Some (Hart (IStore a v :: rest) regs tv rv coh) →
  lstep c (Cfg (c_img c) (c_log c ++ [WMsg a [v] i]) (c_dl c)
               (<[i := Hart rest regs tv rv coh]> (c_harts c))).
Proof.
  intros Hlk. left. exists i, (Hart (IStore a v :: rest) regs tv rv coh).
  split_and!; [done|done|]. simpl. by split_and!.
Qed.

Lemma step_fence c i pr pw sr sw rest regs tv rv coh :
  c_harts c !! i = Some (Hart (IFence pr pw sr sw :: rest) regs tv rv coh) →
  fence_ok i (c_log c) (c_dl c) pw →
  lstep c (Cfg (c_img c) (c_log c) (c_dl c)
               (<[i := Hart rest regs
                        (fence_post i (c_log c) (c_dl c) pr pw sr sw tv rv) rv coh]>
                  (c_harts c))).
Proof.
  intros Hlk Hok. left. exists i, (Hart (IFence pr pw sr sw :: rest) regs tv rv coh).
  split_and!; [done|done|]. simpl. by split_and!.
Qed.

Lemma step_amo c i aq rl r a v rest regs tv rv coh v_old :
  c_harts c !! i = Some (Hart (IAmoSwap aq rl r a v :: rest) regs tv rv coh) →
  excl_read_ok (c_img c) (c_log c) (c_dl c) i rl a v_old →
  lstep c (Cfg (c_img c) (c_log c ++ [WMsg a [v] i]) (c_dl c ++ [length (c_log c)])
               (<[i := Hart rest (<[r := v_old]> regs)
                        (amo_post aq tv (c_dl c)) (S (length (c_dl c))) coh]>
                  (c_harts c))).
Proof.
  intros Hlk Hex. left. exists i, (Hart (IAmoSwap aq rl r a v :: rest) regs tv rv coh).
  split_and!; [done|done|]. simpl. exists v_old. by split_and!.
Qed.

Lemma step_drain c i :
  drain_ok (c_log c) (c_dl c) i →
  lstep c (Cfg (c_img c) (c_log c) (c_dl c ++ [i]) (c_harts c)).
Proof. intros Hok. right. exists i. by split_and!. Qed.

(** Every side condition in a witness run is ground, so it computes.  (The
    durable-notes trap: never [vm_compute] a goal carrying an evar — every
    argument of a [step_*] below is instantiated before these fire.) *)
Ltac solve_load :=
  rewrite /load_ok; split_and!;
  [vm_compute; lia | vm_compute; lia | vm_compute; lia | vm_compute; reflexivity].
Ltac solve_excl := rewrite /excl_read_ok; split; vm_compute; reflexivity.
Ltac solve_fence := rewrite /fence_ok; vm_compute; reflexivity.
Ltac solve_drain := rewrite /drain_ok; vm_compute; reflexivity.

(** Reachability. *)
Notation reach := (rtc lstep).

Lemma inv_reach (I : config → Prop) c0 c :
  I c0 → (∀ a b, I a → lstep a b → I b) → reach c0 c → I c.
Proof. intros H0 Hpres H. induction H as [|???? IH]; [done|]. eauto. Qed.

(* ------------------------------------------------------------------ *)
(** ** Well-formedness: the image is fixed and the drain log is sound

    Carried by every invariant below; the one fact the step proofs need
    from it is [dl_ok] (a drain position's issue index is in the log, and
    no index drains twice). *)

Definition wf (img : image) (c : config) : Prop :=
  c_img c = img ∧ dl_ok (c_log c) (c_dl c).

Lemma dl_ok_app_log log m dl : dl_ok log dl → dl_ok (log ++ [m]) dl.
Proof.
  intros [Hnd Hlt]. split; [done|]. intros i Hi. rewrite length_app /=.
  specialize (Hlt _ Hi). lia.
Qed.

Lemma dl_ok_amo log m dl :
  dl_ok log dl → dl_ok (log ++ [m]) (dl ++ [length log]).
Proof.
  intros [Hnd Hlt]. split.
  - apply list_relations.NoDup_app. split_and!; [done| |apply NoDup_singleton].
    intros x Hx Hx'. apply elem_of_list_singleton in Hx' as ->.
    specialize (Hlt _ Hx). lia.
  - intros i Hi. rewrite length_app /=. apply elem_of_app in Hi as [Hi|Hi].
    + specialize (Hlt _ Hi). lia.
    + apply elem_of_list_singleton in Hi as ->. lia.
Qed.

Lemma wf_step img c c' : wf img c → lstep c c' → wf img c'.
Proof.
  intros [Himg Hok] [Hst|Hst].
  - destruct Hst as (i & h & Hlk & Himg' & Hst). split; [by rewrite Himg'|].
    destruct (h_prog h) as [|[r a|ra r|a v|pr pw sr sw|aq rl r a v] rest]; [done| | | | |].
    + destruct Hst as (tv' & v & _ & -> & -> & _). exact Hok.
    + destruct Hst as (tv' & v & _ & -> & -> & _). exact Hok.
    + destruct Hst as (-> & -> & _). by apply dl_ok_app_log.
    + destruct Hst as (_ & -> & -> & _). exact Hok.
    + destruct Hst as (v_old & _ & -> & -> & _). by apply dl_ok_amo.
  - destruct Hst as (i & Hdr & Himg' & Hlog & Hdl & _).
    split; [by rewrite Himg'|]. rewrite Hlog Hdl. by apply drain_dl_ok.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The read analyses every forbidden proof consumes

    [pend_read_none_of]: a hart with no undrained message to [a] forwards
    nothing.  [tso_read_src_foreign]: a read by a hart with no pending
    message to the byte came from the image or from a drained message at a
    position UNDER THE VIEW (a foreign message) or the hart's own.
    [tso_read_from_below]: such a read cannot come from BELOW a visible
    drained write to the same byte — the latest-visible rule.  Under the
    relaxations these are applied at the load's OWN view; what makes a
    fenced verdict go is that the view is bounded below by the floor, the
    floor by the fence, the fence by the watermark or the drained store. *)

Lemma pend_read_none_of log dl h a :
  (∀ i m, log !! i = Some m → wm_tid m = h → i ∉ dl → msg_byte m a = None) →
  pend_read log dl h a = None.
Proof.
  intros Hno. rewrite /pend_read.
  destruct (pend_down log dl h a (length log)) as [v|] eqn:Hp; [|done].
  destruct (pend_down_some _ _ _ _ _ _ Hp) as (i & m & _ & Hi & Htid & Hnd & Hb).
  rewrite (Hno _ _ Hi Htid Hnd) in Hb. discriminate.
Qed.

Lemma tso_read_src img log dl h tv a v :
  pend_read log dl h a = None →
  tso_read img log dl h tv a = Some v →
  img a = Some v ∨
  ∃ q i m, dl !! q = Some i ∧ log !! i = Some m ∧ msg_byte m a = Some v ∧
           visibleb h tv log dl (S q) = true.
Proof.
  rewrite /tso_read => -> Hr.
  destruct (read_down_le img log dl h tv a (length dl) v Hr)
    as (p & _ & Hvis & Hb).
  destruct p as [|q].
  - left. exact Hb.
  - right. rewrite /dpos_byte /dmsg in Hb.
    destruct (dl !! q) as [i|] eqn:Hq; [|discriminate].
    destruct (log !! i) as [m|] eqn:Hi; [|discriminate].
    exists q, i, m. by split_and!.
Qed.

(** A foreign drained message is visible only by the view. *)
Lemma visibleb_foreign h tv log dl q i m :
  dl !! q = Some i → log !! i = Some m → wm_tid m ≠ h →
  visibleb h tv log dl (S q) = true → (S q ≤ tv)%nat.
Proof.
  intros Hq Hi Hne Hvis.
  destruct (visibleb_true _ _ _ _ _ Hvis) as [?|(q' & i' & m' & Heq & Hq' & Hi' & Htid)];
    [done|].
  assert (q' = q) as -> by lia.
  rewrite Hq' in Hq. injection Hq as <-. rewrite Hi' in Hi. injection Hi as <-.
  exfalso. exact (Hne Htid).
Qed.

Lemma tso_read_from_below img log dl h tv a q i m v0 v :
  pend_read log dl h a = None →
  dl !! q = Some i → log !! i = Some m → msg_byte m a = Some v0 →
  visibleb h tv log dl (S q) = true →
  tso_read img log dl h tv a = Some v →
  ∃ q' i' m', (q ≤ q')%nat ∧ dl !! q' = Some i' ∧ log !! i' = Some m' ∧
              msg_byte m' a = Some v ∧ visibleb h tv log dl (S q') = true.
Proof.
  intros Hpend Hq Hi Hb Hvis Hread.
  assert (Hlt : (q < length dl)%nat) by (eapply lookup_lt_Some; exact Hq).
  assert (Hb' : dpos_byte img log dl (S q) a = Some v0)
    by (rewrite /dpos_byte /dmsg Hq Hi //).
  destruct (read_down_latest img log dl h tv a (length dl) (S q) v0
              ltac:(lia) Hvis Hb') as (p'' & v'' & Hge & Hrd & Hvis'' & Hb'').
  rewrite /tso_read Hpend in Hread. rewrite Hread in Hrd.
  assert (v'' = v) as -> by congruence.
  destruct p'' as [|q']; [lia|].
  rewrite /dpos_byte /dmsg in Hb''.
  destruct (dl !! q') as [i'|] eqn:Hq'; [|discriminate].
  destruct (log !! i') as [m'|] eqn:Hi'; [|discriminate].
  exists q', i', m'. split_and!; [lia|done|done|done|done].
Qed.

(** What MEMORY holds came from the image or from a drained message. *)
Lemma dflat_src img log dl a v :
  dflat img log dl a = Some v →
  img a = Some v ∨
  ∃ q i m, dl !! q = Some i ∧ log !! i = Some m ∧ msg_byte m a = Some v.
Proof.
  rewrite -(read_down_top_flat img log dl 0%nat a) => Hr.
  destruct (read_down_le img log dl 0%nat (length dl) a (length dl) v Hr)
    as (p & _ & _ & Hb).
  destruct p as [|q]; [by left|]. right.
  rewrite /dpos_byte /dmsg in Hb.
  destruct (dl !! q) as [i|] eqn:Hq; [|discriminate].
  destruct (log !! i) as [m|] eqn:Hi; [|discriminate].
  exists q, i, m. by split_and!.
Qed.

(** The messages a drain log names are IN the issue log (from [dl_ok]), so
    an append to the issue log does not disturb them. *)
Lemma dl_lookup_app_log log m dl q i :
  dl_ok log dl → dl !! q = Some i → (log ++ [m]) !! i = log !! i.
Proof.
  intros [_ Hlt] Hq. apply lookup_app_l. apply Hlt. by eapply elem_of_list_lookup_2.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Log bookkeeping *)

Lemma lookup_app_last {A} (l : list A) (m : A) (j : nat) (m' : A) :
  (l ++ [m]) !! j = Some m' →
  ((j < length l)%nat ∧ l !! j = Some m') ∨ (j = length l ∧ m' = m).
Proof.
  intros Hlk. destruct (decide (j < length l)%nat) as [Hlt|Hge].
  - left. split; [done|]. rewrite -Hlk. symmetry. by apply lookup_app_l.
  - right.
    assert ((l ++ [m]) !! j = [m] !! (j - length l)%nat) as Heq
      by (apply lookup_app_r; lia).
    rewrite Heq in Hlk.
    destruct (j - length l)%nat as [|k] eqn:Hk; simpl in Hlk; [|done].
    split; [lia|]. by simplify_eq.
Qed.

(** A lookup of a message OTHER than the freshly appended one is a lookup in
    the old log. *)
Lemma lookup_app_old {A} (l : list A) (m : A) (j : nat) (m' : A) :
  (l ++ [m]) !! j = Some m' → m' ≠ m → l !! j = Some m'.
Proof.
  intros Hlk Hne. apply lookup_app_last in Hlk as [[? ?]|[? ?]]; [done|].
  by destruct Hne.
Qed.

Lemma lookup_app_new {A} (l : list A) (m : A) :
  (l ++ [m]) !! length l = Some m.
Proof. by apply list_lookup_middle. Qed.

(** A drain-log position that names an index of [log] survives appends to
    either log, and the message it names is unchanged. *)
Lemma dpos_app_dl (dl : list nat) (j q i : nat) :
  dl !! q = Some i → (dl ++ [j]) !! q = Some i.
Proof. apply lookup_app_l_Some. Qed.

(** The fence kinds the suite uses. *)
Local Notation FENCE := (IFence true true true true).       (* rw,rw *)
Local Notation FENCE_RR := (IFence true false true false).  (* r,r   *)
Local Notation FENCE_WW := (IFence false true false true).  (* w,w   *)
Local Notation FENCE_RWW := (IFence true true false true).  (* rw,w  *)

(** The empty per-hart read side. *)
Local Notation coh0 := (λ _ : Z, 0%nat).


(* ------------------------------------------------------------------ *)
(** ** "Message [M] is drained at position [q]" — the invariants' vocabulary *)

Definition at_pos (log : list wmsg) (dl : list nat) (q : nat) (M : wmsg) : Prop :=
  ∃ j, dl !! q = Some j ∧ log !! j = Some M.

Lemma at_pos_lt log dl q M : at_pos log dl q M → (q < length dl)%nat.
Proof. intros (j & Hq & _). by eapply lookup_lt_Some. Qed.

Lemma at_pos_app_log log dl q M m :
  dl_ok log dl → at_pos log dl q M → at_pos (log ++ [m]) dl q M.
Proof.
  intros Hok (j & Hq & Hj). exists j. split; [done|].
  rewrite (dl_lookup_app_log _ m _ _ _ Hok Hq) //.
Qed.

Lemma at_pos_app_log_inv log dl q M m :
  dl_ok log dl → at_pos (log ++ [m]) dl q M → at_pos log dl q M.
Proof.
  intros Hok (j & Hq & Hj). exists j. split; [done|].
  rewrite -(dl_lookup_app_log _ m _ _ _ Hok Hq) //.
Qed.

Lemma at_pos_app_dl log dl q M i :
  at_pos log dl q M → at_pos log (dl ++ [i]) q M.
Proof. intros (j & Hq & Hj). exists j. split; [by apply lookup_app_l_Some|done]. Qed.

Lemma at_pos_app_dl_inv log dl q M i :
  at_pos log (dl ++ [i]) q M →
  at_pos log dl q M ∨ (q = length dl ∧ log !! i = Some M).
Proof.
  intros (j & Hq & Hj). apply lookup_app_last in Hq as [[_ Hq]|[-> ->]].
  - left. by exists j.
  - by right.
Qed.

(** The drained message at [q] is unique: two [at_pos] facts at one
    position name one message. *)
Lemma at_pos_inj log dl q M M' :
  at_pos log dl q M → at_pos log dl q M' → M = M'.
Proof.
  intros (j & Hq & Hj) (j' & Hq' & Hj'). rewrite Hq in Hq'. injection Hq' as <-.
  rewrite Hj in Hj'. injection Hj' as ->. done.
Qed.

(** A message the fence has drained sits at SOME position, and the hart's
    floor after a W→R fence is past it. *)
Lemma own_drained_at_pos h log dl j M :
  own_drained h log dl → log !! j = Some M → wm_tid M = h →
  ∃ q, at_pos log dl q M.
Proof.
  intros Hod Hj Htid.
  destruct (elem_of_list_lookup_1 _ _ (own_drained_lookup _ _ _ _ _ Hod Hj Htid))
    as [q Hq].
  exists q, j. done.
Qed.

Lemma at_pos_own_pub h log dl q M :
  at_pos log dl q M → wm_tid M = h → (S q ≤ own_pub h log dl)%nat.
Proof. intros (j & Hq & Hj) Htid. by eapply own_pub_ge. Qed.

(* ================================================================== *)
(** ** SB — store buffering.  Both loads reading 0 is ALLOWED: both stores
       are pending when the loads run. *)

Definition sb_c0 : config :=
  Cfg img0 [] [] [Hart [IStore ax b1; ILoad rg1 ay] ∅ 0%nat 0%nat coh0;
                  Hart [IStore ay b1; ILoad rg2 ax] ∅ 0%nat 0%nat coh0].

Lemma sb_allowed :
  ∃ c, reach sb_c0 c ∧
       (∃ regs tv rv coh, c_harts c !! 0%nat = Some (Hart [] regs tv rv coh) ∧
                          regs !! rg1 = Some b0) ∧
       (∃ regs tv rv coh, c_harts c !! 1%nat = Some (Hart [] regs tv rv coh) ∧
                          regs !! rg2 = Some b0).
Proof.
  rewrite /sb_c0. eexists. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 1%nat); reflexivity|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 0%nat rg1 ay _ _ _ _ _ 0%nat b0);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg2 ax _ _ _ _ _ 0%nat b0);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split.
  - do 4 eexists. split; [reflexivity|]. rewrite lookup_insert //.
  - do 4 eexists. split; [reflexivity|]. rewrite lookup_insert //.
Qed.

(* ================================================================== *)
(** ** SB with a [fence rw,rw] in both harts — (0,0) is FORBIDDEN.

    The mechanism: a fence with a W predecessor WAITS for the hart's store
    to drain and then pushes the floor past its drain position, and the
    drain order is one total order, so whichever hart's store drained
    LATER is forced to see the other's. *)

Local Notation SBX := (WMsg ax [b1] 0%nat).
Local Notation SBY := (WMsg ay [b1] 1%nat).

Lemma SBX_ne_SBY : SBX ≠ SBY.
Proof. intros H. by simplify_eq/=. Qed.
Lemma mb_SBX_x : msg_byte SBX ax = Some b1.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_SBX_y : msg_byte SBX ay = None.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_SBY_x : msg_byte SBY ax = None.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_SBY_y : msg_byte SBY ay = Some b1.
Proof. rewrite msg_byte_single //. Qed.

Definition sbf_c0 : config :=
  Cfg img0 [] [] [Hart [IStore ax b1; FENCE; ILoad rg1 ay] ∅ 0%nat 0%nat coh0;
                  Hart [IStore ay b1; FENCE; ILoad rg2 ax] ∅ 0%nat 0%nat coh0].

Definition sbf_content (log : list wmsg) : Prop :=
  ∀ m, m ∈ log → m = SBX ∨ m = SBY.

Lemma sbf_content_app log m :
  sbf_content log → (m = SBX ∨ m = SBY) → sbf_content (log ++ [m]).
Proof.
  intros Hc Hm m' Hin. apply elem_of_app in Hin as [Hin|Hin]; [by apply Hc|].
  apply elem_of_list_singleton in Hin as ->. done.
Qed.

(** Neither hart ever has a pending message to the byte it LOADS. *)
Lemma sbf_pend_A log dl : sbf_content log → pend_read log dl 0%nat ay = None.
Proof.
  intros Hc. apply pend_read_none_of. intros i m Hi Htid _.
  destruct (Hc m (elem_of_list_lookup_2 _ _ _ Hi)) as [->| ->];
    [apply mb_SBX_y|done].
Qed.

Lemma sbf_pend_B log dl : sbf_content log → pend_read log dl 1%nat ax = None.
Proof.
  intros Hc. apply pend_read_none_of. intros i m Hi Htid _.
  destruct (Hc m (elem_of_list_lookup_2 _ _ _ Hi)) as [->| ->];
    [done|apply mb_SBY_x].
Qed.

(** Hart 0's phases: issued; drained with the floor past it; done, and if
    the load did NOT see [y = 1] then every drain position of [SBY] is above
    [SBX]'s. *)
Definition sbf_A (p : list instr) (regs : gmap nat (bv 8)) (tv : nat)
    (log : list wmsg) (dl : list nat) : Prop :=
  (p = [IStore ax b1; FENCE; ILoad rg1 ay]) ∨
  (p = [FENCE; ILoad rg1 ay] ∧ ∃ j, log !! j = Some SBX) ∨
  (p = [ILoad rg1 ay] ∧ ∃ q, at_pos log dl q SBX ∧ (S q ≤ tv)%nat) ∨
  (p = [] ∧ ∃ q, at_pos log dl q SBX ∧
     (regs !! rg1 ≠ Some b1 → ∀ qy, at_pos log dl qy SBY → (q < qy)%nat)).

Definition sbf_B (p : list instr) (regs : gmap nat (bv 8)) (tv : nat)
    (log : list wmsg) (dl : list nat) : Prop :=
  (p = [IStore ay b1; FENCE; ILoad rg2 ax]) ∨
  (p = [FENCE; ILoad rg2 ax] ∧ ∃ j, log !! j = Some SBY) ∨
  (p = [ILoad rg2 ax] ∧ ∃ q, at_pos log dl q SBY ∧ (S q ≤ tv)%nat) ∨
  (p = [] ∧ ∃ q, at_pos log dl q SBY ∧
     (regs !! rg2 ≠ Some b1 → ∀ qx, at_pos log dl qx SBX → (q < qx)%nat)).

Definition sbf_inv (c : config) : Prop :=
  wf img0 c ∧
  ∃ h0 h1, c_harts c = [h0; h1] ∧ sbf_content (c_log c) ∧
    sbf_A (h_prog h0) (h_regs h0) (h_tv h0) (c_log c) (c_dl c) ∧
    sbf_B (h_prog h1) (h_regs h1) (h_tv h1) (c_log c) (c_dl c).

(** The phases are stable under the OTHER hart's store and under a drain. *)
Lemma sbf_A_app_log p regs tv log dl m :
  dl_ok log dl → sbf_A p regs tv log dl → sbf_A p regs tv (log ++ [m]) dl.
Proof.
  intros Hok [->|[[-> [j Hj]]|[[-> [q [Hq Htv]]]|[-> [q [Hq Hc]]]]]].
  - by left.
  - right; left. split; [done|]. exists j. by apply lookup_app_l_Some.
  - right; right; left. split; [done|]. exists q. split; [by apply at_pos_app_log|done].
  - right; right; right. split; [done|]. exists q. split; [by apply at_pos_app_log|].
    intros Hr qy Hqy. apply Hc; [done|]. by eapply at_pos_app_log_inv.
Qed.

Lemma sbf_B_app_log p regs tv log dl m :
  dl_ok log dl → sbf_B p regs tv log dl → sbf_B p regs tv (log ++ [m]) dl.
Proof.
  intros Hok [->|[[-> [j Hj]]|[[-> [q [Hq Htv]]]|[-> [q [Hq Hc]]]]]].
  - by left.
  - right; left. split; [done|]. exists j. by apply lookup_app_l_Some.
  - right; right; left. split; [done|]. exists q. split; [by apply at_pos_app_log|done].
  - right; right; right. split; [done|]. exists q. split; [by apply at_pos_app_log|].
    intros Hr qx Hqx. apply Hc; [done|]. by eapply at_pos_app_log_inv.
Qed.

Lemma sbf_A_app_dl p regs tv log dl i :
  sbf_A p regs tv log dl → sbf_A p regs tv log (dl ++ [i]).
Proof.
  intros [->|[[-> [j Hj]]|[[-> [q [Hq Htv]]]|[-> [q [Hq Hc]]]]]].
  - by left.
  - right; left. split; [done|]. by exists j.
  - right; right; left. split; [done|]. exists q. split; [by apply at_pos_app_dl|done].
  - right; right; right. split; [done|]. exists q. split; [by apply at_pos_app_dl|].
    intros Hr qy Hqy. apply at_pos_app_dl_inv in Hqy as [Hqy|[-> _]].
    + by apply Hc.
    + by apply at_pos_lt in Hq.
Qed.

Lemma sbf_B_app_dl p regs tv log dl i :
  sbf_B p regs tv log dl → sbf_B p regs tv log (dl ++ [i]).
Proof.
  intros [->|[[-> [j Hj]]|[[-> [q [Hq Htv]]]|[-> [q [Hq Hc]]]]]].
  - by left.
  - right; left. split; [done|]. by exists j.
  - right; right; left. split; [done|]. exists q. split; [by apply at_pos_app_dl|done].
  - right; right; right. split; [done|]. exists q. split; [by apply at_pos_app_dl|].
    intros Hr qx Hqx. apply at_pos_app_dl_inv in Hqx as [Hqx|[-> _]].
    + by apply Hc.
    + by apply at_pos_lt in Hq.
Qed.

Lemma sbf_step c c' : sbf_inv c → lstep c c' → sbf_inv c'.
Proof.
  intros Hinv Hstep.
  assert (Hwf' : wf img0 c') by (eapply wf_step; [apply Hinv|exact Hstep]).
  destruct Hinv as ([Himg Hok] & [p0 regs0 tv0 rv0 coh0'] & [p1 regs1 tv1 rv1 coh1]
          & Hh & Hcont & HA & HB).
  simpl in HA, HB.
  destruct Hstep as [Hstep|Hstep]; last first.
  { (* ---- a drain ---- *)
    destruct Hstep as (i & Hdr & Himg' & Hlog & Hdl & Hharts).
    split; [done|]. eexists _, _. rewrite Hharts Hh Hlog Hdl /drain_log.
    split; [reflexivity|]. split_and!; [done|by apply sbf_A_app_dl|by apply sbf_B_app_dl]. }
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|[|i]]; simpl in Hlk; simplify_eq/=.
  - (* ---- hart 0 ---- *)
    destruct HA as [->|[[-> Hex]|[[-> [q [Hq Htv]]]|[-> _]]]]; simpl in Hst;
      [| | |done].
    + (* store x *)
      destruct Hst as (Hlog & Hdl & Hharts).
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl /store_log. split_and!.
      * apply sbf_content_app; [exact Hcont|by left].
      * right; left. split; [reflexivity|].
        exists (length (c_log c)). apply lookup_app_new.
      * by apply sbf_B_app_log.
    + (* fence rw,rw: waits for SBX to drain, then the floor passes it *)
      destruct Hst as (Hfok & Hlog & Hdl & Hharts).
      destruct Hex as [j Hj].
      pose proof (fence_ok_rel _ _ _ _ Hfok eq_refl) as Hod.
      destruct (own_drained_at_pos _ _ _ _ _ Hod Hj eq_refl) as [q Hq].
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl. split_and!.
      * exact Hcont.
      * right; right; left. split; [reflexivity|]. exists q. split; [exact Hq|].
        pose proof (at_pos_own_pub 0%nat _ _ _ _ Hq eq_refl).
        pose proof (fence_post_drain 0%nat (c_log c) (c_dl c) true true true true tv0 rv0
                      eq_refl). lia.
      * exact HB.
    + (* load rg1 <- y *)
      destruct Hst as (tv' & v & Hok' & Hlog & Hdl & Hharts).
      destruct Hok' as (Hle & Hcoh & Hlen & Hread). rewrite Himg in Hread.
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl. split_and!.
      * exact Hcont.
      * right; right; right. split; [reflexivity|]. exists q. split; [exact Hq|].
        rewrite lookup_insert. intros Hv qy Hqy.
        destruct (decide (q < qy)%nat) as [?|Hn]; [done|]. exfalso.
        destruct Hqy as (jy & Hqy & Hjy).
        assert (Hvis : visibleb 0%nat tv' (c_log c) (c_dl c) (S qy) = true)
          by (apply visibleb_below; lia).
        destruct (tso_read_from_below img0 (c_log c) (c_dl c) 0%nat tv' ay qy jy SBY b1 v
                    (sbf_pend_A _ _ Hcont) Hqy Hjy mb_SBY_y Hvis Hread)
          as (q' & j' & m' & _ & _ & Hj' & Hmb & _).
        destruct (Hcont m' (elem_of_list_lookup_2 _ _ _ Hj')) as [-> | ->].
        { rewrite mb_SBX_y in Hmb. done. }
        rewrite mb_SBY_y in Hmb. apply Hv. congruence.
      * exact HB.
  - (* ---- hart 1 ---- *)
    destruct HB as [->|[[-> Hex]|[[-> [q [Hq Htv]]]|[-> _]]]]; simpl in Hst;
      [| | |done].
    + (* store y *)
      destruct Hst as (Hlog & Hdl & Hharts).
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl /store_log. split_and!.
      * apply sbf_content_app; [exact Hcont|by right].
      * by apply sbf_A_app_log.
      * right; left. split; [reflexivity|].
        exists (length (c_log c)). apply lookup_app_new.
    + (* fence rw,rw *)
      destruct Hst as (Hfok & Hlog & Hdl & Hharts).
      destruct Hex as [j Hj].
      pose proof (fence_ok_rel _ _ _ _ Hfok eq_refl) as Hod.
      destruct (own_drained_at_pos _ _ _ _ _ Hod Hj eq_refl) as [q Hq].
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl. split_and!.
      * exact Hcont.
      * exact HA.
      * right; right; left. split; [reflexivity|]. exists q. split; [exact Hq|].
        pose proof (at_pos_own_pub 1%nat _ _ _ _ Hq eq_refl).
        pose proof (fence_post_drain 1%nat (c_log c) (c_dl c) true true true true tv1 rv1
                      eq_refl). lia.
    + (* load rg2 <- x *)
      destruct Hst as (tv' & v & Hok' & Hlog & Hdl & Hharts).
      destruct Hok' as (Hle & Hcoh & Hlen & Hread). rewrite Himg in Hread.
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl. split_and!.
      * exact Hcont.
      * exact HA.
      * right; right; right. split; [reflexivity|]. exists q. split; [exact Hq|].
        rewrite lookup_insert. intros Hv qx Hqx.
        destruct (decide (q < qx)%nat) as [?|Hn]; [done|]. exfalso.
        destruct Hqx as (jx & Hqx & Hjx).
        assert (Hvis : visibleb 1%nat tv' (c_log c) (c_dl c) (S qx) = true)
          by (apply visibleb_below; lia).
        destruct (tso_read_from_below img0 (c_log c) (c_dl c) 1%nat tv' ax qx jx SBX b1 v
                    (sbf_pend_B _ _ Hcont) Hqx Hjx mb_SBX_x Hvis Hread)
          as (q' & j' & m' & _ & _ & Hj' & Hmb & _).
        destruct (Hcont m' (elem_of_list_lookup_2 _ _ _ Hj')) as [-> | ->].
        { rewrite mb_SBX_x in Hmb. apply Hv. congruence. }
        rewrite mb_SBY_x in Hmb. done.
Qed.

Lemma sbf_inv0 : sbf_inv sbf_c0.
Proof.
  split; [split; [done|split; [apply NoDup_nil_2|by intros ? ?%elem_of_nil]]|].
  eexists _, _. split; [reflexivity|]. simpl.
  split_and!; [by intros ? ?%elem_of_nil|by left|by left].
Qed.

(** SB with both harts fenced: (rg1, rg2) = (0, 0) is UNREACHABLE. *)
Theorem sb_fence_forbidden c regs0 tv0 rv0 coh0' regs1 tv1 rv1 coh1 :
  reach sbf_c0 c →
  c_harts c = [Hart [] regs0 tv0 rv0 coh0'; Hart [] regs1 tv1 rv1 coh1] →
  regs0 !! rg1 = Some b1 ∨ regs1 !! rg2 = Some b1.
Proof.
  intros Hre Hh.
  assert (Hinv : sbf_inv c).
  { eapply inv_reach; [apply sbf_inv0| |exact Hre].
    intros. by eapply sbf_step. }
  destruct Hinv as (_ & g0 & g1 & Hh' & _ & HA & HB).
  rewrite Hh in Hh'. simplify_eq/=.
  destruct HA as [Hc|[[Hc _]|[[Hc _]|[_ [qx [Hqx HA]]]]]]; try discriminate.
  destruct HB as [Hc|[[Hc _]|[[Hc _]|[_ [qy [Hqy HB]]]]]]; try discriminate.
  destruct (decide (regs0 !! rg1 = Some b1)) as [?|Hn0]; [by left|].
  right. destruct (decide (regs1 !! rg2 = Some b1)) as [?|Hn1]; [done|].
  exfalso.
  specialize (HA Hn0 _ Hqy). specialize (HB Hn1 _ Hqx). lia.
Qed.

(** Non-vacuity: the fenced SB harts do complete, and the machine really
    produces the one-sided outcome (0, 1) — the store that drained later is
    the one whose hart is forced to see the other. *)
Lemma sbf_completed_reachable :
  ∃ c regs0 tv0 rv0 coh0' regs1 tv1 rv1 coh1,
    reach sbf_c0 c ∧
    c_harts c = [Hart [] regs0 tv0 rv0 coh0'; Hart [] regs1 tv1 rv1 coh1] ∧
    regs0 !! rg1 = Some b0 ∧ regs1 !! rg2 = Some b1.
Proof.
  rewrite /sbf_c0. eexists _, _, _, _, _, _, _, _, _. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 0%nat); solve_drain|]. simpl.
    eapply rtc_l; [eapply (step_fence _ 0%nat); [reflexivity|solve_fence]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 0%nat rg1 ay _ _ _ _ _ 1%nat b0);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l; [eapply (step_store _ 1%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 1%nat); solve_drain|]. simpl.
    eapply rtc_l; [eapply (step_fence _ 1%nat); [reflexivity|solve_fence]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg2 ax _ _ _ _ _ 2%nat b1);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split; rewrite lookup_insert //.
Qed.


(* ================================================================== *)
(** ** MP — message passing with NO fences.  The weak outcome is ALLOWED
       (herd: allowed under RVWMO): the reader takes the flag at a high
       view and the data at a low one — or the writer's data store simply
       has not drained. *)

Local Notation MPX := (WMsg ax [b1] 0%nat).
Local Notation MPY := (WMsg ay [b1] 0%nat).

Lemma mb_MPX_x : msg_byte MPX ax = Some b1.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_MPX_y : msg_byte MPX ay = None.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_MPY_x : msg_byte MPY ax = None.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_MPY_y : msg_byte MPY ay = Some b1.
Proof. rewrite msg_byte_single //. Qed.

Definition mp_c0 : config :=
  Cfg img0 [] [] [Hart [IStore ax b1; IStore ay b1] ∅ 0%nat 0%nat coh0;
                  Hart [ILoad rg1 ay; ILoad rg2 ax] ∅ 0%nat 0%nat coh0].

Lemma mp_allowed :
  ∃ c h0 regs tv rv coh,
    reach mp_c0 c ∧ c_harts c = [h0; Hart [] regs tv rv coh] ∧
    regs !! rg1 = Some b1 ∧ regs !! rg2 = Some b0.
Proof.
  rewrite /mp_c0. eexists _, _, _, _, _, _. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 1%nat); solve_drain|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg1 ay _ _ _ _ _ 1%nat b1);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg2 ax _ _ _ _ _ 0%nat b0);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
Qed.

(** MP with only the WRITER's [fence w,w]: still ALLOWED — the reader
    reorders its loads (relaxed-rr). *)
Definition mpw_c0 : config :=
  Cfg img0 [] [] [Hart [IStore ax b1; FENCE_WW; IStore ay b1] ∅ 0%nat 0%nat coh0;
                  Hart [ILoad rg1 ay; ILoad rg2 ax] ∅ 0%nat 0%nat coh0].

Lemma mp_wfence_allowed :
  ∃ c h0 regs tv rv coh,
    reach mpw_c0 c ∧ c_harts c = [h0; Hart [] regs tv rv coh] ∧
    regs !! rg1 = Some b1 ∧ regs !! rg2 = Some b0.
Proof.
  rewrite /mpw_c0. eexists _, _, _, _, _, _. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 0%nat); solve_drain|]. simpl.
    eapply rtc_l; [eapply (step_fence _ 0%nat); [reflexivity|solve_fence]|]. simpl.
    eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 1%nat); solve_drain|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg1 ay _ _ _ _ _ 2%nat b1);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg2 ax _ _ _ _ _ 0%nat b0);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
Qed.

(** MP with only the READER's [fence r,r]: ALLOWED — THE W→W RELAXATION'S
    HEADLINE, the verdict that flipped.  The writer's data store is still
    pending when the flag drains; the fenced reader sees the flag and then,
    at a view past it, misses the data because it has not reached memory. *)
Definition mpr_c0 : config :=
  Cfg img0 [] [] [Hart [IStore ax b1; IStore ay b1] ∅ 0%nat 0%nat coh0;
                  Hart [ILoad rg1 ay; FENCE_RR; ILoad rg2 ax] ∅ 0%nat 0%nat coh0].

Lemma mp_rfence_allowed :
  ∃ c h0 regs tv rv coh,
    reach mpr_c0 c ∧ c_harts c = [h0; Hart [] regs tv rv coh] ∧
    regs !! rg1 = Some b1 ∧ regs !! rg2 = Some b0.
Proof.
  rewrite /mpr_c0. eexists _, _, _, _, _, _. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 1%nat); solve_drain|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg1 ay _ _ _ _ _ 1%nat b1);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l; [eapply (step_fence _ 1%nat); [reflexivity|solve_fence]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg2 ax _ _ _ _ _ 1%nat b0);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
Qed.

(* ================================================================== *)
(** ** MP with the RVWMO fences — writer [fence w,w], reader [fence r,r]:
       the weak outcome is FORBIDDEN.

    The writer's fence WAITS for the data store to drain, so the flag
    drains after it.  The reader's fence carries the flag's drain position
    from the watermark to the floor, and the data load reads at or above
    the floor. *)

Definition mpf_c0 : config :=
  Cfg img0 [] [] [Hart [IStore ax b1; FENCE_WW; IStore ay b1] ∅ 0%nat 0%nat coh0;
                  Hart [ILoad rg1 ay; FENCE_RR; ILoad rg2 ax] ∅ 0%nat 0%nat coh0].

(** The writer is the only writer, so its phase FIXES the issue log; past
    its fence the data store (issue index 0) has drained. *)
Definition mpf_W (p : list instr) (log : list wmsg) (dl : list nat) : Prop :=
  (p = [IStore ax b1; FENCE_WW; IStore ay b1] ∧ log = []) ∨
  (p = [FENCE_WW; IStore ay b1] ∧ log = [MPX]) ∨
  (p = [IStore ay b1] ∧ log = [MPX] ∧ 0%nat ∈ dl) ∨
  (p = [] ∧ log = [MPX; MPY] ∧ 0%nat ∈ dl).

(** The drain order the fence buys: wherever the flag drained, the data
    drained below it. *)
Definition mpf_ord (dl : list nat) : Prop :=
  ∀ qy, dl !! qy = Some 1%nat → ∃ qx, dl !! qx = Some 0%nat ∧ (qx < qy)%nat.

(** The reader's phases carry the ordering as it moves: watermark after the
    flag load, floor after the fence. *)
Definition mpf_R (p : list instr) (regs : gmap nat (bv 8)) (tv rv : nat)
    (dl : list nat) : Prop :=
  (p = [ILoad rg1 ay; FENCE_RR; ILoad rg2 ax]) ∨
  (p = [FENCE_RR; ILoad rg2 ax] ∧
     (regs !! rg1 = Some b1 → ∃ qy, dl !! qy = Some 1%nat ∧ (S qy ≤ rv)%nat)) ∨
  (p = [ILoad rg2 ax] ∧
     (regs !! rg1 = Some b1 → ∃ qy, dl !! qy = Some 1%nat ∧ (S qy ≤ tv)%nat)) ∨
  (p = [] ∧ (regs !! rg1 = Some b1 → regs !! rg2 = Some b1)).

Definition mpf_inv (c : config) : Prop :=
  wf img0 c ∧
  ∃ h0 h1, c_harts c = [h0; h1] ∧
    mpf_W (h_prog h0) (c_log c) (c_dl c) ∧ mpf_ord (c_dl c) ∧
    mpf_R (h_prog h1) (h_regs h1) (h_tv h1) (h_rv h1) (c_dl c).

Lemma mpf_W_tid p log dl :
  mpf_W p log dl → ∀ i m, log !! i = Some m → wm_tid m = 0%nat.
Proof.
  intros [[_ ->]|[[_ ->]|[[_ [-> _]]|[_ [-> _]]]]] i m Hi.
  - rewrite lookup_nil in Hi. discriminate.
  - destruct i as [|i]; simpl in Hi; [by simplify_eq|discriminate].
  - destruct i as [|i]; simpl in Hi; [by simplify_eq|discriminate].
  - destruct i as [|[|i]]; simpl in Hi; [by simplify_eq|by simplify_eq|discriminate].
Qed.

Lemma mpf_R_pend p log dl a :
  mpf_W p log dl → pend_read log dl 1%nat a = None.
Proof.
  intros HW. apply pend_read_none_of. intros i m Hi Htid _.
  rewrite (mpf_W_tid _ _ _ HW _ _ Hi) in Htid. discriminate.
Qed.

Lemma mpf_R_app_dl p regs tv rv dl i :
  mpf_R p regs tv rv dl → mpf_R p regs tv rv (dl ++ [i]).
Proof.
  intros [->|[[-> H]|[[-> H]|[-> H]]]].
  - by left.
  - right; left. split; [done|]. intros Hr. destruct (H Hr) as (q & Hq & ?).
    exists q. split; [by apply lookup_app_l_Some|done].
  - right; right; left. split; [done|]. intros Hr. destruct (H Hr) as (q & Hq & ?).
    exists q. split; [by apply lookup_app_l_Some|done].
  - right; right; right. by split.
Qed.

Lemma mpf_step c c' : mpf_inv c → lstep c c' → mpf_inv c'.
Proof.
  intros Hinv Hstep.
  assert (Hwf' : wf img0 c') by (eapply wf_step; [apply Hinv|exact Hstep]).
  destruct Hinv as ([Himg Hok] & [p0 regs0 tv0 rv0 coh0'] & [p1 regs1 tv1 rv1 coh1]
          & Hh & HW & Hord & HR).
  simpl in HW, HR.
  destruct Hstep as [Hstep|Hstep]; last first.
  { (* ---- a drain ---- *)
    destruct Hstep as (i & Hdr & Himg' & Hlog & Hdl & Hharts).
    split; [done|]. eexists _, _. rewrite Hharts Hh Hlog Hdl /drain_log.
    split; [reflexivity|]. split_and!; [| |by apply mpf_R_app_dl].
    - destruct HW as [[-> ->]|[[-> ->]|[[-> [-> Hin]]|[-> [-> Hin]]]]].
      + by left.
      + by right; left.
      + right; right; left. split_and!; [done|done|]. apply elem_of_app. by left.
      + right; right; right. split_and!; [done|done|]. apply elem_of_app. by left.
    - intros qy Hqy. apply lookup_app_last in Hqy as [[_ Hqy]|[-> <-]].
      + destruct (Hord _ Hqy) as (qx & Hqx & ?). exists qx.
        split; [by apply lookup_app_l_Some|done].
      + (* the flag drains now: the data drained before it was issued *)
        destruct (drain_ok_issued _ _ _ Hdr) as [m Hm].
        assert (Hin : 0%nat ∈ c_dl c).
        { destruct HW as [[_ Hl]|[[_ Hl]|[[_ [Hl _]]|[_ [_ Hin]]]]]; [..|exact Hin];
            rewrite Hl in Hm; simpl in Hm; discriminate. }
        apply elem_of_list_lookup_1 in Hin as [qx Hqx]. exists qx.
        split; [by apply lookup_app_l_Some|by eapply lookup_lt_Some]. }
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|[|i]]; simpl in Hlk; simplify_eq/=.
  - (* ---- the writer ---- *)
    destruct HW as [[-> Hl]|[[-> Hl]|[[-> [Hl Hin]]|[-> _]]]]; simpl in Hst;
      [| | |done].
    + (* store x *)
      destruct Hst as (Hlog & Hdl & Hharts).
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. rewrite Hdl. split_and!.
      * right; left. split; [reflexivity|]. rewrite Hlog /store_log Hl //.
      * exact Hord.
      * exact HR.
    + (* fence w,w: waits for the data store to drain *)
      destruct Hst as (Hfok & Hlog & Hdl & Hharts).
      pose proof (fence_ok_rel _ _ _ _ Hfok eq_refl) as Hod.
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. rewrite Hlog Hdl. split_and!.
      * right; right; left. split_and!; [reflexivity|done|].
        eapply (own_drained_lookup 0%nat _ _ 0%nat MPX Hod); [rewrite Hl //|done].
      * exact Hord.
      * exact HR.
    + (* store y *)
      destruct Hst as (Hlog & Hdl & Hharts).
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. rewrite Hdl. split_and!.
      * right; right; right. split_and!; [reflexivity| |done].
        rewrite Hlog /store_log Hl //.
      * exact Hord.
      * exact HR.
  - (* ---- the reader ---- *)
    destruct HR as [->|[[-> Hc]|[[-> Hc]|[-> _]]]]; simpl in Hst; [| | |done].
    + (* load rg1 <- y: the watermark passes the flag's drain position *)
      destruct Hst as (tv' & v & Hok' & Hlog & Hdl & Hharts).
      destruct Hok' as (Hle & Hcoh & Hlen & Hread). rewrite Himg in Hread.
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. rewrite Hlog Hdl. split_and!.
      * exact HW.
      * exact Hord.
      * right; left. split; [reflexivity|]. rewrite lookup_insert.
        intros Hv. assert (v = b1) as -> by congruence.
        destruct (tso_read_src _ _ _ _ _ _ _ (mpf_R_pend _ _ _ ay HW) Hread)
          as [Hi|(q & j & m & Hq & Hj & Hmb & Hvis)].
        { by destruct (img0_y_nb1 Hi). }
        (* the only y-write is [MPY], at issue index 1 *)
        assert (Hj1 : j = 1%nat).
        { destruct HW as [[_ Hl]|[[_ Hl]|[[_ [Hl _]]|[_ [Hl _]]]]]; rewrite Hl in Hj.
          - rewrite lookup_nil in Hj. discriminate.
          - destruct j as [|j]; simpl in Hj; [|discriminate].
            injection Hj as <-. rewrite mb_MPX_y in Hmb. discriminate.
          - destruct j as [|j]; simpl in Hj; [|discriminate].
            injection Hj as <-. rewrite mb_MPX_y in Hmb. discriminate.
          - destruct j as [|[|j]]; simpl in Hj; [| |discriminate];
              injection Hj as <-; [|done].
            rewrite mb_MPX_y in Hmb. discriminate. }
        subst j. exists q. split; [exact Hq|].
        pose proof (visibleb_foreign 1%nat tv' (c_log c) (c_dl c) q 1%nat m Hq Hj
                      ltac:(rewrite (mpf_W_tid _ _ _ HW _ _ Hj) //) Hvis). lia.
    + (* fence r,r: the floor passes the watermark *)
      destruct Hst as (_ & Hlog & Hdl & Hharts).
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. rewrite Hlog Hdl. split_and!.
      * exact HW.
      * exact Hord.
      * right; right; left. split; [reflexivity|]. intros Hv.
        destruct (Hc Hv) as (qy & Hqy & Hrv). exists qy. split; [exact Hqy|].
        pose proof (fence_post_acq 1%nat (c_log c) (c_dl c) true false true false tv1 rv1
                      eq_refl). lia.
    + (* load rg2 <- x: at or above the floor, hence past the data's position *)
      destruct Hst as (tv' & v & Hok' & Hlog & Hdl & Hharts).
      destruct Hok' as (Hle & Hcoh & Hlen & Hread). rewrite Himg in Hread.
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. rewrite Hlog Hdl. split_and!.
      * exact HW.
      * exact Hord.
      * right; right; right. split; [reflexivity|].
        rewrite lookup_insert_ne // lookup_insert.
        intros Hv. destruct (Hc Hv) as (qy & Hqy & Htv).
        destruct (Hord _ Hqy) as (qx & Hqx & Hlt).
        (* the flag has drained, so the log has both messages *)
        assert (Hl : c_log c = [MPX; MPY]).
        { destruct Hok as [_ Hb].
          pose proof (Hb _ (elem_of_list_lookup_2 _ _ _ Hqy)) as H1.
          destruct HW as [[_ Hl]|[[_ Hl]|[[_ [Hl _]]|[_ [Hl _]]]]]; [..|exact Hl];
            rewrite Hl in H1; simpl in H1; lia. }
        assert (Hvis : visibleb 1%nat tv' (c_log c) (c_dl c) (S qx) = true)
          by (apply visibleb_below; lia).
        destruct (tso_read_from_below img0 (c_log c) (c_dl c) 1%nat tv' ax qx 0%nat MPX b1 v
                    (mpf_R_pend _ _ _ ax HW) Hqx ltac:(rewrite Hl //) mb_MPX_x Hvis Hread)
          as (q' & j' & m' & _ & _ & Hj' & Hmb & _).
        rewrite Hl in Hj'.
        destruct j' as [|[|j']]; simpl in Hj'; [| |discriminate];
          injection Hj' as <-.
        { rewrite mb_MPX_x in Hmb. congruence. }
        rewrite mb_MPY_x in Hmb. discriminate.
Qed.

Lemma mpf_inv0 : mpf_inv mpf_c0.
Proof.
  split; [split; [done|split; [apply NoDup_nil_2|by intros ? ?%elem_of_nil]]|].
  eexists _, _. split; [reflexivity|]. simpl.
  split_and!; [by left| |by left].
  intros qy Hqy. rewrite lookup_nil in Hqy. discriminate.
Qed.

(** MP with the RVWMO fences: rg1 = 1 forces rg2 = 1. *)
Theorem mp_fence_forbidden c h0 regs tv rv coh :
  reach mpf_c0 c →
  c_harts c = [h0; Hart [] regs tv rv coh] →
  regs !! rg1 = Some b1 → regs !! rg2 = Some b1.
Proof.
  intros Hre Hh H1.
  assert (Hinv : mpf_inv c).
  { eapply inv_reach; [apply mpf_inv0| |exact Hre]. intros. by eapply mpf_step. }
  destruct Hinv as (_ & g0 & g1 & Hh' & _ & _ & HR).
  rewrite Hh in Hh'. simplify_eq/=.
  destruct HR as [Hc|[[Hc _]|[[Hc _]|[_ Himp]]]]; try discriminate. by apply Himp.
Qed.

(** Non-vacuity: the fenced reader can and does read the flag as 1 — and
    then, as the theorem says, the data too. *)
Lemma mpf_completed_reachable :
  ∃ c h0 regs tv rv coh,
    reach mpf_c0 c ∧ c_harts c = [h0; Hart [] regs tv rv coh] ∧
    regs !! rg1 = Some b1 ∧ regs !! rg2 = Some b1.
Proof.
  rewrite /mpf_c0. eexists _, _, _, _, _, _. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 0%nat); solve_drain|]. simpl.
    eapply rtc_l; [eapply (step_fence _ 0%nat); [reflexivity|solve_fence]|]. simpl.
    eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 1%nat); solve_drain|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg1 ay _ _ _ _ _ 2%nat b1);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l; [eapply (step_fence _ 1%nat); [reflexivity|solve_fence]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg2 ax _ _ _ _ _ 2%nat b1);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
Qed.

(* ================================================================== *)
(** ** MP + addr — the reader's second load is ADDRESS-DEPENDENT on the
       first, with no fence.  RVWMO FORBIDS the weak outcome (ppo rule 9);
       this machine ALLOWS it, because syntactic dependencies are not
       modelled (relaxed-rr.md §5).  Recorded as the standing reminder that
       a proof may appeal to a fence or an [.aq] for ordering, never to a
       dependency.

    The pointer cell [ay] is published as [b1] = address 1 = [az]; the
    reader loads the pointer (sees 1) and then the byte it points to. *)

Definition mpa_c0 : config :=
  Cfg img0 [] [] [Hart [IStore az b1; FENCE_WW; IStore ay b1] ∅ 0%nat 0%nat coh0;
                  Hart [ILoad rg1 ay; ILoadInd rg1 rg2] ∅ 0%nat 0%nat coh0].

Lemma mp_addr_allowed :
  ∃ c h0 regs tv rv coh,
    reach mpa_c0 c ∧ c_harts c = [h0; Hart [] regs tv rv coh] ∧
    regs !! rg1 = Some b1 ∧ regs !! rg2 = Some b0.
Proof.
  rewrite /mpa_c0. eexists _, _, _, _, _, _. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 0%nat); solve_drain|]. simpl.
    eapply rtc_l; [eapply (step_fence _ 0%nat); [reflexivity|solve_fence]|]. simpl.
    eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 1%nat); solve_drain|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg1 ay _ _ _ _ _ 2%nat b1);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l;
      [eapply (step_load_ind _ 1%nat rg1 rg2 _ _ _ _ _ 0%nat b0);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
Qed.


(* ================================================================== *)
(** ** CoRR — read-read coherence.  Reading a fresh value and then a stale
       one is FORBIDDEN (herd: forbidden).

    THE PER-BYTE COHERENCE FLOOR AT WORK: the first load records its view
    at [ax], and the second load of [ax] must read at or above it.  Without
    [coh] the relaxed reader could read 2 then 1.

    Two verdicts, both non-vacuous.  [corr_no_stale]: once C has seen a
    drained write it can never read the era-initial byte again.
    [corr_forbidden]: on the run whose DRAIN order is x=1 then x=2, C that
    read 2 must read 2 again. *)

Local Notation CX1 := (WMsg ax [b1] 0%nat).
Local Notation CX2 := (WMsg ax [b2] 1%nat).

Lemma CX1_ne_CX2 : CX1 ≠ CX2.
Proof.
  intros H. apply b1_ne_b2.
  exact (f_equal (λ m, default b0 (wm_data m !! 0%nat)) H).
Qed.
Lemma mb_CX1 : msg_byte CX1 ax = Some b1.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_CX2 : msg_byte CX2 ax = Some b2.
Proof. rewrite msg_byte_single //. Qed.

Definition corr_c0 : config :=
  Cfg img0 [] [] [Hart [IStore ax b1] ∅ 0%nat 0%nat coh0;
                  Hart [IStore ax b2] ∅ 0%nat 0%nat coh0;
                  Hart [ILoad rg1 ax; ILoad rg2 ax] ∅ 0%nat 0%nat coh0].

Definition corr_content (log : list wmsg) : Prop :=
  ∀ m, m ∈ log → m = CX1 ∨ m = CX2.

Lemma corr_content_app log m :
  corr_content log → (m = CX1 ∨ m = CX2) → corr_content (log ++ [m]).
Proof.
  intros Hc Hm m' Hin. apply elem_of_app in Hin as [Hin|Hin]; [by apply Hc|].
  apply elem_of_list_singleton in Hin as ->. done.
Qed.

Lemma corr_pend log dl : corr_content log → pend_read log dl 2%nat ax = None.
Proof.
  intros Hc. apply pend_read_none_of. intros i m Hi Htid _.
  by destruct (Hc m (elem_of_list_lookup_2 _ _ _ Hi)) as [->| ->].
Qed.

(** The reader's middle phase is stated on its COHERENCE FLOOR at [ax], not
    on its view: that is the one thing the second load is bounded by. *)
Definition corr_C (p : list instr) (regs : gmap nat (bv 8)) (coh : cohmap)
    (log : list wmsg) (dl : list nat) : Prop :=
  (p = [ILoad rg1 ax; ILoad rg2 ax]) ∨
  (p = [ILoad rg2 ax] ∧
     (regs !! rg1 = Some b1 → ∃ q, at_pos log dl q CX1 ∧ (S q ≤ coh ax)%nat) ∧
     (regs !! rg1 = Some b2 → ∃ q, at_pos log dl q CX2 ∧ (S q ≤ coh ax)%nat)) ∨
  (p = [] ∧
     ((regs !! rg1 = Some b1 ∨ regs !! rg1 = Some b2) →
        regs !! rg2 ≠ Some b0) ∧
     (regs !! rg1 = Some b2 →
        regs !! rg2 = Some b2 ∨
        ∃ q1 q2, at_pos log dl q1 CX1 ∧ at_pos log dl q2 CX2 ∧ (q2 ≤ q1)%nat)).

Lemma corr_C_app_log p regs coh log dl m :
  dl_ok log dl → corr_C p regs coh log dl → corr_C p regs coh (log ++ [m]) dl.
Proof.
  intros Hok [->|[[-> [H1 H2]]|[-> [H1 H2]]]].
  - by left.
  - right; left. split; [done|]. split.
    + intros Hr. destruct (H1 Hr) as (q & Hq & ?). exists q.
      split; [by apply at_pos_app_log|done].
    + intros Hr. destruct (H2 Hr) as (q & Hq & ?). exists q.
      split; [by apply at_pos_app_log|done].
  - right; right. split; [done|]. split; [exact H1|].
    intros Hr. destruct (H2 Hr) as [?|(q1 & q2 & Hq1 & Hq2 & Hle)]; [by left|].
    right. exists q1, q2. split_and!; by [apply at_pos_app_log|].
Qed.

Lemma corr_C_app_dl p regs coh log dl i :
  corr_C p regs coh log dl → corr_C p regs coh log (dl ++ [i]).
Proof.
  intros [->|[[-> [H1 H2]]|[-> [H1 H2]]]].
  - by left.
  - right; left. split; [done|]. split.
    + intros Hr. destruct (H1 Hr) as (q & Hq & ?). exists q.
      split; [by apply at_pos_app_dl|done].
    + intros Hr. destruct (H2 Hr) as (q & Hq & ?). exists q.
      split; [by apply at_pos_app_dl|done].
  - right; right. split; [done|]. split; [exact H1|].
    intros Hr. destruct (H2 Hr) as [?|(q1 & q2 & Hq1 & Hq2 & Hle)]; [by left|].
    right. exists q1, q2. split_and!; by [apply at_pos_app_dl|].
Qed.

Definition corr_inv (c : config) : Prop :=
  wf img0 c ∧
  ∃ h0 h1 h2, c_harts c = [h0; h1; h2] ∧ corr_content (c_log c) ∧
    (h_prog h0 = [IStore ax b1] ∨ h_prog h0 = []) ∧
    (h_prog h1 = [IStore ax b2] ∨ h_prog h1 = []) ∧
    corr_C (h_prog h2) (h_regs h2) (h_coh h2) (c_log c) (c_dl c).

Lemma corr_step c c' : corr_inv c → lstep c c' → corr_inv c'.
Proof.
  intros Hinv Hstep.
  assert (Hwf' : wf img0 c') by (eapply wf_step; [apply Hinv|exact Hstep]).
  destruct Hinv as ([Himg Hok] & [p0 regs0 tv0 rv0 coh0'] & [p1 regs1 tv1 rv1 coh1]
          & [p2 regs2 tv2 rv2 coh2] & Hh & Hcont & H0 & H1 & HC).
  simpl in H0, H1, HC.
  destruct Hstep as [Hstep|Hstep]; last first.
  { destruct Hstep as (i & Hdr & Himg' & Hlog & Hdl & Hharts).
    split; [done|]. eexists _, _, _. rewrite Hharts Hh Hlog Hdl /drain_log.
    split; [reflexivity|]. split_and!; [done|done|done|by apply corr_C_app_dl]. }
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|[|[|i]]]; simpl in Hlk; simplify_eq/=.
  - (* writer 0: x := 1 *)
    destruct H0 as [->| ->]; simpl in Hst; [|done].
    destruct Hst as (Hlog & Hdl & Hharts).
    split; [done|]. eexists _, _, _.
    split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
    rewrite Hlog Hdl /store_log. split_and!.
    + apply corr_content_app; [exact Hcont|by left].
    + by right.
    + exact H1.
    + by apply corr_C_app_log.
  - (* writer 1: x := 2 *)
    destruct H1 as [->| ->]; simpl in Hst; [|done].
    destruct Hst as (Hlog & Hdl & Hharts).
    split; [done|]. eexists _, _, _.
    split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
    rewrite Hlog Hdl /store_log. split_and!.
    + apply corr_content_app; [exact Hcont|by right].
    + exact H0.
    + by right.
    + by apply corr_C_app_log.
  - (* the reader *)
    destruct HC as [->|[[-> [Hc1 Hc2]]|[-> _]]]; simpl in Hst; [| |done].
    + (* first load: the coherence floor at [ax] becomes this view *)
      destruct Hst as (tv' & v & Hok' & Hlog & Hdl & Hharts).
      destruct Hok' as (Hle & Hcoh & Hlen & Hread). rewrite Himg in Hread.
      split; [done|]. eexists _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl. split_and!; [exact Hcont|exact H0|exact H1|].
      right; left. split; [reflexivity|]. rewrite lookup_insert coh_upd_eq. split.
      * intros Hv. assert (v = b1) as -> by congruence.
        destruct (tso_read_src _ _ _ _ _ _ _ (corr_pend _ _ Hcont) Hread)
          as [Hi|(q & j & m & Hq & Hj & Hmb & Hvis)].
        { by destruct (img0_x_nb1 Hi). }
        destruct (Hcont m (elem_of_list_lookup_2 _ _ _ Hj)) as [-> | ->];
          last first.
        { rewrite mb_CX2 in Hmb. destruct b1_ne_b2. congruence. }
        exists q. split; [by exists j|].
        eapply (visibleb_foreign 2%nat tv' (c_log c) (c_dl c) q j CX1);
          [exact Hq|exact Hj|done|done].
      * intros Hv. assert (v = b2) as -> by congruence.
        destruct (tso_read_src _ _ _ _ _ _ _ (corr_pend _ _ Hcont) Hread)
          as [Hi|(q & j & m & Hq & Hj & Hmb & Hvis)].
        { by destruct (img0_x_nb2 Hi). }
        destruct (Hcont m (elem_of_list_lookup_2 _ _ _ Hj)) as [-> | ->].
        { rewrite mb_CX1 in Hmb. destruct b1_ne_b2. congruence. }
        exists q. split; [by exists j|].
        eapply (visibleb_foreign 2%nat tv' (c_log c) (c_dl c) q j CX2);
          [exact Hq|exact Hj|done|done].
    + (* second load: bounded below by the coherence floor *)
      destruct Hst as (tv' & v & Hok' & Hlog & Hdl & Hharts).
      destruct Hok' as (Hle & Hcoh & Hlen & Hread). rewrite Himg in Hread.
      split; [done|]. eexists _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl. split_and!; [exact Hcont|exact H0|exact H1|].
      right; right. split; [reflexivity|].
      rewrite lookup_insert_ne // lookup_insert. split.
      * (* no stale read *)
        intros [Hv|Hv] Hv2; assert (v = b0) as -> by congruence.
        -- destruct (Hc1 Hv) as (q & (j & Hq & Hj) & Hjc).
           assert (Hvis : visibleb 2%nat tv' (c_log c) (c_dl c) (S q) = true)
             by (apply visibleb_below; lia).
           destruct (tso_read_from_below img0 (c_log c) (c_dl c) 2%nat tv' ax q j CX1 b1 b0
                       (corr_pend _ _ Hcont) Hq Hj mb_CX1 Hvis Hread)
             as (q' & j' & m' & _ & _ & Hj' & Hmb & _).
           destruct (Hcont m' (elem_of_list_lookup_2 _ _ _ Hj')) as [-> | ->].
           ++ rewrite mb_CX1 in Hmb. apply b0_ne_b1. congruence.
           ++ rewrite mb_CX2 in Hmb. apply b0_ne_b2. congruence.
        -- destruct (Hc2 Hv) as (q & (j & Hq & Hj) & Hjc).
           assert (Hvis : visibleb 2%nat tv' (c_log c) (c_dl c) (S q) = true)
             by (apply visibleb_below; lia).
           destruct (tso_read_from_below img0 (c_log c) (c_dl c) 2%nat tv' ax q j CX2 b2 b0
                       (corr_pend _ _ Hcont) Hq Hj mb_CX2 Hvis Hread)
             as (q' & j' & m' & _ & _ & Hj' & Hmb & _).
           destruct (Hcont m' (elem_of_list_lookup_2 _ _ _ Hj')) as [-> | ->].
           ++ rewrite mb_CX1 in Hmb. apply b0_ne_b1. congruence.
           ++ rewrite mb_CX2 in Hmb. apply b0_ne_b2. congruence.
      * (* coherence *)
        intros Hv. destruct (Hc2 Hv) as (q & (j & Hq & Hj) & Hjc).
        assert (Hvis : visibleb 2%nat tv' (c_log c) (c_dl c) (S q) = true)
          by (apply visibleb_below; lia).
        destruct (tso_read_from_below img0 (c_log c) (c_dl c) 2%nat tv' ax q j CX2 b2 v
                    (corr_pend _ _ Hcont) Hq Hj mb_CX2 Hvis Hread)
          as (q' & j' & m' & Hge & Hq' & Hj' & Hmb & _).
        destruct (Hcont m' (elem_of_list_lookup_2 _ _ _ Hj')) as [-> | ->].
        -- right. exists q', q. rewrite mb_CX1 in Hmb.
           split_and!; [by exists j'|by exists j|lia].
        -- left. rewrite mb_CX2 in Hmb. congruence.
Qed.

Lemma corr_inv0 : corr_inv corr_c0.
Proof.
  split; [split; [done|split; [apply NoDup_nil_2|by intros ? ?%elem_of_nil]]|].
  eexists _, _, _. split; [reflexivity|]. simpl.
  split_and!; [by intros ? ?%elem_of_nil|by left|by left|by left].
Qed.

(** CoRR, part 1: after a fresh read, the era-initial byte is gone forever. *)
Theorem corr_no_stale c h0 h1 regs tv rv coh :
  reach corr_c0 c →
  c_harts c = [h0; h1; Hart [] regs tv rv coh] →
  (regs !! rg1 = Some b1 ∨ regs !! rg1 = Some b2) → regs !! rg2 ≠ Some b0.
Proof.
  intros Hre Hh H1.
  assert (Hinv : corr_inv c).
  { eapply inv_reach; [apply corr_inv0| |exact Hre].
    intros. by eapply corr_step. }
  destruct Hinv as (_ & g0 & g1 & g2 & Hh' & _ & _ & _ & HC).
  rewrite Hh in Hh'. simplify_eq/=.
  destruct HC as [Hc|[[Hc _]|[_ [Himp _]]]]; try discriminate. by apply Himp.
Qed.

(** CoRR, part 2: on the execution whose DRAIN order is x=1 then x=2, a
    reader that saw 2 cannot go back to 1 — it must see 2 again. *)
Theorem corr_forbidden c h0 h1 regs tv rv coh j1 j2 :
  reach corr_c0 c →
  c_harts c = [h0; h1; Hart [] regs tv rv coh] →
  c_log c !! j1 = Some CX1 → c_log c !! j2 = Some CX2 → c_dl c = [j1; j2] →
  regs !! rg1 = Some b2 → regs !! rg2 = Some b2.
Proof.
  intros Hre Hh Hj1 Hj2 Hdl H1.
  assert (Hinv : corr_inv c).
  { eapply inv_reach; [apply corr_inv0| |exact Hre].
    intros. by eapply corr_step. }
  destruct Hinv as (_ & g0 & g1 & g2 & Hh' & _ & _ & _ & HC).
  rewrite Hh in Hh'. simplify_eq/=.
  destruct HC as [Hc|[[Hc _]|[_ [_ Himp]]]]; try discriminate.
  destruct (Himp H1) as [?|(q1 & q2 & (k1 & Hq1 & Hk1) & (k2 & Hq2 & Hk2) & Hle)];
    [done|].
  exfalso. rewrite Hdl in Hq1 Hq2.
  destruct q1 as [|[|q1]]; simpl in Hq1; [| |discriminate]; injection Hq1 as <-.
  - (* x=1 drained first, so x=2 must be at 0 too: the same message twice *)
    destruct q2 as [|q2]; simpl in Hq2; [|lia].
    injection Hq2 as <-. assert (CX1 = CX2) as Hc by congruence.
    exact (CX1_ne_CX2 Hc).
  - (* position 1 holds x=2, not x=1 *)
    assert (CX1 = CX2) as Hc by congruence. exact (CX1_ne_CX2 Hc).
Qed.

(** Non-vacuity: the drain order [CX1; CX2] and the first read of 2 are both
    reachable. *)
Lemma corr_completed_reachable :
  ∃ c h0 h1 regs tv rv coh,
    reach corr_c0 c ∧ c_harts c = [h0; h1; Hart [] regs tv rv coh] ∧
    c_log c = [CX1; CX2] ∧ c_dl c = [0%nat; 1%nat] ∧
    regs !! rg1 = Some b2 ∧ regs !! rg2 = Some b2.
Proof.
  rewrite /corr_c0. eexists _, _, _, _, _, _, _. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 1%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 0%nat); solve_drain|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 1%nat); solve_drain|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 2%nat rg1 ax _ _ _ _ _ 2%nat b2);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 2%nat rg2 ax _ _ _ _ _ 2%nat b2);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
Qed.

(* ================================================================== *)
(** ** CoWW — write-write coherence, one writer.  x=1 then x=2 in program
       order drain in that order: FORBIDDEN to drain x=2 first (herd:
       forbidden).  This is the drain rule's per-byte FIFO, exhibited as a
       fact about every reachable drain log. *)

Local Notation WW1 := (WMsg ax [b1] 0%nat).
Local Notation WW2 := (WMsg ax [b2] 0%nat).

Lemma WW1_ne_WW2 : WW1 ≠ WW2.
Proof.
  intros H. apply b1_ne_b2.
  exact (f_equal (λ m, default b0 (wm_data m !! 0%nat)) H).
Qed.

Lemma mb_WW1 : msg_byte WW1 ax = Some b1.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_WW2 : msg_byte WW2 ax = Some b2.
Proof. rewrite msg_byte_single //. Qed.

Definition coww_c0 : config :=
  Cfg img0 [] [] [Hart [IStore ax b1; IStore ax b2] ∅ 0%nat 0%nat coh0].

Definition coww_inv (c : config) : Prop :=
  wf img0 c ∧
  (∃ h0, c_harts c = [h0] ∧
     ((h_prog h0 = [IStore ax b1; IStore ax b2] ∧ c_log c = []) ∨
      (h_prog h0 = [IStore ax b2] ∧ c_log c = [WW1]) ∨
      (h_prog h0 = [] ∧ c_log c = [WW1; WW2]))) ∧
  (∀ q, c_dl c !! q = Some 1%nat → ∃ q', (q' < q)%nat ∧ c_dl c !! q' = Some 0%nat).

Lemma coww_step c c' : coww_inv c → lstep c c' → coww_inv c'.
Proof.
  intros Hinv Hstep.
  assert (Hwf' : wf img0 c') by (eapply wf_step; [apply Hinv|exact Hstep]).
  destruct Hinv as ([Himg Hok] & ([p0 regs0 tv0 rv0 coh0'] & Hh & HP) & Hord).
  simpl in HP.
  destruct Hstep as [Hstep|Hstep]; last first.
  { destruct Hstep as (i & Hdr & Himg' & Hlog & Hdl & Hharts).
    split; [done|]. rewrite Hharts Hh Hlog Hdl /drain_log. split.
    { eexists. split; [reflexivity|exact HP]. }
    intros q Hq. apply lookup_app_last in Hq as [[_ Hq]|[-> <-]].
    - destruct (Hord _ Hq) as (q' & ? & Hq'). exists q'.
      split; [done|by apply lookup_app_l_Some].
    - (* x=2 drains now: the FIFO says x=1 has drained *)
      destruct (drain_ok_issued _ _ _ Hdr) as [m Hm].
      assert (Hl : c_log c = [WW1; WW2]).
      { destruct HP as [[_ Hl]|[[_ Hl]|[_ Hl]]]; [..|exact Hl];
          rewrite Hl in Hm; simpl in Hm; discriminate. }
      rewrite Hl in Hm. simpl in Hm. injection Hm as <-.
      pose proof (drain_ok_fifo (c_log c) (c_dl c) 1%nat 0%nat WW2 WW1 Hdr
                    ltac:(lia) ltac:(rewrite Hl //) ltac:(rewrite Hl //) eq_refl
                    (msg_overlapb_of_byte _ _ ax _ _ mb_WW1 mb_WW2)) as Hin.
      apply elem_of_list_lookup_1 in Hin as [q' Hq']. exists q'.
      split; [by eapply lookup_lt_Some|by apply lookup_app_l_Some]. }
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|i]; simpl in Hlk; simplify_eq/=.
  destruct HP as [[-> Hl]|[[-> Hl]|[-> Hl]]]; simpl in Hst; [| |done].
  - destruct Hst as (Hlog & Hdl & Hharts).
    split; [done|]. rewrite Hdl. split; [|exact Hord].
    eexists. rewrite Hharts Hh /=. split; [reflexivity|]. simpl.
    right; left. split; [reflexivity|]. rewrite Hlog /store_log Hl //.
  - destruct Hst as (Hlog & Hdl & Hharts).
    split; [done|]. rewrite Hdl. split; [|exact Hord].
    eexists. rewrite Hharts Hh /=. split; [reflexivity|]. simpl.
    right; right. split; [reflexivity|]. rewrite Hlog /store_log Hl //.
Qed.

Lemma coww_inv0 : coww_inv coww_c0.
Proof.
  split; [split; [done|split; [apply NoDup_nil_2|by intros ? ?%elem_of_nil]]|].
  split; [eexists; split; [reflexivity|by left]|].
  intros q Hq. rewrite lookup_nil in Hq. discriminate.
Qed.

(** CoWW: wherever both have drained, x=1 sits below x=2. *)
Theorem coww_forbidden c q1 q2 :
  reach coww_c0 c →
  at_pos (c_log c) (c_dl c) q1 WW1 → at_pos (c_log c) (c_dl c) q2 WW2 →
  (q1 < q2)%nat.
Proof.
  intros Hre (k1 & Hq1 & Hk1) (k2 & Hq2 & Hk2).
  assert (Hinv : coww_inv c).
  { eapply inv_reach; [apply coww_inv0| |exact Hre]. intros. by eapply coww_step. }
  destruct Hinv as ([_ [Hnd _]] & (g0 & _ & HP) & Hord).
  assert (Hl : c_log c = [WW1; WW2]).
  { destruct HP as [[_ Hl]|[[_ Hl]|[_ Hl]]]; [..|exact Hl]; rewrite Hl in Hk2.
    - rewrite lookup_nil in Hk2. discriminate.
    - destruct k2 as [|k2]; simpl in Hk2; [|discriminate].
      assert (WW1 = WW2) as Hc by congruence. by destruct (WW1_ne_WW2 Hc). }
  rewrite Hl in Hk1 Hk2.
  assert (k2 = 1%nat) as ->.
  { destruct k2 as [|[|k2]]; simpl in Hk2; [|done|discriminate].
    assert (WW1 = WW2) as Hc by congruence. by destruct (WW1_ne_WW2 Hc). }
  assert (k1 = 0%nat) as ->.
  { destruct k1 as [|[|k1]]; simpl in Hk1; [done| |discriminate].
    assert (WW1 = WW2) as Hc by congruence. by destruct (WW1_ne_WW2 Hc). }
  destruct (Hord _ Hq2) as (q' & Hlt & Hq').
  by rewrite (NoDup_lookup _ _ _ _ Hnd Hq1 Hq').
Qed.

Lemma coww_completed_reachable :
  ∃ c, reach coww_c0 c ∧ c_log c = [WW1; WW2] ∧ c_dl c = [0%nat; 1%nat].
Proof.
  rewrite /coww_c0. eexists. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 0%nat); solve_drain|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 1%nat); solve_drain|]. simpl.
    apply rtc_refl. }
  done.
Qed.

(* ================================================================== *)
(** ** LB — load buffering.  Both loads returning 1 is FORBIDDEN (herd:
       ALLOWED under RVWMO — this machine keeps R→W order, so the issue
       log cannot contain a store that its own hart's earlier load has not
       resolved; a deliberate over-promise, relaxed-rr.md §2.3). *)

Local Notation LBX := (WMsg ax [b1] 0%nat).   (* hart 0's store *)
Local Notation LBY := (WMsg ay [b1] 1%nat).   (* hart 1's store *)

Lemma LBX_ne_LBY : LBX ≠ LBY.
Proof. intros H. by simplify_eq/=. Qed.
Lemma mb_LBX_x : msg_byte LBX ax = Some b1.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_LBX_y : msg_byte LBX ay = None.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_LBY_x : msg_byte LBY ax = None.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_LBY_y : msg_byte LBY ay = Some b1.
Proof. rewrite msg_byte_single //. Qed.

Definition lb_c0 : config :=
  Cfg img0 [] [] [Hart [ILoad rg1 ay; IStore ax b1] ∅ 0%nat 0%nat coh0;
                  Hart [ILoad rg2 ax; IStore ay b1] ∅ 0%nat 0%nat coh0].

Definition lb_content (log : list wmsg) : Prop :=
  ∀ m, m ∈ log → m = LBX ∨ m = LBY.

Lemma lb_content_app log m :
  lb_content log → (m = LBX ∨ m = LBY) → lb_content (log ++ [m]).
Proof.
  intros Hc Hm m' Hin. apply elem_of_app in Hin as [Hin|Hin]; [by apply Hc|].
  apply elem_of_list_singleton in Hin as ->. done.
Qed.

Lemma lb_pend_0 log dl : lb_content log → pend_read log dl 0%nat ay = None.
Proof.
  intros Hc. apply pend_read_none_of. intros i m Hi Htid _.
  destruct (Hc m (elem_of_list_lookup_2 _ _ _ Hi)) as [->| ->]; [apply mb_LBX_y|done].
Qed.

Lemma lb_pend_1 log dl : lb_content log → pend_read log dl 1%nat ax = None.
Proof.
  intros Hc. apply pend_read_none_of. intros i m Hi Htid _.
  destruct (Hc m (elem_of_list_lookup_2 _ _ _ Hi)) as [->| ->]; [done|apply mb_LBY_x].
Qed.

(** The invariant: each hart's own message is absent from the issue log
    until it stores, a load that returned 1 witnesses the OTHER hart's
    message (drained, hence issued), and the two "returned 1"s are mutually
    exclusive — the last conjunct is established at whichever load runs
    second and is stable thereafter.  Nothing here mentions the drain log,
    so a drain preserves it outright. *)
Definition lb_inv (c : config) : Prop :=
  wf img0 c ∧
  ∃ h0 h1, c_harts c = [h0; h1] ∧ lb_content (c_log c) ∧
    ((h_prog h0 = [ILoad rg1 ay; IStore ax b1] ∨
      h_prog h0 = [IStore ax b1]) → LBX ∉ c_log c) ∧
    ((h_prog h1 = [ILoad rg2 ax; IStore ay b1] ∨
      h_prog h1 = [IStore ay b1]) → LBY ∉ c_log c) ∧
    (h_prog h0 = [ILoad rg1 ay; IStore ax b1] ∨
     h_prog h0 = [IStore ax b1] ∨ h_prog h0 = []) ∧
    (h_prog h1 = [ILoad rg2 ax; IStore ay b1] ∨
     h_prog h1 = [IStore ay b1] ∨ h_prog h1 = []) ∧
    (LBY ∈ c_log c → h_prog h1 = []) ∧
    (h_regs h1 !! rg2 = Some b1 → LBX ∈ c_log c) ∧
    (h_regs h0 !! rg1 = Some b1 → LBY ∈ c_log c) ∧
    ¬ (h_regs h0 !! rg1 = Some b1 ∧ h_regs h1 !! rg2 = Some b1).

Lemma lb_step c c' : lb_inv c → lstep c c' → lb_inv c'.
Proof.
  intros Hinv Hstep.
  assert (Hwf' : wf img0 c') by (eapply wf_step; [apply Hinv|exact Hstep]).
  destruct Hinv as ([Himg Hok] & [p0 regs0 tv0 rv0 coh0'] & [p1 regs1 tv1 rv1 coh1]
          & Hh & Hcont & Hn0 & Hn1 & Hp0 & Hp1 & Hy1 & Hr1 & Hr0 & Hno).
  simpl in Hn0, Hn1, Hp0, Hp1, Hy1, Hr1, Hr0, Hno.
  destruct Hstep as [Hstep|Hstep]; last first.
  { destruct Hstep as (i & Hdr & Himg' & Hlog & Hdl & Hharts).
    split; [done|]. eexists _, _. rewrite Hharts Hh Hlog.
    split; [reflexivity|]. simpl. by split_and!. }
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|[|i]]; simpl in Hlk; simplify_eq/=.
  - (* ---- hart 0 ---- *)
    destruct Hp0 as [->|[->| ->]]; simpl in Hst; [| |done].
    + (* load rg1 <- y *)
      destruct Hst as (tv' & v & Hok' & Hlog & Hdl & Hharts).
      destruct Hok' as (Hle & Hcoh & Hlen & Hread). rewrite Himg in Hread.
      assert (HnX : LBX ∉ c_log c) by (apply Hn0; by left).
      assert (Hv : v = b1 → LBY ∈ c_log c).
      { intros ->.
        destruct (tso_read_src _ _ _ _ _ _ _ (lb_pend_0 _ _ Hcont) Hread)
          as [Hi|(q & j & m & Hq & Hj & Hmb & Hvis)].
        { by destruct (img0_y_nb1 Hi). }
        destruct (Hcont m (elem_of_list_lookup_2 _ _ _ Hj)) as [-> | ->].
        { rewrite mb_LBX_y in Hmb. done. }
        by eapply elem_of_list_lookup_2. }
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog. split_and!.
      * exact Hcont.
      * intros _. exact HnX.
      * exact Hn1.
      * by right; left.
      * exact Hp1.
      * exact Hy1.
      * exact Hr1.
      * rewrite lookup_insert. intros Hv1.
        assert (v = b1) as -> by congruence. by apply Hv.
      * rewrite lookup_insert. intros [Hv1 Hv2].
        assert (v = b1) as Hvb by congruence.
        specialize (Hr1 Hv2). done.
    + (* store x *)
      destruct Hst as (Hlog & Hdl & Hharts).
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog /store_log. split_and!.
      * apply lb_content_app; [exact Hcont|by left].
      * intros [Hc|Hc]; discriminate.
      * intros Hc. apply not_elem_of_app. split; [by apply Hn1|].
        intros Hin%elem_of_list_singleton.
        by destruct (LBX_ne_LBY (eq_sym Hin)).
      * by right; right.
      * exact Hp1.
      * intros Hin. apply Hy1. apply elem_of_app in Hin as [Hin|Hin]; [done|].
        apply elem_of_list_singleton in Hin.
        by destruct (LBX_ne_LBY (eq_sym Hin)).
      * intros Hv. apply elem_of_app. left. by apply Hr1.
      * intros Hv. apply elem_of_app. left. by apply Hr0.
      * exact Hno.
  - (* ---- hart 1 ---- *)
    destruct Hp1 as [->|[->| ->]]; simpl in Hst; [| |done].
    + (* load rg2 <- x *)
      destruct Hst as (tv' & v & Hok' & Hlog & Hdl & Hharts).
      destruct Hok' as (Hle & Hcoh & Hlen & Hread). rewrite Himg in Hread.
      assert (HnY : LBY ∉ c_log c) by (apply Hn1; by left).
      assert (Hv : v = b1 → LBX ∈ c_log c).
      { intros ->.
        destruct (tso_read_src _ _ _ _ _ _ _ (lb_pend_1 _ _ Hcont) Hread)
          as [Hi|(q & j & m & Hq & Hj & Hmb & Hvis)].
        { by destruct (img0_x_nb1 Hi). }
        destruct (Hcont m (elem_of_list_lookup_2 _ _ _ Hj)) as [-> | ->];
          last first.
        { rewrite mb_LBY_x in Hmb. done. }
        by eapply elem_of_list_lookup_2. }
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog. split_and!.
      * exact Hcont.
      * exact Hn0.
      * intros _. exact HnY.
      * exact Hp0.
      * by right; left.
      * intros Hin. by destruct (HnY Hin).
      * rewrite lookup_insert. intros Hv2.
        assert (v = b1) as -> by congruence. by apply Hv.
      * exact Hr0.
      * rewrite lookup_insert. intros [Hv1 Hv2].
        assert (v = b1) as Hvb by congruence.
        specialize (Hr0 Hv1). done.
    + (* store y *)
      destruct Hst as (Hlog & Hdl & Hharts).
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog /store_log. split_and!.
      * apply lb_content_app; [exact Hcont|by right].
      * intros Hc. apply not_elem_of_app. split; [by apply Hn0|].
        intros Hin%elem_of_list_singleton. by destruct (LBX_ne_LBY Hin).
      * intros [Hc|Hc]; discriminate.
      * exact Hp0.
      * by right; right.
      * intros _. reflexivity.
      * intros Hv. apply elem_of_app. left. by apply Hr1.
      * intros Hv. apply elem_of_app. left. by apply Hr0.
      * exact Hno.
Qed.

Lemma lb_inv0 : lb_inv lb_c0.
Proof.
  split; [split; [done|split; [apply NoDup_nil_2|by intros ? ?%elem_of_nil]]|].
  eexists _, _. split; [reflexivity|]. simpl.
  split_and!; try (intros; by apply not_elem_of_nil);
    [by intros ? ?%elem_of_nil|by left|by left| | | |].
  - intros Hin%elem_of_nil. done.
  - by intros ?%lookup_empty_Some.
  - by intros ?%lookup_empty_Some.
  - intros [H _]. by apply lookup_empty_Some in H.
Qed.

(** LB: rg1 = 1 ∧ rg2 = 1 is UNREACHABLE. *)
Theorem lb_forbidden c regs0 tv0 rv0 coh0' regs1 tv1 rv1 coh1 :
  reach lb_c0 c →
  c_harts c = [Hart [] regs0 tv0 rv0 coh0'; Hart [] regs1 tv1 rv1 coh1] →
  regs0 !! rg1 = Some b1 → regs1 !! rg2 ≠ Some b1.
Proof.
  intros Hre Hh Ha Hb.
  assert (Hinv : lb_inv c).
  { eapply inv_reach; [apply lb_inv0| |exact Hre]. intros. by eapply lb_step. }
  destruct Hinv as (_ & g0 & g1 & Hh' & _ & _ & _ & _ & _ & _ & _ & _ & Hno).
  rewrite Hh in Hh'. simplify_eq/=. by apply Hno.
Qed.

(** Non-vacuity: both LB harts complete; the machine produces (0, 1). *)
Lemma lb_completed_reachable :
  ∃ c regs0 tv0 rv0 coh0' regs1 tv1 rv1 coh1,
    reach lb_c0 c ∧
    c_harts c = [Hart [] regs0 tv0 rv0 coh0'; Hart [] regs1 tv1 rv1 coh1] ∧
    regs0 !! rg1 = Some b0 ∧ regs1 !! rg2 = Some b1.
Proof.
  rewrite /lb_c0. eexists _, _, _, _, _, _, _, _, _. split.
  { eapply rtc_l;
      [eapply (step_load _ 0%nat rg1 ay _ _ _ _ _ 0%nat b0);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 0%nat); solve_drain|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg2 ax _ _ _ _ _ 1%nat b1);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l; [eapply (step_store _ 1%nat); reflexivity|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split; rewrite lookup_insert //.
Qed.


(* ================================================================== *)
(** ** IRIW — independent reads of independent writes.  With NO fences the
       weak outcome is ALLOWED (herd: allowed under RVWMO): each reader
       takes its first load high and its second low. *)

Local Notation IX := (WMsg ax [b1] 0%nat).
Local Notation IY := (WMsg ay [b1] 1%nat).

Lemma mb_IX_x : msg_byte IX ax = Some b1.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_IX_y : msg_byte IX ay = None.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_IY_x : msg_byte IY ax = None.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_IY_y : msg_byte IY ay = Some b1.
Proof. rewrite msg_byte_single //. Qed.

Definition iriw_c0 : config :=
  Cfg img0 [] []
      [Hart [IStore ax b1] ∅ 0%nat 0%nat coh0;
       Hart [IStore ay b1] ∅ 0%nat 0%nat coh0;
       Hart [ILoad rg1 ax; ILoad rg2 ay] ∅ 0%nat 0%nat coh0;
       Hart [ILoad rg3 ay; ILoad rg4 ax] ∅ 0%nat 0%nat coh0].

Lemma iriw_allowed :
  ∃ c h0 h1 regs2 tv2 rv2 coh2 regs3 tv3 rv3 coh3,
    reach iriw_c0 c ∧
    c_harts c = [h0; h1; Hart [] regs2 tv2 rv2 coh2; Hart [] regs3 tv3 rv3 coh3] ∧
    regs2 !! rg1 = Some b1 ∧ regs2 !! rg2 = Some b0 ∧
    regs3 !! rg3 = Some b1 ∧ regs3 !! rg4 = Some b0.
Proof.
  rewrite /iriw_c0. eexists _, _, _, _, _, _, _, _, _, _, _. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 1%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 0%nat); solve_drain|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 1%nat); solve_drain|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 2%nat rg1 ax _ _ _ _ _ 1%nat b1);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 2%nat rg2 ay _ _ _ _ _ 0%nat b0);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 3%nat rg3 ay _ _ _ _ _ 2%nat b1);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 3%nat rg4 ax _ _ _ _ _ 0%nat b0);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split_and!.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
Qed.

(* ================================================================== *)
(** ** IRIW with [fence r,r] in both readers — FORBIDDEN (herd: forbidden
       under RVWMO, which is multi-copy atomic).

    The single drain log is the total store order, so "x reached memory
    before y" and "y reached memory before x" cannot both hold; the fences
    are what carry each reader's first observation to its second load. *)

Definition iriwf_c0 : config :=
  Cfg img0 [] []
      [Hart [IStore ax b1] ∅ 0%nat 0%nat coh0;
       Hart [IStore ay b1] ∅ 0%nat 0%nat coh0;
       Hart [ILoad rg1 ax; FENCE_RR; ILoad rg2 ay] ∅ 0%nat 0%nat coh0;
       Hart [ILoad rg3 ay; FENCE_RR; ILoad rg4 ax] ∅ 0%nat 0%nat coh0].

Definition iriw_content (log : list wmsg) : Prop :=
  ∀ m, m ∈ log → m = IX ∨ m = IY.

Lemma iriw_content_app log m :
  iriw_content log → (m = IX ∨ m = IY) → iriw_content (log ++ [m]).
Proof.
  intros Hc Hm m' Hin. apply elem_of_app in Hin as [Hin|Hin]; [by apply Hc|].
  apply elem_of_list_singleton in Hin as ->. done.
Qed.

Lemma iriw_pend log dl h a :
  iriw_content log → (2 ≤ h)%nat → pend_read log dl h a = None.
Proof.
  intros Hc Hh. apply pend_read_none_of. intros i m Hi Htid _.
  destruct (Hc m (elem_of_list_lookup_2 _ _ _ Hi)) as [->| ->]; simpl in Htid; lia.
Qed.

(** Reader C: x, fence, y.  The watermark carries the first observation to
    the fence, the floor carries it to the second load.  The final conjunct
    is "the x-message drained strictly below EVERY drain of the y-message"
    — stable under drains because a fresh drain lands past every existing
    position. *)
Definition iriw_C (p : list instr) (regs : gmap nat (bv 8)) (tv rv : nat)
    (log : list wmsg) (dl : list nat) : Prop :=
  (p = [ILoad rg1 ax; FENCE_RR; ILoad rg2 ay]) ∨
  (p = [FENCE_RR; ILoad rg2 ay] ∧
     (regs !! rg1 = Some b1 → ∃ q, at_pos log dl q IX ∧ (S q ≤ rv)%nat)) ∨
  (p = [ILoad rg2 ay] ∧
     (regs !! rg1 = Some b1 → ∃ q, at_pos log dl q IX ∧ (S q ≤ tv)%nat)) ∨
  (p = [] ∧
     (regs !! rg1 = Some b1 → regs !! rg2 = Some b0 →
        ∃ qx, at_pos log dl qx IX ∧ ∀ qy, at_pos log dl qy IY → (qx < qy)%nat)).

Definition iriw_D (p : list instr) (regs : gmap nat (bv 8)) (tv rv : nat)
    (log : list wmsg) (dl : list nat) : Prop :=
  (p = [ILoad rg3 ay; FENCE_RR; ILoad rg4 ax]) ∨
  (p = [FENCE_RR; ILoad rg4 ax] ∧
     (regs !! rg3 = Some b1 → ∃ q, at_pos log dl q IY ∧ (S q ≤ rv)%nat)) ∨
  (p = [ILoad rg4 ax] ∧
     (regs !! rg3 = Some b1 → ∃ q, at_pos log dl q IY ∧ (S q ≤ tv)%nat)) ∨
  (p = [] ∧
     (regs !! rg3 = Some b1 → regs !! rg4 = Some b0 →
        ∃ qy, at_pos log dl qy IY ∧ ∀ qx, at_pos log dl qx IX → (qy < qx)%nat)).

Lemma iriw_C_app_log p regs tv rv log dl m :
  dl_ok log dl → iriw_C p regs tv rv log dl → iriw_C p regs tv rv (log ++ [m]) dl.
Proof.
  intros Hok [->|[[-> H]|[[-> H]|[-> H]]]].
  - by left.
  - right; left. split; [done|]. intros Hr. destruct (H Hr) as (q & Hq & ?).
    exists q. split; [by apply at_pos_app_log|done].
  - right; right; left. split; [done|]. intros Hr. destruct (H Hr) as (q & Hq & ?).
    exists q. split; [by apply at_pos_app_log|done].
  - right; right; right. split; [done|]. intros H1 H2.
    destruct (H H1 H2) as (qx & Hqx & Hlt).
    exists qx. split; [by apply at_pos_app_log|].
    intros qy Hqy. apply Hlt. by eapply at_pos_app_log_inv.
Qed.

Lemma iriw_D_app_log p regs tv rv log dl m :
  dl_ok log dl → iriw_D p regs tv rv log dl → iriw_D p regs tv rv (log ++ [m]) dl.
Proof.
  intros Hok [->|[[-> H]|[[-> H]|[-> H]]]].
  - by left.
  - right; left. split; [done|]. intros Hr. destruct (H Hr) as (q & Hq & ?).
    exists q. split; [by apply at_pos_app_log|done].
  - right; right; left. split; [done|]. intros Hr. destruct (H Hr) as (q & Hq & ?).
    exists q. split; [by apply at_pos_app_log|done].
  - right; right; right. split; [done|]. intros H1 H2.
    destruct (H H1 H2) as (qy & Hqy & Hlt).
    exists qy. split; [by apply at_pos_app_log|].
    intros qx Hqx. apply Hlt. by eapply at_pos_app_log_inv.
Qed.

Lemma iriw_C_app_dl p regs tv rv log dl i :
  iriw_C p regs tv rv log dl → iriw_C p regs tv rv log (dl ++ [i]).
Proof.
  intros [->|[[-> H]|[[-> H]|[-> H]]]].
  - by left.
  - right; left. split; [done|]. intros Hr. destruct (H Hr) as (q & Hq & ?).
    exists q. split; [by apply at_pos_app_dl|done].
  - right; right; left. split; [done|]. intros Hr. destruct (H Hr) as (q & Hq & ?).
    exists q. split; [by apply at_pos_app_dl|done].
  - right; right; right. split; [done|]. intros H1 H2.
    destruct (H H1 H2) as (qx & Hqx & Hlt).
    exists qx. split; [by apply at_pos_app_dl|].
    intros qy Hqy. apply at_pos_app_dl_inv in Hqy as [Hqy|[-> _]].
    + by apply Hlt.
    + by apply at_pos_lt in Hqx.
Qed.

Lemma iriw_D_app_dl p regs tv rv log dl i :
  iriw_D p regs tv rv log dl → iriw_D p regs tv rv log (dl ++ [i]).
Proof.
  intros [->|[[-> H]|[[-> H]|[-> H]]]].
  - by left.
  - right; left. split; [done|]. intros Hr. destruct (H Hr) as (q & Hq & ?).
    exists q. split; [by apply at_pos_app_dl|done].
  - right; right; left. split; [done|]. intros Hr. destruct (H Hr) as (q & Hq & ?).
    exists q. split; [by apply at_pos_app_dl|done].
  - right; right; right. split; [done|]. intros H1 H2.
    destruct (H H1 H2) as (qy & Hqy & Hlt).
    exists qy. split; [by apply at_pos_app_dl|].
    intros qx Hqx. apply at_pos_app_dl_inv in Hqx as [Hqx|[-> _]].
    + by apply Hlt.
    + by apply at_pos_lt in Hqy.
Qed.

Definition iriwf_inv (c : config) : Prop :=
  wf img0 c ∧
  ∃ h0 h1 h2 h3, c_harts c = [h0; h1; h2; h3] ∧ iriw_content (c_log c) ∧
    (h_prog h0 = [IStore ax b1] ∨ h_prog h0 = []) ∧
    (h_prog h1 = [IStore ay b1] ∨ h_prog h1 = []) ∧
    iriw_C (h_prog h2) (h_regs h2) (h_tv h2) (h_rv h2) (c_log c) (c_dl c) ∧
    iriw_D (h_prog h3) (h_regs h3) (h_tv h3) (h_rv h3) (c_log c) (c_dl c).

Lemma iriwf_step c c' : iriwf_inv c → lstep c c' → iriwf_inv c'.
Proof.
  intros Hinv Hstep.
  assert (Hwf' : wf img0 c') by (eapply wf_step; [apply Hinv|exact Hstep]).
  destruct Hinv as ([Himg Hok] & [q0 g0 u0 w0 k0] & [q1 g1 u1 w1 k1] & [q2 g2 u2 w2 k2]
          & [q3 g3 u3 w3 k3] & Hh & Hcont & H0 & H1 & HC & HD).
  simpl in H0, H1, HC, HD.
  destruct Hstep as [Hstep|Hstep]; last first.
  { destruct Hstep as (i & Hdr & Himg' & Hlog & Hdl & Hharts).
    split; [done|]. eexists _, _, _, _. rewrite Hharts Hh Hlog Hdl /drain_log.
    split; [reflexivity|].
    split_and!; [done|done|done|by apply iriw_C_app_dl|by apply iriw_D_app_dl]. }
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|[|[|[|i]]]]; simpl in Hlk; simplify_eq/=.
  - (* writer x *)
    destruct H0 as [->| ->]; simpl in Hst; [|done].
    destruct Hst as (Hlog & Hdl & Hharts).
    split; [done|]. eexists _, _, _, _.
    split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
    rewrite Hlog Hdl /store_log. split_and!.
    + apply iriw_content_app; [exact Hcont|by left].
    + by right.
    + exact H1.
    + by apply iriw_C_app_log.
    + by apply iriw_D_app_log.
  - (* writer y *)
    destruct H1 as [->| ->]; simpl in Hst; [|done].
    destruct Hst as (Hlog & Hdl & Hharts).
    split; [done|]. eexists _, _, _, _.
    split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
    rewrite Hlog Hdl /store_log. split_and!.
    + apply iriw_content_app; [exact Hcont|by right].
    + exact H0.
    + by right.
    + by apply iriw_C_app_log.
    + by apply iriw_D_app_log.
  - (* reader C *)
    destruct HC as [->|[[-> Hc]|[[-> Hc]|[-> _]]]]; simpl in Hst; [| | |done].
    + (* load x: the watermark passes the x-message's drain position *)
      destruct Hst as (tv' & v & Hok' & Hlog & Hdl & Hharts).
      destruct Hok' as (Hle & Hcoh & Hlen & Hread). rewrite Himg in Hread.
      split; [done|]. eexists _, _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl. split_and!; [exact Hcont|exact H0|exact H1| |exact HD].
      right; left. split; [reflexivity|]. rewrite lookup_insert.
      intros Hv. assert (v = b1) as -> by congruence.
      destruct (tso_read_src _ _ _ _ _ _ _ (iriw_pend _ _ 2%nat ax Hcont ltac:(lia)) Hread)
        as [Hi|(q & j & m & Hq & Hj & Hmb & Hvis)].
      { by destruct (img0_x_nb1 Hi). }
      destruct (Hcont m (elem_of_list_lookup_2 _ _ _ Hj)) as [-> | ->];
        last first.
      { rewrite mb_IY_x in Hmb. done. }
      exists q. split; [by exists j|].
      pose proof (visibleb_foreign 2%nat tv' (c_log c) (c_dl c) q j IX Hq Hj
                    ltac:(done) Hvis). lia.
    + (* fence r,r: the floor passes the watermark *)
      destruct Hst as (_ & Hlog & Hdl & Hharts).
      split; [done|]. eexists _, _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl. split_and!; [exact Hcont|exact H0|exact H1| |exact HD].
      right; right; left. split; [reflexivity|]. intros Hv.
      destruct (Hc Hv) as (q & Hq & Hqrv). exists q. split; [exact Hq|].
      pose proof (fence_post_acq 2%nat (c_log c) (c_dl c) true false true false u2 w2
                    eq_refl). lia.
    + (* load y: at or above the floor *)
      destruct Hst as (tv' & v & Hok' & Hlog & Hdl & Hharts).
      destruct Hok' as (Hle & Hcoh & Hlen & Hread). rewrite Himg in Hread.
      split; [done|]. eexists _, _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl. split_and!; [exact Hcont|exact H0|exact H1| |exact HD].
      right; right; right. split; [reflexivity|].
      rewrite lookup_insert_ne // lookup_insert.
      intros Hv1 Hv2. assert (v = b0) as -> by congruence.
      destruct (Hc Hv1) as (qx & Hqx & Hqtv). exists qx. split; [exact Hqx|].
      intros qy Hqy. destruct (decide (qx < qy)%nat) as [?|Hn]; [done|].
      exfalso. destruct Hqy as (jy & Hqy & Hjy).
      assert (Hvis : visibleb 2%nat tv' (c_log c) (c_dl c) (S qy) = true)
        by (apply visibleb_below; lia).
      destruct (tso_read_from_below img0 (c_log c) (c_dl c) 2%nat tv' ay qy jy IY b1 b0
                  (iriw_pend _ _ 2%nat ay Hcont ltac:(lia)) Hqy Hjy mb_IY_y Hvis Hread)
        as (q' & j' & m' & _ & _ & Hj' & Hmb & _).
      destruct (Hcont m' (elem_of_list_lookup_2 _ _ _ Hj')) as [-> | ->].
      { rewrite mb_IX_y in Hmb. done. }
      rewrite mb_IY_y in Hmb. apply b0_ne_b1. congruence.
  - (* reader D *)
    destruct HD as [->|[[-> Hc]|[[-> Hc]|[-> _]]]]; simpl in Hst; [| | |done].
    + destruct Hst as (tv' & v & Hok' & Hlog & Hdl & Hharts).
      destruct Hok' as (Hle & Hcoh & Hlen & Hread). rewrite Himg in Hread.
      split; [done|]. eexists _, _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl. split_and!; [exact Hcont|exact H0|exact H1|exact HC|].
      right; left. split; [reflexivity|]. rewrite lookup_insert.
      intros Hv. assert (v = b1) as -> by congruence.
      destruct (tso_read_src _ _ _ _ _ _ _ (iriw_pend _ _ 3%nat ay Hcont ltac:(lia)) Hread)
        as [Hi|(q & j & m & Hq & Hj & Hmb & Hvis)].
      { by destruct (img0_y_nb1 Hi). }
      destruct (Hcont m (elem_of_list_lookup_2 _ _ _ Hj)) as [-> | ->].
      { rewrite mb_IX_y in Hmb. done. }
      exists q. split; [by exists j|].
      pose proof (visibleb_foreign 3%nat tv' (c_log c) (c_dl c) q j IY Hq Hj
                    ltac:(done) Hvis). lia.
    + destruct Hst as (_ & Hlog & Hdl & Hharts).
      split; [done|]. eexists _, _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl. split_and!; [exact Hcont|exact H0|exact H1|exact HC|].
      right; right; left. split; [reflexivity|]. intros Hv.
      destruct (Hc Hv) as (q & Hq & Hqrv). exists q. split; [exact Hq|].
      pose proof (fence_post_acq 3%nat (c_log c) (c_dl c) true false true false u3 w3
                    eq_refl). lia.
    + destruct Hst as (tv' & v & Hok' & Hlog & Hdl & Hharts).
      destruct Hok' as (Hle & Hcoh & Hlen & Hread). rewrite Himg in Hread.
      split; [done|]. eexists _, _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl. split_and!; [exact Hcont|exact H0|exact H1|exact HC|].
      right; right; right. split; [reflexivity|].
      rewrite lookup_insert_ne // lookup_insert.
      intros Hv1 Hv2. assert (v = b0) as -> by congruence.
      destruct (Hc Hv1) as (qy & Hqy & Hqtv). exists qy. split; [exact Hqy|].
      intros qx Hqx. destruct (decide (qy < qx)%nat) as [?|Hn]; [done|].
      exfalso. destruct Hqx as (jx & Hqx & Hjx).
      assert (Hvis : visibleb 3%nat tv' (c_log c) (c_dl c) (S qx) = true)
        by (apply visibleb_below; lia).
      destruct (tso_read_from_below img0 (c_log c) (c_dl c) 3%nat tv' ax qx jx IX b1 b0
                  (iriw_pend _ _ 3%nat ax Hcont ltac:(lia)) Hqx Hjx mb_IX_x Hvis Hread)
        as (q' & j' & m' & _ & _ & Hj' & Hmb & _).
      destruct (Hcont m' (elem_of_list_lookup_2 _ _ _ Hj')) as [-> | ->].
      { rewrite mb_IX_x in Hmb. apply b0_ne_b1. congruence. }
      rewrite mb_IY_x in Hmb. done.
Qed.

Lemma iriwf_inv0 : iriwf_inv iriwf_c0.
Proof.
  split; [split; [done|split; [apply NoDup_nil_2|by intros ? ?%elem_of_nil]]|].
  eexists _, _, _, _. split; [reflexivity|]. simpl.
  split_and!; [by intros ? ?%elem_of_nil|by left|by left|by left|by left].
Qed.

(** IRIW with [fence r,r] in both readers: (1,0,1,0) is UNREACHABLE. *)
Theorem iriw_fence_forbidden c h0 h1 regs2 tv2 rv2 coh2 regs3 tv3 rv3 coh3 :
  reach iriwf_c0 c →
  c_harts c = [h0; h1; Hart [] regs2 tv2 rv2 coh2; Hart [] regs3 tv3 rv3 coh3] →
  regs2 !! rg1 = Some b1 → regs2 !! rg2 = Some b0 →
  regs3 !! rg3 = Some b1 → regs3 !! rg4 ≠ Some b0.
Proof.
  intros Hre Hh Ha1 Ha2 Hb1 Hb2.
  assert (Hinv : iriwf_inv c).
  { eapply inv_reach; [apply iriwf_inv0| |exact Hre].
    intros. by eapply iriwf_step. }
  destruct Hinv as (_ & k0 & k1 & k2 & k3 & Hh' & _ & _ & _ & HC & HD).
  rewrite Hh in Hh'. simplify_eq/=.
  destruct HC as [Hc|[[Hc _]|[[Hc _]|[_ HimpC]]]]; try discriminate.
  destruct HD as [Hc|[[Hc _]|[[Hc _]|[_ HimpD]]]]; try discriminate.
  destruct (HimpC Ha1 Ha2) as (qx & Hqx & HltC).
  destruct (HimpD Hb1 Hb2) as (qy & Hqy & HltD).
  specialize (HltC _ Hqy). specialize (HltD _ Hqx). lia.
Qed.

(** Non-vacuity: all four harts complete, and THREE of the four hypothesised
    reads happen — only [rg4 = 0] is missing, which is exactly what the
    theorem forbids. *)
Lemma iriwf_completed_reachable :
  ∃ c h0 h1 regs2 tv2 rv2 coh2 regs3 tv3 rv3 coh3,
    reach iriwf_c0 c ∧
    c_harts c = [h0; h1; Hart [] regs2 tv2 rv2 coh2; Hart [] regs3 tv3 rv3 coh3] ∧
    regs2 !! rg1 = Some b1 ∧ regs2 !! rg2 = Some b0 ∧
    regs3 !! rg3 = Some b1 ∧ regs3 !! rg4 = Some b1.
Proof.
  rewrite /iriwf_c0. eexists _, _, _, _, _, _, _, _, _, _, _. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 0%nat); solve_drain|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 2%nat rg1 ax _ _ _ _ _ 1%nat b1);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l; [eapply (step_fence _ 2%nat); [reflexivity|solve_fence]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 2%nat rg2 ay _ _ _ _ _ 1%nat b0);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l; [eapply (step_store _ 1%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 1%nat); solve_drain|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 3%nat rg3 ay _ _ _ _ _ 2%nat b1);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l; [eapply (step_fence _ 3%nat); [reflexivity|solve_fence]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 3%nat rg4 ax _ _ _ _ _ 2%nat b1);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split_and!.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
Qed.

(* ================================================================== *)
(** ** n6 — the store buffer drains LATE.  ALLOWED (herd: allowed under
       Ztso and RVWMO, forbidden under SC).

    Hart 0 reads its own [x = 1] by forwarding while it is still pending,
    misses hart 1's [y = 2] entirely, and its x-store still reaches memory
    LAST — so memory ends at [x = 1] even though hart 1's [x = 2] is
    program-order later than the [y = 2] hart 0 could not see.  No SC
    interleaving produces this. *)

Definition n6_c0 : config :=
  Cfg img0 [] [] [Hart [IStore ax b1; ILoad rg1 ax; ILoad rg2 ay] ∅ 0%nat 0%nat coh0;
                  Hart [IStore ay b2; IStore ax b2] ∅ 0%nat 0%nat coh0].

Lemma n6_allowed :
  ∃ c, reach n6_c0 c ∧
       (∃ regs tv rv coh, c_harts c !! 0%nat = Some (Hart [] regs tv rv coh) ∧
                          regs !! rg1 = Some b1 ∧ regs !! rg2 = Some b0) ∧
       (∃ regs tv rv coh, c_harts c !! 1%nat = Some (Hart [] regs tv rv coh)) ∧
       dflat img0 (c_log c) (c_dl c) ax = Some b1.
Proof.
  rewrite /n6_c0. eexists. split.
  { eapply rtc_l; [eapply (step_store _ 1%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 1%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 0%nat rg1 ax _ _ _ _ _ 0%nat b1);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 0%nat rg2 ay _ _ _ _ _ 0%nat b0);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 0%nat); solve_drain|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 1%nat); solve_drain|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 2%nat); solve_drain|]. simpl.
    apply rtc_refl. }
  split_and!.
  - do 4 eexists. split; [reflexivity|].
    rewrite lookup_insert. split; [|reflexivity].
    rewrite lookup_insert_ne // lookup_insert //.
  - do 4 eexists. reflexivity.
  - vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(** ** 2+2W — two harts each write both locations in opposite orders.
       The outcome "x ends at hart 0's value AND y ends at hart 1's" is
       ALLOWED (herd: allowed under RVWMO, forbidden under TSO): each hart's
       stores reach memory in the opposite order to their issue.  THE
       VERDICT A DRAINED SET OVER THE ISSUE LOG COULD NOT PRODUCE
       (relaxed-ww.md §1.3). *)

Definition w22_c0 : config :=
  Cfg img0 [] [] [Hart [IStore ax b1; IStore ay b2] ∅ 0%nat 0%nat coh0;
                  Hart [IStore ay b1; IStore ax b2] ∅ 0%nat 0%nat coh0].

Lemma w22_allowed :
  ∃ c, reach w22_c0 c ∧
       (∃ regs tv rv coh, c_harts c !! 0%nat = Some (Hart [] regs tv rv coh)) ∧
       (∃ regs tv rv coh, c_harts c !! 1%nat = Some (Hart [] regs tv rv coh)) ∧
       length (c_dl c) = length (c_log c) ∧
       dflat img0 (c_log c) (c_dl c) ax = Some b1 ∧
       dflat img0 (c_log c) (c_dl c) ay = Some b1.
Proof.
  rewrite /w22_c0. eexists. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 1%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 1%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 3%nat); solve_drain|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 0%nat); solve_drain|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 1%nat); solve_drain|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 2%nat); solve_drain|]. simpl.
    apply rtc_refl. }
  split_and!.
  - do 4 eexists. reflexivity.
  - do 4 eexists. reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(** ** S — store, store / load-of-second, store-to-first.  Hart 1 sees
       hart 0's [y = 1] and then writes [x = 2]; memory ending at hart 0's
       [x = 1] is ALLOWED (herd: allowed under RVWMO): hart 0's x-store
       reaches memory after hart 1's.  Also flipped. *)

Definition s_c0 : config :=
  Cfg img0 [] [] [Hart [IStore ax b1; IStore ay b1] ∅ 0%nat 0%nat coh0;
                  Hart [ILoad rg1 ay; IStore ax b2] ∅ 0%nat 0%nat coh0].

Lemma s_allowed :
  ∃ c, reach s_c0 c ∧
       (∃ regs tv rv coh, c_harts c !! 0%nat = Some (Hart [] regs tv rv coh)) ∧
       (∃ regs tv rv coh, c_harts c !! 1%nat = Some (Hart [] regs tv rv coh) ∧
                          regs !! rg1 = Some b1) ∧
       length (c_dl c) = length (c_log c) ∧
       dflat img0 (c_log c) (c_dl c) ax = Some b1.
Proof.
  rewrite /s_c0. eexists. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 1%nat); solve_drain|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg1 ay _ _ _ _ _ 1%nat b1);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l; [eapply (step_store _ 1%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 2%nat); solve_drain|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 0%nat); solve_drain|]. simpl.
    apply rtc_refl. }
  split_and!.
  - do 4 eexists. reflexivity.
  - do 4 eexists. split; [reflexivity|]. rewrite lookup_insert //.
  - reflexivity.
  - vm_compute. reflexivity.
Qed.


(* ================================================================== *)
(** ** THE xv6 LOCK HANDOFF — [store; fence rw,w; store] against
       [amoswap.aq; load].  FORBIDDEN: if the acquirer's AMO read the
       release store, its later load sees the data.

    The release side: [fence rw,w] WAITS for the data store to drain, so the
    release store (a PLAIN store, as in xv6's [release]) drains after it.
    The acquire side: [amoswap.aq] reads MEMORY — it can only see the
    release store once drained — and lands its floor past the top, hence
    past the data's drain position.  No [.rl] anywhere: the fence is the
    release. *)

Local Notation LKX := (WMsg ax [b1] 0%nat).   (* the data *)
Local Notation LKY := (WMsg ay [b1] 0%nat).   (* the release store *)
Local Notation LKA := (WMsg ay [b2] 1%nat).   (* the acquirer's AMO write *)

Lemma LKX_ne_LKY : LKX ≠ LKY.
Proof. intros H. by simplify_eq/=. Qed.
Lemma LKY_ne_LKA : LKY ≠ LKA.
Proof. intros H. by simplify_eq/=. Qed.
Lemma LKX_ne_LKA : LKX ≠ LKA.
Proof. intros H. by simplify_eq/=. Qed.
Lemma mb_LKX_x : msg_byte LKX ax = Some b1.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_LKX_y : msg_byte LKX ay = None.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_LKY_x : msg_byte LKY ax = None.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_LKY_y : msg_byte LKY ay = Some b1.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_LKA_x : msg_byte LKA ax = None.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_LKA_y : msg_byte LKA ay = Some b2.
Proof. rewrite msg_byte_single //. Qed.

Definition lock_c0 : config :=
  Cfg img0 [] [] [Hart [IStore ax b1; FENCE_RWW; IStore ay b1] ∅ 0%nat 0%nat coh0;
                  Hart [IAmoSwap true false rg2 ay b2; ILoad rg3 ax] ∅ 0%nat 0%nat coh0].

Definition lock_content (log : list wmsg) : Prop :=
  ∀ m, m ∈ log → m = LKX ∨ m = LKY ∨ m = LKA.

Lemma lock_content_app log m :
  lock_content log → (m = LKX ∨ m = LKY ∨ m = LKA) → lock_content (log ++ [m]).
Proof.
  intros Hc Hm m' Hin. apply elem_of_app in Hin as [Hin|Hin]; [by apply Hc|].
  apply elem_of_list_singleton in Hin as ->. done.
Qed.

Lemma lock_pend_1 log dl : lock_content log → pend_read log dl 1%nat ax = None.
Proof.
  intros Hc. apply pend_read_none_of. intros i m Hi Htid _.
  destruct (Hc m (elem_of_list_lookup_2 _ _ _ Hi)) as [->|[->| ->]];
    [done|done|apply mb_LKA_x].
Qed.

(** The releaser's phases: data issued; data drained (the fence has run);
    release issued — and then every drain of the release sits above the
    data's drain position. *)
Definition lock_R (p : list instr) (log : list wmsg) (dl : list nat) : Prop :=
  (p = [IStore ax b1; FENCE_RWW; IStore ay b1] ∧ LKY ∉ log) ∨
  (p = [FENCE_RWW; IStore ay b1] ∧ (∃ j, log !! j = Some LKX) ∧ LKY ∉ log) ∨
  (p = [IStore ay b1] ∧ (∃ q, at_pos log dl q LKX) ∧ LKY ∉ log) ∨
  (p = [] ∧ ∃ q, at_pos log dl q LKX ∧
     ∀ qy, at_pos log dl qy LKY → (q < qy)%nat).

(** The acquirer's phases: after the AMO, "I read the release" puts the
    data's drain position under my floor. *)
Definition lock_A (p : list instr) (regs : gmap nat (bv 8)) (tv : nat)
    (log : list wmsg) (dl : list nat) : Prop :=
  (p = [IAmoSwap true false rg2 ay b2; ILoad rg3 ax]) ∨
  (p = [ILoad rg3 ax] ∧
     (regs !! rg2 = Some b1 → ∃ q, at_pos log dl q LKX ∧ (S q ≤ tv)%nat)) ∨
  (p = [] ∧ (regs !! rg2 = Some b1 → regs !! rg3 = Some b1)).

Definition lock_inv (c : config) : Prop :=
  wf img0 c ∧
  ∃ h0 h1, c_harts c = [h0; h1] ∧ lock_content (c_log c) ∧
    lock_R (h_prog h0) (c_log c) (c_dl c) ∧
    lock_A (h_prog h1) (h_regs h1) (h_tv h1) (c_log c) (c_dl c).

Lemma lock_R_app_log p log dl m :
  dl_ok log dl → m ≠ LKY → lock_R p log dl → lock_R p (log ++ [m]) dl.
Proof.
  intros Hok Hne [[-> Hn]|[[-> [[j Hj] Hn]]|[[-> [[q Hq] Hn]]|[-> [q [Hq Hc]]]]]].
  - left. split; [done|]. apply not_elem_of_app. split; [done|].
    intros Hin%elem_of_list_singleton. by apply Hne.
  - right; left. split; [done|]. split.
    + exists j. by apply lookup_app_l_Some.
    + apply not_elem_of_app. split; [done|].
      intros Hin%elem_of_list_singleton. by apply Hne.
  - right; right; left. split; [done|]. split.
    + exists q. by apply at_pos_app_log.
    + apply not_elem_of_app. split; [done|].
      intros Hin%elem_of_list_singleton. by apply Hne.
  - right; right; right. split; [done|]. exists q. split; [by apply at_pos_app_log|].
    intros qy Hqy. apply Hc. by eapply at_pos_app_log_inv.
Qed.

Lemma lock_R_app_dl p log dl i :
  lock_R p log dl → lock_R p log (dl ++ [i]).
Proof.
  intros [[-> Hn]|[[-> [[j Hj] Hn]]|[[-> [[q Hq] Hn]]|[-> [q [Hq Hc]]]]]].
  - by left.
  - right; left. split_and!; [done|by exists j|done].
  - right; right; left. split_and!; [done|exists q; by apply at_pos_app_dl|done].
  - right; right; right. split; [done|]. exists q. split; [by apply at_pos_app_dl|].
    intros qy Hqy. apply at_pos_app_dl_inv in Hqy as [Hqy|[-> _]].
    + by apply Hc.
    + by apply at_pos_lt in Hq.
Qed.

Lemma lock_A_app_log p regs tv log dl m :
  dl_ok log dl → lock_A p regs tv log dl → lock_A p regs tv (log ++ [m]) dl.
Proof.
  intros Hok [->|[[-> H]|[-> H]]].
  - by left.
  - right; left. split; [done|]. intros Hr. destruct (H Hr) as (q & Hq & ?).
    exists q. split; [by apply at_pos_app_log|done].
  - right; right. by split.
Qed.

Lemma lock_A_app_dl p regs tv log dl i :
  lock_A p regs tv log dl → lock_A p regs tv log (dl ++ [i]).
Proof.
  intros [->|[[-> H]|[-> H]]].
  - by left.
  - right; left. split; [done|]. intros Hr. destruct (H Hr) as (q & Hq & ?).
    exists q. split; [by apply at_pos_app_dl|done].
  - right; right. by split.
Qed.

Lemma lock_step c c' : lock_inv c → lstep c c' → lock_inv c'.
Proof.
  intros Hinv Hstep.
  assert (Hwf' : wf img0 c') by (eapply wf_step; [apply Hinv|exact Hstep]).
  destruct Hinv as ([Himg Hok] & [p0 regs0 tv0 rv0 coh0'] & [p1 regs1 tv1 rv1 coh1]
          & Hh & Hcont & HR & HA).
  simpl in HR, HA.
  destruct Hstep as [Hstep|Hstep]; last first.
  { destruct Hstep as (i & Hdr & Himg' & Hlog & Hdl & Hharts).
    split; [done|]. eexists _, _. rewrite Hharts Hh Hlog Hdl /drain_log.
    split; [reflexivity|].
    split_and!; [done|by apply lock_R_app_dl|by apply lock_A_app_dl]. }
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|[|i]]; simpl in Hlk; simplify_eq/=.
  - (* ---- the releaser ---- *)
    destruct HR as [[-> Hn]|[[-> [[j Hj] Hn]]|[[-> [[q Hq] Hn]]|[-> _]]]];
      simpl in Hst; [| | |done].
    + (* store x: the data *)
      destruct Hst as (Hlog & Hdl & Hharts).
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl /store_log. split_and!.
      * apply lock_content_app; [exact Hcont|by left].
      * right; left. split_and!; [reflexivity| |].
        -- exists (length (c_log c)). apply lookup_app_new.
        -- apply not_elem_of_app. split; [done|].
           intros Hin%elem_of_list_singleton. by apply LKX_ne_LKY.
      * by apply lock_A_app_log.
    + (* fence rw,w: waits for the data to drain *)
      destruct Hst as (Hfok & Hlog & Hdl & Hharts).
      pose proof (fence_ok_rel _ _ _ _ Hfok eq_refl) as Hod.
      destruct (own_drained_at_pos _ _ _ _ _ Hod Hj eq_refl) as [q Hq].
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl. split_and!.
      * exact Hcont.
      * right; right; left. split_and!; [reflexivity|by exists q|done].
      * exact HA.
    + (* store y: the release *)
      destruct Hst as (Hlog & Hdl & Hharts).
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl /store_log. split_and!.
      * apply lock_content_app; [exact Hcont|by right; left].
      * right; right; right. split; [reflexivity|]. exists q.
        split; [by apply at_pos_app_log|].
        intros qy Hqy. exfalso. apply at_pos_app_log_inv in Hqy as (jy & _ & Hjy); [|done].
        apply Hn. by eapply elem_of_list_lookup_2.
      * by apply lock_A_app_log.
  - (* ---- the acquirer ---- *)
    destruct HA as [->|[[-> Hc]|[-> _]]]; simpl in Hst; [| |done].
    + (* amoswap.aq: reads memory, floor to the new top *)
      destruct Hst as (v_old & [Hamo Hmem] & Hlog & Hdl & Hharts).
      rewrite Himg in Hmem.
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl /store_log. split_and!.
      * apply lock_content_app; [exact Hcont|by right; right].
      * apply lock_R_app_dl. apply lock_R_app_log; [done| |done].
        intros Hc. by apply LKY_ne_LKA.
      * right; left. split; [reflexivity|]. rewrite lookup_insert.
        intros Hv. assert (v_old = b1) as -> by congruence.
        destruct (dflat_src _ _ _ _ _ Hmem) as [Hi|(q & j & m & Hq & Hj & Hmb)].
        { by destruct (img0_y_nb1 Hi). }
        (* the byte came from the release store *)
        destruct (Hcont m (elem_of_list_lookup_2 _ _ _ Hj)) as [->|[->| ->]].
        { rewrite mb_LKX_y in Hmb. discriminate. }
        2:{ rewrite mb_LKA_y in Hmb. destruct b1_ne_b2. congruence. }
        (* so the releaser is done, and the data sits below the release *)
        assert (Hpos : at_pos (c_log c) (c_dl c) q LKY) by (by exists j).
        destruct HR as [[_ Hn]|[[_ [_ Hn]]|[[_ [_ Hn]]|[_ [qx [Hqx Hc]]]]]].
        1-3: exfalso; apply Hn; by eapply elem_of_list_lookup_2.
        specialize (Hc _ Hpos).
        exists qx. split.
        -- apply at_pos_app_dl. by apply at_pos_app_log.
        -- rewrite /amo_post. apply at_pos_lt in Hpos. lia.
    + (* load rg3 <- x: at or above the floor, hence past the data *)
      destruct Hst as (tv' & v & Hok' & Hlog & Hdl & Hharts).
      destruct Hok' as (Hle & Hcoh & Hlen & Hread). rewrite Himg in Hread.
      split; [done|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog Hdl. split_and!.
      * exact Hcont.
      * exact HR.
      * right; right. split; [reflexivity|].
        rewrite lookup_insert_ne // lookup_insert.
        intros Hv. destruct (Hc Hv) as (q & (j & Hq & Hj) & Htv).
        assert (Hvis : visibleb 1%nat tv' (c_log c) (c_dl c) (S q) = true)
          by (apply visibleb_below; lia).
        destruct (tso_read_from_below img0 (c_log c) (c_dl c) 1%nat tv' ax q j LKX b1 v
                    (lock_pend_1 _ _ Hcont) Hq Hj mb_LKX_x Hvis Hread)
          as (q' & j' & m' & _ & _ & Hj' & Hmb & _).
        destruct (Hcont m' (elem_of_list_lookup_2 _ _ _ Hj')) as [->|[->| ->]].
        -- rewrite mb_LKX_x in Hmb. congruence.
        -- rewrite mb_LKY_x in Hmb. discriminate.
        -- rewrite mb_LKA_x in Hmb. discriminate.
Qed.

Lemma lock_inv0 : lock_inv lock_c0.
Proof.
  split; [split; [done|split; [apply NoDup_nil_2|by intros ? ?%elem_of_nil]]|].
  eexists _, _. split; [reflexivity|]. simpl.
  split_and!; [by intros ? ?%elem_of_nil| |by left].
  left. split; [done|]. apply not_elem_of_nil.
Qed.

(** The lock handoff: if the acquirer's AMO read the release store, its
    load of the data reads the data. *)
Theorem lock_handoff_forbidden c h0 regs tv rv coh :
  reach lock_c0 c →
  c_harts c = [h0; Hart [] regs tv rv coh] →
  regs !! rg2 = Some b1 → regs !! rg3 = Some b1.
Proof.
  intros Hre Hh H1.
  assert (Hinv : lock_inv c).
  { eapply inv_reach; [apply lock_inv0| |exact Hre]. intros. by eapply lock_step. }
  destruct Hinv as (_ & g0 & g1 & Hh' & _ & _ & HA).
  rewrite Hh in Hh'. simplify_eq/=.
  destruct HA as [Hc|[[Hc _]|[_ Himp]]]; try discriminate. by apply Himp.
Qed.

(** Non-vacuity: the acquirer does read the release, and then the data. *)
Lemma lock_completed_reachable :
  ∃ c h0 regs tv rv coh,
    reach lock_c0 c ∧ c_harts c = [h0; Hart [] regs tv rv coh] ∧
    regs !! rg2 = Some b1 ∧ regs !! rg3 = Some b1.
Proof.
  rewrite /lock_c0. eexists _, _, _, _, _, _. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 0%nat); solve_drain|]. simpl.
    eapply rtc_l; [eapply (step_fence _ 0%nat); [reflexivity|solve_fence]|]. simpl.
    eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 1%nat); solve_drain|]. simpl.
    eapply rtc_l;
      [eapply (step_amo _ 1%nat true false rg2 ay b2 _ _ _ _ _ b1);
        [reflexivity|solve_excl]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg3 ax _ _ _ _ _ 3%nat b1);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
Qed.

(* ================================================================== *)
(** ** [store; amoswap.aq] against [amoswap.aq; load] — ALLOWED (flipped).

    Under one log the AMO's write sat above the hart's earlier store, so an
    AMO that took the word after it saw the store.  With stores draining
    late that is false: [.aq] orders the AMO before LATER accesses of its
    own hart, never the hart's earlier stores before the AMO — that is the
    job of a release fence or [.rl].  The witness: hart 0's data store is
    still pending when both AMOs have run. *)

Local Notation AMX := (WMsg ax [b1] 0%nat).   (* hart 0's plain store *)
Local Notation AMA := (WMsg ay [b1] 0%nat).   (* hart 0's AMO write *)
Local Notation AMB := (WMsg ay [b2] 1%nat).   (* hart 1's AMO write *)

Definition amo_c0 : config :=
  Cfg img0 [] [] [Hart [IStore ax b1; IAmoSwap true false rg1 ay b1] ∅ 0%nat 0%nat coh0;
                  Hart [IAmoSwap true false rg2 ay b2; ILoad rg3 ax] ∅ 0%nat 0%nat coh0].

Lemma amo_aq_alone_allowed :
  ∃ c h0 regs tv rv coh,
    reach amo_c0 c ∧ c_harts c = [h0; Hart [] regs tv rv coh] ∧
    c_log c = [AMX; AMA; AMB] ∧ c_dl c = [1%nat; 2%nat] ∧
    regs !! rg2 = Some b1 ∧ regs !! rg3 = Some b0.
Proof.
  rewrite /amo_c0. eexists _, _, _, _, _, _. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l;
      [eapply (step_amo _ 0%nat true false rg1 ay b1 _ _ _ _ _ b0);
        [reflexivity|solve_excl]|]. simpl.
    eapply rtc_l;
      [eapply (step_amo _ 1%nat true false rg2 ay b2 _ _ _ _ _ b1);
        [reflexivity|solve_excl]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg3 ax _ _ _ _ _ 2%nat b0);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
Qed.

(* ================================================================== *)
(** ** A PENDING PLAIN STORE AGAINST A FOREIGN AMO, same word: the AMO reads
       the OLD value and the store lands AFTER it.

    This is xv6's lock word when [release]'s [sw zero] is still in the
    releaser's buffer while a contender's [amoswap] runs: the contender
    reads "locked", writes "locked", and the release then reaches memory
    — the word ends at 0 and the lock is acquirable.  A model that ranked
    the two by issue order would leave the word at 1 forever
    (relaxed-ww.md §1.3). *)

Definition race_c0 : config :=
  Cfg img0 [] [] [Hart [IStore ay b1] ∅ 0%nat 0%nat coh0;
                  Hart [IAmoSwap true false rg2 ay b2] ∅ 0%nat 0%nat coh0].

Lemma pending_store_lands_after_amo :
  ∃ c h0 regs tv rv coh,
    reach race_c0 c ∧ c_harts c = [h0; Hart [] regs tv rv coh] ∧
    c_dl c = [1%nat; 0%nat] ∧
    regs !! rg2 = Some b0 ∧
    dflat img0 (c_log c) (c_dl c) ay = Some b1.
Proof.
  rewrite /race_c0. eexists _, _, _, _, _, _. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l;
      [eapply (step_amo _ 1%nat true false rg2 ay b2 _ _ _ _ _ b0);
        [reflexivity|solve_excl]|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 0%nat); solve_drain|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split; [reflexivity|]. split.
  - rewrite lookup_insert //.
  - vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(** ** AMO without [.aq] — the .aq knob (relaxed-rr.md).

    The lock shape with hart 1's AMO PLAIN: hart 0 publishes its data
    properly (the store has drained before its AMO), hart 1's AMO reads it
    from memory (so the pair is atomic and hart 1 does see hart 0's AMO in
    the drain log), but the floor does not move, so the later load of [x]
    may read at view 0 — the data is missed.  This is exactly what RVWMO
    allows for an un-annotated AMO, and it is why the lock leaves use
    [amoswap.aq] while the Svadu A/D write-back's plain LR/SC needs no
    ordering.  Exhibited as a reachability witness. *)

Definition amo_plain_c0 : config :=
  Cfg img0 [] []
      [Hart [IStore ax b1; FENCE_RWW; IAmoSwap true false rg1 ay b1] ∅ 0%nat 0%nat coh0;
       Hart [IAmoSwap false false rg2 ay b2; ILoad rg3 ax] ∅ 0%nat 0%nat coh0].

Lemma amo_plain_allowed :
  ∃ c h0 regs tv rv coh,
    reach amo_plain_c0 c ∧ c_harts c = [h0; Hart [] regs tv rv coh] ∧
    c_log c = [AMX; AMA; AMB] ∧ c_dl c = [0%nat; 1%nat; 2%nat] ∧
    regs !! rg2 = Some b1 ∧ regs !! rg3 = Some b0.
Proof.
  rewrite /amo_plain_c0. eexists _, _, _, _, _, _. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_drain _ 0%nat); solve_drain|]. simpl.
    eapply rtc_l; [eapply (step_fence _ 0%nat); [reflexivity|solve_fence]|]. simpl.
    eapply rtc_l;
      [eapply (step_amo _ 0%nat true false rg1 ay b1 _ _ _ _ _ b0);
        [reflexivity|solve_excl]|]. simpl.
    eapply rtc_l;
      [eapply (step_amo _ 1%nat false false rg2 ay b2 _ _ _ _ _ b1);
        [reflexivity|solve_excl]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg3 ax _ _ _ _ _ 0%nat b0);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
Qed.
