(** * TsoLitmus.v — executable litmus programs over the minimal Ztso machine

    A tiny hart-program language (NOT Sail) on top of [TsoMem]'s Ztso view
    machine, plus the litmus suite that leg T1 of
    [claude-notes/projects/tso-port.md] makes a standing obligation: SB with
    and without fences, MP, CoRR, LB, IRIW, n6, and an AMO sanity verdict.

    THE VERDICTS.  Ztso forbids everything RVWMO forbids plus all reordering
    except W→R, so among the classical shapes SB is the ONLY allowed
    relaxation — every other forbidden outcome here is forbidden by the same
    single-log/monotone-view argument, with no fence in sight.  The one extra
    allowed outcome is n6, whose "the buffer drains late" behaviour TSO allows
    and SC forbids; it is the witness that this machine is not secretly SC.

    Under Ztso there are no acquire/release annotations to model (every load
    is an acquire, every store a release), so the language has none — the
    difference from the `weak-memory` branch's [WeakLitmus.v] mold, whose
    loads carry an [aq] flag.

    Like [TsoMem.v] this file imports only stdpp. *)
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

(** The two litmus addresses and the four litmus registers. *)
Local Notation ax := (0%Z).
Local Notation ay := (8%Z).
Local Notation rg1 := (1%nat).
Local Notation rg2 := (2%nat).
Local Notation rg3 := (3%nat).
Local Notation rg4 := (4%nat).

(** The era-initial image: both litmus bytes read as 0 at timestamp 0. *)
Definition img0m : gmap Z (bv 8) := <[ax := b0]> {[ay := b0]}.
(** [TsoMem.image] is a partial FUNCTION on [Z] (the [gmap Arch.pa _]
    Countable trap); the litmus image is still built as a two-entry map. *)
Definition img0 : image := λ a, img0m !! a.

Lemma img0_x : img0 ax = Some b0.
Proof. rewrite /img0 /img0m lookup_insert //. Qed.
Lemma img0_y : img0 ay = Some b0.
Proof. rewrite /img0 /img0m lookup_insert_ne // lookup_singleton //. Qed.
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

    No annotations: under Ztso every load is an acquire and every store a
    release, so [ILoad]/[IStore] carry nothing but their address. *)

Inductive instr :=
| ILoad (reg : nat) (a : Z)
| IStore (a : Z) (v : bv 8)
| IFence (pr pw sr sw : bool)
(** [amoswap.aq]: the read half takes the globally latest value and the write
    half appends, in one step; the view lands past the append. *)
| IAmoSwapAq (reg : nat) (a : Z) (v : bv 8).

Record hart := Hart {
  h_prog : list instr;               (* the remaining program IS the pc *)
  h_regs : gmap nat (bv 8);
  h_tv   : nat;                      (* the WHOLE per-hart memory state *)
}.

Record config := Cfg {
  c_img   : image;
  c_log   : list wmsg;
  c_harts : list hart;
}.

(** One small step: pick a hart, execute its next instruction.  The hart's
    INDEX is its agent id, so forwarding keys on it. *)
Definition lstep (c c' : config) : Prop :=
  ∃ (i : nat) (h : hart),
    c_harts c !! i = Some h ∧ c_img c' = c_img c ∧
    match h_prog h with
    | [] => False
    | ILoad r a :: rest => ∃ (tv' : nat) (v : bv 8),
        load_ok (c_img c) (c_log c) i (h_tv h) tv' a v ∧
        c_log c' = c_log c ∧
        c_harts c' =
          <[i := Hart rest (<[r := v]> (h_regs h)) tv']> (c_harts c)
    | IStore a v :: rest =>
        c_log c' = store_log (c_log c) i a [v] ∧
        c_harts c' = <[i := Hart rest (h_regs h) (h_tv h)]> (c_harts c)
    | IFence pr pw sr sw :: rest =>
        c_log c' = c_log c ∧
        c_harts c' =
          <[i := Hart rest (h_regs h)
                   (fence_post i (c_log c) pr pw sr sw (h_tv h))]> (c_harts c)
    | IAmoSwapAq r a v :: rest => ∃ (v_old : bv 8),
        excl_read_ok (c_img c) (c_log c) i (h_tv h) a v_old ∧
        c_log c' = store_log (c_log c) i a [v] ∧
        c_harts c' =
          <[i := Hart rest (<[r := v_old]> (h_regs h))
                   (S (length (c_log c)))]> (c_harts c)
    end.

(* ------------------------------------------------------------------ *)
(** ** Step constructors (used to exhibit interleavings) *)

Lemma step_load c i r a rest regs tv tv' v :
  c_harts c !! i = Some (Hart (ILoad r a :: rest) regs tv) →
  load_ok (c_img c) (c_log c) i tv tv' a v →
  lstep c (Cfg (c_img c) (c_log c)
               (<[i := Hart rest (<[r := v]> regs) tv']> (c_harts c))).
Proof.
  intros Hlk Hok. exists i, (Hart (ILoad r a :: rest) regs tv).
  split_and!; [done|done|]. simpl. exists tv', v. by split_and!.
Qed.

Lemma step_store c i a v rest regs tv :
  c_harts c !! i = Some (Hart (IStore a v :: rest) regs tv) →
  lstep c (Cfg (c_img c) (c_log c ++ [WMsg a [v] i])
               (<[i := Hart rest regs tv]> (c_harts c))).
Proof.
  intros Hlk. exists i, (Hart (IStore a v :: rest) regs tv).
  split_and!; [done|done|]. simpl. by split_and!.
Qed.

Lemma step_fence c i pr pw sr sw rest regs tv :
  c_harts c !! i = Some (Hart (IFence pr pw sr sw :: rest) regs tv) →
  lstep c (Cfg (c_img c) (c_log c)
               (<[i := Hart rest regs
                        (fence_post i (c_log c) pr pw sr sw tv)]>
                  (c_harts c))).
Proof.
  intros Hlk. exists i, (Hart (IFence pr pw sr sw :: rest) regs tv).
  split_and!; [done|done|]. simpl. by split_and!.
Qed.

Lemma step_amo c i r a v rest regs tv v_old :
  c_harts c !! i = Some (Hart (IAmoSwapAq r a v :: rest) regs tv) →
  excl_read_ok (c_img c) (c_log c) i tv a v_old →
  lstep c (Cfg (c_img c) (c_log c ++ [WMsg a [v] i])
               (<[i := Hart rest (<[r := v_old]> regs)
                        (S (length (c_log c)))]> (c_harts c))).
Proof.
  intros Hlk Hex. exists i, (Hart (IAmoSwapAq r a v :: rest) regs tv).
  split_and!; [done|done|]. simpl. exists v_old. by split_and!.
Qed.

(** Every side condition in a witness run is ground, so it computes.  (The
    durable-notes trap: never [vm_compute] a goal carrying an evar — every
    argument of a [step_*] below is instantiated before these fire.) *)
Ltac solve_load :=
  rewrite /load_ok; split_and!;
  [vm_compute; lia | vm_compute; lia | vm_compute; reflexivity].
Ltac solve_excl := rewrite /excl_read_ok; vm_compute; reflexivity.

(** Reachability. *)
Notation reach := (rtc lstep).

Lemma inv_reach (I : config → Prop) c0 c :
  I c0 → (∀ a b, I a → lstep a b → I b) → reach c0 c → I c.
Proof. intros H0 Hpres H. induction H as [|???? IH]; [done|]. eauto. Qed.

(* ------------------------------------------------------------------ *)
(** ** The two read analyses every forbidden proof consumes

    [tso_read_src]: a read's value came from the image or from a visible
    logged message.  [tso_read_from_below]: a read cannot come from BELOW a
    visible write to the same byte — this is the latest-visible rule, i.e.
    the whole reason Ztso forbids R→R reordering. *)

Lemma tso_read_src img log h tv a v :
  tso_read img log h tv a = Some v →
  img a = Some v ∨
  ∃ k m, log !! k = Some m ∧ msg_byte m a = Some v ∧
         visibleb h tv log (S k) = true.
Proof.
  rewrite /tso_read. intros Hr.
  destruct (read_down_le img log h tv a (length log) v Hr)
    as (t' & _ & Hvis & Hb).
  destruct t' as [|k].
  - left. exact Hb.
  - right. rewrite /log_byte in Hb.
    destruct (log !! k) as [m|] eqn:Hm; [|discriminate].
    exists k, m. by split_and!.
Qed.

Lemma tso_read_from_below img log h tv a k m v0 v :
  log !! k = Some m → msg_byte m a = Some v0 →
  visibleb h tv log (S k) = true →
  tso_read img log h tv a = Some v →
  ∃ k' m', (k ≤ k')%nat ∧ log !! k' = Some m' ∧ msg_byte m' a = Some v ∧
           visibleb h tv log (S k') = true.
Proof.
  intros Hlk Hb Hvis Hread.
  assert (Hlt : (k < length log)%nat) by (eapply lookup_lt_Some; exact Hlk).
  assert (Hb' : log_byte img log (S k) a = Some v0)
    by (rewrite /log_byte Hlk //).
  destruct (read_down_latest img log h tv a (length log) (S k) v0
              ltac:(lia) Hvis Hb') as (t'' & v'' & Hge & Hrd & Hvis'' & Hb'').
  rewrite /tso_read in Hread. rewrite Hread in Hrd.
  assert (v'' = v) as -> by congruence.
  destruct t'' as [|k']; [lia|].
  rewrite /log_byte in Hb''.
  destruct (log !! k') as [m'|] eqn:Hm'; [|discriminate].
  exists k', m'. split_and!; [lia|done|done|done].
Qed.

(** A foreign message is visible only by the view: agent [h] never owns a
    message another agent authored. *)
Lemma visibleb_foreign h tv log k m :
  log !! k = Some m → wm_tid m ≠ h →
  visibleb h tv log (S k) = true → (S k ≤ tv)%nat.
Proof.
  intros Hlk Hne Hvis.
  destruct (visibleb_true _ _ _ _ Hvis) as [?|(i & m' & Heq & Hlk' & Htid)];
    [done|].
  assert (i = k) as -> by lia. rewrite Hlk' in Hlk. by simplify_eq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** [own_pub] bounds a hart's own messages from above

    The one fact the W→R fence needs: after [fence rw,rw] the view is past
    every message this hart has already published. *)

Lemma foldr_max_ge (l : list nat) (i x : nat) :
  l !! i = Some x → (x ≤ foldr Nat.max 0 l)%nat.
Proof.
  revert i. induction l as [|y l IH]; intros [|i] Hlk; simpl in Hlk;
    try discriminate.
  - simplify_eq. simpl. lia.
  - specialize (IH _ Hlk). simpl. lia.
Qed.

Lemma own_pub_ge h log j m :
  log !! j = Some m → wm_tid m = h → (S j ≤ own_pub h log)%nat.
Proof.
  intros Hlk Htid. rewrite /own_pub. apply (foldr_max_ge _ j).
  rewrite list_lookup_imap Hlk /=.
  case_bool_decide as Hb; [done|contradiction].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Log bookkeeping *)

Lemma lookup_app_last (l : list wmsg) (m : wmsg) (j : nat) (m' : wmsg) :
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
Lemma lookup_app_old (l : list wmsg) (m : wmsg) (j : nat) (m' : wmsg) :
  (l ++ [m]) !! j = Some m' → m' ≠ m → l !! j = Some m'.
Proof.
  intros Hlk Hne. apply lookup_app_last in Hlk as [[? ?]|[? ?]]; [done|].
  by destruct Hne.
Qed.

Lemma lookup_app_new (l : list wmsg) (m : wmsg) :
  (l ++ [m]) !! length l = Some m.
Proof. by apply list_lookup_middle. Qed.

(* ================================================================== *)
(** ** SB — store buffering.  Both loads reading 0 is ALLOWED (herd: allowed
       under Ztso; this is the W→R relaxation, and the ONLY one). *)

Definition sb_c0 : config :=
  Cfg img0 [] [Hart [IStore ax b1; ILoad rg1 ay] ∅ 0%nat;
               Hart [IStore ay b1; ILoad rg2 ax] ∅ 0%nat].

Lemma sb_allowed :
  ∃ c, reach sb_c0 c ∧
       (∃ regs tv, c_harts c !! 0%nat = Some (Hart [] regs tv) ∧
                   regs !! rg1 = Some b0) ∧
       (∃ regs tv, c_harts c !! 1%nat = Some (Hart [] regs tv) ∧
                   regs !! rg2 = Some b0).
Proof.
  rewrite /sb_c0. eexists. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 1%nat); reflexivity|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 0%nat rg1 ay _ _ _ 0%nat b0);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg2 ax _ _ _ 0%nat b0);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split.
  - do 2 eexists. split; [reflexivity|]. rewrite lookup_insert //.
  - do 2 eexists. split; [reflexivity|]. rewrite lookup_insert //.
Qed.

(* ================================================================== *)
(** ** SB with a [fence rw,rw] in both harts — (0,0) is FORBIDDEN
       (herd: forbidden).

    The mechanism: a [pw ∧ sr] fence pushes the view past the hart's own
    message, and the log order is the drain order, so whichever hart's store
    landed LATER in the log is forced to see the other's. *)

Local Notation FENCE := (IFence true true true true).
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
  Cfg img0 [] [Hart [IStore ax b1; FENCE; ILoad rg1 ay] ∅ 0%nat;
               Hart [IStore ay b1; FENCE; ILoad rg2 ax] ∅ 0%nat].

Definition sbf_content (log : list wmsg) : Prop :=
  ∀ m, m ∈ log → m = SBX ∨ m = SBY.

Lemma sbf_content_app log m :
  sbf_content log → (m = SBX ∨ m = SBY) → sbf_content (log ++ [m]).
Proof.
  intros Hc Hm m' Hin. apply elem_of_app in Hin as [Hin|Hin]; [by apply Hc|].
  apply elem_of_list_singleton in Hin as ->. done.
Qed.

(** Hart 0's phases.  The last one carries the ONE consequence of a load
    that did not see [y = 1]: the y-message is not below the x-message. *)
Definition sbf_A (p : list instr) (regs : gmap nat (bv 8)) (tv : nat)
    (log : list wmsg) : Prop :=
  (p = [IStore ax b1; FENCE; ILoad rg1 ay]) ∨
  (p = [FENCE; ILoad rg1 ay] ∧ ∃ j, log !! j = Some SBX) ∨
  (p = [ILoad rg1 ay] ∧ (∃ j, log !! j = Some SBX) ∧
     (∀ j, log !! j = Some SBX → (S j ≤ tv)%nat)) ∨
  (p = [] ∧ (∃ j, log !! j = Some SBX) ∧
     (regs !! rg1 ≠ Some b1 →
        ∀ jx jy, log !! jx = Some SBX → log !! jy = Some SBY → (jx < jy)%nat)).

Definition sbf_B (p : list instr) (regs : gmap nat (bv 8)) (tv : nat)
    (log : list wmsg) : Prop :=
  (p = [IStore ay b1; FENCE; ILoad rg2 ax]) ∨
  (p = [FENCE; ILoad rg2 ax] ∧ ∃ j, log !! j = Some SBY) ∨
  (p = [ILoad rg2 ax] ∧ (∃ j, log !! j = Some SBY) ∧
     (∀ j, log !! j = Some SBY → (S j ≤ tv)%nat)) ∨
  (p = [] ∧ (∃ j, log !! j = Some SBY) ∧
     (regs !! rg2 ≠ Some b1 →
        ∀ jx jy, log !! jx = Some SBX → log !! jy = Some SBY → (jy < jx)%nat)).

Definition sbf_inv (c : config) : Prop :=
  c_img c = img0 ∧
  ∃ h0 h1, c_harts c = [h0; h1] ∧ sbf_content (c_log c) ∧
    sbf_A (h_prog h0) (h_regs h0) (h_tv h0) (c_log c) ∧
    sbf_B (h_prog h1) (h_regs h1) (h_tv h1) (c_log c).

Lemma sbf_A_app p regs tv log :
  sbf_A p regs tv log → sbf_A p regs tv (log ++ [SBY]).
Proof.
  intros [->|[[-> [j Hj]]|[[-> [[j Hj] Htv]]|[-> [[j Hj] Hc]]]]].
  - by left.
  - right; left. split; [done|]. exists j. by apply lookup_app_l_Some.
  - right; right; left. split; [done|]. split.
    + exists j. by apply lookup_app_l_Some.
    + intros j' Hj'. apply Htv. by eapply lookup_app_old; [exact Hj'|apply SBX_ne_SBY].
  - right; right; right. split; [done|]. split.
    + exists j. by apply lookup_app_l_Some.
    + intros Hr jx jy Hx Hy.
      assert (Hx' : log !! jx = Some SBX)
        by (eapply lookup_app_old; [exact Hx|apply SBX_ne_SBY]).
      assert (Hlt : (jx < length log)%nat) by (eapply lookup_lt_Some; exact Hx').
      apply lookup_app_last in Hy as [[? Hy]|[-> _]]; [by apply Hc|lia].
Qed.

Lemma sbf_B_app p regs tv log :
  sbf_B p regs tv log → sbf_B p regs tv (log ++ [SBX]).
Proof.
  intros [->|[[-> [j Hj]]|[[-> [[j Hj] Htv]]|[-> [[j Hj] Hc]]]]].
  - by left.
  - right; left. split; [done|]. exists j. by apply lookup_app_l_Some.
  - right; right; left. split; [done|]. split.
    + exists j. by apply lookup_app_l_Some.
    + intros j' Hj'. apply Htv.
      eapply lookup_app_old; [exact Hj'|]. intros Hc'.
      by destruct (SBX_ne_SBY (eq_sym Hc')).
  - right; right; right. split; [done|]. split.
    + exists j. by apply lookup_app_l_Some.
    + intros Hr jx jy Hx Hy.
      assert (Hy' : log !! jy = Some SBY).
      { eapply lookup_app_old; [exact Hy|]. intros Hc'.
        by destruct (SBX_ne_SBY (eq_sym Hc')). }
      assert (Hlt : (jy < length log)%nat) by (eapply lookup_lt_Some; exact Hy').
      apply lookup_app_last in Hx as [[? Hx]|[-> _]]; [by apply Hc|lia].
Qed.

Lemma sbf_step c c' : sbf_inv c → lstep c c' → sbf_inv c'.
Proof.
  intros (Himg & [p0 regs0 tv0] & [p1 regs1 tv1] & Hh & Hcont & HA & HB) Hstep.
  simpl in HA, HB.
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|[|i]]; simpl in Hlk; simplify_eq/=.
  - (* ---- hart 0 ---- *)
    destruct HA as [->|[[-> Hex]|[[-> [Hex Htv]]|[-> _]]]]; simpl in Hst;
      [| | |done].
    + (* store x *)
      destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog /store_log. split_and!.
      * apply sbf_content_app; [exact Hcont|by left].
      * right; left. split; [reflexivity|].
        exists (length (c_log c)). apply lookup_app_new.
      * by apply sbf_B_app.
    + (* fence rw,rw *)
      destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog. split_and!.
      * exact Hcont.
      * right; right; left. split; [reflexivity|]. split; [exact Hex|].
        intros j Hj. rewrite /fence_post /=.
        assert (S j ≤ own_pub 0%nat (c_log c))%nat
          by (eapply own_pub_ge; [exact Hj|reflexivity]).
        lia.
      * exact HB.
    + (* load rg1 <- y *)
      destruct Hst as (tv' & v & Hok & Hlog & Hharts).
      destruct Hok as (Hle & Hlen & Hread). rewrite Himg in Hread.
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog. split_and!.
      * exact Hcont.
      * right; right; right. split; [reflexivity|]. split; [exact Hex|].
        rewrite lookup_insert. intros Hv jx jy Hx Hy.
        destruct (decide (jx < jy)%nat) as [?|Hn]; [done|]. exfalso.
        assert (Hvis : visibleb 0%nat tv' (c_log c) (S jy) = true).
        { apply visibleb_below. specialize (Htv _ Hx). lia. }
        destruct (tso_read_from_below img0 (c_log c) 0%nat tv' ay jy SBY b1 v
                    Hy mb_SBY_y Hvis Hread) as (k' & m' & _ & Hk' & Hmb & _).
        destruct (Hcont m' (elem_of_list_lookup_2 _ _ _ Hk')) as [-> | ->].
        { rewrite mb_SBX_y in Hmb. done. }
        rewrite mb_SBY_y in Hmb. apply Hv. congruence.
      * exact HB.
  - (* ---- hart 1 ---- *)
    destruct HB as [->|[[-> Hex]|[[-> [Hex Htv]]|[-> _]]]]; simpl in Hst;
      [| | |done].
    + (* store y *)
      destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog /store_log. split_and!.
      * apply sbf_content_app; [exact Hcont|by right].
      * by apply sbf_A_app.
      * right; left. split; [reflexivity|].
        exists (length (c_log c)). apply lookup_app_new.
    + (* fence rw,rw *)
      destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog. split_and!.
      * exact Hcont.
      * exact HA.
      * right; right; left. split; [reflexivity|]. split; [exact Hex|].
        intros j Hj. rewrite /fence_post /=.
        assert (S j ≤ own_pub 1%nat (c_log c))%nat
          by (eapply own_pub_ge; [exact Hj|reflexivity]).
        lia.
    + (* load rg2 <- x *)
      destruct Hst as (tv' & v & Hok & Hlog & Hharts).
      destruct Hok as (Hle & Hlen & Hread). rewrite Himg in Hread.
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog. split_and!.
      * exact Hcont.
      * exact HA.
      * right; right; right. split; [reflexivity|]. split; [exact Hex|].
        rewrite lookup_insert. intros Hv jx jy Hx Hy.
        destruct (decide (jy < jx)%nat) as [?|Hn]; [done|]. exfalso.
        assert (Hvis : visibleb 1%nat tv' (c_log c) (S jx) = true).
        { apply visibleb_below. specialize (Htv _ Hy). lia. }
        destruct (tso_read_from_below img0 (c_log c) 1%nat tv' ax jx SBX b1 v
                    Hx mb_SBX_x Hvis Hread) as (k' & m' & _ & Hk' & Hmb & _).
        destruct (Hcont m' (elem_of_list_lookup_2 _ _ _ Hk')) as [-> | ->].
        { rewrite mb_SBX_x in Hmb. apply Hv. congruence. }
        rewrite mb_SBY_x in Hmb. done.
Qed.

Lemma sbf_inv0 : sbf_inv sbf_c0.
Proof.
  split; [done|]. eexists _, _. split; [reflexivity|]. simpl.
  split_and!; [by intros ? ?%elem_of_nil|by left|by left].
Qed.

(** SB with both harts fenced: (rg1, rg2) = (0, 0) is UNREACHABLE. *)
Theorem sb_fence_forbidden c regs0 tv0 regs1 tv1 :
  reach sbf_c0 c →
  c_harts c = [Hart [] regs0 tv0; Hart [] regs1 tv1] →
  regs0 !! rg1 = Some b1 ∨ regs1 !! rg2 = Some b1.
Proof.
  intros Hre Hh.
  assert (Hinv : sbf_inv c).
  { eapply inv_reach; [apply sbf_inv0| |exact Hre].
    intros. by eapply sbf_step. }
  destruct Hinv as (_ & g0 & g1 & Hh' & _ & HA & HB).
  rewrite Hh in Hh'. simplify_eq/=.
  destruct HA as [Hc|[[Hc _]|[[Hc _]|[_ [[jx Hjx] HA]]]]]; try discriminate.
  destruct HB as [Hc|[[Hc _]|[[Hc _]|[_ [[jy Hjy] HB]]]]]; try discriminate.
  destruct (decide (regs0 !! rg1 = Some b1)) as [?|Hn0]; [by left|].
  right. destruct (decide (regs1 !! rg2 = Some b1)) as [?|Hn1]; [done|].
  exfalso.
  specialize (HA Hn0 _ _ Hjx Hjy). specialize (HB Hn1 _ _ Hjx Hjy). lia.
Qed.

(* ================================================================== *)
(** ** MP — message passing with NO fences.  The weak outcome is FORBIDDEN
       (herd: forbidden under Ztso).  THE Ztso HEADLINE: no fence anywhere,
       and the flag/data pair still transfers. *)

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
  Cfg img0 [] [Hart [IStore ax b1; IStore ay b1] ∅ 0%nat;
               Hart [ILoad rg1 ay; ILoad rg2 ax] ∅ 0%nat].

(** The writer is the only writer, so its phase FIXES the log. *)
Definition mp_W (p : list instr) (log : list wmsg) : Prop :=
  (p = [IStore ax b1; IStore ay b1] ∧ log = []) ∨
  (p = [IStore ay b1] ∧ log = [MPX]) ∨
  (p = [] ∧ log = [MPX; MPY]).

(** The reader's phase carries the ordering it accumulated: having seen
    y = 1 its view is past timestamp 2, hence past the x-message at 1. *)
Definition mp_R (p : list instr) (regs : gmap nat (bv 8)) (tv : nat) : Prop :=
  (p = [ILoad rg1 ay; ILoad rg2 ax]) ∨
  (p = [ILoad rg2 ax] ∧ (regs !! rg1 = Some b1 → (2 ≤ tv)%nat)) ∨
  (p = [] ∧ (regs !! rg1 = Some b1 → regs !! rg2 = Some b1)).

Definition mp_inv (c : config) : Prop :=
  c_img c = img0 ∧
  ∃ h0 h1, c_harts c = [h0; h1] ∧
    mp_W (h_prog h0) (c_log c) ∧
    mp_R (h_prog h1) (h_regs h1) (h_tv h1).

Lemma mp_step c c' : mp_inv c → lstep c c' → mp_inv c'.
Proof.
  intros (Himg & [p0 regs0 tv0] & [p1 regs1 tv1] & Hh & HW & HR) Hstep.
  simpl in HW, HR.
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|[|i]]; simpl in Hlk; simplify_eq/=.
  - (* ---- the writer ---- *)
    destruct HW as [[-> Hl]|[[-> Hl]|[-> Hl]]]; simpl in Hst; [| |done].
    + destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * right; left. split; [reflexivity|]. rewrite Hlog /store_log Hl //.
      * exact HR.
    + destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * right; right. split; [reflexivity|]. rewrite Hlog /store_log Hl //.
      * exact HR.
  - (* ---- the reader ---- *)
    destruct HR as [->|[[-> Hc]|[-> _]]]; simpl in Hst; [| |done].
    + (* load rg1 <- y *)
      destruct Hst as (tv' & v & Hok & Hlog & Hharts).
      destruct Hok as (Hle & Hlen & Hread). rewrite Himg in Hread.
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * rewrite Hlog. exact HW.
      * right; left. split; [reflexivity|]. rewrite lookup_insert.
        intros Hv. assert (v = b1) as -> by congruence.
        destruct (tso_read_src _ _ _ _ _ _ Hread) as [Hi|(k & m & Hk & Hmb & Hvis)].
        { by destruct (img0_y_nb1 Hi). }
        (* the only y-write is [MPY], at log position 1 *)
        destruct HW as [[_ Hl]|[[_ Hl]|[_ Hl]]]; rewrite Hl in Hk Hvis.
        { rewrite lookup_nil in Hk. discriminate. }
        { destruct k as [|k]; simpl in Hk; [|discriminate].
          injection Hk as Hm; subst. rewrite mb_MPX_y in Hmb. done. }
        destruct k as [|[|k]]; simpl in Hk; [| |discriminate];
          injection Hk as Hm; subst.
        { rewrite mb_MPX_y in Hmb. done. }
        assert (S 1 ≤ tv')%nat; [|lia].
        eapply (visibleb_foreign 1%nat tv' [MPX; MPY] 1%nat MPY);
          [reflexivity|done|exact Hvis].
    + (* load rg2 <- x *)
      destruct Hst as (tv' & v & Hok & Hlog & Hharts).
      destruct Hok as (Hle & Hlen & Hread). rewrite Himg in Hread.
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * rewrite Hlog. exact HW.
      * right; right. split; [reflexivity|].
        rewrite lookup_insert_ne // lookup_insert.
        intros Hv. specialize (Hc Hv).
        (* the view is past 2, so the log has both messages *)
        assert (Hl : c_log c = [MPX; MPY]).
        { destruct HW as [[_ Hl]|[[_ Hl]|[_ Hl]]]; [| |exact Hl];
            exfalso; rewrite Hl in Hlen; simpl in Hlen; lia. }
        rewrite Hl in Hread.
        assert (Hvis : visibleb 1%nat tv' [MPX; MPY] (S 0) = true)
          by (apply visibleb_below; lia).
        destruct (tso_read_from_below img0 [MPX; MPY] 1%nat tv' ax 0%nat MPX b1 v
                    ltac:(reflexivity) mb_MPX_x Hvis Hread)
          as (k' & m' & _ & Hk' & Hmb & _).
        destruct k' as [|[|k']]; simpl in Hk'; [| |discriminate];
          injection Hk' as Hm; subst.
        { rewrite mb_MPX_x in Hmb. congruence. }
        rewrite mb_MPY_x in Hmb. done.
Qed.

Lemma mp_inv0 : mp_inv mp_c0.
Proof.
  split; [done|]. eexists _, _. split; [reflexivity|]. simpl.
  split; by left.
Qed.

(** MP with NO fences: rg1 = 1 forces rg2 = 1. *)
Theorem mp_forbidden c h0 regs tv :
  reach mp_c0 c →
  c_harts c = [h0; Hart [] regs tv] →
  regs !! rg1 = Some b1 → regs !! rg2 = Some b1.
Proof.
  intros Hre Hh H1.
  assert (Hinv : mp_inv c).
  { eapply inv_reach; [apply mp_inv0| |exact Hre]. intros. by eapply mp_step. }
  destruct Hinv as (_ & g0 & g1 & Hh' & _ & HR).
  rewrite Hh in Hh'. simplify_eq/=.
  destruct HR as [Hc|[[Hc _]|[_ Himp]]]; try discriminate. by apply Himp.
Qed.

(* ================================================================== *)
(** ** CoRR — read-read coherence.  Reading a fresh value and then a stale
       one is FORBIDDEN (herd: forbidden).

    Two verdicts, both non-vacuous.  [corr_no_stale]: once C has seen a
    logged write it can never read the era-initial byte again.
    [corr_forbidden]: on the run whose store order is x=1 then x=2, C that
    read 2 must read 2 again.  (The second is stated at a CONCRETE final log
    because the coherence order is a race between the two writers; the
    statement is the herd verdict for that execution.) *)

Local Notation CX1 := (WMsg ax [b1] 0%nat).
Local Notation CX2 := (WMsg ax [b2] 1%nat).

Lemma mb_CX1 : msg_byte CX1 ax = Some b1.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_CX2 : msg_byte CX2 ax = Some b2.
Proof. rewrite msg_byte_single //. Qed.

Definition corr_c0 : config :=
  Cfg img0 [] [Hart [IStore ax b1] ∅ 0%nat;
               Hart [IStore ax b2] ∅ 0%nat;
               Hart [ILoad rg1 ax; ILoad rg2 ax] ∅ 0%nat].

Definition corr_content (log : list wmsg) : Prop :=
  ∀ m, m ∈ log → m = CX1 ∨ m = CX2.

Lemma corr_content_app log m :
  corr_content log → (m = CX1 ∨ m = CX2) → corr_content (log ++ [m]).
Proof.
  intros Hc Hm m' Hin. apply elem_of_app in Hin as [Hin|Hin]; [by apply Hc|].
  apply elem_of_list_singleton in Hin as ->. done.
Qed.

Definition corr_C (p : list instr) (regs : gmap nat (bv 8)) (tv : nat)
    (log : list wmsg) : Prop :=
  (p = [ILoad rg1 ax; ILoad rg2 ax]) ∨
  (p = [ILoad rg2 ax] ∧
     (regs !! rg1 = Some b1 → ∃ j, log !! j = Some CX1 ∧ (S j ≤ tv)%nat) ∧
     (regs !! rg1 = Some b2 → ∃ j, log !! j = Some CX2 ∧ (S j ≤ tv)%nat)) ∨
  (p = [] ∧
     ((regs !! rg1 = Some b1 ∨ regs !! rg1 = Some b2) →
        regs !! rg2 ≠ Some b0) ∧
     (regs !! rg1 = Some b2 →
        regs !! rg2 = Some b2 ∨
        ∃ j1 j2, log !! j1 = Some CX1 ∧ log !! j2 = Some CX2 ∧
                 (j2 ≤ j1)%nat)).

Lemma corr_C_app p regs tv log m :
  corr_C p regs tv log → corr_C p regs tv (log ++ [m]).
Proof.
  intros [->|[[-> [H1 H2]]|[-> [H1 H2]]]].
  - by left.
  - right; left. split; [done|]. split.
    + intros Hr. destruct (H1 Hr) as (j & Hj & ?). exists j.
      split; [by apply lookup_app_l_Some|done].
    + intros Hr. destruct (H2 Hr) as (j & Hj & ?). exists j.
      split; [by apply lookup_app_l_Some|done].
  - right; right. split; [done|]. split; [exact H1|].
    intros Hr. destruct (H2 Hr) as [?|(j1 & j2 & Hj1 & Hj2 & Hle)]; [by left|].
    right. exists j1, j2. split_and!; by [apply lookup_app_l_Some|].
Qed.

Definition corr_inv (c : config) : Prop :=
  c_img c = img0 ∧
  ∃ h0 h1 h2, c_harts c = [h0; h1; h2] ∧ corr_content (c_log c) ∧
    (h_prog h0 = [IStore ax b1] ∨ h_prog h0 = []) ∧
    (h_prog h1 = [IStore ax b2] ∨ h_prog h1 = []) ∧
    corr_C (h_prog h2) (h_regs h2) (h_tv h2) (c_log c).

Lemma corr_step c c' : corr_inv c → lstep c c' → corr_inv c'.
Proof.
  intros (Himg & [p0 regs0 tv0] & [p1 regs1 tv1] & [p2 regs2 tv2]
          & Hh & Hcont & H0 & H1 & HC) Hstep.
  simpl in H0, H1, HC.
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|[|[|i]]]; simpl in Hlk; simplify_eq/=.
  - (* writer 0: x := 1 *)
    destruct H0 as [->| ->]; simpl in Hst; [|done].
    destruct Hst as [Hlog Hharts].
    split; [rewrite Himg' //|]. eexists _, _, _.
    split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
    rewrite Hlog /store_log. split_and!.
    + apply corr_content_app; [exact Hcont|by left].
    + by right.
    + exact H1.
    + by apply corr_C_app.
  - (* writer 1: x := 2 *)
    destruct H1 as [->| ->]; simpl in Hst; [|done].
    destruct Hst as [Hlog Hharts].
    split; [rewrite Himg' //|]. eexists _, _, _.
    split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
    rewrite Hlog /store_log. split_and!.
    + apply corr_content_app; [exact Hcont|by right].
    + exact H0.
    + by right.
    + by apply corr_C_app.
  - (* the reader *)
    destruct HC as [->|[[-> [Hc1 Hc2]]|[-> _]]]; simpl in Hst; [| |done].
    + (* first load *)
      destruct Hst as (tv' & v & Hok & Hlog & Hharts).
      destruct Hok as (Hle & Hlen & Hread). rewrite Himg in Hread.
      split; [rewrite Himg' //|]. eexists _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog. split_and!; [exact Hcont|exact H0|exact H1|].
      right; left. split; [reflexivity|]. rewrite lookup_insert. split.
      * intros Hv. assert (v = b1) as -> by congruence.
        destruct (tso_read_src _ _ _ _ _ _ Hread)
          as [Hi|(k & m & Hk & Hmb & Hvis)].
        { by destruct (img0_x_nb1 Hi). }
        destruct (Hcont m (elem_of_list_lookup_2 _ _ _ Hk)) as [-> | ->];
          last first.
        { rewrite mb_CX2 in Hmb. destruct b1_ne_b2. congruence. }
        exists k. split; [exact Hk|].
        eapply (visibleb_foreign 2%nat tv' (c_log c) k CX1); [exact Hk|done|done].
      * intros Hv. assert (v = b2) as -> by congruence.
        destruct (tso_read_src _ _ _ _ _ _ Hread)
          as [Hi|(k & m & Hk & Hmb & Hvis)].
        { by destruct (img0_x_nb2 Hi). }
        destruct (Hcont m (elem_of_list_lookup_2 _ _ _ Hk)) as [-> | ->].
        { rewrite mb_CX1 in Hmb. destruct b1_ne_b2. congruence. }
        exists k. split; [exact Hk|].
        eapply (visibleb_foreign 2%nat tv' (c_log c) k CX2); [exact Hk|done|done].
    + (* second load *)
      destruct Hst as (tv' & v & Hok & Hlog & Hharts).
      destruct Hok as (Hle & Hlen & Hread). rewrite Himg in Hread.
      split; [rewrite Himg' //|]. eexists _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog. split_and!; [exact Hcont|exact H0|exact H1|].
      right; right. split; [reflexivity|].
      rewrite lookup_insert_ne // lookup_insert. split.
      * (* no stale read *)
        intros [Hv|Hv] Hv2; assert (v = b0) as -> by congruence.
        -- destruct (Hc1 Hv) as (j & Hj & Hjtv).
           assert (Hvis : visibleb 2%nat tv' (c_log c) (S j) = true)
             by (apply visibleb_below; lia).
           destruct (tso_read_from_below img0 (c_log c) 2%nat tv' ax j CX1 b1 b0
                       Hj mb_CX1 Hvis Hread) as (k' & m' & _ & Hk' & Hmb & _).
           destruct (Hcont m' (elem_of_list_lookup_2 _ _ _ Hk')) as [-> | ->].
           ++ rewrite mb_CX1 in Hmb. apply b0_ne_b1. congruence.
           ++ rewrite mb_CX2 in Hmb. apply b0_ne_b2. congruence.
        -- destruct (Hc2 Hv) as (j & Hj & Hjtv).
           assert (Hvis : visibleb 2%nat tv' (c_log c) (S j) = true)
             by (apply visibleb_below; lia).
           destruct (tso_read_from_below img0 (c_log c) 2%nat tv' ax j CX2 b2 b0
                       Hj mb_CX2 Hvis Hread) as (k' & m' & _ & Hk' & Hmb & _).
           destruct (Hcont m' (elem_of_list_lookup_2 _ _ _ Hk')) as [-> | ->].
           ++ rewrite mb_CX1 in Hmb. apply b0_ne_b1. congruence.
           ++ rewrite mb_CX2 in Hmb. apply b0_ne_b2. congruence.
      * (* coherence *)
        intros Hv. destruct (Hc2 Hv) as (j & Hj & Hjtv).
        assert (Hvis : visibleb 2%nat tv' (c_log c) (S j) = true)
          by (apply visibleb_below; lia).
        destruct (tso_read_from_below img0 (c_log c) 2%nat tv' ax j CX2 b2 v
                    Hj mb_CX2 Hvis Hread) as (k' & m' & Hge & Hk' & Hmb & _).
        destruct (Hcont m' (elem_of_list_lookup_2 _ _ _ Hk')) as [-> | ->].
        -- right. exists k', j. rewrite mb_CX1 in Hmb.
           split_and!; [exact Hk'|exact Hj|lia].
        -- left. rewrite mb_CX2 in Hmb. congruence.
Qed.

Lemma corr_inv0 : corr_inv corr_c0.
Proof.
  split; [done|]. eexists _, _, _. split; [reflexivity|]. simpl.
  split_and!; [by intros ? ?%elem_of_nil|by left|by left|by left].
Qed.

(** CoRR, part 1: after a fresh read, the era-initial byte is gone forever. *)
Theorem corr_no_stale c h0 h1 regs tv :
  reach corr_c0 c →
  c_harts c = [h0; h1; Hart [] regs tv] →
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

(** CoRR, part 2: on the execution whose store order is x=1 then x=2, a
    reader that saw 2 cannot go back to 1 — it must see 2 again. *)
Theorem corr_forbidden c h0 h1 regs tv :
  reach corr_c0 c →
  c_harts c = [h0; h1; Hart [] regs tv] →
  c_log c = [CX1; CX2] →
  regs !! rg1 = Some b2 → regs !! rg2 = Some b2.
Proof.
  intros Hre Hh Hlog H1.
  assert (Hinv : corr_inv c).
  { eapply inv_reach; [apply corr_inv0| |exact Hre].
    intros. by eapply corr_step. }
  destruct Hinv as (_ & g0 & g1 & g2 & Hh' & _ & _ & _ & HC).
  rewrite Hh in Hh'. simplify_eq/=.
  destruct HC as [Hc|[[Hc _]|[_ [_ Himp]]]]; try discriminate.
  destruct (Himp H1) as [?|(j1 & j2 & Hj1 & Hj2 & Hle)]; [done|].
  exfalso. rewrite Hlog in Hj1 Hj2.
  destruct j1 as [|[|j1]]; simpl in Hj1; [| |discriminate].
  - destruct j2 as [|[|j2]]; simpl in Hj2; [| |discriminate];
      [by simplify_eq|lia].
  - by simplify_eq.
Qed.

(* ================================================================== *)
(** ** LB — load buffering.  Both loads returning 1 is FORBIDDEN
       (herd: forbidden under Ztso — R→W is ordered, so the log cannot
       contain a store that its own hart's earlier load has not resolved). *)

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
  Cfg img0 [] [Hart [ILoad rg1 ay; IStore ax b1] ∅ 0%nat;
               Hart [ILoad rg2 ax; IStore ay b1] ∅ 0%nat].

Definition lb_content (log : list wmsg) : Prop :=
  ∀ m, m ∈ log → m = LBX ∨ m = LBY.

Lemma lb_content_app log m :
  lb_content log → (m = LBX ∨ m = LBY) → lb_content (log ++ [m]).
Proof.
  intros Hc Hm m' Hin. apply elem_of_app in Hin as [Hin|Hin]; [by apply Hc|].
  apply elem_of_list_singleton in Hin as ->. done.
Qed.

(** The invariant: each hart's own message is absent from the log until it
    stores, a load that returned 1 witnesses the OTHER hart's message, and
    the two "returned 1"s are mutually exclusive — the last conjunct is
    established at whichever load runs second and is stable thereafter. *)
Definition lb_inv (c : config) : Prop :=
  c_img c = img0 ∧
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
  intros (Himg & [p0 regs0 tv0] & [p1 regs1 tv1] & Hh & Hcont & Hn0 & Hn1
          & Hp0 & Hp1 & Hy1 & Hr1 & Hr0 & Hno) Hstep.
  simpl in Hn0, Hn1, Hp0, Hp1, Hy1, Hr1, Hr0, Hno.
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|[|i]]; simpl in Hlk; simplify_eq/=.
  - (* ---- hart 0 ---- *)
    destruct Hp0 as [->|[->| ->]]; simpl in Hst; [| |done].
    + (* load rg1 <- y *)
      destruct Hst as (tv' & v & Hok & Hlog & Hharts).
      destruct Hok as (Hle & Hlen & Hread). rewrite Himg in Hread.
      assert (HnX : LBX ∉ c_log c) by (apply Hn0; by left).
      assert (Hv : v = b1 → LBY ∈ c_log c).
      { intros ->.
        destruct (tso_read_src _ _ _ _ _ _ Hread)
          as [Hi|(k & m & Hk & Hmb & Hvis)].
        { by destruct (img0_y_nb1 Hi). }
        destruct (Hcont m (elem_of_list_lookup_2 _ _ _ Hk)) as [-> | ->].
        { rewrite mb_LBX_y in Hmb. done. }
        by eapply elem_of_list_lookup_2. }
      split; [rewrite Himg' //|]. eexists _, _.
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
        (* hart 1 already finished, and it did not read 1: else LBX ∈ log *)
        specialize (Hr1 Hv2). done.
    + (* store x *)
      destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
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
      destruct Hst as (tv' & v & Hok & Hlog & Hharts).
      destruct Hok as (Hle & Hlen & Hread). rewrite Himg in Hread.
      assert (HnY : LBY ∉ c_log c) by (apply Hn1; by left).
      assert (Hv : v = b1 → LBX ∈ c_log c).
      { intros ->.
        destruct (tso_read_src _ _ _ _ _ _ Hread)
          as [Hi|(k & m & Hk & Hmb & Hvis)].
        { by destruct (img0_x_nb1 Hi). }
        destruct (Hcont m (elem_of_list_lookup_2 _ _ _ Hk)) as [-> | ->];
          last first.
        { rewrite mb_LBY_x in Hmb. done. }
        by eapply elem_of_list_lookup_2. }
      split; [rewrite Himg' //|]. eexists _, _.
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
      destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
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
  split; [done|]. eexists _, _. split; [reflexivity|]. simpl.
  split_and!; try (intros; by apply not_elem_of_nil);
    [by intros ? ?%elem_of_nil|by left|by left| | | |].
  - intros Hin%elem_of_nil. done.
  - by intros ?%lookup_empty_Some.
  - by intros ?%lookup_empty_Some.
  - intros [H _]. by apply lookup_empty_Some in H.
Qed.

(** LB: rg1 = 1 ∧ rg2 = 1 is UNREACHABLE. *)
Theorem lb_forbidden c regs0 tv0 regs1 tv1 :
  reach lb_c0 c →
  c_harts c = [Hart [] regs0 tv0; Hart [] regs1 tv1] →
  regs0 !! rg1 = Some b1 → regs1 !! rg2 ≠ Some b1.
Proof.
  intros Hre Hh Ha Hb.
  assert (Hinv : lb_inv c).
  { eapply inv_reach; [apply lb_inv0| |exact Hre]. intros. by eapply lb_step. }
  destruct Hinv as (_ & g0 & g1 & Hh' & _ & _ & _ & _ & _ & _ & _ & _ & Hno).
  rewrite Hh in Hh'. simplify_eq/=. by apply Hno.
Qed.

(* ================================================================== *)
(** ** IRIW — independent reads of independent writes.  FORBIDDEN with NO
       fences (herd: forbidden under Ztso; TSO is multi-copy atomic).

    The single global log is the total store order, so "x entered before y"
    and "y entered before x" cannot both hold. *)

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
  Cfg img0 []
      [Hart [IStore ax b1] ∅ 0%nat;
       Hart [IStore ay b1] ∅ 0%nat;
       Hart [ILoad rg1 ax; ILoad rg2 ay] ∅ 0%nat;
       Hart [ILoad rg3 ay; ILoad rg4 ax] ∅ 0%nat].

Definition iriw_content (log : list wmsg) : Prop :=
  ∀ m, m ∈ log → m = IX ∨ m = IY.

Lemma iriw_content_app log m :
  iriw_content log → (m = IX ∨ m = IY) → iriw_content (log ++ [m]).
Proof.
  intros Hc Hm m' Hin. apply elem_of_app in Hin as [Hin|Hin]; [by apply Hc|].
  apply elem_of_list_singleton in Hin as ->. done.
Qed.

(** Reader C: x then y.  Its final conjunct is "the x-message is strictly
    below EVERY y-message" — stable under appends because a fresh message
    lands past every existing index. *)
Definition iriw_C (p : list instr) (regs : gmap nat (bv 8)) (tv : nat)
    (log : list wmsg) : Prop :=
  (p = [ILoad rg1 ax; ILoad rg2 ay]) ∨
  (p = [ILoad rg2 ay] ∧
     (regs !! rg1 = Some b1 → ∃ j, log !! j = Some IX ∧ (S j ≤ tv)%nat)) ∨
  (p = [] ∧
     (regs !! rg1 = Some b1 → regs !! rg2 = Some b0 →
        ∃ jx, log !! jx = Some IX ∧
              ∀ jy, log !! jy = Some IY → (jx < jy)%nat)).

Definition iriw_D (p : list instr) (regs : gmap nat (bv 8)) (tv : nat)
    (log : list wmsg) : Prop :=
  (p = [ILoad rg3 ay; ILoad rg4 ax]) ∨
  (p = [ILoad rg4 ax] ∧
     (regs !! rg3 = Some b1 → ∃ j, log !! j = Some IY ∧ (S j ≤ tv)%nat)) ∨
  (p = [] ∧
     (regs !! rg3 = Some b1 → regs !! rg4 = Some b0 →
        ∃ jy, log !! jy = Some IY ∧
              ∀ jx, log !! jx = Some IX → (jy < jx)%nat)).

Lemma iriw_C_app p regs tv log m :
  iriw_C p regs tv log → iriw_C p regs tv (log ++ [m]).
Proof.
  intros [->|[[-> H]|[-> H]]].
  - by left.
  - right; left. split; [done|]. intros Hr. destruct (H Hr) as (j & Hj & ?).
    exists j. split; [by apply lookup_app_l_Some|done].
  - right; right. split; [done|]. intros H1 H2.
    destruct (H H1 H2) as (jx & Hjx & Hlt).
    assert (Hb : (jx < length log)%nat) by (eapply lookup_lt_Some; exact Hjx).
    exists jx. split; [by apply lookup_app_l_Some|].
    intros jy Hjy. apply lookup_app_last in Hjy as [[? Hjy]|[-> _]];
      [by apply Hlt|lia].
Qed.

Lemma iriw_D_app p regs tv log m :
  iriw_D p regs tv log → iriw_D p regs tv (log ++ [m]).
Proof.
  intros [->|[[-> H]|[-> H]]].
  - by left.
  - right; left. split; [done|]. intros Hr. destruct (H Hr) as (j & Hj & ?).
    exists j. split; [by apply lookup_app_l_Some|done].
  - right; right. split; [done|]. intros H1 H2.
    destruct (H H1 H2) as (jy & Hjy & Hlt).
    assert (Hb : (jy < length log)%nat) by (eapply lookup_lt_Some; exact Hjy).
    exists jy. split; [by apply lookup_app_l_Some|].
    intros jx Hjx. apply lookup_app_last in Hjx as [[? Hjx]|[-> _]];
      [by apply Hlt|lia].
Qed.

Definition iriw_inv (c : config) : Prop :=
  c_img c = img0 ∧
  ∃ h0 h1 h2 h3, c_harts c = [h0; h1; h2; h3] ∧ iriw_content (c_log c) ∧
    (h_prog h0 = [IStore ax b1] ∨ h_prog h0 = []) ∧
    (h_prog h1 = [IStore ay b1] ∨ h_prog h1 = []) ∧
    iriw_C (h_prog h2) (h_regs h2) (h_tv h2) (c_log c) ∧
    iriw_D (h_prog h3) (h_regs h3) (h_tv h3) (c_log c).

Lemma iriw_step c c' : iriw_inv c → lstep c c' → iriw_inv c'.
Proof.
  intros (Himg & [q0 g0 u0] & [q1 g1 u1] & [q2 g2 u2] & [q3 g3 u3]
          & Hh & Hcont & H0 & H1 & HC & HD) Hstep.
  simpl in H0, H1, HC, HD.
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|[|[|[|i]]]]; simpl in Hlk; simplify_eq/=.
  - (* writer x *)
    destruct H0 as [->| ->]; simpl in Hst; [|done].
    destruct Hst as [Hlog Hharts].
    split; [rewrite Himg' //|]. eexists _, _, _, _.
    split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
    rewrite Hlog /store_log. split_and!.
    + apply iriw_content_app; [exact Hcont|by left].
    + by right.
    + exact H1.
    + by apply iriw_C_app.
    + by apply iriw_D_app.
  - (* writer y *)
    destruct H1 as [->| ->]; simpl in Hst; [|done].
    destruct Hst as [Hlog Hharts].
    split; [rewrite Himg' //|]. eexists _, _, _, _.
    split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
    rewrite Hlog /store_log. split_and!.
    + apply iriw_content_app; [exact Hcont|by right].
    + exact H0.
    + by right.
    + by apply iriw_C_app.
    + by apply iriw_D_app.
  - (* reader C *)
    destruct HC as [->|[[-> Hc]|[-> _]]]; simpl in Hst; [| |done].
    + destruct Hst as (tv' & v & Hok & Hlog & Hharts).
      destruct Hok as (Hle & Hlen & Hread). rewrite Himg in Hread.
      split; [rewrite Himg' //|]. eexists _, _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog. split_and!; [exact Hcont|exact H0|exact H1| |exact HD].
      right; left. split; [reflexivity|]. rewrite lookup_insert.
      intros Hv. assert (v = b1) as -> by congruence.
      destruct (tso_read_src _ _ _ _ _ _ Hread)
        as [Hi|(k & m & Hk & Hmb & Hvis)].
      { by destruct (img0_x_nb1 Hi). }
      destruct (Hcont m (elem_of_list_lookup_2 _ _ _ Hk)) as [-> | ->];
        last first.
      { rewrite mb_IY_x in Hmb. done. }
      exists k. split; [exact Hk|].
      eapply (visibleb_foreign 2%nat tv' (c_log c) k IX); [exact Hk|done|done].
    + destruct Hst as (tv' & v & Hok & Hlog & Hharts).
      destruct Hok as (Hle & Hlen & Hread). rewrite Himg in Hread.
      split; [rewrite Himg' //|]. eexists _, _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog. split_and!; [exact Hcont|exact H0|exact H1| |exact HD].
      right; right. split; [reflexivity|].
      rewrite lookup_insert_ne // lookup_insert.
      intros Hv1 Hv2. assert (v = b0) as -> by congruence.
      destruct (Hc Hv1) as (jx & Hjx & Hjtv). exists jx. split; [exact Hjx|].
      intros jy Hjy. destruct (decide (jx < jy)%nat) as [?|Hn]; [done|].
      exfalso.
      assert (Hvis : visibleb 2%nat tv' (c_log c) (S jy) = true)
        by (apply visibleb_below; lia).
      destruct (tso_read_from_below img0 (c_log c) 2%nat tv' ay jy IY b1 b0
                  Hjy mb_IY_y Hvis Hread) as (k' & m' & _ & Hk' & Hmb & _).
      destruct (Hcont m' (elem_of_list_lookup_2 _ _ _ Hk')) as [-> | ->].
      { rewrite mb_IX_y in Hmb. done. }
      rewrite mb_IY_y in Hmb. apply b0_ne_b1. congruence.
  - (* reader D *)
    destruct HD as [->|[[-> Hc]|[-> _]]]; simpl in Hst; [| |done].
    + destruct Hst as (tv' & v & Hok & Hlog & Hharts).
      destruct Hok as (Hle & Hlen & Hread). rewrite Himg in Hread.
      split; [rewrite Himg' //|]. eexists _, _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog. split_and!; [exact Hcont|exact H0|exact H1|exact HC|].
      right; left. split; [reflexivity|]. rewrite lookup_insert.
      intros Hv. assert (v = b1) as -> by congruence.
      destruct (tso_read_src _ _ _ _ _ _ Hread)
        as [Hi|(k & m & Hk & Hmb & Hvis)].
      { by destruct (img0_y_nb1 Hi). }
      destruct (Hcont m (elem_of_list_lookup_2 _ _ _ Hk)) as [-> | ->].
      { rewrite mb_IX_y in Hmb. done. }
      exists k. split; [exact Hk|].
      eapply (visibleb_foreign 3%nat tv' (c_log c) k IY); [exact Hk|done|done].
    + destruct Hst as (tv' & v & Hok & Hlog & Hharts).
      destruct Hok as (Hle & Hlen & Hread). rewrite Himg in Hread.
      split; [rewrite Himg' //|]. eexists _, _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog. split_and!; [exact Hcont|exact H0|exact H1|exact HC|].
      right; right. split; [reflexivity|].
      rewrite lookup_insert_ne // lookup_insert.
      intros Hv1 Hv2. assert (v = b0) as -> by congruence.
      destruct (Hc Hv1) as (jy & Hjy & Hjtv). exists jy. split; [exact Hjy|].
      intros jx Hjx. destruct (decide (jy < jx)%nat) as [?|Hn]; [done|].
      exfalso.
      assert (Hvis : visibleb 3%nat tv' (c_log c) (S jx) = true)
        by (apply visibleb_below; lia).
      destruct (tso_read_from_below img0 (c_log c) 3%nat tv' ax jx IX b1 b0
                  Hjx mb_IX_x Hvis Hread) as (k' & m' & _ & Hk' & Hmb & _).
      destruct (Hcont m' (elem_of_list_lookup_2 _ _ _ Hk')) as [-> | ->].
      { rewrite mb_IX_x in Hmb. apply b0_ne_b1. congruence. }
      rewrite mb_IY_x in Hmb. done.
Qed.

Lemma iriw_inv0 : iriw_inv iriw_c0.
Proof.
  split; [done|]. eexists _, _, _, _. split; [reflexivity|]. simpl.
  split_and!; [by intros ? ?%elem_of_nil|by left|by left|by left|by left].
Qed.

(** IRIW with NO fences: (1,0,1,0) is UNREACHABLE. *)
Theorem iriw_forbidden c h0 h1 regs2 tv2 regs3 tv3 :
  reach iriw_c0 c →
  c_harts c = [h0; h1; Hart [] regs2 tv2; Hart [] regs3 tv3] →
  regs2 !! rg1 = Some b1 → regs2 !! rg2 = Some b0 →
  regs3 !! rg3 = Some b1 → regs3 !! rg4 ≠ Some b0.
Proof.
  intros Hre Hh Ha1 Ha2 Hb1 Hb2.
  assert (Hinv : iriw_inv c).
  { eapply inv_reach; [apply iriw_inv0| |exact Hre].
    intros. by eapply iriw_step. }
  destruct Hinv as (_ & k0 & k1 & k2 & k3 & Hh' & _ & _ & _ & HC & HD).
  rewrite Hh in Hh'. simplify_eq/=.
  destruct HC as [Hc|[[Hc _]|[_ HimpC]]]; try discriminate.
  destruct HD as [Hc|[[Hc _]|[_ HimpD]]]; try discriminate.
  destruct (HimpC Ha1 Ha2) as (jx & Hjx & HltC).
  destruct (HimpD Hb1 Hb2) as (jy & Hjy & HltD).
  specialize (HltC _ Hjy). specialize (HltD _ Hjx). lia.
Qed.

(* ================================================================== *)
(** ** n6 — the store buffer drains LATE.  ALLOWED (herd: allowed under
       Ztso, forbidden under SC).

    Hart 0 reads its own [x = 1] by forwarding while its buffer has not
    drained, misses hart 1's [y = 2] entirely, and its x-store still lands
    LAST in the store order — so flat memory ends at [x = 1] even though
    hart 1's [x = 2] is program-order later than the [y = 2] hart 0 could
    not see.  No SC interleaving produces this. *)

Definition n6_c0 : config :=
  Cfg img0 [] [Hart [IStore ax b1; ILoad rg1 ax; ILoad rg2 ay] ∅ 0%nat;
               Hart [IStore ay b2; IStore ax b2] ∅ 0%nat].

Lemma n6_allowed :
  ∃ c, reach n6_c0 c ∧
       (∃ regs tv, c_harts c !! 0%nat = Some (Hart [] regs tv) ∧
                   regs !! rg1 = Some b1 ∧ regs !! rg2 = Some b0) ∧
       (∃ regs tv, c_harts c !! 1%nat = Some (Hart [] regs tv)) ∧
       flat img0 (c_log c) ax = Some b1.
Proof.
  rewrite /n6_c0. eexists. split.
  { eapply rtc_l; [eapply (step_store _ 1%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 1%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 0%nat rg1 ax _ _ _ 0%nat b1);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 0%nat rg2 ay _ _ _ 0%nat b0);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split_and!.
  - do 2 eexists. split; [reflexivity|].
    rewrite lookup_insert. split; [|reflexivity].
    rewrite lookup_insert_ne // lookup_insert //.
  - do 2 eexists. reflexivity.
  - vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(** ** AMO strength — lock-acquire ordering with ZERO fences.

    [amoswap.aq] reads at the top of the log and lands its view past its own
    append, so an AMO that took the lock word after another hart's AMO sees
    everything that hart published before releasing.  The hypothesis "B's AMO
    is log-later than A's" is stated as an index comparison in the final log;
    without it the outcome is genuinely allowed (B may take the word first). *)

Local Notation AMX := (WMsg ax [b1] 0%nat).   (* hart 0's plain store *)
Local Notation AMA := (WMsg ay [b1] 0%nat).   (* hart 0's AMO write *)
Local Notation AMB := (WMsg ay [b2] 1%nat).   (* hart 1's AMO write *)

Lemma mb_AMX_x : msg_byte AMX ax = Some b1.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_AMA_x : msg_byte AMA ax = None.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_AMB_x : msg_byte AMB ax = None.
Proof. rewrite msg_byte_single //. Qed.
Lemma AMA_ne_AMB : AMA ≠ AMB.
Proof. intros H. by simplify_eq/=. Qed.
Lemma AMA_ne_AMX : AMA ≠ AMX.
Proof. intros H. by simplify_eq/=. Qed.
Lemma AMB_ne_AMX : AMB ≠ AMX.
Proof. intros H. by simplify_eq/=. Qed.
Lemma AMB_ne_AMA : AMB ≠ AMA.
Proof. intros H. by simplify_eq/=. Qed.

Definition amo_c0 : config :=
  Cfg img0 [] [Hart [IStore ax b1; IAmoSwapAq rg1 ay b1] ∅ 0%nat;
               Hart [IAmoSwapAq rg2 ay b2; ILoad rg3 ax] ∅ 0%nat].

Definition amo_content (log : list wmsg) : Prop :=
  ∀ m, m ∈ log → m = AMX ∨ m = AMA ∨ m = AMB.

Lemma amo_content_app log m :
  amo_content log → (m = AMX ∨ m = AMA ∨ m = AMB) →
  amo_content (log ++ [m]).
Proof.
  intros Hc Hm m' Hin. apply elem_of_app in Hin as [Hin|Hin]; [by apply Hc|].
  apply elem_of_list_singleton in Hin as ->. done.
Qed.

Definition amo_A (p : list instr) (log : list wmsg) : Prop :=
  (p = [IStore ax b1; IAmoSwapAq rg1 ay b1]) ∨
  (p = [IAmoSwapAq rg1 ay b1] ∧ ∃ j, log !! j = Some AMX) ∨
  (p = []).

Definition amo_B (p : list instr) (regs : gmap nat (bv 8)) (tv : nat)
    (log : list wmsg) : Prop :=
  (p = [IAmoSwapAq rg2 ay b2; ILoad rg3 ax]) ∨
  (p = [ILoad rg3 ax] ∧ (∀ jb, log !! jb = Some AMB → (S jb ≤ tv)%nat)) ∨
  (p = [] ∧
     (∀ ja jb, log !! ja = Some AMA → log !! jb = Some AMB →
               (ja < jb)%nat → regs !! rg3 = Some b1)).

Definition amo_inv (c : config) : Prop :=
  c_img c = img0 ∧
  ∃ h0 h1, c_harts c = [h0; h1] ∧ amo_content (c_log c) ∧
    (* A's plain store is below A's AMO write: program order = log order *)
    (∀ ja, c_log c !! ja = Some AMA →
           ∃ jx, (jx < ja)%nat ∧ c_log c !! jx = Some AMX) ∧
    amo_A (h_prog h0) (c_log c) ∧
    amo_B (h_prog h1) (h_regs h1) (h_tv h1) (c_log c).

Lemma amo_A_app p log m : amo_A p log → amo_A p (log ++ [m]).
Proof.
  intros [->|[[-> [j Hj]]| ->]]; [by left| |by right; right].
  right; left. split; [done|]. exists j. by apply lookup_app_l_Some.
Qed.

Lemma amo_step c c' : amo_inv c → lstep c c' → amo_inv c'.
Proof.
  intros (Himg & [p0 regs0 tv0] & [p1 regs1 tv1] & Hh & Hcont & Hord & HA & HB)
         Hstep.
  simpl in HA, HB.
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|[|i]]; simpl in Hlk; simplify_eq/=.
  - (* ---- hart 0 ---- *)
    destruct HA as [->|[[-> [jx Hjx]]| ->]]; simpl in Hst; [| |done].
    + (* plain store x := 1 *)
      destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog /store_log. split_and!.
      * apply amo_content_app; [exact Hcont|by left].
      * intros ja Hja.
        assert (Hja' : c_log c !! ja = Some AMA)
          by (eapply lookup_app_old; [exact Hja|apply AMA_ne_AMX]).
        destruct (Hord _ Hja') as (jx & ? & Hjx). exists jx.
        split; [done|by apply lookup_app_l_Some].
      * right; left. split; [reflexivity|].
        exists (length (c_log c)). apply lookup_app_new.
      * destruct HB as [->|[[-> H]|[-> H]]].
        { by left. }
        { right; left. split; [reflexivity|]. intros jb Hjb. apply H.
          eapply lookup_app_old; [exact Hjb|apply AMB_ne_AMX]. }
        right; right. split; [reflexivity|]. intros ja jb Hja Hjb Hlt.
        apply (H ja jb).
        -- eapply lookup_app_old; [exact Hja|apply AMA_ne_AMX].
        -- eapply lookup_app_old; [exact Hjb|apply AMB_ne_AMX].
        -- exact Hlt.
    + (* the AMO write [y := 1] *)
      destruct Hst as (v_old & Hex & Hlog & Hharts).
      assert (Hlt : (jx < length (c_log c))%nat)
        by (eapply lookup_lt_Some; exact Hjx).
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog /store_log. split_and!.
      * apply amo_content_app; [exact Hcont|by right; left].
      * intros ja Hja. apply lookup_app_last in Hja as [[? Hja]|[-> _]].
        -- destruct (Hord _ Hja) as (j & ? & Hj). exists j.
           split; [done|by apply lookup_app_l_Some].
        -- exists jx. split; [done|by apply lookup_app_l_Some].
      * by right; right.
      * destruct HB as [->|[[-> H]|[-> H]]].
        { by left. }
        { right; left. split; [reflexivity|]. intros jb Hjb. apply H.
          eapply lookup_app_old; [exact Hjb|apply AMB_ne_AMA]. }
        right; right. split; [reflexivity|]. intros ja jb Hja Hjb Hlt'.
        assert (Hjb' : c_log c !! jb = Some AMB)
          by (eapply lookup_app_old; [exact Hjb|apply AMB_ne_AMA]).
        assert (Hjbl : (jb < length (c_log c))%nat)
          by (eapply lookup_lt_Some; exact Hjb').
        apply lookup_app_last in Hja as [[? Hja]|[-> _]];
          [by apply (H ja jb)|lia].
  - (* ---- hart 1 ---- *)
    destruct HB as [->|[[-> Htv]|[-> _]]]; simpl in Hst; [| |done].
    + (* the AMO write [y := 2]: the view lands past the append *)
      destruct Hst as (v_old & Hex & Hlog & Hharts).
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog /store_log. split_and!.
      * apply amo_content_app; [exact Hcont|by right; right].
      * intros ja Hja.
        assert (Hja' : c_log c !! ja = Some AMA)
          by (eapply lookup_app_old; [exact Hja|apply AMA_ne_AMB]).
        destruct (Hord _ Hja') as (j & ? & Hj). exists j.
        split; [done|by apply lookup_app_l_Some].
      * by apply amo_A_app.
      * right; left. split; [reflexivity|]. intros jb Hjb.
        assert (jb < length (c_log c ++ [AMB]))%nat
          by (eapply lookup_lt_Some; exact Hjb).
        rewrite length_app /= in H. lia.
    + (* load rg3 <- x *)
      destruct Hst as (tv' & v & Hok & Hlog & Hharts).
      destruct Hok as (Hle & Hlen & Hread). rewrite Himg in Hread.
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog. split_and!.
      * exact Hcont.
      * exact Hord.
      * exact HA.
      * right; right. split; [reflexivity|].
        rewrite lookup_insert. intros ja jb Hja Hjb Hlt.
        specialize (Htv _ Hjb).
        destruct (Hord _ Hja) as (jx & Hjxlt & Hjx).
        assert (Hvis : visibleb 1%nat tv' (c_log c) (S jx) = true)
          by (apply visibleb_below; lia).
        destruct (tso_read_from_below img0 (c_log c) 1%nat tv' ax jx AMX b1 v
                    Hjx mb_AMX_x Hvis Hread) as (k' & m' & _ & Hk' & Hmb & _).
        destruct (Hcont m' (elem_of_list_lookup_2 _ _ _ Hk'))
          as [-> | [-> | ->]].
        -- rewrite mb_AMX_x in Hmb. congruence.
        -- rewrite mb_AMA_x in Hmb. done.
        -- rewrite mb_AMB_x in Hmb. done.
Qed.

Lemma amo_inv0 : amo_inv amo_c0.
Proof.
  split; [done|]. eexists _, _. split; [reflexivity|]. simpl.
  split_and!; [by intros ? ?%elem_of_nil| |by left|by left].
  intros ja Hja. rewrite lookup_nil in Hja. discriminate.
Qed.

(** AMO strength: if hart 1's AMO write is log-later than hart 0's, hart 1's
    plain load of x sees hart 0's pre-AMO store — no fence anywhere. *)
Theorem amo_strong c h0 regs tv ja jb :
  reach amo_c0 c →
  c_harts c = [h0; Hart [] regs tv] →
  c_log c !! ja = Some AMA → c_log c !! jb = Some AMB → (ja < jb)%nat →
  regs !! rg3 = Some b1.
Proof.
  intros Hre Hh Hja Hjb Hlt.
  assert (Hinv : amo_inv c).
  { eapply inv_reach; [apply amo_inv0| |exact Hre].
    intros. by eapply amo_step. }
  destruct Hinv as (_ & g0 & g1 & Hh' & _ & _ & _ & HB).
  rewrite Hh in Hh'. simplify_eq/=.
  destruct HB as [Hc|[[Hc _]|[_ Himp]]]; try discriminate.
  by apply (Himp ja jb).
Qed.

(* ================================================================== *)
(** ** Non-vacuity of the FORBIDDEN verdicts

    A "forbidden" theorem is worth nothing if no completed run reaches the
    shape it quantifies over.  Each verdict above therefore gets a witness:
    a concrete interleaving that runs every hart to completion, lands on
    exactly the configuration shape the verdict is stated over, and
    satisfies the verdict's HYPOTHESES — so what the theorem rules out is
    the outcome, not the shape. *)

(** [sb_fence_forbidden]: the fenced SB harts do complete, and the machine
    really produces the one-sided outcome (0, 1) — the store that lost the
    race to the log is the one whose hart is forced to see the winner. *)
Lemma sbf_completed_reachable :
  ∃ c regs0 tv0 regs1 tv1,
    reach sbf_c0 c ∧ c_harts c = [Hart [] regs0 tv0; Hart [] regs1 tv1] ∧
    regs0 !! rg1 = Some b0 ∧ regs1 !! rg2 = Some b1.
Proof.
  rewrite /sbf_c0. eexists _, _, _, _, _. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_fence _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 0%nat rg1 ay _ _ _ 1%nat b0);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l; [eapply (step_store _ 1%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_fence _ 1%nat); reflexivity|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg2 ax _ _ _ 2%nat b1);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split; rewrite lookup_insert //.
Qed.

(** [mp_forbidden]: the reader can and does read the flag as 1 — and then,
    as the theorem says, the data too. *)
Lemma mp_completed_reachable :
  ∃ c h0 regs tv,
    reach mp_c0 c ∧ c_harts c = [h0; Hart [] regs tv] ∧
    regs !! rg1 = Some b1 ∧ regs !! rg2 = Some b1.
Proof.
  rewrite /mp_c0. eexists _, _, _, _. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg1 ay _ _ _ 2%nat b1);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg2 ax _ _ _ 2%nat b1);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
Qed.

(** [corr_forbidden]/[corr_no_stale]: the concrete log [CX1; CX2] and the
    first read of 2 are both reachable. *)
Lemma corr_completed_reachable :
  ∃ c h0 h1 regs tv,
    reach corr_c0 c ∧ c_harts c = [h0; h1; Hart [] regs tv] ∧
    c_log c = [CX1; CX2] ∧
    regs !! rg1 = Some b2 ∧ regs !! rg2 = Some b2.
Proof.
  rewrite /corr_c0. eexists _, _, _, _, _. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 1%nat); reflexivity|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 2%nat rg1 ax _ _ _ 2%nat b2);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 2%nat rg2 ax _ _ _ 2%nat b2);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split; [reflexivity|]. split.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
Qed.

(** [lb_forbidden]: both LB harts complete; the machine produces (0, 1). *)
Lemma lb_completed_reachable :
  ∃ c regs0 tv0 regs1 tv1,
    reach lb_c0 c ∧ c_harts c = [Hart [] regs0 tv0; Hart [] regs1 tv1] ∧
    regs0 !! rg1 = Some b0 ∧ regs1 !! rg2 = Some b1.
Proof.
  rewrite /lb_c0. eexists _, _, _, _, _. split.
  { eapply rtc_l;
      [eapply (step_load _ 0%nat rg1 ay _ _ _ 0%nat b0);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg2 ax _ _ _ 1%nat b1);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l; [eapply (step_store _ 1%nat); reflexivity|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split; rewrite lookup_insert //.
Qed.

(** [iriw_forbidden]: all four harts complete, and THREE of the four
    hypothesised reads happen — only [rg4 = 0] is missing, which is exactly
    what the theorem forbids. *)
Lemma iriw_completed_reachable :
  ∃ c h0 h1 regs2 tv2 regs3 tv3,
    reach iriw_c0 c ∧
    c_harts c = [h0; h1; Hart [] regs2 tv2; Hart [] regs3 tv3] ∧
    regs2 !! rg1 = Some b1 ∧ regs2 !! rg2 = Some b0 ∧
    regs3 !! rg3 = Some b1 ∧ regs3 !! rg4 = Some b1.
Proof.
  rewrite /iriw_c0. eexists _, _, _, _, _, _, _. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 1%nat); reflexivity|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 2%nat rg1 ax _ _ _ 1%nat b1);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 2%nat rg2 ay _ _ _ 1%nat b0);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 3%nat rg3 ay _ _ _ 2%nat b1);
        [reflexivity|solve_load]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 3%nat rg4 ax _ _ _ 2%nat b1);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split_and!.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
Qed.

(** [amo_strong]: the AMO pair runs, hart 0's AMO write really does land at
    log index 1 with hart 1's at index 2, and hart 1's plain load then reads
    hart 0's pre-AMO store — the verdict, exhibited. *)
Lemma amo_completed_reachable :
  ∃ c h0 regs tv,
    reach amo_c0 c ∧ c_harts c = [h0; Hart [] regs tv] ∧
    c_log c = [AMX; AMA; AMB] ∧
    c_log c !! 1%nat = Some AMA ∧ c_log c !! 2%nat = Some AMB ∧
    regs !! rg3 = Some b1.
Proof.
  rewrite /amo_c0. eexists _, _, _, _. split.
  { eapply rtc_l; [eapply (step_store _ 0%nat); reflexivity|]. simpl.
    eapply rtc_l;
      [eapply (step_amo _ 0%nat rg1 ay b1 _ _ _ b0);
        [reflexivity|solve_excl]|]. simpl.
    eapply rtc_l;
      [eapply (step_amo _ 1%nat rg2 ay b2 _ _ _ b1);
        [reflexivity|solve_excl]|]. simpl.
    eapply rtc_l;
      [eapply (step_load _ 1%nat rg3 ax _ _ _ 3%nat b1);
        [reflexivity|solve_load]|]. simpl.
    apply rtc_refl. }
  split; [reflexivity|]. split; [reflexivity|]. split_and!;
    [reflexivity|reflexivity|].
  rewrite lookup_insert //.
Qed.
