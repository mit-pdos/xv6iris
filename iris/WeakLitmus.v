(** * WeakLitmus.v — executable litmus programs over the M0 view machine

    A tiny hart-program language (NOT Sail) on top of [WeakMem]'s promise-free
    view machine, plus the litmus suite the design doc makes a standing
    obligation ([claude-notes/design/weak-memory.md], "Validation"): SB, MP with
    and without fences, MP with an acquire load, CoRR, LB, IRIW.

    Verdicts are stated against riscv.cat/herd expectations, and the two places
    where this machine is deliberately STRONGER than RVWMO are called out in
    comments as gap witnesses (see [lb_forbidden] and
    [mp_reader_fence_only_forbidden]).

    Like [WeakMem.v] this file imports only stdpp. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite relations list.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem.

(* ------------------------------------------------------------------ *)
(** ** Bytes, addresses, registers

    Everything is a literal so that the concrete side conditions ([bool_decide]
    guards, [gmap] lookups, [coh] defaults) reduce by computation. *)

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

(** The era-initial image: both litmus bytes read as 0 at timestamp 0.  (The
    alternative — seeding explicit init messages into the log — would shift
    every timestamp by the number of init bytes and buy nothing.) *)
Definition img0m : gmap Z (bv 8) := <[ax := b0]> {[ay := b0]}.
(** [WeakMem.image] is a partial FUNCTION on [Z] (so that M1's interpreter can
    read the tree's [gmap Arch.pa _] image through the address seam without a
    [kmap]); the litmus image is still built as a two-entry map. *)
Definition img0 : image := λ a, img0m !! a.

Lemma img0_x : img0 ax = Some b0.
Proof. rewrite /img0 /img0m lookup_insert //. Qed.
Lemma img0_y : img0 ay = Some b0.
Proof. rewrite /img0 /img0m lookup_insert_ne // lookup_singleton //. Qed.

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

(** Reading a concrete log at a concrete timestamp. *)
Lemma log_byte_1 img m rest a : log_byte img (m :: rest) 1 a = msg_byte m a.
Proof. done. Qed.
Lemma log_byte_2 img m0 m1 rest a :
  log_byte img (m0 :: m1 :: rest) 2 a = msg_byte m1 a.
Proof. done. Qed.

(** The reflection of [writes_in] every concrete side condition below goes
    through ([msg_writesb] / [writes_inb] / [not_writes_in_compute] /
    [writes_in_compute]) lives in [WeakMem.v] — the functional interpreter
    [WeakInterp.wexec] checks read admissibility with the same procedure. *)

(* ------------------------------------------------------------------ *)
(** ** The hart-program language *)

Inductive instr :=
| ILoad (reg : nat) (a : Z) (aq : bool)
| IStore (a : Z) (v : bv 8)
| IFence (pr pw sr sw : bool)
(** [amoswap.aq]: an acquire load of the per-byte globally-LATEST value plus a
    store, atomically in one step (design doc, the AMO paragraph: "one
    [prim_step] is a whole instruction, so the read and write halves interleave
    with nothing; atomicity + coherence force the read to take the per-byte
    latest message"). *)
| IAmoSwapAq (reg : nat) (a : Z) (v : bv 8).

Record hart := Hart {
  h_prog : list instr;               (* the remaining program IS the pc *)
  h_regs : gmap nat (bv 8);
  h_ws   : wstate;
}.

Record config := Cfg {
  c_img   : image;
  c_log   : list wmsg;
  c_harts : list hart;
}.

(** One small step: pick a hart, execute its next instruction.  Loads
    ∃-quantify an admissible timestamp ([readable]); stores append at the log's
    fresh top; the AMO does both in one step under the atomicity constraint. *)
Definition lstep (c c' : config) : Prop :=
  ∃ (i : nat) (h : hart),
    c_harts c !! i = Some h ∧ c_img c' = c_img c ∧
    match h_prog h with
    | [] => False
    | ILoad r a aq :: rest => ∃ (t : nat) (v : bv 8),
        log_byte (c_img c) (c_log c) t a = Some v ∧
        readable (c_img c) (c_log c) (h_ws h) (load_vpre (h_ws h) aq) a t ∧
        c_log c' = c_log c ∧
        c_harts c' = <[i := Hart rest (<[r := v]> (h_regs h))
                                 (load_post (h_ws h) aq a t)]> (c_harts c)
    | IStore a v :: rest =>
        c_log c' = c_log c ++ [WMsg a [v] (Some i)] ∧
        c_harts c' = <[i := Hart rest (h_regs h)
                                 (store_post (h_ws h) false a
                                    (S (length (c_log c))))]> (c_harts c)
    | IFence pr pw sr sw :: rest =>
        c_log c' = c_log c ∧
        c_harts c' = <[i := Hart rest (h_regs h)
                                 (fence_post (h_ws h) pr pw sr sw)]> (c_harts c)
    | IAmoSwapAq r a v :: rest => ∃ (t : nat) (vv : bv 8),
        log_byte (c_img c) (c_log c) t a = Some vv ∧
        (* atomicity: the read half takes the globally-latest write to [a] *)
        ¬ writes_in (c_log c) a t (length (c_log c)) ∧
        readable (c_img c) (c_log c) (h_ws h) (load_vpre (h_ws h) true) a t ∧
        c_log c' = c_log c ++ [WMsg a [v] (Some i)] ∧
        c_harts c' = <[i := Hart rest (<[r := vv]> (h_regs h))
                          (store_post (load_post (h_ws h) true a t) false a
                                      (S (length (c_log c))))]> (c_harts c)
    end.

(** The AMO's atomicity constraint really does pin the read: at most one
    timestamp is both a write to [a] and unshadowed in the whole log. *)
Lemma amo_latest_unique img log a t t' :
  is_Some (log_byte img log t a) → ¬ writes_in log a t (length log) →
  is_Some (log_byte img log t' a) → ¬ writes_in log a t' (length log) →
  t = t'.
Proof.
  intros Ht Hnt Ht' Hnt'. exact (latest_unique img log a t t'
    (conj Ht Hnt) (conj Ht' Hnt')).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Step constructors (used to exhibit interleavings) *)

Lemma step_load c i r a aq rest regs ws t v :
  c_harts c !! i = Some (Hart (ILoad r a aq :: rest) regs ws) →
  log_byte (c_img c) (c_log c) t a = Some v →
  readable (c_img c) (c_log c) ws (load_vpre ws aq) a t →
  lstep c (Cfg (c_img c) (c_log c)
               (<[i := Hart rest (<[r := v]> regs) (load_post ws aq a t)]>
                  (c_harts c))).
Proof.
  intros Hlk Hv Hr. exists i, (Hart (ILoad r a aq :: rest) regs ws).
  split_and!; [done|done|]. simpl. exists t, v. by split_and!.
Qed.

Lemma step_store c i a v rest regs ws :
  c_harts c !! i = Some (Hart (IStore a v :: rest) regs ws) →
  lstep c (Cfg (c_img c) (c_log c ++ [WMsg a [v] (Some i)])
               (<[i := Hart rest regs
                        (store_post ws false a (S (length (c_log c))))]>
                  (c_harts c))).
Proof.
  intros Hlk. exists i, (Hart (IStore a v :: rest) regs ws).
  split_and!; [done|done|]. simpl. by split_and!.
Qed.

Lemma step_fence c i pr pw sr sw rest regs ws :
  c_harts c !! i = Some (Hart (IFence pr pw sr sw :: rest) regs ws) →
  lstep c (Cfg (c_img c) (c_log c)
               (<[i := Hart rest regs (fence_post ws pr pw sr sw)]>
                  (c_harts c))).
Proof.
  intros Hlk. exists i, (Hart (IFence pr pw sr sw :: rest) regs ws).
  split_and!; [done|done|]. simpl. by split_and!.
Qed.

(** Reachability. *)
Notation reach := (rtc lstep).

Lemma inv_reach (I : config → Prop) c0 c :
  I c0 → (∀ a b, I a → lstep a b → I b) → reach c0 c → I c.
Proof. intros H0 Hpres H. induction H as [|???? IH]; [done|]. eauto. Qed.

(* ------------------------------------------------------------------ *)
(** ** Litmus programs *)

(** fence rw,w — the release-side writer fence *)
Local Notation FENCE_RW_W := (IFence true true false true).
(** fence r,rw — the acquire-side reader fence *)
Local Notation FENCE_R_RW := (IFence true false true true).
(** fence rw,rw *)
Local Notation FENCE_RW_RW := (IFence true true true true).

Ltac solve_is_Some := vm_compute; by eexists.
Ltac solve_nw := apply not_writes_in_compute; vm_compute; reflexivity.

(* ------------------------------------------------------------------ *)
(** *** SB — store buffering.  Both loads reading 0 is ALLOWED (herd: allowed) *)

Definition sb_prog0 : list instr := [IStore ax b1; ILoad rg1 ay false].
Definition sb_prog1 : list instr := [IStore ay b1; ILoad rg2 ax false].
Definition sb_c0 : config :=
  Cfg img0 [] [Hart sb_prog0 ∅ ws_init; Hart sb_prog1 ∅ ws_init].

Lemma sb_00_reachable :
  ∃ c, reach sb_c0 c ∧
       (∃ regs ws, c_harts c !! 0 = Some (Hart [] regs ws) ∧
                   regs !! rg1 = Some b0) ∧
       (∃ regs ws, c_harts c !! 1 = Some (Hart [] regs ws) ∧
                   regs !! rg2 = Some b0).
Proof.
  rewrite /sb_c0 /sb_prog0 /sb_prog1.
  eexists. split.
  { eapply rtc_l; [eapply (step_store _ 0); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 1); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_load _ 0 rg1 ay false _ _ _ 0 b0);
                   [reflexivity|apply img0_y|split; [solve_is_Some|solve_nw]]|].
    simpl.
    eapply rtc_l; [eapply (step_load _ 1 rg2 ax false _ _ _ 0 b0);
                   [reflexivity|apply img0_x|split; [solve_is_Some|solve_nw]]|].
    simpl. apply rtc_refl. }
  split.
  - do 2 eexists. split; [reflexivity|]. rewrite lookup_insert //.
  - do 2 eexists. split; [reflexivity|]. rewrite lookup_insert //.
Qed.

(* ------------------------------------------------------------------ *)
(** *** MP with no fences — the weak outcome is ALLOWED (herd: allowed) *)

Definition mp_w_nofence : list instr := [IStore ax b1; IStore ay b1].
Definition mp_r_nofence : list instr := [ILoad rg1 ay false; ILoad rg2 ax false].
Definition mp_nofence_c0 : config :=
  Cfg img0 [] [Hart mp_w_nofence ∅ ws_init; Hart mp_r_nofence ∅ ws_init].

Lemma mp_nofence_weak_reachable :
  ∃ c, reach mp_nofence_c0 c ∧
       ∃ regs ws, c_harts c !! 1 = Some (Hart [] regs ws) ∧
                  regs !! rg1 = Some b1 ∧ regs !! rg2 = Some b0.
Proof.
  rewrite /mp_nofence_c0 /mp_w_nofence /mp_r_nofence.
  eexists. split.
  { eapply rtc_l; [eapply (step_store _ 0); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 0); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_load _ 1 rg1 ay false _ _ _ 2 b1);
                   [reflexivity
                   |rewrite log_byte_2 msg_byte_single; vm_compute; reflexivity
                   |split; [solve_is_Some|solve_nw]]|].
    simpl.
    eapply rtc_l; [eapply (step_load _ 1 rg2 ax false _ _ _ 0 b0);
                   [reflexivity|apply img0_x|split; [solve_is_Some|solve_nw]]|].
    simpl. apply rtc_refl. }
  do 2 eexists. split; [reflexivity|]. split.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
Qed.

(* ------------------------------------------------------------------ *)
(** *** MP with a WRITER fence only — still ALLOWED (herd: allowed).

    In this promise-free machine the writer fence is inert (stores are never
    early), so it cannot forbid anything on its own; RVWMO agrees. *)

Definition mp_w_fenced : list instr := [IStore ax b1; FENCE_RW_W; IStore ay b1].
Definition mp_wfence_c0 : config :=
  Cfg img0 [] [Hart mp_w_fenced ∅ ws_init; Hart mp_r_nofence ∅ ws_init].

Lemma mp_wfence_weak_reachable :
  ∃ c, reach mp_wfence_c0 c ∧
       ∃ regs ws, c_harts c !! 1 = Some (Hart [] regs ws) ∧
                  regs !! rg1 = Some b1 ∧ regs !! rg2 = Some b0.
Proof.
  rewrite /mp_wfence_c0 /mp_w_fenced /mp_r_nofence.
  eexists. split.
  { eapply rtc_l; [eapply (step_store _ 0); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_fence _ 0); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_store _ 0); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_load _ 1 rg1 ay false _ _ _ 2 b1);
                   [reflexivity
                   |rewrite log_byte_2 msg_byte_single; vm_compute; reflexivity
                   |split; [solve_is_Some|solve_nw]]|].
    simpl.
    eapply rtc_l; [eapply (step_load _ 1 rg2 ax false _ _ _ 0 b0);
                   [reflexivity|apply img0_x|split; [solve_is_Some|solve_nw]]|].
    simpl. apply rtc_refl. }
  do 2 eexists. split; [reflexivity|]. split.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
Qed.

(* ------------------------------------------------------------------ *)
(** *** SB with both harts fenced — the ONE-SIDED outcome is reachable.

    (0,0) is forbidden with both fences; (0,1) is not, and the machine really
    does produce it: the hart whose store lost the race to the log is forced to
    see the winner's store. *)

Definition sbf_prog0 : list instr :=
  [IStore ax b1; FENCE_RW_RW; ILoad rg1 ay false].
Definition sbf_prog1 : list instr :=
  [IStore ay b1; FENCE_RW_RW; ILoad rg2 ax false].
Definition sbf_c0 : config :=
  Cfg img0 [] [Hart sbf_prog0 ∅ ws_init; Hart sbf_prog1 ∅ ws_init].

Lemma sb_fenced_01_reachable :
  ∃ c, reach sbf_c0 c ∧
       (∃ regs ws, c_harts c !! 0 = Some (Hart [] regs ws) ∧
                   regs !! rg1 = Some b0) ∧
       (∃ regs ws, c_harts c !! 1 = Some (Hart [] regs ws) ∧
                   regs !! rg2 = Some b1).
Proof.
  rewrite /sbf_c0 /sbf_prog0 /sbf_prog1.
  eexists. split.
  { eapply rtc_l; [eapply (step_store _ 0); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_fence _ 0); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_load _ 0 rg1 ay false _ _ _ 0 b0);
                   [reflexivity|apply img0_y|split; [solve_is_Some|solve_nw]]|].
    simpl.
    eapply rtc_l; [eapply (step_store _ 1); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_fence _ 1); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_load _ 1 rg2 ax false _ _ _ 1 b1);
                   [reflexivity
                   |rewrite log_byte_1 msg_byte_single; vm_compute; reflexivity
                   |split; [solve_is_Some|solve_nw]]|].
    simpl. apply rtc_refl. }
  split.
  - do 2 eexists. split; [reflexivity|]. rewrite lookup_insert //.
  - do 2 eexists. split; [reflexivity|]. rewrite lookup_insert //.
Qed.

(* ================================================================== *)
(** ** FORBIDDEN outcomes

    These are the real work: unreachability over ALL interleavings.  Each proof
    is an induction over [reach] with a hand-built global invariant.  Two
    structural facts do the heavy lifting and hold BY CONSTRUCTION of [lstep]:
    the log is append-only (so [writes_in] is monotone), and each hart's stores
    enter the log in program order (a store appends at [S (length log)], and
    the hart cannot run its next store before this one). *)

(** Reading a concrete log at an arbitrary timestamp. *)
Lemma log_byte_cases0 img a t v :
  log_byte img [] t a = Some v → t = 0%nat ∧ img a = Some v.
Proof. destruct t as [|i]; simpl; [intros H; by split|done]. Qed.

Lemma log_byte_cases1 img m a t v :
  log_byte img [m] t a = Some v →
  (t = 0%nat ∧ img a = Some v) ∨ (t = 1%nat ∧ msg_byte m a = Some v).
Proof.
  destruct t as [|[|i]]; simpl; [intros H; left; by split
                                |intros H; right; by split|done].
Qed.

Lemma log_byte_cases2 img m0 m1 a t v :
  log_byte img [m0; m1] t a = Some v →
  (t = 0%nat ∧ img a = Some v) ∨ (t = 1%nat ∧ msg_byte m0 a = Some v)
  ∨ (t = 2%nat ∧ msg_byte m1 a = Some v).
Proof.
  destruct t as [|[|[|i]]]; simpl;
    [intros H; left; by split
    |intros H; right; left; by split
    |intros H; right; right; by split|done].
Qed.

Lemma img0_x_nb1 : img0 ax ≠ Some b1.
Proof. rewrite img0_x. intros H. apply b0_ne_b1. congruence. Qed.
Lemma img0_y_nb1 : img0 ay ≠ Some b1.
Proof. rewrite img0_y. intros H. apply b0_ne_b1. congruence. Qed.

(* ------------------------------------------------------------------ *)
(** *** The MP family: shared message facts and read analyses *)

Local Notation MX := (WMsg ax [b1] (Some 0%nat)).
Local Notation MY := (WMsg ay [b1] (Some 0%nat)).

Lemma mb_MX_x : msg_byte MX ax = Some b1.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_MX_y : msg_byte MX ay = None.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_MY_x : msg_byte MY ax = None.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_MY_y : msg_byte MY ay = Some b1.
Proof. rewrite msg_byte_single //. Qed.

(** The only logs any MP-family run can produce: the writer stores x then y,
    and nothing else ever writes. *)
Definition mp_logs (log : list wmsg) : Prop :=
  log = [] ∨ log = [MX] ∨ log = [MX; MY].

(** Reading y = 1 pins the timestamp to the y-message, and the x-message is
    strictly below it in the global order.  This is where "each hart's stores
    appear in the log in program order" is cashed in. *)
Lemma mp_read_y_1 log t :
  mp_logs log → log_byte img0 log t ay = Some b1 →
  t = 2%nat ∧ writes_in log ax 0 2.
Proof.
  intros [->|[->| ->]] Hlb.
  - apply log_byte_cases0 in Hlb as [_ Hi]. by destruct (img0_y_nb1 Hi).
  - apply log_byte_cases1 in Hlb as [[_ Hi]|[_ Hm]].
    + by destruct (img0_y_nb1 Hi).
    + rewrite mb_MX_y in Hm. done.
  - apply log_byte_cases2 in Hlb as [[_ Hi]|[[_ Hm]|[Ht _]]].
    + by destruct (img0_y_nb1 Hi).
    + rewrite mb_MX_y in Hm. done.
    + split; [done|]. apply writes_in_compute. vm_compute. reflexivity.
Qed.

(** Any non-initial read of x returns 1: the x-message is the only write. *)
Lemma mp_read_x log t v :
  mp_logs log → log_byte img0 log t ax = Some v → t ≠ 0%nat → v = b1.
Proof.
  intros [->|[->| ->]] Hlb Hne.
  - by apply log_byte_cases0 in Hlb as [-> _].
  - apply log_byte_cases1 in Hlb as [[-> _]|[_ Hm]]; [done|].
    rewrite mb_MX_x in Hm. congruence.
  - apply log_byte_cases2 in Hlb as [[-> _]|[[_ Hm]|[_ Hm]]]; [done| |].
    + rewrite mb_MX_x in Hm. congruence.
    + rewrite mb_MY_x in Hm. done.
Qed.

(* ------------------------------------------------------------------ *)
(** *** MP with writer [fence rw,w] AND reader [fence r,rw]:
        the weak outcome is FORBIDDEN (herd: forbidden). *)

Local Notation MPF_W0 := ([IStore ax b1; FENCE_RW_W; IStore ay b1]).
Local Notation MPF_W1 := ([FENCE_RW_W; IStore ay b1]).
Local Notation MPF_W2 := ([IStore ay b1]).
Local Notation MPF_R0 :=
  ([ILoad rg1 ay false; FENCE_R_RW; ILoad rg2 ax false]).
Local Notation MPF_R1 := ([FENCE_R_RW; ILoad rg2 ax false]).
Local Notation MPF_R2 := ([ILoad rg2 ax false]).

Definition mpf_c0 : config :=
  Cfg img0 [] [Hart MPF_W0 ∅ ws_init; Hart MPF_R0 ∅ ws_init].

(** The writer's phase determines the log exactly (it is the only writer). *)
Definition mpf_W (p : list instr) (log : list wmsg) : Prop :=
  (p = MPF_W0 ∧ log = []) ∨ (p = MPF_W1 ∧ log = [MX]) ∨
  (p = MPF_W2 ∧ log = [MX]) ∨ (p = [] ∧ log = [MX; MY]).

(** The reader's phase carries the ordering it has accumulated: once it has
    seen y = 1, the x-message is below its read floor.

    THE FORWARD-BANK CONJUNCT.  Since M1 wires [w_fwd] into the load view
    ([WeakMem.fwd_view]), "the load's post-view covers the timestamp it read"
    only holds for a NON-forwarded read.  A reader that never stores has an
    empty bank, and neither [load_post] nor [fence_post] populates one, so the
    conjunct is trivially inductive — and it is the honest statement of what
    the ordering argument needs.  (The MP+acquire reader needs no such
    conjunct: forwarding is disabled for acquire loads.) *)
Definition mpf_R (p : list instr) (regs : gmap nat (bv 8)) (ws : wstate)
    (log : list wmsg) : Prop :=
  w_fwd ws = ∅ ∧
  ((p = MPF_R0) ∨
   (p = MPF_R1 ∧ (regs !! rg1 = Some b1 → writes_in log ax 0 (w_vrOld ws))) ∨
   (p = MPF_R2 ∧ (regs !! rg1 = Some b1 → writes_in log ax 0 (w_vrNew ws))) ∨
   (p = [] ∧ (regs !! rg1 = Some b1 → regs !! rg2 = Some b1))).

Definition mpf_inv (c : config) : Prop :=
  c_img c = img0 ∧
  ∃ h0 h1, c_harts c = [h0; h1] ∧
    mpf_W (h_prog h0) (c_log c) ∧
    mpf_R (h_prog h1) (h_regs h1) (h_ws h1) (c_log c).

Lemma mpf_W_logs p log : mpf_W p log → mp_logs log.
Proof. rewrite /mp_logs. intros [[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]]; auto. Qed.

Lemma mpf_R_app p regs ws log l :
  mpf_R p regs ws log → mpf_R p regs ws (log ++ l).
Proof.
  intros [Hf HR]. split; [exact Hf|]. destruct HR as [->|[[-> H]|[[-> H]|[-> H]]]].
  - by left.
  - right; left. split; [done|]. intros ?. by apply writes_in_app, H.
  - right; right; left. split; [done|]. intros ?. by apply writes_in_app, H.
  - right; right; right. by split.
Qed.

Lemma mpf_step c c' : mpf_inv c → lstep c c' → mpf_inv c'.
Proof.
  intros (Himg & [p0 regs0 ws0] & [p1 regs1 ws1] & Hh & HW & HR) Hstep.
  simpl in HW, HR.
  pose proof (mpf_W_logs _ _ HW) as Hlogs.
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|[|i]]; simpl in Hlk; simplify_eq/=.
  - (* ---- the writer steps ---- *)
    destruct HW as [[-> Hl]|[[-> Hl]|[[-> Hl]|[-> Hl]]]]; simpl in Hst;
      [| | |done].
    + destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * right; left. split; [reflexivity|]. rewrite Hlog Hl //.
      * rewrite Hlog. by apply mpf_R_app.
    + destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * right; right; left. split; [reflexivity|]. rewrite Hlog Hl //.
      * rewrite Hlog. exact HR.
    + destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * right; right; right. split; [reflexivity|]. rewrite Hlog Hl //.
      * rewrite Hlog. by apply mpf_R_app.
  - (* ---- the reader steps ---- *)
    destruct HR as [Hfwd HR].
    destruct HR as [->|[[-> HRc]|[[-> HRc]|[-> HRc]]]]; simpl in Hst;
      [| | |done].
    + (* load r1 <- y *)
      destruct Hst as (t & v & Hlb & Hrd & Hlog & Hharts).
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * rewrite Hlog. exact HW.
      * split; [rewrite load_post_fwd; exact Hfwd|].
        right; left. split; [reflexivity|]. rewrite lookup_insert.
        intros Hv. assert (v = b1) as -> by congruence.
        rewrite Himg in Hlb.
        apply (mp_read_y_1 _ _ Hlogs) in Hlb as [-> Hw].
        rewrite Hlog. eapply writes_in_mono_hi; [|exact Hw].
        apply load_post_vrOld_nofwd; exact Hfwd.
    + (* fence r,rw *)
      destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * rewrite Hlog. exact HW.
      * split; [rewrite fence_post_fwd; exact Hfwd|].
        right; right; left. split; [reflexivity|]. intros Hv.
        rewrite Hlog. eapply writes_in_mono_hi; [|by apply HRc].
        apply fence_post_vrNew_r.
    + (* load r2 <- x *)
      destruct Hst as (t & v & Hlb & Hrd & Hlog & Hharts).
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * rewrite Hlog. exact HW.
      * split; [rewrite load_post_fwd; exact Hfwd|].
        right; right; right. split; [reflexivity|].
        rewrite lookup_insert_ne // lookup_insert. intros Hv.
        assert (Hpre : writes_in (c_log c) ax 0 (load_vpre ws1 false)).
        { eapply writes_in_mono_hi; [|by apply HRc]. apply load_vpre_vrNew. }
        rewrite Himg in Hlb.
        assert (t ≠ 0%nat) as Hne.
        { eapply readable_not_init; [exact Hrd|exact Hpre]. }
        assert (v = b1) as -> by (eapply mp_read_x; [exact Hlogs|exact Hlb|done]).
        reflexivity.
Qed.

Lemma mpf_inv0 : mpf_inv mpf_c0.
Proof.
  split; [done|]. eexists _, _. split; [reflexivity|]. simpl. split.
  - by left.
  - split; [done|by left].
Qed.

(** MP + writer [fence rw,w] + reader [fence r,rw]: r1 = 1 ∧ r2 = 0 is
    UNREACHABLE.  Agrees with RVWMO. *)
Theorem mp_fenced_forbidden c h0 regs1 ws1 :
  reach mpf_c0 c →
  c_harts c = [h0; Hart [] regs1 ws1] →
  regs1 !! rg1 = Some b1 →
  regs1 !! rg2 ≠ Some b0.
Proof.
  intros Hre Hh H1 H2.
  assert (Hinv : mpf_inv c).
  { eapply inv_reach; [apply mpf_inv0| |exact Hre]. intros. by eapply mpf_step. }
  destruct Hinv as (_ & g0 & g1 & Hh' & _ & _ & HR).
  rewrite Hh in Hh'. simplify_eq/=.
  destruct HR as [Hc|[[Hc _]|[[Hc _]|[_ Himp]]]]; try discriminate.
  pose proof (Himp H1) as H3. apply b0_ne_b1. congruence.
Qed.

(* ------------------------------------------------------------------ *)
(** *** MP with writer [fence rw,w] and an ACQUIRE reader load:
        the weak outcome is FORBIDDEN (herd: forbidden).

    The reader's first access is [ld.aq] on y — the read half of
    [amoswap.w.aq], which is how the kernel's [acquire] is spelled.  No reader
    fence: the acquire's own [vrNew] update does the ordering. *)

Local Notation MPA_R0 := ([ILoad rg1 ay true; ILoad rg2 ax false]).
Local Notation MPA_R1 := ([ILoad rg2 ax false]).

Definition mpa_c0 : config :=
  Cfg img0 [] [Hart MPF_W0 ∅ ws_init; Hart MPA_R0 ∅ ws_init].

Definition mpa_R (p : list instr) (regs : gmap nat (bv 8)) (ws : wstate)
    (log : list wmsg) : Prop :=
  (p = MPA_R0) ∨
  (p = MPA_R1 ∧ (regs !! rg1 = Some b1 → writes_in log ax 0 (w_vrNew ws))) ∨
  (p = [] ∧ (regs !! rg1 = Some b1 → regs !! rg2 = Some b1)).

Definition mpa_inv (c : config) : Prop :=
  c_img c = img0 ∧
  ∃ h0 h1, c_harts c = [h0; h1] ∧
    mpf_W (h_prog h0) (c_log c) ∧
    mpa_R (h_prog h1) (h_regs h1) (h_ws h1) (c_log c).

Lemma mpa_R_app p regs ws log l :
  mpa_R p regs ws log → mpa_R p regs ws (log ++ l).
Proof.
  intros [->|[[-> H]|[-> H]]].
  - by left.
  - right; left. split; [done|]. intros ?. by apply writes_in_app, H.
  - right; right. by split.
Qed.

Lemma mpa_step c c' : mpa_inv c → lstep c c' → mpa_inv c'.
Proof.
  intros (Himg & [p0 regs0 ws0] & [p1 regs1 ws1] & Hh & HW & HR) Hstep.
  simpl in HW, HR.
  pose proof (mpf_W_logs _ _ HW) as Hlogs.
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|[|i]]; simpl in Hlk; simplify_eq/=.
  - destruct HW as [[-> Hl]|[[-> Hl]|[[-> Hl]|[-> Hl]]]]; simpl in Hst;
      [| | |done].
    + destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * right; left. split; [reflexivity|]. rewrite Hlog Hl //.
      * rewrite Hlog. by apply mpa_R_app.
    + destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * right; right; left. split; [reflexivity|]. rewrite Hlog Hl //.
      * rewrite Hlog. exact HR.
    + destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * right; right; right. split; [reflexivity|]. rewrite Hlog Hl //.
      * rewrite Hlog. by apply mpa_R_app.
  - destruct HR as [->|[[-> HRc]|[-> HRc]]]; simpl in Hst; [| |done].
    + (* ld.aq r1 <- y *)
      destruct Hst as (t & v & Hlb & Hrd & Hlog & Hharts).
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * rewrite Hlog. exact HW.
      * right; left. split; [reflexivity|]. rewrite lookup_insert.
        intros Hv. assert (v = b1) as -> by congruence.
        rewrite Himg in Hlb.
        apply (mp_read_y_1 _ _ Hlogs) in Hlb as [-> Hw].
        rewrite Hlog. eapply writes_in_mono_hi; [|exact Hw].
        apply load_post_vrNew_aq.
    + (* load r2 <- x *)
      destruct Hst as (t & v & Hlb & Hrd & Hlog & Hharts).
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * rewrite Hlog. exact HW.
      * right; right. split; [reflexivity|].
        rewrite lookup_insert_ne // lookup_insert. intros Hv.
        assert (Hpre : writes_in (c_log c) ax 0 (load_vpre ws1 false)).
        { eapply writes_in_mono_hi; [|by apply HRc]. apply load_vpre_vrNew. }
        rewrite Himg in Hlb.
        assert (t ≠ 0%nat) as Hne.
        { eapply readable_not_init; [exact Hrd|exact Hpre]. }
        assert (v = b1) as -> by (eapply mp_read_x; [exact Hlogs|exact Hlb|done]).
        reflexivity.
Qed.

Theorem mp_acquire_forbidden c h0 regs1 ws1 :
  reach mpa_c0 c →
  c_harts c = [h0; Hart [] regs1 ws1] →
  regs1 !! rg1 = Some b1 →
  regs1 !! rg2 ≠ Some b0.
Proof.
  intros Hre Hh H1 H2.
  assert (Hinv : mpa_inv c).
  { eapply inv_reach; [|  |exact Hre].
    - split; [done|]. eexists _, _. split; [reflexivity|]. simpl.
      split; by left.
    - intros. by eapply mpa_step. }
  destruct Hinv as (_ & g0 & g1 & Hh' & _ & HR).
  rewrite Hh in Hh'. simplify_eq/=.
  destruct HR as [Hc|[[Hc _]|[_ Himp]]]; try discriminate.
  pose proof (Himp H1) as H3. apply b0_ne_b1. congruence.
Qed.

(* ------------------------------------------------------------------ *)
(** *** GAP WITNESS #2 — MP with NO writer fence but a reader [fence r,rw].

    RVWMO ALLOWS the weak outcome here (nothing orders the writer's two
    stores, so W→W may be reordered), but this machine FORBIDS it: the
    promise-free single-append log hardwires every hart's stores into the
    global order in program order, which is exactly the machinery a promise
    would defeat.  This is the second documented way in which the M0 machine
    is STRONGER than RVWMO (the first is the absence of load buffering — see
    [lb_forbidden]).  Both gaps are in the sound direction for the kernel
    proofs, and both are retired by the M6 robustness theorem. *)

Local Notation MPG_W0 := ([IStore ax b1; IStore ay b1]).
Local Notation MPG_W1 := ([IStore ay b1]).

Definition mpg_c0 : config :=
  Cfg img0 [] [Hart MPG_W0 ∅ ws_init; Hart MPF_R0 ∅ ws_init].

Definition mpg_W (p : list instr) (log : list wmsg) : Prop :=
  (p = MPG_W0 ∧ log = []) ∨ (p = MPG_W1 ∧ log = [MX]) ∨
  (p = [] ∧ log = [MX; MY]).

Definition mpg_inv (c : config) : Prop :=
  c_img c = img0 ∧
  ∃ h0 h1, c_harts c = [h0; h1] ∧
    mpg_W (h_prog h0) (c_log c) ∧
    mpf_R (h_prog h1) (h_regs h1) (h_ws h1) (c_log c).

Lemma mpg_W_logs p log : mpg_W p log → mp_logs log.
Proof. rewrite /mp_logs. intros [[_ ->]|[[_ ->]|[_ ->]]]; auto. Qed.

Lemma mpg_step c c' : mpg_inv c → lstep c c' → mpg_inv c'.
Proof.
  intros (Himg & [p0 regs0 ws0] & [p1 regs1 ws1] & Hh & HW & HR) Hstep.
  simpl in HW, HR.
  pose proof (mpg_W_logs _ _ HW) as Hlogs.
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|[|i]]; simpl in Hlk; simplify_eq/=.
  - destruct HW as [[-> Hl]|[[-> Hl]|[-> Hl]]]; simpl in Hst; [| |done].
    + destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * right; left. split; [reflexivity|]. rewrite Hlog Hl //.
      * rewrite Hlog. by apply mpf_R_app.
    + destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * right; right. split; [reflexivity|]. rewrite Hlog Hl //.
      * rewrite Hlog. by apply mpf_R_app.
  - destruct HR as [Hfwd HR].
    destruct HR as [->|[[-> HRc]|[[-> HRc]|[-> HRc]]]]; simpl in Hst;
      [| | |done].
    + destruct Hst as (t & v & Hlb & Hrd & Hlog & Hharts).
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * rewrite Hlog. exact HW.
      * split; [rewrite load_post_fwd; exact Hfwd|].
        right; left. split; [reflexivity|]. rewrite lookup_insert.
        intros Hv. assert (v = b1) as -> by congruence.
        rewrite Himg in Hlb.
        apply (mp_read_y_1 _ _ Hlogs) in Hlb as [-> Hw].
        rewrite Hlog. eapply writes_in_mono_hi; [|exact Hw].
        apply load_post_vrOld_nofwd; exact Hfwd.
    + destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * rewrite Hlog. exact HW.
      * split; [rewrite fence_post_fwd; exact Hfwd|].
        right; right; left. split; [reflexivity|]. intros Hv.
        rewrite Hlog. eapply writes_in_mono_hi; [|by apply HRc].
        apply fence_post_vrNew_r.
    + destruct Hst as (t & v & Hlb & Hrd & Hlog & Hharts).
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * rewrite Hlog. exact HW.
      * split; [rewrite load_post_fwd; exact Hfwd|].
        right; right; right. split; [reflexivity|].
        rewrite lookup_insert_ne // lookup_insert. intros Hv.
        assert (Hpre : writes_in (c_log c) ax 0 (load_vpre ws1 false)).
        { eapply writes_in_mono_hi; [|by apply HRc]. apply load_vpre_vrNew. }
        rewrite Himg in Hlb.
        assert (t ≠ 0%nat) as Hne.
        { eapply readable_not_init; [exact Hrd|exact Hpre]. }
        assert (v = b1) as -> by (eapply mp_read_x; [exact Hlogs|exact Hlb|done]).
        reflexivity.
Qed.

Theorem mp_reader_fence_only_forbidden c h0 regs1 ws1 :
  reach mpg_c0 c →
  c_harts c = [h0; Hart [] regs1 ws1] →
  regs1 !! rg1 = Some b1 →
  regs1 !! rg2 ≠ Some b0.
Proof.
  intros Hre Hh H1 H2.
  assert (Hinv : mpg_inv c).
  { eapply inv_reach; [|  |exact Hre].
    - split; [done|]. eexists _, _. split; [reflexivity|]. simpl.
      split; [by left|split; [done|by left]].
    - intros. by eapply mpg_step. }
  destruct Hinv as (_ & g0 & g1 & Hh' & _ & _ & HR).
  rewrite Hh in Hh'. simplify_eq/=.
  destruct HR as [Hc|[[Hc _]|[[Hc _]|[_ Himp]]]]; try discriminate.
  pose proof (Himp H1) as H3. apply b0_ne_b1. congruence.
Qed.

(* ------------------------------------------------------------------ *)
(** *** CoRR — read-read coherence.  Seeing x = 2 then x = 1 is FORBIDDEN
        (herd: forbidden; this is RVWMO's load-value/coherence axiom). *)

Local Notation CX1 := (WMsg ax [b1] (Some 0%nat)).
Local Notation CX2 := (WMsg ax [b2] (Some 0%nat)).
Local Notation CORR_W0 := ([IStore ax b1; IStore ax b2]).
Local Notation CORR_W1 := ([IStore ax b2]).
Local Notation CORR_R0 := ([ILoad rg1 ax false; ILoad rg2 ax false]).
Local Notation CORR_R1 := ([ILoad rg2 ax false]).

Definition corr_c0 : config :=
  Cfg img0 [] [Hart CORR_W0 ∅ ws_init; Hart CORR_R0 ∅ ws_init].

Lemma mb_CX1 : msg_byte CX1 ax = Some b1.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_CX2 : msg_byte CX2 ax = Some b2.
Proof. rewrite msg_byte_single //. Qed.

Definition corr_logs (log : list wmsg) : Prop :=
  log = [] ∨ log = [CX1] ∨ log = [CX1; CX2].

(** x = 2 can only come from the SECOND store, at timestamp 2 — and the first
    store then sits strictly below it, which is what pins coherence. *)
Lemma corr_read_b2 log t :
  corr_logs log → log_byte img0 log t ax = Some b2 →
  t = 2%nat ∧ writes_in log ax 1 2.
Proof.
  intros [-> | [-> | ->]] Hlb.
  - apply log_byte_cases0 in Hlb as [_ Hi]. rewrite img0_x in Hi.
    destruct b0_ne_b2. congruence.
  - apply log_byte_cases1 in Hlb as [[_ Hi]|[_ Hm]].
    + rewrite img0_x in Hi. destruct b0_ne_b2. congruence.
    + rewrite mb_CX1 in Hm. destruct b1_ne_b2. congruence.
  - apply log_byte_cases2 in Hlb as [[_ Hi]|[[_ Hm]|[Ht _]]].
    + rewrite img0_x in Hi. destruct b0_ne_b2. congruence.
    + rewrite mb_CX1 in Hm. destruct b1_ne_b2. congruence.
    + split; [done|]. apply writes_in_compute. vm_compute. reflexivity.
Qed.

(** x = 1 can only come from the FIRST store, at timestamp 1. *)
Lemma corr_read_b1 log t :
  corr_logs log → log_byte img0 log t ax = Some b1 → t = 1%nat.
Proof.
  intros [-> | [-> | ->]] Hlb.
  - apply log_byte_cases0 in Hlb as [_ Hi]. by destruct (img0_x_nb1 Hi).
  - apply log_byte_cases1 in Hlb as [[_ Hi]|[Ht _]]; [|done].
    by destruct (img0_x_nb1 Hi).
  - apply log_byte_cases2 in Hlb as [[_ Hi]|[[Ht _]|[_ Hm]]]; [| done |].
    + by destruct (img0_x_nb1 Hi).
    + rewrite mb_CX2 in Hm. destruct b1_ne_b2. congruence.
Qed.

Definition corr_W (p : list instr) (log : list wmsg) : Prop :=
  (p = CORR_W0 ∧ log = []) ∨ (p = CORR_W1 ∧ log = [CX1]) ∨
  (p = [] ∧ log = [CX1; CX2]).

Definition corr_R (p : list instr) (regs : gmap nat (bv 8)) (ws : wstate)
    (log : list wmsg) : Prop :=
  (p = CORR_R0) ∨
  (p = CORR_R1 ∧ (regs !! rg1 = Some b2 → writes_in log ax 1 (coh ws ax))) ∨
  (p = [] ∧ (regs !! rg1 = Some b2 → regs !! rg2 ≠ Some b1)).

Definition corr_inv (c : config) : Prop :=
  c_img c = img0 ∧
  ∃ h0 h1, c_harts c = [h0; h1] ∧
    corr_W (h_prog h0) (c_log c) ∧
    corr_R (h_prog h1) (h_regs h1) (h_ws h1) (c_log c).

Lemma corr_W_logs p log : corr_W p log → corr_logs log.
Proof. rewrite /corr_logs. intros [[_ ->]|[[_ ->]|[_ ->]]]; auto. Qed.

Lemma corr_R_app p regs ws log l :
  corr_R p regs ws log → corr_R p regs ws (log ++ l).
Proof.
  intros [->|[[-> H]|[-> H]]].
  - by left.
  - right; left. split; [done|]. intros ?. by apply writes_in_app, H.
  - right; right. by split.
Qed.

Lemma corr_step c c' : corr_inv c → lstep c c' → corr_inv c'.
Proof.
  intros (Himg & [p0 regs0 ws0] & [p1 regs1 ws1] & Hh & HW & HR) Hstep.
  simpl in HW, HR.
  pose proof (corr_W_logs _ _ HW) as Hlogs.
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|[|i]]; simpl in Hlk; simplify_eq/=.
  - destruct HW as [[-> Hl]|[[-> Hl]|[-> Hl]]]; simpl in Hst; [| |done].
    + destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * right; left. split; [reflexivity|]. rewrite Hlog Hl //.
      * rewrite Hlog. by apply corr_R_app.
    + destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * right; right. split; [reflexivity|]. rewrite Hlog Hl //.
      * rewrite Hlog. by apply corr_R_app.
  - destruct HR as [->|[[-> HRc]|[-> HRc]]]; simpl in Hst; [| |done].
    + (* first load *)
      destruct Hst as (t & v & Hlb & Hrd & Hlog & Hharts).
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * rewrite Hlog. exact HW.
      * right; left. split; [reflexivity|]. rewrite lookup_insert.
        intros Hv. assert (v = b2) as -> by congruence.
        rewrite Himg in Hlb.
        apply (corr_read_b2 _ _ Hlogs) in Hlb as [-> Hw].
        rewrite Hlog. eapply writes_in_mono_hi; [|exact Hw].
        apply load_post_coh.
    + (* second load: coherence forbids going back to timestamp 1 *)
      destruct Hst as (t & v & Hlb & Hrd & Hlog & Hharts).
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. split.
      * rewrite Hlog. exact HW.
      * right; right. split; [reflexivity|].
        rewrite lookup_insert_ne // lookup_insert. intros H1 H2.
        assert (v = b1) as -> by congruence.
        rewrite Himg in Hlb.
        apply (corr_read_b1 _ _ Hlogs) in Hlb as ->.
        destruct Hrd as [_ Hn]. apply Hn.
        eapply writes_in_mono_hi; [|by apply HRc]. lia.
Qed.

Theorem corr_forbidden c h0 regs1 ws1 :
  reach corr_c0 c →
  c_harts c = [h0; Hart [] regs1 ws1] →
  regs1 !! rg1 = Some b2 →
  regs1 !! rg2 ≠ Some b1.
Proof.
  intros Hre Hh H1.
  assert (Hinv : corr_inv c).
  { eapply inv_reach; [|  |exact Hre].
    - split; [done|]. eexists _, _. split; [reflexivity|]. simpl.
      split; by left.
    - intros. by eapply corr_step. }
  destruct Hinv as (_ & g0 & g1 & Hh' & _ & HR).
  rewrite Hh in Hh'. simplify_eq/=.
  destruct HR as [Hc|[[Hc _]|[_ Himp]]]; try discriminate.
  by apply Himp.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Generic list/read helpers used by LB and IRIW *)

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

(** A read that is not the era-initial image is a read of some logged write. *)
Lemma writes_in_read img log a t v :
  log_byte img log t a = Some v → t ≠ 0%nat →
  writes_in log a 0 (length log).
Proof.
  intros Hlb Hne. apply (writes_in_log_byte img). exists t.
  split_and!; [lia| |by eexists].
  apply (log_byte_bounded img log t a). by eexists.
Qed.

Lemma read_x_b1_ne0 log t : log_byte img0 log t ax = Some b1 → t ≠ 0%nat.
Proof. intros Hlb ->. rewrite log_byte_0 in Hlb. by destruct (img0_x_nb1 Hlb). Qed.
Lemma read_y_b1_ne0 log t : log_byte img0 log t ay = Some b1 → t ≠ 0%nat.
Proof. intros Hlb ->. rewrite log_byte_0 in Hlb. by destruct (img0_y_nb1 Hlb). Qed.

(* ------------------------------------------------------------------ *)
(** *** LB — load buffering.  Both loads returning 1 is FORBIDDEN here.

    RVWMO **ALLOWS** this outcome (it is exactly the [po ∪ rf] cycle a
    promising machine produces by certifying a store early).  This machine is
    promise-free, so a store cannot enter the log before the po-earlier load
    resolves, and the outcome is unreachable.  GAP WITNESS #1: the documented
    LB gap of [design/weak-memory.md] Decision 1, retired by the M6 robustness
    theorem.  The proof below is the honest statement of that gap. *)

Local Notation LY := (WMsg ay [b1] (Some 0%nat)).   (* hart 0 stores y *)
Local Notation LX := (WMsg ax [b1] (Some 1%nat)).   (* hart 1 stores x *)
Local Notation LB_P0 := ([ILoad rg1 ax false; IStore ay b1]).
Local Notation LB_P1 := ([IStore ay b1]).
Local Notation LB_Q0 := ([ILoad rg2 ay false; IStore ax b1]).
Local Notation LB_Q1 := ([IStore ax b1]).

Definition lb_c0 : config :=
  Cfg img0 [] [Hart LB_P0 ∅ ws_init; Hart LB_Q0 ∅ ws_init].

Lemma mb_LX_x : msg_byte LX ax = Some b1.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_LX_y : msg_byte LX ay = None.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_LY_x : msg_byte LY ax = None.
Proof. rewrite msg_byte_single //. Qed.
Lemma mb_LY_y : msg_byte LY ay = Some b1.
Proof. rewrite msg_byte_single //. Qed.
Lemma LX_ne_LY : LX ≠ LY.
Proof. intros H. congruence. Qed.

Definition lb_content (log : list wmsg) : Prop :=
  ∀ m, m ∈ log → m = LX ∨ m = LY.

Definition lb_H0 (p : list instr) (regs : gmap nat (bv 8)) (log : list wmsg)
    : Prop :=
  (p = LB_P0 ∧ LY ∉ log) ∨
  (p = LB_P1 ∧ LY ∉ log ∧
     (regs !! rg1 = Some b1 → writes_in log ax 0 (length log))) ∨
  (p = [] ∧ (regs !! rg1 = Some b1 → writes_in log ax 0 (length log))).

Definition lb_H1 (p : list instr) (regs : gmap nat (bv 8)) (log : list wmsg)
    : Prop :=
  (p = LB_Q0 ∧ LX ∉ log) ∨
  (p = LB_Q1 ∧ LX ∉ log ∧
     (regs !! rg2 = Some b1 → writes_in log ay 0 (length log))) ∨
  (p = [] ∧ (regs !! rg2 = Some b1 → writes_in log ay 0 (length log))).

Definition lb_inv (c : config) : Prop :=
  c_img c = img0 ∧
  ∃ h0 h1, c_harts c = [h0; h1] ∧
    lb_content (c_log c) ∧
    lb_H0 (h_prog h0) (h_regs h0) (c_log c) ∧
    lb_H1 (h_prog h1) (h_regs h1) (c_log c) ∧
    (∀ j, c_log c !! j = Some LY → h_regs h0 !! rg1 = Some b1 →
          writes_in (c_log c) ax 0 j) ∧
    (∀ j, c_log c !! j = Some LX → h_regs h1 !! rg2 = Some b1 →
          writes_in (c_log c) ay 0 j).

Lemma lb_content_app log m :
  lb_content log → (m = LX ∨ m = LY) → lb_content (log ++ [m]).
Proof.
  intros Hc Hm m' Hin. apply elem_of_app in Hin as [Hin|Hin]; [by apply Hc|].
  apply elem_of_list_singleton in Hin as ->. done.
Qed.

Lemma notin_app (P m : wmsg) log : P ∉ log → P ≠ m → P ∉ log ++ [m].
Proof.
  intros Hn Hne Hin. apply elem_of_app in Hin as [Hin|Hin]; [done|].
  apply elem_of_list_singleton in Hin. done.
Qed.

Lemma lb_H0_app p regs log m :
  LY ≠ m → lb_H0 p regs log → lb_H0 p regs (log ++ [m]).
Proof.
  intros Hne [[-> Hn]|[[-> [Hn H]]|[-> H]]].
  - left. split; [done|]. by apply notin_app.
  - right; left. split; [done|]. split; [by apply notin_app|].
    intros Hr. eapply writes_in_mono_hi; [|by apply writes_in_app, H].
    rewrite length_app /=. lia.
  - right; right. split; [done|].
    intros Hr. eapply writes_in_mono_hi; [|by apply writes_in_app, H].
    rewrite length_app /=. lia.
Qed.

Lemma lb_H1_app p regs log m :
  LX ≠ m → lb_H1 p regs log → lb_H1 p regs (log ++ [m]).
Proof.
  intros Hne [[-> Hn]|[[-> [Hn H]]|[-> H]]].
  - left. split; [done|]. by apply notin_app.
  - right; left. split; [done|]. split; [by apply notin_app|].
    intros Hr. eapply writes_in_mono_hi; [|by apply writes_in_app, H].
    rewrite length_app /=. lia.
  - right; right. split; [done|].
    intros Hr. eapply writes_in_mono_hi; [|by apply writes_in_app, H].
    rewrite length_app /=. lia.
Qed.

(** The descent that closes LB: an x-message must be preceded by a y-message,
    which must be preceded by an x-message, ... — impossible in a finite log
    that grows only at its end. *)
Lemma lb_descend log :
  lb_content log →
  (∀ j, log !! j = Some LY → writes_in log ax 0 j) →
  (∀ j, log !! j = Some LX → writes_in log ay 0 j) →
  ∀ j, log !! j = Some LX → False.
Proof.
  intros Hcont HY HX.
  assert (H : ∀ n j, (j ≤ n)%nat → log !! j = Some LX → False).
  { induction n as [|n IH]; intros j Hj Hlk.
    - apply HX in Hlk as (t & Ht0 & Htj & m & Hm & Hs). lia.
    - apply HX in Hlk as (t & Ht0 & Htj & m & Hm & Hs).
      assert (m = LY) as ->.
      { destruct (Hcont m (elem_of_list_lookup_2 _ _ _ Hm)) as [-> | ->];
          [|done]. rewrite mb_LX_y in Hs. by destruct Hs. }
      apply HY in Hm as (t' & Ht'0 & Ht'j & m' & Hm' & Hs').
      assert (m' = LX) as ->.
      { destruct (Hcont m' (elem_of_list_lookup_2 _ _ _ Hm')) as [-> | ->];
          [done|]. rewrite mb_LY_x in Hs'. by destruct Hs'. }
      eapply (IH (t' - 1)%nat); [lia|exact Hm']. }
  intros j. by apply (H j j).
Qed.

Lemma lb_step c c' : lb_inv c → lstep c c' → lb_inv c'.
Proof.
  intros (Himg & [p0 regs0 ws0] & [p1 regs1 ws1] & Hh & Hcont & H0 & H1 & J0 & J1)
         Hstep.
  simpl in H0, H1, J0, J1.
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|[|i]]; simpl in Hlk; simplify_eq/=.
  - (* ---- hart 0 ---- *)
    destruct H0 as [[-> Hn]|[[-> [Hn Hw]]|[-> Hw]]]; simpl in Hst; [| |done].
    + (* load rg1 <- x *)
      destruct Hst as (t & v & Hlb & Hrd & Hlog & Hharts).
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog. split_and!.
      * exact Hcont.
      * right; left. split; [reflexivity|]. split; [exact Hn|].
        rewrite lookup_insert. intros Hv.
        assert (v = b1) as -> by congruence. rewrite Himg in Hlb.
        eapply writes_in_read; [exact Hlb|by eapply read_x_b1_ne0].
      * exact H1.
      * intros j Hj _. destruct Hn. by eapply elem_of_list_lookup_2.
      * exact J1.
    + (* store y *)
      destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog. split_and!.
      * apply lb_content_app; [exact Hcont|by right].
      * right; right. split; [reflexivity|].
        intros Hr. eapply writes_in_mono_hi; [|by apply writes_in_app, Hw].
        rewrite length_app /=. lia.
      * apply lb_H1_app; [apply LX_ne_LY|exact H1].
      * intros j Hj Hr. apply lookup_app_last in Hj as [[Hlt Hj]|[-> _]].
        { destruct Hn. by eapply elem_of_list_lookup_2. }
        by apply writes_in_app, Hw.
      * intros j Hj Hr. apply lookup_app_last in Hj as [[Hlt Hj]|[_ Hc]].
        { by apply writes_in_app, J1. }
        by destruct (LX_ne_LY Hc).
  - (* ---- hart 1 ---- *)
    destruct H1 as [[-> Hn]|[[-> [Hn Hw]]|[-> Hw]]]; simpl in Hst; [| |done].
    + (* load rg2 <- y *)
      destruct Hst as (t & v & Hlb & Hrd & Hlog & Hharts).
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog. split_and!.
      * exact Hcont.
      * exact H0.
      * right; left. split; [reflexivity|]. split; [exact Hn|].
        rewrite lookup_insert. intros Hv.
        assert (v = b1) as -> by congruence. rewrite Himg in Hlb.
        eapply writes_in_read; [exact Hlb|by eapply read_y_b1_ne0].
      * exact J0.
      * intros j Hj _. destruct Hn. by eapply elem_of_list_lookup_2.
    + (* store x *)
      destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl.
      rewrite Hlog. split_and!.
      * apply lb_content_app; [exact Hcont|by left].
      * apply lb_H0_app; [intros Hc; by destruct (LX_ne_LY (eq_sym Hc))|exact H0].
      * right; right. split; [reflexivity|].
        intros Hr. eapply writes_in_mono_hi; [|by apply writes_in_app, Hw].
        rewrite length_app /=. lia.
      * intros j Hj Hr. apply lookup_app_last in Hj as [[Hlt Hj]|[_ Hc]].
        { by apply writes_in_app, J0. }
        by destruct (LX_ne_LY (eq_sym Hc)).
      * intros j Hj Hr. apply lookup_app_last in Hj as [[Hlt Hj]|[-> _]].
        { destruct Hn. by eapply elem_of_list_lookup_2. }
        by apply writes_in_app, Hw.
Qed.

Theorem lb_forbidden c regs0 ws0 regs1 ws1 :
  reach lb_c0 c →
  c_harts c = [Hart [] regs0 ws0; Hart [] regs1 ws1] →
  regs0 !! rg1 = Some b1 →
  regs1 !! rg2 ≠ Some b1.
Proof.
  intros Hre Hh Hr0 Hr1.
  assert (Hinv : lb_inv c).
  { eapply inv_reach; [|  |exact Hre].
    - split; [done|]. eexists _, _. split; [reflexivity|]. simpl.
      split_and!.
      + by intros ? ?%elem_of_nil.
      + left. split; [reflexivity|]. apply not_elem_of_nil.
      + left. split; [reflexivity|]. apply not_elem_of_nil.
      + intros j Hj. rewrite lookup_nil in Hj. discriminate.
      + intros j Hj. rewrite lookup_nil in Hj. discriminate.
    - intros. by eapply lb_step. }
  destruct Hinv as (_ & g0 & g1 & Hh' & Hcont & H0 & H1 & J0 & J1).
  rewrite Hh in Hh'. simplify_eq/=.
  destruct H0 as [[Hc _]|[[Hc _]|[_ Hw]]]; try discriminate.
  specialize (Hw Hr0) as (t & Ht0 & Htl & m & Hm & Hs).
  assert (m = LX) as ->.
  { destruct (Hcont m (elem_of_list_lookup_2 _ _ _ Hm)) as [-> | ->]; [done|].
    rewrite mb_LY_x in Hs. by destruct Hs. }
  eapply (lb_descend (c_log c) Hcont); [| |exact Hm].
  - intros j Hj. by apply J0.
  - intros j Hj. by apply J1.
Qed.

(* ------------------------------------------------------------------ *)
(** *** IRIW with both readers fenced — FORBIDDEN (herd: forbidden).

    RVWMO is multi-copy atomic, so two readers cannot observe the two
    independent stores in opposite orders once each pair of loads is separated
    by [fence rw,rw].  Here that falls out of the single global log: "x entered
    the log before y" and "y entered before x" cannot both hold. *)

Local Notation IX := (WMsg ax [b1] (Some 0%nat)).
Local Notation IY := (WMsg ay [b1] (Some 1%nat)).

Definition iriw_c0 : config :=
  Cfg img0 []
      [Hart [IStore ax b1] ∅ ws_init;
       Hart [IStore ay b1] ∅ ws_init;
       Hart [ILoad rg1 ax false; FENCE_RW_RW; ILoad rg2 ay false] ∅ ws_init;
       Hart [ILoad rg1 ay false; FENCE_RW_RW; ILoad rg2 ax false] ∅ ws_init].

(** "[a] was written into the global order strictly before [b] was" — stated
    as a view [v] that already covers a write to [a] and no write to [b].  The
    [v ≤ length log] clause is what makes it stable under later appends. *)
Definition wfirst (log : list wmsg) (a b : Z) : Prop :=
  ∃ v, (v ≤ length log)%nat ∧ writes_in log a 0 v ∧ ¬ writes_in log b 0 v.

Lemma wfirst_app log l a b : wfirst log a b → wfirst (log ++ l) a b.
Proof.
  intros (v & Hv & Hw & Hn). exists v. split_and!.
  - rewrite length_app. lia.
  - by apply writes_in_app.
  - intros Hc. apply Hn. exact (writes_in_app_inv log l b 0 v Hv Hc).
Qed.

Lemma wfirst_absurd log a b : wfirst log a b → wfirst log b a → False.
Proof.
  intros (v & _ & (t & Ht0 & Htv & mt & Hmt & Hst) & Hnb)
         (w & _ & (u & Hu0 & Huw & mu & Hmu & Hsu) & Hna).
  assert (v < u)%nat.
  { destruct (decide (u ≤ v)%nat) as [Hle|?]; [|lia].
    destruct Hnb. exists u. split_and!; [lia|lia|]. exists mu. by split. }
  assert (w < t)%nat.
  { destruct (decide (t ≤ w)%nat) as [Hle|?]; [|lia].
    destruct Hna. exists t. split_and!; [lia|lia|]. exists mt. by split. }
  lia.
Qed.

Lemma msg_ne_b0 (m : wmsg) a : (m = IX ∨ m = IY) → msg_byte m a ≠ Some b0.
Proof.
  intros Hm H.
  assert (Hc : msg_byte m a = None ∨ msg_byte m a = Some b1).
  { destruct Hm as [-> | ->]; rewrite msg_byte_single;
      destruct (bool_decide _); auto. }
  destruct Hc as [Hc|Hc]; rewrite Hc in H; [done|].
  apply b0_ne_b1. congruence.
Qed.

Definition iriw_content (log : list wmsg) : Prop :=
  ∀ m, m ∈ log → m = IX ∨ m = IY.

(** Reading 0 means reading the era-initial image: nothing ever writes 0. *)
Lemma iriw_read_b0 log t a :
  iriw_content log → log_byte img0 log t a = Some b0 → t = 0%nat.
Proof.
  intros Hc Hlb. destruct t as [|i]; [done|]. exfalso.
  rewrite log_byte_S in Hlb.
  destruct (log !! i) as [m|] eqn:Hm; simpl in Hlb; [|done].
  eapply msg_ne_b0; [by apply Hc, (elem_of_list_lookup_2 _ _ _ Hm)|exact Hlb].
Qed.

Lemma writes_in_read_at img log a t v :
  log_byte img log t a = Some v → t ≠ 0%nat → writes_in log a 0 t.
Proof.
  intros Hlb Hne. apply (writes_in_log_byte img). exists t.
  split_and!; [lia|lia|by eexists].
Qed.

(** One reader: loads [a], fences rw,rw, loads [b].  The [w_fwd] conjunct is
    the forward-bank one — see [mpf_R]: a reader that never stores keeps an
    empty bank, which is what makes its load's post-view cover the timestamp
    it read. *)
Definition iriw_R (a b : Z) (p : list instr) (regs : gmap nat (bv 8))
    (ws : wstate) (log : list wmsg) : Prop :=
  w_fwd ws = ∅ ∧
  ((p = [ILoad rg1 a false; FENCE_RW_RW; ILoad rg2 b false]) ∨
   (p = [FENCE_RW_RW; ILoad rg2 b false] ∧
      (regs !! rg1 = Some b1 → writes_in log a 0 (w_vrOld ws))) ∨
   (p = [ILoad rg2 b false] ∧
      (regs !! rg1 = Some b1 → writes_in log a 0 (w_vrNew ws))) ∨
   (p = [] ∧ (regs !! rg1 = Some b1 → regs !! rg2 = Some b0 → wfirst log a b))).

Lemma iriw_R_app a b p regs ws log l :
  iriw_R a b p regs ws log → iriw_R a b p regs ws (log ++ l).
Proof.
  intros [Hf HR]. split; [exact Hf|]. destruct HR as [->|[[-> H]|[[-> H]|[-> H]]]].
  - by left.
  - right; left. split; [done|]. intros ?. by apply writes_in_app, H.
  - right; right; left. split; [done|]. intros ?. by apply writes_in_app, H.
  - right; right; right. split; [done|]. intros ??. by apply wfirst_app, H.
Qed.

Definition iriw_inv (c : config) : Prop :=
  c_img c = img0 ∧
  ∃ h0 h1 h2 h3, c_harts c = [h0; h1; h2; h3] ∧
    iriw_content (c_log c) ∧
    (h_prog h0 = [IStore ax b1] ∨ h_prog h0 = []) ∧
    (h_prog h1 = [IStore ay b1] ∨ h_prog h1 = []) ∧
    iriw_R ax ay (h_prog h2) (h_regs h2) (h_ws h2) (c_log c) ∧
    iriw_R ay ax (h_prog h3) (h_regs h3) (h_ws h3) (c_log c).

Lemma iriw_content_app log m :
  iriw_content log → (m = IX ∨ m = IY) → iriw_content (log ++ [m]).
Proof.
  intros Hc Hm m' Hin. apply elem_of_app in Hin as [Hin|Hin]; [by apply Hc|].
  apply elem_of_list_singleton in Hin as ->. done.
Qed.

Lemma iriw_step c c' : iriw_inv c → lstep c c' → iriw_inv c'.
Proof.
  intros (Himg & [q0 g0 v0] & [q1 g1 v1] & [q2 g2 v2] & [q3 g3 v3]
          & Hh & Hcont & H0 & H1 & H2 & H3) Hstep.
  simpl in H0, H1, H2, H3.
  destruct Hstep as (i & h & Hlk & Himg' & Hst).
  rewrite Hh in Hlk.
  destruct i as [|[|[|[|i]]]]; simpl in Hlk; simplify_eq/=.
  - (* hart 0: store x *)
    destruct H0 as [->| ->]; simpl in Hst; [|done].
    destruct Hst as [Hlog Hharts].
    split; [rewrite Himg' //|]. eexists _, _, _, _.
    split; [rewrite Hharts Hh /=; reflexivity|]. simpl. rewrite Hlog. split_and!.
    + apply iriw_content_app; [exact Hcont|by left].
    + by right.
    + exact H1.
    + by apply iriw_R_app.
    + by apply iriw_R_app.
  - (* hart 1: store y *)
    destruct H1 as [->| ->]; simpl in Hst; [|done].
    destruct Hst as [Hlog Hharts].
    split; [rewrite Himg' //|]. eexists _, _, _, _.
    split; [rewrite Hharts Hh /=; reflexivity|]. simpl. rewrite Hlog. split_and!.
    + apply iriw_content_app; [exact Hcont|by right].
    + exact H0.
    + by right.
    + by apply iriw_R_app.
    + by apply iriw_R_app.
  - (* hart 2: loads x then y *)
    destruct H2 as [Hfwd H2].
    destruct H2 as [->|[[-> Hc]|[[-> Hc]|[-> Hc]]]]; simpl in Hst; [| | |done].
    + destruct Hst as (t & v & Hlb & Hrd & Hlog & Hharts).
      split; [rewrite Himg' //|]. eexists _, _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. rewrite Hlog.
      split_and!; [exact Hcont|exact H0|exact H1| |exact H3].
      split; [rewrite load_post_fwd; exact Hfwd|].
      right; left. split; [reflexivity|]. rewrite lookup_insert.
      intros Hv. assert (v = b1) as -> by congruence. rewrite Himg in Hlb.
      eapply writes_in_mono_hi;
        [apply load_post_vrOld_nofwd; exact Hfwd|].
      eapply writes_in_read_at; [exact Hlb|by eapply read_x_b1_ne0].
    + destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. rewrite Hlog.
      split_and!; [exact Hcont|exact H0|exact H1| |exact H3].
      split; [rewrite fence_post_fwd; exact Hfwd|].
      right; right; left. split; [reflexivity|]. intros Hv.
      eapply writes_in_mono_hi; [apply fence_post_vrNew_r|by apply Hc].
    + destruct Hst as (t & v & Hlb & Hrd & Hlog & Hharts).
      split; [rewrite Himg' //|]. eexists _, _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. rewrite Hlog.
      split_and!; [exact Hcont|exact H0|exact H1| |exact H3].
      split; [rewrite load_post_fwd; exact Hfwd|].
      right; right; right. split; [reflexivity|].
      rewrite lookup_insert_ne // lookup_insert. intros Hv1 Hv2.
      assert (v = b0) as -> by congruence. rewrite Himg in Hlb.
      apply (iriw_read_b0 _ _ _ Hcont) in Hlb as ->.
      destruct Hrd as [_ Hn].
      exists (Nat.min (load_vpre v2 false) (length (c_log c))). split_and!.
      * lia.
      * apply writes_in_clip.
        eapply writes_in_mono_hi; [apply load_vpre_vrNew|by apply Hc].
      * intros Hw. apply Hn. eapply writes_in_mono_hi; [|exact Hw]. lia.
  - (* hart 3: loads y then x *)
    destruct H3 as [Hfwd H3].
    destruct H3 as [->|[[-> Hc]|[[-> Hc]|[-> Hc]]]]; simpl in Hst; [| | |done].
    + destruct Hst as (t & v & Hlb & Hrd & Hlog & Hharts).
      split; [rewrite Himg' //|]. eexists _, _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. rewrite Hlog.
      split_and!; [exact Hcont|exact H0|exact H1|exact H2|].
      split; [rewrite load_post_fwd; exact Hfwd|].
      right; left. split; [reflexivity|]. rewrite lookup_insert.
      intros Hv. assert (v = b1) as -> by congruence. rewrite Himg in Hlb.
      eapply writes_in_mono_hi;
        [apply load_post_vrOld_nofwd; exact Hfwd|].
      eapply writes_in_read_at; [exact Hlb|by eapply read_y_b1_ne0].
    + destruct Hst as [Hlog Hharts].
      split; [rewrite Himg' //|]. eexists _, _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. rewrite Hlog.
      split_and!; [exact Hcont|exact H0|exact H1|exact H2|].
      split; [rewrite fence_post_fwd; exact Hfwd|].
      right; right; left. split; [reflexivity|]. intros Hv.
      eapply writes_in_mono_hi; [apply fence_post_vrNew_r|by apply Hc].
    + destruct Hst as (t & v & Hlb & Hrd & Hlog & Hharts).
      split; [rewrite Himg' //|]. eexists _, _, _, _.
      split; [rewrite Hharts Hh /=; reflexivity|]. simpl. rewrite Hlog.
      split_and!; [exact Hcont|exact H0|exact H1|exact H2|].
      split; [rewrite load_post_fwd; exact Hfwd|].
      right; right; right. split; [reflexivity|].
      rewrite lookup_insert_ne // lookup_insert. intros Hv1 Hv2.
      assert (v = b0) as -> by congruence. rewrite Himg in Hlb.
      apply (iriw_read_b0 _ _ _ Hcont) in Hlb as ->.
      destruct Hrd as [_ Hn].
      exists (Nat.min (load_vpre v3 false) (length (c_log c))). split_and!.
      * lia.
      * apply writes_in_clip.
        eapply writes_in_mono_hi; [apply load_vpre_vrNew|by apply Hc].
      * intros Hw. apply Hn. eapply writes_in_mono_hi; [|exact Hw]. lia.
Qed.

Theorem iriw_forbidden c h0 h1 regs2 ws2 regs3 ws3 :
  reach iriw_c0 c →
  c_harts c = [h0; h1; Hart [] regs2 ws2; Hart [] regs3 ws3] →
  regs2 !! rg1 = Some b1 → regs2 !! rg2 = Some b0 →
  regs3 !! rg1 = Some b1 → regs3 !! rg2 ≠ Some b0.
Proof.
  intros Hre Hh Ha1 Ha2 Hb1 Hb2.
  assert (Hinv : iriw_inv c).
  { eapply inv_reach; [|  |exact Hre].
    - split; [done|]. eexists _, _, _, _. split; [reflexivity|]. simpl.
      split_and!; [by intros ? ?%elem_of_nil|by left|by left
                  |split; [done|by left]|split; [done|by left]].
    - intros. by eapply iriw_step. }
  destruct Hinv as (_ & g0 & g1 & g2 & g3 & Hh' & _ & _ & _ & H2 & H3).
  rewrite Hh in Hh'. simplify_eq/=.
  destruct H2 as [_ H2]. destruct H3 as [_ H3].
  destruct H2 as [Hc|[[Hc _]|[[Hc _]|[_ Himp2]]]]; try discriminate.
  destruct H3 as [Hc|[[Hc _]|[[Hc _]|[_ Himp3]]]]; try discriminate.
  eapply wfirst_absurd; [by apply Himp2|by apply Himp3].
Qed.

(* ------------------------------------------------------------------ *)
(** *** amoswap.w.aq — the read half is forced to the globally-latest write.

    This exercises the [IAmoSwapAq] arm of [lstep].  [amo_latest_unique] says
    the atomicity constraint pins the timestamp; [amo_not_stale] is the
    concrete consequence the kernel's [acquire] depends on — once another
    hart's store to the lock word is in the log, the AMO cannot read the
    era-initial value. *)

Lemma step_amo c i r a v rest regs ws t vv :
  c_harts c !! i = Some (Hart (IAmoSwapAq r a v :: rest) regs ws) →
  log_byte (c_img c) (c_log c) t a = Some vv →
  ¬ writes_in (c_log c) a t (length (c_log c)) →
  readable (c_img c) (c_log c) ws (load_vpre ws true) a t →
  lstep c (Cfg (c_img c) (c_log c ++ [WMsg a [v] (Some i)])
               (<[i := Hart rest (<[r := vv]> regs)
                     (store_post (load_post ws true a t) false a
                                 (S (length (c_log c))))]> (c_harts c))).
Proof.
  intros Hlk Hv Hat Hr. exists i, (Hart (IAmoSwapAq r a v :: rest) regs ws).
  split_and!; [done|done|]. simpl. exists t, vv. by split_and!.
Qed.

Lemma amo_not_stale (m : wmsg) (t : nat) :
  is_Some (msg_byte m ax) → ¬ writes_in [m] ax t 1 → t ≠ 0%nat.
Proof.
  intros Hm Hn ->. apply Hn. exists 1%nat. split_and!; [lia|lia|].
  exists m. by split.
Qed.

Definition amo_c0 : config :=
  Cfg img0 [] [Hart [IStore ax b1] ∅ ws_init;
               Hart [IAmoSwapAq rg1 ax b2] ∅ ws_init].

Lemma amo_swap_reachable :
  ∃ c, reach amo_c0 c ∧
       ∃ regs ws, c_harts c !! 1 = Some (Hart [] regs ws) ∧
                  regs !! rg1 = Some b1.
Proof.
  rewrite /amo_c0. eexists. split.
  { eapply rtc_l; [eapply (step_store _ 0); reflexivity|]. simpl.
    eapply rtc_l; [eapply (step_amo _ 1 rg1 ax b2 _ _ _ 1 b1);
                   [reflexivity
                   |rewrite log_byte_1 msg_byte_single; vm_compute; reflexivity
                   |solve_nw
                   |split; [solve_is_Some|solve_nw]]|].
    simpl. apply rtc_refl. }
  do 2 eexists. split; [reflexivity|]. rewrite lookup_insert //.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The FORWARD BANK, in action.

    No litmus program above reads back its own store, so the M1 wire-in of
    [w_fwd] into the load view ([WeakMem.fwd_view], design doc Decision 3) is
    invisible to every verdict — which is exactly why it needs its own
    witness here, or the wire-in could be vacuous and nobody would notice.

    A hart that stores x = 1 and then loads x back reads its OWN message
    (timestamp 1, which coherence pins), but its read view rises only to the
    view the store banked — [w_vwNew] at store time, i.e. 0 for a hart that
    has issued no fence.  Coherence still records the real timestamp. *)

Local Notation FWD_WS := (store_post ws_init false ax 1).

Lemma fwd_bank_after_store : w_fwd FWD_WS !! ax = Some (1%nat, 0%nat).
Proof. rewrite /store_post /= lookup_insert //. Qed.

(** The forwarded (relaxed) load: post-view 0, NOT the timestamp 1. *)
Lemma fwd_selfread_relaxed :
  w_vrOld (load_post FWD_WS false ax 1) = 0%nat.
Proof. vm_compute. reflexivity. Qed.

(** Coherence is unaffected — the read still cannot go back before its own
    store (this is what keeps CoRR-style verdicts intact). *)
Lemma fwd_selfread_coh : (1 ≤ coh (load_post FWD_WS false ax 1) ax)%nat.
Proof. apply load_post_coh. Qed.

(** An ACQUIRE load is never forwarded (Promising-ARM's [read_view] side
    condition): its post-view is the timestamp, so the kernel's
    [amoswap.w.aq] keeps its full ordering force even on its own lock word. *)
Lemma fwd_selfread_acquire :
  (1 ≤ w_vrOld (load_post FWD_WS true ax 1))%nat.
Proof. vm_compute. lia. Qed.
