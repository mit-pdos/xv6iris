(** * WeakRvwmoConfWit2.v — THE TWO-HART EMISSION WITNESS (route B)

    Design: [claude-notes/design/weak-memory-route-b.md] §4d.4.  The
    companion of [WeakRvwmoConfWit.v], which witnessed [hart_conf] at ONE
    nonempty row (the [sw &started] of [main]).  A single-hart witness
    cannot see the only thing the conformance bundle exists for: TWO harts
    whose rows are tied by a read-from edge.  Every [gdexec_qconf] on the
    tree so far has had at most one nonempty row, so the bundle's
    cross-hart content — a load's [ts] naming another hart's store, the
    graph consistency that makes it legal, and the interleaving that turns
    the two rows into one [exec_prog_ok'] supply — was untested.

    WHAT IS HERE.

    (1) §1 THE LOAD BLOCK.  Hart 1's spin load — [lw a5,0(a4)] at
        [main+0x16], the [while (__atomic_load_n(&started, …) == 0)] of
        xv6's [main], the READ side of the very handshake
        [WeakEvStarted] certifies from the write side.  Its residual monad
        is BUILT HERE, exactly the way [WeakEvStarted] §5 builds the
        store's: the cold-boot register file with [a4 = &started] and the
        PC at [main+0x16], two unevaluated silent stretches ([esil]) with
        the footprint COLLECTED (not guessed), and the load node's request
        read off by the total projection [eread_req_at] and inverted by
        [WeakEvLift.eread_req_at_inv].  Nothing about the load is
        hand-built: the width (4), the address ([&started] = 0x8000a230),
        and the access kind (plain — the acquire is the SEPARATE
        [fence r,rw] at [main+0x18]) are the real machine's.  The block is
        PARAMETRIC in the value read, because the node accepts any word.

    (2) §3 THE MESSAGE-PASSING GRAPH [mpw]: hart 0's row is
        [WeakRvwmoConfWit]'s store, hart 1's row is the load, and the
        load's per-byte [ts] names hart 0's store (write index 1).  It is
        [rvwmo_minus_deps_consistent] and — THE POINT — it is a
        [gdexec_qconf] bundle with BOTH rows nonempty: the first one on
        this tree.

    (3) §4 THE EARLY-READ VARIANT [mpw']: the same two rows with the load
        reading the ERA IMAGE ([ts = 0], the flag still clear) and gmo
        putting the load first.  Also consistent, also qconf — which is
        the honest statement that the emission constrains the VALUE not at
        all: the same monad node emits both.

    (4) §5 THE SUPPLY: [WeakRvwmoSupply.supply_of_qconf] at the two-event
        candidate, i.e. an [exec_prog_ok'] whose per-agent program states
        are the two REAL blocks.  The first genuinely two-hart supply
        witness on the tree.

    §6 records what a genuine [RacyD]-cycle (LB) witness would still cost. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakDeps.
Require Import WeakAxiomatic.
Require Import WeakAxiomatic2.
Require Import WeakRvwmoGraph.
Require Import WeakInterp.
Require Import WeakInterpProj.
Require Import RiscvLang.
Require Import WeakLang.
Require Import WeakLock.
Require Import ColdBoot.
Require Import Kernel.KernelSyms.
Require Import WeakEvLang.
Require Import WeakEvPf.
Require Import WeakPromise.
Require Import WeakPromiseFact.
Require Import WeakPromiseBridge.
Require Import WeakAxRealize.
Require Import WeakEvInst.
Require Import WeakRvwmoConf.
Require Import WeakRvwmoSupply.
Require Import WeakEvLift.
Require Import WeakEvStarted.
Require Import WeakRvwmoConfWit.

(* ====================================================================== *)
(** * 1. THE LOAD BLOCK — [lw a5,0(a4)] at [main+0x16]

    [kernel-rocq]'s image has [0x80000e94: lw a5,0(a4)] (encoding 0x431c,
    compressed) and [started = 0x8000a230].  The register file is
    [WeakEvStarted]'s: the tree's own cold-boot file, with the ADDRESS
    register [a4] set to [&started] and the PC at the load.  (The store
    witness sets [a5]/[a4] instead — the two instructions use the opposite
    registers.) *)

Definition ld_pc : SailStdpp.Values.mword 64 :=
  SailStdpp.Values.mword_of_int (KernelSyms.main + 0x16).
Definition ld_word : Z := 0x431c.
Definition ld_wf : bv 16 := Z_to_bv 16 ld_word.

Definition ld_rs0 : regstate :=
  register_set (R_bitvector_64 nextPC) ld_pc
    (register_set (R_bitvector_64 PC) ld_pc
      (register_set (R_bitvector_64 x14) ev_flag
        (ColdBoot.cold_regs (SailStdpp.Values.mword_of_int 0)))).

(** THE FOOTPRINT, collected (a small readback: a list of register names). *)
Definition ld_c1 : regstate * M unit := erun_any 400 ld_rs0 (riscv_step false).
Definition ld_Dl : list register :=
  ltac:(let x := eval vm_compute in
          (app (erun_regs 400 ld_rs0 (riscv_step false))
             (erun_regs 600 ld_c1.1
                (eread_resume (bv_unsigned ld_wf) ld_c1.2))) in
        exact x).
Definition ld_D : gset register := list_to_set ld_Dl.

(** THE TWO CURSORS, unevaluated compositions ([WeakEvStarted]'s F8 shape):
    [ld_x1] sits at the FETCH node, [ld_x2] at the DATA LOAD node. *)
Definition ld_x0 : ecur := (ld_rs0, riscv_step false).
Definition ld_x1 : ecur := esil 400 ld_D ld_x0.
Definition ld_x2 : ecur := esil 600 ld_D (ecur_read (bv_unsigned ld_wf) ld_x1).

Definition ld_reql : Interface.ReadReq.t 4 :=
  ltac:(let x := eval vm_compute in (eread_req_at 4 ld_x2.2) in
        lazymatch x with Some ?r => exact r | _ => fail 1 "not a read node" end).

(** THE MEASUREMENT.  106 silent nodes to the fetch, 97 more to the load. *)
Lemma ld_len1 : ecount 400 ld_D ld_x0 = 106%nat.
Proof. vm_cast_no_check (eq_refl 106%nat). Qed.
Lemma ld_len2 : ecount 600 ld_D (ecur_read (bv_unsigned ld_wf) ld_x1) = 97%nat.
Proof. vm_cast_no_check (eq_refl 97%nat). Qed.

(** THE LOAD NODE: width 4 at [&started], PLAIN — [(coh, latest, sync) =
    (false, false, false)].  The acquire ordering of the C-level
    [__ATOMIC_ACQUIRE] load is NOT on this access; it is the [fence r,rw]
    at [main+0x18], one instruction later. *)
Lemma ld_load_req : eread_req_at 4 ld_x2.2 = Some ld_reql.
Proof. vm_cast_no_check (eq_refl (Some ld_reql)). Qed.
Lemma ld_load_pa : Interface.ReadReq.pa ld_reql = ev_flag.
Proof. vm_cast_no_check (eq_refl ev_flag). Qed.
Lemma ld_load_plain :
  classify (Interface.ReadReq.access_kind ld_reql) = AkInfo false false false.
Proof. vm_cast_no_check (eq_refl (AkInfo false false false)). Qed.
Lemma ld_load_ram : dev_addr (Interface.ReadReq.pa ld_reql) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.

(** ... and it IS the same byte the store witness writes. *)
Lemma ld_same_flag : pa_z (Interface.ReadReq.pa ld_reql) = pa_z ev_flag.
Proof. by rewrite ld_load_pa. Qed.

(* ---------------------------------------------------------------------- *)
(** ** 1.1 The block *)

(** The hart, sitting at the load node. *)
Definition ld_p0 (cpu : CPU) (rs : regstate) (ib : oib32) : pexv6 :=
  PHart cpu ld_x2.2 rs None ib.

(** ... and where it lands, PER VALUE READ: the node accepts any word, so
    the block is parametric in [w] and nothing downstream may assume one. *)
Definition ld_p1 (w : bv 32) (cpu : CPU) (rs : regstate) (ib : oib32)
    : pexv6 :=
  PHart cpu (eread_resume (bv_unsigned w) ld_x2.2) rs None ib.

Definition ld_ts (t : nat) : list nat := [t; t; t; t].
Definition ld_vs (w : bv 32) : list (bv 8) :=
  [nth_byte w 0; nth_byte w 1; nth_byte w 2; nth_byte w 3].
Definition ld_tvs (t : nat) (w : bv 32) : list (nat * bv 8) :=
  [(t, nth_byte w 0); (t, nth_byte w 1);
   (t, nth_byte w 2); (t, nth_byte w 3)].

(** THE WLABEL the step emits: a plain, non-latest load of four bytes at
    [&started], with the EMPTY address-operand list (deviation D-8: a
    load's base register is not an RVWMO dependency source). *)
Definition ld_wl (t : nat) (w : bv 32) : wlabel :=
  WeakPromise.LLoad false false (pa_z ev_flag) (ld_tvs t w) [].

(** THE ROW: its axiomatic image, ONE graph label. *)
Definition ld_row (t : nat) (w : bv 32) : list WeakAxiomatic.lbl :=
  [WeakAxiomatic.LLoad false (pa_z ev_flag) (ld_ts t) (ld_vs w)].

Definition ld_em (t : nat) (w : bv 32) (cpu : CPU) (rs : regstate)
    (ib : oib32) : hemission :=
  HEm [(ld_wl t w, Some 0%nat)] (ld_p1 w cpu rs ib).

Lemma ld_pstep (t : nat) (w : bv 32) (cpu : CPU) (rs : regstate)
    (ib : oib32) (d0 : dev_state) :
  pstep_ev (ld_p0 cpu rs ib) d0 (ld_wl t w) (ld_p1 w cpu rs ib) d0.
Proof.
  destruct (eread_req_at_inv 4 ld_x2.2 ld_reql ld_load_req)
    as (K & Hm & Hres).
  rewrite /pstep_ev /ld_p0 /ld_p1 (Hres w) Hm.
  split; [reflexivity|]. exists None, None.
  split_and!; [reflexivity|reflexivity|]. left.
  rewrite /pstep_node /pnode_step /=.
  split; [done|]. left. split; [done|].
  exists w, (ld_tvs t w). split_and!; try reflexivity.
  intros j Hj. simpl in Hj.
  destruct j as [|[|[|[|j]]]]; [reflexivity|reflexivity|reflexivity|reflexivity|].
  exfalso. lia.
Qed.

Lemma ld_realizes (t : nat) (w : bv 32) (cpu : CPU) (rs : regstate)
    (ib : oib32) (ws : wstate) :
  hlbl_realizes (ld_p0 cpu rs ib) ws
    (WeakAxiomatic.LLoad false (pa_z ev_flag) (ld_ts t) (ld_vs w))
    (ld_wl t w).
Proof. rewrite /hlbl_realizes /ld_wl. split_and!; [done|done|done|reflexivity]. Qed.

(** THE WITNESS: hart 1's spin load IS an emittable row, at every value. *)
Theorem ld_hart_conf (i : agent) (t : nat) (w : bv 32) (cpu : CPU)
    (rs : regstate) (ib : oib32) (d0 : dev_state) :
  hart_conf i (ld_row t w) (ld_p0 cpu rs ib) (λ _, d0) (ld_em t w cpu rs ib).
Proof.
  rewrite /hart_conf /ld_em /ld_row /=.
  apply (HEone (λ _ : nat, d0) 0%nat ws_init
           (WeakAxiomatic.LLoad false (pa_z ev_flag) (ld_ts t) (ld_vs w))
           [] (ld_p0 cpu rs ib) [] (ld_p0 cpu rs ib) d0
           (ld_wl t w) (ld_p1 w cpu rs ib) [] (ld_p1 w cpu rs ib)).
  - apply ARnil.
  - apply ld_realizes.
  - apply ld_pstep.
  - apply HEnil.
Qed.

Theorem ld_em_devfree (t : nat) (w : bv 32) (cpu : CPU) (rs : regstate)
    (ib : oib32) : em_devfree (ld_em t w cpu rs ib).
Proof.
  rewrite /em_devfree /em_labels /ld_em /=.
  intros [H|H]%elem_of_cons; [by rewrite /ld_wl in H|].
  by apply elem_of_nil in H.
Qed.

(* ====================================================================== *)
(** * 2. THE ROW-DEPS OF A ONE-EVENT EMISSION ARE EMPTY

    Not by computation — the store's operand lists are a function of the
    universally quantified instruction channel [ib] — but by the two
    shape lemmas: an edge's TARGET is the row position of a write item
    (here 0) and an edge's SOURCE is strictly below its target. *)

Lemma row_deps_single (it : eitem) (jk : nat * nat) :
  it.2 = Some 0%nat → jk ∈ row_deps [it] → False.
Proof.
  intros Hit Hjk.
  pose proof (row_deps_lt _ _ Hjk) as Hlt.
  destruct (row_deps_aux_tgt _ _ _ Hjk) as (it' & Hin & Htg & _).
  apply elem_of_list_singleton in Hin as ->.
  rewrite Hit in Htg. simplify_eq. lia.
Qed.

Lemma ev_row_deps_empty (cpu : CPU) (rs : regstate) (ib : oib32) (jk : nat * nat) :
  jk ∈ row_deps (em_items (ev_em cpu rs ib)) → False.
Proof. apply (row_deps_single (ev_wl ib, Some 0%nat)); reflexivity. Qed.

Lemma ld_row_deps_empty (t : nat) (w : bv 32) (cpu : CPU) (rs : regstate)
    (ib : oib32) (jk : nat * nat) :
  jk ∈ row_deps (em_items (ld_em t w cpu rs ib)) → False.
Proof. apply (row_deps_single (ld_wl t w, Some 0%nat)); reflexivity. Qed.

(* ====================================================================== *)
(** * 3. THE TWO-HART GRAPH

    Both harts have a ONE-EVENT row, so there is no program order at all
    and hence no ppo⁻ edge: the whole ordering content of the graph is
    gmo plus the read's [ts]. *)

Definition lb_shape_ok (l : WeakAxiomatic.lbl) : Prop :=
  match l with
  | WeakAxiomatic.LLoad _ _ ts vs => length vs = length ts
  | WeakAxiomatic.LStore _ _ vs _ => vs ≠ []
  | WeakAxiomatic.LFence _ _ _ _ => True
  | WeakAxiomatic.LRmw _ _ _ ts rvs wvs _ =>
      wvs ≠ [] ∧ length wvs = length ts ∧ length rvs = length ts
  end.

Section G2.
  Context (im : image) (r0 r1 : WeakAxiomatic.lbl) (mo : list geid).
  Notation G := (GExec im [[r0]; [r1]] mo).

  Lemma g2_lbl (e : geid) (l : WeakAxiomatic.lbl) :
    gx_lbl G e = Some l →
    (e = (0%nat, 0%nat) ∧ l = r0) ∨ (e = (1%nat, 0%nat) ∧ l = r1).
  Proof.
    destruct e as [i k]. rewrite /gx_lbl /=.
    destruct i as [|[|i]]; simpl; [| |done]; destruct k as [|k]; simpl;
      try done; intros [= <-]; auto.
  Qed.

  Lemma g2_lbl0 : gx_lbl G (0%nat, 0%nat) = Some r0.
  Proof. reflexivity. Qed.
  Lemma g2_lbl1 : gx_lbl G (1%nat, 0%nat) = Some r1.
  Proof. reflexivity. Qed.

  Lemma g2_pos0 (e : geid) : is_Some (gx_lbl G e) → e.2 = 0%nat.
  Proof. intros [l Hl]. by destruct (g2_lbl e l Hl) as [[-> _]|[-> _]]. Qed.

  Lemma g2_nogpo (e1 e2 : geid) : ¬ gpo G e1 e2.
  Proof.
    intros (_ & Hlt & Hs1 & Hs2).
    rewrite (g2_pos0 e1 Hs1) (g2_pos0 e2 Hs2) in Hlt. lia.
  Qed.

  Lemma g2_noppo (e1 e2 : geid) : ¬ gppo G e1 e2.
  Proof.
    intros [[Hpo _]|[Hf|[[Hpo _]|(Hpo & _)]]]; try by eapply g2_nogpo.
    destruct Hf as (pr & pw & sr & sw & (_ & Hlt & kf & H1 & H2 & _) & _ & H2r).
    have Hs2 : is_Some (gx_lbl G e2).
    { destruct H2r as [[(l & Hl & _) _]|[(l & Hl & _) _]]; by exists l. }
    rewrite (g2_pos0 e2 Hs2) in H2. lia.
  Qed.

  Lemma g2_ppo_gmo : gppo_gmo G.
  Proof. intros e1 e2 H. by destruct (g2_noppo e1 e2 H). Qed.

  Lemma g2_gwf :
    NoDup mo →
    (∀ e : geid, e ∈ mo ↔ (e = (0%nat, 0%nat) ∨ e = (1%nat, 0%nat))) →
    lb_is_mem r0 = true → lb_is_mem r1 = true →
    lb_shape_ok r0 → lb_shape_ok r1 →
    gwf G.
  Proof.
    intros Hnd Hmo Hm0 Hm1 Hs0 Hs1. split_and!; [done| |].
    - intros e. split.
      + intros He. destruct (proj1 (Hmo e) He) as [-> | ->].
        * exists r0. split; [reflexivity|exact Hm0].
        * exists r1. split; [reflexivity|exact Hm1].
      + intros (l & Hl & _). apply (proj2 (Hmo e)).
        by destruct (g2_lbl e l Hl) as [[-> _]|[-> _]]; auto.
    - intros i p k l Hp Hk.
      destruct i as [|[|i]]; simpl in Hp; [| |done]; simplify_eq;
        destruct k as [|k]; simpl in Hk; try done; simplify_eq; done.
  Qed.
End G2.

(* ---------------------------------------------------------------------- *)
(** ** 3.1 The era image: the flag byte CLEAR (what [start.c] leaves) *)

Definition mp_img : image := λ a,
  if bool_decide ((pa_z ev_flag ≤ a)%Z ∧ (a < pa_z ev_flag + 4)%Z)
  then Some (nth_byte lock_zero (Z.to_nat (a - pa_z ev_flag)))
  else None.

Lemma mp_img_byte (j : nat) :
  (j < 4)%nat → mp_img (WeakAxiomatic.acc_addr (pa_z ev_flag) j) = Some (nth_byte lock_zero j).
Proof.
  intros Hj. rewrite /mp_img /WeakAxiomatic.acc_addr bool_decide_eq_true_2; [|lia].
  by rewrite Z.add_simpl_l Nat2Z.id.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 3.2 [mpw]: the load reads hart 0's store *)

Definition mpw : gexec :=
  GExec mp_img [ev_row; ld_row 1%nat lock_one]
        [(0%nat, 0%nat); (1%nat, 0%nat)].

Definition mpwd : gdexec := GDExec mpw [].

Lemma mpw_gwrites : gwrites mpw = [(0%nat, 0%nat)].
Proof. reflexivity. Qed.

Lemma mpw_gwix0 : gwix mpw (0%nat, 0%nat) = 1%nat.
Proof. reflexivity. Qed.

Lemma mpw_write_at1 : gwrite_at mpw 1%nat = Some (0%nat, 0%nat).
Proof. reflexivity. Qed.

(** The byte inversions, in the style of [lbg_wr]/[lbg_acc]. *)
Lemma mpw_wr (e : geid) (a : Z) (v : bv 8) :
  gwrites_byte mpw e a v →
  e = (0%nat, 0%nat) ∧
  ∃ j : nat, (j < 4)%nat ∧ a = WeakAxiomatic.acc_addr (pa_z ev_flag) j ∧
             v = nth_byte lock_one j.
Proof.
  intros (l & b & vs & j & Hl & Hwr & Hv & Ha).
  destruct (g2_lbl mp_img _ _ _ e l Hl) as [[-> ->]|[-> ->]];
    rewrite /ev_row /ld_row /= in Hwr; simplify_eq/=.
  split; [done|]. exists j.
  destruct j as [|[|[|[|j]]]]; simpl in Hv; simplify_eq; by eauto with lia.
Qed.

Lemma mpw_rd (e : geid) (a : Z) (t : nat) (v : bv 8) :
  greads_byte mpw e a t v →
  e = (1%nat, 0%nat) ∧ t = 1%nat ∧
  ∃ j : nat, (j < 4)%nat ∧ a = WeakAxiomatic.acc_addr (pa_z ev_flag) j ∧
             v = nth_byte lock_one j.
Proof.
  intros (l & b & ts & vs & j & Hl & Hrd & Ht & Hv & Ha).
  destruct (g2_lbl mp_img _ _ _ e l Hl) as [[-> ->]|[-> ->]];
    rewrite /ev_row /ld_row /= in Hrd; simplify_eq/=.
  have Ht1 : t = 1%nat by (destruct j as [|[|[|[|j]]]]; simpl in Ht; by simplify_eq).
  subst t. split; [done|]. split; [done|]. exists j.
  destruct j as [|[|[|[|j]]]]; simpl in Hv; simplify_eq; by eauto with lia.
Qed.

Lemma mpw_gvis0 : gvisible mpw (0%nat, 0%nat) (1%nat, 0%nat).
Proof.
  left. rewrite /gmo_lt. split_and!.
  - apply elem_of_list_here.
  - apply elem_of_list_further, elem_of_list_here.
  - by vm_compute.
Qed.

Theorem mpw_consistent : rvwmo_minus_consistent mpw.
Proof.
  split_and!.
  - apply (g2_gwf mp_img); [| |done|done|done|done].
    + repeat constructor; rewrite ?elem_of_list_In; simpl; intuition congruence.
    + intros e. rewrite !elem_of_cons elem_of_nil. naive_solver.
  - apply (g2_ppo_gmo mp_img).
  - intros e a t v Hrd.
    destruct (mpw_rd e a t v Hrd) as (-> & -> & j & Hj & -> & ->).
    split.
    + exists (0%nat, 0%nat). split_and!; [exact mpw_write_at1| |exact mpw_gvis0].
      rewrite /gwrites_byte. exists (WeakAxiomatic.LStore false (pa_z ev_flag)
        (wbytes 4 lock_one) WCplain), (pa_z ev_flag), (wbytes 4 lock_one), j.
      split_and!; [reflexivity|reflexivity| |reflexivity].
      destruct j as [|[|[|[|j]]]]; by [reflexivity|lia].
    + intros w' v' Hw' _. destruct (mpw_wr w' _ v' Hw') as (-> & _).
      rewrite mpw_gwix0. lia.
  - intros e a t v Hrd Hw.
    destruct (mpw_rd e a t v Hrd) as (-> & _ & _).
    destruct Hw as (l & Hl & Hlw). rewrite /gx_lbl /= in Hl. by simplify_eq.
Qed.

Theorem mpw_deps_consistent : rvwmo_minus_deps_consistent mpwd.
Proof.
  split_and!; [exact mpw_consistent| |]; by intros rw Hrw%elem_of_nil.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 3.3 THE CONFORMANCE BUNDLE — the first with TWO nonempty rows *)

Definition mp_boot (cpu0 cpu1 : CPU) (rs0 rs1 : regstate) (ib0 ib1 : oib32)
    : agent → pexv6 :=
  λ i, match i with
       | 0%nat => ev_p0 cpu0 rs0 ib0
       | 1%nat => ld_p0 cpu1 rs1 ib1
       | _ => PDisk None
       end.

Theorem mpw_qconf (cpu0 cpu1 : CPU) (rs0 rs1 : regstate) (ib0 ib1 : oib32)
    (d0 : dev_state) :
  gdexec_qconf (mp_boot cpu0 cpu1 rs0 rs1 ib0 ib1) d0 mp_img 2%nat mpwd.
Proof.
  split_and!; [reflexivity|simpl; lia|].
  intros i row Hrow.
  destruct i as [|[|i]]; simpl in Hrow; simplify_eq.
  - exists (ev_em cpu0 rs0 ib0). split_and!.
    + apply ev_hart_conf.
    + apply ev_em_devfree.
    + intros jk Hjk. by destruct (ev_row_deps_empty cpu0 rs0 ib0 jk Hjk).
  - exists (ld_em 1%nat lock_one cpu1 rs1 ib1). split_and!.
    + apply ld_hart_conf.
    + apply ld_em_devfree.
    + intros jk Hjk.
      by destruct (ld_row_deps_empty 1%nat lock_one cpu1 rs1 ib1 jk Hjk).
Qed.

(* ====================================================================== *)
(** * 4. THE EARLY-READ VARIANT: the load sees the era image *)

Definition mpw' : gexec :=
  GExec mp_img [ev_row; ld_row 0%nat lock_zero]
        [(1%nat, 0%nat); (0%nat, 0%nat)].

Definition mpwd' : gdexec := GDExec mpw' [].

Lemma mpw'_gwrites : gwrites mpw' = [(0%nat, 0%nat)].
Proof. reflexivity. Qed.
Lemma mpw'_gwix0 : gwix mpw' (0%nat, 0%nat) = 1%nat.
Proof. reflexivity. Qed.

Lemma mpw'_wr (e : geid) (a : Z) (v : bv 8) :
  gwrites_byte mpw' e a v →
  e = (0%nat, 0%nat) ∧
  ∃ j : nat, (j < 4)%nat ∧ a = WeakAxiomatic.acc_addr (pa_z ev_flag) j ∧
             v = nth_byte lock_one j.
Proof.
  intros (l & b & vs & j & Hl & Hwr & Hv & Ha).
  destruct (g2_lbl mp_img _ _ _ e l Hl) as [[-> ->]|[-> ->]];
    rewrite /ev_row /ld_row /= in Hwr; simplify_eq/=.
  split; [done|]. exists j.
  destruct j as [|[|[|[|j]]]]; simpl in Hv; simplify_eq; by eauto with lia.
Qed.

Lemma mpw'_rd (e : geid) (a : Z) (t : nat) (v : bv 8) :
  greads_byte mpw' e a t v →
  e = (1%nat, 0%nat) ∧ t = 0%nat ∧
  ∃ j : nat, (j < 4)%nat ∧ a = WeakAxiomatic.acc_addr (pa_z ev_flag) j ∧
             v = nth_byte lock_zero j.
Proof.
  intros (l & b & ts & vs & j & Hl & Hrd & Ht & Hv & Ha).
  destruct (g2_lbl mp_img _ _ _ e l Hl) as [[-> ->]|[-> ->]];
    rewrite /ev_row /ld_row /= in Hrd; simplify_eq/=.
  have Ht1 : t = 0%nat by (destruct j as [|[|[|[|j]]]]; simpl in Ht; by simplify_eq).
  subst t. split; [done|]. split; [done|]. exists j.
  destruct j as [|[|[|[|j]]]]; simpl in Hv; simplify_eq; by eauto with lia.
Qed.

(** THE POINT of the variant: the store is NOT visible to the load — it is
    gmo-LATER and cross-hart, so neither disjunct of [gvisible] holds. *)
Lemma mpw'_novis : ¬ gvisible mpw' (0%nat, 0%nat) (1%nat, 0%nat).
Proof.
  intros [Hmo|Hpo]; [|destruct Hpo as (H & _); simpl in H; discriminate H].
  destruct Hmo as (_ & _ & Hlt). vm_compute in Hlt. lia.
Qed.

Theorem mpw'_consistent : rvwmo_minus_consistent mpw'.
Proof.
  split_and!.
  - apply (g2_gwf mp_img); [| |done|done|done|done].
    + repeat constructor; rewrite ?elem_of_list_In; simpl; intuition congruence.
    + intros e. rewrite !elem_of_cons elem_of_nil. naive_solver.
  - apply (g2_ppo_gmo mp_img).
  - intros e a t v Hrd.
    destruct (mpw'_rd e a t v Hrd) as (-> & -> & j & Hj & -> & ->).
    split.
    + by apply mp_img_byte.
    + intros w' v' Hw' Hvis. destruct (mpw'_wr w' _ v' Hw') as (-> & _).
      by destruct (mpw'_novis Hvis).
  - intros e a t v Hrd Hw.
    destruct (mpw'_rd e a t v Hrd) as (-> & _ & _).
    destruct Hw as (l & Hl & Hlw). rewrite /gx_lbl /= in Hl. by simplify_eq.
Qed.

Theorem mpw'_deps_consistent : rvwmo_minus_deps_consistent mpwd'.
Proof.
  split_and!; [exact mpw'_consistent| |]; by intros rw Hrw%elem_of_nil.
Qed.

Theorem mpw'_qconf (cpu0 cpu1 : CPU) (rs0 rs1 : regstate) (ib0 ib1 : oib32)
    (d0 : dev_state) :
  gdexec_qconf (mp_boot cpu0 cpu1 rs0 rs1 ib0 ib1) d0 mp_img 2%nat mpwd'.
Proof.
  split_and!; [reflexivity|simpl; lia|].
  intros i row Hrow.
  destruct i as [|[|i]]; simpl in Hrow; simplify_eq.
  - exists (ev_em cpu0 rs0 ib0). split_and!.
    + apply ev_hart_conf.
    + apply ev_em_devfree.
    + intros jk Hjk. by destruct (ev_row_deps_empty cpu0 rs0 ib0 jk Hjk).
  - exists (ld_em 0%nat lock_zero cpu1 rs1 ib1). split_and!.
    + apply ld_hart_conf.
    + apply ld_em_devfree.
    + intros jk Hjk.
      by destruct (ld_row_deps_empty 0%nat lock_zero cpu1 rs1 ib1 jk Hjk).
Qed.

(* ====================================================================== *)
(** * 5. THE SUPPLY — [exec_prog_ok'] for the two-hart candidate *)

Definition mp_st : WeakAxiomatic.estep :=
  EStep 0%nat (WeakAxiomatic.LStore false (pa_z ev_flag)
                 (wbytes 4 lock_one) WCplain).
Definition mp_ld : WeakAxiomatic.estep :=
  EStep 1%nat (WeakAxiomatic.LLoad false (pa_z ev_flag)
                 (ld_ts 1%nat) (ld_vs lock_one)).

Definition mp_cand : cand := Cand mp_img [mp_st; mp_ld].

Definition mp_rows : agent → list WeakAxiomatic.lbl :=
  λ i, match i with
       | 0%nat => ev_row
       | 1%nat => ld_row 1%nat lock_one
       | _ => []
       end.

Lemma mp_cand_rows (i : agent) :
  (λ s, es_lb s) <$> filter (λ s, es_ag s = i) (cd_tr mp_cand) = mp_rows i.
Proof.
  rewrite /mp_cand /mp_rows /= !filter_cons filter_nil.
  destruct i as [|[|i]]; repeat case_decide; naive_solver.
Qed.

Theorem mp_supply (cpu0 cpu1 : CPU) (rs0 rs1 : regstate) (ib0 ib1 : oib32)
    (d0 : dev_state) :
  ∃ pst : nat → list pexv6,
    pst 0%nat = mp_boot cpu0 cpu1 rs0 rs1 ib0 ib1 <$> seq 0 2 ∧
    exec_prog_ok' pstep_ev pcls_ev pst (λ _, d0) (cand_exec mp_cand).
Proof.
  apply (supply_of_qconf mp_cand (mp_boot cpu0 cpu1 rs0 rs1 ib0 ib1) d0
           mp_rows 2%nat).
  - exact mp_cand_rows.
  - intros i Hi. by destruct i as [|[|i]]; [lia|lia|].
  - intros i Hi. destruct i as [|[|i]].
    + exists (ev_em cpu0 rs0 ib0). apply ev_hart_conf.
    + exists (ld_em 1%nat lock_one cpu1 rs1 ib1). apply ld_hart_conf.
    + exfalso. lia.
Qed.

(* ====================================================================== *)
(** * 6. WHAT A GENUINE [RacyD]-CYCLE (LB) WITNESS WOULD STILL COST

    [WeakRvwmoCert4] §5.7 records that there is no two-hart cycle witness
    "without a second emitted block".  §1 above IS that second block, so
    the record is now stale in its stated reason — but a CYCLE is still out
    of reach, for a different and sharper reason.  Honestly:

    (a) WHAT IS FREE NOW.  A cycle needs four blocks, two per hart
        (load a; store b | load b; store a).  The two INSTRUCTION kinds are
        both concrete: the [c.sw] of [WeakRvwmoConfWit] and the [c.lw] of
        §1.  Their ADDRESSES are not an obstacle either: the address lives
        in the cursor's register file ([a5] for the store, [a4] for the
        load), so a second pair at a different byte is one more
        [ColdBoot.cold_regs] instantiation — a ~1.5 s [vm_compute], the
        same shape as §1.  The graph side is the shape delivered in §3–§4.

    (b) THE ONE MISSING MECHANISM: [esil] ⟶ [adm_run].  Every block in the
        tree — [ev_*], [ld_*] — has an EMPTY administrative run ([ARnil]):
        it starts AT its memory node.  A two-event ROW needs the block for
        the load and the block for the store separated by an
        [adm_run true] covering the ~200 silent nodes from the load's
        resume, across the instruction boundary, to the store's node.
        [WeakEvStarted] §4 certifies exactly that stretch — but at the WP
        tier, as an [esil]/[ecur_loop] composition.  Nothing in the tree
        turns an [esil] stretch into an [adm_run] at the [pstep_ev] tier,
        and the translation is not a formality: the nodes in the stretch
        emit [LRegW], [LCtrl] and [LInstr] (not [LSilent]), they move the
        instruction channel [ib] ([ib_rd]/[ib_ann]), and those are exactly
        the labels [row_deps] reads.  That bridge is the whole price:
        a new leaf of the order of [WeakEvLift]'s stretch kit, plus one
        measured stretch per instruction pair.

    (c) AND THE MODEL SAYS THE CYCLE MUST BE CARRIED.  RVWMO⁻ has NO ppo
        arm from a plain load to a po-later store at a different byte —
        that is precisely why [WeakRvwmoGraph.lbg] is consistent.  So a
        genuine cycle needs the two same-hart edges to come from
        [row_deps] (an address/data/control dependency, ppo 9–11, ordered
        by [gdeps_gmo]) or from a fence.  In xv6's own [main] the loaded
        flag feeds only the [beqz] — a CONTROL dependency, which
        [WeakRvwmoConf.dstep] does record in [ds_ctl] — so the natural
        carrier is available in principle, but only through (b).  xv6's
        real cross-hart ordering is the LOCK, and route B handles that by
        [WeakRvwmoLock.cs_kill], not by a cycle witness.

    VERDICT: not within reach today; (b) is the single blocking item, and
    it is a leaf-sized piece of work, not a design problem. *)

(* ====================================================================== *)
(** * 7. AUDIT *)

Print Assumptions ld_hart_conf.
Print Assumptions mpw_qconf.
Print Assumptions mpw'_qconf.
Print Assumptions mp_supply.
