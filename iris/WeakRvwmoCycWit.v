(** * WeakRvwmoCycWit.v — THE [RacyD]-CYCLE WITNESS, AND THE WALK RUN ON IT

    Design: [claude-notes/design/weak-memory-route-b.md] §4e/§4f; the
    EIGHTH-PASS checkpoint item 1 of
    [claude-notes/projects/weak-memory-certification.md] ("Build the
    [RacyD]-cycle witness FIRST so the walk is checked non-vacuously").

    [WeakRvwmoWalk] reduces (R-2) [walk_supply] to a per-state certification
    policy.  A reduction is only worth its statement if the thing it reduces
    to is INHABITED at the shape the consumer actually meets — an
    [RacyD]-CYCLE graph, since [walk_supply] is invoked nowhere else.  This
    file builds one and RUNS THE WALK ON IT.

    ------------------------------------------------------------------------
    WHAT IS REAL AND WHAT IS HAND-BUILT — stated up front, because that is
    the honest content of a witness.

    REAL (the kernel's own, verbatim):
      - the access-kind records and the widths: both requests are built from
        [WeakEvStarted.ev_reqw] (the real [sw &started] write request of
        [main]) and [WeakRvwmoConfWit2.ld_reql] (the real [lw a5,0(a4)] read
        request at [main+0x16]), keeping their [access_kind], [va],
        [translation] and [tag] fields and changing ONLY the physical
        address.  So "plain, 4 bytes, RAM" is the machine's classification
        ([ev_store_plain] / [ld_load_plain]), not a hand-written constant.
      - the stored value [WeakLock.lock_one] and its byte decomposition.
      - one of the two addresses IS [&started] ([WeakEvStarted.ev_flag]).
      - every step relation, projection and consistency lemma used below is
        the tree's ([WeakEvInst.pstep_ev], [WeakRvwmoConf.hlbl_realizes],
        [WeakRvwmoCert]'s snoc calculus, [WeakRvwmoCert4.seg_step]).

    HAND-BUILT (and why it has to be):
      - the two-node MONAD FRAGMENT [cy_m] — a [MemRead] node followed by a
        [MemWrite] node — in the style of [WeakEvProv] §10's [wit_m].  NO
        xv6 code path has the shape an LB cycle needs (a load of byte A
        immediately followed by a store of a DIFFERENT byte B, with the two
        harts' roles swapped), and the real code's load is followed by ~117
        administrative nodes and a fetch before its next memory event
        ([WeakRvwmoAdm] §3).  Bridging that stretch is the [adm_run]
        machinery's job and is orthogonal to what this witness checks; the
        second address [cy_B] is [&started + 8].

    ------------------------------------------------------------------------
    WHAT IS CHECKED.

      §1  the hand-built two-event block: the node fragment, its two
          [pstep_ev] steps and its two [hlbl_realizes] projections.
      §2  [cy_hart_conf] — the block IS a [WeakRvwmoConf.hart_conf] at a
          TWO-EVENT row (a load then a store), with an empty [row_deps].
      §3  THE GRAPH [cyg]: LB, two harts, two events each, gmo
          [[sw B; lw B; sw A; lw A]].  [rvwmo_minus_deps_consistent],
          [gdexec_qconf], and — the point — a real [RacyD] CYCLE
          ([cyg_cycle]).
      §4  THE WALK, RUN.  The four certified steps, the two [seg_step]s,
          [walk_policy] at [cyg] discharged, and [cyg_walk] — the
          conclusion of [WeakRvwmoWalk.walk_supply_of_steps] at [cyg]:
          a [segs_run] whose final log IS [log_of cyg].
      §5  the audit.

    Nothing below is [Admitted] or [Axiom]-ed.  A LEAF. *)
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
Require Import WeakAxiomatic3.
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
Require Import WeakEvLift.
Require Import WeakEvStarted.
Require Import WeakSrvwmoLitmus.
Require Import WeakRvwmoConf.
Require Import WeakRvwmoSupply.
Require Import WeakRvwmoConfWit.
Require Import WeakRvwmoConfWit2.
Require Import WeakRvwmoAcyc.
Require Import WeakRvwmoCert.
Require Import WeakRvwmoFloor.
Require Import WeakRvwmoCert2.
Require Import WeakRvwmoCert3.
Require Import WeakRvwmoCert4.
Require Import WeakRvwmoKillArms.
Require Import WeakRvwmoGlue.
Require Import WeakRvwmoWalk.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** * 1. THE HAND-BUILT TWO-EVENT BLOCK *)

(** ** 1.1 The two addresses, and the requests

    Both requests keep every field of a REAL request but the address. *)
Definition cy_A : Arch.pa := ev_flag.
Definition cy_B : Arch.pa := SailStdpp.Values.mword_of_int (KernelSyms.started + 8).

Definition cy_wreq (a : Arch.pa) : Interface.WriteReq.t 4 :=
  Interface.WriteReq.make 4 a
    (Interface.WriteReq.access_kind ev_reqw)
    (Interface.WriteReq.value ev_reqw)
    (Interface.WriteReq.va ev_reqw)
    (Interface.WriteReq.translation ev_reqw)
    (Interface.WriteReq.tag ev_reqw).

Definition cy_rreq (a : Arch.pa) : Interface.ReadReq.t 4 :=
  Interface.ReadReq.make 4 a
    (Interface.ReadReq.access_kind ld_reql)
    (Interface.ReadReq.va ld_reql)
    (Interface.ReadReq.translation ld_reql)
    (Interface.ReadReq.tag ld_reql).

Lemma cy_wreq_plain a :
  classify (Interface.WriteReq.access_kind (cy_wreq a)) = AkInfo false false false.
Proof. apply ev_store_plain. Qed.

Lemma cy_rreq_plain a :
  classify (Interface.ReadReq.access_kind (cy_rreq a)) = AkInfo false false false.
Proof. apply ld_load_plain. Qed.

Lemma cy_wreq_val a : Interface.WriteReq.value (cy_wreq a) = lock_one.
Proof. apply ev_store_val. Qed.

Lemma cy_A_ram : dev_addr cy_A = false.
Proof. rewrite /cy_A -ev_store_pa. apply ev_store_ram. Qed.

Lemma cy_B_ram : dev_addr cy_B = false.
Proof. by vm_compute. Qed.

Definition zA : Z := pa_z cy_A.
Definition zB : Z := pa_z cy_B.

Lemma zA_val : zA = 2147525168.
Proof. by vm_compute. Qed.
Lemma zB_val : zB = 2147525176.
Proof. by vm_compute. Qed.

(** ** 1.2 The node fragment

    THREE nodes: a [MemRead] whose continuation IGNORES the value read — so
    the second memory node is reached at every answer, which is exactly what
    a certification that SUBSTITUTES the read needs — an [InstrAnnounce],
    and a [MemWrite].

    THE ANNOUNCE IS NOT DECORATION, and finding out why is what this witness
    bought: without it the load and the store are ONE instruction, so
    [WeakRvwmoConf.dstep]'s [ds_ld] still holds the load's row position when
    the store is emitted and [row_deps] carries the edge [(0,1)] — rule 13's
    "the instruction's own earlier reads precede its translated access".  A
    graph with that edge on BOTH harts is not LB-consistent at all: the four
    dep/rf edges force [gmo] to cycle, which is precisely the store-dep
    fragment doing its job.  The announce is the instruction BOUNDARY that
    resets [ds_ld] ([WeakRvwmoConf.dstep]'s [LInstr] arm), and it is an
    ADMINISTRATIVE node ([WeakAxRealize.lb_admin true LInstr]), so it lives
    in the second block's [adm_run] and not in the row. *)
Definition cy_ob : bvn := bv_to_bvn (Z_to_bv 32 0).
Definition cy_ib1 : oib32 := ib_ann (ib_of_bvn cy_ob).

Definition cy_m2 : M unit := Interface.Ret tt.

Definition cy_m1 (aS : Arch.pa) : M unit :=
  Interface.Next (Interface.MemWrite 4 (cy_wreq aS)) (λ _, cy_m2).

Definition cy_ma (aS : Arch.pa) : M unit :=
  Interface.Next (Interface.InstrAnnounce cy_ob) (λ _, cy_m1 aS).

Definition cy_m (aL aS : Arch.pa) : M unit :=
  Interface.Next (Interface.MemRead 4 (cy_rreq aL)) (λ _, cy_ma aS).

Definition cy_p0 (aL aS : Arch.pa) (cpu : CPU) (rs : regstate) : pexv6 :=
  PHart cpu (cy_m aL aS) rs None ib_none.
Definition cy_pa (aS : Arch.pa) (cpu : CPU) (rs : regstate) : pexv6 :=
  PHart cpu (cy_ma aS) rs None ib_none.
Definition cy_p1 (aS : Arch.pa) (cpu : CPU) (rs : regstate) : pexv6 :=
  PHart cpu (cy_m1 aS) rs None cy_ib1.
Definition cy_p2 (cpu : CPU) (rs : regstate) : pexv6 :=
  PHart cpu cy_m2 rs None cy_ib1.

(** ** 1.3 The bytes, and the three labels *)
Definition cy_bytes : list (bv 8) := wbytes 4 lock_one.

Lemma cy_bytes_ne : cy_bytes ≠ [].
Proof.
  have Hl : length cy_bytes = 4%nat by apply (wbytes_length 4).
  intros H. by rewrite H /= in Hl.
Qed.

Lemma cy_bytes_nth (j : nat) :
  (j < 4)%nat → cy_bytes !! j = Some (nth_byte lock_one j).
Proof. intros Hj. by apply (wbytes_lookup 4 lock_one j). Qed.

(** The read's per-byte answer list, at a chosen source index. *)
Definition cy_tvs (ts : list nat) : list (nat * bv 8) := zip ts cy_bytes.

Definition cy_wl_ld (a : Arch.pa) (ts : list nat) : wlabel :=
  WeakPromise.LLoad false false (pa_z a) (cy_tvs ts) [].

Definition cy_wl_st (a : Arch.pa) : wlabel :=
  WeakPromise.LStore false (pa_z a) (wbytes 4 lock_one)
    (deps_asrc (deps_of_ib (ib_bits cy_ib1)))
    (deps_vsrc (deps_of_ib (ib_bits cy_ib1))).

Lemma cy_tvs_fst ts : length ts = 4%nat → (cy_tvs ts).*1 = ts.
Proof.
  intros Hl. rewrite /cy_tvs fst_zip //.
  have -> : length cy_bytes = 4%nat by apply (wbytes_length 4).
  lia.
Qed.

Lemma cy_tvs_snd ts : length ts = 4%nat → (cy_tvs ts).*2 = cy_bytes.
Proof.
  intros Hl. rewrite /cy_tvs snd_zip //.
  have -> : length cy_bytes = 4%nat by apply (wbytes_length 4).
  lia.
Qed.

Lemma cy_tvs_len ts : length ts = 4%nat → length (cy_tvs ts) = 4%nat.
Proof.
  intros Hl. rewrite /cy_tvs length_zip Hl.
  have -> : length cy_bytes = 4%nat by apply (wbytes_length 4).
  lia.
Qed.

(** ** 1.4 The three steps *)

Lemma cy_pstep_ld (aL aS : Arch.pa) (cpu : CPU) (rs : regstate)
    (d : dev_state) (ts : list nat) :
  dev_addr aL = false → length ts = 4%nat →
  pstep_ev (cy_p0 aL aS cpu rs) d (cy_wl_ld aL ts) (cy_pa aS cpu rs) d.
Proof.
  intros Hram Hts.
  rewrite /pstep_ev /cy_p0 /cy_pa. split; [reflexivity|].
  exists None, None. split_and!; [reflexivity|reflexivity|].
  left. rewrite /pstep_node /cy_m /pnode_step /=.
  rewrite Hram. split; [reflexivity|]. left. split; [reflexivity|].
  exists lock_one, (cy_tvs ts). split_and!;
    [by apply cy_tvs_len| |reflexivity|reflexivity|reflexivity|reflexivity
    |reflexivity|reflexivity].
  intros j Hj. rewrite (cy_tvs_snd ts Hts). apply cy_bytes_nth. by simpl in Hj.
Qed.

Lemma cy_pstep_ann (aS : Arch.pa) (cpu : CPU) (rs : regstate) (d : dev_state) :
  pstep_ev (cy_pa aS cpu rs) d LInstr (cy_p1 aS cpu rs) d.
Proof.
  rewrite /pstep_ev /cy_pa /cy_p1. split; [reflexivity|].
  exists None, (Some cy_ib1). split_and!; [reflexivity|reflexivity|].
  left. rewrite /pstep_node /cy_ma /pnode_step /=.
  by split_and!.
Qed.

Lemma cy_pstep_st (aS : Arch.pa) (cpu : CPU) (rs : regstate) (d : dev_state) :
  dev_addr aS = false →
  pstep_ev (cy_p1 aS cpu rs) d (cy_wl_st aS) (cy_p2 cpu rs) d.
Proof.
  intros Hram.
  rewrite /pstep_ev /cy_p1 /cy_p2. split; [reflexivity|].
  exists None, None. split_and!; [reflexivity|reflexivity|].
  left. rewrite /pstep_node /cy_m1 /pnode_step /=.
  rewrite Hram. split; [done|]. left.
  split_and!; [reflexivity| |reflexivity|reflexivity|reflexivity|reflexivity
              |reflexivity].
  rewrite /cy_wl_st. reflexivity.
Qed.

(** ** 1.5 The two projections *)

Lemma cy_realizes_ld (aL aS : Arch.pa) (cpu : CPU) (rs : regstate)
    (ws : wstate) (ts : list nat) :
  length ts = 4%nat →
  hlbl_realizes (cy_p0 aL aS cpu rs) ws
    (WeakAxiomatic.LLoad false (pa_z aL) ts cy_bytes) (cy_wl_ld aL ts).
Proof.
  intros Hts. rewrite /hlbl_realizes /cy_wl_ld.
  split_and!; [done|done|done|].
  rewrite /proj_lbl (cy_tvs_fst ts Hts) (cy_tvs_snd ts Hts) //.
Qed.

Lemma cy_realizes_st (aS : Arch.pa) (cpu : CPU) (rs : regstate) (ws : wstate) :
  w_relp ws = false →
  hlbl_realizes (cy_p1 aS cpu rs) ws
    (WeakAxiomatic.LStore false (pa_z aS) cy_bytes WCplain) (cy_wl_st aS).
Proof.
  intros Hrel. rewrite /hlbl_realizes /cy_wl_st.
  split_and!; [done|done|done|].
  rewrite /proj_lbl /pcls_ev /cy_p1 /pnode_wclass /cy_m1 /=.
  by rewrite /wm_class_of /= Hrel /cy_bytes.
Qed.

(* ====================================================================== *)
(** * 2. THE TWO-EVENT ROW, EMITTED

    [HEone] twice and [HEnil]: the load block with an EMPTY administrative
    run, then the store block whose administrative run is the single
    [LInstr] of §1.2, then the end.  The only non-trivial side condition is
    the store's CLASS, and it is [WeakRvwmoConf.lbl_post_relp]'s content: a
    load leaves [w_relp] alone, so the fold's [w_relp] is still [ws_init]'s
    and the class is [WCplain]. *)

Definition cy_row (aL aS : Arch.pa) (ts : list nat) : list WeakAxiomatic.lbl :=
  [WeakAxiomatic.LLoad false (pa_z aL) ts cy_bytes;
   WeakAxiomatic.LStore false (pa_z aS) cy_bytes WCplain].

Definition cy_em (aL aS : Arch.pa) (ts : list nat) (cpu : CPU) (rs : regstate)
    : hemission :=
  HEm [(cy_wl_ld aL ts, Some 0%nat); (LInstr, None); (cy_wl_st aS, Some 1%nat)]
      (cy_p2 cpu rs).

Lemma cy_relp_after_load (aL : Arch.pa) (ts : list nat) :
  w_relp (lbl_post 0%nat ws_init
            (WeakAxiomatic.LLoad false (pa_z aL) ts cy_bytes)) = false.
Proof. by rewrite lbl_post_relp. Qed.

Theorem cy_hart_conf (i : agent) (aL aS : Arch.pa) (ts : list nat)
    (cpu : CPU) (rs : regstate) (d0 : dev_state) :
  dev_addr aL = false → dev_addr aS = false → length ts = 4%nat →
  hart_conf i (cy_row aL aS ts) (cy_p0 aL aS cpu rs) (λ _, d0)
    (cy_em aL aS ts cpu rs).
Proof.
  intros HrL HrS Hts.
  rewrite /hart_conf /cy_em /cy_row /=.
  apply (HEone (λ _ : nat, d0) 0%nat ws_init
           (WeakAxiomatic.LLoad false (pa_z aL) ts cy_bytes)
           [WeakAxiomatic.LStore false (pa_z aS) cy_bytes WCplain]
           (cy_p0 aL aS cpu rs) [] (cy_p0 aL aS cpu rs) d0
           (cy_wl_ld aL ts) (cy_pa aS cpu rs)
           [(LInstr, None); (cy_wl_st aS, Some 1%nat)] (cy_p2 cpu rs)).
  - apply ARnil.
  - by apply cy_realizes_ld.
  - by apply cy_pstep_ld.
  - apply (HEone (λ _ : nat, d0) 1%nat
             (lbl_post 0%nat ws_init
                (WeakAxiomatic.LLoad false (pa_z aL) ts cy_bytes))
             (WeakAxiomatic.LStore false (pa_z aS) cy_bytes WCplain)
             [] (cy_pa aS cpu rs) [LInstr] (cy_p1 aS cpu rs) d0
             (cy_wl_st aS) (cy_p2 cpu rs) [] (cy_p2 cpu rs)).
    + eapply ARcons; [done|apply cy_pstep_ann|apply ARnil].
    + apply cy_realizes_st. by apply cy_relp_after_load.
    + by apply cy_pstep_st.
    + apply HEnil.
Qed.

Theorem cy_em_devfree (aL aS : Arch.pa) (ts : list nat) (cpu : CPU)
    (rs : regstate) : em_devfree (cy_em aL aS ts cpu rs).
Proof.
  rewrite /em_devfree /em_labels /cy_em /=.
  intros H. apply elem_of_cons in H as [H|H]; [by rewrite /cy_wl_ld in H|].
  apply elem_of_cons in H as [H|H]; [done|].
  apply elem_of_cons in H as [H|H]; [by rewrite /cy_wl_st in H|].
  by apply elem_of_nil in H.
Qed.

(** THE EMISSION CARRIES NO DEPENDENCY EDGE — computed, not assumed.  This
    is the fact the announce buys (§1.2). *)
Lemma cy_row_deps_empty (aL aS : Arch.pa) (ts : list nat) (cpu : CPU)
    (rs : regstate) (jk : nat * nat) :
  jk ∈ row_deps (em_items (cy_em aL aS ts cpu rs)) → False.
Proof.
  have -> : row_deps (em_items (cy_em aL aS ts cpu rs)) = [] by vm_compute.
  by intros ?%elem_of_nil.
Qed.

(* ====================================================================== *)
(** * 3. THE GRAPH: LB, WITH A REAL [RacyD] CYCLE

    Two harts, two events each — a load then a store, the addresses
    SWAPPED between the harts — and the [gmo] the design names,
    [[sw B; lw B; sw A; lw A]] (one store EARLY).  Each load reads the
    OTHER hart's store: that is the LB shape, and it is exactly the
    execution RVWMO⁻ allows and rule 14 does not. *)

Definition cy_ts2 : list nat := [2%nat; 2%nat; 2%nat; 2%nat].
Definition cy_ts1 : list nat := [1%nat; 1%nat; 1%nat; 1%nat].

(** The era image: both words already hold [lock_one]'s bytes.  That is not
    cosmetic — [WeakRvwmoCert2.lbl_reidx] lets a certified read differ from
    the graph's only in its TIMESTAMPS, so the substituted read of §4 must
    return the same BYTES, and its source is the image. *)
Definition cy_img : image := λ a,
  if bool_decide (zA ≤ a < zA + 4) then cy_bytes !! Z.to_nat (a - zA)
  else if bool_decide (zB ≤ a < zB + 4) then cy_bytes !! Z.to_nat (a - zB)
  else Some (bv_0 8).

Definition cyg : gexec :=
  GExec cy_img
        [cy_row cy_A cy_B cy_ts2; cy_row cy_B cy_A cy_ts1]
        [(0%nat, 1%nat); (1%nat, 0%nat); (1%nat, 1%nat); (0%nat, 0%nat)].

Definition cygd : gdexec := GDExec cyg [].

Lemma cyg_lbl (e : geid) (l : WeakAxiomatic.lbl) :
  gx_lbl cyg e = Some l →
  (e = (0%nat, 0%nat) ∧ l = WeakAxiomatic.LLoad false zA cy_ts2 cy_bytes) ∨
  (e = (0%nat, 1%nat) ∧ l = WeakAxiomatic.LStore false zB cy_bytes WCplain) ∨
  (e = (1%nat, 0%nat) ∧ l = WeakAxiomatic.LLoad false zB cy_ts1 cy_bytes) ∨
  (e = (1%nat, 1%nat) ∧ l = WeakAxiomatic.LStore false zA cy_bytes WCplain).
Proof.
  destruct e as [i k]. rewrite /gx_lbl /cyg /cy_row /=.
  destruct i as [|[|i]]; simpl; [| |done];
    destruct k as [|[|k]]; simpl; try done; intros [= <-]; auto.
Qed.

Lemma cyg_pos (e : geid) : is_Some (gx_lbl cyg e) → (e.2 < 2)%nat.
Proof.
  intros [l Hl].
  destruct (cyg_lbl e l Hl) as [[-> _]|[[-> _]|[[-> _]|[-> _]]]]; simpl; lia.
Qed.

Lemma cy_bytes_len : length cy_bytes = 4%nat.
Proof. apply (wbytes_length 4). Qed.

(** The two words are DISJOINT: [&started] and [&started + 8]. *)
Lemma cy_ranges_disj (j j' : nat) :
  (j < 4)%nat → (j' < 4)%nat →
  WeakAxiomatic.acc_addr zA j ≠ WeakAxiomatic.acc_addr zB j'.
Proof. rewrite /WeakAxiomatic.acc_addr zA_val zB_val. lia. Qed.

Lemma cyg_wr (e : geid) (a : Z) (v : bv 8) :
  gwrites_byte cyg e a v →
  ∃ j : nat, (j < 4)%nat ∧ cy_bytes !! j = Some v ∧
    ((e = (0%nat, 1%nat) ∧ a = WeakAxiomatic.acc_addr zB j) ∨
     (e = (1%nat, 1%nat) ∧ a = WeakAxiomatic.acc_addr zA j)).
Proof.
  intros (l & b & vs & j & Hl & Hwr & Hv & Ha).
  destruct (cyg_lbl e l Hl) as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]];
    rewrite /= in Hwr; simplify_eq.
  - exists j. pose proof (lookup_lt_Some _ _ _ Hv) as Hlt.
    rewrite cy_bytes_len in Hlt. split_and!; [lia|exact Hv|]. by left.
  - exists j. pose proof (lookup_lt_Some _ _ _ Hv) as Hlt.
    rewrite cy_bytes_len in Hlt. split_and!; [lia|exact Hv|]. by right.
Qed.

Lemma cyg_rd (e : geid) (a : Z) (t : nat) (v : bv 8) :
  greads_byte cyg e a t v →
  ∃ j : nat, (j < 4)%nat ∧ cy_bytes !! j = Some v ∧
    ((e = (0%nat, 0%nat) ∧ t = 2%nat ∧ a = WeakAxiomatic.acc_addr zA j) ∨
     (e = (1%nat, 0%nat) ∧ t = 1%nat ∧ a = WeakAxiomatic.acc_addr zB j)).
Proof.
  intros (l & b & ts & vs & j & Hl & Hrd & Ht & Hv & Ha).
  destruct (cyg_lbl e l Hl) as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]];
    rewrite /= in Hrd; simplify_eq.
  - exists j. pose proof (lookup_lt_Some _ _ _ Hv) as Hlt.
    rewrite cy_bytes_len in Hlt.
    have Ht2 : t = 2%nat
      by (destruct j as [|[|[|[|j]]]]; simpl in Ht; by simplify_eq).
    split_and!; [lia|exact Hv|]. left. by split_and!.
  - exists j. pose proof (lookup_lt_Some _ _ _ Hv) as Hlt.
    rewrite cy_bytes_len in Hlt.
    have Ht1 : t = 1%nat
      by (destruct j as [|[|[|[|j]]]]; simpl in Ht; by simplify_eq).
    split_and!; [lia|exact Hv|]. right. by split_and!.
Qed.

Lemma cyg_gwrites : gwrites cyg = [(0%nat, 1%nat); (1%nat, 1%nat)].
Proof. reflexivity. Qed.

Lemma cyg_at1 : gwrite_at cyg 1%nat = Some (0%nat, 1%nat).
Proof. reflexivity. Qed.
Lemma cyg_at2 : gwrite_at cyg 2%nat = Some (1%nat, 1%nat).
Proof. reflexivity. Qed.
Lemma cyg_wix1 : gwix cyg (0%nat, 1%nat) = 1%nat.
Proof. reflexivity. Qed.
Lemma cyg_wix2 : gwix cyg (1%nat, 1%nat) = 2%nat.
Proof. reflexivity. Qed.

(** ** 3.1 Consistency *)

Lemma cyg_gmo_20 : gmo_lt cyg (1%nat, 1%nat) (0%nat, 0%nat).
Proof.
  split_and!.
  - by apply elem_of_list_further, elem_of_list_further, elem_of_list_here.
  - by apply elem_of_list_further, elem_of_list_further,
             elem_of_list_further, elem_of_list_here.
  - by vm_compute.
Qed.

Lemma cyg_gmo_01 : gmo_lt cyg (0%nat, 1%nat) (1%nat, 0%nat).
Proof.
  split_and!.
  - by apply elem_of_list_here.
  - by apply elem_of_list_further, elem_of_list_here.
  - by vm_compute.
Qed.

Lemma cyg_gwf : gwf cyg.
Proof.
  split_and!.
  - repeat constructor; rewrite ?elem_of_list_In; simpl; intuition congruence.
  - intros e. split.
    + intros He.
      apply elem_of_cons in He as [->|He];
        [by eexists; split; [reflexivity|reflexivity]|].
      apply elem_of_cons in He as [->|He];
        [by eexists; split; [reflexivity|reflexivity]|].
      apply elem_of_cons in He as [->|He];
        [by eexists; split; [reflexivity|reflexivity]|].
      apply elem_of_cons in He as [->|He];
        [by eexists; split; [reflexivity|reflexivity]|].
      by apply elem_of_nil in He.
    + intros (l & Hl & _).
      destruct (cyg_lbl e l Hl) as [[-> _]|[[-> _]|[[-> _]|[-> _]]]].
      * by apply elem_of_list_further, elem_of_list_further,
                  elem_of_list_further, elem_of_list_here.
      * by apply elem_of_list_here.
      * by apply elem_of_list_further, elem_of_list_here.
      * by apply elem_of_list_further, elem_of_list_further,
                  elem_of_list_here.
  - intros i p k l Hp Hk.
    have Hb : cy_bytes ≠ [] := cy_bytes_ne.
    have Hl4 : length cy_bytes = 4%nat := cy_bytes_len.
    destruct i as [|[|i]]; simpl in Hp; [| |done]; simplify_eq;
      destruct k as [|[|k]]; simpl in Hk; try done; simplify_eq;
      rewrite /cy_ts2 /cy_ts1 /=; by rewrite ?Hl4.
Qed.

(** The BYTE each event touches, inverted. *)
Lemma cyg_acc (e : geid) (a : Z) :
  gaccesses cyg e a →
  ∃ j : nat, (j < 4)%nat ∧
    ((e = (0%nat, 0%nat) ∧ a = WeakAxiomatic.acc_addr zA j) ∨
     (e = (0%nat, 1%nat) ∧ a = WeakAxiomatic.acc_addr zB j) ∨
     (e = (1%nat, 0%nat) ∧ a = WeakAxiomatic.acc_addr zB j) ∨
     (e = (1%nat, 1%nat) ∧ a = WeakAxiomatic.acc_addr zA j)).
Proof.
  intros [(v & Hw)|(t & v & Hr)].
  - destruct (cyg_wr e a v Hw) as (j & Hj & _ & [[-> ->]|[-> ->]]);
      exists j; split; [exact Hj| |exact Hj|]; auto.
  - destruct (cyg_rd e a t v Hr) as (j & Hj & _ & [(-> & _ & ->)|(-> & _ & ->)]);
      exists j; split; [exact Hj| |exact Hj|]; auto.
Qed.

(** No ppo⁻ arm fires: the two events of a hart touch DISJOINT words, there
    is no fence between them, and no access is an acquire or a release. *)
Lemma cyg_noppo (e1 e2 : geid) : ¬ gppo cyg e1 e2.
Proof.
  intros Hppo.
  have Hpo : ∀ x y, gpo cyg x y →
      (x = (0%nat, 0%nat) ∧ y = (0%nat, 1%nat)) ∨
      (x = (1%nat, 0%nat) ∧ y = (1%nat, 1%nat)).
  { intros x y (Hs & Hlt & [lx Hx] & [ly Hy]).
    destruct (cyg_lbl x lx Hx) as [[-> _]|[[-> _]|[[-> _]|[-> _]]]];
      destruct (cyg_lbl y ly Hy) as [[-> _]|[[-> _]|[[-> _]|[-> _]]]];
      simpl in Hs, Hlt; try lia; try done; auto. }
  destruct Hppo as [Hloc|[Hf|[Hacq|Hra]]].
  - destruct Hloc as (Hp & a & Ha1 & Ha2).
    destruct (Hpo _ _ Hp) as [[-> ->]|[-> ->]].
    + destruct (cyg_acc _ _ Ha1)
        as (j & Hj & [[_ E1]|[[Hc _]|[[Hc _]|[Hc _]]]]); [|done|done|done].
      destruct (cyg_acc _ _ Ha2)
        as (j' & Hj' & [[Hc _]|[[_ E2]|[[Hc _]|[Hc _]]]]); [done| |done|done].
      apply (cy_ranges_disj j j' Hj Hj'). by rewrite -E1 -E2.
    + destruct (cyg_acc _ _ Ha1)
        as (j & Hj & [[Hc _]|[[Hc _]|[[_ E1]|[Hc _]]]]); [done|done| |done].
      destruct (cyg_acc _ _ Ha2)
        as (j' & Hj' & [[Hc _]|[[Hc _]|[[Hc _]|[_ E2]]]]); [done|done|done|].
      apply (cy_ranges_disj j' j Hj' Hj). by rewrite -E2 -E1.
  - destruct Hf as (pr & pw & sr & sw & (Hs & Hlt & kf & H1 & H2 & Hkf) & _ & He2).
    have He2s : is_Some (gx_lbl cyg e2).
    { destruct He2 as [[(l & Hl & _) _]|[(l & Hl & _) _]]; by exists l. }
    have Hb2 : (e2.2 < 2)%nat by apply cyg_pos.
    destruct (cyg_lbl (e1.1, kf) _ Hkf)
      as [[Hc _]|[[Hc _]|[[Hc _]|[Hc _]]]]; injection Hc as _ Hkv; lia.
  - destruct Hacq as (_ & _ & (l & Hl & Haq) & _).
    destruct (cyg_lbl e1 l Hl) as [[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]];
      by rewrite /= in Haq.
  - destruct Hra as (_ & _ & (l & Hl & Hrl) & _ & _).
    destruct (cyg_lbl e1 l Hl) as [[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]];
      by rewrite /= in Hrl.
Qed.

Theorem cyg_consistent : rvwmo_minus_consistent cyg.
Proof.
  split_and!.
  - exact cyg_gwf.
  - intros e1 e2 H. by destruct (cyg_noppo e1 e2 H).
  - intros e a t v Hrd.
    destruct (cyg_rd e a t v Hrd)
      as (j & Hj & Hv & [(-> & -> & ->)|(-> & -> & ->)]).
    + split.
      * exists (1%nat, 1%nat). split_and!; [exact cyg_at2| |].
        { exists (WeakAxiomatic.LStore false zA cy_bytes WCplain), zA,
                 cy_bytes, j. by split_and!. }
        { left. exact cyg_gmo_20. }
      * intros w' v' Hw' _.
        destruct (cyg_wr w' _ v' Hw') as (j' & Hj' & _ & [[-> Ha]|[-> _]]).
        { exfalso. by apply (cy_ranges_disj j j' Hj Hj'). }
        { rewrite cyg_wix2. lia. }
    + split.
      * exists (0%nat, 1%nat). split_and!; [exact cyg_at1| |].
        { exists (WeakAxiomatic.LStore false zB cy_bytes WCplain), zB,
                 cy_bytes, j. by split_and!. }
        { left. exact cyg_gmo_01. }
      * intros w' v' Hw' _.
        destruct (cyg_wr w' _ v' Hw') as (j' & Hj' & _ & [[-> _]|[-> Ha]]).
        { rewrite cyg_wix1. lia. }
        { exfalso. by apply (cy_ranges_disj j' j Hj' Hj). }
  - intros e a t v Hrd Hw.
    destruct (cyg_rd e a t v Hrd) as (j & _ & _ & [(-> & _ & _)|(-> & _ & _)]);
      destruct Hw as (l & Hl & Hlw); rewrite /gx_lbl /= in Hl;
      by simplify_eq.
Qed.

Theorem cyg_deps_consistent : rvwmo_minus_deps_consistent cygd.
Proof.
  split_and!; [exact cyg_consistent| |]; by intros rw Hrw%elem_of_nil.
Qed.

(** ** 3.2 The conformance bundle *)

Definition cy_boot (cpu0 cpu1 : CPU) (rs0 rs1 : regstate) : agent → pexv6 :=
  λ i, match i with
       | 0%nat => cy_p0 cy_A cy_B cpu0 rs0
       | 1%nat => cy_p0 cy_B cy_A cpu1 rs1
       | _ => PDisk None
       end.

Theorem cyg_qconf (cpu0 cpu1 : CPU) (rs0 rs1 : regstate) (d0 : dev_state) :
  gdexec_qconf (cy_boot cpu0 cpu1 rs0 rs1) d0 cy_img 2%nat cygd.
Proof.
  split_and!; [reflexivity|simpl; lia|].
  intros i row Hrow.
  destruct i as [|[|i]]; simpl in Hrow; simplify_eq.
  - exists (cy_em cy_A cy_B cy_ts2 cpu0 rs0). split_and!.
    + apply cy_hart_conf; [apply cy_A_ram|apply cy_B_ram|reflexivity].
    + apply cy_em_devfree.
    + intros jk Hjk. by destruct (cy_row_deps_empty _ _ _ _ _ jk Hjk).
  - exists (cy_em cy_B cy_A cy_ts1 cpu1 rs1). split_and!.
    + apply cy_hart_conf; [apply cy_B_ram|apply cy_A_ram|reflexivity].
    + apply cy_em_devfree.
    + intros jk Hjk. by destruct (cy_row_deps_empty _ _ _ _ _ jk Hjk).
Qed.

(** ** 3.3 THE CYCLE — the point of the witness

    Four arms, alternating [gpow] (po into a write — rule 14's own edge,
    which RVWMO⁻ does NOT have) and [grf].  This is exactly the shape
    [WeakRvwmoGlue.cycle_segments] decomposes and [walk_supply] is invoked
    at. *)

Lemma cyg_gpow0 : gpow cyg (0%nat, 0%nat) (0%nat, 1%nat).
Proof.
  split_and!.
  - split_and!; [reflexivity|simpl; lia|by eexists|by eexists].
  - by eexists.
  - reflexivity.
Qed.

Lemma cyg_gpow1 : gpow cyg (1%nat, 0%nat) (1%nat, 1%nat).
Proof.
  split_and!.
  - split_and!; [reflexivity|simpl; lia|by eexists|by eexists].
  - by eexists.
  - reflexivity.
Qed.

Lemma cyg_grf0 : grf cyg (0%nat, 1%nat) (1%nat, 0%nat).
Proof.
  exists (WeakAxiomatic.acc_addr zB 0%nat), 1%nat, (nth_byte lock_one 0%nat).
  split; [|exact cyg_at1].
  exists (WeakAxiomatic.LLoad false zB cy_ts1 cy_bytes), zB, cy_ts1, cy_bytes,
         0%nat.
  split_and!; [reflexivity|reflexivity|reflexivity| |reflexivity].
  apply cy_bytes_nth. lia.
Qed.

Lemma cyg_grf1 : grf cyg (1%nat, 1%nat) (0%nat, 0%nat).
Proof.
  exists (WeakAxiomatic.acc_addr zA 0%nat), 2%nat, (nth_byte lock_one 0%nat).
  split; [|exact cyg_at2].
  exists (WeakAxiomatic.LLoad false zA cy_ts2 cy_bytes), zA, cy_ts2, cy_bytes,
         0%nat.
  split_and!; [reflexivity|reflexivity|reflexivity| |reflexivity].
  apply cy_bytes_nth. lia.
Qed.

Theorem cyg_cycle : tc (RacyD cygd) (0%nat, 0%nat) (0%nat, 0%nat).
Proof.
  eapply tc_l; [left; left; exact cyg_gpow0|].
  eapply tc_l; [left; right; left; exact cyg_grf0|].
  eapply tc_l; [left; left; exact cyg_gpow1|].
  apply tc_once. left; right; left. exact cyg_grf1.
Qed.

(** … and the cycle in the form [walk_supply]'s own hypotheses take it. *)
Theorem cyg_segments : ∃ z ss, ss ≠ [] ∧ raw_chain cygd z z ss.
Proof.
  apply (cycle_segments cygd (0%nat, 0%nat)); [|exact cyg_cycle].
  by destruct cyg_deps_consistent as (_ & ? & _).
Qed.

(* ====================================================================== *)
(** * 4. THE WALK, RUN ON THE CYCLE

    Four certified steps, two [seg_step]s, and — through
    [WeakRvwmoWalk]'s own engine ([wlk_inv_step] twice, then
    [log_of_of_pfx]) — the conclusion [walk_supply] asks for, at a graph
    that really carries an [RacyD] cycle.

    THE READ POLICY, in the concrete: hart 0's load is the SUBSTITUTED one
    (its graph source is hart 1's store, which the log does not yet hold),
    so it reads the ERA IMAGE — [WeakRvwmoCert.latest_read_lbl] at the
    empty log — and [lbl_reidx] holds because the image carries the same
    bytes.  Hart 1's load is TRUE: by the time it runs, hart 0's store IS
    in the log at index 1, which is exactly its graph source. *)

(** The "other agent" twin of [WeakRvwmoCert2.cand_snoc_relp]. *)
Lemma cand_snoc_relp_ne (c : cand) (i j : agent) (lb : WeakAxiomatic.lbl) :
  j ≠ i →
  w_relp (ms_ws (cand_last_st (cand_snoc c (EStep i lb))) j)
  = w_relp (ms_ws (cand_last_st c) j).
Proof.
  intros Hne.
  have H1 : cand_last_st (cand_snoc c (EStep i lb))
          = stt (cand_exec (cand_snoc c (EStep i lb))) (S (cd_end c))
    by rewrite {1}/cand_last_st cd_end_snoc.
  rewrite H1 (cand_next _ (cd_end c) (EStep i lb) (cand_snoc_tr_end c _))
          (cand_snoc_last_st c (EStep i lb)).
  by rewrite (mnext_ws_ne _ _ _ _ Hne).
Qed.

Section walkrun.
  Context (cpu0 cpu1 : CPU) (rs0 rs1 : regstate) (d0 : dev_state).

  Notation boot := (cy_boot cpu0 cpu1 rs0 rs1).

  (** ** 4.1 The four candidates *)
  Definition cw_c0 : cand := Cand cy_img [].
  Definition cw_lb0 : WeakAxiomatic.lbl := latest_read_lbl cw_c0 false zA 4.
  Definition cw_c1 : cand := cand_snoc cw_c0 (EStep 0%nat cw_lb0).
  Definition cw_lb1 : WeakAxiomatic.lbl :=
    WeakAxiomatic.LStore false zB cy_bytes WCplain.
  Definition cw_c2 : cand := cand_snoc cw_c1 (EStep 0%nat cw_lb1).
  Definition cw_lb2 : WeakAxiomatic.lbl := latest_read_lbl cw_c2 false zB 4.
  Definition cw_c3 : cand := cand_snoc cw_c2 (EStep 1%nat cw_lb2).
  Definition cw_lb3 : WeakAxiomatic.lbl :=
    WeakAxiomatic.LStore false zA cy_bytes WCplain.
  Definition cw_c4 : cand := cand_snoc cw_c3 (EStep 1%nat cw_lb3).

  (** ** 4.2 The two substituted / true reads, COMPUTED *)
  Lemma cw_log0 : cd_log_end cw_c0 = [].
  Proof. reflexivity. Qed.

  Lemma cw_log2 : cd_log_end cw_c2 = [WMsg zB cy_bytes (Some 0%nat) WCplain].
  Proof. by rewrite /cw_c2 /cw_c1 !cd_log_end_snoc. Qed.

  Lemma cw_lb0_eq :
    cw_lb0 = WeakAxiomatic.LLoad false zA [0%nat; 0%nat; 0%nat; 0%nat] cy_bytes.
  Proof. rewrite /cw_lb0 /latest_read_lbl. by vm_compute. Qed.

  Lemma cw_lb2_eq :
    cw_lb2 = WeakAxiomatic.LLoad false zB cy_ts1 cy_bytes.
  Proof.
    rewrite /cw_lb2 /latest_read_lbl /lrd_ts /lrd_vs cw_log2.
    have -> : cd_img cw_c2 = cy_img by reflexivity.
    by vm_compute.
  Qed.

  (** ** 4.3 Consistency of the four *)
  Lemma cw_c0_cons : srvwmo_consistent cw_c0.
  Proof.
    apply srvwmo_of_wf, cand_reachable. intros k s Hs. by destruct k.
  Qed.

  Lemma cw_bytes0 : latest_bytes_ok cw_c0 zA 4.
  Proof.
    intros j Hj. rewrite cw_log0.
    destruct j as [|[|[|[|j]]]]; try lia; vm_compute; by eexists.
  Qed.

  Lemma cw_c1_cons : srvwmo_consistent cw_c1.
  Proof. apply snoc_latest_consistent; [apply cw_c0_cons|apply cw_bytes0]. Qed.

  Lemma cw_c2_cons : srvwmo_consistent cw_c2.
  Proof. apply snoc_write_consistent; [apply cw_c1_cons|apply cy_bytes_ne]. Qed.

  Lemma cw_bytes2 : latest_bytes_ok cw_c2 zB 4.
  Proof.
    intros j Hj. rewrite cw_log2.
    have -> : cd_img cw_c2 = cy_img by reflexivity.
    destruct j as [|[|[|[|j]]]]; try lia; vm_compute; by eexists.
  Qed.

  Lemma cw_c3_cons : srvwmo_consistent cw_c3.
  Proof. apply snoc_latest_consistent; [apply cw_c2_cons|apply cw_bytes2]. Qed.

  Lemma cw_c4_cons : srvwmo_consistent cw_c4.
  Proof. apply snoc_write_consistent; [apply cw_c3_cons|apply cy_bytes_ne]. Qed.
  (** ** 4.4 The [w_relp] facts the two store projections need *)
  Lemma cw_relp0 : w_relp (ms_ws (cand_last_st cw_c0) 0%nat) = false.
  Proof. reflexivity. Qed.

  Lemma cw_relp0_1 : w_relp (ms_ws (cand_last_st cw_c0) 1%nat) = false.
  Proof. reflexivity. Qed.

  Lemma cw_relp1 : w_relp (ms_ws (cand_last_st cw_c1) 0%nat) = false.
  Proof. by rewrite /cw_c1 cand_snoc_relp cw_relp0 cw_lb0_eq. Qed.

  Lemma cw_relp3 : w_relp (ms_ws (cand_last_st cw_c3) 1%nat) = false.
  Proof.
    rewrite /cw_c3 cand_snoc_relp /cw_c2 (cand_snoc_relp_ne _ 0%nat 1%nat);
      [|done].
    rewrite /cw_c1 (cand_snoc_relp_ne _ 0%nat 1%nat); [|done].
    by rewrite cw_relp0_1 cw_lb2_eq.
  Qed.

  (** ** 4.5 The process supply, one [exec_prog_ok'_snoc] per event *)
  Definition cw_pst0 : nat → list pexv6 := λ _, boot <$> seq 0 2.
  Definition cw_dv0 : nat → dev_state := λ _, d0.
  Definition cw_pst1 : nat → list pexv6 :=
    pst_snoc cw_c0 cw_pst0 0%nat (cy_pa cy_B cpu0 rs0).
  Definition cw_dv1 : nat → dev_state := dv_snoc cw_c0 cw_dv0 d0.
  Definition cw_pst2 : nat → list pexv6 :=
    pst_snoc cw_c1 cw_pst1 0%nat (cy_p2 cpu0 rs0).
  Definition cw_dv2 : nat → dev_state := dv_snoc cw_c1 cw_dv1 d0.
  Definition cw_pst3 : nat → list pexv6 :=
    pst_snoc cw_c2 cw_pst2 1%nat (cy_pa cy_A cpu1 rs1).
  Definition cw_dv3 : nat → dev_state := dv_snoc cw_c2 cw_dv2 d0.
  Definition cw_pst4 : nat → list pexv6 :=
    pst_snoc cw_c3 cw_pst3 1%nat (cy_p2 cpu1 rs1).
  Definition cw_dv4 : nat → dev_state := dv_snoc cw_c3 cw_dv3 d0.

  Lemma cw_prog0 :
    exec_prog_ok' pstep_ev pcls_ev cw_pst0 cw_dv0 (cand_exec cw_c0).
  Proof. intros k s Hs. rewrite cand_ex_tr in Hs. by destruct k. Qed.

  Lemma cw_prog1 :
    exec_prog_ok' pstep_ev pcls_ev cw_pst1 cw_dv1 (cand_exec cw_c1).
  Proof.
    apply (exec_prog_ok'_snoc cw_c0 0%nat (cy_p0 cy_A cy_B cpu0 rs0)
             (cy_p0 cy_A cy_B cpu0 rs0) d0 [] (cy_wl_ld cy_A [0%nat;0%nat;0%nat;0%nat])
             cw_lb0 (cy_pa cy_B cpu0 rs0) d0 cw_pst0 cw_dv0).
    - apply cw_prog0.
    - reflexivity.
    - apply ARnil.
    - rewrite cw_lb0_eq. by apply cy_realizes_ld.
    - apply cy_pstep_ld; [apply cy_A_ram|reflexivity].
  Qed.

  Lemma cw_prog2 :
    exec_prog_ok' pstep_ev pcls_ev cw_pst2 cw_dv2 (cand_exec cw_c2).
  Proof.
    apply (exec_prog_ok'_snoc cw_c1 0%nat (cy_pa cy_B cpu0 rs0)
             (cy_p1 cy_B cpu0 rs0) d0 [LInstr] (cy_wl_st cy_B)
             cw_lb1 (cy_p2 cpu0 rs0) d0 cw_pst1 cw_dv1).
    - apply cw_prog1.
    - reflexivity.
    - eapply ARcons; [done|apply cy_pstep_ann|apply ARnil].
    - apply cy_realizes_st, cw_relp1.
    - apply cy_pstep_st, cy_B_ram.
  Qed.

  Lemma cw_prog3 :
    exec_prog_ok' pstep_ev pcls_ev cw_pst3 cw_dv3 (cand_exec cw_c3).
  Proof.
    apply (exec_prog_ok'_snoc cw_c2 1%nat (cy_p0 cy_B cy_A cpu1 rs1)
             (cy_p0 cy_B cy_A cpu1 rs1) d0 [] (cy_wl_ld cy_B cy_ts1)
             cw_lb2 (cy_pa cy_A cpu1 rs1) d0 cw_pst2 cw_dv2).
    - apply cw_prog2.
    - reflexivity.
    - apply ARnil.
    - rewrite cw_lb2_eq. by apply cy_realizes_ld.
    - apply cy_pstep_ld; [apply cy_B_ram|reflexivity].
  Qed.

  Lemma cw_prog4 :
    exec_prog_ok' pstep_ev pcls_ev cw_pst4 cw_dv4 (cand_exec cw_c4).
  Proof.
    apply (exec_prog_ok'_snoc cw_c3 1%nat (cy_pa cy_A cpu1 rs1)
             (cy_p1 cy_A cpu1 rs1) d0 [LInstr] (cy_wl_st cy_A)
             cw_lb3 (cy_p2 cpu1 rs1) d0 cw_pst3 cw_dv3).
    - apply cw_prog3.
    - reflexivity.
    - eapply ARcons; [done|apply cy_pstep_ann|apply ARnil].
    - apply cy_realizes_st, cw_relp3.
    - apply cy_pstep_st, cy_A_ram.
  Qed.
  (** ** 4.6 The two certified segments *)
  Definition cw_S0 : cyc_state := CSt cw_c0 cw_pst0 cw_dv0.
  Definition cw_S2 : cyc_state := CSt cw_c2 cw_pst2 cw_dv2.
  Definition cw_S4 : cyc_state := CSt cw_c4 cw_pst4 cw_dv4.

  Definition cw_o0 : segout :=
    SegOut 0%nat (cy_row cy_A cy_B cy_ts2) 0%nat
           [EStep 0%nat cw_lb0; EStep 0%nat cw_lb1].
  Definition cw_o1 : segout :=
    SegOut 1%nat (cy_row cy_B cy_A cy_ts1) 2%nat
           [EStep 1%nat cw_lb2; EStep 1%nat cw_lb3].

  Lemma cw_S0_ok : cst_ok d0 cw_S0.
  Proof. split_and!; [apply cw_c0_cons|apply cw_prog0|reflexivity]. Qed.

  Lemma cw_S2_ok : cst_ok d0 cw_S2.
  Proof. split_and!; [apply cw_c2_cons|apply cw_prog2|reflexivity]. Qed.

  Lemma cw_S4_ok : cst_ok d0 cw_S4.
  Proof. split_and!; [apply cw_c4_cons|apply cw_prog4|reflexivity]. Qed.

  Lemma cw_seg0 : seg_step d0 cw_o0 cw_S0 cw_S2.
  Proof.
    split_and!; [apply cw_S0_ok|apply cw_S2_ok|reflexivity|reflexivity| |].
    - intros s Hs. apply elem_of_cons in Hs as [->|Hs]; [done|].
      apply elem_of_cons in Hs as [->|Hs]; [done|by apply elem_of_nil in Hs].
    - rewrite /cy_row. apply Forall2_cons_2; [|apply Forall2_cons_2; [|done]].
      + rewrite cw_lb0_eq. by split_and!.
      + reflexivity.
  Qed.

  Lemma cw_seg1 : seg_step d0 cw_o1 cw_S2 cw_S4.
  Proof.
    split_and!; [apply cw_S2_ok|apply cw_S4_ok|reflexivity|reflexivity| |].
    - intros s Hs. apply elem_of_cons in Hs as [->|Hs]; [done|].
      apply elem_of_cons in Hs as [->|Hs]; [done|by apply elem_of_nil in Hs].
    - rewrite /cy_row. apply Forall2_cons_2; [|apply Forall2_cons_2; [|done]].
      + rewrite cw_lb2_eq. by split_and!.
      + reflexivity.
  Qed.

  (** ** 4.7 … as [WeakRvwmoWalk]'s own steps

    [wlk_step_of_seg] is what turns each into one step of the walk: the
    segment is "non-writes, then one store", so its appended messages are
    the single message of the graph's [(n+1)]-st write.  Note the SECOND
    segment's read is [cy_ts1] = [1;1;1;1] — the graph's own source, in the
    log by then — while the FIRST is the substituted one. *)
  Lemma cw_gmsg1 : gmsg cyg (0%nat, 1%nat) = Some (WMsg zB cy_bytes (Some 0%nat) WCplain).
  Proof. reflexivity. Qed.

  Lemma cw_gmsg2 : gmsg cyg (1%nat, 1%nat) = Some (WMsg zA cy_bytes (Some 1%nat) WCplain).
  Proof. reflexivity. Qed.

  Theorem cw_step0 : wlk_step cyg d0 cw_S0 0%nat.
  Proof.
    eapply (wlk_step_of_seg cyg d0 cw_S0 cw_S2 0%nat cw_o0
              [WeakAxiomatic.LLoad false zA cy_ts2 cy_bytes]
              false zB cy_bytes WCplain (0%nat, 1%nat));
      [apply cw_seg0|reflexivity| |reflexivity|reflexivity|reflexivity
      |exact cyg_at1|exact cw_gmsg1].
    by apply Forall_singleton.
  Qed.

  Theorem cw_step1 : wlk_step cyg d0 cw_S2 1%nat.
  Proof.
    eapply (wlk_step_of_seg cyg d0 cw_S2 cw_S4 1%nat cw_o1
              [WeakAxiomatic.LLoad false zB cy_ts1 cy_bytes]
              false zA cy_bytes WCplain (1%nat, 1%nat));
      [apply cw_seg1|reflexivity| |reflexivity|reflexivity|reflexivity
      |exact cyg_at2|exact cw_gmsg2].
    by apply Forall_singleton.
  Qed.

  (** ** 4.8 THE WALK'S CONCLUSION, at the cycle graph *)
  Lemma cw_inv0 : wlk_inv boot d0 2%nat cyg cw_S0 0%nat.
  Proof.
    split_and!; [apply cw_S0_ok|reflexivity|reflexivity|reflexivity|].
    apply wlog_pfx_nil.
  Qed.

  Lemma cw_pfx2 : wlog_pfx cyg 1%nat (cd_log_end cw_c2).
  Proof.
    rewrite cw_log2.
    exact (wlog_pfx_snoc cyg 0%nat [] (0%nat, 1%nat) _
             (wlog_pfx_nil cyg) cyg_at1 cw_gmsg1).
  Qed.

  Lemma cw_inv2 : wlk_inv boot d0 2%nat cyg cw_S2 1%nat.
  Proof.
    split_and!; [apply cw_S2_ok|reflexivity|reflexivity|reflexivity|].
    exact cw_pfx2.
  Qed.

  Lemma cw_log4 :
    cd_log_end cw_c4
    = [WMsg zB cy_bytes (Some 0%nat) WCplain]
      ++ [WMsg zA cy_bytes (Some 1%nat) WCplain].
  Proof. by rewrite /cw_c4 /cw_c3 2!cd_log_end_snoc cw_log2. Qed.

  Lemma cw_pfx4 : wlog_pfx cyg 2%nat (cd_log_end cw_c4).
  Proof.
    rewrite cw_log4.
    exact (wlog_pfx_snoc cyg 1%nat [WMsg zB cy_bytes (Some 0%nat) WCplain]
             (1%nat, 1%nat) _ cw_pfx2 cyg_at2 cw_gmsg2).
  Qed.

  Lemma cw_inv4 : wlk_inv boot d0 2%nat cyg cw_S4 2%nat.
  Proof.
    split_and!; [apply cw_S4_ok|reflexivity|reflexivity|reflexivity|].
    exact cw_pfx4.
  Qed.

  (** THE WITNESS.  Exactly [WeakRvwmoGlue2.walk_supply]'s conclusion, at a
      graph that carries a real [RacyD] cycle ([cyg_cycle]) and is
      [gdexec_qconf]-conformant ([cyg_qconf]). *)
  Theorem cyg_walk :
    ∃ (l : list segout) (S0 Sf : cyc_state),
      segs_run d0 l S0 Sf ∧
      cd_img (cst_c Sf) = gx_img cyg ∧
      cst_pst Sf 0%nat = boot <$> seq 0 2 ∧
      cst_dv Sf 0%nat = d0 ∧
      log_of cyg (cd_log (cst_c Sf) (length (cd_tr (cst_c Sf)))).
  Proof.
    exists [cw_o0; cw_o1], cw_S0, cw_S4.
    destruct cw_inv4 as (Hok & Himg & Hpst & Hdv & Hpfx).
    split_and!; [|exact Himg|exact Hpst|exact Hdv|].
    - eapply segs_more; [apply cw_seg0|].
      eapply segs_more; [apply cw_seg1|].
      apply segs_done, cw_S4_ok.
    - apply log_of_of_pfx.
      have -> : length (gwrites cyg) = 2%nat by rewrite cyg_gwrites.
      exact Hpfx.
  Qed.
End walkrun.

(* ====================================================================== *)
(** * 5. AUDIT

    [Print Assumptions] over the whole chain: the five rv64d reservation
    axioms of tier 1 and nothing else.  In particular the [RacyD] cycle,
    the conformance bundle and the walk's conclusion at [cyg] are all
    hypothesis-free. *)

Print Assumptions cy_pstep_ld.
Print Assumptions cy_pstep_ann.
Print Assumptions cy_pstep_st.
Print Assumptions cy_hart_conf.
Print Assumptions cy_row_deps_empty.
Print Assumptions cyg_consistent.
Print Assumptions cyg_deps_consistent.
Print Assumptions cyg_qconf.
Print Assumptions cyg_cycle.
Print Assumptions cyg_segments.
Print Assumptions cyg_walk.
