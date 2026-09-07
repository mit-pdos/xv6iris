(* ====================================================================== *)
(* VConcStep.v -- MORE THAN ONE HART, against [RiscvLang.prim_step].       *)
(*                                                                         *)
(* [VExecStep] carries a single hart's [exec] run to a chain of the        *)
(* language's own steps.  A litmus test cannot use it: a race has two      *)
(* harts and the suite's question is whether the model has an execution    *)
(* for each outcome the hardware showed, which is a question about an      *)
(* INTERLEAVING.  Run such a case through the single-hart theorem and the  *)
(* second hart never executes -- the DONE flag is never published and the  *)
(* run burns its budget on a program that cannot finish.                   *)
(*                                                                         *)
(* WHAT MADE THIS POSSIBLE WITHOUT A SECOND BRIDGE.  [VExecStep]'s chain   *)
(* is already parametric in the hart; what it lacked was the other half of *)
(* the invariant -- that stepping THIS hart leaves what is known about the *)
(* OTHERS standing.  [others_kept] is that half, and with it every lemma   *)
(* below is composition.  Nothing here re-crosses the flat/relaxed gap.    *)
(*                                                                         *)
(* WHY READING THE TOP IS LEGAL FOR TWO HARTS.  [mnode_step]'s plain-load  *)
(* arm picks any view at or above the hart's floor and under the top, so   *)
(* the TOP is always one of them -- which is the flat cache, which is what *)
(* [exec] reads.  That is not an SC collapse and does not need one hart:   *)
(* it is the strongest read TSO allows, and a schedule built from it       *)
(* denotes real model executions.  What it CANNOT exhibit is an outcome    *)
(* that needs a hart to read STALE -- store buffering's (0,0), finding 24. *)
(* Those need [VTso]'s [PStale] and are not provable here; a case whose    *)
(* observation needs one does not compute to that observation, and fails   *)
(* rather than passing on a weaker claim.                                  *)
(*                                                                         *)
(* NO DEVICE STEPS.  A litmus test races two harts over memory; it drives  *)
(* no UART and no disk, and this driver therefore never settles the device *)
(* fabric.  That is a restriction and it is deliberate: it is what lets    *)
(* the whole multi-hart layer stand on the hart chain alone.  A            *)
(* concurrency test that needs a device wants [VExecStep]'s settle lemmas  *)
(* threaded with [others_kept] too, which is a bigger change than this.    *)
(*                                                                         *)
(* THE GRANULARITY IS ONE INSTRUCTION, and that is a SUBSET of the model's *)
(* interleavings -- [prim_step] is one Sail-monad node, so another hart    *)
(* can land between the two halves of one instruction.  Subset is the safe *)
(* direction: every schedule here denotes a real model execution, and an   *)
(* outcome that needed a sub-instruction interleaving shows up as a case   *)
(* that cannot be matched rather than one that wrongly passes.             *)
(* ====================================================================== *)
From Stdlib Require Import List ZArith Lia.
From stdpp Require Import base list gmap functions relations bitvector.definitions.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvExec VirtioModel DevModel ColdBoot.
Require Import RiscvLang TsoMemPa.
From VTest Require Import VTest VRun VTso VExecStep.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 0. THE RELAXED INTERPRETER MEETS THE MODEL.                             *)
(*                                                                         *)
(*    [VExecStep]'s [enode_mnode] is this for the FLAT interpreter, and it *)
(*    has to cross the flat/relaxed gap arm by arm.  These do not:         *)
(*    [VTso.tnode] was written against [mnode_step]'s arms, so every arm   *)
(*    below is a matter of naming the witnesses.  What they buy is the     *)
(*    STALE read -- the one thing the flat interpreter cannot express, and *)
(*    the one thing store buffering's (0,0) needs.                         *)
(* ---------------------------------------------------------------------- *)

(* THE FUNCTIONAL TSO READ MEETS THE RELATIONAL ONE.  [tso_read_bytes_f]
   gathers the bytes and assembles them; [tso_read_bytes] is the arm's
   premise, one equation per byte.  The proof is [read_bytes_spec]'s, with
   the flat lookup replaced by [tso_read] -- the gathering, the assembly and
   the [nth_byte] round-trip are the same. *)
Lemma tso_read_bytes_f_spec (img : gmap Arch.pa (bv 8)) (log : list pwmsg)
    (h : agent) (tv : nat) (pa : Arch.pa) (n : N) (w : bv (8 * n)) :
  tso_read_bytes_f img log h tv pa n = Some w ->
  tso_read_bytes img log h tv pa n w.
Proof.
  unfold tso_read_bytes_f, tso_read_bytes.
  destruct (mapM (fun j : nat => tso_read img log h tv (pa_add pa j))
                 (seq 0 (N.to_nat n))) as [bs|] eqn:Hm; [|discriminate].
  intros [= <-] j Hj.
  apply mapM_Some_1 in Hm.
  pose proof (Forall2_length Hm) as Hlen. rewrite length_seq in Hlen.
  assert (Hjlt : (j < length bs)%nat) by (rewrite <- Hlen; lia).
  assert (Hseq : seq 0 (N.to_nat n) !! j = Some j).
  { rewrite lookup_seq_lt by (rewrite <- Hlen in Hjlt; lia). f_equal. }
  destruct (Forall2_lookup_l _ _ _ _ _ Hm Hseq) as (b & Hbs & Hmm).
  rewrite Hmm. f_equal.
  assert (Hbb : bs !!! j = b) by (apply list_lookup_total_correct; exact Hbs).
  apply bv_eq. rewrite nth_byte_unsigned.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  pose proof (assemble_bytes_bound bs) as [Hlo Hhi]. rewrite <- Hlen in Hhi.
  rewrite (Z.mod_small (assemble_bytes bs));
    [| split; [lia| rewrite N2Z.inj_mul; lia ] ].
  pose proof (assemble_bytes_byte bs j Hjlt) as Hbyte.
  rewrite Nat2Z.inj_mul in Hbyte. change (Z.of_nat 8) with 8 in Hbyte.
  replace (Z.of_N (8 * N.of_nat j)) with (8 * Z.of_nat j) by (rewrite N2Z.inj_mul; lia).
  rewrite Hbyte, Hbb. reflexivity.
Qed.

(* ONE NODE OF THE RELAXED INTERPRETER IS ONE [mnode_step].

   [VExecStep]'s [enode_mnode] is this for the FLAT interpreter, and it has
   to cross the flat/relaxed gap arm by arm.  This does not: [VTso.tnode]
   was written against [mnode_step]'s arms -- [stale_view] IS the two
   premises of the plain-load arm, [hr_read] IS its post-state -- so every
   arm here is a matter of naming the witnesses.  What it buys is the STALE
   read, which the flat interpreter cannot express and which store
   buffering's (0,0) needs. *)
(* [hok_bounds] with the two facts the relaxed arms add: the stale view is
   a max over the footprint's coherence floors, and every one of those is
   under the top. *)
Ltac tso_bounds :=
  repeat first
    [ assumption | reflexivity
    | apply Nat.max_lub | apply if_le | apply fence_post_le | apply own_pub_le
    | apply coh_upd_win_le | apply coh_win_max_le
    | progress (unfold stale_view, hr_read, hr_excl, hr_clear, excl_tv, write_tv)
    | progress cbn [hr_rv hr_coh]
    | lia ].

Lemma tnode_mnode (pol : rpol) (cpu : CPU) (g : gstate) (s : mstate)
    (m m' : M unit) (s' : mstate) (log' : list pwmsg) (tv' : nat) (hr' : hread) :
  hart_ok cpu g s ->
  tnode pol (hart_agent cpu) g.(gimg) s g.(glog) (g.(gtv) cpu) (g.(ghr) cpu) m
    = Some (m', s', log', tv', hr') ->
  exists itv' r',
    mnode_step (others_resv g.(gresv) cpu) (hart_agent cpu) g.(gimg)
      s g.(glog) (g.(gtv) cpu) (g.(gitv) cpu) (g.(ghr) cpu) (g.(gresv) cpu)
      m m' s' log' tv' itv' hr' r'
    /\ hart_ok cpu (wb cpu g s' log' tv' itv' hr' r') s'.
Proof.
  intros Hok Hn.
  pose proof Hok as [Hr Hm Hd Hfl Hal Htv Hitv Hrv Hcoh].
  destruct m as [y|T oc k]; [discriminate Hn|].
  destruct oc; cbn [tnode] in Hn;
    first
      [ discriminate Hn
      | (* the state no-ops: the same equations on both sides *)
        revert Hn; intros [= <- <- <- <- <-];
        exists (g.(gitv) cpu), (g.(gresv) cpu);
        split;
          [ cbn [mnode_step]; repeat split; reflexivity
          | apply (hart_ok_wb_same cpu g s _); try exact Hok;
            try (cbn; reflexivity); tso_bounds ]
      | idtac ].
  (* --- A LOAD ------------------------------------------------------ *)
  - destruct (dev_addr (Interface.ReadReq.pa t)) eqn:Hda.
    + (* MMIO: the device answers, and its state may move *)
      destruct (dev_read (mdev s) (Interface.ReadReq.pa t) n) as [[w d']|] eqn:Hdr;
        [|discriminate Hn].
      revert Hn; intros [= <- <- <- <- <-].
      exists (g.(gitv) cpu), (g.(gresv) cpu).
      split.
      * cbn [mnode_step]. rewrite Hda. exists w, d'.
        repeat split; first [ exact Hdr | reflexivity ].
      * apply (hart_ok_wb_same cpu g s _); try exact Hok;
          try (cbn; reflexivity); tso_bounds.
    + destruct (ak_excl (Interface.ReadReq.access_kind t)) eqn:Hex.
      * (* THE EXCLUSIVE READ: never blocked, because [ho_alone] says no
           other hart reserves anything *)
        destruct (read_bytes (mem s) (Interface.ReadReq.pa t) n) as [w|] eqn:Hrb;
          [|discriminate Hn].
        revert Hn; intros [= <- <- <- <- <-].
        exists (g.(gitv) cpu), (Some (snap_of (Interface.ReadReq.pa t) n w)).
        split.
        -- cbn [mnode_step]. rewrite Hda. right. right.
           split; [exact Hex|]. right.
           split; [rewrite Hal; set_solver|].
           exists w. repeat split;
             first [ reflexivity
                   | intros j Hj; exact (read_bytes_spec _ _ _ _ Hrb j Hj) ].
        -- apply (hart_ok_wb_same cpu g s _); try exact Hok;
             try (cbn; reflexivity);
             tso_bounds.
      * destruct (ak_ifetch (Interface.ReadReq.access_kind t)) eqn:Hif.
        -- (* THE FETCH, at the TOP view and with the icache's agent --
              [tso_read_top_flat] holds for every agent, which is why the
              flat cache is a fetch the arm admits whatever [pol] says *)
           destruct (read_bytes (mem s) (Interface.ReadReq.pa t) n) as [w|] eqn:Hrb;
             [|discriminate Hn].
           revert Hn; intros [= <- <- <- <- <-].
           exists (g.(gitv) cpu), (g.(gresv) cpu).
           split.
           ++ cbn [mnode_step]. rewrite Hda. left. split; [exact Hif|].
              exists (length g.(glog)), w.
              repeat split;
                first [ assumption | reflexivity | apply Nat.le_refl
                      | intros j Hj; rewrite tso_read_top_flat, <- Hfl, Hm;
                        exact (read_bytes_spec _ _ _ _ Hrb j Hj) ].
           ++ apply (hart_ok_wb_same cpu g s _); try exact Hok;
                try (cbn; reflexivity); tso_bounds.
        -- destruct pol.
           ++ (* PFresh: at the top of the log, which is the flat cache *)
              destruct (read_bytes (mem s) (Interface.ReadReq.pa t) n) as [w|] eqn:Hrb;
                [|discriminate Hn].
              revert Hn; intros [= <- <- <- <- <-].
              exists (g.(gitv) cpu), (g.(gresv) cpu).
              split.
              ** cbn [mnode_step]. rewrite Hda. right. left.
                 split; [exact Hif|]. split; [exact Hex|].
                 exists (length g.(glog)), w.
                 repeat split;
                   first [ assumption | reflexivity | apply Nat.le_refl
                         | intros j Hj; apply Hcoh
                         | intros j Hj; rewrite tso_read_top_flat, <- Hfl, Hm;
                           exact (read_bytes_spec _ _ _ _ Hrb j Hj) ].
              ** apply (hart_ok_wb_same cpu g s _); try exact Hok;
                   try (cbn; reflexivity);
                   tso_bounds.
           ++ (* PStale: at the LOWEST view the arm admits, which is what
                 [stale_view] computes -- and it is the whole point of this
                 file: the other hart's later message is above it and stays
                 invisible, which is store buffering's (0,0) *)
              destruct (tso_read_bytes_f g.(gimg) g.(glog) (hart_agent cpu)
                          (stale_view (ghr g cpu) (gtv g cpu)
                             (Interface.ReadReq.pa t) n)
                          (Interface.ReadReq.pa t) n) as [w|] eqn:Hrb;
                [|discriminate Hn].
              revert Hn; intros [= <- <- <- <- <-].
              exists (g.(gitv) cpu), (g.(gresv) cpu).
              split.
              ** cbn [mnode_step]. rewrite Hda. right. left.
                 split; [exact Hif|]. split; [exact Hex|].
                 eexists (stale_view (ghr g cpu) (gtv g cpu)
                            (Interface.ReadReq.pa t) n), w.
                 repeat split;
                   first
                     [ reflexivity
                     | (unfold stale_view; apply Nat.le_max_l)
                     | (unfold stale_view; apply Nat.max_lub;
                        [exact Htv | apply coh_win_max_le; exact Hcoh])
                     | (intros j Hj; unfold stale_view;
                        eapply Nat.le_trans;
                        [apply coh_win_max_ge; exact Hj | apply Nat.le_max_r])
                     | (intros j Hj;
                        exact (tso_read_bytes_f_spec _ _ _ _ _ _ _ Hrb j Hj)) ].
              ** apply (hart_ok_wb_same cpu g s _); try exact Hok;
                   try (cbn; reflexivity);
                   tso_bounds.
  (* --- A STORE ----------------------------------------------------- *)
  - destruct (dev_addr (Interface.WriteReq.pa t)) eqn:Hda.
    + (* MMIO write: strongly ordered, no log *)
      destruct (dev_write (mdev s) (Interface.WriteReq.pa t) n
                          (Interface.WriteReq.value t)) as [d'|] eqn:Hdw;
        [|discriminate Hn].
      revert Hn; intros [= <- <- <- <- <-].
      exists (g.(gitv) cpu), None.
      split.
      * cbn [mnode_step]. rewrite Hda. exists d'.
        repeat split; first [ exact Hdw | reflexivity ].
      * apply (hart_ok_wb_same cpu g s _); try exact Hok;
          try (cbn; reflexivity); tso_bounds.
    + (* THE RAM STORE: append the message, and the flat cache keeps
         lock-step with the append *)
      revert Hn; intros [= <- <- <- <- <-].
      exists (g.(gitv) cpu), None.
      split.
      * cbn [mnode_step]. rewrite Hda. right.
        split; [rewrite Hal; set_solver|].
        repeat split; reflexivity.
      * apply hart_ok_wb; try assumption.
        -- cbn [mem].
           assert (Hms : mem s = flat (gimg g) (glog g))
             by (rewrite <- Hm; exact Hfl).
           symmetry. rewrite Hms. unfold snap_of. apply flat_store.
        -- (* the floor: a plain store moves nothing, the conditional half
              of an acquire pair takes it past its own append *)
           unfold write_tv. rewrite length_app. cbn [length].
           apply if_le; [apply if_le|]; lia.
        -- rewrite length_app. cbn [length]. lia.
        -- unfold hr_clear; cbn [hr_rv]. rewrite length_app. cbn [length]. lia.
        -- intros a. unfold hr_clear; cbn [hr_coh]. specialize (Hcoh a).
           rewrite length_app. cbn [length]. lia.
  (* --- A FENCE ----------------------------------------------------- *)
  - revert Hn; intros [= <- <- <- <- <-].
    exists (if fence_ifetch b
            then Nat.max (g.(gitv) cpu)
                   (fence_post (hart_agent cpu) g.(glog) true false
                      (g.(gtv) cpu) (hr_rv (g.(ghr) cpu)))
            else g.(gitv) cpu),
           (g.(gresv) cpu).
    split.
    * cbn [mnode_step]. repeat split; reflexivity.
    * apply (hart_ok_wb_same cpu g s _); try exact Hok;
        try (cbn; reflexivity); tso_bounds.
Qed.

(* ---------------------------------------------------------------------- *)
(* 1. THE STATE THE INTERPRETER CAN COMPUTE.                               *)
(*                                                                         *)
(*    A [gstate] carries the write log and every hart's views; the         *)
(*    interpreter computes none of that -- in the single-hart theorem the  *)
(*    [gstate] is existential from beginning to end and only the [mstate]  *)
(*    is evaluated.  The multi-hart analogue of [mstate] is this: every    *)
(*    hart's registers beside ONE memory and ONE device fabric.            *)
(* ---------------------------------------------------------------------- *)

Record cstate := CState {
  cregs : CPU -> regstate;
  cmem  : gmap Arch.pa (bv 8);
  cdev  : dev_state;
}.

Definition cfocus (cs : cstate) (c : CPU) : mstate :=
  MState (cs.(cregs) c) cs.(cmem) cs.(cdev).

Definition cput (cs : cstate) (c : CPU) (s : mstate) : cstate :=
  CState (<[c := s.(sregs)]> cs.(cregs)) s.(mem) s.(mdev).

Definition cflag (cs : cstate) : bool := flag_set (cfocus cs hart_primary).

(* ---------------------------------------------------------------------- *)
(* 2. THE SCHEDULE.  A list of harts, one whole instruction each.          *)
(* ---------------------------------------------------------------------- *)

Definition cinstr (tick : bool) (c : CPU) (cs : cstate) : option cstate :=
  match exec (riscv_step tick) (cfocus cs c) with
  | Some (_, s') => Some (cput cs c s')
  | None => None
  end.

Fixpoint crun (tick : bool) (sch : list CPU) (cs : cstate) : option cstate :=
  match sch with
  | [] => Some cs
  | c :: sch' => match cinstr tick c cs with
                 | Some cs' => crun tick sch' cs'
                 | None => None
                 end
  end.

(* After the interleaving a case cares about, both harts just have to reach
   the DONE flag; [cfinish] repeats [round] until one of them publishes. *)
Fixpoint cfinish (tick : bool) (round : list CPU) (n : nat) (cs : cstate)
  : option cstate :=
  if cflag cs then Some cs else
  match n with
  | 0%nat => None
  | S n' => match crun tick round cs with
            | Some cs' => cfinish tick round n' cs'
            | None => None
            end
  end.

(* ---------------------------------------------------------------------- *)
(* 3. THE INVARIANT, for EVERY hart rather than one.                       *)
(* ---------------------------------------------------------------------- *)

Record gs_ok (g : gstate) : Prop := GsOk {
  gs_flat : g.(gmem) = flat g.(gimg) g.(glog);
  gs_res  : all_resv g.(gresv) = ∅;
  gs_tv   : forall c, (g.(gtv) c <= length g.(glog))%nat;
  gs_itv  : forall c, (g.(gitv) c <= length g.(glog))%nat;
  gs_rv   : forall c, (hr_rv (g.(ghr) c) <= length g.(glog))%nat;
  gs_coh  : forall c a, (hr_coh (g.(ghr) c) a <= length g.(glog))%nat;
}.

Record cs_ok (cs : cstate) (g : gstate) : Prop := CsOk {
  cs_regs : forall c, g.(gregs) c = cs.(cregs) c;
  cs_mem  : g.(gmem) = cs.(cmem);
  cs_dev  : g.(gdev) = cs.(cdev);
}.

Lemma others_resv_of_all (gr : CPU -> option resv) (cpu : CPU) :
  all_resv gr = ∅ -> others_resv gr cpu = ∅.
Proof.
  intros H. apply set_eq. intros a. split; [|set_solver].
  intros Ha. rewrite <- H. unfold others_resv in Ha. unfold all_resv.
  apply elem_of_union_list in Ha as (X & HX & Hin).
  apply elem_of_list_fmap in HX as (c & -> & Hc).
  destruct (decide (c = cpu)) as [->|Hne]; [set_solver|].
  apply elem_of_union_list. exists (resv_dom gr c). split; [|exact Hin].
  apply elem_of_list_fmap. exists c. split; [reflexivity|exact Hc].
Qed.

(* every hart of a [gs_ok] state satisfies the SINGLE-hart invariant
   against its own projection, which is what lets [VExecStep] step it *)
Lemma cs_hart_ok (cs : cstate) (g : gstate) (c : CPU) :
  gs_ok g -> cs_ok cs g -> hart_ok c g (cfocus cs c).
Proof.
  intros [Hfl Hres Htv Hitv Hrv Hcoh] [Hr Hm Hd].
  constructor; cbn [cfocus sregs mem mdev].
  - apply Hr.
  - exact Hm.
  - exact Hd.
  - exact Hfl.
  - exact (others_resv_of_all _ c Hres).
  - apply Htv.
  - apply Hitv.
  - apply Hrv.
  - apply Hcoh.
Qed.

Lemma log_len_le (g g' : gstate) (c : CPU) :
  others_kept c g g' -> (length g.(glog) <= length g'.(glog))%nat.
Proof.
  intros [[ext Hext] _ _ _ _ _ _]. rewrite Hext, length_app. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. ONE INSTRUCTION OF ONE HART IS A CHAIN OF [prim_step]s.              *)
(*                                                                         *)
(*    An item is the instruction AND the boundary that follows it, in that *)
(*    order, and the order is what makes the invariant hold BETWEEN items: *)
(*    the boundary is where a dangling reservation is dropped, so every    *)
(*    switch point has [all_resv = ∅] and any hart can be the next one.    *)
(*    That is also why the pool's uniform point is [riscv_step tick] and   *)
(*    not [Ret tt].                                                        *)
(* ---------------------------------------------------------------------- *)

(* [nsteps_trans] concatenates the observation lists, and unifying
   [?k1 ++ ?k2] with [[]] does not solve; both halves are silent here, so
   this is the same lemma with the concatenation already done. *)
Lemma nsteps_trans_nil (n m : nat) (r1 r2 r3 : language.cfg riscv_lang) :
  @language.nsteps riscv_lang n r1 [] r2 ->
  @language.nsteps riscv_lang m r2 [] r3 ->
  @language.nsteps riscv_lang (n + m) r1 [] r3.
Proof. intros H1 H2. exact (nsteps_trans n m r1 r2 r3 [] [] H1 H2). Qed.

Lemma cinstr_nsteps (tick : bool) (gen : nat) (c : CPU)
    (t1 t2 : list mexpr) (cs cs' : cstate) (g : gstate) :
  thread_live g gen -> gs_ok g -> cs_ok cs g ->
  cinstr tick c cs = Some cs' ->
  exists N g',
    @language.nsteps riscv_lang N
      (t1 ++ HartE gen c (riscv_step tick) :: t2, g) []
      (t1 ++ HartE gen c (riscv_step tick) :: t2, g')
    /\ thread_live g' gen /\ gs_ok g' /\ cs_ok cs' g'.
Proof.
  intros Hlive Hgs Hcs Hci.
  pose proof (cs_hart_ok cs g c Hgs Hcs) as Hok.
  unfold cinstr in Hci.
  destruct (exec (riscv_step tick) (cfocus cs c)) as [[u s1]|] eqn:Hex;
    [|discriminate Hci].
  revert Hci; intros [= <-].
  (* the instruction *)
  destruct (exec_nsteps tick gen c t1 t2 (riscv_step tick) (cfocus cs c) u s1 g
              Hex Hlive Hok) as (N1 & g1 & Hn1 & Hok1 & Hlv1 & Hk1).
  (* ...and the boundary that ends it, which drops the reservation *)
  destruct (boundary_prim tick gen c g1 s1 u Hlv1 Hok1)
    as (g2 & Hps2 & Hok2 & Hlv2 & Hres2 & Hk2).
  pose proof (others_kept_trans c g g1 g2 Hk1 Hk2) as Hk.
  exists (N1 + 1)%nat, g2.
  split.
  { eapply nsteps_trans_nil; [exact Hn1|].
    apply (nsteps_l_nil 0%nat _ (t1 ++ HartE gen c (riscv_step tick) :: t2, g2));
      [exact (hstep_step gen c t1 t2 _ _ g1 g2 Hps2)
      |apply language.nsteps_refl]. }
  split; [exact Hlv2|].
  pose proof Hok2 as [Hr2 Hm2 Hd2 Hfl2 Hal2 Htv2 Hitv2 Hrv2 Hcoh2].
  pose proof Hgs as [Hfl Hres Htv Hitv Hrv Hcoh].
  pose proof Hcs as [Hr Hm Hd].
  pose proof (log_len_le g g2 c Hk) as Hlen.
  destruct Hk as [_ _ Hkregs Hkresv Hktv Hkitv Hkhr].
  split.
  - constructor; try assumption.
    + intros c'. destruct (decide (c' = c)) as [->|Hne]; [exact Htv2|].
      rewrite (Hktv c' Hne). exact (Nat.le_trans _ _ _ (Htv c') Hlen).
    + intros c'. destruct (decide (c' = c)) as [->|Hne]; [exact Hitv2|].
      rewrite (Hkitv c' Hne). exact (Nat.le_trans _ _ _ (Hitv c') Hlen).
    + intros c'. destruct (decide (c' = c)) as [->|Hne]; [exact Hrv2|].
      rewrite (Hkhr c' Hne). exact (Nat.le_trans _ _ _ (Hrv c') Hlen).
    + intros c' a. destruct (decide (c' = c)) as [->|Hne]; [exact (Hcoh2 a)|].
      rewrite (Hkhr c' Hne). exact (Nat.le_trans _ _ _ (Hcoh c' a) Hlen).
  - constructor; cbn [cput cregs cmem cdev].
    + intros c'. destruct (decide (c' = c)) as [->|Hne].
      * rewrite greg_ins_eq. exact Hr2.
      * rewrite (greg_ins_ne _ c c' _ Hne). rewrite (Hkregs c' Hne). apply Hr.
    + exact Hm2.
    + exact Hd2.
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. ...AND SO IS A WHOLE SCHEDULE.                                       *)
(*                                                                         *)
(*    The pool is left abstract: all this needs is that every hart the     *)
(*    schedule names is IN it, at the uniform point.                       *)
(* ---------------------------------------------------------------------- *)

Lemma crun_nsteps (tick : bool) (gen : nat) (ts : list mexpr) :
  forall (sch : list CPU) (cs cs' : cstate) (g : gstate),
  (forall c, c ∈ sch -> HartE gen c (riscv_step tick) ∈ ts) ->
  thread_live g gen -> gs_ok g -> cs_ok cs g ->
  crun tick sch cs = Some cs' ->
  exists N g',
    @language.nsteps riscv_lang N (ts, g) [] (ts, g')
    /\ thread_live g' gen /\ gs_ok g' /\ cs_ok cs' g'.
Proof.
  induction sch as [|c sch IH]; intros cs cs' g Hin Hlive Hgs Hcs Hrun.
  - cbn [crun] in Hrun. revert Hrun; intros [= <-].
    exists 0%nat, g. split; [apply language.nsteps_refl|]. auto.
  - cbn [crun] in Hrun.
    destruct (cinstr tick c cs) as [cs1|] eqn:Hci; [|discriminate Hrun].
    assert (Hc : HartE gen c (riscv_step tick) ∈ ts)
      by (apply Hin; apply elem_of_list_here).
    apply elem_of_list_split in Hc as (t1 & t2 & Hts).
    destruct (cinstr_nsteps tick gen c t1 t2 cs cs1 g Hlive Hgs Hcs Hci)
      as (N1 & g1 & Hn1 & Hlv1 & Hgs1 & Hcs1).
    rewrite <- Hts in Hn1.
    destruct (IH cs1 cs' g1
                (fun c' Hc' => Hin c' (elem_of_list_further _ _ _ Hc'))
                Hlv1 Hgs1 Hcs1 Hrun) as (N2 & g2 & Hn2 & Hlv2 & Hgs2 & Hcs2).
    exists (N1 + N2)%nat, g2.
    split; [exact (nsteps_trans_nil _ _ _ _ _ Hn1 Hn2)|auto].
Qed.

Lemma cfinish_nsteps (tick : bool) (gen : nat) (ts : list mexpr)
    (round : list CPU) :
  (forall c, c ∈ round -> HartE gen c (riscv_step tick) ∈ ts) ->
  forall (n : nat) (cs cs' : cstate) (g : gstate),
  thread_live g gen -> gs_ok g -> cs_ok cs g ->
  cfinish tick round n cs = Some cs' ->
  exists N g',
    @language.nsteps riscv_lang N (ts, g) [] (ts, g')
    /\ thread_live g' gen /\ gs_ok g' /\ cs_ok cs' g'.
Proof.
  intros Hin n. induction n as [|n IH]; intros cs cs' g Hlive Hgs Hcs Hfin.
  - cbn [cfinish] in Hfin. destruct (cflag cs); [|discriminate Hfin].
    revert Hfin; intros [= <-].
    exists 0%nat, g. split; [apply language.nsteps_refl|]. auto.
  - cbn [cfinish] in Hfin. destruct (cflag cs).
    { revert Hfin; intros [= <-].
      exists 0%nat, g. split; [apply language.nsteps_refl|]. auto. }
    destruct (crun tick round cs) as [cs1|] eqn:Hrun; [|discriminate Hfin].
    destruct (crun_nsteps tick gen ts round cs cs1 g Hin Hlive Hgs Hcs Hrun)
      as (N1 & g1 & Hn1 & Hlv1 & Hgs1 & Hcs1).
    destruct (IH cs1 cs' g1 Hlv1 Hgs1 Hcs1 Hfin)
      as (N2 & g2 & Hn2 & Hlv2 & Hgs2 & Hcs2).
    exists (N1 + N2)%nat, g2.
    split; [exact (nsteps_trans_nil _ _ _ _ _ Hn1 Hn2)|auto].
Qed.


(* ---------------------------------------------------------------------- *)
(* 6. THE POOL.                                                            *)
(*                                                                         *)
(*    [power_fork] hands over every hart at [Ret tt]; the driver's uniform *)
(*    point is [riscv_step tick].  One boundary step per hart the schedule *)
(*    uses takes it there, and a boundary changes nothing the computation  *)
(*    can see -- it is the same [mstate] on both sides.                    *)
(* ---------------------------------------------------------------------- *)

Lemma loop_in_pool (gen : nat) (c : CPU) : LoopE gen c ∈ power_fork gen.
Proof.
  unfold power_fork. apply elem_of_app. left.
  apply elem_of_list_fmap. exists c. split; [reflexivity|apply finite.elem_of_enum].
Qed.

(* the two ends of an instruction are not the same node, which is what
   keeps an already-booted hart's thread out of the way of the next one *)
Lemma riscv_step_ne_ret (tick : bool) (u : unit) :
  riscv_step tick <> Interface.Ret u.
Proof. unfold riscv_step. discriminate. Qed.

Lemma elem_of_replace (x e e' : mexpr) (t1 t2 : list mexpr) :
  x ∈ t1 ++ e :: t2 -> x <> e -> x ∈ t1 ++ e' :: t2.
Proof.
  intros Hin Hne. apply elem_of_app in Hin as [H|H].
  - apply elem_of_app. by left.
  - apply elem_of_cons in H as [->|H]; [contradiction (Hne eq_refl)|].
    apply elem_of_app. right. apply elem_of_cons. by right.
Qed.

(* the boundary alone: one hart, [Ret tt] to [riscv_step tick], with the
   computation's state untouched *)
Lemma boot_one (tick : bool) (gen : nat) (c : CPU)
    (t1 t2 : list mexpr) (cs : cstate) (g : gstate) :
  thread_live g gen -> gs_ok g -> cs_ok cs g ->
  exists g',
    @language.nsteps riscv_lang 1
      (t1 ++ HartE gen c (Interface.Ret tt) :: t2, g) []
      (t1 ++ HartE gen c (riscv_step tick) :: t2, g')
    /\ thread_live g' gen /\ gs_ok g' /\ cs_ok cs g'.
Proof.
  intros Hlive Hgs Hcs.
  pose proof (cs_hart_ok cs g c Hgs Hcs) as Hok.
  destruct (boundary_prim tick gen c g (cfocus cs c) tt Hlive Hok)
    as (g1 & Hps1 & Hok1 & Hlv1 & Hres1 & Hk1).
  pose proof (log_len_le g g1 c Hk1) as Hlen.
  pose proof Hok1 as [Hr1 Hm1 Hd1 Hfl1 Hal1 Htv1 Hitv1 Hrv1 Hcoh1].
  pose proof Hgs as [Hfl Hres Htv Hitv Hrv Hcoh].
  pose proof Hcs as [Hr Hm Hd].
  cbn [cfocus sregs mem mdev] in Hr1, Hm1, Hd1.
  destruct Hk1 as [_ _ Hkr Hkv Hktv Hkitv Hkhr].
  exists g1. split.
  { apply (nsteps_l_nil 0%nat _ (t1 ++ HartE gen c (riscv_step tick) :: t2, g1));
      [exact (hstep_step gen c t1 t2 _ _ g g1 Hps1)
      |apply language.nsteps_refl]. }
  split; [exact Hlv1|]. split.
  - constructor; try assumption.
    + intros c'. destruct (decide (c' = c)) as [->|Hne]; [exact Htv1|].
      rewrite (Hktv c' Hne). exact (Nat.le_trans _ _ _ (Htv c') Hlen).
    + intros c'. destruct (decide (c' = c)) as [->|Hne]; [exact Hitv1|].
      rewrite (Hkitv c' Hne). exact (Nat.le_trans _ _ _ (Hitv c') Hlen).
    + intros c'. destruct (decide (c' = c)) as [->|Hne]; [exact Hrv1|].
      rewrite (Hkhr c' Hne). exact (Nat.le_trans _ _ _ (Hrv c') Hlen).
    + intros c' a. destruct (decide (c' = c)) as [->|Hne]; [exact (Hcoh1 a)|].
      rewrite (Hkhr c' Hne). exact (Nat.le_trans _ _ _ (Hcoh c' a) Hlen).
  - constructor.
    + intros c'. destruct (decide (c' = c)) as [->|Hne];
        [exact Hr1|rewrite (Hkr c' Hne); apply Hr].
    + exact Hm1.
    + exact Hd1.
Qed.

(* ...and the TWO harts a litmus test races.  Two rather than a fold over a
   list: every case in this suite is [smp=2], and the general version needs
   the harts to be distinct threads anyway -- which for two is just [c0 <>
   c1] and for a list is a [NoDup] that buys nothing here. *)
Lemma pool_boot2 (tick : bool) (gen : nat) (c0 c1 : CPU) (ts : list mexpr)
    (cs : cstate) (g : gstate) :
  c0 <> c1 ->
  thread_live g gen -> gs_ok g -> cs_ok cs g ->
  HartE gen c0 (Interface.Ret tt) ∈ ts ->
  HartE gen c1 (Interface.Ret tt) ∈ ts ->
  exists N ts' g',
    @language.nsteps riscv_lang N (ts, g) [] (ts', g')
    /\ thread_live g' gen /\ gs_ok g' /\ cs_ok cs g'
    /\ HartE gen c0 (riscv_step tick) ∈ ts'
    /\ HartE gen c1 (riscv_step tick) ∈ ts'.
Proof.
  intros Hne Hlive Hgs Hcs H0 H1.
  apply elem_of_list_split in H0 as (t1 & t2 & Hts). subst ts.
  destruct (boot_one tick gen c0 t1 t2 cs g Hlive Hgs Hcs)
    as (g1 & Hn1 & Hlv1 & Hgs1 & Hcs1).
  assert (H1' : HartE gen c1 (Interface.Ret tt)
                  ∈ t1 ++ HartE gen c0 (riscv_step tick) :: t2).
  { apply (elem_of_replace _ (HartE gen c0 (Interface.Ret tt)));
      [exact H1|intros Heq; congruence]. }
  apply elem_of_list_split in H1' as (u1 & u2 & Hts1).
  destruct (boot_one tick gen c1 u1 u2 cs g1 Hlv1 Hgs1 Hcs1)
    as (g2 & Hn2 & Hlv2 & Hgs2 & Hcs2).
  rewrite Hts1 in Hn1.
  exists (1 + 1)%nat, (u1 ++ HartE gen c1 (riscv_step tick) :: u2), g2.
  split; [exact (nsteps_trans_nil _ _ _ _ _ Hn1 Hn2)|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  split.
  - apply (elem_of_replace _ (HartE gen c1 (Interface.Ret tt))).
    + rewrite <- Hts1. apply elem_of_app. right. apply elem_of_list_here.
    + pose proof (riscv_step_ne_ret tick tt) as Hrs. intros Heq. congruence.
  - apply elem_of_app. right. apply elem_of_list_here.
Qed.

(* ---------------------------------------------------------------------- *)
(* 7. THE TEST'S OWN STARTING POINT.                                       *)
(*                                                                         *)
(*    [VRun.test_gstate] is the machine the theorem starts from; this is   *)
(*    what the driver computes from.  Every hart lands where ITS OWN boot  *)
(*    chain leaves it -- [cold_regs] is parametric in the hart id and the  *)
(*    gstate gives index [c] the id [hart + c] -- so a two-hart program    *)
(*    that reads [mhartid] to tell the harts apart sees what it sees on    *)
(*    the machine.                                                         *)
(* ---------------------------------------------------------------------- *)

Definition conc_start (hart : Z) (text : list Z) (rs : list region)
    (disk_init : list (Z * list Z)) : cstate :=
  CState (fun c => ColdBoot.cold_regs
                     (SailStdpp.Values.mword_of_int (hart + Z.of_nat (fin_to_nat c))))
         (mem_of text rs) (dev_of (img_of_sectors disk_init)).

Lemma gs_ok_test_gstate (hart : Z) (text : list Z) (rs : list region)
    (disk_init : list (Z * list Z)) :
  gs_ok (test_gstate hart text rs disk_init).
Proof.
  pose proof (hart_ok_test_start hart text rs disk_init)
    as [Hr Hm Hd Hfl Hal Htv Hitv Hrv Hcoh].
  constructor.
  - exact Hfl.
  - apply (all_resv_of_none _ hart_primary); [exact Hal|reflexivity].
  - intros c. exact Htv.
  - intros c. exact Hitv.
  - intros c. exact Hrv.
  - intros c a. exact (Hcoh a).
Qed.

Lemma cs_ok_conc_start (hart : Z) (text : list Z) (rs : list region)
    (disk_init : list (Z * list Z)) :
  cs_ok (conc_start hart text rs disk_init) (test_gstate hart text rs disk_init).
Proof. constructor; reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 8. THE FORM A GENERATED PROOF USES.                                     *)
(*                                                                         *)
(*    The named interleaving, then both harts to the DONE flag, then look  *)
(*    -- and the whole of it is one chain of [RiscvLang.prim_step]s from   *)
(*    [VRun.test_config].  The intermediate states are folded into a       *)
(*    MATCH so a generator writes down nothing but the schedule.           *)
(* ---------------------------------------------------------------------- *)

Definition conc_result (tick : bool) (sch round : list CPU) (n : nat)
    (hart : Z) (text : list Z) (rs : list region)
    (disk_init : list (Z * list Z)) : option cstate :=
  match crun tick sch (conc_start hart text rs disk_init) with
  | Some cs => cfinish tick round n cs
  | None => None
  end.

Theorem conc_shows (tick : bool) (c0 c1 : CPU) (sch round : list CPU) (n : nat)
    (hart : Z) (text : list Z) (rs : list region)
    (disk_init : list (Z * list Z)) (o : observation) :
  c0 <> c1 ->
  (forall c, c ∈ sch -> c = c0 \/ c = c1) ->
  (forall c, c ∈ round -> c = c0 \/ c = c1) ->
  match conc_result tick sch round n hart text rs disk_init with
  | Some cs => peek_mem cs.(cmem) result_base result_size = o.(o_result)
               /\ serial_of (Some (cfocus cs hart_primary)) = o.(o_uart)
               /\ v_disk (dvirtio cs.(cdev)) = disk_of_sectors o.(o_disk)
  | None => False
  end ->
  exists N l ts g,
    @language.nsteps riscv_lang N
      (test_config hart text rs disk_init) l (ts, g)
    /\ obs_in l = [] /\ observed_at g o.
Proof.
  intros Hne Hsch Hround.
  unfold conc_result.
  destruct (crun tick sch (conc_start hart text rs disk_init)) as [cs1|] eqn:Hrun;
    [|intros []].
  destruct (cfinish tick round n cs1) as [cs2|] eqn:Hfin; [|intros []].
  intros (Hres & Hser & Hdsk).
  assert (Hlive0 : thread_live (test_gstate hart text rs disk_init) 0)
    by (split; reflexivity).
  pose proof (gs_ok_test_gstate hart text rs disk_init) as Hgs0.
  pose proof (cs_ok_conc_start hart text rs disk_init) as Hcs0.
  (* 1. every hart the schedule uses, from [Ret tt] to the uniform point *)
  destruct (pool_boot2 tick 0 c0 c1 (power_fork 0)
              (conc_start hart text rs disk_init)
              (test_gstate hart text rs disk_init)
              Hne Hlive0 Hgs0 Hcs0 (loop_in_pool 0 c0) (loop_in_pool 0 c1))
    as (N0 & ts' & gb & Hn0 & Hlvb & Hgsb & Hcsb & Hin0 & Hin1).
  assert (Hin : forall c, c = c0 \/ c = c1 ->
                  HartE 0 c (riscv_step tick) ∈ ts')
    by (intros c Hc; destruct Hc as [Hc|Hc]; subst c; assumption).
  (* 2. the named interleaving *)
  destruct (crun_nsteps tick 0 ts' sch (conc_start hart text rs disk_init) cs1 gb
              (fun c Hc => Hin c (Hsch c Hc)) Hlvb Hgsb Hcsb Hrun)
    as (N1 & g1 & Hn1 & Hlv1 & Hgs1 & Hcs1).
  (* 3. ...and both harts to the flag *)
  destruct (cfinish_nsteps tick 0 ts' round
              (fun c Hc => Hin c (Hround c Hc)) n cs1 cs2 g1
              Hlv1 Hgs1 Hcs1 Hfin)
    as (N2 & g2 & Hn2 & Hlv2 & Hgs2 & Hcs2).
  exists (N0 + (N1 + N2))%nat, [], ts', g2.
  split.
  { unfold test_config.
    exact (nsteps_trans_nil _ _ _ _ _ Hn0
             (nsteps_trans_nil _ _ _ _ _ Hn1 Hn2)). }
  split; [reflexivity|].
  (* the observation, read off the hart that published it *)
  pose proof (cs_hart_ok cs2 g2 hart_primary Hgs2 Hcs2) as Hok2.
  apply (observed_at_of_hart_ok hart_primary g2 (cfocus cs2 hart_primary) o Hok2).
  - unfold result_of. cbn [cfocus mem]. exact Hres.
  - exact Hser.
  - cbn [cfocus mdev]. exact Hdsk.
Qed.

(* ---------------------------------------------------------------------- *)
(* 9. THE TWO-HART FORM, which is every case in this suite.                *)
(*                                                                         *)
(*    A schedule is a list of BITS rather than of harts -- [false] is the  *)
(*    first hart, [true] the second -- so "this schedule only names the    *)
(*    two harts the pool booted" holds by construction and a generated     *)
(*    proof carries no side conditions at all.                             *)
(* ---------------------------------------------------------------------- *)

Definition chart0 : CPU := 0%fin.
Definition chart1 : CPU := 1%fin.

Definition hof (b : bool) : CPU := if b then chart1 else chart0.
Definition csch (bs : list bool) : list CPU := hof <$> bs.

Lemma chart_ne : chart0 <> chart1.
Proof. discriminate. Qed.

Lemma csch_in (bs : list bool) (c : CPU) :
  c ∈ csch bs -> c = chart0 \/ c = chart1.
Proof.
  intros H. apply elem_of_list_fmap in H as (b & -> & _).
  destruct b; [by right|by left].
Qed.

Definition conc2_result (tick : bool) (bs : list bool) (n : nat)
    (hart : Z) (text : list Z) (rs : list region)
    (disk_init : list (Z * list Z)) : option cstate :=
  conc_result tick (csch bs) (csch [false; true]) n hart text rs disk_init.

Theorem conc2_shows (tick : bool) (bs : list bool) (n : nat)
    (hart : Z) (text : list Z) (rs : list region)
    (disk_init : list (Z * list Z)) (o : observation) :
  match conc2_result tick bs n hart text rs disk_init with
  | Some cs => peek_mem cs.(cmem) result_base result_size = o.(o_result)
               /\ serial_of (Some (cfocus cs hart_primary)) = o.(o_uart)
               /\ v_disk (dvirtio cs.(cdev)) = disk_of_sectors o.(o_disk)
  | None => False
  end ->
  exists N l ts g,
    @language.nsteps riscv_lang N
      (test_config hart text rs disk_init) l (ts, g)
    /\ obs_in l = [] /\ observed_at g o.
Proof.
  apply (conc_shows tick chart0 chart1 (csch bs) (csch [false; true]) n
           hart text rs disk_init o chart_ne
           (csch_in bs) (csch_in [false; true])).
Qed.
