(* ====================================================================== *)
(* VIcacheStep.v -- THE INSTRUCTION VIEW, against [RiscvLang.prim_step].   *)
(*                                                                         *)
(* [VConcStep] carries the relaxed DATA side: a load may read at a view    *)
(* below the top, which is store buffering.  The FETCH side is the other   *)
(* half of the same story and it is a different view: an instruction fetch *)
(* reads latest-visible TO THE ICACHE AGENT -- which authors nothing, so   *)
(* there is no forwarding -- at some view at or above the hart's           *)
(* INSTRUCTION view, and only [fence.i] raises that view.  A store over    *)
(* the hart's own code may therefore fetch as the OLD instruction until    *)
(* the next fence.i (claude-notes/design/icache.md).                       *)
(*                                                                         *)
(* WHY THIS FILE EXISTS.  [VTso]'s fetch reads the flat cache, which is    *)
(* the fetch at the TOP view -- the coherent choice, and the only one      *)
(* [VConcStep] can name.  Measured, core_icache's board capture is the     *)
(* OTHER one: the U74 answers 1 1 1 2 where a coherent icache answers      *)
(* 2 2 2 2, and 1 1 1 2 is an execution the model HAS.  Naming it needs    *)
(* the instruction view threaded, which is [VIcache.itexec]; this is its   *)
(* soundness lemma and the chain over it.                                  *)
(*                                                                         *)
(* ONE HART.  A self-modifying-code test races a hart against ITSELF, so   *)
(* there is no interleaving to name and no second hart to keep an          *)
(* invariant for.  What is threaded is the era image, the log and the two  *)
(* views.                                                                  *)
(* ====================================================================== *)
From Stdlib Require Import List ZArith Lia.
From stdpp Require Import base list gmap functions relations bitvector.definitions.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvExec VirtioModel DevModel ColdBoot.
Require Import RiscvLang TsoMemPa.
From VTest Require Import VTest VRun VTso VExecStep VConcStep VIcache.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. ONE NODE OF THE FETCH-AWARE INTERPRETER IS ONE [mnode_step].         *)
(*                                                                         *)
(*    [VConcStep.tnode_mnode] with the instruction view threaded.  The     *)
(*    difference is one arm: the FETCH.  [IFresh] reads the flat cache,    *)
(*    which is the fetch at the top ([tso_read_top_flat] holds for every   *)
(*    agent, the icache's included); [IStale] reads AT the instruction     *)
(*    view with the icache's own agent, which is the lowest the arm        *)
(*    admits.  [itv'] is COMPUTED here rather than chosen, because         *)
(*    [fence.i] is what moves it and [inode] already says how -- which is  *)
(*    why the FENCE needs no arm of its own here: [inode] computes exactly *)
(*    the witness [mnode_step] names, so the generic tactic closes it.     *)
(* ---------------------------------------------------------------------- *)

Lemma inode_mnode (ip : ipol) (cpu : CPU) (g : gstate) (s : mstate)
    (m m' : M unit) (s' : mstate) (log' : list pwmsg) (tv' itv' : nat)
    (hr' : hread) :
  hart_ok cpu g s ->
  inode ip (hart_agent cpu) g.(gimg) s g.(glog) (g.(gtv) cpu) (g.(gitv) cpu)
        (g.(ghr) cpu) m
    = Some (m', s', log', tv', itv', hr') ->
  exists r',
    mnode_step (others_resv g.(gresv) cpu) (hart_agent cpu) g.(gimg)
      s g.(glog) (g.(gtv) cpu) (g.(gitv) cpu) (g.(ghr) cpu) (g.(gresv) cpu)
      m m' s' log' tv' itv' hr' r'
    /\ hart_ok cpu (wb cpu g s' log' tv' itv' hr' r') s'.
Proof.
  intros Hok Hn.
  pose proof Hok as [Hr Hm Hd Hfl Hal Htv Hitv Hrv Hcoh].
  destruct m as [y|T oc k]; [discriminate Hn|].
  destruct oc; cbn [inode] in Hn;
    first
      [ discriminate Hn
      | revert Hn; intros [= <- <- <- <- <- <-];
        exists (g.(gresv) cpu);
        split;
          [ cbn [mnode_step]; repeat split; reflexivity
          | apply (hart_ok_wb_same cpu g s _); try exact Hok;
            try (cbn; reflexivity); tso_bounds ]
      | idtac ].
  (* --- A LOAD ------------------------------------------------------ *)
  - destruct (dev_addr (Interface.ReadReq.pa t)) eqn:Hda.
    + destruct (dev_read (mdev s) (Interface.ReadReq.pa t) n) as [[w d']|] eqn:Hdr;
        [|discriminate Hn].
      revert Hn; intros [= <- <- <- <- <- <-].
      exists (g.(gresv) cpu).
      split.
      * cbn [mnode_step]. rewrite Hda. exists w, d'.
        repeat split; first [ exact Hdr | reflexivity ].
      * apply (hart_ok_wb_same cpu g s _); try exact Hok;
          try (cbn; reflexivity); tso_bounds.
    + destruct (ak_ifetch (Interface.ReadReq.access_kind t)) eqn:Hif.
      * (* THE FETCH, and the whole point of the file *)
        destruct ip.
        -- (* IFresh: the flat cache IS the fetch at the top view *)
           destruct (read_bytes (mem s) (Interface.ReadReq.pa t) n) as [w|] eqn:Hrb;
             [|discriminate Hn].
           revert Hn; intros [= <- <- <- <- <- <-].
           exists (g.(gresv) cpu).
           split.
           ++ cbn [mnode_step]. rewrite Hda. left. split; [exact Hif|].
              exists (length g.(glog)), w.
              repeat split;
                first [ assumption | reflexivity | apply Nat.le_refl
                      | intros j Hj; rewrite tso_read_top_flat, <- Hfl, Hm;
                        exact (read_bytes_spec _ _ _ _ Hrb j Hj) ].
           ++ apply (hart_ok_wb_same cpu g s _); try exact Hok;
                try (cbn; reflexivity); tso_bounds.
        -- (* IStale: AT the instruction view, with the icache's agent --
              nothing stored since the last fence.i is visible to it *)
           destruct (tso_read_bytes_f g.(gimg) g.(glog) (ifetch_agent (hart_agent cpu))
                       (g.(gitv) cpu) (Interface.ReadReq.pa t) n) as [w|] eqn:Hrb;
             [|discriminate Hn].
           revert Hn; intros [= <- <- <- <- <- <-].
           exists (g.(gresv) cpu).
           split.
           ++ cbn [mnode_step]. rewrite Hda. left. split; [exact Hif|].
              exists (g.(gitv) cpu), w.
              repeat split;
                first [ assumption | reflexivity | apply Nat.le_refl
                      | intros j Hj;
                        exact (tso_read_bytes_f_spec _ _ _ _ _ _ _ Hrb j Hj) ].
           ++ apply (hart_ok_wb_same cpu g s _); try exact Hok;
                try (cbn; reflexivity); tso_bounds.
      * destruct (ak_excl (Interface.ReadReq.access_kind t)) eqn:Hex.
        -- (* THE EXCLUSIVE READ *)
           destruct (read_bytes (mem s) (Interface.ReadReq.pa t) n) as [w|] eqn:Hrb;
             [|discriminate Hn].
           revert Hn; intros [= <- <- <- <- <- <-].
           exists (Some (snap_of (Interface.ReadReq.pa t) n w)).
           split.
           ++ cbn [mnode_step]. rewrite Hda. right. right.
              split; [exact Hex|]. right.
              split; [rewrite Hal; set_solver|].
              exists w. repeat split;
                first [ reflexivity
                      | intros j Hj; exact (read_bytes_spec _ _ _ _ Hrb j Hj) ].
           ++ apply (hart_ok_wb_same cpu g s _); try exact Hok;
                try (cbn; reflexivity); tso_bounds.
        -- (* THE PLAIN DATA READ, at the top: the hart is alone in its era *)
           destruct (read_bytes (mem s) (Interface.ReadReq.pa t) n) as [w|] eqn:Hrb;
             [|discriminate Hn].
           revert Hn; intros [= <- <- <- <- <- <-].
           exists (g.(gresv) cpu).
           split.
           ++ cbn [mnode_step]. rewrite Hda. right. left.
              split; [exact Hif|]. split; [exact Hex|].
              exists (length g.(glog)), w.
              repeat split;
                first [ assumption | reflexivity | apply Nat.le_refl
                      | intros j Hj; apply Hcoh
                      | intros j Hj; rewrite tso_read_top_flat, <- Hfl, Hm;
                        exact (read_bytes_spec _ _ _ _ Hrb j Hj) ].
           ++ apply (hart_ok_wb_same cpu g s _); try exact Hok;
                try (cbn; reflexivity); tso_bounds.
  (* --- A STORE ----------------------------------------------------- *)
  - destruct (dev_addr (Interface.WriteReq.pa t)) eqn:Hda.
    + destruct (dev_write (mdev s) (Interface.WriteReq.pa t) n
                          (Interface.WriteReq.value t)) as [d'|] eqn:Hdw;
        [|discriminate Hn].
      revert Hn; intros [= <- <- <- <- <- <-].
      exists None.
      split.
      * cbn [mnode_step]. rewrite Hda. exists d'.
        repeat split; first [ exact Hdw | reflexivity ].
      * apply (hart_ok_wb_same cpu g s _); try exact Hok;
          try (cbn; reflexivity); tso_bounds.
    + revert Hn; intros [= <- <- <- <- <- <-].
      exists None.
      split.
      * cbn [mnode_step]. rewrite Hda. right.
        split; [rewrite Hal; set_solver|].
        repeat split; reflexivity.
      * apply hart_ok_wb; try assumption.
        -- cbn [mem].
           assert (Hms : mem s = flat (gimg g) (glog g))
             by (rewrite <- Hm; exact Hfl).
           symmetry. rewrite Hms. unfold snap_of. apply flat_store.
        -- unfold write_tv. rewrite length_app. cbn [length].
           apply if_le; [apply if_le|]; lia.
        -- rewrite length_app. cbn [length]. lia.
        -- unfold hr_clear; cbn [hr_rv]. rewrite length_app. cbn [length]. lia.
        -- intros a. unfold hr_clear; cbn [hr_coh]. specialize (Hcoh a).
           rewrite length_app. cbn [length]. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE STATE, AND WHAT IT MEANS.                                        *)
(*                                                                         *)
(*    [VIcache.istate] is already the right record -- the machine, the     *)
(*    log and the two views -- so this is only the invariant tying it to   *)
(*    a [gstate] at the primary.                                           *)
(* ---------------------------------------------------------------------- *)

Record is_ok (img : gmap Arch.pa (bv 8)) (st : istate) (g : gstate) : Prop := IsOk {
  is_hart : hart_ok hart_primary g st.(i_s);
  (* NO [all_resv = ∅] here.  A node-level invariant cannot have it -- an
     exclusive read holds a reservation until the instruction boundary --
     and it is not needed: with one hart, [others_resv] is the union over
     the harts that never step, which [hart_ok]'s own [ho_alone] carries. *)
  is_img  : g.(gimg) = img;
  is_log  : g.(glog) = st.(i_log);
  is_tv   : g.(gtv) hart_primary = st.(i_tv);
  is_itv  : g.(gitv) hart_primary = st.(i_itv);
  is_hr   : g.(ghr) hart_primary = st.(i_hr);
}.

(* one node at a time to the instruction boundary; the boundary itself is a
   [prim_step] of its own ([boundary_prim]), so this stops at [Ret] without
   clearing the acquire bit and [iinstr] applies its effect after *)
Fixpoint irun_n (fuel : nat) (ip : ipol) (h : agent)
    (img : gmap Arch.pa (bv 8)) (m : M unit) (s : mstate)
    (log : list pwmsg) (tv itv : nat) (hr : hread) {struct fuel}
  : option (mstate * list pwmsg * nat * nat * hread) :=
  match m with
  | Interface.Ret _ => Some (s, log, tv, itv, hr)
  | _ =>
      match fuel with
      | 0%nat => None
      | S f =>
          match inode ip h img s log tv itv hr m with
          | Some (m', s', log', tv', itv', hr') =>
              irun_n f ip h img m' s' log' tv' itv' hr'
          | None => None
          end
      end
  end.

Definition iinstr (ip : ipol) (fuel : nat) (tick : bool)
    (img : gmap Arch.pa (bv 8)) (st : istate) : option istate :=
  match irun_n fuel ip (hart_agent hart_primary) img (riscv_step tick)
               st.(i_s) st.(i_log) st.(i_tv) st.(i_itv) st.(i_hr) with
  | Some (s', log', tv', itv', hr') =>
      Some (IState s' log' tv' itv' (hr_clear hr'))
  | None => None
  end.

Fixpoint ifin (ip : ipol) (fuel : nat) (tick : bool)
    (img : gmap Arch.pa (bv 8)) (n : nat) (st : istate) : option istate :=
  if flag_set st.(i_s) then Some st else
  match n with
  | 0%nat => None
  | S n' => match iinstr ip fuel tick img st with
            | Some st' => ifin ip fuel tick img n' st'
            | None => None
            end
  end.

(* ---------------------------------------------------------------------- *)
(* 3. ...AND THE CHAIN.                                                    *)
(* ---------------------------------------------------------------------- *)

Lemma irun_hstep (ip : ipol) (gen : nat) (fuel : nat) :
  forall (m : M unit) (g : gstate) (img : gmap Arch.pa (bv 8)) (st : istate)
         (s' : mstate) (log' : list pwmsg) (tv' itv' : nat) (hr' : hread),
  thread_live g gen -> is_ok img st g ->
  irun_n fuel ip (hart_agent hart_primary) img m st.(i_s) st.(i_log)
         st.(i_tv) st.(i_itv) st.(i_hr) = Some (s', log', tv', itv', hr') ->
  exists g',
    rtc (hstep gen hart_primary) (m, g) (Interface.Ret tt, g')
    /\ thread_live g' gen /\ hart_ok hart_primary g' s'
    /\ g'.(gimg) = g.(gimg) /\ g'.(glog) = log'
    /\ g'.(gtv) hart_primary = tv' /\ g'.(gitv) hart_primary = itv'
    /\ g'.(ghr) hart_primary = hr'.
Proof.
  induction fuel as [|f IH];
    intros m g img st s' log' tv' itv' hr' Hlive Hst Ht;
    pose proof Hst as [Hok Himg Hlog Htv Hitv Hhr].
  - destruct m as [y|T oc k]; cbn [irun_n] in Ht; [|discriminate Ht].
    revert Ht; intros [= <- <- <- <- <-]. destruct y.
    exists g. split; [apply rtc_refl|].
    split; [assumption|]. split; [exact Hok|].
    rewrite Hlog, Htv, Hitv, Hhr. repeat split.
  - destruct m as [y|T oc k]; cbn [irun_n] in Ht.
    { revert Ht; intros [= <- <- <- <- <-]. destruct y.
      exists g. split; [apply rtc_refl|].
      split; [assumption|]. split; [exact Hok|].
      rewrite Hlog, Htv, Hitv, Hhr. repeat split. }
    rewrite <- Hlog, <- Htv, <- Hitv, <- Hhr, <- Himg in Ht.
    destruct (inode ip (hart_agent hart_primary) g.(gimg) st.(i_s) g.(glog)
                (g.(gtv) hart_primary) (g.(gitv) hart_primary)
                (g.(ghr) hart_primary) (Interface.Next oc k))
      as [[[[[[m1 s1] log1] tv1] itv1] hr1]|] eqn:Hn; [|discriminate Ht].
    destruct (inode_mnode ip hart_primary g st.(i_s) (Interface.Next oc k)
                m1 s1 log1 tv1 itv1 hr1 Hok Hn) as (r1 & Hnode & Hok1).
    rewrite <- (hart_ok_proj hart_primary g st.(i_s) Hok) in Hnode.
    pose proof (mnode_prim gen hart_primary g (Interface.Next oc k) m1 s1 log1
                  tv1 itv1 hr1 r1 Hlive Hnode) as Hps.
    set (g1 := wb hart_primary g s1 log1 tv1 itv1 hr1 r1) in *.
    assert (Hlv1 : thread_live g1 gen)
      by (unfold thread_live, g1, wb in *; cbn [gpow ggen] in *; exact Hlive).
    assert (Hst1 : is_ok img (IState s1 log1 tv1 itv1 hr1) g1).
    { constructor; cbn [i_s i_log i_tv i_itv i_hr];
        unfold g1, wb; cbn [gregs gmem gdev ggen gpow gresv gimg glog gtv gitv ghr].
      - exact Hok1.
      - exact Himg.
      - reflexivity.
      - apply gtv_ins_eq.
      - apply gtv_ins_eq.
      - apply ghr_ins_eq. }
    rewrite Himg in Ht.
    destruct (IH m1 g1 img (IState s1 log1 tv1 itv1 hr1) s' log' tv' itv' hr'
                Hlv1 Hst1 Ht) as (g' & Hrtc & Hlv' & Hok' & Hi' & Hl' & Hv' & Hiv' & Hh').
    exists g'. split.
    { assert (Hstep1 : hstep gen hart_primary (Interface.Next oc k, g) (m1, g1))
        by (unfold hstep; cbn [fst snd]; exact Hps).
      eapply rtc_l; [exact Hstep1|exact Hrtc]. }
    split; [assumption|]. split; [assumption|].
    split; [rewrite Hi'; unfold g1, wb; reflexivity|].
    split; [exact Hl'|]. split; [exact Hv'|]. split; [exact Hiv'|exact Hh'].
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. ONE INSTRUCTION, AND THEN THE WHOLE RUN.                             *)
(*                                                                         *)
(*    An item is the instruction AND the boundary after it, as in          *)
(*    [VConcStep]: the boundary is where the pending acquire is consumed,  *)
(*    and it moves neither view.                                           *)
(* ---------------------------------------------------------------------- *)

Lemma iinstr_nsteps (ip : ipol) (fuel : nat) (tick : bool) (gen : nat)
    (t1 t2 : list mexpr) (img : gmap Arch.pa (bv 8))
    (st st' : istate) (g : gstate) :
  thread_live g gen -> is_ok img st g ->
  iinstr ip fuel tick img st = Some st' ->
  exists N g',
    @language.nsteps riscv_lang N
      (t1 ++ HartE gen hart_primary (riscv_step tick) :: t2, g) []
      (t1 ++ HartE gen hart_primary (riscv_step tick) :: t2, g')
    /\ thread_live g' gen /\ is_ok img st' g'.
Proof.
  intros Hlive Hst Hi.
  pose proof Hst as [Hok Himg Hlog Htv Hitv Hhr].
  unfold iinstr in Hi.
  destruct (irun_n fuel ip (hart_agent hart_primary) img (riscv_step tick)
              st.(i_s) st.(i_log) st.(i_tv) st.(i_itv) st.(i_hr))
    as [[[[[s1 log1] tv1] itv1] hr1]|] eqn:Hr; [|discriminate Hi].
  revert Hi; intros [= <-].
  destruct (irun_hstep ip gen fuel (riscv_step tick) g img st s1 log1 tv1 itv1 hr1
              Hlive Hst Hr)
    as (g1 & Hrtc & Hlv1 & Hok1 & Hi1 & Hl1 & Hv1 & Hiv1 & Hh1).
  destruct (hstep_nsteps gen hart_primary t1 t2 (riscv_step tick, g)
              (Interface.Ret tt, g1) Hrtc) as [N1 Hn1]; cbn [fst snd] in Hn1.
  destruct (boundary_prim tick gen hart_primary g1 s1 tt Hlv1 Hok1)
    as (g2 & Hps2 & Hok2 & Hlv2 & Hres2 & Hk2 & Hbl & Hbv & Hbiv & Hbh).
  exists (N1 + 1)%nat, g2.
  split.
  { eapply nsteps_trans_nil; [exact Hn1|].
    apply (nsteps_l_nil 0%nat _
             (t1 ++ HartE gen hart_primary (riscv_step tick) :: t2, g2));
      [exact (hstep_step gen hart_primary t1 t2 _ _ g1 g2 Hps2)
      |apply language.nsteps_refl]. }
  split; [exact Hlv2|].
  constructor; cbn [i_s i_log i_tv i_itv i_hr].
  - exact Hok2.
  - (* the boundary is a write-back at this hart: the era image stands *)
    destruct Hk2 as [_ Hkimg _ _ _ _ _]. rewrite Hkimg, Hi1. exact Himg.
  - rewrite Hbl. exact Hl1.
  - rewrite Hbv. exact Hv1.
  - rewrite Hbiv. exact Hiv1.
  - rewrite Hbh. unfold hr_clear. rewrite Hh1. reflexivity.
Qed.

Lemma ifin_nsteps (ip : ipol) (fuel : nat) (tick : bool) (gen : nat)
    (ts : list mexpr) (img : gmap Arch.pa (bv 8)) :
  HartE gen hart_primary (riscv_step tick) ∈ ts ->
  forall (n : nat) (st st' : istate) (g : gstate),
  thread_live g gen -> is_ok img st g ->
  ifin ip fuel tick img n st = Some st' ->
  exists N g',
    @language.nsteps riscv_lang N (ts, g) [] (ts, g')
    /\ thread_live g' gen /\ is_ok img st' g'.
Proof.
  intros Hin n. apply elem_of_list_split in Hin as (t1 & t2 & Hts).
  induction n as [|n IH]; intros st st' g Hlive Hst Hf.
  - cbn [ifin] in Hf. destruct (flag_set st.(i_s)); [|discriminate Hf].
    revert Hf; intros [= <-].
    exists 0%nat, g. split; [apply language.nsteps_refl|]. auto.
  - cbn [ifin] in Hf. destruct (flag_set st.(i_s)).
    { revert Hf; intros [= <-].
      exists 0%nat, g. split; [apply language.nsteps_refl|]. auto. }
    destruct (iinstr ip fuel tick img st) as [st1|] eqn:Hi; [|discriminate Hf].
    destruct (iinstr_nsteps ip fuel tick gen t1 t2 img st st1 g Hlive Hst Hi)
      as (N1 & g1 & Hn1 & Hlv1 & Hst1).
    rewrite <- Hts in Hn1.
    destruct (IH st1 st' g1 Hlv1 Hst1 Hf) as (N2 & g2 & Hn2 & Hlv2 & Hst2).
    exists (N1 + N2)%nat, g2.
    split; [exact (nsteps_trans_nil _ _ _ _ _ Hn1 Hn2)|auto].
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. THE FORM A GENERATED PROOF USES.                                     *)
(*                                                                         *)
(*    The era begins with an EMPTY log, so both views start at 0 -- which  *)
(*    is why an [IStale] fetch reads the era image, i.e. the code as it    *)
(*    was LOADED, however many times the program has since stored over it. *)
(*    Only [fence.i] moves the instruction view off 0.                     *)
(* ---------------------------------------------------------------------- *)

Definition icache_start (hart : Z) (text : list Z) (rs : list region)
    (disk_init : list (Z * list Z)) : istate :=
  IState (exec_start hart text rs disk_init) [] 0%nat 0%nat hread0.

Definition icache_result (ip : ipol) (tick : bool) (n : nat)
    (hart : Z) (text : list Z) (rs : list region)
    (disk_init : list (Z * list Z)) : option istate :=
  ifin ip node_fuel tick (mem_of text rs) n
       (icache_start hart text rs disk_init).

Theorem icache_shows (ip : ipol) (tick : bool) (n : nat)
    (hart : Z) (text : list Z) (rs : list region)
    (disk_init : list (Z * list Z)) (o : observation) :
  match icache_result ip tick n hart text rs disk_init with
  | Some st => peek_mem (mem st.(i_s)) result_base result_size = o.(o_result)
               /\ serial_of (Some st.(i_s)) = o.(o_uart)
               /\ disk_at (v_disk (dvirtio (mdev st.(i_s)))) o.(o_disk)
  | None => False
  end ->
  exists N l ts g,
    @language.nsteps riscv_lang N
      (test_config hart text rs disk_init) l (ts, g)
    /\ obs_in l = [] /\ observed_at g o.
Proof.
  unfold icache_result.
  destruct (ifin ip node_fuel tick (mem_of text rs) n
              (icache_start hart text rs disk_init)) as [st2|] eqn:Hfin;
    [|intros []].
  intros (Hres & Hser & Hdsk).
  assert (Hlive0 : thread_live (test_gstate hart text rs disk_init) 0)
    by (split; reflexivity).
  assert (Hst0 : is_ok (mem_of text rs) (icache_start hart text rs disk_init)
                       (test_gstate hart text rs disk_init)).
  { constructor; cbn [icache_start i_s i_log i_tv i_itv i_hr];
      try reflexivity. exact (hart_ok_test_start hart text rs disk_init). }
  pose proof Hst0 as [Hok0 _ _ _ _ _].
  (* the pool hands the hart over at [Ret tt]; one boundary takes it to the
     uniform point, and moves neither view *)
  pose proof (loop_in_pool 0 hart_primary) as Hlp.
  apply elem_of_list_split in Hlp as (t1 & t2 & Hts).
  assert (Hpool : HartE 0 hart_primary (riscv_step tick)
                    ∈ t1 ++ HartE 0 hart_primary (riscv_step tick) :: t2)
    by (apply elem_of_app; right; apply elem_of_list_here).
  destruct (boundary_prim tick 0 hart_primary
              (test_gstate hart text rs disk_init)
              (exec_start hart text rs disk_init) tt Hlive0 Hok0)
    as (gb & Hpsb & Hokb & Hlvb & Hresb & Hkb & Hbl & Hbv & Hbiv & Hbh).
  assert (Hstb : is_ok (mem_of text rs) (icache_start hart text rs disk_init) gb).
  { destruct Hkb as [_ Hkimg _ _ _ _ _].
    constructor; cbn [icache_start i_s i_log i_tv i_itv i_hr].
    - exact Hokb.
    - rewrite Hkimg. reflexivity.
    - rewrite Hbl. reflexivity.
    - rewrite Hbv. reflexivity.
    - rewrite Hbiv. reflexivity.
    - rewrite Hbh. reflexivity. }
  destruct (ifin_nsteps ip node_fuel tick 0
              (t1 ++ HartE 0 hart_primary (riscv_step tick) :: t2)
              (mem_of text rs)
              Hpool n
              (icache_start hart text rs disk_init) st2 gb Hlvb Hstb Hfin)
    as (N2 & g2 & Hn2 & Hlv2 & Hst2).
  exists (1 + N2)%nat, [],
         (t1 ++ HartE 0 hart_primary (riscv_step tick) :: t2), g2.
  split.
  { unfold test_config. rewrite Hts.
    apply (nsteps_trans_nil 1%nat N2 _
             (t1 ++ HartE 0 hart_primary (riscv_step tick) :: t2, gb));
      [|exact Hn2].
    apply (nsteps_l_nil 0%nat _
             (t1 ++ HartE 0 hart_primary (riscv_step tick) :: t2, gb));
      [exact (hstep_step 0 hart_primary t1 t2 _ _ _ gb Hpsb)
      |apply language.nsteps_refl]. }
  split; [reflexivity|].
  pose proof Hst2 as [Hok2 _ _ _ _ _].
  apply (observed_at_of_hart_ok hart_primary g2 st2.(i_s) o Hok2).
  - unfold result_of. exact Hres.
  - exact Hser.
  - exact Hdsk.
Qed.
