(* HartEvents.v -- the per-memory-event WP rules, item 2 of the proof
   interface (claude-notes/design/main-cycle-port.md §5): one rule per event
   class -- RAM read (plain and EXCLUSIVE), RAM write, MMIO read, MMIO
   write.  (The pinned-text fetch rule is a later derived specialization of
   [wp_hart_ram_read].)

   THE RESERVATION (design §3a) shows up in exactly two ways here, and both
   are INSIDE the proofs, not in the statements: a RAM write or an exclusive
   read whose footprint meets another hart's reservation SELF-LOOPS, and the
   rule absorbs that arm by Löb (the caller's premise is untouched on that
   arm, so the IH applies verbatim); and the caller learns nothing about the
   hart's own reservation from these rules -- [wp_hart_step] ∀-quantifies
   it -- which is right until the conditional-write rule that will need the
   [resv_frag].  The exclusive-read rule below therefore has the SAME
   statement as the plain one; what differs is only which language arm it
   takes.

   THE CURRENCY IS TODAY'S: each rule hands the caller a fupd σ-callback
   with [mstate_interp], exactly as [wp_exec_step] did, so the points-to /
   invariant reasoning happens with the same bridges the existing leaves use
   ([mem_valid], [text_valid], [phys_valid], the gen_heap update lemmas).
   What each rule internalizes is the per-node successor INVERSION: the
   caller's witness pins the machine's one successor, so the continuation is
   stated at the resumed cursor ([hread_resume]/[hwrite_resume]) and never
   at a ∀-quantified next state.

   Each rule takes its node's PROJECTION fact ([hread_req_at]/[hwrite_req_at]
   = Some req) rather than a syntactic [Interface.Next ... K] hypothesis --
   the finding-F8 discipline: no call site ever writes a continuation down. *)
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift.
Require VirtioQueue.   (* [write_bytes_lookup]: the snapshot's per-byte hits *)
(* [tso_read_bytes] (the plain load's obligation) and [view_lb] (the
   receipt).  Import is not transitive.  NOTE what is NOT used from
   [TsoCtx] here: the receipt is stated at the MACHINE level
   ([TsoGhost.view_lb] at the era's names), and [TsoCtx.hart_view_lb] is the
   Σ-surface wrapper over it -- tso-machine-flip.md §6 amendment A6.6. *)
Require Import TsoMemPa TsoGhost.
Require Import TsoCtx.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* THE SNAPSHOT BRIDGE (design §3a): a reservation whose snapshot still     *)
(* agrees with memory ([resv_ok], handed over by [wp_hart_step_resv]) pins  *)
(* the word the conditional write finds -- it is the word the exclusive     *)
(* read returned.  The width bound is what rules out aliasing inside the    *)
(* footprint ([pa_add] wraps at 2^64); every real access is ≤ 16 bytes.     *)
(* ---------------------------------------------------------------------- *)
Lemma snap_of_read_bytes (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
    (w : bv (8 * n)) :
  Z.of_N n < 18446744073709551616 ->
  snap_of pa n w ⊆ mm ->
  read_bytes mm pa n = Some w.
Proof.
  intros Hn Hsub.
  assert (Hbytes : forall j : nat, (N.of_nat j < n)%N ->
            mm !! pa_add pa j = Some (nth_byte w j)).
  { intros j Hj.
    pose proof (VirtioQueue.write_bytes_lookup ∅ pa n w j Hn Hj) as Hhit.
    eapply map_subseteq_spec; [exact Hsub|exact Hhit]. }
  destruct (read_bytes mm pa n) as [w'|] eqn:Hrb.
  - f_equal. apply bv_eq_of_bytes. intros j Hj.
    pose proof (read_bytes_spec _ _ _ _ Hrb j Hj) as H0.
    pose proof (Hbytes j Hj) as H1.
    rewrite H0 in H1. apply Some_inj in H1. exact H1.
  - exfalso. revert Hrb. unfold read_bytes.
    case_match eqn:Hm; [congruence|]. intros _.
    apply stdpp.list_monad.mapM_None_1, List.Exists_exists in Hm.
    destruct Hm as (j & Hj & Hnone).
    apply List.in_seq in Hj.
    assert (Hjn : (N.of_nat j < n)%N) by lia.
    rewrite (Hbytes j Hjn) in Hnone. congruence.
Qed.

(* THE STORE'S VIEW MOVE (tso-machine-flip.md §2), spelled once so the two
   write rules share their shape and their receipt: a PLAIN store does NOT
   move the author's view -- that is store buffering, and advancing it would
   forbid SB -- while the AMO / conditional half takes the view PAST its own
   append ("the drain includes my write"). *)
Definition wstore_tv (ak : Interface.accessKind) (log : list pwmsg)
    (tv : nat) : nat :=
  if ak_excl ak then S (length log) else tv.

(* [vstep] at the hart it moved: the premise [tso_interp_of_receipt_at] wants
   when the plain read mints its receipt (A6.47 ruling 2). *)
Lemma vstep_here (h : agent) (t : nat) (log : list pwmsg) (V : agent -> nat) :
  vstep h t log V h = t.
Proof. rewrite /vstep. case_decide as Hd; [reflexivity | congruence]. Qed.

Section events.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* ------------------------------------------------------------------ *)
  (* THE STRONGLY-ORDERED RAM READ RULE IS GONE (RULING 1 overruled by the *)
  (* owner, 2026-08-26).  It was §6's [Mobl_ram] -- a FLAT [read_bytes]    *)
  (* obligation with no view advance -- and it was proven from the         *)
  (* machine's strong RAM-read arm, which no longer exists: every          *)
  (* non-exclusive read, implicit ones included, now takes the plain arm.  *)
  (* It is NOT a derivable special case of the plain rule (a flat cell     *)
  (* says nothing about what a view below the top sees), so it is deleted  *)
  (* rather than deprecated.  Its instances -- the M-, S- and U-mode fetch *)
  (* lanes and the PTE reads -- move to [wp_hart_ram_read_plain] and       *)
  (* discharge [Mobl_ram_plain] from the PRISTINE tier (kernel text and    *)
  (* boot-built PT mappings are timestamp-0 and read the same at every     *)
  (* view), from store forwarding (a hart's own PT writes), or from the    *)
  (* ctx tier (the user lanes).  The de-confliction project that wants a   *)
  (* real strong arm back will restore this rule together with the parked  *)
  (* Sail patch; see the flip note's rewritten RULING 1.                   *)
  (* ------------------------------------------------------------------ *)


  (* ------------------------------------------------------------------ *)
  (* ------------------------------------------------------------------ *)
  (* THE VALUE-AFTER-VIEW PLAIN READ (tso-pin-memo.md §0, ruling 1).      *)
  (*                                                                     *)
  (* The rule above quantifies ONE [w] good at EVERY reachable view.      *)
  (* That is FALSE of the machine wherever a completed write sits above   *)
  (* the reader's view -- the Svadu A/D write-back is exactly that case:  *)
  (* a reader below the write-back's timestamp reads the OLD word and one *)
  (* above it reads the NEW one, two values, one existential.  So the     *)
  (* obligation has to move INSIDE the ∀ [tv'], and what the caller pins  *)
  (* is a PREDICATE [P] rather than a value.                             *)
  (*                                                                     *)
  (* This is A6.47 ruling 2's move made once more -- parameterise the     *)
  (* continuation -- and it costs the same: the eleven existing call      *)
  (* sites of the pair above do not move, because the old rule is         *)
  (* RE-DERIVED from this one (below) by the byte-wise determinism step   *)
  (* that used to sit in its proof.                                      *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_hart_ram_read_plain_ex {X : Type} (C : M X -> M unit)
      (n : N) (req : Interface.ReadReq.t n) (m : M X)
      (P : bv (8 * n) -> Prop) :
    mctx C ->
    hread_req_at n m = Some req ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_excl (Interface.ReadReq.access_kind req) = false ->
    gen_cert -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
       ⌜∀ tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
          ∃ w : bv (8 * n),
            tso_read_bytes img log (hart_agent cpu_id) tv'
              (Interface.ReadReq.pa req) n w ∧ P w⌝ ∗
       ▷ (|={∅,⊤}=> mstate_interp σ ∗
            tso_interp_of riscv_eraGS img σ.(mem) log V ∗
            (∀ (tvn : nat) (w : bv (8 * n)),
               ⌜(tv <= tvn)%nat⌝ -∗ ⌜(tvn <= length log)%nat⌝ -∗
               ⌜tso_read_bytes img log (hart_agent cpu_id) tvn
                  (Interface.ReadReq.pa req) n w⌝ -∗
               ⌜P w⌝ -∗
               view_lb view_name loglen_name (hart_agent cpu_id) tvn -∗
               WP (HartE gen_id cpu_id (C (hread_resume (bv_unsigned w) m))
                   : expr riscv_lang)))) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    iIntros (HC Hproj Hdev Hexcl) "#Hcert H".
    destruct (hread_req_at_inv _ _ _ Hproj) as (K & Hm & Hres).
    assert (Hg : C m = Interface.Next (Interface.MemRead n req)
                         (fun v => C (K v)))
      by (rewrite Hm; exact (HC _ (Interface.MemRead n req) K eq_refl)).
    rewrite Hg.
    iApply (wp_hart_step with "Hcert").
    { intros oth0 h0 img0 σ0 log0 tv0 r0 m'0 σ'0 log'0 tv'0 r'0 Hs.
      rewrite /mnode_step in Hs. cbn beta iota in Hs.
      rewrite Hdev in Hs. cbn beta iota in Hs.
      destruct Hs as [(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)
                     |(Hex & _)]; [done|congruence]. }
    iIntros (σ oth rv img log tv V) "%Htv Hσ Htso".
    iDestruct (tso_interp_of_bound with "Htso") as %Hb.
    assert (Htvlen : (tv <= length log)%nat) by (rewrite -Htv; apply Hb).
    iMod ("H" $! σ img log tv V with "[//] Hσ Htso") as "[%Hrd Hk]".
    destruct (Hrd tv (Nat.le_refl tv) Htvlen) as (w0 & Hw0 & HP0).
    iModIntro. iExists (C (K (inl (w0, None)))), σ, log, tv, rv.
    iSplitR.
    { iPureIntro. rewrite /mnode_step. cbn beta iota.
      rewrite Hdev. cbn beta iota.
      left. split; [exact Hexcl|].
      exists tv, w0. split_and!; [lia|exact Htvlen| |done|done|done|done|done].
      exact Hw0. }
    iNext. iIntros (m' σ' log' tv' rv') "%Hstep".
    rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
    rewrite Hdev in Hstep. cbn beta iota in Hstep.
    destruct Hstep as [(_ & tvn & w' & Hlo & Hhi & Hbytes' & -> & -> & ->
                        & -> & ->)
                      |(Hex & _)]; [|congruence].
    destruct (Hrd tvn Hlo Hhi) as (w1 & Hw1 & HP1).
    assert (w' = w1) as ->.
    { apply bv_eq_of_bytes. intros j Hj.
      pose proof (Hw1 j Hj) as H0.
      pose proof (Hbytes' j Hj) as H1.
      rewrite H1 in H0. apply Some_inj in H0. exact H0. }
    iMod "Hk" as "(Hσ & Htso & HWP)".
    assert (Hadv : (V (hart_agent cpu_id) <= tvn)%nat)
      by (rewrite Htv; exact Hlo).
    iMod (tso_interp_of_advance _ img σ.(mem) log V (hart_agent cpu_id) tvn
            (fin_to_nat_lt cpu_id) Hadv Hhi with "Htso") as "Htso".
    iDestruct (tso_interp_of_receipt_at riscv_eraGS img σ.(mem) log
                 (vstep (hart_agent cpu_id) tvn log V) (hart_agent cpu_id) tvn
                 (vstep_here (hart_agent cpu_id) tvn log V)
                 with "Htso") as "[Htso #Hrcpt]".
    iModIntro. rewrite -(Hres w1). iFrame "Hσ Htso".
    iApply ("HWP" $! tvn w1 with "[//] [//] [//] [//] Hrcpt").
  Qed.

  (* RAM READ, THE PLAIN EXPLICIT ONE -- the arm the flip changed, and    *)
  (* §6's [Mobl_ram_plain].  The machine advances this hart's view        *)
  (* NONDETERMINISTICALLY (anywhere from where it is to the top of the    *)
  (* log) and then reads latest-visible AT THAT VIEW, so a caller that    *)
  (* wants to pin the value must own it AT EVERY REACHABLE VIEW: hence    *)
  (* the ∀ [tv'] in the obligation, which is exactly what                 *)
  (* [TsoCtx.twin_load_ok] concludes from [ctx_pointsto] + [own_context]. *)
  (* The rule then pays the (monotone) view advance itself, so the        *)
  (* caller hands the bundle back at the view it received.                *)
  (*                                                                      *)
  (* AND IT MINTS THE RECEIPT (A6.47 ruling 2).  The machine CHOOSES the   *)
  (* advanced view [tvn], and the one moment that number is known with     *)
  (* the view authority in hand is right after the step, inside this rule. *)
  (* So the callback hands back a WP PARAMETERISED BY the receipt: the     *)
  (* rule advances, mints [view_lb h tvn] (an inclusion, not an update --  *)
  (* free), and applies.  A consumer that does not want it writes          *)
  (* [iIntros (tvn _ _) "_"] and is otherwise unchanged; a consumer that   *)
  (* DOES want it -- any message-passing read, the boot [started] flag     *)
  (* first -- now has a minting site with no new machinery.  The step from *)
  (* the VALUE read to a position ([tvn ≥ F] because the message that      *)
  (* published this value sits at [F] and I did not write it) is           *)
  (* per-proof and deliberately stays in the proofs.                       *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_hart_ram_read_plain {X : Type} (C : M X -> M unit)
      (n : N) (req : Interface.ReadReq.t n) (m : M X) :
    mctx C ->
    hread_req_at n m = Some req ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_excl (Interface.ReadReq.access_kind req) = false ->
    gen_cert -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
       ∃ w : bv (8 * n),
         ⌜∀ tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
            tso_read_bytes img log (hart_agent cpu_id) tv'
              (Interface.ReadReq.pa req) n w⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp σ ∗
              tso_interp_of riscv_eraGS img σ.(mem) log V ∗
              (∀ tvn : nat, ⌜(tv <= tvn)%nat⌝ -∗ ⌜(tvn <= length log)%nat⌝ -∗
                 view_lb view_name loglen_name (hart_agent cpu_id) tvn -∗
                 WP (HartE gen_id cpu_id (C (hread_resume (bv_unsigned w) m))
                     : expr riscv_lang)))) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    (* RE-DERIVED from the value-after-view rule (tso-pin-memo.md §0): the
       existential moves outside by the byte-wise determinism step that used
       to sit here, and the eleven call sites do not notice. *)
    iIntros (HC Hproj Hdev Hexcl) "#Hcert H".
    iApply (wp_hart_ram_read_plain_ex C n req m
              (fun _ : bv (8 * n) => True) HC Hproj Hdev Hexcl
              with "Hcert").
    iIntros (σ img log tv V) "%Htv Hσ Htso".
    iMod ("H" $! σ img log tv V with "[//] Hσ Htso") as (w) "[%Hrd Hk]".
    iModIntro. iSplitR.
    { iPureIntro. intros tv' Hlo Hhi. exists w. split; [by apply Hrd | done]. }
    iNext. iMod "Hk" as "(Hσ & Htso & HWP)". iModIntro. iFrame "Hσ Htso".
    iIntros (tvn w') "%Hlo %Hhi %Hrd' _ #Hrcpt".
    assert (w' = w) as ->.
    { apply bv_eq_of_bytes. intros j Hj.
      pose proof (Hrd tvn Hlo Hhi j Hj) as H0.
      pose proof (Hrd' j Hj) as H1.
      rewrite H0 in H1. apply Some_inj in H1. by symmetry. }
    iApply ("HWP" $! tvn with "[//] [//] Hrcpt").
  Qed.

  (* ------------------------------------------------------------------ *)
  (* RAM WRITE.  Total, so there is no witness at all: the caller           *)
  (* re-establishes [mstate_interp] at the written map, with the gen_heap  *)
  (* update happening inside its fupd.  Which of the two arms fires is     *)
  (* decided by σ (another hart's reservation on the footprint ⇒ self-      *)
  (* loop), and the rule sees σ BEFORE running the caller's premise, so on  *)
  (* the self-loop arm the premise survives and Löb closes it.              *)
  (* ------------------------------------------------------------------ *)
  (* §6's [Wobl_ram]: the flat update AND the append.  The caller owes the  *)
  (* bundle back at the APPENDED log -- that is where the four ghost steps  *)
  (* live (γts to the new top over the footprint, γlogm persist, the        *)
  (* mono_nat bump, the dirty-set insert), and they cannot be done here     *)
  (* because the per-byte timestamp FRAGMENTS ride inside the caller's own  *)
  (* [ctx_pointsto]s.  The view moves by [wstore_tv]: not at all for a      *)
  (* plain store, past its own append for the AMO half.                     *)
  (* THE RECEIPT (§6 amendment A6.6) is minted from the bundle the caller   *)
  (* hands back -- it is the post-append top that the acquire needs -- and  *)
  (* reaches the continuation beside the [resv_frag].                       *)
  Lemma wp_hart_ram_write {X : Type} (C : M X -> M unit)
      (n : N) (req : Interface.WriteReq.t n) (m : M X) (rr : option resv) :
    mctx C ->
    hwrite_req_at n m = Some req ->
    dev_addr (Interface.WriteReq.pa req) = false ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
       ▷ (|={∅,⊤}=> mstate_interp
              (MState σ.(sregs)
                 (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
                    (Interface.WriteReq.value req)) σ.(mdev)) ∗
            tso_interp_of riscv_eraGS img
              (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
                 (Interface.WriteReq.value req))
              (log ++ [PWMsg (snap_of (Interface.WriteReq.pa req) n
                                (Interface.WriteReq.value req))
                         (hart_agent cpu_id)])%list
              (vstep (hart_agent cpu_id)
                 (wstore_tv (Interface.WriteReq.access_kind req) log tv)
                 (log ++ [PWMsg (snap_of (Interface.WriteReq.pa req) n
                                   (Interface.WriteReq.value req))
                            (hart_agent cpu_id)])%list V) ∗
            (resv_frag cpu_id None -∗
             view_lb view_name loglen_name (hart_agent cpu_id)
               (wstore_tv (Interface.WriteReq.access_kind req) log tv) -∗
             WP (HartE gen_id cpu_id (C (hwrite_resume m)) : expr riscv_lang)))) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    iIntros (HC Hproj Hdev) "#Hcert Hfrag H".
    destruct (hwrite_req_at_inv _ _ _ Hproj) as (K & Hm & Hres).
    assert (Hg : C m = Interface.Next (Interface.MemWrite n req)
                         (fun v => C (K v)))
      by (rewrite Hm; exact (HC _ (Interface.MemWrite n req) K eq_refl)).
    rewrite Hg.
    iLöb as "IH".
    iApply (wp_hart_step_resv _ rr with "Hcert Hfrag").
    iIntros (σ oth img log tv V) "_ %Htv Hσ Htso".
    destruct (decide (footprint (Interface.WriteReq.pa req) n ## oth))
      as [Hfree|Hblocked].
    - (* the write *)
      iMod ("H" $! σ img log tv V with "[//] Hσ Htso") as "Hk".
      iModIntro.
      iExists (C (K (inl None))),
        (MState σ.(sregs)
           (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
              (Interface.WriteReq.value req)) σ.(mdev)),
        (log ++ [PWMsg (snap_of (Interface.WriteReq.pa req) n
                          (Interface.WriteReq.value req))
                   (hart_agent cpu_id)])%list,
        (wstore_tv (Interface.WriteReq.access_kind req) log tv), None.
      iSplitR.
      { iPureIntro. rewrite /mnode_step. cbn beta iota.
        rewrite Hdev. cbn beta iota. right. done. }
      iNext. iIntros (m' σ' log' tv' rv') "%Hstep".
      rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
      rewrite Hdev in Hstep. cbn beta iota in Hstep.
      destruct Hstep as [(Hov & _) | (_ & -> & -> & -> & -> & ->)]; [done|].
      iMod "Hk" as "(Hσ & Htso & HWP)".
      iDestruct (tso_interp_of_receipt_at _ _ _ _ _ (hart_agent cpu_id)
                   (wstore_tv (Interface.WriteReq.access_kind req) log tv)
                   (vstep_self _ _ _ _) with "Htso") as "[Htso Hrec]".
      iModIntro. iFrame "Hσ Htso".
      iIntros "Hfrag". rewrite -Hres. iApply ("HWP" with "Hfrag Hrec").
    - (* blocked by another hart's reservation: self-loop, premise intact *)
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
      iExists (Interface.Next (Interface.MemWrite n req) (fun v => C (K v))),
        σ, log, tv, rr.
      iSplitR.
      { iPureIntro. rewrite /mnode_step. cbn beta iota.
        rewrite Hdev. cbn beta iota. left. done. }
      iNext. iIntros (m' σ' log' tv' rv') "%Hstep".
      rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
      rewrite Hdev in Hstep. cbn beta iota in Hstep.
      destruct Hstep as [(_ & -> & -> & -> & -> & ->) | (Hfree & _)]; [|done].
      iMod "Hmask" as "_". iModIntro. iFrame "Hσ".
      iSplitL "Htso".
      { rewrite -Htv. iApply (tso_interp_of_idle with "Htso"). }
      iIntros "Hfrag". iApply ("IH" with "Hfrag H").
  Qed.

  (* ------------------------------------------------------------------ *)
  (* RAM READ, EXCLUSIVE ([ak_excl = true]): the same read, the same       *)
  (* statement; the language also records the snapshot as this hart's     *)
  (* reservation (invisible here -- see the header) and self-loops while   *)
  (* another hart reserves any of the bytes -- dropping the hart's own     *)
  (* stale reservation as it waits -- which Löb absorbs.                   *)
  (* ------------------------------------------------------------------ *)
  (* "DRAIN, THEN READ MEMORY".  The read is still against the FLAT cache --
     reading [s.(mem)] IS reading at the log top ([tso_read_top_flat]) -- so
     the caller's obligation is today's [read_bytes] fact.  What is new is
     the VIEW: the arm takes it to the top, and that is the one moment an
     ACQUIRE RECEIPT is honestly produced, so the rule mints it and hands it
     to the callback beside the (already advanced) bundle
     (tso-machine-flip.md §6 amendment A6.6).  The receipt is persistent: a
     caller that does not want it drops it. *)
  Lemma wp_hart_ram_read_excl {X : Type} (C : M X -> M unit)
      (n : N) (req : Interface.ReadReq.t n) (m : M X) (rr : option resv) :
    mctx C ->
    hread_req_at n m = Some req ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_excl (Interface.ReadReq.access_kind req) = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log
         (vstep (hart_agent cpu_id) (length log) log V) -∗
       view_lb view_name loglen_name (hart_agent cpu_id) (length log) ={⊤,∅}=∗
       ∃ w : bv (8 * n),
         ⌜read_bytes σ.(mem) (Interface.ReadReq.pa req) n = Some w⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp σ ∗
              tso_interp_of riscv_eraGS img σ.(mem) log
                (vstep (hart_agent cpu_id) (length log) log V) ∗
              (resv_frag cpu_id (Some (snap_of (Interface.ReadReq.pa req) n w)) -∗
               WP (HartE gen_id cpu_id (C (hread_resume (bv_unsigned w) m))
                   : expr riscv_lang)))) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    iIntros (HC Hproj Hdev Hexcl) "#Hcert Hfrag H".
    destruct (hread_req_at_inv _ _ _ Hproj) as (K & Hm & Hres).
    assert (Hg : C m = Interface.Next (Interface.MemRead n req)
                         (fun v => C (K v)))
      by (rewrite Hm; exact (HC _ (Interface.MemRead n req) K eq_refl)).
    rewrite Hg.
    (* the blocked arm RELEASES the stale reservation, so the IH is taken at
       every frag value *)
    iLöb as "IH" forall (rr).
    iApply (wp_hart_step_resv _ rr with "Hcert Hfrag").
    iIntros (σ oth img log tv V) "_ %Htv Hσ Htso".
    destruct (decide (footprint (Interface.ReadReq.pa req) n ## oth))
      as [Hfree|Hblocked].
    - (* the read, now reserving; the view goes to the top and the receipt
         is born there *)
      iMod (tso_interp_of_top _ img σ.(mem) log V (hart_agent cpu_id)
              (fin_to_nat_lt cpu_id) with "Htso") as "[Htso #Hrec]".
      iMod ("H" $! σ img log tv V with "[//] Hσ Htso Hrec") as (w) "[%Hrb Hk]".
      iModIntro. iExists (C (K (inl (w, None)))), σ, log, (length log),
        (Some (snap_of (Interface.ReadReq.pa req) n w)).
      iSplitR.
      { iPureIntro. rewrite /mnode_step. cbn beta iota.
        rewrite Hdev. cbn beta iota.
        right. split; [exact Hexcl|]. right. split; [exact Hfree|].
        exists w. split; [exact (read_bytes_spec _ _ _ _ Hrb)|]. done. }
      iNext. iIntros (m' σ' log' tv' rv') "%Hstep".
      rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
      rewrite Hdev in Hstep. cbn beta iota in Hstep.
      destruct Hstep as [(Hs1 & _)
                        |(_ & [(Hov & _)
                              |(_ & w' & Hbytes' & -> & -> & -> & -> & ->)])];
        [congruence|done|].
      assert (w' = w) as ->.
      { apply bv_eq_of_bytes. intros j Hj.
        pose proof (read_bytes_spec _ _ _ _ Hrb j Hj) as H0.
        pose proof (Hbytes' j Hj) as H1.
        rewrite H1 in H0. apply Some_inj in H0. exact H0. }
      iMod "Hk" as "(Hσ & Htso & HWP)". iModIntro. iFrame "Hσ Htso".
      iIntros "Hfrag". rewrite -(Hres w). iApply ("HWP" with "Hfrag").
    - (* blocked: self-loop, own stale reservation dropped, premise intact.
         The view does NOT move on this arm -- a hart that is waiting has
         drained nothing. *)
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
      iExists (Interface.Next (Interface.MemRead n req) (fun v => C (K v))),
        σ, log, tv, None.
      iSplitR.
      { iPureIntro. rewrite /mnode_step. cbn beta iota.
        rewrite Hdev. cbn beta iota.
        right. split; [exact Hexcl|]. left. done. }
      iNext. iIntros (m' σ' log' tv' rv') "%Hstep".
      rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
      rewrite Hdev in Hstep. cbn beta iota in Hstep.
      destruct Hstep as [(Hs1 & _)
                        |(_ & [(_ & -> & -> & -> & -> & ->) | (Hfree & _)])];
        [congruence| |done].
      iMod "Hmask" as "_". iModIntro. iFrame "Hσ".
      iSplitL "Htso".
      { rewrite -Htv. iApply (tso_interp_of_idle with "Htso"). }
      iIntros "Hfrag". iApply ("IH" with "Hfrag H").
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE CONDITIONAL WRITE: the RAM write of an RMW whose exclusive read   *)
  (* this hart made, at the frag that read handed out.  Same language arm  *)
  (* as a plain store; what is NEW is knowledge: [wp_hart_step_resv] hands *)
  (* over [resv_ok] for the hart's own snapshot, so the caller learns the  *)
  (* word memory holds IS the word it read -- the one invariant access an  *)
  (* acquire needs.  A blocked arm is absorbed by Löb with the frag         *)
  (* unchanged (a blocked write keeps its reservation, design §3a).        *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_hart_ram_write_cond {X : Type} (C : M X -> M unit)
      (n : N) (req : Interface.WriteReq.t n) (m : M X) (w : bv (8 * n)) :
    mctx C ->
    hwrite_req_at n m = Some req ->
    dev_addr (Interface.WriteReq.pa req) = false ->
    Z.of_N n < 18446744073709551616 ->
    gen_cert -∗
    resv_frag cpu_id (Some (snap_of (Interface.WriteReq.pa req) n w)) -∗
    (∀ σ img log tv V,
       ⌜read_bytes σ.(mem) (Interface.WriteReq.pa req) n = Some w⌝ -∗
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
       ▷ (|={∅,⊤}=> mstate_interp
              (MState σ.(sregs)
                 (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
                    (Interface.WriteReq.value req)) σ.(mdev)) ∗
            tso_interp_of riscv_eraGS img
              (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
                 (Interface.WriteReq.value req))
              (log ++ [PWMsg (snap_of (Interface.WriteReq.pa req) n
                                (Interface.WriteReq.value req))
                         (hart_agent cpu_id)])%list
              (vstep (hart_agent cpu_id)
                 (wstore_tv (Interface.WriteReq.access_kind req) log tv)
                 (log ++ [PWMsg (snap_of (Interface.WriteReq.pa req) n
                                   (Interface.WriteReq.value req))
                            (hart_agent cpu_id)])%list V) ∗
            (resv_frag cpu_id None -∗
             view_lb view_name loglen_name (hart_agent cpu_id)
               (wstore_tv (Interface.WriteReq.access_kind req) log tv) -∗
             WP (HartE gen_id cpu_id (C (hwrite_resume m)) : expr riscv_lang)))) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    iIntros (HC Hproj Hdev Hn) "#Hcert Hfrag H".
    destruct (hwrite_req_at_inv _ _ _ Hproj) as (K & Hm & Hres).
    assert (Hg : C m = Interface.Next (Interface.MemWrite n req)
                         (fun v => C (K v)))
      by (rewrite Hm; exact (HC _ (Interface.MemWrite n req) K eq_refl)).
    rewrite Hg.
    iLöb as "IH".
    iApply (wp_hart_step_resv _ (Some (snap_of (Interface.WriteReq.pa req) n w))
              with "Hcert Hfrag").
    iIntros (σ oth img log tv V) "%Hok %Htv Hσ Htso".
    pose proof (snap_of_read_bytes _ _ _ _ Hn (Hok _ eq_refl)) as Hrb.
    destruct (decide (footprint (Interface.WriteReq.pa req) n ## oth))
      as [Hfree|Hblocked].
    - (* the write, at the pinned old value *)
      iMod ("H" $! σ img log tv V with "[//] [//] Hσ Htso") as "Hk".
      iModIntro.
      iExists (C (K (inl None))),
        (MState σ.(sregs)
           (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
              (Interface.WriteReq.value req)) σ.(mdev)),
        (log ++ [PWMsg (snap_of (Interface.WriteReq.pa req) n
                          (Interface.WriteReq.value req))
                   (hart_agent cpu_id)])%list,
        (wstore_tv (Interface.WriteReq.access_kind req) log tv), None.
      iSplitR.
      { iPureIntro. rewrite /mnode_step. cbn beta iota.
        rewrite Hdev. cbn beta iota. right. done. }
      iNext. iIntros (m' σ' log' tv' rv') "%Hstep".
      rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
      rewrite Hdev in Hstep. cbn beta iota in Hstep.
      destruct Hstep as [(Hov & _) | (_ & -> & -> & -> & -> & ->)]; [done|].
      iMod "Hk" as "(Hσ & Htso & HWP)".
      iDestruct (tso_interp_of_receipt_at _ _ _ _ _ (hart_agent cpu_id)
                   (wstore_tv (Interface.WriteReq.access_kind req) log tv)
                   (vstep_self _ _ _ _) with "Htso") as "[Htso Hrec]".
      iModIntro. iFrame "Hσ Htso".
      iIntros "Hfrag". rewrite -Hres. iApply ("HWP" with "Hfrag Hrec").
    - (* blocked (never, once reservations are pairwise disjoint -- but the
         rule need not know): self-loop, frag and premise intact *)
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
      iExists (Interface.Next (Interface.MemWrite n req) (fun v => C (K v))),
        σ, log, tv, (Some (snap_of (Interface.WriteReq.pa req) n w)).
      iSplitR.
      { iPureIntro. rewrite /mnode_step. cbn beta iota.
        rewrite Hdev. cbn beta iota. left. done. }
      iNext. iIntros (m' σ' log' tv' rv') "%Hstep".
      rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
      rewrite Hdev in Hstep. cbn beta iota in Hstep.
      destruct Hstep as [(_ & -> & -> & -> & -> & ->) | (Hfree & _)]; [|done].
      iMod "Hmask" as "_". iModIntro. iFrame "Hσ".
      iSplitL "Htso".
      { rewrite -Htv. iApply (tso_interp_of_idle with "Htso"). }
      iIntros "Hfrag". iApply ("IH" with "Hfrag H").
  Qed.

  (* ------------------------------------------------------------------ *)
  (* MMIO READ.  The device answers and its state may move (an RHR read   *)
  (* pops the receive FIFO); the accessor is the PARTIAL [dev_read], so   *)
  (* the caller's witness is also the not-stuck evidence.                 *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_hart_dev_read {X : Type} (C : M X -> M unit)
      (n : N) (req : Interface.ReadReq.t n) (m : M X) :
    mctx C ->
    hread_req_at n m = Some req ->
    dev_addr (Interface.ReadReq.pa req) = true ->
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ∃ (w : bv (8 * n)) (d' : dev_state),
         ⌜dev_read σ.(mdev) (Interface.ReadReq.pa req) n = Some (w, d')⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗
              WP (HartE gen_id cpu_id (C (hread_resume (bv_unsigned w) m))
                  : expr riscv_lang))) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    (* Proof plan: via wp_hart_step; [dev_read] is a function, so the
       arm's ∃ (w, d') is pinned by the witness equation. *)
    iIntros (HC Hproj Hdev) "#Hcert H".
    destruct (hread_req_at_inv _ _ _ Hproj) as (K & Hm & Hres).
    assert (Hg : C m = Interface.Next (Interface.MemRead n req)
                         (fun v => C (K v)))
      by (rewrite Hm; exact (HC _ (Interface.MemRead n req) K eq_refl)).
    rewrite Hg.
    iApply (wp_hart_step with "Hcert").
    { intros oth0 h0 img0 σ0 log0 tv0 r0 m'0 σ'0 log'0 tv'0 r'0 Hs.
      rewrite /mnode_step in Hs. cbn beta iota in Hs.
      rewrite Hdev in Hs. cbn beta iota in Hs.
      destruct Hs as (_ & _ & _ & _ & _ & _ & _ & ->). done. }
    (* strongly ordered (RULING 2): no log, no view action, so the bundle is
       returned exactly as it came *)
    iIntros (σ oth rv img log tv V) "%Htv Hσ Htso".
    iMod ("H" $! σ with "Hσ") as (w d') "[%Hdr Hk]".
    iModIntro. iExists (C (K (inl (w, None)))), (MState σ.(sregs) σ.(mem) d'),
      log, tv, rv.
    iSplitR.
    { iPureIntro. rewrite /mnode_step. cbn beta iota.
      rewrite Hdev. cbn beta iota.
      exists w, d'. done. }
    iNext. iIntros (m' σ' log' tv' rv') "%Hstep".
    rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
    rewrite Hdev in Hstep. cbn beta iota in Hstep.
    destruct Hstep as (w' & d'' & Hdr' & -> & -> & -> & -> & ->).
    rewrite Hdr in Hdr'. injection Hdr' as <- <-.
    iMod "Hk" as "[Hσ HWP]". iModIntro.
    rewrite -(Hres w). iFrame "Hσ HWP".
    rewrite -Htv. iApply (tso_interp_of_idle with "Htso").
  Qed.

  (* ------------------------------------------------------------------ *)
  (* MMIO WRITE.  A [MemWrite] event, so it clears the hart's own         *)
  (* reservation -- invisible to the caller here.                         *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_hart_dev_write {X : Type} (C : M X -> M unit)
      (n : N) (req : Interface.WriteReq.t n) (m : M X) (rr : option resv) :
    mctx C ->
    hwrite_req_at n m = Some req ->
    dev_addr (Interface.WriteReq.pa req) = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ∃ d' : dev_state,
         ⌜dev_write σ.(mdev) (Interface.WriteReq.pa req) n
            (Interface.WriteReq.value req) = Some d'⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗
              (resv_frag cpu_id None -∗
               WP (HartE gen_id cpu_id (C (hwrite_resume m)) : expr riscv_lang)))) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    (* Proof plan: as wp_hart_dev_read, in the frag form (an MMIO write is a
       [MemWrite] event and clears the reservation). *)
    iIntros (HC Hproj Hdev) "#Hcert Hfrag H".
    destruct (hwrite_req_at_inv _ _ _ Hproj) as (K & Hm & Hres).
    assert (Hg : C m = Interface.Next (Interface.MemWrite n req)
                         (fun v => C (K v)))
      by (rewrite Hm; exact (HC _ (Interface.MemWrite n req) K eq_refl)).
    rewrite Hg.
    iApply (wp_hart_step_resv _ rr with "Hcert Hfrag").
    iIntros (σ oth img log tv V) "_ %Htv Hσ Htso".
    iMod ("H" $! σ with "Hσ") as (d') "[%Hdw Hk]".
    iModIntro. iExists (C (K (inl None))), (MState σ.(sregs) σ.(mem) d'),
      log, tv, None.
    iSplitR.
    { iPureIntro. rewrite /mnode_step. cbn beta iota.
      rewrite Hdev. cbn beta iota.
      exists d'. done. }
    iNext. iIntros (m' σ' log' tv' rv') "%Hstep".
    rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
    rewrite Hdev in Hstep. cbn beta iota in Hstep.
    destruct Hstep as (d'' & Hdw' & -> & -> & -> & -> & ->).
    rewrite Hdw in Hdw'. injection Hdw' as <-.
    iMod "Hk" as "[Hσ HWP]". iModIntro. iFrame "Hσ".
    iSplitL "Htso".
    { rewrite -Htv. iApply (tso_interp_of_idle with "Htso"). }
    iIntros "Hfrag". rewrite -Hres. iApply ("HWP" with "Hfrag").
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE [swp] FORMS.  Same four rules, phrased so a caller composing a   *)
  (* sub-monad by [swp_bind] never has to name a context: the event fires *)
  (* and the proof continues at the RESUME, still in [swp].               *)
  (* ------------------------------------------------------------------ *)

  Lemma swp_hart_ram_read_plain {X : Type} (n : N)
      (req : Interface.ReadReq.t n) (m : M X) (Φ : X -> iProp Σ) :
    hread_req_at n m = Some req ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_excl (Interface.ReadReq.access_kind req) = false ->
    gen_cert -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
       ∃ w : bv (8 * n),
         ⌜∀ tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
            tso_read_bytes img log (hart_agent cpu_id) tv'
              (Interface.ReadReq.pa req) n w⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp σ ∗
              tso_interp_of riscv_eraGS img σ.(mem) log V ∗
              (∀ tvn : nat, ⌜(tv <= tvn)%nat⌝ -∗ ⌜(tvn <= length log)%nat⌝ -∗
                 view_lb view_name loglen_name (hart_agent cpu_id) tvn -∗
                 swp (hread_resume (bv_unsigned w) m) Φ))) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj Hdev Hexcl) "#Hcert H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_ram_read_plain C n req m HC Hproj Hdev Hexcl
              with "Hcert [H Hcont]").
    iIntros (σ img log tv V) "%Htv Hσ Htso".
    iMod ("H" $! σ img log tv V with "[//] Hσ Htso") as (w) "[%Hrd Hk]".
    iModIntro. iExists w. iSplitR; [done|]. iNext.
    iMod "Hk" as "(Hσ & Htso & Hswp)". iModIntro. iFrame "Hσ Htso".
    iIntros (tvn Hlo Hhi) "#Hrcpt".
    iApply (swp_use _ Φ C HC with "[Hswp] Hcont").
    iApply ("Hswp" $! tvn with "[//] [//] Hrcpt").
  Qed.

  (* the [swp] form of the value-after-view read (tso-pin-memo.md §0).
     This is the one the PT walk uses -- [PtTreeAdue] / [HartSKpt] compose
     in [swp] -- and it is where [fobl_ram_ex]'s obligation lands. *)
  Lemma swp_hart_ram_read_plain_ex {X : Type} (n : N)
      (req : Interface.ReadReq.t n) (m : M X) (Φ : X -> iProp Σ)
      (P : bv (8 * n) -> Prop) :
    hread_req_at n m = Some req ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_excl (Interface.ReadReq.access_kind req) = false ->
    gen_cert -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
       ⌜∀ tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
          ∃ w : bv (8 * n),
            tso_read_bytes img log (hart_agent cpu_id) tv'
              (Interface.ReadReq.pa req) n w ∧ P w⌝ ∗
       ▷ (|={∅,⊤}=> mstate_interp σ ∗
            tso_interp_of riscv_eraGS img σ.(mem) log V ∗
            (∀ (tvn : nat) (w : bv (8 * n)),
               ⌜(tv <= tvn)%nat⌝ -∗ ⌜(tvn <= length log)%nat⌝ -∗
               ⌜tso_read_bytes img log (hart_agent cpu_id) tvn
                  (Interface.ReadReq.pa req) n w⌝ -∗
               ⌜P w⌝ -∗
               view_lb view_name loglen_name (hart_agent cpu_id) tvn -∗
               swp (hread_resume (bv_unsigned w) m) Φ))) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj Hdev Hexcl) "#Hcert H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_ram_read_plain_ex C n req m P HC Hproj Hdev Hexcl
              with "Hcert [H Hcont]").
    iIntros (σ img log tv V) "%Htv Hσ Htso".
    iMod ("H" $! σ img log tv V with "[//] Hσ Htso") as "[%Hrd Hk]".
    iModIntro. iSplitR; [done|]. iNext.
    iMod "Hk" as "(Hσ & Htso & Hswp)". iModIntro. iFrame "Hσ Htso".
    iIntros (tvn w) "%Hlo %Hhi %Hrd' %HP #Hrcpt".
    iApply (swp_use _ Φ C HC with "[Hswp] Hcont").
    iApply ("Hswp" $! tvn w with "[//] [//] [//] [//] Hrcpt").
  Qed.

  Lemma swp_hart_ram_read_excl {X : Type} (n : N) (req : Interface.ReadReq.t n)
      (m : M X) (Φ : X -> iProp Σ) (rr : option resv) :
    hread_req_at n m = Some req ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_excl (Interface.ReadReq.access_kind req) = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log
         (vstep (hart_agent cpu_id) (length log) log V) -∗
       view_lb view_name loglen_name (hart_agent cpu_id) (length log) ={⊤,∅}=∗
       ∃ w : bv (8 * n),
         ⌜read_bytes σ.(mem) (Interface.ReadReq.pa req) n = Some w⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp σ ∗
              tso_interp_of riscv_eraGS img σ.(mem) log
                (vstep (hart_agent cpu_id) (length log) log V) ∗
              (resv_frag cpu_id (Some (snap_of (Interface.ReadReq.pa req) n w)) -∗
               swp (hread_resume (bv_unsigned w) m) Φ))) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj Hdev Hexcl) "#Hcert Hfrag H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_ram_read_excl C n req m rr HC Hproj Hdev Hexcl
              with "Hcert Hfrag [H Hcont]").
    iIntros (σ img log tv V) "%Htv Hσ Htso Hrec".
    iMod ("H" $! σ img log tv V with "[//] Hσ Htso Hrec") as (w) "[%Hrb Hk]".
    iModIntro. iExists w. iSplitR; [done|]. iNext.
    iMod "Hk" as "(Hσ & Htso & Hswp)". iModIntro. iFrame "Hσ Htso".
    iIntros "Hfrag".
    iApply (swp_use _ Φ C HC with "[Hswp Hfrag] Hcont"). by iApply "Hswp".
  Qed.

  Lemma swp_hart_ram_write {X : Type} (n : N) (req : Interface.WriteReq.t n)
      (m : M X) (Φ : X -> iProp Σ) (rr : option resv) :
    hwrite_req_at n m = Some req ->
    dev_addr (Interface.WriteReq.pa req) = false ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
       ▷ (|={∅,⊤}=> mstate_interp
              (MState σ.(sregs)
                 (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
                    (Interface.WriteReq.value req)) σ.(mdev)) ∗
            tso_interp_of riscv_eraGS img
              (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
                 (Interface.WriteReq.value req))
              (log ++ [PWMsg (snap_of (Interface.WriteReq.pa req) n
                                (Interface.WriteReq.value req))
                         (hart_agent cpu_id)])%list
              (vstep (hart_agent cpu_id)
                 (wstore_tv (Interface.WriteReq.access_kind req) log tv)
                 (log ++ [PWMsg (snap_of (Interface.WriteReq.pa req) n
                                   (Interface.WriteReq.value req))
                            (hart_agent cpu_id)])%list V) ∗
            (resv_frag cpu_id None -∗
             view_lb view_name loglen_name (hart_agent cpu_id)
               (wstore_tv (Interface.WriteReq.access_kind req) log tv) -∗
             swp (hwrite_resume m) Φ))) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj Hdev) "#Hcert Hfrag H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_ram_write C n req m rr HC Hproj Hdev
              with "Hcert Hfrag [H Hcont]").
    iIntros (σ img log tv V) "%Htv Hσ Htso".
    iMod ("H" $! σ img log tv V with "[//] Hσ Htso") as "Hk".
    iModIntro. iNext.
    iMod "Hk" as "(Hσ & Htso & Hswp)". iModIntro. iFrame "Hσ Htso".
    iIntros "Hfrag Hrec".
    iApply (swp_use _ Φ C HC with "[Hswp Hfrag Hrec] Hcont").
    by iApply ("Hswp" with "Hfrag Hrec").
  Qed.

  Lemma swp_hart_ram_write_cond {X : Type} (n : N) (req : Interface.WriteReq.t n)
      (m : M X) (Φ : X -> iProp Σ) (w : bv (8 * n)) :
    hwrite_req_at n m = Some req ->
    dev_addr (Interface.WriteReq.pa req) = false ->
    Z.of_N n < 18446744073709551616 ->
    gen_cert -∗
    resv_frag cpu_id (Some (snap_of (Interface.WriteReq.pa req) n w)) -∗
    (∀ σ img log tv V,
       ⌜read_bytes σ.(mem) (Interface.WriteReq.pa req) n = Some w⌝ -∗
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
       ▷ (|={∅,⊤}=> mstate_interp
              (MState σ.(sregs)
                 (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
                    (Interface.WriteReq.value req)) σ.(mdev)) ∗
            tso_interp_of riscv_eraGS img
              (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
                 (Interface.WriteReq.value req))
              (log ++ [PWMsg (snap_of (Interface.WriteReq.pa req) n
                                (Interface.WriteReq.value req))
                         (hart_agent cpu_id)])%list
              (vstep (hart_agent cpu_id)
                 (wstore_tv (Interface.WriteReq.access_kind req) log tv)
                 (log ++ [PWMsg (snap_of (Interface.WriteReq.pa req) n
                                   (Interface.WriteReq.value req))
                            (hart_agent cpu_id)])%list V) ∗
            (resv_frag cpu_id None -∗
             view_lb view_name loglen_name (hart_agent cpu_id)
               (wstore_tv (Interface.WriteReq.access_kind req) log tv) -∗
             swp (hwrite_resume m) Φ))) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj Hdev Hn) "#Hcert Hfrag H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_ram_write_cond C n req m w HC Hproj Hdev Hn
              with "Hcert Hfrag [H Hcont]").
    iIntros (σ img log tv V) "%Hrb %Htv Hσ Htso".
    iMod ("H" $! σ img log tv V with "[//] [//] Hσ Htso") as "Hk".
    iModIntro. iNext.
    iMod "Hk" as "(Hσ & Htso & Hswp)". iModIntro. iFrame "Hσ Htso".
    iIntros "Hfrag Hrec".
    iApply (swp_use _ Φ C HC with "[Hswp Hfrag Hrec] Hcont").
    by iApply ("Hswp" with "Hfrag Hrec").
  Qed.

  Lemma swp_hart_dev_read {X : Type} (n : N) (req : Interface.ReadReq.t n)
      (m : M X) (Φ : X -> iProp Σ) :
    hread_req_at n m = Some req ->
    dev_addr (Interface.ReadReq.pa req) = true ->
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ∃ (w : bv (8 * n)) (d' : dev_state),
         ⌜dev_read σ.(mdev) (Interface.ReadReq.pa req) n = Some (w, d')⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗
              swp (hread_resume (bv_unsigned w) m) Φ)) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj Hdev) "#Hcert H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_dev_read C n req m HC Hproj Hdev with "Hcert [H Hcont]").
    iIntros (σ) "Hσ". iMod ("H" $! σ with "Hσ") as (w d') "[%Hdr Hk]".
    iModIntro. iExists w, d'. iSplitR; [done|]. iNext.
    iMod "Hk" as "[Hσ Hswp]". iModIntro. iFrame "Hσ".
    iApply (swp_use _ Φ C HC with "Hswp Hcont").
  Qed.

  Lemma swp_hart_dev_write {X : Type} (n : N) (req : Interface.WriteReq.t n)
      (m : M X) (Φ : X -> iProp Σ) (rr : option resv) :
    hwrite_req_at n m = Some req ->
    dev_addr (Interface.WriteReq.pa req) = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ∃ d' : dev_state,
         ⌜dev_write σ.(mdev) (Interface.WriteReq.pa req) n
            (Interface.WriteReq.value req) = Some d'⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗
              (resv_frag cpu_id None -∗ swp (hwrite_resume m) Φ))) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj Hdev) "#Hcert Hfrag H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_dev_write C n req m rr HC Hproj Hdev
              with "Hcert Hfrag [H Hcont]").
    iIntros (σ) "Hσ". iMod ("H" $! σ with "Hσ") as (d') "[%Hdw Hk]".
    iModIntro. iExists d'. iSplitR; [done|]. iNext.
    iMod "Hk" as "[Hσ Hswp]". iModIntro. iFrame "Hσ". iIntros "Hfrag".
    iApply (swp_use _ Φ C HC with "[Hswp Hfrag] Hcont"). by iApply "Hswp".
  Qed.

End events.
