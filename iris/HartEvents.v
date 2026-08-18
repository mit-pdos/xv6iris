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

Section events.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------ *)
  (* RAM READ, the plain one ([ak_excl = false]): never blocked, never    *)
  (* reserving.  The exclusive twin follows it.                           *)
  (*                                                                      *)
  (* The caller's witness is a [read_bytes] fact -- the same shape        *)
  (* [exec] pins reads with -- which both certifies the arm's ∃ and,      *)
  (* via [read_bytes_spec] + [bv_eq_of_bytes], makes the read value       *)
  (* UNIQUE, so the continuation runs at exactly [hread_resume w].        *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_hart_ram_read {X : Type} (C : M X -> M unit)
      (n : N) (req : Interface.ReadReq.t n) (m : M X) :
    mctx C ->
    hread_req_at n m = Some req ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_excl (Interface.ReadReq.access_kind req) = false ->
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ∃ w : bv (8 * n),
         ⌜read_bytes σ.(mem) (Interface.ReadReq.pa req) n = Some w⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp σ ∗
              WP (HartE gen_id cpu_id (C (hread_resume (bv_unsigned w) m))
                  : expr riscv_lang))) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    (* Proof plan: via wp_hart_step.  Witness: the plain-read arm with
       [read_bytes_spec] supplying the per-byte lookups.  Inversion: the
       arm's ∃ w' has all bytes pinned by the same lookups, so
       [bv_eq_of_bytes] gives w' = w; the continuation is [hread_req_at_inv]'s
       K equation. *)
    iIntros (HC Hproj Hdev Hexcl) "#Hcert H".
    destruct (hread_req_at_inv _ _ _ Hproj) as (K & Hm & Hres).
    assert (Hg : C m = Interface.Next (Interface.MemRead n req)
                         (fun v => C (K v)))
      by (rewrite Hm; exact (HC _ (Interface.MemRead n req) K eq_refl)).
    rewrite Hg.
    iApply (wp_hart_step with "Hcert").
    { intros oth0 σ0 r0 m'0 σ'0 r'0 Hs.
      rewrite /mnode_step in Hs. cbn beta iota in Hs.
      rewrite Hdev in Hs. cbn beta iota in Hs.
      destruct Hs as [(_ & _ & _ & _ & _ & ->) | (Hex & _)]; [done|congruence]. }
    iIntros (σ oth rv) "Hσ".
    iMod ("H" $! σ with "Hσ") as (w) "[%Hrb Hk]".
    iModIntro. iExists (C (K (inl (w, None)))), σ, rv.
    iSplitR.
    { iPureIntro. rewrite /mnode_step. cbn beta iota.
      rewrite Hdev. cbn beta iota.
      left. split; [exact Hexcl|]. exists w.
      split; [exact (read_bytes_spec _ _ _ _ Hrb)|]. done. }
    iNext. iIntros (m' σ' rv') "%Hstep".
    rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
    rewrite Hdev in Hstep. cbn beta iota in Hstep.
    destruct Hstep as [(_ & w' & Hbytes' & -> & -> & ->) | (Hex & _)];
      last congruence.
    assert (w' = w) as ->.
    { apply bv_eq_of_bytes. intros j Hj.
      pose proof (read_bytes_spec _ _ _ _ Hrb j Hj) as H0.
      pose proof (Hbytes' j Hj) as H1.
      rewrite H1 in H0. apply Some_inj in H0. exact H0. }
    iMod "Hk" as "[Hσ HWP]". iModIntro.
    rewrite -(Hres w). by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* RAM WRITE.  Total, so there is no witness at all: the caller           *)
  (* re-establishes [mstate_interp] at the written map, with the gen_heap  *)
  (* update happening inside its fupd.  Which of the two arms fires is     *)
  (* decided by σ (another hart's reservation on the footprint ⇒ self-      *)
  (* loop), and the rule sees σ BEFORE running the caller's premise, so on  *)
  (* the self-loop arm the premise survives and Löb closes it.              *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_hart_ram_write {X : Type} (C : M X -> M unit)
      (n : N) (req : Interface.WriteReq.t n) (m : M X) (rr : option resv) :
    mctx C ->
    hwrite_req_at n m = Some req ->
    dev_addr (Interface.WriteReq.pa req) = false ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ▷ (|={∅,⊤}=> mstate_interp
              (MState σ.(sregs)
                 (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
                    (Interface.WriteReq.value req)) σ.(mdev)) ∗
            (resv_frag cpu_id None -∗
             WP (HartE gen_id cpu_id (C (hwrite_resume m)) : expr riscv_lang)))) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    (* Proof plan: via wp_hart_step_resv; the write arm when the footprint is
       free of other harts' reservations, the self-loop arm otherwise --
       absorbed by Löb with the premise and the frag untouched. *)
    iIntros (HC Hproj Hdev) "#Hcert Hfrag H".
    destruct (hwrite_req_at_inv _ _ _ Hproj) as (K & Hm & Hres).
    assert (Hg : C m = Interface.Next (Interface.MemWrite n req)
                         (fun v => C (K v)))
      by (rewrite Hm; exact (HC _ (Interface.MemWrite n req) K eq_refl)).
    rewrite Hg.
    iLöb as "IH".
    iApply (wp_hart_step_resv _ rr with "Hcert Hfrag").
    iIntros (σ oth) "_ Hσ".
    destruct (decide (footprint (Interface.WriteReq.pa req) n ## oth))
      as [Hfree|Hblocked].
    - (* the write *)
      iMod ("H" $! σ with "Hσ") as "Hk".
      iModIntro.
      iExists (C (K (inl None))),
        (MState σ.(sregs)
           (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
              (Interface.WriteReq.value req)) σ.(mdev)), None.
      iSplitR.
      { iPureIntro. rewrite /mnode_step. cbn beta iota.
        rewrite Hdev. cbn beta iota. right. done. }
      iNext. iIntros (m' σ' rv') "%Hstep".
      rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
      rewrite Hdev in Hstep. cbn beta iota in Hstep.
      destruct Hstep as [(Hov & _) | (_ & -> & -> & ->)]; [done|].
      iMod "Hk" as "[Hσ HWP]". iModIntro. iFrame "Hσ".
      iIntros "Hfrag". rewrite -Hres. iApply ("HWP" with "Hfrag").
    - (* blocked by another hart's reservation: self-loop, premise intact *)
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
      iExists (Interface.Next (Interface.MemWrite n req) (fun v => C (K v))),
        σ, rr.
      iSplitR.
      { iPureIntro. rewrite /mnode_step. cbn beta iota.
        rewrite Hdev. cbn beta iota. left. done. }
      iNext. iIntros (m' σ' rv') "%Hstep".
      rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
      rewrite Hdev in Hstep. cbn beta iota in Hstep.
      destruct Hstep as [(_ & -> & -> & ->) | (Hfree & _)]; [|done].
      iMod "Hmask" as "_". iModIntro. iFrame "Hσ".
      iIntros "Hfrag". iApply ("IH" with "Hfrag H").
  Qed.

  (* ------------------------------------------------------------------ *)
  (* RAM READ, EXCLUSIVE ([ak_excl = true]): the same read, the same       *)
  (* statement; the language also records the snapshot as this hart's     *)
  (* reservation (invisible here -- see the header) and self-loops while   *)
  (* another hart reserves any of the bytes -- dropping the hart's own     *)
  (* stale reservation as it waits -- which Löb absorbs.                   *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_hart_ram_read_excl {X : Type} (C : M X -> M unit)
      (n : N) (req : Interface.ReadReq.t n) (m : M X) (rr : option resv) :
    mctx C ->
    hread_req_at n m = Some req ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_excl (Interface.ReadReq.access_kind req) = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ∃ w : bv (8 * n),
         ⌜read_bytes σ.(mem) (Interface.ReadReq.pa req) n = Some w⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp σ ∗
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
    iIntros (σ oth) "_ Hσ".
    destruct (decide (footprint (Interface.ReadReq.pa req) n ## oth))
      as [Hfree|Hblocked].
    - (* the read, now reserving *)
      iMod ("H" $! σ with "Hσ") as (w) "[%Hrb Hk]".
      iModIntro. iExists (C (K (inl (w, None)))), σ,
        (Some (snap_of (Interface.ReadReq.pa req) n w)).
      iSplitR.
      { iPureIntro. rewrite /mnode_step. cbn beta iota.
        rewrite Hdev. cbn beta iota.
        right. split; [exact Hexcl|]. right. split; [exact Hfree|].
        exists w. split; [exact (read_bytes_spec _ _ _ _ Hrb)|]. done. }
      iNext. iIntros (m' σ' rv') "%Hstep".
      rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
      rewrite Hdev in Hstep. cbn beta iota in Hstep.
      destruct Hstep as [(Hex & _) | (_ & [(Hov & _) | (_ & w' & Hbytes' & -> & -> & ->)])];
        [congruence|done|].
      assert (w' = w) as ->.
      { apply bv_eq_of_bytes. intros j Hj.
        pose proof (read_bytes_spec _ _ _ _ Hrb j Hj) as H0.
        pose proof (Hbytes' j Hj) as H1.
        rewrite H1 in H0. apply Some_inj in H0. exact H0. }
      iMod "Hk" as "[Hσ HWP]". iModIntro. iFrame "Hσ".
      iIntros "Hfrag". rewrite -(Hres w). iApply ("HWP" with "Hfrag").
    - (* blocked: self-loop, own stale reservation dropped, premise intact *)
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
      iExists (Interface.Next (Interface.MemRead n req) (fun v => C (K v))),
        σ, None.
      iSplitR.
      { iPureIntro. rewrite /mnode_step. cbn beta iota.
        rewrite Hdev. cbn beta iota.
        right. split; [exact Hexcl|]. left. done. }
      iNext. iIntros (m' σ' rv') "%Hstep".
      rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
      rewrite Hdev in Hstep. cbn beta iota in Hstep.
      destruct Hstep as [(Hex & _) | (_ & [(_ & -> & -> & ->) | (Hfree & _)])];
        [congruence| |done].
      iMod "Hmask" as "_". iModIntro. iFrame "Hσ".
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
    (∀ σ, ⌜read_bytes σ.(mem) (Interface.WriteReq.pa req) n = Some w⌝ -∗
       mstate_interp σ ={⊤,∅}=∗
       ▷ (|={∅,⊤}=> mstate_interp
              (MState σ.(sregs)
                 (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
                    (Interface.WriteReq.value req)) σ.(mdev)) ∗
            (resv_frag cpu_id None -∗
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
    iIntros (σ oth) "%Hok Hσ".
    pose proof (snap_of_read_bytes _ _ _ _ Hn (Hok _ eq_refl)) as Hrb.
    destruct (decide (footprint (Interface.WriteReq.pa req) n ## oth))
      as [Hfree|Hblocked].
    - (* the write, at the pinned old value *)
      iMod ("H" $! σ with "[//] Hσ") as "Hk".
      iModIntro.
      iExists (C (K (inl None))),
        (MState σ.(sregs)
           (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
              (Interface.WriteReq.value req)) σ.(mdev)), None.
      iSplitR.
      { iPureIntro. rewrite /mnode_step. cbn beta iota.
        rewrite Hdev. cbn beta iota. right. done. }
      iNext. iIntros (m' σ' rv') "%Hstep".
      rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
      rewrite Hdev in Hstep. cbn beta iota in Hstep.
      destruct Hstep as [(Hov & _) | (_ & -> & -> & ->)]; [done|].
      iMod "Hk" as "[Hσ HWP]". iModIntro. iFrame "Hσ".
      iIntros "Hfrag". rewrite -Hres. iApply ("HWP" with "Hfrag").
    - (* blocked (never, once reservations are pairwise disjoint -- but the
         rule need not know): self-loop, frag and premise intact *)
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
      iExists (Interface.Next (Interface.MemWrite n req) (fun v => C (K v))),
        σ, (Some (snap_of (Interface.WriteReq.pa req) n w)).
      iSplitR.
      { iPureIntro. rewrite /mnode_step. cbn beta iota.
        rewrite Hdev. cbn beta iota. left. done. }
      iNext. iIntros (m' σ' rv') "%Hstep".
      rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
      rewrite Hdev in Hstep. cbn beta iota in Hstep.
      destruct Hstep as [(_ & -> & -> & ->) | (Hfree & _)]; [|done].
      iMod "Hmask" as "_". iModIntro. iFrame "Hσ".
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
    { intros oth0 σ0 r0 m'0 σ'0 r'0 Hs.
      rewrite /mnode_step in Hs. cbn beta iota in Hs.
      rewrite Hdev in Hs. cbn beta iota in Hs.
      destruct Hs as (_ & _ & _ & _ & _ & ->). done. }
    iIntros (σ oth rv) "Hσ".
    iMod ("H" $! σ with "Hσ") as (w d') "[%Hdr Hk]".
    iModIntro. iExists (C (K (inl (w, None)))), (MState σ.(sregs) σ.(mem) d'), rv.
    iSplitR.
    { iPureIntro. rewrite /mnode_step. cbn beta iota.
      rewrite Hdev. cbn beta iota.
      exists w, d'. done. }
    iNext. iIntros (m' σ' rv') "%Hstep".
    rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
    rewrite Hdev in Hstep. cbn beta iota in Hstep.
    destruct Hstep as (w' & d'' & Hdr' & -> & -> & ->).
    rewrite Hdr in Hdr'. injection Hdr' as <- <-.
    iMod "Hk" as "[Hσ HWP]". iModIntro.
    rewrite -(Hres w). by iFrame.
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
    iIntros (σ oth) "_ Hσ".
    iMod ("H" $! σ with "Hσ") as (d') "[%Hdw Hk]".
    iModIntro. iExists (C (K (inl None))), (MState σ.(sregs) σ.(mem) d'), None.
    iSplitR.
    { iPureIntro. rewrite /mnode_step. cbn beta iota.
      rewrite Hdev. cbn beta iota.
      exists d'. done. }
    iNext. iIntros (m' σ' rv') "%Hstep".
    rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
    rewrite Hdev in Hstep. cbn beta iota in Hstep.
    destruct Hstep as (d'' & Hdw' & -> & -> & ->).
    rewrite Hdw in Hdw'. injection Hdw' as <-.
    iMod "Hk" as "[Hσ HWP]". iModIntro. iFrame "Hσ".
    iIntros "Hfrag". rewrite -Hres. iApply ("HWP" with "Hfrag").
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE [swp] FORMS.  Same four rules, phrased so a caller composing a   *)
  (* sub-monad by [swp_bind] never has to name a context: the event fires *)
  (* and the proof continues at the RESUME, still in [swp].               *)
  (* ------------------------------------------------------------------ *)

  Lemma swp_hart_ram_read {X : Type} (n : N) (req : Interface.ReadReq.t n)
      (m : M X) (Φ : X -> iProp Σ) :
    hread_req_at n m = Some req ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_excl (Interface.ReadReq.access_kind req) = false ->
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ∃ w : bv (8 * n),
         ⌜read_bytes σ.(mem) (Interface.ReadReq.pa req) n = Some w⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp σ ∗
              swp (hread_resume (bv_unsigned w) m) Φ)) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj Hdev Hexcl) "#Hcert H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_ram_read C n req m HC Hproj Hdev Hexcl
              with "Hcert [H Hcont]").
    iIntros (σ) "Hσ". iMod ("H" $! σ with "Hσ") as (w) "[%Hrb Hk]".
    iModIntro. iExists w. iSplitR; [done|]. iNext.
    iMod "Hk" as "[Hσ Hswp]". iModIntro. iFrame "Hσ".
    iApply (swp_use _ Φ C HC with "Hswp Hcont").
  Qed.

  Lemma swp_hart_ram_read_excl {X : Type} (n : N) (req : Interface.ReadReq.t n)
      (m : M X) (Φ : X -> iProp Σ) (rr : option resv) :
    hread_req_at n m = Some req ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_excl (Interface.ReadReq.access_kind req) = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ∃ w : bv (8 * n),
         ⌜read_bytes σ.(mem) (Interface.ReadReq.pa req) n = Some w⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp σ ∗
              (resv_frag cpu_id (Some (snap_of (Interface.ReadReq.pa req) n w)) -∗
               swp (hread_resume (bv_unsigned w) m) Φ))) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj Hdev Hexcl) "#Hcert Hfrag H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_ram_read_excl C n req m rr HC Hproj Hdev Hexcl
              with "Hcert Hfrag [H Hcont]").
    iIntros (σ) "Hσ". iMod ("H" $! σ with "Hσ") as (w) "[%Hrb Hk]".
    iModIntro. iExists w. iSplitR; [done|]. iNext.
    iMod "Hk" as "[Hσ Hswp]". iModIntro. iFrame "Hσ". iIntros "Hfrag".
    iApply (swp_use _ Φ C HC with "[Hswp Hfrag] Hcont"). by iApply "Hswp".
  Qed.

  Lemma swp_hart_ram_write {X : Type} (n : N) (req : Interface.WriteReq.t n)
      (m : M X) (Φ : X -> iProp Σ) (rr : option resv) :
    hwrite_req_at n m = Some req ->
    dev_addr (Interface.WriteReq.pa req) = false ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ▷ (|={∅,⊤}=> mstate_interp
              (MState σ.(sregs)
                 (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
                    (Interface.WriteReq.value req)) σ.(mdev)) ∗
            (resv_frag cpu_id None -∗ swp (hwrite_resume m) Φ))) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj Hdev) "#Hcert Hfrag H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_ram_write C n req m rr HC Hproj Hdev
              with "Hcert Hfrag [H Hcont]").
    iIntros (σ) "Hσ". iMod ("H" $! σ with "Hσ") as "Hk". iModIntro. iNext.
    iMod "Hk" as "[Hσ Hswp]". iModIntro. iFrame "Hσ". iIntros "Hfrag".
    iApply (swp_use _ Φ C HC with "[Hswp Hfrag] Hcont"). by iApply "Hswp".
  Qed.

  Lemma swp_hart_ram_write_cond {X : Type} (n : N) (req : Interface.WriteReq.t n)
      (m : M X) (Φ : X -> iProp Σ) (w : bv (8 * n)) :
    hwrite_req_at n m = Some req ->
    dev_addr (Interface.WriteReq.pa req) = false ->
    Z.of_N n < 18446744073709551616 ->
    gen_cert -∗
    resv_frag cpu_id (Some (snap_of (Interface.WriteReq.pa req) n w)) -∗
    (∀ σ, ⌜read_bytes σ.(mem) (Interface.WriteReq.pa req) n = Some w⌝ -∗
       mstate_interp σ ={⊤,∅}=∗
       ▷ (|={∅,⊤}=> mstate_interp
              (MState σ.(sregs)
                 (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
                    (Interface.WriteReq.value req)) σ.(mdev)) ∗
            (resv_frag cpu_id None -∗ swp (hwrite_resume m) Φ))) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj Hdev Hn) "#Hcert Hfrag H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_ram_write_cond C n req m w HC Hproj Hdev Hn
              with "Hcert Hfrag [H Hcont]").
    iIntros (σ) "%Hrb Hσ". iMod ("H" $! σ with "[//] Hσ") as "Hk".
    iModIntro. iNext.
    iMod "Hk" as "[Hσ Hswp]". iModIntro. iFrame "Hσ". iIntros "Hfrag".
    iApply (swp_use _ Φ C HC with "[Hswp Hfrag] Hcont"). by iApply "Hswp".
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
