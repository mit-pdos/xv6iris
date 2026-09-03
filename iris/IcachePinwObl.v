(* IcachePinwObl.v -- A6.145 4b-iii: the lock-free guard read's OBLIGATION.

   ilock's and iunlock's [lw a5,8(a0)] run with no lock held.  Under the
   word-set pin the ref cell is four RAW pinw ledger bytes inside
   [itable_body_pinw], so the load leaf is [WpSconfMem.wp_load_s_sconf_au_rel]
   with [Res := iref_pin_rows k w lo tst] (the window crossing the step out
   of [IcacheInv.iref_load_pinw_au] -- whose open already AGREED the
   caller's slice (g, lo) against the slot's liveness arm, so the window's
   pin floor IS the slice's), and THIS lemma is the leaf's read obligation:

   - the slice's ctx floor (carried by [IcacheRef.live_fracc] in every
     inode_ref/inode_shr bundle) cashes through the running context into
     the hart's view bound ([TsoCtx.own_context_floor_view]);
   - [TsoCtx.ledger_read_pinw_ok] then reads the WHOLE window off the pin:
     at every view the drain may choose, the four bytes assemble a member of
     [iref_set] -- a word in [1 .. IREFSLOTS], never 0, never torn.

   Stated at the [gstate] level ([tso_interp_at]); the consumer does the
   [tso_interp_of_at_gs] rewrite and the KT0 identity at its own site, the
   way [StartedInv.started_read_obl]'s consumers do. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth dfrac.
From iris.base_logic.lib Require Import invariants gen_heap own mono_nat.
Require Import SailStdpp.Base SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExec.
Require Import TsoMemPa TsoGhost TsoCtx.
Require Import CtxPinw.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import Xv6G.

Section IcachePinwObl.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{ICFG : icfg}.
  Context `{GEN : GenId}.
  Context `{XI : CurCtx}.

  (* A6.146: the credential's cash-in -- either arm of [cred_floor] buys
     the two-armed read licence at [lo]. *)
  Lemma cred_floor_vis `{CIDw : CpuId} (lo tl : nat) :
    (lo <= tl)%nat ->
    TsoCtx.own_context TsoCtx.cur_ctx -∗ IcacheRef.cred_floor lo tl -∗
    TsoCtx.own_context TsoCtx.cur_ctx ∗
    ∃ K : nat,
      view_lb view_name loglen_name (hart_agent cpu_id) K ∗
      TsoCtx.ledger_vis (hart_agent cpu_id) K lo.
  Proof.
    iIntros (Hlotl) "Hctx #Hfl".
    iDestruct "Hfl" as "[Hflc | (%a & Hw)]".
    - iDestruct (TsoCtx.own_context_floor_view TsoCtx.cur_ctx tl
                   with "Hctx Hflc") as "[Hctx Hview]".
      iDestruct "Hview" as (K) "[#HvK %HtlK]".
      iFrame "Hctx". iExists K. iFrame "HvK".
      iApply TsoCtx.ledger_vis_below. lia.
    - iDestruct (TsoCtx.own_context_wrote_vis TsoCtx.cur_ctx lo a
                   with "Hctx Hw") as "[Hctx Hview]".
      iDestruct "Hview" as (K) "[#HvK #Hvis]".
      iFrame "Hctx". iExists K. iFrame "HvK Hvis".
  Qed.

  Lemma iref_read_obl `{CIDw : CpuId} (g : gstate) (k : nat)
      (w : mword 32) (lo tst tl : nat) :
    (lo <= tl)%nat ->
    tso_interp_at riscv_eraGS g -∗
    TsoCtx.own_context TsoCtx.cur_ctx -∗
    IcacheRef.cred_floor lo tl -∗
    iref_pin_rows k w lo tst -∗
    ⌜forall tvr : nat, (g.(gtv) cpu_id <= tvr)%nat ->
       (exists v : mword 32,
          tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tvr
            (i_ref (ientry k)) 4 v)
       /\ (forall v : mword 32,
             tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tvr
               (i_ref (ientry k)) 4 v ->
             (0 < bv_unsigned v < 2 ^ 31)%Z)⌝.
  Proof.
    iIntros (Hlotl) "Hint Hctx #Hfl Hrows".
    iDestruct (cred_floor_vis lo tl Hlotl with "Hctx Hfl")
      as "[Hctx Hview]".
    iDestruct "Hview" as (K) "[#HvK #Hvis]".
    iAssert ([∗ list] j ∈ seq 0 4, ∃ t : nat,
        TsoCtx.phys_ledger_pinw (pa_add (i_ref (ientry k)) j) (DfracOwn 1)
          (nth_byte w j) t
          (TsoMemPa.TsPinw (i_ref (ientry k)) 4 j lo iref_set))%I
      with "[Hrows]" as "Hrows".
    { iApply (big_sepL_mono with "Hrows"). iIntros (i j Hij) "H".
      iDestruct "H" as (t) "[_ H]". iExists t. iFrame "H". }
    iDestruct (TsoCtx.ledger_read_pinw_vis g (i_ref (ientry k)) 4 lo K
                 iref_set (DfracOwn 1) (nth_byte w) ltac:(lia)
                 with "Hint HvK Hvis Hrows") as %Hrd.
    iPureIntro. intros tvr Htvr.
    destruct (Hrd tvr Htvr) as (fw & Hmem & Hbytes).
    pose proof Hmem as (z & Hz & Hfz).
    split.
    - exists (mword_of_int z : mword 32).
      intros j HjN.
      assert (Hj4 : (j < 4)%nat) by lia.
      rewrite (Hbytes j Hj4) (Hfz j Hj4). reflexivity.
    - intros v Hv.
      apply (iref_set_read v fw); [exact Hmem |].
      intros j Hj4.
      assert (HjN : (N.of_nat j < 4)%N) by lia.
      specialize (Hv j HjN). rewrite (Hbytes j Hj4) in Hv.
      injection Hv. auto.
  Qed.

  (* THE LOCK HOLDER's EXACT READ obligation: the A6.144 floor row covers
     every stamp in the window, so the read is the LATEST value -- exactly
     [iref_word M k] -- at every view the drain may choose. *)
  Lemma iref_read_locked_obl `{CIDw : CpuId} (g : gstate)
      (k : nat) (w : mword 32) (lo tst tl : nat) :
    (tst <= tl)%nat ->
    tso_interp_at riscv_eraGS g -∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    TsoCtx.own_context TsoCtx.cur_ctx -∗
    TsoCtx.ctx_floor TsoCtx.cur_ctx tl -∗
    iref_pin_rows k w lo tst -∗
    ⌜forall tvr : nat, (g.(gtv) cpu_id <= tvr)%nat ->
       tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tvr
         (i_ref (ientry k)) 4 w⌝.
  Proof.
    iIntros (Htsttl) "Hint Hgh Hctx #Hfl Hrows".
    iDestruct (TsoCtx.own_context_floor_view TsoCtx.cur_ctx tl with "Hctx Hfl")
      as "[Hctx Hview]".
    iDestruct "Hview" as (K) "[#HvK %HtlK]".
    iDestruct (view_lb_le view_name loglen_name (hart_agent cpu_id) K tl HtlK
                 with "HvK") as "#Hvtl".
    iAssert ([∗ list] j ∈ seq 0 4, ∃ t : nat, ⌜(t <= tl)%nat⌝ ∗
        TsoCtx.phys_ledger_pinw (pa_add (i_ref (ientry k)) j) (DfracOwn 1)
          (nth_byte w j) t
          (TsoMemPa.TsPinw (i_ref (ientry k)) 4 j lo iref_set))%I
      with "[Hrows]" as "Hrows".
    { iApply (big_sepL_mono with "Hrows"). iIntros (i j Hij) "H".
      iDestruct "H" as (t) "[%Ht H]". iExists t. iFrame "H".
      iPureIntro. lia. }
    iDestruct (CtxPinw.ledger_read_pinw_latest g (i_ref (ientry k)) 4 tl
                 (DfracOwn 1) (nth_byte w)
                 (fun j => TsoMemPa.TsPinw (i_ref (ientry k)) 4 j lo iref_set)
                 with "Hint Hgh Hvtl Hrows") as %Hrd.
    iPureIntro. intros tvr Htvr j HjN.
    assert (Hj4 : (j < 4)%nat) by lia.
    exact (Hrd tvr Htvr j Hj4).
  Qed.

  (* the LEAF-SHAPED exact read: existence + uniqueness in the two-part
     form [WpAu4.wp_lw_au_rel_s_sconf]'s obligation wants, uniqueness by
     byte extensionality off [tso_read]'s functionality. *)
  Lemma iref_read_locked_all `{CIDw : CpuId} (g : gstate)
      (k : nat) (w : mword 32) (lo tst tl : nat) :
    (tst <= tl)%nat ->
    tso_interp_at riscv_eraGS g -∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    TsoCtx.own_context TsoCtx.cur_ctx -∗
    TsoCtx.ctx_floor TsoCtx.cur_ctx tl -∗
    iref_pin_rows k w lo tst -∗
    ⌜forall tvr : nat, (g.(gtv) cpu_id <= tvr)%nat ->
       (exists v : mword 32,
          tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tvr
            (i_ref (ientry k)) (Z.to_N 4) v)
       /\ (forall v : mword 32,
             tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tvr
               (i_ref (ientry k)) (Z.to_N 4) v -> v = w)⌝.
  Proof.
    iIntros (Htsttl) "Hint Hgh Hctx #Hfl Hrows".
    iDestruct (iref_read_locked_obl g k w lo tst tl Htsttl
                 with "Hint Hgh Hctx Hfl Hrows") as %HH.
    iPureIntro. intros tvr Htvr.
    specialize (HH tvr Htvr).
    split.
    - exists w. exact HH.
    - intros v Hv. apply (bv_eq_of_bytes (n := 4%N)).
      intros j Hj.
      specialize (Hv j Hj). specialize (HH j Hj).
      rewrite Hv in HH. injection HH as HB. apply bv_eq. exact HB.
  Qed.

End IcachePinwObl.
