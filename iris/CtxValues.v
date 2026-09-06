(* CtxValues.v -- §0.47′: [ctx_values ξ a S], the context-relative upper
   bound on a cell's observable values.

   "Your raw points-to has the history from the beginning of time, but
   almost always what you want is the history from the possible race
   window, and that race window doesn't start from 0 each time."  (owner)

   [ctx_values ξ a dq S] says: there is a floor position B, at or below
   ξ's bound (or ξ's own write), such that every value ξ's hart can ever
   read from [a] is in S.  It is an UPPER BOUND -- contexts move up and
   the observable set only shrinks -- so the fact is stable, and it makes
   no claim about "the value at the bound" (there is no such stable
   thing).  Internally it is the LANDED pin arm plus [ctx_pointsto]'s own
   two-arm justification:

     ∃ B v t, phys_ledger_pin a dq v t B S ∗
              (ctx_floor ξ B  ∨  ctx_wrote ξ B a ∗ cv_touch a B S)

   CLEAN arm: ξ's bound has passed B, so ξ's hart's view has too, and
   [ledger_read_pin_ok] gives reads ∈ S.  DIRTY arm: the message at B is
   ξ's hart's OWN (the dirty registry is the authorship witness -- no
   author field, no new ghost), so the descent can never settle below B
   at any view, and [TsoMemPa.pin_ok_author] gives reads ∈ S with no
   view receipt at all.  The boot hart holds the kernel page table this
   way; a secondary holds the SAME fact at its own context via the clean
   arm after the started barrier.

   THE THREE RULES (§0.47′):
     read  : { ctx_values ξ a S } read a { v. v ∈ S }   (ctx_values_read)
     write : open the invariant, write any v' ∈ S, close it unchanged
             (the landed [ledger_store_win_pin_ok]; a member write is
             invisible to an upper bound)
     mint  : the creator converts its own [ctx_phys_pointsto] cells
             (ctx_values_mint); establishment is where the invariant is
             born, and B is the creator's own write.                     *)

From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap.
From stdpp.bitvector Require Import definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import csum excl agree.
From iris.base_logic.lib Require Import gen_heap ghost_map own.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto.
Require Import TsoMemPa TsoGhost TsoCtx.

Local Open Scope Z_scope.

Section CtxValues.
  Context `{!riscvGS Σ}.

  (* the floor write's receipt: at B the log holds a message writing a
     family byte to [a] (or B = 0, the image floor, where [pin_ok]
     already covers every view).  Persistent: it is a log-position
     agreement plus pure facts. *)
  Definition cv_touch (a : Arch.pa) (B : nat) (Sv : gset (bv 8)) : iProp Σ :=
    (⌜B = 0%nat⌝ ∨
     ∃ (i : nat) (m : TsoMemPa.pwmsg) (b : bv 8),
       ⌜B = S i⌝ ∗ ledger_msg_at i m ∗
       ⌜TsoMemPa.msg_byte m a = Some b⌝ ∗ ⌜b ∈ Sv⌝)%I.

  Global Instance cv_touch_persistent a B Sv : Persistent (cv_touch a B Sv).
  Proof. rewrite /cv_touch. apply _. Qed.
  Global Instance cv_touch_timeless a B Sv : Timeless (cv_touch a B Sv).
  Proof. rewrite /cv_touch. apply _. Qed.

  (* TWO LOGS (relaxed-ww.md §2.10): the justification is the cell's own,
     UNCHANGED -- [key_at]'s two arms with the dirty arm's floor receipt,
     and the chain.  The pin's bound is the stamp itself: the racy payload
     is the LEGACY one-log [pin_ok] (stage E re-founds it), and what the
     reader consumes is the stamp's drain position ([cv_key_read]). *)
  Definition ctx_values (ξ : CtxId) (a : Arch.pa) (dq : dfrac)
      (Sv : gset (bv 8)) : iProp Σ :=
    (∃ (t : nat) (v : bv 8),
       phys_ledger_pin a dq v t t Sv ∗
       chain_ev chain_name t ∗
       ((∃ p : nat, dpos_ev dpos_name t p ∗ ctx_floor ξ p) ∨
        (ctx_wrote ξ t a ∗ cv_touch a t Sv)))%I.

  Global Instance ctx_values_timeless ξ a dq Sv :
    Timeless (ctx_values ξ a dq Sv).
  Proof. rewrite /ctx_values. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (* interp extractions (pure outputs; callers use them under a pure     *)
  (* [iAssert], which keeps the context)                                 *)
  (* ------------------------------------------------------------------ *)

  Lemma cv_msg_lookup (g : gstate) (i : nat) (m : TsoMemPa.pwmsg) :
    tso_interp_at riscv_eraGS g -∗ ledger_msg_at i m -∗
    ⌜g.(glog) !! i = Some m⌝.
  Proof.
    iIntros "Hint #Hm".
    iDestruct "Hint"
      as "(%TM & %LM & %DP & %FR & %CH & Hts & %Hdom & %Htie & Hlm & %HLM & Hlen & Hv & Hdp & #Hdps & %Hdpo & Hdl & Hfr & #Hfrs & %Hfro & Hch & %Hcho & %Hmm)".
    iDestruct (ghost_map_lookup with "Hlm Hm") as %HL.
    iPureIntro. rewrite -HLM. exact HL.
  Qed.

  Lemma cv_pin_ok (g : gstate) (a : Arch.pa) (dq : dfrac)
      (v : bv 8) (t B : nat) (Sv : gset (bv 8)) :
    tso_interp_at riscv_eraGS g -∗ phys_ledger_pin a dq v t B Sv -∗
    ⌜TsoMemPa.pin_ok g.(gimg) g.(glog) a B Sv⌝.
  Proof.
    iIntros "Hint [Hp Hts]".
    iDestruct "Hint"
      as "(%TM & %LM & %DP & %FR & %CH & Hauth & %Hdom & %Htie & Hlm & %HLM & Hlen & Hv & Hdp & #Hdps & %Hdpo & Hdl & Hfr & #Hfrs & %Hfro & Hch & %Hcho & %Hmm)".
    iDestruct (ghost_map_lookup with "Hauth Hts") as %HTM.
    iPureIntro.
    exact (TsoMemPa.ts_ok_pin _ _ _ _ _ _ _ _ (Htie _ _ HTM) eq_refl).
  Qed.

  (* THE READ AT THE FLOOR'S DRAIN POSITION.  A pinned cell's bound [B] is
     its publication FLOOR: the stamp the family was pinned at (the cell may
     have been restamped since, by family writes through the pin gate).  A
     reader whose view has passed the floor's drain position sees the floor
     write or a later one to the byte -- [chain_ev] at the floor is what
     puts every earlier write BELOW it in the drain order -- and the pin's
     store gates keep every later write in the family.
     relaxed-ww STAGE E: the two-log pin theory ([TsoMemPa.pin_ok] is legacy,
     over the issue log alone); tracked in claude-notes/projects/relaxed-ww.md. *)
  Lemma cv_key_read `{CID : CpuId} (g : gstate) (a : Arch.pa) (dq : dfrac)
      (v : bv 8) (t B p : nat) (Sv : gset (bv 8)) :
    tso_interp_at riscv_eraGS g -∗
    dpos_ev dpos_name B p -∗
    TsoGhost.view_lb view_name dlen_name (hart_agent cpu_id) p -∗
    chain_ev chain_name B -∗
    phys_ledger_pin a dq v t B Sv -∗
    ⌜forall tv, (g.(gtv) cpu_id <= tv)%nat ->
       exists b, TsoMemPa.tso_read g.(gimg) g.(glog) g.(gdlog) (hart_agent cpu_id) tv a
                 = Some b /\ b ∈ Sv⌝.
  Proof.
  Admitted.

  Lemma cv_latest (g : gstate) (a : Arch.pa) (dq : dfrac)
      (v : bv 8) (t : nat) :
    tso_interp_at riscv_eraGS g -∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    phys_pointsto a dq v -∗
    (a ↪[ts_name]{dq} ((t, TsoMemPa.ts_pay_none) : TsoMemPa.ts_elem)) -∗
    ⌜TsoMemPa.latest g.(gimg) g.(glog) a t v⌝.
  Proof.
    iIntros "Hint Hgh Hp Hts".
    iDestruct "Hint"
      as "(%TM & %LM & %DP & %FR & %CH & Hauth & %Hdom & %Htie & Hlm & %HLM & Hlen & Hv & Hdp & #Hdps & %Hdpo & Hdl & Hfr & #Hfrs & %Hfro & Hch & %Hcho & %Hmm)".
    iDestruct (ghost_map_lookup with "Hauth Hts") as %HTM.
    iEval (rewrite /phys_pointsto) in "Hp".
    iDestruct "Hp" as "[Hp %Hram]".
    iDestruct (gen_heap_valid with "Hgh Hp") as %Hgm.
    iPureIntro.
    destruct (TsoMemPa.ts_ok_latest _ _ _ _ _ _ (Htie _ _ HTM))
      as (v0 & Hgm0 & Hlat).
    rewrite Hgm in Hgm0. by injection Hgm0 as <-.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE MINT: the creator converts its own context cell.  The clean/    *)
  (* dirty justification travels UNCHANGED; the dirty case additionally  *)
  (* records the floor write's receipt off the creator's own token       *)
  (* (dirty_ok's own-message arm IS the authorship witness).             *)
  (* ------------------------------------------------------------------ *)

  Lemma ctx_values_mint `{CID : CpuId} (g : gstate) (ξ : CtxId)
      (a : Arch.pa) (v : bv 8) (Sv : gset (bv 8)) :
    v ∈ Sv ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ctx_phys_pointsto ξ a (DfracOwn 1) v ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗
    own_context ξ ∗
    ctx_values ξ a (DfracOwn 1) Sv.
  Proof.
    iIntros (Hv) "Hgh Hint Hrun Hc".
    rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def.
    iDestruct "Hc" as (t) "(Hp & Hts & #Hkey & #Hchain)".
    iAssert (⌜TsoMemPa.latest g.(gimg) g.(glog) a t v⌝)%I as %Hlat.
    { iApply (cv_latest with "Hint Hgh Hp Hts"). }
    iMod (ledger_pin_mint g a v t t Sv (le_n t) Hv with "Hgh Hint [Hp Hts]")
      as "(Hgh & Hint & Hpin)".
    { rewrite /phys_ledger_at. iFrame "Hp Hts". }
    iDestruct "Hkey" as "[(%p & #Hdp & #Hfl) | #Hdirty]".
    - (* CLEAN: the stamp is drained under ξ's bound *)
      iModIntro. iFrame "Hgh Hint Hrun".
      iExists t, v. iFrame "Hpin Hchain". iLeft. iExists p. iFrame "Hdp Hfl".
    - (* DIRTY: ξ's own write; record the receipt off the token *)
      destruct t as [|i].
      + (* stamp 0: the image floor, drained at every position *)
        iModIntro. iFrame "Hgh Hint Hrun".
        iExists 0%nat, v. iFrame "Hpin Hchain". iLeft. iExists 0%nat.
        iSplit; [iApply TsoGhost.dpos_ev_0 | rewrite /ctx_floor; iApply TsoGhost.llb_0].
      + (* stamp S i: [latest] says log !! i writes v to a *)
        destruct Hlat as [Hbyte _].
        rewrite /TsoMemPa.log_byte in Hbyte.
        destruct (g.(glog) !! i) as [m|] eqn:Hlog; last done.
        (* the token's dirty_ok at (S i, a): drained under the bound, or own *)
        rewrite own_context_unseal /own_context_def.
        iDestruct "Hrun" as (Btok K D) "([Hb Hd] & #HK & %HBK & #Hoks)".
        iDestruct (TsoGhost.dset_lookup with "Hd Hdirty") as %HinD.
        iDestruct (big_sepS_elem_of _ _ _ HinD with "Hoks") as "#Hok".
        iDestruct "Hok" as "[#Hdp | Hown]".
        * (* drained under the token's bound: the clean arm at [Btok] *)
          iEval (cbn) in "Hdp".
          iDestruct (TsoGhost.llb_get with "Hb") as "[Hb #Hllb]".
          iModIntro. iFrame "Hgh Hint".
          iSplitL "Hb Hd".
          { iExists Btok, K, D. iFrame "Hb Hd HK Hoks". by iPureIntro. }
          iExists (S i), v. iFrame "Hpin Hchain". iLeft. iExists Btok.
          iFrame "Hdp". rewrite /ctx_floor. iExact "Hllb".
        * (* the own-message arm: the receipt *)
          iDestruct "Hown" as (i' m') "(%Hii & #Hm & %Htid)".
          cbn in Hii. injection Hii as <-.
          iAssert (⌜g.(glog) !! i = Some m'⌝)%I as %Hlog'.
          { iApply (cv_msg_lookup with "Hint Hm"). }
          rewrite Hlog in Hlog'. injection Hlog' as <-.
          iModIntro. iFrame "Hgh Hint".
          iSplitL "Hb Hd".
          { iExists Btok, K, D. iFrame "Hb Hd HK Hoks". by iPureIntro. }
          iExists (S i), v. iFrame "Hpin Hchain". iRight.
          iSplit; [iExact "Hdirty" |].
          iRight. iExists i, m, v. iFrame "Hm".
          iSplit; [by iPureIntro |]. iSplit; by iPureIntro.
  Qed.

  Definition cv_own (h : agent) (a : Arch.pa) (p : nat) : iProp Σ :=
    (∃ (i : nat) (m : TsoMemPa.pwmsg) (b : bv 8),
       ⌜p = S i⌝ ∗ ledger_msg_at i m ∗
       ⌜TsoMemPa.msg_byte m a = Some b⌝ ∗ ⌜TsoMemPa.pm_tid m = h⌝)%I.

  Global Instance cv_own_persistent h a p : Persistent (cv_own h a p).
  Proof. rewrite /cv_own. apply _. Qed.
  Global Instance cv_own_timeless h a p : Timeless (cv_own h a p).
  Proof. rewrite /cv_own. apply _. Qed.

  (* THE AUTHOR'S READ: the floor is the author's OWN message, so the
     descent settles on it or on a later family write -- store forwarding
     ([TsoMemPa.visibleb]'s own arm) if it is still pending, the drain flat
     if not, where [chain_ev] puts every earlier write to the byte below it.
     No view receipt, no token.
     relaxed-ww STAGE E: the author arm over two logs ([TsoMemPa.pin_ok_author]
     is the legacy one-log statement); tracked in
     claude-notes/projects/relaxed-ww.md. *)
  Lemma cv_own_read (g : gstate) (a : Arch.pa) (dq : dfrac)
      (v : bv 8) (t B : nat) (Sv : gset (bv 8)) (h : agent) :
    tso_interp_at riscv_eraGS g -∗
    chain_ev chain_name B -∗
    phys_ledger_pin a dq v t B Sv -∗
    cv_own h a B -∗
    ⌜forall tv, exists b,
       TsoMemPa.tso_read g.(gimg) g.(glog) g.(gdlog) h tv a = Some b /\ b ∈ Sv⌝.
  Proof.
  Admitted.


  (* ------------------------------------------------------------------ *)
  (* THE RACY READ RULE: you get one of the values from the set.         *)
  (* ------------------------------------------------------------------ *)

  Lemma ctx_values_read `{CID : CpuId} (g : gstate) (ξ : CtxId)
      (a : Arch.pa) (dq : dfrac) (Sv : gset (bv 8)) :
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ctx_values ξ a dq Sv -∗
    ⌜forall tv, (g.(gtv) cpu_id <= tv)%nat ->
       exists b, TsoMemPa.tso_read g.(gimg) g.(glog) g.(gdlog) (hart_agent cpu_id) tv a
                 = Some b /\ b ∈ Sv⌝.
  Proof.
    iIntros "Hint Hrun Hc".
    iDestruct "Hc" as (t v) "(Hpin & #Hchain & Harm)".
    rewrite own_context_unseal /own_context_def.
    iDestruct "Hrun" as (Btok K D) "([Hb Hd] & #HK & %HBK & #Hoks)".
    iDestruct "Harm" as "[(%p & #Hdp & #Hfl) | [#Hdirty #Htouch]]".
    - (* CLEAN: the stamp is drained under ξ's bound, which this hart's floor
         has passed *)
      rewrite /ctx_floor.
      iDestruct (TsoGhost.llb_valid with "Hb Hfl") as %HpB.
      iDestruct (TsoGhost.view_lb_le view_name dlen_name (hart_agent cpu_id) K p
                   ltac:(lia) with "HK") as "#Hp".
      iApply (cv_key_read with "Hint Hdp Hp Hchain Hpin").
    - (* DIRTY: the token certifies the stamp is drained under the bound, or
         that the message is this hart's own *)
      iDestruct (TsoGhost.dset_lookup with "Hd Hdirty") as %HinD.
      iDestruct (big_sepS_elem_of _ _ _ HinD with "Hoks") as "#Hok".
      iDestruct "Hok" as "[#Hdp | Hown]".
      + iEval (cbn) in "Hdp".
        iDestruct (TsoGhost.view_lb_le view_name dlen_name (hart_agent cpu_id) K Btok
                     HBK with "HK") as "#HB".
        iApply (cv_key_read with "Hint Hdp HB Hchain Hpin").
      + (* own: the author's read, at every view *)
        iDestruct "Hown" as (i' m') "(%Hii & #Hm' & %Htid)". cbn in Hii.
        iDestruct "Htouch" as "[%HB0 | Hseed]"; [rewrite HB0 in Hii; discriminate Hii|].
        iDestruct "Hseed" as (i m b) "(%HBi & #Hm & %Hmb & %HbS)".
        rewrite HBi in Hii. injection Hii as <-.
        iAssert (⌜g.(glog) !! i = Some m⌝)%I as %Hlog.
        { iApply (cv_msg_lookup with "Hint Hm"). }
        iAssert (⌜g.(glog) !! i = Some m'⌝)%I as %Hlog'.
        { iApply (cv_msg_lookup with "Hint Hm'"). }
        rewrite Hlog in Hlog'. injection Hlog' as <-.
        iDestruct (cv_own_read g a dq v t t Sv (hart_agent cpu_id)
                     with "Hint Hchain Hpin []") as %Hrd.
        { iExists i, m, b. iFrame "Hm". iPureIntro. split_and!; done. }
        iPureIntro. intros tv _. exact (Hrd tv).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE KERNEL-SLOT READ (relaxed-ww.md, the two-log slot credential): a
     run of per-byte pins at ∃-floors under the tree's ISSUE bound [B],
     each byte carrying one of three anchors for its floor [Ba]:
       - floor 0, the image;
       - the BOOT HART's own message ([cv_own 0]) -- minted at
         establishment with no drain and no view, read by hart 0 through
         store forwarding and by a secondary through hart 0's release
         fence RECORD ([TsoCtx.fr_at 0 L M], [B <= L]): the started flag
         drains above [M] and the anchor drained under it;
       - a stamp already DRAINED at the mint, under the tree's DRAIN bound
         [Bd] ([kpt_dbound], the boot hart's view receipt at the mint) --
         read by hart 0 through that receipt and by a secondary through
         [Bd <= V], off the started flag's drain position.
     The reader's credential is [cv_boot_cred B]: the boot hart's view
     receipt at [Bd], or a secondary's [kpt_pub B]. *)

  (* THE TREE'S DRAIN BOUND: a one-shot agreement in [KptGhost.kptbR]'s
     shape, shot at establishment at the boot publisher's view receipt.  It
     lives HERE (below [PtTree]) so the slot rows can name it by agreement
     rather than by an index in the tier. *)
  Definition kptd_unset : iProp Σ :=
    own kptd_name (Cinl (Excl ()) : kptbR).
  Definition kpt_dbound (Bd : nat) : iProp Σ :=
    own kptd_name (Cinr (to_agree (Bd : leibnizO nat)) : kptbR).

  Global Instance kptd_unset_timeless : Timeless kptd_unset.
  Proof. apply _. Qed.
  Global Instance kpt_dbound_timeless Bd : Timeless (kpt_dbound Bd).
  Proof. apply _. Qed.
  Global Instance kpt_dbound_persistent Bd : Persistent (kpt_dbound Bd).
  Proof. apply own_core_persistent, Cinr_core_id, _. Qed.

  Lemma kptd_shoot (Bd : nat) : kptd_unset ==∗ kpt_dbound Bd.
  Proof.
    iIntros "H". iMod (own_update with "H") as "$"; [|done].
    apply cmra_update_exclusive; done.
  Qed.

  Lemma kpt_dbound_agree (Bd Bd' : nat) :
    kpt_dbound Bd -∗ kpt_dbound Bd' -∗ ⌜ Bd = Bd' ⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite -Cinr_op Cinr_valid to_agree_op_valid_L in Hv.
    by iPureIntro.
  Qed.

  (* a byte's anchor at its floor *)
  Definition kpt_anchor (a : Arch.pa) (Ba : nat) : iProp Σ :=
    (⌜Ba = 0%nat⌝ ∨ cv_own 0%nat a Ba ∨
     ∃ Bd : nat, kpt_dbound Bd ∗ dpos_ev dpos_name Ba Bd)%I.

  Global Instance kpt_anchor_persistent a Ba : Persistent (kpt_anchor a Ba).
  Proof. rewrite /kpt_anchor. apply _. Qed.
  Global Instance kpt_anchor_timeless a Ba : Timeless (kpt_anchor a Ba).
  Proof. rewrite /kpt_anchor. apply _. Qed.

  (* A SECONDARY'S CREDENTIAL: a view receipt at [V]; hart 0's release
     record at some issue length [L >= B]; a message issued at or after
     [L] (the started flag) drained under [V]; and the drain bound under
     [V].  Assembled in [ProofMainSecondary] off the started read. *)
  Definition kpt_pub `{CID : CpuId} (B : nat) : iProp Σ :=
    (∃ (V L M s q Bd : nat),
       TsoGhost.view_lb view_name dlen_name (hart_agent cpu_id) V ∗
       fr_at 0%nat L M ∗ ⌜(B <= L)%nat⌝ ∗
       dpos_at dpos_name s q ∗ ⌜(L <= s)%nat /\ (q <= V)%nat⌝ ∗
       kpt_dbound Bd ∗ ⌜(Bd <= V)%nat⌝)%I.

  Global Instance kpt_pub_persistent `{CID : CpuId} B : Persistent (kpt_pub B).
  Proof. rewrite /kpt_pub. apply _. Qed.

  Definition cv_boot_cred `{CID : CpuId} (B : nat) : iProp Σ :=
    ((⌜hart_agent cpu_id = 0%nat⌝ ∗
      ∃ Bd : nat, kpt_dbound Bd ∗ TsoGhost.view_lb view_name dlen_name 0%nat Bd) ∨
     kpt_pub B)%I.

  Global Instance cv_boot_cred_persistent `{CID : CpuId} B :
    Persistent (cv_boot_cred B).
  Proof. rewrite /cv_boot_cred. apply _. Qed.

  Lemma cv_boot_cred_boot `{CID : CpuId} (B Bd : nat) :
    hart_agent cpu_id = 0%nat ->
    kpt_dbound Bd -∗ TsoGhost.view_lb view_name dlen_name 0%nat Bd -∗
    cv_boot_cred B.
  Proof.
    intros H0. iIntros "#Hd #Hv". iLeft.
    iSplit; [by iPureIntro|]. iExists Bd. iFrame "Hd Hv".
  Qed.

  Lemma cv_boot_cred_pub `{CID : CpuId} (B : nat) :
    kpt_pub B -∗ cv_boot_cred B.
  Proof. iIntros "H". iRight. iExact "H". Qed.


  (* a bounded choice principle: name the per-byte floors of a run *)
  Lemma big_sepL_seq_exist (n : nat) (Φ : nat -> nat -> iProp Σ) :
    ([∗ list] j ∈ seq 0 n, ∃ Bx : nat, Φ j Bx) -∗
    ∃ Bf : nat -> nat, [∗ list] j ∈ seq 0 n, Φ j (Bf j).
  Proof.
    iInduction n as [|n] "IH".
    - iIntros "_". iExists (fun _ => 0%nat). done.
    - rewrite !seq_S !big_sepL_app /=.
      iIntros "[Hb [Hlast _]]".
      iDestruct ("IH" with "Hb") as (Bf0) "Hb".
      iDestruct "Hlast" as (Bn) "Hlast".
      iExists (fun j => if decide (j = n) then Bn else Bf0 j).
      iSplitL "Hb".
      + iApply (big_sepL_impl with "Hb"). iIntros "!>" (k j Hkj) "H".
        apply lookup_seq in Hkj. destruct Hkj as [-> Hlt].
        destruct (decide (0 + k = n)%nat) as [Heq|Hne];
          [exfalso; lia | iExact "H"].
      + simpl. rewrite decide_True; [ | lia]. by iFrame "Hlast".
  Qed.

  (* the started flag's drain witness, at the machine *)
  Local Lemma dpos_at_pos (g : gstate) (s q : nat) :
    tso_interp_at riscv_eraGS g -∗ dpos_at dpos_name s q -∗
    ⌜∃ q0, g.(gdlog) !! q0 = Some s ∧ q = S q0⌝.
  Proof.
    iIntros "Hint #Hat".
    iDestruct "Hint"
      as "(%TM & %LM & %DP & %FR & %CH & Hauth & %Hdom & %Htie & Hlm & %HLM & Hlen & Hv & Hdp & #Hdps & %Hdpo & Hdl & Hfr & #Hfrs & %Hfro & Hch & %Hcho & %Hmm)".
    iDestruct (ghost_map_lookup with "Hdp Hat") as %HDP.
    iPureIntro. exact (proj1 (Hdpo _ _) HDP).
  Qed.

  (* ONE BYTE, under either credential *)
  Lemma cv_anchor_read `{CID : CpuId} (g : gstate) (a : Arch.pa)
      (dq : dfrac) (v : bv 8) (t Ba B : nat) (Sv : TsoMemPa.byteset) :
    (Ba <= B)%nat ->
    tso_interp_at riscv_eraGS g -∗
    cv_boot_cred B -∗
    phys_ledger_pin a dq v t Ba Sv -∗
    chain_ev chain_name Ba -∗
    kpt_anchor a Ba -∗
    ⌜forall (tv' : nat), (g.(gtv) cpu_id <= tv')%nat ->
       exists b, TsoMemPa.tso_read g.(gimg) g.(glog) g.(gdlog) (hart_agent cpu_id) tv' a
                 = Some b /\ b ∈ Sv⌝.
  Proof.
    intros HBa. iIntros "Hint #Hcred Hpin #Hchain #Han".
    iDestruct "Han" as "[%HBa0 | [#Hown | (%Bd & #Hd & #Hev)]]".
    - (* the image floor: drained at 0, visible at every view *)
      subst Ba.
      iDestruct (cv_key_read g a dq v t 0%nat 0%nat Sv
                   with "Hint [] [] Hchain Hpin") as %Hrd.
      { by iLeft. }
      { iApply TsoGhost.view_lb_0. }
      iPureIntro. exact Hrd.
    - (* the boot hart's own message *)
      iDestruct "Hcred" as "[[%H0 _] | Hpub]".
      + iEval (rewrite -H0) in "Hown".
        iDestruct (cv_own_read g a dq v t Ba Sv (hart_agent cpu_id)
                     with "Hint Hchain Hpin Hown") as %Hrd.
        iPureIntro. intros tv' _. exact (Hrd tv').
      + iDestruct "Hpub" as (V L M s q Bd) "(#HV & #Hfr & %HBL & #Hs & [%HLs %HqV] & _)".
        iDestruct "Hown" as (i m b) "(%HBi & #Hm & %Hmb & %Htid)". subst Ba.
        iDestruct (fr_at_flushed g 0%nat L M i m ltac:(lia) Htid
                     with "Hint Hfr Hm") as "#HevM".
        iDestruct (fr_at_after g 0%nat L M with "Hint Hfr") as %(_ & _ & Hafter).
        iDestruct (dpos_at_pos g s q with "Hint Hs") as %(q0 & Hq0 & ->).
        have HMV : (M <= V)%nat by (have := Hafter _ _ Hq0 HLs; lia).
        iDestruct (dpos_ev_mono _ _ _ V HMV with "HevM") as "#HevV".
        iDestruct (cv_key_read g a dq v t (S i) V Sv
                     with "Hint HevV HV Hchain Hpin") as %Hrd.
        iPureIntro. exact Hrd.
    - (* drained at the mint, under the drain bound *)
      iDestruct "Hcred" as "[[%H0 (%Bd' & #Hd' & #Hv0)] | Hpub]".
      + iDestruct (kpt_dbound_agree with "Hd Hd'") as %<-.
        iEval (rewrite -H0) in "Hv0".
        iDestruct (cv_key_read g a dq v t Ba Bd Sv
                     with "Hint Hev Hv0 Hchain Hpin") as %Hrd.
        iPureIntro. exact Hrd.
      + iDestruct "Hpub" as (V L M s q Bd') "(#HV & _ & _ & _ & _ & #Hd' & %HBdV)".
        iDestruct (kpt_dbound_agree with "Hd Hd'") as %<-.
        iDestruct (dpos_ev_mono _ _ _ V HBdV with "Hev") as "#HevV".
        iDestruct (cv_key_read g a dq v t Ba V Sv
                     with "Hint HevV HV Hchain Hpin") as %Hrd.
        iPureIntro. exact Hrd.
  Qed.

  Lemma cv_slot_read_ok `{CID : CpuId} (g : gstate) (a : Arch.pa)
      (dq : dfrac) (f : nat -> bv 8) (n : nat) (B : nat)
      (Sf : nat -> TsoMemPa.byteset) :
    tso_interp_at riscv_eraGS g -∗
    cv_boot_cred B -∗
    ([∗ list] j ∈ seq 0 n, ∃ (Ba t : nat), ⌜(Ba <= B)%nat⌝ ∗
       phys_ledger_pin (pa_add a j) dq (f j) t Ba (Sf j) ∗
       chain_ev chain_name Ba ∗ kpt_anchor (pa_add a j) Ba) -∗
    ⌜forall (tv' : nat), (g.(gtv) cpu_id <= tv')%nat ->
       forall j : nat, (j < n)%nat ->
         exists b, TsoMemPa.tso_read g.(gimg) g.(glog) g.(gdlog) (hart_agent cpu_id)
                     tv' (pa_add a j) = Some b /\ b ∈ Sf j⌝.
  Proof.
    iIntros "Hint #Hcred Hb".
    iAssert (⌜forall j : nat, (j < n)%nat ->
               forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
                 exists b, TsoMemPa.tso_read g.(gimg) g.(glog) g.(gdlog)
                             (hart_agent cpu_id) tv' (pa_add a j) = Some b
                           /\ b ∈ Sf j⌝)%I as %HH; last first.
    { iPureIntro. intros tv' Htv j Hj. exact (HH j Hj tv' Htv). }
    rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
    iDestruct (big_sepL_lookup _ (seq 0 n) j j with "Hb")
      as (Ba t) "(%HBa & Hbj & #Hchain & #Han)".
    { rewrite lookup_seq_lt; [reflexivity|lia]. }
    iApply (cv_anchor_read g (pa_add a j) dq (f j) t Ba B (Sf j) HBa
              with "Hint Hcred Hbj Hchain Han").
  Qed.


  (* THE SLOT AT THE DRAIN FLAT (relaxed-ww): what the A/D write-back's
     exclusive re-read sees.  The reader has no own store to the slot
     pending (the exclusive read's same-address guard), so its own anchors
     have drained; every anchor is then drained under the reader's view
     ([cv_anchor_read]'s three arms), the floor's chain puts every earlier
     write below it, and the pin's gates keep every later write in the
     family -- so the drain flat's byte is in the family.
     relaxed-ww STAGE E: the two-log pin theory; tracked in
     claude-notes/projects/relaxed-ww.md. *)
  Lemma cv_slot_dmem_ok `{CID : CpuId} (g : gstate) (a : Arch.pa)
      (dq : dfrac) (f : nat -> bv 8) (n : nat) (B : nat)
      (Sf : nat -> TsoMemPa.byteset) :
    ~ own_fp_pending (hart_agent cpu_id) g.(glog) g.(gdlog) a (N.of_nat n) ->
    tso_interp_at riscv_eraGS g -∗
    cv_boot_cred B -∗
    ([∗ list] j ∈ seq 0 n, ∃ (Ba t : nat), ⌜(Ba <= B)%nat⌝ ∗
       phys_ledger_pin (pa_add a j) dq (f j) t Ba (Sf j) ∗
       chain_ev chain_name Ba ∗ kpt_anchor (pa_add a j) Ba) -∗
    ⌜forall j : nat, (j < n)%nat ->
       exists b, TsoMemPa.dmem g.(gimg) g.(glog) g.(gdlog) !! pa_add a j = Some b
                 /\ b ∈ Sf j⌝.
  Proof.
  Admitted.

End CtxValues.
