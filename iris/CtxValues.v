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
From iris.base_logic.lib Require Import gen_heap ghost_map.
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

  Definition ctx_values (ξ : CtxId) (a : Arch.pa) (dq : dfrac)
      (Sv : gset (bv 8)) : iProp Σ :=
    (∃ (B t : nat) (v : bv 8),
       phys_ledger_pin a dq v t B Sv ∗
       (ctx_floor ξ B ∨ (ctx_wrote ξ B a ∗ cv_touch a B Sv)))%I.

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
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hlm & %HLM & Hlen & Hv & %Hmm)".
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
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hlm & %HLM & Hlen & Hv & %Hmm)".
    iDestruct (ghost_map_lookup with "Hauth Hts") as %HTM.
    iPureIntro.
    exact (TsoMemPa.ts_ok_pin _ _ _ _ _ _ _ (Htie _ _ HTM) eq_refl).
  Qed.

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
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hlm & %HLM & Hlen & Hv & %Hmm)".
    iDestruct (ghost_map_lookup with "Hauth Hts") as %HTM.
    iEval (rewrite /phys_pointsto) in "Hp".
    iDestruct "Hp" as "[Hp %Hram]".
    iDestruct (gen_heap_valid with "Hgh Hp") as %Hgm.
    iPureIntro.
    destruct (TsoMemPa.ts_ok_latest _ _ _ _ _ (Htie _ _ HTM))
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
    iDestruct "Hc" as (t) "(Hp & Hts & Harm)".
    iAssert (⌜TsoMemPa.latest g.(gimg) g.(glog) a t v⌝)%I as %Hlat.
    { iApply (cv_latest with "Hint Hgh Hp Hts"). }
    iDestruct "Harm" as "[#Hclean | #Hdirty]".
    - (* CLEAN: the floor is under ξ's bound *)
      iMod (ledger_pin_mint g a v t t Sv (le_n t) Hv with "Hgh Hint [Hp Hts]")
        as "(Hgh & Hint & Hpin)".
      { rewrite /phys_ledger_at. iFrame "Hp Hts". }
      iModIntro. iFrame "Hgh Hint Hrun".
      iExists t, t, v. iFrame "Hpin". iLeft. iExact "Hclean".
    - (* DIRTY: ξ's own write; record the receipt off the token *)
      destruct t as [|i].
      + (* stamp 0: the image floor -- use the clean arm, llb at 0 *)
        iMod (ledger_pin_mint g a v 0 0 Sv (le_n 0) Hv with "Hgh Hint [Hp Hts]")
          as "(Hgh & Hint & Hpin)".
        { rewrite /phys_ledger_at. iFrame "Hp Hts". }
        iModIntro. iFrame "Hgh Hint Hrun".
        iExists 0%nat, 0%nat, v. iFrame "Hpin". iLeft.
        rewrite /ctx_floor. iApply TsoGhost.llb_0.
      + (* stamp S i: [latest] says log !! i writes v to a *)
        destruct Hlat as [Hbyte _].
        rewrite /TsoMemPa.log_byte in Hbyte.
        destruct (g.(glog) !! i) as [m|] eqn:Hlog; last done.
        (* the token's dirty_ok at (S i, a): own-message or under-bound *)
        rewrite own_context_unseal /own_context_def.
        iDestruct "Hrun"
          as (Btok K W D) "(Hat & #HK & %HBK & #HW & %HDW & #Hoks)".
        iDestruct (TsoGhost.dset_lookup with "[Hat] [Hdirty]") as %HinD.
        { iDestruct "Hat" as "[_ $]". }
        { iExact "Hdirty". }
        iDestruct (big_sepS_elem_of _ _ _ HinD with "Hoks") as "#Hok".
        iDestruct "Hok" as "[%Hle | Hown]".
        * (* under the token's bound: clean arm via llb *)
          iDestruct "Hat" as "[Hb Hd]".
          iDestruct (TsoGhost.llb_get with "Hb") as "[Hb #Hllb]".
          iMod (ledger_pin_mint g a v (S i) (S i) Sv (le_n _) Hv
                  with "Hgh Hint [Hp Hts]") as "(Hgh & Hint & Hpin)".
          { rewrite /phys_ledger_at. iFrame "Hp Hts". }
          iModIntro. iFrame "Hgh Hint".
          iSplitL "Hb Hd".
          { iExists Btok, K, W, D. iFrame "Hb Hd HK HW Hoks".
            iSplit; by iPureIntro. }
          iExists (S i), (S i), v. iFrame "Hpin". iLeft.
          rewrite /ctx_floor.
          iApply (TsoGhost.llb_le with "Hllb"). cbn in Hle. lia.
        * (* the own-message arm: the receipt *)
          iDestruct "Hown" as (i' m') "(%Hii & #Hm & %Htid)".
          cbn in Hii. injection Hii as <-.
          iAssert (⌜g.(glog) !! i = Some m'⌝)%I as %Hlog'.
          { iApply (cv_msg_lookup with "Hint Hm"). }
          rewrite Hlog in Hlog'. injection Hlog' as <-.
          iMod (ledger_pin_mint g a v (S i) (S i) Sv (le_n _) Hv
                  with "Hgh Hint [Hp Hts]") as "(Hgh & Hint & Hpin)".
          { rewrite /phys_ledger_at. iFrame "Hp Hts". }
          iModIntro. iFrame "Hgh Hint".
          iSplitL "Hat".
          { iExists Btok, K, W, D. iFrame "Hat HK HW Hoks".
            iSplit; by iPureIntro. }
          iExists (S i), (S i), v. iFrame "Hpin". iRight.
          iSplit; [iExact "Hdirty" |].
          iRight. iExists i, m, v. iFrame "Hm".
          iSplit; [by iPureIntro |]. iSplit; by iPureIntro.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE RACY READ RULE: you get one of the values from the set.         *)
  (* ------------------------------------------------------------------ *)

  Lemma ctx_values_read `{CID : CpuId} (g : gstate) (ξ : CtxId)
      (a : Arch.pa) (dq : dfrac) (Sv : gset (bv 8)) :
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ctx_values ξ a dq Sv -∗
    ⌜forall tv, (g.(gtv) cpu_id <= tv)%nat ->
       exists b, TsoMemPa.tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv a
                 = Some b /\ b ∈ Sv⌝.
  Proof.
    iIntros "Hint Hrun Hc".
    iDestruct "Hc" as (B t v) "(Hpin & Harm)".
    iAssert (⌜TsoMemPa.pin_ok g.(gimg) g.(glog) a B Sv⌝)%I as %Hpin.
    { iApply (cv_pin_ok with "Hint Hpin"). }
    iDestruct "Harm" as "[#Hclean | [#Hdirty #Htouch]]".
    - (* CLEAN: ξ's bound passed B, so this hart's view has too *)
      rewrite own_context_unseal /own_context_def.
      iDestruct "Hrun"
        as (Btok K W D) "(Hat & #HK & %HBK & #HW & %HDW & #Hoks)".
      iDestruct "Hat" as "[Hb Hd]".
      rewrite /ctx_floor.
      iDestruct (TsoGhost.llb_valid with "Hb Hclean") as %HBtok.
      iDestruct (TsoGhost.view_lb_le view_name loglen_name (hart_agent cpu_id) K B ltac:(lia) with "HK") as "#HB".
      iDestruct (ledger_read_pin_ok g a dq v t B Sv with "Hint HB [Hpin]")
        as %Hrd.
      { iExact "Hpin". }
      iPureIntro. intros tv Htv. exact (Hrd (hart_agent cpu_id) tv Htv).
    - (* DIRTY: the author arm *)
      iDestruct "Htouch" as "[%HB0 | Hseed]".
      + (* B = 0: pin_ok covers every view outright *)
        subst B. iPureIntro. intros tv Htv.
        exact (Hpin (hart_agent cpu_id) tv (Nat.le_0_l tv)).
      + iDestruct "Hseed" as (i m b) "(%HBi & #Hm & %Hmb & %HbS)".
        iAssert (⌜g.(glog) !! i = Some m⌝)%I as %Hlog.
        { iApply (cv_msg_lookup with "Hint Hm"). }
        (* the token certifies the message at B is this hart's own,
           or that B is under the bound (then the clean route applies) *)
        rewrite own_context_unseal /own_context_def.
        iDestruct "Hrun"
          as (Btok K W D) "(Hat & #HK & %HBK & #HW & %HDW & #Hoks)".
        iDestruct (TsoGhost.dset_lookup with "[Hat] [Hdirty]") as %HinD.
        { iDestruct "Hat" as "[_ $]". }
        { iExact "Hdirty". }
        iDestruct (big_sepS_elem_of _ _ _ HinD with "Hoks") as "#Hok".
        iDestruct "Hok" as "[%Hle | Hown]".
        * (* under the bound: view receipt route *)
          iDestruct "Hat" as "[Hb Hd]".
          cbn in Hle.
          iDestruct (TsoGhost.view_lb_le view_name loglen_name (hart_agent cpu_id) K B ltac:(lia) with "HK")
            as "#HB".
          iDestruct (ledger_read_pin_ok g a dq v t B Sv with "Hint HB [Hpin]")
            as %Hrd.
          { iExact "Hpin". }
          iPureIntro. intros tv Htv. exact (Hrd (hart_agent cpu_id) tv Htv).
        * (* own: [pin_ok_author] *)
          iDestruct "Hown" as (i' m') "(%Hii & #Hm' & %Htid)".
          cbn in Hii. rewrite HBi in Hii. injection Hii as <-.
          iAssert (⌜g.(glog) !! i = Some m'⌝)%I as %Hlog'.
          { iApply (cv_msg_lookup with "Hint Hm'"). }
          rewrite Hlog in Hlog'. injection Hlog' as <-.
          iPureIntro. intros tv Htv.
          apply (TsoMemPa.pin_ok_author g.(gimg) g.(glog) a B B b Sv
                   (hart_agent cpu_id) Hpin (Nat.le_refl B)).
          -- (* always visible: the own arm *)
             intros tv'. rewrite HBi /TsoMemPa.visibleb Hlog /= Htid.
             rewrite (bool_decide_eq_true_2 _ eq_refl). by rewrite orb_true_r.
          -- rewrite HBi /TsoMemPa.log_byte Hlog. exact Hmb.
          -- rewrite HBi. apply lookup_lt_Some in Hlog. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE WALKER-FACING CREDENTIAL (A6.135 §1).  [cv_own h a p]: position *)
  (* p is h's OWN message touching [a].  Persistent, TOKEN-FREE at the   *)
  (* read: the walker never holds [own_context].  [cv_cred a B] is the   *)
  (* per-hart disjunction the page-table walk consumes: either the       *)
  (* hart's view has passed the arm's floor (a secondary, via the        *)
  (* started receipt), or the floor is dominated by the hart's own       *)
  (* write (the boot hart's anchors, minted at establishment).           *)
  (* ------------------------------------------------------------------ *)

  Definition cv_own (h : agent) (a : Arch.pa) (p : nat) : iProp Σ :=
    (∃ (i : nat) (m : TsoMemPa.pwmsg) (b : bv 8),
       ⌜p = S i⌝ ∗ ledger_msg_at i m ∗
       ⌜TsoMemPa.msg_byte m a = Some b⌝ ∗ ⌜TsoMemPa.pm_tid m = h⌝)%I.

  Global Instance cv_own_persistent h a p : Persistent (cv_own h a p).
  Proof. rewrite /cv_own. apply _. Qed.
  Global Instance cv_own_timeless h a p : Timeless (cv_own h a p).
  Proof. rewrite /cv_own. apply _. Qed.

  Definition cv_cred `{CID : CpuId} (a : Arch.pa) (B : nat) : iProp Σ :=
    (TsoGhost.view_lb view_name loglen_name (hart_agent cpu_id) B ∨
     ∃ (p : nat), ⌜(B <= p)%nat⌝ ∗ cv_own (hart_agent cpu_id) a p)%I.

  Global Instance cv_cred_persistent `{CID : CpuId} a B :
    Persistent (cv_cred a B).
  Proof. rewrite /cv_cred. apply _. Qed.

  Lemma cv_cred_le `{CID : CpuId} (a : Arch.pa) (B B' : nat) :
    (B <= B')%nat -> cv_cred a B' -∗ cv_cred a B.
  Proof.
    iIntros (Hle) "[#Hv | (%p & %Hp & #Ho)]".
    - iLeft. iApply (TsoGhost.view_lb_le with "Hv"). lia.
    - iRight. iExists p. iSplit; [iPureIntro; lia | iExact "Ho"].
  Qed.

  (* the author's read: settle at or above the own anchor, family via
     [pin_ok] at the settle's own view.  No view receipt, no token. *)
  Lemma cv_own_read (g : gstate) (a : Arch.pa) (dq : dfrac)
      (v : bv 8) (t B p : nat) (Sv : gset (bv 8)) (h : agent) :
    (B <= p)%nat ->
    tso_interp_at riscv_eraGS g -∗
    phys_ledger_pin a dq v t B Sv -∗
    cv_own h a p -∗
    ⌜forall tv, exists b,
       TsoMemPa.tso_read g.(gimg) g.(glog) h tv a = Some b /\ b ∈ Sv⌝.
  Proof.
    iIntros (HBp) "Hint Hpin #Hown".
    iAssert (⌜TsoMemPa.pin_ok g.(gimg) g.(glog) a B Sv⌝)%I as %Hpin.
    { iApply (cv_pin_ok with "Hint Hpin"). }
    iDestruct "Hown" as (i m b0) "(%Hp & #Hm & %Hmb & %Htid)".
    iAssert (⌜g.(glog) !! i = Some m⌝)%I as %Hlog.
    { iApply (cv_msg_lookup with "Hint Hm"). }
    iPureIntro. intros tv.
    apply (TsoMemPa.pin_ok_author g.(gimg) g.(glog) a B p b0 Sv h Hpin HBp).
    - intros tv'. rewrite Hp /TsoMemPa.visibleb Hlog /= Htid.
      rewrite (bool_decide_eq_true_2 _ eq_refl). by rewrite orb_true_r.
    - rewrite Hp /TsoMemPa.log_byte Hlog. exact Hmb.
    - rewrite Hp. apply lookup_lt_Some in Hlog. lia.
  Qed.

  (* the one law the page-table walk consumes *)
  Lemma cv_cred_read `{CID : CpuId} (g : gstate) (a : Arch.pa)
      (dq : dfrac) (v : bv 8) (t B : nat) (Sv : gset (bv 8)) :
    tso_interp_at riscv_eraGS g -∗
    phys_ledger_pin a dq v t B Sv -∗
    cv_cred a B -∗
    ⌜forall tv, (g.(gtv) cpu_id <= tv)%nat ->
       exists b, TsoMemPa.tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv a
                 = Some b /\ b ∈ Sv⌝.
  Proof.
    iIntros "Hint Hpin [#Hv | (%p & %Hp & #Ho)]".
    - iDestruct (ledger_read_pin_ok g a dq v t B Sv with "Hint Hv Hpin")
        as %Hrd.
      iPureIntro. intros tv Htv. exact (Hrd (hart_agent cpu_id) tv Htv).
    - iDestruct (cv_own_read g a dq v t B p Sv (hart_agent cpu_id) Hp
                   with "Hint Hpin Ho") as %Hrd.
      iPureIntro. intros tv _. exact (Hrd tv).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE KERNEL-SLOT READ (A6.135): a run of per-byte pins at ∃-floors    *)
  (* under a global [B], each byte carrying the boot hart's own-write     *)
  (* anchor (or floor 0).  The reader's credential: a view receipt at     *)
  (* [B] (a secondary, via the started barrier) OR being the boot hart    *)
  (* (the anchors are its own messages -- token-free, view-free).         *)
  (* ------------------------------------------------------------------ *)
  (* the WALK's per-hart credential: a view receipt at the tree's global
     bound (a secondary, off the started barrier) or being the boot hart
     (whose anchors ride in the slots). *)
  Definition cv_boot_cred `{CID : CpuId} (B : nat) : iProp Σ :=
    (TsoGhost.view_lb view_name loglen_name (hart_agent cpu_id) B ∨
     (⌜hart_agent cpu_id = 0%nat⌝ ∗ TsoGhost.llb loglen_name B))%I.

  Global Instance cv_boot_cred_persistent `{CID : CpuId} B :
    Persistent (cv_boot_cred B).
  Proof. rewrite /cv_boot_cred. apply _. Qed.
  Global Instance cv_boot_cred_timeless `{CID : CpuId} B :
    Timeless (cv_boot_cred B).
  Proof. rewrite /cv_boot_cred. apply _. Qed.

  Lemma cv_boot_cred_view `{CID : CpuId} (B : nat) :
    TsoGhost.view_lb view_name loglen_name (hart_agent cpu_id) B -∗
    cv_boot_cred B.
  Proof. iIntros "H". iLeft. iExact "H". Qed.

  Lemma cv_boot_cred_boot `{CID : CpuId} (B : nat) :
    hart_agent cpu_id = 0%nat ->
    TsoGhost.llb loglen_name B -∗ cv_boot_cred B.
  Proof.
    intros H0. iIntros "Hl". iRight.
    iSplitR; [by iPureIntro | iExact "Hl"].
  Qed.

  Lemma cv_boot_cred_llb `{CID : CpuId} (B : nat) :
    cv_boot_cred B -∗ TsoGhost.llb loglen_name B.
  Proof.
    iIntros "[Hv | [_ Hl]]";
      [iApply (TsoGhost.view_lb_llb with "Hv") | iExact "Hl"].
  Qed.

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

  Lemma cv_slot_read_ok `{CID : CpuId} (g : gstate) (a : Arch.pa)
      (dq : dfrac) (f : nat -> bv 8) (n : nat) (B : nat)
      (Sf : nat -> TsoMemPa.byteset) :
    tso_interp_at riscv_eraGS g -∗
    cv_boot_cred B -∗
    ([∗ list] j ∈ seq 0 n, ∃ (Ba t : nat), ⌜(Ba <= B)%nat⌝ ∗
       phys_ledger_pin (pa_add a j) dq (f j) t Ba (Sf j) ∗
       (⌜Ba = 0%nat⌝ ∨ cv_own 0%nat (pa_add a j) Ba ∨
        TsoGhost.view_lb view_name loglen_name 0%nat Ba)) -∗
    ⌜forall (tv' : nat), (g.(gtv) cpu_id <= tv')%nat ->
       forall j : nat, (j < n)%nat ->
         exists b, TsoMemPa.tso_read g.(gimg) g.(glog) (hart_agent cpu_id)
                     tv' (pa_add a j) = Some b /\ b ∈ Sf j⌝.
  Proof.
    iIntros "Hint #Hcred Hb". iEval (rewrite /cv_boot_cred) in "Hcred".
    iAssert (⌜forall j : nat, (j < n)%nat ->
               forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
                 exists b, TsoMemPa.tso_read g.(gimg) g.(glog)
                             (hart_agent cpu_id) tv' (pa_add a j) = Some b
                           /\ b ∈ Sf j⌝)%I as %HH; last first.
    { iPureIntro. intros tv' Htv j Hj. exact (HH j Hj tv' Htv). }
    rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
    iDestruct (big_sepL_lookup _ (seq 0 n) j j with "Hb")
      as (Ba t) "(%HBa & Hbj & #Han)".
    { rewrite lookup_seq_lt; [reflexivity|lia]. }
    iDestruct "Hcred" as "[Hv | [%H0 _]]".
    - (* a view receipt at the global bound covers every arm uniformly *)
      iDestruct (TsoGhost.view_lb_le _ _ _ B Ba HBa with "Hv") as "#HvBa".
      iDestruct (ledger_read_pin_ok g (pa_add a j) dq (f j) t Ba (Sf j)
                   with "Hint HvBa Hbj") as %Hrd.
      iPureIntro. intros tv' Htv'.
      exact (Hrd (hart_agent cpu_id) tv' Htv').
    - (* the boot hart: 3-way on the slot's own credential *)
      iDestruct "Han" as "[%HBa0 | [#Hown | #Hv0]]".
      + subst Ba.
        iDestruct (ledger_read_pin_ok g (pa_add a j) dq (f j) t 0%nat (Sf j)
                     with "Hint [] Hbj") as %Hrd.
        { iApply TsoGhost.view_lb_0. }
        iPureIntro. intros tv' Htv'.
        exact (Hrd (hart_agent cpu_id) tv' Htv').
      + (* its own anchor, no view receipt *)
        iEval (rewrite -H0) in "Hown".
        iDestruct (cv_own_read g (pa_add a j) dq (f j) t Ba Ba (Sf j)
                     (hart_agent cpu_id) (Nat.le_refl Ba)
                     with "Hint Hbj Hown") as %Hrd.
        iPureIntro. intros tv' _. exact (Hrd tv').
      + (* the drained-publisher receipt, recorded in the slot *)
        iEval (rewrite -H0) in "Hv0".
        iDestruct (ledger_read_pin_ok g (pa_add a j) dq (f j) t Ba (Sf j)
                     with "Hint Hv0 Hbj") as %Hrd.
        iPureIntro. intros tv' Htv'.
        exact (Hrd (hart_agent cpu_id) tv' Htv').
  Qed.

End CtxValues.
