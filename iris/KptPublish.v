(* KptPublish.v -- THE CANON PIN'S PUBLICATION GATE, at the TREE
   (tso-machine-flip.md A6.70's ruling; tso-pin-memo.md §5.6(b); A6.135;
   relaxed-ww.md, the two-log slot credential).

   [KptShare.kpt_inv_alloc] wants [kptree_own B 2 (DfracOwn 1) t], i.e.
   [PtTree.ptree_own_at (KTier B)], whose slots are per-byte
   [TsoCtx.phys_ledger_pin]s at their own floors with a
   [CtxValues.kpt_anchor] each.  A table under construction is
   [ptree_own_at (UTier xi)], whose slots are [ctx_phys_word_pointsto] --
   elements pinned to [None] BY DEFINITION.  This file is the move from one
   to the other: [TsoCtx.ledger_pin_mint] per byte, folded over the 512
   slots of a node and then over the node's children.

   THE BOOT ROUTE IS THE ONLY ROUTE (A6.135; relaxed-ww).  The site is
   kvminithart's `csrw satp` node ([SpecKvminithart]), where hart 0 has
   NOT drained -- so every byte is published at ITS OWN WRITE STAMP, with
   no drain and no log top, and the byte's anchor is read off the running
   token's justification ([TsoCtx.key_at]): a stamp already drained under
   the token's bound becomes the DRAINED arm at the tree's drain bound
   ([CtxValues.kpt_dbound], shot here at the token's view receipt [K]);
   the hart's OWN message becomes the own arm ([CtxValues.cv_own 0]).
   Hart 0 reads through its view receipt at [K] and store forwarding; a
   secondary reads through hart 0's release-fence record and the started
   flag ([CtxValues.kpt_pub], assembled in [ProofMainSecondary]).

   THE TOKEN IS THREADED UNSEALED.  The mint needs the token's bound [Btok]
   and view receipt [K] to be the SAME across all 4096 bytes (the drain
   bound is shot once, at [K]), and a sealed [own_context] re-opened per
   byte would name fresh existentials each time -- so the fold threads
   [TsoCtx.ctx_tok xi Btok] with the persistent halves alongside, and
   [kptree_publish_boot] seals it back at the end.  The drained
   publication route (§5 of the one-log design, [kptree_publish]) had no
   site and is gone. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map mono_nat.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto.
Require Import TsoMemPa TsoGhost TsoCtx.
Require Import PtreeType CommonWalk PtAdBits PtTree.
Require Import CtxValues.
Require Import CtxPinMint.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* §0 A WORD IS IN ITS OWN FAMILY -- the mint's per-byte obligation, and    *)
(* the reason the publication needs no premise about the table's CONTENT.  *)
(* At an interior slot the family is eight singletons; at a leaf, byte 0's *)
(* is the four-element A/D class, which contains the leaf's own byte by    *)
(* [PtAdBits.pte_set_ad_refl] ("every word is an A/D variant of itself").  *)
(* ---------------------------------------------------------------------- *)
Lemma pte_slot_set_self (w : mword 64) (j : nat) :
  nth_byte w j ∈ pte_slot_set w j.
Proof.
  rewrite /pte_slot_set. destruct j as [|j'].
  - cbn [Nat.eqb]. destruct (pte_nonleafb w).
    + apply TsoMemPa.byteset_sing_in.
    + destruct (pte_set_ad_refl w) as (a & d & Hw).
      rewrite {1}Hw. apply pte_ad_byte0_set_ad.
  - cbn [Nat.eqb]. apply TsoMemPa.byteset_sing_in.
Qed.

Section KptPublish.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------ *)
  (* §1 THE GENERIC CHILD FOLD, over a threaded resource [R].             *)
  (* ------------------------------------------------------------------ *)
  Lemma pt_kids_publish (g : gstate) (R : iProp Σ) (P Q : ptree -> iProp Σ)
      (l : list Z) (K : Z -> option ptree) :
    (forall c : ptree,
       ⊢ gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
         tso_interp_at riscv_eraGS g -∗ R -∗ P c ==∗
         gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
         tso_interp_at riscv_eraGS g ∗ R ∗ Q c) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ R -∗
    ([∗ list] i ∈ l, match K i with Some c => P c | None => emp end) ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ R ∗
    ([∗ list] i ∈ l, match K i with Some c => Q c | None => emp end).
  Proof.
    intros Hstep. induction l as [|i l IH].
    - iIntros "Hgh Hint Hrun Hl". iModIntro. iFrame "Hgh Hint Hrun".
      iExact "Hl".
    - rewrite !big_sepL_cons.
      iIntros "Hgh Hint Hrun [Hc Hl]".
      destruct (K i) as [c|].
      + iMod (Hstep c with "Hgh Hint Hrun Hc") as "(Hgh & Hint & Hrun & Hc)".
        iMod (IH with "Hgh Hint Hrun Hl") as "(Hgh & Hint & Hrun & Hl)".
        iModIntro. iFrame "Hgh Hint Hrun Hc Hl".
      + iMod (IH with "Hgh Hint Hrun Hl") as "(Hgh & Hint & Hrun & Hl)".
        iModIntro. iFrame "Hgh Hint Hrun Hl".
  Qed.

  (* the same fold with the per-child step as a PERSISTENT WAND, for a
     caller whose step closes over resources of its own (the boot
     telescope's hart identity, bound and receipt). *)
  Lemma pt_kids_publish_w (g : gstate) (R : iProp Σ) (P Q : ptree -> iProp Σ)
      (l : list Z) (K : Z -> option ptree) :
    □ (∀ c : ptree,
         gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
         tso_interp_at riscv_eraGS g -∗ R -∗ P c ==∗
         gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
         tso_interp_at riscv_eraGS g ∗ R ∗ Q c) -∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ R -∗
    ([∗ list] i ∈ l, match K i with Some c => P c | None => emp end) ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ R ∗
    ([∗ list] i ∈ l, match K i with Some c => Q c | None => emp end).
  Proof.
    iIntros "#Hstep". iInduction l as [|i l] "IHl".
    - iIntros "Hgh Hint Hrun Hl". iModIntro. iFrame "Hgh Hint Hrun".
      iExact "Hl".
    - rewrite !big_sepL_cons.
      iIntros "Hgh Hint Hrun [Hc Hl]".
      destruct (K i) as [c|].
      + iMod ("Hstep" $! c with "Hgh Hint Hrun Hc")
          as "(Hgh & Hint & Hrun & Hc)".
        iMod ("IHl" with "Hgh Hint Hrun Hl") as "(Hgh & Hint & Hrun & Hl)".
        iModIntro. iFrame "Hgh Hint Hrun Hc Hl".
      + iMod ("IHl" with "Hgh Hint Hrun Hl") as "(Hgh & Hint & Hrun & Hl)".
        iModIntro. iFrame "Hgh Hint Hrun Hl".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §2 THE BOOT PUBLICATION, byte by byte.                              *)
  (*                                                                     *)
  (* The threaded resource is the running token's authority               *)
  (* [ctx_tok xi Btok]; beside it, persistent: the token's dirty-set   *)
  (* justifications at [Btok], the drain bound shot at [K] ([Btok <= K],  *)
  (* the token's own view receipt).  A byte comes out pinned at its own   *)
  (* stamp [t] (so the pin's floor is [t], and [t <= length glog] is the  *)
  (* tree's issue bound), with the chain evidence [ctx_phys_pointsto]     *)
  (* already carries and its anchor read off [key_at]'s justification.    *)
  (* ------------------------------------------------------------------ *)
  (* the running token, OPENED: its authority at [Btok] with the dirty
     set's justifications beside it.  Named so the fold never states the
     set's type (its decidable-equality instance is [TsoCtx]'s). *)
  Definition ctx_tok (xi : CtxId) (Btok : nat) : iProp Σ :=
    (∃ D, ctx_at xi 1 Btok D ∗
          [∗ set] k ∈ D, dirty_ok logm_name dpos_name (hart_agent cpu_id) Btok k)%I.

  Lemma ctx_phys_byte_publish_boot (g : gstate) (xi : CtxId)
      (Btok K : nat)
      (a : Arch.pa) (v : bv 8) (Sv : TsoMemPa.byteset) :
    hart_agent cpu_id = 0%nat ->
    v ∈ Sv ->
    (Btok <= K)%nat ->
    kpt_dbound K -∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ ctx_tok xi Btok -∗
    ctx_phys_pointsto xi a (DfracOwn 1) v ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ ctx_tok xi Btok ∗
    (∃ Ba t : nat, ⌜(Ba <= length g.(glog))%nat⌝ ∗
       phys_ledger_pin a (DfracOwn 1) v t Ba Sv ∗
       chain_ev chain_name Ba ∗ kpt_anchor a Ba).
  Proof.
    intros H0 Hv HBK. iIntros "#Hdb Hgh Hint (%D & [Hb Hd] & #Hoks) Hbyte".
    rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def.
    iDestruct "Hbyte" as (t) "(Hpt & Hts & #Hkey & #Hchain)".
    iDestruct (tso_interp_ts_le g a (DfracOwn 1)
                 ((t, TsoMemPa.ts_pay_none) : TsoMemPa.ts_elem)
                 with "Hint Hts") as %Htlen.
    cbn in Htlen.
    iDestruct (CtxValues.cv_latest g a (DfracOwn 1) v t
                 with "Hint Hgh Hpt Hts") as %Hlat.
    iMod (ledger_pin_mint g a v t Sv Hv
            with "Hgh Hint [Hpt Hts]") as "(Hgh & Hint & Hpin)".
    { rewrite /phys_ledger_at. iFrame "Hpt Hts". }
    (* the anchor, off the key's justification *)
    iAssert (kpt_anchor a t) as "#Han".
    { rewrite /kpt_anchor.
      iDestruct "Hkey" as "[(%p & #Hev & #Hlb) | #Hdirty]".
      - (* CLEAN under the token's bound: drained under [K] *)
        iDestruct (TsoGhost.llb_valid with "Hb Hlb") as %HpB.
        iRight. iRight. iExists K. iFrame "Hdb".
        iApply (dpos_ev_mono with "Hev"). lia.
      - (* DIRTY: the token's registry decides *)
        iDestruct (TsoGhost.dset_lookup with "Hd Hdirty") as %HinD.
        iDestruct (big_sepS_elem_of _ _ _ HinD with "Hoks") as "#Hok".
        iDestruct "Hok" as "[#Hev | (%i & %m & %Hti & #Hm & %Htid)]".
        + iRight. iRight. iExists K. iFrame "Hdb".
          iApply (dpos_ev_mono with "Hev"). cbn. lia.
        + (* the hart's OWN MESSAGE: the byte it wrote is [v] *)
          cbn in Hti. subst t.
          iAssert (⌜g.(glog) !! i = Some m⌝)%I as %Hlog.
          { iApply (CtxValues.cv_msg_lookup with "Hint Hm"). }
          destruct Hlat as [Hbyte _].
          rewrite /TsoMemPa.log_byte Hlog in Hbyte.
          iRight. iLeft. iExists i, m, v.
          iSplitR; [by iPureIntro |]. iSplitR; [iExact "Hm" |].
          iSplit; iPureIntro; [exact Hbyte | rewrite Htid; exact H0]. }
    iModIntro. iFrame "Hgh Hint".
    iSplitL "Hb Hd". { iExists D. iFrame "Hb Hd Hoks". }
    iExists t, t. iFrame "Hpin Hchain Han". by iPureIntro.
  Qed.

  Lemma ctx_phys_bytes_publish_boot (g : gstate) (xi : CtxId)
      (Btok K : nat)
      (a : Arch.pa) (n : nat) (f : nat -> bv 8)
      (Sf : nat -> TsoMemPa.byteset) :
    hart_agent cpu_id = 0%nat ->
    (forall j : nat, (j < n)%nat -> f j ∈ Sf j) ->
    (Btok <= K)%nat ->
    kpt_dbound K -∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ ctx_tok xi Btok -∗
    ([∗ list] j ∈ seq 0 n, ctx_phys_pointsto xi (pa_add a j) (DfracOwn 1) (f j))
    ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ ctx_tok xi Btok ∗
    ([∗ list] j ∈ seq 0 n, ∃ Ba t : nat, ⌜(Ba <= length g.(glog))%nat⌝ ∗
       phys_ledger_pin (pa_add a j) (DfracOwn 1) (f j) t Ba (Sf j) ∗
       chain_ev chain_name Ba ∗ kpt_anchor (pa_add a j) Ba).
  Proof.
    intros H0 Hf HBK. iIntros "#Hdb".
    iInduction n as [|n] "IH" forall (Hf).
    - iIntros "Hgh Hint Hrun Hl". iModIntro. iFrame "Hgh Hint Hrun".
      iExact "Hl".
    - rewrite seq_S !big_sepL_app /=.
      iIntros "Hgh Hint Hrun [Hb [Hlast _]]".
      iMod ("IH" with "[] Hgh Hint Hrun Hb") as "(Hgh & Hint & Hrun & Hb)".
      { iPureIntro. intros j Hj. apply Hf. lia. }
      iMod (ctx_phys_byte_publish_boot g xi Btok K (pa_add a n) (f n) (Sf n)
              H0 (Hf n ltac:(lia)) HBK with "Hdb Hgh Hint Hrun Hlast")
        as "(Hgh & Hint & Hrun & Hlast)".
      iModIntro. iFrame "Hgh Hint Hrun Hb Hlast".
  Qed.

  Lemma kpt_slot_publish_boot (g : gstate) (xi : CtxId)
      (Btok K : nat)
      (a : Arch.pa) (w : bv 64) :
    hart_agent cpu_id = 0%nat ->
    (Btok <= K)%nat ->
    kpt_dbound K -∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ ctx_tok xi Btok -∗
    ctx_phys_word_pointsto xi a (DfracOwn 1) w ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ ctx_tok xi Btok ∗
    kpt_slot_pin a (DfracOwn 1) w (length g.(glog)).
  Proof.
    intros H0 HBK. iIntros "#Hdb Hgh Hint Hrun Hw".
    iDestruct (ctx_phys_word_pointsto_aligned_p with "Hw") as %Hal.
    iDestruct (ctx_phys_word_pointsto_bytes with "Hw") as "Hb".
    iMod (ctx_phys_bytes_publish_boot g xi Btok K a 8 (nth_byte w)
            (pte_slot_set w) H0
            (fun j (_ : (j < 8)%nat) => pte_slot_set_self w j) HBK
            with "Hdb Hgh Hint Hrun Hb") as "(Hgh & Hint & Hrun & Hb)".
    iModIntro. iFrame "Hgh Hint Hrun".
    rewrite /kpt_slot_pin. iSplitR; [by iPureIntro |]. iExact "Hb".
  Qed.

  Lemma pt_slots_publish_boot (g : gstate) (xi : CtxId)
      (Btok K : nat)
      (l : list Z) (F : Z -> Arch.pa) (W : Z -> mword 64) :
    hart_agent cpu_id = 0%nat ->
    (Btok <= K)%nat ->
    kpt_dbound K -∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ ctx_tok xi Btok -∗
    ([∗ list] i ∈ l, pt_slot_own (UTier xi) (F i) (DfracOwn 1) (W i)) ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ ctx_tok xi Btok ∗
    ([∗ list] i ∈ l, pt_slot_own (KTier (length g.(glog))) (F i) (DfracOwn 1) (W i)).
  Proof.
    intros H0 HBK. iIntros "#Hdb". iInduction l as [|i l] "IH".
    - iIntros "Hgh Hint Hrun Hl". iModIntro. iFrame "Hgh Hint Hrun".
      iExact "Hl".
    - rewrite !big_sepL_cons.
      iIntros "Hgh Hint Hrun [Hs Hl]".
      rewrite (pt_slot_own_ctx (UTier xi) xi (F i) (DfracOwn 1) (W i) eq_refl).
      iMod (kpt_slot_publish_boot g xi Btok K (F i) (W i) H0 HBK
              with "Hdb Hgh Hint Hrun Hs") as "(Hgh & Hint & Hrun & Hs)".
      iMod ("IH" with "Hgh Hint Hrun Hl") as "(Hgh & Hint & Hrun & Hl)".
      iModIntro. iFrame "Hgh Hint Hrun Hl".
      rewrite (pt_slot_own_ker (KTier (length g.(glog))) (length g.(glog))
                 (F i) (DfracOwn 1) (W i) eq_refl).
      iExact "Hs".
  Qed.

  Lemma pt_page_publish_boot (g : gstate) (xi : CtxId)
      (Btok K : nat) (t : ptree) :
    hart_agent cpu_id = 0%nat ->
    (Btok <= K)%nat ->
    kpt_dbound K -∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ ctx_tok xi Btok -∗
    pt_page_own_at (UTier xi) (DfracOwn 1) t ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ ctx_tok xi Btok ∗
    pt_page_own_at (KTier (length g.(glog))) (DfracOwn 1) t.
  Proof.
    intros H0 HBK. iIntros "#Hdb Hgh Hint Hrun [#Hcl Hs]".
    iMod (pt_slots_publish_boot g xi Btok K (seqZ 0 512)
            (fun i => u_pte_addr (pt_base t) (mword_of_int i))
            (fun i => pt_ents t (mword_of_int i)) H0 HBK
            with "Hdb Hgh Hint Hrun Hs")
      as "(Hgh & Hint & Hrun & Hs)".
    iModIntro. iFrame "Hgh Hint Hrun". rewrite /pt_page_own_at.
    iFrame "Hcl Hs".
  Qed.

  Lemma ptree_own_publish_boot (g : gstate) (xi : CtxId)
      (Btok K : nat) (lvl : nat) (t : ptree) :
    hart_agent cpu_id = 0%nat ->
    (Btok <= K)%nat ->
    kpt_dbound K -∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ ctx_tok xi Btok -∗
    ptree_own_at (UTier xi) lvl (DfracOwn 1) t ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ ctx_tok xi Btok ∗
    ptree_own_at (KTier (length g.(glog))) lvl (DfracOwn 1) t.
  Proof.
    intros H0 HBK. iIntros "#Hdb".
    iInduction lvl as [|lvl] "IH" forall (t).
    - iIntros "Hgh Hint Hrun [Hp _]".
      iMod (pt_page_publish_boot g xi Btok K t H0 HBK
              with "Hdb Hgh Hint Hrun Hp") as "(Hgh & Hint & Hrun & Hp)".
      iModIntro. iFrame "Hgh Hint Hrun Hp".
    - iIntros "Hgh Hint Hrun [Hp Hk]".
      iMod (pt_page_publish_boot g xi Btok K t H0 HBK
              with "Hdb Hgh Hint Hrun Hp") as "(Hgh & Hint & Hrun & Hp)".
      iMod (pt_kids_publish_w g (ctx_tok xi Btok)
              (fun c => ptree_own_at (UTier xi) lvl (DfracOwn 1) c)
              (fun c => ptree_own_at (KTier (length g.(glog))) lvl (DfracOwn 1) c)
              (seqZ 0 512) (fun i => pt_kids t (mword_of_int i))
              with "[] Hgh Hint Hrun Hk") as "(Hgh & Hint & Hrun & Hk)".
      { iIntros "!>" (c). iApply "IH". }
      iModIntro. iFrame "Hgh Hint Hrun Hp Hk".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §3 THE TREE: the token is opened once, the drain bound shot at its    *)
  (* view receipt, and the token sealed back.  Out come the tree at the   *)
  (* issue bound, the bound's log-position receipt ([KptShare.kpt_inv_alloc] *)
  (* wants it) and hart 0's read credential.                              *)
  (* ------------------------------------------------------------------ *)
  Lemma kptree_publish_boot (g : gstate) (xi : CtxId) (lvl : nat) (t : ptree) :
    hart_agent cpu_id = 0%nat ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗ kptd_unset -∗
    ptree_own_at (UTier xi) lvl (DfracOwn 1) t ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    ptree_own_at (KTier (length g.(glog))) lvl (DfracOwn 1) t ∗
    llb loglen_name (length g.(glog)) ∗
    cv_boot_cred (length g.(glog)).
  Proof.
    intros H0. iIntros "Hgh Hint Hrun Hunset Ht".
    iDestruct (tso_interp_loglen_llb g with "Hint") as "[Hint #Hllb]".
    rewrite own_context_unseal /own_context_def.
    iDestruct "Hrun" as (Btok K D) "(Hat & #HK & %HBK & #Hoks)".
    iMod (kptd_shoot K with "Hunset") as "#Hdb".
    iMod (ptree_own_publish_boot g xi Btok K lvl t H0 HBK
            with "Hdb Hgh Hint [Hat] Ht") as "(Hgh & Hint & Htok & Ht)".
    { iExists D. iFrame "Hat Hoks". }
    iDestruct "Htok" as (D') "[Hat #Hoks']".
    iModIntro. iFrame "Hgh Hint Ht Hllb".
    iSplitL "Hat".
    { iExists Btok, K, D'. iFrame "Hat HK Hoks'". by iPureIntro. }
    iEval (rewrite H0) in "HK".
    iApply (cv_boot_cred_boot _ K H0 with "Hdb HK").
  Qed.

End KptPublish.
