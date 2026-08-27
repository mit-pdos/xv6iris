(* CtxPinMint.v -- THE CANON PIN'S PRODUCER SIDE, at the BYTE and the WORD
   (tso-machine-flip.md A6.70; tso-pin-memo.md §5.2/§5.6(b)).

   A6.53 built the pin's CONSUMER side end to end -- [TsoCtx.ledger_pin_mint]
   (the element update, off an ALREADY-UNREGISTERED [phys_ledger_at]),
   [ledger_read_pin_ok] (the walk's discharge), [ledger_store_win_pin_ok]
   (the A/D write-back's gate) -- and A6.70 measured what was missing: there
   is no law anywhere that takes a byte OUT of a context and INTO the pinned
   tier.  [PtTree.pt_slot_own (KTier B)] is [phys_ledger_word_pin]; a table
   under construction is [ctx_phys_word_pointsto] at the builder's ξ; and
   [ctx_pointsto] / [ctx_phys_pointsto] / [phys_ledger] all pin the ts
   element's option arm to [None] BY DEFINITION (which is what keeps every
   ordinary store gate sound with no new premise).  So the crossing is a
   GHOST UPDATE against the interp and nothing weaker can be it.

   WHAT THE UPDATE OWES, and why it is honest here: [TsoMemPa.pin_ok] --
   "from view [B] on, EVERY agent's read of [a] lands in [Sv]".
   [TsoMemPa.pin_ok_mint] discharges it from the address's LATEST write
   ([t ≤ B] and the value in [Sv]) -- A6.47's refuted standing tie, true as
   a CREATION obligation, which is the whole re-framing -- and the interp
   itself supplies [latest] together with [t ≤ length glog]
   ([TsoMemPa.log_byte_some_le]).  So the caller's only real premise is that
   [B] is AT OR ABOVE THE LOG TOP: a publisher that has drained
   ([RiscvLang.fence_drains] at [__sync_synchronize]) has exactly that, and
   its own view IS such a [B].

   THE CLEAN/DIRTY BIT IS DROPPED, not paid: a dirty entry is a ghost-map
   FRAGMENT, and abandoning one leaves [own_context]'s "every dirty stamp is
   a legal log position" arm intact (it quantifies over the AUTHORITY's
   domain, which does not move).  That is why no [own_context] premise
   appears below -- see [KptPublish.v]'s header for why the tree-level gate
   threads the token anyway.

   WHY ITS OWN FILE: [TsoCtx.v] sits under the whole tree and this is a
   derivation off its PUBLIC unseal lemmas and public gates -- the
   [TsoCtxAbsorbLb.v] precedent (A6.68), same reason.  Fold it into
   [TsoCtx.v]'s pin block at cutover. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map mono_nat.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto Ktier.
Require Import TsoMemPa TsoGhost.
Require Import TsoCtx.
Local Open Scope Z_scope.

Section CtxPinMint.
  Context `{!riscvGS Σ}.

  (* ------------------------------------------------------------------ *)
  (* §1 THE TIMESTAMP IS A LEGAL LOG POSITION.  Read straight off the     *)
  (* interp's LATEST tie: [latest] asks for [log_byte … t a = Some v],    *)
  (* and [log_byte] is [None] past the end of the log.  This is the half  *)
  (* of the mint obligation the caller must NOT be asked for -- it is     *)
  (* true of every element in the map and of nothing the caller holds.    *)
  (* ------------------------------------------------------------------ *)
  Lemma tso_interp_ts_le (g : gstate) (a : Arch.pa) (dq : dfrac)
      (e : TsoMemPa.ts_elem) :
    tso_interp_at riscv_eraGS g -∗ a ↪[ts_name]{dq} e -∗
    ⌜(e.1 <= length g.(glog))%nat⌝.
  Proof.
    iIntros "Hint He".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    iDestruct (ghost_map_lookup with "Hauth He") as %HTM.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTM)) as (v0 & _ & Hlat).
    iPureIntro. destruct Hlat as [Hlb _].
    exact (log_byte_some_le _ _ _ _ _ Hlb).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §1a THE HART'S OWN PUBLICATIONS.  A message this hart wrote sits at   *)
  (* an index below its own [own_pub], which is what a DRAIN carries the   *)
  (* view past ([TsoMemPa.fence_post]).  Two pure steps stdpp does not     *)
  (* have; kept here rather than in [TsoMemPa] because that file is under  *)
  (* the whole tree and this is a leaf.                                    *)
  (* ------------------------------------------------------------------ *)
  Lemma foldr_max_ge (l : list nat) (x : nat) :
    x ∈ l -> (x <= foldr Nat.max 0%nat l)%nat.
  Proof. induction 1; simpl; lia. Qed.

  Lemma own_pub_ge (h : agent) (log : list pwmsg) (i : nat) (msg : pwmsg) :
    log !! i = Some msg -> pm_tid msg = h -> (S i <= own_pub h log)%nat.
  Proof.
    intros Hlk Htid. rewrite /own_pub. apply foldr_max_ge.
    apply elem_of_lookup_imap. exists i, msg. split; [|exact Hlk].
    rewrite bool_decide_eq_true_2; [reflexivity|exact Htid].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §1b THE TOKEN'S BOUND ON ITS OWN BYTES, and this is the sentence     *)
  (* that makes the publication fit a FENCE rather than a top-of-log.     *)
  (*                                                                      *)
  (* A byte registered to a context the hart is RUNNING has a timestamp    *)
  (* that is either                                                       *)
  (*   - CLEAN: under the token's own bound [B], which the token's         *)
  (*     receipt puts under this hart's view; or                          *)
  (*   - DIRTY: an entry of the token's dirty set, and [TsoGhost.dirty_ok] *)
  (*     says a dirty entry is either under [B] too or is THIS HART'S OWN  *)
  (*     MESSAGE -- in which case its index is under [own_pub], which a    *)
  (*     drain has carried the view past.                                 *)
  (*                                                                      *)
  (* Those are exactly [TsoMemPa.visibleb]'s two arms, one tier up.  The   *)
  (* alternative -- demanding [length glog <= gtv cpu_id] -- would need    *)
  (* [TsoMemPa.all_own], a fact about OTHER agents that no client holds.   *)
  (* ------------------------------------------------------------------ *)
  Lemma ctx_phys_ts_own `{CID : CpuId} (g : gstate) (xi : CtxId)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) (t : nat) :
    (own_pub (hart_agent cpu_id) g.(glog) <= g.(gtv) cpu_id)%nat ->
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    phys_pointsto a dq v -∗ a ↪[ts_name]{dq} ((t, None) : TsoMemPa.ts_elem) -∗
    (llb (ctx_bound_name xi) t ∨ (t, a) ↪[ctx_dirty_name xi]{dq} ()) -∗
    ⌜(t <= g.(gtv) cpu_id)%nat⌝.
  Proof.
    iIntros (Hdrain) "Hint Hrun Hpt Hts Hbit".
    rewrite own_context_unseal /own_context_def.
    iDestruct "Hrun"
      as (B K W D) "([Hb' Hd'] & #HK & %HBK & #HW & %HDW & #Hoks)".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    iDestruct (view_auth_valid with "Hvw HK") as %HKtv.
    rewrite avf_hart in HKtv.
    iDestruct "Hbit" as "[Hclean | Hdirty]".
    - iDestruct (llb_valid with "Hb' Hclean") as %HtB. iPureIntro. lia.
    - iDestruct (ghost_map_lookup with "Hd' Hdirty") as %HDlk.
      iDestruct (big_sepM_lookup _ _ _ _ HDlk with "Hoks") as "Hok".
      iDestruct "Hok" as "[%Hle | (%i & %msg & %Hti & Hi & %Htid)]".
      + cbn in Hle. iPureIntro. lia.
      + iDestruct (ghost_map_lookup with "Hm Hi") as %HLi.
        cbn in Hti. iPureIntro.
        rewrite HLM in HLi.
        have := own_pub_ge (hart_agent cpu_id) g.(glog) i msg HLi Htid.
        lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §2 THE BYTE GATE.  A registered byte owned OUTRIGHT leaves its       *)
  (* context and arrives pinned at the publisher's OWN VIEW.  The         *)
  (* fraction is [DfracOwn 1] and cannot be weakened: [ghost_map_update]  *)
  (* is a full-fraction move, and that is also what makes [Sv] a genuine  *)
  (* confinement afterwards -- nobody else can write the cell.            *)
  (* ------------------------------------------------------------------ *)
  Lemma ctx_phys_pin_mint `{CID : CpuId} (g : gstate) (xi : CtxId)
      (a : Arch.pa) (v : bv 8) (Sv : TsoMemPa.byteset) :
    (own_pub (hart_agent cpu_id) g.(glog) <= g.(gtv) cpu_id)%nat ->
    v ∈ Sv ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    ctx_phys_pointsto xi a (DfracOwn 1) v ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    ∃ t : nat, phys_ledger_pin a (DfracOwn 1) v t (g.(gtv) cpu_id) Sv.
  Proof.
    iIntros (Hdrain Hv) "Hgh Hint Hrun Hb".
    rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def.
    iDestruct "Hb" as (t) "(Hpt & Hts & Hbit)".
    iDestruct (ctx_phys_ts_own g xi a (DfracOwn 1) v t Hdrain
                 with "Hint Hrun Hpt Hts Hbit") as %Htb.
    iMod (ledger_pin_mint g a v t (g.(gtv) cpu_id) Sv Htb Hv
            with "Hgh Hint [$Hpt $Hts]") as "(Hgh & Hint & Hpin)".
    iModIntro. iFrame "Hgh Hint Hrun". iExists t. iExact "Hpin".
  Qed.

  (* the byte-run form, folded left to right so the interp AND THE TOKEN  *)
  (* thread: an [n]-byte window of registered bytes arrives as [n] pinned  *)
  (* ones at the publisher's own view, with the allowed sets indexed by    *)
  (* OFFSET.                                                              *)
  Lemma ctx_phys_bytes_pin_mint `{CID : CpuId} (g : gstate) (xi : CtxId)
      (a : Arch.pa) (n : nat) (f : nat -> bv 8)
      (Sf : nat -> TsoMemPa.byteset) :
    (own_pub (hart_agent cpu_id) g.(glog) <= g.(gtv) cpu_id)%nat ->
    (forall j : nat, (j < n)%nat -> f j ∈ Sf j) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    ([∗ list] j ∈ seq 0 n, ctx_phys_pointsto xi (pa_add a j) (DfracOwn 1) (f j))
    ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    ([∗ list] j ∈ seq 0 n, ∃ t : nat,
       phys_ledger_pin (pa_add a j) (DfracOwn 1) (f j) t (g.(gtv) cpu_id) (Sf j)).
  Proof.
    intros Hdrain. induction n as [|n IH]; intros Hf.
    - iIntros "Hgh Hint Hrun Hl". iModIntro. iFrame "Hgh Hint Hrun".
      iExact "Hl".
    - rewrite seq_S !big_sepL_app /=.
      iIntros "Hgh Hint Hrun [Hb [Hlast _]]".
      iMod (IH ltac:(intros j Hj; apply Hf; lia) with "Hgh Hint Hrun Hb")
        as "(Hgh & Hint & Hrun & Hb)".
      iMod (ctx_phys_pin_mint g xi (pa_add a n) (f n) (Sf n) Hdrain
              (Hf n ltac:(lia)) with "Hgh Hint Hrun Hlast")
        as "(Hgh & Hint & Hrun & Hlast)".
      iModIntro. iFrame "Hgh Hint Hrun Hb Hlast".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §3 THE WORD GATE -- the shape a page-table SLOT is spelled at.  The  *)
  (* set family is a parameter for [TsoCtx]'s own reason (naming          *)
  (* [pte_canon] at this altitude is the layering violation candidate     *)
  (* (iv) was rejected for); [PtTree.pte_slot_set] supplies it one file   *)
  (* up.                                                                  *)
  (* ------------------------------------------------------------------ *)
  Lemma ctx_phys_word_pin_mint `{CID : CpuId} (g : gstate) (xi : CtxId)
      (a : Arch.pa) (w : bv 64) (Sf : nat -> TsoMemPa.byteset) :
    (own_pub (hart_agent cpu_id) g.(glog) <= g.(gtv) cpu_id)%nat ->
    (forall j : nat, (j < 8)%nat -> nth_byte w j ∈ Sf j) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    ctx_phys_word_pointsto xi a (DfracOwn 1) w ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    phys_ledger_word_pin a (DfracOwn 1) w (g.(gtv) cpu_id) Sf.
  Proof.
    iIntros (Hdrain HS) "Hgh Hint Hrun Hw".
    iDestruct (ctx_phys_word_pointsto_aligned_p with "Hw") as %Hal.
    iDestruct (ctx_phys_word_pointsto_bytes with "Hw") as "Hb".
    iMod (ctx_phys_bytes_pin_mint g xi a 8 (nth_byte w) Sf Hdrain HS
            with "Hgh Hint Hrun Hb") as "(Hgh & Hint & Hrun & Hb)".
    iModIntro. iFrame "Hgh Hint Hrun".
    by iApply (phys_ledger_word_pin_intro a (DfracOwn 1) w (g.(gtv) cpu_id)
                 Sf Hal).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §4 THE RECEIPT, AT THE CURRENT VIEW.  [TsoCtx.hart_view_lb_get] asks *)
  (* for the at-the-top premise only to COMPARE a stamp against the view; *)
  (* the receipt itself is an INCLUSION and is free at any state          *)
  (* ([mm_ok] already bounds the view by the log length).  A publisher     *)
  (* needs it to hand its own bound on to every later reader.             *)
  (* ------------------------------------------------------------------ *)
  Lemma hart_view_lb_now `{CID : CpuId} (g : gstate) :
    tso_interp_at riscv_eraGS g -∗
    tso_interp_at riscv_eraGS g ∗ hart_view_lb (g.(gtv) cpu_id).
  Proof.
    rewrite hart_view_lb_unseal /hart_view_lb_def.
    iIntros "Hint".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as [Hflat Htv].
    iDestruct (view_lb_get _ _ (avf g) (length g.(glog)) (hart_agent cpu_id)
                with "Hv Hlen") as "(Hv & Hlen & #Hrcpt)".
    { rewrite avf_hart. apply Htv. }
    rewrite avf_hart. iFrame "Hrcpt".
    iExists TM, LM. iFrame. iPureIntro. split_and!; done.
  Qed.

End CtxPinMint.
