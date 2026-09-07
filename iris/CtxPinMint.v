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
Require Import RiscvModelBytes RiscvLang RiscvPtsto.
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
      as "(%TM & %LM & %DP & %FR & %CH & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & Hdp & #Hdps & %Hdpo & Hdl & Hfr & #Hfrs & %Hfro & Hch & %Hcho & %Hmm)".
    destruct Hmm as (Hmm & Hdlog & Hera).
    iDestruct (ghost_map_lookup with "Hauth He") as %HTM.
    destruct (ts_ok_latest _ _ _ _ _ _ (Htie _ _ HTM)) as (v0 & _ & Hlat).
    iPureIntro. destruct Hlat as [Hlb _].
    exact (log_byte_some_le _ _ _ _ _ Hlb).
  Qed.

  (* §1a/§1b/§2/§3 -- THE DRAIN-ROUTE MINTS (pin at the publisher's own view,
     with [own_pub h glog <= gtv] as the premise) ARE GONE under two logs
     (relaxed-ww.md §2.7): a view is a DRAIN position and a pin's bound
     has to be one too, minted at the publishing fence's record.  That is
     stage E's restatement of [TsoMemPa.pin_ok]; until then the ISSUE-top
     route below is the only mint. *)

  (* §3b, THE LOG-TOP MINTS, ARE GONE (relaxed-ww.md §2.14, the review's
     amendment): a pin is minted AT ITS FLOOR ([TsoCtx.ledger_pin_mint],
     [t = B]) because the two-log reader reads it through the drain of
     the write the floor names.  The kernel table's own-message anchors
     are minted on the boot route ([KptPublish]) at the byte's latest
     write, which is the floor. *)

  (* ------------------------------------------------------------------ *)
  (* §4 THE RECEIPT, AT THE CURRENT VIEW.  [TsoCtxLedger.hart_view_lb_get] asks *)
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
      as "(%TM & %LM & %DP & %FR & %CH & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & Hdp & #Hdps & %Hdpo & Hdl & Hfr & #Hfrs & %Hfro & Hch & %Hcho & %Hmm)".
    destruct Hmm as ((Hflat & Htv & Hcov) & Hdlog & Hera).
    iDestruct (view_lb_get _ _ (avf g) (length g.(gdlog)) (hart_agent cpu_id)
                with "Hv Hdl") as "(Hv & Hdl & #Hrcpt)".
    { rewrite avf_hart. apply Htv. }
    rewrite avf_hart. iFrame "Hrcpt".
    iExists TM, LM, DP, FR, CH. iFrame "Hts Hm Hlen Hv Hdp Hdps Hdl Hfr Hfrs Hch".
    iPureIntro. split_and!; done.
  Qed.

End CtxPinMint.
