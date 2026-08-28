
  (* ---------------------------------------------------------------- *)
  (* THE STORE GATE and its window loop                                *)
  (* ---------------------------------------------------------------- *)

  (* THE FORWARD HALF of [write_bytes]'s lookup law.  [RiscvLang] exports
     the OUTSIDE half ([write_bytes_lookup_notin]) and the BACKWARD half
     ([snap_of_lookup_Some]); the store gate needs the forward one -- a
     store's own byte is what the map holds INSIDE the window -- which is
     true exactly when the window's physical addresses are pairwise
     distinct (the gate's second premise; a wrapping window would alias). *)
  Local Lemma foldr_ins_lookup_in (l : list nat) (pa : Arch.pa)
      (f : nat -> bv 8) (mm : gmap Arch.pa (bv 8)) (j : nat) :
    j ∈ l ->
    (forall j1 j2, j1 ∈ l -> j2 ∈ l -> pa_add pa j1 = pa_add pa j2 -> j1 = j2) ->
    foldr (fun k acc => <[pa_add pa k := f k]> acc) mm l !! pa_add pa j
    = Some (f j).
  Proof.
    induction l as [|k l IH]; intros Hj Hinj.
    - by apply elem_of_nil in Hj.
    - destruct (decide (k = j)) as [->|Hne].
      + by rewrite /= lookup_insert.
      + have Hne' : pa_add pa k <> pa_add pa j.
        { intros Heq. apply Hne. by apply (Hinj k j); [left|exact Hj|]. }
        rewrite /= lookup_insert_ne; last exact Hne'.
        apply elem_of_cons in Hj as [Heq|Hj']; first done.
        apply IH; first exact Hj'.
        intros j1 j2 H1 H2 Heq. apply (Hinj j1 j2); [by right|by right|exact Heq].
  Qed.

  Local Lemma write_bytes_lookup_in {w : N} (mm : gmap Arch.pa (bv 8))
      (pa : Arch.pa) (n : N) (v : bv w) (j : nat) :
    (N.of_nat j < n)%N ->
    (forall j1 j2 : nat, (N.of_nat j1 < n)%N -> (N.of_nat j2 < n)%N ->
       pa_add pa j1 = pa_add pa j2 -> j1 = j2) ->
    write_bytes mm pa n v !! pa_add pa j = Some (nth_byte v j).
  Proof.
    intros Hj Hinj. unfold write_bytes. apply foldr_ins_lookup_in.
    - apply elem_of_seq. lia.
    - intros j1 j2 H1 H2. apply elem_of_seq in H1. apply elem_of_seq in H2.
      apply Hinj; lia.
  Qed.

  (* THE WINDOW LOOP.  Three authorities move in lock-step under ONE
     foldr shape -- the flat cache (whose foldr IS [write_bytes]), the
     per-byte timestamp map, and the context's dirty set -- and the five
     pure outputs are exactly what the interp's two ties, its dom
     conjunct, and the token's watermark/justification need at the new
     top.  Stated over an arbitrary index list so the induction is
     available; the gate instantiates [l := seq 0 (N.to_nat n)]. *)
  Local Lemma ctx_store_window {KTR : CurKtier} (ξ : CtxId)
      (va pa : Arch.pa) (ppn : mword 44) (old new : nat -> bv 8)
      (t' W : nat) (l : list nat) (mm : gmap Arch.pa (bv 8))
      (TM : gmap Arch.pa nat) (D : gmap (nat * Arch.pa) unit) :
    (forall j : nat, j ∈ l -> pa_of ppn (pa_add va j) = pa_add pa j) ->
    (forall j1 j2 : nat, j1 ∈ l -> j2 ∈ l ->
       pa_add pa j1 = pa_add pa j2 -> j1 = j2) ->
    (forall j : nat, j ∈ l -> svpn_of (pa_add va j) = svpn_of va) ->
    NoDup l ->
    dom TM = dom mm ->
    (forall k, k ∈ dom D -> (k.1 ≤ W)%nat) -> (W < t')%nat ->
    kmap_at (svpn_of va) ppn KP_rw -∗
    gen_heap_interp (hG := riscv_memGS) mm -∗
    ghost_map_auth ts_name 1 TM -∗
    ghost_map_auth (ctx_dirty_name ξ) 1 D -∗
    ([∗ list] j ∈ l,
       ctx_pointsto (KTR := KTR) ξ (pa_add va j) (DfracOwn 1) (old j)) ==∗
    ∃ (mm' : gmap Arch.pa (bv 8)) (TM' : gmap Arch.pa nat)
      (D' : gmap (nat * Arch.pa) unit),
      ⌜mm' = foldr (fun j acc => <[pa_add pa j := new j]> acc) mm l⌝ ∗
      ⌜dom TM' = dom mm'⌝ ∗
      ⌜forall j, j ∈ l -> TM' !! pa_add pa j = Some t'
                          /\ mm' !! pa_add pa j = Some (new j)⌝ ∗
      ⌜forall a, (forall j, j ∈ l -> pa_add pa j <> a) ->
         TM' !! a = TM !! a /\ mm' !! a = mm !! a⌝ ∗
      ⌜forall k, k ∈ dom D' ->
         (exists j, j ∈ l /\ k = (t', pa_add pa j)) \/ k ∈ dom D⌝ ∗
      gen_heap_interp (hG := riscv_memGS) mm' ∗
      ghost_map_auth ts_name 1 TM' ∗
      ghost_map_auth (ctx_dirty_name ξ) 1 D' ∗
      ([∗ list] j ∈ l,
         ctx_pointsto (KTR := KTR) ξ (pa_add va j) (DfracOwn 1) (new j)).
  Proof.
    induction l as [|j0 l IH];
      iIntros (Hpa Hinj Hsvpn Hnd Hdm HDW HWt) "#Hk Hgh Hts Hd Hfs".
    - iModIntro. iExists mm, TM, D. iFrame "Hgh Hts Hd Hfs".
      iPureIntro. split_and!.
      + done.
      + exact Hdm.
      + intros j Hj. by apply elem_of_nil in Hj.
      + intros a _. done.
      + intros k Hk. by right.
    - apply NoDup_cons in Hnd as [Hj0 Hnd].
      iDestruct "Hfs" as "[Hf Hfs]".
      have Hpa' : forall j : nat, j ∈ l -> pa_of ppn (pa_add va j) = pa_add pa j.
      { intros j Hj. apply Hpa. by right. }
      have Hinj' : forall j1 j2 : nat, j1 ∈ l -> j2 ∈ l ->
         pa_add pa j1 = pa_add pa j2 -> j1 = j2.
      { intros j1 j2 H1 H2. apply Hinj; by right. }
      have Hsvpn' : forall j : nat, j ∈ l -> svpn_of (pa_add va j) = svpn_of va.
      { intros j Hj. apply Hsvpn. by right. }
      iMod (IH Hpa' Hinj' Hsvpn' Hnd Hdm HDW HWt with "Hk Hgh Hts Hd Hfs")
        as (mm1 TM1 D1)
           "(%Hmm1 & %Hdm1 & %Hin1 & %Hout1 & %HD1 & Hgh & Hts & Hd & Hfs)".
      (* the head byte: pin its claim to [ppn], then move all three *)
      have Hsv : svpn_of (pa_add va j0) = svpn_of va.
      { apply Hsvpn. by left. }
      have Hpaj : pa_of ppn (pa_add va j0) = pa_add pa j0.
      { apply Hpa. by left. }
      iEval (rewrite ctx_pointsto_unseal /ctx_pointsto_def) in "Hf".
      iDestruct "Hf" as (ppn0 t0) "(Hk0 & %Hc0 & %Hr0 & %Hp0 & Hpt & Hte & Hbit)".
      iAssert (kmap_at (svpn_of (pa_add va j0)) ppn KP_rw) as "#Hkk".
      { rewrite Hsv. iExact "Hk". }
      iDestruct (kmap_at_agree with "Hk0 Hkk") as %[-> _].
      iClear "Hk0 Hkk". iClear "Hbit".
      rewrite Hpaj in Hr0. rewrite Hpaj.
      iMod (gen_heap_update _ _ _ (new j0) with "Hgh Hpt") as "[Hgh Hpt]".
      iMod (ghost_map_update t' with "Hts Hte") as "[Hts Hte]".
      have Hfresh : D1 !! (t', pa_add pa j0) = None.
      { destruct (D1 !! (t', pa_add pa j0)) as [[]|] eqn:HDk; last done.
        exfalso.
        destruct (HD1 _ (elem_of_dom_2 _ _ _ HDk)) as [(j & Hj & Heq)|Hk0].
        - apply Hj0. injection Heq as Heq.
          have -> : j0 = j by apply Hinj; [by left|by right|exact Heq].
          exact Hj.
        - have := HDW _ Hk0. simpl. lia. }
      iMod (ghost_map_insert (t', pa_add pa j0) () Hfresh with "Hd") as "[Hd Hdt]".
      iModIntro.
      iExists (<[pa_add pa j0 := new j0]> mm1), (<[pa_add pa j0 := t']> TM1),
              (<[(t', pa_add pa j0) := ()]> D1).
      iSplit; first (iPureIntro; by rewrite /= Hmm1).
      iSplit; first (iPureIntro; by rewrite !dom_insert_L Hdm1).
      iSplit.
      { iPureIntro. intros j Hj.
        destruct (decide (j = j0)) as [->|Hne].
        - by rewrite !lookup_insert.
        - have Hj' : j ∈ l by (apply elem_of_cons in Hj as [->|?]; done).
          have Hne' : pa_add pa j0 <> pa_add pa j.
          { intros Heq. apply Hne. symmetry. apply Hinj; [by left|by right|done]. }
          rewrite !lookup_insert_ne //. by apply Hin1. }
      iSplit.
      { iPureIntro. intros a Ha.
        have Hne0 : pa_add pa j0 <> a by apply Ha; left.
        have Hnet : (t', pa_add pa j0) <> (t', a).
        { intros Heq. by injection Heq. }
        rewrite !lookup_insert_ne //. apply Hout1.
        intros j Hj. apply Ha. by right. }
      iSplit.
      { iPureIntro. intros k Hk.
        rewrite dom_insert_L elem_of_union elem_of_singleton in Hk.
        destruct Hk as [->|Hk].
        - left. exists j0. split; [by left|done].
        - destruct (HD1 _ Hk) as [(j & Hj & Heq)|Hk0].
          + left. exists j. split; [by right|done].
          + by right. }
      iFrame "Hgh Hts Hd".
      simpl. iFrame "Hfs".
      iEval (rewrite ctx_pointsto_unseal /ctx_pointsto_def).
      iExists ppn, t'. rewrite Hpaj Hsv. iFrame "Hk Hpt Hte".
      iSplit; first done. iSplit; first done. iSplit; first done.
      iRight. iExact "Hdt".
  Qed.

  (* THE STORE GATE ([TsoCtxTwin2.twin_store_ok] at the machine's write
     arm, n-byte form): a store by the running hart appends ONE message
     and moves the flat cache in lock-step; the window's facts
     re-register at the new top as DIRTY (their author-tie is the
     freshly persisted log entry).  The view side is the ARM's business:
     [g'] may keep this hart's view (plain store) or bump it past the
     append (the AMO write half); both are monotone. *)
  Lemma ctx_store_ghost `{CID : CpuId} {KTR : CurKtier} (g g' : gstate)
      (ξ : CtxId) (va : Arch.pa) (ppn : mword 44) (n : N) {wsz : N}
      (v : bv wsz) (old : nat -> bv 8) :
    let pa := pa_of ppn va in
    let msg := PWMsg (snap_of pa n v) (hart_agent cpu_id) in
    (forall j : nat, (N.of_nat j < n)%N ->
       pa_of ppn (pa_add va j) = pa_add pa j) ->
    (forall j1 j2 : nat, (N.of_nat j1 < n)%N -> (N.of_nat j2 < n)%N ->
       pa_add pa j1 = pa_add pa j2 -> j1 = j2) ->
    (forall j1 j2 : nat, (N.of_nat j1 < n)%N -> (N.of_nat j2 < n)%N ->
       pa_add va j1 = pa_add va j2 -> j1 = j2) ->
    (forall j : nat, (N.of_nat j < n)%N ->
       svpn_of (pa_add va j) = svpn_of va) ->
    g'.(gmem) = write_bytes g.(gmem) pa n v ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = g.(glog) ++ [msg] ->
    (forall c : CPU, g'.(gtv) c = g.(gtv) c \/
       (g'.(gtv) c = S (length g.(glog)))) ->
    kmap_at (svpn_of va) ppn KP_rw -∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ctx_pointsto (KTR := KTR) ξ (pa_add va j) (DfracOwn 1) (old j)) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    own_context ξ ∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ctx_pointsto (KTR := KTR) ξ (pa_add va j) (DfracOwn 1) (nth_byte v j)).
  Proof.
    cbv zeta.
    intros Hpa Hinj Hinjva Hsvpn Hmem' Himg' Hlog' Htv'.
    iIntros "#Hk Hgh Hint Hrun Hfacts".
    iEval (rewrite own_context_unseal /own_context_def) in "Hrun".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as [Hflat Htvb].
    iDestruct "Hrun"
      as "(%B & %K & %W & %D & [Hb Hd] & #HK & %HBK & #HW & %HDW & #Hoks)".
    iDestruct (llb_valid with "Hlen HW") as %HWlen.
    (* the message, persisted into the log ghost at its own slot *)
    have HLMfresh : LM !! length g.(glog) = None.
    { rewrite HLM. apply lookup_ge_None_2. lia. }
    iMod (ghost_map_insert_persist (length g.(glog))
            (PWMsg (snap_of (pa_of ppn va) n v) (hart_agent cpu_id))
            HLMfresh with "Hm") as "[Hm #Hlogm]".
    iMod (mono_nat_own_update (length g'.(glog)) with "Hlen") as "[Hlen #Hllb]".
    { rewrite Hlog' length_app /=. lia. }
    (* the view: monotone on both arms of the premise *)
    have Hview : forall h, (avf g h ≤ avf g' h)%nat.
    { intros h. rewrite /avf. destruct (lt_dec h NCPU) as [Hlt|Hge].
      - destruct (Htv' (nat_to_fin Hlt)) as [Heq|Heq]; rewrite Heq; first lia.
        have := Htvb (nat_to_fin Hlt). lia.
      - rewrite Hlog' length_app /=. lia. }
    iMod (view_auth_update _ (avf g) (avf g') Hview with "Hv") as "Hv".
    (* the window *)
    have Hpal : forall j : nat, j ∈ seq 0 (N.to_nat n) ->
       pa_of ppn (pa_add va j) = pa_add (pa_of ppn va) j.
    { intros j Hj. apply elem_of_seq in Hj. apply Hpa. lia. }
    have Hinjl : forall j1 j2 : nat, j1 ∈ seq 0 (N.to_nat n) ->
       j2 ∈ seq 0 (N.to_nat n) ->
       pa_add (pa_of ppn va) j1 = pa_add (pa_of ppn va) j2 -> j1 = j2.
    { intros j1 j2 H1 H2. apply elem_of_seq in H1. apply elem_of_seq in H2.
      apply Hinj; lia. }
    have Hsvl : forall j : nat, j ∈ seq 0 (N.to_nat n) ->
       svpn_of (pa_add va j) = svpn_of va.
    { intros j Hj. apply elem_of_seq in Hj. apply Hsvpn. lia. }
    have HWt : (W < S (length g.(glog)))%nat by lia.
    iMod (ctx_store_window ξ va (pa_of ppn va) ppn old (nth_byte v)
            (S (length g.(glog))) W (seq 0 (N.to_nat n)) g.(gmem) TM D
            Hpal Hinjl Hsvl (NoDup_seq 0 (N.to_nat n)) Hdom HDW HWt
            with "Hk Hgh Hts Hd Hfacts")
      as (mm1 TM1 D1)
         "(%Hmm1 & %Hdm1 & %Hin1 & %Hout1 & %HD1 & Hgh & Hts & Hd & Hfacts)".
    have Hmm1' : mm1 = write_bytes g.(gmem) (pa_of ppn va) n v.
    { rewrite Hmm1. reflexivity. }
    iModIntro.
    iSplitL "Hgh".
    { by rewrite Hmem' -Hmm1'. }
    iSplitL "Hts Hm Hlen Hv".
    { iExists TM1, (<[length g.(glog)
                      := PWMsg (snap_of (pa_of ppn va) n v)
                           (hart_agent cpu_id)]> LM).
      iFrame "Hts Hm Hlen Hv". iPureIntro. split_and!.
      - rewrite Hmem' -Hmm1'. exact Hdm1.
      - intros a t Ha.
        destruct (decide (a ∈ footprint (pa_of ppn va) n)) as [Hf|Hf].
        + apply elem_of_footprint in Hf as (j & Hj & ->).
          have Hjl : j ∈ seq 0 (N.to_nat n) by (apply elem_of_seq; lia).
          destruct (Hin1 j Hjl) as [HT Hmv].
          rewrite HT in Ha. injection Ha as <-.
          exists (nth_byte v j). split.
          * rewrite Hmem' -Hmm1'. exact Hmv.
          * rewrite Himg' Hlog'. apply latest_app_new.
            rewrite /msg_byte /= /snap_of.
            by apply write_bytes_lookup_in.
        + have Hne : forall j, j ∈ seq 0 (N.to_nat n) ->
             pa_add (pa_of ppn va) j <> a.
          { intros j Hj Heq. apply Hf, elem_of_footprint. exists j.
            apply elem_of_seq in Hj. split; [lia|done]. }
          destruct (Hout1 a Hne) as [HT Hmv].
          rewrite HT in Ha.
          destruct (Htie a t Ha) as (v0 & Hg0 & Hlat).
          exists v0. split.
          * rewrite Hmem' -Hmm1' Hmv. exact Hg0.
          * rewrite Himg' Hlog'. apply latest_app_frame; last exact Hlat.
            rewrite /msg_byte /= /snap_of.
            by rewrite (write_bytes_lookup_notin ∅ _ _ _ _ Hf) lookup_empty.
      - intros i. rewrite Hlog'.
        destruct (decide (i = length g.(glog))) as [->|Hne].
        + rewrite lookup_insert. symmetry. by apply list_lookup_middle.
        + rewrite lookup_insert_ne; last done. rewrite HLM.
          destruct (decide (i < length g.(glog))%nat) as [Hlt|Hge].
          * by rewrite lookup_app_l.
          * rewrite !lookup_ge_None_2 //; rewrite ?length_app /=; lia.
      - split.
        + rewrite Hmem' Himg' Hlog' /snap_of flat_store -Hflat. reflexivity.
        + intros c. rewrite Hlog' length_app /=.
          destruct (Htv' c) as [Heq|Heq]; rewrite Heq;
            [have := Htvb c; lia | lia]. }
    iSplitL "Hb Hd"; last iExact "Hfacts".
    rewrite own_context_unseal /own_context_def.
    iExists B, K, (length g'.(glog)), D1.
    iFrame "Hb Hd HK".
    iSplit; first done.
    iSplit; first (rewrite /llb; iLeft; iExact "Hllb").
    iSplit.
    { iPureIntro. intros k Hk.
      rewrite Hlog' length_app /=.
      destruct (HD1 _ Hk) as [(j & Hj & ->)|Hk0]; simpl; first lia.
      have := HDW _ Hk0. lia. }
    iApply big_sepM_intro. iIntros "!>" (k [] Hk).
    destruct (HD1 _ (elem_of_dom_2 _ _ _ Hk)) as [(j & Hj & ->)|Hk0].
    - iRight.
      iExists (length g.(glog)),
        (PWMsg (snap_of (pa_of ppn va) n v) (hart_agent cpu_id)).
      iFrame "Hlogm". iPureIntro. by split.
    - apply elem_of_dom in Hk0 as [[] Hk0].
      iDestruct (big_sepM_lookup _ _ _ _ Hk0 with "Hoks") as "H".
      iExact "H".
  Qed.
