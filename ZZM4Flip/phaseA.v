  (* ================================================================== *)
  (* THE M4 LOCK KIT'S LEDGER-TIER GATES (tso-m4-memo.md; A6.84).        *)
  (*                                                                    *)
  (* The lock's two cells cannot live in the ctx tower: the WORD is      *)
  (* written by whichever hart wins the AMO, and the OWNER cell carries  *)
  (* a claim about the log that only a ledger element can hold.  Both    *)
  (* therefore sit at the LEDGER tier, which is ξ-FREE -- and that is    *)
  (* what keeps [is_lock] a closed term (tso-port.md §0.19′) with no ∃ξ  *)
  (* at all, rather than an existential nothing can eliminate.           *)
  (*                                                                    *)
  (* What a ledger cell does NOT carry is the address's MAPPING, so the  *)
  (* lock's invariant carries the two [wordw_claim]s persistently        *)
  (* instead.  That is the trade the tier change makes, and it is a good *)
  (* one: the claim is about the ADDRESS, not the value, so it is        *)
  (* persistent and one peek serves every leaf.                          *)
  (* ================================================================== *)

  (* AT KT0 A CTX BYTE IS A LEDGER BYTE, and the bridge is the tier pin
     the cell already carries: [ktier_pin KT0 ppn a] IS [pa_of ppn a = a]
     ([ktier_pin_id]), so no external claim is needed.  ONE-WAY, as
     always: the ctx residue (the clean/dirty bit) is dropped, and a cell
     that has left the tower does not come back. *)
  Lemma ctx_pointsto_ledger_kt0 (ξ : CtxId) (a : Arch.pa) (dq : dfrac)
      (v : bv 8) :
    ctx_pointsto (KTR := KT0) ξ a dq v ⊢ phys_ledger a dq v.
  Proof.
    rewrite (ctx_pointsto_phys (KTR := KT0) ξ a dq v).
    iIntros "(%ppn & _ & _ & %Hpin & Hb)".
    rewrite (ktier_pin_id ppn a Hpin).
    by iApply ctx_phys_pointsto_ledger.
  Qed.

  (* ---- THE FOUR-BYTE LEDGER WORD: the lock word's carrier ---- *)
  Definition phys_ledger_word4 (a : Arch.pa) (dq : dfrac) (w : bv 32) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗
     [∗ list] j ∈ seq 0 4, phys_ledger (pa_add a j) dq (nth_byte w j))%I.

  Lemma phys_ledger_word4_unfold a dq w :
    phys_ledger_word4 a dq w ⊣⊢
    ⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗
    ([∗ list] j ∈ seq 0 4, phys_ledger (pa_add a j) dq (nth_byte w j)).
  Proof. reflexivity. Qed.

  Lemma phys_ledger_word4_aligned_p a dq w :
    phys_ledger_word4 a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 4 = true⌝.
  Proof. iIntros "[$ _]". Qed.

  Lemma phys_ledger_word4_bytes a dq w :
    phys_ledger_word4 a dq w ⊢
    [∗ list] j ∈ seq 0 4, phys_ledger (pa_add a j) dq (nth_byte w j).
  Proof. iIntros "[_ $]". Qed.

  Lemma phys_ledger_word4_intro a dq w :
    is_aligned_paddr (Physaddr a) 4 = true ->
    ([∗ list] j ∈ seq 0 4, phys_ledger (pa_add a j) dq (nth_byte w j))
    ⊢ phys_ledger_word4 a dq w.
  Proof. iIntros (Hal) "H". by iFrame. Qed.

  Global Instance phys_ledger_word4_timeless a dq w :
    Timeless (phys_ledger_word4 a dq w).
  Proof. rewrite /phys_ledger_word4. apply _. Qed.

  (* the creator's crossing: a KT0 ctx word IS the ledger word *)
  Lemma ctx_word4_ledger_kt0 (ξ : CtxId) (a : Arch.pa) (dq : dfrac) (w : bv 32) :
    ctx_word4_pointsto (KTR := KT0) ξ a dq w ⊢ phys_ledger_word4 a dq w.
  Proof.
    rewrite ctx_word4_pointsto_unfold /phys_ledger_word4.
    iIntros "[$ Hb]".
    iApply (big_sepL_impl with "Hb"). iIntros "!>" (k j _) "H".
    by iApply ctx_pointsto_ledger_kt0.
  Qed.

  Lemma ctx_word_ledger_kt0 (ξ : CtxId) (a : Arch.pa) (dq : dfrac) (w : bv 64) :
    ctx_word_pointsto (KTR := KT0) ξ a dq w ⊢ phys_ledger_word a dq w.
  Proof.
    rewrite ctx_word_pointsto_unfold /phys_ledger_word.
    iIntros "[$ Hb]".
    iApply (big_sepL_impl with "Hb"). iIntros "!>" (k j _) "H".
    by iApply ctx_pointsto_ledger_kt0.
  Qed.

  (* ---- THE HOLDER'S READ, at a cell whose payload is set ----
     [ledger_read_vis_ok]'s twin for a WPAY cell.  Same proof: the
     element's payload arm plays no part in the LATEST tie, which is all
     the read consumes.  It exists because the lock's owner cell carries
     the racy payload and its HOLDER still wants the exact value it
     itself wrote. *)
  Lemma ledger_read_wpay_vis_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) (t B : nat) (W : ts_win) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) B -∗
    ledger_vis (hart_agent cpu_id) B t -∗
    phys_ledger_wpay a dq v t W -∗
    ⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
       tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' a = Some v⌝.
  Proof.
    iIntros "Hgh Hint #HB #Hvis [Hpt Htse]".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    iDestruct (phys_valid with "Hgh Hpt") as %Hgm.
    iDestruct (ghost_map_lookup with "Hts Htse") as %HTMt.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTMt)) as (v0 & Hgm0 & Hlat).
    rewrite Hgm in Hgm0. injection Hgm0 as <-.
    iDestruct (view_auth_valid with "Hv HB") as %HBtvs.
    rewrite avf_hart in HBtvs.
    iAssert (⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
               visibleb (hart_agent cpu_id) tv' g.(glog) t = true⌝)%I as %Hvis.
    { iDestruct "Hvis" as "[%Hb | (%i & %mg & %Hti & Hi & %Htid)]".
      - iPureIntro. intros tv' Htv'. apply visibleb_below. lia.
      - iDestruct (ghost_map_lookup with "Hm Hi") as %HLi.
        iPureIntro. intros tv' _. rewrite Hti.
        apply (visibleb_own _ _ _ _ mg); [by rewrite -HLM | done]. }
    iPureIntro. intros tv' Htv'.
    apply (tso_read_of_latest _ _ _ _ _ t); [exact Hlat|by apply Hvis].
  Qed.

  (* and its window form, in the shape a load leaf's obligation wants *)
  Lemma ledger_read_wpay_bytes_vis_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (n : nat) {m : N} (w : bv m) (dq : dfrac) (B : nat)
      (Wf : nat -> ts_win) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) B -∗
    ([∗ list] j ∈ seq 0 n, ∃ t : nat, ledger_vis (hart_agent cpu_id) B t ∗
       phys_ledger_wpay (pa_add a j) dq (nth_byte w j) t (Wf j)) -∗
    ⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
       tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tv' a
         (N.of_nat n) w⌝.
  Proof.
    iIntros "Hgh Hint #HB Hb".
    iAssert (⌜forall j : nat, (j < n)%nat ->
               forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
                 tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' (pa_add a j)
                 = Some (nth_byte w j)⌝)%I as %HH.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 n) j j with "Hb") as (t) "[#Hvis Hbj]".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (ledger_read_wpay_vis_ok g (pa_add a j) dq (nth_byte w j) t B (Wf j)
                with "Hgh Hint HB Hvis Hbj"). }
    iPureIntro. intros tv' Htv' j Hj. apply HH; [lia|exact Htv'].
  Qed.

  (* a windowed byte is RAM, like every other ledger byte *)
  Lemma phys_ledger_wpay_ram a dq v t W :
    phys_ledger_wpay a dq v t W ⊢ ⌜addr_is_ram a⌝.
  Proof.
    iIntros "[Hp _]". rewrite /phys_pointsto. by iDestruct "Hp" as "[_ $]".
  Qed.

  (* ---- THE WINDOW STORE, in the shape the two cpu-field stores want ----
     [ledger_store_win_pin_ok]'s twin: the payload's [z], [cp] and FLOOR
     are unchanged and only [own] moves, which is exactly
     [win_ok1_app_store]'s two arms lifted to a whole word.  It hands the
     append's own message fragment back, because the AUTHOR of an acquire
     store is the hart whose later read of the cell must be exact. *)
  Lemma phys_ledger_wpay_win_map (pa : Arch.pa) (n : N) {m : N}
      (v : bv m) (dq : dfrac) (Wf : Arch.pa -> ts_win) (Wg : nat -> ts_win) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    (forall j : nat, (j < N.to_nat n)%nat -> Wf (pa_add pa j) = Wg j) ->
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ∃ t : nat, phys_ledger_wpay (pa_add pa j) dq (nth_byte v j) t (Wg j))
    ⊣⊢ wpay_map_own (snap_of pa n v) dq Wf.
  Proof.
    intros Hn HW. rewrite /wpay_map_own /snap_of /write_bytes.
    rewrite <- (big_sepM_foldr_ins
                 (fun a b => ∃ t : nat, phys_ledger_wpay a dq b t (Wf a))%I
                 (fun j => nth_byte v j) pa (seq 0 (N.to_nat n))
                 ltac:(by apply tso_nodup_win)).
    apply big_opL_proper. intros k j Hk.
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    by rewrite (HW (0 + k)%nat ltac:(lia)).
  Qed.

  Lemma ledger_store_win_wpay_ok `{CID : CpuId} (g g' : gstate)
      (base : Arch.pa) (n : N) {m : N} (vold vnew : bv m) (lo : nat)
      (z : nat -> bv 8) (cp : agent -> nat -> bv 8)
      (own own' : agent -> option nat) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    ((forall j, (j < N.to_nat n)%nat -> nth_byte vnew j = z j)
       /\ own' (hart_agent cpu_id) = Some (S (length g.(glog)))
     \/ (forall j, (j < N.to_nat n)%nat -> nth_byte vnew j = cp (hart_agent cpu_id) j)
       /\ own' (hart_agent cpu_id) = None) ->
    (forall h, h <> hart_agent cpu_id -> own' h = own h) ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg (snap_of base n vnew) (hart_agent cpu_id)])%list ->
    g'.(gmem) = write_bytes g.(gmem) base n vnew ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n), ∃ t : nat,
       phys_ledger_wpay (pa_add base j) (DfracOwn 1) (nth_byte vold j) t
         (TsWin base (N.to_nat n) j z cp own lo)) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    ledger_msg_at (length g.(glog))
      (PWMsg (snap_of base n vnew) (hart_agent cpu_id)) ∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       phys_ledger_wpay (pa_add base j) (DfracOwn 1) (nth_byte vnew j)
         (S (length g.(glog))) (TsWin base (N.to_nat n) j z cp own' lo)).
  Proof.
    iIntros (Hn Hstore Hoth Himg Hlog Hmem Htv Htvok') "Hgh Hint Hold".
    set (Wold := fun a : Arch.pa =>
           TsWin base (N.to_nat n) (Z.to_nat (uint a - uint base)) z cp own lo).
    set (Wf := fun a : Arch.pa =>
           TsWin base (N.to_nat n) (Z.to_nat (uint a - uint base)) z cp own' lo).
    assert (HWold : forall j : nat, (j < N.to_nat n)%nat ->
              Wold (pa_add base j) = TsWin base (N.to_nat n) j z cp own lo).
    { intros j Hj. rewrite /Wold (pa_add_off base j) //. lia. }
    assert (HWf : forall j : nat, (j < N.to_nat n)%nat ->
              Wf (pa_add base j) = TsWin base (N.to_nat n) j z cp own' lo).
    { intros j Hj. rewrite /Wf (pa_add_off base j) //. lia. }
    rewrite (phys_ledger_wpay_win_map base n vold (DfracOwn 1) Wold
               (fun j => TsWin base (N.to_nat n) j z cp own lo) Hn HWold).
    iMod (ledger_store_wpay_ok g g' (hart_agent cpu_id)
            (snap_of base n vold) (snap_of base n vnew)
            base (N.to_nat n) lo z cp own own' Wold Wf
            ltac:(by rewrite !dom_snap_of) HWold HWf
            ltac:(intros a Ha; apply dom_snap_of_elem in Ha;
                  destruct Ha as (j & Hj & ->); by exists j)
            ltac:(case: Hstore => [[Hcl Ho] | [Hme Ho]];
                  [ left; split; [ intros j Hj;
                      rewrite (snap_of_lookup base n vnew j ltac:(lia)) (Hcl j Hj) //
                    | exact Ho ]
                  | right; split; [ intros j Hj;
                      rewrite (snap_of_lookup base n vnew j ltac:(lia)) (Hme j Hj) //
                    | exact Ho ] ])
            Hoth Himg Hlog
            ltac:(by rewrite Hmem write_bytes_union) Htv Htvok'
            with "Hgh Hint Hold") as "($ & $ & $ & Hnew)".
    iModIntro.
    rewrite (phys_ledger_wpay_win_map base n vnew (DfracOwn 1) Wf
               (fun j => TsWin base (N.to_nat n) j z cp own' lo) Hn HWf).
    rewrite /wpay_map_own.
    iApply (big_sepM_mono with "Hnew"). iIntros (a v _) "H".
    by iExists (S (length g.(glog))).
  Qed.
