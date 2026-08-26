(* FileInv.v -- the ftable lock's resource ([ftable_res]/[is_ftable]) and the
   reference-count ghost-step lemmas: allocating a fresh slot
   ([file_alloc_step]), duplicating/closing a reference ([flive_dup],
   [flive_close{,_last}], [file_dup_step], [file_close{,_last}_step]), and the
   two fraction laws fileclose runs on ([file_rest_absorb], [file_rest_join]).
   Needed only by filealloc/filedup/fileclose/sys_open/sys_pipe/sys_fork/kexit
   -- anything that CHANGES a reference count.

   The geometry, reference-count algebra, and [file_ref]/[fslot] that every
   HOLDER of a file reference needs now live in FileInvDefs.v.  This file is
   that Defs file plus the ghost-step lemmas below it, split out so the
   latter -- needed only by the handful of proofs above -- compiles IN
   PARALLEL with [ProcInv]/[SchedCtx]/[SpecPiperead]/[ProofPiperead] instead
   of sitting as a serial prerequisite of all of them.  `Require Import
   FileInv` still gets everything (this file `Require Export`s FileInvDefs);
   switch to `Require Import FileInvDefs` wherever only the light half is
   needed.  See claude-notes/optimization.md.

   See the "off" note at the bottom of this file and design/file-table.md. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import auth gmap frac numbers.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own cancelable_invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import WpLock.
Require Import TsoCtx.   (* the lock payload's context axis; [<{ }>] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Export FileInvDefs.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import IrefSlots.  (* [iref_frac] -- see FileInvDefs.file_core *)
Local Open Scope Z_scope.

Section FileInv.
  Context `{!riscvGS Σ, !xv6G Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{XI : CurCtx}.


  Definition ftable_res (γ : gname) : iProp Σ :=
    (∃ M : gmap nat (Qp * positive),
       ftable_auth γ M ∗
       (* the fd-slot supply: the table is where the conservation law is
          checked, because the table is what holds one unit per reference. *)
       fd_slots_auth ∗
       ⌜∀ k, is_Some (M !! k) -> (k < NFILE)%nat⌝ ∗
       [∗ list] k ∈ seq 0 NFILE, fslot γ M k)%I.

  (* the whole table: the spinlock named "ftable" over that resource.
     Persistent, so every core shares it. *)
  Definition is_ftable (γl γ : gname) : iProp Σ :=
    is_lock γl ftable_addr "ftable"%string <{ ftable_res γ }>.

  Global Instance is_ftable_persistent γl γ : Persistent (is_ftable γl γ).
  Proof. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  Content: agreement and the fractional split                         *)
  (* ------------------------------------------------------------------ *)

  (* Two fds onto the same file agree on its content -- for free, because a
     reference carries genuine points-to fractions.  No [agree] ghost. *)
  Lemma file_fields_agree k q1 C1 q2 C2 :
    file_fields k q1 C1 -∗ file_fields k q2 C2 -∗ ⌜C1 = C2⌝.
  Proof.
    rewrite /file_fields.
    iIntros "(Ht1 & Hr1 & Hw1 & Hp1 & Hi1 & Hm1)".
    iIntros "(Ht2 & Hr2 & Hw2 & Hp2 & Hi2 & Hm2)".
    iDestruct (word4_pointsto_agree with "Ht1 Ht2") as %E1.
    iDestruct (ctx_pointsto_agree with "Hr1 Hr2") as %E2.
    iDestruct (ctx_pointsto_agree with "Hw1 Hw2") as %E3.
    iDestruct (ctx_word_pointsto_agree with "Hp1 Hp2") as %E4.
    iDestruct (ctx_word_pointsto_agree with "Hi1 Hi2") as %E5.
    iDestruct (word2_pointsto_agree with "Hm1 Hm2") as %E7.
    iPureIntro. destruct C1, C2; cbn in *. congruence.
  Qed.

  (* THE FILE'S INODE, read out of a reference at ANY fraction.  This is the
     bridge the off-borrow invariant is opened with: the invariant holds the
     OTHER half of the same cell, so agreement identifies the two. *)
  Lemma file_fields_ip k q C :
    file_fields k q C -∗ a_fip k ↦₈{DfracOwn (q/2)} fc_ip C.
  Proof. iIntros "(_ & _ & _ & _ & $ & _)". Qed.

  Lemma file_ref_agree γ k q1 C1 q2 C2 :
    file_ref γ k q1 C1 -∗ file_ref γ k q2 C2 -∗ ⌜C1 = C2⌝.
  Proof.
    iIntros "(_ & H1 & _) (_ & H2 & _)".
    by iApply (file_fields_agree with "H1 H2").
  Qed.

  (* the split filedup performs and fileclose undoes. *)
  Lemma file_fields_frac_split k q1 q2 C :
    file_fields k (q1 + q2) C ⊣⊢ file_fields k q1 C ∗ file_fields k q2 C.
  Proof.
    rewrite /file_fields.
    rewrite (word4_pointsto_frac_split (a_ftype k)).
    rewrite (ctx_pointsto_frac_split _ (a_freadable k)).
    rewrite (ctx_pointsto_frac_split _ (a_fwritable k)).
    rewrite (ctx_word_pointsto_frac_split _ (a_fpipe k)).
    rewrite (word2_pointsto_frac_split (a_fmajor k)).
    (* the ip cell is at HALF, and halving distributes over the sum *)
    rewrite Qp.div_add_distr (ctx_word_pointsto_frac_split _ (a_fip k)).
    iSplit.
    - iIntros "([A1 B1] & [A2 B2] & [A3 B3] & [A4 B4] & [A5 B5] & [A6 B6])".
      iFrame.
    - iIntros "[(A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6)]".
      iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  Reaching into the table                                             *)
  (* ------------------------------------------------------------------ *)

  (* Borrow one slot out of the NFILE-way big-sep and put it back, possibly
     under a DIFFERENT authority map -- which is what filealloc needs: its
     scan borrows slot after slot unchanged (M' := M), and the slot it takes
     is given back at [<[i := (1,1)]> M].  Since [fslot γ M k] reads only
     [M !! k], every other slot is untouched by the update. *)
  Lemma ftable_slots_acc (γ : gname) (M : gmap nat (Qp * positive)) (i : nat) :
    (i < NFILE)%nat ->
    ([∗ list] k ∈ seq 0 NFILE, fslot γ M k) -∗
    fslot γ M i ∗
    (∀ M' : gmap nat (Qp * positive),
       ⌜∀ k, k ≠ i -> M' !! k = M !! k⌝ -∗ fslot γ M' i -∗
       [∗ list] k ∈ seq 0 NFILE, fslot γ M' k).
  Proof.
    iIntros (Hi) "H".
    assert (Hlk : seq 0 NFILE !! i = Some i).
    { apply lookup_seq. lia. }
    rewrite (big_sepL_delete (fun _ k => fslot γ M k) (seq 0 NFILE) i i Hlk).
    iDestruct "H" as "[$ Hrest]".
    iIntros (M' HM') "Hi".
    rewrite (big_sepL_delete (fun _ k => fslot γ M' k) (seq 0 NFILE) i i Hlk).
    iFrame "Hi".
    iApply (big_sepL_mono with "Hrest").
    intros idx y Hy. destruct (decide (idx = i)) as [->|Hne]; [done|].
    (* in [seq 0 NFILE] the element IS the index, so [y <> i] *)
    apply lookup_seq in Hy as [-> _].
    unfold fslot. rewrite (HM' _ Hne). done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The algebra's two load-bearing validity facts                       *)
  (* ------------------------------------------------------------------ *)

  (* A reference's fragment against the authority.  The second conjunct is
     THE fact the whole design turns on: the holder of the ONLY reference
     holds the FULL fraction, hence write access -- which is what licenses
     sys_open's unlocked initialization and fileclose's [type = FD_NONE]. *)
  Lemma fref_tok_lookup γ M k q :
    ftable_auth γ M -∗ fref_tok γ k q -∗
    ⌜∃ qt n, M !! k = Some (qt, n) /\ (qt ≤ 1)%Qp /\
       (n = 1%positive -> q = qt) /\ (q = qt -> n = 1%positive) /\
       (n <> 1%positive -> (q < qt)%Qp)⌝.
  Proof.
    rewrite /ftable_auth /fref_tok. iIntros "[Ha _] Hf".
    iDestruct (fref_own_valid_2 with "Ha Hf")
      as %[Hincl Hval]%auth_both_valid_discrete.
    iPureIntro.
    apply singleton_included_l in Hincl as [y [Hy Hle]].
    apply leibniz_equiv in Hy. destruct y as [qt n]. exists qt, n.
    split; [exact Hy|].
    (* the authority's own validity bounds the OUTSTANDING total, which is
       what the [n >= 2] close needs before it may subtract from it. *)
    split.
    { specialize (Hval k). rewrite Hy in Hval.
      destruct Hval as [Hvq _]; simpl in Hvq. by apply frac_valid in Hvq. }
    apply Some_included in Hle as [Heq | Hlt].
    - (* the fragment IS the whole entry: same fraction, count 1 *)
      destruct Heq as [Hq Hn]; cbn in Hq, Hn.
      split; [by intros _|]. split; [by intros _; rewrite -Hn|].
      intros Hne. exfalso. apply Hne. by rewrite -Hn.
    - (* strictly included, so BOTH components strictly grow -- and the
         fraction one is what the [n >= 2] close needs to SUBTRACT. *)
      apply pair_included in Hlt as [Hq Hn]; cbn in Hq, Hn.
      apply frac_included in Hq. apply pos_included in Hn.
      split; [|split].
      + intros Hc. exfalso. rewrite Hc in Hn. lia.
      + intros Hc. exfalso. rewrite Hc in Hq. by apply (irreflexivity Qp.lt qt).
      + by intros _.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The liveness counter's four steps                                   *)
  (* ------------------------------------------------------------------ *)

  (* They mirror the reference count exactly -- the counter IS the count
     column of [M] -- so each one is the corresponding [file_*_step]'s local
     update with the fraction component dropped.  They are separate lemmas
     rather than inlined so that the reason the counter exists (the borrow
     protocol, FileOff.v) stays legible here. *)

  Lemma flive_alloc γ (m : gmap nat positive) k :
    m !! k = None ->
    flive_own γ (● m) ==∗
    flive_own γ (● (<[k := 1%positive]> m)) ∗ flive_tok γ k.
  Proof.
    intros Hm. iIntros "Ha". rewrite /flive_tok.
    iMod (flive_own_update _ _
            (● (<[k := 1%positive]> m) ⋅ ◯ {[k := 1%positive]}) with "Ha") as "H".
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update _ k 1%positive); done. }
    rewrite flive_own_op. by iDestruct "H" as "[$ $]".
  Qed.

  Lemma flive_dup γ (m : gmap nat positive) k (n : positive) :
    m !! k = Some n ->
    flive_own γ (● m) -∗ flive_tok γ k ==∗
    flive_own γ (● (<[k := Pos.succ n]> m)) ∗ flive_tok γ k ∗ flive_tok γ k.
  Proof.
    intros Hm. iIntros "Ha Hf". rewrite /flive_tok.
    iMod (flive_own_update_2 _ _ _ (● (<[k := Pos.succ n]> m))
            (◯ {[k := 2%positive]}) with "Ha Hf") as "[$ Hfrag]".
    { apply auth_update.
      apply (singleton_local_update _ k n 1%positive (Pos.succ n) 2%positive Hm).
      apply local_update_discrete. intros mz Hv Hz.
      split; [done|].
      destruct mz as [nf|]; simpl in Hz |- *.
      - rewrite pos_op_add in Hz. rewrite pos_op_add. rewrite Hz.
        apply pos_succ_1_add.
      - by rewrite Hz. }
    assert (Hsp : ({[k := 2%positive]} : gmap nat positive)
                  = {[k := 1%positive]} ⋅ {[k := 1%positive]}).
    { rewrite singleton_op. reflexivity. }
    rewrite Hsp auth_frag_op flive_own_op.
    by iDestruct "Hfrag" as "[$ $]".
  Qed.

  Lemma flive_close γ (m : gmap nat positive) k (n : positive) :
    m !! k = Some (Pos.succ n) ->
    flive_own γ (● m) -∗ flive_tok γ k ==∗ flive_own γ (● (<[k := n]> m)).
  Proof.
    intros Hm. iIntros "Ha Hf". rewrite /flive_tok.
    iMod (flive_own_update_2' γ (● m) (◯ {[k := 1%positive]})
            (● (<[k := n]> m)) with "Ha Hf") as "$"; [|done].
    apply auth_update_dealloc, gmap_local_update. intros i.
    destruct (decide (i = k)) as [->|Hne]; last first.
    { assert (Hki : k <> i) by auto.
      pose proof (lookup_singleton_ne (M:=gmap nat) k i 1%positive Hki) as Hs.
      pose proof (lookup_insert_ne m k i n Hki) as Hmi.
      apply local_update_discrete. intros mz Hv Hz.
      rewrite Hs in Hz. rewrite Hmi. split; [exact Hv | exact Hz]. }
    pose proof (lookup_singleton (M:=gmap nat) k 1%positive) as Hs.
    pose proof (lookup_insert m k n) as Hmi.
    apply local_update_discrete. intros mz Hv Hz.
    rewrite Hm in Hz, Hv. rewrite Hs in Hz. rewrite Hmi.
    destruct mz as [[nf|]|]; simpl in Hz.
    - apply Some_equiv_inj in Hz. rewrite pos_op_add in Hz.
      assert (Hn' : Pos.succ n = (1 + nf)%positive) by exact Hz.
      assert (Hnf : nf = n) by lia. subst nf.
      split; [done | reflexivity].
    - exfalso. rewrite right_id in Hz. apply Some_equiv_inj in Hz.
      assert (Hn' : Pos.succ n = 1%positive) by exact Hz. lia.
    - exfalso. apply Some_equiv_inj in Hz.
      assert (Hn' : Pos.succ n = 1%positive) by exact Hz. lia.
  Qed.

  Lemma flive_close_last γ (m : gmap nat positive) k :
    m !! k = Some 1%positive ->
    flive_own γ (● m) -∗ flive_tok γ k ==∗ flive_own γ (● (delete k m)).
  Proof.
    intros Hm. iIntros "Ha Hf". rewrite /flive_tok.
    iMod (flive_own_update_2' γ (● m) (◯ {[k := 1%positive]})
            (● (delete k m)) with "Ha Hf") as "$"; [|done].
    apply auth_update_dealloc, gmap_local_update. intros i.
    destruct (decide (i = k)) as [->|Hne]; last first.
    { assert (Hki : k <> i) by auto.
      pose proof (lookup_singleton_ne (M:=gmap nat) k i 1%positive Hki) as Hs.
      pose proof (lookup_delete_ne m k i Hki) as Hmi.
      apply local_update_discrete. intros mz Hv Hz.
      rewrite Hs in Hz. rewrite Hmi. split; [exact Hv | exact Hz]. }
    pose proof (lookup_singleton (M:=gmap nat) k 1%positive) as Hs.
    pose proof (lookup_delete m k) as Hmi.
    apply local_update_discrete. intros mz Hv Hz.
    rewrite Hm in Hz. rewrite Hs in Hz. rewrite Hmi.
    destruct mz as [[nf|]|]; simpl in Hz.
    - exfalso. apply Some_equiv_inj in Hz. rewrite pos_op_add in Hz.
      assert (Hn' : 1%positive = (1 + nf)%positive) by exact Hz. lia.
    - split; done.
    - split; done.
  Qed.

  (* OBLIGATION (b), the ghost half: at the LAST reference the authority
     records ONE unit, so a second one -- the one a stale checked-out state
     would be parking -- cannot exist.  This is what lets the exclusive holder
     of a slot reclaim [f->off] holding NO inode lock. *)
  Lemma flive_excl_last γ (m : gmap nat positive) k :
    m !! k = Some 1%positive ->
    flive_own γ (● m) -∗ flive_tok γ k -∗ flive_tok γ k -∗ False.
  Proof.
    intros Hm. iIntros "Ha H1 H2". rewrite /flive_tok.
    iDestruct (flive_own_valid_2 γ (● m)
                 (◯ {[k := 1%positive]} ⋅ ◯ {[k := 1%positive]})
                 with "Ha [H1 H2]") as %Hv.
    { iApply flive_own_op. iFrame. }
    iPureIntro.
    rewrite -auth_frag_op singleton_op pos_op_add in Hv.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    apply singleton_included_l in Hincl as [y [Hy Hle]].
    rewrite Hm in Hy. apply Some_equiv_inj in Hy.
    assert (Hy' : 1%positive = y) by exact Hy. subst y.
    apply Some_included in Hle as [Heq | Hlt].
    - assert (Hc : (1 + 1)%positive = 1%positive) by exact Heq. lia.
    - apply pos_included in Hlt. lia.
  Qed.

  (* OBLIGATION (b), R-open-1b's form: THE CANCEL, and it is the LAST
     CLOSER'S move.  fileclose's last-reference arm is the only party that
     ever again holds fraction one of the slot INSIDE ftable.lock, so it is
     where the off-borrow cinv is retired and the two cells go back to
     [fslot]'s free arm for the next filealloc.  Cancelling yields the BODY,
     disjunction and all; what resolves the disjunction is the COUNT, exactly
     as [off_acc_excl] resolved it before -- at the last reference the
     authority records ONE unit and the closer holds it, so the parked one
     cannot exist.

     Uniform in [armed], because the closer must cancel BEFORE its ghost step
     (the refutation reads the very entry the step deletes) and the type is
     not tested until much later; an unarmed body has no disjunction to
     refute.  fileclose never READS [off] (gcc emits no such load), so this
     is internal to the lock and [SpecFileclose] does not move. *)
  Lemma off_hold_cancel (E : coPset) (γ γx : gname) (armed : bool)
      (M : gmap nat (Qp * positive)) (k : nat) (qt : Qp) :
    ↑(offN .@ k) ⊆ E ->
    M !! k = Some (qt, 1%positive) ->
    off_hold γ k γx armed 1 -∗ ftable_auth γ M -∗ flive_tok γ k
    ={E}=∗ ftable_auth γ M ∗ flive_tok γ k ∗ off_raw k.
  Proof.
    iIntros (HE HM) "[#Hci Hown] [Ha Hl] Hlv".
    assert (Hml : Mcount M !! k = Some 1%positive)
      by (rewrite Mcount_lookup HM; reflexivity).
    iMod (cinv_cancel with "Hci Hown") as "H"; [exact HE|].
    iMod "H". rewrite /off_content. destruct armed; last first.
    { iModIntro. rewrite /ftable_auth. iFrame "Ha Hl Hlv". iExact "H". }
    iDestruct "H" as (ip) "[Hip Hd]".
    iDestruct "Hd" as "[Hres | [_ Hlv2]]"; last first.
    { iExFalso. iApply (flive_excl_last γ (Mcount M) k Hml with "Hl Hlv Hlv2"). }
    iDestruct "Hres" as (v) "[Hc %Hwf]".
    iModIntro. rewrite /ftable_auth. iFrame "Ha Hl Hlv".
    iExists ip, v. iFrame. done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The three ghost steps, all performed under ftable.lock              *)
  (* ------------------------------------------------------------------ *)

  (* filealloc: [ref = 0] -> [ref = 1].  Allocate the authority entry at
     (1,1) and hand the invariant's WHOLE content fraction out as the
     exclusive reference. *)
  Lemma file_alloc_step γ M k C :
    M !! k = None ->
    ftable_auth γ M -∗ file_fields k 1 C -∗ file_pay γ k 1 C ==∗
    ftable_auth γ (<[k := (1%Qp, 1%positive)]> M) ∗ file_ref γ k 1 C.
  Proof.
    iIntros (HM) "[Ha Hl] Hf Hp".
    rewrite /ftable_auth /fref_tok.
    assert (Hml : Mcount M !! k = None)
      by (rewrite Mcount_lookup HM; reflexivity).
    iMod (flive_alloc γ (Mcount M) k Hml with "Hl") as "[Hl Hlv]".
    iMod (fref_own_update _ _
            (● (<[k := (1%Qp, 1%positive)]> M) ⋅ ◯ {[k := (1%Qp, 1%positive)]})
            with "Ha") as "H".
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update _ k (1%Qp, 1%positive)); [done|].
      split; done. }
    rewrite fref_own_op. iDestruct "H" as "[Ha Hfrag]".
    rewrite Mcount_insert. cbn [snd].
    iModIntro. iFrame "Ha Hl". rewrite /file_ref /fref_tok. iFrame.
  Qed.

  (* filedup: [ref++].  The new reference's fraction comes out of the
     CALLER's -- nothing is conjured, which is exactly why the invariant's
     leftover [file_rest γ k qt] is untouched. *)
  Lemma file_dup_step γ M k q C qt (n : positive) :
    M !! k = Some (qt, n) ->
    ftable_auth γ M -∗ file_ref γ k q C ==∗
    ftable_auth γ (<[k := (qt, Pos.succ n)]> M) ∗
    file_ref γ k (q/2)%Qp C ∗ file_ref γ k (q/2)%Qp C.
  Proof.
    iIntros (HM) "[Ha Hl] (Hf & Hc & Hp & Hlv)".
    rewrite /ftable_auth /fref_tok.
    assert (Hml : Mcount M !! k = Some n)
      by (rewrite Mcount_lookup HM; reflexivity).
    iMod (flive_dup γ (Mcount M) k n Hml with "Hl Hlv") as "(Hl & Hlv1 & Hlv2)".
    rewrite Mcount_insert. cbn [snd].
    iMod (fref_own_update_2 _ _ _ (● (<[k := (qt, Pos.succ n)]> M))
            (◯ {[k := (q, 2%positive)]}) with "Ha Hf") as "[Ha Hfrag]".
    { apply auth_update.
      apply (singleton_local_update _ k (qt, n) (q, 1%positive)
                                      (qt, Pos.succ n) (q, 2%positive) HM).
      apply local_update_discrete. intros mz Hv Hz.
      destruct Hv as [Hvq Hvn]. split; [by split|].
      destruct mz as [[qf nf]|]; destruct Hz as [Hq Hn]; simpl in Hq, Hn.
      - split; simpl; [exact Hq|]. rewrite Hn !pos_op_add. apply pos_succ_1_add.
      - split; simpl; [exact Hq|]. by rewrite Hn. }
    iModIntro. iFrame "Ha Hl".
    (* split the fragment: (q/2,1) ⋅ (q/2,1) = (q,2) *)
    rewrite /file_ref /fref_tok.
    assert (Hsp : ({[k := (q, 2%positive)]} : gmap nat (Qp * positive))
                  = {[k := ((q/2)%Qp, 1%positive)]} ⋅ {[k := ((q/2)%Qp, 1%positive)]}).
    { rewrite singleton_op. f_equal. rewrite -pair_op.
      by rewrite frac_op Qp.div_2. }
    rewrite Hsp auth_frag_op fref_own_op.
    iDestruct "Hfrag" as "[Hfa Hfb]".
    (* and the content fraction, and the payload, likewise *)
    iEval (rewrite -{1}(Qp.div_2 q) file_fields_frac_split) in "Hc".
    iEval (rewrite -{1}(Qp.div_2 q) file_pay_split) in "Hp".
    iDestruct "Hc" as "[Hca Hcb]". iDestruct "Hp" as "[Hpa Hpb]".
    iFrame.
  Qed.

  (* fileclose, [--ref > 0]: the departing reference's fraction has to go
     SOMEWHERE, and it goes back into the authority's outstanding total (and,
     on the points-to side, into [file_rest]).  That is why the frac component
     tracks outstanding fraction rather than being pinned at 1. *)
  Lemma file_close_step γ M k q C qt (n : positive) (qr : Qp) :
    M !! k = Some (qt, Pos.succ n) ->
    (qt - q)%Qp = Some qr ->
    ftable_auth γ M -∗ file_ref γ k q C ==∗
    ftable_auth γ (<[k := (qr, n)]> M) ∗ file_fields k q C ∗
    file_pay γ k q C.
  Proof.
    iIntros (HM Hsub) "[Ha Hl] (Hf & Hc & Hp & Hlv)".
    rewrite /ftable_auth /fref_tok.
    assert (Hml : Mcount M !! k = Some (Pos.succ n))
      by (rewrite Mcount_lookup HM; reflexivity).
    iMod (flive_close γ (Mcount M) k n Hml with "Hl Hlv") as "Hl".
    rewrite Mcount_insert. cbn [snd].
    apply Qp.sub_Some in Hsub.       (* qt = q + qr *)
    iMod (fref_own_update_2' γ (● M) (◯ {[k := (q, 1%positive)]})
            (● (<[k := (qr, n)]> M)) with "Ha Hf") as "Ha"; last first.
    { iModIntro. iFrame. }
    apply auth_update_dealloc, gmap_local_update. intros i.
    destruct (decide (i = k)) as [->|Hne]; last first.
    { (* untouched slot: the fragment is absent on both sides *)
      assert (Hki : k <> i) by auto.
      pose proof (lookup_singleton_ne (M:=gmap nat) k i (q, 1%positive) Hki) as Hs.
      pose proof (lookup_insert_ne M k i (qr, n) Hki) as Hm.
      apply local_update_discrete. intros mz Hv Hz.
      rewrite Hs in Hz. rewrite Hm. split; [exact Hv | exact Hz]. }
    pose proof (lookup_singleton (M:=gmap nat) k (q, 1%positive)) as Hs.
    pose proof (lookup_insert M k (qr, n)) as Hm.
    apply local_update_discrete. intros mz Hv Hz.
    rewrite HM in Hz, Hv. rewrite Hs in Hz. rewrite Hm.
    (* the frame is an [option] of the ENTRY, so three shapes *)
    destruct mz as [[[qf nf]|]|]; simpl in Hz.
    - (* a real frame -- it is exactly what the entry shrinks to *)
      apply Some_equiv_inj in Hz. destruct Hz as [Hq Hn]; simpl in Hq, Hn.
      rewrite pos_op_add in Hn.
      assert (Hn' : Pos.succ n = (1 + nf)%positive) by exact Hn.
      assert (Hnf : nf = n) by lia.
      rewrite frac_op in Hq.
      assert (Hqf : qf = qr).
      { apply (inj (Qp.add q)). by rewrite -Hq -Hsub. }
      subst nf qf. split; last first.
      { by constructor. }
      (* qr ≤ qt ≤ 1 *)
      destruct Hv as [Hvq _]; simpl in Hvq. apply frac_valid in Hvq.
      split; simpl; [|done].
      apply frac_valid. etrans; [|exact Hvq]. rewrite Hsub. apply Qp.le_add_r.
    - (* empty frame: the entry would have to BE (q,1), i.e. Pos.succ n = 1 *)
      exfalso. rewrite right_id in Hz. apply Some_equiv_inj in Hz.
      destruct Hz as [_ Hn]; simpl in Hn.
      assert (Hn' : Pos.succ n = 1%positive) by exact Hn. lia.
    - (* no frame: same contradiction *)
      exfalso. apply Some_equiv_inj in Hz.
      destruct Hz as [_ Hn]; simpl in Hn.
      assert (Hn' : Pos.succ n = 1%positive) by exact Hn. lia.
  Qed.

  (* fileclose, [--ref == 0]: [fref_tok_lookup] forced [q = qt], so the closer
     holds every share that was ever handed out, and the slot leaves the
     authority.  The OUTSTANDING total [qt] is not 1 in general -- every
     earlier close returned its fraction to [file_rest] and shrank it -- so
     what the closer walks away with is [qt], and the rest of the slot is
     still in the invariant.  [file_rest_join] below is where they meet.

     Note the entry can be deleted at any [qt]: it is the COUNT component
     that is exclusive here, since [positiveR] has no unit, so no frame can
     sit beside a fragment recording the last reference. *)
  Lemma file_close_last_ghost γ M k (qt : Qp) :
    M !! k = Some (qt, 1%positive) ->
    ftable_auth γ M -∗ fref_tok γ k qt -∗ flive_tok γ k ==∗
    ftable_auth γ (delete k M).
  Proof.
    iIntros (HM) "[Ha Hl] Hf Hlv".
    rewrite /ftable_auth /fref_tok.
    assert (Hml : Mcount M !! k = Some 1%positive)
      by (rewrite Mcount_lookup HM; reflexivity).
    iMod (flive_close_last γ (Mcount M) k Hml with "Hl Hlv") as "Hl".
    rewrite Mcount_delete.
    iMod (fref_own_update_2' γ (● M) (◯ {[k := (qt, 1%positive)]})
            (● (delete k M)) with "Ha Hf") as "Ha"; last first.
    { iModIntro. iFrame. }
    apply auth_update_dealloc, gmap_local_update. intros i.
    destruct (decide (i = k)) as [->|Hne]; last first.
    { (* untouched slot: the fragment is absent on both sides *)
      assert (Hki : k <> i) by auto.
      pose proof (lookup_singleton_ne (M:=gmap nat) k i (qt, 1%positive) Hki) as Hs.
      pose proof (lookup_delete_ne M k i Hki) as Hm.
      apply local_update_discrete. intros mz Hv Hz.
      rewrite Hs in Hz. rewrite Hm. split; [exact Hv | exact Hz]. }
    pose proof (lookup_singleton (M:=gmap nat) k (qt, 1%positive)) as Hs.
    pose proof (lookup_delete M k) as Hm.
    apply local_update_discrete. intros mz Hv Hz.
    rewrite HM in Hz. rewrite Hs in Hz. rewrite Hm.
    destruct mz as [[[qf nf]|]|]; simpl in Hz.
    - (* a frame at this key would make the count 1 + nf, and it is 1 *)
      exfalso. apply Some_equiv_inj in Hz. destruct Hz as [_ Hn]; simpl in Hn.
      rewrite pos_op_add in Hn.
      assert (Hn' : 1%positive = (1 + nf)%positive) by exact Hn. lia.
    - split; done.
    - split; done.
  Qed.

  (* the same step with the reference's points-to half framed through -- the
     shape most callers want.  fileclose's own last-reference arm uses the
     GHOST half above instead, because it has to cancel the off-borrow cinv
     first (the refutation reads the entry this step deletes) and by then it
     holds the joined fraction rather than [qt]. *)
  Lemma file_close_last_step γ M k C (qt : Qp) :
    M !! k = Some (qt, 1%positive) ->
    ftable_auth γ M -∗ file_ref γ k qt C ==∗
    ftable_auth γ (delete k M) ∗ file_fields k qt C ∗
    file_pay γ k qt C.
  Proof.
    iIntros (HM) "Hauth (Hf & Hc & Hp & Hlv)".
    iMod (file_close_last_ghost γ M k qt HM with "Hauth Hf Hlv") as "$".
    iModIntro. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  [file_rest]: the fraction the invariant still holds                 *)
  (* ------------------------------------------------------------------ *)

  (* THE LAST CLOSER'S JOIN.  Its own share plus whatever the invariant kept
     is the whole slot -- content cells, payload names and payload alike.
     This is what puts a WHOLE pipe end in fileclose's hands, and hence what
     licenses [pipeclose(ff.pipe, ff.writable)]. *)
  Lemma file_rest_join γ k (qt : Qp) C :
    (qt ≤ 1)%Qp ->
    file_fields k qt C -∗ file_pay γ k qt C -∗ file_rest γ k qt -∗
    file_fields k 1 C ∗ file_pay γ k 1 C.
  Proof.
    intros Hle. rewrite /file_rest.
    destruct (1 - qt)%Qp as [q'|] eqn:Et.
    - apply Qp.sub_Some in Et.        (* 1 = qt + q' *)
      iIntros "Hf Hp (%C' & Hf' & Hp')".
      iDestruct (file_fields_agree with "Hf Hf'") as %<-.
      rewrite Et file_fields_frac_split file_pay_split. iFrame.
    - (* nothing left over: [qt] is already the whole of it *)
      apply Qp.sub_None in Et.
      assert (qt = 1%Qp) as -> by (apply (anti_symm (⊑@{Qp})); done).
      iIntros "$ $ _". done.
  Qed.

  (* ... and the DEPARTING reference's, when it is not the last: its fraction
     goes back into the leftover, which is why [fileUR]'s frac component
     tracks OUTSTANDING fraction rather than being pinned at 1. *)
  Lemma file_rest_absorb γ k (qt q qr : Qp) C :
    (qt - q)%Qp = Some qr -> (qt ≤ 1)%Qp ->
    file_rest γ k qt -∗ file_fields k q C -∗ file_pay γ k q C -∗
    file_rest γ k qr.
  Proof.
    intros Hsub Hle. apply Qp.sub_Some in Hsub.   (* qt = q + qr *)
    rewrite /file_rest.
    destruct (1 - qt)%Qp as [s|] eqn:Et.
    - apply Qp.sub_Some in Et.                     (* 1 = qt + s *)
      assert (Hr : (1 - qr)%Qp = Some (q + s)%Qp).
      { apply Qp.sub_Some. rewrite Et Hsub.
        by rewrite (Qp.add_comm q qr) -Qp.add_assoc. }
      rewrite Hr.
      iIntros "(%C' & Hf' & Hp') Hf Hp".
      iDestruct (file_fields_agree with "Hf Hf'") as %<-.
      iExists C. rewrite file_fields_frac_split file_pay_split. iFrame.
    - apply Qp.sub_None in Et.
      assert (qt = 1%Qp) as Hqt by (apply (anti_symm (⊑@{Qp})); done).
      assert (Hr : (1 - qr)%Qp = Some q).
      { apply Qp.sub_Some. rewrite -Hqt Hsub. apply Qp.add_comm. }
      rewrite Hr. iIntros "_ Hf Hp". iExists C. iFrame.
  Qed.

End FileInv.

(* ------------------------------------------------------------------ *)
(*  Boot: minting the table's ghost                                     *)
(* ------------------------------------------------------------------ *)

(* The authority starts empty -- every slot free -- and every slot's names
   ghost exists from the start, held at fraction 1 by the free-slot arm of
   [fslot] exactly as its content cells are.  Nothing is ever allocated or
   freed per slot afterwards: a slot's names are simply OVERWRITTEN by
   whoever holds it exclusively ([fpay_tok_update]), which is what lets
   pipealloc publish a payload with no lock in hand.

   Nothing calls this yet -- the ftable lock is not wired at boot (fileinit
   is proven, but [ftable_res] is still a premise everywhere).  It is here
   because a resource nobody can MINT is a design hole that only surfaces
   when the wiring is written. *)
Definition fpay_v0 : prodR fracR (agreeR (leibnizO fpnames)) :=
  (1%Qp, to_agree (inhabitant : leibnizO fpnames)).

Fixpoint fpay_map0 (n : nat) : fpayUR :=
  match n with
  | O => ∅
  | S k => <[k := fpay_v0]> (fpay_map0 k)
  end.

Lemma fpay_map0_none (n i : nat) : (n <= i)%nat -> fpay_map0 n !! i = None.
Proof.
  revert i. induction n as [|n IH]; intros i Hi; [done|].
  cbn [fpay_map0]. rewrite lookup_insert_ne; [apply IH; lia | lia].
Qed.

Lemma fpay_map0_valid (n : nat) : ✓ (fpay_map0 n).
Proof.
  induction n as [|n IH];
    [cbn [fpay_map0]; intros i; rewrite lookup_empty; done|].
  cbn [fpay_map0]. apply insert_valid; [|exact IH].
  split; done.
Qed.

Section FileGhostAlloc.
  Context `{!riscvGS Σ, !xv6G Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.

  Lemma fpay_map0_split (γ : gname) (n : nat) :
    own γ ((ε, (fpay_map0 n, ε)) : fileUR) ⊢
    [∗ list] k ∈ seq 0 n, own γ ((ε, ({[ k := fpay_v0 ]}, ε)) : fileUR).
  Proof.
    induction n as [|n IH]; [by iIntros "_"|].
    rewrite seq_S big_sepL_app. iIntros "H". cbn [fpay_map0].
    rewrite (insert_singleton_op (fpay_map0 n) n fpay_v0);
      [|apply fpay_map0_none; lia].
    assert (Hsp : ((ε, ({[n := fpay_v0]} ⋅ fpay_map0 n, ε)) : fileUR)
                  ≡ ((ε, ({[n := fpay_v0]}, ε)) : fileUR)
                    ⋅ ((ε, (fpay_map0 n, ε)) : fileUR)).
    { rewrite -!pair_op !left_id. reflexivity. }
    rewrite Hsp own_op. iDestruct "H" as "[Hk Hm]".
    iSplitL "Hm"; [by iApply IH | by iFrame].
  Qed.

  Lemma ftable_ghosts_alloc :
    ⊢ |==> ∃ γ, ftable_auth γ ∅ ∗
                [∗ list] k ∈ seq 0 NFILE, ∃ pn, fpay_tok γ k 1 pn.
  Proof.
    iMod (own_alloc (((● (∅ : gmap nat (Qp * positive))),
                      (fpay_map0 NFILE, ● (∅ : gmap nat positive)))
                     : fileUR)) as (γ) "H".
    { split; cbn [fst snd].
      - apply auth_auth_valid. intros i. rewrite lookup_empty. done.
      - split; cbn [fst snd].
        + apply fpay_map0_valid.
        + apply auth_auth_valid. intros i. rewrite lookup_empty. done. }
    iModIntro. iExists γ.
    assert (Hsp : ((● (∅ : gmap nat (Qp * positive)),
                    (fpay_map0 NFILE, ● (∅ : gmap nat positive))) : fileUR)
                  ≡ ((● (∅ : gmap nat (Qp * positive)),
                      (ε, ● (∅ : gmap nat positive))) : fileUR)
                    ⋅ ((ε, (fpay_map0 NFILE, ε)) : fileUR)).
    { rewrite -!pair_op !right_id !left_id. reflexivity. }
    rewrite Hsp own_op. iDestruct "H" as "[Ha Hm]".
    iSplitL "Ha".
    { rewrite /ftable_auth /fref_own /flive_own /Mcount fmap_empty.
      rewrite -own_op.
      assert (He : (((● (∅ : gmap nat (Qp * positive)), ε) : fileUR)
                    ⋅ (ε, (ε, ● (∅ : gmap nat positive))))
                   ≡ ((● (∅ : gmap nat (Qp * positive)),
                       (ε, ● (∅ : gmap nat positive))) : fileUR)).
      { rewrite -!pair_op !left_id !right_id. reflexivity. }
      rewrite He. iExact "Ha". }
    iDestruct (fpay_map0_split with "Hm") as "Hm".
    iApply (big_sepL_mono with "Hm"). intros ? k ?. iIntros "H".
    iExists inhabitant. iExact "H".
  Qed.

  (* ================================================================== *)
  (* THE TABLE, MINTED: [NFILE] raw entries become the lock's resource.   *)
  (*                                                                    *)
  (* This is the other half of [ftable_ghosts_alloc] -- the physical one  *)
  (* -- and together they are what [main] runs the moment fileinit hands  *)
  (* back the zeroed lock word.  Everything comes from the image except   *)
  (* three ghost rows, and each of the three is exactly one thing:        *)
  (*                                                                    *)
  (*   [fd_slots_auth]  the fd-slot AUTHORITY.  [ftable_res] holds it     *)
  (*                    because the table is where the conservation law   *)
  (*                    is checked -- one unit per outstanding reference. *)
  (*                    It is minted once, at the boot fan-out, and was   *)
  (*                    DROPPED there before this lemma existed.          *)
  (*   [iref_slots NFILE]  one whole unit per FREE slot.  A free slot's   *)
  (*                    payload is untyped, and an untyped payload IS its  *)
  (*                    iref unit ([file_core_none]); sys_open spends it   *)
  (*                    retyping to FD_INODE and fileclose puts it back.   *)
  (*                    These are the [NFILE] units [IREFSLOTS] is sized   *)
  (*                    for -- NOT the boot chain's two ([IREFBOOT]).      *)
  (*   [ftable_ghosts_alloc]  the authority at the EMPTY map, plus one     *)
  (*                    names ghost per slot.                             *)
  (*                                                                    *)
  (* THE PER-SLOT fupd IS THE OFF-BORROW cinv, one per entry: a slot       *)
  (* carries an off-invariant for its whole life and it is UNARMED while   *)
  (* the slot is untyped, so what goes in is the two raw cells and there   *)
  (* is no disjunction to establish ([off_hold]'s header).  Its name then  *)
  (* has to be recorded in the slot's [fpnames], which is the one thing    *)
  (* [ftable_ghosts_alloc] could not know: it hands out [inhabitant] and   *)
  (* this lemma overwrites the [fp_ocv] field with [fpay_tok_update].      *)
  (* ================================================================== *)
  Lemma ftable_res_boot `{XI : CurCtx} (E : coPset) :
    ([∗ list] k ∈ seq 0 NFILE, fentry_raw k) -∗
    fd_slots_auth -∗
    iref_slots NFILE ={E}=∗
    ∃ γ : gname, ftable_res γ.
  Proof.
    iIntros "Hraw Hfda Hir".
    iMod ftable_ghosts_alloc as (γ) "[Hauth Htoks]".
    iDestruct (iref_slots_to_any (seq 0 NFILE) with "[Hir]") as "Hunits".
    { rewrite length_seq. iExact "Hir". }
    (* the three families, zipped into one so the per-slot work is a single
       [big_sepL_mono] under [big_sepL_fupd] rather than three walks. *)
    iAssert ([∗ list] k ∈ seq 0 NFILE,
               (fentry_raw k ∗ (∃ pn, fpay_tok γ k 1 pn) ∗ iref_slot))%I
      with "[Hraw Htoks Hunits]" as "Hall".
    { rewrite !big_sepL_sep. iFrame "Hraw Htoks Hunits". }
    iAssert (|={E}=> [∗ list] k ∈ seq 0 NFILE, fslot γ ∅ k)%I
      with "[Hall]" as ">Hslots".
    { iApply big_sepL_fupd. iApply (big_sepL_mono with "Hall").
      intros i k _. iIntros "(Hraw & (%pn & Htok) & Hu)".
      rewrite /fentry_raw.
      iDestruct "Hraw" as "(Hty & Href & (%r & Hrd) & (%w & Hwr) &
                            (%pp & Hpp) & (%ip & Hip) & Hoff & (%mj & Hmj))".
      (* [f->ip] in half: the reference's half and the invariant's. *)
      iDestruct (bi.equiv_entails_1_1 _ _
                   (ctx_word_pointsto_frac_split _ (a_fip k) (1/2) (1/2) ip)
                   with "[Hip]") as "[Hip1 Hip2]".
      { iEval (rewrite Qp.div_2). iExact "Hip". }
      iMod (off_hold_alloc E γ k false with "[Hip2 Hoff]") as (γx) "Hoffhold".
      { rewrite /off_raw. iExists ip, (mword_of_int 0 : mword 32).
        iFrame "Hip2 Hoff". iPureIntro. exact off_wf_zero. }
      iMod (fpay_tok_update γ k pn
              (MkFPNames (fp_lock pn) (fp_pipe pn) (fp_icv pn) (fp_iq pn)
                 (fp_ig pn) γx) with "Htok") as "Htok".
      iModIntro.
      rewrite /fslot lookup_empty.
      iSplitL "Href"; [iExact "Href"|].
      iExists (MkFContent FD_NONE r w pp ip mj).
      iSplitR; [iPureIntro; reflexivity|].
      iSplitL "Hty Hrd Hwr Hpp Hip1 Hmj".
      { rewrite /file_fields.
        cbn [fc_type fc_readable fc_writable fc_pipe fc_ip fc_major].
        iFrame "Hty Hrd Hwr Hpp Hmj". iExact "Hip1". }
      rewrite /file_pay /file_payload.
      iExists (MkFPNames (fp_lock pn) (fp_pipe pn) (fp_icv pn) (fp_iq pn)
                 (fp_ig pn) γx).
      iSplitL "Htok"; [iExact "Htok"|].
      iSplitL "Hu".
      { rewrite (file_core_none 1 _ (MkFContent FD_NONE r w pp ip mj) eq_refl).
        rewrite -iref_slot_frac. iExact "Hu". }
      rewrite (file_armed_none (MkFContent FD_NONE r w pp ip mj) eq_refl).
      cbn [fp_ocv]. iExact "Hoffhold". }
    iModIntro. iExists γ. rewrite /ftable_res.
    iExists ∅. iFrame "Hauth Hfda".
    iSplitR.
    { iPureIntro. intros k Hk. rewrite lookup_empty in Hk.
      by destruct Hk as [? ?]. }
    iExact "Hslots".
  Qed.

End FileGhostAlloc.
