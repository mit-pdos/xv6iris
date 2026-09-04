(* FileOffProtocol.v -- THE LIFE OF [f->off], AS A CHAIN OF GHOST LEMMAS WITH
   NO PROGRAM (tso-cutover r25 day one; plan §9 items 24 R5, 25, 27).

   Rule 0 checks that a statement is well-typed, not that it is satisfiable
   or final.  This file is the mechanical form of the two day-one checklist
   lines (per-arm producers; every self-absorbed deposit names the acquire
   that pays it): the cell's lifecycle over the FINAL shapes, one lemma per
   step, each lemma's premises exactly the previous one's conclusions.  A
   double-claimed cell is an unprovable filealloc step, a false split an
   unprovable dup step, a floorless absorb an unprovable checkout.  Every
   proof here is a SKELETON until lane (ii); the gate is that the chain is
   STATED and compiles.

   THE CHAIN (item 24's "life of the cell"):
     boot        the free row holds the word at the free tier          [proto_boot_row]
     filealloc   the opener takes [file_pay] at FD_NONE, the word free  [proto_filealloc]
                 inside; NO box, NO birth                                 [proto_open_slot]
     publish     [f->off = 0] over the free word re-mints the cell at   [proto_store]
                 the storer's context; THEN the box is born, the share
                 minted at mass 1, the L2 row inserted                    [proto_publish]
     dup         a pure split of the share by fraction                  [proto_dup]
     read        checkout under ip->lock: [Kt] by R1 at the acquire     [proto_read_checkout]
                 presenting the share's llb, [Kp] from the row's floor;
                 park after the read                                      [proto_read_park]
     close       non-last: a pure join                                  [proto_close_join]
                 last: the free-tier withdraw, then the retype to FD_NONE [proto_last_close]
     realloc     filealloc again on the same slot                       [proto_realloc]
     fork        the parent dups, the child reads at ITS context        [proto_fork_child_read]
   Every absorb has an acquire in front of it: the creator deposits at the
   birth and never absorbs; a reader absorbs after its ilock acquire; the
   closer never absorbs. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import auth gmap ufrac gset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_var invariants.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto.
Require Import TsoGhost TsoCtx CtxBox.   (* [llb loglen_name], [ufrac] stamps *)
Require Import MemClaim.   (* [wordw_free], [wordw_pointsto] -- the store's two faces *)
Require Import FdSlots IrefSlots FileInvDefs FileInv OffBox.   (* [irefslotG] must be IMPORTED, or the binder below silently generalises it *)
Require Import IcacheRef.   (* [NINODE], [ientry] *)
Require Import Xv6G.
Local Open Scope Z_scope.

(* PROTOCOL INVARIANT -- ONE OFF STEP PER HOLD (plan §9 item 36, pre-empt 2).
   Under one ip->lock hold a holder checks its fd's off box out at most once:
   the checkout takes the box's row FOLDED (its floor is the [Kp]) and leaves
   the inode's other rows in DEP form; after the park the parker holds no
   floor at the new stamp, so the rows go back to iunlock in dep form and are
   re-floored only by the `_in` release (R2).  A second checkout in the same
   hold would have no [Kp].  fileread and filewrite do exactly one per hold
   (filewrite re-locks per chunk); sys_open's birth inserts at tp 0 and needs
   no floor. *)

Section FileOffProtocol.
  Context `{!riscvGS Σ, !xv6G Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{XI : CurCtx} `{CID : CpuId}.

  (* ---- boot: the free row holds the word at the free tier ---- *)
  Lemma proto_boot_row (γ : gname) (M : gmap nat (Qp * positive)) (k : nat) :
    M !! k = None ->
    fslot γ M k -∗
    a_fref k ↦₄ (mword_of_int 0 : mword 32) ∗
    ∃ C pn, ⌜fc_type C = FD_NONE⌝ ∗ file_fields k 1 C ∗
            fpay_tok γ k 1 pn ∗ file_core_noff 1 pn C ∗ off_free k 1.
  Proof.
    intros HM. rewrite /fslot HM.
    iIntros "[Href (%C & %Hty & Hflds & Hpay)]". iFrame "Href".
    iDestruct "Hpay" as (pn) "[Hpn Hcore]". rewrite /file_core.
    iDestruct "Hcore" as "[Hnoff Hoff]". rewrite (file_core_off_none k 1 pn C Hty).
    iExists C, pn. iFrame "Hflds Hpn Hnoff Hoff". iPureIntro. exact Hty.
  Qed.

  (* ---- filealloc: the ghost step is main's, pure ---- *)
  Lemma proto_filealloc (γ : gname) (M : gmap nat (Qp * positive)) (k : nat) (C : fcontent) :
    M !! k = None -> fc_type C = FD_NONE ->
    ftable_auth γ M -∗ file_fields k 1 C -∗ file_pay γ k 1 C ==∗
    ftable_auth γ (<[k := (1%Qp, 1%positive)]> M) ∗ file_ref γ k 1 FdClosed.
  Proof. intros HM Hty. exact (file_alloc_step γ M k C HM Hty). Qed.

  (* ---- the opener's slot: the word comes out FREE ---- *)
  Lemma proto_open_slot (E : coPset) (γ : gname) (k : nat) :
    file_ref γ k 1 FdClosed ={E}=∗
    ∃ (C : fcontent) (pn : fpnames),
      ⌜fc_type C = FD_NONE⌝ ∗
      fref_tok γ k 1 ∗ flive_tok k ∗ fpay_tok γ k 1 pn ∗
      file_fields k 1 C ∗ file_core_noff 1 pn C ∗ off_free k 1.
  Proof.
    iIntros "(%Cf & Href & Hflds & (%pn & %Hok & Hnames & Hcore) & Hlive)".
    cbn in Hok. set (Ht := Hok : fc_type Cf = FD_NONE).
    rewrite /file_core. iDestruct "Hcore" as "[Hnoff Hoff]".
    rewrite (file_core_off_none k 1 pn Cf Ht).
    iModIntro. iExists Cf, pn. iFrame "Href Hlive Hnames Hflds Hnoff Hoff".
    iPureIntro. exact Ht.
  Qed.

  (* ---- the store: the free word IS the store leaf's premise, and the
          leaf's result IS the resident cell at the storer's context ---- *)
  Lemma proto_store_free (k : nat) :
    off_free k 1 ⊣⊢ wordw_free 4 (a_foff k).
  Proof.
    rewrite /off_free /wordw_free. change (Z.to_nat 4) with 4%nat. reflexivity.
  Qed.
  Lemma proto_store_remint (k : nat) :
    wordw_pointsto 4 (a_foff k) (DfracOwn 1) (mword_of_int 0 : mword 32) ⊢ off_resident k.
  Proof.
    iIntros "H". rewrite /off_resident. iExists (mword_of_int 0).
    iSplitL "H".
    { rewrite /wordw_pointsto TsoCtx.ctx_word4_pointsto_unfold.
      change (Z.to_nat 4) with 4%nat. iExact "H". }
    iPureIntro. exact off_wf_zero.
  Qed.

  (* ---- the publish: birth on the re-minted cell, share at mass 1, the L2
          row into inode [i]'s set; the creator deposits and never absorbs ---- *)
  Lemma proto_publish (E : coPset) (i k : nat) (C : fcontent) :
    ↑(offBoxN .@ k) ⊆ E -> (i < NINODE)%nat -> fc_ip C = ientry i -> fc_type C = FD_INODE ->
    own_context cur_ctx -∗ off_resident k -∗ off_rows off_cfg i cur_ctx ={E}=∗
    own_context cur_ctx ∗ off_rows off_cfg i cur_ctx ∗
    ∃ γb : box_names, off_fd k 1 γb C.
  Proof.
    iIntros (HE Hi Hip Hty) "Hctx Hres Hrows".
    iMod (own_alloc (● (∅ : gmap (nat * nat) ufrac))) as (γs) "Hst".
    { apply auth_auth_valid. exact (ucmra_unit_valid (A := gmapUR (nat * nat) ufracR)). }
    iMod (ghost_var_alloc (ghost_varG0 := kalloc_count_inG) 0%nat) as (γc) "Hc".
    iMod (ghost_var_alloc (inhabitant : slot_reg nat unit)) as (γd) "Hd".
    iMod (ghost_var_alloc (inhabitant : l2_reg nat)) as (γp) "Hp".
    set (γb := BoxNames γs γc γd γp).
    iMod (off_publish_park off_cfg i k γb cur_ctx E HE
            with "Hst Hc Hd Hp Hctx Hres Hrows")
      as "(Hctx & #Hbox & %T0 & %T & Hregd & Hllb & Hcnt & Href & #Hmem & Hrows)".
    iModIntro. iFrame "Hctx Hrows". iExists γb.
    rewrite /off_fd. iExists i, T0.
    iSplitR; [iPureIntro; exact Hip|]. iSplitR; [iPureIntro; exact Hi|].
    iFrame "Hbox Hmem Hregd Hcnt".
    rewrite /off_ref_stamps. iExists {[ (k, T) := 1%Qp ]}.
    iSplitR; [iPureIntro; apply CtxBox.qsum_singleton|]. iExact "Href".
  Qed.

  (* ---- dup: a pure split of the share by fraction ---- *)
  Lemma proto_dup (k : nat) (q1 q2 : Qp) (γb : box_names) (C : fcontent) :
    off_fd k (q1 + q2) γb C ⊣⊢ off_fd k q1 γb C ∗ off_fd k q2 γb C.
  Proof. apply off_fd_split. Qed.

  (* ---- read, step 0: name the share's stamps fragment and present its
          llb at the ilock acquire; R1 returns a floor at least that high
          (reviewer 2, item 31: the tie that makes the checkout provable) ---- *)
  Lemma proto_read_llb (k : nat) (q : Qp) (γb : box_names) (C : fcontent) :
    off_fd k q γb C -∗
    ∃ m : gmap (nat * nat) ufrac, off_fd_at k q γb C m ∗ llb loglen_name (max_stamp m).
  Proof.
    rewrite /off_fd /off_fd_at /off_ref_stamps.
    iIntros "(%i & %T0 & %Hip & %Hi & #Hbox & #Hmem & Hd & Hc & (%m & %Hq & Href))".
    rewrite /CtxBox.reference. iDestruct "Href" as "(%Hne & %Hk & Hfrag & #Hllb)".
    iExists m. iSplitL "Hd Hc Hfrag"; [| iExact "Hllb"].
    iExists i, T0.
    iSplitR; [iPureIntro; exact Hip|]. iSplitR; [iPureIntro; exact Hi|].
    iFrame "Hbox Hmem Hd Hc". iSplitR; [iPureIntro; exact Hq|].
    iSplitR; [iPureIntro; exact Hne|]. iSplitR; [iPureIntro; exact Hk|].
    iFrame "Hfrag". iExact "Hllb".
  Qed.

  (* ---- read: checkout under ip->lock.  [Kt] is R1's floor at the ilock
          acquire, at least the share's llb ([max_stamp m ≤ Kt]); [Kp] is the
          row's transported floor inside off_rows.  THE ONE ABSORB, after the
          acquire. ---- *)
  Lemma proto_read_checkout (E : coPset) (i k : nat) (q : Qp) (γb : box_names) (C : fcontent)
      (m : gmap (nat * nat) ufrac) (Kt : nat) (ξ : CtxId) :
    ↑(offBoxN .@ k) ⊆ E -> fc_ip C = ientry i -> (i < NINODE)%nat ->
    (max_stamp m ≤ Kt)%nat ->
    own_context ξ -∗ ctx_floor ξ Kt -∗
    off_fd_at k q γb C m -∗
    off_rows off_cfg i ξ ={E}=∗
    own_context ξ ∗ off_resident (XI := ξ) k ∗
    off_box k γb ∗ off_member off_cfg i γb ∗
    ∃ T0 : nat,
      CtxBox.l2_hold (X := unit) γb k m ∗
      ghost_var (bx_slotd γb) (q / 2) (SlotReg T0 false k None : slot_reg nat unit) ∗
      ghost_var (ghost_varG0 := kalloc_count_inG) (bx_cnt γb) (q / 2) 1%nat ∗
      (∃ T : nat, off_rows_dep_but off_cfg i γb T).
  Proof.
    iIntros (HE Hip Hi HKt) "Hctx #Hflt Hat Hrows".
    rewrite /off_fd_at.
    iDestruct "Hat" as (i' T0) "(%Hip' & %Hi' & #Hbox & #Hmem & Hd & Hc & %Hq & Href)".
    assert (i' = i) as ->.
    { apply (ientry_inj i' i); [lia | lia | congruence]. }
    (* the box's own L2 row, out of the inode's rows: its floor is the [Kp] *)
    iDestruct (off_rows_take_dep off_cfg i γb ξ with "Hmem Hrows") as "[(%s & Hrow) Hback]".
    rewrite /off_l2_row /CtxBox.l2_row.
    iDestruct "Hrow" as "[(Hrp & %Hh & #Hflp) #Hllbs]".
    iMod (off_read_checkout off_cfg i k γb ξ m Kt (lr_tp s) E HE HKt
            with "Hbox Hctx Hflt Hflp Hmem Href [Hrp]") as "(Hctx & Hres & Hhold)".
    { iExists s. iFrame "Hrp". iPureIntro. split; [exact Hh | lia]. }
    iModIntro. iFrame "Hctx Hres Hbox Hmem". iExists T0. iFrame "Hhold Hd Hc".
    iExact "Hback".
  Qed.

  (* ---- read: park after the read; the row goes back into the set at the
          fresh stamp ---- *)
  Lemma proto_read_park (E : coPset) (i k : nat) (q : Qp) (γb : box_names) (C : fcontent)
      (m : gmap (nat * nat) ufrac) (T0 Tr : nat) (ξ : CtxId) :
    ↑(offBoxN .@ k) ⊆ E -> fc_ip C = ientry i -> (i < NINODE)%nat ->
    qsum m = Qp_to_Qc q ->
    own_context ξ -∗ off_resident (XI := ξ) k -∗
    CtxBox.l2_hold (X := unit) γb k m -∗
    ghost_var (bx_slotd γb) (q / 2) (SlotReg T0 false k None : slot_reg nat unit) -∗
    ghost_var (ghost_varG0 := kalloc_count_inG) (bx_cnt γb) (q / 2) 1%nat -∗
    off_box k γb -∗ off_member off_cfg i γb -∗
    off_rows_dep_but off_cfg i γb Tr ={E}=∗
    own_context ξ ∗ off_fd k q γb C ∗
    ∃ T' : nat, off_rows_dep off_cfg i T'.
  Proof.
    iIntros (HE Hip Hi Hq) "Hctx Hres Hhold Hd Hc #Hbox #Hmem Hrest".
    iMod (off_read_park k γb ξ m E HE with "Hbox Hctx Hres Hhold")
      as "(Hctx & %T' & %q' & %Hq' & Hrp & Href & #Hllb)".
    iModIntro. iFrame "Hctx". iSplitL "Hd Hc Href".
    { rewrite /off_fd. iExists i, T0. iFrame "Hbox Hmem Hd Hc".
      iSplitR; [iPureIntro; exact Hip|]. iSplitR; [iPureIntro; exact Hi|].
      rewrite /off_ref_stamps. iExists {[ (k, T') := q' ]}. iFrame "Href".
      iPureIntro. rewrite CtxBox.qsum_singleton Hq'. exact Hq. }
    (* the parked row goes back into the dep set at the joined bound; no
       floor is needed (item 36) -- the `_in` release folds *)
    iExists (Nat.max Tr T').
    iApply (off_rows_dep_insert off_cfg i γb Tr (L2Reg T' None) eq_refl with "Hrest Hrp Hllb").
  Qed.

  (* ---- close, non-last: a pure join ---- *)
  Lemma proto_close_join (k : nat) (q1 q2 : Qp) (γb : box_names) (C : fcontent) :
    off_fd k q1 γb C ∗ off_fd k q2 γb C ⊢ off_fd k (q1 + q2) γb C.
  Proof. rewrite (off_fd_split k q1 q2). done. Qed.

  (* ---- close, last: the whole share in hand; the free-tier withdraw; the
          retype puts the free word into the FD_NONE payload ---- *)
  Lemma proto_last_close (E : coPset) (k : nat) (γb : box_names) (C : fcontent) :
    ↑(offBoxN .@ k) ⊆ E ->
    off_fd k 1 γb C ={E}=∗ off_free k 1.
  Proof.
    iIntros (HE) "Hfd". rewrite /off_fd.
    iDestruct "Hfd" as (i T0) "(%Hip & %Hi & Hbox & _ & Hregd & Hcnt & Hst)".
    rewrite /off_ref_stamps. iDestruct "Hst" as (m) "[%Hq Href]".
    iMod (off_last_close k _ T0 m E HE Hq with "Hbox Hregd Hcnt Href") as "[_ Hfree]".
    iModIntro. rewrite /off_free. iFrame "Hfree". iPureIntro. apply a_foff_aligned.
  Qed.
  Lemma proto_retype_none (k : nat) (pn : fpnames) (C' : fcontent) :
    fc_type C' = FD_NONE ->
    off_free k 1 ⊢ file_core_off k 1 pn C'.
  Proof. intros Ht. by rewrite (file_core_off_none k 1 pn C' Ht). Qed.

  (* ---- realloc: the same slot, freed, is allocated again -- the row's word
          is the free one the last close left ---- *)
  Lemma proto_realloc (γ : gname) (M : gmap nat (Qp * positive)) (k : nat) (C : fcontent) :
    M !! k = None -> fc_type C = FD_NONE ->
    ftable_auth γ M -∗ file_fields k 1 C -∗ file_pay γ k 1 C ==∗
    ftable_auth γ (<[k := (1%Qp, 1%positive)]> M) ∗ file_ref γ k 1 FdClosed.
  Proof. intros HM Hty. exact (file_alloc_step γ M k C HM Hty). Qed.

  (* ---- fork: the parent dups (a pure split) and KEEPS one half; the child
          reads at ITS context ξ' with the other: the share is context-free,
          so no morph is needed; the child runs [proto_read_llb] on its half,
          presents the llb at its ilock acquire ([max_stamp m ≤ Kt] by R1),
          and its [Kp] is the row's floor at ξ'.  Both halves are returned
          (reviewer 1, item 29); the read is [proto_read_checkout] at ξ' over
          one of them (reviewer 2, item 31: at the named fragment). ---- *)
  Lemma proto_fork_child_read (E : coPset) (i k : nat) (q : Qp) (γb : box_names) (C : fcontent)
      (ξ' : CtxId) :
    ↑(offBoxN .@ k) ⊆ E -> fc_ip C = ientry i -> (i < NINODE)%nat ->
    off_fd k q γb C -∗
    off_fd k (q / 2) γb C ∗ off_fd k (q / 2) γb C ∗
    □ (∀ (m : gmap (nat * nat) ufrac) (Kt : nat),
         ⌜(max_stamp m ≤ Kt)%nat⌝ -∗
         own_context ξ' -∗ ctx_floor ξ' Kt -∗ off_fd_at k (q / 2) γb C m -∗ off_rows off_cfg i ξ' ={E}=∗
         own_context ξ' ∗ off_resident (XI := ξ') k ∗
         off_box k γb ∗ off_member off_cfg i γb ∗
         ∃ T0 : nat,
           CtxBox.l2_hold (X := unit) γb k m ∗
           ghost_var (bx_slotd γb) (q / 2 / 2) (SlotReg T0 false k None : slot_reg nat unit) ∗
           ghost_var (ghost_varG0 := kalloc_count_inG) (bx_cnt γb) (q / 2 / 2) 1%nat ∗
           (∃ T : nat, off_rows_dep_but off_cfg i γb T)).
  Proof.
    iIntros (HE Hip Hi) "Hfd".
    rewrite -{1}(Qp.div_2 q) off_fd_split. iDestruct "Hfd" as "[$ $]".
    iModIntro. iIntros (m Kt HKt) "Hctx Hfl Hat Hrows".
    iApply (proto_read_checkout E i k (q / 2) γb C m Kt ξ' HE Hip Hi HKt
              with "Hctx Hfl Hat Hrows").
  Qed.

  (* ---- the other arms of [file_core_off], named (reviewer 2, optional
          links): pipe and device keep the free word through the retype; the
          fdalloc-failed close at FD_NONE is the retype followed by the free
          row (there is no box to abandon). ---- *)
  Lemma proto_retype_other (k : nat) (q : Qp) (pn : fpnames) (C : fcontent) :
    fc_type C = FD_PIPE \/ fc_type C = FD_DEVICE ->
    off_free k q ⊢ file_core_off k q pn C.
  Proof.
    intros Hty. rewrite /file_core_off.
    rewrite bool_decide_eq_false_2; [done|].
    destruct Hty as [Ht | Ht]; rewrite Ht; intro Hc;
      apply (f_equal bv_unsigned) in Hc; by vm_compute in Hc.
  Qed.
  Lemma proto_close_fdalloc_failed (γ : gname) (M : gmap nat (Qp * positive)) (k : nat) (C : fcontent) :
    M !! k = Some (1%Qp, 1%positive) -> fc_type C = FD_NONE ->
    ftable_auth γ M -∗ file_ref γ k 1 FdClosed ==∗
    ftable_auth γ (delete k M) ∗ ∃ C' : fcontent, file_fields k 1 C' ∗ file_pay γ k 1 C'.
  Proof.
    iIntros (HM Hty) "Ha (%C' & Href & Hflds & Hpay & Hlive)".
    iMod (file_close_last_ghost γ M k 1 HM with "Ha Href Hlive") as "Ha".
    iModIntro. iFrame "Ha". iExists C'. iFrame "Hflds".
    iApply (file_pay_st_pay with "Hpay").
  Qed.
End FileOffProtocol.
