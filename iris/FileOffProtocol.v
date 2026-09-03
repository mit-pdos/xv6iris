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
Require Import TsoMemPa TsoGhost TsoCtx CtxBox.   (* [llb loglen_name], [ufrac] stamps *)
Require Import WpSconfMem.   (* [wordw_free], [wordw_pointsto] -- the store's two faces *)
Require Import FdSlots IrefSlots FileInvDefs FileInv OffBox.   (* [irefslotG] must be IMPORTED, or the binder below silently generalises it *)
Require Import IcacheRef.   (* [NINODE], [ientry] *)
Require Import Xv6G.
Local Open Scope Z_scope.

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
  Proof. (* SKELETON r25 chain *) Admitted.

  (* ---- filealloc: the ghost step is main's, pure ---- *)
  Lemma proto_filealloc (γ : gname) (M : gmap nat (Qp * positive)) (k : nat) (C : fcontent) :
    M !! k = None -> fc_type C = FD_NONE ->
    ftable_auth γ M -∗ file_fields k 1 C -∗ file_pay γ k 1 C ==∗
    ftable_auth γ (<[k := (1%Qp, 1%positive)]> M) ∗ file_ref γ k 1 FdClosed.
  Proof. (* SKELETON r25 chain: = FileInv.file_alloc_step *) Admitted.

  (* ---- the opener's slot: the word comes out FREE ---- *)
  Lemma proto_open_slot (E : coPset) (γ : gname) (k : nat) :
    file_ref γ k 1 FdClosed ={E}=∗
    ∃ (C : fcontent) (pn : fpnames),
      ⌜fc_type C = FD_NONE⌝ ∗
      fref_tok γ k 1 ∗ flive_tok k ∗ fpay_tok γ k 1 pn ∗
      file_fields k 1 C ∗ file_core_noff 1 pn C ∗ off_free k 1.
  Proof. (* SKELETON r25 chain: = ProofSysOpenParts.so_open_slot's off part *) Admitted.

  (* ---- the store: the free word IS the store leaf's premise, and the
          leaf's result IS the resident cell at the storer's context ---- *)
  Lemma proto_store_free (k : nat) :
    off_free k 1 ⊣⊢ wordw_free 4 (a_foff k).
  Proof. (* SKELETON r25 chain (item 24) *) Admitted.
  Lemma proto_store_remint (k : nat) :
    wordw_pointsto 4 (a_foff k) (DfracOwn 1) (mword_of_int 0 : mword 32) ⊢ off_resident k.
  Proof. (* SKELETON r25 chain: word4 unfolding + off_wf_zero *) Admitted.

  (* ---- the publish: birth on the re-minted cell, share at mass 1, the L2
          row into inode [i]'s set; the creator deposits and never absorbs ---- *)
  Lemma proto_publish (E : coPset) (i k : nat) (C : fcontent) :
    ↑(offBoxN .@ k) ⊆ E -> (i < NINODE)%nat -> fc_ip C = ientry i -> fc_type C = FD_INODE ->
    own_context cur_ctx -∗ off_resident k -∗ off_rows off_cfg i cur_ctx ={E}=∗
    own_context cur_ctx ∗
    ∃ γb : box_names, off_fd k 1 γb C ∗ (ctx_floor cur_ctx 0 -∗ off_rows off_cfg i cur_ctx).
  Proof. (* SKELETON r25 chain: = ProofSysOpenParts.so_deposit *) Admitted.

  (* ---- dup: a pure split of the share by fraction ---- *)
  Lemma proto_dup (k : nat) (q1 q2 : Qp) (γb : box_names) (C : fcontent) :
    off_fd k (q1 + q2) γb C ⊣⊢ off_fd k q1 γb C ∗ off_fd k q2 γb C.
  Proof. (* SKELETON r25 chain: = FileInvDefs.off_fd_split *) Admitted.

  (* ---- read, step 0: name the share's stamps fragment and present its
          llb at the ilock acquire; R1 returns a floor at least that high
          (reviewer 2, item 31: the tie that makes the checkout provable) ---- *)
  Lemma proto_read_llb (k : nat) (q : Qp) (γb : box_names) (C : fcontent) :
    off_fd k q γb C -∗
    ∃ m : gmap (nat * nat) ufrac, off_fd_at k q γb C m ∗ llb loglen_name (max_stamp m).
  Proof. (* SKELETON r25 chain: off_ref_stamps unfolds to the fragment and its llb *) Admitted.

  (* ---- read: checkout under ip->lock.  [Kt] is R1's floor at the ilock
          acquire, at least the share's llb ([max_stamp m ≤ Kt]); [Kp] is the
          row's transported floor inside off_rows.  THE ONE ABSORB, after the
          acquire. ---- *)
  Lemma proto_read_checkout (E : coPset) (i k : nat) (q : Qp) (γb : box_names) (C : fcontent)
      (m : gmap (nat * nat) ufrac) (Kt : nat) (ξ : CtxId) :
    ↑(offBoxN .@ k) ⊆ E -> fc_ip C = ientry i -> (max_stamp m ≤ Kt)%nat ->
    own_context ξ -∗ ctx_floor ξ Kt -∗
    off_fd_at k q γb C m -∗
    off_rows off_cfg i ξ ={E}=∗
    own_context ξ ∗ off_resident (XI := ξ) k ∗
    ∃ T0 : nat,
      CtxBox.l2_hold (X := unit) γb k m ∗
      ghost_var (bx_slotd γb) (q / 2) (SlotReg T0 false k None : slot_reg nat unit) ∗
      ghost_var (ghost_varG0 := kalloc_count_inG) (bx_cnt γb) (q / 2) 1%nat ∗
      (∀ s' : l2_reg nat, off_l2_row γb s' ξ -∗ off_rows off_cfg i ξ).
  Proof. (* SKELETON r25 chain: off_rows_take + OffBox.off_read_checkout *) Admitted.

  (* ---- read: park after the read; the row goes back into the set at the
          fresh stamp ---- *)
  Lemma proto_read_park (E : coPset) (i k : nat) (q : Qp) (γb : box_names) (C : fcontent)
      (m : gmap (nat * nat) ufrac) (T0 : nat) (ξ : CtxId) :
    ↑(offBoxN .@ k) ⊆ E -> fc_ip C = ientry i -> (i < NINODE)%nat ->
    qsum m = Qp_to_Qc q ->
    own_context ξ -∗ off_resident (XI := ξ) k -∗
    CtxBox.l2_hold (X := unit) γb k m -∗
    ghost_var (bx_slotd γb) (q / 2) (SlotReg T0 false k None : slot_reg nat unit) -∗
    ghost_var (ghost_varG0 := kalloc_count_inG) (bx_cnt γb) (q / 2) 1%nat -∗
    off_box k γb -∗ off_member off_cfg i γb -∗
    (∀ s' : l2_reg nat, off_l2_row γb s' ξ -∗ off_rows off_cfg i ξ) ={E}=∗
    own_context ξ ∗ off_fd k q γb C ∗
    ∃ T' : nat, llb loglen_name T' ∗ (ctx_floor ξ T' -∗ off_rows off_cfg i ξ).
  Proof. (* SKELETON r25 chain: OffBox.off_read_park + the row back *) Admitted.

  (* ---- close, non-last: a pure join ---- *)
  Lemma proto_close_join (k : nat) (q1 q2 : Qp) (γb : box_names) (C : fcontent) :
    off_fd k q1 γb C ∗ off_fd k q2 γb C ⊢ off_fd k (q1 + q2) γb C.
  Proof. (* SKELETON r25 chain: off_fd_split, right to left *) Admitted.

  (* ---- close, last: the whole share in hand; the free-tier withdraw; the
          retype puts the free word into the FD_NONE payload ---- *)
  Lemma proto_last_close (E : coPset) (k : nat) (γb : box_names) (C : fcontent) :
    ↑(offBoxN .@ k) ⊆ E ->
    off_fd k 1 γb C ={E}=∗ off_free k 1.
  Proof. (* SKELETON r25 chain: OffBox.off_last_close *) Admitted.
  Lemma proto_retype_none (k : nat) (pn : fpnames) (C' : fcontent) :
    fc_type C' = FD_NONE ->
    off_free k 1 ⊢ file_core_off k 1 pn C'.
  Proof. (* SKELETON r25 chain: the non-INODE arm IS off_free *) Admitted.

  (* ---- realloc: the same slot, freed, is allocated again -- the row's word
          is the free one the last close left ---- *)
  Lemma proto_realloc (γ : gname) (M : gmap nat (Qp * positive)) (k : nat) (C : fcontent) :
    M !! k = None -> fc_type C = FD_NONE ->
    ftable_auth γ M -∗ file_fields k 1 C -∗ file_pay γ k 1 C ==∗
    ftable_auth γ (<[k := (1%Qp, 1%positive)]> M) ∗ file_ref γ k 1 FdClosed.
  Proof. (* SKELETON r25 chain: = proto_filealloc *) Admitted.

  (* ---- fork: the parent dups (a pure split) and KEEPS one half; the child
          reads at ITS context ξ' with the other: the share is context-free,
          so no morph is needed; the child runs [proto_read_llb] on its half,
          presents the llb at its ilock acquire ([max_stamp m ≤ Kt] by R1),
          and its [Kp] is the row's floor at ξ'.  Both halves are returned
          (reviewer 1, item 29); the read is [proto_read_checkout] at ξ' over
          one of them (reviewer 2, item 31: at the named fragment). ---- *)
  Lemma proto_fork_child_read (E : coPset) (i k : nat) (q : Qp) (γb : box_names) (C : fcontent)
      (ξ' : CtxId) :
    ↑(offBoxN .@ k) ⊆ E -> fc_ip C = ientry i ->
    off_fd k q γb C -∗
    off_fd k (q / 2) γb C ∗ off_fd k (q / 2) γb C ∗
    □ (∀ (m : gmap (nat * nat) ufrac) (Kt : nat),
         ⌜(max_stamp m ≤ Kt)%nat⌝ -∗
         own_context ξ' -∗ ctx_floor ξ' Kt -∗ off_fd_at k (q / 2) γb C m -∗ off_rows off_cfg i ξ' ={E}=∗
         own_context ξ' ∗ off_resident (XI := ξ') k ∗
         ∃ T0 : nat,
           CtxBox.l2_hold (X := unit) γb k m ∗
           ghost_var (bx_slotd γb) (q / 2 / 2) (SlotReg T0 false k None : slot_reg nat unit) ∗
           ghost_var (ghost_varG0 := kalloc_count_inG) (bx_cnt γb) (q / 2 / 2) 1%nat ∗
           (∀ s' : l2_reg nat, off_l2_row γb s' ξ' -∗ off_rows off_cfg i ξ')).
  Proof. (* SKELETON r25 chain: proto_dup at q/2 + q/2 (both kept), then proto_read_checkout at ξ' *) Admitted.

  (* ---- the other arms of [file_core_off], named (reviewer 2, optional
          links): pipe and device keep the free word through the retype; the
          fdalloc-failed close at FD_NONE is the retype followed by the free
          row (there is no box to abandon). ---- *)
  Lemma proto_retype_other (k : nat) (q : Qp) (pn : fpnames) (C : fcontent) :
    fc_type C = FD_PIPE \/ fc_type C = FD_DEVICE ->
    off_free k q ⊢ file_core_off k q pn C.
  Proof. (* SKELETON r25 chain: the non-INODE arm IS off_free *) Admitted.
  Lemma proto_close_fdalloc_failed (γ : gname) (M : gmap nat (Qp * positive)) (k : nat) (C : fcontent) :
    M !! k = Some (1%Qp, 1%positive) -> fc_type C = FD_NONE ->
    ftable_auth γ M -∗ file_ref γ k 1 FdClosed ==∗
    ftable_auth γ (delete k M) ∗ ∃ C' : fcontent, file_fields k 1 C' ∗ file_pay γ k 1 C'.
  Proof. (* SKELETON r25 chain: = FileInv.file_close_last_step at FD_NONE; the payload holds off_free k 1 *) Admitted.
End FileOffProtocol.
