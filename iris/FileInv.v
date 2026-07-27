(* FileInv.v -- the open-file table: [struct file]'s geometry, the
   reference-count algebra, the "holding a reference on a struct file"
   predicate, and the resource [ftable.lock] protects.  Kept apart from any
   whole-function proof so filealloc / filedup / fileclose / sys_open share it.

   The design (and the reasoning behind the algebra) is written up in
   claude-notes/design/file-table.md; the short version:

     struct file { int type; int ref; char readable; char writable;
                   struct pipe *pipe; struct inode *ip; uint off; short major; }
     struct { struct spinlock lock; struct file file[NFILE]; } ftable;

   Three different disciplines govern the fields, and the model keeps them
   apart:

   * [ref] is protected by ftable.lock -- filealloc's scan reads the [ref]
     field of EVERY entry, so all NFILE of those cells live in the lock's
     resource and none of them ever travels with a reference.
   * the other fields are immutable while [ref > 0] and are read with no lock
     at all, so a reference has to carry a real points-to FRACTION of them.
   * [off] is mutable under ip->lock; see the "off" note at the bottom.

   The two halves are tied together by one authoritative ghost map, keyed by
   slot index: [M !! k = Some (q,n)] says slot k has n outstanding references
   holding fraction q of the content between them, and [k ∉ dom M] says the
   slot is free.  Because [fracR] has no unit and [positiveR] no zero, a
   fragment [(q,1)] included in [(qt,n)] forces [n = 1 -> q = qt]: THE HOLDER
   OF THE ONLY REFERENCE HOLDS THE FULL FRACTION, hence write access.  That is
   what licenses sys_open's unlocked initialization of a fresh file and
   fileclose's [f->type = FD_NONE] at ref 0. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import auth gmap frac numbers.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import ArrCursor.
Require Import WpLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  Geometry                                                           *)
(* ------------------------------------------------------------------ *)

(* struct ftable { struct spinlock lock; struct file file[NFILE]; }, so the
   lock is the first member and &ftable.lock = &ftable (SpecFileinit.v). *)
Definition ftable_addr : mword 64 := mword_of_int KernelSyms.ftable.

Definition NFILE : nat := 100%nat.
Definition file_stride : Z := 40.               (* the loop's [addi s1,s1,40] *)
Definition file_base : Z := KernelSyms.ftable + 24.

(* the [k]th entry, &ftable.file[k].  [fnode NFILE] is one past the last entry
   -- which is where the next global (<disk>) starts, and is the literal end
   pointer filealloc's scan compares its cursor against. *)
Definition fnode (k : nat) : mword 64 := acur file_base file_stride k.

(* the field addresses, in the EXACT [add_vec base (sign_extend' 64 imm)] form
   the instructions compute, so a load/store address unifies with the cell
   without rewriting. *)
Definition foff_of (a : mword 64) (i : Z) : mword 64 :=
  add_vec a (sign_extend' 64 (mword_of_int i : mword 12)).

Definition a_ftype     (k : nat) : mword 64 := fnode k.
Definition a_fref      (k : nat) : mword 64 := foff_of (fnode k) 4.
Definition a_freadable (k : nat) : mword 64 := foff_of (fnode k) 8.
Definition a_fwritable (k : nat) : mword 64 := foff_of (fnode k) 9.
Definition a_fpipe     (k : nat) : mword 64 := foff_of (fnode k) 16.
Definition a_fip       (k : nat) : mword 64 := foff_of (fnode k) 24.
Definition a_foff      (k : nat) : mword 64 := foff_of (fnode k) 32.
Definition a_fmajor    (k : nat) : mword 64 := foff_of (fnode k) 36.

(* the side conditions [ArrCursor]'s cursor lemmas take, discharged once. *)
Lemma file_base_nonneg : 0 <= file_base.
Proof. unfold file_base, KernelSyms.ftable. lia. Qed.
Lemma file_stride_pos : 0 < file_stride.
Proof. unfold file_stride. lia. Qed.
Lemma file_end_fits : file_base + file_stride * Z.of_nat NFILE < 2 ^ 64.
Proof.
  unfold file_base, file_stride, NFILE, KernelSyms.ftable.
  assert (H : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  rewrite H. lia.
Qed.

(* the four [type] codes (file.h's anonymous enum). *)
Definition FD_NONE   : mword 32 := mword_of_int 0.
Definition FD_PIPE   : mword 32 := mword_of_int 1.
Definition FD_INODE  : mword 32 := mword_of_int 2.
Definition FD_DEVICE : mword 32 := mword_of_int 3.

(* ------------------------------------------------------------------ *)
(*  The reference-count algebra                                        *)
(* ------------------------------------------------------------------ *)

Definition fileUR : ucmra := authUR (gmapUR nat (prodR fracR positiveR)).

Class fileG (Σ : gFunctors) := FileG { file_inG :: inG Σ fileUR }.
Definition fileΣ : gFunctors := #[GFunctor fileUR].
Global Instance subG_fileΣ {Σ} : subG fileΣ Σ -> fileG Σ.
Proof. solve_inG. Qed.

(* the immutable-while-referenced content of a [struct file]: every field but
   [ref].  [fc_off] is here for now -- see the "off" note at the bottom. *)
Record fcontent := MkFContent {
  fc_type     : mword 32;
  fc_readable : bv 8;
  fc_writable : bv 8;
  fc_pipe     : mword 64;
  fc_ip       : mword 64;
  fc_off      : mword 32;
  fc_major    : bv 16;
}.

(* ------------------------------------------------------------------ *)
(*  The [ref] word: zero exactly on a free slot                         *)
(* ------------------------------------------------------------------ *)

(* filealloc's scan tests [f->ref] with a sign-extending 4-byte load and a
   [c.beqz], so what the branch consumes is the 64-bit sign extension of the
   stored word.  These two lemmas are the whole content of "the physical test
   and the ghost state agree": a slot outside the authority reads zero, a slot
   inside it reads its (positive, in-range) count and so reads nonzero. *)
Lemma fref_word_zero :
  eq_vec (sign_extend' 64 (mword_of_int 0 : mword 32)) (zero_reg : mword 64) = true.
Proof. apply eq_vec_true_iff. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma fref_word_nonzero (n : positive) :
  Z.pos n < 2 ^ 31 ->
  eq_vec (sign_extend' 64 (mword_of_int (Z.pos n) : mword 32)) (zero_reg : mword 64) = false.
Proof.
  intro Hn.
  (* [lia] cannot evaluate [2^k]; name the three literals first. *)
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  assert (E32 : (2 ^ 32 = 4294967296)%Z) by (vm_compute; reflexivity).
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  rewrite E31 in Hn.
  assert (Hlt32 : (Z.pos n < 2 ^ 32)%Z) by (rewrite E32; lia).
  (* the stored word's unsigned value is [n] itself (no wrap) ... *)
  assert (Hu : bv_unsigned (mword_of_int (Z.pos n) : mword 32) = Z.pos n).
  { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (Z.of_N 32) with 32. rewrite E32.
    rewrite Z.mod_small; [reflexivity | lia]. }
  (* ... and it is below the half modulus, so the sign extension is the
     identity on the value. *)
  assert (Hs : bv_signed (mword_of_int (Z.pos n) : mword 32) = Z.pos n).
  { unfold bv_signed. rewrite Hu. apply bv_swrap_small.
    unfold bv_half_modulus, bv_modulus. change (Z.of_N 32) with 32.
    assert (Ehalf : (2 ^ 32 / 2 = 2147483648)%Z) by (vm_compute; reflexivity).
    rewrite Ehalf. lia. }
  apply eq_vec_false_iff. intro Hc. apply (f_equal bv_unsigned) in Hc.
  assert (Hz : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite Hz in Hc. revert Hc.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned. rewrite Hs.
  unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite E64. rewrite Z.mod_small; [lia|]. lia.
Qed.

(* the count component's [⋅] IS [Pos.add]; naming it lets [lia] see the
   arithmetic in the local-update side conditions. *)
Lemma pos_op_add (a b : positive) : (a ⋅ b) = (a + b)%positive.
Proof. reflexivity. Qed.
Lemma pos_succ_1_add (b : positive) : Pos.succ (1 + b) = (2 + b)%positive.
Proof. lia. Qed.

Section FileInv.
  Context `{!riscvGS Σ, !lockG Σ, !fileG Σ}.

  (* ---- the content cells, at an arbitrary dfrac ---- *)
  Definition file_fields (k : nat) (dq : dfrac) (C : fcontent) : iProp Σ :=
    (a_ftype k     ↦₄{dq} fc_type C ∗
     a_freadable k ↦ₘ{dq} fc_readable C ∗
     a_fwritable k ↦ₘ{dq} fc_writable C ∗
     a_fpipe k     ↦₈{dq} fc_pipe C ∗
     a_fip k       ↦₈{dq} fc_ip C ∗
     a_foff k      ↦₄{dq} fc_off C ∗
     a_fmajor k    ↦₂{dq} fc_major C)%I.

  (* ---- one reference's ghost fragment ---- *)
  Definition fref_tok (γ : gname) (k : nat) (q : Qp) : iProp Σ :=
    own γ (◯ {[ k := (q, 1%positive) ]}).

  (* ---- THE predicate: holding one reference on file slot [k] ----

     The unit of ownership everywhere a [struct file *] is held: a process's
     p->ofile[fd], a syscall's local [struct file *f], pipealloc's two
     half-built files.  It is NOT persistent and NOT duplicable -- duplicating
     it is filedup, which must run under ftable.lock and bump the physical
     count.  [file_ref γ k 1 C] is the exclusive (writable) state. *)
  Definition file_ref (γ : gname) (k : nat) (q : Qp) (C : fcontent) : iProp Σ :=
    (fref_tok γ k q ∗ file_fields k (DfracOwn q) C)%I.

  (* ---- the ftable lock's resource ----

     The invariant holds every slot's [ref] cell (filealloc scans them all),
     and, per slot, whatever content fraction has NOT been handed out: all of
     it when the slot is free, [1-q] when q is out, nothing at all when q = 1.
     Note what is NOT here: the content of a referenced file.  That is exactly
     why fileread can read f->type / f->ip holding no lock. *)
  Definition file_rest (k : nat) (q : Qp) : iProp Σ :=
    match (1 - q)%Qp with
    | Some q' => (∃ C, file_fields k (DfracOwn q') C)%I
    | None    => emp%I
    end.

  (* q = 1 -- every share is out, so the invariant keeps nothing. *)
  Lemma file_rest_full (k : nat) : file_rest k 1 ⊣⊢ emp.
  Proof.
    rewrite /file_rest.
    assert (Hs : (1 - 1)%Qp = None) by (apply Qp.sub_None; done).
    rewrite Hs. reflexivity.
  Qed.

  Definition fslot (M : gmap nat (Qp * positive)) (k : nat) : iProp Σ :=
    match M !! k with
    | None =>
        (a_fref k ↦₄ (mword_of_int 0 : mword 32) ∗
         ∃ C, ⌜fc_type C = FD_NONE⌝ ∗ file_fields k (DfracOwn 1) C)%I
    | Some (q, n) =>
        (⌜Z.pos n < 2 ^ 31⌝ ∗
         a_fref k ↦₄ (mword_of_int (Z.pos n) : mword 32) ∗
         file_rest k q)%I
    end.

  Definition ftable_res (γ : gname) : iProp Σ :=
    (∃ M : gmap nat (Qp * positive),
       own γ (● M) ∗
       ⌜∀ k, is_Some (M !! k) -> (k < NFILE)%nat⌝ ∗
       [∗ list] k ∈ seq 0 NFILE, fslot M k)%I.

  (* the whole table: the spinlock named "ftable" over that resource.
     Persistent, so every core shares it. *)
  Definition is_ftable (γl γ : gname) : iProp Σ :=
    is_lock γl ftable_addr "ftable"%string (ftable_res γ).

  Global Instance is_ftable_persistent γl γ : Persistent (is_ftable γl γ).
  Proof. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  Content: agreement and the fractional split                         *)
  (* ------------------------------------------------------------------ *)

  (* Two fds onto the same file agree on its content -- for free, because a
     reference carries genuine points-to fractions.  No [agree] ghost. *)
  Lemma file_fields_agree k dq1 C1 dq2 C2 :
    file_fields k dq1 C1 -∗ file_fields k dq2 C2 -∗ ⌜C1 = C2⌝.
  Proof.
    rewrite /file_fields.
    iIntros "(Ht1 & Hr1 & Hw1 & Hp1 & Hi1 & Ho1 & Hm1)".
    iIntros "(Ht2 & Hr2 & Hw2 & Hp2 & Hi2 & Ho2 & Hm2)".
    iDestruct (word4_pointsto_agree with "Ht1 Ht2") as %E1.
    iDestruct (mem_pointsto_agree with "Hr1 Hr2") as %E2.
    iDestruct (mem_pointsto_agree with "Hw1 Hw2") as %E3.
    iDestruct (word_pointsto_agree with "Hp1 Hp2") as %E4.
    iDestruct (word_pointsto_agree with "Hi1 Hi2") as %E5.
    iDestruct (word4_pointsto_agree with "Ho1 Ho2") as %E6.
    iDestruct (word2_pointsto_agree with "Hm1 Hm2") as %E7.
    iPureIntro. destruct C1, C2; cbn in *. congruence.
  Qed.

  Lemma file_ref_agree γ k q1 C1 q2 C2 :
    file_ref γ k q1 C1 -∗ file_ref γ k q2 C2 -∗ ⌜C1 = C2⌝.
  Proof. iIntros "[_ H1] [_ H2]". by iApply (file_fields_agree with "H1 H2"). Qed.

  (* the split filedup performs and fileclose undoes. *)
  Lemma file_fields_frac_split k q1 q2 C :
    file_fields k (DfracOwn (q1 + q2)) C ⊣⊢
    file_fields k (DfracOwn q1) C ∗ file_fields k (DfracOwn q2) C.
  Proof.
    rewrite /file_fields.
    rewrite (word4_pointsto_frac_split (a_ftype k)).
    rewrite (mem_pointsto_frac_split (a_freadable k)).
    rewrite (mem_pointsto_frac_split (a_fwritable k)).
    rewrite (word_pointsto_frac_split (a_fpipe k)).
    rewrite (word_pointsto_frac_split (a_fip k)).
    rewrite (word4_pointsto_frac_split (a_foff k)).
    rewrite (word2_pointsto_frac_split (a_fmajor k)).
    iSplit.
    - iIntros "([A1 B1] & [A2 B2] & [A3 B3] & [A4 B4] & [A5 B5] & [A6 B6] & [A7 B7])".
      iFrame.
    - iIntros "[(A1 & A2 & A3 & A4 & A5 & A6 & A7) (B1 & B2 & B3 & B4 & B5 & B6 & B7)]".
      iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  Reaching into the table                                             *)
  (* ------------------------------------------------------------------ *)

  (* Borrow one slot out of the NFILE-way big-sep and put it back, possibly
     under a DIFFERENT authority map -- which is what filealloc needs: its
     scan borrows slot after slot unchanged (M' := M), and the slot it takes
     is given back at [<[i := (1,1)]> M].  Since [fslot M k] reads only
     [M !! k], every other slot is untouched by the update. *)
  Lemma ftable_slots_acc (M : gmap nat (Qp * positive)) (i : nat) :
    (i < NFILE)%nat ->
    ([∗ list] k ∈ seq 0 NFILE, fslot M k) -∗
    fslot M i ∗
    (∀ M' : gmap nat (Qp * positive),
       ⌜∀ k, k ≠ i -> M' !! k = M !! k⌝ -∗ fslot M' i -∗
       [∗ list] k ∈ seq 0 NFILE, fslot M' k).
  Proof.
    iIntros (Hi) "H".
    assert (Hlk : seq 0 NFILE !! i = Some i).
    { apply lookup_seq. lia. }
    rewrite (big_sepL_delete (fun _ k => fslot M k) (seq 0 NFILE) i i Hlk).
    iDestruct "H" as "[$ Hrest]".
    iIntros (M' HM') "Hi".
    rewrite (big_sepL_delete (fun _ k => fslot M' k) (seq 0 NFILE) i i Hlk).
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
    own γ (● M) -∗ fref_tok γ k q -∗
    ⌜∃ qt n, M !! k = Some (qt, n) /\
       (n = 1%positive -> q = qt) /\ (q = qt -> n = 1%positive)⌝.
  Proof.
    rewrite /fref_tok. iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %[Hincl _]%auth_both_valid_discrete.
    iPureIntro.
    apply singleton_included_l in Hincl as [y [Hy Hle]].
    apply leibniz_equiv in Hy. destruct y as [qt n]. exists qt, n.
    split; [exact Hy|].
    apply Some_included in Hle as [Heq | Hlt].
    - (* the fragment IS the whole entry: same fraction, count 1 *)
      destruct Heq as [Hq Hn]; cbn in Hq, Hn.
      split; intros _; [exact Hq | by rewrite -Hn].
    - (* strictly included, so BOTH components strictly grow *)
      apply pair_included in Hlt as [Hq Hn]; cbn in Hq, Hn.
      apply frac_included in Hq. apply pos_included in Hn.
      split; intros Hc.
      + exfalso. rewrite Hc in Hn. lia.
      + exfalso. rewrite Hc in Hq. by apply (irreflexivity Qp.lt qt).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The three ghost steps, all performed under ftable.lock              *)
  (* ------------------------------------------------------------------ *)

  (* filealloc: [ref = 0] -> [ref = 1].  Allocate the authority entry at
     (1,1) and hand the invariant's WHOLE content fraction out as the
     exclusive reference. *)
  Lemma file_alloc_step γ M k C :
    M !! k = None ->
    own γ (● M) -∗ file_fields k (DfracOwn 1) C ==∗
    own γ (● (<[k := (1%Qp, 1%positive)]> M)) ∗ file_ref γ k 1 C.
  Proof.
    iIntros (HM) "Ha Hf".
    iMod (own_update with "Ha") as "[Ha Hfrag]".
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update _ k (1%Qp, 1%positive)); [done|].
      split; done. }
    iModIntro. iFrame "Ha". rewrite /file_ref /fref_tok. iFrame.
  Qed.

  (* filedup: [ref++].  The new reference's fraction comes out of the
     CALLER's -- nothing is conjured, which is exactly why the invariant's
     leftover [file_rest k qt] is untouched. *)
  Lemma file_dup_step γ M k q C qt (n : positive) :
    M !! k = Some (qt, n) ->
    own γ (● M) -∗ file_ref γ k q C ==∗
    own γ (● (<[k := (qt, Pos.succ n)]> M)) ∗
    file_ref γ k (q/2)%Qp C ∗ file_ref γ k (q/2)%Qp C.
  Proof.
    iIntros (HM) "Ha [Hf Hc]".
    iMod (own_update_2 with "Ha Hf") as "[Ha Hfrag]".
    { apply auth_update.
      apply (singleton_local_update _ k (qt, n) (q, 1%positive)
                                      (qt, Pos.succ n) (q, 2%positive) HM).
      apply local_update_discrete. intros mz Hv Hz.
      destruct Hv as [Hvq Hvn]. split; [by split|].
      destruct mz as [[qf nf]|]; destruct Hz as [Hq Hn]; simpl in Hq, Hn.
      - split; simpl; [exact Hq|]. rewrite Hn !pos_op_add. apply pos_succ_1_add.
      - split; simpl; [exact Hq|]. by rewrite Hn. }
    iModIntro. iFrame "Ha".
    (* split the fragment: (q/2,1) ⋅ (q/2,1) = (q,2) *)
    rewrite /file_ref /fref_tok.
    assert (Hsp : ({[k := (q, 2%positive)]} : gmap nat (Qp * positive))
                  = {[k := ((q/2)%Qp, 1%positive)]} ⋅ {[k := ((q/2)%Qp, 1%positive)]}).
    { rewrite singleton_op. f_equal. rewrite -pair_op.
      by rewrite frac_op Qp.div_2. }
    rewrite Hsp auth_frag_op own_op.
    iDestruct "Hfrag" as "[$ $]".
    (* and the content fraction, likewise *)
    rewrite -{1}(Qp.div_2 q) file_fields_frac_split.
    iDestruct "Hc" as "[$ $]".
  Qed.

  (* fileclose, [--ref > 0]: the departing reference's fraction has to go
     SOMEWHERE, and it goes back into the authority's outstanding total (and,
     on the points-to side, into [file_rest]).  That is why the frac component
     tracks outstanding fraction rather than being pinned at 1. *)
  Lemma file_close_step γ M k q C qt (n : positive) (qr : Qp) :
    M !! k = Some (qt, Pos.succ n) ->
    (qt - q)%Qp = Some qr ->
    own γ (● M) -∗ file_ref γ k q C ==∗
    own γ (● (<[k := (qr, n)]> M)) ∗ file_fields k (DfracOwn q) C.
  Proof.
    iIntros (HM Hsub) "Ha [Hf $]".
    apply Qp.sub_Some in Hsub.       (* qt = q + qr *)
    iMod (own_update_2 with "Ha Hf") as "$"; [|done].
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

  (* fileclose, [--ref == 0]: validity forced [q = qt = 1] (fref_tok_lookup),
     so the closer walks away with fraction 1 of every content cell -- enough
     to write [type = FD_NONE] -- and the slot leaves the authority. *)
  Lemma file_close_last_step γ M k C :
    M !! k = Some (1%Qp, 1%positive) ->
    own γ (● M) -∗ file_ref γ k 1 C ==∗
    own γ (● (delete k M)) ∗ file_fields k (DfracOwn 1) C.
  Proof.
    iIntros (HM) "Ha [Hf $]".
    iMod (own_update_2 with "Ha Hf") as "$"; [|done].
    (* [(1,1)] is exclusive in [prodR fracR positiveR] (a second share would
       push the fraction past 1), so the whole entry just goes away. *)
    apply auth_update_dealloc, delete_singleton_local_update. apply _.
  Qed.

End FileInv.
