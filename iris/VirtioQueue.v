(* ====================================================================== *)
(* VirtioQueue.v -- the KEYED driver-side queue protocol, pure layer.      *)
(*                                                                         *)
(* VirtioModel section 7 states the device-thread obligation FLAT: a set   *)
(* [S] of reachable ring positions over one pinned control map [ctl].      *)
(* That form is what the device thread consumes, but the DRIVER needs to   *)
(* manipulate the obligation per-request: publish a new slot, watch the    *)
(* device complete the oldest one, and RECLAIM a completed slot's bytes    *)
(* (shrinking the lease).  This file is the keyed presentation:            *)
(*                                                                         *)
(*   - requests are keyed by their NAT sequence number [p] (the p-th       *)
(*     request ever published); [wrap16] bridges to the 16-bit ring        *)
(*     counters, and every 16-bit fact is recovered from the separation    *)
(*     fact that positions in the window pin DISTINCT avail-ring entries,  *)
(*     never from modular window arithmetic;                               *)
(*   - a slot's [pin] (the sub-map of the lease the device only reads)     *)
(*     DETERMINES its request ([slot_pin_ok]), including -- for a write     *)
(*     request -- the payload, so the device step at that slot is a         *)
(*     computable function ([vslot_post]/[vslot_writes]);                  *)
(*   - [vproto_ok] is the whole keyed obligation; [vproto_flat] derives    *)
(*     VirtioModel's [virtio_queue_ok] from it, so the PROVEN device-side  *)
(*     lemmas (not-stalled, step) keep working unchanged;                  *)
(*   - [vproto_ok_publish] / [vproto_step_det] / [vproto_ok_reclaim] are   *)
(*     the three surgeries the Iris layer (VirtioProto.v) performs.        *)
(*                                                                         *)
(* Design rationale: claude-notes/design/virtio-driver.md.                 *)
(* ====================================================================== *)

From stdpp Require Import gmap.
From stdpp Require Import bitvector.definitions.

Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import VirtioModel.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* -1. Byte-map helpers.                                                   *)
(*                                                                         *)
(*     RiscvModelBytes states [read_bytes] one way only (a successful read  *)
(*     pins the bytes); the queue protocol needs the CONTENT-level facts    *)
(*     too -- how to build a read, how a read frames along a sub-map, and   *)
(*     what a [write_bytes]/[write_byte_list] touches.  They are stated     *)
(*     over an arbitrary byte map, so any other DMA-shaped proof can reuse  *)
(*     them.                                                               *)
(* ---------------------------------------------------------------------- *)

(* -- a tiny disjointness toolkit.  [set_solver] must NOT be used on goals   *)
(*    mentioning [used_page_pas] / [pa_range] at a LITERAL size: it unfolds   *)
(*    [list_to_set] over a 4096-element list and does not come back.  These   *)
(*    lemmas are over abstract sets, so every such step is one [apply].       *)

Section gset_tools.
  Context {A : Type} `{Countable A}.

  Lemma gset_disj_mono (X X' Y Y' : gset A) :
    X ⊆ X' -> Y ⊆ Y' -> X' ## Y' -> X ## Y.
  Proof.
    intros HX HY Hd. apply elem_of_disjoint. intros a Ha Hb.
    exact (proj1 (elem_of_disjoint _ _) Hd a (HX a Ha) (HY a Hb)).
  Qed.

  Lemma gset_disj_sub_l (X X' Y : gset A) : X ⊆ X' -> X' ## Y -> X ## Y.
  Proof. intro HX. apply gset_disj_mono; [exact HX | reflexivity]. Qed.

  Lemma gset_disj_sub_r (X Y Y' : gset A) : Y ⊆ Y' -> X ## Y' -> X ## Y.
  Proof. intro HY. apply gset_disj_mono; [reflexivity | exact HY]. Qed.

  Lemma gset_disj_sym (X Y : gset A) : X ## Y -> Y ## X.
  Proof.
    intro Hd. apply elem_of_disjoint. intros a Ha Hb.
    exact (proj1 (elem_of_disjoint _ _) Hd a Hb Ha).
  Qed.

  Lemma gset_disj_union_l (X Y Z : gset A) : X ## Z -> Y ## Z -> (X ∪ Y) ## Z.
  Proof.
    intros H1 H2. apply elem_of_disjoint. intros a Ha Hb.
    apply elem_of_union in Ha as [Ha|Ha].
    - exact (proj1 (elem_of_disjoint _ _) H1 a Ha Hb).
    - exact (proj1 (elem_of_disjoint _ _) H2 a Ha Hb).
  Qed.

  Lemma gset_disj_union_r (X Y Z : gset A) : X ## Y -> X ## Z -> X ## (Y ∪ Z).
  Proof.
    intros H1 H2. apply gset_disj_sym, gset_disj_union_l; apply gset_disj_sym;
      [exact H1 | exact H2].
  Qed.

  Lemma gset_eq_of_elem (X Y : gset A) : (forall x, x ∈ X <-> x ∈ Y) -> X = Y.
  Proof. intro Hx. apply set_eq_subseteq. split; intros x Hin; apply Hx; exact Hin. Qed.

  Lemma gset_union_assoc (X Y Z : gset A) : X ∪ (Y ∪ Z) = (X ∪ Y) ∪ Z.
  Proof. apply gset_eq_of_elem. intro x. rewrite !elem_of_union. tauto. Qed.

  (* pulling one element out of the left summand (used by the step's domain
     bookkeeping; [set_solver] cannot do this one here) *)
  Lemma gset_union_split (X Y : gset A) (a : A) :
    a ∈ X -> X ∪ Y = (X ∖ {[a]}) ∪ ({[a]} ∪ Y).
  Proof.
    intro Ha. apply set_eq_subseteq. split; intros x Hx.
    - apply elem_of_union in Hx as [Hx|Hx].
      + destruct (decide (x = a)) as [->|Hne].
        * apply elem_of_union_r, elem_of_union_l, elem_of_singleton. reflexivity.
        * apply elem_of_union_l, elem_of_difference. split; [exact Hx|].
          intro Hc. apply elem_of_singleton in Hc. exact (Hne Hc).
      + apply elem_of_union_r, elem_of_union_r. exact Hx.
    - apply elem_of_union in Hx as [Hx|Hx].
      + apply elem_of_difference in Hx as [Hx _]. apply elem_of_union_l. exact Hx.
      + apply elem_of_union in Hx as [Hx|Hx].
        * apply elem_of_singleton in Hx. subst x. apply elem_of_union_l. exact Ha.
        * apply elem_of_union_r. exact Hx.
  Qed.

  Lemma gset_diff_union_notin (X Y : gset A) (a : A) :
    a ∉ X -> (X ∪ Y) ∖ {[a]} = X ∪ (Y ∖ {[a]}).
  Proof.
    intro Ha. apply gset_eq_of_elem. intro x.
    rewrite elem_of_difference, !elem_of_union, elem_of_difference,
            elem_of_singleton.
    split.
    - intros [[H1|H1] Hne]; [ left; exact H1 | right; split; [exact H1|exact Hne] ].
    - intros [H1|[H1 Hne]].
      + split; [ left; exact H1 | ]. intros ->. exact (Ha H1).
      + split; [ right; exact H1 | exact Hne ].
  Qed.

  Lemma gset_sub_diff (X D Y : gset A) : X ⊆ D -> X ## Y -> X ⊆ D ∖ Y.
  Proof.
    intros HD Hd a Ha. apply elem_of_difference. split; [exact (HD a Ha)|].
    intro Hb. exact (proj1 (elem_of_disjoint _ _) Hd a Ha Hb).
  Qed.
End gset_tools.

(* -- [pa_add] is 64-bit WRAPPING addition; every distinctness fact about   *)
(*    small offsets from a common base goes through [pa_add_inj].           *)

Lemma vq_add_vec_unsigned (x y : SailStdpp.Values.mword 64) :
  bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, SailStdpp.Values.to_word, SailStdpp.Values.get_word,
    MachineWord.MachineWord.add.
  rewrite bv_add_unsigned. reflexivity.
Qed.

Lemma vq_moi_unsigned (k : Z) :
  bv_unsigned (SailStdpp.Values.mword_of_int k : SailStdpp.Values.mword 64)
  = bv_wrap 64 k.
Proof.
  unfold SailStdpp.Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* NB the [: mword 64] ascription: [pa_add] lands in [Arch.pa], whose width is
   an unreduced [Z_idx] match, and [bv_unsigned] would elaborate at THAT width
   (the two print identically and then fail to rewrite). *)
Lemma pa_add_unsigned (a : Arch.pa) (j : nat) :
  bv_unsigned (pa_add a j : SailStdpp.Values.mword 64)
  = bv_wrap 64 (bv_unsigned (a : SailStdpp.Values.mword 64) + Z.of_nat j).
Proof.
  unfold pa_add, add_vec_int.
  rewrite vq_add_vec_unsigned, vq_moi_unsigned, bv_wrap_add_idemp_r. reflexivity.
Qed.

Lemma vq_mod64 : bv_modulus 64 = 18446744073709551616.
Proof. vm_compute. reflexivity. Qed.

(* the two directions of address equality, both stated at the REDUCED width so
   that [pa_add_unsigned] actually rewrites in them *)
Lemma pa_eq_of_unsigned (x y : Arch.pa) :
  bv_unsigned (x : SailStdpp.Values.mword 64)
  = bv_unsigned (y : SailStdpp.Values.mword 64) -> x = y.
Proof. intro H. apply bv_eq. exact H. Qed.

Lemma pa_unsigned_of_eq (x y : Arch.pa) :
  x = y ->
  bv_unsigned (x : SailStdpp.Values.mword 64)
  = bv_unsigned (y : SailStdpp.Values.mword 64).
Proof. intros ->. reflexivity. Qed.

(* the cancellation, as plain-Z arithmetic (lia is reliable only here) *)
Lemma vq_wrap_cancel (u i j : Z) :
  0 <= i < 18446744073709551616 -> 0 <= j < 18446744073709551616 ->
  (u + i) `mod` 18446744073709551616 = (u + j) `mod` 18446744073709551616 ->
  i = j.
Proof.
  intros Hi Hj Heq.
  assert (Hd : (i - j) `mod` 18446744073709551616 = 0).
  { replace (i - j) with ((u + i) - (u + j)) by lia.
    rewrite Zminus_mod, Heq, Z.sub_diag. reflexivity. }
  apply Z.mod_divide in Hd; [| lia ].
  destruct Hd as [k Hk]. nia.
Qed.

Lemma pa_add_inj (a : Arch.pa) (i j : nat) :
  Z.of_nat i < 18446744073709551616 -> Z.of_nat j < 18446744073709551616 ->
  pa_add a i = pa_add a j -> i = j.
Proof.
  intros Hi Hj Heq.
  apply pa_unsigned_of_eq in Heq.
  rewrite !pa_add_unsigned in Heq. unfold bv_wrap in Heq. rewrite vq_mod64 in Heq.
  assert (Hz : Z.of_nat i = Z.of_nat j)
    by (apply (vq_wrap_cancel (bv_unsigned (a : SailStdpp.Values.mword 64)));
        [ lia | lia | exact Heq ]).
  lia.
Qed.

Lemma pa_add_zero (a : Arch.pa) : pa_add a 0%nat = a.
Proof.
  apply pa_eq_of_unsigned. rewrite (pa_add_unsigned a 0).
  change (Z.of_nat 0) with 0. rewrite Z.add_0_r. apply bv_wrap_bv_unsigned.
Qed.

Lemma pa_add_add (a : Arch.pa) (i j : nat) :
  pa_add (pa_add a i) j = pa_add a (i + j).
Proof.
  apply pa_eq_of_unsigned. rewrite !pa_add_unsigned, bv_wrap_add_idemp_l.
  f_equal. lia.
Qed.

Lemma pa_off_add (a : Arch.pa) (z : Z) (j : nat) :
  pa_add (pa_off a z) j = pa_add a (Z.to_nat z + j).
Proof. unfold pa_off. apply pa_add_add. Qed.

Lemma pa_off_off (a : Arch.pa) (z1 z2 : Z) :
  0 <= z1 -> 0 <= z2 -> pa_off (pa_off a z1) z2 = pa_off a (z1 + z2).
Proof. intros H1 H2. unfold pa_off. rewrite pa_add_add. f_equal. lia. Qed.

(* -- domains of the byte-writing primitives -- *)

Lemma foldr_ins_dom {A : Type} (f : A -> Arch.pa) (g : A -> bv 8) (l : list A)
    (mm : gmap Arch.pa (bv 8)) :
  dom (foldr (fun x acc => <[ f x := g x ]> acc) mm l)
  = list_to_set (f <$> l) ∪ dom mm.
Proof.
  induction l as [|x l IH].
  - cbn [foldr fmap list_fmap list_to_set]. set_solver.
  - cbn [foldr fmap list_fmap list_to_set].
    rewrite dom_insert_L. rewrite IH. set_solver.
Qed.

Lemma foldr_ins_dom_sub {A : Type} (f : A -> Arch.pa) (g : A -> bv 8) (l : list A)
    (mm : gmap Arch.pa (bv 8)) (X : gset Arch.pa) :
  dom mm ⊆ X -> (forall x, x ∈ l -> f x ∈ X) ->
  dom (foldr (fun x acc => <[ f x := g x ]> acc) mm l) ⊆ X.
Proof.
  intros Hm Hl. rewrite (foldr_ins_dom f g l mm). apply union_least; [|exact Hm].
  intros y Hy. apply elem_of_list_to_set, elem_of_list_fmap in Hy as (x & -> & Hx).
  exact (Hl x Hx).
Qed.

Lemma write_byte_list_dom_sub (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa)
    (bs : list (bv 8)) (X : gset Arch.pa) :
  dom mm ⊆ X -> (forall j : nat, (j < length bs)%nat -> pa_add pa j ∈ X) ->
  dom (write_byte_list mm pa bs) ⊆ X.
Proof.
  intros Hm Hj. unfold write_byte_list.
  apply (foldr_ins_dom_sub (fun jb => pa_add pa (fst jb)) snd); [exact Hm|].
  intros x Hx. apply elem_of_list_lookup in Hx as (i & Hi).
  rewrite list_lookup_imap in Hi.
  destruct (bs !! i) as [b|] eqn:Hb; [| discriminate ].
  cbn in Hi. injection Hi as <-. cbn [fst].
  apply Hj. apply lookup_lt_Some in Hb. exact Hb.
Qed.

(* -- reads: monotone in the map, build one from its bytes -- *)

(* [RiscvModelBytes.nth_byte_assemble_len], restated locally: the assembled
   word of a byte list reproduces those bytes at any width wide enough. *)
Lemma vq_nth_byte_assemble (m : N) (bs : list (bv 8)) (j : nat) :
  8 * Z.of_nat (length bs) <= Z.of_N m -> (j < length bs)%nat ->
  nth_byte (Z_to_bv m (assemble_bytes bs) : bv m) j = bs !!! j.
Proof.
  intros Hlen Hj. apply bv_eq. rewrite nth_byte_unsigned, Z_to_bv_unsigned.
  pose proof (assemble_bytes_bound bs) as [Hlo Hhi].
  assert (Hws : bv_wrap m (assemble_bytes bs) = assemble_bytes bs).
  { apply bv_wrap_small. unfold bv_modulus. split; [lia|].
    eapply Z.lt_le_trans; [exact Hhi|]. apply Z.pow_le_mono_r; lia. }
  rewrite Hws.
  assert (Hab : (assemble_bytes bs ≫ Z.of_nat (8 * j)) `mod` 2 ^ 8
                = bv_unsigned (bs !!! j)) by (apply assemble_bytes_byte; lia).
  rewrite <- Hab. f_equal. f_equal. lia.
Qed.

Lemma mapM_lookup_mono (m1 m2 : gmap Arch.pa (bv 8)) (f : nat -> Arch.pa)
    (l : list nat) (bs : list (bv 8)) :
  m1 ⊆ m2 ->
  mapM (fun j : nat => m1 !! f j) l = Some bs ->
  mapM (fun j : nat => m2 !! f j) l = Some bs.
Proof.
  intros Hs Hm. apply mapM_Some. apply mapM_Some in Hm.
  eapply Forall2_impl; [| exact Hm ].
  intros x y Hxy. exact (lookup_weaken _ _ _ _ Hxy Hs).
Qed.

Lemma read_bytes_mono (m1 m2 : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
    (w : bv (8 * n)) :
  m1 ⊆ m2 -> read_bytes m1 pa n = Some w -> read_bytes m2 pa n = Some w.
Proof.
  intros Hs. unfold read_bytes.
  destruct (mapM (fun j : nat => m1 !! pa_add pa j) (seq 0 (N.to_nat n)))
    as [bs|] eqn:Hm; [|discriminate].
  rewrite (mapM_lookup_mono m1 m2 (pa_add pa) _ bs Hs Hm). exact id.
Qed.

Lemma read_byte_list_mono (m1 m2 : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : nat)
    (bs : list (bv 8)) :
  m1 ⊆ m2 -> read_byte_list m1 pa n = Some bs -> read_byte_list m2 pa n = Some bs.
Proof. intro Hs. unfold read_byte_list. apply mapM_lookup_mono. exact Hs. Qed.

Lemma read_bytes_of_list (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
    (v : bv (8 * n)) :
  (forall j : nat, (N.of_nat j < n)%N -> mm !! pa_add pa j = Some (nth_byte v j)) ->
  read_bytes mm pa n = Some v.
Proof.
  intros Hb.
  set (bs := (fun j : nat => nth_byte v j) <$> seq 0 (N.to_nat n)).
  assert (Hlen : length bs = N.to_nat n)
    by (subst bs; rewrite length_fmap, length_seq; reflexivity).
  assert (Hm : mapM (fun j : nat => mm !! pa_add pa j) (seq 0 (N.to_nat n)) = Some bs).
  { apply mapM_Some. subst bs. apply Forall2_fmap_r.
    apply Forall_Forall2_diag, Forall_forall. intros j Hj.
    apply elem_of_list_In, elem_of_seq in Hj. apply Hb. lia. }
  unfold read_bytes. rewrite Hm. f_equal.
  apply bv_eq_of_bytes. intros j Hj.
  assert (Hjl : (j < length bs)%nat) by lia.
  assert (Hb1 : 8 * Z.of_nat (length bs) <= Z.of_N (8 * n)).
  { rewrite Hlen, N2Z.inj_mul. lia. }
  rewrite (vq_nth_byte_assemble (8 * n) bs j Hb1 Hjl).
  assert (Hlk : bs !! j = Some (nth_byte v j)).
  { subst bs. rewrite list_lookup_fmap, lookup_seq_lt by lia. reflexivity. }
  apply list_lookup_total_correct. exact Hlk.
Qed.

(* -- read-after-write, at the same address and width -- *)

Lemma wb_gen_lookup {w : N} (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (v : bv w)
    (l : list nat) (j : nat) :
  (forall i : nat, i ∈ l -> Z.of_nat i < 18446744073709551616) ->
  Z.of_nat j < 18446744073709551616 -> j ∈ l ->
  foldr (fun i acc => <[ pa_add pa i := nth_byte v i ]> acc) mm l !! pa_add pa j
  = Some (nth_byte v j).
Proof.
  induction l as [|i l IH]; intros Hb Hj Hin.
  { exfalso. exact (not_elem_of_nil j Hin). }
  simpl. destruct (decide (i = j)) as [->|Hne].
  - apply lookup_insert.
  - rewrite lookup_insert_ne.
    + apply IH.
      * intros k Hk. apply Hb, elem_of_list_further, Hk.
      * exact Hj.
      * apply elem_of_cons in Hin as [->|Hin]; [ done | exact Hin ].
    + intro Heq. apply Hne.
      apply (pa_add_inj pa i j); [ apply Hb, elem_of_list_here | exact Hj | exact Heq ].
Qed.

Lemma write_bytes_lookup {w : N} (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
    (v : bv w) (j : nat) :
  Z.of_N n < 18446744073709551616 -> (N.of_nat j < n)%N ->
  write_bytes mm pa n v !! pa_add pa j = Some (nth_byte v j).
Proof.
  intros Hn Hj. unfold write_bytes. apply wb_gen_lookup.
  - intros i Hi. apply elem_of_seq in Hi. lia.
  - lia.
  - apply elem_of_seq. lia.
Qed.

Lemma read_write_bytes (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
    (v : bv (8 * n)) :
  Z.of_N n < 18446744073709551616 ->
  read_bytes (write_bytes mm pa n v) pa n = Some v.
Proof.
  intro Hn. apply read_bytes_of_list. intros j Hj.
  apply write_bytes_lookup; [exact Hn | exact Hj].
Qed.

(* ---------------------------------------------------------------------- *)
(* 0. Sequence numbers and geometry.                                      *)
(* ---------------------------------------------------------------------- *)

Definition wrap16 (p : nat) : bv 16 := Z_to_bv 16 (Z.of_nat p).

Lemma wrap16_S (p : nat) : wrap16 (S p) = bv_add (wrap16 p) (Z_to_bv 16 1).
Proof.
  unfold wrap16. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r.
  apply f_equal2; [lia | reflexivity].
Qed.

(* injectivity of [wrap16] within any window of width < 2^16 *)
Lemma wrap16_inj_window (p q : nat) :
  (p < q)%nat -> Z.of_nat q - Z.of_nat p < 65536 -> wrap16 p <> wrap16 q.
Proof.
  intros Hlt Hw Heq.
  unfold wrap16 in Heq.
  apply bv_eq in Heq. rewrite !Z_to_bv_unsigned in Heq.
  unfold bv_wrap, bv_modulus in Heq.
  change (2 ^ Z.of_N 16) with 65536 in Heq.
  assert (Hd : (Z.of_nat q - Z.of_nat p) `mod` 65536 = 0).
  { rewrite Zminus_mod, Heq, Z.sub_diag. reflexivity. }
  assert (Hqp : 0 <= Z.of_nat q - Z.of_nat p < 65536) by lia.
  rewrite (Z.mod_small _ _ Hqp) in Hd. lia.
Qed.

(* all the per-position geometry is for the ONLY configuration xv6 ever
   makes live: queue size 8 *)
Definition ring_entry_pa (c : virtio_cfg) (p : nat) : Arch.pa :=
  pa_off (vc_avail c) (vq_avail_ring_off + 2 * (Z.of_nat p `mod` 8)).
Definition used_elem_pa (c : virtio_cfg) (p : nat) : Arch.pa :=
  pa_off (vc_used c) (vq_used_ring_off + vq_used_elem_size * (Z.of_nat p `mod` 8)).
Definition avail_idx_pa (c : virtio_cfg) : Arch.pa :=
  pa_off (vc_avail c) vq_idx_off.
Definition used_idx_pa (c : virtio_cfg) : Arch.pa :=
  pa_off (vc_used c) vq_idx_off.

Definition pa_range (a : Arch.pa) (n : nat) : gset Arch.pa :=
  list_to_set ((fun j : nat => pa_add a j) <$> seq 0 n).

Definition avail_idx_dom (c : virtio_cfg) : gset Arch.pa :=
  pa_range (avail_idx_pa c) 2.
Definition used_page_pas (c : virtio_cfg) : gset Arch.pa :=
  pa_range (vc_used c) 4096.

(* -- [pa_range] and the byte primitives' footprints -- *)

Lemma pa_range_intro (a : Arch.pa) (n j : nat) :
  (j < n)%nat -> pa_add a j ∈ pa_range a n.
Proof.
  intro Hj. unfold pa_range. apply elem_of_list_to_set, elem_of_list_fmap.
  exists j. split; [reflexivity|]. apply elem_of_seq. lia.
Qed.

Lemma pa_range_elim (a : Arch.pa) (n : nat) (x : Arch.pa) :
  x ∈ pa_range a n -> exists j, (j < n)%nat /\ x = pa_add a j.
Proof.
  unfold pa_range. intro Hx.
  apply elem_of_list_to_set, elem_of_list_fmap in Hx as (j & -> & Hj).
  apply elem_of_seq in Hj. exists j. split; [lia|reflexivity].
Qed.

Lemma pa_off_range (a : Arch.pa) (z : Z) (j n : nat) :
  0 <= z -> z + Z.of_nat j < Z.of_nat n -> pa_add (pa_off a z) j ∈ pa_range a n.
Proof. intros Hz Hlt. rewrite pa_off_add. apply pa_range_intro. lia. Qed.

Lemma write_bytes_dom {w : N} (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
    (v : bv w) :
  dom (write_bytes mm pa n v) = pa_range pa (N.to_nat n) ∪ dom mm.
Proof.
  unfold write_bytes, pa_range. apply (foldr_ins_dom (pa_add pa) (nth_byte v)).
Qed.

Lemma write_bytes_dom_sub {w : N} (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
    (v : bv w) (X : gset Arch.pa) :
  dom mm ⊆ X -> (forall j : nat, (j < N.to_nat n)%nat -> pa_add pa j ∈ X) ->
  dom (write_bytes mm pa n v) ⊆ X.
Proof.
  intros Hm Hj. rewrite write_bytes_dom. apply union_least; [|exact Hm].
  intros x Hx. apply pa_range_elim in Hx as (j & Hjn & ->). exact (Hj j Hjn).
Qed.

Lemma read_bytes_dom_sub (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
    (w : bv (8 * n)) :
  read_bytes mm pa n = Some w -> pa_range pa (N.to_nat n) ⊆ dom mm.
Proof.
  intros Hr x Hx. apply pa_range_elim in Hx as (j & Hj & ->).
  apply elem_of_dom. exists (nth_byte w j).
  apply (read_bytes_spec mm pa n w Hr j). lia.
Qed.

(* the avail-ring index field, as a 2-byte map holding [wrap16 np] *)
Definition avail_idx_bytes (c : virtio_cfg) (np : nat) : gmap Arch.pa (bv 8) :=
  write_bytes ∅ (avail_idx_pa c) 2 (wrap16 np).

(* 2^16 is a multiple of the queue size 8, so the mod-8 ring arithmetic
   commutes with the 16-bit wrap. *)
Lemma vq_mod_65536_8 (x : Z) : (x `mod` 65536) `mod` 8 = x `mod` 8.
Proof.
  rewrite (Z.mod_eq x 65536) by lia.
  replace (x - 65536 * (x / 65536)) with (x + (- (8192 * (x / 65536))) * 8) by lia.
  apply Z_mod_plus_full.
Qed.

Lemma pa_range_base (a : Arch.pa) (n : nat) : (0 < n)%nat -> a ∈ pa_range a n.
Proof. intro Hn. rewrite <- (pa_add_zero a) at 1. apply pa_range_intro. lia. Qed.

Lemma avail_idx_bytes_dom (c : virtio_cfg) (np : nat) :
  dom (avail_idx_bytes c np) = avail_idx_dom c.
Proof.
  unfold avail_idx_bytes, avail_idx_dom. rewrite write_bytes_dom.
  change (N.to_nat 2) with 2%nat. rewrite dom_empty_L. set_solver.
Qed.

Lemma avail_idx_bytes_read (c : virtio_cfg) (np : nat) :
  read_bytes (avail_idx_bytes c np) (avail_idx_pa c) 2 = Some (wrap16 np).
Proof.
  unfold avail_idx_bytes. apply read_write_bytes. lia.
Qed.

(* [avail_ring_at] at a wrapped position reads the per-position ring entry:
   2^16 is divisible by the queue size 8, so the mod-8 arithmetic commutes
   with the wrap. *)
Lemma avail_ring_at_wrap (c : virtio_cfg) (mv : vmem) (p : nat) :
  vc_qnum c = Z_to_bv 32 8 ->
  avail_ring_at c mv (wrap16 p) = view_word mv (ring_entry_pa c p) 2.
Proof.
  intro Hq. unfold avail_ring_at, ring_entry_pa. rewrite Hq.
  assert (Hq8 : bv_unsigned (Z_to_bv 32 8) = 8) by (vm_compute; reflexivity).
  rewrite Hq8.
  assert (Hm : bv_unsigned (wrap16 p) `mod` 8 = Z.of_nat p `mod` 8).
  { unfold wrap16. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 16) with 65536. apply vq_mod_65536_8. }
  rewrite Hm. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 1. One slot: the pinned request.                                       *)
(* ---------------------------------------------------------------------- *)

Record vslot := VSlot {
  vs_req  : vio_req;         (* the parsed request; type is IN or OUT *)
  (* THE BLOCK'S CONTENT, as the DRIVER asserts it: for an OUT request the
     pinned payload it is about to write; for an IN request the content the
     block already has (the driver owns the disk points-to, so it knows).
     Recording it for IN too is what makes [slot_pend_res]'s disk fragments
     identifiable when the publisher collects its payoff -- an existentially
     quantified list there would come back opaque and no read could be tied
     back to the caller's [disk_block]. *)
  vs_data : list (bv 8);
}.

Definition vs_is_out (sl : vslot) : bool :=
  bv_unsigned (vr_type (vs_req sl)) =? virtio_blk_t_out.
Definition vs_sector_off (sl : vslot) : Z :=
  bv_unsigned (vr_sector (vs_req sl)) * virtio_sector_size.
Definition vs_len (sl : vslot) : nat :=
  Z.to_nat (bv_unsigned (vr_len (vs_req sl))).

(* What one slot's pin has to say.  The pin is a sub-map of the lease's
   control region; [slot_pin_ok] makes the request a FUNCTION of it: every
   bus view that agrees with the pin parses position [p] to exactly
   [vs_req sl], and (for a write request) reads exactly [vs_data sl] out of
   the data buffer.  The ring-entry clause is stated separately because the
   window argument (positions in flight pin DISTINCT ring entries, so there
   are at most 8 of them) keys off it. *)
Record slot_pin_ok (c : virtio_cfg) (p : nat) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) : Prop := {
  spo_ring : read_bytes pin (ring_entry_pa c p) 2 = Some (vr_head (vs_req sl));
  spo_type : bv_unsigned (vr_type (vs_req sl)) = virtio_blk_t_in
             \/ bv_unsigned (vr_type (vs_req sl)) = virtio_blk_t_out;
  spo_len  : bv_unsigned (vr_len (vs_req sl)) = 1024;
  spo_out  : vs_is_out sl = true ->
             read_byte_list pin (vr_buf (vs_req sl)) 1024 = Some (vs_data sl);
  (* STATEMENT ADJUSTED (2026-07-28): the status byte must not lie INSIDE the
     data buffer.  For a read request the device writes the buffer AFTER the
     status byte ([virtio_complete]), so without this the completed request's
     status byte would hold a data byte and the driver could not conclude
     "status = OK" at reclaim.  It is a genuine well-formedness condition on
     the published chain (xv6's status lives in [struct disk], the buffer in a
     [struct buf]), so it belongs here, next to the other chain conditions. *)
  spo_stat : vs_is_out sl = false ->
             vr_status (vs_req sl) ∉ pa_range (vr_buf (vs_req sl)) (vs_len sl);
  spo_req  : forall mv : vmem, mem_view pin mv ->
             req_at c mv (wrap16 p) = Some (vs_req sl);
}.

(* the slot's WRITABLE footprint: the status byte, and (for a read request,
   where the device writes the data) the whole buffer *)
Definition slot_wr (sl : vslot) : gset Arch.pa :=
  {[ vr_status (vs_req sl) ]} ∪
  (if vs_is_out sl then ∅ else pa_range (vr_buf (vs_req sl)) (vs_len sl)).

Definition slot_fp (sl : vslot) (pin : gmap Arch.pa (bv 8)) : gset Arch.pa :=
  dom pin ∪ slot_wr sl.

Lemma slot_fp_pin (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  dom pin ⊆ slot_fp sl pin.
Proof. unfold slot_fp. apply union_subseteq_l. Qed.

Lemma slot_fp_wr (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  slot_wr sl ⊆ slot_fp sl pin.
Proof. unfold slot_fp. apply union_subseteq_r. Qed.

(* -- the determined completion -- *)

Definition vslot_post (v : virtio_state) (sl : vslot) : virtio_state :=
  VirtioState (v_cfg v)
              (bv_or (v_isr v) (Z_to_bv 32 vio_isr_used_buffer))
              (bv_add (v_seen v) (Z_to_bv 16 1))
              (bv_add (v_used_idx v) (Z_to_bv 16 1))
              (if vs_is_out sl
               then disk_write (v_disk v) (vs_sector_off sl) (vs_data sl)
               else v_disk v).

Definition vslot_writes (c : virtio_cfg) (ui : bv 16) (dk : Z -> bv 8)
    (sl : vslot) : gmap Arch.pa (bv 8) :=
  let r := vs_req sl in
  let ws := <[ vr_status r := Z_to_bv 8 virtio_blk_s_ok ]>
              (virtio_used_writes c ui r) in
  if vs_is_out sl then ws
  else write_byte_list ws (vr_buf r) (disk_read dk (vs_sector_off sl) (vs_len sl)).

Lemma disk_read_length (dk : Z -> bv 8) (off : Z) (n : nat) :
  length (disk_read dk off n) = n.
Proof. unfold disk_read. rewrite length_fmap, length_seq. reflexivity. Qed.

(* The used-ring report always lands in the used PAGE: with queue size 8 the
   element is at [used + 4 + 8*(ui mod 8)] (at most 60) and the index field at
   [used + 2], so 4096 bytes cover every [ui]. *)
Lemma virtio_used_writes_dom (c : virtio_cfg) (ui : bv 16) (r : vio_req) :
  vc_qnum c = Z_to_bv 32 8 ->
  dom (virtio_used_writes c ui r) ⊆ used_page_pas c.
Proof.
  intro Hq. unfold virtio_used_writes. cbv zeta. rewrite Hq.
  assert (Hq8 : bv_unsigned (Z_to_bv 32 8) = 8) by (vm_compute; reflexivity).
  rewrite Hq8.
  pose proof (Z.mod_pos_bound (bv_unsigned ui) 8 ltac:(lia)) as [Hs0 Hs1].
  assert (H4096 : Z.of_nat 4096 = 4096) by (vm_compute; reflexivity).
  unfold used_page_pas, vq_used_ring_off, vq_used_elem_size, vq_idx_off.
  apply write_bytes_dom_sub.
  - apply write_bytes_dom_sub.
    + apply write_bytes_dom_sub.
      * rewrite dom_empty_L. apply empty_subseteq.
      * intros j Hj. change (N.to_nat 4) with 4%nat in Hj.
        apply pa_off_range; [lia|]. rewrite H4096. lia.
    + intros j Hj. change (N.to_nat 4) with 4%nat in Hj.
      rewrite pa_off_off by lia. apply pa_off_range; [lia|].
      rewrite H4096. lia.
  - intros j Hj. change (N.to_nat 2) with 2%nat in Hj.
    apply pa_off_range; [lia|]. rewrite H4096. lia.
Qed.

(* the determined write set stays inside the slot's writable footprint and the
   used page -- the two regions the lease hands the device *)
Lemma vslot_writes_dom_sub (c : virtio_cfg) (p : nat) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) (ui : bv 16) (dk : Z -> bv 8) :
  vc_qnum c = Z_to_bv 32 8 -> slot_pin_ok c p sl pin ->
  dom (vslot_writes c ui dk sl) ⊆ slot_wr sl ∪ used_page_pas c.
Proof.
  intros Hq Hslot. unfold vslot_writes. cbv zeta.
  pose proof (virtio_used_writes_dom c ui (vs_req sl) Hq) as Hused.
  assert (Hws : dom (<[ vr_status (vs_req sl) := Z_to_bv 8 virtio_blk_s_ok ]>
                       (virtio_used_writes c ui (vs_req sl)))
                ⊆ slot_wr sl ∪ used_page_pas c).
  { rewrite dom_insert_L. apply union_least.
    - apply singleton_subseteq_l, elem_of_union_l.
      unfold slot_wr. apply elem_of_union_l, elem_of_singleton. reflexivity.
    - etransitivity; [ exact Hused | apply union_subseteq_r ]. }
  destruct (vs_is_out sl) eqn:Hout; [exact Hws|].
  apply write_byte_list_dom_sub; [exact Hws|].
  intros j Hj. rewrite disk_read_length in Hj.
  apply elem_of_union_l. unfold slot_wr. rewrite Hout.
  apply elem_of_union_r, pa_range_intro. exact Hj.
Qed.

(* THE determinism fact: at a pinned slot the device's completion is a
   function of the slot alone (the only view-dependence [virtio_complete] has
   left is the OUT payload, and [spo_out] fixes that). *)
Lemma vslot_complete (c : virtio_cfg) (p : nat) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) (mv : vmem) (v : virtio_state) :
  slot_pin_ok c p sl pin -> mem_view pin mv -> v_cfg v = c ->
  virtio_complete v mv (vs_req sl)
  = (vslot_post v sl, vslot_writes c (v_used_idx v) (v_disk v) sl).
Proof.
  intros Hslot Hview Hcfg.
  pose proof (spo_type _ _ _ _ Hslot) as Htype.
  pose proof (spo_len _ _ _ _ Hslot) as Hlen.
  unfold virtio_complete, vslot_post, vslot_writes, vs_is_out, vs_sector_off, vs_len.
  cbv zeta. rewrite Hcfg.
  destruct Htype as [Hin|Hout].
  - rewrite Hin. unfold virtio_blk_t_in, virtio_blk_t_out.
    cbn [Z.eqb orb Pos.eqb]. reflexivity.
  - assert (Hout' : vs_is_out sl = true)
      by (unfold vs_is_out; rewrite Hout; unfold virtio_blk_t_out; reflexivity).
    pose proof (spo_out _ _ _ _ Hslot Hout') as Hro.
    pose proof (view_bytes_read pin mv (vr_buf (vs_req sl)) 1024 (vs_data sl)
                  Hview Hro) as Hvb.
    rewrite Hout. unfold virtio_blk_t_in, virtio_blk_t_out.
    cbn [Z.eqb orb Pos.eqb]. rewrite Hlen.
    assert (H1024 : Z.to_nat 1024 = 1024%nat) by (vm_compute; reflexivity).
    rewrite H1024, Hvb. reflexivity.
Qed.

(* ...and hence the step at a pinned slot, when it fires, is that function *)
Lemma vslot_req_step (c : virtio_cfg) (p : nat) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) (mv : vmem) (v v' : virtio_state)
    (w : gmap Arch.pa (bv 8)) :
  slot_pin_ok c p sl pin -> mem_view pin mv ->
  v_cfg v = c -> v_seen v = wrap16 p ->
  virtio_req_step v mv = Some (v', w) ->
  v' = vslot_post v sl /\ w = vslot_writes c (v_used_idx v) (v_disk v) sl.
Proof.
  intros Hslot Hview Hcfg Hseen Hstep.
  unfold virtio_req_step in Hstep.
  destruct (negb (virtio_pending v mv)); [discriminate|].
  rewrite Hcfg, Hseen, (spo_req _ _ _ _ Hslot mv Hview) in Hstep.
  rewrite (vslot_complete c p sl pin mv v Hslot Hview Hcfg) in Hstep.
  injection Hstep as Hv Hw. split; [ symmetry; exact Hv | symmetry; exact Hw ].
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The keyed protocol state and its obligation.                        *)
(* ---------------------------------------------------------------------- *)

Record vproto := VProto {
  vp_nc   : nat;                                (* completed count *)
  vp_np   : nat;                                (* published count *)
  vp_pend : gmap nat vslot;                     (* dom = [nc, np), contiguous *)
  vp_done : gmap nat vslot;                     (* dom ⊆ [_, nc) *)
  vp_pin  : gmap nat (gmap Arch.pa (bv 8));     (* per-slot pins *)
}.

Definition vp_slots (pr : vproto) : gmap nat vslot :=
  vp_pend pr ∪ vp_done pr.

(* the control region this state pins: the published index plus every pin *)
Definition pins_union (pins : gmap nat (gmap Arch.pa (bv 8)))
  : gmap Arch.pa (bv 8) :=
  map_fold (fun _ pin acc => pin ∪ acc) ∅ pins.

Definition vproto_ctl (c : virtio_cfg) (pr : vproto) : gmap Arch.pa (bv 8) :=
  avail_idx_bytes c (vp_np pr) ∪ pins_union (vp_pin pr).

Record vproto_ok (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa) : Prop := {
  vpo_qnum : vc_qnum c = Z_to_bv 32 8;
  vpo_live : virtio_live c = true;
  vpo_ncnp : (vp_nc pr <= vp_np pr)%nat;
  vpo_pend_dom : dom (vp_pend pr) = set_seq (vp_nc pr) (vp_np pr - vp_nc pr);
  vpo_done_lt : forall p, p ∈ dom (vp_done pr) -> (p < vp_nc pr)%nat;
  vpo_pin_dom : dom (vp_pin pr) = dom (vp_pend pr) ∪ dom (vp_done pr);
  vpo_slot : forall p sl pin,
      vp_slots pr !! p = Some sl -> vp_pin pr !! p = Some pin ->
      slot_pin_ok c p sl pin;
  (* footprints: pairwise disjoint, self-disjoint (a slot's writable bytes
     are not its own pin), and away from the standing regions *)
  vpo_fp_disj : forall p q slp slq pinp pinq,
      p <> q ->
      vp_slots pr !! p = Some slp -> vp_pin pr !! p = Some pinp ->
      vp_slots pr !! q = Some slq -> vp_pin pr !! q = Some pinq ->
      slot_fp slp pinp ## slot_fp slq pinq;
  vpo_wr_pin : forall p sl pin,
      vp_slots pr !! p = Some sl -> vp_pin pr !! p = Some pin ->
      slot_wr sl ## dom pin;
  vpo_standing : forall p sl pin,
      vp_slots pr !! p = Some sl -> vp_pin pr !! p = Some pin ->
      slot_fp sl pin ## (avail_idx_dom c ∪ used_page_pas c);
  vpo_idx_used : avail_idx_dom c ## used_page_pas c;
  (* everything inside the lease *)
  vpo_fp_D : forall p sl pin,
      vp_slots pr !! p = Some sl -> vp_pin pr !! p = Some pin ->
      slot_fp sl pin ⊆ D;
  vpo_used_D : used_page_pas c ⊆ D;
  vpo_idx_D : avail_idx_dom c ⊆ D;
}.

(* pend and done never overlap (done is strictly below nc, pend at or above) *)
Lemma vproto_pend_done_disj (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa) :
  vproto_ok c pr D -> dom (vp_pend pr) ## dom (vp_done pr).
Proof.
  intro Hok. apply elem_of_disjoint. intros x Hx Hy.
  rewrite (vpo_pend_dom _ _ _ Hok) in Hx. apply elem_of_set_seq in Hx.
  pose proof (vpo_done_lt _ _ _ Hok x Hy). lia.
Qed.

(* each slot's pin is inside the control map *)
Lemma pins_union_lookup (pins : gmap nat (gmap Arch.pa (bv 8))) (p : nat)
    (pin : gmap Arch.pa (bv 8)) :
  (forall q1 q2 m1 m2, q1 <> q2 -> pins !! q1 = Some m1 -> pins !! q2 = Some m2 ->
     dom m1 ## dom m2) ->
  pins !! p = Some pin -> pin ⊆ pins_union pins.
Proof.
  revert p pin. unfold pins_union.
  apply (map_fold_weak_ind
           (fun (acc : gmap Arch.pa (bv 8)) (m : gmap nat (gmap Arch.pa (bv 8))) =>
              forall (p : nat) (pin : gmap Arch.pa (bv 8)),
                (forall q1 q2 m1 m2, q1 <> q2 -> m !! q1 = Some m1 ->
                   m !! q2 = Some m2 -> dom m1 ## dom m2) ->
                m !! p = Some pin -> pin ⊆ acc)).
  - intros p pin _ Hp. rewrite lookup_empty in Hp. discriminate.
  - intros i x m r Hi IH p pin Hdisj Hp.
    destruct (decide (p = i)) as [->|Hne].
    + rewrite lookup_insert in Hp. injection Hp as <-. apply map_union_subseteq_l.
    + rewrite lookup_insert_ne in Hp by congruence.
      assert (Hsub : pin ⊆ r).
      { apply (IH p pin); [| exact Hp ].
        intros q1 q2 m1 m2 Hq Hm1 Hm2. apply (Hdisj q1 q2).
        - exact Hq.
        - rewrite lookup_insert_ne; [exact Hm1|].
          intros Hc. rewrite <- Hc, Hi in Hm1. discriminate.
        - rewrite lookup_insert_ne; [exact Hm2|].
          intros Hc. rewrite <- Hc, Hi in Hm2. discriminate. }
      apply virtio_ctl_union; [| exact Hsub ].
      apply (Hdisj i p x pin).
      * congruence.
      * apply lookup_insert.
      * rewrite lookup_insert_ne; [exact Hp|]. congruence.
Qed.

(* the dual direction, needed to keep the device's writes off the pins *)
Lemma pins_union_dom_inv (pins : gmap nat (gmap Arch.pa (bv 8))) (a : Arch.pa) :
  a ∈ dom (pins_union pins) ->
  exists q m, pins !! q = Some m /\ a ∈ dom m.
Proof.
  revert a. unfold pins_union.
  apply (map_fold_weak_ind
           (fun (acc : gmap Arch.pa (bv 8)) (m : gmap nat (gmap Arch.pa (bv 8))) =>
              forall a : Arch.pa, a ∈ dom acc ->
                exists q mq, m !! q = Some mq /\ a ∈ dom mq)).
  - intros a Ha. rewrite dom_empty_L in Ha. exfalso.
    exact (proj1 (elem_of_empty a) Ha).
  - intros i x m r Hi IH a Ha. rewrite dom_union_L in Ha.
    apply elem_of_union in Ha as [Ha|Ha].
    + exists i, x. split; [apply lookup_insert | exact Ha].
    + destruct (IH a Ha) as (q & mq & Hq & Hmq). exists q, mq. split; [|exact Hmq].
      rewrite lookup_insert_ne; [exact Hq|].
      intros Hc. rewrite <- Hc, Hi in Hq. discriminate.
Qed.

(* joining one more pin, and peeling one off: both need pairwise disjointness
   (the fold only commutes there) *)
Lemma pins_union_insert (pins : gmap nat (gmap Arch.pa (bv 8))) (p : nat)
    (pin : gmap Arch.pa (bv 8)) :
  pins !! p = None ->
  (forall q1 q2 m1 m2, q1 <> q2 ->
     <[ p := pin ]> pins !! q1 = Some m1 -> <[ p := pin ]> pins !! q2 = Some m2 ->
     m1 ##ₘ m2) ->
  pins_union (<[ p := pin ]> pins) = pin ∪ pins_union pins.
Proof.
  intros Hp Hdisj. unfold pins_union.
  assert (Hcomm : forall (j1 j2 : nat) (z1 z2 y : gmap Arch.pa (bv 8)),
            j1 <> j2 ->
            <[ p := pin ]> pins !! j1 = Some z1 ->
            <[ p := pin ]> pins !! j2 = Some z2 ->
            z1 ∪ (z2 ∪ y) = z2 ∪ (z1 ∪ y)).
  { intros j1 j2 z1 z2 y Hj Hz1 Hz2. rewrite !map_union_assoc. f_equal.
    apply map_union_comm. exact (Hdisj j1 j2 z1 z2 Hj Hz1 Hz2). }
  exact (map_fold_insert_L
           (fun (_ : nat) (m0 acc : gmap Arch.pa (bv 8)) => m0 ∪ acc)
           ∅ p pin pins Hcomm Hp).
Qed.

Lemma pins_union_delete (pins : gmap nat (gmap Arch.pa (bv 8))) (p : nat)
    (pin : gmap Arch.pa (bv 8)) :
  pins !! p = Some pin ->
  (forall q1 q2 m1 m2, q1 <> q2 -> pins !! q1 = Some m1 -> pins !! q2 = Some m2 ->
     m1 ##ₘ m2) ->
  pins_union pins = pin ∪ pins_union (delete p pins).
Proof.
  intros Hp Hdisj.
  assert (Hpins : <[ p := pin ]> (delete p pins) = pins)
    by (apply insert_delete; exact Hp).
  transitivity (pins_union (<[ p := pin ]> (delete p pins)));
    [ rewrite Hpins; reflexivity | ].
  apply pins_union_insert; [ apply lookup_delete | ].
  rewrite Hpins. exact Hdisj.
Qed.

(* -- reading the protocol state's own bookkeeping -- *)

Lemma vproto_pend_slot (pr : vproto) (p : nat) (sl : vslot) :
  vp_pend pr !! p = Some sl -> vp_slots pr !! p = Some sl.
Proof. intro H. unfold vp_slots. apply lookup_union_Some_l. exact H. Qed.

Lemma vproto_slot_dom (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa) :
  vproto_ok c pr D -> dom (vp_pin pr) = dom (vp_slots pr).
Proof.
  intro Hok. unfold vp_slots. rewrite dom_union_L. exact (vpo_pin_dom _ _ _ Hok).
Qed.

Lemma vproto_slot_of_pin (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (p : nat) (pin : gmap Arch.pa (bv 8)) :
  vproto_ok c pr D -> vp_pin pr !! p = Some pin ->
  exists sl, vp_slots pr !! p = Some sl.
Proof.
  intros Hok Hpin.
  assert (Hd : p ∈ dom (vp_slots pr)).
  { rewrite <- (vproto_slot_dom c pr D Hok). apply elem_of_dom. exists pin. exact Hpin. }
  apply elem_of_dom in Hd. exact Hd.
Qed.

Lemma vproto_pins_disj (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa) :
  vproto_ok c pr D ->
  forall q1 q2 m1 m2, q1 <> q2 ->
    vp_pin pr !! q1 = Some m1 -> vp_pin pr !! q2 = Some m2 -> m1 ##ₘ m2.
Proof.
  intros Hok q1 q2 m1 m2 Hne H1 H2.
  destruct (vproto_slot_of_pin c pr D q1 m1 Hok H1) as [sl1 Hs1].
  destruct (vproto_slot_of_pin c pr D q2 m2 Hok H2) as [sl2 Hs2].
  pose proof (vpo_fp_disj _ _ _ Hok q1 q2 sl1 sl2 m1 m2 Hne Hs1 H1 Hs2 H2) as Hfp.
  apply map_disjoint_dom.
  apply (gset_disj_mono (dom m1) (slot_fp sl1 m1) (dom m2) (slot_fp sl2 m2));
    [ apply slot_fp_pin | apply slot_fp_pin | exact Hfp ].
Qed.

Lemma vproto_pin_ctl (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (p : nat) (pin : gmap Arch.pa (bv 8)) :
  vproto_ok c pr D -> vp_pin pr !! p = Some pin ->
  pin ⊆ vproto_ctl c pr.
Proof.
  intros Hok Hpin.
  assert (Hsub : pin ⊆ pins_union (vp_pin pr)).
  { apply (pins_union_lookup _ p); [| exact Hpin ].
    intros q1 q2 m1 m2 Hne H1 H2. apply map_disjoint_dom.
    exact (vproto_pins_disj c pr D Hok q1 q2 m1 m2 Hne H1 H2). }
  unfold vproto_ctl. apply virtio_ctl_union; [| exact Hsub ].
  rewrite avail_idx_bytes_dom.
  destruct (vproto_slot_of_pin c pr D p pin Hok Hpin) as [sl Hs].
  pose proof (vpo_standing _ _ _ Hok p sl pin Hs Hpin) as Hst.
  apply gset_disj_sym.
  apply (gset_disj_mono (dom pin) (slot_fp sl pin)
                        (avail_idx_dom c) (avail_idx_dom c ∪ used_page_pas c));
    [ apply slot_fp_pin | apply union_subseteq_l | exact Hst ].
Qed.

Lemma vproto_ctl_idx (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa) :
  vproto_ok c pr D ->
  read_bytes (vproto_ctl c pr) (avail_idx_pa c) 2 = Some (wrap16 (vp_np pr)).
Proof.
  intros _. unfold vproto_ctl.
  apply (read_bytes_mono (avail_idx_bytes c (vp_np pr)));
    [ apply map_union_subseteq_l | apply avail_idx_bytes_read ].
Qed.

(* THE window fact, from separation instead of arithmetic: every slot in
   flight pins its own avail-ring entry, the pins are disjoint, and there are
   only 8 ring entries -- so the window [min slot, np) has width at most 8,
   and in particular [np - nc <= 8]. *)
Lemma vproto_window (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa) :
  vproto_ok c pr D -> (vp_np pr - vp_nc pr <= 8)%nat.
Proof.
  intro Hok.
  destruct (decide (vp_np pr - vp_nc pr <= 8)%nat) as [Hle|Hgt]; [exact Hle|].
  exfalso.
  (* both [nc] and [nc+8] would be in flight, and they pin the SAME ring entry *)
  assert (Hget : forall q, (q < vp_np pr - vp_nc pr)%nat ->
            exists sl pin, vp_slots pr !! (vp_nc pr + q)%nat = Some sl
                           /\ vp_pin pr !! (vp_nc pr + q)%nat = Some pin
                           /\ ring_entry_pa c (vp_nc pr + q)%nat ∈ dom pin).
  { intros q Hq.
    assert (Hin : (vp_nc pr + q)%nat ∈ dom (vp_pend pr)).
    { rewrite (vpo_pend_dom _ _ _ Hok). apply elem_of_set_seq. lia. }
    apply elem_of_dom in Hin as [sl Hsl].
    assert (Hpd : (vp_nc pr + q)%nat ∈ dom (vp_pin pr)).
    { rewrite (vpo_pin_dom _ _ _ Hok). apply elem_of_union_l, elem_of_dom.
      exists sl. exact Hsl. }
    apply elem_of_dom in Hpd as [pin Hpin].
    pose proof (vproto_pend_slot pr _ _ Hsl) as Hs.
    exists sl, pin. split; [exact Hs|]. split; [exact Hpin|].
    pose proof (spo_ring _ _ _ _ (vpo_slot _ _ _ Hok _ sl pin Hs Hpin)) as Hr.
    apply (read_bytes_dom_sub pin (ring_entry_pa c (vp_nc pr + q)%nat) 2 _ Hr).
    apply pa_range_base. change (N.to_nat 2) with 2%nat. lia. }
  destruct (Hget 0%nat ltac:(lia)) as (sl1 & pin1 & Hs1 & Hp1 & Hd1).
  destruct (Hget 8%nat ltac:(lia)) as (sl2 & pin2 & Hs2 & Hp2 & Hd2).
  assert (Hring : ring_entry_pa c (vp_nc pr + 8)%nat
                  = ring_entry_pa c (vp_nc pr + 0)%nat).
  { unfold ring_entry_pa. f_equal. f_equal. f_equal.
    rewrite !Nat2Z.inj_add. change (Z.of_nat 8) with 8. change (Z.of_nat 0) with 0.
    rewrite Z.add_0_r.
    replace (Z.of_nat (vp_nc pr) + 8) with (Z.of_nat (vp_nc pr) + 1 * 8) by lia.
    apply Z_mod_plus_full. }
  rewrite Hring in Hd2.
  pose proof (vpo_fp_disj _ _ _ Hok (vp_nc pr + 0)%nat (vp_nc pr + 8)%nat
                sl1 sl2 pin1 pin2 ltac:(lia) Hs1 Hp1 Hs2 Hp2) as Hdisj.
  exact (proj1 (elem_of_disjoint _ _) Hdisj _
           (slot_fp_pin sl1 pin1 _ Hd1) (slot_fp_pin sl2 pin2 _ Hd2)).
Qed.

(* THE separation payoff: everything a slot's step may write -- its own
   writable bytes and the used page -- misses the whole control region. *)
Lemma vproto_wr_off_ctl (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (p : nat) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vproto_ok c pr D ->
  vp_slots pr !! p = Some sl -> vp_pin pr !! p = Some pin ->
  (slot_wr sl ∪ used_page_pas c) ## dom (vproto_ctl c pr).
Proof.
  intros Hok Hs Hpin.
  pose proof (vpo_standing _ _ _ Hok p sl pin Hs Hpin) as Hst.
  apply elem_of_disjoint. intros a Ha Hb.
  unfold vproto_ctl in Hb. rewrite dom_union_L, avail_idx_bytes_dom in Hb.
  apply elem_of_union in Hb as [Hb|Hb].
  - (* the pinned avail index *)
    apply elem_of_union in Ha as [Ha|Ha].
    + exact (proj1 (elem_of_disjoint _ _) Hst a
               (slot_fp_wr sl pin a Ha) (elem_of_union_l _ _ _ Hb)).
    + exact (proj1 (elem_of_disjoint _ _) (vpo_idx_used _ _ _ Hok) a Hb Ha).
  - (* somebody's pin *)
    apply pins_union_dom_inv in Hb as (q & mq & Hq & Hmq).
    destruct (vproto_slot_of_pin c pr D q mq Hok Hq) as [slq Hsq].
    pose proof (vpo_standing _ _ _ Hok q slq mq Hsq Hq) as Hstq.
    destruct (decide (q = p)) as [->|Hne].
    + rewrite Hq in Hpin. injection Hpin as <-.
      apply elem_of_union in Ha as [Ha|Ha].
      * exact (proj1 (elem_of_disjoint _ _) (vpo_wr_pin _ _ _ Hok p sl mq Hs Hq)
                 a Ha Hmq).
      * exact (proj1 (elem_of_disjoint _ _) Hstq a
                 (slot_fp_pin slq mq a Hmq) (elem_of_union_r _ _ _ Ha)).
    + pose proof (vpo_fp_disj _ _ _ Hok p q sl slq pin mq
                    (fun e => Hne (eq_sym e)) Hs Hpin Hsq Hq) as Hd.
      apply elem_of_union in Ha as [Ha|Ha].
      * exact (proj1 (elem_of_disjoint _ _) Hd a
                 (slot_fp_wr sl pin a Ha) (slot_fp_pin slq mq a Hmq)).
      * exact (proj1 (elem_of_disjoint _ _) Hstq a
                 (slot_fp_pin slq mq a Hmq) (elem_of_union_r _ _ _ Ha)).
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The flat form: VirtioModel section 7 derived from the keyed state.  *)
(* ---------------------------------------------------------------------- *)

Lemma vproto_flat (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa) :
  vproto_ok c pr D ->
  virtio_queue_ok c (vproto_ctl c pr) D
    (set_map wrap16 (dom (vp_pend pr)))
    (wrap16 (vp_np pr)) (wrap16 (vp_nc pr)).
Proof.
  intros Hok _.
  split; [ exact (vproto_ctl_idx c pr D Hok) | ].
  split.
  - (* the device's position is the published one, or still in flight *)
    destruct (decide (vp_nc pr = vp_np pr)) as [He|Hne].
    + left. rewrite He. reflexivity.
    + right. apply elem_of_map_2. rewrite (vpo_pend_dom _ _ _ Hok).
      apply elem_of_set_seq. pose proof (vpo_ncnp _ _ _ Hok). lia.
  - intros i Hi. apply elem_of_map_1 in Hi as (p & -> & Hp).
    pose proof Hp as Hp'.
    apply elem_of_dom in Hp as [sl Hsl].
    assert (Hpd : p ∈ dom (vp_pin pr)).
    { rewrite (vpo_pin_dom _ _ _ Hok). apply elem_of_union_l, elem_of_dom.
      exists sl. exact Hsl. }
    apply elem_of_dom in Hpd as [pin Hpin].
    pose proof (vproto_pend_slot pr p sl Hsl) as Hs.
    pose proof (vpo_slot _ _ _ Hok p sl pin Hs Hpin) as Hslot.
    split.
    + (* the slot obligation *)
      intros mv Hview.
      assert (Hvpin : mem_view pin mv).
      { apply (mem_view_subseteq pin (vproto_ctl c pr) mv);
          [ exact (vproto_pin_ctl c pr D p pin Hok Hpin) | exact Hview ]. }
      pose proof (spo_req _ _ _ _ Hslot mv Hvpin) as Hreq.
      split.
      * unfold virtio_chain_ok. unfold req_at in Hreq.
        destruct (chain_at c mv (wrap16 p)) as [[[[h d0] d1] d2]|];
          [reflexivity | discriminate].
      * intros isr ui dk v' w Hstep.
        destruct (vslot_req_step c p sl pin mv
                    (VirtioState c isr (wrap16 p) ui dk) v' w
                    Hslot Hvpin eq_refl eq_refl Hstep) as [_ Hw].
        cbn [v_used_idx v_disk] in Hw. subst w.
        pose proof (vslot_writes_dom_sub c p sl pin ui dk
                      (vpo_qnum _ _ _ Hok) Hslot) as Hsub.
        split.
        -- etransitivity; [ exact Hsub | ]. apply union_least.
           ++ etransitivity; [ apply slot_fp_wr |
                exact (vpo_fp_D _ _ _ Hok p sl pin Hs Hpin) ].
           ++ exact (vpo_used_D _ _ _ Hok).
        -- apply (gset_disj_sub_l _ (slot_wr sl ∪ used_page_pas c));
             [ exact Hsub | exact (vproto_wr_off_ctl c pr D p sl pin Hok Hs Hpin) ].
    + (* the successor position is published, or itself in flight *)
      rewrite <- wrap16_S.
      rewrite (vpo_pend_dom _ _ _ Hok) in Hp'. apply elem_of_set_seq in Hp'.
      destruct (decide (S p = vp_np pr)) as [He|Hne].
      * left. rewrite He. reflexivity.
      * right. apply elem_of_map_2. rewrite (vpo_pend_dom _ _ _ Hok).
        apply elem_of_set_seq. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. The determined step.                                                *)
(* ---------------------------------------------------------------------- *)

(* If the device is at position [nc] with something pending, the step it
   takes is COMPUTED by the slot: post-state [vslot_post], write set
   [vslot_writes].  (The only view-dependence [virtio_complete] has left is
   the OUT payload, and the pin fixes it.) *)
Lemma vproto_step_det (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (v : virtio_state) (mv : vmem) :
  vproto_ok c pr D ->
  v_cfg v = c -> v_seen v = wrap16 (vp_nc pr) ->
  mem_view (vproto_ctl c pr) mv ->
  (vp_nc pr < vp_np pr)%nat ->
  exists sl pin,
    vp_pend pr !! vp_nc pr = Some sl /\ vp_pin pr !! vp_nc pr = Some pin /\
    virtio_req_step v mv
      = Some (vslot_post v sl, vslot_writes c (v_used_idx v) (v_disk v) sl).
Proof.
  intros Hok Hcfg Hseen Hview Hlt.
  assert (Hin : vp_nc pr ∈ dom (vp_pend pr)).
  { rewrite (vpo_pend_dom _ _ _ Hok). apply elem_of_set_seq. lia. }
  apply elem_of_dom in Hin as [sl Hsl].
  assert (Hpd : vp_nc pr ∈ dom (vp_pin pr)).
  { rewrite (vpo_pin_dom _ _ _ Hok). apply elem_of_union_l, elem_of_dom.
    exists sl. exact Hsl. }
  apply elem_of_dom in Hpd as [pin Hpin].
  exists sl, pin. split; [exact Hsl|]. split; [exact Hpin|].
  pose proof (vproto_pend_slot pr _ _ Hsl) as Hs.
  pose proof (vpo_slot _ _ _ Hok _ sl pin Hs Hpin) as Hslot.
  assert (Hvpin : mem_view pin mv).
  { apply (mem_view_subseteq pin (vproto_ctl c pr) mv);
      [ exact (vproto_pin_ctl c pr D _ pin Hok Hpin) | exact Hview ]. }
  assert (Hpend : virtio_pending v mv = true).
  { unfold virtio_pending. rewrite Hcfg, (vpo_live _ _ _ Hok). cbn [andb].
    apply negb_true_iff, Z.eqb_neq.
    rewrite (avail_idx_pinned c (vproto_ctl c pr) mv (wrap16 (vp_np pr))
               Hview (vproto_ctl_idx c pr D Hok)), Hseen.
    pose proof (vproto_window c pr D Hok) as Hw.
    assert (Hne : wrap16 (vp_nc pr) <> wrap16 (vp_np pr))
      by (apply wrap16_inj_window; lia).
    intro Heq. apply Hne, bv_eq. symmetry. exact Heq. }
  unfold virtio_req_step. rewrite Hpend. cbn [negb].
  rewrite Hcfg, Hseen, (spo_req _ _ _ _ Hslot mv Hvpin).
  rewrite (vslot_complete c (vp_nc pr) sl pin mv v Hslot Hvpin Hcfg). reflexivity.
Qed.

(* Conversely, a step that FIRED means something was pending: the published
   index the view reports is pinned to [wrap16 np], and the wrap of the
   window (width <= 8) is injective. *)
Lemma vproto_step_pend (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (v : virtio_state) (mv : vmem) (v' : virtio_state)
    (w : gmap Arch.pa (bv 8)) :
  vproto_ok c pr D ->
  v_cfg v = c -> v_seen v = wrap16 (vp_nc pr) ->
  mem_view (vproto_ctl c pr) mv ->
  virtio_req_step v mv = Some (v', w) ->
  (vp_nc pr < vp_np pr)%nat.
Proof.
  intros Hok Hcfg Hseen Hview Hstep.
  destruct (decide (vp_nc pr < vp_np pr)%nat) as [Hlt|Hge]; [exact Hlt|].
  exfalso.
  pose proof (vpo_ncnp _ _ _ Hok) as Hle.
  assert (Heq : vp_nc pr = vp_np pr) by lia.
  assert (Hnp : virtio_pending v mv = false).
  { unfold virtio_pending. rewrite Hcfg.
    rewrite (avail_idx_pinned c (vproto_ctl c pr) mv (wrap16 (vp_np pr))
               Hview (vproto_ctl_idx c pr D Hok)), Hseen, Heq, Z.eqb_refl.
    apply andb_false_r. }
  unfold virtio_req_step in Hstep. rewrite Hnp in Hstep. cbn [negb] in Hstep.
  discriminate.
Qed.

(* the keyed obligation survives its own step: [nc] moves from pend to done *)
Definition vproto_step_state (pr : vproto) (sl : vslot) : vproto :=
  VProto (S (vp_nc pr)) (vp_np pr)
         (delete (vp_nc pr) (vp_pend pr))
         (<[ vp_nc pr := sl ]> (vp_done pr))
         (vp_pin pr).

Lemma vproto_ok_step (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (sl : vslot) :
  vproto_ok c pr D ->
  vp_pend pr !! vp_nc pr = Some sl ->
  vproto_ok c (vproto_step_state pr sl) D.
Proof.
  intros Hok Hsl.
  assert (Hslots : vp_slots (vproto_step_state pr sl) = vp_slots pr).
  { unfold vp_slots, vproto_step_state. cbn [vp_pend vp_done].
    apply map_eq. intro q. destruct (decide (q = vp_nc pr)) as [->|Hne].
    - rewrite lookup_union_r by apply lookup_delete.
      rewrite lookup_insert. symmetry. apply lookup_union_Some_l. exact Hsl.
    - rewrite !lookup_union, lookup_delete_ne by congruence.
      rewrite lookup_insert_ne by congruence. reflexivity. }
  assert (Hnc : vp_nc pr ∈ dom (vp_pend pr))
    by (apply elem_of_dom; exists sl; exact Hsl).
  assert (Hlt : (vp_nc pr < vp_np pr)%nat).
  { pose proof Hnc as Hc. rewrite (vpo_pend_dom _ _ _ Hok) in Hc.
    apply elem_of_set_seq in Hc. lia. }
  constructor.
  - exact (vpo_qnum _ _ _ Hok).
  - exact (vpo_live _ _ _ Hok).
  - unfold vproto_step_state. cbn [vp_nc vp_np]. lia.
  - unfold vproto_step_state. cbn [vp_nc vp_np vp_pend].
    rewrite dom_delete_L, (vpo_pend_dom _ _ _ Hok). set_solver by lia.
  - unfold vproto_step_state. cbn [vp_nc vp_done]. intros q Hq.
    rewrite dom_insert_L in Hq. apply elem_of_union in Hq as [Hq|Hq].
    + apply elem_of_singleton in Hq. lia.
    + pose proof (vpo_done_lt _ _ _ Hok q Hq). lia.
  - unfold vproto_step_state. cbn [vp_nc vp_pend vp_done vp_pin].
    rewrite dom_delete_L, dom_insert_L, (vpo_pin_dom _ _ _ Hok).
    apply gset_union_split. exact Hnc.
  - intros q slq pinq H1 H2. rewrite Hslots in H1.
    exact (vpo_slot _ _ _ Hok q slq pinq H1 H2).
  - intros q1 q2 sl1 sl2 pin1 pin2 Hne H1 H2 H3 H4.
    rewrite Hslots in H1, H3.
    exact (vpo_fp_disj _ _ _ Hok q1 q2 sl1 sl2 pin1 pin2 Hne H1 H2 H3 H4).
  - intros q slq pinq H1 H2. rewrite Hslots in H1.
    exact (vpo_wr_pin _ _ _ Hok q slq pinq H1 H2).
  - intros q slq pinq H1 H2. rewrite Hslots in H1.
    exact (vpo_standing _ _ _ Hok q slq pinq H1 H2).
  - exact (vpo_idx_used _ _ _ Hok).
  - intros q slq pinq H1 H2. rewrite Hslots in H1.
    exact (vpo_fp_D _ _ _ Hok q slq pinq H1 H2).
  - exact (vpo_used_D _ _ _ Hok).
  - exact (vpo_idx_D _ _ _ Hok).
Qed.

(* the step does not move the control map: the device writes no pinned byte *)
Lemma vproto_step_ctl (c : virtio_cfg) (pr : vproto) (sl : vslot) :
  vproto_ctl c (vproto_step_state pr sl) = vproto_ctl c pr.
Proof. reflexivity. Qed.

(* the step's writes: inside the lease, off the control region -- restated
   over the keyed state for the Iris layer's convenience *)
Lemma vslot_writes_dom (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (sl : vslot) (pin : gmap Arch.pa (bv 8)) (ui : bv 16) (dk : Z -> bv 8) :
  vproto_ok c pr D ->
  vp_pend pr !! vp_nc pr = Some sl -> vp_pin pr !! vp_nc pr = Some pin ->
  dom (vslot_writes c ui dk sl) ⊆ slot_wr sl ∪ used_page_pas c
  /\ dom (vslot_writes c ui dk sl) ## dom (vproto_ctl c pr).
Proof.
  intros Hok Hsl Hpin.
  pose proof (vproto_pend_slot pr _ _ Hsl) as Hs.
  pose proof (vpo_slot _ _ _ Hok _ sl pin Hs Hpin) as Hslot.
  pose proof (vslot_writes_dom_sub c (vp_nc pr) sl pin ui dk
                (vpo_qnum _ _ _ Hok) Hslot) as Hsub.
  split; [exact Hsub|].
  apply (gset_disj_sub_l _ (slot_wr sl ∪ used_page_pas c));
    [ exact Hsub | exact (vproto_wr_off_ctl c pr D _ sl pin Hok Hs Hpin) ].
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. Publish: appending slot [np].                                       *)
(* ---------------------------------------------------------------------- *)

Definition vproto_publish_state (pr : vproto) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) : vproto :=
  VProto (vp_nc pr) (S (vp_np pr))
         (<[ vp_np pr := sl ]> (vp_pend pr))
         (vp_done pr)
         (<[ vp_np pr := pin ]> (vp_pin pr)).

(* All the NEW disjointness hypotheses come from OWNERSHIP at the Iris layer
   (the publisher physically holds the new pin and writable bytes, so they
   are disjoint from the lease, whose domain covers everything old). *)
Lemma vproto_ok_publish (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vproto_ok c pr D ->
  slot_pin_ok c (vp_np pr) sl pin ->
  slot_wr sl ## dom pin ->
  slot_fp sl pin ## D ->
  vproto_ok c (vproto_publish_state pr sl pin) (D ∪ slot_fp sl pin).
Proof.
  intros Hok Hnew Hwr Hdisj.
  pose proof (vpo_ncnp _ _ _ Hok) as Hle.
  assert (Hslots : vp_slots (vproto_publish_state pr sl pin)
                   = <[ vp_np pr := sl ]> (vp_slots pr)).
  { unfold vp_slots, vproto_publish_state. cbn [vp_pend vp_done].
    symmetry. apply insert_union_l. }
  assert (Hother : forall slq pinq q,
            vp_slots pr !! q = Some slq -> vp_pin pr !! q = Some pinq ->
            slot_fp sl pin ## slot_fp slq pinq).
  { intros slq pinq q H1 H2.
    apply (gset_disj_sub_r _ _ D);
      [ exact (vpo_fp_D _ _ _ Hok q slq pinq H1 H2) | exact Hdisj ]. }
  assert (Hpins : vp_pin (vproto_publish_state pr sl pin)
                  = <[ vp_np pr := pin ]> (vp_pin pr)) by reflexivity.
  assert (Hlook : forall q slq pinq,
            vp_slots (vproto_publish_state pr sl pin) !! q = Some slq ->
            vp_pin (vproto_publish_state pr sl pin) !! q = Some pinq ->
            (q = vp_np pr /\ slq = sl /\ pinq = pin)
            \/ (vp_slots pr !! q = Some slq /\ vp_pin pr !! q = Some pinq)).
  { intros q slq pinq H1 H2. rewrite Hslots in H1. rewrite Hpins in H2.
    apply lookup_insert_Some in H1 as [[Hq1 Hs1]|[Hq1 H1]];
      apply lookup_insert_Some in H2 as [[Hq2 Hs2]|[Hq2 H2]].
    - left. split; [congruence|]. split; congruence.
    - exfalso. congruence.
    - exfalso. congruence.
    - right. split; assumption. }
  constructor.
  - exact (vpo_qnum _ _ _ Hok).
  - exact (vpo_live _ _ _ Hok).
  - unfold vproto_publish_state. cbn [vp_nc vp_np]. lia.
  - unfold vproto_publish_state. cbn [vp_nc vp_np vp_pend].
    rewrite dom_insert_L, (vpo_pend_dom _ _ _ Hok). set_solver by lia.
  - exact (vpo_done_lt _ _ _ Hok).
  - unfold vproto_publish_state. cbn [vp_pend vp_done vp_pin].
    rewrite !dom_insert_L, (vpo_pin_dom _ _ _ Hok). apply gset_union_assoc.
  - intros q slq pinq H1 H2.
    destruct (Hlook q slq pinq H1 H2) as [(-> & -> & ->)|[Ha Hb]].
    + exact Hnew.
    + exact (vpo_slot _ _ _ Hok q slq pinq Ha Hb).
  - intros q1 q2 sl1 sl2 pin1 pin2 Hne H1 H2 H3 H4.
    destruct (Hlook q1 sl1 pin1 H1 H2) as [(-> & -> & ->)|[Ha1 Hb1]];
      destruct (Hlook q2 sl2 pin2 H3 H4) as [(He2 & -> & ->)|[Ha2 Hb2]].
    + congruence.
    + exact (Hother sl2 pin2 q2 Ha2 Hb2).
    + apply gset_disj_sym. exact (Hother sl1 pin1 q1 Ha1 Hb1).
    + exact (vpo_fp_disj _ _ _ Hok q1 q2 sl1 sl2 pin1 pin2 Hne Ha1 Hb1 Ha2 Hb2).
  - intros q slq pinq H1 H2.
    destruct (Hlook q slq pinq H1 H2) as [(-> & -> & ->)|[Ha Hb]].
    + exact Hwr.
    + exact (vpo_wr_pin _ _ _ Hok q slq pinq Ha Hb).
  - intros q slq pinq H1 H2.
    destruct (Hlook q slq pinq H1 H2) as [(-> & -> & ->)|[Ha Hb]].
    + apply (gset_disj_sub_r _ _ D); [| exact Hdisj ].
      apply union_least;
        [ exact (vpo_idx_D _ _ _ Hok) | exact (vpo_used_D _ _ _ Hok) ].
    + exact (vpo_standing _ _ _ Hok q slq pinq Ha Hb).
  - exact (vpo_idx_used _ _ _ Hok).
  - intros q slq pinq H1 H2.
    destruct (Hlook q slq pinq H1 H2) as [(-> & -> & ->)|[Ha Hb]].
    + apply union_subseteq_r.
    + etransitivity;
        [ exact (vpo_fp_D _ _ _ Hok q slq pinq Ha Hb) | apply union_subseteq_l ].
  - etransitivity; [ exact (vpo_used_D _ _ _ Hok) | apply union_subseteq_l ].
  - etransitivity; [ exact (vpo_idx_D _ _ _ Hok) | apply union_subseteq_l ].
Qed.

(* the new control map: the index bytes advance, the new pin joins *)
Lemma vproto_publish_ctl (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vproto_ok c pr D ->
  slot_fp sl pin ## D ->
  vproto_ctl c (vproto_publish_state pr sl pin)
  = avail_idx_bytes c (S (vp_np pr)) ∪ (pin ∪ pins_union (vp_pin pr)).
Proof.
  intros Hok Hdisj.
  assert (Hnpin : vp_pin pr !! vp_np pr = None).
  { apply not_elem_of_dom. rewrite (vpo_pin_dom _ _ _ Hok). intro Hc.
    apply elem_of_union in Hc as [Hc|Hc].
    - rewrite (vpo_pend_dom _ _ _ Hok) in Hc. apply elem_of_set_seq in Hc. lia.
    - pose proof (vpo_done_lt _ _ _ Hok _ Hc). pose proof (vpo_ncnp _ _ _ Hok).
      lia. }
  assert (Hnewdisj : forall q m, vp_pin pr !! q = Some m -> pin ##ₘ m).
  { intros q m Hq. destruct (vproto_slot_of_pin c pr D q m Hok Hq) as [slq Hsq].
    apply map_disjoint_dom.
    apply (gset_disj_mono (dom pin) (slot_fp sl pin) (dom m) D).
    - apply slot_fp_pin.
    - etransitivity;
        [ apply slot_fp_pin | exact (vpo_fp_D _ _ _ Hok q slq m Hsq Hq) ].
    - exact Hdisj. }
  assert (Hd : forall q1 q2 m1 m2, q1 <> q2 ->
            <[ vp_np pr := pin ]> (vp_pin pr) !! q1 = Some m1 ->
            <[ vp_np pr := pin ]> (vp_pin pr) !! q2 = Some m2 -> m1 ##ₘ m2).
  { intros q1 q2 m1 m2 Hne H1 H2.
    apply lookup_insert_Some in H1 as [[Ha1 Hb1]|[Ha1 H1]];
      apply lookup_insert_Some in H2 as [[Ha2 Hb2]|[Ha2 H2]].
    - exfalso. congruence.
    - subst m1. exact (Hnewdisj q2 m2 H2).
    - subst m2. apply map_disjoint_sym. exact (Hnewdisj q1 m1 H1).
    - exact (vproto_pins_disj c pr D Hok q1 q2 m1 m2 Hne H1 H2). }
  assert (Hc1 : vproto_ctl c (vproto_publish_state pr sl pin)
                = avail_idx_bytes c (S (vp_np pr))
                  ∪ pins_union (<[ vp_np pr := pin ]> (vp_pin pr)))
    by reflexivity.
  rewrite Hc1, (pins_union_insert (vp_pin pr) (vp_np pr) pin Hnpin Hd).
  reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 6. Reclaim: removing a completed slot.                                 *)
(* ---------------------------------------------------------------------- *)

Definition vproto_reclaim_state (pr : vproto) (p : nat) : vproto :=
  VProto (vp_nc pr) (vp_np pr)
         (vp_pend pr) (delete p (vp_done pr)) (delete p (vp_pin pr)).

Lemma vproto_ok_reclaim (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (p : nat) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vproto_ok c pr D ->
  vp_done pr !! p = Some sl -> vp_pin pr !! p = Some pin ->
  vproto_ok c (vproto_reclaim_state pr p) (D ∖ slot_fp sl pin).
Proof.
  intros Hok Hdone Hpin.
  assert (Hplt : (p < vp_nc pr)%nat).
  { apply (vpo_done_lt _ _ _ Hok), elem_of_dom. exists sl. exact Hdone. }
  assert (Hnpend : vp_pend pr !! p = None).
  { apply not_elem_of_dom. rewrite (vpo_pend_dom _ _ _ Hok). intro Hc.
    apply elem_of_set_seq in Hc. lia. }
  assert (Hs : vp_slots pr !! p = Some sl).
  { unfold vp_slots. rewrite lookup_union_r by exact Hnpend. exact Hdone. }
  assert (Hdn : delete p (vp_pend pr) = vp_pend pr)
    by (apply delete_notin; exact Hnpend).
  assert (Hslots : vp_slots (vproto_reclaim_state pr p) = delete p (vp_slots pr)).
  { unfold vp_slots, vproto_reclaim_state. cbn [vp_pend vp_done].
    rewrite delete_union, Hdn. reflexivity. }
  assert (Hpins : vp_pin (vproto_reclaim_state pr p) = delete p (vp_pin pr))
    by reflexivity.
  assert (Hdd : vp_done (vproto_reclaim_state pr p) = delete p (vp_done pr))
    by reflexivity.
  assert (Hlook : forall q slq pinq,
            vp_slots (vproto_reclaim_state pr p) !! q = Some slq ->
            vp_pin (vproto_reclaim_state pr p) !! q = Some pinq ->
            q <> p /\ vp_slots pr !! q = Some slq /\ vp_pin pr !! q = Some pinq).
  { intros q slq pinq H1 H2. rewrite Hslots in H1. rewrite Hpins in H2.
    apply lookup_delete_Some in H1 as [Hq1 H1].
    apply lookup_delete_Some in H2 as [Hq2 H2].
    split; [congruence|]. split; assumption. }
  constructor.
  - exact (vpo_qnum _ _ _ Hok).
  - exact (vpo_live _ _ _ Hok).
  - exact (vpo_ncnp _ _ _ Hok).
  - exact (vpo_pend_dom _ _ _ Hok).
  - intros q Hq. apply (vpo_done_lt _ _ _ Hok).
    rewrite Hdd, dom_delete_L in Hq.
    apply elem_of_difference in Hq as [Hq _]. exact Hq.
  - rewrite Hpins, Hdd, !dom_delete_L, (vpo_pin_dom _ _ _ Hok).
    apply gset_diff_union_notin, not_elem_of_dom. exact Hnpend.
  - intros q slq pinq H1 H2.
    destruct (Hlook q slq pinq H1 H2) as (Hq & Ha & Hb).
    exact (vpo_slot _ _ _ Hok q slq pinq Ha Hb).
  - intros q1 q2 sl1 sl2 pin1 pin2 Hne H1 H2 H3 H4.
    destruct (Hlook q1 sl1 pin1 H1 H2) as (Hq1 & Ha1 & Hb1).
    destruct (Hlook q2 sl2 pin2 H3 H4) as (Hq2 & Ha2 & Hb2).
    exact (vpo_fp_disj _ _ _ Hok q1 q2 sl1 sl2 pin1 pin2 Hne Ha1 Hb1 Ha2 Hb2).
  - intros q slq pinq H1 H2.
    destruct (Hlook q slq pinq H1 H2) as (Hq & Ha & Hb).
    exact (vpo_wr_pin _ _ _ Hok q slq pinq Ha Hb).
  - intros q slq pinq H1 H2.
    destruct (Hlook q slq pinq H1 H2) as (Hq & Ha & Hb).
    exact (vpo_standing _ _ _ Hok q slq pinq Ha Hb).
  - exact (vpo_idx_used _ _ _ Hok).
  - intros q slq pinq H1 H2.
    destruct (Hlook q slq pinq H1 H2) as (Hq & Ha & Hb).
    apply gset_sub_diff; [ exact (vpo_fp_D _ _ _ Hok q slq pinq Ha Hb) | ].
    apply gset_disj_sym.
    exact (vpo_fp_disj _ _ _ Hok p q sl slq pin pinq
             (fun e => Hq (eq_sym e)) Hs Hpin Ha Hb).
  - apply gset_sub_diff; [ exact (vpo_used_D _ _ _ Hok) | ].
    apply gset_disj_sym.
    apply (gset_disj_sub_r _ _ (avail_idx_dom c ∪ used_page_pas c));
      [ apply union_subseteq_r
      | exact (vpo_standing _ _ _ Hok p sl pin Hs Hpin) ].
  - apply gset_sub_diff; [ exact (vpo_idx_D _ _ _ Hok) | ].
    apply gset_disj_sym.
    apply (gset_disj_sub_r _ _ (avail_idx_dom c ∪ used_page_pas c));
      [ apply union_subseteq_l
      | exact (vpo_standing _ _ _ Hok p sl pin Hs Hpin) ].
Qed.

Lemma vproto_reclaim_ctl (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (p : nat) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vproto_ok c pr D ->
  vp_done pr !! p = Some sl -> vp_pin pr !! p = Some pin ->
  vproto_ctl c (vproto_reclaim_state pr p)
  = avail_idx_bytes c (vp_np pr) ∪ pins_union (delete p (vp_pin pr))
  /\ pin ##ₘ (avail_idx_bytes c (vp_np pr) ∪ pins_union (delete p (vp_pin pr)))
  /\ vproto_ctl c pr
    = pin ∪ (avail_idx_bytes c (vp_np pr) ∪ pins_union (delete p (vp_pin pr))).
Proof.
  intros Hok Hdone Hpin.
  assert (Hplt : (p < vp_nc pr)%nat).
  { apply (vpo_done_lt _ _ _ Hok), elem_of_dom. exists sl. exact Hdone. }
  assert (Hnpend : vp_pend pr !! p = None).
  { apply not_elem_of_dom. rewrite (vpo_pend_dom _ _ _ Hok). intro Hc.
    apply elem_of_set_seq in Hc. lia. }
  assert (Hs : vp_slots pr !! p = Some sl).
  { unfold vp_slots. rewrite lookup_union_r by exact Hnpend. exact Hdone. }
  split; [ reflexivity | ].
  assert (Hdj : pin ##ₘ (avail_idx_bytes c (vp_np pr)
                         ∪ pins_union (delete p (vp_pin pr)))).
  { apply map_disjoint_dom. rewrite dom_union_L, avail_idx_bytes_dom.
    apply gset_disj_union_r.
    - apply (gset_disj_mono (dom pin) (slot_fp sl pin)
               (avail_idx_dom c) (avail_idx_dom c ∪ used_page_pas c));
        [ apply slot_fp_pin | apply union_subseteq_l
        | exact (vpo_standing _ _ _ Hok p sl pin Hs Hpin) ].
    - apply elem_of_disjoint. intros a Ha Hb.
      apply pins_union_dom_inv in Hb as (q & mq & Hq & Hmq).
      apply lookup_delete_Some in Hq as [Hne Hq].
      pose proof (vproto_pins_disj c pr D Hok p q pin mq Hne Hpin Hq) as Hd.
      apply map_disjoint_dom in Hd.
      exact (proj1 (elem_of_disjoint _ _) Hd a Ha Hmq). }
  split; [ exact Hdj | ].
  destruct (proj1 (map_disjoint_union_r pin (avail_idx_bytes c (vp_np pr))
                     (pins_union (delete p (vp_pin pr)))) Hdj) as [Hd1 _].
  unfold vproto_ctl.
  rewrite (pins_union_delete (vp_pin pr) p pin Hpin (vproto_pins_disj c pr D Hok)).
  rewrite !map_union_assoc. f_equal.
  apply map_union_comm, map_disjoint_sym. exact Hd1.
Qed.

(* ---------------------------------------------------------------------- *)
(* 7. The empty (fresh-after-init) instance.                              *)
(* ---------------------------------------------------------------------- *)

Definition vproto0 : vproto := VProto 0 0 ∅ ∅ ∅.

Lemma vproto_ok_init (c : virtio_cfg) :
  vc_qnum c = Z_to_bv 32 8 ->
  virtio_live c = true ->
  avail_idx_dom c ## used_page_pas c ->
  vproto_ok c vproto0 (avail_idx_dom c ∪ used_page_pas c).
Proof.
  intros Hq Hlive Hiu.
  assert (Hpend0 : vp_pend vproto0 = (∅ : gmap nat vslot)) by reflexivity.
  assert (Hdone0 : vp_done vproto0 = (∅ : gmap nat vslot)) by reflexivity.
  assert (Hpin0 : vp_pin vproto0 = (∅ : gmap nat (gmap Arch.pa (bv 8))))
    by reflexivity.
  assert (Hemp : vp_slots vproto0 = (∅ : gmap nat vslot)).
  { unfold vp_slots. rewrite Hpend0, Hdone0. apply map_eq. intro q.
    rewrite lookup_union, !lookup_empty. reflexivity. }
  constructor.
  - exact Hq.
  - exact Hlive.
  - reflexivity.
  - rewrite Hpend0, dom_empty_L. reflexivity.
  - intros q Hqd. rewrite Hdone0, dom_empty_L in Hqd.
    exfalso. exact (proj1 (elem_of_empty q) Hqd).
  - rewrite Hpend0, Hdone0, Hpin0, !dom_empty_L.
    apply gset_eq_of_elem. intro x. rewrite elem_of_union. tauto.
  - intros q slq pinq H1 _. rewrite Hemp, lookup_empty in H1. discriminate.
  - intros q1 q2 sl1 sl2 pin1 pin2 _ H1 _ _ _.
    rewrite Hemp, lookup_empty in H1. discriminate.
  - intros q slq pinq H1 _. rewrite Hemp, lookup_empty in H1. discriminate.
  - intros q slq pinq H1 _. rewrite Hemp, lookup_empty in H1. discriminate.
  - exact Hiu.
  - intros q slq pinq H1 _. rewrite Hemp, lookup_empty in H1. discriminate.
  - apply union_subseteq_r.
  - apply union_subseteq_l.
Qed.

Lemma vproto0_ctl (c : virtio_cfg) :
  vproto_ctl c vproto0 = avail_idx_bytes c 0.
Proof.
  assert (Hc : vproto_ctl c vproto0
               = avail_idx_bytes c 0 ∪ pins_union ∅) by reflexivity.
  rewrite Hc. unfold pins_union. rewrite map_fold_empty.
  apply map_eq. intro a. rewrite lookup_union, lookup_empty.
  destruct (avail_idx_bytes c 0 !! a); reflexivity.
Qed.
