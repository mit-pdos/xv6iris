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
(* SECTOR-ATOMIC DISK + THE VOLATILE WRITE CACHE                          *)
(* (claude-notes/completed/sector-atomic-disk.md;                          *)
(*  claude-notes/projects/async-disk.md).  An OUT request's data is        *)
(* CAPTURED into the device's own cache in one step                        *)
(* ([VirtioModel.virtio_capture_step]) and then DRAINS to the durable      *)
(* image one 512-byte sector at a time, in any order                       *)
(* ([VirtioModel.virtio_drain_step]); the completion moves NO disk byte at *)
(* all ([vslot_post]).  With the cache DECLINED (xv6 clears FLUSH, so      *)
(* [VirtioModel.virtio_wce] is false) the drains all precede the           *)
(* completion, which is the writethrough discipline this file's [vs_todo]  *)
(* counts down.  Two consequences live in this file:                       *)
(*                                                                         *)
(*   - [vslot] carries ONE crash-permit key, [vs_perm] (the ruling of      *)
(*     sector-atomic-disk.md §6e).  The request's obligation is a SINGLE   *)
(*     sequential permit ([RiscvPtsto.disk_seq_permit]) that unfolds one   *)
(*     sector at a time; the channel entry stays at that one key and is    *)
(*     RE-INDEXED at each landing, from the sectors still to land          *)
(*     ([vs_todo] below) down to the empty set, whose leaf is the          *)
(*     completion's identity permit delivering the client's receipt.  A    *)
(*     READ has no sectors, so its entry is at the leaf from the start --  *)
(*     which is what keeps the completion arm DIRECTION-AGNOSTIC.          *)
(*                                                                         *)
(*   - [vs_torn] is the block's content mid-flight: the payload's bytes in *)
(*     the sectors that have landed, the old ones elsewhere.  A crash      *)
(*     between two landings leaves exactly that on the disk.               *)
(*                                                                         *)
(* Design rationale: claude-notes/design/virtio-driver.md.                 *)
(* ====================================================================== *)

From stdpp Require Import gmap.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.definitions.

Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import VirtioModel.
(* The [set_solver] override.  EXPORT, not Import: this import is         *)
(* deliberately "dead" -- the file compiles without it, just far slower --  *)
(* and the nightly dead-import sweep skips [Require Export] lines.         *)
(* It has to be HERE rather than inherited: [Require Export] only          *)
(* propagates through an unbroken chain of Exports, and this tree's        *)
(* intermediate files use [Require Import], so nothing downstream inherits *)
(* it.  See FastSetSolver.v.                                              *)
Require Export FastSetSolver.

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

(* -- THE WINDOW, in the protocol's [nat] positions --------------------- *)
(*                                                                        *)
(*    The device's window arithmetic ([VirtioModel] section 5b) is modular *)
(*    distance on [bv 16]; the protocol counts positions in [nat] and      *)
(*    never wraps.  These three lemmas are the bridge, and they all lean   *)
(*    on the SAME fact: the live window is at most eight positions wide    *)
(*    (the ring has eight entries and a published-unserved position pins   *)
(*    its own), so [wrap16] is injective on it.                            *)

Lemma wrap16_add (p k : nat) :
  wrap16 (p + k) = bv_add (wrap16 p) (Z_to_bv 16 (Z.of_nat k)).
Proof.
  unfold wrap16. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r.
  apply f_equal2; [lia | reflexivity].
Qed.

Lemma vdist_wrap16 (lo k : nat) :
  (Z.of_nat k < 65536) -> vdist (wrap16 lo) (wrap16 (lo + k)) = Z.of_nat k.
Proof.
  intro Hk. unfold vdist, wrap16.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 16) with 65536.
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r.
  replace (Z.of_nat (lo + k) - Z.of_nat lo) with (Z.of_nat k) by lia.
  apply Z.mod_small. lia.
Qed.

Lemma vpos_pub_wrap16 (lo np : nat) (p : bv 16) :
  (lo <= np)%nat -> (np - lo <= 8)%nat ->
  vpos_pub (wrap16 lo) (wrap16 np) p = true <->
  exists k, (k < np - lo)%nat /\ p = wrap16 (lo + k).
Proof.
  intros Hle Hw.
  assert (Hnp : vdist (wrap16 lo) (wrap16 np) = Z.of_nat (np - lo)).
  { pose proof (vdist_wrap16 lo (np - lo)%nat ltac:(lia)) as Hd.
    replace (lo + (np - lo))%nat with np in Hd by lia. exact Hd. }
  unfold vpos_pub. rewrite Hnp. split.
  - intro H. apply Z.ltb_lt in H.
    pose proof (vdist_bounds (wrap16 lo) p) as Hb.
    exists (Z.to_nat (vdist (wrap16 lo) p)). split; [lia|].
    (* the position at that distance IS [p]: distance determines it *)
    symmetry. apply (vdist_inj (wrap16 lo)).
    rewrite vdist_wrap16 by lia. lia.
  - intros (k & Hk & ->). rewrite vdist_wrap16 by lia. apply Z.ltb_lt. lia.
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
  (* THE CRASH-PERMIT KEY (PermInv.v; claude-notes/design/fs-log.md stage 4).
     Every published request carries a permit -- an OUT request the client's
     real one, an IN request the trivial identity ([disk_write_permit True]),
     which is why this is a PAIR and not an option: keeping it uniform is
     what keeps the completion direction-agnostic (the completing slot is
     chosen inside [virtio_proto_step], so its caller cannot case-split on
     the direction).  [fst] is the permit invariant's map key, [snd] is the
     saved-proposition gname that pins the client's receipt.  PURE DATA, so
     the slot stays timeless and rides [disk_inv] -- that is the whole point
     of the split, and the [vs_data] rule again: an exclusive resource taken
     across a sleep must be IDENTIFIED in the record the invariant keys on,
     or the woken publisher gets it back opaque.
     Spelled [positive] because this file is deliberately iris-free;
     [gname := positive], so every consumer reads it as a gname.
     ONE key per request (sector-atomic-disk.md §6e): the cell it names
     holds the whole SEQUENTIAL permit and is re-indexed at every sector
     landing, so nothing about the slot has to grow with the sector count. *)
  vs_perm : nat * positive;
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

(* THE COMPLETION DOES NOT MOVE THE IMAGE, NOR THE CACHE.  Every byte of an
   OUT request's data reached the CACHE at the capture and the durable image
   at the drains, both before the completion was enabled
   ([VirtioModel.virtio_complete_ok] gates [VirtioModel.virtio_req_step]), so
   all this step does is the used-ring report, the status byte, the interrupt
   -- and MARK THE POSITION SERVED, releasing the capture latch. *)
Definition vslot_post (v : virtio_state) (sl : vslot) (i : bv 16)
  : virtio_state :=
  VirtioState (v_cfg v) (bv_or (v_isr v) (Z_to_bv 32 vio_isr_used_buffer))
    (vserve (v_seen v) (v_ahead v) i).1 (vserve (v_seen v) (v_ahead v) i).2
    (bv_add (v_used_idx v) (Z_to_bv 16 1)) (v_disk v) (v_cache v)
    (if bool_decide (v_taken v = Some i) then None else v_taken v)
    (v_cap v).

(* THE SLOT'S WRITE IDENTITY (claude-notes/design/fs-log.md stage 4 phase
   C2a): what this request does to the disk image, as the pure
   [VirtioModel.disk_wr] datum a crash permit is indexed by.  Derived from
   the slot, so nothing has to be recorded twice -- the tie between the
   permit's index and the request is [VirtioProto.slot_pend_res] holding the
   pending token AT [vs_wr sl], and [vslot_post_wr] below is what lets the
   DMA completion discharge the permit's obligation. *)
Definition vs_wr (sl : vslot) : disk_wr :=
  if vs_is_out sl then Some (vs_sector_off sl, vs_data sl) else None.

(* ...and hence the identity the completion's (now TRIVIAL) permit needs:
   the image the machine moves to is [wr_apply None] of the one it moved
   from.  This is what keeps [VirtioProto.virtio_proto_step]'s interface --
   and [WpUart.wp_disk_loop]'s completion arm -- uniform over the request's
   direction while the real, per-sector permits fire elsewhere. *)
Lemma vslot_post_wr (v : virtio_state) (sl : vslot) (i : bv 16) :
  v_disk (vslot_post v sl i) = wr_apply None (v_disk v).
Proof. reflexivity. Qed.

Lemma vslot_post_cache (v : virtio_state) (sl : vslot) (i : bv 16) :
  v_cache (vslot_post v sl i) = v_cache v.
Proof. reflexivity. Qed.

Lemma vslot_post_taken (v : virtio_state) (sl : vslot) (i : bv 16) :
  v_taken (vslot_post v sl i)
  = (if bool_decide (v_taken v = Some i) then None else v_taken v).
Proof. reflexivity. Qed.

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
   function of the slot and the image it reads.  Since the completion no
   longer transfers the OUT payload (it was captured earlier, and drained
   sector by sector), the last piece of view-dependence it had is gone --
   only the pinned request matters, and the IMAGE a READ reports is the
   CACHE-OVERLAID one ([VirtioModel.cache_view]), which is read-your-writes.
   In writethrough the cache is empty at every completion, so
   [vslot_writes_cache_view] below turns that back into the durable image. *)
Lemma vslot_complete (c : virtio_cfg) (p : nat) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) (mv : vmem) (v : virtio_state) (i : bv 16) :
  slot_pin_ok c p sl pin -> mem_view pin mv -> v_cfg v = c ->
  virtio_complete v mv (vs_req sl) i
  = (vslot_post v sl i, vslot_writes c (v_used_idx v) (cache_view v) sl).
Proof.
  intros Hslot Hview Hcfg.
  pose proof (spo_type _ _ _ _ Hslot) as Htype.
  unfold virtio_complete, vslot_post, vslot_writes, vs_is_out, vs_sector_off, vs_len.
  cbv zeta. rewrite Hcfg.
  destruct Htype as [Hin|Hout]; rewrite ?Hin, ?Hout;
    unfold virtio_blk_t_in, virtio_blk_t_out, virtio_blk_t_flush;
    cbn [Z.eqb orb Pos.eqb]; reflexivity.
Qed.

(* WRITETHROUGH COLLAPSES THE OVERLAY: a read whose own sectors are not in
   the cache reports the DURABLE image's bytes, which is what the completion
   gate buys ([VirtioModel.virtio_complete_ok]).  The device may still be
   holding SOME OTHER request's payload -- the served order is free -- and
   that is why this is stated per request rather than over the whole cache. *)
Lemma vslot_writes_cache_view (c : virtio_cfg) (ui : bv 16) (v : virtio_state)
    (sl : vslot) :
  vreq_touch (vs_req sl) ∩ dom (v_cache v) = ∅ ->
  vslot_writes c ui (cache_view v) sl = vslot_writes c ui (v_disk v) sl.
Proof.
  intro H. unfold vslot_writes. cbv zeta.
  destruct (vs_is_out sl); [reflexivity|].
  unfold vs_sector_off, vs_len. by rewrite (cache_view_read v (vs_req sl) H).
Qed.

(* ...and hence the step at a pinned slot, when it fires, is that function.
   [virtio_req_step]'s gate ([VirtioModel.virtio_complete_ok]) is simply
   discharged by the fact that the step DID fire. *)
Lemma vslot_req_step (c : virtio_cfg) (p : nat) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) (mv : vmem) (v v' : virtio_state)
    (w : gmap Arch.pa (bv 8)) :
  slot_pin_ok c p sl pin -> mem_view pin mv ->
  v_cfg v = c ->
  virtio_req_step v mv (wrap16 p) = Some (v', w) ->
  v' = vslot_post v sl (wrap16 p)
  /\ w = vslot_writes c (v_used_idx v) (cache_view v) sl.
Proof.
  intros Hslot Hview Hcfg Hstep.
  unfold virtio_req_step in Hstep.
  destruct (negb (virtio_serve_ok v mv (wrap16 p))); [discriminate|].
  rewrite Hcfg, (spo_req _ _ _ _ Hslot mv Hview) in Hstep.
  destruct (negb (virtio_complete_ok v (vs_req sl) (wrap16 p))); [discriminate|].
  rewrite (vslot_complete c p sl pin mv v (wrap16 p) Hslot Hview Hcfg) in Hstep.
  injection Hstep as Hv Hw. split; [ symmetry; exact Hv | symmetry; exact Hw ].
Qed.

(* THE GATE, READ BACK: a completion that fired proves the request was
   completABLE -- for an OUT that its data had been captured and (in
   writethrough) that none of its sectors was still cached, i.e. every one of
   them had drained.  This is what lets [VirtioProto] conclude that the
   block's durable content IS the payload at the instant the publisher is
   woken -- the completion itself moves no byte. *)
Lemma vslot_req_step_gate (c : virtio_cfg) (p : nat) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) (mv : vmem) (v v' : virtio_state)
    (w : gmap Arch.pa (bv 8)) :
  slot_pin_ok c p sl pin -> mem_view pin mv ->
  v_cfg v = c ->
  virtio_req_step v mv (wrap16 p) = Some (v', w) ->
  virtio_complete_ok v (vs_req sl) (wrap16 p) = true.
Proof.
  intros Hslot Hview Hcfg Hstep.
  unfold virtio_req_step in Hstep.
  destruct (negb (virtio_serve_ok v mv (wrap16 p))); [discriminate|].
  rewrite Hcfg, (spo_req _ _ _ _ Hslot mv Hview) in Hstep.
  destruct (virtio_complete_ok v (vs_req sl) (wrap16 p)) eqn:Hd;
    [reflexivity|].
  cbn [negb] in Hstep. discriminate.
Qed.

(* ---------------------------------------------------------------------- *)
(* 1b. SECTOR LANDINGS at a pinned slot.                                  *)
(*                                                                        *)
(*    A 512-byte sector lands atomically and a 1024-byte block does not    *)
(*    (claude-notes/completed/sector-atomic-disk.md).  Between the publish  *)
(*    and the completion the block therefore holds a TORN mixture of its   *)
(*    old content and the payload -- old bytes in the sectors that have    *)
(*    not landed, payload bytes in the ones that have -- and that is what  *)
(*    [VirtioProto.slot_pend_res] has to state about the disk fragments it *)
(*    is holding on the publisher's behalf.  [vs_torn] is that mixture as  *)
(*    a predicate on the CURRENT content, parameterized by the landed set. *)
(* ---------------------------------------------------------------------- *)

(* [VirtioModel.vreq_wr] reads the payload off the bus; the pin fixes it, so
   at a pinned slot the device's write identity IS the slot's own [vs_wr].
   This is what ties the per-sector permit indices [wr_sector (vs_wr sl) i]
   to the image move a DRAIN actually makes. *)
Lemma vslot_vreq_wr (c : virtio_cfg) (p : nat) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) (mv : vmem) :
  slot_pin_ok c p sl pin -> mem_view pin mv ->
  vreq_wr mv (vs_req sl) = vs_wr sl.
Proof.
  intros Hslot Hview.
  pose proof (spo_type _ _ _ _ Hslot) as Htype.
  pose proof (spo_len _ _ _ _ Hslot) as Hlen.
  unfold vreq_wr, vs_wr, vs_is_out, vs_sector_off.
  destruct Htype as [Hin|Hout].
  - rewrite Hin. unfold virtio_blk_t_in, virtio_blk_t_out.
    cbn [Z.eqb Pos.eqb]. reflexivity.
  - assert (Hout' : vs_is_out sl = true)
      by (unfold vs_is_out; rewrite Hout; unfold virtio_blk_t_out; reflexivity).
    pose proof (spo_out _ _ _ _ Hslot Hout') as Hro.
    pose proof (view_bytes_read pin mv (vr_buf (vs_req sl)) 1024 (vs_data sl)
                  Hview Hro) as Hvb.
    rewrite Hout. unfold virtio_blk_t_out. cbn [Z.eqb Pos.eqb].
    rewrite Hlen.
    assert (H1024 : Z.to_nat 1024 = 1024%nat) by (vm_compute; reflexivity).
    rewrite H1024, Hvb. reflexivity.
Qed.

(* ...and the sector COUNT the model gates the completion on is the slot's *)
Lemma vslot_vreq_nsectors (c : virtio_cfg) (p : nat) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) (mv : vmem) :
  slot_pin_ok c p sl pin -> mem_view pin mv ->
  vreq_nsectors (vs_req sl) = wr_nsectors (vs_wr sl).
Proof.
  intros Hslot Hview.
  rewrite <- (vslot_vreq_wr c p sl pin mv Hslot Hview).
  symmetry. apply vreq_nsectors_wr.
Qed.

(* the payload's length, from the pin: a request always names 1024 bytes *)
Lemma vq_read_byte_list_len (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : nat)
    (bs : list (bv 8)) :
  read_byte_list mm pa n = Some bs -> length bs = n.
Proof.
  unfold read_byte_list. intro Hm. apply mapM_Some_1 in Hm.
  pose proof (Forall2_length Hm) as Hlen. rewrite length_seq in Hlen. lia.
Qed.

Lemma vslot_data_len (c : virtio_cfg) (p : nat) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) :
  slot_pin_ok c p sl pin -> vs_is_out sl = true ->
  length (vs_data sl) = vs_len sl.
Proof.
  intros Hslot Hout.
  pose proof (spo_len _ _ _ _ Hslot) as Hlen.
  pose proof (vq_read_byte_list_len pin (vr_buf (vs_req sl)) 1024 (vs_data sl)
                (spo_out _ _ _ _ Hslot Hout)) as Hdl.
  unfold vs_len. rewrite Hlen, Hdl. vm_compute. reflexivity.
Qed.

(* the sector count, in the slot's own vocabulary *)
Lemma vslot_nsectors_out (sl : vslot) :
  vs_is_out sl = true -> vreq_nsectors (vs_req sl) = sector_count (vs_len sl).
Proof.
  unfold vs_is_out, vreq_nsectors, vs_len. intro H. by rewrite H.
Qed.

Lemma vslot_wr_out (sl : vslot) :
  vs_is_out sl = true -> vs_wr sl = Some (vs_sector_off sl, vs_data sl).
Proof. intro H. unfold vs_wr. by rewrite H. Qed.

(* the sector count agrees with the request's WITHOUT a bus view: the pin
   fixes the payload's length, and that is all [wr_nsectors] reads *)
Lemma vslot_nsectors_pin (c : virtio_cfg) (p : nat) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) :
  slot_pin_ok c p sl pin ->
  vreq_nsectors (vs_req sl) = wr_nsectors (vs_wr sl).
Proof.
  intro Hslot. destruct (vs_is_out sl) eqn:Hout.
  - rewrite (vslot_nsectors_out sl Hout), (vslot_wr_out sl Hout).
    cbn [wr_nsectors snd]. by rewrite (vslot_data_len c p sl pin Hslot Hout).
  - assert (Hne : bv_unsigned (vr_type (vs_req sl)) <> virtio_blk_t_out).
    { unfold vs_is_out in Hout. by apply Z.eqb_neq. }
    rewrite (vreq_nsectors_in _ Hne). unfold vs_wr. rewrite Hout. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 1b'. THE SLOT'S CACHE (claude-notes/projects/async-disk.md).            *)
(*                                                                        *)
(*    The device's write cache is keyed by ABSOLUTE SECTOR NUMBER, so      *)
(*    sector [i] of this slot's request lives at key [vs_key sl i].  At a   *)
(*    pinned slot the entries the capture deposits are a function of the   *)
(*    slot alone ([vslot_vreq_cache]) -- the pin fixes the payload -- which *)
(*    is what lets the Iris slot resource state what the device is holding *)
(*    without quantifying over a bus view.                                 *)
(* ---------------------------------------------------------------------- *)

Definition vs_key (sl : vslot) (i : nat) : Z := vreq_key (vs_req sl) i.

(* the absolute sector numbers this request touches *)
Definition vs_sectors (sl : vslot) : gset Z := vreq_sectors (vs_req sl).

Lemma vs_key_inj (sl : vslot) (i j : nat) : vs_key sl i = vs_key sl j -> i = j.
Proof. apply vreq_key_inj. Qed.

Lemma vs_sectors_spec (c : virtio_cfg) (p : nat) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) (s : Z) :
  slot_pin_ok c p sl pin ->
  (s ∈ vs_sectors sl
   <-> exists i, (i < wr_nsectors (vs_wr sl))%nat /\ s = vs_key sl i).
Proof.
  intro Hslot. unfold vs_sectors, vs_key.
  rewrite (vreq_sectors_spec (vs_req sl) s).
  by rewrite (vslot_nsectors_pin c p sl pin Hslot).
Qed.

(* WHAT THE CAPTURE DEPOSITS, in the slot's own vocabulary *)
Definition vslot_cache (sl : vslot) : gmap Z (list (bv 8)) :=
  list_to_map ((fun i => (vs_key sl i, wr_sector_bytes (vs_wr sl) i))
                 <$> seq 0 (wr_nsectors (vs_wr sl))).

Lemma vslot_vreq_cache (c : virtio_cfg) (p : nat) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) (mv : vmem) :
  slot_pin_ok c p sl pin -> mem_view pin mv ->
  vreq_cache mv (vs_req sl) = vslot_cache sl.
Proof.
  intros Hslot Hview. unfold vreq_cache, vreq_cache_of, vslot_cache, vs_key.
  rewrite (vslot_vreq_wr c p sl pin mv Hslot Hview).
  by rewrite (vslot_nsectors_pin c p sl pin Hslot).
Qed.

Lemma vslot_cache_lookup (sl : vslot) (i : nat) :
  (i < wr_nsectors (vs_wr sl))%nat ->
  vslot_cache sl !! vs_key sl i = Some (wr_sector_bytes (vs_wr sl) i).
Proof.
  intro Hi. unfold vslot_cache. apply elem_of_list_to_map.
  - rewrite <- list_fmap_compose.
    apply (NoDup_fmap_2_strong (vs_key sl)); [| apply NoDup_seq ].
    intros x y _ _ Hxy. exact (vs_key_inj sl x y Hxy).
  - apply elem_of_list_fmap. exists i. split; [reflexivity|].
    apply elem_of_seq. lia.
Qed.

Lemma vslot_cache_dom (sl : vslot) :
  dom (vslot_cache sl) = list_to_set (vs_key sl <$> seq 0 (wr_nsectors (vs_wr sl))).
Proof.
  unfold vslot_cache. rewrite dom_list_to_map_L, <- list_fmap_compose.
  reflexivity.
Qed.

(* ...and that domain IS the request's sector set, so the writethrough
   invariant's "everything cached belongs to the head request" is exactly
   "the cache is a sub-map of what the capture deposited". *)
Lemma vslot_cache_dom_sectors (c : virtio_cfg) (p : nat) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) :
  slot_pin_ok c p sl pin -> dom (vslot_cache sl) = vs_sectors sl.
Proof.
  intro Hslot. rewrite vslot_cache_dom.
  unfold vs_sectors, vreq_sectors, vs_key.
  by rewrite (vslot_nsectors_pin c p sl pin Hslot).
Qed.

(* a drain shrinks the cache, so the sub-map fact it needs survives it *)
Lemma vslot_cache_sub_delete (ca : gmap Z (list (bv 8))) (sl : vslot) (s : Z) :
  ca ⊆ vslot_cache sl -> delete s ca ⊆ vslot_cache sl.
Proof.
  intro Hsub. etransitivity; [ apply delete_subseteq | exact Hsub ].
Qed.

(* THE DRAIN'S IMAGE MOVE, in the slot's vocabulary: the permit index stays
   [wr_sector (vs_wr sl) i] even though the bytes now come out of the cache. *)
Lemma vslot_drain_image (sl : vslot) (i : nat) (dk : Z -> bv 8) :
  disk_write dk (virtio_sector_size * vs_key sl i) (wr_sector_bytes (vs_wr sl) i)
  = wr_apply (wr_sector (vs_wr sl) i) dk.
Proof.
  destruct (vs_is_out sl) eqn:Hout.
  - rewrite (vslot_wr_out sl Hout).
    replace (virtio_sector_size * vs_key sl i)
      with (vs_sector_off sl + virtio_sector_size * Z.of_nat i)
      by (unfold vs_key, vreq_key, vs_sector_off; lia).
    apply wr_sector_write.
  - assert (Hnone : vs_wr sl = None) by (unfold vs_wr; by rewrite Hout).
    rewrite Hnone, wr_sector_none, wr_apply_none, wr_sector_bytes_none.
    apply disk_write_nil.
Qed.

(* ---------------------------------------------------------------------- *)
(* THE SECTORS STILL TO DRAIN (sector-atomic-disk.md §6e, restated for the *)
(* write cache: claude-notes/projects/async-disk.md).                      *)
(*                                                                        *)
(* The request's single channel entry is INDEXED by this set: right after  *)
(* the capture it is every sector of the write, each DRAIN removes one,    *)
(* and the writethrough completion finds it empty -- which is exactly when *)
(* the sequential permit has unfolded down to its leaf.  A READ has no     *)
(* sectors, so it is empty from the start.  Derived from the slot and the  *)
(* device's CACHE DOMAIN ([S], i.e. [dom (VirtioModel.v_cache v)]), so     *)
(* nothing is recorded twice -- what used to be read off a landed set is   *)
(* now read off the entries the device is still holding.                   *)
(* ---------------------------------------------------------------------- *)
Definition vs_todo (sl : vslot) (S : gset Z) : gset nat :=
  filter (fun i => vs_key sl i ∈ S)
         (set_seq 0 (wr_nsectors (vs_wr sl)) : gset nat).

Lemma vs_todo_elem (sl : vslot) (S : gset Z) (i : nat) :
  i ∈ vs_todo sl S <-> (i < wr_nsectors (vs_wr sl))%nat /\ vs_key sl i ∈ S.
Proof.
  unfold vs_todo. rewrite elem_of_filter, elem_of_set_seq.
  split; [ intros [H1 H2]; split; [lia|exact H1]
         | intros [H1 H2]; split; [exact H2|lia] ].
Qed.

Lemma vs_todo_in (sl : vslot) (S : gset Z) (i : nat) :
  (i < wr_nsectors (vs_wr sl))%nat -> vs_key sl i ∈ S -> i ∈ vs_todo sl S.
Proof. intros H1 H2. apply vs_todo_elem. by split. Qed.

(* one DRAIN removes exactly its own sector -- and no other, because the
   sector keys are injective in the index *)
Lemma vs_todo_step (sl : vslot) (S : gset Z) (i : nat) :
  vs_todo sl (S ∖ {[ vs_key sl i ]}) = vs_todo sl S ∖ {[ i ]}.
Proof.
  apply set_eq. intro x.
  rewrite elem_of_difference, !vs_todo_elem, elem_of_difference,
          elem_of_singleton, elem_of_singleton.
  split.
  - intros [Hx [Hin Hne]]. split; [by split|].
    intros ->. by apply Hne.
  - intros [[Hx Hin] Hne]. split; [exact Hx|]. split; [exact Hin|].
    intro He. apply Hne. exact (vs_key_inj sl x i He).
Qed.

(* every sector drained: nothing left, so the entry is at the leaf *)
Lemma vs_todo_done (sl : vslot) (S : gset Z) :
  (forall i, (i < wr_nsectors (vs_wr sl))%nat -> vs_key sl i ∉ S) ->
  vs_todo sl S = ∅.
Proof.
  intro Hall. apply set_eq. intro x. rewrite vs_todo_elem, elem_of_empty.
  split; [| tauto]. intros [Hx Hin]. exact (Hall x Hx Hin).
Qed.

(* the empty cache is the leaf, whatever the request *)
Lemma vs_todo_empty (sl : vslot) : vs_todo sl ∅ = ∅.
Proof. apply vs_todo_done. intros i _. apply not_elem_of_empty. Qed.

(* RIGHT AFTER THE CAPTURE nothing has drained, so every sector is still to
   do -- the sequential permit is at its root. *)
Lemma vs_todo_full (sl : vslot) :
  vs_todo sl (dom (vslot_cache sl)) = set_seq 0 (wr_nsectors (vs_wr sl)).
Proof.
  apply set_eq. intro x. rewrite vs_todo_elem, elem_of_set_seq.
  rewrite vslot_cache_dom, elem_of_list_to_set, elem_of_list_fmap.
  split.
  - intros [Hx _]. lia.
  - intros Hx. assert (Hlt : (x < wr_nsectors (vs_wr sl))%nat) by lia.
    split; [exact Hlt|]. exists x. split; [reflexivity|].
    apply elem_of_seq. lia.
Qed.

(* THE REQUEST'S WHOLE SECTOR INDEX SET -- what the sequential permit's ROOT
   is indexed at, and what a freshly published request still owes.  A READ
   owes nothing, so this is empty for it.  ([PermInv.perm_deposit_kq] hands
   the client's permit out at exactly this set, which is why the publish site
   needs no conversion at all.) *)
Definition vs_all (sl : vslot) : gset nat :=
  set_seq 0 (wr_nsectors (vs_wr sl)).

Lemma vs_all_elem (sl : vslot) (i : nat) :
  i ∈ vs_all sl <-> (i < wr_nsectors (vs_wr sl))%nat.
Proof. unfold vs_all. rewrite elem_of_set_seq. lia. Qed.

(* what is still owed is always part of it *)
Lemma vs_todo_sub (sl : vslot) (S : gset Z) : vs_todo sl S ⊆ vs_all sl.
Proof.
  intros x Hx. apply vs_todo_elem in Hx as [Hlt _].
  exact (proj2 (vs_all_elem sl x) Hlt).
Qed.

(* ...and a READ's is empty outright *)
Lemma vs_all_read (sl : vslot) : vs_is_out sl = false -> vs_all sl = ∅.
Proof.
  intro Hin. apply set_eq. intro x.
  assert (Hz : wr_nsectors (vs_wr sl) = 0%nat)
    by (unfold vs_wr; rewrite Hin; reflexivity).
  split.
  - intro Hx. apply vs_all_elem in Hx. rewrite Hz in Hx. lia.
  - intro Hx. by apply elem_of_empty in Hx.
Qed.

(* -- THE SECTORS THAT HAVE ALREADY DRAINED, as the complement of what is
   still owed.  [VirtioProto.slot_pend_res] is indexed by the OWED set (the
   permit's own index), and [vs_torn] speaks about the LANDED one, so this is
   the one conversion between the two vocabularies. *)
Definition vs_kept (sl : vslot) (td : gset nat) : gset nat :=
  vs_all sl ∖ td.

(* AT THE PUBLISH nothing has landed *)
Lemma vs_kept_full (sl : vslot) : vs_kept sl (vs_all sl) = ∅.
Proof. unfold vs_kept. apply difference_diag_L. Qed.

(* ...AT THE COMPLETION everything has *)
Lemma vs_kept_nil (sl : vslot) : vs_kept sl ∅ = vs_all sl.
Proof. unfold vs_kept. apply difference_empty_L. Qed.

(* ...and ONE DRAIN moves exactly its own sector across *)
Lemma vs_kept_step (sl : vslot) (td : gset nat) (i : nat) :
  (i < wr_nsectors (vs_wr sl))%nat ->
  vs_kept sl (td ∖ {[ i ]}) = {[ i ]} ∪ vs_kept sl td.
Proof.
  intro Hi.
  assert (Hin : i ∈ vs_all sl) by exact (proj2 (vs_all_elem sl i) Hi).
  unfold vs_kept. apply set_eq. intro x.
  rewrite elem_of_union, elem_of_singleton, !elem_of_difference,
          elem_of_singleton.
  split.
  - intros [Hx Hn]. destruct (decide (x = i)) as [Heq|Hne]; [by left|].
    right. split; [exact Hx|]. intro Htd. apply Hn. by split.
  - intros [Heq|[Hx Hn]].
    + rewrite Heq. split; [exact Hin|]. intros [_ Hne]. by apply Hne.
    + split; [exact Hx|]. intros [Htd _]. by apply Hn.
Qed.

(* a READ owes nothing per-sector *)
Lemma vs_todo_read (sl : vslot) (S : gset Z) :
  vs_is_out sl = false -> vs_todo sl S = ∅.
Proof.
  intro Hin. apply vs_todo_done. intros i Hi.
  exfalso. unfold vs_wr in Hi. rewrite Hin in Hi.
  unfold wr_nsectors in Hi. lia.
Qed.

(* THE COMPLETION GATE, IN THE SLOT'S VOCABULARY: nothing left to drain is
   exactly [VirtioModel.virtio_complete_ok]'s writethrough disjointness. *)
Lemma vs_todo_nil_disj (c : virtio_cfg) (p : nat) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) (S : gset Z) :
  slot_pin_ok c p sl pin ->
  (vs_todo sl S = ∅ <-> vs_sectors sl ∩ S = ∅).
Proof.
  intro Hslot. split.
  - intro Hnil. apply set_eq. intro x. rewrite elem_of_empty.
    rewrite elem_of_intersection. split; [| tauto].
    intros [Hs Hx].
    apply (vs_sectors_spec c p sl pin x Hslot) in Hs as (i & Hi & ->).
    assert (Hin : i ∈ vs_todo sl S) by (apply vs_todo_in; done).
    rewrite Hnil in Hin. by apply elem_of_empty in Hin.
  - intro Hdisj. apply vs_todo_done. intros i Hi Hin.
    assert (Hs : vs_key sl i ∈ vs_sectors sl).
    { apply (vs_sectors_spec c p sl pin _ Hslot). by exists i. }
    assert (Hx : vs_key sl i ∈ vs_sectors sl ∩ S)
      by (apply elem_of_intersection; by split).
    rewrite Hdisj in Hx. by apply elem_of_empty in Hx.
Qed.

(* -- reading an image back as a byte list -- *)

Lemma vq_disk_read_length (dk : Z -> bv 8) (o : Z) (n : nat) :
  length (disk_read dk o n) = n.
Proof. unfold disk_read. by rewrite length_fmap, length_seq. Qed.

Lemma vq_disk_read_lookup (dk : Z -> bv 8) (o : Z) (n j : nat) :
  (j < n)%nat -> disk_read dk o n !! j = Some (dk (o + Z.of_nat j)).
Proof.
  intro Hj. unfold disk_read. rewrite list_lookup_fmap.
  rewrite (lookup_seq_lt 0 n j Hj). reflexivity.
Qed.

(* THE RE-READ IDENTITY: rewriting a window with what an image ALREADY holds
   there reproduces that image, provided the two agree outside the window.
   This is what turns a per-sector image move into a [disk_bytes] update of
   the block the publisher owns. *)
Lemma disk_write_read_range (dk dk' : Z -> bv 8) (o : Z) (n : nat) :
  (forall a : Z, a < o \/ o + Z.of_nat n <= a -> dk' a = dk a) ->
  disk_write dk o (disk_read dk' o n) = dk'.
Proof.
  intro Hout. apply functional_extensionality. intro a.
  destruct (decide (o <= a < o + Z.of_nat n)) as [Hin|Hno].
  - apply disk_write_in; [lia|].
    rewrite (vq_disk_read_lookup dk' o n (Z.to_nat (a - o)) ltac:(lia)).
    f_equal. f_equal. lia.
  - rewrite disk_write_out by (rewrite vq_disk_read_length; lia).
    symmetry. apply Hout. lia.
Qed.

(* ONE SECTOR OF THE SLOT'S WRITE stays inside the block, so re-reading the
   block after a landing is exactly the landing. *)
Lemma vs_sector_image (sl : vslot) (dk : Z -> bv 8) (i : nat) :
  length (vs_data sl) = vs_len sl ->
  disk_write dk (vs_sector_off sl)
    (disk_read (wr_apply (wr_sector (vs_wr sl) i) dk)
               (vs_sector_off sl) (vs_len sl))
  = wr_apply (wr_sector (vs_wr sl) i) dk.
Proof.
  intro Hdlen. apply disk_write_read_range. intros a Ha.
  destruct (vs_is_out sl) eqn:Hout.
  - rewrite (vslot_wr_out sl Hout). apply wr_sector_outside. rewrite Hdlen. lia.
  - assert (Hnone : vs_wr sl = None) by (unfold vs_wr; by rewrite Hout).
    rewrite Hnone, wr_sector_none, wr_apply_none. reflexivity.
Qed.

(* -- the torn content -- *)

Definition vs_torn (sl : vslot) (ld : gset nat) (bs : list (bv 8)) : Prop :=
  forall j : nat, (j < vs_len sl)%nat ->
    Nat.div j virtio_sector_bytes ∈ ld -> bs !! j = vs_data sl !! j.

(* nothing landed yet: no constraint at all *)
Lemma vs_torn_empty (sl : vslot) (bs : list (bv 8)) : vs_torn sl ∅ bs.
Proof. intros j _ Hj. exfalso. by apply elem_of_empty in Hj. Qed.

(* a READ never lands a sector, and its content is pinned outright *)
Lemma vs_torn_data (sl : vslot) (ld : gset nat) : vs_torn sl ld (vs_data sl).
Proof. intros j _ _. reflexivity. Qed.

(* THE PAYOFF: once every sector has landed, the block holds the payload --
   which is what the woken publisher is owed. *)
Lemma vs_torn_full (sl : vslot) (ld : gset nat) (bs : list (bv 8)) :
  length bs = vs_len sl -> length (vs_data sl) = vs_len sl ->
  (forall i, (i < sector_count (vs_len sl))%nat -> i ∈ ld) ->
  vs_torn sl ld bs -> bs = vs_data sl.
Proof.
  intros Hlen Hdlen Hall Htorn. apply list_eq. intro j.
  destruct (decide (j < vs_len sl)%nat) as [Hj|Hj].
  - apply Htorn; [exact Hj|]. apply Hall, sector_count_lt. exact Hj.
  - assert (Hb : bs !! j = None) by (apply lookup_ge_None_2; lia).
    assert (Hd : vs_data sl !! j = None) by (apply lookup_ge_None_2; lia).
    by rewrite Hb, Hd.
Qed.

(* THE STEP: landing sector [i] adds it to the landed set and moves the
   block's content by exactly that sector. *)
Lemma vs_torn_sector (sl : vslot) (dk : Z -> bv 8) (ld : gset nat) (i : nat) :
  vs_is_out sl = true -> length (vs_data sl) = vs_len sl ->
  vs_torn sl ld (disk_read dk (vs_sector_off sl) (vs_len sl)) ->
  vs_torn sl ({[ i ]} ∪ ld)
    (disk_read (wr_apply (wr_sector (vs_wr sl) i) dk)
               (vs_sector_off sl) (vs_len sl)).
Proof.
  intros Hout Hdlen Htorn j Hj Hmem.
  rewrite (vq_disk_read_lookup _ _ _ j Hj).
  rewrite (vslot_wr_out sl Hout).
  pose proof (sector_of_bounds j) as Hb.
  destruct (decide (Nat.div j virtio_sector_bytes = i)) as [Heq|Hne].
  - (* this sector just landed: the byte is the payload's *)
    rewrite <- Heq.
    rewrite (wr_sector_hit (vs_sector_off sl) (vs_data sl)
               (Nat.div j virtio_sector_bytes) _ dk);
      [| unfold virtio_sector_size, virtio_sector_bytes in *; lia
       | unfold virtio_sector_size, virtio_sector_bytes in *; lia ].
    assert (Hsx : is_Some (vs_data sl !! j))
      by (apply lookup_lt_is_Some_2; lia).
    destruct Hsx as [x Hx]. rewrite Hx. f_equal.
    apply (disk_write_in dk (vs_sector_off sl) (vs_data sl)
             (vs_sector_off sl + Z.of_nat j) x); [lia|].
    replace (Z.to_nat (vs_sector_off sl + Z.of_nat j - vs_sector_off sl))
      with j by lia. exact Hx.
  - (* some OTHER sector: the byte is unchanged, and it had already landed *)
    rewrite wr_sector_miss;
      [| destruct (Nat.lt_total (Nat.div j virtio_sector_bytes) i)
           as [Hlt|[He|Hgt]];
         [ left | exfalso; exact (Hne He) | right ];
         unfold virtio_sector_size, virtio_sector_bytes in *; lia ].
    rewrite <- (vq_disk_read_lookup dk (vs_sector_off sl) (vs_len sl) j Hj).
    apply Htorn; [exact Hj|].
    apply elem_of_union in Hmem as [Hmem|Hmem]; [|exact Hmem].
    exfalso. apply Hne. by apply elem_of_singleton in Hmem.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The keyed protocol state and its obligation.                        *)
(* ---------------------------------------------------------------------- *)

(* THE KEYED PROTOCOL STATE.  Positions are [nat] here and never wrap; the
   device counts them in [bv 16] and does ([wrap16] is the bridge, and the
   window bound [vpo_win] is what makes it injective where it matters).

   THE SERVED SET IS NOT AN INTERVAL any more (tools/vtest/README.md finding
   5): the device answers published positions in whatever order it finishes
   them, so [vp_srv] is an arbitrary subset of the published ones and
   [vp_pend] is exactly its complement.  What stays contiguous is the WINDOW:
   [vp_lo] is the lowest unserved position, everything below it is served and
   forgotten, and the ring's eight entries bound its width. *)
Record vproto := VProto {
  vp_nc   : nat;                                (* completions = used index *)
  vp_np   : nat;                                (* published count *)
  vp_lo   : nat;                                (* the watermark *)
  vp_tk   : option nat;                         (* the latched position *)
  vp_srv  : gset nat;                           (* the positions SERVED *)
  vp_pend : gmap nat vslot;                     (* dom = [0,np) minus srv *)
  vp_done : gmap nat vslot;                     (* served, not yet reclaimed *)
  vp_uix  : gmap nat nat;                       (* position -> used index *)
  vp_pin  : gmap nat (gmap Arch.pa (bv 8));     (* per-slot pins *)
}.

(* the served positions the WATERMARK has not absorbed, as the device holds
   them: [VirtioModel.v_ahead] *)
Definition vp_ah_of (lo : nat) (srv : gset nat) : gset (bv 16) :=
  set_map wrap16 (filter (fun q => (lo <= q)%nat) srv).

Definition vp_ah (pr : vproto) : gset (bv 16) := vp_ah_of (vp_lo pr) (vp_srv pr).

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
  (* THE WINDOW.  Published positions split into served and pending; the
     watermark sits at the lowest unserved one; and the live window is at
     most the ring's eight entries wide, which is what makes [wrap16]
     injective on it ([vproto_wrap_inj]).  The width bound is not assumed at
     the publish -- it is DERIVED there, from the fact that position
     [lo + 8] would pin the same ring entry as [lo]. *)
  vpo_srv_np : forall q, q ∈ vp_srv pr -> (q < vp_np pr)%nat;
  vpo_pend_dom : dom (vp_pend pr) = set_seq 0 (vp_np pr) ∖ vp_srv pr;
  vpo_lo_np : (vp_lo pr <= vp_np pr)%nat;
  vpo_lo_srv : forall q, (q < vp_lo pr)%nat -> q ∈ vp_srv pr;
  vpo_lo_min : (vp_lo pr < vp_np pr)%nat -> vp_lo pr ∉ vp_srv pr;
  vpo_win : (vp_np pr - vp_lo pr <= 8)%nat;
  (* the used index counts completions, and each served position has its own *)
  vpo_nc : vp_nc pr = size (vp_srv pr);
  vpo_uix_dom : dom (vp_uix pr) = vp_srv pr;
  vpo_uix_lt : forall q u, vp_uix pr !! q = Some u -> (u < vp_nc pr)%nat;
  vpo_uix_inj : forall q1 q2 u,
      vp_uix pr !! q1 = Some u -> vp_uix pr !! q2 = Some u -> q1 = q2;
  (* ...and every used index below the count is SOME position's: that is what
     lets the interrupt handler, which walks used indices, name the position
     it is looking at *)
  vpo_uix_surj : forall u, (u < vp_nc pr)%nat ->
      exists q, vp_uix pr !! q = Some u;
  (* the capture latch names a request that is still outstanding *)
  vpo_tk : forall q, vp_tk pr = Some q -> q ∈ dom (vp_pend pr);
  vpo_done_lt : forall p, p ∈ dom (vp_done pr) -> p ∈ vp_srv pr;
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

(* pend and done never overlap: done is served, pend is exactly what is not *)
Lemma vproto_pend_done_disj (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa) :
  vproto_ok c pr D -> dom (vp_pend pr) ## dom (vp_done pr).
Proof.
  intro Hok. apply elem_of_disjoint. intros x Hx Hy.
  rewrite (vpo_pend_dom _ _ _ Hok) in Hx.
  pose proof (vpo_done_lt _ _ _ Hok x Hy). set_solver.
Qed.

(* the completion count never runs past the published one *)
Lemma vproto_ncnp (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa) :
  vproto_ok c pr D -> (vp_nc pr <= vp_np pr)%nat.
Proof.
  intro Hok. rewrite (vpo_nc _ _ _ Hok).
  transitivity (size (set_seq 0 (vp_np pr) : gset nat)).
  - apply subseteq_size. intros q Hq. apply elem_of_set_seq.
    pose proof (vpo_srv_np _ _ _ Hok q Hq). lia.
  - by rewrite size_set_seq.
Qed.

(* a pending position is inside the window, and the pending positions are
   exactly the unserved published ones *)
Lemma vproto_pend_win (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (q : nat) :
  vproto_ok c pr D -> q ∈ dom (vp_pend pr) ->
  (vp_lo pr <= q < vp_np pr)%nat.
Proof.
  intros Hok Hq. rewrite (vpo_pend_dom _ _ _ Hok) in Hq.
  apply elem_of_difference in Hq as [Hlt Hns].
  apply elem_of_set_seq in Hlt. split; [| lia ].
  destruct (decide (vp_lo pr <= q)%nat) as [Hle|Hgt]; [exact Hle|].
  exfalso. apply Hns, (vpo_lo_srv _ _ _ Hok). lia.
Qed.

(* THE INJECTIVITY the [bv 16] side needs, and the only thing the window
   bound is for: two distinct positions of one live window never wrap onto
   the same available-ring index. *)
Lemma vproto_wrap_inj (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (q1 q2 : nat) :
  vproto_ok c pr D ->
  (vp_lo pr <= q1 <= vp_np pr)%nat -> (vp_lo pr <= q2 <= vp_np pr)%nat ->
  wrap16 q1 = wrap16 q2 -> q1 = q2.
Proof.
  intros Hok H1 H2 Heq.
  pose proof (vpo_win _ _ _ Hok) as Hw.
  destruct (Nat.lt_total q1 q2) as [Hlt|[He|Hgt]]; [| exact He |].
  - exfalso. exact (wrap16_inj_window q1 q2 Hlt ltac:(lia) Heq).
  - exfalso. exact (wrap16_inj_window q2 q1 Hgt ltac:(lia) (eq_sym Heq)).
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
(* the watermark never runs ahead of the completion count: everything below
   it has been served, and each served position was counted *)
Lemma vproto_lo_nc (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa) :
  vproto_ok c pr D -> (vp_lo pr <= vp_nc pr)%nat.
Proof.
  intro Hok. rewrite (vpo_nc _ _ _ Hok).
  transitivity (size (set_seq 0 (vp_lo pr) : gset nat));
    [ by rewrite size_set_seq | ].
  apply subseteq_size. intros q Hq.
  apply elem_of_set_seq in Hq. apply (vpo_lo_srv _ _ _ Hok). lia.
Qed.

(* AT MOST EIGHT REQUESTS ARE EVER OUTSTANDING, which is the ring's own
   size: this is [vpo_win] read through the completion count. *)
Lemma vproto_window (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa) :
  vproto_ok c pr D -> (vp_np pr - vp_nc pr <= 8)%nat.
Proof.
  intro Hok. pose proof (vproto_lo_nc _ _ _ Hok).
  pose proof (vpo_win _ _ _ Hok). lia.
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
    (wrap16 (vp_np pr)) (wrap16 (vp_lo pr)) (vp_ah pr).
Proof.
  intros Hok _.
  split; [ exact (vproto_ctl_idx c pr D Hok) | ].
  split.
  - (* THE PUBLISHED INDEX IS NOT ONE OF THE SERVED POSITIONS: a served
       position was published, so it is strictly below [np], and [wrap16] is
       injective on the window that contains both. *)
    intro Hc. unfold vp_ah, vp_ah_of in Hc.
    apply elem_of_map_1 in Hc as (q & Heq & Hq).
    apply elem_of_filter in Hq as [Hlo Hsrv].
    pose proof (vpo_srv_np _ _ _ Hok q Hsrv) as Hlt.
    pose proof (vproto_wrap_inj c pr D q (vp_np pr) Hok
                  ltac:(lia) ltac:(pose proof (vpo_lo_np _ _ _ Hok); lia)
                  (eq_sym Heq)). lia.
  - split.
    + (* COVERAGE: a position the device may still serve is a pending one.
         [vpos_pub_wrap16] turns the modular window test into "[lo] plus an
         offset below the width", and the served ones are exactly the ones
         the free test has already excluded. *)
      intros p Hfree. unfold vfree in Hfree.
      apply andb_prop in Hfree as [Hpub Hnah].
      apply (vpos_pub_wrap16 (vp_lo pr) (vp_np pr) p
               (vpo_lo_np _ _ _ Hok) (vpo_win _ _ _ Hok)) in Hpub
        as (k & Hk & ->).
      apply elem_of_map_2.
      rewrite (vpo_pend_dom _ _ _ Hok). apply elem_of_difference. split.
      * apply elem_of_set_seq. lia.
      * intro Hsrv. apply negb_true_iff, bool_decide_eq_false in Hnah.
        apply Hnah. unfold vp_ah, vp_ah_of.
        apply elem_of_map_2, elem_of_filter. split; [lia|exact Hsrv].
    + (* ...and every pending position is a well-formed request whose step
         writes inside the lease. *)
      intros i Hi. apply elem_of_map_1 in Hi as (p & -> & Hp).
      pose proof Hp as Hp'.
      apply elem_of_dom in Hp as [sl Hsl].
      assert (Hpd : p ∈ dom (vp_pin pr)).
      { rewrite (vpo_pin_dom _ _ _ Hok). apply elem_of_union_l, elem_of_dom.
        exists sl. exact Hsl. }
      apply elem_of_dom in Hpd as [pin Hpin].
      pose proof (vproto_pend_slot pr p sl Hsl) as Hs.
      pose proof (vpo_slot _ _ _ Hok p sl pin Hs Hpin) as Hslot.
      intros mv Hview.
      assert (Hvpin : mem_view pin mv).
      { apply (mem_view_subseteq pin (vproto_ctl c pr) mv);
          [ exact (vproto_pin_ctl c pr D p pin Hok Hpin) | exact Hview ]. }
      pose proof (spo_req _ _ _ _ Hslot mv Hvpin) as Hreq.
      split.
      * unfold virtio_chain_ok. unfold req_at in Hreq.
        destruct (chain_at c mv (wrap16 p)) as [[[[h d0] d1] d2]|];
          [reflexivity | discriminate].
      * intros isr lo ah ui dk ca tk cp v' w Hstep.
        destruct (vslot_req_step c p sl pin mv
                    (VirtioState c isr lo ah ui dk ca tk cp) v' w
                    Hslot Hvpin eq_refl Hstep) as [_ Hw].
        cbn [v_used_idx] in Hw. subst w.
        pose proof (vslot_writes_dom_sub c p sl pin ui
                      (cache_view (VirtioState c isr lo ah ui dk ca tk cp))
                      (vpo_qnum _ _ _ Hok) Hslot) as Hsub.
        split.
        -- etransitivity; [ exact Hsub | ]. apply union_least.
           ++ etransitivity; [ apply slot_fp_wr |
                exact (vpo_fp_D _ _ _ Hok p sl pin Hs Hpin) ].
           ++ exact (vpo_used_D _ _ _ Hok).
        -- apply (gset_disj_sub_l _ (slot_wr sl ∪ used_page_pas c));
             [ exact Hsub | exact (vproto_wr_off_ctl c pr D p sl pin Hok Hs Hpin) ].
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. The determined step.                                                *)
(* ---------------------------------------------------------------------- *)

(* A DEVICE WITH WORK TO DO IS A DRIVER THAT PUBLISHED SOMETHING: the
   published index the view reports is pinned to [wrap16 np], and the wrap of
   the window (width <= 8) is injective.  Both determined-step lemmas below
   run through this. *)
(* THE POSITION A DEVICE STEP NAMES IS A PENDING SLOT.  The device works in
   [bv 16] and picks whichever outstanding request it likes; this is what
   turns that choice back into the protocol's own [nat] position, with the
   slot and pin the driver deposited there.  It replaces the old
   "the step is at the head" reasoning, which is exactly the assumption the
   completion-order fix removed. *)
Lemma vproto_serve_slot (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (v : virtio_state) (mv : vmem) (i : bv 16) :
  vproto_ok c pr D ->
  v_cfg v = c -> v_seen v = wrap16 (vp_lo pr) -> v_ahead v = vp_ah pr ->
  mem_view (vproto_ctl c pr) mv ->
  virtio_serve_ok v mv i = true ->
  exists p sl pin,
    (vp_lo pr <= p < vp_np pr)%nat /\ i = wrap16 p
    /\ vp_pend pr !! p = Some sl /\ vp_pin pr !! p = Some pin
    /\ slot_pin_ok c p sl pin.
Proof.
  intros Hok Hcfg Hseen Hah Hview Hserve.
  pose proof (virtio_serve_free _ _ _ Hserve) as Hfree.
  rewrite Hcfg,
          (avail_idx_pinned c (vproto_ctl c pr) mv (wrap16 (vp_np pr))
             Hview (vproto_ctl_idx c pr D Hok)), Hseen, Hah in Hfree.
  destruct (vproto_flat c pr D Hok (vpo_live _ _ _ Hok))
    as (_ & _ & Hcov & _).
  apply Hcov, elem_of_map_1 in Hfree as (p & -> & Hp).
  pose proof (vproto_pend_win c pr D p Hok Hp) as Hwin.
  apply elem_of_dom in Hp as [sl Hsl].
  assert (Hpd : p ∈ dom (vp_pin pr)).
  { rewrite (vpo_pin_dom _ _ _ Hok). apply elem_of_union_l, elem_of_dom.
    exists sl. exact Hsl. }
  apply elem_of_dom in Hpd as [pin Hpin].
  exists p, sl, pin.
  split_and!; [ exact (proj1 Hwin) | exact (proj2 Hwin) | reflexivity
              | exact Hsl | exact Hpin | ].
  exact (vpo_slot _ _ _ Hok _ sl pin (vproto_pend_slot pr _ _ Hsl) Hpin).
Qed.

(* If the device COMPLETES at position [nc], the step it took is COMPUTED by
   the slot: post-state [vslot_post], write set [vslot_writes], and the
   completion gate held.

   RESTATED (sector-atomic-disk.md stage 2) from "here is the step the device
   WILL take" to "here is what the step it TOOK was".  The constructive form
   is no longer provable from the protocol alone -- the completion is gated on
   [virtio_complete_ok], which is a fact about the DEVICE's cache and the
   feature word, not about the queue -- and no caller ever wanted it:
   [VirtioProto] always has the step in hand and only needs to identify it. *)
Lemma vproto_step_det (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (v : virtio_state) (mv : vmem) (i : bv 16) (v' : virtio_state)
    (w : gmap Arch.pa (bv 8)) :
  vproto_ok c pr D ->
  v_cfg v = c -> v_seen v = wrap16 (vp_lo pr) -> v_ahead v = vp_ah pr ->
  mem_view (vproto_ctl c pr) mv ->
  virtio_req_step v mv i = Some (v', w) ->
  exists p sl pin,
    (vp_lo pr <= p < vp_np pr)%nat /\ i = wrap16 p /\
    vp_pend pr !! p = Some sl /\ vp_pin pr !! p = Some pin /\
    slot_pin_ok c p sl pin /\
    mem_view pin mv /\
    virtio_complete_ok v (vs_req sl) (wrap16 p) = true /\
    v' = vslot_post v sl (wrap16 p)
    /\ w = vslot_writes c (v_used_idx v) (cache_view v) sl.
Proof.
  intros Hok Hcfg Hseen Hah Hview Hstep.
  assert (Hs : virtio_serve_ok v mv i = true).
  { unfold virtio_req_step in Hstep.
    destruct (virtio_serve_ok v mv i) eqn:Hs; [reflexivity|]. by cbn in Hstep. }
  destruct (vproto_serve_slot c pr D v mv i Hok Hcfg Hseen Hah Hview Hs)
    as (p & sl & pin & Hwin & -> & Hsl & Hpin & Hslot).
  assert (Hvpin : mem_view pin mv).
  { apply (mem_view_subseteq pin (vproto_ctl c pr) mv);
      [ exact (vproto_pin_ctl c pr D _ pin Hok Hpin) | exact Hview ]. }
  exists p, sl, pin.
  split_and!; [ exact (proj1 Hwin) | exact (proj2 Hwin) | reflexivity
              | exact Hsl | exact Hpin | exact Hslot | exact Hvpin | | | ].
  - exact (vslot_req_step_gate c p sl pin mv v v' w Hslot Hvpin Hcfg Hstep).
  - exact (proj1 (vslot_req_step c p sl pin mv v v' w
                    Hslot Hvpin Hcfg Hstep)).
  - exact (proj2 (vslot_req_step c p sl pin mv v v' w
                    Hslot Hvpin Hcfg Hstep)).
Qed.

(* Conversely, a step that FIRED means something was pending. *)
Lemma vproto_step_pend (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (v : virtio_state) (mv : vmem) (i : bv 16) (v' : virtio_state)
    (w : gmap Arch.pa (bv 8)) :
  vproto_ok c pr D ->
  v_cfg v = c -> v_seen v = wrap16 (vp_lo pr) -> v_ahead v = vp_ah pr ->
  mem_view (vproto_ctl c pr) mv ->
  virtio_req_step v mv i = Some (v', w) ->
  (vp_lo pr < vp_np pr)%nat.
Proof.
  intros Hok Hcfg Hseen Hah Hview Hstep.
  destruct (vproto_step_det c pr D v mv i v' w Hok Hcfg Hseen Hah Hview Hstep)
    as (p & sl & pin & Hlo & Hhi & _). lia.
Qed.

(* THE CAPTURE, at the consumed position (claude-notes/projects/async-disk.md):
   which slot's payload entered the cache, and what the cache became.  The
   request is necessarily a WRITE -- nothing else is captured -- and its data
   had not been taken before, which is what makes the permit the slot is
   holding for it still PENDING.  The DURABLE image does not move at all. *)
Lemma vproto_capture_det (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (v : virtio_state) (mv : vmem) (i : bv 16) (v' : virtio_state) :
  vproto_ok c pr D ->
  v_cfg v = c -> v_seen v = wrap16 (vp_lo pr) -> v_ahead v = vp_ah pr ->
  mem_view (vproto_ctl c pr) mv ->
  virtio_capture_step v mv i = Some v' ->
  exists p sl pin,
    (vp_lo pr <= p < vp_np pr)%nat /\ i = wrap16 p /\
    vp_pend pr !! p = Some sl /\ vp_pin pr !! p = Some pin /\
    slot_pin_ok c p sl pin /\
    vs_is_out sl = true /\ v_taken v = None /\
    v' = VirtioState (v_cfg v) (v_isr v) (v_seen v) (v_ahead v) (v_used_idx v)
           (v_disk v) (vslot_cache sl ∪ v_cache v) (Some i) (v_cap v).
Proof.
  intros Hok Hcfg Hseen Hah Hview Hstep.
  destruct (virtio_capture_step_shape v mv v' i Hstep) as (r & Hr & Hv').
  destruct (virtio_capture_step_enabled v mv v' r i Hr Hstep)
    as (Hs & Hty & Ht).
  destruct (vproto_serve_slot c pr D v mv i Hok Hcfg Hseen Hah Hview Hs)
    as (p & sl & pin & Hwin & Hi & Hsl & Hpin & Hslot).
  assert (Hvpin : mem_view pin mv).
  { apply (mem_view_subseteq pin (vproto_ctl c pr) mv);
      [ exact (vproto_pin_ctl c pr D _ pin Hok Hpin) | exact Hview ]. }
  (* the request the device is working on IS the pinned slot's *)
  assert (Hreq : r = vs_req sl).
  { pose proof (spo_req _ _ _ _ Hslot mv Hvpin) as Hsq.
    rewrite Hcfg, Hi in Hr. rewrite Hr in Hsq. by injection Hsq as <-. }
  subst r.
  assert (Hout : vs_is_out sl = true)
    by (unfold vs_is_out; rewrite Hty; unfold virtio_blk_t_out; reflexivity).
  exists p, sl, pin. split_and!;
    [ exact (proj1 Hwin) | exact (proj2 Hwin) | exact Hi | exact Hsl
    | exact Hpin | exact Hslot | exact Hout | exact Ht | ].
  rewrite Hv', (vslot_vreq_cache c p sl pin mv Hslot Hvpin).
  reflexivity.
Qed.

(* THE DRAIN.  It reads NOTHING off the bus and consults no ring, so nothing
   about it is determined by the queue: what identifies it is the
   WRITETHROUGH INVARIANT -- everything cached belongs to the head request
   ([VirtioModel.virtio_wt_inv]) -- plus the fact that the entries the device
   is holding are the ones its capture deposited.  Given those, the drained
   key names a sector INDEX of the slot, its bytes are that sector's, and the
   durable image moves by exactly [wr_sector (vs_wr sl) i] -- which is the
   permit index the client deposited. *)
Lemma vproto_drain_det (c : virtio_cfg) (p : nat) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) (v : virtio_state) (s : Z) (v' : virtio_state) :
  slot_pin_ok c p sl pin ->
  dom (v_cache v) ⊆ vs_sectors sl ->
  v_cache v ⊆ vslot_cache sl ->
  virtio_drain_step v s = Some v' ->
  exists i, (i < wr_nsectors (vs_wr sl))%nat /\ s = vs_key sl i
    /\ v_cache v !! s = Some (wr_sector_bytes (vs_wr sl) i)
    /\ v' = VirtioState (v_cfg v) (v_isr v) (v_seen v) (v_ahead v)
               (v_used_idx v) (wr_apply (wr_sector (vs_wr sl) i) (v_disk v))
               (delete s (v_cache v)) (v_taken v) (v_cap v).
Proof.
  intros Hslot Hdom Hsub Hstep.
  destruct (virtio_drain_step_shape v s v' Hstep) as (bs & Hbs & Hv').
  assert (Hin : s ∈ vs_sectors sl).
  { apply Hdom, elem_of_dom. by exists bs. }
  apply (vs_sectors_spec c p sl pin s Hslot) in Hin as (i & Hi & ->).
  (* the bytes are the ones the capture deposited for that sector *)
  assert (Hbs' : bs = wr_sector_bytes (vs_wr sl) i).
  { pose proof (lookup_weaken _ _ _ _ Hbs Hsub) as Hlk.
    rewrite (vslot_cache_lookup sl i Hi) in Hlk. by injection Hlk as <-. }
  subst bs.
  exists i. split_and!; [exact Hi|reflexivity|exact Hbs|].
  rewrite Hv'. by rewrite vslot_drain_image.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4b. THE WATERMARK, on both sides of the [wrap16] bridge.                *)
(*                                                                        *)
(*     The device walks its watermark forward past positions it has        *)
(*     already served ([VirtioModel.vseen_adv]); the protocol does the same *)
(*     walk over [nat] positions.  [vseen_adv_vp] is the one lemma that     *)
(*     says the two walks agree -- which is what lets the keyed state       *)
(*     predict the device's [v_seen]/[v_ahead] after a completion.  Both    *)
(*     halves rest on [wrap16] being injective on the live window.          *)
(* ---------------------------------------------------------------------- *)

Fixpoint vp_adv (f lo : nat) (srv : gset nat) : nat :=
  match f with
  | O => lo
  | S f' => if bool_decide (lo ∈ srv) then vp_adv f' (S lo) srv else lo
  end.

(* the walk moves forwards, no further than its fuel, over served positions
   only, and stops at an unserved one unless it ran out *)
Lemma vp_adv_ge (f lo : nat) (srv : gset nat) : (lo <= vp_adv f lo srv)%nat.
Proof.
  revert lo. induction f as [|f IH]; intro lo; cbn [vp_adv]; [lia|].
  destruct (bool_decide (lo ∈ srv)); [| lia ].
  pose proof (IH (S lo)). lia.
Qed.

Lemma vp_adv_le (f lo : nat) (srv : gset nat) :
  (vp_adv f lo srv <= lo + f)%nat.
Proof.
  revert lo. induction f as [|f IH]; intro lo; cbn [vp_adv]; [lia|].
  destruct (bool_decide (lo ∈ srv)); [| lia ].
  pose proof (IH (S lo)). lia.
Qed.

Lemma vp_adv_below (f lo q : nat) (srv : gset nat) :
  (lo <= q)%nat -> (q < vp_adv f lo srv)%nat -> q ∈ srv.
Proof.
  revert lo. induction f as [|f IH]; intros lo Hlo Hq; cbn [vp_adv] in Hq;
    [lia|].
  destruct (bool_decide (lo ∈ srv)) eqn:Hin; [| lia ].
  apply bool_decide_eq_true in Hin.
  destruct (decide (q = lo)) as [->|Hne]; [exact Hin|].
  apply (IH (S lo)); [lia|exact Hq].
Qed.

(* THE PENDING SET'S DOMAIN, moved by hand rather than by [set_solver]:
   these are the two shapes the transitions produce, and a general set
   solver builds a proof term over [set_seq] that is expensive to check. *)
Lemma pend_dom_publish (np : nat) (srv : gset nat) :
  np ∉ srv ->
  {[ np ]} ∪ (set_seq 0 np ∖ srv) = set_seq 0 (S np) ∖ srv.
Proof. intro Hn. rewrite set_seq_S_end_union_L. set_solver. Qed.

Lemma pend_dom_step (np p : nat) (srv : gset nat) :
  (set_seq 0 np ∖ srv) ∖ {[ p ]} = set_seq 0 np ∖ ({[ p ]} ∪ srv).
Proof. set_solver. Qed.

(* THE WATERMARK AFTER A SERVE.  Named rather than written inline so that
   [cbn] cannot unfold the walk's fuel into a term of a thousand matches. *)
Definition vp_lo_next (lo : nat) (srv : gset nat) : nat := vp_adv 8 lo srv.

Lemma vp_adv_np (f lo np : nat) (srv : gset nat) :
  (forall q, q ∈ srv -> (q < np)%nat) -> (lo <= np)%nat ->
  (vp_adv f lo srv <= np)%nat.
Proof.
  revert lo. induction f as [|f IH]; intros lo Hsrv Hle; cbn [vp_adv]; [lia|].
  destruct (bool_decide (lo ∈ srv)) eqn:Hin; [| lia ].
  apply bool_decide_eq_true in Hin. pose proof (Hsrv lo Hin).
  apply IH; [exact Hsrv|lia].
Qed.

Lemma vp_adv_stop (f lo : nat) (srv : gset nat) :
  vp_adv f lo srv = (lo + f)%nat \/ vp_adv f lo srv ∉ srv.
Proof.
  revert lo. induction f as [|f IH]; intro lo; cbn [vp_adv]; [left; lia|].
  destruct (bool_decide (lo ∈ srv)) eqn:Hin.
  - destruct (IH (S lo)) as [He|Hn]; [left; lia | by right].
  - right. apply bool_decide_eq_false in Hin. exact Hin.
Qed.

(* membership in the device's served set, read back as a [nat] position *)
Lemma vp_ah_of_mem (lo np q : nat) (srv : gset nat) :
  (lo <= np)%nat -> (np - lo <= 8)%nat ->
  (forall r, r ∈ srv -> (r < np)%nat) -> (lo <= q <= np)%nat ->
  wrap16 q ∈ vp_ah_of lo srv <-> (q ∈ srv /\ (lo <= q)%nat).
Proof.
  intros Hle Hw Hsrv Hq. unfold vp_ah_of. split.
  - intro Hin. apply elem_of_map_1 in Hin as (r & Heq & Hr).
    apply elem_of_filter in Hr as [Hlo Hrs].
    pose proof (Hsrv r Hrs) as Hrn.
    assert (r = q).
    { destruct (Nat.lt_total r q) as [Hlt|[He|Hgt]]; [| exact He |].
      - exfalso. exact (wrap16_inj_window r q Hlt ltac:(lia) (eq_sym Heq)).
      - exfalso. exact (wrap16_inj_window q r Hgt ltac:(lia) Heq). }
    subst r. by split.
  - intros [Hqs Hlo]. apply elem_of_map_2, elem_of_filter. by split.
Qed.

(* ...and one step of the walk, on the device's side *)
Lemma vp_ah_of_succ (lo np : nat) (srv : gset nat) :
  (lo <= np)%nat -> (np - lo <= 8)%nat ->
  (forall r, r ∈ srv -> (r < np)%nat) ->
  vp_ah_of lo srv ∖ {[ wrap16 lo ]} = vp_ah_of (S lo) srv.
Proof.
  intros Hle Hw Hsrv. apply set_eq. intro x. split.
  - intro Hx. apply elem_of_difference in Hx as [Hin Hne].
    unfold vp_ah_of in Hin |- *.
    apply elem_of_map_1 in Hin as (r & -> & Hr).
    apply elem_of_filter in Hr as [Hlo Hrs].
    apply elem_of_map_2, elem_of_filter. split; [| exact Hrs ].
    destruct (decide (r = lo)) as [->|Hrl]; [ set_solver | lia ].
  - intro Hx. unfold vp_ah_of in Hx |- *.
    apply elem_of_map_1 in Hx as (r & -> & Hr).
    apply elem_of_filter in Hr as [Hlo Hrs].
    pose proof (Hsrv r Hrs) as Hrn.
    apply elem_of_difference. split.
    + apply elem_of_map_2, elem_of_filter. split; [lia|exact Hrs].
    + intro Hc. apply elem_of_singleton in Hc.
      exact (wrap16_inj_window lo r ltac:(lia) ltac:(lia) (eq_sym Hc)).
Qed.

(* THE TWO WALKS AGREE.  Both stop at the first unserved position, and they
   take the same steps to get there, so ONE fuel serves for both. *)
Lemma vseen_adv_vp (f lo np : nat) (srv : gset nat) :
  (lo <= np)%nat -> (np - lo <= 8)%nat ->
  (forall q, q ∈ srv -> (q < np)%nat) ->
  vseen_adv f (wrap16 lo) (vp_ah_of lo srv)
  = (wrap16 (vp_adv f lo srv), vp_ah_of (vp_adv f lo srv) srv).
Proof.
  revert lo. induction f as [|f IH]; intros lo Hle Hw Hsrv;
    cbn [vseen_adv vp_adv]; [reflexivity|].
  destruct (decide (lo ∈ srv)) as [Hin|Hout].
  - (* served: both walks advance *)
    pose proof (Hsrv lo Hin) as Hlon.
    rewrite (bool_decide_eq_true_2 (wrap16 lo ∈ vp_ah_of lo srv))
      by (apply (vp_ah_of_mem lo np lo srv Hle Hw Hsrv ltac:(lia)); by split).
    rewrite (vp_ah_of_succ lo np srv Hle Hw Hsrv).
    rewrite (bool_decide_eq_true_2 (lo ∈ srv) Hin).
    unfold one16. rewrite <- wrap16_S.
    apply IH; [lia|lia|exact Hsrv].
  - (* unserved: both stop here *)
    rewrite (bool_decide_eq_false_2 (wrap16 lo ∈ vp_ah_of lo srv))
      by (rewrite (vp_ah_of_mem lo np lo srv Hle Hw Hsrv ltac:(lia));
          intros [Hc _]; exact (Hout Hc)).
    by rewrite (bool_decide_eq_false_2 (lo ∈ srv) Hout).
Qed.

(* the keyed obligation survives its own step: [nc] moves from pend to done *)
Definition vproto_step_state (pr : vproto) (p : nat) (sl : vslot) : vproto :=
  VProto (S (vp_nc pr)) (vp_np pr)
         (vp_lo_next (vp_lo pr) ({[ p ]} ∪ vp_srv pr))
         (* THE LATCH IS RELEASED ONLY BY ITS OWN REQUEST
            ([VirtioModel.virtio_complete]): completing some other position
            leaves another request's captured payload where it was. *)
         (if bool_decide (vp_tk pr = Some p) then None else vp_tk pr)
         ({[ p ]} ∪ vp_srv pr)
         (delete p (vp_pend pr))
         (<[ p := sl ]> (vp_done pr))
         (<[ p := vp_nc pr ]> (vp_uix pr))
         (vp_pin pr).

Lemma vproto_ok_step (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (p : nat) (sl : vslot) :
  vproto_ok c pr D ->
  vp_pend pr !! p = Some sl ->
  vproto_ok c (vproto_step_state pr p sl) D.
Proof.
  intros Hok Hsl.
  assert (Hslots : vp_slots (vproto_step_state pr p sl) = vp_slots pr).
  { unfold vp_slots, vproto_step_state. cbn [vp_pend vp_done].
    apply map_eq. intro q. destruct (decide (q = p)) as [->|Hne].
    - rewrite lookup_union_r by apply lookup_delete.
      rewrite lookup_insert. symmetry. apply lookup_union_Some_l. exact Hsl.
    - rewrite !lookup_union, lookup_delete_ne by congruence.
      rewrite lookup_insert_ne by congruence. reflexivity. }
  assert (Hpd : p ∈ dom (vp_pend pr))
    by (apply elem_of_dom; exists sl; exact Hsl).
  pose proof Hpd as Hpd'. rewrite (vpo_pend_dom _ _ _ Hok) in Hpd'.
  apply elem_of_difference in Hpd' as [Hplt Hpns].
  apply elem_of_set_seq in Hplt.
  pose proof (vproto_pend_win c pr D p Hok Hpd) as Hwin.
  pose proof (vpo_win _ _ _ Hok) as Hw8.
  pose proof (vpo_lo_np _ _ _ Hok) as Hlonp.
  (* the served set after the step, and the positions it bounds *)
  set (srv' := {[ p ]} ∪ vp_srv pr).
  assert (Hsrv' : forall q, q ∈ srv' -> (q < vp_np pr)%nat).
  { intros q Hq. apply elem_of_union in Hq as [Hq|Hq].
    - apply elem_of_singleton in Hq. lia.
    - exact (vpo_srv_np _ _ _ Hok q Hq). }
  set (lo' := vp_lo_next (vp_lo pr) srv').
  assert (Hlo'ge : (vp_lo pr <= lo')%nat) by apply vp_adv_ge.
  assert (Hlo'le : (lo' <= vp_np pr)%nat)
    by exact (vp_adv_np 8 (vp_lo pr) (vp_np pr) srv' Hsrv' Hlonp).
  constructor.
  - exact (vpo_qnum _ _ _ Hok).
  - exact (vpo_live _ _ _ Hok).
  - unfold vproto_step_state. cbn [vp_srv vp_np]. exact Hsrv'.
  - unfold vproto_step_state. cbn [vp_np vp_pend vp_srv].
    rewrite dom_delete_L, (vpo_pend_dom _ _ _ Hok). apply pend_dom_step.
  - unfold vproto_step_state. cbn [vp_lo vp_np]. unfold vp_lo_next.
    exact (vp_adv_np 8 (vp_lo pr) (vp_np pr) ({[ p ]} ∪ vp_srv pr)
             Hsrv' Hlonp).
  - unfold vproto_step_state. cbn [vp_lo vp_srv]. unfold vp_lo_next.
    intros q Hq.
    destruct (decide (q < vp_lo pr)%nat) as [Hlt|Hge].
    + apply elem_of_union_r, (vpo_lo_srv _ _ _ Hok). exact Hlt.
    + apply (vp_adv_below 8 (vp_lo pr) q ({[ p ]} ∪ vp_srv pr));
        [lia|exact Hq].
  - unfold vproto_step_state. cbn [vp_lo vp_np vp_srv]. intro Hlt.
    unfold vp_lo_next in Hlt |- *.
    destruct (vp_adv_stop 8 (vp_lo pr) ({[ p ]} ∪ vp_srv pr)) as [He|Hn];
      [| exact Hn ].
    exfalso. rewrite He in Hlt. lia.
  - unfold vproto_step_state. cbn [vp_lo vp_np]. unfold vp_lo_next.
    pose proof (vp_adv_ge 8 (vp_lo pr) ({[ p ]} ∪ vp_srv pr)). lia.
  - (* the completion count is the served set's size, and [p] is new to it *)
    unfold vproto_step_state. cbn [vp_nc vp_srv].
    rewrite (vpo_nc _ _ _ Hok), size_union by set_solver.
    rewrite size_singleton. lia.
  - unfold vproto_step_state. cbn [vp_uix vp_srv].
    rewrite dom_insert_L, (vpo_uix_dom _ _ _ Hok). reflexivity.
  - unfold vproto_step_state. cbn [vp_uix vp_nc]. intros q u Hq.
    destruct (decide (q = p)) as [->|Hne].
    + rewrite lookup_insert in Hq. injection Hq as <-. lia.
    + rewrite lookup_insert_ne in Hq by congruence.
      pose proof (vpo_uix_lt _ _ _ Hok q u Hq). lia.
  - unfold vproto_step_state. cbn [vp_uix]. intros q1 q2 u H1 H2.
    assert (Hfresh : forall q u', vp_uix pr !! q = Some u' -> u' <> vp_nc pr).
    { intros q u' Hu. pose proof (vpo_uix_lt _ _ _ Hok q u' Hu). lia. }
    destruct (decide (q1 = p)) as [->|H1n]; destruct (decide (q2 = p)) as [->|H2n].
    + reflexivity.
    + rewrite lookup_insert in H1. injection H1 as <-.
      rewrite lookup_insert_ne in H2 by congruence.
      exfalso. exact (Hfresh q2 _ H2 eq_refl).
    + rewrite lookup_insert in H2. injection H2 as <-.
      rewrite lookup_insert_ne in H1 by congruence.
      exfalso. exact (Hfresh q1 _ H1 eq_refl).
    + rewrite lookup_insert_ne in H1 by congruence.
      rewrite lookup_insert_ne in H2 by congruence.
      exact (vpo_uix_inj _ _ _ Hok q1 q2 u H1 H2).
  - unfold vproto_step_state. cbn [vp_uix vp_nc]. intros u Hu.
    destruct (decide (u = vp_nc pr)) as [->|Hne].
    + exists p. apply lookup_insert.
    + destruct (vpo_uix_surj _ _ _ Hok u ltac:(lia)) as [q Hq].
      exists q. rewrite lookup_insert_ne; [exact Hq|].
      (* [p] had no used index before the step: it was pending *)
      intro Hpq.
      assert (Hpd2 : p ∈ dom (vp_uix pr)).
      { apply elem_of_dom. exists u. by rewrite Hpq. }
      rewrite (vpo_uix_dom _ _ _ Hok) in Hpd2. contradiction.
  - unfold vproto_step_state. cbn [vp_tk vp_pend]. intros q Hq.
    destruct (bool_decide (vp_tk pr = Some p)) eqn:Hb; [discriminate|].
    apply bool_decide_eq_false in Hb.
    assert (Hne : q <> p) by (intro Hc; subst q; exact (Hb Hq)).
    rewrite dom_delete_L. apply elem_of_difference.
    split; [ exact (vpo_tk _ _ _ Hok q Hq) | set_solver ].
  - unfold vproto_step_state. cbn [vp_done vp_srv]. intros q Hq.
    rewrite dom_insert_L in Hq. apply elem_of_union in Hq as [Hq|Hq].
    + apply elem_of_singleton in Hq. subst q. set_solver.
    + apply elem_of_union_r. exact (vpo_done_lt _ _ _ Hok q Hq).
  - unfold vproto_step_state. cbn [vp_pend vp_done vp_pin].
    rewrite dom_delete_L, dom_insert_L, (vpo_pin_dom _ _ _ Hok).
    apply gset_union_split. exact Hpd.
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

(* THE STEP'S EFFECT ON THE DEVICE'S OWN WATERMARK AND SERVED SET: exactly
   what [VirtioModel.vserve] computes, which is what lets the keyed state
   predict the post-state of a completion. *)
Lemma vproto_step_vserve (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (p : nat) (sl : vslot) :
  vproto_ok c pr D ->
  vp_pend pr !! p = Some sl ->
  vserve (wrap16 (vp_lo pr)) (vp_ah pr) (wrap16 p)
  = (wrap16 (vp_lo (vproto_step_state pr p sl)),
     vp_ah (vproto_step_state pr p sl)).
Proof.
  intros Hok Hsl.
  assert (Hpd : p ∈ dom (vp_pend pr))
    by (apply elem_of_dom; exists sl; exact Hsl).
  destruct (vproto_pend_win c pr D p Hok Hpd) as [Hwlo Hwhi].
  pose proof (vpo_win _ _ _ Hok) as Hw8.
  pose proof (vpo_lo_np _ _ _ Hok) as Hlonp.
  set (srv' := {[ p ]} ∪ vp_srv pr).
  assert (Hsrv' : forall q, q ∈ srv' -> (q < vp_np pr)%nat).
  { intros q Hq. apply elem_of_union in Hq as [Hq|Hq].
    - apply elem_of_singleton in Hq. lia.
    - exact (vpo_srv_np _ _ _ Hok q Hq). }
  (* the device's set after the mark IS the protocol's *)
  assert (Hah : {[ wrap16 p ]} ∪ vp_ah pr = vp_ah_of (vp_lo pr) srv').
  { unfold vp_ah, vp_ah_of, srv'.
    rewrite filter_union_L, set_map_union_L.
    assert (Hfs : filter (fun q => (vp_lo pr <= q)%nat) ({[ p ]} : gset nat)
                  = {[ p ]}) by (apply filter_singleton_L; [apply _|exact Hwlo]).
    rewrite Hfs, set_map_singleton_L. reflexivity. all: apply _. }
  (* one fuel serves both walks, so they run in lockstep *)
  unfold vserve. rewrite Hah.
  unfold vproto_step_state. cbn [vp_lo vp_srv].
  unfold vp_ah. cbn [vp_lo vp_srv].
  unfold vp_lo_next.
  apply (vseen_adv_vp 8 (vp_lo pr) (vp_np pr) srv');
    [ lia | lia | exact Hsrv' ].
Qed.

(* the step does not move the control map: the device writes no pinned byte *)
Lemma vproto_step_ctl (c : virtio_cfg) (pr : vproto) (p : nat) (sl : vslot) :
  vproto_ctl c (vproto_step_state pr p sl) = vproto_ctl c pr.
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

(* THE CAPTURE: the latch takes a position, and nothing else moves. *)
Definition vproto_capture_state (pr : vproto) (p : nat) : vproto :=
  VProto (vp_nc pr) (vp_np pr) (vp_lo pr) (Some p) (vp_srv pr)
         (vp_pend pr) (vp_done pr) (vp_uix pr) (vp_pin pr).

Lemma vproto_ok_capture (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (p : nat) (sl : vslot) :
  vproto_ok c pr D -> vp_pend pr !! p = Some sl ->
  vproto_ok c (vproto_capture_state pr p) D.
Proof.
  intros Hok Hsl. constructor.
  - exact (vpo_qnum _ _ _ Hok).
  - exact (vpo_live _ _ _ Hok).
  - exact (vpo_srv_np _ _ _ Hok).
  - exact (vpo_pend_dom _ _ _ Hok).
  - exact (vpo_lo_np _ _ _ Hok).
  - exact (vpo_lo_srv _ _ _ Hok).
  - exact (vpo_lo_min _ _ _ Hok).
  - exact (vpo_win _ _ _ Hok).
  - exact (vpo_nc _ _ _ Hok).
  - exact (vpo_uix_dom _ _ _ Hok).
  - exact (vpo_uix_lt _ _ _ Hok).
  - exact (vpo_uix_inj _ _ _ Hok).
  - exact (vpo_uix_surj _ _ _ Hok).
  - unfold vproto_capture_state. cbn [vp_tk vp_pend]. intros q Hq.
    injection Hq as <-. apply elem_of_dom. by exists sl.
  - exact (vpo_done_lt _ _ _ Hok).
  - exact (vpo_pin_dom _ _ _ Hok).
  - exact (vpo_slot _ _ _ Hok).
  - exact (vpo_fp_disj _ _ _ Hok).
  - exact (vpo_wr_pin _ _ _ Hok).
  - exact (vpo_standing _ _ _ Hok).
  - exact (vpo_idx_used _ _ _ Hok).
  - exact (vpo_fp_D _ _ _ Hok).
  - exact (vpo_used_D _ _ _ Hok).
  - exact (vpo_idx_D _ _ _ Hok).
Qed.

Lemma vproto_capture_ctl (c : virtio_cfg) (pr : vproto) (p : nat) :
  vproto_ctl c (vproto_capture_state pr p) = vproto_ctl c pr.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 5. Publish: appending slot [np].                                       *)
(* ---------------------------------------------------------------------- *)

Definition vproto_publish_state (pr : vproto) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) : vproto :=
  VProto (vp_nc pr) (S (vp_np pr)) (vp_lo pr) (vp_tk pr) (vp_srv pr)
         (<[ vp_np pr := sl ]> (vp_pend pr))
         (vp_done pr)
         (vp_uix pr)
         (<[ vp_np pr := pin ]> (vp_pin pr)).

(* Projections of the publish state as REWRITE RULES.  [cbn] must not be
   pointed at these goals: the published count appears as [S (vp_np pr)] and
   [cbn] would unfold [set_seq 0 (S _)] one step and then normalise the
   resulting gset union into its map representation, which is a term the size
   of the window and takes minutes to build. *)
Lemma vppq_nc (pr : vproto) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vp_nc (vproto_publish_state pr sl pin) = vp_nc pr.
Proof. reflexivity. Qed.
Lemma vppq_np (pr : vproto) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vp_np (vproto_publish_state pr sl pin) = S (vp_np pr).
Proof. reflexivity. Qed.
Lemma vppq_lo (pr : vproto) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vp_lo (vproto_publish_state pr sl pin) = vp_lo pr.
Proof. reflexivity. Qed.
Lemma vppq_tk (pr : vproto) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vp_tk (vproto_publish_state pr sl pin) = vp_tk pr.
Proof. reflexivity. Qed.
Lemma vppq_srv (pr : vproto) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vp_srv (vproto_publish_state pr sl pin) = vp_srv pr.
Proof. reflexivity. Qed.
Lemma vppq_pend (pr : vproto) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vp_pend (vproto_publish_state pr sl pin) = <[ vp_np pr := sl ]> (vp_pend pr).
Proof. reflexivity. Qed.
Lemma vppq_done (pr : vproto) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vp_done (vproto_publish_state pr sl pin) = vp_done pr.
Proof. reflexivity. Qed.
Lemma vppq_uix (pr : vproto) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vp_uix (vproto_publish_state pr sl pin) = vp_uix pr.
Proof. reflexivity. Qed.
Lemma vppq_pin (pr : vproto) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vp_pin (vproto_publish_state pr sl pin) = <[ vp_np pr := pin ]> (vp_pin pr).
Proof. reflexivity. Qed.

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
  pose proof (vproto_ncnp _ _ _ Hok) as Hle.
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
  (* THE WINDOW CANNOT SATURATE, and this is where that is proved rather
     than assumed: if the window were already eight wide, the watermark's own
     position would be pending, and the entry it pins in the available ring
     is the very one this publish is claiming ([lo] and [lo+8] are the same
     ring slot).  The publisher's fresh pin is disjoint from the lease, which
     holds that one -- so the eighth publish cannot happen. *)
  assert (Hnotfull : (vp_np pr - vp_lo pr < 8)%nat).
  { pose proof (vpo_win _ _ _ Hok) as Hw8.
    destruct (decide (vp_np pr - vp_lo pr < 8)%nat) as [Hlt|Hge]; [exact Hlt|].
    exfalso.
    assert (Heq : (vp_np pr = vp_lo pr + 8)%nat)
      by (pose proof (vpo_lo_np _ _ _ Hok); lia).
    assert (Hlolt : (vp_lo pr < vp_np pr)%nat) by lia.
    assert (Hlopd : vp_lo pr ∈ dom (vp_pend pr)).
    { rewrite (vpo_pend_dom _ _ _ Hok). apply elem_of_difference.
      split; [ apply elem_of_set_seq; lia | exact (vpo_lo_min _ _ _ Hok Hlolt) ]. }
    apply elem_of_dom in Hlopd as [sllo Hsllo].
    assert (Hpdlo : vp_lo pr ∈ dom (vp_pin pr)).
    { rewrite (vpo_pin_dom _ _ _ Hok). apply elem_of_union_l, elem_of_dom.
      exists sllo. exact Hsllo. }
    apply elem_of_dom in Hpdlo as [pinlo Hpinlo].
    pose proof (vproto_pend_slot pr _ _ Hsllo) as Hslo.
    pose proof (vpo_slot _ _ _ Hok _ sllo pinlo Hslo Hpinlo) as Hslotlo.
    (* both pins hold the same ring entry *)
    assert (Hring : ring_entry_pa c (vp_np pr) = ring_entry_pa c (vp_lo pr)).
    { unfold ring_entry_pa. f_equal. f_equal. f_equal.
      rewrite Heq, Nat2Z.inj_add. change (Z.of_nat 8) with 8.
      replace (Z.of_nat (vp_lo pr) + 8) with (Z.of_nat (vp_lo pr) + 1 * 8)
        by lia.
      apply Z_mod_plus_full. }
    assert (Hin1 : ring_entry_pa c (vp_np pr) ∈ dom pin).
    { apply (read_bytes_dom_sub pin (ring_entry_pa c (vp_np pr)) 2 _
               (spo_ring _ _ _ _ Hnew)).
      apply pa_range_base. change (N.to_nat 2) with 2%nat. lia. }
    assert (Hin2 : ring_entry_pa c (vp_lo pr) ∈ dom pinlo).
    { apply (read_bytes_dom_sub pinlo (ring_entry_pa c (vp_lo pr)) 2 _
               (spo_ring _ _ _ _ Hslotlo)).
      apply pa_range_base. change (N.to_nat 2) with 2%nat. lia. }
    rewrite Hring in Hin1.
    exact (proj1 (elem_of_disjoint _ _) Hdisj _ (slot_fp_pin sl pin _ Hin1)
             (proj1 (elem_of_subseteq _ _)
                (vpo_fp_D _ _ _ Hok _ sllo pinlo Hslo Hpinlo) _
                (slot_fp_pin sllo pinlo _ Hin2))). }
  assert (Hnpsrv : vp_np pr ∉ vp_srv pr).
  { intro Hc. pose proof (vpo_srv_np _ _ _ Hok _ Hc). lia. }
  constructor.
  - exact (vpo_qnum _ _ _ Hok).
  - exact (vpo_live _ _ _ Hok).
  - rewrite vppq_srv, vppq_np. intros q Hq.
    pose proof (vpo_srv_np _ _ _ Hok q Hq). lia.
  - rewrite vppq_pend, vppq_np, vppq_srv.
    rewrite dom_insert_L, (vpo_pend_dom _ _ _ Hok).
    apply pend_dom_publish. exact Hnpsrv.
  - rewrite vppq_lo, vppq_np. pose proof (vpo_lo_np _ _ _ Hok). lia.
  - rewrite vppq_lo, vppq_srv. exact (vpo_lo_srv _ _ _ Hok).
  - rewrite vppq_lo, vppq_np, vppq_srv. intro Hlt.
    destruct (decide (vp_lo pr < vp_np pr)%nat) as [Hlo|Hlo].
    + exact (vpo_lo_min _ _ _ Hok Hlo).
    + intro Hc. apply Hnpsrv.
      assert (He : vp_lo pr = vp_np pr)
        by (pose proof (vpo_lo_np _ _ _ Hok); lia).
      by rewrite <- He.
  - rewrite vppq_lo, vppq_np. lia.
  - rewrite vppq_nc, vppq_srv. exact (vpo_nc _ _ _ Hok).
  - rewrite vppq_uix, vppq_srv. exact (vpo_uix_dom _ _ _ Hok).
  - rewrite vppq_uix, vppq_nc. exact (vpo_uix_lt _ _ _ Hok).
  - rewrite vppq_uix. exact (vpo_uix_inj _ _ _ Hok).
  - rewrite vppq_uix, vppq_nc. exact (vpo_uix_surj _ _ _ Hok).
  - rewrite vppq_tk, vppq_pend. intros q Hq.
    rewrite dom_insert_L. apply elem_of_union_r.
    exact (vpo_tk _ _ _ Hok q Hq).
  - rewrite vppq_done, vppq_srv. exact (vpo_done_lt _ _ _ Hok).
  - rewrite vppq_pend, vppq_done, vppq_pin.
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
    - rewrite (vpo_pend_dom _ _ _ Hok) in Hc.
      apply elem_of_difference in Hc as [Hc _].
      apply elem_of_set_seq in Hc. lia.
    - pose proof (vpo_srv_np _ _ _ Hok _ (vpo_done_lt _ _ _ Hok _ Hc)). lia. }
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
  VProto (vp_nc pr) (vp_np pr) (vp_lo pr) (vp_tk pr) (vp_srv pr)
         (vp_pend pr) (delete p (vp_done pr)) (vp_uix pr)
         (delete p (vp_pin pr)).

Lemma vproto_ok_reclaim (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (p : nat) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vproto_ok c pr D ->
  vp_done pr !! p = Some sl -> vp_pin pr !! p = Some pin ->
  vproto_ok c (vproto_reclaim_state pr p) (D ∖ slot_fp sl pin).
Proof.
  intros Hok Hdone Hpin.
  assert (Hpsrv : p ∈ vp_srv pr).
  { apply (vpo_done_lt _ _ _ Hok), elem_of_dom. exists sl. exact Hdone. }
  assert (Hnpend : vp_pend pr !! p = None).
  { apply not_elem_of_dom. rewrite (vpo_pend_dom _ _ _ Hok). set_solver. }
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
  - exact (vpo_srv_np _ _ _ Hok).
  - exact (vpo_pend_dom _ _ _ Hok).
  - exact (vpo_lo_np _ _ _ Hok).
  - exact (vpo_lo_srv _ _ _ Hok).
  - exact (vpo_lo_min _ _ _ Hok).
  - exact (vpo_win _ _ _ Hok).
  - exact (vpo_nc _ _ _ Hok).
  - exact (vpo_uix_dom _ _ _ Hok).
  - exact (vpo_uix_lt _ _ _ Hok).
  - exact (vpo_uix_inj _ _ _ Hok).
  - exact (vpo_uix_surj _ _ _ Hok).
  - exact (vpo_tk _ _ _ Hok).
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
  assert (Hpsrv : p ∈ vp_srv pr).
  { apply (vpo_done_lt _ _ _ Hok), elem_of_dom. exists sl. exact Hdone. }
  assert (Hnpend : vp_pend pr !! p = None).
  { apply not_elem_of_dom. rewrite (vpo_pend_dom _ _ _ Hok). set_solver. }
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

Definition vproto0 : vproto := VProto 0 0 0 None ∅ ∅ ∅ ∅ ∅.

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
  - intros q Hq0. exfalso. exact (proj1 (elem_of_empty q) Hq0).
  - rewrite Hpend0, dom_empty_L. set_solver.
  - reflexivity.
  - intros q Hq0. exfalso. unfold vproto0 in Hq0. cbn [vp_lo] in Hq0. lia.
  - intros _. set_solver.
  - reflexivity.
  - by rewrite size_empty.
  - by rewrite dom_empty_L.
  - intros q u Hu. rewrite lookup_empty in Hu. discriminate.
  - intros q1 q2 u Hu _. rewrite lookup_empty in Hu. discriminate.
  - intros u Hu. exfalso. cbn in Hu. lia.
  - discriminate.
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
