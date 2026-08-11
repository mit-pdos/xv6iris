(** * WeakVariant.v — batch-6 P1: the variant lattice of a kernel-PT leaf
    window under weak execution

    THE RACY SURFACE of a kernel-table translation is ONE 8-byte leaf window
    (batch-6 design block, fact 1): every message ever appended to it is an
    A/D variant [PtAdBits.pte_set_ad w0 a d] of the canonical leaf [w0], and
    A/D are bits 6/7 — both in BYTE 0 of the little-endian word (fact 2).
    This file is the PURE layer that turns those two facts into the lemmas
    the weak absorption theorem (P4) consumes:

    §1  BYTE STABILITY: a variant agrees with [w0] on bytes 1–7, and ANY
        per-byte mixture of variant bytes assembles back to a variant (the
        load-mixture lemma) — so a weak read that picks a different message
        per byte still returns a variant.
    §2  THE VALUE-PINNED BYTE: a byte all of whose log values agree behaves
        SC — every admissible read returns THE value.  This is what makes
        bytes 1–7 of the window deterministic.
    §3  THE VALUE-CLOSURE PREDICATE [wlog_variants log a8 w0] ("every log
        message touching the window writes variant bytes"), its monotonicity
        under appends, its preservation across a CAS-model write-back (the
        written word is [update_PTE_Bits] of a fresh word that is itself a
        variant — [pte_set_ad_absorb] closes the loop), and the collapse of
        [WeakRacy.wadm] / [WeakInterp.wread_ok] at the window: the read word
        IS a variant (7 bytes pinned + byte 0 enumerated).
    §4  BIT-MONOTONICITY UNDER THE CAS DISCIPLINE.  Historically the log was
        NOT monotone (a stale plain write-back could regress D at the top of
        the log — the recorded non-monotonicity finding); under the LANDED
        atomic-recheck model every write derives from the log-latest value
        with bits only ORed, and monotonicity is RESTORED: if every window
        write is fresh-derived ([wbyte_fresh_derived]), the A/D bits are
        monotone along the log and the latest word dominates every readable
        variant ([pte_ad_le]).  The corollary the absorption theorem wants:
        whether [update_PTE_Bits] FIRES on the fresh word is decided by the
        latest word alone — a stale variant that still needs bits can never
        make the CAS write when the fresh word already has them, and if the
        fresh word needs them then so does every stale variant
        ([update_PTE_Bits_fires_mono]).
    §5  the [wlat8] iProp bundle: the 8 per-byte [γlat] elements of a window,
        and the bridge from [WeakGhost.wlat_interp] to the pure premises
        above ([wwin_latest]).  Kept minimal — the invariant itself is P4's.

    THE COVER PREMISE [wwin_covered] is the pure shadow of the per-hart
    receipt [⊒ V_kpt]: the hart's read floor already covers a write to every
    window byte, which bars the era-initial image (pre-kvminit garbage) from
    every admissible read — [readable]'s coherence clause does the work.

    Everything up to §4 is pure (WeakMem/WeakInterp altitude); only §5 talks
    to the ghost state. *)
From Stdlib Require Import ZArith Bool Lia Wf_nat.
From stdpp Require Import gmap list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import RiscvLang RiscvPtsto.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakRacy.
Require Import WeakWord8.
Require Import PtAdBits.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 0. The byte/testbit kit *)

(** Bit [i] of byte [j] is bit [8j+i] of the word. *)
Lemma nth_byte_testbit {m : N} (w : bv m) (j : nat) (i : Z) :
  0 <= i < 8 ->
  Z.testbit (bv_unsigned (nth_byte w j)) i
  = Z.testbit (bv_unsigned w) (8 * Z.of_nat j + i).
Proof.
  intros Hi. rewrite nth_byte_unsigned.
  rewrite (Z.mod_pow2_bits_low _ 8 i ltac:(lia)).
  rewrite (Z.shiftr_spec _ _ i ltac:(lia)).
  f_equal. lia.
Qed.

(** ... and byte 0 in particular reads the word's own low bits. *)
Lemma nth_byte0_testbit {m : N} (w : bv m) (i : Z) :
  0 <= i < 8 ->
  Z.testbit (bv_unsigned (nth_byte w 0)) i = Z.testbit (bv_unsigned w) i.
Proof.
  intros Hi. rewrite (nth_byte_testbit w 0 i Hi). reflexivity.
Qed.

(** A 1-bit word is zero exactly when its bit 0 is clear. *)
Local Lemma mword1_zero_iff (x : mword 1) :
  x = (mword_of_int 0 : mword 1) <-> Z.testbit (bv_unsigned x) 0 = false.
Proof.
  destruct (mword1_cases x) as [-> | ->]; split; intros H.
  - vm_compute. reflexivity.
  - reflexivity.
  - exfalso. apply (f_equal (fun y : mword 1 => bv_unsigned y)) in H.
    vm_compute in H. discriminate.
  - vm_compute in H. discriminate.
Qed.

Local Lemma eq_vec1_zero_true (x : mword 1) :
  eq_vec x ('b"0") = true <-> x = (mword_of_int 0 : mword 1).
Proof.
  destruct (mword1_cases x) as [-> | ->]; split; intros H.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute in H. discriminate.
  - exfalso. apply (f_equal (fun y : mword 1 => bv_unsigned y)) in H.
    vm_compute in H. discriminate.
Qed.

Local Lemma mw1_ne_mw0 : ('b"1" : mword 1) <> (mword_of_int 0 : mword 1).
Proof.
  intros H. apply (f_equal (fun y : mword 1 => bv_unsigned y)) in H.
  vm_compute in H. discriminate.
Qed.

(* ====================================================================== *)
(** ** 1. Byte stability: variants agree on bytes 1–7 *)

(** Bytes 1–7 of a variant are the base word's own — A/D live in byte 0. *)
Lemma pte_set_ad_nth_byte_high (w : mword 64) (a d : mword 1) (j : nat) :
  (1 <= j < 8)%nat ->
  nth_byte (pte_set_ad w a d) j = nth_byte w j.
Proof.
  intros Hj. apply (bv_eq_testbit 8). intros k Hk.
  assert (Hk8 : 0 <= k < 8) by (change (Z.of_N 8) with 8 in Hk; lia).
  rewrite (nth_byte_testbit (pte_set_ad w a d) j k Hk8).
  rewrite (nth_byte_testbit w j k Hk8).
  rewrite (pte_set_ad_testbit w a d (8 * Z.of_nat j + k) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq (8 * Z.of_nat j + k) 6) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq (8 * Z.of_nat j + k) 7) ltac:(lia)).
  reflexivity.
Qed.

(** THE LOAD-MIXTURE LEMMA.  A word whose every byte is SOME variant's byte
    is itself a variant — byte 0 fixes the (a, d), bytes 1–7 are pinned.
    This is what makes a per-byte weak read of the window safe: different
    bytes may come from DIFFERENT messages, and the assembled word is still
    a variant. *)
Lemma pte_variant_mix (w0 : mword 64) (w : bv (8 * 8)%N) :
  (forall j : nat, (j < 8)%nat ->
     exists a d : mword 1, nth_byte w j = nth_byte (pte_set_ad w0 a d) j) ->
  exists a d : mword 1, (w : mword 64) = pte_set_ad w0 a d.
Proof.
  intros Hb.
  destruct (Hb 0%nat ltac:(lia)) as (a & d & H0).
  exists a, d.
  apply (@bv_eq_of_bytes 8 w (pte_set_ad w0 a d)).
  intros j Hj.
  assert (Hjn : (j < 8)%nat) by lia.
  destruct j as [|j']; [exact H0|].
  destruct (Hb (S j') Hjn) as (a' & d' & Hj').
  rewrite Hj'.
  rewrite (pte_set_ad_nth_byte_high w0 a' d' (S j') ltac:(lia)).
  rewrite (pte_set_ad_nth_byte_high w0 a d (S j') ltac:(lia)).
  reflexivity.
Qed.

(* ====================================================================== *)
(** ** 2. The value-pinned byte: unanimity makes a byte SC *)

(** If every timestamp that holds a value for [a] holds [v], any admissible
    read of [a] returns [v] — [readable] only ever picks a timestamp that
    writes the byte.  Stated at [WeakMem] altitude. *)
Lemma readable_pinned_val (img : image) (log : list wmsg) (ws : wstate)
    (vpre : nat) (a : Z) (v : bv 8) (t : nat) :
  (forall (t' : nat) (b : bv 8), log_byte img log t' a = Some b -> b = v) ->
  readable img log ws vpre a t ->
  log_byte img log t a = Some v.
Proof.
  intros Hv [[b Hb] _]. rewrite Hb. f_equal. exact (Hv t b Hb).
Qed.

(** ... and at the interpreter's [wbyte_ok]. *)
Lemma wbyte_ok_pinned_val (s : wmstate) (ak : akinfo) (a : Z) (v : bv 8)
    (t : nat) (b : bv 8) :
  (forall (t' : nat) (b' : bv 8),
     log_byte (wimg s) (wm_log s) t' a = Some b' -> b' = v) ->
  wbyte_ok s ak a t b -> b = v.
Proof. intros Hv [Hb _]. exact (Hv t b Hb). Qed.

(** A cover premise turns "some writer is below the hart's floor" into
    "the whole log has a writer" — the clipping step both exclusion lemmas
    below share. *)
Local Lemma writes_in_to_len (log : list wmsg) (a : Z) (V : nat) :
  writes_in log a 0 V -> writes_in log a 0 (length log).
Proof.
  intros H.
  eapply writes_in_mono_hi; [apply Nat.le_min_r|].
  apply writes_in_clip, H.
Qed.

(** THE IMAGE-EXCLUSION LEMMA: with the hart's read floor covering a write
    to [a] (the receipt's pure shadow), NO admissible read — at ANY access
    kind — returns the era-initial image. *)
Lemma wbyte_ok_not_init (s : wmstate) (ak : akinfo) (a : Z) (t : nat)
    (b : bv 8) :
  writes_in (wm_log s) a 0 (w_vrNew (wm_ws s)) ->
  wbyte_ok s ak a t b -> t <> 0%nat.
Proof.
  intros Hcov [Hb Hadm].
  destruct (ak_coh ak).
  - intros ->. apply Hadm. exact (writes_in_to_len _ _ _ Hcov).
  - destruct Hadm as [Hrd _].
    apply (readable_not_init _ _ _ _ _ _ Hrd).
    eapply writes_in_mono_hi; [|exact Hcov].
    apply load_vpre_vrNew.
Qed.

(** The source of a non-initial value is a log MESSAGE. *)
Lemma log_byte_msg (img : image) (log : list wmsg) (t : nat) (a : Z)
    (v : bv 8) :
  log_byte img log t a = Some v ->
  t = 0%nat \/ exists (i : nat) (m : wmsg),
      t = S i /\ log !! i = Some m /\ msg_byte m a = Some v.
Proof.
  destruct t as [|i]; [by left|]. rewrite log_byte_S.
  destruct (log !! i) as [m|] eqn:Hm; simpl; [|discriminate].
  intros Hv. right. exists i, m. split_and!; [reflexivity|exact Hm|exact Hv].
Qed.

(** The message-unanimity form of the pinned byte: if every LOG MESSAGE
    writes [v] at [a] and the image is excluded by the cover, every
    admissible read returns [v] — "this byte behaves SC". *)
Lemma wbyte_ok_pinned_val_msgs (s : wmstate) (ak : akinfo) (a : Z) (v : bv 8)
    (t : nat) (b : bv 8) :
  (forall m : wmsg, m ∈ wm_log s ->
     forall b' : bv 8, msg_byte m a = Some b' -> b' = v) ->
  writes_in (wm_log s) a 0 (w_vrNew (wm_ws s)) ->
  wbyte_ok s ak a t b -> b = v.
Proof.
  intros Hv Hcov Hok.
  pose proof (wbyte_ok_not_init s ak a t b Hcov Hok) as Hne.
  destruct Hok as [Hb _].
  destruct (log_byte_msg _ _ _ _ _ Hb) as [Hz|(i & m & -> & Hm & Hmb)];
    [by destruct (Hne Hz)|].
  exact (Hv m (elem_of_list_lookup_2 _ _ _ Hm) b Hmb).
Qed.

(* ====================================================================== *)
(** ** 3. The value-closure predicate and the [wadm] collapse *)

(** One message writes only variant bytes into the window at [a8]: there is
    ONE (a, d) such that every window byte the message writes is that
    variant's byte.  (A message that does not touch the window satisfies
    this vacuously — [wmsg_variant_untouched].) *)
Definition wmsg_variant (a8 : Z) (w0 : mword 64) (m : wmsg) : Prop :=
  exists a d : mword 1,
    forall j : nat, (j < 8)%nat ->
      forall b : bv 8, msg_byte m (a8 + Z.of_nat j) = Some b ->
        b = nth_byte (pte_set_ad w0 a d) j.

(** THE VALUE-CLOSURE PREDICATE: every message of the log is a variant
    writer (or does not touch the window).  This is the whole-log conjunct
    of P4's [wkpt_inv]; the lemmas below are its preservation kit. *)
Definition wlog_variants (log : list wmsg) (a8 : Z) (w0 : mword 64) : Prop :=
  forall m : wmsg, m ∈ log -> wmsg_variant a8 w0 m.

Lemma wlog_variants_nil (a8 : Z) (w0 : mword 64) : wlog_variants [] a8 w0.
Proof. intros m Hm. by apply elem_of_nil in Hm. Qed.

Lemma wlog_variants_lookup (log : list wmsg) (a8 : Z) (w0 : mword 64)
    (i : nat) (m : wmsg) :
  wlog_variants log a8 w0 -> log !! i = Some m -> wmsg_variant a8 w0 m.
Proof. intros Hv Hm. exact (Hv m (elem_of_list_lookup_2 _ _ _ Hm)). Qed.

(** A message disjoint from the window is vacuously a variant writer. *)
Lemma wmsg_variant_untouched (a8 : Z) (w0 : mword 64) (m : wmsg) :
  (forall j : nat, (j < 8)%nat -> msg_byte m (a8 + Z.of_nat j) = None) ->
  wmsg_variant a8 w0 m.
Proof.
  intros Hno. exists ('b"0"), ('b"0"). intros j Hj b Hb.
  rewrite (Hno j Hj) in Hb. discriminate.
Qed.

(** Monotonicity under appends whose new messages are variant writers (in
    particular, appends that do not touch the window at all). *)
Lemma wlog_variants_app (log ms : list wmsg) (a8 : Z) (w0 : mword 64) :
  wlog_variants log a8 w0 ->
  (forall m : wmsg, m ∈ ms -> wmsg_variant a8 w0 m) ->
  wlog_variants (log ++ ms) a8 w0.
Proof.
  intros Hlog Hms m Hm. apply elem_of_app in Hm as [Hm|Hm]; auto.
Qed.

(** An appended whole-window write whose value is a variant. *)
Lemma wmsg_variant_write (tid : option nat) (pa : Arch.pa)
    (v : bv (8 * 8)%N) (a8 : Z) (w0 : mword 64) :
  pa_z pa = a8 ->
  (exists a d : mword 1, (v : mword 64) = pte_set_ad w0 a d) ->
  wmsg_variant a8 w0 (wwrite_msg tid pa 8 v).
Proof.
  intros Hpa (a & d & Hv). exists a, d. intros j Hj b Hb.
  assert (Hab : msg_byte (wwrite_msg tid pa 8 v) (a8 + Z.of_nat j)
                = Some (nth_byte v j)).
  { rewrite -Hpa. apply (wwrite_msg_byte tid pa 8 v j). exact Hj. }
  rewrite Hab in Hb. injection Hb as <-.
  exact (f_equal (fun x : mword 64 => nth_byte x j) Hv).
Qed.

(** [update_PTE_Bits] of a variant is a variant — the absorption law at the
    log's altitude ([update_PTE_Bits_set_ad] + [pte_set_ad_absorb]). *)
Lemma update_PTE_Bits_variant (w0 fresh w' : mword 64)
    (acc : MemoryAccessType mem_payload) :
  (exists a d : mword 1, fresh = pte_set_ad w0 a d) ->
  update_PTE_Bits (fresh : mword 64) acc = Some w' ->
  exists a d : mword 1, w' = pte_set_ad w0 a d.
Proof.
  intros (a0 & d0 & Hf) Hup.
  destruct (update_PTE_Bits_set_ad _ _ _ Hup) as (a & d & Hw').
  exists a, d. rewrite Hw' Hf. apply pte_set_ad_absorb.
Qed.

(** THE PRESERVATION LEMMA for a CAS-model write-back: the appended message
    writes [update_PTE_Bits fresh], and [fresh] — the CAS's exclusive read,
    i.e. the log-latest window word under the invariant — is itself a
    variant.  The closure survives the append. *)
Lemma wlog_variants_writeback (tid : option nat) (pa : Arch.pa)
    (acc : MemoryAccessType mem_payload) (log : list wmsg) (a8 : Z)
    (w0 fresh w' : mword 64) (v : bv (8 * 8)%N) :
  pa_z pa = a8 ->
  (exists a d : mword 1, fresh = pte_set_ad w0 a d) ->
  update_PTE_Bits (fresh : mword 64) acc = Some w' ->
  (v : mword 64) = w' ->
  wlog_variants log a8 w0 ->
  wlog_variants (log ++ [wwrite_msg tid pa 8 v]) a8 w0.
Proof.
  intros Hpa Hf Hup Hv Hlog.
  apply wlog_variants_app; [exact Hlog|].
  intros m Hm. apply elem_of_list_singleton in Hm as ->.
  apply (wmsg_variant_write tid pa v a8 w0 Hpa).
  destruct (update_PTE_Bits_variant w0 fresh w' acc Hf Hup) as (a & d & Hw').
  exists a, d. rewrite Hv. exact Hw'.
Qed.

(** *** The collapse at the window *)

(** The cover premise for a whole window — the pure shadow of the receipt
    [⊒ V_kpt]: the hart's read floor covers a write to every window byte. *)
Definition wwin_covered (s : wmstate) (ra : Arch.pa) : Prop :=
  forall j : nat, (j < 8)%nat ->
    writes_in (wm_log s) (acc_addr ra j) 0 (w_vrNew (wm_ws s)).

(** A non-initial window byte value is a variant byte. *)
Local Lemma log_byte_variant (s : wmstate) (ra : Arch.pa) (w0 : mword 64)
    (j t : nat) (b : bv 8) :
  (j < 8)%nat ->
  wlog_variants (wm_log s) (pa_z ra) w0 ->
  t <> 0%nat ->
  log_byte (wimg s) (wm_log s) t (acc_addr ra j) = Some b ->
  exists a d : mword 1, b = nth_byte (pte_set_ad w0 a d) j.
Proof.
  intros Hj Hvar Hne Hb.
  destruct (log_byte_msg _ _ _ _ _ Hb) as [Hz|(i & m & -> & Hm & Hmb)];
    [by destruct (Hne Hz)|].
  destruct (wlog_variants_lookup _ _ _ _ _ Hvar Hm) as (a & d & Hv).
  exists a, d. exact (Hv j Hj b Hmb).
Qed.

(** One admissible byte of the window is a variant byte. *)
Lemma wbyte_ok_variant (s : wmstate) (ak : akinfo) (ra : Arch.pa)
    (w0 : mword 64) (j t : nat) (b : bv 8) :
  (j < 8)%nat ->
  wlog_variants (wm_log s) (pa_z ra) w0 ->
  wwin_covered s ra ->
  wbyte_ok s ak (acc_addr ra j) t b ->
  exists a d : mword 1, b = nth_byte (pte_set_ad w0 a d) j.
Proof.
  intros Hj Hvar Hcov Hok.
  pose proof (wbyte_ok_not_init s ak _ t b (Hcov j Hj) Hok) as Hne.
  destruct Hok as [Hb _].
  exact (log_byte_variant s ra w0 j t b Hj Hvar Hne Hb).
Qed.

(** THE [wadm] COLLAPSE: [WeakRacy]'s per-byte admissibility at the window
    — the whole ∀-oracle surface of a racy read — implies the read word is
    a variant of the canonical leaf.  The per-byte spelling is bytes 1–7
    pinned + byte 0 enumerated; the mixture lemma reassembles it. *)
Lemma wadm_variant (s : wmstate) (rak : akinfo) (ra : Arch.pa)
    (w0 : mword 64) (w : bv (8 * 8)%N) :
  wlog_variants (wm_log s) (pa_z ra) w0 ->
  wwin_covered s ra ->
  wadm s rak ra 8 w ->
  exists a d : mword 1, (w : mword 64) = pte_set_ad w0 a d.
Proof.
  intros Hvar Hcov Hadm.
  apply pte_variant_mix. intros j Hj.
  destruct (Hadm j ltac:(vm_compute; lia)) as (t & Hok).
  exact (wbyte_ok_variant s rak ra w0 j t _ Hj Hvar Hcov Hok).
Qed.

(** ... the same collapse against [WeakInterp]'s read/assemble shape. *)
Lemma wread_ok_variant (s : wmstate) (ak : akinfo) (ra : Arch.pa)
    (w0 : mword 64) (ts : list nat) (w : bv (8 * 8)%N) :
  wlog_variants (wm_log s) (pa_z ra) w0 ->
  wwin_covered s ra ->
  wread_ok s ak ra 8 ts w ->
  exists a d : mword 1, (w : mword 64) = pte_set_ad w0 a d.
Proof.
  intros Hvar Hcov [_ Hbytes].
  apply pte_variant_mix. intros j Hj.
  refine (wbyte_ok_variant s ak ra w0 j (ts !!! j) _ Hj Hvar Hcov _).
  apply Hbytes. lia.
Qed.

(** The per-byte reading of the collapse, for a consumer that wants the
    pinned bytes directly rather than the assembled variant. *)
Lemma wadm_variant_bytes (s : wmstate) (rak : akinfo) (ra : Arch.pa)
    (w0 : mword 64) (w : bv (8 * 8)%N) :
  wlog_variants (wm_log s) (pa_z ra) w0 ->
  wwin_covered s ra ->
  wadm s rak ra 8 w ->
  (forall j : nat, (1 <= j < 8)%nat -> nth_byte w j = nth_byte w0 j) /\
  (exists a d : mword 1, nth_byte w 0 = nth_byte (pte_set_ad w0 a d) 0).
Proof.
  intros Hvar Hcov Hadm.
  destruct (wadm_variant s rak ra w0 w Hvar Hcov Hadm) as (a & d & Hw).
  split.
  - intros j Hj.
    assert (Hb : nth_byte w j = nth_byte (pte_set_ad w0 a d) j)
      by (exact (f_equal (fun x : mword 64 => nth_byte x j) Hw)).
    rewrite Hb. apply pte_set_ad_nth_byte_high. exact Hj.
  - exists a, d. exact (f_equal (fun x : mword 64 => nth_byte x 0%nat) Hw).
Qed.

(** Bytes 1–7 through the closure: every admissible read of a high window
    byte returns the CANONICAL byte — the "seven pinned bytes behave SC"
    statement, [wbyte_ok_pinned_val_msgs] instantiated by byte stability. *)
Lemma wlog_variants_pinned_byte (s : wmstate) (ak : akinfo) (ra : Arch.pa)
    (w0 : mword 64) (j t : nat) (b : bv 8) :
  (1 <= j < 8)%nat ->
  wlog_variants (wm_log s) (pa_z ra) w0 ->
  wwin_covered s ra ->
  wbyte_ok s ak (acc_addr ra j) t b ->
  b = nth_byte w0 j.
Proof.
  intros Hj Hvar Hcov Hok.
  destruct (wbyte_ok_variant s ak ra w0 j t b ltac:(lia) Hvar Hcov Hok)
    as (a & d & Hb).
  rewrite Hb. apply pte_set_ad_nth_byte_high. exact Hj.
Qed.

(* ====================================================================== *)
(** ** 4. Bit-monotonicity under the CAS discipline *)

(** *** 4a. The A/D order, at byte and word altitude *)

(** "[b']'s A/D bits dominate [b]'s" — the order on variant BYTES. *)
Definition ad_bits_le (b b' : bv 8) : Prop :=
  (Z.testbit (bv_unsigned b) 6 = true -> Z.testbit (bv_unsigned b') 6 = true) /\
  (Z.testbit (bv_unsigned b) 7 = true -> Z.testbit (bv_unsigned b') 7 = true).

Lemma ad_bits_le_refl (b : bv 8) : ad_bits_le b b.
Proof. by split. Qed.

Lemma ad_bits_le_trans (b1 b2 b3 : bv 8) :
  ad_bits_le b1 b2 -> ad_bits_le b2 b3 -> ad_bits_le b1 b3.
Proof. intros [Ha1 Hd1] [Ha2 Hd2]. split; auto. Qed.

(** The two flag getters, spelled exactly as the model's update path reads
    them ([update_PTE_Bits]'s [pte_flags] projections). *)
Definition pte_getA (w : mword 64) : mword 1 :=
  _get_PTE_Flags_A (Mk_PTE_Flags (subrange_vec_dec w 7 0)).
Definition pte_getD (w : mword 64) : mword 1 :=
  _get_PTE_Flags_D (Mk_PTE_Flags (subrange_vec_dec w 7 0)).

Lemma pte_getA_testbit (w : mword 64) :
  Z.testbit (bv_unsigned (pte_getA w)) 0 = Z.testbit (bv_unsigned w) 6.
Proof. unfold pte_getA, _get_PTE_Flags_A, Mk_PTE_Flags. mw_prep. tbk. Qed.

Lemma pte_getD_testbit (w : mword 64) :
  Z.testbit (bv_unsigned (pte_getD w)) 0 = Z.testbit (bv_unsigned w) 7.
Proof. unfold pte_getD, _get_PTE_Flags_D, Mk_PTE_Flags. mw_prep. tbk. Qed.

Lemma pte_getA_set_ad (w : mword 64) (a d : mword 1) :
  pte_getA (pte_set_ad w a d) = a.
Proof.
  apply (bv_eq_testbit 1). intros k Hk.
  assert (k = 0) as -> by (change (Z.of_N 1) with 1 in Hk; lia).
  rewrite pte_getA_testbit.
  rewrite (pte_set_ad_testbit w a d 6 ltac:(lia)). reflexivity.
Qed.

Lemma pte_getD_set_ad (w : mword 64) (a d : mword 1) :
  pte_getD (pte_set_ad w a d) = d.
Proof.
  apply (bv_eq_testbit 1). intros k Hk.
  assert (k = 0) as -> by (change (Z.of_N 1) with 1 in Hk; lia).
  rewrite pte_getD_testbit.
  rewrite (pte_set_ad_testbit w a d 7 ltac:(lia)). reflexivity.
Qed.

Lemma pte_getA_zero_iff (w : mword 64) :
  pte_getA w = (mword_of_int 0 : mword 1)
  <-> Z.testbit (bv_unsigned w) 6 = false.
Proof. rewrite -pte_getA_testbit. exact (mword1_zero_iff (pte_getA w)). Qed.

Lemma pte_getD_zero_iff (w : mword 64) :
  pte_getD w = (mword_of_int 0 : mword 1)
  <-> Z.testbit (bv_unsigned w) 7 = false.
Proof. rewrite -pte_getD_testbit. exact (mword1_zero_iff (pte_getD w)). Qed.

(** The order on variant WORDS: same canonical form, A/D bits only grow.
    (No order is stated on the LATTICE itself in any invariant — the design
    block forbids it; this order is about the LOG under the CAS discipline,
    where it is real.) *)
Definition pte_ad_le (w w' : mword 64) : Prop :=
  pte_canon w = pte_canon w' /\
  (pte_getA w' = (mword_of_int 0 : mword 1) ->
     pte_getA w = (mword_of_int 0 : mword 1)) /\
  (pte_getD w' = (mword_of_int 0 : mword 1) ->
     pte_getD w = (mword_of_int 0 : mword 1)).

Lemma pte_ad_le_refl (w : mword 64) : pte_ad_le w w.
Proof. by split. Qed.

Lemma pte_ad_le_trans (w1 w2 w3 : mword 64) :
  pte_ad_le w1 w2 -> pte_ad_le w2 w3 -> pte_ad_le w1 w3.
Proof.
  intros (Hc1 & Ha1 & Hd1) (Hc2 & Ha2 & Hd2).
  split; [congruence|]. split; auto.
Qed.

(** The byte-0 projection of the word order ... *)
Lemma pte_ad_le_byte0 (w w' : mword 64) :
  pte_ad_le w w' -> ad_bits_le (nth_byte w 0) (nth_byte w' 0).
Proof.
  intros (_ & HA & HD). split.
  - intros H6.
    rewrite (nth_byte0_testbit w 6 ltac:(lia)) in H6.
    rewrite (nth_byte0_testbit w' 6 ltac:(lia)).
    destruct (Z.testbit (bv_unsigned w') 6) eqn:E; [reflexivity|].
    exfalso.
    pose proof (HA (proj2 (pte_getA_zero_iff w') E)) as HA0.
    apply (proj1 (pte_getA_zero_iff w)) in HA0. congruence.
  - intros H7.
    rewrite (nth_byte0_testbit w 7 ltac:(lia)) in H7.
    rewrite (nth_byte0_testbit w' 7 ltac:(lia)).
    destruct (Z.testbit (bv_unsigned w') 7) eqn:E; [reflexivity|].
    exfalso.
    pose proof (HD (proj2 (pte_getD_zero_iff w') E)) as HD0.
    apply (proj1 (pte_getD_zero_iff w)) in HD0. congruence.
Qed.

(** ... and its converse for two VARIANTS of one base (the canonical halves
    come free from absorption, so byte 0 carries the whole order). *)
Lemma pte_ad_le_of_byte0 (w0 w w' : mword 64) :
  (exists a d : mword 1, w = pte_set_ad w0 a d) ->
  (exists a d : mword 1, w' = pte_set_ad w0 a d) ->
  ad_bits_le (nth_byte w 0) (nth_byte w' 0) ->
  pte_ad_le w w'.
Proof.
  intros (a & d & Hw) (a' & d' & Hw') [H6 H7].
  split; [|split].
  - rewrite Hw Hw' !pte_canon_set_ad. reflexivity.
  - intros HA'. apply (proj2 (pte_getA_zero_iff w)).
    apply (proj1 (pte_getA_zero_iff w')) in HA'.
    destruct (Z.testbit (bv_unsigned w) 6) eqn:E; [|reflexivity].
    exfalso.
    assert (H6w : Z.testbit (bv_unsigned (nth_byte w 0)) 6 = true)
      by (rewrite (nth_byte0_testbit w 6 ltac:(lia)); exact E).
    pose proof (H6 H6w) as H6w'.
    rewrite (nth_byte0_testbit w' 6 ltac:(lia)) in H6w'.
    congruence.
  - intros HD'. apply (proj2 (pte_getD_zero_iff w)).
    apply (proj1 (pte_getD_zero_iff w')) in HD'.
    destruct (Z.testbit (bv_unsigned w) 7) eqn:E; [|reflexivity].
    exfalso.
    assert (H7w : Z.testbit (bv_unsigned (nth_byte w 0)) 7 = true)
      by (rewrite (nth_byte0_testbit w 7 ltac:(lia)); exact E).
    pose proof (H7 H7w) as H7w'.
    rewrite (nth_byte0_testbit w' 7 ltac:(lia)) in H7w'.
    congruence.
Qed.

(** *** 4b. [update_PTE_Bits] only ORs bits, and firing is monotone *)

(** The exact shape of a fired update: A is set to 1, D is set to 1 or kept.
    (The model's [update_PTE_Bits] body, read off once — everything below
    is a corollary.) *)
Lemma update_PTE_Bits_shape (w w' : mword 64)
    (acc : MemoryAccessType mem_payload) :
  update_PTE_Bits (w : mword 64) acc = Some w' ->
  exists d : mword 1,
    w' = pte_set_ad w ('b"1") d /\
    (d = ('b"1" : mword 1) \/ d = pte_getD w).
Proof.
  unfold update_PTE_Bits. cbn zeta.
  destruct (orb _ _); [|discriminate].
  intros H. injection H as <-.
  eexists. split.
  - unfold pte_set_ad. reflexivity.
  - destruct (andb _ _); [left; reflexivity|right; reflexivity].
Qed.

(** A fired update only ORs the A/D bits: the pre-word is [pte_ad_le] the
    written word.  (Together with the CAS reading the LATEST value, this is
    what restores bit-monotonicity of the log.) *)
Lemma update_PTE_Bits_ad_ge (w w' : mword 64)
    (acc : MemoryAccessType mem_payload) :
  update_PTE_Bits (w : mword 64) acc = Some w' ->
  pte_ad_le w w'.
Proof.
  intros Hup.
  destruct (update_PTE_Bits_shape w w' acc Hup) as (d & Hw' & Hd).
  split; [|split].
  - rewrite Hw' pte_canon_set_ad. reflexivity.
  - intros HA'. exfalso.
    rewrite Hw' pte_getA_set_ad in HA'. exact (mw1_ne_mw0 HA').
  - intros HD'. rewrite Hw' pte_getD_set_ad in HD'.
    destruct Hd as [Hd|Hd].
    + exfalso. rewrite Hd in HD'. exact (mw1_ne_mw0 HD').
    + rewrite -Hd. exact HD'.
Qed.

(** WHETHER THE UPDATE FIRES IS MONOTONE DOWNWARD in the A/D order: if the
    bit-larger word (the CAS's FRESH read) still needs bits, so does every
    bit-smaller variant (the stale walk read).  Hence under monotonicity
    the write-back EVENT is a function of the LATEST word alone — the
    corollary the absorption theorem wants ([update_PTE_Bits_fires_latest]).
    The boolean core first: *)
Local Lemma fires_mono_core (dD dD' dA dA' : mword 1) (sd sa : bool) :
  (eq_vec dD' ('b"0") = true -> eq_vec dD ('b"0") = true) ->
  (eq_vec dA' ('b"0") = true -> eq_vec dA ('b"0") = true) ->
  orb (andb (eq_vec dD' ('b"0")) sd) (andb (eq_vec dA' ('b"0")) sa) = true ->
  orb (andb (eq_vec dD ('b"0")) sd) (andb (eq_vec dA ('b"0")) sa) = true.
Proof.
  intros HD HA Hg. apply orb_true_iff.
  apply orb_true_iff in Hg as [Hg|Hg]; apply andb_true_iff in Hg as [H1 H2].
  - left. apply andb_true_iff. split; [exact (HD H1)|exact H2].
  - right. apply andb_true_iff. split; [exact (HA H1)|exact H2].
Qed.

Lemma update_PTE_Bits_fires_mono (w w' : mword 64)
    (acc : MemoryAccessType mem_payload) :
  pte_ad_le w w' ->
  is_Some (update_PTE_Bits (w' : mword 64) acc) ->
  is_Some (update_PTE_Bits (w : mword 64) acc).
Proof.
  intros (_ & HA & HD) [x Hx].
  unfold update_PTE_Bits in Hx |- *. cbn zeta in Hx |- *.
  lazymatch type of Hx with
  | (if ?g then _ else _) = _ => destruct g eqn:Hg'
  end; [|discriminate].
  lazymatch goal with
  | |- is_Some (if ?g then _ else _) =>
      cut (g = true); [intros ->; by eexists|]
  end.
  refine (fires_mono_core (pte_getD w) (pte_getD w') (pte_getA w)
            (pte_getA w') _ _ _ _ Hg').
  - intros H. apply (proj2 (eq_vec1_zero_true _)).
    apply HD. exact (proj1 (eq_vec1_zero_true _) H).
  - intros H. apply (proj2 (eq_vec1_zero_true _)).
    apply HA. exact (proj1 (eq_vec1_zero_true _) H).
Qed.

(** The packaging the absorption proof reads off: with the stale read below
    the fresh word, "a write-back happens" ⟺ "the FRESH word needs bits" —
    the event is decided by the latest value alone. *)
Lemma update_PTE_Bits_fires_latest (wr wl : mword 64)
    (acc : MemoryAccessType mem_payload) :
  pte_ad_le wr wl ->
  (is_Some (update_PTE_Bits (wr : mword 64) acc) /\
   is_Some (update_PTE_Bits (wl : mword 64) acc))
  <-> is_Some (update_PTE_Bits (wl : mword 64) acc).
Proof.
  intros Hle. split.
  - intros [_ H]. exact H.
  - intros H. split; [|exact H].
    exact (update_PTE_Bits_fires_mono wr wl acc Hle H).
Qed.

(** *** 4c. The fresh-derived log and its monotonicity *)

(** A timestamp that writes [a] is at or below the latest writer. *)
Lemma writes_le_latest_ts (img : image) (log : list wmsg) (a : Z) (t : nat) :
  is_Some (log_byte img log t a) -> (t <= latest_ts log a)%nat.
Proof.
  intros Hs.
  destruct (decide (t <= latest_ts log a)%nat) as [Hle|Hgt]; [exact Hle|].
  exfalso. apply (latest_ts_top log a).
  apply (writes_in_log_byte img). exists t.
  split_and!; [lia|exact (log_byte_bounded _ _ _ _ Hs)|exact Hs].
Qed.

(** [log_byte] restricted to a prefix agrees with the full log below the
    cut.  EXPORTED (it was [Local]): every clipped-discipline argument needs
    it, and [WeakKpt] §1e had re-proved it verbatim. *)
Lemma log_byte_take (img : image) (log : list wmsg) (i t : nat)
    (a : Z) :
  (t <= i)%nat -> (i <= length log)%nat ->
  log_byte img (take i log) t a = log_byte img log t a.
Proof.
  intros Ht Hi.
  rewrite -{2}(take_drop i log).
  rewrite (log_byte_app img (take i log) (drop i log) t a) //.
  rewrite length_take. lia.
Qed.

(** THE CAS DISCIPLINE, as a predicate on the log: every message writing
    byte [a] wrote a value that DOMINATES the latest value at its own
    append time (the value it derived from with bits only ORed).  This is
    exactly what a landed-CAS write-back gives ([update_PTE_Bits_ad_ge] at
    the latest word), and what a plain write-back historically did NOT. *)
Definition wbyte_fresh_derived (img : image) (log : list wmsg) (a : Z)
    : Prop :=
  forall (i : nat) (m : wmsg) (b : bv 8),
    log !! i = Some m -> msg_byte m a = Some b ->
    exists bf : bv 8,
      log_byte img (take i log) (latest_ts (take i log) a) a = Some bf /\
      ad_bits_le bf b.

(** THE BIT-MONOTONICITY THEOREM: under the CAS discipline the A/D bits of
    byte [a] are monotone along the log — any two values, in timestamp
    order, are [ad_bits_le]-ordered. *)
Lemma wbyte_fresh_derived_mono (img : image) (log : list wmsg) (a : Z) :
  wbyte_fresh_derived img log a ->
  forall (t' t : nat) (b b' : bv 8),
    (t <= t')%nat ->
    log_byte img log t a = Some b ->
    log_byte img log t' a = Some b' ->
    ad_bits_le b b'.
Proof.
  intros Hfd t'.
  induction t' as [t' IH] using lt_wf_ind.
  intros t b b' Hle Hb Hb'.
  destruct (decide (t = t')) as [->|Hne].
  { rewrite Hb in Hb'. injection Hb' as <-. apply ad_bits_le_refl. }
  assert (Hlt : (t < t')%nat) by lia.
  destruct t' as [|i']; [lia|].
  rewrite log_byte_S in Hb'.
  destruct (log !! i') as [m'|] eqn:Hm'; simpl in Hb'; [|discriminate].
  destruct (Hfd i' m' b' Hm' Hb') as (bf & Hbf & Hfb').
  assert (Hi' : (i' < length log)%nat) by (apply lookup_lt_Some in Hm'; lia).
  assert (Hlenp : length (take i' log) = i') by (rewrite length_take; lia).
  assert (Htsp : (latest_ts (take i' log) a <= i')%nat)
    by (pose proof (latest_ts_le (take i' log) a); lia).
  (* the prefix's latest value, read at the FULL log *)
  assert (Hbf' : log_byte img log (latest_ts (take i' log) a) a = Some bf)
    by (rewrite -(log_byte_take img log i' _ a Htsp ltac:(lia)); exact Hbf).
  (* [t] is a writer inside the prefix, hence below its latest *)
  assert (Hbp : log_byte img (take i' log) t a = Some b)
    by (rewrite (log_byte_take img log i' t a ltac:(lia) ltac:(lia)); exact Hb).
  assert (Htle : (t <= latest_ts (take i' log) a)%nat)
    by (apply (writes_le_latest_ts img (take i' log) a t); by exists b).
  apply (ad_bits_le_trans b bf b');
    [|exact Hfb'].
  exact (IH (latest_ts (take i' log) a) ltac:(lia) t b bf Htle Hb Hbf').
Qed.

(** ... hence the LATEST word dominates every value in the log — "the
    latest word carries the union of the variant bits". *)
Lemma wbyte_fresh_derived_latest (img : image) (log : list wmsg) (a : Z)
    (t : nat) (b bl : bv 8) :
  wbyte_fresh_derived img log a ->
  log_byte img log t a = Some b ->
  log_byte img log (latest_ts log a) a = Some bl ->
  ad_bits_le b bl.
Proof.
  intros Hfd Hb Hbl.
  refine (wbyte_fresh_derived_mono img log a Hfd (latest_ts log a) t b bl
            _ Hb Hbl).
  apply (writes_le_latest_ts img). by exists b.
Qed.

(** Preservation of the discipline across an append: the new message's byte
    must dominate the CURRENT latest value (vacuous for a message that does
    not write [a]). *)
Lemma wbyte_fresh_derived_app (img : image) (log : list wmsg) (m : wmsg)
    (a : Z) :
  wbyte_fresh_derived img log a ->
  (forall b : bv 8, msg_byte m a = Some b ->
     exists bf : bv 8,
       log_byte img log (latest_ts log a) a = Some bf /\ ad_bits_le bf b) ->
  wbyte_fresh_derived img (log ++ [m]) a.
Proof.
  intros Hfd Hnew i m0 b Hi Hb.
  destruct (decide (i < length log)%nat) as [Hlt|Hge].
  - rewrite (lookup_app_l log [m] i Hlt) in Hi.
    destruct (Hfd i m0 b Hi Hb) as (bf & Hbf & Hle).
    exists bf. split; [|exact Hle].
    rewrite (take_app_le log [m] i ltac:(lia)). exact Hbf.
  - assert (Hieq : i = length log).
    { apply lookup_lt_Some in Hi. rewrite length_app /= in Hi. lia. }
    subst i.
    rewrite (lookup_app_r log [m] (length log) (Nat.le_refl _)) Nat.sub_diag /=
      in Hi.
    injection Hi as <-.
    destruct (Hnew b Hb) as (bf & Hbf & Hle).
    exists bf. split; [|exact Hle].
    rewrite (take_app_le log [m] (length log) (Nat.le_refl _)).
    rewrite (take_ge log (length log) (Nat.le_refl _)). exact Hbf.
Qed.

(** The CAS write-back instance of the append premise, at the window's byte
    0 (the only byte with A/D content; bytes 1–7 are value-identical, so
    their discipline instance is [ad_bits_le_refl]-trivial through the
    closure).  [fresh] is the CAS's exclusive read = the latest window
    word; the appended value is [update_PTE_Bits fresh]. *)
Lemma wbyte_fresh_derived_writeback (img : image) (log : list wmsg)
    (tid : option nat) (pa : Arch.pa) (acc : MemoryAccessType mem_payload)
    (fresh w' : mword 64) (v : bv (8 * 8)%N) :
  log_byte img log (latest_ts log (pa_z pa)) (pa_z pa)
    = Some (nth_byte fresh 0) ->
  update_PTE_Bits (fresh : mword 64) acc = Some w' ->
  (v : mword 64) = w' ->
  wbyte_fresh_derived img log (pa_z pa) ->
  wbyte_fresh_derived img (log ++ [wwrite_msg tid pa 8 v]) (pa_z pa).
Proof.
  intros Hlat Hup Hv Hfd.
  apply (wbyte_fresh_derived_app img log _ _ Hfd).
  intros b Hb.
  assert (Hb0 : msg_byte (wwrite_msg tid pa 8 v) (pa_z pa)
                = Some (nth_byte v 0)).
  { rewrite -(acc_addr_0 pa).
    apply (wwrite_msg_byte tid pa 8 v 0%nat). lia. }
  rewrite Hb0 in Hb. injection Hb as <-.
  exists (nth_byte fresh 0). split; [exact Hlat|].
  assert (Hle : ad_bits_le (nth_byte fresh 0) (nth_byte w' 0))
    by (apply pte_ad_le_byte0, (update_PTE_Bits_ad_ge fresh w' acc Hup)).
  assert (Hnb : nth_byte v 0 = nth_byte w' 0)
    by (exact (f_equal (fun x : mword 64 => nth_byte x 0%nat) Hv)).
  rewrite Hnb. exact Hle.
Qed.

(** *** 4d. The window-level capstone *)

(** The latest window word, byte by byte — exactly what the invariant's 8
    [γlat] elements say ([WeakGhost.latest_val] per byte; §5 derives it
    from [wlat8]). *)
Definition wwin_latest (s : wmstate) (ra : Arch.pa) (wl : bv (8 * 8)%N)
    : Prop :=
  forall j : nat, (j < 8)%nat ->
    exists t : nat,
      latest_val (wimg s) (wm_log s) (acc_addr ra j) t (nth_byte wl j).

(** The latest window word is a variant (its bytes are message bytes — the
    cover premise excludes an image-only byte). *)
Lemma wwin_latest_variant (s : wmstate) (ra : Arch.pa) (w0 : mword 64)
    (wl : bv (8 * 8)%N) :
  wlog_variants (wm_log s) (pa_z ra) w0 ->
  wwin_covered s ra ->
  wwin_latest s ra wl ->
  exists a d : mword 1, (wl : mword 64) = pte_set_ad w0 a d.
Proof.
  intros Hvar Hcov Hlat.
  apply pte_variant_mix. intros j Hj.
  destruct (Hlat j Hj) as (t & Hlv).
  assert (Hne : t <> 0%nat).
  { intros ->. destruct Hlv as [_ Hn]. apply Hn.
    exact (writes_in_to_len _ _ _ (Hcov j Hj)). }
  exact (log_byte_variant s ra w0 j t _ Hj Hvar Hne (proj1 Hlv)).
Qed.

(** THE CAPSTONE: under the closure, the CAS discipline and the receipt's
    cover, EVERY admissible read of the window is a variant BELOW the
    latest word — so by [update_PTE_Bits_fires_latest] the write-back event
    of a walk that read it is decided by the latest word alone. *)
Lemma wadm_pte_ad_le_latest (s : wmstate) (rak : akinfo) (ra : Arch.pa)
    (w0 : mword 64) (w wl : bv (8 * 8)%N) :
  wlog_variants (wm_log s) (pa_z ra) w0 ->
  wbyte_fresh_derived (wimg s) (wm_log s) (pa_z ra) ->
  wwin_covered s ra ->
  wwin_latest s ra wl ->
  wadm s rak ra 8 w ->
  pte_ad_le (w : mword 64) (wl : mword 64).
Proof.
  intros Hvar Hfd Hcov Hlat Hadm.
  destruct (wadm_variant s rak ra w0 w Hvar Hcov Hadm) as (aw & dw & Hw).
  destruct (wwin_latest_variant s ra w0 wl Hvar Hcov Hlat) as (al & dl & Hwl).
  (* byte 0's order, through the discipline *)
  destruct (Hadm 0%nat ltac:(vm_compute; lia)) as (t0 & Hok0).
  destruct Hok0 as [Hb0 _].
  destruct (Hlat 0%nat ltac:(lia)) as (tl & Hlv).
  assert (Htl : latest_ts (wm_log s) (acc_addr ra 0) = tl)
    by (apply (latest_ts_eq (wimg s)), (latest_val_latest _ _ _ _ _ Hlv)).
  rewrite acc_addr_0 in Hb0 Htl.
  destruct Hlv as [Hbl _]. rewrite acc_addr_0 in Hbl.
  assert (Hble : ad_bits_le (nth_byte w 0) (nth_byte wl 0)).
  { refine (wbyte_fresh_derived_mono (wimg s) (wm_log s) (pa_z ra) Hfd
              tl t0 _ _ _ Hb0 Hbl).
    rewrite -Htl. apply (writes_le_latest_ts (wimg s)).
    by exists (nth_byte w 0). }
  refine (pte_ad_le_of_byte0 w0 _ _ _ _ Hble).
  - by exists aw, dw.
  - by exists al, dl.
Qed.

(* ====================================================================== *)
(** ** 5. The window's γlat elements, tied to §4's pure premises.
    The bundle itself is [WeakWord8.wlat8] — the window's eight per-byte
    latest-write elements at one shared timestamp, with its store/retarget
    kit already built there; NOTHING is re-defined here.  Deliberately
    minimal — [wkpt_inv] itself is P4's. *)

Section wlat8.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** The bundle IS the latest window word — §4d's [wwin_latest] premise,
      straight out of [wlat_interp]. *)
  Lemma wlat8_win_latest (σ : wmstate) (ea : Arch.pa) (dq : dfrac)
      (t : nat) (w : bv 64) :
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat8 ea dq t w -∗
    ⌜wwin_latest σ ea w⌝.
  Proof.
    iIntros "Hi (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    iDestruct (wlat_lookup with "Hi H0") as %E0.
    iDestruct (wlat_lookup with "Hi H1") as %E1.
    iDestruct (wlat_lookup with "Hi H2") as %E2.
    iDestruct (wlat_lookup with "Hi H3") as %E3.
    iDestruct (wlat_lookup with "Hi H4") as %E4.
    iDestruct (wlat_lookup with "Hi H5") as %E5.
    iDestruct (wlat_lookup with "Hi H6") as %E6.
    iDestruct (wlat_lookup with "Hi H7") as %E7.
    iPureIntro. intros j Hj. exists t.
    destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];
      [exact E0|exact E1|exact E2|exact E3|exact E4|exact E5|exact E6
      |exact E7|lia].
  Qed.

  (** ... and hence, under the closure + cover, a variant of the canonical
      leaf — the shape [wkpt_inv]'s leaf conjunct holds it in. *)
  Lemma wlat8_variant (σ : wmstate) (ea : Arch.pa) (dq : dfrac) (t : nat)
      (w0 : mword 64) (w : bv 64) :
    wlog_variants (wm_log σ) (pa_z ea) w0 ->
    wwin_covered σ ea ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat8 ea dq t w -∗
    ⌜exists a d : mword 1, (w : mword 64) = pte_set_ad w0 a d⌝.
  Proof.
    intros Hvar Hcov. iIntros "Hi Hw".
    iDestruct (wlat8_win_latest with "Hi Hw") as %Hlat.
    iPureIntro. exact (wwin_latest_variant σ ea w0 w Hvar Hcov Hlat).
  Qed.

End wlat8.
