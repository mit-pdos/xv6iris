(* LogDefs.v -- dependency-light log names, on-disk geometry, and mirror
   propositions shared with layers that do not need the log invariant. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From Stdlib Require Import FunctionalExtensionality.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import own ghost_var ghost_map mono_nat.
Require Import RiscvModelBytes.
Require Import RiscvLang.   (* [GenId]/[gen_id]: the born-true mirror row is per-era *)
Require Import RiscvPtsto.
(* [lock_free_tok] / [lock_ghost_alloc]: the "log" spinlock's ghost name is
   one of [log_names]'s four, so the free-state bundle below cannot be
   stated without them.  This is the ONE reason this otherwise
   dependency-light file names the lock layer at all; every current importer
   of LogDefs already has WpLock in its transitive closure (FsCrash and
   IcacheRef require it directly), so nothing downstream gains a dependency. *)
Require Import WpLockAt.
Require Export Xv6Cameras.  (* [logG], [op_entry] *)
Local Open Scope Z_scope.

(* On-disk log geometry: one header block followed by [LOGBLOCKS] slots. *)
Definition LOGBLOCKS : nat := 30%nat.

Definition log_hdr_bno (logstart : Z) : Z := logstart.
Definition log_slot_bno (logstart : Z) (i : nat) : Z :=
  logstart + 1 + Z.of_nat i.
Definition log_region_set (logstart : Z) : gset Z :=
  list_to_set ((fun i => log_slot_bno logstart i) <$> seq 0 LOGBLOCKS)
  ∪ {[ log_hdr_bno logstart ]}.

(* THE HOME BLOCKS: the covered range minus the log's own storage.  Stated
   here, in the geometry's own file, rather than beside the recovery
   relation that first needed it ([FsCrash]) -- the log INVARIANT names it
   too (durable-disk stage G1's rows are about the home blocks), and
   [FsCrash] cannot be on [LogInv]'s cone.  [FsCrash] re-exports this
   file, so every existing reading of it is unchanged. *)
Definition fs_home_set (cov : gset Z) (logstart : Z) : gset Z :=
  cov ∖ log_region_set logstart.

(* The first little-endian 32-bit word of an on-disk log header. *)
Definition hdr_n (bs : list (bv 8)) : Z := assemble_bytes (take 4 bs).

Lemma hdr_n_nonneg (bs : list (bv 8)) : 0 <= hdr_n bs.
Proof. rewrite /hdr_n. apply assemble_bytes_bound. Qed.

(* ---------------------------------------------------------------------- *)
(* The FULL header decode.                                                 *)
(*                                                                         *)
(* [struct logheader] is [int n; int block[LOGBLOCKS];] -- a run of         *)
(* little-endian 32-bit words.  [hdr_n] above decodes the FIRST one; this   *)
(* is the whole thing, and [hdr_dec_n] is the bridge that says the two      *)
(* agree on it.                                                             *)
(*                                                                         *)
(* TOTAL and junk-tolerant by construction: a short block simply assembles  *)
(* fewer bytes ([take]/[drop] never fail), so no well-formedness premise    *)
(* rides on the decoder and a garbage header decodes to SOMETHING rather    *)
(* than to nothing.  That matters: recovery must be defined at every        *)
(* physical disk, including one a crash left mid-write.                     *)
(* ---------------------------------------------------------------------- *)

Definition le_word (bs : list (bv 8)) (i : nat) : Z :=
  assemble_bytes (take 4 (drop (4 * i)%nat bs)).

Definition hdr_dec (bs : list (bv 8)) : nat * list Z :=
  let n := Z.to_nat (le_word bs 0) in
  (n, (fun i => le_word bs (S i)) <$> seq 0 n).

Lemma le_word_0 (bs : list (bv 8)) : le_word bs 0 = hdr_n bs.
Proof. rewrite /le_word /hdr_n Nat.mul_0_r drop_0 //. Qed.

(* THE BRIDGING LEMMA: the full decoder's [n] IS [hdr_n]. *)
Lemma hdr_dec_n (bs : list (bv 8)) : Z.of_nat (hdr_dec bs).1 = hdr_n bs.
Proof.
  rewrite /hdr_dec /= le_word_0. apply Z2Nat.id, hdr_n_nonneg.
Qed.

Lemma hdr_dec_length (bs : list (bv 8)) :
  length (hdr_dec bs).2 = (hdr_dec bs).1.
Proof. rewrite /hdr_dec /= length_fmap length_seq //. Qed.

Lemma hdr_dec_zero (bs : list (bv 8)) :
  hdr_n bs = 0 -> hdr_dec bs = (0%nat, []).
Proof. intros Hn. rewrite /hdr_dec le_word_0 Hn //. Qed.

(* ---------------------------------------------------------------------- *)
(* THE MIRROR's READINGS (durable-disk stage E2).  [log_mirror] is the      *)
(* era's picture of the whole durable disk, one total block view            *)
(* ([RiscvPtsto.lm_view]); these are the derived readings the log layer     *)
(* states its assertions at, and the pointwise update a WAL write's permit  *)
(* hands the era back.                                                      *)
(* ---------------------------------------------------------------------- *)

(* the era's picture after one block write *)
Definition lm_upd (M : log_mirror) (b : Z) (bs : list (bv 8)) : log_mirror :=
  MkLogMirror (fun c => if decide (c = b) then bs else lm_view M c).

(* the on-disk header's reading *)
Definition lm_hdr (M : log_mirror) (ls : Z) : nat * list Z :=
  hdr_dec (lm_view M (log_hdr_bno ls)).

Lemma lm_upd_view_eq (M : log_mirror) (b : Z) (bs : list (bv 8)) :
  lm_view (lm_upd M b bs) b = bs.
Proof. rewrite /lm_upd /=. by rewrite decide_True. Qed.

Lemma lm_upd_view_ne (M : log_mirror) (b c : Z) (bs : list (bv 8)) :
  c <> b -> lm_view (lm_upd M b bs) c = lm_view M c.
Proof. intros Hc. rewrite /lm_upd /=. by rewrite decide_False. Qed.

(* THE PICTURE IS A POINTWISE MAP, so two updates at the SAME block collapse
   to the later one.  This is what makes a torn write's two landings end at
   ONE value whichever order the device chooses (durable-disk stage E2', the
   value-chained permits' composition), and it is the only place the mirror's
   record equality is ever needed -- hence the one functional-extensionality
   use, which the assumption audit already carries. *)
Lemma lm_upd_idem (M : log_mirror) (b : Z) (x y : list (bv 8)) :
  lm_upd (lm_upd M b x) b y = lm_upd M b y.
Proof.
  rewrite /lm_upd /=. f_equal. apply functional_extensionality. intro c.
  by destruct (decide (c = b)).
Qed.

(* ---------------------------------------------------------------------- *)
(* THE INSTALL PASS'S PICTURE, AS A TERM (durable-disk 1a).                 *)
(*                                                                         *)
(* An install pass overwrites home block [Ws[i]] with the logged content    *)
(* [Lw i], one entry at a time, and the crash permits that ride it are      *)
(* CURSOR-INDEXED ([SpecInstallTrans]'s [R : nat -> iProp]) because a       *)
(* value-chained client hands its mirror half back at a DIFFERENT value per *)
(* entry.  This is that chain, over the header's own write set, plus the    *)
(* three readings its callers need: what it does to a block it never writes *)
(* ([lm_install_miss]), what it does to the on-disk header's reading        *)
(* ([lm_install_hdr]), and what it leaves at an installed block             *)
(* ([lm_install_hit]).  The last one is half of the CAUGHT-UP fact          *)
(* ([FsCrash.fs_clear_keep_seq_permit]'s premise): home = slot at every     *)
(* entry, by computation on the chained value and nothing about the disk.   *)
(* ---------------------------------------------------------------------- *)
Fixpoint lm_install (M : log_mirror) (Ws : list Z)
    (Lw : nat -> list (bv 8)) (t : nat) : log_mirror :=
  match t with
  | O => M
  | S t' => lm_upd (lm_install M Ws Lw t') (Ws !!! t') (Lw t')
  end.

Lemma lm_install_miss (M : log_mirror) (Ws : list Z)
    (Lw : nat -> list (bv 8)) (t : nat) (c : Z) :
  (t <= length Ws)%nat ->
  (forall (i : nat) (b : Z), (i < t)%nat -> Ws !! i = Some b -> b <> c) ->
  lm_view (lm_install M Ws Lw t) c = lm_view M c.
Proof.
  induction t as [|t IH]; [reflexivity|].
  intros Ht Hne. cbn [lm_install].
  destruct (lookup_lt_is_Some_2 Ws t ltac:(lia)) as [b Hb].
  rewrite (list_lookup_total_correct Ws t b Hb).
  rewrite (lm_upd_view_ne _ _ _ _ (not_eq_sym (Hne t b ltac:(lia) Hb))).
  apply IH; [lia | intros i v Hi Hv; exact (Hne i v ltac:(lia) Hv)].
Qed.

Lemma lm_install_hdr (M : log_mirror) (Ws : list Z)
    (Lw : nat -> list (bv 8)) (ls : Z) (t : nat) :
  (t <= length Ws)%nat ->
  (forall (i : nat) (b : Z), (i < t)%nat -> Ws !! i = Some b ->
     b <> log_hdr_bno ls) ->
  lm_hdr (lm_install M Ws Lw t) ls = lm_hdr M ls.
Proof.
  intros Ht Hne. rewrite /lm_hdr (lm_install_miss M Ws Lw t _ Ht Hne) //.
Qed.

(* THE DUPLICATE-FREEDOM PREMISE IS THE INJECTIVITY IT IS USED THROUGH,
   not a [NoDup]: two files in this tree resolve the bare name to two
   different inductives (stdlib's and stdpp's), and a caller can always
   supply this shape from whichever one it holds. *)
Lemma lm_install_hit (M : log_mirror) (Ws : list Z)
    (Lw : nat -> list (bv 8)) (t j : nat) (b : Z) :
  (forall (i k : nat) (c : Z), Ws !! i = Some c -> Ws !! k = Some c -> i = k) ->
  (t <= length Ws)%nat ->
  (j < t)%nat -> Ws !! j = Some b ->
  lm_view (lm_install M Ws Lw t) b = Lw j.
Proof.
  induction t as [|t IH]; [lia|]. intros Hinj Ht Hj Hb. cbn [lm_install].
  destruct (lookup_lt_is_Some_2 Ws t ltac:(lia)) as [v Hv].
  rewrite (list_lookup_total_correct Ws t v Hv).
  destruct (decide (j = t)) as [->|Hne].
  - rewrite Hv in Hb. injection Hb as ->. by rewrite lm_upd_view_eq.
  - assert (Hneq : b <> v).
    { intro Hc. apply Hne. apply (Hinj j t b Hb). rewrite Hc. exact Hv. }
    rewrite (lm_upd_view_ne _ _ _ _ Hneq).
    apply IH; [exact Hinj | lia | lia | exact Hb].
Qed.

Section LogMirrorDefs.
  Context `{!riscvGS Σ}.

  (* The era's half, at a NAMED picture -- what a WAL caller chains its
     knowledge of the durable disk through. *)
  Definition log_mirror_half (M : log_mirror) : iProp Σ :=
    ghost_var mirror_name (1/2) M.

  (* The era's half, indexed by the on-disk header's reading only. *)
  Definition log_mirror_at (ls : Z) (h : nat * list Z) : iProp Σ :=
    (∃ M : log_mirror, log_mirror_half M ∗ ⌜lm_hdr M ls = h⌝)%I.

  Global Instance log_mirror_half_timeless M : Timeless (log_mirror_half M).
  Proof. rewrite /log_mirror_half. apply _. Qed.
  Global Instance log_mirror_at_timeless ls h : Timeless (log_mirror_at ls h).
  Proof. rewrite /log_mirror_at /log_mirror_half. apply _. Qed.

  (* THE ERA'S MIRROR, BORN TRUE AND IN CUSTODY (durable-disk 1a).
     PowerOn allocates the era's mirror variable at the picture of the disk
     the era actually boots on AND installs the crash record's custody arm
     in the SAME fupd ([FsCrash.P_fs_swap]), so the boot client starts with
     a NAMED half plus the swap receipt rather than with the whole variable
     and a swap still to do.  This is the row the boot chain carries from
     [RiscvAdequacy.power_boot_res] all the way to [initlog], and it is what
     makes every boot-path disk write a value-chained one: nothing on the
     boot path re-bases [fr_D], so [initlog] and [install_trans]'s
     recovering arms move no exposed ghost state.

     The old whole-variable form ([log_mirror_full]) is GONE with the boot
     swap it existed for. *)
  Definition log_mirror_born `{GEN : GenId} (M : log_mirror) : iProp Σ :=
    (log_mirror_half M ∗ swap_lb (S gen_id))%I.

  Global Instance log_mirror_born_timeless `{GEN : GenId} M :
    Timeless (log_mirror_born M).
  Proof. rewrite /log_mirror_born /log_mirror_half /swap_lb. apply _. Qed.
End LogMirrorDefs.

Record log_names := MkLogNames {
  ln_lk  : gname;   (* the "log" spinlock *)
  ln_ops : gname;   (* the operation ledger *)
  ln_ep  : gname;   (* the batch epoch *)
  ln_lg  : gname;   (* the append registry *)
}.

(* ==================================================================== *)
(*  THE FOUR GNAMES' FREE STATE, AS ONE TOKEN                            *)
(*                                                                      *)
(*  claude-notes/projects/fs-cfg-boot.md, THE PRINCIPLE: every ghost     *)
(*  name the file system's configuration record mentions is minted ONCE, *)
(*  in the era fupd, and every downstream constructor FILLS a name it is *)
(*  handed rather than returning a fresh one.  [icfg_log] is such a      *)
(*  field ([IcacheRef.icfg_alloc] already takes the whole [log_names] as *)
(*  a tie argument), so [initlog] -- which used to mint all four at WP   *)
(*  time and return them existentially -- has to become an [_at] form.   *)
(*                                                                      *)
(*  [log_free_tok γ] is what the era hands it: the four names AT THEIR   *)
(*  GENESIS VALUES, in exactly the shape [LogInv.log_res] wants them     *)
(*  ([ProofInitlog] discharges its ledger / epoch / registry conjuncts   *)
(*  by [iExact] against these).  It is the boot-side twin of the three   *)
(*  one-name lemmas [LogInv.log_ledger_alloc] / [log_epoch_alloc] /      *)
(*  [log_reg_alloc], which had [ProofInitlog] as their only consumer and *)
(*  are now unused.                                                     *)
(*                                                                      *)
(*  GENESIS IS EPOCH ONE, not zero (fs-log.md §G.17/§G.20): the region   *)
(*  receipt's "never observed" counter value is zero and the two must    *)
(*  not collide, so [log_res]'s [⌜1 <= E⌝] is established here and the   *)
(*  only later transition is the commit bump.                            *)
(* ==================================================================== *)
Section LogGhostAlloc.
  Context `{!riscvGS Σ, !lockG Σ, !logG Σ}.

  Definition log_free_tok (γ : log_names) : iProp Σ :=
    (lock_free_tok (ln_lk γ) ∗
     ghost_map_auth (ln_ops γ) 1 (∅ : gmap nat op_entry) ∗
     mono_nat_auth_own (ln_ep γ) 1 1%nat ∗
     own (ln_lg γ) (● (∅ : gset (nat * Z))))%I.

  Lemma log_ghost_alloc : ⊢ |==> ∃ γ : log_names, log_free_tok γ.
  Proof.
    iMod lock_ghost_alloc as (γlk) "Hlk".
    iMod (ghost_map_alloc_empty (K:=nat) (V:=op_entry)) as (γops) "Hops".
    iMod (mono_nat_own_alloc 1%nat) as (γep) "[Hep _]".
    iMod (own_alloc (● (∅ : gset (nat * Z)))) as (γlg) "Hlg";
      [ apply auth_auth_valid; done | ].
    iModIntro. iExists (MkLogNames γlk γops γep γlg).
    rewrite /log_free_tok /=. iFrame "Hlk Hops Hep Hlg".
  Qed.
End LogGhostAlloc.
