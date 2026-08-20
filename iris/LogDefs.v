(* LogDefs.v -- dependency-light log names, on-disk geometry, and mirror
   propositions shared with layers that do not need the log invariant. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import own ghost_var ghost_map mono_nat.
Require Import RiscvModelBytes.
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

(* The first little-endian 32-bit word of an on-disk log header. *)
Definition hdr_n (bs : list (bv 8)) : Z := assemble_bytes (take 4 bs).

Lemma hdr_n_nonneg (bs : list (bv 8)) : 0 <= hdr_n bs.
Proof. rewrite /hdr_n. apply assemble_bytes_bound. Qed.

Section LogMirrorDefs.
  Context `{!riscvGS Σ}.

  (* The whole variable before crash custody takes one half. *)
  Definition log_mirror_full : iProp Σ :=
    (∃ M : log_mirror, ghost_var mirror_name 1 M)%I.

  (* The era's half, indexed by the on-disk header picture. *)
  Definition log_mirror_at (h : nat * list Z) : iProp Σ :=
    (∃ M : log_mirror,
       ghost_var mirror_name (1/2) M ∗ ⌜lm_hdr M = h⌝)%I.

  Global Instance log_mirror_at_timeless h : Timeless (log_mirror_at h).
  Proof. rewrite /log_mirror_at. apply _. Qed.
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
