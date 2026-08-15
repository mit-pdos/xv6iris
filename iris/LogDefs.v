(* LogDefs.v -- dependency-light log names, on-disk geometry, and mirror
   propositions shared with layers that do not need the log invariant. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_var.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
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
