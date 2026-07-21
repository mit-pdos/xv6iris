(* MstatusBits.v -- the mstatus transform theory: what trap entry and SRET
   do to the mstatus register, as pure functions of a SYMBOLIC input, plus
   the per-field lemmas and the trap/SRET round trip.

   This file owns BOTH transforms' definitions (trap_ms here, sret_ms1..5 /
   sret_newpriv / sret_tgt below) so that the theory and the definitions it
   is about live together.  It is deliberately at the very bottom of the
   dependency graph -- no intra-iris Requires at all -- because both the
   S-mode WP tower (WpSmodeSret and up) and the user-mode trap proofs
   (UserTrap and up) need it.  Keeping sret_ms* in WpSmodeSret.v used to
   force the entire S-mode WP tower in front of every user-mode proof.

   Kept FREE of iris/proofmode imports: the Ltac here uses vanilla-Coq
   rewrite syntax (comma lists + `by`), which ssreflect (pulled in by the
   proofmode) would re-parse.  See WpIntrCore.v for the consumers. *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import bitvector.definitions bitvector.tactics.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* §1 The symbolic-mstatus bit toolkit.                                   *)
(* ===================================================================== *)

(* Reduce mword subrange/update_subrange towers to stdpp-bv primitives.    *)
Ltac mw_prep :=
  unfold subrange_vec_dec, update_subrange_vec_dec;
  unfold MachineWord.update_slice, MachineWord.slice;
  cbn [get_word];
  rewrite ?autocast_refl;
  unfold to_word_idx, to_word, get_word;
  rewrite ?MachineWord.MachineWord.cast_idx_refl.

(* Normalize the closed N-index arithmetic (Z_idx / N.add / Z.of_N) that
   otherwise confuses lia. *)
Ltac zn_norm :=
  repeat match goal with
  | |- context [MachineWord.Z_idx ?z] => progress reduce_closed (MachineWord.Z_idx z)
  end;
  repeat match goal with
  | |- context [N.add ?a ?b] => progress reduce_closed (N.add a b)
  | |- context [N.sub ?a ?b] => progress reduce_closed (N.sub a b)
  end;
  repeat match goal with
  | |- context [Z.of_N ?a] => progress reduce_closed (Z.of_N a)
  end.

(* Chase one Z.testbit through the bv_concat/bv_extract tower.            *)
Ltac tb_rw :=
  zn_norm;
  (* The two structural rewrites -- bv_extract_unsigned and bv_concat_unsigned'
     -- account for ~68% of this file (per Ltac profiling): a symbolic-mstatus
     read chases a testbit through a 5-deep update_slice tower, so the tower
     expands to a large bv_extract/bv_concat term.  Peeling ONE occurrence per
     iteration of a `repeat (first [...])` re-scans and re-typechecks that whole
     term every step -- O(n^2).  Instead alternate BULK passes that rewrite ALL
     occurrences at once (`rewrite ?lem`): extracts expose concats, concats
     expose the next layer's extracts, repeat until saturated.  ~2.4x on the
     deep tb2 lemmas.  The two rewrites are kept in the cleanup loop below as a
     fallback for any stragglers the bulk pass leaves un-normalised. *)
  repeat (progress (rewrite ?bv_extract_unsigned; rewrite ?bv_concat_unsigned'; zn_norm));
  (* Cleanup: the wrap/shift/lor identities (side-conditioned, so not `?`-batchable)
     plus the boolean-identity normalisation LAST -- as the first branch it was
     retried after every structural rewrite and re-scanned the whole goal. *)
  repeat (first
    [ rewrite bv_extract_unsigned
    | rewrite bv_concat_unsigned'
    | rewrite bv_wrap_spec_low by lia
    | rewrite bv_wrap_spec_high by lia
    | rewrite Z.lor_spec
    | rewrite Z.shiftl_spec by lia
    | rewrite Z.shiftr_spec by lia
    | rewrite Z.testbit_neg_r by lia
    | rewrite Z.bits_0
    | progress zn_norm
    | progress rewrite ?orb_false_l, ?orb_false_r, ?andb_true_l, ?andb_false_l
    ]);
  first [ reflexivity | f_equal; lia | vm_compute; reflexivity | lia ].

(* bv equality from the IN-RANGE testbits only (out-of-range bits vanish
   into the wrap). *)
Lemma bv_eq_testbit (n : N) (y z : bv n) :
  (forall k, 0 <= k < Z.of_N n ->
     Z.testbit (bv_unsigned y) k = Z.testbit (bv_unsigned z) k) ->
  y = z.
Proof.
  intros H. apply bv_eq.
  rewrite <- (bv_wrap_bv_unsigned n y), <- (bv_wrap_bv_unsigned n z).
  apply Z.bits_inj'; intros k Hk.
  destruct (decide (k < Z.of_N n)).
  - rewrite !bv_wrap_spec_low by lia. apply H. lia.
  - rewrite !bv_wrap_spec_high by lia. reflexivity.
Qed.

(* mword-64 equality of two 1-bit extracts: single testbit obligation. *)
Ltac tb1 := apply (bv_eq_testbit 1); intros k Hk;
            assert (k = 0) as -> by lia; tb_rw.
Ltac tb2 := apply (bv_eq_testbit 2); intros k Hk;
            destruct (decide (k = 0)) as [->|];
            [| assert (k = 1) as -> by lia]; tb_rw.

(* --------------------------------------------------------------------- *)
(* The S-mode interrupt-trap mstatus tower (trap_handler Supervisor with   *)
(* cur_privilege = Supervisor and Zicfilp supported): SPELP := elp;        *)
(* SPIE := SIE; SIE := 0; SPP := 1 -- in the model's exact update order.   *)
(* --------------------------------------------------------------------- *)
Definition trap_ms (elp_v : mword 1) (ms : mword 64) : mword 64 :=
  let ms_e := update_subrange_vec_dec ms 23 23 elp_v in
  let ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e) in
  let ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0") in
  update_subrange_vec_dec ms_b 8 8 ('b"1").

Lemma trap_ms_SIE (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SIE (trap_ms elp_v ms) = ('b"0" : mword 1).
Proof. unfold trap_ms, _get_Mstatus_SIE; cbn zeta; mw_prep; tb1. Qed.

Lemma trap_ms_SPIE (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SPIE (trap_ms elp_v ms) = _get_Mstatus_SIE ms.
Proof. unfold trap_ms, _get_Mstatus_SPIE, _get_Mstatus_SIE; cbn zeta; mw_prep; tb1. Qed.

Lemma trap_ms_SPP (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SPP (trap_ms elp_v ms) = ('b"1" : mword 1).
Proof. unfold trap_ms, _get_Mstatus_SPP; cbn zeta; mw_prep; tb1. Qed.

Lemma trap_ms_MPRV (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_MPRV (trap_ms elp_v ms) = _get_Mstatus_MPRV ms.
Proof. unfold trap_ms, _get_Mstatus_MPRV; cbn zeta; mw_prep; tb1. Qed.

Lemma trap_ms_MXR (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_MXR (trap_ms elp_v ms) = _get_Mstatus_MXR ms.
Proof. unfold trap_ms, _get_Mstatus_MXR; cbn zeta; mw_prep; tb1. Qed.

Lemma trap_ms_TSR (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_TSR (trap_ms elp_v ms) = _get_Mstatus_TSR ms.
Proof. unfold trap_ms, _get_Mstatus_TSR; cbn zeta; mw_prep; tb1. Qed.

Lemma trap_ms_SXL (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SXL (trap_ms elp_v ms) = _get_Mstatus_SXL ms.
Proof. unfold trap_ms, _get_Mstatus_SXL; cbn zeta; mw_prep; tb2. Qed.

(* --------------------------------------------------------------------- *)
(* The SRET post-execute CSR tower, as functions of the initial mstatus /  *)
(* sepc (names as in the archived WpKvSret.v).  WpSmodeSret.v proves the   *)
(* WP that produces these; the theory of what they DO to each field is     *)
(* below.                                                                  *)
(* --------------------------------------------------------------------- *)
Definition sret_ms1 (ms0 : mword 64) := update_subrange_vec_dec ms0 1 1 (_get_Mstatus_SPIE ms0).
Definition sret_ms2 (ms0 : mword 64) := update_subrange_vec_dec (sret_ms1 ms0) 5 5 ('b"1").
Definition sret_newpriv (ms0 : mword 64) : Privilege :=
  if eq_vec (_get_Mstatus_SPP (sret_ms2 ms0)) ('b"1") then Supervisor else User.
Definition sret_ms3 (ms0 : mword 64) := update_subrange_vec_dec (sret_ms2 ms0) 8 8 ('b"0").
Definition sret_ms4 (ms0 : mword 64) := update_subrange_vec_dec (sret_ms3 ms0) 17 17 ('b"0").
Definition sret_ms5 (ms0 : mword 64) := update_subrange_vec_dec (sret_ms4 ms0) 23 23 (landing_pad_bits_backwards NO_LP_EXPECTED).
Definition sret_tgt (sepc0 : mword 64) := update_vec_dec sepc0 0 ('b"0").

(* --------------------------------------------------------------------- *)
(* The SRET tower over a SYMBOLIC input.                                   *)
(* --------------------------------------------------------------------- *)
Lemma sret_ms5_SIE (x : mword 64) :
  _get_Mstatus_SIE (sret_ms5 x) = _get_Mstatus_SPIE x.
Proof.
  unfold sret_ms5, sret_ms4, sret_ms3, sret_ms2, sret_ms1,
    _get_Mstatus_SIE, _get_Mstatus_SPIE.
  mw_prep; tb1.
Qed.

Lemma sret_ms5_MPRV (x : mword 64) :
  _get_Mstatus_MPRV (sret_ms5 x) = ('b"0" : mword 1).
Proof.
  unfold sret_ms5, sret_ms4, sret_ms3, sret_ms2, sret_ms1, _get_Mstatus_MPRV.
  mw_prep; tb1.
Qed.

Lemma sret_ms5_MXR (x : mword 64) :
  _get_Mstatus_MXR (sret_ms5 x) = _get_Mstatus_MXR x.
Proof.
  unfold sret_ms5, sret_ms4, sret_ms3, sret_ms2, sret_ms1, _get_Mstatus_MXR.
  mw_prep; tb1.
Qed.

Lemma sret_ms5_TSR (x : mword 64) :
  _get_Mstatus_TSR (sret_ms5 x) = _get_Mstatus_TSR x.
Proof.
  unfold sret_ms5, sret_ms4, sret_ms3, sret_ms2, sret_ms1, _get_Mstatus_TSR.
  mw_prep; tb1.
Qed.

Lemma sret_ms5_SXL (x : mword 64) :
  _get_Mstatus_SXL (sret_ms5 x) = _get_Mstatus_SXL x.
Proof.
  unfold sret_ms5, sret_ms4, sret_ms3, sret_ms2, sret_ms1, _get_Mstatus_SXL.
  mw_prep; tb2.
Qed.

(* SPP over the two SRET pre-updates (bits 1 and 5): untouched.           *)
Lemma sret_ms2_SPP (x : mword 64) :
  _get_Mstatus_SPP (sret_ms2 x) = _get_Mstatus_SPP x.
Proof.
  unfold sret_ms2, sret_ms1, _get_Mstatus_SPP. mw_prep; tb1.
Qed.

(* trap_handler's SPP := 1 makes SRET return to Supervisor.               *)
Lemma sret_newpriv_trap_ms (elp_v : mword 1) (ms : mword 64) :
  sret_newpriv (trap_ms elp_v ms) = Supervisor.
Proof.
  unfold sret_newpriv. rewrite sret_ms2_SPP. rewrite trap_ms_SPP.
  vm_compute. reflexivity.
Qed.

(* ---- THE HEADLINE FACT: the trap + SRET round trip restores SIE = 1 ---- *)
Lemma roundtrip_SIE (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SIE (sret_ms5 (trap_ms elp_v ms)) = _get_Mstatus_SIE ms.
Proof. rewrite sret_ms5_SIE. apply trap_ms_SPIE. Qed.

(* eq_vec corollaries in the exact shapes the WP premises use. *)
Lemma trap_ms_SIE_false (elp_v : mword 1) (ms : mword 64) :
  eq_vec (_get_Mstatus_SIE (trap_ms elp_v ms)) ('b"1") = false.
Proof. rewrite trap_ms_SIE. vm_compute. reflexivity. Qed.

Lemma roundtrip_SIE_true (elp_v : mword 1) (ms : mword 64) :
  eq_vec (_get_Mstatus_SIE ms) ('b"1") = true ->
  eq_vec (_get_Mstatus_SIE (sret_ms5 (trap_ms elp_v ms))) ('b"1") = true.
Proof. intros H. rewrite roundtrip_SIE. exact H. Qed.

Lemma trap_ms_MPRV_false (elp_v : mword 1) (ms : mword 64) :
  eq_vec (_get_Mstatus_MPRV ms) ('b"1") = false ->
  eq_vec (_get_Mstatus_MPRV (trap_ms elp_v ms)) ('b"1") = false.
Proof. intros H. rewrite trap_ms_MPRV. exact H. Qed.

Lemma roundtrip_MPRV_false (elp_v : mword 1) (ms : mword 64) :
  eq_vec (_get_Mstatus_MPRV (sret_ms5 (trap_ms elp_v ms))) ('b"1") = false.
Proof. rewrite sret_ms5_MPRV. vm_compute. reflexivity. Qed.

Lemma trap_ms_MXR_true (elp_v : mword 1) (ms : mword 64) :
  eq_vec (_get_Mstatus_MXR ms) ('b"0") = true ->
  eq_vec (_get_Mstatus_MXR (trap_ms elp_v ms)) ('b"0") = true.
Proof. intros H. rewrite trap_ms_MXR. exact H. Qed.

Lemma roundtrip_MXR_true (elp_v : mword 1) (ms : mword 64) :
  eq_vec (_get_Mstatus_MXR ms) ('b"0") = true ->
  eq_vec (_get_Mstatus_MXR (sret_ms5 (trap_ms elp_v ms))) ('b"0") = true.
Proof. intros H. rewrite sret_ms5_MXR. rewrite trap_ms_MXR. exact H. Qed.

Lemma trap_ms_TSR_false (elp_v : mword 1) (ms : mword 64) :
  eq_vec (_get_Mstatus_TSR ms) ('b"1") = false ->
  eq_vec (_get_Mstatus_TSR (trap_ms elp_v ms)) ('b"1") = false.
Proof. intros H. rewrite trap_ms_TSR. exact H. Qed.

Lemma roundtrip_TSR_false (elp_v : mword 1) (ms : mword 64) :
  eq_vec (_get_Mstatus_TSR ms) ('b"1") = false ->
  eq_vec (_get_Mstatus_TSR (sret_ms5 (trap_ms elp_v ms))) ('b"1") = false.
Proof. intros H. rewrite sret_ms5_TSR. rewrite trap_ms_TSR. exact H. Qed.

Lemma trap_ms_SXL_eq (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SXL ms = ('b"10" : mword 2) ->
  _get_Mstatus_SXL (trap_ms elp_v ms) = ('b"10" : mword 2).
Proof. intros H. rewrite trap_ms_SXL. exact H. Qed.

Lemma roundtrip_SXL_eq (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SXL ms = ('b"10" : mword 2) ->
  _get_Mstatus_SXL (sret_ms5 (trap_ms elp_v ms)) = ('b"10" : mword 2).
Proof. intros H. rewrite sret_ms5_SXL. rewrite trap_ms_SXL. exact H. Qed.

(* --------------------------------------------------------------------- *)
(* The ext-state / dirty / MPP fields (bits 16:15 XS, 14:13 FS, 10:9 VS,   *)
(* 63 SD, 12:11 MPP): NEITHER trap_ms (bits 23,5,1,8) NOR sret_ms5 (bits    *)
(* 1,5,8,17,23) touches them, so they ride through the round trip intact.  *)
(* Needed to discharge [legalize_sie_clear_idem] on [trap_ms elp ms].      *)
(* --------------------------------------------------------------------- *)
Lemma trap_ms_XS (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_XS (trap_ms elp_v ms) = _get_Mstatus_XS ms.
Proof. unfold trap_ms, _get_Mstatus_XS; cbn zeta; mw_prep; tb2. Qed.

Lemma trap_ms_FS (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_FS (trap_ms elp_v ms) = _get_Mstatus_FS ms.
Proof. unfold trap_ms, _get_Mstatus_FS; cbn zeta; mw_prep; tb2. Qed.

Lemma trap_ms_VS (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_VS (trap_ms elp_v ms) = _get_Mstatus_VS ms.
Proof. unfold trap_ms, _get_Mstatus_VS; cbn zeta; mw_prep; tb2. Qed.

Lemma trap_ms_MPP (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_MPP (trap_ms elp_v ms) = _get_Mstatus_MPP ms.
Proof. unfold trap_ms, _get_Mstatus_MPP; cbn zeta; mw_prep; tb2. Qed.

Lemma trap_ms_SD (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SD (trap_ms elp_v ms) = _get_Mstatus_SD ms.
Proof. unfold trap_ms, _get_Mstatus_SD; cbn zeta; mw_prep; tb1. Qed.

Lemma sret_ms5_XS (x : mword 64) :
  _get_Mstatus_XS (sret_ms5 x) = _get_Mstatus_XS x.
Proof. unfold sret_ms5, sret_ms4, sret_ms3, sret_ms2, sret_ms1, _get_Mstatus_XS. mw_prep; tb2. Qed.

Lemma sret_ms5_FS (x : mword 64) :
  _get_Mstatus_FS (sret_ms5 x) = _get_Mstatus_FS x.
Proof. unfold sret_ms5, sret_ms4, sret_ms3, sret_ms2, sret_ms1, _get_Mstatus_FS. mw_prep; tb2. Qed.

Lemma sret_ms5_VS (x : mword 64) :
  _get_Mstatus_VS (sret_ms5 x) = _get_Mstatus_VS x.
Proof. unfold sret_ms5, sret_ms4, sret_ms3, sret_ms2, sret_ms1, _get_Mstatus_VS. mw_prep; tb2. Qed.

Lemma sret_ms5_MPP (x : mword 64) :
  _get_Mstatus_MPP (sret_ms5 x) = _get_Mstatus_MPP x.
Proof. unfold sret_ms5, sret_ms4, sret_ms3, sret_ms2, sret_ms1, _get_Mstatus_MPP. mw_prep; tb2. Qed.

Lemma sret_ms5_SD (x : mword 64) :
  _get_Mstatus_SD (sret_ms5 x) = _get_Mstatus_SD x.
Proof. unfold sret_ms5, sret_ms4, sret_ms3, sret_ms2, sret_ms1, _get_Mstatus_SD. mw_prep; tb1. Qed.

Lemma roundtrip_XS (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_XS (sret_ms5 (trap_ms elp_v ms)) = _get_Mstatus_XS ms.
Proof. rewrite sret_ms5_XS. apply trap_ms_XS. Qed.

Lemma roundtrip_FS (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_FS (sret_ms5 (trap_ms elp_v ms)) = _get_Mstatus_FS ms.
Proof. rewrite sret_ms5_FS. apply trap_ms_FS. Qed.

Lemma roundtrip_VS (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_VS (sret_ms5 (trap_ms elp_v ms)) = _get_Mstatus_VS ms.
Proof. rewrite sret_ms5_VS. apply trap_ms_VS. Qed.

Lemma roundtrip_MPP (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_MPP (sret_ms5 (trap_ms elp_v ms)) = _get_Mstatus_MPP ms.
Proof. rewrite sret_ms5_MPP. apply trap_ms_MPP. Qed.

Lemma roundtrip_SD (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SD (sret_ms5 (trap_ms elp_v ms)) = _get_Mstatus_SD ms.
Proof. rewrite sret_ms5_SD. apply trap_ms_SD. Qed.
