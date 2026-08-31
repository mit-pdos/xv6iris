(* ===================================================================== *)
(* UEchoKernel.v -- `echo`'s WHOLE-PROCESS WP as a CONSTRUCTOR of the      *)
(* trapframe-keyed slot: the ENTRY DEPOSIT, with no assumption.           *)
(*                                                                        *)
(* Beside sync's, echo's deposit has one extra job: it must hand the       *)
(* program its ARGUMENT VECTOR.  [UkRun.uslot_of_urun_ro] is what makes    *)
(* that cheap.  It cuts the key's writable data at the entry sp -- frames  *)
(* below, exec's arguments at or above -- carves the twelve words of free  *)
(* stack out of the low half exactly as before, and PERSISTS the high      *)
(* half.  Because the high half is read-only, as many views of it may be   *)
(* taken as the program wants and none has to be disjoint from any other,  *)
(* so nothing here (and nothing in the gate) ever decides whether two argv *)
(* slots point at the same string.                                        *)
(*                                                                        *)
(* THE ENTRY CONDITIONS are all facts about the KEY:                       *)
(*                                                                        *)
(*   Hpc     the resume pc is [start]                                      *)
(*   Hsub    the image contains the dumped text                            *)
(*   Hx      page 0 is X and not W                                         *)
(*   Hroom   96 bytes of room below the resume sp, 8-aligned...            *)
(*   Hstk    ...and those 96 bytes present in the key's writable data      *)
(*   Hargs   the argc/argv area is well formed AT OR ABOVE the entry sp    *)
(*           ([UkAbi.uk_args_c], the canonical form at the SCANNED string  *)
(*           lengths -- it names no length function of its own)            *)
(*   Havd    ...and every byte of that area present in the writable data   *)
(*                                                                        *)
(* [Hargs]'s [uka_lo] at [lo = uint sp] is what puts the argument area on  *)
(* the far side of the cut from the frames, and hence what makes the two   *)
(* carves independent.                                                    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import WpMmodeLeafBase.
Require Import UmodeArith UmodeAbi.
Require Import WpUmodeLoad.
Require Import UkAbi.
Require Import UserPerm UexecSlot UexecRet.
Require Import UserHeap UkRun UkEcho.
Require Import UCodeEcho.
Require Import TsoCtx.
Require User.EchoSyms User.EchoInstrs.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 THE KEY'S OWN READINGS: where the frame, the array and the count    *)
(* are, read off the trapframe the kernel is resuming.                    *)
(* ===================================================================== *)
Definition uvis_sp (W : uvis) : mword 64 :=
  tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1.
Definition uvis_av (W : uvis) : Z :=
  uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx (mword_of_int 11 : mword 5)).
Definition uvis_argc (W : uvis) : Z :=
  uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx (mword_of_int 10 : mword 5)).

(* THE ARGUMENT LIST THE IMAGE SPELLS.  Nothing here is a choice: the
   pointer is the eight image bytes of the slot read as a word, the length
   is what a scan of the string finds, and the bytes are the image's.  That
   is what lets the gate be a predicate on the key alone. *)
Definition echo_arg (M : gmap Z (bv 8)) (av : Z) (i : nat) : uarg :=
  UArg (uk_argv_p M av (Z.of_nat i))
       (Z.to_nat (uk_slens M av (Z.of_nat i)))
       (fun j : nat =>
          default ubyte0 (M !! (uk_argv_p M av (Z.of_nat i) + Z.of_nat j)%Z)).

Definition echo_args (M : gmap Z (bv 8)) (av : Z) (argcn : nat) : list uarg :=
  echo_arg M av <$> seq 0 argcn.

Lemma echo_args_length (M : gmap Z (bv 8)) (av : Z) (argcn : nat) :
  length (echo_args M av argcn) = argcn.
Proof. unfold echo_args. rewrite length_fmap length_seq. reflexivity. Qed.

Lemma echo_args_lookup (M : gmap Z (bv 8)) (av : Z) (argcn i : nat) :
  (i < argcn)%nat -> echo_args M av argcn !! i = Some (echo_arg M av i).
Proof.
  intro Hi. unfold echo_args. rewrite list_lookup_fmap.
  rewrite (lookup_seq_lt 0 argcn i Hi). reflexivity.
Qed.

Section UEchoKernel.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.

  (* ------------------------------------------------------------------- *)
  (* §2 THE VECTOR, OUT OF THE PERSISTED AREA.                            *)
  (* ------------------------------------------------------------------- *)
  Lemma udata_lo_sub (M : gmap Z (bv 8)) (π : gmap (mword 27) uperm) (sz : Z) :
    udata_lo M π sz ⊆ M.
  Proof.
    unfold udata_lo, udata_part.
    etransitivity; apply map_filter_subseteq.
  Qed.

  (* [Z.rem] is what [UkAbi.uk_args] states its alignment with; [ustack] and
     [uargv] speak [mod].  At a nonnegative address they agree. *)
  Lemma zrem_mod_8 (a : Z) : 0 <= a -> Z.rem a 8 = 0 -> a mod 8 = 0.
  Proof.
    intros H0 Hr.
    rewrite (Z.mod_eq a 8 ltac:(lia)).
    rewrite <- (Z.quot_div_nonneg a 8 H0 ltac:(lia)).
    rewrite (Z.rem_eq a 8 ltac:(lia)) in Hr. lia.
  Qed.

  (* the area's bytes ARE the image's bytes, at any address the argument
     area covers.  Everything below is an instance of this. *)
  Lemma echo_area_lookup (M : gmap Z (bv 8)) (π : gmap (mword 27) uperm)
      (sz lo a : Z) :
    lo <= a -> is_Some (udata_lo M π sz !! a) ->
    base.filter (fun kv : Z * bv 8 => ~ (kv.1 < lo)) (udata_lo M π sz) !! a
    = M !! a.
  Proof.
    intros Hla [b Hb].
    rewrite (umap_filter_lookup_ge (udata_lo M π sz) lo a b ltac:(lia) Hb).
    symmetry.
    exact (proj1 (map_subseteq_spec _ M) (udata_lo_sub M π sz) a b Hb).
  Qed.

  (* ONE ARRAY SLOT: eight image bytes, read as the pointer word. *)
  Lemma echo_argv_word_of_area (γd : gname) (M : gmap Z (bv 8))
      (π : gmap (mword 27) uperm) (sz av lo argc : Z) (i : nat) :
    lo <= av ->
    (i < Z.to_nat argc)%nat ->
    uk_rd π M av (8 * argc) ->
    (forall j : nat, (j < 8 * Z.to_nat argc)%nat ->
       is_Some (udata_lo M π sz !! (av + Z.of_nat j)%Z)) ->
    ([∗ map] k ↦ b ∈ (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < lo)) (udata_lo M π sz)), ubyteq γd DfracDiscarded k b) -∗
      uwordq γd DfracDiscarded (av + 8 * Z.of_nat i)
        (mword_of_int (ua_ptr (echo_arg M av i))).
  Proof.
    intros Hlo Hi Hrd Havd. iIntros "#HA".
    assert (Hex : forall j : nat, (j < Z.to_nat 8)%nat ->
              exists b : bv 8,
                M !! (av + 8 * Z.of_nat i + Z.of_nat j)%Z = Some b).
    { intros j Hj.
      destruct (ukrd_bytes _ _ _ _ Hrd (8 * Z.of_nat i + Z.of_nat j)
                  ltac:(lia)) as [b Hb].
      exists b. replace (av + 8 * Z.of_nat i + Z.of_nat j)%Z
                  with (av + (8 * Z.of_nat i + Z.of_nat j))%Z by lia.
      exact Hb. }
    pose proof (uM_word_bytes M (av + 8 * Z.of_nat i) 8 ltac:(lia) Hex) as Hbw.
    assert (Hbytes : forall j : nat, (j < 8)%nat ->
              (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < lo)) (udata_lo M π sz))
                !! (av + 8 * Z.of_nat i + Z.of_nat j)%Z
              = Some (nth_byte
                        (mword_of_int (ua_ptr (echo_arg M av i)) : mword 64)
                        j)).
    { intros j Hj.
      assert (Hpres : is_Some (udata_lo M π sz
                        !! (av + 8 * Z.of_nat i + Z.of_nat j)%Z)).
      { replace (av + 8 * Z.of_nat i + Z.of_nat j)%Z
          with (av + Z.of_nat (8 * i + j)%nat)%Z by lia.
        exact (Havd (8 * i + j)%nat ltac:(lia)). }
      rewrite (echo_area_lookup M π sz lo
                 (av + 8 * Z.of_nat i + Z.of_nat j)%Z ltac:(lia) Hpres).
      cbn [ua_ptr echo_arg].
      rewrite (uk_argv_p_w M av (Z.of_nat i)). unfold uk_argv_w.
      exact (Hbw j ltac:(lia)). }
    iApply (uwordq_of_pmap γd (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < lo)) (udata_lo M π sz)) (av + 8 * Z.of_nat i)
              (mword_of_int (ua_ptr (echo_arg M av i))) Hbytes with "HA").
  Qed.

  (* ...AND THE STRING IT POINTS AT. *)
  Lemma echo_argv_str_of_area (γd : gname) (M : gmap Z (bv 8))
      (π : gmap (mword 27) uperm) (sz av lo : Z) (i : nat) :
    lo <= uk_argv_p M av (Z.of_nat i) ->
    0 <= uk_slens M av (Z.of_nat i) < 2 ^ 31 ->
    ucstr M (uk_argv_p M av (Z.of_nat i))
      (uk_slens M av (Z.of_nat i)) ->
    (forall j : nat,
       (j <= Z.to_nat (uk_slens M av (Z.of_nat i)))%nat ->
       is_Some (udata_lo M π sz
                 !! (uk_argv_p M av (Z.of_nat i) + Z.of_nat j)%Z)) ->
    ([∗ map] k ↦ b ∈ (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < lo)) (udata_lo M π sz)), ubyteq γd DfracDiscarded k b) -∗
      ustr γd DfracDiscarded (ua_ptr (echo_arg M av i))
        (ua_len (echo_arg M av i)) (ua_bytes (echo_arg M av i)).
  Proof.
    intros Hpl Hll Hcs Havs. iIntros "#HA".
    cbn [ua_ptr ua_len ua_bytes echo_arg].
    assert (Hlen : Z.of_nat
                     (Z.to_nat (uk_slens M av (Z.of_nat i)))
                   = uk_slens M av (Z.of_nat i))
      by (apply Z2Nat.id; lia).
    iApply (ustr_of_pmap γd (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < lo)) (udata_lo M π sz)) (uk_argv_p M av (Z.of_nat i))
              (Z.to_nat (uk_slens M av (Z.of_nat i)))
              (fun j : nat =>
                 default ubyte0
                   (M !! (uk_argv_p M av (Z.of_nat i) + Z.of_nat j)%Z))).
    - intros j Hj.
      destruct (ucs_body _ _ _ Hcs (Z.of_nat j) ltac:(lia)) as (b & Hb & Hnz).
      rewrite Hb. exact Hnz.
    - lia.
    - intros j Hj.
      rewrite (echo_area_lookup M π sz lo
                 (uk_argv_p M av (Z.of_nat i) + Z.of_nat j)%Z ltac:(lia)
                 (Havs j ltac:(lia))).
      destruct (ucs_body _ _ _ Hcs (Z.of_nat j) ltac:(lia)) as (b & Hb & _).
      rewrite Hb. reflexivity.
    - rewrite (echo_area_lookup M π sz lo
                 (uk_argv_p M av (Z.of_nat i)
                  + Z.of_nat (Z.to_nat
                       (uk_slens M av (Z.of_nat i))))%Z
                 ltac:(lia)
                 (Havs (Z.to_nat (uk_slens M av (Z.of_nat i)))
                    ltac:(apply Nat.le_refl))).
      rewrite Hlen. exact (ucs_nul _ _ _ Hcs).
    - iExact "HA".
  Qed.

  (* ONE ELEMENT: the slot and the string it points at, together. *)
  Lemma echo_argv_elem_of_area (γd : gname) (M : gmap Z (bv 8))
      (π : gmap (mword 27) uperm) (sz av lo argc : Z) (i : nat) :
    lo <= av ->
    (i < Z.to_nat argc)%nat ->
    uk_rd π M av (8 * argc) ->
    lo <= uk_argv_p M av (Z.of_nat i) ->
    0 <= uk_slens M av (Z.of_nat i) < 2 ^ 31 ->
    ucstr M (uk_argv_p M av (Z.of_nat i))
      (uk_slens M av (Z.of_nat i)) ->
    (forall j : nat, (j < 8 * Z.to_nat argc)%nat ->
       is_Some (udata_lo M π sz !! (av + Z.of_nat j)%Z)) ->
    (forall j : nat,
       (j <= Z.to_nat (uk_slens M av (Z.of_nat i)))%nat ->
       is_Some (udata_lo M π sz
                 !! (uk_argv_p M av (Z.of_nat i) + Z.of_nat j)%Z)) ->
    ([∗ map] k ↦ b ∈ (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < lo)) (udata_lo M π sz)), ubyteq γd DfracDiscarded k b) -∗
      uwordq γd DfracDiscarded (av + 8 * Z.of_nat i)
        (mword_of_int (ua_ptr (echo_arg M av i))) ∗
      ustr γd DfracDiscarded (ua_ptr (echo_arg M av i))
        (ua_len (echo_arg M av i)) (ua_bytes (echo_arg M av i)).
  Proof.
    intros Hlo Hi Hrd Hpl Hll Hcs Havd Havs. iIntros "#HA".
    iSplit.
    - iApply (echo_argv_word_of_area γd M π sz av lo argc i Hlo Hi Hrd Havd
                with "HA").
    - iApply (echo_argv_str_of_area γd M π sz av lo i Hpl Hll Hcs Havs
                with "HA").
  Qed.

  (* THE WHOLE VECTOR.                                                      *)
  (*                                                                        *)
  (* NOTE the length is [uk_slens M av i] throughout and NEVER              *)
  (* [uk_slen M (uk_argv_p M av i)], even though the two are convertible.   *)
  (* Asking the kernel to convert them is fatal: it unfolds both, lands on  *)
  (* two [uscan _ _ uk_slen_fuel] applications, and iota-reduces            *)
  (* [uk_slen_fuel = Z.to_nat (2^31)] -- a UNARY nat.  So the form          *)
  (* [uk_args_c] hands out is the form everything downstream is stated in.  *)
  Lemma echo_uargv_of_area (γd : gname) (M : gmap Z (bv 8))
      (π : gmap (mword 27) uperm) (sz av lo argc : Z) :
    0 <= lo ->
    uk_args_c π M av argc lo ->
    (forall j : nat, (j < 8 * Z.to_nat argc)%nat ->
       is_Some (udata_lo M π sz !! (av + Z.of_nat j)%Z)) ->
    (forall i j : nat, (i < Z.to_nat argc)%nat ->
       (j <= Z.to_nat (uk_slens M av (Z.of_nat i)))%nat ->
       is_Some (udata_lo M π sz
                 !! (uk_argv_p M av (Z.of_nat i) + Z.of_nat j)%Z)) ->
    ([∗ map] k ↦ b ∈ (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < lo)) (udata_lo M π sz)), ubyteq γd DfracDiscarded k b) -∗
      uargv γd av (echo_args M av (Z.to_nat argc)).
  Proof.
    intros Hlo0 Hargs Havd Havs. iIntros "#HA".
    pose proof Hargs as Hargs'.
    destruct Hargs' as [Hal Hlo Hargc Hrd Hptr].
    rewrite /uargv.
    iSplit; [ iPureIntro; apply zrem_mod_8; [ lia | exact Hal ] | ].
    iSplit; [ iPureIntro; rewrite echo_args_length; lia | ].
    rewrite /echo_args big_sepL_fmap.
    iApply big_sepL_intro. iIntros "!>" (k i Hki).
    apply lookup_seq in Hki as [Hki Hlt].
    assert (Hik : i = k) by lia. subst i.
    destruct (Hptr (Z.of_nat k) ltac:(lia)) as (Hpl & Hll & Hcs & _).
    iApply (echo_argv_elem_of_area γd M π sz av lo argc k Hlo Hlt Hrd
              Hpl Hll Hcs Havd (fun j Hj => Havs k j Hlt Hj) with "HA").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* §3 THE ENTRY CONDITIONS IN DECIDABLE FORM.  Each is a bounded ∀,     *)
  (* which no [Decision] instance finds on its own; the [Forall]-over-     *)
  (* [seq] form does, plus the one lemma that converts.  Same shape as     *)
  (* [USyncKernel.sync_stkdata], one level deeper for the strings.         *)
  (* ------------------------------------------------------------------- *)
  Definition echo_stkdata (W : uvis) : Prop :=
    Forall (fun j : nat =>
              is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                        !! (uint (uvis_sp W) - 8 * Z.of_nat 12
                            + Z.of_nat j)%Z))
           (seq 0 (8 * 12)).

  Global Instance echo_stkdata_dec (W : uvis) : Decision (echo_stkdata W).
  Proof.
    unfold echo_stkdata. apply Forall_dec. intro j.
    match goal with
    | |- context [ ?m !! ?k ] => destruct (m !! k) as [b |] eqn:E
    end.
    - left. exists b. reflexivity.
    - right. intros [x Hx]. discriminate.
  Defined.

  Lemma echo_stkdata_all (W : uvis) :
    echo_stkdata W ->
    forall j : nat, (j < 8 * 12)%nat ->
      is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                !! (uint (uvis_sp W) - 8 * Z.of_nat 12 + Z.of_nat j)%Z).
  Proof.
    unfold echo_stkdata. rewrite Forall_forall. intros HF j Hj.
    apply HF. apply in_seq. lia.
  Qed.

  (* the argv ARRAY's bytes... *)
  Definition echo_avd_arr (W : uvis) : Prop :=
    Forall (fun j : nat =>
              is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                        !! (uvis_av W + Z.of_nat j)%Z))
           (seq 0 (8 * Z.to_nat (uvis_argc W))).

  Global Instance echo_avd_arr_dec (W : uvis) : Decision (echo_avd_arr W).
  Proof.
    unfold echo_avd_arr. apply Forall_dec. intro j.
    match goal with
    | |- context [ ?m !! ?k ] => destruct (m !! k) as [b |] eqn:E
    end.
    - left. exists b. reflexivity.
    - right. intros [x Hx]. discriminate.
  Defined.

  Lemma echo_avd_arr_all (W : uvis) :
    echo_avd_arr W ->
    forall j : nat, (j < 8 * Z.to_nat (uvis_argc W))%nat ->
      is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                !! (uvis_av W + Z.of_nat j)%Z).
  Proof.
    unfold echo_avd_arr. rewrite Forall_forall. intros HF j Hj.
    apply HF. apply in_seq. lia.
  Qed.

  (* ...and every string's, terminator included *)
  Definition echo_avd_str (W : uvis) : Prop :=
    Forall (fun i : nat =>
              Forall (fun j : nat =>
                        is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                                  !! (uk_argv_p (uvis_M W) (uvis_av W)
                                        (Z.of_nat i) + Z.of_nat j)%Z))
                     (seq 0 (S (Z.to_nat (uk_slens (uvis_M W) (uvis_av W)
                                            (Z.of_nat i))))))
           (seq 0 (Z.to_nat (uvis_argc W))).

  Global Instance echo_avd_str_dec (W : uvis) : Decision (echo_avd_str W).
  Proof.
    unfold echo_avd_str. apply Forall_dec. intro i.
    apply Forall_dec. intro j.
    match goal with
    | |- context [ ?m !! ?k ] => destruct (m !! k) as [b |] eqn:E
    end.
    - left. exists b. reflexivity.
    - right. intros [x Hx]. discriminate.
  Defined.

  Lemma echo_avd_str_all (W : uvis) :
    echo_avd_str W ->
    forall i j : nat, (i < Z.to_nat (uvis_argc W))%nat ->
      (j <= Z.to_nat (uk_slens (uvis_M W) (uvis_av W) (Z.of_nat i)))%nat ->
      is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                !! (uk_argv_p (uvis_M W) (uvis_av W) (Z.of_nat i)
                    + Z.of_nat j)%Z).
  Proof.
    unfold echo_avd_str. rewrite Forall_forall. intros HF i j Hi Hj.
    assert (Hin : In i (seq 0 (Z.to_nat (uvis_argc W))))
      by (apply in_seq; lia).
    pose proof (HF i Hin) as Hi'. rewrite Forall_forall in Hi'.
    apply Hi'. apply in_seq. lia.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §4 THE DEPOSIT.                                                      *)
  (* ------------------------------------------------------------------- *)
  Lemma echo_uexec_slot (W : uvis) :
    tf_resume_pc (uvis_tf W) = (mword_of_int EchoSyms.start : mword 64) ->
    echo_text_sub (uvis_M W) ->
    (forall a : Z, 0 <= a < 4096 ->
       ux_addr (uvis_perm W) a /\ ~ uw_addr (uvis_perm W) a) ->
    96 <= uint (uvis_sp W) ->
    uint (uvis_sp W) mod 8 = 0 ->
    (forall j : nat, (j < 8 * 12)%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (uvis_sp W) - 8 * Z.of_nat 12 + Z.of_nat j)%Z)) ->
    uk_args_c (uvis_perm W) (uvis_M W) (uvis_av W) (uvis_argc W)
      (uint (uvis_sp W)) ->
    (forall j : nat, (j < 8 * Z.to_nat (uvis_argc W))%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uvis_av W + Z.of_nat j)%Z)) ->
    (forall i j : nat, (i < Z.to_nat (uvis_argc W))%nat ->
       (j <= Z.to_nat (uk_slens (uvis_M W) (uvis_av W) (Z.of_nat i)))%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uk_argv_p (uvis_M W) (uvis_av W) (Z.of_nat i)
                     + Z.of_nat j)%Z)) ->
    ⊢ uslot W.
  Proof.
    intros Hpc Hsub Hx Hroom Hal8 Hstk Hargs Havd Havs.
    assert (Hsp0 : 0 <= uint (uvis_sp W)) by lia.
    assert (Hargc0 : 0 <= uvis_argc W)
      by exact (proj1 (uka_argc _ _ _ _ _ _ Hargs)).
    iApply (uslot_of_urun_ro W 12 Hal8
              ltac:(unfold uvis_sp in Hroom; lia) Hstk).
    iIntros (γt γd γs h) "%Hsz Hszf #Ht #HA Hrun".
    rewrite Hpc.
    iApply (wp_kecho_start γt γd γs h (tf_resume_gpr0 (uvis_tf W))
              (uvis_av W)
              (echo_args (uvis_M W) (uvis_av W) (Z.to_nat (uvis_argc W))) 0
              ltac:(rewrite echo_args_length;
                    rewrite (Z2Nat.id (uvis_argc W) Hargc0);
                    unfold uvis_argc; symmetry; apply moi_of_uint)
              ltac:(unfold uvis_av; symmetry; apply moi_of_uint)
              with "[] [] Hrun").
    { iApply (echo_code_of_text γt (uvis_M W) (uvis_perm W) Hsub Hx
                with "Ht"). }
    { iApply (echo_uargv_of_area γd (uvis_M W) (uvis_perm W) (uvis_sz W)
                (uvis_av W) (uint (uvis_sp W)) (uvis_argc W)
                Hsp0 Hargs Havd Havs with "HA"). }
  Qed.

End UEchoKernel.
