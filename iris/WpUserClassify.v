(* WpUserClassify.v -- the decode -> classification connection.

   [decode_total_u_set] (DecodeSetU.v) says every 32-bit word decodes to a
   constructor of the explicit image [decodable_u].  [ustep_case]
   (WpUserSteps.v) is the disjunction the step dispatcher consumes.  This
   file starts wiring the two together: given the shared "fetch-hit" premise
   bundle for a word [w] at [va], route the constructor [w] decodes to into
   its [ustep_case] disjunct.

   The connection is PARTIAL by construction.  Several [decodable_u]
   constructors have no [ustep_case] home -- LOAD/STORE/AMO/LOADRES/STORECON
   are standalone spatial theorems, and BTYPE/JAL/JALR carry runtime
   [g]-dependent guards (branch-taken, target alignment) that cannot be
   decided generically.  So this file covers the guard-free constructors and
   grows over time; [covered_u] names exactly the constructors handled so
   far.  This first slice: the unconditional trap/no-op ops ILLEGAL (-> the
   trap disjunct), PAUSE and NTL (-> the no-op disjunct). *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec.
Require Import WpDecodeBridge.
Require Import UmodeFetch UmodeEcall.
Require Import UptInv WpUserBase.
Require Import WpUserSteps.
Require Import DecodeSetU.
Local Open Scope Z_scope.
Import Defs.

(* ---------------------------------------------------------------------- *)
(* Unconditional execute facts for the trivially-direct ops.  Each
   dispatches to [returnM <direct result>]; the [change ... with] keeps the
   [execute] dispatcher out of the proof term (no reservation-axiom leak). *)

Lemma exec_execute_ILLEGAL_any (z : mword 32) s :
  exec (execute (ILLEGAL z)) s = Some (Illegal_Instruction tt, s).
Proof.
  change (execute (ILLEGAL z)) with (returnM (execute_ILLEGAL z) : M ExecutionResult).
  unfold execute_ILLEGAL. apply exec_returnM.
Qed.

Lemma exec_execute_PAUSE_any (u : unit) s :
  exec (execute (PAUSE u)) s = Some (RETIRE_SUCCESS, s).
Proof.
  destruct u.
  change (execute (PAUSE tt)) with (returnM (execute_PAUSE tt) : M ExecutionResult).
  unfold execute_PAUSE. apply exec_returnM.
Qed.

Lemma exec_execute_NTL_any (nt : ntl_type) s :
  exec (execute (NTL nt)) s = Some (RETIRE_SUCCESS, s).
Proof.
  change (execute (NTL nt)) with (returnM (execute_NTL nt) : M ExecutionResult).
  unfold execute_NTL. apply exec_returnM.
Qed.

Section WpUserClassify.
  Context `{CID : CpuId}.
  Context (U : WpUserBase.uctx).

  Local Notation code := (WpUserBase.code U).
  Local Notation spec := (WpUserBase.spec U).
  Local Notation ustep_case := (WpUserSteps.ustep_case U).

  (* The fetch-hit premise bundle shared by [ustep_case]'s decode disjuncts
     (5-15): the word [w] is fetched from a mapped, checked, non-PBMT,
     4-aligned canonical code page and is not compressed. *)
  Definition ufetch_hit (va : mword 64) (vpn : mword 27) (i : uwalk_info)
      (w : mword 32) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) : Prop :=
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
    uw_check_ok (InstructionFetch tt) i /\
    update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
    is_aligned_vaddr (Virtaddr va) 4 = true /\
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
    isRVC (subrange_vec_dec w 15 0) = false.

  (* A word whose execute is unconditionally state-preserving RETIRE lands in
     the no-op disjunct (11). *)
  Lemma classify_nop (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (ii : instruction) :
    (forall s, exec (execute ii) s = Some (RETIRE_SUCCESS, s)) ->
    is_lpad_instruction ii = false ->
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hexec Hlpad
      (Hvec & Hchk & Hupd & Hpbmt & Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC) Hdec.
    unfold ustep_case, WpUserSteps.ustep_case.
    right; right; right; right; right; right; right; right; right; right; left.
    exists vpn, i, w, ii. repeat split; assumption.
  Qed.

  (* A word whose execute is unconditionally Illegal lands in the trap
     disjunct (12). *)
  Lemma classify_illegal (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (ii : instruction) :
    (forall s, exec (execute ii) s = Some (Illegal_Instruction tt, s)) ->
    is_lpad_instruction ii = false ->
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hexec Hlpad
      (Hvec & Hchk & Hupd & Hpbmt & Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC) Hdec.
    unfold ustep_case, WpUserSteps.ustep_case.
    right; right; right; right; right; right; right; right; right; right; right; left.
    exists vpn, i, w, ii. repeat split; assumption.
  Qed.

  (* The constructors this file classifies so far. *)
  Definition covered_u (ii : instruction) : bool :=
    match ii with
    | ILLEGAL _ => true
    | PAUSE _ => true
    | NTL _ => true
    | _ => false
    end.

  (* A [covered_u] constructor executes unconditionally: it is not a landing
     pad, and either it always retires state-preserving (PAUSE/NTL -> the
     no-op disjunct) or it always traps Illegal (ILLEGAL -> the trap
     disjunct).  The goal mentions [ii], so the field of the surviving
     constructor is tied by unification (no dangling evar). *)
  Lemma covered_u_exec (ii : instruction) :
    covered_u ii = true ->
    is_lpad_instruction ii = false /\
    ((forall s, exec (execute ii) s = Some (RETIRE_SUCCESS, s)) \/
     (forall s, exec (execute ii) s = Some (Illegal_Instruction tt, s))).
  Proof.
    intros Hcov. destruct ii; try discriminate Hcov; clear Hcov;
      (split; [ reflexivity | ]);
      first [ left; apply exec_execute_PAUSE_any
            | left; apply exec_execute_NTL_any
            | right; apply exec_execute_ILLEGAL_any ].
  Qed.

  (* The connection: given the fetch-hit bundle and the decode fact for the
     word, any [covered_u] constructor is placed into [ustep_case].  The
     caller obtains the decode fact and [decodable_u]-membership from
     [decode_total_u_set w] and checks [covered_u] by computation. *)
  Lemma classify_covered (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (ii : instruction) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
    covered_u ii = true ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec Hcov.
    destruct (covered_u_exec ii Hcov) as (Hlpad & [Hnop | Hill]).
    - exact (classify_nop va ms_v g tlbvec vpn i w ii Hnop Hlpad Hf Hdec).
    - exact (classify_illegal va ms_v g tlbvec vpn i w ii Hill Hlpad Hf Hdec).
  Qed.

  (* The full pipeline: [decode_total_u_set] supplies the (unique, agreeing)
     decoded instruction and its [decodable_u] membership; the caller only
     has to confirm -- by computation on that constructor -- that it is
     [covered_u].  Uncovered words (LOAD/STORE/AMO/branches/jumps) fall
     outside this lemma and are handled by their own step theorems. *)
  Lemma classify_of_decode (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) :
    ufetch_hit va vpn i w tlbvec ->
    (forall ii, decodable_u ii = true ->
       (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
       covered_u ii = true) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hcov.
    destruct (decode_total_u_set w) as (ii & Hdu & Hdec).
    exact (classify_covered va ms_v g tlbvec vpn i w ii Hf Hdec (Hcov ii Hdu Hdec)).
  Qed.

End WpUserClassify.
