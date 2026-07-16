(* WpUserClassifyTotal.v -- the total-classification capstone: prove
   [∀ frame, ustep_case ∨ ustep_mem_case ∨ ustep_fault_case] with no
   TLB-hit premise, then feed it to [user_step_holds_full] for an
   unconditional [wp_user_exec].  Built incrementally against local
   well-formedness hypotheses; the [uctx] contract fields are baked in
   at the end. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep.
Require Import UmodeFetch.
Require Import UptInv WpUserBase.
Require Import WpUserSteps.
Require Import WpUserClassify.
Require Import WpDecodeBridge.
Require Import UmodeEcall.
Require Import DecodeSetU.
Local Open Scope Z_scope.
Import Defs.

(* ------------------------------------------------------------------ *)
(* Fetch-word existence: if all 4 bytes of an instruction slot are
   present in a byte map, they assemble into a concrete word whose
   [nth_byte]s are exactly those bytes.  This is the pure engine that
   turns a "page is resident in [code]" well-formedness fact into the
   [∃ w, ...] fetch premise of [ufetch_hit].                          *)
(* ------------------------------------------------------------------ *)

(* [nth_byte] of a little-endian assembled word recovers each byte.  This is
   the instance-free core (it never touches a gmap, only [bv 8] values), so it
   sidesteps the [Arch.pa] Countable-instance mismatch between [read_bytes]
   (stdpp [bv_countable]) and the [uctx] [code]/[data] maps. *)
Lemma nth_byte_assemble (bs : list (bv 8)) (j : nat) :
  (j < length bs)%nat ->
  nth_byte (Z_to_bv (8 * N.of_nat (length bs)) (assemble_bytes bs)) j = bs !!! j.
Proof.
  intros Hjlt.
  apply bv_eq. rewrite nth_byte_unsigned.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  pose proof (assemble_bytes_bound bs) as [Hlo Hhi].
  rewrite (Z.mod_small (assemble_bytes bs));
    [| split; [lia | rewrite N2Z.inj_mul; lia ] ].
  pose proof (assemble_bytes_byte bs j Hjlt) as Hbyte.
  rewrite Nat2Z.inj_mul in Hbyte. change (Z.of_nat 8) with 8 in Hbyte.
  replace (Z.of_N (8 * N.of_nat j)) with (8 * Z.of_nat j) by (rewrite N2Z.inj_mul; lia).
  rewrite Hbyte. reflexivity.
Qed.

(* Four bytes assemble into a concrete 32-bit word whose [nth_byte]s are
   exactly those bytes -- the pure fetch-word constructor. *)
Lemma word_of_bytes4 (b0 b1 b2 b3 : bv 8) :
  exists w : mword 32,
    nth_byte w 0%nat = b0 /\ nth_byte w 1%nat = b1 /\
    nth_byte w 2%nat = b2 /\ nth_byte w 3%nat = b3.
Proof.
  exists (Z_to_bv 32 (assemble_bytes [b0;b1;b2;b3])).
  pose proof (fun j Hj => nth_byte_assemble [b0;b1;b2;b3] j Hj) as H.
  simpl length in H. change (8 * N.of_nat 4)%N with 32%N in H.
  split; [|split; [|split]].
  - exact (H 0%nat ltac:(lia)).
  - exact (H 1%nat ltac:(lia)).
  - exact (H 2%nat ltac:(lia)).
  - exact (H 3%nat ltac:(lia)).
Qed.

(* Two bytes assemble into a 16-bit halfword (compressed fetch). *)
Lemma hword_of_bytes2 (b0 b1 : bv 8) :
  exists h : mword 16,
    nth_byte h 0%nat = b0 /\ nth_byte h 1%nat = b1.
Proof.
  exists (Z_to_bv 16 (assemble_bytes [b0;b1])).
  pose proof (fun j Hj => nth_byte_assemble [b0;b1] j Hj) as H.
  simpl length in H. change (8 * N.of_nat 2)%N with 16%N in H.
  split.
  - exact (H 0%nat ltac:(lia)).
  - exact (H 1%nat ltac:(lia)).
Qed.

(* Package: given the four instruction bytes present in a byte map [mm]
   (any instance), there is a word [w] with [mm !! pa_add pa j = Some
   (nth_byte w j)] for j < 4 -- the exact shape of the [ufetch_hit] fetch
   conjunct.  Works for [code] regardless of its Countable instance. *)
Lemma bytes_to_word4 {K} `{Countable K} (mm : gmap K (bv 8))
    (nb : nat -> K) :
  (forall j, (j < 4)%nat -> exists b, mm !! nb j = Some b) ->
  exists w : mword 32,
    forall j, (j < 4)%nat -> mm !! nb j = Some (nth_byte w j).
Proof.
  intros Hex.
  destruct (Hex 0%nat ltac:(lia)) as [b0 Hb0].
  destruct (Hex 1%nat ltac:(lia)) as [b1 Hb1].
  destruct (Hex 2%nat ltac:(lia)) as [b2 Hb2].
  destruct (Hex 3%nat ltac:(lia)) as [b3 Hb3].
  destruct (word_of_bytes4 b0 b1 b2 b3) as (w & E0 & E1 & E2 & E3).
  exists w. intros j Hj.
  destruct j as [|[|[|[|j']]]]; try lia;
    first [ rewrite E0 | rewrite E1 | rewrite E2 | rewrite E3 ]; assumption.
Qed.

Lemma bytes_to_hword2 {K} `{Countable K} (mm : gmap K (bv 8))
    (nb : nat -> K) :
  (forall j, (j < 2)%nat -> exists b, mm !! nb j = Some b) ->
  exists h : mword 16,
    forall j, (j < 2)%nat -> mm !! nb j = Some (nth_byte h j).
Proof.
  intros Hex.
  destruct (Hex 0%nat ltac:(lia)) as [b0 Hb0].
  destruct (Hex 1%nat ltac:(lia)) as [b1 Hb1].
  destruct (hword_of_bytes2 b0 b1) as (h & E0 & E1).
  exists h. intros j Hj.
  destruct j as [|[|j']]; try lia;
    first [ rewrite E0 | rewrite E1 ]; assumption.
Qed.

(* ==================================================================== *)
(* Section: the fetch-side producers, against a LOCAL code-residence     *)
(* hypothesis (baked into uctx at the end).                              *)
(* ==================================================================== *)
Section Total.
  Context `{CID : CpuId}.
  Context (U : WpUserBase.uctx).

  Local Notation code := (WpUserBase.code U).
  Local Notation spec := (WpUserBase.spec U).
  Local Notation ufetch_hit := (WpUserClassify.ufetch_hit U).
  Local Notation cfetch_hit := (WpUserClassify.cfetch_hit U).
  Local Notation ustep_case := (WpUserSteps.ustep_case U).

  (* Fetch-fault producer 1: a 4-aligned but non-canonical pc lands in
     [ustep_case] disjunct 1 (instruction-address fetch fault, no page
     walk needed). *)
  Lemma produce_noncanonical (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = true ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hal Hnc. unfold WpUserSteps.ustep_case.
    left. split; assumption.
  Qed.

  (* Fetch-fault producer 2: a 4-aligned, canonical pc whose vpn is
     unmapped (kernel-only) lands in [ustep_case] disjunct 2. *)
  Lemma produce_unmapped (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (vpn : mword 27) :
    spec !! vpn = None ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hnone Hal Hcanon Hvpn. unfold WpUserSteps.ustep_case.
    right; left. exists vpn. repeat split; assumption.
  Qed.

  (* Fetch-fault producer 3: a mapped, fetch-checked page whose leaf PTE
     still needs an A-bit update (ADUE = 0) lands in [ustep_case]
     disjunct 3 (the atomic-update fault). *)
  Lemma produce_adfault (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (pte' : mword 64) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = Some pte' ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hsome Hchk Hupd Hal Hcanon Hvpn. unfold WpUserSteps.ustep_case.
    right; right; left. exists vpn, ie, pte'. repeat split; assumption.
  Qed.

  (* For a 4-aligned, canonical, executable, A-set, mapped page whose
     instruction bytes are resident in [code], the fetch either yields a
     full 32-bit word ([ufetch_hit]) or a compressed halfword
     ([cfetch_hit]) -- decided by [isRVC] of the low halfword.  This is
     the core fetch-premise producer for the classification's decode step. *)
  Lemma produce_fetch_4aligned
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    (forall j : nat, (j < 4)%nat ->
       exists b, code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some b) ->
    (exists w : mword 32, ufetch_hit va vpn ie w tlbvec)
    \/ (exists h : mword 16, cfetch_hit va vpn ie h tlbvec).
  Proof.
    intros Hsome Hchk Hupd Hpbmt Hval Hcanon Hvpn_def Hpaal Hres.
    destruct (bytes_to_word4 code
                (fun j => pa_add (u_pa (upt_entry vpn ie) va vpn) j) Hres)
      as [w Hcw].
    destruct (isRVC (subrange_vec_dec w 15 0)) eqn:Hrvc.
    - (* compressed: low halfword is an RVC instruction *)
      right. exists (subrange_vec_dec w 15 0).
      unfold WpUserClassify.cfetch_hit.
      split; [exact Hsome |].
      split; [exact Hchk |].
      split; [exact Hupd |].
      split; [exact Hpbmt |].
      split; [exact Hcanon |].
      split; [exact Hvpn_def |].
      split.
      + (* c_fetch_mode, 4-aligned branch *)
        left. exists w.
        split; [exact Hval |].
        split; [exact Hpaal |].
        split; [exact Hcw | reflexivity].
      + exact Hrvc.
    - (* full 32-bit instruction *)
      left. exists w.
      unfold WpUserClassify.ufetch_hit.
      split; [exact Hsome |].
      split; [exact Hchk |].
      split; [exact Hupd |].
      split; [exact Hpbmt |].
      split; [exact Hcw |].
      split; [exact Hval |].
      split; [exact Hcanon |].
      split; [exact Hvpn_def |].
      split; [exact Hpaal | exact Hrvc].
  Qed.

  (* Case-5 dispatch for an executable, A-set, 4-aligned page whose full
     32-bit words all decode to compute/system instructions in the
     [classifiable_u] set: the fetch either retires (full word ->
     [classify_word_of_decode] -> [ustep_case]) or is compressed and
     hands back a [cfetch_hit] for the compressed dispatcher to consume.
     This composes [produce_fetch_4aligned] with the proven full-word
     classifier; it needs NO new arms and is total over rd (the full-word
     compute disjuncts carry the [if uint rd =? 0 ...] form). *)
  Lemma dispatch_full_page_classifiable
      (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (vpn : mword 27) (ie : uwalk_info)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    (forall j : nat, (j < 4)%nat ->
       exists b, code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some b) ->
    (forall w : mword 32, ufetch_hit va vpn ie w tlbvec ->
       forall ii, decodable_u ii = true ->
         (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
         classifiable_u ii = true) ->
    ustep_case va ms_v g tlbvec
    \/ (exists h : mword 16, cfetch_hit va vpn ie h tlbvec).
  Proof.
    intros Hsome Hchk Hupd Hpbmt Hval Hcanon Hvpn_def Hpaal Hres Hcl.
    destruct (produce_fetch_4aligned va vpn ie tlbvec
                Hsome Hchk Hupd Hpbmt Hval Hcanon Hvpn_def Hpaal Hres)
      as [[w Huf] | [h Hcf]].
    - left.
      exact (WpUserClassify.classify_word_of_decode U va ms_v g tlbvec vpn ie w
               Huf (Hcl w Huf)).
    - right. exists h. exact Hcf.
  Qed.

  (* Total BTYPE not-taken dispatch: a fetched, decoded conditional branch
     whose runtime condition is FALSE falls through to pc+4, landing in
     the fall-through disjunct regardless of branch op.  The fall case
     needs no target-alignment side condition, so this is total over all
     six [bop] constructors (the taken case additionally needs a 4-aligned
     target, and 2-aligned/misaligned taken targets are a separate arm). *)
  Lemma classify_btype_fall_dispatch
      (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (imm : mword 13) (rs2 rs1 : mword 5) (op : bop) :
    ufetch_hit va vpn ie w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (BTYPE (imm, Regidx rs2, Regidx rs1, op), s0)) ->
    match op with
    | BEQ  => eq_vec (g !!! Regidx rs1) (g !!! Regidx rs2) = false
    | BNE  => neq_vec (g !!! Regidx rs1) (g !!! Regidx rs2) = false
    | BLT  => zopz0zI_s (g !!! Regidx rs1) (g !!! Regidx rs2) = false
    | BGE  => zopz0zKzJ_s (g !!! Regidx rs1) (g !!! Regidx rs2) = false
    | BLTU => zopz0zI_u (g !!! Regidx rs1) (g !!! Regidx rs2) = false
    | BGEU => zopz0zKzJ_u (g !!! Regidx rs1) (g !!! Regidx rs2) = false
    end ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec Hc. destruct op.
    - exact (WpUserClassify.classify_btype_beq_fall U va ms_v g tlbvec vpn ie w imm rs2 rs1 Hf Hdec Hc).
    - exact (WpUserClassify.classify_btype_bne_fall U va ms_v g tlbvec vpn ie w imm rs2 rs1 Hf Hdec Hc).
    - exact (WpUserClassify.classify_btype_blt_fall U va ms_v g tlbvec vpn ie w imm rs2 rs1 Hf Hdec Hc).
    - exact (WpUserClassify.classify_btype_bge_fall U va ms_v g tlbvec vpn ie w imm rs2 rs1 Hf Hdec Hc).
    - exact (WpUserClassify.classify_btype_bltu_fall U va ms_v g tlbvec vpn ie w imm rs2 rs1 Hf Hdec Hc).
    - exact (WpUserClassify.classify_btype_bgeu_fall U va ms_v g tlbvec vpn ie w imm rs2 rs1 Hf Hdec Hc).
  Qed.

  (* Total BTYPE taken dispatch for a 4-aligned target: condition TRUE and
     the branch target [va + sext imm] is 4-aligned (bit0 = 0, bit1 = 0)
     -> the taken disjunct, for every branch op.  (A 2-aligned or odd
     target that is taken is a separate, still-missing, arm.) *)
  Lemma classify_btype_taken_dispatch
      (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (imm : mword 13) (rs2 rs1 : mword 5) (op : bop) :
    ufetch_hit va vpn ie w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (BTYPE (imm, Regidx rs2, Regidx rs1, op), s0)) ->
    match op with
    | BEQ  => eq_vec (g !!! Regidx rs1) (g !!! Regidx rs2) = true
    | BNE  => neq_vec (g !!! Regidx rs1) (g !!! Regidx rs2) = true
    | BLT  => zopz0zI_s (g !!! Regidx rs1) (g !!! Regidx rs2) = true
    | BGE  => zopz0zKzJ_s (g !!! Regidx rs1) (g !!! Regidx rs2) = true
    | BLTU => zopz0zI_u (g !!! Regidx rs1) (g !!! Regidx rs2) = true
    | BGEU => zopz0zKzJ_u (g !!! Regidx rs1) (g !!! Regidx rs2) = true
    end ->
    eq_vec (access_vec_dec (add_vec va (sign_extend' 64 imm)) 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec (add_vec va (sign_extend' 64 imm)) 1) = false ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec Hc H0 H1. destruct op.
    - exact (WpUserClassify.classify_btype_beq_taken U va ms_v g tlbvec vpn ie w imm rs2 rs1 Hf Hdec Hc H0 H1).
    - exact (WpUserClassify.classify_btype_bne_taken U va ms_v g tlbvec vpn ie w imm rs2 rs1 Hf Hdec Hc H0 H1).
    - exact (WpUserClassify.classify_btype_blt_taken U va ms_v g tlbvec vpn ie w imm rs2 rs1 Hf Hdec Hc H0 H1).
    - exact (WpUserClassify.classify_btype_bge_taken U va ms_v g tlbvec vpn ie w imm rs2 rs1 Hf Hdec Hc H0 H1).
    - exact (WpUserClassify.classify_btype_bltu_taken U va ms_v g tlbvec vpn ie w imm rs2 rs1 Hf Hdec Hc H0 H1).
    - exact (WpUserClassify.classify_btype_bgeu_taken U va ms_v g tlbvec vpn ie w imm rs2 rs1 Hf Hdec Hc H0 H1).
  Qed.

End Total.

(* ==================================================================== *)
(* ROADMAP for the total classification (capstone, multi-session).      *)
(*                                                                      *)
(* GOAL: prove [user_classify]:                                         *)
(*   forall va ms_v g tlbvec, upt_tlb_ok spec tlbvec ->                 *)
(*     _get_Mstatus_SXL ms_v = 'b"10" ->                                *)
(*     ustep_case va ms_v g tlbvec \/ ustep_mem_case va ms_v g tlbvec   *)
(*     \/ ustep_fault_case va ms_v g tlbvec                             *)
(* then feed it to WpUserFull.user_step_holds_full for an               *)
(* unconditional wp_user_exec.                                          *)
(*                                                                      *)
(* uctx WELL-FORMEDNESS FIELDS still to add (safe: no concrete uctx     *)
(* instance exists yet -- verified 2026-07-16). Develop against LOCAL   *)
(* Hypotheses in a Section here first, bake into uctx (WpUserBase:44)   *)
(* only once the classification is proven:                              *)
(*   Hcode_resident : for every executable-mapped vpn (spec!!vpn=Some   *)
(*     ie, uw_check_ok (InstructionFetch tt) ie) and every va in that   *)
(*     page, the 4 instruction bytes at u_pa(upt_entry vpn ie) va vpn   *)
(*     are present in [code]  (-> bytes_to_word4 gives the fetch word). *)
(*   Hdata_resident / Hcode_readable : for every read-mapped data vpn,  *)
(*     the page's phys bytes are in [code] ∪ [data]  (LOAD source).     *)
(*   Hmapped_exec_or_fault, Hmapped_perms : relate spec perms so a      *)
(*     mapped page is either exec (fetch ok) or the fetch faults; ditto *)
(*     Load/Store Data perms -> mem_case vs fault_case.                 *)
(*                                                                      *)
(* CASE TREE (over va, then decode, then -- for LOAD/STORE -- eaF):     *)
(*  1. va NOT canonical -> ustep_case disjunct 1 (fetch noncanonical).  *)
(*  2. vpn := extract(va); spec!!vpn = None -> ustep_case disjunct 2.   *)
(*  3. Some ie, not exec (uw_check_ok fetch fails) -> NEEDS a new       *)
(*     "mapped-but-not-executable" fetch-fault arm (MISSING - build it  *)
(*     both exec-side and as a ustep_case/fault disjunct).              *)
(*  4. exec, A-update needed (update_PTE_Bits = Some) -> ustep_case     *)
(*     disjunct 3, via [produce_adfault]  (DONE).                       *)
(*  5. exec, A-set: produce the fetch word/halfword (bytes_to_word4 +   *)
(*     Hcode_resident) via [produce_fetch_4aligned] (DONE); case isRVC: *)
(*       - full 32-bit: ufetch_hit; decode_total_u_set -> dispatch:     *)
(*           * classifiable_u/covered_u -> classify_word_of_decode      *)
(*             NOTE: the full-word compute disjuncts (ITYPE/RTYPE/...)   *)
(*             use the TOTAL [if uint rd =? 0 then s else set_reg ...]   *)
(*             execute form, so classify_word is TOTAL over rd -- the    *)
(*             rd=x0 HINT cases need NO extra arm on the full-word side. *)
(*           * JAL/JALR -> classify_jal/jalr (target 2-aligned via C)   *)
(*           * BTYPE -> eval branch cond on g (decidable) ->            *)
(*             classify_btype_*_{taken,fall}                            *)
(*           * LOAD/STORE/AMO -> DATA-SIDE (step 6)                     *)
(*       - compressed 16-bit: cfetch_hit (c_fetch_mode 4-aligned or,    *)
(*         for 2-aligned va, 2-aligned branch); dispatch the C_* the    *)
(*         same way via the classify_c_* lemmas.                        *)
(*         *** GAP (found 2026-07-16): unlike the full-word leaves, the  *)
(*         compressed classify_c_* compute leaves (classify_c_add/mv/    *)
(*         addi/... and every RVC ITYPE/RTYPE/UTYPE/SHIFTIOP/RTYPEW/MUL  *)
(*         expander) REQUIRE [uint rd <> 0] (RVC disjuncts 16-31 bake    *)
(*         rd<>0 in via [do N right]).  So the compressed dispatcher is  *)
(*         NOT total: the rd=x0 RVC HINT cases (C_ADD x0, C_MV x0, ...   *)
(*         C_SLLI x0, C_ADDI x0 = C_NOP-form) have NO disjunct and need  *)
(*         either (a) new rd=0 RVC compute arms, or (b) proof that the   *)
(*         rd=0 expansions collapse to a RETIRE that lands in the RVC    *)
(*         no-op disjunct (classify_c_nop, disjunct for state-preserving *)
(*         RETIRE).  Build these BEFORE the compressed dispatcher.       *)
(*  6. DATA-SIDE (LOAD/STORE/AMO): eaF := g!!!rs1 + imm; decide         *)
(*       - Virtaddr eaF canonical? aligned to width? (decidable)        *)
(*       - vpnD := extract(eaF); spec!!vpnD None -> ustep_fault_case;   *)
(*         Some ieD, perms/A/PBMT -> width-aligned + bytes in code/data *)
(*         -> ustep_mem_case (the matching width disjunct).             *)
(*       - MISSING ARMS to build first: misaligned-load/store fault,    *)
(*         data-no-perm fault, data-TLB-miss (walk inside execute --    *)
(*         task #29). ustep_mem_case/fault_case currently only cover    *)
(*         data-HIT + aligned + unmapped; misalignment has NO disjunct. *)
(*                                                                      *)
(* DECIDABILITY helpers needed: canonical-va (neq_vec ... decidable),   *)
(* is_aligned_vaddr (decidable), spec!!vpn (gmap lookup), uw_check_ok   *)
(* (needs a decision procedure or a spec-level exec/read/write-perm     *)
(* classification in uwalk_info), update_PTE_Bits (option match),       *)
(* byte-residence (∈ code/data, gset/gmap membership decidable).        *)
(*                                                                      *)
(* DONE so far (this file, all green, zero admits):                     *)
(*   - word_of_bytes4 / bytes_to_word4 (+ hword variants): the instance- *)
(*     free byte->word fetch-word constructor.                          *)
(*   - produce_fetch_4aligned: page facts + code residence -> ufetch_hit *)
(*     \/ cfetch_hit  (isRVC split) -- the case-5 fetch producer.        *)
(*   - produce_noncanonical / produce_unmapped / produce_adfault:       *)
(*     the case-1/2/4 ustep_case leaves (disjuncts 1/2/3), no new arms.  *)
(*   - dispatch_full_page_classifiable: case-5 full-word compute/system  *)
(*     composition (produce_fetch + classify_word_of_decode), total/rd.  *)
(*   - classify_btype_fall_dispatch / classify_btype_taken_dispatch:     *)
(*     total BTYPE decode dispatch over all 6 bop (fall unconditional;   *)
(*     taken for 4-aligned targets).                                     *)
(*                                                                      *)
(* FETCH-SIDE now complete EXCEPT these residual obligations, each       *)
(* blocked on a MISSING arm (build in step C):                          *)
(*   - JAL/JALR rd=x0 (plain jump, no link): classify_jal/jalr require   *)
(*     uint rd<>0; rd=0 needs a new disjunct.                           *)
(*   - JAL/JALR/BTYPE taken to a non-4-aligned target: misaligned-       *)
(*     instruction-fetch fault, no disjunct yet.                        *)
(*   - full-word LOAD/STORE/AMO: route to the data side (step 6).        *)
(*                                                                      *)
(* NEXT (in dependency order):                                          *)
(*   B. Compressed rd=0 HINT arms (see case-5 GAP) then the compressed  *)
(*      classifiable dispatcher (classifiable_c + classify_c_word), plus *)
(*      the compressed jump/branch (C_J/C_JR/C_JALR/C_BEQZ/C_BNEZ)       *)
(*      dispatch mirroring the full-word BTYPE dispatchers above.        *)
(*   C. The MISSING fault arms: mapped-non-exec fetch, misaligned       *)
(*      fetch/jump-target, misaligned/no-perm data, data-TLB-miss.      *)
(*      Each = new ustep_case/mem/fault disjunct + exec-side soundness   *)
(*      arm (forces ~30-file rebuild; batch these).                     *)
(*   D. uctx wf fields (above) + the top-level va case tree tying it     *)
(*      all together into [user_classify], fed to user_step_holds_full. *)
(* ==================================================================== *)
