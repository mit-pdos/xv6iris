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
Require Import UmodeFetch.
Require Import UptInv WpUserBase.
Require Import WpUserSteps.
Require Import WpUserClassify.
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
(*     disjunct 3 (adfault).                                            *)
(*  5. exec, A-set: produce the fetch word/halfword (bytes_to_word4 +   *)
(*     Hcode_resident); case isRVC(low halfword):                       *)
(*       - full 32-bit: ufetch_hit; decode_total_u_set -> dispatch:     *)
(*           * classifiable_u/covered_u -> classify_word_of_decode      *)
(*           * JAL/JALR -> classify_jal/jalr (target 2-aligned via C)   *)
(*           * BTYPE -> eval branch cond on g (decidable) ->            *)
(*             classify_btype_*_{taken,fall}                            *)
(*           * LOAD/STORE/AMO -> DATA-SIDE (step 6)                     *)
(*       - compressed 16-bit: cfetch_hit (c_fetch_mode 4-aligned or,    *)
(*         for 2-aligned va, 2-aligned branch); dispatch the C_* the    *)
(*         same way via the classify_c_* lemmas.                        *)
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
(* DONE so far: word_of_bytes4 / bytes_to_word4 (+ hword) -- the fetch- *)
(* word constructor. NEXT: open Section (Context CID + U + notations    *)
(* mirroring WpUserClassify:629), add the local Hcode_resident, prove   *)
(* produce_fetch: exec+A-set+aligned+canonical page facts ->            *)
(*   (∃ w, ufetch_hit va vpn ie w tlbvec) \/                            *)
(*   (∃ h, cfetch_hit va vpn ie h tlbvec)  (case on isRVC).             *)
(* ==================================================================== *)
