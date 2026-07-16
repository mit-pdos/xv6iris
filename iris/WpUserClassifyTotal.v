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
Require Import WpUserFull.
Require Import WpDecodeBridge.
Require Import UmodeEcall.
Require Import DecodeSetU.
Require Import WpUserDecodeWidth.
Require Import AlignBits.
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
  Local Notation ustep_mem_case := (WpUserFull.ustep_mem_case U).
  Local Notation ustep_fault_case := (WpUserFull.ustep_fault_case U).
  Local Notation data := (WpUserBase.data U).

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

  (* Fetch-fault producer 4: a 4-aligned, canonical, MAPPED page whose leaf
     PTE denies EXECUTE permission lands in [ustep_case] disjunct 45 (the
     instruction-fetch page fault).  [uw_check_denied] is the negation twin of
     [uw_check_ok]; at wiring, the uctx field [Hfetch_perm_total] supplies
     [uw_check_ok fetch ie \/ uw_check_denied fetch ie] for every mapped vpn. *)
  Lemma produce_noexec (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (vpn : mword 27) (i : uwalk_info) :
    spec !! vpn = Some i ->
    uw_check_denied (InstructionFetch tt) i ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hsome Hden Hal Hcanon Hvpn. unfold WpUserSteps.ustep_case.
    do 44 right. left. exists vpn, i. repeat split; assumption.
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

  (* Case-5 dispatch, STRENGTHENED: for an executable, A-set, 4-aligned page
     whose fetched instruction -- full 32-bit OR compressed 16-bit -- is
     classifiable, the fetch RETIRES into [ustep_case] outright.  This is
     [dispatch_full_page_classifiable] with the leftover [cfetch_hit] escape
     hatch discharged by the compressed classifier [classify_c_word_of_decode]
     (GAP2).  It composes produce_fetch_4aligned (isRVC split) with the two
     word/halfword classifiers, needs NO new arms, and is total over rd on
     both geometries (the compute disjuncts carry the total rd form; RVC rd=x0
     HINTs are outside [classifiable_c] by construction). *)
  Lemma dispatch_full_page
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
    (forall h : mword 16, cfetch_hit va vpn ie h tlbvec ->
       forall ii, decodable_c ii = true ->
         (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
         WpUserClassify.classifiable_c ii = true) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hsome Hchk Hupd Hpbmt Hval Hcanon Hvpn_def Hpaal Hres Hcl_u Hcl_c.
    destruct (produce_fetch_4aligned va vpn ie tlbvec
                Hsome Hchk Hupd Hpbmt Hval Hcanon Hvpn_def Hpaal Hres)
      as [[w Huf] | [h Hcf]].
    - exact (WpUserClassify.classify_word_of_decode U va ms_v g tlbvec vpn ie w
               Huf (Hcl_u w Huf)).
    - exact (WpUserClassify.classify_c_word_of_decode U va ms_v g tlbvec vpn ie h
               Hcf (Hcl_c h Hcf)).
  Qed.

  (* 4-ALIGNED CANONICAL page router (fetch-fault + classifiable-compute legs).
     Given va is 4-aligned and canonical with page number [vpn], and a "page
     verdict" for [vpn] -- one of {unmapped, execute-denied, A-update-needed,
     or (executable, A-set, PBMT-normal, resident, and every instruction in the
     page classifiable on both geometries)} -- the classification lands in
     [ustep_case].  The verdict is exactly what the uctx wf fields supply per
     mapped page.  This covers the fetch-fault outcomes and the compute/system
     retire; control-flow (JAL/JALR/BTYPE) and data (LOAD/STORE/AMO) are
     additional verdict legs routed by classify_* / the data side (follow-up).
     Non-canonical va is handled separately by [produce_noncanonical]. *)
  Lemma dispatch_4aligned_canonical
      (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (vpn : mword 27) :
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    ( spec !! vpn = None
      \/ (exists i, spec !! vpn = Some i /\ uw_check_denied (InstructionFetch tt) i)
      \/ (exists ie pte', spec !! vpn = Some ie /\
            uw_check_ok (InstructionFetch tt) ie /\
            update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = Some pte')
      \/ (exists ie, spec !! vpn = Some ie /\
            uw_check_ok (InstructionFetch tt) ie /\
            update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
            _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
            is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
            (forall j : nat, (j < 4)%nat ->
               exists b, code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some b) /\
            (forall w : mword 32, ufetch_hit va vpn ie w tlbvec ->
               forall ii, decodable_u ii = true ->
                 (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
                 classifiable_u ii = true) /\
            (forall h : mword 16, cfetch_hit va vpn ie h tlbvec ->
               forall ii, decodable_c ii = true ->
                 (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
                 WpUserClassify.classifiable_c ii = true)) ) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hal Hcanon Hvpn Hverdict.
    destruct Hverdict as
      [Hnone
      | [ [i [Hs Hden]]
      | [ [ie [pte' [Hs [Hok Hupd]]]]
      | [ie [Hs [Hok [Hupd [Hpbmt [Hpaal [Hres [Hcl_u Hcl_c]]]]]]]] ] ] ].
    - exact (produce_unmapped va ms_v g tlbvec vpn Hnone Hal Hcanon Hvpn).
    - exact (produce_noexec va ms_v g tlbvec vpn i Hs Hden Hal Hcanon Hvpn).
    - exact (produce_adfault va ms_v g tlbvec vpn ie pte' Hs Hok Hupd Hal Hcanon Hvpn).
    - exact (dispatch_full_page va ms_v g vpn ie tlbvec
               Hs Hok Hupd Hpbmt Hal Hcanon Hvpn Hpaal Hres Hcl_u Hcl_c).
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

  (* BTYPE routing leg for the 4-aligned dispatcher: a fetched, decoded
     conditional branch classifies either as fall-through (runtime condition
     FALSE) or as taken to a 4-aligned target (condition TRUE + target bit0=0,
     bit1=0).  Total over all six [bop].  The one uncovered runtime shape -- a
     TAKEN branch to a 2-aligned (compressed) target -- is a separate arm (the
     Zca jump-target generalization) and is simply not offered by the
     disjunctive hypothesis here. *)
  Lemma dispatch_4aligned_btype
      (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (imm : mword 13) (rs2 rs1 : mword 5) (op : bop) :
    ufetch_hit va vpn ie w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (BTYPE (imm, Regidx rs2, Regidx rs1, op), s0)) ->
    ( (match op with
       | BEQ  => eq_vec (g !!! Regidx rs1) (g !!! Regidx rs2) = false
       | BNE  => neq_vec (g !!! Regidx rs1) (g !!! Regidx rs2) = false
       | BLT  => zopz0zI_s (g !!! Regidx rs1) (g !!! Regidx rs2) = false
       | BGE  => zopz0zKzJ_s (g !!! Regidx rs1) (g !!! Regidx rs2) = false
       | BLTU => zopz0zI_u (g !!! Regidx rs1) (g !!! Regidx rs2) = false
       | BGEU => zopz0zKzJ_u (g !!! Regidx rs1) (g !!! Regidx rs2) = false
       end)
      \/ ((match op with
       | BEQ  => eq_vec (g !!! Regidx rs1) (g !!! Regidx rs2) = true
       | BNE  => neq_vec (g !!! Regidx rs1) (g !!! Regidx rs2) = true
       | BLT  => zopz0zI_s (g !!! Regidx rs1) (g !!! Regidx rs2) = true
       | BGE  => zopz0zKzJ_s (g !!! Regidx rs1) (g !!! Regidx rs2) = true
       | BLTU => zopz0zI_u (g !!! Regidx rs1) (g !!! Regidx rs2) = true
       | BGEU => zopz0zKzJ_u (g !!! Regidx rs1) (g !!! Regidx rs2) = true
       end)
       /\ eq_vec (access_vec_dec (add_vec va (sign_extend' 64 imm)) 0) ('b"0") = true
       /\ bit_to_bool (access_vec_dec (add_vec va (sign_extend' 64 imm)) 1) = false) ) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec [Hfall | [Htaken [H0 H1]]].
    - exact (classify_btype_fall_dispatch va ms_v g tlbvec vpn ie w imm rs2 rs1 op Hf Hdec Hfall).
    - exact (classify_btype_taken_dispatch va ms_v g tlbvec vpn ie w imm rs2 rs1 op Hf Hdec Htaken H0 H1).
  Qed.

  (* H4 FRAGMENT (fetch-fault + compute): the 4-aligned branch of
     [user_classify] for pages whose instructions are all compute/system
     (classifiable).  Derives [is_aligned_vaddr .. 4 = true] from the low-bit
     facts via [align4_of_low_bits], handles the NON-canonical pc itself
     ([produce_noncanonical]), and delegates the canonical page verdict
     (unmapped / execute-denied / A-update / classifiable-retire) to
     [dispatch_4aligned_canonical].  Control-flow (BTYPE/JAL/JALR) and data
     (LOAD/STORE) pages are additional verdict legs (dispatch_4aligned_btype,
     classify_jal/jalr, and the produce_mem / produce_fault producers); the
     full H4 unions all of them under the decode-family case-split. *)
  Lemma dispatch_4aligned_compute
      (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (vpn : mword 27) :
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    ( neq_vec (bits_of_virtaddr (Virtaddr va))
        (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = true
      \/ ( neq_vec (bits_of_virtaddr (Virtaddr va))
             (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false
           /\ ( spec !! vpn = None
                \/ (exists i, spec !! vpn = Some i /\ uw_check_denied (InstructionFetch tt) i)
                \/ (exists ie pte', spec !! vpn = Some ie /\
                      uw_check_ok (InstructionFetch tt) ie /\
                      update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = Some pte')
                \/ (exists ie, spec !! vpn = Some ie /\
                      uw_check_ok (InstructionFetch tt) ie /\
                      update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
                      _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
                      is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
                      (forall j : nat, (j < 4)%nat ->
                         exists b, code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some b) /\
                      (forall w : mword 32, ufetch_hit va vpn ie w tlbvec ->
                         forall ii, decodable_u ii = true ->
                           (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
                           classifiable_u ii = true) /\
                      (forall h : mword 16, cfetch_hit va vpn ie h tlbvec ->
                         forall ii, decodable_c ii = true ->
                           (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
                           WpUserClassify.classifiable_c ii = true)) ) ) ) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hb0 Hb1 Hvpn Hcase.
    assert (Hal : is_aligned_vaddr (Virtaddr va) 4 = true)
      by (apply align4_of_low_bits; assumption).
    destruct Hcase as [Hnc | [Hcanon Hverdict]].
    - exact (produce_noncanonical va ms_v g tlbvec Hal Hnc).
    - exact (dispatch_4aligned_canonical va ms_v g tlbvec vpn Hal Hcanon Hvpn Hverdict).
  Qed.

  (* TOP-LEVEL REDUCTION for [user_classify].  Splits the total classification
     over pc's low two bits and discharges the ODD-pc branch outright (it lands
     in [ustep_case] disjunct 51, the fetch-address-misaligned fault, which is
     just the pure fact [neq_vec (access_vec_dec va 0) 'b"0" = true]).  The two
     remaining branches -- 4-aligned (bit1=0) and 2-aligned (bit1=1) -- are
     left as obligations [H4]/[H2].  This is the skeleton of [user_classify]:
     once H4 and H2 are proven (even conditionally, e.g. under the aligned-data
     side hypothesis), [user_classify_from_branches H4 H2] IS the total
     classifier, and [wp_user_exec_full (user_step_holds_full ...)] turns it
     into the end-to-end "runs user code forever" theorem. *)
  Theorem user_classify_from_branches :
    (forall (va ms_v : mword 64) (g : gmap regidx (mword 64))
            (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
        upt_tlb_ok spec tlbvec ->
        _get_Mstatus_SXL ms_v = 'b"10" ->
        neq_vec (access_vec_dec va 0) ('b"0") = false ->
        neq_vec (access_vec_dec va 1) ('b"0") = false ->
        ustep_case va ms_v g tlbvec \/ ustep_mem_case va ms_v g tlbvec
        \/ ustep_fault_case va ms_v g tlbvec) ->
    (forall (va ms_v : mword 64) (g : gmap regidx (mword 64))
            (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
        upt_tlb_ok spec tlbvec ->
        _get_Mstatus_SXL ms_v = 'b"10" ->
        neq_vec (access_vec_dec va 0) ('b"0") = false ->
        neq_vec (access_vec_dec va 1) ('b"0") = true ->
        ustep_case va ms_v g tlbvec \/ ustep_mem_case va ms_v g tlbvec
        \/ ustep_fault_case va ms_v g tlbvec) ->
    forall (va ms_v : mword 64) (g : gmap regidx (mword 64))
           (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
      upt_tlb_ok spec tlbvec ->
      _get_Mstatus_SXL ms_v = 'b"10" ->
      ustep_case va ms_v g tlbvec \/ ustep_mem_case va ms_v g tlbvec
      \/ ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros H4 H2 va ms_v g tlbvec Hok HSXL.
    destruct (neq_vec (access_vec_dec va 0) ('b"0")) eqn:Hb0.
    - (* ODD pc: ustep_case disjunct 51 (fetch-address-misalign fault) *)
      left. unfold WpUserSteps.ustep_case.
      do 50 right. left. exact Hb0.
    - destruct (neq_vec (access_vec_dec va 1) ('b"0")) eqn:Hb1.
      + exact (H2 va ms_v g tlbvec Hok HSXL Hb0 Hb1).
      + exact (H4 va ms_v g tlbvec Hok HSXL Hb0 Hb1).
  Qed.

  (* ================================================================ *)
  (* DATA-SIDE success producers: one pure lemma per ustep_mem_case   *)
  (* disjunct.  Each routes a decoded, aligned LOAD/STORE (fetch OK,   *)
  (* data page mapped & permitted) into the matching width disjunct.  *)
  (* ================================================================ *)

  Lemma produce_mem_ld8 (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info) (imm : mword 12) (rs1 rd : mword 5) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, false, 8), s0)) ->
    uint rd <> 0 ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Load Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Load Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD)) 8 = true ->
    (forall j : nat, (j < 8)%nat -> pa_add (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) j ∈ data) ->
    ustep_mem_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_mem_case.
    left. exists vpn, ie, w, vpnD, ieD, imm, rs1, rd.
    repeat split; assumption.
  Qed.

  Lemma produce_mem_lw4 (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info) (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4), s0)) ->
    uint rd <> 0 ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Load Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Load Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD)) 4 = true ->
    (forall j : nat, (j < 4)%nat -> pa_add (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) j ∈ data) ->
    ustep_mem_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_mem_case.
    do 1 right; left. exists vpn, ie, w, vpnD, ieD, imm, rs1, rd, is_unsigned.
    repeat split; assumption.
  Qed.

  Lemma produce_mem_lh2 (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info) (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 2), s0)) ->
    uint rd <> 0 ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Load Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Load Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 2 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD)) 2 = true ->
    (forall j : nat, (j < 2)%nat -> pa_add (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) j ∈ data) ->
    ustep_mem_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_mem_case.
    do 2 right; left. exists vpn, ie, w, vpnD, ieD, imm, rs1, rd, is_unsigned.
    repeat split; assumption.
  Qed.

  Lemma produce_mem_lb1 (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info) (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1), s0)) ->
    uint rd <> 0 ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Load Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Load Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 1 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD)) 1 = true ->
    (forall j : nat, (j < 1)%nat -> pa_add (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) j ∈ data) ->
    ustep_mem_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_mem_case.
    do 3 right; left. exists vpn, ie, w, vpnD, ieD, imm, rs1, rd, is_unsigned.
    repeat split; assumption.
  Qed.

  Lemma produce_mem_sd8 (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info) (imm : mword 12) (rs2 rs1 : mword 5) :
    (uint (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) + 8 <= 18446744073709551616)%Z ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 8), s0)) ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Store Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Store Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD)) 8 = true ->
    (forall j : nat, (j < 8)%nat -> pa_add (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) j ∈ data) ->
    ustep_mem_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_mem_case.
    do 4 right; left. exists vpn, ie, w, vpnD, ieD, imm, rs2, rs1.
    repeat split; assumption.
  Qed.

  Lemma produce_mem_sw4 (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info) (imm : mword 12) (rs2 rs1 : mword 5) :
    (uint (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) + 4 <= 18446744073709551616)%Z ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 4), s0)) ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Store Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Store Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD)) 4 = true ->
    (forall j : nat, (j < 4)%nat -> pa_add (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) j ∈ data) ->
    ustep_mem_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_mem_case.
    do 5 right; left. exists vpn, ie, w, vpnD, ieD, imm, rs2, rs1.
    repeat split; assumption.
  Qed.

  Lemma produce_mem_sh2 (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info) (imm : mword 12) (rs2 rs1 : mword 5) :
    (uint (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) + 2 <= 18446744073709551616)%Z ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 2), s0)) ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Store Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Store Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 2 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD)) 2 = true ->
    (forall j : nat, (j < 2)%nat -> pa_add (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) j ∈ data) ->
    ustep_mem_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_mem_case.
    do 6 right; left. exists vpn, ie, w, vpnD, ieD, imm, rs2, rs1.
    repeat split; assumption.
  Qed.

  Lemma produce_mem_sb1 (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info) (imm : mword 12) (rs2 rs1 : mword 5) :
    (uint (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) + 1 <= 18446744073709551616)%Z ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 1), s0)) ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Store Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Store Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 1 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD)) 1 = true ->
    (forall j : nat, (j < 1)%nat -> pa_add (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) j ∈ data) ->
    ustep_mem_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_mem_case.
    do 7 right. exists vpn, ie, w, vpnD, ieD, imm, rs2, rs1.
    repeat split; assumption.
  Qed.


  (* ================================================================ *)
  (* DATA-FAULT producers: one pure lemma per load/store disjunct of  *)
  (* ustep_fault_case.  UNMAPPED (spec!!vpnD=None) disjuncts 0-7 and   *)
  (* DATA-NO-PERM (uw_check_denied) disjuncts 10-17.  Mirror the      *)
  (* produce_mem_* success producers above.                           *)
  (* ================================================================ *)

  Lemma produce_fault_ld8_unmapped (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 8), s0)) ->
    spec !! vpnD = None ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_fault_case.
    left. exists vpn, ie, w, vpnD, imm, rs1, rd, is_unsigned.
    repeat split; assumption.
  Qed.

  Lemma produce_fault_lw4_unmapped (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4), s0)) ->
    spec !! vpnD = None ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_fault_case.
    do 1 right; left. exists vpn, ie, w, vpnD, imm, rs1, rd, is_unsigned.
    repeat split; assumption.
  Qed.

  Lemma produce_fault_lh2_unmapped (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 2), s0)) ->
    spec !! vpnD = None ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 2 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_fault_case.
    do 2 right; left. exists vpn, ie, w, vpnD, imm, rs1, rd, is_unsigned.
    repeat split; assumption.
  Qed.

  Lemma produce_fault_lb1_unmapped (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1), s0)) ->
    spec !! vpnD = None ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 1 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_fault_case.
    do 3 right; left. exists vpn, ie, w, vpnD, imm, rs1, rd, is_unsigned.
    repeat split; assumption.
  Qed.

  Lemma produce_fault_sd8_unmapped (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (imm : mword 12) (rs2 rs1 : mword 5) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 8), s0)) ->
    spec !! vpnD = None ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_fault_case.
    do 4 right; left. exists vpn, ie, w, vpnD, imm, rs2, rs1.
    repeat split; assumption.
  Qed.

  Lemma produce_fault_sw4_unmapped (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (imm : mword 12) (rs2 rs1 : mword 5) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 4), s0)) ->
    spec !! vpnD = None ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_fault_case.
    do 5 right; left. exists vpn, ie, w, vpnD, imm, rs2, rs1.
    repeat split; assumption.
  Qed.

  Lemma produce_fault_sh2_unmapped (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (imm : mword 12) (rs2 rs1 : mword 5) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 2), s0)) ->
    spec !! vpnD = None ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 2 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_fault_case.
    do 6 right; left. exists vpn, ie, w, vpnD, imm, rs2, rs1.
    repeat split; assumption.
  Qed.

  Lemma produce_fault_sb1_unmapped (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (imm : mword 12) (rs2 rs1 : mword 5) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 1), s0)) ->
    spec !! vpnD = None ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 1 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_fault_case.
    do 7 right; left. exists vpn, ie, w, vpnD, imm, rs2, rs1.
    repeat split; assumption.
  Qed.

  Lemma produce_fault_lw4_noperm (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info) (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4), s0)) ->
    spec !! vpnD = Some ieD ->
    uw_check_denied (Load Data) ieD ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_fault_case.
    do 10 right; left. exists vpn, ie, w, vpnD, ieD, imm, rs1, rd, is_unsigned.
    repeat split; assumption.
  Qed.

  Lemma produce_fault_ld8_noperm (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info) (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 8), s0)) ->
    spec !! vpnD = Some ieD ->
    uw_check_denied (Load Data) ieD ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_fault_case.
    do 11 right; left. exists vpn, ie, w, vpnD, ieD, imm, rs1, rd, is_unsigned.
    repeat split; assumption.
  Qed.

  Lemma produce_fault_lh2_noperm (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info) (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 2), s0)) ->
    spec !! vpnD = Some ieD ->
    uw_check_denied (Load Data) ieD ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 2 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_fault_case.
    do 12 right; left. exists vpn, ie, w, vpnD, ieD, imm, rs1, rd, is_unsigned.
    repeat split; assumption.
  Qed.

  Lemma produce_fault_lb1_noperm (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info) (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1), s0)) ->
    spec !! vpnD = Some ieD ->
    uw_check_denied (Load Data) ieD ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 1 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_fault_case.
    do 13 right; left. exists vpn, ie, w, vpnD, ieD, imm, rs1, rd, is_unsigned.
    repeat split; assumption.
  Qed.

  Lemma produce_fault_sd8_noperm (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info) (imm : mword 12) (rs2 rs1 : mword 5) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 8), s0)) ->
    spec !! vpnD = Some ieD ->
    uw_check_denied (Store Data) ieD ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_fault_case.
    do 14 right; left. exists vpn, ie, w, vpnD, ieD, imm, rs2, rs1.
    repeat split; assumption.
  Qed.

  Lemma produce_fault_sw4_noperm (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info) (imm : mword 12) (rs2 rs1 : mword 5) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 4), s0)) ->
    spec !! vpnD = Some ieD ->
    uw_check_denied (Store Data) ieD ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_fault_case.
    do 15 right; left. exists vpn, ie, w, vpnD, ieD, imm, rs2, rs1.
    repeat split; assumption.
  Qed.

  Lemma produce_fault_sh2_noperm (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info) (imm : mword 12) (rs2 rs1 : mword 5) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 2), s0)) ->
    spec !! vpnD = Some ieD ->
    uw_check_denied (Store Data) ieD ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 2 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_fault_case.
    do 16 right; left. exists vpn, ie, w, vpnD, ieD, imm, rs2, rs1.
    repeat split; assumption.
  Qed.

  Lemma produce_fault_sb1_noperm (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info) (imm : mword 12) (rs2 rs1 : mword 5) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 1), s0)) ->
    spec !! vpnD = Some ieD ->
    uw_check_denied (Store Data) ieD ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 1 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros.
    unfold WpUserFull.ustep_fault_case.
    do 17 right; left. exists vpn, ie, w, vpnD, ieD, imm, rs2, rs1.
    repeat split; assumption.
  Qed.

  (* ================================================================ *)
  (* DATA-SIDE dispatcher for a decoded 4-byte LOAD.  Given the shared *)
  (* fetch-side facts (page mapped, executable, A-set, the 4 code      *)
  (* bytes present and decoding to [LOAD (imm, rs1, rd, is_unsigned,   *)
  (* 4)]) plus a 3-way verdict on the effective data address           *)
  (* eaF := g!!!rs1 + imm -- unmapped / mapped-but-denied / mapped-    *)
  (* permitted-and-aligned -- route to [ustep_fault_case] (first two)  *)
  (* or [ustep_mem_case] (third), composing the produce_* leaves.      *)
  (* This is the H4 data-side leg for LW/LWU; the exhaustiveness proof  *)
  (* supplies the verdict from the uctx data residence/perm fields.     *)
  (* ================================================================ *)
  Lemma dispatch_load4
      (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4), s0)) ->
    uint rd <> 0 ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ( spec !! vpnD = None
      \/ (exists ieD, spec !! vpnD = Some ieD /\ uw_check_denied (Load Data) ieD)
      \/ (exists ieD, spec !! vpnD = Some ieD /\
            uw_check_ok (Load Data) ieD /\
            update_PTE_Bits (uw_pte0 ieD) (Load Data) = None /\
            _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
            is_aligned_paddr (Physaddr (u_pa (upt_entry vpnD ieD)
              (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD)) 4 = true /\
            (forall j : nat, (j < 4)%nat ->
               pa_add (u_pa (upt_entry vpnD ieD)
                 (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) j ∈ data)) ) ->
    ustep_mem_case va ms_v g tlbvec \/ ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hrd
           HeaAl HeaCanon HvpnD Hverdict.
    destruct Hverdict as [Hnone | [ [ieD [HsD Hden]] | [ieD [HsD [HokD [HupdD [HpbmtD [HpaalD Hdres]]]]]] ] ].
    - (* unmapped data page -> load page-fault *)
      right. exact (produce_fault_lw4_unmapped va ms_v g tlbvec vpn ie w vpnD imm rs1 rd is_unsigned
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hnone HeaAl HeaCanon HvpnD).
    - (* mapped but load-denied -> load page-fault (no-perm) *)
      right. exact (produce_fault_lw4_noperm va ms_v g tlbvec vpn ie w vpnD ieD imm rs1 rd is_unsigned
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec HsD Hden HeaAl HeaCanon HvpnD).
    - (* mapped, permitted, aligned -> load success *)
      left. exact (produce_mem_lw4 va ms_v g tlbvec vpn ie w vpnD ieD imm rs1 rd is_unsigned
        Hs Hok Hupd Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hrd
        HsD HokD HupdD HpbmtD HeaAl HeaCanon HvpnD HpaalD Hdres).
  Qed.

  Lemma dispatch_load8
      (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (imm : mword 12) (rs1 rd : mword 5) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, false, 8), s0)) ->
    uint rd <> 0 ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ( spec !! vpnD = None
      \/ (exists ieD, spec !! vpnD = Some ieD /\ uw_check_denied (Load Data) ieD)
      \/ (exists ieD, spec !! vpnD = Some ieD /\
            uw_check_ok (Load Data) ieD /\
            update_PTE_Bits (uw_pte0 ieD) (Load Data) = None /\
            _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
            is_aligned_paddr (Physaddr (u_pa (upt_entry vpnD ieD)
              (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD)) 8 = true /\
            (forall j : nat, (j < 8)%nat ->
               pa_add (u_pa (upt_entry vpnD ieD)
                 (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) j ∈ data)) ) ->
    ustep_mem_case va ms_v g tlbvec \/ ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hrd
           HeaAl HeaCanon HvpnD Hverdict.
    destruct Hverdict as [Hnone | [ [ieD [HsD Hden]] | [ieD [HsD [HokD [HupdD [HpbmtD [HpaalD Hdres]]]]]] ] ].
    - right. exact (produce_fault_ld8_unmapped va ms_v g tlbvec vpn ie w vpnD imm rs1 rd false
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hnone HeaAl HeaCanon HvpnD).
    - right. exact (produce_fault_ld8_noperm va ms_v g tlbvec vpn ie w vpnD ieD imm rs1 rd false
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec HsD Hden HeaAl HeaCanon HvpnD).
    - left. exact (produce_mem_ld8 va ms_v g tlbvec vpn ie w vpnD ieD imm rs1 rd
        Hs Hok Hupd Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hrd
        HsD HokD HupdD HpbmtD HeaAl HeaCanon HvpnD HpaalD Hdres).
  Qed.

  Lemma dispatch_load2
      (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 2), s0)) ->
    uint rd <> 0 ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 2 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ( spec !! vpnD = None
      \/ (exists ieD, spec !! vpnD = Some ieD /\ uw_check_denied (Load Data) ieD)
      \/ (exists ieD, spec !! vpnD = Some ieD /\
            uw_check_ok (Load Data) ieD /\
            update_PTE_Bits (uw_pte0 ieD) (Load Data) = None /\
            _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
            is_aligned_paddr (Physaddr (u_pa (upt_entry vpnD ieD)
              (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD)) 2 = true /\
            (forall j : nat, (j < 2)%nat ->
               pa_add (u_pa (upt_entry vpnD ieD)
                 (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) j ∈ data)) ) ->
    ustep_mem_case va ms_v g tlbvec \/ ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hrd
           HeaAl HeaCanon HvpnD Hverdict.
    destruct Hverdict as [Hnone | [ [ieD [HsD Hden]] | [ieD [HsD [HokD [HupdD [HpbmtD [HpaalD Hdres]]]]]] ] ].
    - right. exact (produce_fault_lh2_unmapped va ms_v g tlbvec vpn ie w vpnD imm rs1 rd is_unsigned
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hnone HeaAl HeaCanon HvpnD).
    - right. exact (produce_fault_lh2_noperm va ms_v g tlbvec vpn ie w vpnD ieD imm rs1 rd is_unsigned
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec HsD Hden HeaAl HeaCanon HvpnD).
    - left. exact (produce_mem_lh2 va ms_v g tlbvec vpn ie w vpnD ieD imm rs1 rd is_unsigned
        Hs Hok Hupd Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hrd
        HsD HokD HupdD HpbmtD HeaAl HeaCanon HvpnD HpaalD Hdres).
  Qed.

  Lemma dispatch_load1
      (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1), s0)) ->
    uint rd <> 0 ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 1 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ( spec !! vpnD = None
      \/ (exists ieD, spec !! vpnD = Some ieD /\ uw_check_denied (Load Data) ieD)
      \/ (exists ieD, spec !! vpnD = Some ieD /\
            uw_check_ok (Load Data) ieD /\
            update_PTE_Bits (uw_pte0 ieD) (Load Data) = None /\
            _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
            is_aligned_paddr (Physaddr (u_pa (upt_entry vpnD ieD)
              (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD)) 1 = true /\
            (forall j : nat, (j < 1)%nat ->
               pa_add (u_pa (upt_entry vpnD ieD)
                 (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) j ∈ data)) ) ->
    ustep_mem_case va ms_v g tlbvec \/ ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hrd
           HeaAl HeaCanon HvpnD Hverdict.
    destruct Hverdict as [Hnone | [ [ieD [HsD Hden]] | [ieD [HsD [HokD [HupdD [HpbmtD [HpaalD Hdres]]]]]] ] ].
    - right. exact (produce_fault_lb1_unmapped va ms_v g tlbvec vpn ie w vpnD imm rs1 rd is_unsigned
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hnone HeaAl HeaCanon HvpnD).
    - right. exact (produce_fault_lb1_noperm va ms_v g tlbvec vpn ie w vpnD ieD imm rs1 rd is_unsigned
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec HsD Hden HeaAl HeaCanon HvpnD).
    - left. exact (produce_mem_lb1 va ms_v g tlbvec vpn ie w vpnD ieD imm rs1 rd is_unsigned
        Hs Hok Hupd Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hrd
        HsD HokD HupdD HpbmtD HeaAl HeaCanon HvpnD HpaalD Hdres).
  Qed.

  Lemma dispatch_store4
      (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (imm : mword 12) (rs2 rs1 : mword 5) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 4), s0)) ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ( spec !! vpnD = None
      \/ (exists ieD, spec !! vpnD = Some ieD /\ uw_check_denied (Store Data) ieD)
      \/ (exists ieD, spec !! vpnD = Some ieD /\
            uw_check_ok (Store Data) ieD /\
            update_PTE_Bits (uw_pte0 ieD) (Store Data) = None /\
            _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
            is_aligned_paddr (Physaddr (u_pa (upt_entry vpnD ieD)
              (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD)) 4 = true /\
            (uint (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) + 4 <= 18446744073709551616)%Z /\
            (forall j : nat, (j < 4)%nat ->
               pa_add (u_pa (upt_entry vpnD ieD)
                 (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) j ∈ data)) ) ->
    ustep_mem_case va ms_v g tlbvec \/ ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec
           HeaAl HeaCanon HvpnD Hverdict.
    destruct Hverdict as [Hnone | [ [ieD [HsD Hden]] | [ieD [HsD [HokD [HupdD [HpbmtD [HpaalD [Hnowrap Hdres]]]]]]] ] ].
    - right. exact (produce_fault_sw4_unmapped va ms_v g tlbvec vpn ie w vpnD imm rs2 rs1
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hnone HeaAl HeaCanon HvpnD).
    - right. exact (produce_fault_sw4_noperm va ms_v g tlbvec vpn ie w vpnD ieD imm rs2 rs1
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec HsD Hden HeaAl HeaCanon HvpnD).
    - left. exact (produce_mem_sw4 va ms_v g tlbvec vpn ie w vpnD ieD imm rs2 rs1 Hnowrap
        Hs Hok Hupd Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec
        HsD HokD HupdD HpbmtD HeaAl HeaCanon HvpnD HpaalD Hdres).
  Qed.

  Lemma dispatch_store8
      (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (imm : mword 12) (rs2 rs1 : mword 5) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 8), s0)) ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ( spec !! vpnD = None
      \/ (exists ieD, spec !! vpnD = Some ieD /\ uw_check_denied (Store Data) ieD)
      \/ (exists ieD, spec !! vpnD = Some ieD /\
            uw_check_ok (Store Data) ieD /\
            update_PTE_Bits (uw_pte0 ieD) (Store Data) = None /\
            _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
            is_aligned_paddr (Physaddr (u_pa (upt_entry vpnD ieD)
              (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD)) 8 = true /\
            (uint (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) + 8 <= 18446744073709551616)%Z /\
            (forall j : nat, (j < 8)%nat ->
               pa_add (u_pa (upt_entry vpnD ieD)
                 (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) j ∈ data)) ) ->
    ustep_mem_case va ms_v g tlbvec \/ ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec
           HeaAl HeaCanon HvpnD Hverdict.
    destruct Hverdict as [Hnone | [ [ieD [HsD Hden]] | [ieD [HsD [HokD [HupdD [HpbmtD [HpaalD [Hnowrap Hdres]]]]]]] ] ].
    - right. exact (produce_fault_sd8_unmapped va ms_v g tlbvec vpn ie w vpnD imm rs2 rs1
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hnone HeaAl HeaCanon HvpnD).
    - right. exact (produce_fault_sd8_noperm va ms_v g tlbvec vpn ie w vpnD ieD imm rs2 rs1
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec HsD Hden HeaAl HeaCanon HvpnD).
    - left. exact (produce_mem_sd8 va ms_v g tlbvec vpn ie w vpnD ieD imm rs2 rs1 Hnowrap
        Hs Hok Hupd Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec
        HsD HokD HupdD HpbmtD HeaAl HeaCanon HvpnD HpaalD Hdres).
  Qed.

  Lemma dispatch_store2
      (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (imm : mword 12) (rs2 rs1 : mword 5) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 2), s0)) ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 2 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ( spec !! vpnD = None
      \/ (exists ieD, spec !! vpnD = Some ieD /\ uw_check_denied (Store Data) ieD)
      \/ (exists ieD, spec !! vpnD = Some ieD /\
            uw_check_ok (Store Data) ieD /\
            update_PTE_Bits (uw_pte0 ieD) (Store Data) = None /\
            _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
            is_aligned_paddr (Physaddr (u_pa (upt_entry vpnD ieD)
              (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD)) 2 = true /\
            (uint (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) + 2 <= 18446744073709551616)%Z /\
            (forall j : nat, (j < 2)%nat ->
               pa_add (u_pa (upt_entry vpnD ieD)
                 (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) j ∈ data)) ) ->
    ustep_mem_case va ms_v g tlbvec \/ ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec
           HeaAl HeaCanon HvpnD Hverdict.
    destruct Hverdict as [Hnone | [ [ieD [HsD Hden]] | [ieD [HsD [HokD [HupdD [HpbmtD [HpaalD [Hnowrap Hdres]]]]]]] ] ].
    - right. exact (produce_fault_sh2_unmapped va ms_v g tlbvec vpn ie w vpnD imm rs2 rs1
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hnone HeaAl HeaCanon HvpnD).
    - right. exact (produce_fault_sh2_noperm va ms_v g tlbvec vpn ie w vpnD ieD imm rs2 rs1
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec HsD Hden HeaAl HeaCanon HvpnD).
    - left. exact (produce_mem_sh2 va ms_v g tlbvec vpn ie w vpnD ieD imm rs2 rs1 Hnowrap
        Hs Hok Hupd Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec
        HsD HokD HupdD HpbmtD HeaAl HeaCanon HvpnD HpaalD Hdres).
  Qed.

  Lemma dispatch_store1
      (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (imm : mword 12) (rs2 rs1 : mword 5) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 1), s0)) ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) 1 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ( spec !! vpnD = None
      \/ (exists ieD, spec !! vpnD = Some ieD /\ uw_check_denied (Store Data) ieD)
      \/ (exists ieD, spec !! vpnD = Some ieD /\
            uw_check_ok (Store Data) ieD /\
            update_PTE_Bits (uw_pte0 ieD) (Store Data) = None /\
            _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
            is_aligned_paddr (Physaddr (u_pa (upt_entry vpnD ieD)
              (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD)) 1 = true /\
            (uint (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) + 1 <= 18446744073709551616)%Z /\
            (forall j : nat, (j < 1)%nat ->
               pa_add (u_pa (upt_entry vpnD ieD)
                 (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) j ∈ data)) ) ->
    ustep_mem_case va ms_v g tlbvec \/ ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec
           HeaAl HeaCanon HvpnD Hverdict.
    destruct Hverdict as [Hnone | [ [ieD [HsD Hden]] | [ieD [HsD [HokD [HupdD [HpbmtD [HpaalD [Hnowrap Hdres]]]]]]] ] ].
    - right. exact (produce_fault_sb1_unmapped va ms_v g tlbvec vpn ie w vpnD imm rs2 rs1
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hnone HeaAl HeaCanon HvpnD).
    - right. exact (produce_fault_sb1_noperm va ms_v g tlbvec vpn ie w vpnD ieD imm rs2 rs1
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec HsD Hden HeaAl HeaCanon HvpnD).
    - left. exact (produce_mem_sb1 va ms_v g tlbvec vpn ie w vpnD ieD imm rs2 rs1 Hnowrap
        Hs Hok Hupd Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec
        HsD HokD HupdD HpbmtD HeaAl HeaCanon HvpnD HpaalD Hdres).
  Qed.

  (* ================================================================ *)
  (* WIDTH-ROUTING legs: a decoded LOAD/STORE has a SYMBOLIC width     *)
  (* field (word_width := Z); load_width_cases/store_width_cases       *)
  (* (WpUserDecodeWidth) pin it to {1,2,4,8}, so we case-split and     *)
  (* route to the matching per-width dispatcher.  These give the       *)
  (* exhaustiveness proof ONE call per decoded LOAD/STORE instead of a *)
  (* hand-rolled width split.  The LOAD leg takes a deferred           *)
  (* [W = 8 -> is_unsigned = false] hypothesis: the width-8 UNSIGNED   *)
  (* encoding (LDU) decodes to LOAD(_,_,_,true,8) and is illegal at    *)
  (* EXECUTE (not decode), so it is NOT a data-memory case -- the      *)
  (* exhaustiveness routes that (rare) case to the illegal path and    *)
  (* never calls this leg with W=8/is_unsigned=true.                   *)
  (* ================================================================ *)
  Lemma dispatch_load_word
      (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) (W : Z) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, W), s0)) ->
    uint rd <> 0 ->
    (W = 8 -> is_unsigned = false) ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) W = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ( spec !! vpnD = None
      \/ (exists ieD, spec !! vpnD = Some ieD /\ uw_check_denied (Load Data) ieD)
      \/ (exists ieD, spec !! vpnD = Some ieD /\
            uw_check_ok (Load Data) ieD /\
            update_PTE_Bits (uw_pte0 ieD) (Load Data) = None /\
            _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
            is_aligned_paddr (Physaddr (u_pa (upt_entry vpnD ieD)
              (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD)) W = true /\
            (forall j : nat, (j < Z.to_nat W)%nat ->
               pa_add (u_pa (upt_entry vpnD ieD)
                 (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) j ∈ data)) ) ->
    ustep_mem_case va ms_v g tlbvec \/ ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hrd Hisu8
           HeaAl HeaCanon HvpnD Hverdict.
    destruct (load_width_cases w imm rs1 rd is_unsigned W Hdec) as [HW | [HW | [HW | HW]]].
    - subst W. exact (dispatch_load1 va ms_v g tlbvec vpn ie w vpnD imm rs1 rd is_unsigned
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hrd HeaAl HeaCanon HvpnD Hverdict).
    - subst W. exact (dispatch_load2 va ms_v g tlbvec vpn ie w vpnD imm rs1 rd is_unsigned
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hrd HeaAl HeaCanon HvpnD Hverdict).
    - subst W. exact (dispatch_load4 va ms_v g tlbvec vpn ie w vpnD imm rs1 rd is_unsigned
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hrd HeaAl HeaCanon HvpnD Hverdict).
    - subst W. specialize (Hisu8 eq_refl). subst is_unsigned.
      exact (dispatch_load8 va ms_v g tlbvec vpn ie w vpnD imm rs1 rd
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec Hrd HeaAl HeaCanon HvpnD Hverdict).
  Qed.

  Lemma dispatch_store_word
      (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (imm : mword 12) (rs2 rs1 : mword 5) (W : Z) :
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, W), s0)) ->
    is_aligned_vaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))) W = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm))))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    ( spec !! vpnD = None
      \/ (exists ieD, spec !! vpnD = Some ieD /\ uw_check_denied (Store Data) ieD)
      \/ (exists ieD, spec !! vpnD = Some ieD /\
            uw_check_ok (Store Data) ieD /\
            update_PTE_Bits (uw_pte0 ieD) (Store Data) = None /\
            _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
            is_aligned_paddr (Physaddr (u_pa (upt_entry vpnD ieD)
              (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD)) W = true /\
            (uint (u_pa (upt_entry vpnD ieD) (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) + W <= 18446744073709551616)%Z /\
            (forall j : nat, (j < Z.to_nat W)%nat ->
               pa_add (u_pa (upt_entry vpnD ieD)
                 (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)) vpnD) j ∈ data)) ) ->
    ustep_mem_case va ms_v g tlbvec \/ ustep_fault_case va ms_v g tlbvec.
  Proof.
    intros Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec
           HeaAl HeaCanon HvpnD Hverdict.
    destruct (store_width_cases w imm rs2 rs1 W Hdec) as [HW | [HW | [HW | HW]]]; subst W.
    - exact (dispatch_store1 va ms_v g tlbvec vpn ie w vpnD imm rs2 rs1
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec HeaAl HeaCanon HvpnD Hverdict).
    - exact (dispatch_store2 va ms_v g tlbvec vpn ie w vpnD imm rs2 rs1
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec HeaAl HeaCanon HvpnD Hverdict).
    - exact (dispatch_store4 va ms_v g tlbvec vpn ie w vpnD imm rs2 rs1
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec HeaAl HeaCanon HvpnD Hverdict).
    - exact (dispatch_store8 va ms_v g tlbvec vpn ie w vpnD imm rs2 rs1
        Hs Hok Hupd Hpbmt Hres Hmprv Hmxr Hval Hcanon Hvpn Hpaal Hnrvc Hdec HeaAl HeaCanon HvpnD Hverdict).
  Qed.


End Total.

(* ==================================================================== *)
(* SESSION 3 PROGRESS 2026-07-16 (landed on main, all green, 0 admits): *)
(*  - DATA-SIDE DISPATCHERS COMPLETE: dispatch_load4 (this file) +       *)
(*    dispatch_load8/2/1 + dispatch_store4/8/2/1.  Each composes its     *)
(*    three produce_* leaves (mem / fault-unmapped / fault-noperm) under *)
(*    a 3-way effective-address verdict, concluding                      *)
(*    ustep_mem_case \/ ustep_fault_case.  These are the per-width H4    *)
(*    data-side legs; the exhaustiveness proof supplies the verdict from *)
(*    the uctx data residence/perm wf fields.                            *)
(*  - DECODE WIDTH TOTALITY: WpUserDecodeWidth.v (new file, ordered      *)
(*    before this one; axiom-CLEAN) proves load_width_cases /            *)
(*    store_width_cases : a decoded LOAD/STORE width W in {1,2,4,8},     *)
(*    via a goodbP leaf predicate Pwidth + goodbP_exec extraction.  This *)
(*    lets the exhaustiveness case-split a decoded LOAD/STORE (whose     *)
(*    word_width := Z field is SYMBOLIC) into the 4 concrete-width       *)
(*    dispatchers.                                                       *)
(*  - MODEL FINDING (routing consequence): the width-8 UNSIGNED load     *)
(*    encoding (funct3=111, "LDU") is NOT rejected at DECODE -- it       *)
(*    decodes to LOAD(_,_,_,true,8) and is rejected at EXECUTE (illegal).*)
(*    (Confirmed: a goodbP leaf predicate negb(isu && W=?8) does NOT     *)
(*    close -- the W=8 LOAD leaf has symbolic isu.)  So "W=8 => signed"  *)
(*    is FALSE at the decode level.  CONSEQUENCE for the exhaustiveness: *)
(*    a decoded W=8 LOAD with isu=true must route to the illegal/fault   *)
(*    path (execute rejects it), NOT to the signed produce_mem_ld8; only *)
(*    isu=false W=8 LOADs are ld8 successes.  The isu=true W=8 case needs *)
(*    routing to ustep_case's illegal disjunct (execute = Illegal), like *)
(*    the privileged-illegal ops -- verify the execute-illegal fact for  *)
(*    LDU exists / build it as a classify leaf.                          *)
(*                                                                      *)
(* NEXT ASSEMBLY STEP (dispatch_fetched_word): case-split the decoded ii *)
(* over decodable_u (54 ctors) and route:                               *)
(*   classifiable_u -> classify_word_of_decode (ustep_case)             *)
(*   BTYPE -> classify_btype_{fall,taken}_dispatch (eval cond on g)     *)
(*   JAL/JALR rd<>0 -> classify_jal/jalr ; rd=0 -> no-link arms 47-50   *)
(*   LOAD  -> load_width_cases; per width dispatch_load{W} (+ the LDU    *)
(*            isu=true/W=8 -> illegal caveat above)                      *)
(*   STORE -> store_width_cases; per width dispatch_store{W}            *)
(*   AMO   -> ustep_mem_case success (task #25 -- NOT yet wired)        *)
(*   LOADRES/STORECON -> LR/SC fault arms (exist)                      *)
(*   ECALL -> byte-keyed disjunct (subtlety); WRS -> NO arm (gap!)     *)
(* Requires Require Import WpUserDecodeWidth in this file, plus the     *)
(* uctx data-verdict wf field (local Section hyp first).  BLOCKED       *)
(* beyond H4: H2 (ARM 2 split-fetch engine), arm C (misaligned L/S),    *)
(* AMO-success wiring, and the WRS gap (see below).                     *)
(* ==================================================================== *)

(* ==================================================================== *)
(* SESSION 3 (cont.) -- LOAD/STORE width-routing legs DONE + WRS scoped. *)
(*  - dispatch_load_word / dispatch_store_word (this file): route a      *)
(*    decoded LOAD/STORE (symbolic word_width := Z) via                  *)
(*    load_width_cases / store_width_cases into the concrete-width       *)
(*    dispatch_load{1,2,4,8} / dispatch_store{1,2,4,8}.  ONE call per     *)
(*    decoded L/S for the exhaustiveness.  The verdict residence bound   *)
(*    is stated as (j < Z.to_nat W)%nat and unifies with the per-width   *)
(*    dispatchers' literal bounds by conversion after subst.             *)
(*  - WRS GAP is REAL and NOT a no-op (checked rv64d.v):                 *)
(*      execute_WRS _ = Enter_Wait (WAIT_WRS_STO / WAIT_WRS_NTO);        *)
(*      wait_is_nop (WAIT_WRS_STO/NTO) = FALSE (per wait_is_nop def).    *)
(*    The step handler (rv64d.v:41779) on Enter_Wait with ~wait_is_nop   *)
(*    WRITES hart_state := HART_WAITING, then the post-step match        *)
(*    (HART_WAITING _ => returnM true) SUCCEEDS -- so a WRS SAFELY puts  *)
(*    the hart into a wait state (the Loop keeps stepping, hart stays    *)
(*    waiting, each step a successful no-op).  So WRS is neither a        *)
(*    retire (ustep_case), a mem access, nor a fault -- NONE of the      *)
(*    three case Props cover it, so user_classify is NOT TOTAL without   *)
(*    a WRS arm.  BUILDABLE (not a framework overhaul): a new arm        *)
(*    [ustep_wrs] that steps WRS -> HART_WAITING and proves WP Loop from *)
(*    a waiting hart (a Lob loop on the wait state -- the waiting step   *)
(*    returns true forever, so it is SAFE), plus a ustep_case tail       *)
(*    disjunct.  Same shape for WFI (also Enter_Wait, U-mode: gated by   *)
(*    plat_wfi_available_to_usermode -> WAIT_WFI or trap).  This wait-   *)
(*    state arm family is a distinct milestone (est. a focused session). *)
(* ==================================================================== *)

(* ==================================================================== *)
(* SESSION 2 PROGRESS 2026-07-16 (landed on main, all green, 0 admits): *)
(*  - BUILD ENV: builds only under opam switch /shared/xv6rocq (Rocq    *)
(*    9.0.1); a fresh shell defaults to /root/.opam/xv6iris (9.1.1, no   *)
(*    stdpp bitvector / no SailStdpp).  ALWAYS eval $(opam env --switch= *)
(*    /shared/xv6rocq) first (also in every build subagent).             *)
(*  - CHAIN LINK DONE: WpUserFull.wp_user_exec_full -- the end-to-end    *)
(*    "WP Loop forever" at FULL (mem+fault) coverage; takes the 3-way    *)
(*    disjunction and forwards through the proven user_step_holds_full.  *)
(*    A total [user_classify] plugs straight in.  This is the target.    *)
(*  - ARM 2 fetch engine DONE: exec_fetch_F_Base_2_U_gen (UmodeFetchC)   *)
(*    the 2-aligned 32-bit split-fetch MODEL lemma; and                  *)
(*    WpUserSplitFetch.wp_instr_u_split -- the additive engine (two TLB  *)
(*    hits, continuation byte-identical to wp_instr_u_hit so retire arms *)
(*    ride it unchanged).  Key fact: a TLB-hit translateAddr is state-   *)
(*    preserving, so both halfword translates thread s->s->s.            *)
(*  - ARM 2 wiring PART C DONE: WpUserSplitCompute.ustep_u_split_compute *)
(*    + ustep_case disjunct 52 (2-aligned ITYPE compute retire, all iop; *)
(*    fetch-HIT-based since there is no split-fetch-miss engine).        *)
(*    ustep_case_sound extended; user_step_holds_full needed NO edit (it *)
(*    forwards ustep_case wholesale to ustep_case_sound).                *)
(*  - GAP2 compressed dispatcher DONE: WpUserClassify.classifiable_c +   *)
(*    classify_c_word_of_decode (mirror of classify_word_of_decode via   *)
(*    decode_total_c_set); covers compressed compute + trap/no-op, with  *)
(*    the SAME exclusions as classifiable_u (rd=x0 HINTs baked out via   *)
(*    negb(uint rd =? 0); g-dependent control flow and standalone L/S    *)
(*    excluded).                                                          *)
(*                                                                      *)
(* FRONTIER toward user_classify (next session, focused synthesis):      *)
(*  (1) THE va-CASE-TREE SYNTHESIS itself (the hard capstone): develop   *)
(*      against LOCAL Section hypotheses for the uctx wf fields          *)
(*      (Hcode_resident, Hfetch_perm_total, data residence/perm), then   *)
(*      bake into uctx last.  Compose the producers/dispatchers          *)
(*      (produce_*, dispatch_full_page_classifiable, classify_btype_*,   *)
(*      and now classify_c_word_of_decode) under a split on va's low     *)
(*      bits + decode.  DESIGN QUESTION to resolve here: whether a       *)
(*      SINGLE generic [exec (execute ii) (set nextPC va+4) =            *)
(*      RETIRE_SUCCESS] disjunct (wp_instr_u_split's continuation is     *)
(*      generic over ii) can replace the per-family 2-aligned disjuncts  *)
(*      -- if so, disjunct 52 generalizes and the other compute          *)
(*      families need NO extra disjuncts.  Decide before cloning more    *)
(*      per-family 2-aligned arms (avoid speculative duplication).       *)
(*  (2) PART D: high-half fetch fault (2-aligned, va+2 page unmapped/    *)
(*      noexec) -- fault-tower clone, new ustep_case disjunct.           *)
(*  (3) DATA side: route LOAD/STORE (aligned) to ustep_mem_case, and     *)
(*      atomics SUCCESS into ustep_mem_case (task #25); the 21-way       *)
(*      ustep_fault_case already covers data-no-perm + LR/SC/AMO         *)
(*      misalign faults.                                                 *)
(*  (4) INTERIM: assemble user_classify with the data-side side-hyp      *)
(*      [is_aligned_vaddr eaF W = true]; feed wp_user_exec_full for a    *)
(*      real (aligned-data) end-to-end theorem; arm C removes it last.   *)
(* ==================================================================== *)

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
(*     "mapped-but-not-executable" fetch-fault arm (BUILDABLE, low-med). *)
(*     SCOPED 2026-07-16 (agent): upt_fault_wf does NOT need changing    *)
(*     (the noexec case is spec!!vpn=Some i, orthogonal to the None-only *)
(*     invariant; slot reads come from upt_spec via upt_walk_read_ptes). *)
(*     Develop against a LOCAL premise [uw_check_denied (InstructionFetch*)
(*     tt) i] (the PTE_Check_Failure/PTE_No_Permission twin of           *)
(*     uw_check_ok, UptInv.v:80).  Lemma chain (all CLONES of proven     *)
(*     unmapped/adfault code; leaf exec_rec_walk_leaf_noperm CommonWalk. *)
(*     v:475 already exists):  upt_noexec_walk_fault (clone upt_unmapped_ *)
(*     walk_fault UptInv.v:446) ; exec_translate_TLB_hit_u_noperm (novel *)
(*     bit, clone UmodeFetchFault.v:77) ; exec_translate_walk_user_noperm*)
(*     (clone WpUserFetch.v:54) ; generalize exec_translateAddr_fetch_u_ *)
(*     needs_update_of_translate over the PTW_Error ; upt_translateAddr_ *)
(*     fetch_noexec (clone upt_translateAddr_fetch_adfault WpUserFetch.v: *)
(*     589 -- combined hit+walk, since a mapped vpn may be TLB-cached) ;  *)
(*     ustep_noexec_fetch_fault (clone ustep_fetch_adfault_u WpUserFetch. *)
(*     v:668; trap tower is byte-identical E_Fetch_Page_Fault).  At       *)
(*     WIRING add uctx field Hfetch_perm_total: forall vpn i, spec!!vpn=  *)
(*     Some i -> uw_check_ok fetch i \/ uw_check_denied fetch i (model-   *)
(*     true; could later be proven from uw_wf).  Needed: a program may    *)
(*     jump into a readable data page.                                    *)
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
(*      classifiable dispatcher (classifiable_c + classify_c_word).      *)
(*      Compressed jump/branch status:                                   *)
(*        - C_BEQZ/C_BNEZ: fall+taken already covered by classify_c_     *)
(*          beqz/bnez_{fall,taken} (taken = 4-aligned; misaligned = arm). *)
(*        - C_JALR: classify_c_jalr covers rd<>0 + 4-aligned target.     *)
(*        - C_J, C_JR: NO leaves exist -- MISSING arms (compressed        *)
(*          unconditional jump, and rd=x0 register jump).  Build these.   *)
(*   C. The MISSING fault arms: mapped-non-exec fetch, misaligned       *)
(*      fetch/jump-target, misaligned/no-perm data, data-TLB-miss.      *)
(*      Each = new ustep_case/mem/fault disjunct + exec-side soundness   *)
(*      arm (forces ~30-file rebuild; batch these).                     *)
(*   D. uctx wf fields (above) + the top-level va case tree tying it     *)
(*      all together into [user_classify], fed to user_step_holds_full. *)
(* ==================================================================== *)

(* ==================================================================== *)
(* SCOPING RESULTS 2026-07-16 (three parallel agents; model-grounded).  *)
(* Full plans with file:line in the session; synthesis below.           *)
(*                                                                      *)
(* MODEL FACTS that reshape the plan:                                   *)
(*  * plat_misaligned_access (rv64d.v:12712) = {load_store:=None;        *)
(*    lrsc:=AccessFault; amo:=AccessFault}.  So a misaligned REGULAR     *)
(*    load/store is NOT a fault -- the model SPLITS it (split_misaligned)*)
(*    and each piece translates separately (success, or per-piece PF).   *)
(*    Do NOT add a "misaligned regular L/S fault" disjunct -- UNSOUND.    *)
(*    Only LR/SC (misalign -> access fault) and AMO (execute_AMO self-   *)
(*    checks alignment, rv64d.v:40367 -> E_SAMO_Access_Fault) fault.      *)
(*  * Misaligned FETCH/jump/branch: with Zca enabled only an ODD target  *)
(*    faults, and odd targets are UNREACHABLE (imm encodes bit0=0; JALR  *)
(*    force-clears bit0).  No misaligned-fetch fault arm.  The real gap   *)
(*    is a RETIRING generalization (exec_jump_to_zca, drop bit1=false)    *)
(*    so taken jumps/branches to 2-aligned COMPRESSED targets classify.   *)
(*  * DATA-TLB-MISS is ALREADY DONE: success path via wp_instr_u_data    *)
(*    walk-fill; unmapped-PF via state-abstract upt_translateAddr_load_  *)
(*    unmapped.  No new data-miss arm needed.                            *)
(*                                                                      *)
(* BUILDABLE ARM FAMILIES (all clones; local uw_check_denied premise;    *)
(* NOT yet wired into the shared Prop defs):                            *)
(*  ARM 1  fetch-noexec PF  -> new ustep_case disjunct; clones of        *)
(*         upt_unmapped_walk_fault / upt_translateAddr_fetch_adfault /    *)
(*         ustep_fetch_adfault_u; novel bit = exec_translate_TLB_hit_u_   *)
(*         noperm.  uctx field Hfetch_perm_total at wiring.               *)
(*  ARM A  data-no-perm PF  -> 8 new ustep_fault_case disjuncts; clones   *)
(*         of upt_unmapped_walk_fault (mapped leaf, exec_rec_walk_leaf_    *)
(*         noperm CommonWalk.v:475) + upt_translateAddr_load_unmapped +   *)
(*         ustep_load_pf_4_u.  NO invariant change (upt_spec owns mapped  *)
(*         slots).  Reuses generic exec_translateAddr_load_walk_u_pf.     *)
(*  ARM B  LR/SC/AMO misalign access-fault -> 3 new ustep_fault_case      *)
(*         disjuncts; clones of ustep_lr/sc_fault_u with SHORTER towers   *)
(*         (alignment gate, no translate).  AMO tower trivial.            *)
(*  GAP1   rd=0 RVC HINT -> ONE new ustep_case disjunct (ExecuteAs base   *)
(*         -> state-preserving RETIRE) + ONE generic arm ustep_c_execas_  *)
(*         nop (clone ustep_c_nop, swap wp_instr_c_hit_direct -> _hit).   *)
(*         Only 7 ctors reach rd=x0: C_ADDI C_LI C_SLLI C_MV C_ADD        *)
(*         C_ADDIW C_LUI.  Needs _rd0 base-retire exec facts (ITYPE/      *)
(*         SHIFTIOP/UTYPE _rd0 exist; build RTYPE/RTYPEW/MUL _rd0).        *)
(*  GAP2   classifiable_c (26 compute/system ctors) + classify_c_word +   *)
(*         classify_c_word_of_decode (mirror classify_word etc).         *)
(*         legs buildable NOW off existing classify_c_* leaves; 7 full-rd *)
(*         legs DEPEND on GAP1's disjunct.                                *)
(*  GAP3   C_J / C_JR (rd=x0 jumps, no home even at base) -> 2 base       *)
(*         (+2 RVC) disjuncts + arms + conditional leaves; clones of      *)
(*         ustep_jal/jalr minus the reg_update link.  exec_execute_JALR_  *)
(*         ret exists (JR); build exec_execute_JAL_rd0 (J).               *)
(*  ARM C  misaligned REGULAR L/S split -> HARD, no template (multi-piece *)
(*         untilMT loop tower + multi-window success disjunct).  Separate *)
(*         milestone, schedule LAST.                                      *)
(*                                                                      *)
(* WIRING (serial, orchestrator): batch ARM 1 + GAP1 + GAP3 into ONE     *)
(* ustep_case def edit; batch ARM A + ARM B into ONE ustep_fault_case    *)
(* edit; add uctx fields (Hfetch_perm_total) last; each def edit forces   *)
(* the dependency-closure rebuild.  Also wire AMO/LR/SC SUCCESS into      *)
(* ustep_mem_case (currently only 8 L/S disjuncts).                       *)
(* ==================================================================== *)

(* ==================================================================== *)
(* ENDGAME (interface pinned 2026-07-16).  The unconditional theorem =   *)
(* prove [user_classify] then plumb it through two ALREADY-PROVEN steps: *)
(*   user_step_holds_full (WpUserFull.v:636): takes the FULL disjunction *)
(*     Hfull : forall va ms_v g tlbvec, upt_tlb_ok spec tlbvec ->        *)
(*       SXL='b"10" -> ustep_case \/ ustep_mem_case \/ ustep_fault_case, *)
(*     and discharges every disjunct (ustep_case via ustep_case_sound;   *)
(*     mem/fault via the frame dispatchers).  Already Qed.               *)
(*   wp_user_exec (WpUserBase.v:232): user_step_obligation -> end-to-end *)
(*     WP (Loop) forever from user_frame.                                *)
(* So TWO deliverables remain:                                           *)
(*   (1) user_classify -- the TOTAL case tree (this file), the sole hard *)
(*       remaining lemma; needs every arm wired as a disjunct + the uctx *)
(*       wf fields.  Requires a riscvGS-free statement is IMPOSSIBLE for  *)
(*       the mem/fault disjuncts?  NO -- ustep_mem_case/ustep_fault_case *)
(*       are PURE Props (WpUserFull.v:87/351), so user_classify is a pure *)
(*       Prop lemma, provable in the current (pure) section here.        *)
(*   (2) wp_user_exec_full -- trivial: clone wp_user_exec_v1 (WpUserSteps *)
(*       .v:1803) but call user_step_holds_full (full disjunction) not   *)
(*       user_step_holds (ustep_case only).  Needs a riscvGS section.    *)
(* NOTE wp_user_exec_v1 takes ONLY ustep_case, so it is NOT the total    *)
(* theorem -- it cannot cover data loads/stores.  The unconditional      *)
(* theorem is the _full variant.                                         *)
(* ==================================================================== *)

(* ==================================================================== *)
(* user_classify SCOPING 2026-07-16: va is UNCONSTRAINED.               *)
(* user_frame (WpUserBase.v:171) pins only [pc_is va] -- va is fully     *)
(* existential, NO alignment invariant.  user_step_holds_full's Hfull   *)
(* quantifies forall va.  So user_classify must be TOTAL over arbitrary  *)
(* va.  Case-split on va's low two bits:                                 *)
(*   * bit0=1 (ODD va): the model's fetch (rv64d.v ~41373) gates         *)
(*     E_Fetch_Addr_Align on [target[0]<>0 OR (target[1]<>0 AND ~Zca)];  *)
(*     odd va => target[0]<>0 => a DELIVERABLE E_Fetch_Addr_Align fault  *)
(*     (NOT the stuck jump_to assert -- that is a different path).       *)
(*     NEEDS a new arm ustep_fetch_misalign (clone the noexec/adfault    *)
(*     fetch-fault tower, cause E_Fetch_Addr_Align, gate on odd va) +    *)
(*     a ustep_case tail disjunct.  Tractable (fault-tower clone).       *)
(*   * bit0=0, bit1=1 (2-ALIGNED not 4): fetch reads the low halfword;   *)
(*     if isRVC -> cfetch_hit via c_fetch_mode's 2-aligned branch        *)
(*     (COVERED, WpUserSteps.v:161-166 RVC disjuncts).  If NOT isRVC ->  *)
(*     a full 32-bit instruction spanning two halfword reads at va/va+2  *)
(*     (possibly cross-page): ufetch_hit requires is_aligned_vaddr va 4  *)
(*     = true, so this is UNCOVERED.  NEEDS a new 2-aligned-full-word    *)
(*     fetch arm (novel: two-halfword non-atomic fetch path, Ziccif=0).  *)
(*     HARDER -- new fetch tower.  This case IS reachable (pc advances   *)
(*     by 2 after a compressed instruction, then a full-word follows).   *)
(*   * bit0=0, bit1=0 (4-ALIGNED): fully covered by the 50-way ustep_    *)
(*     case (fetch faults 1-3/45, ecall 4, compute/branch/jump 5-44,     *)
(*     RVC-HINT 46, no-link jumps 47-50) + the producers/dispatchers     *)
(*     above.                                                            *)
(* => user_classify is blocked on TWO more arms: ustep_fetch_misalign    *)
(*    (odd va, easy) and 2-aligned-full-word-fetch (harder).  Build      *)
(*    both, wire as ustep_case tail disjuncts, THEN assemble the va      *)
(*    case tree.  ALSO still needed for the DATA side of the tree:       *)
(*    routing LOAD/STORE/AMO to ustep_mem_case (success) vs the wired    *)
(*    fault disjuncts, which needs the data residence/perm uctx facts    *)
(*    (local hypotheses first) and the misaligned-regular-L/S split      *)
(*    (arm C, deferred).                                                 *)
(* ==================================================================== *)

(* ==================================================================== *)
(* TWO-ARMS SCOPING 2026-07-16 (agent, citation-backed).                *)
(* Model: non-RVFI fetch tt (rv64d.v:41457, else :41462).  Zca on =>    *)
(* w__7 = (PC[0]<>0); if true -> F_Error(E_Fetch_Addr_Align,PC) at      *)
(* :41480-82 BEFORE any translate.  Else Ziccif branch: 4-aligned =>     *)
(* single fetch_bytes; 2-aligned (:41504-31) => fetch_bytes PC 2 -> ilo, *)
(* if isRVC F_RVC else fetch_bytes (PC+2) 2 -> ihi, F_Base(concat ihi    *)
(* ilo).  fetch_bytes (:41427/:41439) translates its OWN granule_start,  *)
(* so the two halves translate INDEPENDENTLY (high half faults alone,    *)
(* reported at PC+2, :41523).                                            *)
(*                                                                      *)
(* ARM 1 ustep_fetch_misalign (odd va) -- LOW, being built.             *)
(*   model: exec_fetch_u_addr_align (clone+truncate exec_fetch_u_        *)
(*     pagefault_4 UmodeFetchFault.v:175); arm: clone ustep_noexec_      *)
(*     fetch_fault (WpUserFetch.v:937) MINUS its translate block, e:=    *)
(*     E_Fetch_Addr_Align (cause 0, rv64d.v:13585; stval=va since        *)
(*     misaligned_fetch_writes_xtval=true rv64d.v:12773).  New uctx      *)
(*     field Hdel_fetch_addr_align (mirror Hdel_fetchpf WpUserBase.v:66).*)
(*     Disjunct = just [neq_vec (access_vec_dec va 0) 'b"0" = true].     *)
(*                                                                      *)
(* ARM 2 2-aligned full-word split fetch -- MEDIUM (~week), NOT yet      *)
(* built; unavoidable for a truly-total user_classify (2-aligned-not-4   *)
(* pc with a 32-bit instr IS reachable; user_frame pins only pc_is va).  *)
(*   The HARD model tower ALREADY EXISTS for S-mode: exec_fetch_F_Base_  *)
(*   2_S_gen (SmodeCore.v:892-944) -- state-polymorphic 2+2 split, two   *)
(*   independent translates (Htrl va->s1, Htrh va+2->s2), concludes      *)
(*   F_Base w at s2.  Build exec_fetch_F_Base_2_U_gen by the documented  *)
(*   S->U copy-generalize (abstract pal/pah, Supervisor->User; same      *)
(*   pattern as exec_fetch_F_Base_4_U_gen UmodeFetch.v:416).             *)
(*   ENGINE BLOCKER: wp_instr_u/_hit/_data hardcode exec_fetch_F_Base_4_ *)
(*   U_gen (WpUserBase.v:404/599/1681/1915).  Introduce b_fetch_mode     *)
(*   (4-aligned single-window OR 2-aligned split), the full-word twin of *)
(*   c_fetch_mode (WpUserSteps.v:159), and generalize the wp_instr_u*    *)
(*   engines to destruct it (copy the two fetch-construction blocks,     *)
(*   duplicate the tail per branch -- the SAME recipe used for the RVC   *)
(*   dual-geometry engine wp_instr_c_hit).  Then every retiring _u arm   *)
(*   rides it unchanged; decode/execute reuse is total (exec_hart_       *)
(*   active_progress_base_gen SmodeCore.v:175 is fetch-source-agnostic   *)
(*   once w=concat ihi ilo is assembled).  Two new ustep_case disjuncts: *)
(*   (i) 2-aligned RETIRE (TWO vpn lookups spec!!vpnL/vpnH, per-half     *)
(*   2-byte code residence, then identical decode/execute conjuncts);    *)
(*   (ii) high-half fetch fault (spec!!vpnH=None / noexec on iH; tval    *)
(*   va+2).  Perf watch: the engine destruct adds a duplicated tail to   *)
(*   EVERY retiring _u arm's compile.                                    *)
(* ==================================================================== *)

(* ==================================================================== *)
(* ARM C SCOPING 2026-07-16 (agent): misaligned REGULAR load/store       *)
(* split.  HIGH difficulty, standalone multi-session milestone.          *)
(* Model (config-pinned): sys_misaligned_byte_by_byte=false, allowed_    *)
(* within_exp=0, so a genuinely-misaligned W in {2,4,8} always splits    *)
(* to (n,bytes)=(W/2^k, 2^k) with k=ctz(eaF) in [0,log2 W).  split_      *)
(* misaligned does NOT vm_compute for symbolic eaF -> the classifier     *)
(* must case-split on eaF's low bits to supply k.  Reachable combos:     *)
(* W2{k0}, W4{k0,k1}, W8{k0,k1,k2} = 6 load + 6 store split shapes.      *)
(* Pieces translate INDEPENDENTLY (may straddle a page -> up to 2 vpns), *)
(* each piece i aligned to [bytes] at eaF+i*bytes.                       *)
(* COST: 1 reusable execR_untilMT_step core (small; unfold like execR_   *)
(* untilMT_1 WpLoad.v:244 but stop at the recursive call) + ~12 success  *)
(* towers (FIXED UNROLLING per (W,k), NOT symbolic-n induction -- the    *)
(* ctz case-split is unavoidable anyway, so concrete n is cheaper) +     *)
(* ~44 PARTIAL-LOOP FAULT towers (piece i first to fault; xtval = the    *)
(* FAULTING PIECE's vaddr eaF+i*bytes, so NEW fault disjuncts, not the   *)
(* existing eaF-xtval ones; use execR_untilMT_1_early UmodeLrsc.v:131) + *)
(* generalized multi-window peel/restore (n windows at distinct paD_i,   *)
(* not the single-window data_window_acc_gen WpUserMemStep.v:202) +      *)
(* multi-run value assembly (n x nth_byte_assemble).  Do NOT add a       *)
(* "misaligned regular L/S fault" disjunct -- UNSOUND (model splits).    *)
(*                                                                      *)
(* STRATEGY (decided): ship an INTERIM user_classify with an explicit    *)
(* data-side side-hypothesis [is_aligned_vaddr eaF W = true] (a GENUINE  *)
(* weakening -- eaF = g!!!rs1 + imm is arbitrary since user_frame pins   *)
(* nothing about g, so it is NOT derivable from any invariant).  That    *)
(* interim theorem assembles the WHOLE case tree and yields wp_user_     *)
(* exec_full for the aligned-data fragment NOW (all of ustep_case,       *)
(* aligned ustep_mem_case/fault_case, atomics-misalign faults route).    *)
(* Then arm C is the LAST milestone: it removes that one hypothesis to   *)
(* make the theorem fully unconditional.  Config note (NOT recommended   *)
(* without an explicit decision): regenerating the model with sys_       *)
(* misaligned_byte_by_byte=true collapses the split to a uniform (W,1),  *)
(* killing the ctz case-split -- an observable model-config change.      *)
(* ==================================================================== *)
