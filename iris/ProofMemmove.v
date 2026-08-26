(* ProofMemmove.v -- the whole-function WP proof for the kernel's [memmove],
   over the SIE-agnostic sconf world.  Like memset's fill, memmove's copy runs
   OUTSIDE the interrupt-disabled region, so it threads the [sie_cap_gpr] bundle
   (sconf + sie_cap + gpr_file, no [intr_count]) and its loop is a fuel
   induction on the remaining byte count, not an iLob.

   Structure, following the source's control flow:

     +0x00..+0x06  prologue: the 2-slot frame push, the ra/s0 spills, c.addi4spn
     +0x08         c.beqz on the count -- len = 0 jumps straight to the epilogue
     +0x0a         bltu a1,a0: src <u dst?  ->  the overlap test at +0x30
     +0x0e..+0x16  ASCENDING setup: (uint)n truncation, a5 := src + n, a4 := dst
     +0x18..+0x24  the copy loop            [mm_loop]
     +0x28..+0x2e  epilogue: reload ra/s0, frame trade back, ret   [mm_epilogue]
     +0x30..+0x3a  the overlap test: dst >=u src + n?  -> back to +0x0e
     +0x3e..+0x5e  the DESCENDING loop -- UNREACHABLE, see below

   The two paths that reach the ascending setup (+0x0a not taken, and +0x3a
   taken) differ only in two clobbered caller-saved registers, so everything
   from +0x0e on is proved once, over an arbitrary register map, as [mm_fwd].

   The descending loop is reached only when [src <u dst] and [dst <u src + n],
   which pins dst strictly inside the source range ([mm_overlap_index]).  The
   precondition owns the source and destination bytes SEPARATELY, and separation
   refutes exactly that ([mem_bytes_notin_r] -- the DESTINATION is the exclusive
   side, since the source rides the caller's dfrac), so the +0x3a arm closes
   by contradiction before it steps -- the descending loop's instructions are
   never fetched and CodeMemmove does not even decode them.

   EXPLICIT-CPUID: the whole function threads a generic [b : bool], exactly the
   shape of ProofPlicinit.v / ProofStrlen.v.  [mm_epilogue] and [mm_fwd] are
   non-recursive fragments of the whole-function contract, so each takes its
   own leading (shadowing) hart [`{CID0 : CpuId} `{XI : CurCtx}`] and its continuation
   argument is [wp_next]-wrapped, discharged the same two-step way the
   outermost function is; a caller then treats a call to one of them exactly
   like a leaf application, peeling a fresh [(CIDk, Hsk)] off its result.
   [mm_loop] recurses via [induction rem], so it needs TWO harts kept
   separate: [CIDh] (its [Hcont]'s fixed anchor, forwarded unchanged across
   every recursive call) and [CID0] (this iteration's own entry hart, free to
   change at each step) -- see the comment at [mm_loop] itself. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto InstrBytes KernelText.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import HartTp WpNext IntrDefs.
Require Import CodeMemmove.
Require Import ByteCursor.
Require Import CalleeSaved.
Require Import StackOwn.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Require Import SpecMemmove.
Require Import KernelRvcDecode.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.

(* [rget m k] at a NON-tp index is the plain map lookup ([rget_ne]) -- the
   one-line bridge from a leaf's [rget] to the register-map facts a
   whole-function proof already has.  Written name-free (durable-notes: an
   Ltac body cannot mention a hypothesis by literal name). *)
Local Ltac rgne :=
  rewrite rget_ne;
  [ | let H1 := fresh in let H2 := fresh in
      intro H1; injection H1 as H2; vm_compute in H2; congruence ].

(* ===================================================================== *)
(*  Pure helpers.                                                         *)
(* ===================================================================== *)

Local Lemma seq_cons (start len : nat) : seq start (S len) = start :: seq (S start) len.
Proof. reflexivity. Qed.

(* memmove takes the DESCENDING branch exactly when [src <u dst] and
   [dst <u src + (uint)n].  For a nonzero count that fits in 32 bits those two
   together place dst strictly inside the source range: there is an index
   [j < len] whose source byte IS the destination base.  No no-wrap hypothesis
   is needed -- if [src + n] wraps 2^64 then [src + n <=u src <u dst] and the
   second test is already false. *)
(* the arithmetic core, over plain integers: the two unsigned tests place the
   destination base strictly inside the source range.  (Kept free of any
   [bv_unsigned] so [lia] sees only Z variables -- with bitvector.tactics'
   zify hook in scope, a goal mentioning [bv_unsigned] makes [lia] give up
   with "Cannot find witness".) *)
Local Lemma mm_overlap_arith (s d l : Z) :
  (0 < l)%Z -> (l < 4294967296)%Z ->
  (0 <= s)%Z -> (0 <= d)%Z -> (d < 18446744073709551616)%Z ->
  (s < d)%Z -> (d < (l + s) mod 18446744073709551616)%Z ->
  (0 < d - s)%Z /\ (d - s < l)%Z.
Proof.
  intros Hl0 Hl32 Hs0 Hd0 Hd1 Hsd Hin.
  destruct (Z_lt_ge_dec (l + s) 18446744073709551616) as [Hnw | Hw].
  - rewrite Z.mod_small in Hin; [| lia]. lia.
  - replace (l + s)%Z
      with ((l + s - 18446744073709551616) + 1 * 18446744073709551616)%Z in Hin by lia.
    rewrite Z_mod_plus_full in Hin.
    rewrite Z.mod_small in Hin; [| lia]. lia.
Qed.

(* memmove takes the DESCENDING branch exactly when [src <u dst] and
   [dst <u src + (uint)n].  For a nonzero count that fits in 32 bits those two
   together place dst strictly inside the source range: there is an index
   [j < len] whose source byte IS the destination base.  No no-wrap hypothesis
   is needed -- if [src + n] wraps 2^64 then [src + n <=u src <u dst] and the
   second test is already false. *)
Local Lemma mm_overlap_index (p_src p_dst : mword 64) (len : nat) :
  (0 < len)%nat -> (Z.of_nat len < 2 ^ 32)%Z ->
  (uint p_src < uint p_dst)%Z ->
  (uint p_dst < uint (add_vec (mword_of_int (Z.of_nat len) : mword 64) p_src))%Z ->
  exists j : nat, (j < len)%nat /\ pa_add p_src j = p_dst.
Proof.
  intros Hlen0 Hlen32 Hlt Hin.
  assert (E32 : (2 ^ 32 = 4294967296)%Z) by (vm_compute; reflexivity).
  assert (Hm : bv_modulus 64 = 18446744073709551616%Z) by (vm_compute; reflexivity).
  rewrite E32 in Hlen32.
  assert (HL0 : (0 < Z.of_nat len)%Z) by lia.
  pose proof (bv_unsigned_in_range 64 p_src) as [HS0 HS1].
  pose proof (bv_unsigned_in_range 64 p_dst) as [HD0 HD1].
  rewrite Hm in HD1.
  rewrite !uint_unsigned in Hlt. rewrite !uint_unsigned in Hin.
  (* the end pointer, as a wrapped sum *)
  assert (Hend : bv_unsigned (add_vec (mword_of_int (Z.of_nat len) : mword 64) p_src)
               = ((Z.of_nat len + bv_unsigned p_src) mod 18446744073709551616)%Z).
  { rewrite add_vec64_unsigned. rewrite moi64_unsigned.
    unfold bv_wrap. rewrite Hm. rewrite Zplus_mod_idemp_l. reflexivity. }
  rewrite Hend in Hin.
  destruct (mm_overlap_arith (bv_unsigned p_src) (bv_unsigned p_dst) (Z.of_nat len)
              HL0 Hlen32 HS0 HD0 HD1 Hlt Hin) as [Hj0 Hj1].
  exists (Z.to_nat (bv_unsigned p_dst - bv_unsigned p_src)). split.
  - apply Nat2Z.inj_lt. rewrite Z2Nat.id; [| apply Z.lt_le_incl; exact Hj0].
    exact Hj1.
  - apply bv_eq. unfold pa_add, add_vec_int.
    rewrite add_vec64_unsigned. rewrite moi64_unsigned.
    rewrite Z2Nat.id; [| apply Z.lt_le_incl; exact Hj0].
    unfold bv_wrap. rewrite Hm. rewrite Zplus_mod_idemp_r.
    assert (Heq : (bv_unsigned p_src + (bv_unsigned p_dst - bv_unsigned p_src))%Z
                  = bv_unsigned p_dst) by ring.
    rewrite Heq. apply Z.mod_small. split; [ exact HD0 | exact HD1 ].
Qed.

Module MemmoveProof : MEMMOVE.

Section ProofMemmove.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.


  Context {kt : ktier}.
  (* the source's and the destination's own tiers -- see SpecMemmove.v's note *)
  Context {kts ktw : ktier}.
  Context `{!KtierLe kts kt} `{!KtierLe ktw kt}.
  (* THE CTX MIRROR of [RiscvPtsto.mem_bytes_notin_r].  After the M1 flip
     BOTH sides of memmove's aliasing refutation are context facts, so this
     is NOT a seam: the same induction runs over [TsoCtx]'s exported
     [ctx_pointsto_ne] and no shim is involved. *)
  Local Lemma ctx_bytes_notin_r {kt1 kt2 : ktier} (x1 x2 : CtxId)
      (a c : Arch.pa) (k n : nat) (dq : dfrac) (f : nat -> bv 8) (v : bv 8) :
    ([∗ list] j ∈ seq k n, ctx_pointsto (KTR := kt1) x1 (pa_add a j) dq (f j)) -∗
    ctx_pointsto (KTR := kt2) x2 c (DfracOwn 1) v -∗
    ⌜forall j, (k <= j < k + n)%nat -> pa_add a j <> c⌝.
  Proof.
    revert k. induction n as [|n IH]; intros k; simpl.
    - iIntros "_ _". iPureIntro. intros j Hj. lia.
    - iIntros "[Hh Ht] Hc".
      iDestruct (ctx_pointsto_ne with "Hc Hh") as %Hne0.
      iDestruct (IH (S k) with "Ht Hc") as %Hrest.
      iPureIntro. intros j Hj.
      destruct (decide (j = k)) as [->|Hjk]; [exact (fun H => Hne0 (eq_sym H))|].
      apply Hrest. lia.
  Qed.

  (* [callee_saved] from agreement on the twelve registers the function never
     touches, plus the two frame registers it saves and restores. *)
  Local Lemma cs_from_agree (m M : regfile) :
    M !!! Regidx csp_rs1 = m !!! Regidx csp_rs1 ->
    M !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5) ->
    (forall c : mword 5, is_cs_idx c = true -> c <> (mword_of_int 8 : mword 5) ->
       c <> csp_rs1 -> M !!! Regidx c = m !!! Regidx c) ->
    callee_saved m M.
  Proof.
    intros Hsp Hs0 Hrest. unfold callee_saved. repeat split;
      first [ exact Hsp | exact Hs0
            | apply Hrest; (vm_compute; first [ reflexivity | discriminate ]) ].
  Qed.

  (* strip an insert to a CALLER-saved register off a lookup of the
     callee-saved [c] (whose [is_cs_idx c = true] is [Hc]). *)
  Local Ltac strip_caller Hc :=
    repeat (rewrite upd_ne;
            [| apply not_eq_sym; apply is_cs_idx_true_neq;
               [ vm_compute; reflexivity | exact Hc ]]).

  (* =================================================================== *)
  (*  EPILOGUE (memmove+0x28..+0x2e): reload ra/s0 from the frame, trade   *)
  (*  the two slots back, ret.  Stated over an ARBITRARY register map [M]   *)
  (*  that agrees with the entry map [m0] on the callee-saved registers     *)
  (*  other than the two the frame holds, so both the len = 0 arm and the   *)
  (*  post-loop arm use it.  Non-recursive: a single leading (shadowing)     *)
  (*  hart [CID0] suffices, resolved fresh by unification at each call.     *)
  (* =================================================================== *)
  Local Lemma mm_epilogue `{CID0 : CpuId} 
      (m0 M : regfile) (n : nat) (b : bool) (pcur : mword 64) :
    let sp0 := (m0 !!! Regidx csp_rs1 : mword 64) in
    let ra0 := (m0 !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
    let s00 := (m0 !!! Regidx (mword_of_int 8 : mword 5) : mword 64) in
    (2 <= n)%nat ->
    M !!! Regidx csp_rs1 = pa_stk sp0 2 ->
    (forall c : mword 5, is_cs_idx c = true -> c <> (mword_of_int 8 : mword 5) ->
       c <> csp_rs1 -> M !!! Regidx c = m0 !!! Regidx c) ->
    kernel_text -∗
    sie_cap_gpr kt (CID := CID0) M (n - 2) b pcur -∗
    pc_is (CID := CID0) (mword_of_int (KernelSyms.memmove + 0x28)) -∗
    (pa_stk sp0 1) ↦₈[kt] ra0 -∗
    (pa_stk sp0 2) ↦₈[kt] s00 -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf,
      sie_cap_gpr kt mf n b pcur -∗
      pc_is (ret_pc ra0) -∗
      ⌜ mf !!! Regidx (mword_of_int 10 : mword 5)
        = M !!! Regidx (mword_of_int 10 : mword 5) ⌝ -∗
      ⌜ callee_saved m0 mf ⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 ra0 s00 Hn Hsp HMcs.
    set (ra_idx := (mword_of_int 1 : mword 5)).
    set (s0_idx := (mword_of_int 8 : mword 5)).
    set (M4 := <[Regidx ra_idx := regval_into_reg ra0]> M).
    set (M5 := <[Regidx s0_idx := regval_into_reg s00]> M4).
    iIntros "#Htext Hcg Hpc Hb1 Hb2 Hcont".
    (* the two frame-cell addresses, off the sp the frame is anchored at *)
    assert (Hoff1 : add_vec (pa_stk sp0 2)
                      (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                    = pa_stk sp0 1).
    { unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hoff2 : add_vec (pa_stk sp0 2)
                      (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                    = pa_stk sp0 2).
    { unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ---- +0x28: c.ldsp ra,8(sp) ---- *)
    iApply (wp_cldsp_s_sconf (kt := kt) (ktd := kt) (mword_of_int (KernelSyms.memmove + 0x28)) (mword_of_int 1 : mword 6)
              ra_idx M (n - 2) ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hb1]").
    { iApply (minstr_mm_28 with "Htext"). }
    { iEval (rewrite Hsp). iEval (rewrite Hoff1). iExact "Hb1". }
    iIntros (CID1 Hs1) "Hcg Hpc Hb1".
    iEval (rewrite Hsp) in "Hb1". iEval (rewrite Hoff1) in "Hb1".
    assert (Hp2a : add_vec_int (mword_of_int (KernelSyms.memmove + 0x28) : mword 64) 2
                   = mword_of_int (KernelSyms.memmove + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2a) in "Hpc".
    change (<[Regidx ra_idx := regval_into_reg ra0]> M) with M4.
    (* ---- +0x2a: c.ldsp s0,0(sp) ---- *)
    assert (HspM4 : M4 !!! Regidx csp_rs1 = pa_stk sp0 2).
    { unfold M4. rewrite upd_ne; [ exact Hsp | vm_compute; discriminate ]. }
    iApply (wp_cldsp_s_sconf (kt := kt) (ktd := kt) (mword_of_int (KernelSyms.memmove + 0x2a)) (mword_of_int 0 : mword 6)
              s0_idx M4 (n - 2) s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hb2]").
    { iApply (minstr_mm_2a with "Htext"). }
    { iEval (rewrite HspM4). iEval (rewrite Hoff2). iExact "Hb2". }
    iIntros (CID2 Hs2) "Hcg Hpc Hb2".
    iEval (rewrite HspM4) in "Hb2". iEval (rewrite Hoff2) in "Hb2".
    assert (Hp2c : add_vec_int (mword_of_int (KernelSyms.memmove + 0x2a) : mword 64) 2
                   = mword_of_int (KernelSyms.memmove + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2c) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg s00]> M4) with M5.
    (* ---- +0x2c: c.addi sp,16 -- trade the two slots back ---- *)
    assert (HspM5 : M5 !!! Regidx csp_rs1 = pa_stk sp0 2).
    { unfold M5. rewrite upd_ne; [ exact HspM4 | vm_compute; discriminate ]. }
    assert (Hup : add_vec (M5 !!! Regidx csp_rs1)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0).
    { rewrite HspM5. apply stk_pop_16. }
    assert (Hpop : M5 !!! Regidx csp_rs1
                   = pa_stk (add_vec (M5 !!! Regidx csp_rs1)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hup. exact HspM5. }
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.memmove + 0x2c)) (mword_of_int 16 : mword 6)
              M5 (n - 2) 2 b Hpop with "Hcg Hpc [] [Hb1 Hb2]").
    { iApply (minstr_mm_2c with "Htext"). }
    { iEval (rewrite Hup). iApply (stack_own_2_intro (KTR := kt) with "Hb1 Hb2"). }
    iIntros (CID3 Hs3) "Hcg Hpc".
    assert (Hp2e : add_vec_int (mword_of_int (KernelSyms.memmove + 0x2c) : mword 64) 2
                   = mword_of_int (KernelSyms.memmove + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2e) in "Hpc".
    iEval (rewrite Hup) in "Hcg".
    set (M6 := <[Regidx csp_rs1 := regval_into_reg sp0]> M5).
    assert (Hn2 : (n - 2 + 2)%nat = n) by lia.
    iEval (rewrite Hn2) in "Hcg".
    (* ---- +0x2e: c.jr ra ---- *)
    assert (HraM6 : M6 !!! Regidx ra_idx = ra0).
    { unfold M6. rewrite upd_ne; [| vm_compute; discriminate].
      unfold M5. rewrite upd_ne; [| vm_compute; discriminate].
      unfold M4. apply upd_eq. }
    assert (HraM6' : forall CID' : CpuId, rget (CID := CID') M6 ra_idx = ra0)
      by (intros CID'; rgne; exact HraM6).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.memmove + 0x2e)) ra_idx M6 n b
              ltac:(vm_compute; discriminate) with "Hcg Hpc []").
    { iApply (minstr_mm_2e with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc".
    iEval (rewrite HraM6') in "Hpc".
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! M6 with "Hcg Hpc [%] [%]").
    - unfold M6, M5, M4. repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      reflexivity.
    - apply cs_from_agree.
      + unfold M6. rewrite upd_eq. reflexivity.
      + unfold M6. rewrite upd_ne; [| vm_compute; discriminate].
        unfold M5. apply upd_eq.
      + intros c Hc Hc8 Hcsp.
        unfold M6. rewrite upd_ne; [| congruence].
        unfold M5. rewrite upd_ne; [| unfold s0_idx; congruence].
        unfold M4. rewrite upd_ne;
          [| apply not_eq_sym; apply is_cs_idx_true_neq;
             [ vm_compute; reflexivity | exact Hc ]].
        exact (HMcs c Hc Hc8 Hcsp).
  Qed.

  (* =================================================================== *)
  (*  THE COPY LOOP (memmove+0x18..+0x24).                                 *)
  (*                                                                       *)
  (*    a1 = src cursor, a4 = dst cursor (both bumped BEFORE the access,    *)
  (*    which is why the lbu/sb displacements are -1), a5 = src + len.      *)
  (*                                                                       *)
  (*  Fuel induction on the remaining count [rem]; the taken back-edge's    *)
  (*  later is stripped by iNext against the induction hypothesis.          *)
  (*                                                                        *)
  (*  TWO harts, deliberately kept separate (as in ProofStrlen.v's           *)
  (*  [sl_loop]): [CIDh] anchors [Hcont] -- [Hcont] is supplied ONCE, by      *)
  (*  [mm_loop]'s caller, and is forwarded UNCHANGED across every recursive   *)
  (*  call, so its type (hence [CIDh]) must stay fixed for the whole          *)
  (*  induction; it is a LEMMA parameter, outside the "forall rem off m",     *)
  (*  so [induction rem] never touches it.  [CID0], by contrast, is THIS      *)
  (*  iteration's own entry hart and must be free to change at each           *)
  (*  recursive step, with [Hchain] threading "still traces back to CIDh"     *)
  (*  through the recursion. *)
  (* =================================================================== *)
  Local Lemma mm_loop 
      (p_src p_dst : mword 64) (len : nat) (src_bytes dst_olds : nat -> bv 8) (n : nat)
      (dqs : dfrac) (b : bool) (pcur : mword 64) (CIDh : CpuId) :
    (Z.of_nat len < 2 ^ 64)%Z ->
    forall (rem off : nat) (m : regfile) (CID0 : CpuId),
    (b = false \/ pcur = zero_reg -> (CID0 : CPU) = (CIDh : CPU)) ->
    (off + rem = len)%nat -> (1 <= rem)%nat ->
    m !!! Regidx (mword_of_int 11 : mword 5) = pa_add p_src off ->
    m !!! Regidx (mword_of_int 14 : mword 5) = pa_add p_dst off ->
    m !!! Regidx (mword_of_int 15 : mword 5)
      = add_vec (mword_of_int (Z.of_nat len) : mword 64) p_src ->
    sie_cap_gpr kt (CID := CID0) m n b pcur -∗
    kernel_text -∗
    pc_is (CID := CID0) (mword_of_int (KernelSyms.memmove + 0x18)) -∗
    ([∗ list] j ∈ seq off rem, (pa_add p_src j) ↦ₘ[kts]{dqs} src_bytes j) -∗
    ([∗ list] j ∈ seq off rem, (pa_add p_dst j) ↦ₘ[ktw] dst_olds j) -∗
    wp_next (CID0 := CIDh) b pcur (fun (CID : CpuId) =>
      ∀ mf,
      sie_cap_gpr kt mf n b pcur -∗
      pc_is (mword_of_int (KernelSyms.memmove + 0x28)) -∗
      ([∗ list] j ∈ seq off rem, (pa_add p_src j) ↦ₘ[kts]{dqs} src_bytes j) -∗
      ([∗ list] j ∈ seq off rem, (pa_add p_dst j) ↦ₘ[ktw] src_bytes j) -∗
      ⌜ mf !!! Regidx (mword_of_int 10 : mword 5)
        = m !!! Regidx (mword_of_int 10 : mword 5) ⌝ -∗
      ⌜ callee_saved m mf ⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlen64.
    set (a1_idx := (mword_of_int 11 : mword 5)).
    set (a3_idx := (mword_of_int 13 : mword 5)).
    set (a4_idx := (mword_of_int 14 : mword 5)).
    set (a5_idx := (mword_of_int 15 : mword 5)).
    induction rem as [| rem' IH]; intros off m CID0 Hchain Hsum Hrem Ha1 Ha4 Ha5;
      [ exfalso; lia |].
    iIntros "Hcg #Htext Hpc Hsrc Hdst Hcont".
    (* peel the byte at [off] off both buffers ([big_opL] on a cons IS a
       separating conjunction, so no [big_sepL_cons] rewrite is needed -- and an
       implicit-Phi one would not even elaborate with two buffers in scope) *)
    rewrite (seq_cons off rem').
    iDestruct "Hsrc" as "[Hs0 Hsrc]".
    iDestruct "Hdst" as "[Hd0 Hdst]".
    (* ---- +0x18: c.addi a1,1 ---- *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.memmove + 0x18)) a1_idx (mword_of_int 1 : mword 6)
              m n b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (minstr_mm_18 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hpc".
    assert (Ha1' : rget (CID := CID0) m a1_idx = pa_add p_src off) by (rgne; exact Ha1).
    assert (Hp1a : add_vec_int (mword_of_int (KernelSyms.memmove + 0x18) : mword 64) 2
                   = mword_of_int (KernelSyms.memmove + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    set (m1 := <[Regidx a1_idx := regval_into_reg
          (add_vec (rget (CID := CID0) m a1_idx)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> m).
    (* ---- +0x1a: c.addi a4,1 ---- *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.memmove + 0x1a)) a4_idx (mword_of_int 1 : mword 6)
              m1 n b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (minstr_mm_1a with "Htext"). }
    iIntros (CID2 Hs2) "Hcg Hpc".
    assert (Hm1a4 : m1 !!! Regidx a4_idx = pa_add p_dst off).
    { unfold m1. rewrite upd_ne; [exact Ha4 | vm_compute; discriminate]. }
    assert (Hm1a4' : rget (CID := CID1) m1 a4_idx = pa_add p_dst off)
      by (rgne; exact Hm1a4).
    assert (Hp1c : add_vec_int (mword_of_int (KernelSyms.memmove + 0x1a) : mword 64) 2
                   = mword_of_int (KernelSyms.memmove + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c) in "Hpc".
    set (m2 := <[Regidx a4_idx := regval_into_reg
          (add_vec (rget (CID := CID1) m1 a4_idx)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> m1).
    (* both cursors are now one past the byte about to be copied *)
    assert (Hstep : forall (p : mword 64) (j : nat),
              add_vec (pa_add p j) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
              = pa_add p (S j)).
    { intros p j. apply pa_add_step. apply bv_eq; vm_compute; reflexivity. }
    assert (Hback : forall (p : mword 64) (j : nat),
              add_vec (pa_add p (S j)) (sign_extend' 64 (mword_of_int 0xfff : mword 12))
              = pa_add p j).
    { intros p j. apply pa_add_back1. apply bv_eq; vm_compute; reflexivity. }
    assert (Ha1_2 : m2 !!! Regidx a1_idx = pa_add p_src (S off)).
    { unfold m2. rewrite upd_ne; [| vm_compute; discriminate].
      unfold m1. rewrite upd_eq. unfold regval_into_reg. rewrite Ha1'. apply Hstep. }
    assert (Ha4_2 : m2 !!! Regidx a4_idx = pa_add p_dst (S off)).
    { unfold m2. rewrite upd_eq. unfold regval_into_reg. rewrite Hm1a4'. apply Hstep. }
    assert (Ha5_2 : m2 !!! Regidx a5_idx
                   = add_vec (mword_of_int (Z.of_nat len) : mword 64) p_src).
    { unfold m2, m1. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite upd_ne; [| vm_compute; discriminate]. exact Ha5. }
    assert (Ha1_2' : rget (CID := CID2) m2 a1_idx = pa_add p_src (S off))
      by (rgne; exact Ha1_2).
    (* ---- +0x1c: lbu a3,-1(a1) ---- *)
    iApply (wp_lbu_s_sconf (kt := kt) (ktd := kts) (mword_of_int (KernelSyms.memmove + 0x1c)) a3_idx a1_idx
              (mword_of_int 0xfff : mword 12) m2 n (src_bytes off : mword 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hs0]").
    { iApply (minstr_mm_1c with "Htext"). }
    { iEval (rewrite Ha1_2' (Hback p_src off)). iExact "Hs0". }
    iIntros (CID3 Hs3) "Hcg Hpc Hs0".
    assert (Hp20 : add_vec_int (mword_of_int (KernelSyms.memmove + 0x1c) : mword 64) 4
                   = mword_of_int (KernelSyms.memmove + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp20) in "Hpc".
    iEval (rewrite Ha1_2' (Hback p_src off)) in "Hs0".
    set (m3 := <[Regidx a3_idx := regval_into_reg (zero_extend' 64 (src_bytes off : mword 8))]> m2).
    (* ---- +0x20: sb a3,-1(a4) ---- *)
    assert (Ha3v : m3 !!! Regidx a3_idx = zero_extend' 64 (src_bytes off : mword 8))
      by (unfold m3; apply upd_eq).
    assert (Ha3v' : rget (CID := CID3) m3 a3_idx = zero_extend' 64 (src_bytes off : mword 8))
      by (rgne; exact Ha3v).
    assert (Ha4v : m3 !!! Regidx a4_idx = pa_add p_dst (S off)).
    { unfold m3. rewrite upd_ne; [| vm_compute; discriminate]. exact Ha4_2. }
    assert (Ha4v' : rget (CID := CID3) m3 a4_idx = pa_add p_dst (S off))
      by (rgne; exact Ha4v).
    iApply (wp_sb_s_sconf (kt := kt) (ktd := ktw) (mword_of_int (KernelSyms.memmove + 0x20)) a3_idx a4_idx
              (mword_of_int 0xfff : mword 12) m3 n (dst_olds off) b
              with "Hcg Hpc [] [Hd0]").
    { iApply (minstr_mm_20 with "Htext"). }
    { iEval (rewrite Ha4v' (Hback p_dst off)). iExact "Hd0". }
    iIntros (CID4 Hs4) "Hcg Hpc Hd0".
    assert (Hp24 : add_vec_int (mword_of_int (KernelSyms.memmove + 0x20) : mword 64) 4
                   = mword_of_int (KernelSyms.memmove + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    iEval (rewrite Ha4v' (Hback p_dst off)) in "Hd0".
    iEval (rewrite Ha3v') in "Hd0". iEval (rewrite trunc8_zext8) in "Hd0".
    (* ---- +0x24: bne a5,a1 -- back to the loop top unless the cursor is done ---- *)
    assert (Ha1_3 : m3 !!! Regidx a1_idx = pa_add p_src (S off)).
    { unfold m3. rewrite upd_ne; [| vm_compute; discriminate]. exact Ha1_2. }
    assert (Ha5_3 : m3 !!! Regidx a5_idx
                    = add_vec (mword_of_int (Z.of_nat len) : mword 64) p_src).
    { unfold m3. rewrite upd_ne; [| vm_compute; discriminate]. exact Ha5_2. }
    assert (Ha1_3' : rget (CID := CID3) m3 a1_idx = pa_add p_src (S off))
      by (rgne; exact Ha1_3).
    assert (Ha5_3' : rget (CID := CID3) m3 a5_idx
                    = add_vec (mword_of_int (Z.of_nat len) : mword 64) p_src)
      by (rgne; exact Ha5_3).
    assert (Hcmp : neq_vec (rget (CID := CID3) m3 a5_idx) (rget (CID := CID3) m3 a1_idx)
                   = negb (Nat.eqb (S off) len)).
    { rewrite Ha1_3'. rewrite Ha5_3'. rewrite neq_vec_comm.
      apply pa_add_cmp_bound; [ exact Hlen64 | lia ]. }
    destruct rem' as [| rem''].
    - (* last byte: the cursor has reached a5, so the bne falls through *)
      assert (Hlast : (S off = len)%nat) by lia.
      assert (Hfall : neq_vec (rget (CID := CID3) m3 a5_idx) (rget (CID := CID3) m3 a1_idx) = false).
      { rewrite Hcmp. rewrite Hlast. rewrite Nat.eqb_refl. reflexivity. }
      iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.memmove + 0x24))
                (mword_of_int 0x1ff4 : mword 13) a1_idx a5_idx m3 n b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hfall
                with "Hcg Hpc []").
      { iApply (minstr_mm_24 with "Htext"). }
      iIntros (CID5 Hs5) "Hcg Hpc".
      assert (Hp28 : add_vec_int (mword_of_int (KernelSyms.memmove + 0x24) : mword 64) 4
                     = mword_of_int (KernelSyms.memmove + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp28) in "Hpc".
      assert (HmCs : callee_saved m m3).
      { unfold m3, m2, m1.
        apply callee_saved_insert_r; [ vm_compute; reflexivity |].
        apply callee_saved_insert_r; [ vm_compute; reflexivity |].
        apply callee_saved_insert_r; [ vm_compute; reflexivity |].
        apply callee_saved_refl. }
      assert (Ha0eq : m3 !!! Regidx (mword_of_int 10 : mword 5)
                     = m !!! Regidx (mword_of_int 10 : mword 5)).
      { unfold m3, m2, m1. repeat (rewrite upd_ne; [| vm_compute; discriminate]).
        reflexivity. }
      iSpecialize ("Hcont" $! CID5 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! m3 with "Hcg Hpc [Hs0 Hsrc] [Hd0 Hdst] [%] [%]").
      + iSplitL "Hs0"; [ iExact "Hs0" | iExact "Hsrc" ].
      + iSplitL "Hd0"; [ iExact "Hd0" | iExact "Hdst" ].
      + exact Ha0eq.
      + exact HmCs.
    - (* more bytes: the bne is taken back to +0x18 *)
      assert (Htaken : neq_vec (rget (CID := CID3) m3 a5_idx) (rget (CID := CID3) m3 a1_idx) = true).
      { rewrite Hcmp. destruct (Nat.eqb_spec (S off) len) as [He | Hne];
          [ exfalso; lia | reflexivity ]. }
      iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.memmove + 0x24))
                (mword_of_int 0x1ff4 : mword 13) a1_idx a5_idx m3 n b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Htaken
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (minstr_mm_24 with "Htext"). }
      iNext. iIntros (CID5 Hs5) "Hcg Hpc".
      assert (Hback18 : add_vec (mword_of_int (KernelSyms.memmove + 0x24) : mword 64)
                          (sign_extend' 64 (mword_of_int 0x1ff4 : mword 13))
                        = mword_of_int (KernelSyms.memmove + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hback18) in "Hpc".
      assert (Hchain' : b = false \/ pcur = zero_reg -> (CID5 : CPU) = (CIDh : CPU)) by wp_next_chain.
      iApply (IH (S off) m3 CID5 Hchain' ltac:(lia) ltac:(lia) Ha1_3 Ha4v Ha5_3
                with "Hcg Htext Hpc Hsrc Hdst").
      iIntros (CIDr Hsr mf) "Hcg Hpc Hsrc Hdst %Ha0f %Hcsf".
      iSpecialize ("Hcont" $! CIDr with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "Hcg Hpc [Hs0 Hsrc] [Hd0 Hdst] [%] [%]").
      + iSplitL "Hs0"; [ iExact "Hs0" | iExact "Hsrc" ].
      + iSplitL "Hd0"; [ iExact "Hd0" | iExact "Hdst" ].
      + rewrite Ha0f. unfold m3, m2, m1.
        repeat (rewrite upd_ne; [| vm_compute; discriminate]). reflexivity.
      + apply (callee_saved_trans m m3 mf); [| exact Hcsf ].
        unfold m3, m2, m1.
        apply callee_saved_insert_r; [ vm_compute; reflexivity |].
        apply callee_saved_insert_r; [ vm_compute; reflexivity |].
        apply callee_saved_insert_r; [ vm_compute; reflexivity |].
        apply callee_saved_refl.
  Qed.

  (* =================================================================== *)
  (*  THE ASCENDING PATH (memmove+0x0e onwards), over an ARBITRARY entry   *)
  (*  map [M]: the (uint)n truncation, the a5/a4 setup, the copy loop and  *)
  (*  the epilogue.  Both of the source's two routes to +0x0e instantiate   *)
  (*  this, so none of it is proved twice.  Non-recursive: a single          *)
  (*  leading (shadowing) hart [CID0] suffices, as for [mm_epilogue].        *)
  (* =================================================================== *)
  Local Lemma mm_fwd `{CID0 : CpuId} 
      (m0 M : regfile) (n len : nat) (src_bytes dst_olds : nat -> bv 8)
      (dqs : dfrac) (b : bool) (pcur : mword 64) :
    let sp0 := (m0 !!! Regidx csp_rs1 : mword 64) in
    let ra0 := (m0 !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
    let s00 := (m0 !!! Regidx (mword_of_int 8 : mword 5) : mword 64) in
    let p_dst := (m0 !!! Regidx (mword_of_int 10 : mword 5) : mword 64) in
    let p_src := (m0 !!! Regidx (mword_of_int 11 : mword 5) : mword 64) in
    (2 <= n)%nat -> (0 < len)%nat -> (Z.of_nat len < 2 ^ 32)%Z ->
    M !!! Regidx (mword_of_int 10 : mword 5) = p_dst ->
    M !!! Regidx (mword_of_int 11 : mword 5) = p_src ->
    M !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int (Z.of_nat len) : mword 64) ->
    M !!! Regidx csp_rs1 = pa_stk sp0 2 ->
    (forall c : mword 5, is_cs_idx c = true -> c <> (mword_of_int 8 : mword 5) ->
       c <> csp_rs1 -> M !!! Regidx c = m0 !!! Regidx c) ->
    kernel_text -∗
    sie_cap_gpr kt (CID := CID0) M (n - 2) b pcur -∗
    pc_is (CID := CID0) (mword_of_int (KernelSyms.memmove + 0x0e)) -∗
    (pa_stk sp0 1) ↦₈[kt] ra0 -∗
    (pa_stk sp0 2) ↦₈[kt] s00 -∗
    ([∗ list] j ∈ seq 0 len, (pa_add p_src j) ↦ₘ[kts]{dqs} src_bytes j) -∗
    ([∗ list] j ∈ seq 0 len, (pa_add p_dst j) ↦ₘ[ktw] dst_olds j) -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mfin,
      sie_cap_gpr kt mfin n b pcur -∗
      pc_is (ret_pc ra0) -∗
      ([∗ list] j ∈ seq 0 len, (pa_add p_src j) ↦ₘ[kts]{dqs} src_bytes j) -∗
      ([∗ list] j ∈ seq 0 len, (pa_add p_dst j) ↦ₘ[ktw] src_bytes j) -∗
      ⌜ mfin !!! Regidx (mword_of_int 10 : mword 5) = p_dst ⌝ -∗
      ⌜ callee_saved m0 mfin ⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 ra0 s00 p_dst p_src Hn Hlen0 Hlen32 HMa0 HMa1 HMa2 HMsp HMcs.
    set (a0_idx := (mword_of_int 10 : mword 5)).
    set (a2_idx := (mword_of_int 12 : mword 5)).
    set (a4_idx := (mword_of_int 14 : mword 5)).
    set (a5_idx := (mword_of_int 15 : mword 5)).
    assert (Hlen64 : (Z.of_nat len < 2 ^ 64)%Z)
      by (apply (Z.lt_trans _ (2 ^ 32)); [ exact Hlen32 | vm_compute; reflexivity ]).
    assert (Hlenu : bv_unsigned (mword_of_int (Z.of_nat len) : mword 64) = Z.of_nat len).
    { rewrite moi64_unsigned. apply bv_wrap_small.
      split; [ apply Nat2Z.is_nonneg |].
      apply (Z.lt_trans _ (2 ^ 32)); [ exact Hlen32 |].
      unfold bv_modulus. vm_compute. reflexivity. }
    iIntros "#Htext Hcg Hpc Hb1 Hb2 Hsrc Hdst Hcont".
    (* ---- +0x0e: c.slli a2,32 ---- *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.memmove + 0x0e)) (Regidx a2_idx) a2_idx
              (mword_of_int 32 : mword 6) M (n - 2) b
              eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (minstr_mm_0e with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hpc".
    assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.memmove + 0x0e) : mword 64) 2
                   = mword_of_int (KernelSyms.memmove + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    set (M1 := <[Regidx a2_idx := regval_into_reg
          (shift_bits_left (rget (CID := CID0) M a2_idx)
             (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))]> M).
    assert (HMa2' : rget (CID := CID0) M a2_idx = (mword_of_int (Z.of_nat len) : mword 64))
      by (rgne; exact HMa2).
    (* ---- +0x10: c.srli a2,32 ---- *)
    iApply (wp_csrli_s_sconf (mword_of_int (KernelSyms.memmove + 0x10)) (Cregidx (mword_of_int 4)) a2_idx
              (mword_of_int 32 : mword 6) M1 (n - 2) b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (minstr_mm_10 with "Htext"). }
    iIntros (CID2 Hs2) "Hcg Hpc".
    assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.memmove + 0x10) : mword 64) 2
                   = mword_of_int (KernelSyms.memmove + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    set (M2 := <[Regidx a2_idx := regval_into_reg
          (shift_bits_right (rget (CID := CID1) M1 a2_idx)
             (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))]> M1).
    assert (HM1a2 : M1 !!! Regidx a2_idx
                    = shift_bits_left (rget (CID := CID0) M a2_idx)
                        (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
      by (unfold M1; apply upd_eq).
    assert (HM1a2' : rget (CID := CID1) M1 a2_idx
                    = shift_bits_left (rget (CID := CID0) M a2_idx)
                        (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
      by (rgne; exact HM1a2).
    (* the round trip through 32 bits is the identity on the count *)
    assert (HM2a2 : M2 !!! Regidx a2_idx = (mword_of_int (Z.of_nat len) : mword 64)).
    { unfold M2. rewrite upd_eq. unfold regval_into_reg.
      rewrite HM1a2' HMa2'. apply slli32_srli32. rewrite Hlenu. exact Hlen32. }
    assert (HM2a2' : rget (CID := CID2) M2 a2_idx = (mword_of_int (Z.of_nat len) : mword 64))
      by (rgne; exact HM2a2).
    assert (HM1a1 : M1 !!! Regidx (mword_of_int 11 : mword 5) = p_src).
    { unfold M1. rewrite upd_ne; [| vm_compute; discriminate]. exact HMa1. }
    assert (HM2a1 : M2 !!! Regidx (mword_of_int 11 : mword 5) = p_src).
    { unfold M2. rewrite upd_ne; [| vm_compute; discriminate]. exact HM1a1. }
    assert (HM2a1' : rget (CID := CID2) M2 (mword_of_int 11 : mword 5) = p_src)
      by (rgne; exact HM2a1).
    assert (HM1a0 : M1 !!! Regidx a0_idx = p_dst).
    { unfold M1. rewrite upd_ne; [| vm_compute; discriminate]. exact HMa0. }
    assert (HM2a0 : M2 !!! Regidx a0_idx = p_dst).
    { unfold M2. rewrite upd_ne; [| vm_compute; discriminate]. exact HM1a0. }
    (* ---- +0x12: add a5,a1,a2 -- the source end pointer ---- *)
    iApply (wp_add_s_sconf (mword_of_int (KernelSyms.memmove + 0x12)) a5_idx (mword_of_int 11 : mword 5)
              a2_idx (add_vec p_src (mword_of_int (Z.of_nat len) : mword 64)) M2 (n - 2) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rewrite HM2a1'; rewrite HM2a2'; reflexivity)
              with "Hcg Hpc []").
    { iApply (minstr_mm_12 with "Htext"). }
    iIntros (CID3 Hs3) "Hcg Hpc".
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.memmove + 0x12) : mword 64) 4
                   = mword_of_int (KernelSyms.memmove + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    set (M3 := <[Regidx a5_idx := regval_into_reg
          (add_vec p_src (mword_of_int (Z.of_nat len) : mword 64))]> M2).
    assert (HM3a0 : M3 !!! Regidx a0_idx = p_dst).
    { unfold M3. rewrite upd_ne; [| vm_compute; discriminate]. exact HM2a0. }
    assert (HM3a0' : rget (CID := CID3) M3 a0_idx = p_dst) by (rgne; exact HM3a0).
    (* ---- +0x16: c.mv a4,a0 -- the destination cursor ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.memmove + 0x16)) a4_idx a0_idx M3 (n - 2) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (minstr_mm_16 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc".
    assert (Hp18 : add_vec_int (mword_of_int (KernelSyms.memmove + 0x16) : mword 64) 2
                   = mword_of_int (KernelSyms.memmove + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    set (M4 := <[Regidx a4_idx := regval_into_reg (add_vec zero_reg (rget (CID := CID3) M3 a0_idx))]> M3).
    (* the loop's three entry facts *)
    assert (HM4a1 : M4 !!! Regidx (mword_of_int 11 : mword 5) = pa_add p_src 0).
    { rewrite pa_add_0.
      unfold M4. rewrite upd_ne; [| vm_compute; discriminate].
      unfold M3. rewrite upd_ne; [| vm_compute; discriminate]. exact HM2a1. }
    assert (HM4a4 : M4 !!! Regidx a4_idx = pa_add p_dst 0).
    { rewrite pa_add_0.
      unfold M4. rewrite upd_eq. unfold regval_into_reg.
      rewrite HM3a0' add_vec_zero_l. reflexivity. }
    assert (HM4a5 : M4 !!! Regidx a5_idx
                    = add_vec (mword_of_int (Z.of_nat len) : mword 64) p_src).
    { unfold M4. rewrite upd_ne; [| vm_compute; discriminate].
      unfold M3. rewrite upd_eq. unfold regval_into_reg. apply add_vec64_comm. }
    (* ---- +0x18..+0x24: the copy loop ---- *)
    iApply (mm_loop p_src p_dst len src_bytes dst_olds (n - 2) dqs b pcur CID4 Hlen64
              len 0%nat M4 CID4 ltac:(intros _; reflexivity) ltac:(lia) ltac:(lia)
              HM4a1 HM4a4 HM4a5
              with "Hcg Htext Hpc Hsrc Hdst").
    iIntros (CIDl Hsl mf) "Hcg Hpc Hsrc Hdst %Ha0f %Hcsf".
    (* ---- +0x28..+0x2e: the epilogue ---- *)
    assert (HmfA0 : mf !!! Regidx a0_idx = p_dst).
    { rewrite Ha0f. unfold M4. rewrite upd_ne; [| vm_compute; discriminate].
      unfold M3. rewrite upd_ne; [| vm_compute; discriminate]. exact HM2a0. }
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk sp0 2).
    { rewrite (callee_saved_lookup Hcsf csp_rs1 ltac:(vm_compute; reflexivity)).
      unfold M4, M3, M2, M1. repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      exact HMsp. }
    assert (HmfCs : forall c : mword 5, is_cs_idx c = true ->
              c <> (mword_of_int 8 : mword 5) -> c <> csp_rs1 ->
              mf !!! Regidx c = m0 !!! Regidx c).
    { intros c Hc Hc8 Hcsp.
      rewrite (callee_saved_lookup Hcsf c Hc).
      unfold M4, M3, M2, M1. strip_caller Hc.
      exact (HMcs c Hc Hc8 Hcsp). }
    iApply (mm_epilogue m0 mf n b pcur Hn Hmfsp HmfCs
              with "Htext Hcg Hpc Hb1 Hb2").
    iIntros (CID5 Hs5 mfin) "Hcg Hpc %Ha0fin %Hcsfin".
    iSpecialize ("Hcont" $! CID5 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mfin with "Hcg Hpc Hsrc Hdst [%] [%]").
    - rewrite Ha0fin. exact HmfA0.
    - exact Hcsfin.
  Qed.

  (* =================================================================== *)
  (*  THE WHOLE FUNCTION.                                                  *)
  (* =================================================================== *)
  Lemma wp_memmove_sconf
      (m0 : regfile) (n : nat) (len : nat) (src_bytes dst_olds : nat -> bv 8)
      (dqs : dfrac) (b : bool) (pcur : mword 64)
    : wp_memmove_sconf_body kt kts ktw m0 n len src_bytes dst_olds dqs b pcur.
  Proof.
    cbv beta delta [wp_memmove_sconf_body].
    intros a0_idx a1_idx a2_idx pcE ra0 p_dst p_src ret_tgt Hn Hlen32 Ha2.
    set (ra_idx := (mword_of_int 1 : mword 5)).
    set (s0_idx := (mword_of_int 8 : mword 5)).
    set (a3_idx := (mword_of_int 13 : mword 5)).
    set (a4_idx := (mword_of_int 14 : mword 5)).
    set (sp0 := (m0 !!! Regidx csp_rs1 : mword 64)).
    set (s00 := (m0 !!! Regidx s0_idx : mword 64)).
    set (imm_entry := (mword_of_int 48 : mword 6)).
    set (nzimm_s0 := (mword_of_int 4 : mword 8)).
    set (imm8_beqz := (mword_of_int 16 : mword 8)).
    set (sp' := add_vec sp0 (sign_extend' 64 (sign_extend' 12 imm_entry))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0).
    assert (Hlenu : bv_unsigned (mword_of_int (Z.of_nat len) : mword 64) = Z.of_nat len).
    { rewrite moi64_unsigned. apply bv_wrap_small.
      split; [ apply Nat2Z.is_nonneg |].
      apply (Z.lt_trans _ (2 ^ 32)); [ exact Hlen32 |].
      unfold bv_modulus. vm_compute. reflexivity. }
    assert (HpcE : pcE = mword_of_int (KernelSyms.memmove + 0x00))
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite HpcE.
    iIntros "Hcg #Htext Hpc Hsrc Hdst Hcont".
    (* ---- +0x00: c.addi sp,-16 -- the 2-slot frame push ---- *)
    assert (Hsp' : sp' = pa_stk sp0 2).
    { unfold sp', imm_entry, pa_stk, add_vec_int.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_caddi_sp_push_s_sconf (mword_of_int (KernelSyms.memmove + 0x00)) imm_entry m0 n 2 b Hn Hsp'
              with "Hcg Hpc []").
    { iApply (minstr_mm_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    assert (Hp02 : add_vec_int (mword_of_int (KernelSyms.memmove + 0x00) : mword 64) 2
                   = mword_of_int (KernelSyms.memmove + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (v1 v2) "[Hb1 Hb2]".
    assert (Hcsp1 : m1 !!! Regidx csp_rs1 = sp') by (unfold m1; apply upd_eq).
    assert (Hpa1 : add_vec (m1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 1).
    { rewrite Hcsp1. rewrite Hsp'. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (m1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk sp0 2).
    { rewrite Hcsp1. rewrite Hsp'. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hb1".
    iEval (rewrite -Hpa2) in "Hb2".
    (* ---- +0x02: c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf (kt := kt) (ktd := kt) (mword_of_int (KernelSyms.memmove + 0x02)) (mword_of_int 1 : mword 6)
              ra_idx m1 (n - 2) v1 b with "Hcg Hpc [] Hb1").
    { iApply (minstr_mm_02 with "Htext"). }
    iIntros (CID2 Hs2) "Hcg Hpc Hb1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.memmove + 0x02) : mword 64) 2
                   = mword_of_int (KernelSyms.memmove + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* ---- +0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf (kt := kt) (ktd := kt) (mword_of_int (KernelSyms.memmove + 0x04)) (mword_of_int 0 : mword 6)
              s0_idx m1 (n - 2) v2 b with "Hcg Hpc [] Hb2").
    { iApply (minstr_mm_04 with "Htext"). }
    iIntros (CID3 Hs3) "Hcg Hpc Hb2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.memmove + 0x04) : mword 64) 2
                   = mword_of_int (KernelSyms.memmove + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    assert (Hra1 : m1 !!! Regidx ra_idx = ra0)
      by (unfold m1; rewrite upd_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (Hra1' : forall CID' : CpuId, rget (CID := CID') m1 ra_idx = ra0)
      by (intros CID'; rgne; exact Hra1).
    assert (Hs01 : m1 !!! Regidx s0_idx = s00)
      by (unfold m1, s00; rewrite upd_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (Hs01' : forall CID' : CpuId, rget (CID := CID') m1 s0_idx = s00)
      by (intros CID'; rgne; exact Hs01).
    iEval (rewrite Hpa1 Hra1') in "Hb1".
    iEval (rewrite Hpa2 Hs01') in "Hb2".
    (* ---- +0x06: c.addi4spn s0,sp,16 ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.memmove + 0x06)) (Cregidx (mword_of_int 0))
              nzimm_s0 s0_idx m1 (n - 2) b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (minstr_mm_06 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc".
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.memmove + 0x06) : mword 64) 2
                   = mword_of_int (KernelSyms.memmove + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* fold the frame pointer's value through [Hcsp1] BEFORE naming the map: a
       map whose stored value still contains [m1 !!! Regidx csp_rs1] carries an
       insert-lookup inside itself, and [rewrite upd_ne] then matches THAT
       occurrence instead of the one being peeled. *)
    iEval (rewrite Hcsp1) in "Hcg".
    set (m2 := <[Regidx s0_idx := regval_into_reg
          (add_vec sp' (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1).
    (* m2's register facts, once and for all.  Peeled insert by insert: with the
       whole [sie_cap_gpr] context in scope, [reg_lookup]'s single [vm_compute]
       does not come back on these goals. *)
    assert (Hm2sp : m2 !!! Regidx csp_rs1 = pa_stk sp0 2).
    { unfold m2. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite Hcsp1. exact Hsp'. }
    assert (Hm2a0 : m2 !!! Regidx a0_idx = p_dst).
    { unfold m2. rewrite upd_ne; [| vm_compute; discriminate].
      unfold m1. rewrite upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (Hm2a1 : m2 !!! Regidx a1_idx = p_src).
    { unfold m2. rewrite upd_ne; [| vm_compute; discriminate].
      unfold m1. rewrite upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (Hm2a2 : m2 !!! Regidx a2_idx = (mword_of_int (Z.of_nat len) : mword 64)).
    { unfold m2. rewrite upd_ne; [| vm_compute; discriminate].
      unfold m1. rewrite upd_ne; [| vm_compute; discriminate]. exact Ha2. }
    assert (Hm2cs : forall c : mword 5, is_cs_idx c = true -> c <> s0_idx ->
              c <> csp_rs1 -> m2 !!! Regidx c = m0 !!! Regidx c).
    { intros c Hc Hc8 Hcsp. unfold m2. rewrite upd_ne; [| congruence ].
      unfold m1. rewrite upd_ne; [ reflexivity | congruence ]. }
    destruct len as [| len'].
    - (* ============ len = 0: the c.beqz jumps to the epilogue ============ *)
      assert (Hz : eq_vec (m2 !!! Regidx a2_idx) zero_reg = true)
        by (rewrite Hm2a2; vm_compute; reflexivity).
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.memmove + 0x08)) imm8_beqz
                (Cregidx (mword_of_int 4)) a2_idx m2 (n - 2) b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hz
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (minstr_mm_08 with "Htext"). }
      iNext. iIntros (CID5 Hs5) "Hcg Hpc".
      assert (Hpsuf : add_vec (mword_of_int (KernelSyms.memmove + 0x08) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec imm8_beqz ('b"0"))))
                      = mword_of_int (KernelSyms.memmove + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpsuf) in "Hpc".
      iApply (mm_epilogue m0 m2 n b pcur Hn Hm2sp Hm2cs
                with "Htext Hcg Hpc Hb1 Hb2").
      iIntros (CID6 Hs6 mfin) "Hcg Hpc %Ha0fin %Hcsfin".
      iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mfin with "Hcg Hpc Hsrc Hdst [%] [%]").
      + rewrite Ha0fin. exact Hm2a0.
      + exact Hcsfin.
    - (* ============ 0 < len: the c.beqz falls through ============ *)
      assert (Hlen0 : (0 < S len')%nat) by lia.
      assert (Hnz : eq_vec (m2 !!! Regidx a2_idx) zero_reg = false).
      { rewrite Hm2a2. apply eq_vec_false_iff. intro Hc.
        apply (f_equal bv_unsigned) in Hc. rewrite Hlenu in Hc.
        assert (Hzr : bv_unsigned (zero_reg : mword 64) = 0%Z)
          by (vm_compute; reflexivity).
        rewrite Hzr in Hc. lia. }
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.memmove + 0x08)) imm8_beqz
                (Cregidx (mword_of_int 4)) a2_idx m2 (n - 2) b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hnz
                with "Hcg Hpc []").
      { iApply (minstr_mm_08 with "Htext"). }
      iIntros (CID5 Hs5) "Hcg Hpc".
      assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.memmove + 0x08) : mword 64) 2
                     = mword_of_int (KernelSyms.memmove + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp0a) in "Hpc".
      (* ---- +0x0a: bltu a1,a0 -- is the source below the destination? ---- *)
      destruct (zopz0zI_u (m2 !!! Regidx a1_idx) (m2 !!! Regidx a0_idx)) eqn:Hbltu.
      + (* src <u dst: the overlap test at +0x30 runs *)
        iApply (wp_bltu_taken_s_sconf (mword_of_int (KernelSyms.memmove + 0x0a))
                  (mword_of_int 0x26 : mword 13) a0_idx a1_idx m2 (n - 2) b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hbltu
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (minstr_mm_0a with "Htext"). }
        iNext. iIntros (CID6 Hs6) "Hcg Hpc".
        assert (Hp30 : add_vec (mword_of_int (KernelSyms.memmove + 0x0a) : mword 64)
                         (sign_extend' 64 (mword_of_int 0x26 : mword 13))
                       = mword_of_int (KernelSyms.memmove + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp30) in "Hpc".
        (* ---- +0x30: slli a3,a2,32.  The count is supplied as an explicit
           [wval], so the resulting map does NOT store [m2 !!! Regidx a2_idx] --
           an insert-lookup inside a stored value is what makes a later
           [rewrite upd_ne] match the wrong occurrence. ---- *)
        iApply (wp_slli_s_sconf (mword_of_int (KernelSyms.memmove + 0x30)) a3_idx a2_idx
                  (mword_of_int 32 : mword 6)
                  (shift_bits_left (mword_of_int (Z.of_nat (S len')) : mword 64)
                     (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
                  m2 (n - 2) b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(rewrite (rget_ne m2 a2_idx ltac:(vm_compute; discriminate));
                        rewrite Hm2a2; reflexivity)
                  with "Hcg Hpc []").
        { iApply (minstr_mm_30 with "Htext"). }
        iIntros (CID7 Hs7) "Hcg Hpc".
        assert (Hp34 : add_vec_int (mword_of_int (KernelSyms.memmove + 0x30) : mword 64) 4
                       = mword_of_int (KernelSyms.memmove + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp34) in "Hpc".
        set (m3 := <[Regidx a3_idx := regval_into_reg
              (shift_bits_left (mword_of_int (Z.of_nat (S len')) : mword 64)
                 (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))]> m2).
        assert (Hm3a3 : m3 !!! Regidx a3_idx
                        = shift_bits_left (mword_of_int (Z.of_nat (S len')) : mword 64)
                            (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
          by (unfold m3; apply upd_eq).
        assert (Hm3a3' : rget (CID := CID7) m3 a3_idx
                        = shift_bits_left (mword_of_int (Z.of_nat (S len')) : mword 64)
                            (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
          by (rgne; exact Hm3a3).
        (* ---- +0x34: c.srli a3,32 -- the count round trip closes ---- *)
        iApply (wp_csrli_s_sconf (mword_of_int (KernelSyms.memmove + 0x34)) (Cregidx (mword_of_int 5))
                  a3_idx (mword_of_int 32 : mword 6) m3 (n - 2) b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (minstr_mm_34 with "Htext"). }
        iIntros (CID8 Hs8) "Hcg Hpc".
        assert (Hp36 : add_vec_int (mword_of_int (KernelSyms.memmove + 0x34) : mword 64) 2
                       = mword_of_int (KernelSyms.memmove + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp36) in "Hpc".
        assert (Htr : shift_bits_right
                        (shift_bits_left (mword_of_int (Z.of_nat (S len')) : mword 64)
                           (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
                        (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0)
                      = (mword_of_int (Z.of_nat (S len')) : mword 64)).
        { apply slli32_srli32. rewrite Hlenu. exact Hlen32. }
        iEval (rewrite Hm3a3') in "Hcg". iEval (rewrite Htr) in "Hcg".
        set (m4 := <[Regidx a3_idx :=
              regval_into_reg (mword_of_int (Z.of_nat (S len')) : mword 64)]> m3).
        assert (Hm4a3 : m4 !!! Regidx a3_idx = (mword_of_int (Z.of_nat (S len')) : mword 64))
          by (unfold m4; apply upd_eq).
        assert (Hm4a1 : m4 !!! Regidx a1_idx = p_src).
        { unfold m4. rewrite upd_ne; [| vm_compute; discriminate].
          unfold m3. rewrite upd_ne; [| vm_compute; discriminate]. exact Hm2a1. }
        assert (Hm4a1' : rget (CID := CID8) m4 a1_idx = p_src) by (rgne; exact Hm4a1).
        assert (Hm4a0 : m4 !!! Regidx a0_idx = p_dst).
        { unfold m4. rewrite upd_ne; [| vm_compute; discriminate].
          unfold m3. rewrite upd_ne; [| vm_compute; discriminate]. exact Hm2a0. }
        assert (Hm4a3' : rget (CID := CID8) m4 a3_idx = (mword_of_int (Z.of_nat (S len')) : mword 64))
          by (rgne; exact Hm4a3).
        (* ---- +0x36: add a4,a1,a3 -- the source end pointer ---- *)
        iApply (wp_add_s_sconf (mword_of_int (KernelSyms.memmove + 0x36)) a4_idx a1_idx a3_idx
                  (add_vec (mword_of_int (Z.of_nat (S len')) : mword 64) p_src) m4 (n - 2) b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(rewrite Hm4a1' Hm4a3'; apply add_vec64_comm)
                  with "Hcg Hpc []").
        { iApply (minstr_mm_36 with "Htext"). }
        iIntros (CID9 Hs9) "Hcg Hpc".
        assert (Hp3a : add_vec_int (mword_of_int (KernelSyms.memmove + 0x36) : mword 64) 4
                       = mword_of_int (KernelSyms.memmove + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp3a) in "Hpc".
        set (m5 := <[Regidx a4_idx := regval_into_reg
              (add_vec (mword_of_int (Z.of_nat (S len')) : mword 64) p_src)]> m4).
        assert (Hm5a4 : m5 !!! Regidx a4_idx
                        = add_vec (mword_of_int (Z.of_nat (S len')) : mword 64) p_src)
          by (unfold m5; apply upd_eq).
        assert (Hm5a0 : m5 !!! Regidx a0_idx = p_dst).
        { unfold m5. rewrite upd_ne; [| vm_compute; discriminate]. exact Hm4a0. }
        (* ---- +0x3a: bgeu a0,a4 -- is the destination at or past the source end? ---- *)
        destruct (zopz0zKzJ_u (m5 !!! Regidx a0_idx) (m5 !!! Regidx a4_idx)) eqn:Hbgeu.
        * (* taken: the ranges do not overlap, so the ascending copy runs *)
          iApply (wp_bgeu_taken_s_sconf (mword_of_int (KernelSyms.memmove + 0x3a))
                    (mword_of_int 0x1fd4 : mword 13) a4_idx a0_idx m5 (n - 2) b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hbgeu
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (minstr_mm_3a with "Htext"). }
          iNext. iIntros (CID10 Hs10) "Hcg Hpc".
          assert (Hp0e : add_vec (mword_of_int (KernelSyms.memmove + 0x3a) : mword 64)
                           (sign_extend' 64 (mword_of_int 0x1fd4 : mword 13))
                         = mword_of_int (KernelSyms.memmove + 0x0e))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp0e) in "Hpc".
          iApply (mm_fwd m0 m5 n (S len') src_bytes dst_olds dqs b pcur Hn Hlen0 Hlen32
                    Hm5a0 ltac:(unfold m5, m4, m3;
                                repeat (rewrite upd_ne; [| vm_compute; discriminate]);
                                exact Hm2a1)
                    ltac:(unfold m5, m4, m3;
                          repeat (rewrite upd_ne; [| vm_compute; discriminate]);
                          exact Hm2a2)
                    ltac:(unfold m5, m4, m3;
                          repeat (rewrite upd_ne; [| vm_compute; discriminate]);
                          exact Hm2sp)
                    ltac:(intros c Hc Hc8 Hcsp; unfold m5, m4, m3;
                          strip_caller Hc; exact (Hm2cs c Hc Hc8 Hcsp))
                    with "Htext Hcg Hpc Hb1 Hb2 Hsrc Hdst").
          iIntros (CID11 Hs11 mfin) "Hcg Hpc Hsrc Hdst %Ha0fin %Hcsfin".
          iSpecialize ("Hcont" $! CID11 with "[%]"); [wp_next_chain|].
          iApply ("Hcont" $! mfin with "Hcg Hpc Hsrc Hdst [%] [%]").
          -- exact Ha0fin.
          -- exact Hcsfin.
        * (* fall-through: dst is strictly inside the source range -- the two
             buffers would have to share a byte, which their separate ownership
             refutes.  This is the only place the non-overlap contract is used. *)
          iExFalso.
          assert (Hsrc_lt : (uint p_src < uint p_dst)%Z).
          { unfold zopz0zI_u in Hbltu.
            rewrite Hm2a1 in Hbltu. rewrite Hm2a0 in Hbltu.
            apply Z.ltb_lt. exact Hbltu. }
          assert (Hdst_in : (uint p_dst
                             < uint (add_vec (mword_of_int (Z.of_nat (S len')) : mword 64) p_src))%Z).
          { unfold zopz0zKzJ_u in Hbgeu.
            rewrite Hm5a0 in Hbgeu. rewrite Hm5a4 in Hbgeu.
            rewrite Z.geb_leb in Hbgeu. apply Z.leb_gt in Hbgeu. exact Hbgeu. }
          destruct (mm_overlap_index p_src p_dst (S len') Hlen0 Hlen32 Hsrc_lt Hdst_in)
            as (j & Hjlt & Hjeq).
          (* peel byte 0 off the DESTINATION only: [mem_bytes_notin_r] has to
             see the source buffer still indexed by [seq 0 len], so the
             [seq_cons] unfolding must not leak into it.
               IT IS THE [_r] FORM because the source now rides the caller's
             [dqs] and only the DESTINATION byte is exclusive -- the whole side
             of the refutation moved when the source went fractional, but the
             refutation itself is the same one. *)
          iEval (rewrite (seq_cons 0 len')) in "Hdst".
          iDestruct "Hdst" as "[Hd0 _]".
          iEval (rewrite pa_add_0) in "Hd0".
          iDestruct (ctx_bytes_notin_r with "Hsrc Hd0") as %Hnotin.
          destruct (Hnotin j ltac:(lia) Hjeq).
      + (* src >=u dst: no overlap is possible, the ascending copy runs directly *)
        assert (Hp0e : add_vec_int (mword_of_int (KernelSyms.memmove + 0x0a) : mword 64) 4
                       = mword_of_int (KernelSyms.memmove + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_bltu_fall_s_sconf (mword_of_int (KernelSyms.memmove + 0x0a))
                  (mword_of_int 0x26 : mword 13) a0_idx a1_idx m2 (n - 2) b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hbltu
                  with "Hcg Hpc []").
        { iApply (minstr_mm_0a with "Htext"). }
        iIntros (CID6 Hs6) "Hcg Hpc".
        iEval (rewrite Hp0e) in "Hpc".
        iApply (mm_fwd m0 m2 n (S len') src_bytes dst_olds dqs b pcur Hn Hlen0 Hlen32
                  Hm2a0 Hm2a1 Hm2a2 Hm2sp Hm2cs
                  with "Htext Hcg Hpc Hb1 Hb2 Hsrc Hdst").
        iIntros (CID7 Hs7 mfin) "Hcg Hpc Hsrc Hdst %Ha0fin %Hcsfin".
        iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! mfin with "Hcg Hpc Hsrc Hdst [%] [%]").
        -- exact Ha0fin.
        -- exact Hcsfin.
  Qed.

End ProofMemmove.

End MemmoveProof.
