(* ProofEitherCopy.v -- the whole-function WPs for xv6's either_copyout()
   and either_copyin().

     int either_copyout(int user_dst, uint64 dst, void *src, uint64 len) {
       struct proc *p = myproc();
       if (user_dst) return copyout(p->pagetable, p->sz, dst, src, len);
       else { memmove((char * )dst, src, len); return 0; }
     }
     int either_copyin(void *dst, int user_src, uint64 src, uint64 len) {
       struct proc *p = myproc();
       if (user_src) return copyin(p->pagetable, p->sz, dst, src, len);
       else { memmove(dst, (char * )src, len); return 0; }
     }

   The contracts are SpecEitherCopyout.v / SpecEitherCopyin.v.  Both
   functions are 32 instructions over a 48-byte six-slot frame, with two
   arms rejoining at the epilogue (+0x2c).

   *** either_copyOUT IS TWO STACK SLOTS SHORT: SpecEitherCopyout.v needs
   [either_copyout_stack : nat := 58%nat], not 56. ***  copyout's own frame is
   [addi sp,sp,-112] = 14 slots in this image, so SpecCopyout.v asks
   [52 <= K] (14 + vmfault's 38); either_copyout's frame is 6 slots, so the
   caller must promise 6 + 52 = 58.  The constant is still the pre-bump
   6 + 50 = 56, and the [lia] proving [52 <= av - 6] at the copyout call is
   the only thing in this file that does not go through -- a scratch copy
   with that one premise stubbed reaches Qed.  **either_copyIN is fine at
   56**: copyin's and copyinstr's frames are [addi sp,sp,-96] = 12 slots, so
   their budget stayed 50 and [either_copyin_stack = 6 + 50] is exact.

   *** THE [psz] ARGUMENT, xv6 `4f2fc8b`. ***  The user arm gained one
   instruction -- [ld a1,72(a0)] at +0x24, between the argument [c.mv]s and
   the [ld a0,80(a0)] that follows -- so the whole tail from +0x24 on sits
   two bytes higher, and the three argument moves shifted a register each
   (a3/a2/a1 -> a4/a3/a2).  The [p->sz] cell it reads comes out of the SAME
   [proc_priv_core_copy] borrow that already served [p->pagetable]; the copy
   contracts themselves no longer take either cell (SpecCopyin.v).

   ONE FILE, TWO FUNCTORS, because gcc emitted ONE code block twice: the
   two functions differ only in which of a0/a1 is the flag (+0x10/+0x12) and
   in their three [jal] targets.  What that buys is [ec_epi], the durable-
   notes recipe for a block emitted twice -- the eight-instruction epilogue
   proved ONCE, parameterized by its pcs and taking its [instr] facts and
   pc-successor equations as premises, then instantiated at both addresses.

   THREE THINGS WORTH REUSING.

   * THE FLAG IS THE RETURN VALUE on the kernel arm.  [mv a0,s1] at +0x46
     returns the flag register, which is sound only because the [c.beqz] at
     +0x1c already proved it zero -- so the arm's answer is not a literal
     the decoder produced but a fact recovered from the branch
     ([eq_vec_true_iff], then [ec_zero_reg_moi] to name it [mword_of_int 0]).

   * THE [sext.w] IS NOT FREE at a symbolic count.  memmove wants
     [a2 = mword_of_int (Z.of_nat len)] and the machine hands it
     [sign_extend' 64 (subrange_vec_dec (len + 0) 31 0)]; the two agree only
     below 2^31, which is why the kernel arm's length premise is tighter
     than the user arm's ([RiscvExtras.sextw_moi]).  Per the durable notes'
     iEval trap, the value is NOT rewritten inside the register map: the
     leaf's raw output is [set] and the LOOKUP is proved instead.

   * [proc_priv] IS BORROWED ONLY ON THE USER ARM.  The kernel arm never
     reads p->pagetable, so [ProcInv.proc_priv_copy] is taken inside the
     [destruct user] rather than before it -- which is what lets the
     precondition be [if user then proc_priv else the destination buffer].

   [Set Printing Depth 40] is mandatory in any file proving over
   [proc_priv]: without it a one-line mistake prints a 4096-conjunct goal
   and reads as a hang (durable-notes). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import CodeEitherCopy.
Require Import SpecMyproc SpecMemmove SpecCopyin SpecCopyout.
Require Import SpecEitherCopyout SpecEitherCopyin.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  Pure arithmetic, shared by both functions.                            *)
(* ===================================================================== *)


(* the kernel arm returns the FLAG register, which the [c.beqz] proved zero *)
Lemma ec_zero_reg_moi : (zero_reg : mword 64) = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* the numeric premises myproc / copy* / memmove take; [lia] cannot evaluate
   the powers, so they are [vm_compute]d here rather than inline at the call
   (the inline-[ltac:] trap, optimization.md). *)
Lemma ec_len32 (len : nat) : (Z.of_nat len < 2 ^ 31) -> (Z.of_nat len < 2 ^ 32).
Proof. change (2 ^ 31) with 2147483648. change (2 ^ 32) with 4294967296. lia. Qed.

Lemma ec_len31 (len : nat) : (Z.of_nat len < 2 ^ 31) -> (Z.of_nat len < 2147483648).
Proof. change (2 ^ 31) with 2147483648. lia. Qed.

(* ===================================================================== *)
(*  The epilogue, +0x2a .. +0x38 -- ONE lemma for both functions.         *)
(* ===================================================================== *)
Section EitherCopyEpilogue.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Lemma ec_epi `{CID0 : CpuId}
      (q2a q2c q2e q30 q32 q34 q36 q38 : mword 64)
      (m Mt : regfile) (av : nat) (rv : mword 64)
      (sp0 ra0 s00 s10 s20 s30 s40 : mword 64) (p : mword 64) (b : bool) :
    (6 <= av)%nat ->
    add_vec_int q2a 2 = q2c -> add_vec_int q2c 2 = q2e ->
    add_vec_int q2e 2 = q30 -> add_vec_int q30 2 = q32 ->
    add_vec_int q32 2 = q34 -> add_vec_int q34 2 = q36 ->
    add_vec_int q36 2 = q38 ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Rs3 = s30 ->
    m !!! Regidx Rs4 = s40 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 6 ->
    Mt !!! Regidx Ra0 = rv ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 ->
        Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr Mt (av - 6)%nat b p -∗
    instr q2a true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) -∗
    instr q2c true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) -∗
    instr q2e true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) -∗
    instr q30 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) -∗
    instr q32 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) -∗
    instr q34 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) -∗
    instr q36 true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) -∗
    instr q38 true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) -∗
    pc_is q2a -∗
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    word_pointsto (pa_stk sp0 4) (DfracOwn 1) s20 -∗
    word_pointsto (pa_stk sp0 5) (DfracOwn 1) s30 -∗
    word_pointsto (pa_stk sp0 6) (DfracOwn 1) s40 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr mf av b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav H2c H2e H30 H32 H34 H36 H38
           Hsp0 Hra0 Hs00 Hs10 Hs20 Hs30 Hs40 Hmtsp Hmta0 Hthr.
    iIntros "Hcg Hi2c Hi2e Hi30 Hi32 Hi34 Hi36 Hi38 Hi3a Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hcont".
    (* ---- +0x2a: c.ldsp ra,40(sp) ---- *)
    assert (Hpa1 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hmtsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf q2a (mword_of_int 5 : mword 6) Rra Mt (av - 6)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2c Hb1 [-]").
    iIntros (CID1 Hs1) "Hcg Hpc Hb1".
    iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> Mt).
    change (<[Regidx Rra := regval_into_reg ra0]> Mt) with T1.
    iEval (rewrite H2c) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T1 upd_ne; [exact Hmtsp | reg_neq]).
    (* ---- +0x2c: c.ldsp s0,32(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf q2c (mword_of_int 4 : mword 6) Rs0 T1 (av - 6)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e Hb2 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hb2".
    iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    change (<[Regidx Rs0 := regval_into_reg s00]> T1) with T2.
    iEval (rewrite H2e) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T2 upd_ne; [exact HT1sp | reg_neq]).
    (* ---- +0x2e: c.ldsp s1,24(sp) ---- *)
    assert (Hpa3 : add_vec (T2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_cldsp_s_sconf q2e (mword_of_int 3 : mword 6) Rs1 T2 (av - 6)%nat s10 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi30 Hb3 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc Hb3".
    iEval (rewrite Hpa3) in "Hb3".
    set (T3 := <[Regidx Rs1 := regval_into_reg s10]> T2).
    change (<[Regidx Rs1 := regval_into_reg s10]> T2) with T3.
    iEval (rewrite H30) in "Hpc".
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T3 upd_ne; [exact HT2sp | reg_neq]).
    (* ---- +0x30: c.ldsp s2,16(sp) ---- *)
    assert (Hpa4 : add_vec (T3 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HT3sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa4) in "Hb4".
    iApply (wp_cldsp_s_sconf q30 (mword_of_int 2 : mword 6) Rs2 T3 (av - 6)%nat s20 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi32 Hb4 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc Hb4".
    iEval (rewrite Hpa4) in "Hb4".
    set (T4 := <[Regidx Rs2 := regval_into_reg s20]> T3).
    change (<[Regidx Rs2 := regval_into_reg s20]> T3) with T4.
    iEval (rewrite H32) in "Hpc".
    assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T4 upd_ne; [exact HT3sp | reg_neq]).
    (* ---- +0x32: c.ldsp s3,8(sp) ---- *)
    assert (Hpa5 : add_vec (T4 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { rewrite HT4sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa5) in "Hb5".
    iApply (wp_cldsp_s_sconf q32 (mword_of_int 1 : mword 6) Rs3 T4 (av - 6)%nat s30 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi34 Hb5 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc Hb5".
    iEval (rewrite Hpa5) in "Hb5".
    set (T5 := <[Regidx Rs3 := regval_into_reg s30]> T4).
    change (<[Regidx Rs3 := regval_into_reg s30]> T4) with T5.
    iEval (rewrite H34) in "Hpc".
    assert (HT5sp : T5 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T5 upd_ne; [exact HT4sp | reg_neq]).
    (* ---- +0x34: c.ldsp s4,0(sp) ---- *)
    assert (Hpa6 : add_vec (T5 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { rewrite HT5sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa6) in "Hb6".
    iApply (wp_cldsp_s_sconf q34 (mword_of_int 0 : mword 6) Rs4 T5 (av - 6)%nat s40 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi36 Hb6 [-]").
    iIntros (CID6 Hs6) "Hcg Hpc Hb6".
    iEval (rewrite Hpa6) in "Hb6".
    set (T6 := <[Regidx Rs4 := regval_into_reg s40]> T5).
    change (<[Regidx Rs4 := regval_into_reg s40]> T5) with T6.
    iEval (rewrite H36) in "Hpc".
    assert (HT6sp : T6 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T6 upd_ne; [exact HT5sp | reg_neq]).
    (* ---- +0x36: c.addi16sp sp,48 (frame pop) ---- *)
    assert (Hwv : add_vec (T6 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0)
      by (rewrite HT6sp; apply stk_pop_48).
    assert (Hpop : T6 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T6 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6)
      by (rewrite Hwv; exact HT6sp).
    iAssert (stack_own sp0 6) with "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hb1"; [iExists _; iExact "Hb1" |].
      iSplitL "Hb2"; [iExists _; iExact "Hb2" |].
      iSplitL "Hb3"; [iExists _; iExact "Hb3" |].
      iSplitL "Hb4"; [iExists _; iExact "Hb4" |].
      iSplitL "Hb5"; [iExists _; iExact "Hb5" |].
      iSplitL "Hb6"; [iExists _; iExact "Hb6" |].
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf q36 (mword_of_int 3 : mword 6) T6 (av - 6)%nat 6 b Hpop
              with "Hcg Hpc Hi38 Hframe [-]").
    iIntros (CID7 Hs7) "Hcg Hpc".
    assert (Hnk : ((av - 6) + 6)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    iEval (rewrite H38) in "Hpc".
    set (T7 := <[Regidx csp_rs1 := regval_into_reg (add_vec (T6 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> T6).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (T6 !!! Regidx csp_rs1)
              (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> T6) with T7.
    (* ---- +0x38: c.ret ---- *)
    assert (HT7ra : T7 !!! Regidx Rra = ra0).
    { rewrite /T7 upd_ne; [| reg_neq]. rewrite /T6 upd_ne; [| reg_neq].
      rewrite /T5 upd_ne; [| reg_neq]. rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf q38 Rra T7 av b ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi3a [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rewrite (rget_ne (CID := CID7) T7 Rra ltac:(vm_compute; discriminate)) HT7ra) in "Hpc".
    (* ---- the postcondition ---- *)
    assert (HT7sp : T7 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /T7 upd_eq Hwv; symmetry; exact Hsp0).
    assert (HT7s0 : T7 !!! Regidx Rs0 = m !!! Regidx Rs0).
    { rewrite /T7 upd_ne; [| reg_neq]. rewrite /T6 upd_ne; [| reg_neq].
      rewrite /T5 upd_ne; [| reg_neq]. rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_eq. symmetry; exact Hs00. }
    assert (HT7s1 : T7 !!! Regidx Rs1 = m !!! Regidx Rs1).
    { rewrite /T7 upd_ne; [| reg_neq]. rewrite /T6 upd_ne; [| reg_neq].
      rewrite /T5 upd_ne; [| reg_neq]. rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_eq. symmetry; exact Hs10. }
    assert (HT7s2 : T7 !!! Regidx Rs2 = m !!! Regidx Rs2).
    { rewrite /T7 upd_ne; [| reg_neq]. rewrite /T6 upd_ne; [| reg_neq].
      rewrite /T5 upd_ne; [| reg_neq]. rewrite /T4 upd_eq. symmetry; exact Hs20. }
    assert (HT7s3 : T7 !!! Regidx Rs3 = m !!! Regidx Rs3).
    { rewrite /T7 upd_ne; [| reg_neq]. rewrite /T6 upd_ne; [| reg_neq].
      rewrite /T5 upd_eq. symmetry; exact Hs30. }
    assert (HT7s4 : T7 !!! Regidx Rs4 = m !!! Regidx Rs4).
    { rewrite /T7 upd_ne; [| reg_neq]. rewrite /T6 upd_eq. symmetry; exact Hs40. }
    assert (HT7a0 : T7 !!! Regidx Ra0 = rv).
    { rewrite /T7 upd_ne; [| reg_neq]. rewrite /T6 upd_ne; [| reg_neq].
      rewrite /T5 upd_ne; [| reg_neq]. rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_ne; [| reg_neq]. exact Hmta0. }
    assert (Hthr7 : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 ->
              T7 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18 N19 N20.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /T7 upd_ne; [| congruence].
      rewrite /T6 upd_ne; [| congruence].
      rewrite /T5 upd_ne; [| congruence].
      rewrite /T4 upd_ne; [| congruence].
      rewrite /T3 upd_ne; [| congruence].
      rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [| congruence].
      apply Hthr; assumption. }
    iSpecialize ("Hcont" $! CID8 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! T7 with "[%] Hcg Hpc").
    split; [| exact HT7a0].
    unfold callee_saved.
    split; [exact HT7sp|].
    split; [exact HT7s0|].
    split; [exact HT7s1|].
    split; [exact HT7s2|].
    split; [exact HT7s3|].
    split; [exact HT7s4|].
    split; [apply Hthr7; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr7; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr7; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr7; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr7; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr7; vm_compute; first [reflexivity | discriminate]|].
    apply Hthr7; vm_compute; first [reflexivity | discriminate].
  Qed.

End EitherCopyEpilogue.

(* ===================================================================== *)
(*  either_copyout                                                        *)
(* ===================================================================== *)
Module EitherCopyoutProof (Myproc : MYPROC) (Copyout : COPYOUT) (Memmove : MEMMOVE)
  : EITHER_COPYOUT.

Section ProofEitherCopyout.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).

  Lemma wp_either_copyout_sconf (γa : gname) (γf : gname)
      (m : regfile) (av lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (user : bool) (len : nat)
      (src_bytes dst_olds : nat -> bv 8) (b : bool)
    : wp_either_copyout_sconf_body γa γf m av lvl eb p C pid V user len
        src_bytes dst_olds b.
  Proof.
    cbv beta delta [wp_either_copyout_sconf_body].
    intros pcE dst src ret_tgt Hav Hflag Hlenw Hlen Hlvl.
    unfold either_copyout_stack in Hav.
    set (sp0 := m !!! Regidx csp_rs1).
    set (ra0 := m !!! Regidx Rra).
    set (s00 := m !!! Regidx Rs0).
    set (s10 := m !!! Regidx Rs1).
    set (s20 := m !!! Regidx Rs2).
    set (s30 := m !!! Regidx Rs3).
    set (s40 := m !!! Regidx Rs4).
    set (uw  := m !!! Regidx Ra0).
    iIntros "Hcg Hcpu #Htext Hpc #Henv Hsrc Hres Hcont".
    iPoseProof (eco_00 with "Htext") as "Hi00".
    iPoseProof (eco_02 with "Htext") as "Hi02".
    iPoseProof (eco_04 with "Htext") as "Hi04".
    iPoseProof (eco_06 with "Htext") as "Hi06".
    iPoseProof (eco_08 with "Htext") as "Hi08".
    iPoseProof (eco_0a with "Htext") as "Hi0a".
    iPoseProof (eco_0c with "Htext") as "Hi0c".
    iPoseProof (eco_0e with "Htext") as "Hi0e".
    iPoseProof (eco_10 with "Htext") as "Hi10".
    iPoseProof (eco_12 with "Htext") as "Hi12".
    iPoseProof (eco_14 with "Htext") as "Hi14".
    iPoseProof (eco_16 with "Htext") as "Hi16".
    iPoseProof (eco_18 with "Htext") as "Hi18".
    iPoseProof (eco_1c with "Htext") as "Hi1c".
    iPoseProof (eco_1e with "Htext") as "Hi1e".
    iPoseProof (eco_20 with "Htext") as "Hi20".
    iPoseProof (eco_22 with "Htext") as "Hi22".
    iPoseProof (eco_24 with "Htext") as "Hi24".
    iPoseProof (eco_26 with "Htext") as "Hi26".
    iPoseProof (eco_28 with "Htext") as "Hi28".
    iPoseProof (eco_2c with "Htext") as "Hi2c".
    iPoseProof (eco_2e with "Htext") as "Hi2e".
    iPoseProof (eco_30 with "Htext") as "Hi30".
    iPoseProof (eco_32 with "Htext") as "Hi32".
    iPoseProof (eco_34 with "Htext") as "Hi34".
    iPoseProof (eco_36 with "Htext") as "Hi36".
    iPoseProof (eco_38 with "Htext") as "Hi38".
    iPoseProof (eco_3a with "Htext") as "Hi3a".
    iPoseProof (eco_3c with "Htext") as "Hi3c".
    iPoseProof (eco_40 with "Htext") as "Hi40".
    iPoseProof (eco_42 with "Htext") as "Hi42".
    iPoseProof (eco_44 with "Htext") as "Hi44".
    iPoseProof (eco_48 with "Htext") as "Hi48".
    iPoseProof (eco_4a with "Htext") as "Hi4a".
    (* ---- +0x00: c.addi16sp sp,-48 (frame push) ---- *)
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) m av 6 b
              ltac:(lia) (stk_push_48 sp0) with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
              (add_vec (m !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with R1.
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /R1 upd_eq; apply stk_push_48).
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & _)".
    iDestruct "S1" as (u1) "Hk1". iDestruct "S2" as (u2) "Hk2".
    iDestruct "S3" as (u3) "Hk3". iDestruct "S4" as (u4) "Hk4".
    iDestruct "S5" as (u5) "Hk5". iDestruct "S6" as (u6) "Hk6".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb5 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb6 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* ---- +0x02 .. +0x0c: save ra / s0 / s1 / s2 / s3 / s4 ---- *)
    iEval (rewrite -Hb1) in "Hk1".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x02)) (mword_of_int 5 : mword 6) Rra
              R1 (av - 6)%nat u1 b with "Hcg Hpc Hi02 Hk1 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hk1".
    iEval (rewrite Hb1) in "Hk1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iEval (rewrite -Hb2) in "Hk2".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x04)) (mword_of_int 4 : mword 6) Rs0
              R1 (av - 6)%nat u2 b with "Hcg Hpc Hi04 Hk2 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc Hk2".
    iEval (rewrite Hb2) in "Hk2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iEval (rewrite -Hb3) in "Hk3".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x06)) (mword_of_int 3 : mword 6) Rs1
              R1 (av - 6)%nat u3 b with "Hcg Hpc Hi06 Hk3 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc Hk3".
    iEval (rewrite Hb3) in "Hk3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iEval (rewrite -Hb4) in "Hk4".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x08)) (mword_of_int 2 : mword 6) Rs2
              R1 (av - 6)%nat u4 b with "Hcg Hpc Hi08 Hk4 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc Hk4".
    iEval (rewrite Hb4) in "Hk4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    iEval (rewrite -Hb5) in "Hk5".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x0a)) (mword_of_int 1 : mword 6) Rs3
              R1 (av - 6)%nat u5 b with "Hcg Hpc Hi0a Hk5 [-]").
    iIntros (CID6 Hs6) "Hcg Hpc Hk5".
    iEval (rewrite Hb5) in "Hk5".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    iEval (rewrite -Hb6) in "Hk6".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x0c)) (mword_of_int 0 : mword 6) Rs4
              R1 (av - 6)%nat u6 b with "Hcg Hpc Hi0c Hk6 [-]").
    iIntros (CID7 Hs7) "Hcg Hpc Hk6".
    iEval (rewrite Hb6) in "Hk6".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* name the six saved values *)
    assert (HR1ra : R1 !!! Regidx Rra = ra0) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1s0 : R1 !!! Regidx Rs0 = s00) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1s1 : R1 !!! Regidx Rs1 = s10) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1s2 : R1 !!! Regidx Rs2 = s20) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1s3 : R1 !!! Regidx Rs3 = s30) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1s4 : R1 !!! Regidx Rs4 = s40) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite (rget_ne (CID := CID1) R1 Rra ltac:(vm_compute; discriminate)) HR1ra) in "Hk1".
    iEval (rewrite (rget_ne (CID := CID2) R1 Rs0 ltac:(vm_compute; discriminate)) HR1s0) in "Hk2".
    iEval (rewrite (rget_ne (CID := CID3) R1 Rs1 ltac:(vm_compute; discriminate)) HR1s1) in "Hk3".
    iEval (rewrite (rget_ne (CID := CID4) R1 Rs2 ltac:(vm_compute; discriminate)) HR1s2) in "Hk4".
    iEval (rewrite (rget_ne (CID := CID5) R1 Rs3 ltac:(vm_compute; discriminate)) HR1s3) in "Hk5".
    iEval (rewrite (rget_ne (CID := CID6) R1 Rs4 ltac:(vm_compute; discriminate)) HR1s4) in "Hk6".
    (* ---- +0x0e: c.addi4spn s0,sp,48 (s0's VALUE is never read) ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x0e))
              (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) Rs0 R1 (av - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    change (<[Regidx Rs0 := regval_into_reg
              (add_vec (R1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1) with R2.
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* ---- +0x10: c.mv s1,a0 -- s1 := user_dst ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x10)) Rs1 Ra0 R2 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (R3 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    change (<[Regidx Rs1 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2) with R3.
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* ---- +0x12: c.mv s4,a1 -- s4 := dst ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x12)) Rs4 Ra1 R3 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 [-]").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (R4 := <[Regidx Rs4 := regval_into_reg (add_vec zero_reg (R3 !!! Regidx Ra1))]> R3).
    change (<[Regidx Rs4 := regval_into_reg (add_vec zero_reg (R3 !!! Regidx Ra1))]> R3) with R4.
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* ---- +0x14: c.mv s3,a2 -- s3 := src ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x14)) Rs3 Ra2 R4 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [-]").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (R5 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (R4 !!! Regidx Ra2))]> R4).
    change (<[Regidx Rs3 := regval_into_reg (add_vec zero_reg (R4 !!! Regidx Ra2))]> R4) with R5.
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* ---- +0x16: c.mv s2,a3 -- s2 := len ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x16)) Rs2 Ra3 R5 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [-]").
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (R6 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (R5 !!! Regidx Ra3))]> R5).
    change (<[Regidx Rs2 := regval_into_reg (add_vec zero_reg (R5 !!! Regidx Ra3))]> R5) with R6.
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x18))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* what the four [c.mv]s parked *)
    assert (HR2a0 : R2 !!! Regidx Ra0 = uw).
    { rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [reflexivity | reg_neq]. }
    assert (HR3s1 : R3 !!! Regidx Rs1 = uw)
      by (rewrite /R3 upd_eq HR2a0; apply add_vec_zero_l).
    assert (HR3a1 : R3 !!! Regidx Ra1 = dst).
    { rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq].
      rewrite /R1 upd_ne; [reflexivity | reg_neq]. }
    assert (HR4s4 : R4 !!! Regidx Rs4 = dst)
      by (rewrite /R4 upd_eq HR3a1; apply add_vec_zero_l).
    assert (HR4a2 : R4 !!! Regidx Ra2 = src).
    { rewrite /R4 upd_ne; [| reg_neq]. rewrite /R3 upd_ne; [| reg_neq].
      rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [reflexivity | reg_neq]. }
    assert (HR5s3 : R5 !!! Regidx Rs3 = src)
      by (rewrite /R5 upd_eq HR4a2; apply add_vec_zero_l).
    assert (HR5a3 : R5 !!! Regidx Ra3 = (mword_of_int (Z.of_nat len) : mword 64)).
    { rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
      rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq].
      rewrite /R1 upd_ne; [exact Hlenw | reg_neq]. }
    assert (HR6s2 : R6 !!! Regidx Rs2 = (mword_of_int (Z.of_nat len) : mword 64))
      by (rewrite /R6 upd_eq HR5a3; apply add_vec_zero_l).
    assert (HR6s1 : R6 !!! Regidx Rs1 = uw).
    { rewrite /R6 upd_ne; [| reg_neq]. rewrite /R5 upd_ne; [| reg_neq].
      rewrite /R4 upd_ne; [exact HR3s1 | reg_neq]. }
    assert (HR6s3 : R6 !!! Regidx Rs3 = src)
      by (rewrite /R6 upd_ne; [exact HR5s3 | reg_neq]).
    assert (HR6s4 : R6 !!! Regidx Rs4 = dst).
    { rewrite /R6 upd_ne; [| reg_neq]. rewrite /R5 upd_ne; [exact HR4s4 | reg_neq]. }
    assert (HR6sp : R6 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /R6 upd_ne; [| reg_neq]. rewrite /R5 upd_ne; [| reg_neq].
      rewrite /R4 upd_ne; [| reg_neq]. rewrite /R3 upd_ne; [| reg_neq].
      rewrite /R2 upd_ne; [exact HR1sp | reg_neq]. }
    (* ---- +0x18: jal ra,myproc ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x18))
              Rra (mword_of_int 2094674 : mword 21) R6 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi18 [-]").
    iIntros (CID13 Hs13) "Hcg Hpc".
    set (R7 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x18) : mword 64) 4)]> R6).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x18) : mword 64) 4)]> R6) with R7.
    assert (Hjmp : add_vec (mword_of_int (KernelSyms.either_copyout + 0x18) : mword 64)
                     (sign_extend' 64 (mword_of_int 2094674 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    assert (HR7ra : R7 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x18) : mword 64) 4)
      by (rewrite /R7 upd_eq; reflexivity).
    assert (HR7sp : R7 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /R7 upd_ne; [exact HR6sp | reg_neq]).
    assert (HR7s1 : R7 !!! Regidx Rs1 = uw)
      by (rewrite /R7 upd_ne; [exact HR6s1 | reg_neq]).
    assert (HR7s2 : R7 !!! Regidx Rs2 = (mword_of_int (Z.of_nat len) : mword 64))
      by (rewrite /R7 upd_ne; [exact HR6s2 | reg_neq]).
    assert (HR7s3 : R7 !!! Regidx Rs3 = src)
      by (rewrite /R7 upd_ne; [exact HR6s3 | reg_neq]).
    assert (HR7s4 : R7 !!! Regidx Rs4 = dst)
      by (rewrite /R7 upd_ne; [exact HR6s4 | reg_neq]).
    (* ---- myproc(): a0 = p ---- *)
    (* [Hcpu] rode through the leaf steps untouched (only [Hcg]/[Hpc] are part
       of an ordinary leaf's own footprint), so it is still anchored at the
       ENTRY hart -- re-anchor it at [CID13] before crossing into myproc. *)
    iDestruct (cpu_own_transport CID CID13 lvl eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Myproc.wp_myproc_sconf R7 (av - 6)%nat lvl eb p C b
              Hlvl ltac:(lia) with "Hcg Hcpu Htext Hpc [-]").
    iIntros (CID14 Hs14 ms Am) "%Hms Hcg Hcpu Hpc %HcsA".
    destruct HcsA as [HcsA HAa0].
    assert (Hpc1c : ret_pc (R7 !!! Regidx Rra) = mword_of_int (KernelSyms.either_copyout + 0x1c))
      by (rewrite HR7ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    assert (HAsp : Am !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)); exact HR7sp).
    assert (HAs1 : Am !!! Regidx Rs1 = uw)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HR7s1).
    assert (HAs2 : Am !!! Regidx Rs2 = (mword_of_int (Z.of_nat len) : mword 64))
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 18) ltac:(vm_compute; reflexivity)); exact HR7s2).
    assert (HAs3 : Am !!! Regidx Rs3 = src)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 19) ltac:(vm_compute; reflexivity)); exact HR7s3).
    assert (HAs4 : Am !!! Regidx Rs4 = dst)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 20) ltac:(vm_compute; reflexivity)); exact HR7s4).
    (* the residual threading fact every arm hands to [ec_epi] *)
    assert (HthrA : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 ->
              Am !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18 N19 N20.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite (callee_saved_lookup HcsA r Hr).
      rewrite /R7 upd_ne; [| congruence].
      rewrite /R6 upd_ne; [| congruence].
      rewrite /R5 upd_ne; [| congruence].
      rewrite /R4 upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [| congruence]. reflexivity. }
    (* the pc-successor equations [ec_epi] takes *)
    assert (Hq2e : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x2e))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hq30 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x30))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hq32 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hq34 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hq36 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x34) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x36))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hq38 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x36) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x38))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hq3a : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x38) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x3a))
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- +0x1c: c.beqz s1 -- the flag decides the arm ---- *)
    destruct user.
    - (* ================= user_dst != 0: copyout ================= *)
      assert (Hnz : eq_vec (Am !!! Regidx Rs1) zero_reg = false)
        by (rewrite HAs1; exact Hflag).
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x1c)) (mword_of_int 16 : mword 8)
                (Cregidx (mword_of_int 1)) Rs1 Am (av - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hnz
                with "Hcg Hpc Hi1c [-]").
      iIntros (CID15 Hs15) "Hcg Hpc".
      assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x1e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1e) in "Hpc".
      (* the ONE borrow out of [proc_priv] *)
      iDestruct (proc_priv_core_sz_bound with "Hres") as %Hszb.
      iDestruct (proc_priv_core_copy with "Hres") as "(Hszc & Hptc & Hpt & Hpback)".
      (* ---- +0x1e: c.mv a4,s2 -- len (the psz shifted every argument down) ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x1e)) Ra4 Rs2 Am (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi1e [-]").
      iIntros (CID16 Hs16) "Hcg Hpc".
      set (U1 := <[Regidx Ra4 := regval_into_reg (add_vec zero_reg (Am !!! Regidx Rs2))]> Am).
      change (<[Regidx Ra4 := regval_into_reg (add_vec zero_reg (Am !!! Regidx Rs2))]> Am) with U1.
      assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x20))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp20) in "Hpc".
      (* ---- +0x20: c.mv a3,s3 -- src ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x20)) Ra3 Rs3 U1 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi20 [-]").
      iIntros (CID17 Hs17) "Hcg Hpc".
      set (U2 := <[Regidx Ra3 := regval_into_reg (add_vec zero_reg (U1 !!! Regidx Rs3))]> U1).
      change (<[Regidx Ra3 := regval_into_reg (add_vec zero_reg (U1 !!! Regidx Rs3))]> U1) with U2.
      assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x22))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      (* ---- +0x22: c.mv a2,s4 -- dstva ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x22)) Ra2 Rs4 U2 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi22 [-]").
      iIntros (CID18 Hs18) "Hcg Hpc".
      set (U3 := <[Regidx Ra2 := regval_into_reg (add_vec zero_reg (U2 !!! Regidx Rs4))]> U2).
      change (<[Regidx Ra2 := regval_into_reg (add_vec zero_reg (U2 !!! Regidx Rs4))]> U2) with U3.
      assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x24))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      assert (HU3a0 : U3 !!! Regidx Ra0 = p).
      { rewrite /U3 upd_ne; [| reg_neq]. rewrite /U2 upd_ne; [| reg_neq].
        rewrite /U1 upd_ne; [exact HAa0 | reg_neq]. }
      (* ---- +0x24: c.ld a1,72(a0) -- a1 := p->sz, copyout's NEW psz ---- *)
      assert (Hszaddr : add_vec (U3 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 72 : mword 12))
                        = p_sz p)
        by (rewrite HU3a0; reflexivity).
      iEval (rewrite -Hszaddr) in "Hszc".
      iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x24)) Ra1 Ra0
                (mword_of_int 72 : mword 12) U3 (av - 6)%nat (pv_sz V) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi24 Hszc [-]").
      iIntros (CID18b Hs18b) "Hcg Hpc Hszc".
      iEval (rewrite Hszaddr) in "Hszc".
      set (Uz := <[Regidx Ra1 := regval_into_reg (pv_sz V)]> U3).
      change (<[Regidx Ra1 := regval_into_reg (pv_sz V)]> U3) with Uz.
      assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x26))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      assert (HUza0 : Uz !!! Regidx Ra0 = p)
        by (rewrite /Uz upd_ne; [exact HU3a0 | reg_neq]).
      (* ---- +0x26: c.ld a0,80(a0) -- a0 := p->pagetable ---- *)
      assert (Hptaddr : add_vec (Uz !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 80 : mword 12))
                        = p_pagetable p)
        by (rewrite HUza0; reflexivity).
      iEval (rewrite -Hptaddr) in "Hptc".
      iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x26)) Ra0 Ra0
                (mword_of_int 80 : mword 12) Uz (av - 6)%nat (page_base (ud_root (pv_upt V))) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi26 Hptc [-]").
      iIntros (CID19 Hs19) "Hcg Hpc Hptc".
      iEval (rewrite Hptaddr) in "Hptc".
      set (U4 := <[Regidx Ra0 := regval_into_reg (page_base (ud_root (pv_upt V)))]> Uz).
      change (<[Regidx Ra0 := regval_into_reg (page_base (ud_root (pv_upt V)))]> Uz) with U4.
      assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x28))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp28) in "Hpc".
      (* ---- +0x28: jal ra,copyout ---- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x28))
                Rra (mword_of_int 2093692 : mword 21) U4 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi28 [-]").
      iIntros (CID20 Hs20) "Hcg Hpc".
      set (U5 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x28) : mword 64) 4)]> U4).
      change (<[Regidx Rra := regval_into_reg
                (add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x28) : mword 64) 4)]> U4) with U5.
      assert (Hjco : add_vec (mword_of_int (KernelSyms.either_copyout + 0x28) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093692 : mword 21)) = mword_of_int KernelSyms.copyout)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjco) in "Hpc".
      assert (HU5ra : U5 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x28) : mword 64) 4)
        by (rewrite /U5 upd_eq; reflexivity).
      assert (HU5a0 : U5 !!! Regidx Ra0 = page_base (ud_root (pv_upt V))).
      { rewrite /U5 upd_ne; [| reg_neq]. rewrite /U4 upd_eq. reflexivity. }
      assert (HU5a1 : U5 !!! Regidx Ra1 = pv_sz V).
      { rewrite /U5 upd_ne; [| reg_neq]. rewrite /U4 upd_ne; [| reg_neq].
        rewrite /Uz upd_eq. reflexivity. }
      assert (HU5a3 : U5 !!! Regidx Ra3 = src).
      { rewrite /U5 upd_ne; [| reg_neq]. rewrite /U4 upd_ne; [| reg_neq].
        rewrite /Uz upd_ne; [| reg_neq].
        rewrite /U3 upd_ne; [| reg_neq]. rewrite /U2 upd_eq.
        rewrite /U1 upd_ne; [| reg_neq]. rewrite HAs3. apply add_vec_zero_l. }
      assert (HU5a4 : U5 !!! Regidx Ra4 = (mword_of_int (Z.of_nat len) : mword 64)).
      { rewrite /U5 upd_ne; [| reg_neq]. rewrite /U4 upd_ne; [| reg_neq].
        rewrite /Uz upd_ne; [| reg_neq].
        rewrite /U3 upd_ne; [| reg_neq]. rewrite /U2 upd_ne; [| reg_neq].
        rewrite /U1 upd_eq. rewrite HAs2. apply add_vec_zero_l. }
      assert (HU5sp : U5 !!! Regidx csp_rs1 = pa_stk sp0 6).
      { rewrite /U5 upd_ne; [| reg_neq]. rewrite /U4 upd_ne; [| reg_neq].
        rewrite /Uz upd_ne; [| reg_neq].
        rewrite /U3 upd_ne; [| reg_neq]. rewrite /U2 upd_ne; [| reg_neq].
        rewrite /U1 upd_ne; [exact HAsp | reg_neq]. }
      assert (HthrU5 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 ->
                U5 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18 N19 N20.
        assert (N1 : r <> mword_of_int 1)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N11 : r <> mword_of_int 11)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N12 : r <> mword_of_int 12)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N13 : r <> mword_of_int 13)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N14 : r <> mword_of_int 14)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /U5 upd_ne; [| congruence].
        rewrite /U4 upd_ne; [| congruence].
        rewrite /Uz upd_ne; [| congruence].
        rewrite /U3 upd_ne; [| congruence].
        rewrite /U2 upd_ne; [| congruence].
        rewrite /U1 upd_ne; [| congruence]. apply HthrA; assumption. }
      (* copyout's frame is 14 slots, so its budget is 52, not copyin's 50
         (SpecCopyout.v).  [either_copyout_stack] is still 56 = 6 + 50, which
         is two short -- see this file's header. *)
      assert (HK52 : (52 <= av - 6)%nat) by lia.
      iEval (rewrite -HU5a3) in "Hsrc".
      (* [Hcpu] rode through untouched since myproc handed it back at [CID14];
         re-anchor it at [CID20] before crossing into copyout. *)
      iDestruct (cpu_own_transport CID14 CID20 lvl eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iApply (Copyout.wp_copyout_sconf γa U5 (pv_upt V) (pv_sz V) len src_bytes
                (av - 6)%nat lvl eb p C b
                HK52 HU5a0 HU5a1 HU5a4 Hlen Hszb Hlvl
                with "Hcg Hcpu Htext Hpc Hpt Henv Hsrc [-]").
      iIntros (CID21 Hs21 mr P') "Hcg Hcpu Hpc Hpt Hsrc %Hcsr %Hext %Hret".
      assert (Hpc2c : ret_pc (U5 !!! Regidx Rra) = mword_of_int (KernelSyms.either_copyout + 0x2c))
        by (rewrite HU5ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc2c) in "Hpc".
      iEval (rewrite HU5a3) in "Hsrc".
      iAssert (⌜uptd_ext_sz (pv_sz V) (pv_upt V) P'⌝)%I as "#Hxe"; [iPureIntro; exact Hext|].
      iDestruct ("Hpback" $! P' with "Hxe Hszc Hptc Hpt") as "Hres".
      assert (Hrsp : mr !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite (callee_saved_lookup Hcsr csp_rs1 ltac:(vm_compute; reflexivity)); exact HU5sp).
      assert (Hthrr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 ->
                mr !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18 N19 N20.
        rewrite (callee_saved_lookup Hcsr r Hr). apply HthrU5; assumption. }
      iApply (ec_epi (mword_of_int (KernelSyms.either_copyout + 0x2c)) (mword_of_int (KernelSyms.either_copyout + 0x2e))
                (mword_of_int (KernelSyms.either_copyout + 0x30)) (mword_of_int (KernelSyms.either_copyout + 0x32))
                (mword_of_int (KernelSyms.either_copyout + 0x34)) (mword_of_int (KernelSyms.either_copyout + 0x36))
                (mword_of_int (KernelSyms.either_copyout + 0x38)) (mword_of_int (KernelSyms.either_copyout + 0x3a))
                m mr av (mr !!! Regidx Ra0) sp0 ra0 s00 s10 s20 s30 s40 p b
                ltac:(lia) Hq2e Hq30 Hq32 Hq34 Hq36 Hq38 Hq3a
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                Hrsp eq_refl Hthrr
                with "Hcg Hi2c Hi2e Hi30 Hi32 Hi34 Hi36 Hi38 Hi3a Hpc Hk1 Hk2 Hk3 Hk4 Hk5 Hk6 [-]").
      iIntros (CID22 Hs22 mf) "[%Hcsf %Hfa0] Hcg Hpc".
      (* [Hcpu] rode through [ec_epi] untouched since copyout handed it back
         at [CID21]; re-anchor it at [CID22] before discharging [Hcont]. *)
      iDestruct (cpu_own_transport CID21 CID22 lvl eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iSpecialize ("Hcont" $! CID22 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "[%] Hcg Hcpu Hpc Hsrc [Hres]").
      { exact Hcsf. }
      rewrite /either_copyout_post. rewrite Hfa0.
      iSplitR; [iPureIntro; exact Hret|].
      iExists P'. iSplitR; [iPureIntro; exact (uptd_ext_sz_ext _ _ _ Hext)|]. iExact "Hres".
    - (* ================= user_dst == 0: memmove ================= *)
      assert (Hz : eq_vec (Am !!! Regidx Rs1) zero_reg = true)
        by (rewrite HAs1; exact Hflag).
      assert (Huw0 : uw = (zero_reg : mword 64))
        by (apply eq_vec_true_iff; exact Hflag).
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x1c)) (mword_of_int 16 : mword 8)
                (Cregidx (mword_of_int 1)) Rs1 Am (av - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hz
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi1c [-]").
      iApply bi.later_intro. iIntros (CID15 Hs15) "Hcg Hpc".
      assert (Hjt : add_vec (mword_of_int (KernelSyms.either_copyout + 0x1c) : mword 64)
                      (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 16 : mword 8) ('b"0"))))
                    = mword_of_int (KernelSyms.either_copyout + 0x3c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjt) in "Hpc".
      (* ---- +0x3a: sext.w a2,s2 -- the memmove count ---- *)
      iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x3c)) Ra2 Rs2
                (mword_of_int 0 : mword 12) Am (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi3c [-]").
      iIntros (CID16 Hs16) "Hcg Hpc".
      set (K1 := <[Regidx Ra2 := regval_into_reg
                    (sign_extend' 64 (subrange_vec_dec
                       (add_vec (Am !!! Regidx Rs2) (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> Am).
      change (<[Regidx Ra2 := regval_into_reg
                (sign_extend' 64 (subrange_vec_dec
                   (add_vec (Am !!! Regidx Rs2) (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> Am) with K1.
      assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x3c) : mword 64) 4 = mword_of_int (KernelSyms.either_copyout + 0x40))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      assert (HK1a2 : K1 !!! Regidx Ra2 = (mword_of_int (Z.of_nat len) : mword 64)).
      { rewrite /K1 upd_eq HAs2.
        exact (sextw_moi (Z.of_nat len) (Nat2Z.is_nonneg len) (ec_len31 len Hlen)). }
      (* ---- +0x3e: c.mv a1,s3 -- src ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x40)) Ra1 Rs3 K1 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi40 [-]").
      iIntros (CID17 Hs17) "Hcg Hpc".
      set (K2 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (K1 !!! Regidx Rs3))]> K1).
      change (<[Regidx Ra1 := regval_into_reg (add_vec zero_reg (K1 !!! Regidx Rs3))]> K1) with K2.
      assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x42))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      (* ---- +0x40: c.mv a0,s4 -- dst ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x42)) Ra0 Rs4 K2 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi42 [-]").
      iIntros (CID18 Hs18) "Hcg Hpc".
      set (K3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (K2 !!! Regidx Rs4))]> K2).
      change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (K2 !!! Regidx Rs4))]> K2) with K3.
      assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x44))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp44) in "Hpc".
      (* ---- +0x42: jal ra,memmove ---- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x44))
                Rra (mword_of_int 2091558 : mword 21) K3 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi44 [-]").
      iIntros (CID19 Hs19) "Hcg Hpc".
      set (K4 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x44) : mword 64) 4)]> K3).
      change (<[Regidx Rra := regval_into_reg
                (add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x44) : mword 64) 4)]> K3) with K4.
      assert (Hjmm : add_vec (mword_of_int (KernelSyms.either_copyout + 0x44) : mword 64)
                       (sign_extend' 64 (mword_of_int 2091558 : mword 21)) = mword_of_int KernelSyms.memmove)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjmm) in "Hpc".
      assert (HK4ra : K4 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x44) : mword 64) 4)
        by (rewrite /K4 upd_eq; reflexivity).
      assert (HK4a0 : K4 !!! Regidx Ra0 = dst).
      { rewrite /K4 upd_ne; [| reg_neq]. rewrite /K3 upd_eq.
        rewrite /K2 upd_ne; [| reg_neq]. rewrite /K1 upd_ne; [| reg_neq].
        rewrite HAs4. apply add_vec_zero_l. }
      assert (HK4a1 : K4 !!! Regidx Ra1 = src).
      { rewrite /K4 upd_ne; [| reg_neq]. rewrite /K3 upd_ne; [| reg_neq].
        rewrite /K2 upd_eq. rewrite /K1 upd_ne; [| reg_neq].
        rewrite HAs3. apply add_vec_zero_l. }
      assert (HK4a2 : K4 !!! Regidx Ra2 = (mword_of_int (Z.of_nat len) : mword 64)).
      { rewrite /K4 upd_ne; [| reg_neq]. rewrite /K3 upd_ne; [| reg_neq].
        rewrite /K2 upd_ne; [exact HK1a2 | reg_neq]. }
      assert (HK4sp : K4 !!! Regidx csp_rs1 = pa_stk sp0 6).
      { rewrite /K4 upd_ne; [| reg_neq]. rewrite /K3 upd_ne; [| reg_neq].
        rewrite /K2 upd_ne; [| reg_neq]. rewrite /K1 upd_ne; [exact HAsp | reg_neq]. }
      assert (HK4s1 : K4 !!! Regidx Rs1 = uw).
      { rewrite /K4 upd_ne; [| reg_neq]. rewrite /K3 upd_ne; [| reg_neq].
        rewrite /K2 upd_ne; [| reg_neq]. rewrite /K1 upd_ne; [exact HAs1 | reg_neq]. }
      assert (HthrK4 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 ->
                K4 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18 N19 N20.
        assert (N1 : r <> mword_of_int 1)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N11 : r <> mword_of_int 11)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N12 : r <> mword_of_int 12)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /K4 upd_ne; [| congruence].
        rewrite /K3 upd_ne; [| congruence].
        rewrite /K2 upd_ne; [| congruence].
        rewrite /K1 upd_ne; [| congruence]. apply HthrA; assumption. }
      iEval (rewrite -HK4a1) in "Hsrc".
      iEval (rewrite -HK4a0) in "Hres".
      iApply (Memmove.wp_memmove_sconf K4 (av - 6)%nat len src_bytes dst_olds b p
                ltac:(lia) (ec_len32 len Hlen) HK4a2
                with "Hcg Htext Hpc Hsrc Hres [-]").
      iIntros (CID20 Hs20 mfin) "Hcg Hpc Hsrc Hdst %Hmma0 %Hcsmm".
      assert (Hpc48 : ret_pc (K4 !!! Regidx Rra) = mword_of_int (KernelSyms.either_copyout + 0x48))
        by (rewrite HK4ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc48) in "Hpc".
      iEval (rewrite HK4a1) in "Hsrc".
      iEval (rewrite HK4a0) in "Hdst".
      (* ---- +0x46: c.mv a0,s1 -- the flag, which the beqz proved is 0 ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x48)) Ra0 Rs1 mfin (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi48 [-]").
      iIntros (CID21 Hs21) "Hcg Hpc".
      set (L1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mfin !!! Regidx Rs1))]> mfin).
      change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mfin !!! Regidx Rs1))]> mfin) with L1.
      assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.either_copyout + 0x48) : mword 64) 2 = mword_of_int (KernelSyms.either_copyout + 0x4a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4a) in "Hpc".
      assert (Hmms1 : mfin !!! Regidx Rs1 = uw)
        by (rewrite (callee_saved_lookup Hcsmm (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HK4s1).
      assert (HL1a0 : L1 !!! Regidx Ra0 = (mword_of_int 0 : mword 64)).
      { rewrite /L1 upd_eq Hmms1 Huw0 add_vec_zero_l. exact ec_zero_reg_moi. }
      (* ---- +0x48: c.j -0x1e -- into the shared epilogue ---- *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.either_copyout + 0x4a))
                (sign_extend' 21 (concat_vec (mword_of_int 2033 : mword 11) ('b"0")))
                L1 (av - 6)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi4a [-]").
      iIntros (CID22 Hs22). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Hjc : add_vec (mword_of_int (KernelSyms.either_copyout + 0x4a) : mword 64)
                      (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2033 : mword 11) ('b"0"))))
                    = mword_of_int (KernelSyms.either_copyout + 0x2c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjc) in "Hpc".
      assert (HL1sp : L1 !!! Regidx csp_rs1 = pa_stk sp0 6).
      { rewrite /L1 upd_ne; [| reg_neq].
        rewrite (callee_saved_lookup Hcsmm csp_rs1 ltac:(vm_compute; reflexivity)). exact HK4sp. }
      assert (HthrL1 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 ->
                L1 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18 N19 N20.
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /L1 upd_ne; [| congruence].
        rewrite (callee_saved_lookup Hcsmm r Hr). apply HthrK4; assumption. }
      iApply (ec_epi (mword_of_int (KernelSyms.either_copyout + 0x2c)) (mword_of_int (KernelSyms.either_copyout + 0x2e))
                (mword_of_int (KernelSyms.either_copyout + 0x30)) (mword_of_int (KernelSyms.either_copyout + 0x32))
                (mword_of_int (KernelSyms.either_copyout + 0x34)) (mword_of_int (KernelSyms.either_copyout + 0x36))
                (mword_of_int (KernelSyms.either_copyout + 0x38)) (mword_of_int (KernelSyms.either_copyout + 0x3a))
                m L1 av (mword_of_int 0 : mword 64) sp0 ra0 s00 s10 s20 s30 s40 p b
                ltac:(lia) Hq2e Hq30 Hq32 Hq34 Hq36 Hq38 Hq3a
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                HL1sp HL1a0 HthrL1
                with "Hcg Hi2c Hi2e Hi30 Hi32 Hi34 Hi36 Hi38 Hi3a Hpc Hk1 Hk2 Hk3 Hk4 Hk5 Hk6 [-]").
      iIntros (CID23 Hs23 mf) "[%Hcsf %Hfa0] Hcg Hpc".
      (* [Hcpu] rode through memmove and [ec_epi] untouched since myproc
         handed it back at [CID14]; re-anchor it at [CID23] before
         discharging [Hcont]. *)
      iDestruct (cpu_own_transport CID14 CID23 lvl eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iSpecialize ("Hcont" $! CID23 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "[%] Hcg Hcpu Hpc Hsrc [Hdst]").
      { exact Hcsf. }
      rewrite /either_copyout_post. rewrite Hfa0.
      iSplitR; [iPureIntro; reflexivity|]. iExact "Hdst".
  Qed.

End ProofEitherCopyout.

End EitherCopyoutProof.

(* ===================================================================== *)
(*  either_copyin -- the same block, a0/a1 swapped and copyin below it.    *)
(* ===================================================================== *)
Module EitherCopyinProof (Myproc : MYPROC) (Copyin : COPYIN) (Memmove : MEMMOVE)
  : EITHER_COPYIN.

Section ProofEitherCopyin.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).

  Lemma wp_either_copyin_sconf (γa : gname) (γf : gname)
      (m : regfile) (av lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (user : bool) (len : nat)
      (src_bytes dst_olds : nat -> bv 8) (b : bool)
    : wp_either_copyin_sconf_body γa γf m av lvl eb p C pid V user len
        src_bytes dst_olds b.
  Proof.
    cbv beta delta [wp_either_copyin_sconf_body].
    intros pcE dst src ret_tgt Hav Hflag Hlenw Hlen Hlvl.
    unfold either_copyin_stack in Hav.
    set (sp0 := m !!! Regidx csp_rs1).
    set (ra0 := m !!! Regidx Rra).
    set (s00 := m !!! Regidx Rs0).
    set (s10 := m !!! Regidx Rs1).
    set (s20 := m !!! Regidx Rs2).
    set (s30 := m !!! Regidx Rs3).
    set (s40 := m !!! Regidx Rs4).
    set (uw  := m !!! Regidx Ra1).
    iIntros "Hcg Hcpu #Htext Hpc #Henv Hdst Hres Hcont".
    iPoseProof (eci_00 with "Htext") as "Hi00".
    iPoseProof (eci_02 with "Htext") as "Hi02".
    iPoseProof (eci_04 with "Htext") as "Hi04".
    iPoseProof (eci_06 with "Htext") as "Hi06".
    iPoseProof (eci_08 with "Htext") as "Hi08".
    iPoseProof (eci_0a with "Htext") as "Hi0a".
    iPoseProof (eci_0c with "Htext") as "Hi0c".
    iPoseProof (eci_0e with "Htext") as "Hi0e".
    iPoseProof (eci_10 with "Htext") as "Hi10".
    iPoseProof (eci_12 with "Htext") as "Hi12".
    iPoseProof (eci_14 with "Htext") as "Hi14".
    iPoseProof (eci_16 with "Htext") as "Hi16".
    iPoseProof (eci_18 with "Htext") as "Hi18".
    iPoseProof (eci_1c with "Htext") as "Hi1c".
    iPoseProof (eci_1e with "Htext") as "Hi1e".
    iPoseProof (eci_20 with "Htext") as "Hi20".
    iPoseProof (eci_22 with "Htext") as "Hi22".
    iPoseProof (eci_24 with "Htext") as "Hi24".
    iPoseProof (eci_26 with "Htext") as "Hi26".
    iPoseProof (eci_28 with "Htext") as "Hi28".
    iPoseProof (eci_2c with "Htext") as "Hi2c".
    iPoseProof (eci_2e with "Htext") as "Hi2e".
    iPoseProof (eci_30 with "Htext") as "Hi30".
    iPoseProof (eci_32 with "Htext") as "Hi32".
    iPoseProof (eci_34 with "Htext") as "Hi34".
    iPoseProof (eci_36 with "Htext") as "Hi36".
    iPoseProof (eci_38 with "Htext") as "Hi38".
    iPoseProof (eci_3a with "Htext") as "Hi3a".
    iPoseProof (eci_3c with "Htext") as "Hi3c".
    iPoseProof (eci_40 with "Htext") as "Hi40".
    iPoseProof (eci_42 with "Htext") as "Hi42".
    iPoseProof (eci_44 with "Htext") as "Hi44".
    iPoseProof (eci_48 with "Htext") as "Hi48".
    iPoseProof (eci_4a with "Htext") as "Hi4a".
    (* ---- +0x00: c.addi16sp sp,-48 (frame push) ---- *)
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) m av 6 b
              ltac:(lia) (stk_push_48 sp0) with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
              (add_vec (m !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with R1.
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /R1 upd_eq; apply stk_push_48).
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & _)".
    iDestruct "S1" as (u1) "Hk1". iDestruct "S2" as (u2) "Hk2".
    iDestruct "S3" as (u3) "Hk3". iDestruct "S4" as (u4) "Hk4".
    iDestruct "S5" as (u5) "Hk5". iDestruct "S6" as (u6) "Hk6".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb5 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb6 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* ---- +0x02 .. +0x0c: save ra / s0 / s1 / s2 / s3 / s4 ---- *)
    iEval (rewrite -Hb1) in "Hk1".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x02)) (mword_of_int 5 : mword 6) Rra
              R1 (av - 6)%nat u1 b with "Hcg Hpc Hi02 Hk1 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hk1".
    iEval (rewrite Hb1) in "Hk1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iEval (rewrite -Hb2) in "Hk2".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x04)) (mword_of_int 4 : mword 6) Rs0
              R1 (av - 6)%nat u2 b with "Hcg Hpc Hi04 Hk2 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc Hk2".
    iEval (rewrite Hb2) in "Hk2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iEval (rewrite -Hb3) in "Hk3".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x06)) (mword_of_int 3 : mword 6) Rs1
              R1 (av - 6)%nat u3 b with "Hcg Hpc Hi06 Hk3 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc Hk3".
    iEval (rewrite Hb3) in "Hk3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iEval (rewrite -Hb4) in "Hk4".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x08)) (mword_of_int 2 : mword 6) Rs2
              R1 (av - 6)%nat u4 b with "Hcg Hpc Hi08 Hk4 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc Hk4".
    iEval (rewrite Hb4) in "Hk4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    iEval (rewrite -Hb5) in "Hk5".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x0a)) (mword_of_int 1 : mword 6) Rs3
              R1 (av - 6)%nat u5 b with "Hcg Hpc Hi0a Hk5 [-]").
    iIntros (CID6 Hs6) "Hcg Hpc Hk5".
    iEval (rewrite Hb5) in "Hk5".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    iEval (rewrite -Hb6) in "Hk6".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x0c)) (mword_of_int 0 : mword 6) Rs4
              R1 (av - 6)%nat u6 b with "Hcg Hpc Hi0c Hk6 [-]").
    iIntros (CID7 Hs7) "Hcg Hpc Hk6".
    iEval (rewrite Hb6) in "Hk6".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    assert (HR1ra : R1 !!! Regidx Rra = ra0) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1s0 : R1 !!! Regidx Rs0 = s00) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1s1 : R1 !!! Regidx Rs1 = s10) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1s2 : R1 !!! Regidx Rs2 = s20) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1s3 : R1 !!! Regidx Rs3 = s30) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1s4 : R1 !!! Regidx Rs4 = s40) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite (rget_ne (CID := CID1) R1 Rra ltac:(vm_compute; discriminate)) HR1ra) in "Hk1".
    iEval (rewrite (rget_ne (CID := CID2) R1 Rs0 ltac:(vm_compute; discriminate)) HR1s0) in "Hk2".
    iEval (rewrite (rget_ne (CID := CID3) R1 Rs1 ltac:(vm_compute; discriminate)) HR1s1) in "Hk3".
    iEval (rewrite (rget_ne (CID := CID4) R1 Rs2 ltac:(vm_compute; discriminate)) HR1s2) in "Hk4".
    iEval (rewrite (rget_ne (CID := CID5) R1 Rs3 ltac:(vm_compute; discriminate)) HR1s3) in "Hk5".
    iEval (rewrite (rget_ne (CID := CID6) R1 Rs4 ltac:(vm_compute; discriminate)) HR1s4) in "Hk6".
    (* ---- +0x0e: c.addi4spn s0,sp,48 ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x0e))
              (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) Rs0 R1 (av - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    change (<[Regidx Rs0 := regval_into_reg
              (add_vec (R1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1) with R2.
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* ---- +0x10: c.mv s4,a0 -- s4 := dst ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x10)) Rs4 Ra0 R2 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (R3 := <[Regidx Rs4 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    change (<[Regidx Rs4 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2) with R3.
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* ---- +0x12: c.mv s1,a1 -- s1 := user_src ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x12)) Rs1 Ra1 R3 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 [-]").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (R4 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (R3 !!! Regidx Ra1))]> R3).
    change (<[Regidx Rs1 := regval_into_reg (add_vec zero_reg (R3 !!! Regidx Ra1))]> R3) with R4.
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* ---- +0x14: c.mv s3,a2 -- s3 := src ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x14)) Rs3 Ra2 R4 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [-]").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (R5 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (R4 !!! Regidx Ra2))]> R4).
    change (<[Regidx Rs3 := regval_into_reg (add_vec zero_reg (R4 !!! Regidx Ra2))]> R4) with R5.
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* ---- +0x16: c.mv s2,a3 -- s2 := len ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x16)) Rs2 Ra3 R5 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [-]").
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (R6 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (R5 !!! Regidx Ra3))]> R5).
    change (<[Regidx Rs2 := regval_into_reg (add_vec zero_reg (R5 !!! Regidx Ra3))]> R5) with R6.
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x18))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* what the four [c.mv]s parked *)
    assert (HR2a0 : R2 !!! Regidx Ra0 = dst).
    { rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [reflexivity | reg_neq]. }
    assert (HR3s4 : R3 !!! Regidx Rs4 = dst)
      by (rewrite /R3 upd_eq HR2a0; apply add_vec_zero_l).
    assert (HR3a1 : R3 !!! Regidx Ra1 = uw).
    { rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq].
      rewrite /R1 upd_ne; [reflexivity | reg_neq]. }
    assert (HR4s1 : R4 !!! Regidx Rs1 = uw)
      by (rewrite /R4 upd_eq HR3a1; apply add_vec_zero_l).
    assert (HR4a2 : R4 !!! Regidx Ra2 = src).
    { rewrite /R4 upd_ne; [| reg_neq]. rewrite /R3 upd_ne; [| reg_neq].
      rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [reflexivity | reg_neq]. }
    assert (HR5s3 : R5 !!! Regidx Rs3 = src)
      by (rewrite /R5 upd_eq HR4a2; apply add_vec_zero_l).
    assert (HR5a3 : R5 !!! Regidx Ra3 = (mword_of_int (Z.of_nat len) : mword 64)).
    { rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
      rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq].
      rewrite /R1 upd_ne; [exact Hlenw | reg_neq]. }
    assert (HR6s2 : R6 !!! Regidx Rs2 = (mword_of_int (Z.of_nat len) : mword 64))
      by (rewrite /R6 upd_eq HR5a3; apply add_vec_zero_l).
    assert (HR6s1 : R6 !!! Regidx Rs1 = uw).
    { rewrite /R6 upd_ne; [| reg_neq]. rewrite /R5 upd_ne; [exact HR4s1 | reg_neq]. }
    assert (HR6s3 : R6 !!! Regidx Rs3 = src)
      by (rewrite /R6 upd_ne; [exact HR5s3 | reg_neq]).
    assert (HR6s4 : R6 !!! Regidx Rs4 = dst).
    { rewrite /R6 upd_ne; [| reg_neq]. rewrite /R5 upd_ne; [| reg_neq].
      rewrite /R4 upd_ne; [exact HR3s4 | reg_neq]. }
    assert (HR6sp : R6 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /R6 upd_ne; [| reg_neq]. rewrite /R5 upd_ne; [| reg_neq].
      rewrite /R4 upd_ne; [| reg_neq]. rewrite /R3 upd_ne; [| reg_neq].
      rewrite /R2 upd_ne; [exact HR1sp | reg_neq]. }
    (* ---- +0x18: jal ra,myproc ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x18))
              Rra (mword_of_int 2094598 : mword 21) R6 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi18 [-]").
    iIntros (CID13 Hs13) "Hcg Hpc".
    set (R7 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x18) : mword 64) 4)]> R6).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x18) : mword 64) 4)]> R6) with R7.
    assert (Hjmp : add_vec (mword_of_int (KernelSyms.either_copyin + 0x18) : mword 64)
                     (sign_extend' 64 (mword_of_int 2094598 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    assert (HR7ra : R7 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x18) : mword 64) 4)
      by (rewrite /R7 upd_eq; reflexivity).
    assert (HR7sp : R7 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /R7 upd_ne; [exact HR6sp | reg_neq]).
    assert (HR7s1 : R7 !!! Regidx Rs1 = uw)
      by (rewrite /R7 upd_ne; [exact HR6s1 | reg_neq]).
    assert (HR7s2 : R7 !!! Regidx Rs2 = (mword_of_int (Z.of_nat len) : mword 64))
      by (rewrite /R7 upd_ne; [exact HR6s2 | reg_neq]).
    assert (HR7s3 : R7 !!! Regidx Rs3 = src)
      by (rewrite /R7 upd_ne; [exact HR6s3 | reg_neq]).
    assert (HR7s4 : R7 !!! Regidx Rs4 = dst)
      by (rewrite /R7 upd_ne; [exact HR6s4 | reg_neq]).
    (* ---- myproc(): a0 = p ---- *)
    (* [Hcpu] rode through the leaf steps untouched (only [Hcg]/[Hpc] are part
       of an ordinary leaf's own footprint), so it is still anchored at the
       ENTRY hart -- re-anchor it at [CID13] before crossing into myproc. *)
    iDestruct (cpu_own_transport CID CID13 lvl eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Myproc.wp_myproc_sconf R7 (av - 6)%nat lvl eb p C b
              Hlvl ltac:(lia) with "Hcg Hcpu Htext Hpc [-]").
    iIntros (CID14 Hs14 ms Am) "%Hms Hcg Hcpu Hpc %HcsA".
    destruct HcsA as [HcsA HAa0].
    assert (Hpc1c : ret_pc (R7 !!! Regidx Rra) = mword_of_int (KernelSyms.either_copyin + 0x1c))
      by (rewrite HR7ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    assert (HAsp : Am !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)); exact HR7sp).
    assert (HAs1 : Am !!! Regidx Rs1 = uw)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HR7s1).
    assert (HAs2 : Am !!! Regidx Rs2 = (mword_of_int (Z.of_nat len) : mword 64))
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 18) ltac:(vm_compute; reflexivity)); exact HR7s2).
    assert (HAs3 : Am !!! Regidx Rs3 = src)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 19) ltac:(vm_compute; reflexivity)); exact HR7s3).
    assert (HAs4 : Am !!! Regidx Rs4 = dst)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 20) ltac:(vm_compute; reflexivity)); exact HR7s4).
    assert (HthrA : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 ->
              Am !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18 N19 N20.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite (callee_saved_lookup HcsA r Hr).
      rewrite /R7 upd_ne; [| congruence].
      rewrite /R6 upd_ne; [| congruence].
      rewrite /R5 upd_ne; [| congruence].
      rewrite /R4 upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [| congruence]. reflexivity. }
    assert (Hq2e : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x2e))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hq30 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x30))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hq32 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hq34 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hq36 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x34) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x36))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hq38 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x36) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x38))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hq3a : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x38) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x3a))
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- +0x1c: c.beqz s1 ---- *)
    destruct user.
    - (* ================= user_src != 0: copyin ================= *)
      assert (Hnz : eq_vec (Am !!! Regidx Rs1) zero_reg = false)
        by (rewrite HAs1; exact Hflag).
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x1c)) (mword_of_int 16 : mword 8)
                (Cregidx (mword_of_int 1)) Rs1 Am (av - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hnz
                with "Hcg Hpc Hi1c [-]").
      iIntros (CID15 Hs15) "Hcg Hpc".
      assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x1e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1e) in "Hpc".
      iDestruct (proc_priv_core_sz_bound with "Hres") as %Hszb.
      iDestruct (proc_priv_core_copy with "Hres") as "(Hszc & Hptc & Hpt & Hpback)".
      (* ---- +0x1e: c.mv a4,s2 -- len (the psz shifted every argument down) ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x1e)) Ra4 Rs2 Am (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi1e [-]").
      iIntros (CID16 Hs16) "Hcg Hpc".
      set (U1 := <[Regidx Ra4 := regval_into_reg (add_vec zero_reg (Am !!! Regidx Rs2))]> Am).
      change (<[Regidx Ra4 := regval_into_reg (add_vec zero_reg (Am !!! Regidx Rs2))]> Am) with U1.
      assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x20))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp20) in "Hpc".
      (* ---- +0x20: c.mv a3,s3 -- srcva ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x20)) Ra3 Rs3 U1 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi20 [-]").
      iIntros (CID17 Hs17) "Hcg Hpc".
      set (U2 := <[Regidx Ra3 := regval_into_reg (add_vec zero_reg (U1 !!! Regidx Rs3))]> U1).
      change (<[Regidx Ra3 := regval_into_reg (add_vec zero_reg (U1 !!! Regidx Rs3))]> U1) with U2.
      assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x22))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      (* ---- +0x22: c.mv a2,s4 -- the kernel destination ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x22)) Ra2 Rs4 U2 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi22 [-]").
      iIntros (CID18 Hs18) "Hcg Hpc".
      set (U3 := <[Regidx Ra2 := regval_into_reg (add_vec zero_reg (U2 !!! Regidx Rs4))]> U2).
      change (<[Regidx Ra2 := regval_into_reg (add_vec zero_reg (U2 !!! Regidx Rs4))]> U2) with U3.
      assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x24))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      assert (HU3a0 : U3 !!! Regidx Ra0 = p).
      { rewrite /U3 upd_ne; [| reg_neq]. rewrite /U2 upd_ne; [| reg_neq].
        rewrite /U1 upd_ne; [exact HAa0 | reg_neq]. }
      (* ---- +0x24: c.ld a1,72(a0) -- a1 := p->sz, copyin's NEW psz ---- *)
      assert (Hszaddr : add_vec (U3 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 72 : mword 12))
                        = p_sz p)
        by (rewrite HU3a0; reflexivity).
      iEval (rewrite -Hszaddr) in "Hszc".
      iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x24)) Ra1 Ra0
                (mword_of_int 72 : mword 12) U3 (av - 6)%nat (pv_sz V) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi24 Hszc [-]").
      iIntros (CID18b Hs18b) "Hcg Hpc Hszc".
      iEval (rewrite Hszaddr) in "Hszc".
      set (Uz := <[Regidx Ra1 := regval_into_reg (pv_sz V)]> U3).
      change (<[Regidx Ra1 := regval_into_reg (pv_sz V)]> U3) with Uz.
      assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x26))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      assert (HUza0 : Uz !!! Regidx Ra0 = p)
        by (rewrite /Uz upd_ne; [exact HU3a0 | reg_neq]).
      (* ---- +0x26: c.ld a0,80(a0) -- a0 := p->pagetable ---- *)
      assert (Hptaddr : add_vec (Uz !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 80 : mword 12))
                        = p_pagetable p)
        by (rewrite HUza0; reflexivity).
      iEval (rewrite -Hptaddr) in "Hptc".
      iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x26)) Ra0 Ra0
                (mword_of_int 80 : mword 12) Uz (av - 6)%nat (page_base (ud_root (pv_upt V))) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi26 Hptc [-]").
      iIntros (CID19 Hs19) "Hcg Hpc Hptc".
      iEval (rewrite Hptaddr) in "Hptc".
      set (U4 := <[Regidx Ra0 := regval_into_reg (page_base (ud_root (pv_upt V)))]> Uz).
      change (<[Regidx Ra0 := regval_into_reg (page_base (ud_root (pv_upt V)))]> Uz) with U4.
      assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x28))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp28) in "Hpc".
      (* ---- +0x26: jal ra,copyin ---- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x28))
                Rra (mword_of_int 2093814 : mword 21) U4 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi28 [-]").
      iIntros (CID20 Hs20) "Hcg Hpc".
      set (U5 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x28) : mword 64) 4)]> U4).
      change (<[Regidx Rra := regval_into_reg
                (add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x28) : mword 64) 4)]> U4) with U5.
      assert (Hjci : add_vec (mword_of_int (KernelSyms.either_copyin + 0x28) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093814 : mword 21)) = mword_of_int KernelSyms.copyin)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjci) in "Hpc".
      assert (HU5ra : U5 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x28) : mword 64) 4)
        by (rewrite /U5 upd_eq; reflexivity).
      assert (HU5a0 : U5 !!! Regidx Ra0 = page_base (ud_root (pv_upt V))).
      { rewrite /U5 upd_ne; [| reg_neq]. rewrite /U4 upd_eq. reflexivity. }
      assert (HU5a1 : U5 !!! Regidx Ra1 = pv_sz V).
      { rewrite /U5 upd_ne; [| reg_neq]. rewrite /U4 upd_ne; [| reg_neq].
        rewrite /Uz upd_eq. reflexivity. }
      assert (HU5a2 : U5 !!! Regidx Ra2 = dst).
      { rewrite /U5 upd_ne; [| reg_neq]. rewrite /U4 upd_ne; [| reg_neq].
        rewrite /Uz upd_ne; [| reg_neq].
        rewrite /U3 upd_eq. rewrite /U2 upd_ne; [| reg_neq].
        rewrite /U1 upd_ne; [| reg_neq]. rewrite HAs4. apply add_vec_zero_l. }
      assert (HU5a4 : U5 !!! Regidx Ra4 = (mword_of_int (Z.of_nat len) : mword 64)).
      { rewrite /U5 upd_ne; [| reg_neq]. rewrite /U4 upd_ne; [| reg_neq].
        rewrite /Uz upd_ne; [| reg_neq].
        rewrite /U3 upd_ne; [| reg_neq]. rewrite /U2 upd_ne; [| reg_neq].
        rewrite /U1 upd_eq. rewrite HAs2. apply add_vec_zero_l. }
      assert (HU5sp : U5 !!! Regidx csp_rs1 = pa_stk sp0 6).
      { rewrite /U5 upd_ne; [| reg_neq]. rewrite /U4 upd_ne; [| reg_neq].
        rewrite /Uz upd_ne; [| reg_neq].
        rewrite /U3 upd_ne; [| reg_neq]. rewrite /U2 upd_ne; [| reg_neq].
        rewrite /U1 upd_ne; [exact HAsp | reg_neq]. }
      assert (HthrU5 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 ->
                U5 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18 N19 N20.
        assert (N1 : r <> mword_of_int 1)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N11 : r <> mword_of_int 11)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N12 : r <> mword_of_int 12)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N13 : r <> mword_of_int 13)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N14 : r <> mword_of_int 14)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /U5 upd_ne; [| congruence].
        rewrite /U4 upd_ne; [| congruence].
        rewrite /Uz upd_ne; [| congruence].
        rewrite /U3 upd_ne; [| congruence].
        rewrite /U2 upd_ne; [| congruence].
        rewrite /U1 upd_ne; [| congruence]. apply HthrA; assumption. }
      assert (HK50 : (50 <= av - 6)%nat) by lia.
      iEval (rewrite -HU5a2) in "Hdst".
      (* [Hcpu] rode through untouched since myproc handed it back at [CID14];
         re-anchor it at [CID20] before crossing into copyin. *)
      iDestruct (cpu_own_transport CID14 CID20 lvl eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iApply (Copyin.wp_copyin_sconf γa U5 (pv_upt V) (pv_sz V) len dst_olds
                (av - 6)%nat lvl eb p C b
                HK50 HU5a0 HU5a1 HU5a4 Hlen Hszb Hlvl
                with "Hcg Hcpu Htext Hpc Hpt Henv Hdst [-]").
      iIntros (CID21 Hs21 mr P' dst_new) "Hcg Hcpu Hpc Hpt Hdst %Hcsr %Hext %Hret".
      assert (Hpc2c : ret_pc (U5 !!! Regidx Rra) = mword_of_int (KernelSyms.either_copyin + 0x2c))
        by (rewrite HU5ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc2c) in "Hpc".
      iEval (rewrite HU5a2) in "Hdst".
      iAssert (⌜uptd_ext_sz (pv_sz V) (pv_upt V) P'⌝)%I as "#Hxe"; [iPureIntro; exact Hext|].
      iDestruct ("Hpback" $! P' with "Hxe Hszc Hptc Hpt") as "Hres".
      assert (Hrsp : mr !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite (callee_saved_lookup Hcsr csp_rs1 ltac:(vm_compute; reflexivity)); exact HU5sp).
      assert (Hthrr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 ->
                mr !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18 N19 N20.
        rewrite (callee_saved_lookup Hcsr r Hr). apply HthrU5; assumption. }
      iApply (ec_epi (mword_of_int (KernelSyms.either_copyin + 0x2c)) (mword_of_int (KernelSyms.either_copyin + 0x2e))
                (mword_of_int (KernelSyms.either_copyin + 0x30)) (mword_of_int (KernelSyms.either_copyin + 0x32))
                (mword_of_int (KernelSyms.either_copyin + 0x34)) (mword_of_int (KernelSyms.either_copyin + 0x36))
                (mword_of_int (KernelSyms.either_copyin + 0x38)) (mword_of_int (KernelSyms.either_copyin + 0x3a))
                m mr av (mr !!! Regidx Ra0) sp0 ra0 s00 s10 s20 s30 s40 p b
                ltac:(lia) Hq2e Hq30 Hq32 Hq34 Hq36 Hq38 Hq3a
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                Hrsp eq_refl Hthrr
                with "Hcg Hi2c Hi2e Hi30 Hi32 Hi34 Hi36 Hi38 Hi3a Hpc Hk1 Hk2 Hk3 Hk4 Hk5 Hk6 [-]").
      iIntros (CID22 Hs22 mf) "[%Hcsf %Hfa0] Hcg Hpc".
      (* [Hcpu] rode through [ec_epi] untouched since copyin handed it back
         at [CID21]; re-anchor it at [CID22] before discharging [Hcont]. *)
      iDestruct (cpu_own_transport CID21 CID22 lvl eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iSpecialize ("Hcont" $! CID22 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "[%] Hcg Hcpu Hpc [Hres Hdst]").
      { exact Hcsf. }
      rewrite /either_copyin_post. rewrite Hfa0.
      iSplitR; [iPureIntro; exact Hret|].
      iSplitL "Hres".
      { iExists P'. iSplitR; [iPureIntro; exact (uptd_ext_sz_ext _ _ _ Hext)|]. iExact "Hres". }
      iExists dst_new. iExact "Hdst".
    - (* ================= user_src == 0: memmove ================= *)
      assert (Hz : eq_vec (Am !!! Regidx Rs1) zero_reg = true)
        by (rewrite HAs1; exact Hflag).
      assert (Huw0 : uw = (zero_reg : mword 64))
        by (apply eq_vec_true_iff; exact Hflag).
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x1c)) (mword_of_int 16 : mword 8)
                (Cregidx (mword_of_int 1)) Rs1 Am (av - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hz
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi1c [-]").
      iApply bi.later_intro. iIntros (CID15 Hs15) "Hcg Hpc".
      assert (Hjt : add_vec (mword_of_int (KernelSyms.either_copyin + 0x1c) : mword 64)
                      (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 16 : mword 8) ('b"0"))))
                    = mword_of_int (KernelSyms.either_copyin + 0x3c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjt) in "Hpc".
      (* ---- +0x3a: sext.w a2,s2 ---- *)
      iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x3c)) Ra2 Rs2
                (mword_of_int 0 : mword 12) Am (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi3c [-]").
      iIntros (CID16 Hs16) "Hcg Hpc".
      set (K1 := <[Regidx Ra2 := regval_into_reg
                    (sign_extend' 64 (subrange_vec_dec
                       (add_vec (Am !!! Regidx Rs2) (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> Am).
      change (<[Regidx Ra2 := regval_into_reg
                (sign_extend' 64 (subrange_vec_dec
                   (add_vec (Am !!! Regidx Rs2) (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> Am) with K1.
      assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x3c) : mword 64) 4 = mword_of_int (KernelSyms.either_copyin + 0x40))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      assert (HK1a2 : K1 !!! Regidx Ra2 = (mword_of_int (Z.of_nat len) : mword 64)).
      { rewrite /K1 upd_eq HAs2.
        exact (sextw_moi (Z.of_nat len) (Nat2Z.is_nonneg len) (ec_len31 len Hlen)). }
      (* ---- +0x3e: c.mv a1,s3 -- src ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x40)) Ra1 Rs3 K1 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi40 [-]").
      iIntros (CID17 Hs17) "Hcg Hpc".
      set (K2 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (K1 !!! Regidx Rs3))]> K1).
      change (<[Regidx Ra1 := regval_into_reg (add_vec zero_reg (K1 !!! Regidx Rs3))]> K1) with K2.
      assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x42))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      (* ---- +0x40: c.mv a0,s4 -- dst ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x42)) Ra0 Rs4 K2 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi42 [-]").
      iIntros (CID18 Hs18) "Hcg Hpc".
      set (K3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (K2 !!! Regidx Rs4))]> K2).
      change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (K2 !!! Regidx Rs4))]> K2) with K3.
      assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x44))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp44) in "Hpc".
      (* ---- +0x42: jal ra,memmove ---- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x44))
                Rra (mword_of_int 2091482 : mword 21) K3 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi44 [-]").
      iIntros (CID19 Hs19) "Hcg Hpc".
      set (K4 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x44) : mword 64) 4)]> K3).
      change (<[Regidx Rra := regval_into_reg
                (add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x44) : mword 64) 4)]> K3) with K4.
      assert (Hjmm : add_vec (mword_of_int (KernelSyms.either_copyin + 0x44) : mword 64)
                       (sign_extend' 64 (mword_of_int 2091482 : mword 21)) = mword_of_int KernelSyms.memmove)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjmm) in "Hpc".
      assert (HK4ra : K4 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x44) : mword 64) 4)
        by (rewrite /K4 upd_eq; reflexivity).
      assert (HK4a0 : K4 !!! Regidx Ra0 = dst).
      { rewrite /K4 upd_ne; [| reg_neq]. rewrite /K3 upd_eq.
        rewrite /K2 upd_ne; [| reg_neq]. rewrite /K1 upd_ne; [| reg_neq].
        rewrite HAs4. apply add_vec_zero_l. }
      assert (HK4a1 : K4 !!! Regidx Ra1 = src).
      { rewrite /K4 upd_ne; [| reg_neq]. rewrite /K3 upd_ne; [| reg_neq].
        rewrite /K2 upd_eq. rewrite /K1 upd_ne; [| reg_neq].
        rewrite HAs3. apply add_vec_zero_l. }
      assert (HK4a2 : K4 !!! Regidx Ra2 = (mword_of_int (Z.of_nat len) : mword 64)).
      { rewrite /K4 upd_ne; [| reg_neq]. rewrite /K3 upd_ne; [| reg_neq].
        rewrite /K2 upd_ne; [exact HK1a2 | reg_neq]. }
      assert (HK4sp : K4 !!! Regidx csp_rs1 = pa_stk sp0 6).
      { rewrite /K4 upd_ne; [| reg_neq]. rewrite /K3 upd_ne; [| reg_neq].
        rewrite /K2 upd_ne; [| reg_neq]. rewrite /K1 upd_ne; [exact HAsp | reg_neq]. }
      assert (HK4s1 : K4 !!! Regidx Rs1 = uw).
      { rewrite /K4 upd_ne; [| reg_neq]. rewrite /K3 upd_ne; [| reg_neq].
        rewrite /K2 upd_ne; [| reg_neq]. rewrite /K1 upd_ne; [exact HAs1 | reg_neq]. }
      assert (HthrK4 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 ->
                K4 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18 N19 N20.
        assert (N1 : r <> mword_of_int 1)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N11 : r <> mword_of_int 11)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N12 : r <> mword_of_int 12)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /K4 upd_ne; [| congruence].
        rewrite /K3 upd_ne; [| congruence].
        rewrite /K2 upd_ne; [| congruence].
        rewrite /K1 upd_ne; [| congruence]. apply HthrA; assumption. }
      iEval (rewrite -HK4a1) in "Hres".
      iEval (rewrite -HK4a0) in "Hdst".
      iApply (Memmove.wp_memmove_sconf K4 (av - 6)%nat len src_bytes dst_olds b p
                ltac:(lia) (ec_len32 len Hlen) HK4a2
                with "Hcg Htext Hpc Hres Hdst [-]").
      iIntros (CID20 Hs20 mfin) "Hcg Hpc Hsrc Hdst %Hmma0 %Hcsmm".
      assert (Hpc48 : ret_pc (K4 !!! Regidx Rra) = mword_of_int (KernelSyms.either_copyin + 0x48))
        by (rewrite HK4ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc48) in "Hpc".
      iEval (rewrite HK4a1) in "Hsrc".
      iEval (rewrite HK4a0) in "Hdst".
      (* ---- +0x46: c.mv a0,s1 -- the flag, which the beqz proved is 0 ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x48)) Ra0 Rs1 mfin (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi48 [-]").
      iIntros (CID21 Hs21) "Hcg Hpc".
      set (L1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mfin !!! Regidx Rs1))]> mfin).
      change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mfin !!! Regidx Rs1))]> mfin) with L1.
      assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.either_copyin + 0x48) : mword 64) 2 = mword_of_int (KernelSyms.either_copyin + 0x4a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4a) in "Hpc".
      assert (Hmms1 : mfin !!! Regidx Rs1 = uw)
        by (rewrite (callee_saved_lookup Hcsmm (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HK4s1).
      assert (HL1a0 : L1 !!! Regidx Ra0 = (mword_of_int 0 : mword 64)).
      { rewrite /L1 upd_eq Hmms1 Huw0 add_vec_zero_l. exact ec_zero_reg_moi. }
      (* ---- +0x48: c.j -0x1e ---- *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.either_copyin + 0x4a))
                (sign_extend' 21 (concat_vec (mword_of_int 2033 : mword 11) ('b"0")))
                L1 (av - 6)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi4a [-]").
      iIntros (CID22 Hs22). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Hjc : add_vec (mword_of_int (KernelSyms.either_copyin + 0x4a) : mword 64)
                      (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2033 : mword 11) ('b"0"))))
                    = mword_of_int (KernelSyms.either_copyin + 0x2c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjc) in "Hpc".
      assert (HL1sp : L1 !!! Regidx csp_rs1 = pa_stk sp0 6).
      { rewrite /L1 upd_ne; [| reg_neq].
        rewrite (callee_saved_lookup Hcsmm csp_rs1 ltac:(vm_compute; reflexivity)). exact HK4sp. }
      assert (HthrL1 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 ->
                L1 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18 N19 N20.
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /L1 upd_ne; [| congruence].
        rewrite (callee_saved_lookup Hcsmm r Hr). apply HthrK4; assumption. }
      iApply (ec_epi (mword_of_int (KernelSyms.either_copyin + 0x2c)) (mword_of_int (KernelSyms.either_copyin + 0x2e))
                (mword_of_int (KernelSyms.either_copyin + 0x30)) (mword_of_int (KernelSyms.either_copyin + 0x32))
                (mword_of_int (KernelSyms.either_copyin + 0x34)) (mword_of_int (KernelSyms.either_copyin + 0x36))
                (mword_of_int (KernelSyms.either_copyin + 0x38)) (mword_of_int (KernelSyms.either_copyin + 0x3a))
                m L1 av (mword_of_int 0 : mword 64) sp0 ra0 s00 s10 s20 s30 s40 p b
                ltac:(lia) Hq2e Hq30 Hq32 Hq34 Hq36 Hq38 Hq3a
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                HL1sp HL1a0 HthrL1
                with "Hcg Hi2c Hi2e Hi30 Hi32 Hi34 Hi36 Hi38 Hi3a Hpc Hk1 Hk2 Hk3 Hk4 Hk5 Hk6 [-]").
      iIntros (CID23 Hs23 mf) "[%Hcsf %Hfa0] Hcg Hpc".
      (* [Hcpu] rode through memmove and [ec_epi] untouched since myproc
         handed it back at [CID14]; re-anchor it at [CID23] before
         discharging [Hcont]. *)
      iDestruct (cpu_own_transport CID14 CID23 lvl eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iSpecialize ("Hcont" $! CID23 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "[%] Hcg Hcpu Hpc [Hsrc Hdst]").
      { exact Hcsf. }
      rewrite /either_copyin_post. rewrite Hfa0.
      iSplitR; [iPureIntro; reflexivity|]. iFrame "Hsrc Hdst".
  Qed.

End ProofEitherCopyin.

End EitherCopyinProof.
