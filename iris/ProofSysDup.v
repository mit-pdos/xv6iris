(* ProofSysDup.v -- the whole-function WP proof of xv6's sys_dup().

   Contract: SpecSysDup.v.  Decode: CodeSysDup.v.  Linked: LinkSysDup.v.

   THIS IS THE FUNCTION THE PAYLOAD-DEFICIT DESIGN EXISTS FOR, and the resource
   story is the whole point, so it is worth reading before the tactics:

     argfd    reports which descriptor [fd0] the argument names, and the
              pointer [fv = fnode k] it holds.  It takes NOTHING: the
              reference stays inside [proc_priv].
     LEND     [ProcInv.proc_priv_lend] splits the block at the fd table and
              takes descriptor [fd0]'s [file_ref] out.  What is left of the
              array is [proc_ofiles_owe ... {[fd0]}] -- fd0's cell still names
              the file, but its payload is here in our hands.
     fdalloc  gets the core plus the holed array, and fills the least free
              descriptor [fd1].  It needs no reference (it only stores a
              pointer), releases the [fd_slot] that descriptor owned, and
              leaves the deficit at {[fd1]} u {[fd0]}.
     filedup  eats that [fd_slot] -- the unit is what pays for the higher
              count -- and splits our one reference into two halves.
     REPAY    one half settles fd0, the other settles fd1
              ([ProcInv.proc_ofiles_repay] twice), the deficit is empty, and
              [ProcInv.proc_priv_join] hands the block back.

   The ledger closes with ZERO allowance, and the two descriptors are provably
   distinct (fd0 is non-null by argfd, fd1 is null by [fd_frees]), which is what
   lets the two repayments not collide.

   THREE EXITS, ONE EPILOGUE ([sd_tail] at +0x3c), and the asymmetry worth
   knowing: s1/s2 are pushed only AFTER the argfd call, so on the
   argfd-failure path frame slots 3 and 4 are never written -- [callee_saved]
   holds there because those registers were never touched, and on the other two
   paths because they were saved and reloaded.  [sd_tail] therefore takes slots
   3..6 at ARBITRARY values.

   EXPLICIT-CPUID: three calls, so the [cpu_own] transports are the usual
   [cpu_own_transport ... ltac:(wp_next_chain)] before each. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import VcGen.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl WpSmodeIntr.
Require Import StackOwn.
Require Import ProcGeom CpuOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import SpecArgfd SpecFdalloc SpecFiledup SpecSysDup.
Require Import KernelRvcDecode.
Require Import CodeSysDup.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.


(* ===================================================================== *)
(*  Pure side conditions, at the top level where [lia] has no mwords in   *)
(*  scope.                                                                *)
(* ===================================================================== *)

(* the [&f] the prologue computes: s0-40 is frame slot 5 *)
Lemma sd_addr_f (sp0 : mword 64) :
  add_vec sp0 (sign_extend' 64 (mword_of_int 0xfd8 : mword 12)) = pa_stk sp0 5.
Proof. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. Qed.

(* ... rebased on the CURRENT sp, which is what [sie_cap_gpr]'s bounds are
   about.  argfd's [pf] must be non-null, and the honest reason is that an
   address the kernel stack occupies never is. *)
Lemma sd_addr_f_base (X : mword 64) : pa_stk X 5 = add_vec_int (pa_stk X 6) 8.
Proof. unfold pa_stk. rewrite avi_assoc. f_equal; lia. Qed.

(* a descriptor index is a non-negative [int], so [bltz] falls through *)
Lemma sd_sint_moi (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  sint (mword_of_int z : mword 64) = z.
Proof.
  intro Hz.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  rewrite moi64_unsigned. rewrite bvw64_small; [| lia].
  apply bv_swrap_small.
  assert (Hhm : bv_half_modulus 64 = (2 ^ 63)%Z) by reflexivity. rewrite Hhm.
  assert (E63 : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
  lia.
Qed.

Lemma sd_fd_nonneg (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  zopz0zI_s (mword_of_int z : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hz. unfold zopz0zI_s. apply Z.ltb_ge.
  assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
  rewrite (sd_sint_moi z Hz). lia.
Qed.

Lemma sd_fd_range (n : nat) : (n < NOFILE)%nat -> (0 <= Z.of_nat n < 2 ^ 31)%Z.
Proof.
  unfold NOFILE. intro Hn.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  lia.
Qed.

(* [-1] IS negative, so the two failure arms' [bltz] is taken *)
Lemma sd_m1_neg : zopz0zI_s (mword_of_int (-1) : mword 64) (zero_reg : mword 64) = true.
Proof. vm_compute; reflexivity. Qed.

(* argfd's SUCCESS value is 0, which is not negative *)
Lemma sd_zero_nonneg : zopz0zI_s (zero_reg : mword 64) (zero_reg : mword 64) = false.
Proof. vm_compute; reflexivity. Qed.

Module SysDupProof (Argfd : ARGFD) (Fdalloc : FDALLOC) (Filedup : FILEDUP) : SYSDUP.

Section ProofSysDup.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation Rra  := (mword_of_int 1  : mword 5).
  Notation Rs0  := (mword_of_int 8  : mword 5).
  Notation Rs1  := (mword_of_int 9  : mword 5).
  Notation Rs2  := (mword_of_int 18 : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
  Notation Ra1  := (mword_of_int 11 : mword 5).
  Notation Ra2  := (mword_of_int 12 : mword 5).
  Notation Ra5  := (mword_of_int 15 : mword 5).

  (* the current sp's bounds, out of the stack capability *)
  (* THE CARVE THIS READS IS ARM-DEPENDENT, hence the [0 < k] premise.
     [IntrDefs.sie_cap] owns [trap_res bb + k] slots, and [trap_res false] is
     NOTHING -- so at the interrupts-off arm the ONLY slots underwriting an sp
     bound are the caller's own [k], and a zero-slot carve says nothing about
     sp at all.  (Under the old arm-blind reserve the 78 reserved slots
     covered it at either arm, which is why this used to need no premise.
     The premise is local to this helper: every call site sits inside the
     capstone, whose [<fn>_stack <= av] premise is already unfolded, so it is
     a [lia].) *)
  Lemma sd_sp_bounds `{CID0 : CpuId} (mm : regfile) (k : nat)
      (bb : bool) (pp : mword 64) :
    (0 < k)%nat ->
    sie_cap_gpr KT1 mm k bb pp -∗
    ⌜(8 <= uint (mm !!! Regidx csp_rs1) < 274877906944 + 8)%Z⌝.
  Proof.
    iIntros (Hk) "(_ & _ & (Hstk & _ & _) & _)".
    iApply (stack_own_sp_bounds (KTR := KT1) _ (trap_res bb + k)%nat with "Hstk").
    destruct bb; unfold trap_res; lia.
  Qed.

  (* =================================================================== *)
  (*  The shared tail at +0x3c, entered by all THREE arms.                *)
  (* =================================================================== *)
  (* Only ra and s0 are popped here: s1/s2 are handled by whichever arm got
     here (restored, or never touched), which is why they arrive already in
     agreement with [m] and why slots 3..6 are arbitrary. *)
  Lemma sd_tail `{CID0 : CpuId}
      (m Mt : regfile) (av : nat) (rv : mword 64)
      (sp0 ra0 s00 : mword 64) (w3 w4 w5 w6 : bv 64)
      (p : mword 64) (b : bool) :
    (6 <= av)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 6 ->
    Mt !!! Regidx Ra5 = rv ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
        Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr KT1 Mt (av - 6)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.sys_dup + 0x3c) : mword 64) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) w3 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) w4 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) w5 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) w6 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr KT1 mf av b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav Hsp0 Hra0 Hs00 Hmtsp Hmta5 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hcont".
    (* ---- +0x3c: c.mv a0,a5 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x3c)) Ra0 Ra5 Mt (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (sdi_3c with "Htext"). }
    iIntros (CIDt0 Hkt0) "Hcg Hpc".
    set (T0 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mt !!! Regidx Ra5))]> Mt).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mt !!! Regidx Ra5))]> Mt) with T0.
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x3c) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e) in "Hpc".
    assert (HT0a0 : T0 !!! Regidx Ra0 = rv).
    { rewrite /T0 upd_eq Hmta5. apply add_vec_zero_l. }
    assert (HT0sp : T0 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T0 upd_ne; [exact Hmtsp | vm_compute; discriminate]).
    (* ---- +0x3e: c.ldsp ra,40(sp) ---- *)
    assert (Hpa1 : add_vec (T0 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HT0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x3e))
              (mword_of_int 5 : mword 6) Rra T0 (av - 6)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb1").
    { iApply (sdi_3e with "Htext"). }
    iIntros (CIDt1 Hkt1) "Hcg Hpc Hb1".
    iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> T0).
    change (<[Regidx Rra := regval_into_reg ra0]> T0) with T1.
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x3e) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T1 upd_ne; [exact HT0sp | vm_compute; discriminate]).
    (* ---- +0x40: c.ldsp s0,32(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x40))
              (mword_of_int 4 : mword 6) Rs0 T1 (av - 6)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb2").
    { iApply (sdi_40 with "Htext"). }
    iIntros (CIDt2 Hkt2) "Hcg Hpc Hb2".
    iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    change (<[Regidx Rs0 := regval_into_reg s00]> T1) with T2.
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x40) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T2 upd_ne; [exact HT1sp | vm_compute; discriminate]).
    (* ---- +0x42: c.addi16sp sp,48 (frame pop) ---- *)
    assert (Hwv : add_vec (T2 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0)
      by (rewrite HT2sp; apply stk_pop_48).
    assert (Hpop : T2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T2 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6)
      by (rewrite Hwv; exact HT2sp).
    assert (E5 : pa_stk (pa_stk sp0 4) 1 = pa_stk sp0 5) by (rewrite pa_stk_assoc; reflexivity).
    assert (E6 : pa_stk (pa_stk sp0 4) 2 = pa_stk sp0 6) by (rewrite pa_stk_assoc; reflexivity).
    iEval (rewrite -E5) in "Hb5".
    iEval (rewrite -E6) in "Hb6".
    iDestruct (stack_own_4_intro sp0 ra0 s00 w3 w4 with "Hb1 Hb2 Hb3 Hb4") as "Hf14".
    iDestruct (stack_own_2_intro (pa_stk sp0 4) w5 w6 with "Hb5 Hb6") as "Hf56".
    iAssert (stack_own (KTR := KT1) sp0 6) with "[Hf14 Hf56]" as "Hframe".
    { rewrite (stack_own_split (KTR := KT1) sp0 4 6 ltac:(lia)). change (6 - 4)%nat with 2%nat. iFrame. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x42))
              (mword_of_int 3 : mword 6) T2 (av - 6)%nat 6 b Hpop
              with "Hcg Hpc [] Hframe").
    { iApply (sdi_42 with "Htext"). }
    iIntros (CIDt3 Hkt3) "Hcg Hpc".
    assert (Hnk : ((av - 6) + 6)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x42) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp44) in "Hpc".
    set (T3 := <[Regidx csp_rs1 := regval_into_reg (add_vec (T2 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> T2).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (T2 !!! Regidx csp_rs1)
              (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> T2) with T3.
    (* ---- +0x44: c.ret ---- *)
    assert (HT3ra : T3 !!! Regidx Rra = ra0).
    { rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x44)) Rra T3 av b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc []").
    { iApply (sdi_44 with "Htext"). }
    iIntros (CIDt4 Hkt4) "Hcg Hpc".
    iEval (rewrite (rget_ne (CID := CIDt3) T3 Rra ltac:(vm_compute; discriminate))) in "Hpc".
    iEval (rewrite HT3ra) in "Hpc".
    (* ---- the postcondition ---- *)
    assert (HT3sp : T3 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /T3 upd_eq Hwv; symmetry; exact Hsp0).
    assert (HT3s0 : T3 !!! Regidx Rs0 = m !!! Regidx Rs0).
    { rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_eq. symmetry; exact Hs00. }
    assert (HT3a0 : T3 !!! Regidx Ra0 = rv).
    { rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_ne; [| vm_compute; discriminate]. exact HT0a0. }
    assert (Hthr3 : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> T3 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /T3 upd_ne; [| congruence].
      rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [| congruence].
      rewrite /T0 upd_ne; [| congruence].
      apply Hthr; assumption. }
    iSpecialize ("Hcont" $! CIDt4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! T3 with "[%] Hcg Hpc").
    split; [| exact HT3a0].
    unfold callee_saved.
    split; [exact HT3sp|].
    split; [exact HT3s0|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    apply Hthr3; vm_compute; first [reflexivity | discriminate].
  Qed.

  (* =================================================================== *)
  (*  THE CAPSTONE.                                                       *)
  (* =================================================================== *)
  Lemma wp_sys_dup_sconf (γl γf : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
      (v : mword 64) (pid : mword 32) (V : pprivate) (b : bool) (lks : gset string)
    : wp_sys_dup_sconf_body γl γf m av n eb p v pid V b lks.
  Proof.
    cbv beta delta [wp_sys_dup_sconf_body].
    intros pcE ret_tgt Harg Hn Hav Hftno.
    
    set (sp0 := m !!! Regidx csp_rs1).
    set (ra0 := m !!! Regidx Rra).
    set (s00 := m !!! Regidx Rs0).
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    iIntros "Hcg Hcpu #Htext #Hdata Hpc #Hftab Hpriv Hfrag Hcont".
    iDestruct (proc_priv_ofile_len with "Hpriv") as %Hoflen.
    (* ===================== PROLOGUE (48-byte frame) ===================== *)
    (* ---- +0x00: c.addi16sp sp,-48 ---- *)
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) m av 6 b
              ltac:(lia) (stk_push_48 (m !!! Regidx csp_rs1))
              with "Hcg Hpc []").
    { iApply (sdi_00 with "Htext"). }
    iIntros (CID1 Hk1) "Hcg Hframe Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.sys_dup + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /M1 upd_eq; apply stk_push_48).
    assert (E5 : pa_stk (pa_stk sp0 4) 1 = pa_stk sp0 5) by (rewrite pa_stk_assoc; reflexivity).
    assert (E6 : pa_stk (pa_stk sp0 4) 2 = pa_stk sp0 6) by (rewrite pa_stk_assoc; reflexivity).
    rewrite (stack_own_split (KTR := KT1) sp0 4 6 ltac:(lia)). change (6 - 4)%nat with 2%nat.
    iDestruct "Hframe" as "[Hf14 Hf56]".
    iDestruct (stack_own_4_elim with "Hf14") as (u1 u2 u3 u4) "(Hs1 & Hs2 & Hs3 & Hs4)".
    iDestruct (stack_own_2_elim with "Hf56") as (w5 w6) "[Hs5 Hs6]".
    iEval (rewrite E5) in "Hs5". iEval (rewrite E6) in "Hs6".
    (* ---- +0x02: c.sdsp ra,40(sp) ---- *)
    assert (Hpa1 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa2 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hs1".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x02))
              (mword_of_int 5 : mword 6) Rra M1 (av - 6)%nat u1 b
              with "Hcg Hpc [] Hs1").
    { iApply (sdi_02 with "Htext"). }
    iIntros (CID2 Hk2) "Hcg Hpc Hs1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- +0x04: c.sdsp s0,32(sp) ---- *)
    iEval (rewrite -Hpa2) in "Hs2".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x04))
              (mword_of_int 4 : mword 6) Rs0 M1 (av - 6)%nat u2 b
              with "Hcg Hpc [] Hs2").
    { iApply (sdi_04 with "Htext"). }
    iIntros (CID3 Hk3) "Hcg Hpc Hs2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    assert (HM1ra : M1 !!! Regidx Rra = ra0)
      by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HM1s0 : M1 !!! Regidx Rs0 = s00)
      by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite (rget_ne (CID := CID1) M1 Rra ltac:(vm_compute; discriminate))
             Hpa1 HM1ra) in "Hs1".
    iEval (rewrite (rget_ne (CID := CID2) M1 Rs0 ltac:(vm_compute; discriminate))
             Hpa2 HM1s0) in "Hs2".
    (* ---- +0x06: c.addi4spn s0,sp,48 ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) Rs0
              M1 (av - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (sdi_06 with "Htext"). }
    iIntros (CID4 Hk4) "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> M1).
    change (<[Regidx Rs0 := regval_into_reg
              (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> M1) with M2.
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    assert (HM2s0 : M2 !!! Regidx Rs0 = sp0).
    { rewrite /M2 upd_eq HM1sp. apply stk_fp_48. }
    assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /M2 upd_ne; [exact HM1sp | vm_compute; discriminate]).
    (* ---- +0x08: addi a2,s0,-40 -- a2 := &f ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x08)) Ra2 Rs0
              (mword_of_int 0xfd8 : mword 12) M2 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (sdi_08 with "Htext"). }
    iIntros (CID5 Hk5) "Hcg Hpc".
    set (M3 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (M2 !!! Regidx Rs0) (sign_extend' 64 (mword_of_int 0xfd8 : mword 12)))]> M2).
    change (<[Regidx Ra2 := regval_into_reg
              (add_vec (M2 !!! Regidx Rs0) (sign_extend' 64 (mword_of_int 0xfd8 : mword 12)))]> M2) with M3.
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x08) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_dup + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    assert (HM3a2 : M3 !!! Regidx Ra2 = pa_stk sp0 5).
    { rewrite /M3 upd_eq HM2s0. apply sd_addr_f. }
    (* ---- +0x0c: c.li a1,0 -- pfd = 0 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x0c)) Ra1 (mword_of_int 0 : mword 6)
              (zero_reg : mword 64) M3 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (sdi_0c with "Htext"). }
    iIntros (CID6 Hk6) "Hcg Hpc".
    set (M4 := <[Regidx Ra1 := regval_into_reg (zero_reg : mword 64)]> M3).
    change (<[Regidx Ra1 := regval_into_reg (zero_reg : mword 64)]> M3) with M4.
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* ---- +0x0e: c.li a0,0 -- the argument index ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x0e)) Ra0 (mword_of_int 0 : mword 6)
              (zero_reg : mword 64) M4 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (sdi_0e with "Htext"). }
    iIntros (CID7 Hk7) "Hcg Hpc".
    set (M5 := <[Regidx Ra0 := regval_into_reg (zero_reg : mword 64)]> M4).
    change (<[Regidx Ra0 := regval_into_reg (zero_reg : mword 64)]> M4) with M5.
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x0e) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* ---- +0x10: jal ra,argfd ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x10)) Rra
              (mword_of_int 2096626 : mword 21) M5 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (sdi_10 with "Htext"). }
    iIntros (CID8 Hk8) "Hcg Hpc".
    set (M6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x10) : mword 64) 4)]> M5).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x10) : mword 64) 4)]> M5) with M6.
    assert (Hjaf : add_vec (mword_of_int (KernelSyms.sys_dup + 0x10) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096626 : mword 21)) = mword_of_int KernelSyms.argfd)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjaf) in "Hpc".
    assert (HM6ra : M6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x10) : mword 64) 4)
      by (rewrite /M6 upd_eq; reflexivity).
    assert (HM6a0 : M6 !!! Regidx Ra0 = (zero_reg : mword 64)).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate]. rewrite /M5 upd_eq. reflexivity. }
    assert (HM6a1 : M6 !!! Regidx Ra1 = (zero_reg : mword 64)).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate].
      rewrite /M5 upd_ne; [| vm_compute; discriminate]. rewrite /M4 upd_eq. reflexivity. }
    assert (HM6a2 : M6 !!! Regidx Ra2 = pa_stk sp0 5).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate].
      rewrite /M5 upd_ne; [| vm_compute; discriminate].
      rewrite /M4 upd_ne; [| vm_compute; discriminate]. exact HM3a2. }
    assert (HM6sp : M6 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate].
      rewrite /M5 upd_ne; [| vm_compute; discriminate].
      rewrite /M4 upd_ne; [| vm_compute; discriminate].
      rewrite /M3 upd_ne; [| vm_compute; discriminate]. exact HM2sp. }
    assert (HM6s0 : M6 !!! Regidx Rs0 = sp0).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate].
      rewrite /M5 upd_ne; [| vm_compute; discriminate].
      rewrite /M4 upd_ne; [| vm_compute; discriminate].
      rewrite /M3 upd_ne; [| vm_compute; discriminate]. exact HM2s0. }
    assert (HM6thr : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> M6 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N11 : r <> mword_of_int 11)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N12 : r <> mword_of_int 12)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /M6 upd_ne; [| congruence].
      rewrite /M5 upd_ne; [| congruence].
      rewrite /M4 upd_ne; [| congruence].
      rewrite /M3 upd_ne; [| congruence].
      rewrite /M2 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [reflexivity | congruence]. }
    (* argfd's out-parameter [pf] is frame slot 5; [pfd] is NULL *)
    (* the helper's [0 < k] premise, from the capstone's own stack budget.
       Named rather than [ltac:(lia)]-inline: at that position [k] is still
       an unresolved evar, and [lia] answers "Cannot find witness". *)
    assert (Hkpos : (0 < (av - 6)%nat)%nat) by lia.
    iDestruct (sd_sp_bounds _ _ _ _ Hkpos with "Hcg") as %Hspb.
    rewrite HM6sp in Hspb.
    assert (Hs5nz : M6 !!! Regidx Ra2 <> (zero_reg : mword 64)).
    { rewrite HM6a2 sd_addr_f_base. apply stack_off_nonzero; [exact Hspb | lia]. }
    assert (HM6a0' : M6 !!! Regidx Ra0 = (mword_of_int (Z.of_nat 0) : mword 64)).
    { rewrite HM6a0. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -HM6a2) in "Hs5".
    iDestruct (cpu_own_transport CID CID8 n eb p b ltac:(wp_next_chain) with "Hcpu")
      as "Hcpu".
    iApply (Argfd.wp_argfd_sconf γf M6 (av - 6)%nat n eb p 0%nat v pid V
              (word_lo w5) w5 b lks
              ltac:(unfold NARG; lia) HM6a0' Harg Hs5nz Hn
              ltac:(lia)
              with "Hcg Hcpu Htext Hdata Hpc Hpriv [] Hs5").
    { (* sys_dup passes [pfd = 0]: no cell, and none is written *)
      iApply (ofd_out_null _ (word_lo w5)). exact HM6a1. }
    iIntros (CID9 Hk9 A) "%HcsA Hcg Hcpu Hpc Hpriv Hpost".
    assert (Hpc14 : ret_pc (M6 !!! Regidx Rra) = mword_of_int (KernelSyms.sys_dup + 0x14))
      by (rewrite HM6ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    assert (HAsp : A !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)); exact HM6sp).
    assert (HAs0 : A !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsA Rs0 ltac:(vm_compute; reflexivity)); exact HM6s0).
    assert (HAthr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> A !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8. rewrite (callee_saved_lookup HcsA r Hr). apply HM6thr; assumption. }
    (* ---- +0x14: c.li a5,-1 -- pre-load the failure return value ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x14)) Ra5 (mword_of_int 63 : mword 6)
              (mword_of_int (-1) : mword 64) A (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (sdi_14 with "Htext"). }
    iIntros (CID10 Hk10) "Hcg Hpc".
    set (B1 := <[Regidx Ra5 := regval_into_reg (mword_of_int (-1) : mword 64)]> A).
    change (<[Regidx Ra5 := regval_into_reg (mword_of_int (-1) : mword 64)]> A) with B1.
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x14) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    assert (HB1a5 : B1 !!! Regidx Ra5 = (mword_of_int (-1) : mword 64))
      by (rewrite /B1 upd_eq; reflexivity).
    assert (HB1sp : B1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /B1 upd_ne; [exact HAsp | vm_compute; discriminate]).
    assert (HB1s0 : B1 !!! Regidx Rs0 = sp0)
      by (rewrite /B1 upd_ne; [exact HAs0 | vm_compute; discriminate]).
    assert (HB1a0 : B1 !!! Regidx Ra0 = A !!! Regidx Ra0)
      by (rewrite /B1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HB1thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> B1 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8.
      assert (N15 : r <> mword_of_int 15)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /B1 upd_ne; [| congruence]. apply HAthr; assumption. }
    (* ---- +0x16: bltz a0 -- did argfd fail? ---- *)
    rewrite /argfd_post. iDestruct "Hpost" as "[Hfail | Hsucc]".
    { (* ===================== argfd said -1 ===================== *)
      iDestruct "Hfail" as "([%Hr %Hnone] & _ & Hs5)".
      iEval (rewrite HM6a2) in "Hs5".
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x16))
                (mword_of_int 38 : mword 13) Ra0 B1 (av - 6)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HB1a0 Hr; exact sd_m1_neg)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (sdi_16 with "Htext"). }
      iApply bi.later_intro. iIntros (CID11 Hk11) "Hcg Hpc".
      assert (Htgt3c : add_vec (mword_of_int (KernelSyms.sys_dup + 0x16) : mword 64)
                         (sign_extend' 64 (mword_of_int 38 : mword 13))
                       = mword_of_int (KernelSyms.sys_dup + 0x3c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt3c) in "Hpc".
      (* slots 3 and 4 were never written on this path *)
      assert (HshCID11 : b = false \/ p = zero_reg -> (CID11 : CPU) = (CID : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift HshCID11 with "Hcont") as "Hcont".
      iApply (sd_tail (CID0 := CID11) m B1 av (mword_of_int (-1) : mword 64)
                sp0 ra0 s00 u3 u4 w5 w6 p b
                ltac:(lia) eq_refl eq_refl eq_refl HB1sp HB1a5 HB1thr
                with "Hcg Htext Hpc Hs1 Hs2 Hs3 Hs4 Hs5 Hs6").
      iIntros (CIDz1 Hkz1 Fz1) "%HcsF Hcg Hpc".
      destruct HcsF as [HcsF HFa0].
      iDestruct (cpu_own_transport CID9 CIDz1 n eb p b ltac:(wp_next_chain) with "Hcpu")
      as "Hcpu".
    iSpecialize ("Hcont" $! CIDz1 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Fz1 with "[%] Hcg Hcpu Hpc [Hpriv Hfrag]"); [exact HcsF|].
      rewrite /sys_dup_post. iLeft. iSplitR; [| iFrame "Hpriv Hfrag"].
      iPureIntro. split; [exact HFa0 | exact Hnone]. }
    (* ===================== argfd found the descriptor ===================== *)
    iDestruct "Hsucc" as (fd0 fv) "([%Hrv0 %Hsome] & _ & Hs5)".
    iEval (rewrite HM6a2) in "Hs5".
    destruct (arg_fd_lookup v (pv_ofile V) fd0 fv Hsome) as (Hfd0lt & Hlk0 & Hfvnz & _).
    iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x16))
              (mword_of_int 38 : mword 13) Ra0 B1 (av - 6)%nat b
              ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite HB1a0 Hrv0; exact sd_zero_nonneg)
              with "Hcg Hpc []").
    { iApply (sdi_16 with "Htext"). }
    iIntros (CID11 Hk11) "Hcg Hpc".
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x16) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_dup + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* ---- +0x1a / +0x1c: save s1 and s2 ---- *)
    assert (Hpa3 : add_vec (B1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HB1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa4 : add_vec (B1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HB1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa3) in "Hs3".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x1a))
              (mword_of_int 3 : mword 6) Rs1 B1 (av - 6)%nat u3 b
              with "Hcg Hpc [] Hs3").
    { iApply (sdi_1a with "Htext"). }
    iIntros (CID12 Hk12) "Hcg Hpc Hs3".
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x1a) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    iEval (rewrite -Hpa4) in "Hs4".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x1c))
              (mword_of_int 2 : mword 6) Rs2 B1 (av - 6)%nat u4 b
              with "Hcg Hpc [] Hs4").
    { iApply (sdi_1c with "Htext"). }
    iIntros (CID13 Hk13) "Hcg Hpc Hs4".
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x1c) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    assert (HB1s1 : B1 !!! Regidx Rs1 = m !!! Regidx Rs1)
      by (apply HB1thr; vm_compute; first [reflexivity | discriminate]).
    assert (HB1s2 : B1 !!! Regidx Rs2 = m !!! Regidx Rs2)
      by (apply HB1thr; vm_compute; first [reflexivity | discriminate]).
    iEval (rewrite (rget_ne (CID := CID11) B1 Rs1 ltac:(vm_compute; discriminate))
             Hpa3 HB1s1) in "Hs3".
    iEval (rewrite (rget_ne (CID := CID12) B1 Rs2 ltac:(vm_compute; discriminate))
             Hpa4 HB1s2) in "Hs4".
    (* ---- +0x1e: ld s1,-40(s0) -- s1 := f ---- *)
    assert (Haddrf : add_vec (B1 !!! Regidx Rs0)
                       (sign_extend' 64 (mword_of_int 0xfd8 : mword 12)) = pa_stk sp0 5)
      by (rewrite HB1s0; apply sd_addr_f).
    iEval (rewrite -Haddrf) in "Hs5".
    iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x1e)) Rs1 Rs0
              (mword_of_int 0xfd8 : mword 12) B1 (av - 6)%nat fv b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hs5").
    { iApply (sdi_1e with "Htext"). }
    iIntros (CID14 Hk14) "Hcg Hpc Hs5".
    iEval (rewrite Haddrf) in "Hs5".
    set (B2 := <[Regidx Rs1 := regval_into_reg fv]> B1).
    change (<[Regidx Rs1 := regval_into_reg fv]> B1) with B2.
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x1e) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_dup + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    assert (HB2s1 : B2 !!! Regidx Rs1 = fv) by (rewrite /B2 upd_eq; reflexivity).
    assert (HB2sp : B2 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /B2 upd_ne; [exact HB1sp | vm_compute; discriminate]).
    assert (HB2s0 : B2 !!! Regidx Rs0 = sp0)
      by (rewrite /B2 upd_ne; [exact HB1s0 | vm_compute; discriminate]).
    (* ---- +0x22: c.mv a0,s1 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x22)) Ra0 Rs1 B2 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (sdi_22 with "Htext"). }
    iIntros (CID15 Hk15) "Hcg Hpc".
    set (B3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (B2 !!! Regidx Rs1))]> B2).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (B2 !!! Regidx Rs1))]> B2) with B3.
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x22) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    assert (HB3a0 : B3 !!! Regidx Ra0 = fv).
    { rewrite /B3 upd_eq HB2s1. apply add_vec_zero_l. }
    (* ---- +0x24: jal ra,fdalloc ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x24)) Rra
              (mword_of_int 2096696 : mword 21) B3 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (sdi_24 with "Htext"). }
    iIntros (CID16 Hk16) "Hcg Hpc".
    set (B4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x24) : mword 64) 4)]> B3).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x24) : mword 64) 4)]> B3) with B4.
    assert (Hjfd : add_vec (mword_of_int (KernelSyms.sys_dup + 0x24) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096696 : mword 21)) = mword_of_int KernelSyms.fdalloc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjfd) in "Hpc".
    assert (HB4ra : B4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x24) : mword 64) 4)
      by (rewrite /B4 upd_eq; reflexivity).
    assert (HB4a0 : B4 !!! Regidx Ra0 = fv)
      by (rewrite /B4 upd_ne; [exact HB3a0 | vm_compute; discriminate]).
    assert (HB4s1 : B4 !!! Regidx Rs1 = fv).
    { rewrite /B4 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [exact HB2s1 | vm_compute; discriminate]. }
    assert (HB4sp : B4 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /B4 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [exact HB2sp | vm_compute; discriminate]. }
    assert (HB4s0 : B4 !!! Regidx Rs0 = sp0).
    { rewrite /B4 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [exact HB2s0 | vm_compute; discriminate]. }
    (* ===================== THE LOAN =====================
       fdalloc wants the block, and filedup will want THIS descriptor's
       reference, so the reference comes out first and the array goes in
       holed. *)
    iDestruct (proc_priv_lend γf p pid V fd0 fv Hlk0 Hfvnz with "Hpriv")
      as (k q Cf stf) "((%Hfvk & %Hklt & %Hty) & Href & Hauth0 & Hcore & Hof)".
    iDestruct (cpu_own_transport CID9 CID16 n eb p b ltac:(wp_next_chain) with "Hcpu")
      as "Hcpu".
    iApply (Fdalloc.wp_fdalloc_sconf γf k {[fd0]} B4 (av - 6)%nat n eb p pid V b lks
              ltac:(rewrite HB4a0 Hfvk; reflexivity) Hklt Hn
              ltac:(lia)
              with "Hcg Hcpu Htext Hdata Hpc Hcore Hof").
    iIntros (CID17 Hk17 D0) "%HcsD0 Hcg Hcpu Hpc Hcore Hpost2".
    assert (Hpc28 : ret_pc (B4 !!! Regidx Rra) = mword_of_int (KernelSyms.sys_dup + 0x28))
      by (rewrite HB4ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    assert (HD0sp : D0 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite (callee_saved_lookup HcsD0 csp_rs1 ltac:(vm_compute; reflexivity)); exact HB4sp).
    assert (HD0s0 : D0 !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsD0 Rs0 ltac:(vm_compute; reflexivity)); exact HB4s0).
    assert (HD0s1 : D0 !!! Regidx Rs1 = fv)
      by (rewrite (callee_saved_lookup HcsD0 Rs1 ltac:(vm_compute; reflexivity)); exact HB4s1).
    assert (HD0thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> D0 !!! Regidx r = m !!! Regidx r).
    { intros r Hrr Ncsp N8 N9 N18.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hrr; vm_compute in Hrr; discriminate).
      assert (N10 : r <> mword_of_int 10)
        by (intro He; rewrite He in Hrr; vm_compute in Hrr; discriminate).
      rewrite (callee_saved_lookup HcsD0 r Hrr).
      rewrite /B4 upd_ne; [| congruence].
      rewrite /B3 upd_ne; [| congruence].
      rewrite /B2 upd_ne; [| congruence].
      apply HB1thr; assumption. }
    (* ---- +0x28: c.mv s2,a0 -- s2 := fd ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x28)) Rs2 Ra0 D0 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (sdi_28 with "Htext"). }
    iIntros (CID18 Hk18) "Hcg Hpc".
    set (D1 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (D0 !!! Regidx Ra0))]> D0).
    change (<[Regidx Rs2 := regval_into_reg (add_vec zero_reg (D0 !!! Regidx Ra0))]> D0) with D1.
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x28) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    assert (HD1s2 : D1 !!! Regidx Rs2 = D0 !!! Regidx Ra0).
    { rewrite /D1 upd_eq. apply add_vec_zero_l. }
    assert (HD1a0 : D1 !!! Regidx Ra0 = D0 !!! Regidx Ra0)
      by (rewrite /D1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HD1s1 : D1 !!! Regidx Rs1 = fv)
      by (rewrite /D1 upd_ne; [exact HD0s1 | vm_compute; discriminate]).
    assert (HD1sp : D1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /D1 upd_ne; [exact HD0sp | vm_compute; discriminate]).
    assert (HD1s0 : D1 !!! Regidx Rs0 = sp0)
      by (rewrite /D1 upd_ne; [exact HD0s0 | vm_compute; discriminate]).
    assert (HD1thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> D1 !!! Regidx r = m !!! Regidx r).
    { intros r Hrr Ncsp N8 N9 N18.
      rewrite /D1 upd_ne; [| congruence]. apply HD0thr; assumption. }
    (* ---- +0x2a: c.li a5,-1 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x2a)) Ra5 (mword_of_int 63 : mword 6)
              (mword_of_int (-1) : mword 64) D1 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (sdi_2a with "Htext"). }
    iIntros (CID19 Hk19) "Hcg Hpc".
    set (D2 := <[Regidx Ra5 := regval_into_reg (mword_of_int (-1) : mword 64)]> D1).
    change (<[Regidx Ra5 := regval_into_reg (mword_of_int (-1) : mword 64)]> D1) with D2.
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x2a) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    assert (HD2a5 : D2 !!! Regidx Ra5 = (mword_of_int (-1) : mword 64))
      by (rewrite /D2 upd_eq; reflexivity).
    assert (HD2a0 : D2 !!! Regidx Ra0 = D0 !!! Regidx Ra0)
      by (rewrite /D2 upd_ne; [exact HD1a0 | vm_compute; discriminate]).
    assert (HD2s1 : D2 !!! Regidx Rs1 = fv)
      by (rewrite /D2 upd_ne; [exact HD1s1 | vm_compute; discriminate]).
    assert (HD2s2 : D2 !!! Regidx Rs2 = D0 !!! Regidx Ra0)
      by (rewrite /D2 upd_ne; [exact HD1s2 | vm_compute; discriminate]).
    assert (HD2sp : D2 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /D2 upd_ne; [exact HD1sp | vm_compute; discriminate]).
    assert (HD2s0 : D2 !!! Regidx Rs0 = sp0)
      by (rewrite /D2 upd_ne; [exact HD1s0 | vm_compute; discriminate]).
    assert (HD2thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> D2 !!! Regidx r = m !!! Regidx r).
    { intros r Hrr Ncsp N8 N9 N18.
      assert (N15 : r <> mword_of_int 15)
        by (intro He; rewrite He in Hrr; vm_compute in Hrr; discriminate).
      rewrite /D2 upd_ne; [| congruence]. apply HD1thr; assumption. }
    (* ---- +0x2c: bltz a0 -- did fdalloc fail? ---- *)
    rewrite /fdalloc_post. iDestruct "Hpost2" as "[Hf2 | Hs2ok]".
    { (* ============ the table was full: return -1, undo nothing ============ *)
      iDestruct "Hf2" as "([%Hr2 %Hnone2] & Hof)".
      (* the reference goes straight back where it came from *)
      (* NOT [set_solver]: it runs naive_solver over the WHOLE context, which
         here is ~200 hypotheses of large mword terms -- 106 s for [fd0 not in
         {}].  See claude-notes/optimization.md. *)
      iDestruct (proc_ofiles_repay γf (pv_fdg V) p (pv_ofile V) ∅ fd0 k q Cf stf
                   ltac:(apply not_elem_of_empty)
                   ltac:(rewrite Hlk0 Hfvk; reflexivity) Hklt Hty
                   with "[Hof] Href Hauth0") as "Hof".
      { rewrite (union_empty_r_L {[fd0]}). iExact "Hof". }
      iDestruct (proc_priv_join with "Hcore Hof") as "Hpriv".
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x2c))
                (mword_of_int 26 : mword 13) Ra0 D2 (av - 6)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HD2a0 Hr2; exact sd_m1_neg)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (sdi_2c with "Htext"). }
      iApply bi.later_intro. iIntros (CID20 Hk20) "Hcg Hpc".
      assert (Htgt46 : add_vec (mword_of_int (KernelSyms.sys_dup + 0x2c) : mword 64)
                         (sign_extend' 64 (mword_of_int 26 : mword 13))
                       = mword_of_int (KernelSyms.sys_dup + 0x46))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt46) in "Hpc".
      (* ---- +0x46 / +0x48: pop s1 and s2 ---- *)
      assert (Hpb3 : add_vec (D2 !!! Regidx csp_rs1)
                       (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
      { rewrite HD2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite -Hpb3) in "Hs3".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x46))
                (mword_of_int 3 : mword 6) Rs1 D2 (av - 6)%nat (m !!! Regidx Rs1) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hs3").
      { iApply (sdi_46 with "Htext"). }
      iIntros (CID21 Hk21) "Hcg Hpc Hs3".
      iEval (rewrite Hpb3) in "Hs3".
      set (F1 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> D2).
      change (<[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> D2) with F1.
      assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x46) : mword 64) 2
                      = mword_of_int (KernelSyms.sys_dup + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp48) in "Hpc".
      assert (HF1sp : F1 !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite /F1 upd_ne; [exact HD2sp | vm_compute; discriminate]).
      assert (Hpb4 : add_vec (F1 !!! Regidx csp_rs1)
                       (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
      { rewrite HF1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite -Hpb4) in "Hs4".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x48))
                (mword_of_int 2 : mword 6) Rs2 F1 (av - 6)%nat (m !!! Regidx Rs2) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hs4").
      { iApply (sdi_48 with "Htext"). }
      iIntros (CID22 Hk22) "Hcg Hpc Hs4".
      iEval (rewrite Hpb4) in "Hs4".
      set (F2 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> F1).
      change (<[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> F1) with F2.
      assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x48) : mword 64) 2
                      = mword_of_int (KernelSyms.sys_dup + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4a) in "Hpc".
      (* ---- +0x4a: c.j -> the epilogue ---- *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x4a))
                (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")))
                F2 (av - 6)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (sdi_4a with "Htext"). }
      iIntros (CID23 Hk23). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htgt3c : add_vec (mword_of_int (KernelSyms.sys_dup + 0x4a) : mword 64)
                         (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0"))))
                       = mword_of_int (KernelSyms.sys_dup + 0x3c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt3c) in "Hpc".
      assert (HF2sp : F2 !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite /F2 upd_ne; [exact HF1sp | vm_compute; discriminate]).
      assert (HF2a5 : F2 !!! Regidx Ra5 = (mword_of_int (-1) : mword 64)).
      { rewrite /F2 upd_ne; [| vm_compute; discriminate].
        rewrite /F1 upd_ne; [exact HD2a5 | vm_compute; discriminate]. }
      assert (HF2thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> F2 !!! Regidx r = m !!! Regidx r).
      { intros r Hrr Ncsp N8.
        destruct (decide (r = Rs2)) as [->|N18]; [by rewrite /F2 upd_eq|].
        rewrite /F2 upd_ne; [| congruence].
        destruct (decide (r = Rs1)) as [->|N9]; [by rewrite /F1 upd_eq|].
        rewrite /F1 upd_ne; [| congruence]. apply HD2thr; assumption. }
      assert (HshCID23 : b = false \/ p = zero_reg -> (CID23 : CPU) = (CID : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift HshCID23 with "Hcont") as "Hcont".
      iApply (sd_tail (CID0 := CID23) m F2 av (mword_of_int (-1) : mword 64)
                sp0 ra0 s00 (m !!! Regidx Rs1) (m !!! Regidx Rs2) fv w6 p b
                ltac:(lia) eq_refl eq_refl eq_refl HF2sp HF2a5 HF2thr
                with "Hcg Htext Hpc Hs1 Hs2 Hs3 Hs4 Hs5 Hs6").
      iIntros (CIDz2 Hkz2 Fz2) "%HcsF Hcg Hpc".
      destruct HcsF as [HcsF HFa0].
      iDestruct (cpu_own_transport CID17 CIDz2 n eb p b ltac:(wp_next_chain) with "Hcpu")
      as "Hcpu".
    iSpecialize ("Hcont" $! CIDz2 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Fz2 with "[%] Hcg Hcpu Hpc [Hpriv Hfrag]"); [exact HcsF|].
      rewrite /sys_dup_post. iRight. iLeft.
      iExists fd0, fv. iSplitR; [| iFrame "Hpriv Hfrag"].
      iPureIntro. split; [exact HFa0|]. split; [exact Hsome | exact Hnone2]. }
    (* ============ the descriptor was allocated: duplicate ============ *)
    iDestruct "Hs2ok" as (fd1 l) "([%Hr2 %Hfr1] & Hof & Hunit & Hauth1)".
    pose proof (fd_frees_head_lt (pv_ofile V) fd1 l Hfr1) as Hfd1len.
    assert (Hfd1N : (fd1 < NOFILE)%nat) by (rewrite -Hoflen; exact Hfd1len).
    assert (Hfree1 : pv_ofile V !! fd1 = Some (zero_reg : mword 64))
      by exact (fd_frees_head (pv_ofile V) fd1 l Hfr1).
    (* THE TWO DESCRIPTORS ARE DISTINCT: fd0's entry is non-null, fd1's is *)
    assert (Hne01 : fd1 <> fd0).
    { intro He. rewrite He Hlk0 in Hfree1. injection Hfree1 as He2.
      apply Hfvnz. exact He2. }
    iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x2c))
              (mword_of_int 26 : mword 13) Ra0 D2 (av - 6)%nat b
              ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite HD2a0 Hr2; apply sd_fd_nonneg; apply sd_fd_range; exact Hfd1N)
              with "Hcg Hpc []").
    { iApply (sdi_2c with "Htext"). }
    iIntros (CID20 Hk20) "Hcg Hpc".
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x2c) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_dup + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* ---- +0x30: c.mv a0,s1 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x30)) Ra0 Rs1 D2 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (sdi_30 with "Htext"). }
    iIntros (CID21 Hk21) "Hcg Hpc".
    set (G1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (D2 !!! Regidx Rs1))]> D2).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (D2 !!! Regidx Rs1))]> D2) with G1.
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x30) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    assert (HG1a0 : G1 !!! Regidx Ra0 = fv).
    { rewrite /G1 upd_eq HD2s1. apply add_vec_zero_l. }
    (* ---- +0x32: jal ra,filedup ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x32)) Rra
              (mword_of_int 2093974 : mword 21) G1 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (sdi_32 with "Htext"). }
    iIntros (CID22 Hk22) "Hcg Hpc".
    set (G2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x32) : mword 64) 4)]> G1).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x32) : mword 64) 4)]> G1) with G2.
    assert (Hjfdp : add_vec (mword_of_int (KernelSyms.sys_dup + 0x32) : mword 64)
                      (sign_extend' 64 (mword_of_int 2093974 : mword 21)) = mword_of_int KernelSyms.filedup)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjfdp) in "Hpc".
    assert (HG2ra : G2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x32) : mword 64) 4)
      by (rewrite /G2 upd_eq; reflexivity).
    assert (HG2a0 : G2 !!! Regidx Ra0 = fv)
      by (rewrite /G2 upd_ne; [exact HG1a0 | vm_compute; discriminate]).
    assert (HG2sp : G2 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /G2 upd_ne; [| vm_compute; discriminate].
      rewrite /G1 upd_ne; [exact HD2sp | vm_compute; discriminate]. }
    assert (HG2s2 : G2 !!! Regidx Rs2 = D0 !!! Regidx Ra0).
    { rewrite /G2 upd_ne; [| vm_compute; discriminate].
      rewrite /G1 upd_ne; [exact HD2s2 | vm_compute; discriminate]. }
    assert (HG2thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> G2 !!! Regidx r = m !!! Regidx r).
    { intros r Hrr Ncsp N8 N9 N18.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hrr; vm_compute in Hrr; discriminate).
      assert (N10 : r <> mword_of_int 10)
        by (intro He; rewrite He in Hrr; vm_compute in Hrr; discriminate).
      rewrite /G2 upd_ne; [| congruence].
      rewrite /G1 upd_ne; [| congruence].
      apply HD2thr; assumption. }
    iDestruct (cpu_own_transport CID17 CID22 n eb p b ltac:(wp_next_chain) with "Hcpu")
      as "Hcpu".
    (* THE UNIT fdalloc RELEASED IS WHAT PAYS FOR THE HIGHER COUNT *)
    iApply (Filedup.wp_filedup_sconf γl γf k q Cf _ G2 n eb p (av - 6)%nat b lks
              ltac:(lia) Hn ltac:(rewrite HG2a0 Hfvk; reflexivity) Hftno
              with "Hcg Hcpu Htext Hpc Hftab Hunit Href").
    all: try lkbelow.
    iIntros (CID23 Hk23 G3) "Hcg Hcpu Hpc [%HcsG3 %HG3a0] Href0 Href1".
    assert (Hpc36 : ret_pc (G2 !!! Regidx Rra) = mword_of_int (KernelSyms.sys_dup + 0x36))
      by (rewrite HG2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc36) in "Hpc".
    assert (HG3sp : G3 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite (callee_saved_lookup HcsG3 csp_rs1 ltac:(vm_compute; reflexivity)); exact HG2sp).
    assert (HG3s2 : G3 !!! Regidx Rs2 = D0 !!! Regidx Ra0)
      by (rewrite (callee_saved_lookup HcsG3 Rs2 ltac:(vm_compute; reflexivity)); exact HG2s2).
    assert (HG3thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> G3 !!! Regidx r = m !!! Regidx r).
    { intros r Hrr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup HcsG3 r Hrr). apply HG2thr; assumption. }
    (* ===================== THE TWO REPAYMENTS =====================
       filedup handed back two halves; one settles the destination descriptor
       fdalloc filled, the other the source we borrowed from. *)
    assert (Hlk1 : pv_ofile (upd_ofile V fd1 (fnode k)) !! fd1 = Some (fnode k)).
    { cbn [upd_ofile pv_ofile pv_fdg]. apply list_lookup_insert. rewrite Hoflen. exact Hfd1N. }
    assert (Hlk0' : pv_ofile (upd_ofile V fd1 (fnode k)) !! fd0 = Some (fnode k)).
    { cbn [upd_ofile pv_ofile pv_fdg]. rewrite list_lookup_insert_ne; [| exact Hne01].
      rewrite Hlk0 Hfvk. reflexivity. }
    (* THE DESTINATION IS THE ONE THAT CHANGES STATE.  fdalloc handed out its
       authority at [FdClosed]; it has to arrive at the source file's type,
       and that move is what this syscall spends the fragment bundle on. *)
    iDestruct (fd_frags_any_acc (pv_fdg V) fd1 Hfd1N with "Hfrag")
      as (stq) "[Hfr Hfrback]".
    iMod (fd_st_move _ fd1 FdClosed stq stf with "Hauth1 Hfr")
      as "[Hauth1 Hfr]".
    iDestruct ("Hfrback" with "Hfr") as "Hfrag".
    iDestruct (proc_ofiles_repay γf (pv_fdg V) p (pv_ofile (upd_ofile V fd1 (fnode k)))
                 {[fd0]} fd1 k (q/2)%Qp Cf stf
                 ltac:(apply not_elem_of_singleton_2; exact Hne01)
                 Hlk1 Hklt Hty with "Hof Href0 Hauth1") as "Hof".
    (* the SOURCE keeps its state: the authority the loan took out goes back
       exactly as it came, so no second bundle access is needed. *)
    iDestruct (proc_ofiles_repay γf (pv_fdg V) p (pv_ofile (upd_ofile V fd1 (fnode k)))
                 ∅ fd0 k (q/2)%Qp Cf stf ltac:(apply not_elem_of_empty) Hlk0' Hklt Hty
                 with "[Hof] Href1 Hauth0") as "Hof".
    { rewrite (union_empty_r_L {[fd0]}). iExact "Hof". }
    iDestruct (proc_priv_join with "[Hcore] Hof") as "Hpriv".
    { rewrite proc_priv_core_upd_ofile. iExact "Hcore". }
    (* ---- +0x36: c.mv a5,s2 -- the return value ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x36)) Ra5 Rs2 G3 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (sdi_36 with "Htext"). }
    iIntros (CID24 Hk24) "Hcg Hpc".
    set (G4 := <[Regidx Ra5 := regval_into_reg (add_vec zero_reg (G3 !!! Regidx Rs2))]> G3).
    change (<[Regidx Ra5 := regval_into_reg (add_vec zero_reg (G3 !!! Regidx Rs2))]> G3) with G4.
    assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x36) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp38) in "Hpc".
    assert (HG4a5 : G4 !!! Regidx Ra5 = (mword_of_int (Z.of_nat fd1) : mword 64)).
    { rewrite /G4 upd_eq HG3s2 -Hr2. apply add_vec_zero_l. }
    assert (HG4sp : G4 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /G4 upd_ne; [exact HG3sp | vm_compute; discriminate]).
    (* ---- +0x38 / +0x3a: pop s1 and s2 ---- *)
    assert (Hpc3 : add_vec (G4 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HG4sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpc3) in "Hs3".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x38))
              (mword_of_int 3 : mword 6) Rs1 G4 (av - 6)%nat (m !!! Regidx Rs1) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hs3").
    { iApply (sdi_38 with "Htext"). }
    iIntros (CID25 Hk25) "Hcg Hpc Hs3".
    iEval (rewrite Hpc3) in "Hs3".
    set (G5 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> G4).
    change (<[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> G4) with G5.
    assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x38) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3a) in "Hpc".
    assert (HG5sp : G5 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /G5 upd_ne; [exact HG4sp | vm_compute; discriminate]).
    assert (Hpc4 : add_vec (G5 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HG5sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpc4) in "Hs4".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x3a))
              (mword_of_int 2 : mword 6) Rs2 G5 (av - 6)%nat (m !!! Regidx Rs2) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hs4").
    { iApply (sdi_3a with "Htext"). }
    iIntros (CID26 Hk26) "Hcg Hpc Hs4".
    iEval (rewrite Hpc4) in "Hs4".
    set (G6 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> G5).
    change (<[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> G5) with G6.
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x3a) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3c) in "Hpc".
    assert (HG6sp : G6 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /G6 upd_ne; [exact HG5sp | vm_compute; discriminate]).
    assert (HG6a5 : G6 !!! Regidx Ra5 = (mword_of_int (Z.of_nat fd1) : mword 64)).
    { rewrite /G6 upd_ne; [| vm_compute; discriminate].
      rewrite /G5 upd_ne; [exact HG4a5 | vm_compute; discriminate]. }
    assert (HG6thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> G6 !!! Regidx r = m !!! Regidx r).
    { intros r Hrr Ncsp N8.
      destruct (decide (r = Rs2)) as [->|N18]; [by rewrite /G6 upd_eq|].
      rewrite /G6 upd_ne; [| congruence].
      destruct (decide (r = Rs1)) as [->|N9]; [by rewrite /G5 upd_eq|].
      rewrite /G5 upd_ne; [| congruence].
      assert (N15 : r <> mword_of_int 15)
        by (intro He; rewrite He in Hrr; vm_compute in Hrr; discriminate).
      rewrite /G4 upd_ne; [| congruence].
      apply HG3thr; assumption. }
    (* ---- the epilogue ---- *)
    assert (HshCID26 : b = false \/ p = zero_reg -> (CID26 : CPU) = (CID : CPU)) by wp_next_chain.
    iDestruct (wp_next_shift HshCID26 with "Hcont") as "Hcont".
    iApply (sd_tail (CID0 := CID26) m G6 av (mword_of_int (Z.of_nat fd1) : mword 64)
              sp0 ra0 s00 (m !!! Regidx Rs1) (m !!! Regidx Rs2) fv w6 p b
              ltac:(lia) eq_refl eq_refl eq_refl HG6sp HG6a5 HG6thr
              with "Hcg Htext Hpc Hs1 Hs2 Hs3 Hs4 Hs5 Hs6").
    iIntros (CIDz3 Hkz3 Fz3) "%HcsF Hcg Hpc".
    destruct HcsF as [HcsF HFa0].
    iDestruct (cpu_own_transport CID23 CIDz3 n eb p b ltac:(wp_next_chain) with "Hcpu")
      as "Hcpu".
    iSpecialize ("Hcont" $! CIDz3 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Fz3 with "[%] Hcg Hcpu Hpc [Hpriv Hfrag]"); [exact HcsF|].
    rewrite /sys_dup_post. iRight. iRight.
    iExists fd0, fd1, fv, l. iSplitR.
    { iPureIntro. split; [exact HFa0|]. split; [exact Hsome | exact Hfr1]. }
    rewrite Hfvk. iFrame "Hpriv Hfrag".
  Qed.

End ProofSysDup.

End SysDupProof.
