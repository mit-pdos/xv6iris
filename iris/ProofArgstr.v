(* ProofArgstr.v -- the whole-function WP for xv6's argstr().

     int argstr(int n, char *buf, int max) {
       uint64 addr;
       argaddr(n, &addr);
       return fetchstr(addr, buf, max);
     }

   Twenty instructions, a 32-byte frame with all four slots used, and NO
   BRANCH AT ALL: argaddr is inlined to a bare [jal argraw] whose [a0] goes
   straight into fetchstr, so the local [uint64 addr] never reaches memory.
   That is what makes this the shortest proof in the cone -- one straight
   line from the prologue to the epilogue, with no arms to rejoin and hence
   no tail lemma.  The contract is SpecArgstr.v.

   THE ONE STRUCTURAL IDEA: [proc_priv] is split TWICE, in sequence and never
   at once.  argraw wants the trapframe page, which [ProcInv.proc_priv_tf]
   lends out and takes back around the call; fetchstr wants the block WHOLE
   (it does its own [proc_priv_copy] inside).  Because the two calls are
   sequential, the first borrow is closed before the second is opened, and
   neither accessor ever has to know about the other.

   THE FRAME IS ASYMMETRIC, as in fetchaddr: [c.addi sp,-32] pushes but
   [c.addi16sp sp,32] pops. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile WpMmodeLeafBase.
Require Import SmodeCore.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import CpuOwn.
Require Import StackOwn CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpLock.
Require Import UserPtTree.
Require Import FdSlots FileInv ProcInv.
Require Import CodeArgstr.
Require Import SpecArgraw SpecFetchstr.
Require Import SpecArgstr.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.



Module ArgstrProof (Argraw : ARGRAW) (Fetchstr : FETCHSTR) : ARGSTR.

Section ProofArgstr.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).

  Lemma wp_argstr_sconf (γf : gname) (Φ : mval -> iProp Σ)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (i : nat) (v : mword 64)
      (pid : mword 32) (V : pprivate) (maxn : nat) (buf_olds : nat -> bv 8) (b : bool)
    : wp_argstr_sconf_body γf Φ m av n eb p C i v pid V maxn buf_olds b.
  Proof.
    cbv beta delta [wp_argstr_sconf_body].
    intros pcE buf ret_tgt Hi Ha0 Hargs Hn Hav Hmax Hmax31.
    unfold argstr_stack in Hav.
    set (sp0 := m !!! Regidx csp_rs1).
    set (ra0 := m !!! Regidx Rra).
    set (s00 := m !!! Regidx Rs0).
    set (s10 := m !!! Regidx Rs1).
    set (s20 := m !!! Regidx Rs2).
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    iIntros "Hcg Hcpu #Htext #Hdata Hpc Hpriv Hbuf Hcont".
    iPoseProof (asi_00 with "Htext") as "Hi00".
    iPoseProof (asi_02 with "Htext") as "Hi02".
    iPoseProof (asi_04 with "Htext") as "Hi04".
    iPoseProof (asi_06 with "Htext") as "Hi06".
    iPoseProof (asi_08 with "Htext") as "Hi08".
    iPoseProof (asi_0a with "Htext") as "Hi0a".
    iPoseProof (asi_0c with "Htext") as "Hi0c".
    iPoseProof (asi_0e with "Htext") as "Hi0e".
    iPoseProof (asi_10 with "Htext") as "Hi10".
    iPoseProof (asi_14 with "Htext") as "Hi14".
    iPoseProof (asi_16 with "Htext") as "Hi16".
    iPoseProof (asi_18 with "Htext") as "Hi18".
    iPoseProof (asi_1c with "Htext") as "Hi1c".
    iPoseProof (asi_1e with "Htext") as "Hi1e".
    iPoseProof (asi_20 with "Htext") as "Hi20".
    iPoseProof (asi_22 with "Htext") as "Hi22".
    iPoseProof (asi_24 with "Htext") as "Hi24".
    iPoseProof (asi_26 with "Htext") as "Hi26".
    (* ---- +0x00: c.addi sp,-32 (frame push) ---- *)
    iApply (wp_caddi_sp_push_s_sconf Φ pcE (mword_of_int 32 : mword 6) m av 4 b
              ltac:(lia) (stk_push_32 (m !!! Regidx csp_rs1))
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hk1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
              (add_vec (m !!! Regidx csp_rs1)
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with M1.
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.argstr + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /M1 upd_eq; apply stk_push_32).
    iDestruct (stack_own_4_elim with "Hframe") as (u1 u2 u3 u4) "(Hs1 & Hs2 & Hs3 & Hs4)".
    (* ---- +0x02 .. +0x08: save ra / s0 / s1 / s2 ---- *)
    assert (Hpa1 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa2 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa3 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa4 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hs1".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.argstr + 0x02))
              (mword_of_int 3 : mword 6) Rra M1 (av - 4)%nat u1 b
              with "Hcg Hpc Hi02 Hs1 [-]").
    iIntros (CID2 Hk2) "Hcg Hpc Hs1".
    iEval (rgne) in "Hs1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.argstr + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.argstr + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iEval (rewrite -Hpa2) in "Hs2".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.argstr + 0x04))
              (mword_of_int 2 : mword 6) Rs0 M1 (av - 4)%nat u2 b
              with "Hcg Hpc Hi04 Hs2 [-]").
    iIntros (CID3 Hk3) "Hcg Hpc Hs2".
    iEval (rgne) in "Hs2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.argstr + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.argstr + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iEval (rewrite -Hpa3) in "Hs3".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.argstr + 0x06))
              (mword_of_int 1 : mword 6) Rs1 M1 (av - 4)%nat u3 b
              with "Hcg Hpc Hi06 Hs3 [-]").
    iIntros (CID4 Hk4) "Hcg Hpc Hs3".
    iEval (rgne) in "Hs3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.argstr + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.argstr + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iEval (rewrite -Hpa4) in "Hs4".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.argstr + 0x08))
              (mword_of_int 0 : mword 6) Rs2 M1 (av - 4)%nat u4 b
              with "Hcg Hpc Hi08 Hs4 [-]").
    iIntros (CID5 Hk5) "Hcg Hpc Hs4".
    iEval (rgne) in "Hs4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.argstr + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.argstr + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    assert (HM1ra : M1 !!! Regidx Rra = ra0)
      by (rewrite /M1 upd_ne; [reflexivity | reg_neq]).
    assert (HM1s0 : M1 !!! Regidx Rs0 = s00)
      by (rewrite /M1 upd_ne; [reflexivity | reg_neq]).
    assert (HM1s1 : M1 !!! Regidx Rs1 = s10)
      by (rewrite /M1 upd_ne; [reflexivity | reg_neq]).
    assert (HM1s2 : M1 !!! Regidx Rs2 = s20)
      by (rewrite /M1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite Hpa1 HM1ra) in "Hs1".
    iEval (rewrite Hpa2 HM1s0) in "Hs2".
    iEval (rewrite Hpa3 HM1s1) in "Hs3".
    iEval (rewrite Hpa4 HM1s2) in "Hs4".
    (* ---- +0x0a: c.addi4spn s0,sp,32 (s0's VALUE is never read) ---- *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (KernelSyms.argstr + 0x0a))
              (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) Rs0
              M1 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hk6) "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1).
    change (<[Regidx Rs0 := regval_into_reg
              (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1) with M2.
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.argstr + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.argstr + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* ---- +0x0c: c.mv s2,a1 -- s2 := buf ---- *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.argstr + 0x0c))
              Rs2 Ra1 M2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID7 Hk7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (M3 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (M2 !!! Regidx Ra1))]> M2).
    change (<[Regidx Rs2 := regval_into_reg (add_vec zero_reg (M2 !!! Regidx Ra1))]> M2) with M3.
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.argstr + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.argstr + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* ---- +0x0e: c.mv s1,a2 -- s1 := max ---- *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.argstr + 0x0e))
              Rs1 Ra2 M3 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID8 Hk8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (M4 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (M3 !!! Regidx Ra2))]> M3).
    change (<[Regidx Rs1 := regval_into_reg (add_vec zero_reg (M3 !!! Regidx Ra2))]> M3) with M4.
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.argstr + 0x0e) : mword 64) 2
                    = mword_of_int (KernelSyms.argstr + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* what the two [c.mv]s parked *)
    assert (HM2a1 : M2 !!! Regidx Ra1 = buf).
    { rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    assert (HM3s2 : M3 !!! Regidx Rs2 = buf)
      by (rewrite /M3 upd_eq HM2a1; apply add_vec_zero_l).
    assert (HM3a2 : M3 !!! Regidx Ra2 = (mword_of_int (Z.of_nat maxn) : mword 64)).
    { rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [| reg_neq].
      rewrite /M1 upd_ne; [exact Hmax | reg_neq]. }
    assert (HM4s1 : M4 !!! Regidx Rs1 = (mword_of_int (Z.of_nat maxn) : mword 64))
      by (rewrite /M4 upd_eq HM3a2; apply add_vec_zero_l).
    assert (HM4s2 : M4 !!! Regidx Rs2 = buf)
      by (rewrite /M4 upd_ne; [exact HM3s2 | reg_neq]).
    assert (HM4a0 : M4 !!! Regidx Ra0 = mword_of_int (Z.of_nat i)).
    { rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_ne; [| reg_neq].
      rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [exact Ha0 | reg_neq]. }
    assert (HM4sp : M4 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_ne; [| reg_neq].
      rewrite /M2 upd_ne; [| reg_neq]. exact HM1sp. }
    (* ---- +0x10: jal ra,argraw ---- *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.argstr + 0x10))
              Rra (mword_of_int 2096846 : mword 21) M4 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi10 [-]").
    iIntros (CID9 Hk9) "Hcg Hpc".
    set (M5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.argstr + 0x10) : mword 64) 4)]> M4).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.argstr + 0x10) : mword 64) 4)]> M4) with M5.
    assert (Hjar : add_vec (mword_of_int (KernelSyms.argstr + 0x10) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096846 : mword 21)) = mword_of_int KernelSyms.argraw)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjar) in "Hpc".
    assert (HM5ra : M5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.argstr + 0x10) : mword 64) 4)
      by (rewrite /M5 upd_eq; reflexivity).
    assert (HM5a0 : M5 !!! Regidx Ra0 = mword_of_int (Z.of_nat i))
      by (rewrite /M5 upd_ne; [exact HM4a0 | reg_neq]).
    assert (HM5sp : M5 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /M5 upd_ne; [exact HM4sp | reg_neq]).
    assert (HM5s1 : M5 !!! Regidx Rs1 = (mword_of_int (Z.of_nat maxn) : mword 64))
      by (rewrite /M5 upd_ne; [exact HM4s1 | reg_neq]).
    assert (HM5s2 : M5 !!! Regidx Rs2 = buf)
      by (rewrite /M5 upd_ne; [exact HM4s2 | reg_neq]).
    (* the residual threading fact, established once at the call boundary *)
    assert (HthrM5 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> M5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /M5 upd_ne; [| congruence].
      rewrite /M4 upd_ne; [| congruence].
      rewrite /M3 upd_ne; [| congruence].
      rewrite /M2 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence]. reflexivity. }
    (* ---- the FIRST borrow: argraw wants the trapframe page ---- *)
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfp & Htfa & Hpbacktf)".
    iDestruct (cpu_own_transport CID CID9 n eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Argraw.wp_argraw_sconf Φ M5 (av - 4)%nat n eb p C
              i (ud_tfp (pv_upt V)) (pv_tf V) v (DfracOwn (1/4)) b
              Hi HM5a0 Hargs Hn ltac:(lia)
              with "Hcg Hcpu Htext Hdata Hpc Htfp Htfa [-]").
    iIntros (CID10 Hk10 A) "[%HcsA %HAa0] Hcg Hcpu Hpc Htfp Htfa".
    iDestruct ("Hpbacktf" with "Htfp Htfa") as "Hpriv".
    assert (Hpc14 : ret_pc (M5 !!! Regidx Rra) = mword_of_int (KernelSyms.argstr + 0x14))
      by (rewrite HM5ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    assert (HAsp : A !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)); exact HM5sp).
    assert (HAs1 : A !!! Regidx Rs1 = (mword_of_int (Z.of_nat maxn) : mword 64))
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HM5s1).
    assert (HAs2 : A !!! Regidx Rs2 = buf)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 18) ltac:(vm_compute; reflexivity)); exact HM5s2).
    assert (HthrA : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> A !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup HcsA r Hr). apply HthrM5; assumption. }
    (* ---- +0x14: c.mv a2,s1 -- a2 := max ---- *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.argstr + 0x14))
              Ra2 Rs1 A (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [-]").
    iIntros (CID11 Hk11) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A1 := <[Regidx Ra2 := regval_into_reg (add_vec zero_reg (A !!! Regidx Rs1))]> A).
    change (<[Regidx Ra2 := regval_into_reg (add_vec zero_reg (A !!! Regidx Rs1))]> A) with A1.
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.argstr + 0x14) : mword 64) 2
                    = mword_of_int (KernelSyms.argstr + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* ---- +0x16: c.mv a1,s2 -- a1 := buf ---- *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.argstr + 0x16))
              Ra1 Rs2 A1 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [-]").
    iIntros (CID12 Hk12) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A2 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Rs2))]> A1).
    change (<[Regidx Ra1 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Rs2))]> A1) with A2.
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.argstr + 0x16) : mword 64) 2
                    = mword_of_int (KernelSyms.argstr + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    assert (HA1s2 : A1 !!! Regidx Rs2 = buf)
      by (rewrite /A1 upd_ne; [exact HAs2 | reg_neq]).
    assert (HA2a1 : A2 !!! Regidx Ra1 = buf)
      by (rewrite /A2 upd_eq HA1s2; apply add_vec_zero_l).
    assert (HA2a2 : A2 !!! Regidx Ra2 = (mword_of_int (Z.of_nat maxn) : mword 64)).
    { rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_eq HAs1. apply add_vec_zero_l. }
    assert (HA2sp : A2 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [exact HAsp | reg_neq]. }
    (* ---- +0x18: jal ra,fetchstr ---- *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.argstr + 0x18))
              Rra (mword_of_int 2097008 : mword 21) A2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi18 [-]").
    iIntros (CID13 Hk13) "Hcg Hpc".
    set (A3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.argstr + 0x18) : mword 64) 4)]> A2).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.argstr + 0x18) : mword 64) 4)]> A2) with A3.
    assert (Hjfs : add_vec (mword_of_int (KernelSyms.argstr + 0x18) : mword 64)
                     (sign_extend' 64 (mword_of_int 2097008 : mword 21)) = mword_of_int KernelSyms.fetchstr)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjfs) in "Hpc".
    assert (HA3ra : A3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.argstr + 0x18) : mword 64) 4)
      by (rewrite /A3 upd_eq; reflexivity).
    assert (HA3a1 : A3 !!! Regidx Ra1 = buf)
      by (rewrite /A3 upd_ne; [exact HA2a1 | reg_neq]).
    assert (HA3a2 : A3 !!! Regidx Ra2 = (mword_of_int (Z.of_nat maxn) : mword 64))
      by (rewrite /A3 upd_ne; [exact HA2a2 | reg_neq]).
    assert (HA3sp : A3 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /A3 upd_ne; [exact HA2sp | reg_neq]).
    assert (HthrA3 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> A3 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N11 : r <> mword_of_int 11)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N12 : r <> mword_of_int 12)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence]. apply HthrA; assumption. }
    assert (HKfs : (fetchstr_stack <= av - 4)%nat) by (unfold fetchstr_stack; lia).
    iEval (rewrite -HA3a1) in "Hbuf".
    (* ---- fetchstr(addr, buf, max) ---- *)
    iDestruct (cpu_own_transport CID10 CID13 n eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Fetchstr.wp_fetchstr_sconf γf Φ A3 (av - 4)%nat n eb p C pid V maxn buf_olds b
              Hn HKfs HA3a2 Hmax31
              with "Hcg Hcpu Htext Hpc Hpriv Hbuf [-]").
    iIntros (CID14 Hk14 mr buf_new) "%Hcsr Hcg Hcpu Hpc Hpriv Hbuf %Hret".
    iEval (rewrite HA3a1) in "Hbuf".
    assert (Hpc1c : ret_pc (A3 !!! Regidx Rra) = mword_of_int (KernelSyms.argstr + 0x1c))
      by (rewrite HA3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    assert (Hrsp : mr !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite (callee_saved_lookup Hcsr csp_rs1 ltac:(vm_compute; reflexivity)); exact HA3sp).
    assert (Hthrr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> mr !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcsr r Hr). apply HthrA3; assumption. }
    (* ===================== EPILOGUE ===================== *)
    (* ---- +0x1c: c.ldsp ra,24(sp) ---- *)
    assert (Hqa1 : add_vec (mr !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hrsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hqa1) in "Hs1".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.argstr + 0x1c))
              (mword_of_int 3 : mword 6) Rra mr (av - 4)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c Hs1 [-]").
    iIntros (CID15 Hk15) "Hcg Hpc Hs1".
    iEval (rewrite Hqa1) in "Hs1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> mr).
    change (<[Regidx Rra := regval_into_reg ra0]> mr) with T1.
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.argstr + 0x1c) : mword 64) 2
                    = mword_of_int (KernelSyms.argstr + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T1 upd_ne; [exact Hrsp | reg_neq]).
    (* ---- +0x1e: c.ldsp s0,16(sp) ---- *)
    assert (Hqa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hqa2) in "Hs2".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.argstr + 0x1e))
              (mword_of_int 2 : mword 6) Rs0 T1 (av - 4)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e Hs2 [-]").
    iIntros (CID16 Hk16) "Hcg Hpc Hs2".
    iEval (rewrite Hqa2) in "Hs2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    change (<[Regidx Rs0 := regval_into_reg s00]> T1) with T2.
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.argstr + 0x1e) : mword 64) 2
                    = mword_of_int (KernelSyms.argstr + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T2 upd_ne; [exact HT1sp | reg_neq]).
    (* ---- +0x20: c.ldsp s1,8(sp) ---- *)
    assert (Hqa3 : add_vec (T2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hqa3) in "Hs3".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.argstr + 0x20))
              (mword_of_int 1 : mword 6) Rs1 T2 (av - 4)%nat s10 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20 Hs3 [-]").
    iIntros (CID17 Hk17) "Hcg Hpc Hs3".
    iEval (rewrite Hqa3) in "Hs3".
    set (T3 := <[Regidx Rs1 := regval_into_reg s10]> T2).
    change (<[Regidx Rs1 := regval_into_reg s10]> T2) with T3.
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.argstr + 0x20) : mword 64) 2
                    = mword_of_int (KernelSyms.argstr + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T3 upd_ne; [exact HT2sp | reg_neq]).
    (* ---- +0x22: c.ldsp s2,0(sp) ---- *)
    assert (Hqa4 : add_vec (T3 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HT3sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hqa4) in "Hs4".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.argstr + 0x22))
              (mword_of_int 0 : mword 6) Rs2 T3 (av - 4)%nat s20 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 Hs4 [-]").
    iIntros (CID18 Hk18) "Hcg Hpc Hs4".
    iEval (rewrite Hqa4) in "Hs4".
    set (T4 := <[Regidx Rs2 := regval_into_reg s20]> T3).
    change (<[Regidx Rs2 := regval_into_reg s20]> T3) with T4.
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.argstr + 0x22) : mword 64) 2
                    = mword_of_int (KernelSyms.argstr + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T4 upd_ne; [exact HT3sp | reg_neq]).
    (* ---- +0x24: c.addi16sp sp,32 (the frame pop) ---- *)
    assert (Hwv : add_vec (T4 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
      by (rewrite HT4sp; apply stk_pop_32).
    assert (Hpop : T4 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T4 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv; exact HT4sp).
    iDestruct (stack_own_4_intro sp0 ra0 s00 s10 s20 with "Hs1 Hs2 Hs3 Hs4") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (KernelSyms.argstr + 0x24))
              (mword_of_int 2 : mword 6) T4 (av - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi24 Hframe [-]").
    iIntros (CID19 Hk19) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.argstr + 0x24) : mword 64) 2
                    = mword_of_int (KernelSyms.argstr + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    set (T5 := <[Regidx csp_rs1 := regval_into_reg (add_vec (T4 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> T4).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (T4 !!! Regidx csp_rs1)
              (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> T4) with T5.
    (* ---- +0x26: c.ret ---- *)
    assert (HT5ra : T5 !!! Regidx Rra = ra0).
    { rewrite /T5 upd_ne; [| reg_neq].
      rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf Φ (mword_of_int (KernelSyms.argstr + 0x26))
              Rra T5 av b ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi26 [-]").
    iIntros (CID20 Hk20) "Hcg Hpc".
    assert (Hretfin : ret_pc (rget T5 Rra) = ret_tgt).
    { rgne. rewrite HT5ra. reflexivity. }
    iEval (rewrite Hretfin) in "Hpc".
    (* ===================== return ===================== *)
    assert (HT5sp : T5 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /T5 upd_eq Hwv; reflexivity).
    assert (HT5s0 : T5 !!! Regidx Rs0 = m !!! Regidx Rs0).
    { rewrite /T5 upd_ne; [| reg_neq].
      rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_eq. reflexivity. }
    assert (HT5s1 : T5 !!! Regidx Rs1 = m !!! Regidx Rs1).
    { rewrite /T5 upd_ne; [| reg_neq].
      rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_eq. reflexivity. }
    assert (HT5s2 : T5 !!! Regidx Rs2 = m !!! Regidx Rs2).
    { rewrite /T5 upd_ne; [| reg_neq].
      rewrite /T4 upd_eq. reflexivity. }
    assert (HT5a0 : T5 !!! Regidx Ra0 = mr !!! Regidx Ra0).
    { rewrite /T5 upd_ne; [| reg_neq].
      rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_ne; [reflexivity | reg_neq]. }
    assert (Hthr5 : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              T5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /T5 upd_ne; [| congruence].
      rewrite /T4 upd_ne; [| congruence].
      rewrite /T3 upd_ne; [| congruence].
      rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [| congruence].
      apply Hthrr; assumption. }
    (* [Hcpu] was delivered at [CID14] by fetchstr's own [wp_next]; six more
       plain instructions have moved the hart to [CID20]. *)
    iDestruct (cpu_own_transport CID14 CID20 n eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CID20 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! T5 buf_new with "[%] Hcg Hcpu Hpc Hpriv Hbuf [%]").
    { unfold callee_saved.
      split; [exact HT5sp|].
      split; [exact HT5s0|].
      split; [exact HT5s1|].
      split; [exact HT5s2|].
      split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
      split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
      split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
      split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
      split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
      split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
      split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
      split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
      apply Hthr5; vm_compute; first [reflexivity | discriminate]. }
    rewrite HT5a0. exact Hret.
  Qed.

End ProofArgstr.

End ArgstrProof.
