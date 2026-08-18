(* ProofSysGetpid.v -- whole-function WP for sys_getpid(), the smallest
   consumer of the [struct proc] resource split (design/proc-struct.md).

     uint64 sys_getpid(void) { return myproc()->pid; }

   Ten instructions (KernelInstrs @ 0x800028f0); the frame is byte-identical
   to cpuid's (0x1141 / 0xe406 / 0xe022 / 0x0800 ... 0x60a2 / 0x6402 / 0x0141 /
   0x8082), so those eight decodes reuse KernelRvcDecode's shared templates and
   the frame-cancel lemma is cpuid's.  Only two words are fresh: the
   [jal ra,myproc] and the [c.lw a0,48(a0)].

   The interesting content is one line: the [c.lw] reads [p_pid p] out of
   [ProcInv.proc_priv], via [proc_priv_pid]'s read-only 1/4 fraction, with NO
   lock held -- while another core may be reading the very same field under
   [p->lock].  The save/restore of ra/s0 SPANS the myproc call, so the final
   [callee_saved] does not factor through the two halves and is discharged
   componentwise (the [cs_through] shape, as in ProofHoldingsleep). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
Require Import IntrDefs HartTp WpNext.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import SpecMyproc.
Require Import SpecSysGetpid.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import CodeSysGetpid.
Import Defs.
Local Open Scope Z_scope.

(* ---- the two decodes not shared with the cpuid-shaped frame ---- *)

(* +0x08  0xfdbfe0ef  jal ra,myproc
   (0x800028f8 -> 0x800018d2 is -4134; the 21-bit field is 2^21 - 4134) *)



(* sys_getpid's balanced 16-byte frame: entry [addi sp,-16] and exit
   [addi sp,+16] cancel (identical to cpuid's / mycpu's). *)
Lemma sg_frame_cancel (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = X.
Proof.
  assert (add_vec_unsigned : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
  assert (HA : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)) : mword 64)
             = 18446744073709551600) by (vm_compute; reflexivity).
  assert (HB : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)) : mword 64)
             = 16) by (vm_compute; reflexivity).
  rewrite HA HB. rewrite <- Z.add_assoc.
  replace (18446744073709551600 + 16) with (bv_modulus 64) by (vm_compute; reflexivity).
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

Module SysGetpidProof (Myproc : MYPROC) : SYSGETPID.

Section ProofSysGetpid.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.











  (* =================================================================== *)
  (*  THE CAPSTONE.                                                       *)
  (* =================================================================== *)
  Lemma wp_sys_getpid_sconf (γf : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
      (pid : mword 32) (V : pprivate) (b : bool) (lks : gset string)
    : wp_sys_getpid_sconf_body γf m av n eb p pid V b lks.
  Proof.
    cbv beta delta [wp_sys_getpid_sconf_body].
    intros pcE ret_tgt Hn Hav.
    set (imm_entry := (mword_of_int 48 : mword 6)).
    set (imm_dealloc := (mword_of_int 16 : mword 6)).
    set (nzimm_s0 := (mword_of_int 4 : mword 8)).
    set (sp0 := m !!! Regidx csp_rs1).
    set (ra0 := m !!! Regidx (mword_of_int 1 : mword 5)).
    set (s00 := m !!! Regidx (mword_of_int 8 : mword 5)).
    set (sp' := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry))).
    set (M1 := <[Regidx csp_rs1 := regval_into_reg sp']> m).
    set (M2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> M1).
    iIntros "Hcg Hcpu #Htext Hpc Hpriv Hcont".
    iPoseProof (sg_00 with "Htext") as "Hi00".
    iPoseProof (sg_02 with "Htext") as "Hi02".
    iPoseProof (sg_04 with "Htext") as "Hi04".
    iPoseProof (sg_06 with "Htext") as "Hi06".
    iPoseProof (sg_08 with "Htext") as "Hi08".
    iPoseProof (sg_0c with "Htext") as "Hi0c".
    iPoseProof (sg_0e with "Htext") as "Hi0e".
    iPoseProof (sg_10 with "Htext") as "Hi10".
    iPoseProof (sg_12 with "Htext") as "Hi12".
    iPoseProof (sg_14 with "Htext") as "Hi14".
    assert (Hcsp1 : M1 !!! Regidx csp_rs1 = sp') by (apply upd_eq).
    assert (Hpush : sp' = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold sp', pa_stk, add_vec_int, imm_entry.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* ---- +0x00: c.addi sp,-16 (frame push) ---- *)
    iApply (wp_caddi_sp_push_s_sconf pcE imm_entry m av 2 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.sys_getpid + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (vr24 vs16) "[Hbra Hbs0]".
    assert (Hpa1 : add_vec (M1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (M1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hbra".
    iEval (rewrite -Hpa2) in "Hbs0".
    (* ---- +0x02: c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_getpid + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5) M1 (av - 2)%nat vr24 b
              with "Hcg Hpc Hi02 Hbra").
    iIntros (CID2 Hs2) "Hcg Hpc Hbra".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.sys_getpid + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.sys_getpid + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- +0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_getpid + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5) M1 (av - 2)%nat vs16 b
              with "Hcg Hpc Hi04 Hbs0").
    iIntros (CID3 Hs3) "Hcg Hpc Hbs0".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.sys_getpid + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.sys_getpid + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* the two saved values, named for the epilogue's reloads.  The stores'
       own postcondition now spells the written value via [rget] (the
       leaf is generic over its source register), so the bridge from the
       raw fact goes through [rgne] even though ra/s0 are never tp. *)
    assert (Hra0v : forall (CID' : CpuId), rget (CID := CID') M1 (mword_of_int 1 : mword 5) = ra0).
    { intros CID'; rgne. unfold M1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hs00v : forall (CID' : CpuId), rget (CID := CID') M1 (mword_of_int 8 : mword 5) = s00).
    { intros CID'; rgne. unfold M1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite Hra0v) in "Hbra".
    iEval (rewrite Hs00v) in "Hbs0".
    (* ---- +0x06: c.addi4spn s0,sp,16 ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.sys_getpid + 0x06)) (Cregidx (mword_of_int 0)) nzimm_s0 (mword_of_int 8 : mword 5) M1 (av - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hs4) "Hcg Hpc".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.sys_getpid + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.sys_getpid + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> M1) with M2.
    (* ---- +0x08: jal ra,myproc ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_getpid + 0x08)) (mword_of_int 1 : mword 5) (mword_of_int 2093006 : mword 21)
              M2 (av - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (Bj := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sys_getpid + 0x08) : mword 64) 4)]> M2).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sys_getpid + 0x08) : mword 64) 4)]> M2) with Bj.
    assert (Hjmp : add_vec (mword_of_int (KernelSyms.sys_getpid + 0x08) : mword 64) (sign_extend' 64 (mword_of_int 2093006 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    assert (HBjra : Bj !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.sys_getpid + 0x08) : mword 64) 4) by (rewrite /Bj upd_eq; reflexivity).
    (* [Hcpu] rode through the four leaf steps untouched (only [Hcg]/[Hpc] are
       part of an ordinary leaf's own footprint), so it is still anchored at
       the ENTRY hart -- re-anchor it at [CID5] before crossing into myproc. *)
    iDestruct (cpu_own_transport CID CID5 n eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    (* ---- myproc(): a0 = p, callee-saved preserved ---- *)
    iApply (Myproc.wp_myproc_sconf Bj (av - 2)%nat n eb p b
              _ Hn ltac:(lia)
              with "Hcg Hcpu Htext Hpc").
    iIntros (CID6 Hs6 ms MF) "%Hms Hcg Hcpu Hpc %HcsMF".
    destruct HcsMF as [HcsMF HMFa0].
    assert (Hpc0c : ret_pc (Bj !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.sys_getpid + 0x0c))
      by (rewrite HBjra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    (* ---- +0x0c: c.lw a0,48(a0) -- THE read: myproc()->pid ---- *)
    iDestruct (proc_priv_pid with "Hpriv") as "[Hpid Hpidback]".
    assert (Haddr0c : add_vec (MF !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00")))) = p_pid p).
    { rewrite HMFa0. rewrite /p_pid.
      replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00"))) : mword 64)
        with (sign_extend' 64 (mword_of_int 48 : mword 12) : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      reflexivity. }
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.sys_getpid + 0x0c)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5)
              (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00"))) MF (av - 2)%nat pid b
              (dqm := DfracOwn (1/4))
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [Hpid]").
    { iEval (rewrite Haddr0c). iExact "Hpid". }
    iIntros (CID7 Hs7) "Hcg Hpc Hpid".
    iEval (rewrite Haddr0c) in "Hpid".
    iDestruct ("Hpidback" with "Hpid") as "Hpriv".
    set (E0c := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (sign_extend' 64 pid)]> MF).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (sign_extend' 64 pid)]> MF) with E0c.
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.sys_getpid + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.sys_getpid + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* ---- the frame is still where we left it: sp survived the call ---- *)
    assert (HE0csp : E0c !!! Regidx csp_rs1 = sp').
    { rewrite /E0c upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup HcsMF csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /Bj upd_ne; [| vm_compute; discriminate].
      rewrite /M2 upd_ne; [| vm_compute; discriminate].
      exact Hcsp1. }
    assert (Hpa1' : add_vec (E0c !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HE0csp -Hcsp1. exact Hpa1. }
    assert (Hpa2' : add_vec (E0c !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HE0csp -Hcsp1. exact Hpa2. }
    iEval (rewrite Hpa1 -Hpa1') in "Hbra".
    iEval (rewrite Hpa2 -Hpa2') in "Hbs0".
    (* ---- +0x0e: c.ldsp ra,8(sp) ---- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_getpid + 0x0e)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5) E0c (av - 2)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e Hbra").
    iIntros (CID8 Hs8) "Hcg Hpc Hbra".
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.sys_getpid + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.sys_getpid + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    set (E0e := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0]> E0c).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0]> E0c) with E0e.
    (* ---- +0x10: c.ldsp s0,0(sp) ---- *)
    assert (HE0esp : E0e !!! Regidx csp_rs1 = E0c !!! Regidx csp_rs1)
      by (rewrite /E0e upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite -HE0esp) in "Hbs0".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_getpid + 0x10)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5) E0e (av - 2)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 Hbs0").
    iIntros (CID9 Hs9) "Hcg Hpc Hbs0".
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.sys_getpid + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.sys_getpid + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    set (E10 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00]> E0e).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00]> E0e) with E10.
    (* ---- +0x12: c.addi sp,16 (frame pop) ---- *)
    assert (HE10sp : E10 !!! Regidx csp_rs1 = sp').
    { rewrite /E10 upd_ne; [| vm_compute; discriminate].
      rewrite HE0esp. exact HE0csp. }
    assert (Hwv : add_vec (E10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)) = sp0).
    { rewrite HE10sp. unfold sp', imm_dealloc, imm_entry, sp0. apply sg_frame_cancel. }
    assert (Hpop : E10 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc))) 2).
    { rewrite Hwv HE10sp. exact Hpush. }
    iEval (rewrite Hpa1') in "Hbra".
    iEval (rewrite HE0esp Hpa2') in "Hbs0".
    iDestruct (stack_own_2_intro sp0 with "Hbra Hbs0") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.sys_getpid + 0x12)) imm_dealloc E10
              (av - 2)%nat 2 b Hpop
              with "Hcg Hpc Hi12 Hframe").
    iIntros (CID10 Hs10) "Hcg Hpc".
    assert (Hnk : ((av - 2) + 2)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.sys_getpid + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.sys_getpid + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    set (E12 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> E10).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> E10) with E12.
    (* ---- +0x14: c.ret ---- *)
    assert (HE12ra : E12 !!! Regidx (mword_of_int 1 : mword 5) = ra0).
    { rewrite /E12 upd_ne; [| vm_compute; discriminate].
      rewrite /E10 upd_ne; [| vm_compute; discriminate].
      rewrite /E0e upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.sys_getpid + 0x14)) (mword_of_int 1 : mword 5) E12 av b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi14").
    iIntros (CID11 Hs11) "Hcg Hpc".
    assert (Hra_final : ret_pc (E12 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HE12ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    (* ---- the postcondition ---- *)
    (* sp and s0 were saved/restored ACROSS the myproc call, so [callee_saved
       m E12] does not factor through the two halves: each conjunct goes on
       its own.  Everything but sp/s0 rides through untouched. *)
    assert (HE12csp : E12 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /E12 upd_eq; exact Hwv).
    assert (HE12s0 : E12 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
    { rewrite /E12 upd_ne; [| vm_compute; discriminate].
      rewrite /E10 upd_eq. reflexivity. }
    assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
                     r <> csp_rs1 -> r <> mword_of_int 8 ->
                     E12 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /E12 upd_ne; [| congruence].
      rewrite /E10 upd_ne; [| congruence].
      rewrite /E0e upd_ne; [| congruence].
      rewrite /E0c upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsMF r Hr).
      rewrite /Bj upd_ne; [| congruence].
      rewrite /M2 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence]. reflexivity. }
    assert (HE12a0 : E12 !!! Regidx (mword_of_int 10 : mword 5) = sign_extend' 64 pid).
    { rewrite /E12 upd_ne; [| vm_compute; discriminate].
      rewrite /E10 upd_ne; [| vm_compute; discriminate].
      rewrite /E0e upd_ne; [| vm_compute; discriminate].
      rewrite /E0c upd_eq. reflexivity. }
    iSpecialize ("Hcont" $! CID11 with "[%]"); [wp_next_chain|].
    (* [Hcpu] has sat at [CID6] (myproc's own resumed hart) since the crossing;
       the five leaf steps since then never touched it. *)
    iDestruct (cpu_own_transport CID6 CID11 n eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply ("Hcont" $! E12 with "[%] Hcg Hcpu Hpc Hpriv").
    split; [| exact HE12a0].
    unfold callee_saved.
    split_and!.
    - exact HE12csp.
    - exact HE12s0.
    - apply Hthr; vm_compute; first [reflexivity | discriminate].
    - apply Hthr; vm_compute; first [reflexivity | discriminate].
    - apply Hthr; vm_compute; first [reflexivity | discriminate].
    - apply Hthr; vm_compute; first [reflexivity | discriminate].
    - apply Hthr; vm_compute; first [reflexivity | discriminate].
    - apply Hthr; vm_compute; first [reflexivity | discriminate].
    - apply Hthr; vm_compute; first [reflexivity | discriminate].
    - apply Hthr; vm_compute; first [reflexivity | discriminate].
    - apply Hthr; vm_compute; first [reflexivity | discriminate].
    - apply Hthr; vm_compute; first [reflexivity | discriminate].
    - apply Hthr; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofSysGetpid.

End SysGetpidProof.
