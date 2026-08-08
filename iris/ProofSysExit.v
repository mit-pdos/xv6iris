(* ProofSysExit.v -- whole-function WP for sys_exit().

   The C, the instruction map and the contract are in SpecSysExit.v.  The
   prologue and the argument fetch are ProofSysKill.v's shape byte for byte
   ([int n] is the UPPER half of frame slot 3, so [word_pointsto_split4] /
   [word_pointsto_join4] apply exactly as there) with the trapframe
   fraction BORROWED out of [proc_priv] for the argint call and put
   straight back, ProofSysWait.v's move -- because kexit, like kwait,
   wants the whole block back.

   PAST THE [jal kexit] THERE IS NOTHING TO PROVE.  kexit's own contract
   diverges (no continuation: its conclusion IS [WP Loop {{Φ}}]), so
   applying it discharges this function's goal outright.  The dead
   [li a0,0]/epilogue/ret tail gcc still emits (because it does not know
   kexit is noreturn) is never reached and is decoded by nobody's proof --
   which is also why sys_exit's own frame slots (Hb1/Hb2/Hb3lo/Hb3hi/Hb4)
   are simply framed away into kexit's call rather than rejoined: nothing
   ever reloads them. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import SmodeCore.
Require Import RiscvModelBytes InstrBytes.
Require Import StackOwn CalleeSaved.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSmodeIntr.
Require Import IntrDefs WpNext.
Require Import CpuOwn.
Require Import WpLock.
Require Import ProcGeom.
Require Import FdSlots FileInv.
Require Import ProcInv.
Require Import KallocInv.
Require Import UserPtTree.
Require Import SpecFileclose.
Require Import WpUart.
Require Import DiskPtsto.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import SpecArgint SpecKexit.
Require Import SpecSysExit.
From Kernel Require KernelInstrs KernelSyms.
Require Import CodeSysExit.
Import Defs.
Local Open Scope Z_scope.
(* a failing tactic in a WP over [proc_priv] otherwise spends tens of
   minutes FORMATTING the goal -- see claude-notes/durable-notes.md. *)
Set Printing Depth 40.

Notation SE := KernelSyms.sys_exit.

(* [addi a1,s0,-20] and [lw a0,-20(s0)]: [&n] is the UPPER half of frame
   slot 3, sys_kill's [skl_addr_pid] shape exactly (same -20 offset). *)
Lemma sex_addr_n (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 0xfec : mword 12)) = pa_add (StackOwn.pa_stk X 3) 4.
Proof.
  unfold StackOwn.pa_stk, pa_add, add_vec_int. rewrite add_vec_off2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

(* The stack budget, as a NAMED lemma with only [nat] in scope: an inline
   [ltac:(lia)] answers "Cannot find witness" under the zify hook once the
   context carries [bv_unsigned]s. *)
Lemma sex_frame (av : nat) : (K_sys_exit <= av)%nat -> (4 <= av)%nat.
Proof. unfold K_sys_exit. lia. Qed.
Lemma sex_Kai (av : nat) : (K_sys_exit <= av)%nat -> (18 <= av - 4)%nat.
Proof. unfold K_sys_exit, SpecKexit.K_kexit. lia. Qed.
Lemma sex_Kke (av : nat) : (K_sys_exit <= av)%nat -> (SpecKexit.K_kexit <= av - 4)%nat.
Proof. unfold K_sys_exit. lia. Qed.
Lemma sex_ilvl0 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma sex_arg0 : (0 < NARG)%nat.
Proof. unfold NARG. lia. Qed.

Module SysExitProof (Argint : ARGINT) (Kexit : KEXIT) : SYSEXIT.

Section ProofSysExit.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac pcstep := apply bv_eq; vm_compute; reflexivity.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).

  Lemma wp_sys_exit_sconf
      (γft γf γw : gname)
      (Φ : mval -> iProp Σ) (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64) (dqi : dfrac)
      (γkl : gname) (γka : gname * gname)
      (on : option nat) (fn : fclose_names)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool)
      (pid : mword 32) (V : pprivate) (v0 : mword 64)
    : wp_sys_exit_sconf_body γft γf γw Φ γs j γl γu γd γk pd pav pu bn γ γfs
                             cov logstart dev ip dqi γkl γka on fn
                             m av eb C b pid V v0.
  Proof.
    cbv beta delta [wp_sys_exit_sconf_body].
    intros pcE pj Hfn Hj Hgl Hv0 Hav Hgeo Heb.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext #Hdata Hpc #Hprocs #Hscheds #Hpanic Hpark
             #Hlk #Hft #Hkl Hkav #Hbio #Hlog #Hcrash #Hcert #Hdev #Hgeom
             #Hdlk Hbs Hip Hfds Hpriv".
    iPoseProof (se_00 with "Htext") as "Hi00".
    iPoseProof (se_02 with "Htext") as "Hi02".
    iPoseProof (se_04 with "Htext") as "Hi04".
    iPoseProof (se_06 with "Htext") as "Hi06".
    iPoseProof (se_08 with "Htext") as "Hi08".
    iPoseProof (se_0c with "Htext") as "Hi0c".
    iPoseProof (se_0e with "Htext") as "Hi0e".
    iPoseProof (se_12 with "Htext") as "Hi12".
    iPoseProof (se_16 with "Htext") as "Hi16".
    (* ===================== PROLOGUE (32-byte frame) ===================== *)
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    iApply (wp_caddi_sp_push_s_sconf Φ pcE (mword_of_int 32 : mword 6) m av 4 b
              (sex_frame av Hav) (stk_push_32 (m !!! Regidx csp_rs1))
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hk1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with M1.
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (SE + 0x02)) by pcstep.
    iEval (rewrite Hpp02) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /M1 upd_eq; apply stk_push_32).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (u1) "Hb1". iDestruct "S2" as (u2) "Hb2".
    iDestruct "S3" as (w3) "Hb3". iDestruct "S4" as (u4) "Hb4".
    (* the local [n] is the upper half of slot 3 *)
    iDestruct (word_pointsto_aligned_p with "Hb3") as %Hal3.
    iDestruct (word_pointsto_split4 with "Hb3") as "[Hb3lo Hb3hi]".
    (* the two save-slot addresses, as the c.sdsp displacements compute them *)
    assert (Hpa : forall u k : nat, (k + u = 4)%nat -> (u < 4)%nat ->
              add_vec (M1 !!! Regidx csp_rs1)
                (zero_extend' 64 (concat_vec (mword_of_int (Z.of_nat u) : mword 6) ('b"000")))
              = pa_stk sp0 k).
    { intros u k Hku Hu. rewrite HM1sp.
      destruct u as [|[|[|[|]]]]; try lia; destruct k as [|[|[|[|[|]]]]]; try lia;
        unfold pa_stk, add_vec_int; rewrite add_vec_off2;
        apply f_equal; apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa1 := Hpa 3%nat 1%nat ltac:(lia) ltac:(lia)).
    assert (Hpa2 := Hpa 2%nat 2%nat ltac:(lia) ltac:(lia)).
    (* +0x02 c.sdsp ra,24(sp) ; +0x04 c.sdsp s0,16(sp) *)
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (SE + 0x02)) (mword_of_int 3 : mword 6) Rra
              M1 (av - 4)%nat u1 b with "Hcg Hpc Hi02 Hb1 [-]").
    iIntros (CID2 Hk2) "Hcg Hpc Hb1".
    assert (Hpp04 : add_vec_int (mword_of_int (SE + 0x02) : mword 64) 2 = mword_of_int (SE + 0x04)) by pcstep.
    iEval (rewrite Hpp04) in "Hpc".
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (SE + 0x04)) (mword_of_int 2 : mword 6) Rs0
              M1 (av - 4)%nat u2 b with "Hcg Hpc Hi04 Hb2 [-]").
    iIntros (CID3 Hk3) "Hcg Hpc Hb2".
    assert (Hpp06 : add_vec_int (mword_of_int (SE + 0x04) : mword 64) 2 = mword_of_int (SE + 0x06)) by pcstep.
    iEval (rewrite Hpp06) in "Hpc".
    assert (HM1ra : M1 !!! Regidx Rra = m !!! Regidx Rra)
      by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HM1s0 : M1 !!! Regidx Rs0 = m !!! Regidx Rs0)
      by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rgne; rewrite Hpa1 HM1ra) in "Hb1".
    iEval (rgne; rewrite Hpa2 HM1s0) in "Hb2".
    (* +0x06 c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (SE + 0x06)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 M1 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06 [-]").
    iIntros (CID4 Hk4) "Hcg Hpc".
    set (A1 := <[Regidx Rs0 := regval_into_reg
        (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1) with A1.
    assert (Hpp08 : add_vec_int (mword_of_int (SE + 0x06) : mword 64) 2 = mword_of_int (SE + 0x08)) by pcstep.
    iEval (rewrite Hpp08) in "Hpc".
    assert (HA1s0 : A1 !!! Regidx Rs0 = sp0)
      by (rewrite /A1 upd_eq HM1sp; apply stk_fp_32).
    assert (HA1sp : A1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /A1 upd_ne; [exact HM1sp | vm_compute; discriminate]).
    (* +0x08 addi a1,s0,-20 : a1 := &n *)
    assert (Hrg08 : rget (CID := CID4) A1 Rs0 = A1 !!! Regidx Rs0) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf Φ (mword_of_int (SE + 0x08)) Ra1 Rs0 (mword_of_int 0xfec : mword 12)
              A1 (av - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08 [-]").
    iIntros (CID5 Hk5) "Hcg Hpc".
    iEval (rewrite Hrg08) in "Hcg".
    set (A2 := <[Regidx Ra1 := regval_into_reg
        (add_vec (A1 !!! Regidx Rs0) (sign_extend' 64 (mword_of_int 0xfec : mword 12)))]> A1).
    change (<[Regidx Ra1 := regval_into_reg
        (add_vec (A1 !!! Regidx Rs0) (sign_extend' 64 (mword_of_int 0xfec : mword 12)))]> A1) with A2.
    assert (Hpp0c : add_vec_int (mword_of_int (SE + 0x08) : mword 64) 4 = mword_of_int (SE + 0x0c)) by pcstep.
    iEval (rewrite Hpp0c) in "Hpc".
    assert (HA2a1 : A2 !!! Regidx Ra1 = pa_add (pa_stk sp0 3) 4)
      by (rewrite /A2 upd_eq HA1s0; apply sex_addr_n).
    (* +0x0c c.li a0,0 *)
    iApply (wp_cli_s_sconf Φ (mword_of_int (SE + 0x0c)) Ra0 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) A2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID6 Hk6) "Hcg Hpc".
    set (A3 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> A2).
    change (<[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> A2) with A3.
    assert (Hpp0e : add_vec_int (mword_of_int (SE + 0x0c) : mword 64) 2 = mword_of_int (SE + 0x0e)) by pcstep.
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e jal ra,argint *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (SE + 0x0e)) Rra (mword_of_int 2096942 : mword 21)
              A3 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID7 Hk7) "Hcg Hpc".
    set (A4 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SE + 0x0e) : mword 64) 4)]> A3).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SE + 0x0e) : mword 64) 4)]> A3) with A4.
    assert (Hjai : add_vec (mword_of_int (SE + 0x0e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096942 : mword 21)) = mword_of_int KernelSyms.argint)
      by pcstep.
    iEval (rewrite Hjai) in "Hpc".
    assert (HA4ra : A4 !!! Regidx Rra = add_vec_int (mword_of_int (SE + 0x0e) : mword 64) 4)
      by (rewrite /A4; apply upd_eq).
    assert (HA4a0 : A4 !!! Regidx Ra0 = mword_of_int (Z.of_nat 0%nat)).
    { rewrite /A4 upd_ne; [| vm_compute; discriminate]. rewrite /A3. apply upd_eq. }
    assert (HA4a1 : A4 !!! Regidx Ra1 = pa_add (pa_stk sp0 3) 4).
    { rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate]. exact HA2a1. }
    assert (HA4s0 : A4 !!! Regidx Rs0 = sp0).
    { rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate]. exact HA1s0. }
    assert (HA4sp : A4 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate]. exact HA1sp. }
    (* ===================== argint(0, &n) ===================== *)
    (* the trapframe fraction is BORROWED out of the private block: kexit
       wants the block back whole, so it goes straight back below. *)
    iDestruct (proc_priv_tf γf pj pid V with "Hpriv") as "(Htf & Hpage & Hback)".
    iEval (rewrite -HA4a1) in "Hb3hi".
    iDestruct (cpu_own_transport CID CID7 0%nat eb pj C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Argint.wp_argint_sconf Φ A4 (av - 4)%nat 0%nat eb pj C 0%nat
              (ud_tfp (pv_upt V)) (pv_tf V) v0 (word_hi w3) (DfracOwn (1/4)) b
              sex_arg0 HA4a0 Hv0 sex_ilvl0 (sex_Kai av Hav)
              with "Hcg Hcpu Htext Hdata Hpc Htf Hpage Hb3hi [-]").
    iIntros (CID8 Hk8 Mai) "%HcsAi Hcg Hcpu Hpc Htf Hpage Hb3hi".
    iEval (rewrite HA4a1) in "Hb3hi".
    iDestruct ("Hback" with "Htf Hpage") as "Hpriv".
    assert (Hpp12 : ret_pc (A4 !!! Regidx Rra) = mword_of_int (SE + 0x12))
      by (rewrite HA4ra; pcstep).
    iEval (rewrite Hpp12) in "Hpc".
    assert (HAis0 : Mai !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsAi Rs0 ltac:(vm_compute; reflexivity)); exact HA4s0).
    (* +0x12 lw a0,-20(s0) : a0 := n *)
    assert (Haddrn : add_vec (rget (CID := CID8) Mai Rs0)
                       (sign_extend' 64 (mword_of_int 0xfec : mword 12)) = pa_add (pa_stk sp0 3) 4).
    { rewrite (rget_ne (CID := CID8) Mai Rs0 ltac:(vm_compute; discriminate)) HAis0.
      apply sex_addr_n. }
    iEval (rewrite -Haddrn) in "Hb3hi".
    iApply (wp_lw_s_sconf Φ (mword_of_int (SE + 0x12)) Ra0 Rs0 (mword_of_int 0xfec : mword 12)
              Mai (av - 4)%nat (arg_int32 v0) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 Hb3hi [-]").
    iIntros (CID9 Hk9) "Hcg Hpc Hb3hi".
    set (B1 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 (arg_int32 v0))]> Mai).
    change (<[Regidx Ra0 := regval_into_reg (sign_extend' 64 (arg_int32 v0))]> Mai) with B1.
    assert (Hpp16 : add_vec_int (mword_of_int (SE + 0x12) : mword 64) 4 = mword_of_int (SE + 0x16)) by pcstep.
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 jal ra,kexit *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (SE + 0x16)) Rra (mword_of_int 2094896 : mword 21)
              B1 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi16 [-]").
    iIntros (CID10 Hk10) "Hcg Hpc".
    set (B2 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SE + 0x16) : mword 64) 4)]> B1).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SE + 0x16) : mword 64) 4)]> B1) with B2.
    assert (Hjke : add_vec (mword_of_int (SE + 0x16) : mword 64)
                     (sign_extend' 64 (mword_of_int 2094896 : mword 21)) = mword_of_int KernelSyms.kexit)
      by pcstep.
    iEval (rewrite Hjke) in "Hpc".
    (* ===================== kexit(n) -- DIVERGES ===================== *)
    (* kexit's own contract takes no continuation: applying it closes this
       function's goal outright.  Every frame slot still held (Hb1/Hb2/
       Hb3lo/Hb4) is simply framed away in [-] -- nothing ever reloads
       them, because nothing after this call is reachable. *)
    iDestruct (cpu_own_transport CID8 CID10 0%nat eb pj C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Kexit.wp_kexit_sconf γft γf γw Φ γs j γl γu γd γk pd pav pu bn γ γfs
              cov logstart dev ip dqi γkl γka on fn B2 (av - 4)%nat eb C b pid V
              Hfn Hj Hgl (sex_Kke av Hav) Hgeo Heb
              with "Hcg Hcpu Htext Hpc Hprocs Hscheds Hpanic Hpark Hlk
                    Hft Hkl Hkav Hbio Hlog Hcrash Hcert Hdev Hgeom Hdlk Hbs
                    Hip Hfds Hpriv").
  Qed.

End ProofSysExit.

End SysExitProof.
