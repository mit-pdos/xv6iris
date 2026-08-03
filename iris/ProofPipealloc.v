(* ProofPipealloc.v -- pipealloc over the SIE-agnostic sconf world.

     filealloc() x2  ->  kalloc()  ->  initlock(&pi->lock,"pipe")
       -> eight unlocked stores into the two struct files
       -> return 0
     bad: fileclose whichever files were taken; return -1

   Three things carry the proof.

   The two [struct file *] cells the caller passes are ordinary points-tos, so
   the control flow is decided by what was LAST STORED into them, not by the
   register: every [c.beqz] after a call reloads the cell.  The proof therefore
   keeps [pf0 ↦₈ x] / [pf1 ↦₈ x] as the state of the two output slots and reads
   the branch condition off that -- which is exactly why the two dead arms
   ([+0x96] and [+0xa2], "*f0 == 0 although filealloc succeeded") close: a file
   slot's address [fnode k] is never null ([fnode_nonzero]).

   The page kalloc returns is carved into [struct pipe]'s cells once, by
   [PipeInv.page_own_pipe_raw]; after the four stores and initlock, [new_pipe]
   turns them into the pipe and its two end references.

   The four exits rejoin at +0xb8, so the epilogue is factored as an
   [iAssert]ed continuation ([Hepi]) taken before the first branch -- it owns
   the four saved frame slots (ra/s0/s1/s4), the two scratch ones (s2/s3, whose
   contents differ per path), and the caller's [Hcont]; each arm hands it the
   returned value and the matching [pipealloc_post] disjunct. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RegFile.
Require Import InstrBytes.
Require Import WpAuipc.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelDataInv.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import FdSlots FileInv.
Require Import KallocInv.
Require Import PipeInv.
Require Import CodePipealloc.
Require Import WpLock.
Require Import WpSmodeIntr.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import ProcGeom CpuOwn.
Require Import SpecFilealloc SpecKalloc SpecInitlock SpecFileclose.
Require Import SpecPipealloc.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.


(* [fnode_nonzero] -- a file slot's address is never null, which is what
   kills pipealloc's two dead "*f0 == 0" arms -- is FileInv's, at the
   geometry's own altitude. *)

Module PipeallocProof (Filealloc : FILEALLOC) (Kalloc : KALLOC)
                      (Initlock : INITLOCK) (Fileclose : FILECLOSE) : PIPEALLOC.

Section ProofPipealloc.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !fileG Σ, !fdslotG Σ, !kallocG Σ, !pipeG Σ}.
  Context `{CID : CpuId}.

  Notation PA := KernelSyms.pipealloc.

  (* register indices, named once *)
  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rz  := (mword_of_int 0 : mword 5).

  Local Ltac regne :=
    first [ congruence
          | apply not_eq_sym; apply is_cs_idx_true_neq;
            [vm_compute; reflexivity | assumption]
          | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption] ].

  Lemma wp_pipealloc_sconf (Φ : mval -> iProp Σ)
      (γfl γf : gname) (γkl : gname) (γk : gname * gname) (fl : mword 64)
      (m : regfile) (v0 v1 : mword 64) (on : option nat)
      (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat) (b : bool)
    : wp_pipealloc_sconf_body Φ γfl γf γkl γk fl m v0 v1 on n eb p C K b.
  Proof.
    cbv beta delta [wp_pipealloc_sconf_body].
    intros pcE pf0 pf1 ret_tgt HK Hfl Hnoffpos.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext #Hkdata Hpc #Hftab #Hkmem Hav #Hpanic Hslota Hslotb Hc0 Hc1 Hcont".
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    (* the "pipe" string literal (4 chars + NUL), read out of the data image *)
    assert (Hpipestr : forall j bt, cstring_bytes "pipe"%string !! j = Some bt ->
                         KernelData.kernel_data !! (pipe_name_str + Z.of_nat j)%Z = Some bt).
    { intros j bt Hj.
      do 5 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string pipe_name_str "pipe"%string
                  (mword_of_int pipe_name_str) eq_refl
                  ltac:(unfold text_end, pipe_name_str; lia) Hpipestr
                  with "Hkdata") as "#Hstr".
    (* ===== PROLOGUE: 6-slot frame, ra/s0/s1/s4 saves, s0 := sp+48 ===== *)
    iPoseProof (pai_00 with "Htext") as "Hi00".
    iPoseProof (pai_02 with "Htext") as "Hi02".
    iPoseProof (pai_04 with "Htext") as "Hi04".
    iPoseProof (pai_06 with "Htext") as "Hi06".
    iPoseProof (pai_08 with "Htext") as "Hi08".
    iPoseProof (pai_0a with "Htext") as "Hi0a".
    iPoseProof (pai_0c with "Htext") as "Hi0c".
    iPoseProof (pai_0e with "Htext") as "Hi0e".
    iPoseProof (pai_10 with "Htext") as "Hi10".
    iPoseProof (pai_14 with "Htext") as "Hi14".
    iPoseProof (pai_18 with "Htext") as "Hi18".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 6).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf Φ pcE (mword_of_int 61 : mword 6) m K 6 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & _)".
    iDestruct "S1" as (u40) "Hr40". iDestruct "S2" as (u32) "Hr32".
    iDestruct "S3" as (u24) "Hr24". iDestruct "S4" as (u16) "Hr16".
    iDestruct "S5" as (u8)  "Hr8".  iDestruct "S6" as (u0)  "Hr0".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hs4pa : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                    = pa_stk sp0 4) by (rewrite -HspR1; exact Hb4).
    assert (Hs5pa : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                    = pa_stk sp0 5) by (rewrite -HspR1; exact Hb5).
    iEval (rewrite -Hb1) in "Hr40". iEval (rewrite -Hb2) in "Hr32".
    iEval (rewrite -Hb3) in "Hr24". iEval (rewrite -Hb4) in "Hr16".
    iEval (rewrite -Hb5) in "Hr8".  iEval (rewrite -Hb6) in "Hr0".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (PA + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,40(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (PA + 0x02)) (mword_of_int 5 : mword 6) Rra
              R1 (K - 6)%nat u40 b with "Hcg Hpc Hi02 Hr40 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hr40". iEval (rgne) in "Hr40".
    assert (Hpp04 : add_vec_int (mword_of_int (PA + 0x02) : mword 64) 2 = mword_of_int (PA + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,32(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (PA + 0x04)) (mword_of_int 4 : mword 6) Rs0
              R1 (K - 6)%nat u32 b with "Hcg Hpc Hi04 Hr32 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc Hr32". iEval (rgne) in "Hr32".
    assert (Hpp06 : add_vec_int (mword_of_int (PA + 0x04) : mword 64) 2 = mword_of_int (PA + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,24(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (PA + 0x06)) (mword_of_int 3 : mword 6) Rs1
              R1 (K - 6)%nat u24 b with "Hcg Hpc Hi06 Hr24 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc Hr24". iEval (rgne) in "Hr24".
    assert (Hpp08 : add_vec_int (mword_of_int (PA + 0x06) : mword 64) 2 = mword_of_int (PA + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s4,0(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (PA + 0x08)) (mword_of_int 0 : mword 6) Rs4
              R1 (K - 6)%nat u0 b with "Hcg Hpc Hi08 Hr0 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc Hr0". iEval (rgne) in "Hr0".
    assert (Hpp0a : add_vec_int (mword_of_int (PA + 0x08) : mword 64) 2 = mword_of_int (PA + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.addi4spn s0,sp,48 *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (PA + 0x0a)) (Cregidx (mword_of_int 0))
              (mword_of_int 12 : mword 8) Rs0 R1 (K - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    assert (Hpp0c : add_vec_int (mword_of_int (PA + 0x0a) : mword 64) 2 = mword_of_int (PA + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.mv s1,a0   (s1 := f0) *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (PA + 0x0c)) Rs1 Ra0
              R2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID7 Hs7) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R3 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    assert (HR3s1 : R3 !!! Regidx Rs1 = pf0).
    { rewrite /R3 upd_eq /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      apply add_vec_zero_l. }
    assert (Hpp0e : add_vec_int (mword_of_int (PA + 0x0c) : mword 64) 2 = mword_of_int (PA + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.mv s4,a1   (s4 := f1) *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (PA + 0x0e)) Rs4 Ra1
              R3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID8 Hs8) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R4 := <[Regidx Rs4 := regval_into_reg (add_vec zero_reg (R3 !!! Regidx Ra1))]> R3).
    assert (HR4s4 : R4 !!! Regidx Rs4 = pf1).
    { rewrite /R4 upd_eq /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      apply add_vec_zero_l. }
    assert (HR4s1 : R4 !!! Regidx Rs1 = pf0)
      by (rewrite /R4 upd_ne; [exact HR3s1 | vm_compute; discriminate]).
    assert (HR4a1 : R4 !!! Regidx Ra1 = pf1).
    { rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HR4a0 : R4 !!! Regidx Ra0 = pf0).
    { rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hpp10 : add_vec_int (mword_of_int (PA + 0x0e) : mword 64) 2 = mword_of_int (PA + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 sd zero,0(a1)   ( *f1 = 0) *)
    assert (HR4a1r : rget R4 Ra1 = pf1) by (rgne; exact HR4a1).
    iEval (rewrite -(addv_sext0 pf1) -HR4a1r) in "Hc1".
    iApply (wp_sd_zero_s_sconf Φ (mword_of_int (PA + 0x10)) Ra1 (mword_of_int 0 : mword 12)
              R4 (K - 6)%nat v1 b with "Hcg Hpc Hi10 Hc1 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc Hc1". iEval (rgne) in "Hc1".
    iEval (rewrite HR4a1 addv_sext0) in "Hc1".
    assert (Hpp14 : add_vec_int (mword_of_int (PA + 0x10) : mword 64) 4 = mword_of_int (PA + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 sd zero,0(a0)   ( *f0 = 0) *)
    assert (HR4a0r : rget R4 Ra0 = pf0) by (rgne; exact HR4a0).
    iEval (rewrite -(addv_sext0 pf0) -HR4a0r) in "Hc0".
    iApply (wp_sd_zero_s_sconf Φ (mword_of_int (PA + 0x14)) Ra0 (mword_of_int 0 : mword 12)
              R4 (K - 6)%nat v0 b with "Hcg Hpc Hi14 Hc0 [-]").
    iIntros (CID10 Hs10) "Hcg Hpc Hc0". iEval (rgne) in "Hc0".
    iEval (rewrite HR4a0 addv_sext0) in "Hc0".
    assert (Hpp18 : add_vec_int (mword_of_int (PA + 0x14) : mword 64) 4 = mword_of_int (PA + 0x18))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".

    (* ================================================================= *)
    (*  THE EPILOGUE, taken before the arms split (+0xb8 .. +0xc2).       *)
    (* ================================================================= *)
    iPoseProof (pai_b8 with "Htext") as "Hib8".
    iPoseProof (pai_ba with "Htext") as "Hiba".
    iPoseProof (pai_bc with "Htext") as "Hibc".
    iPoseProof (pai_be with "Htext") as "Hibe".
    iPoseProof (pai_c0 with "Htext") as "Hic0".
    iPoseProof (pai_c2 with "Htext") as "Hic2".
    set (EPI := (wp_next (CID0 := CID) b p (fun (CIDe : CpuId) =>
        ∀ (mj : regfile) (res : mword 64),
        ⌜ mj !!! Regidx csp_rs1 = spr
          /\ mj !!! Regidx Ra0 = res
          /\ (forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 ->
                mj !!! Regidx c = m !!! Regidx c) ⌝ -∗
        sie_cap_gpr mj (K - 6)%nat b p -∗
        pc_is (mword_of_int (PA + 0xb8)) -∗
        cpu_own n eb p C b -∗
        (∃ w4 w5 : mword 64, pa_stk sp0 4 ↦₈ w4 ∗ pa_stk sp0 5 ↦₈ w5) -∗
        pipealloc_post γf γk on pf0 pf1 res -∗
        WP (Loop : expr riscv_lang) {{ Φ }}))%I).
    iAssert EPI with "[Hcont Hr40 Hr32 Hr24 Hr0]" as "Hepi".
    { rewrite /EPI.
      iIntros (CIDe Hbe mj res) "(%Hjsp & %Hja0 & %Hjthr) Hcg Hpc Hcnt Hslots Hpost".
      iDestruct "Hslots" as (w4 w5) "[Hs4c Hs5c]".
      iEval (rewrite HspR1) in "Hr40". iEval (rewrite HspR1) in "Hr32".
      iEval (rewrite HspR1) in "Hr24". iEval (rewrite HspR1) in "Hr0".
      (* +0xb8 c.ldsp ra,40(sp) *)
      iApply (wp_cldsp_s_sconf Φ (mword_of_int (PA + 0xb8)) (mword_of_int 5 : mword 6) Rra
                mj (K - 6)%nat (R1 !!! Regidx Rra) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hib8 [Hr40] [-]").
      { iEval (rewrite Hjsp). iExact "Hr40". }
      iIntros (CIDf1 Hsf1) "Hcg Hpc Hr40". iEval (rewrite Hjsp) in "Hr40".
      set (P1 := <[Regidx Rra := regval_into_reg (R1 !!! Regidx Rra)]> mj).
      assert (HP1sp : P1 !!! Regidx csp_rs1 = spr)
        by (rewrite /P1 upd_ne; [exact Hjsp | vm_compute; discriminate]).
      assert (Hpbba : add_vec_int (mword_of_int (PA + 0xb8) : mword 64) 2 = mword_of_int (PA + 0xba))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpbba) in "Hpc".
      (* +0xba c.ldsp s0,32(sp) *)
      iApply (wp_cldsp_s_sconf Φ (mword_of_int (PA + 0xba)) (mword_of_int 4 : mword 6) Rs0
                P1 (K - 6)%nat (R1 !!! Regidx Rs0) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hiba [Hr32] [-]").
      { iEval (rewrite HP1sp). iExact "Hr32". }
      iIntros (CIDf2 Hsf2) "Hcg Hpc Hr32". iEval (rewrite HP1sp) in "Hr32".
      set (P2 := <[Regidx Rs0 := regval_into_reg (R1 !!! Regidx Rs0)]> P1).
      assert (HP2sp : P2 !!! Regidx csp_rs1 = spr)
        by (rewrite /P2 upd_ne; [exact HP1sp | vm_compute; discriminate]).
      assert (Hpbbc : add_vec_int (mword_of_int (PA + 0xba) : mword 64) 2 = mword_of_int (PA + 0xbc))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpbbc) in "Hpc".
      (* +0xbc c.ldsp s1,24(sp) *)
      iApply (wp_cldsp_s_sconf Φ (mword_of_int (PA + 0xbc)) (mword_of_int 3 : mword 6) Rs1
                P2 (K - 6)%nat (R1 !!! Regidx Rs1) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hibc [Hr24] [-]").
      { iEval (rewrite HP2sp). iExact "Hr24". }
      iIntros (CIDf3 Hsf3) "Hcg Hpc Hr24". iEval (rewrite HP2sp) in "Hr24".
      set (P3 := <[Regidx Rs1 := regval_into_reg (R1 !!! Regidx Rs1)]> P2).
      assert (HP3sp : P3 !!! Regidx csp_rs1 = spr)
        by (rewrite /P3 upd_ne; [exact HP2sp | vm_compute; discriminate]).
      assert (Hpbbe : add_vec_int (mword_of_int (PA + 0xbc) : mword 64) 2 = mword_of_int (PA + 0xbe))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpbbe) in "Hpc".
      (* +0xbe c.ldsp s4,0(sp) *)
      iApply (wp_cldsp_s_sconf Φ (mword_of_int (PA + 0xbe)) (mword_of_int 0 : mword 6) Rs4
                P3 (K - 6)%nat (R1 !!! Regidx Rs4) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hibe [Hr0] [-]").
      { iEval (rewrite HP3sp). iExact "Hr0". }
      iIntros (CIDf4 Hsf4) "Hcg Hpc Hr0". iEval (rewrite HP3sp) in "Hr0".
      set (P4 := <[Regidx Rs4 := regval_into_reg (R1 !!! Regidx Rs4)]> P3).
      assert (HP4sp : P4 !!! Regidx csp_rs1 = spr)
        by (rewrite /P4 upd_ne; [exact HP3sp | vm_compute; discriminate]).
      assert (Hpbc0 : add_vec_int (mword_of_int (PA + 0xbe) : mword 64) 2 = mword_of_int (PA + 0xc0))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpbc0) in "Hpc".
      (* +0xc0 c.addi16sp sp,48 -- the frame trade back *)
      set (P5 := <[Regidx csp_rs1 := regval_into_reg
                    (add_vec (P4 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> P4).
      assert (Hwv : add_vec (P4 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0).
      { rewrite HP4sp. unfold spr, sp0. apply frame_cancel_48. }
      assert (Hpop : P4 !!! Regidx csp_rs1
                     = pa_stk (add_vec (P4 !!! Regidx csp_rs1)
                                 (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
      { rewrite Hwv HP4sp. unfold spr, sp0, pa_stk, add_vec_int.
        apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      iAssert (stack_own sp0 6) with "[Hr40 Hr32 Hr24 Hs4c Hs5c Hr0]" as "Hframe6".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hr40"; [iEval (rewrite -Hb1 HspR1); iExists _; iExact "Hr40"|].
        iSplitL "Hr32"; [iEval (rewrite -Hb2 HspR1); iExists _; iExact "Hr32"|].
        iSplitL "Hr24"; [iEval (rewrite -Hb3 HspR1); iExists _; iExact "Hr24"|].
        iSplitL "Hs4c"; [iExists _; iExact "Hs4c"|].
        iSplitL "Hs5c"; [iExists _; iExact "Hs5c"|].
        iSplitL "Hr0";  [iEval (rewrite -Hb6 HspR1); iExists _; iExact "Hr0"|].
        done. }
      iEval (rewrite -Hwv) in "Hframe6".
      iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (PA + 0xc0)) (mword_of_int 3 : mword 6)
                P4 (K - 6)%nat 6 b Hpop with "Hcg Hpc Hic0 Hframe6 [-]").
      iIntros (CIDf5 Hsf5) "Hcg Hpc".
      assert (Hnk : ((K - 6) + 6)%nat = K) by lia.
      iEval (rewrite Hnk) in "Hcg".
      change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (P4 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> P4) with P5.
      assert (Hpbc2 : add_vec_int (mword_of_int (PA + 0xc0) : mword 64) 2 = mword_of_int (PA + 0xc2))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpbc2) in "Hpc".
      (* +0xc2 c.ret *)
      assert (HP5ra : P5 !!! Regidx Rra = m !!! Regidx Rra).
      { rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /P2 upd_ne; [| vm_compute; discriminate].
        rewrite /P1 upd_eq.
        rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
      assert (HP5a0 : P5 !!! Regidx Ra0 = res).
      { rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /P2 upd_ne; [| vm_compute; discriminate].
        rewrite /P1 upd_ne; [exact Hja0 | vm_compute; discriminate]. }
      iApply (wp_cret_s_sconf Φ (mword_of_int (PA + 0xc2)) Rra P5 K b
                ltac:(vm_compute; discriminate) with "Hcg Hpc Hic2 [-]").
      iIntros (CIDf6 Hsf6) "Hcg Hpc".
      iEval (rgne) in "Hpc".
      assert (Hretf : ret_pc (P5 !!! Regidx Rra) = ret_tgt) by (rewrite HP5ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      iDestruct (cpu_own_transport CIDe CIDf6 n eb p C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CIDf6 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! P5 with "Hcg Hcnt Hpc [%] [Hpost]").
      2:{ rewrite HP5a0. iExact "Hpost". }
      { assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
                  c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> c <> Rra ->
                  P5 !!! Regidx c = m !!! Regidx c).
        { intros c Hcs N2 N8 N9 N20 N1.
          rewrite /P5 upd_ne; [| regne].
          rewrite /P4 upd_ne; [| regne].
          rewrite /P3 upd_ne; [| regne].
          rewrite /P2 upd_ne; [| regne].
          rewrite /P1 upd_ne; [| regne].
          apply Hjthr; assumption. }
        unfold callee_saved.
        assert (Hc2 : P5 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1).
        { rewrite /P5 upd_eq. rewrite HP4sp. unfold regval_into_reg, spr, sp0.
          apply frame_cancel_48. }
        assert (Hc8 : P5 !!! Regidx Rs0 = m !!! Regidx Rs0).
        { rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /P2 upd_eq.
          rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
        assert (Hc9 : P5 !!! Regidx Rs1 = m !!! Regidx Rs1).
        { rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_ne; [| vm_compute; discriminate].
          rewrite /P3 upd_eq.
          rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
        assert (Hc20 : P5 !!! Regidx Rs4 = m !!! Regidx Rs4).
        { rewrite /P5 upd_ne; [| vm_compute; discriminate].
          rewrite /P4 upd_eq.
          rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
        repeat split;
          first [ exact Hc2 | exact Hc8 | exact Hc9 | exact Hc20
                | apply Hthread; vm_compute; first [reflexivity | discriminate] ]. } }

    (* ================================================================= *)
    (*  THE FAILURE TAIL.  Two entry points, because pipealloc's three     *)
    (*  bad paths join at different instructions: +0xa4 (close *f0 first)  *)
    (*  and +0xa8 (nothing to close).  Offered as a CONJUNCTION with the   *)
    (*  epilogue -- exactly one is taken, so they share the resources.     *)
    (* ================================================================= *)
    (* THE fd UNIT RIDES WITH THE CELL, exactly as [ProcInv.ofile_slot] does
       it: either *f1 is null and the unit that would have paid for its
       reference is already banked, or *f1 names a live file whose reference
       we still hold -- and the fileclose that consumes it hands the unit
       back.  Either way the tail leaves with one unit for THIS end, which is
       what lets the epilogue pay [pipealloc_post]'s two. *)
    set (PF1 := ((pf1 ↦₈ (zero_reg : mword 64) ∗ fd_slot)
                 ∨ (∃ (k1 : nat) (Cf1 : fcontent),
                      ⌜(k1 < NFILE)%nat⌝ ∗ pf1 ↦₈ fnode k1 ∗ file_ref γf k1 1 Cf1))%I).
    set (T8 := (wp_next (CID0 := CID) b p (fun (CIDt : CpuId) =>
        ∀ (Mt : regfile),
        ⌜ Mt !!! Regidx csp_rs1 = spr
          /\ Mt !!! Regidx Rs4 = pf1
          /\ (forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 ->
                Mt !!! Regidx c = m !!! Regidx c) ⌝ -∗
        sie_cap_gpr Mt (K - 6)%nat b p -∗
        pc_is (mword_of_int (PA + 0xa8)) -∗
        cpu_own n eb p C b -∗
        (∃ w4 w5 : mword 64, pa_stk sp0 4 ↦₈ w4 ∗ pa_stk sp0 5 ↦₈ w5) -∗
        (∃ w : mword 64, pf0 ↦₈ w) -∗
        (* the READ end's unit: banked by the time control reaches +0xa8,
           either because filealloc gave it straight back or because the
           fileclose at +0xa4 did *)
        fd_slot -∗
        PF1 -∗
        kalloc_avail γk on -∗
        WP (Loop : expr riscv_lang) {{ Φ }}))%I).
    set (T4C := (wp_next (CID0 := CID) b p (fun (CIDu : CpuId) =>
        ∀ (Mt : regfile) (k0 : nat) (Cf0 : fcontent),
        ⌜ Mt !!! Regidx csp_rs1 = spr
          /\ Mt !!! Regidx Rs4 = pf1
          /\ Mt !!! Regidx Ra0 = fnode k0
          /\ (forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 ->
                Mt !!! Regidx c = m !!! Regidx c) ⌝ -∗
        sie_cap_gpr Mt (K - 6)%nat b p -∗
        pc_is (mword_of_int (PA + 0xa4)) -∗
        cpu_own n eb p C b -∗
        file_ref γf k0 1 Cf0 -∗
        (∃ w4 w5 : mword 64, pa_stk sp0 4 ↦₈ w4 ∗ pa_stk sp0 5 ↦₈ w5) -∗
        (∃ w : mword 64, pf0 ↦₈ w) -∗
        PF1 -∗
        kalloc_avail γk on -∗
        WP (Loop : expr riscv_lang) {{ Φ }}))%I).
    iPoseProof (pai_a4 with "Htext") as "Hia4".
    iPoseProof (pai_a8 with "Htext") as "Hia8".
    iPoseProof (pai_ac with "Htext") as "Hiac".
    iPoseProof (pai_ae with "Htext") as "Hiae".
    iPoseProof (pai_b0 with "Htext") as "Hib0".
    iPoseProof (pai_b2 with "Htext") as "Hib2".
    iPoseProof (pai_b6 with "Htext") as "Hib6".
    iAssert (EPI ∧ T8)%I with "[Hepi]" as "HK1".
    { iSplit; [iExact "Hepi"|]. rewrite /T8.
      iIntros (CIDt Hbt Mt) "(%Htsp & %Hts4 & %Htthr) Hcg Hpc Hcnt Hslots Hcell0 Hunit0 Hcell1 Hav".
      (* the value sitting in *f1 is what the last branch tests *)
      iAssert (∃ x : mword 64, pf1 ↦₈ x ∗
                 (⌜x = (zero_reg : mword 64)⌝ ∗ fd_slot
                  ∨ ∃ (k1 : nat) (Cf1 : fcontent),
                      ⌜(k1 < NFILE)%nat /\ x = fnode k1⌝ ∗ file_ref γf k1 1 Cf1))%I
        with "[Hcell1]" as (x) "[Hcell1 Hx]".
      { rewrite /PF1. iDestruct "Hcell1" as "[[H Hu]|H]".
        - iExists (zero_reg : mword 64). iFrame "H". iLeft. by iFrame "Hu".
        - iDestruct "H" as (k1 Cf1) "(%Hk1 & Hc & Href)".
          iExists (fnode k1). iFrame "Hc". iRight. iExists k1, Cf1. iFrame "Href".
          iPureIntro. split; [exact Hk1 | reflexivity]. }
      (* +0xa8 ld a5,0(s4) *)
      assert (Ha8ad : pf1 = add_vec (Mt !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 0 : mword 12))).
      { rewrite Hts4. symmetry. apply addv_sext0. }
      assert (Ha8ad' : pf1 = add_vec (rget Mt Rs4) (sign_extend' 64 (mword_of_int 0 : mword 12)))
        by (rgne; exact Ha8ad).
      iEval (rewrite Ha8ad') in "Hcell1".
      iApply (wp_ld_s_sconf Φ (mword_of_int (PA + 0xa8)) Ra5 Rs4 (mword_of_int 0 : mword 12)
                Mt (K - 6)%nat x b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hia8 Hcell1 [-]").
      iIntros (CIDt1 Hst1) "Hcg Hpc Hcell1". iEval (rgne) in "Hcell1".
      iEval (rewrite -Ha8ad) in "Hcell1".
      set (U1 := <[Regidx Ra5 := regval_into_reg x]> Mt).
      assert (HU1a5 : U1 !!! Regidx Ra5 = x) by (rewrite /U1; apply upd_eq).
      assert (HU1sp : U1 !!! Regidx csp_rs1 = spr)
        by (rewrite /U1 upd_ne; [exact Htsp | vm_compute; discriminate]).
      assert (Hpaac : add_vec_int (mword_of_int (PA + 0xa8) : mword 64) 4 = mword_of_int (PA + 0xac))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpaac) in "Hpc".
      (* +0xac c.li a0,-1 *)
      iApply (wp_cli_s_sconf Φ (mword_of_int (PA + 0xac)) Ra0 (mword_of_int 63 : mword 6)
                (mword_of_int (-1) : mword 64) U1 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hiac [-]").
      iIntros (CIDt2 Hst2) "Hcg Hpc".
      set (U2 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> U1).
      assert (HU2a5 : U2 !!! Regidx Ra5 = x)
        by (rewrite /U2 upd_ne; [exact HU1a5 | vm_compute; discriminate]).
      assert (HU2a0 : U2 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
        by (rewrite /U2; apply upd_eq).
      assert (HU2sp : U2 !!! Regidx csp_rs1 = spr)
        by (rewrite /U2 upd_ne; [exact HU1sp | vm_compute; discriminate]).
      assert (HU2thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 ->
                U2 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N20.
        rewrite /U2 upd_ne; [| regne]. rewrite /U1 upd_ne; [| regne].
        apply Htthr; assumption. }
      assert (Hpaae : add_vec_int (mword_of_int (PA + 0xac) : mword 64) 2 = mword_of_int (PA + 0xae))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpaae) in "Hpc".
      (* +0xae c.beqz a5 *)
      iDestruct "Hx" as "[[%Hx0 Hunit1] | Hx]".
      - (* *f1 holds 0: nothing else to close, straight to the epilogue *)
        iApply (wp_cbeqz_taken_s_sconf Φ (mword_of_int (PA + 0xae)) (mword_of_int 5 : mword 8)
                  (Cregidx (mword_of_int 7)) Ra5 U2 (K - 6)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HU2a5 Hx0; apply eq_vec_true_iff; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hiae [-]").
        iApply bi.later_intro. iIntros (CIDt3 Hst3) "Hcg Hpc".
        assert (Htgt8 : add_vec (mword_of_int (PA + 0xae) : mword 64)
                          (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0"))))
                        = mword_of_int (PA + 0xb8))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt8) in "Hpc".
        iDestruct (cpu_own_transport CIDt CIDt3 n eb p C b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iSpecialize ("Hepi" $! CIDt3 with "[%]"); [wp_next_chain|].
        iApply ("Hepi" $! U2 (mword_of_int (-1) : mword 64) with "[%] Hcg Hpc Hcnt Hslots [Hav Hunit0 Hunit1 Hcell0 Hcell1]").
        { split; [exact HU2sp|]. split; [exact HU2a0 | exact HU2thr]. }
        rewrite /pipealloc_post. iLeft. iSplitR; [done|].
        iFrame "Hav Hunit0 Hunit1".
        iDestruct "Hcell0" as (w) "Hc0". iExists w, x. iFrame "Hc0 Hcell1".
      - (* *f1 holds a live file: close it too *)
        iDestruct "Hx" as (k1 Cf1) "[%Hk1x Href1]".
        destruct Hk1x as [Hk1 Hxf].
        iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (PA + 0xae)) (mword_of_int 5 : mword 8)
                  (Cregidx (mword_of_int 7)) Ra5 U2 (K - 6)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HU2a5 Hxf; apply fnode_nonzero; exact Hk1)
                  with "Hcg Hpc Hiae [-]").
        iIntros (CIDt3 Hst3) "Hcg Hpc".
        assert (Hpab0 : add_vec_int (mword_of_int (PA + 0xae) : mword 64) 2 = mword_of_int (PA + 0xb0))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpab0) in "Hpc".
        (* +0xb0 c.mv a0,a5 *)
        iApply (wp_cmv_s_sconf Φ (mword_of_int (PA + 0xb0)) Ra0 Ra5
                  U2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hib0 [-]").
        iIntros (CIDt4 Hst4) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (U3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (U2 !!! Regidx Ra5))]> U2).
        assert (HU3a0 : U3 !!! Regidx Ra0 = fnode k1).
        { rewrite /U3 upd_eq HU2a5 Hxf. apply add_vec_zero_l. }
        assert (HU3thr : forall c : mword 5, is_cs_idx c = true ->
                  c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 ->
                  U3 !!! Regidx c = m !!! Regidx c).
        { intros c Hcs N2 N8 N9 N20. rewrite /U3 upd_ne; [| regne]. apply HU2thr; assumption. }
        assert (HU3sp : U3 !!! Regidx csp_rs1 = spr)
          by (rewrite /U3 upd_ne; [exact HU2sp | vm_compute; discriminate]).
        assert (Hpab2 : add_vec_int (mword_of_int (PA + 0xb0) : mword 64) 2 = mword_of_int (PA + 0xb2))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpab2) in "Hpc".
        (* +0xb2 jal ra,fileclose *)
        iApply (wp_jal_s_sconf Φ (mword_of_int (PA + 0xb2)) Rra (mword_of_int 0x1ffc32 : mword 21)
                  U3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hib2 [-]").
        iIntros (CIDt5 Hst5) "Hcg Hpc".
        set (U4 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (PA + 0xb2) : mword 64) 4)]> U3).
        assert (Htgtfc : add_vec (mword_of_int (PA + 0xb2) : mword 64)
                           (sign_extend' 64 (mword_of_int 0x1ffc32 : mword 21))
                         = mword_of_int KernelSyms.fileclose)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgtfc) in "Hpc".
        assert (HU4a0 : U4 !!! Regidx Ra0 = fnode k1)
          by (rewrite /U4 upd_ne; [exact HU3a0 | vm_compute; discriminate]).
        assert (HU4thr : forall c : mword 5, is_cs_idx c = true ->
                  c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 ->
                  U4 !!! Regidx c = m !!! Regidx c).
        { intros c Hcs N2 N8 N9 N20. rewrite /U4 upd_ne; [| regne]. apply HU3thr; assumption. }
        assert (HU4ra : U4 !!! Regidx Rra = add_vec_int (mword_of_int (PA + 0xb2) : mword 64) 4)
          by (rewrite /U4; apply upd_eq).
        iDestruct (cpu_own_transport CIDt CIDt5 n eb p C b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iApply (Fileclose.wp_fileclose_sconf Φ γfl γf k1 1%Qp Cf1 U4 n eb p C (K - 6)%nat b
                  ltac:(unfold fileclose_stack; lia) Hnoffpos HU4a0
                  with "Hcg Hcnt Htext Hpc Hftab Hpanic Href1 [-]").
        (* fileclose hands back the unit the reference was holding: it is
           the WRITE end's, and together with [Hunit0] it pays the two
           [pipealloc_post]'s failure arm promises. *)
        iIntros (CIDt6 Hst6 mr) "Hcg Hcnt Hpc %Hfcpins Hunit1".
        assert (Hpcb6 : ret_pc (U4 !!! Regidx Rra) = mword_of_int (PA + 0xb6))
          by (rewrite HU4ra; apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpcb6) in "Hpc".
        pose proof Hfcpins as Hfcpins_cs.
        (* +0xb6 c.li a0,-1 *)
        iApply (wp_cli_s_sconf Φ (mword_of_int (PA + 0xb6)) Ra0 (mword_of_int 63 : mword 6)
                  (mword_of_int (-1) : mword 64) mr (K - 6)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hib6 [-]").
        iIntros (CIDt7 Hst7) "Hcg Hpc".
        set (U5 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> mr).
        assert (Hpab8 : add_vec_int (mword_of_int (PA + 0xb6) : mword 64) 2 = mword_of_int (PA + 0xb8))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpab8) in "Hpc".
        iDestruct (cpu_own_transport CIDt6 CIDt7 n eb p C b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iSpecialize ("Hepi" $! CIDt7 with "[%]"); [wp_next_chain|].
        iApply ("Hepi" $! U5 (mword_of_int (-1) : mword 64) with "[%] Hcg Hpc Hcnt Hslots [Hav Hunit0 Hunit1 Hcell0 Hcell1]").
        { split.
          { rewrite /U5 upd_ne; [| vm_compute; discriminate].
            rewrite (callee_saved_lookup Hfcpins_cs csp_rs1 ltac:(vm_compute; reflexivity)).
            exact HU3sp. }
          split; [rewrite /U5; apply upd_eq|].
          intros c Hcs N2 N8 N9 N20.
          rewrite /U5 upd_ne; [| regne].
          rewrite (callee_saved_lookup Hfcpins_cs c Hcs).
          apply HU4thr; assumption. }
        rewrite /pipealloc_post. iLeft. iSplitR; [done|].
        iFrame "Hav Hunit0 Hunit1".
        iDestruct "Hcell0" as (w) "Hc0". iExists w, x. iFrame "Hc0 Hcell1". }
    (* ---- the +0xa4 entry: close *f0 first, then fall into T8 ---- *)
    iAssert (EPI ∧ T8 ∧ T4C)%I with "[HK1]" as "HK".
    { iSplit; [iDestruct "HK1" as "[$ _]"|].
      iSplit; [iDestruct "HK1" as "[_ $]"|].
      iDestruct "HK1" as "[_ Ht8]". rewrite /T4C.
      iIntros (CIDu Hbu Mt k0 Cf0) "(%Htsp & %Hts4 & %Hta0 & %Htthr) Hcg Hpc Hcnt Href0 Hslots Hcell0 Hcell1 Hav".
      (* +0xa4 jal ra,fileclose *)
      iApply (wp_jal_s_sconf Φ (mword_of_int (PA + 0xa4)) Rra (mword_of_int 0x1ffc40 : mword 21)
                Mt (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hia4 [-]").
      iIntros (CIDu1 Hsu1) "Hcg Hpc".
      set (V1 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (PA + 0xa4) : mword 64) 4)]> Mt).
      assert (Htgtfc : add_vec (mword_of_int (PA + 0xa4) : mword 64)
                         (sign_extend' 64 (mword_of_int 0x1ffc40 : mword 21))
                       = mword_of_int KernelSyms.fileclose)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtfc) in "Hpc".
      assert (HV1a0 : V1 !!! Regidx Ra0 = fnode k0)
        by (rewrite /V1 upd_ne; [exact Hta0 | vm_compute; discriminate]).
      assert (HV1thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 ->
                V1 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N20. rewrite /V1 upd_ne; [| regne]. apply Htthr; assumption. }
      assert (HV1ra : V1 !!! Regidx Rra = add_vec_int (mword_of_int (PA + 0xa4) : mword 64) 4)
        by (rewrite /V1; apply upd_eq).
      iDestruct (cpu_own_transport CIDu CIDu1 n eb p C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply (Fileclose.wp_fileclose_sconf Φ γfl γf k0 1%Qp Cf0 V1 n eb p C (K - 6)%nat b
                ltac:(unfold fileclose_stack; lia) Hnoffpos HV1a0
                with "Hcg Hcnt Htext Hpc Hftab Hpanic Href0 [-]").
      (* the READ end's unit, banked for T8 *)
      iIntros (CIDu2 Hsu2 mr) "Hcg Hcnt Hpc %Hfcpins Hunit0".
      assert (Hpca8 : ret_pc (V1 !!! Regidx Rra) = mword_of_int (PA + 0xa8))
        by (rewrite HV1ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpca8) in "Hpc".
      pose proof Hfcpins as Hfcpins_cs.
      iSpecialize ("Ht8" $! CIDu2 with "[%]"); [wp_next_chain|].
      iApply ("Ht8" $! mr with "[%] Hcg Hpc Hcnt Hslots Hcell0 Hunit0 Hcell1 Hav").
      split.
      { rewrite (callee_saved_lookup Hfcpins_cs csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite /V1 upd_ne; [exact Htsp | vm_compute; discriminate]. }
      split.
      { rewrite (callee_saved_lookup Hfcpins_cs (mword_of_int 20) ltac:(vm_compute; reflexivity)).
        rewrite /V1 upd_ne; [exact Hts4 | vm_compute; discriminate]. }
      intros c Hcs N2 N8 N9 N20.
      rewrite (callee_saved_lookup Hfcpins_cs c Hcs). apply HV1thr; assumption. }

    (* ================================================================= *)
    (*  +0x18  jal ra,filealloc  -- the first file                        *)
    (* ================================================================= *)
    iPoseProof (pai_1c with "Htext") as "Hi1c".
    iPoseProof (pai_1e with "Htext") as "Hi1e".
    iPoseProof (pai_20 with "Htext") as "Hi20".
    iPoseProof (pai_24 with "Htext") as "Hi24".
    iPoseProof (pai_28 with "Htext") as "Hi28".
    iPoseProof (pai_a0 with "Htext") as "Hia0".
    iPoseProof (pai_a2 with "Htext") as "Hia2".
    iApply (wp_jal_s_sconf Φ (mword_of_int (PA + 0x18)) Rra (mword_of_int 0x1ffc28 : mword 21)
              R4 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi18 [-]").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (mA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (PA + 0x18) : mword 64) 4)]> R4).
    assert (Htgtfa : add_vec (mword_of_int (PA + 0x18) : mword 64)
                       (sign_extend' 64 (mword_of_int 0x1ffc28 : mword 21))
                     = mword_of_int KernelSyms.filealloc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtfa) in "Hpc".
    assert (HR4thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 ->
              R4 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N20.
      rewrite /R4 upd_ne; [| regne]. rewrite /R3 upd_ne; [| regne].
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (HmAthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 ->
              mA !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N20. rewrite /mA upd_ne; [| regne]. apply HR4thr; assumption. }
    assert (HmAsp : mA !!! Regidx csp_rs1 = spr).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate]. exact HspR1. }
    assert (HmAs1 : mA !!! Regidx Rs1 = pf0)
      by (rewrite /mA upd_ne; [exact HR4s1 | vm_compute; discriminate]).
    assert (HmAs4 : mA !!! Regidx Rs4 = pf1)
      by (rewrite /mA upd_ne; [exact HR4s4 | vm_compute; discriminate]).
    assert (HmAra : mA !!! Regidx Rra = add_vec_int (mword_of_int (PA + 0x18) : mword 64) 4)
      by (rewrite /mA; apply upd_eq).
    iDestruct (cpu_own_transport CID CID11 n eb p C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Filealloc.wp_filealloc_sconf Φ γfl γf mA n eb p C (K - 6)%nat b
              ltac:(lia) Hnoffpos
              with "Hcg Hcnt Htext Hpc Hftab Hpanic Hslota [-]").
    iIntros (CID12 Hs12 mB) "Hcg Hcnt Hpc %HcsB Hpost0".
    assert (Hpc1c : ret_pc (mA !!! Regidx Rra) = mword_of_int (PA + 0x1c))
      by (rewrite HmAra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    pose proof HcsB as HcsB_cs.
    assert (HmBsp : mB !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup HcsB_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HmAsp).
    assert (HmBs1 : mB !!! Regidx Rs1 = pf0)
      by (rewrite (callee_saved_lookup HcsB_cs (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HmAs1).
    assert (HmBs4 : mB !!! Regidx Rs4 = pf1)
      by (rewrite (callee_saved_lookup HcsB_cs (mword_of_int 20) ltac:(vm_compute; reflexivity)); exact HmAs4).
    assert (HmBthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 ->
              mB !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N20.
      rewrite (callee_saved_lookup HcsB_cs c Hcs). apply HmAthr; assumption. }
    (* +0x1c c.sd a0,0(s1)   ( *f0 = filealloc() ) *)
    assert (H1cad : pf0 = add_vec (mB !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite HmBs1. symmetry. apply addv_sext0. }
    assert (H1cad' : pf0 = add_vec (rget mB Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12)))
      by (rgne; exact H1cad).
    iEval (rewrite H1cad') in "Hc0".
    iApply (wp_csd_s_sconf Φ (mword_of_int (PA + 0x1c)) Ra0 Rs1 (mword_of_int 0 : mword 12)
              mB (K - 6)%nat (zero_reg : mword 64) b with "Hcg Hpc Hi1c Hc0 [-]").
    iIntros (CID13 Hs13) "Hcg Hpc Hc0". iEval (rgne) in "Hc0". iEval (rgne) in "Hc0".
    iEval (rewrite -H1cad) in "Hc0".
    assert (Hpp1e : add_vec_int (mword_of_int (PA + 0x1c) : mword 64) 2 = mword_of_int (PA + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e c.beqz a0 -- the table was full? *)
    rewrite /filealloc_post.
    iDestruct "Hpost0" as "[[%Hz0 Hslota'] | Hpost0]".
    { (* PATH A: no file at all.  Both cells hold 0; jump to +0xa8. *)
      iApply (wp_cbeqz_taken_s_sconf Φ (mword_of_int (PA + 0x1e)) (mword_of_int 69 : mword 8)
                (Cregidx (mword_of_int 2)) Ra0 mB (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Hz0; apply eq_vec_true_iff; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi1e [-]").
      iApply bi.later_intro. iIntros (CID14 Hs14) "Hcg Hpc".
      assert (HtgtA : add_vec (mword_of_int (PA + 0x1e) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 69 : mword 8) ('b"0"))))
                      = mword_of_int (PA + 0xa8))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite HtgtA) in "Hpc".
      iEval (rewrite Hb4) in "Hr16". iEval (rewrite Hb5) in "Hr8".
      iDestruct "HK" as "[_ [Ht8 _]]".
      iDestruct (cpu_own_transport CID12 CID14 n eb p C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Ht8" $! CID14 with "[%]"); [wp_next_chain|].
      iApply ("Ht8" $! mB with "[%] Hcg Hpc Hcnt [Hr16 Hr8] [Hc0] Hslota' [Hc1 Hslotb] Hav").
      { split; [exact HmBsp|]. split; [exact HmBs4 | exact HmBthr]. }
      { iExists u16, u8. iFrame "Hr16 Hr8". }
      { iExists (mB !!! Regidx Ra0). iExact "Hc0". }
      { rewrite /PF1. iLeft. iFrame "Hc1 Hslotb". } }
    iDestruct "Hpost0" as (k0 Cf0) "[%Hk0 Href0]".
    destruct Hk0 as (Hk0lt & Hk0eq & Hk0ty).
    iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (PA + 0x1e)) (mword_of_int 69 : mword 8)
              (Cregidx (mword_of_int 2)) Ra0 mB (K - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite Hk0eq; apply fnode_nonzero; exact Hk0lt)
              with "Hcg Hpc Hi1e [-]").
    iIntros (CID14 Hs14) "Hcg Hpc".
    iEval (rewrite Hk0eq) in "Hc0".
    assert (Hpp20 : add_vec_int (mword_of_int (PA + 0x1e) : mword 64) 2 = mword_of_int (PA + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* ================================================================= *)
    (*  +0x20  jal ra,filealloc  -- the second file                       *)
    (* ================================================================= *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (PA + 0x20)) Rra (mword_of_int 0x1ffc20 : mword 21)
              mB (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi20 [-]").
    iIntros (CID15 Hs15) "Hcg Hpc".
    set (mC := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (PA + 0x20) : mword 64) 4)]> mB).
    assert (Htgtfa2 : add_vec (mword_of_int (PA + 0x20) : mword 64)
                        (sign_extend' 64 (mword_of_int 0x1ffc20 : mword 21))
                      = mword_of_int KernelSyms.filealloc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtfa2) in "Hpc".
    assert (HmCthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 ->
              mC !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N20. rewrite /mC upd_ne; [| regne]. apply HmBthr; assumption. }
    assert (HmCsp : mC !!! Regidx csp_rs1 = spr)
      by (rewrite /mC upd_ne; [exact HmBsp | vm_compute; discriminate]).
    assert (HmCs1 : mC !!! Regidx Rs1 = pf0)
      by (rewrite /mC upd_ne; [exact HmBs1 | vm_compute; discriminate]).
    assert (HmCs4 : mC !!! Regidx Rs4 = pf1)
      by (rewrite /mC upd_ne; [exact HmBs4 | vm_compute; discriminate]).
    assert (HmCra : mC !!! Regidx Rra = add_vec_int (mword_of_int (PA + 0x20) : mword 64) 4)
      by (rewrite /mC; apply upd_eq).
    iDestruct (cpu_own_transport CID12 CID15 n eb p C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Filealloc.wp_filealloc_sconf Φ γfl γf mC n eb p C (K - 6)%nat b
              ltac:(lia) Hnoffpos
              with "Hcg Hcnt Htext Hpc Hftab Hpanic Hslotb [-]").
    iIntros (CID16 Hs16 mD) "Hcg Hcnt Hpc %HcsD Hpost1".
    assert (Hpc24 : ret_pc (mC !!! Regidx Rra) = mword_of_int (PA + 0x24))
      by (rewrite HmCra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    pose proof HcsD as HcsD_cs.
    assert (HmDsp : mD !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup HcsD_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HmCsp).
    assert (HmDs1 : mD !!! Regidx Rs1 = pf0)
      by (rewrite (callee_saved_lookup HcsD_cs (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HmCs1).
    assert (HmDs4 : mD !!! Regidx Rs4 = pf1)
      by (rewrite (callee_saved_lookup HcsD_cs (mword_of_int 20) ltac:(vm_compute; reflexivity)); exact HmCs4).
    assert (HmDthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 ->
              mD !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N20.
      rewrite (callee_saved_lookup HcsD_cs c Hcs). apply HmCthr; assumption. }
    (* +0x24 sd a0,0(s4)   ( *f1 = filealloc() ) *)
    assert (H24ad : pf1 = add_vec (mD !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite HmDs4. symmetry. apply addv_sext0. }
    assert (H24ad' : pf1 = add_vec (rget mD Rs4) (sign_extend' 64 (mword_of_int 0 : mword 12)))
      by (rgne; exact H24ad).
    iEval (rewrite H24ad') in "Hc1".
    iApply (wp_sd_s_sconf Φ (mword_of_int (PA + 0x24)) Ra0 Rs4 (mword_of_int 0 : mword 12)
              mD (K - 6)%nat (zero_reg : mword 64) b with "Hcg Hpc Hi24 Hc1 [-]").
    iIntros (CID17 Hs17) "Hcg Hpc Hc1". iEval (rgne) in "Hc1". iEval (rgne) in "Hc1".
    iEval (rewrite -H24ad) in "Hc1".
    assert (Hpp28 : add_vec_int (mword_of_int (PA + 0x24) : mword 64) 4 = mword_of_int (PA + 0x28))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    (* +0x28 c.beqz a0 *)
    rewrite /filealloc_post.
    iDestruct "Hpost1" as "[[%Hz1 Hslotb'] | Hpost1]".
    { (* PATH B: only the first file was taken.  Close it: jump to +0xa0. *)
      iApply (wp_cbeqz_taken_s_sconf Φ (mword_of_int (PA + 0x28)) (mword_of_int 60 : mword 8)
                (Cregidx (mword_of_int 2)) Ra0 mD (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Hz1; apply eq_vec_true_iff; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi28 [-]").
      iApply bi.later_intro. iIntros (CID18 Hs18) "Hcg Hpc".
      assert (HtgtB : add_vec (mword_of_int (PA + 0x28) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 60 : mword 8) ('b"0"))))
                      = mword_of_int (PA + 0xa0))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite HtgtB) in "Hpc".
      iEval (rewrite Hz1) in "Hc1".
      (* +0xa0 c.ld a0,0(s1) : reload *f0 *)
      assert (Ha0ad : pf0 = add_vec (mD !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))).
      { rewrite HmDs1. symmetry. apply addv_sext0. }
      assert (Ha0ad' : pf0 = add_vec (rget mD Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12)))
        by (rgne; exact Ha0ad).
      iEval (rewrite Ha0ad') in "Hc0".
      iApply (wp_cld_s_sconf Φ (mword_of_int (PA + 0xa0)) Ra0 Rs1 (mword_of_int 0 : mword 12)
                mD (K - 6)%nat (fnode k0) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hia0 Hc0 [-]").
      iIntros (CID19 Hs19) "Hcg Hpc Hc0". iEval (rgne) in "Hc0".
      iEval (rewrite -Ha0ad) in "Hc0".
      set (B1 := <[Regidx Ra0 := regval_into_reg (fnode k0)]> mD).
      assert (HB1a0 : B1 !!! Regidx Ra0 = fnode k0) by (rewrite /B1; apply upd_eq).
      assert (HB1sp : B1 !!! Regidx csp_rs1 = spr)
        by (rewrite /B1 upd_ne; [exact HmDsp | vm_compute; discriminate]).
      assert (HB1s4 : B1 !!! Regidx Rs4 = pf1)
        by (rewrite /B1 upd_ne; [exact HmDs4 | vm_compute; discriminate]).
      assert (HB1thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 ->
                B1 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N20. rewrite /B1 upd_ne; [| regne]. apply HmDthr; assumption. }
      assert (Hppa2 : add_vec_int (mword_of_int (PA + 0xa0) : mword 64) 2 = mword_of_int (PA + 0xa2))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppa2) in "Hpc".
      (* +0xa2 c.beqz a0 -- DEAD: a file slot's address is never null *)
      iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (PA + 0xa2)) (mword_of_int 17 : mword 8)
                (Cregidx (mword_of_int 2)) Ra0 B1 (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HB1a0; apply fnode_nonzero; exact Hk0lt)
                with "Hcg Hpc Hia2 [-]").
      iIntros (CID20 Hs20) "Hcg Hpc".
      assert (Hppa4 : add_vec_int (mword_of_int (PA + 0xa2) : mword 64) 2 = mword_of_int (PA + 0xa4))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppa4) in "Hpc".
      iEval (rewrite Hb4) in "Hr16". iEval (rewrite Hb5) in "Hr8".
      iDestruct "HK" as "[_ [_ Ht4]]".
      iDestruct (cpu_own_transport CID16 CID20 n eb p C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Ht4" $! CID20 with "[%]"); [wp_next_chain|].
      iApply ("Ht4" $! B1 k0 Cf0 with "[%] Hcg Hpc Hcnt Href0 [Hr16 Hr8] [Hc0] [Hc1 Hslotb'] Hav").
      { split; [exact HB1sp|]. split; [exact HB1s4|]. split; [exact HB1a0 | exact HB1thr]. }
      { iExists u16, u8. iFrame "Hr16 Hr8". }
      { iExists (fnode k0). iExact "Hc0". }
      { rewrite /PF1. iLeft. iFrame "Hc1 Hslotb'". } }
    iDestruct "Hpost1" as (k1 Cf1) "[%Hk1 Href1]".
    destruct Hk1 as (Hk1lt & Hk1eq & Hk1ty).
    iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (PA + 0x28)) (mword_of_int 60 : mword 8)
              (Cregidx (mword_of_int 2)) Ra0 mD (K - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite Hk1eq; apply fnode_nonzero; exact Hk1lt)
              with "Hcg Hpc Hi28 [-]").
    iIntros (CID18 Hs18) "Hcg Hpc".
    iEval (rewrite Hk1eq) in "Hc1".
    assert (Hpp2a : add_vec_int (mword_of_int (PA + 0x28) : mword 64) 2 = mword_of_int (PA + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".

    (* ================================================================= *)
    (*  Both files taken.  Save s2, call kalloc.                          *)
    (* ================================================================= *)
    iPoseProof (pai_2a with "Htext") as "Hi2a".
    iPoseProof (pai_2c with "Htext") as "Hi2c".
    iPoseProof (pai_30 with "Htext") as "Hi30".
    iPoseProof (pai_32 with "Htext") as "Hi32".
    iPoseProof (pai_94 with "Htext") as "Hi94".
    iPoseProof (pai_96 with "Htext") as "Hi96".
    iPoseProof (pai_98 with "Htext") as "Hi98".
    iPoseProof (pai_9a with "Htext") as "Hi9a".
    (* +0x2a c.sdsp s2,16(sp) *)
    iEval (rewrite HspR1) in "Hr16".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (PA + 0x2a)) (mword_of_int 2 : mword 6) Rs2
              mD (K - 6)%nat u16 b with "Hcg Hpc Hi2a [Hr16] [-]").
    { iEval (rewrite HmDsp). iExact "Hr16". }
    iIntros (CID19 Hs19) "Hcg Hpc Hr16". iEval (rgne) in "Hr16".
    iEval (rewrite HmDsp) in "Hr16".
    assert (Hpp2c : add_vec_int (mword_of_int (PA + 0x2a) : mword 64) 2 = mword_of_int (PA + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    (* +0x2c jal ra,kalloc *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (PA + 0x2c)) Rra (mword_of_int 0x1fc78a : mword 21)
              mD (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi2c [-]").
    iIntros (CID20 Hs20) "Hcg Hpc".
    set (mE := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (PA + 0x2c) : mword 64) 4)]> mD).
    assert (Htgtka : add_vec (mword_of_int (PA + 0x2c) : mword 64)
                       (sign_extend' 64 (mword_of_int 0x1fc78a : mword 21))
                     = mword_of_int KernelSyms.kalloc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtka) in "Hpc".
    assert (HmEthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 ->
              mE !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N20. rewrite /mE upd_ne; [| regne]. apply HmDthr; assumption. }
    assert (HmEsp : mE !!! Regidx csp_rs1 = spr)
      by (rewrite /mE upd_ne; [exact HmDsp | vm_compute; discriminate]).
    assert (HmEs1 : mE !!! Regidx Rs1 = pf0)
      by (rewrite /mE upd_ne; [exact HmDs1 | vm_compute; discriminate]).
    assert (HmEs4 : mE !!! Regidx Rs4 = pf1)
      by (rewrite /mE upd_ne; [exact HmDs4 | vm_compute; discriminate]).
    assert (HmEra : mE !!! Regidx Rra = add_vec_int (mword_of_int (PA + 0x2c) : mword 64) 4)
      by (rewrite /mE; apply upd_eq).
    iDestruct (cpu_own_transport CID16 CID20 n eb p C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Kalloc.wp_kalloc_sconf Φ γkl γk fl mE on n eb p C (K - 6)%nat b
              ltac:(lia) Hfl Hnoffpos
              with "Hcg Hcnt Htext Hpc Hkmem Hav Hpanic [-]").
    iIntros (CID21 Hs21 mF) "Hcg Hcnt Hpc %HcsF Hkp".
    assert (Hpc30 : ret_pc (mE !!! Regidx Rra) = mword_of_int (PA + 0x30))
      by (rewrite HmEra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc30) in "Hpc".
    pose proof HcsF as HcsF_cs.
    assert (HmFsp : mF !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup HcsF_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HmEsp).
    assert (HmFs1 : mF !!! Regidx Rs1 = pf0)
      by (rewrite (callee_saved_lookup HcsF_cs (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HmEs1).
    assert (HmFs4 : mF !!! Regidx Rs4 = pf1)
      by (rewrite (callee_saved_lookup HcsF_cs (mword_of_int 20) ltac:(vm_compute; reflexivity)); exact HmEs4).
    assert (HmFthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 ->
              mF !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N20.
      rewrite (callee_saved_lookup HcsF_cs c Hcs). apply HmEthr; assumption. }
    assert (HmFs2 : mF !!! Regidx Rs2 = m !!! Regidx Rs2)
      by (apply HmFthr; vm_compute; first [reflexivity | discriminate]).
    (* +0x30 c.mv s2,a0 *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (PA + 0x30)) Rs2 Ra0
              mF (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi30 [-]").
    iIntros (CID22 Hs22) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (G1 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (mF !!! Regidx Ra0))]> mF).
    assert (HG1s2 : G1 !!! Regidx Rs2 = mF !!! Regidx Ra0)
      by (rewrite /G1 upd_eq; apply add_vec_zero_l).
    assert (HG1a0 : G1 !!! Regidx Ra0 = mF !!! Regidx Ra0)
      by (rewrite /G1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HG1sp : G1 !!! Regidx csp_rs1 = spr)
      by (rewrite /G1 upd_ne; [exact HmFsp | vm_compute; discriminate]).
    assert (HG1s1 : G1 !!! Regidx Rs1 = pf0)
      by (rewrite /G1 upd_ne; [exact HmFs1 | vm_compute; discriminate]).
    assert (HG1s4 : G1 !!! Regidx Rs4 = pf1)
      by (rewrite /G1 upd_ne; [exact HmFs4 | vm_compute; discriminate]).
    assert (HG1thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> c <> Rs2 ->
              G1 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N20 N18.
      rewrite /G1 upd_ne; [| regne]. apply HmFthr; assumption. }
    assert (Hpp32 : add_vec_int (mword_of_int (PA + 0x30) : mword 64) 2 = mword_of_int (PA + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* +0x32 c.beqz a0 -- no free page? *)
    rewrite /kalloc_post.
    iDestruct "Hkp" as "[(%Hnull & _ & Hav) | (%Hpv & Hpage & Hav)]".
    { (* PATH C: no page.  Reload *f0, restore s2, and close both files. *)
      iApply (wp_cbeqz_taken_s_sconf Φ (mword_of_int (PA + 0x32)) (mword_of_int 49 : mword 8)
                (Cregidx (mword_of_int 2)) Ra0 G1 (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HG1a0 Hnull; apply eq_vec_true_iff; apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi32 [-]").
      iApply bi.later_intro. iIntros (CID23 Hs23) "Hcg Hpc".
      assert (HtgtC : add_vec (mword_of_int (PA + 0x32) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 49 : mword 8) ('b"0"))))
                      = mword_of_int (PA + 0x94))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite HtgtC) in "Hpc".
      (* +0x94 c.ld a0,0(s1) *)
      assert (H94ad : pf0 = add_vec (G1 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))).
      { rewrite HG1s1. symmetry. apply addv_sext0. }
      assert (H94ad' : pf0 = add_vec (rget G1 Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12)))
        by (rgne; exact H94ad).
      iEval (rewrite H94ad') in "Hc0".
      iApply (wp_cld_s_sconf Φ (mword_of_int (PA + 0x94)) Ra0 Rs1 (mword_of_int 0 : mword 12)
                G1 (K - 6)%nat (fnode k0) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi94 Hc0 [-]").
      iIntros (CID24 Hs24) "Hcg Hpc Hc0". iEval (rgne) in "Hc0".
      iEval (rewrite -H94ad) in "Hc0".
      set (C1 := <[Regidx Ra0 := regval_into_reg (fnode k0)]> G1).
      assert (HC1a0 : C1 !!! Regidx Ra0 = fnode k0) by (rewrite /C1; apply upd_eq).
      assert (HC1sp : C1 !!! Regidx csp_rs1 = spr)
        by (rewrite /C1 upd_ne; [exact HG1sp | vm_compute; discriminate]).
      assert (HC1s4 : C1 !!! Regidx Rs4 = pf1)
        by (rewrite /C1 upd_ne; [exact HG1s4 | vm_compute; discriminate]).
      assert (HC1thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> c <> Rs2 ->
                C1 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N20 N18. rewrite /C1 upd_ne; [| regne]. apply HG1thr; assumption. }
      assert (Hpp96 : add_vec_int (mword_of_int (PA + 0x94) : mword 64) 2 = mword_of_int (PA + 0x96))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp96) in "Hpc".
      (* +0x96 c.beqz a0 -- DEAD *)
      iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (PA + 0x96)) (mword_of_int 3 : mword 8)
                (Cregidx (mword_of_int 2)) Ra0 C1 (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HC1a0; apply fnode_nonzero; exact Hk0lt)
                with "Hcg Hpc Hi96 [-]").
      iIntros (CID25 Hs25) "Hcg Hpc".
      assert (Hpp98 : add_vec_int (mword_of_int (PA + 0x96) : mword 64) 2 = mword_of_int (PA + 0x98))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp98) in "Hpc".
      (* +0x98 c.ldsp s2,16(sp) -- restore s2 *)
      iApply (wp_cldsp_s_sconf Φ (mword_of_int (PA + 0x98)) (mword_of_int 2 : mword 6) Rs2
                C1 (K - 6)%nat (mD !!! Regidx Rs2) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi98 [Hr16] [-]").
      { iEval (rewrite HC1sp). iExact "Hr16". }
      iIntros (CID26 Hs26) "Hcg Hpc Hr16".
      iEval (rewrite HC1sp) in "Hr16".
      set (C2 := <[Regidx Rs2 := regval_into_reg (mD !!! Regidx Rs2)]> C1).
      assert (HC2s2 : C2 !!! Regidx Rs2 = m !!! Regidx Rs2).
      { rewrite /C2 upd_eq.
        apply (HmDthr Rs2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). }
      assert (HC2a0 : C2 !!! Regidx Ra0 = fnode k0)
        by (rewrite /C2 upd_ne; [exact HC1a0 | vm_compute; discriminate]).
      assert (HC2sp : C2 !!! Regidx csp_rs1 = spr)
        by (rewrite /C2 upd_ne; [exact HC1sp | vm_compute; discriminate]).
      assert (HC2s4 : C2 !!! Regidx Rs4 = pf1)
        by (rewrite /C2 upd_ne; [exact HC1s4 | vm_compute; discriminate]).
      assert (HC2thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 ->
                C2 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N20.
        destruct (decide (c = Rs2)) as [->|N18]; [exact HC2s2|].
        rewrite /C2 upd_ne; [| regne]. apply HC1thr; assumption. }
      assert (Hpp9a : add_vec_int (mword_of_int (PA + 0x98) : mword 64) 2 = mword_of_int (PA + 0x9a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp9a) in "Hpc".
      (* +0x9a c.j +0xa4 *)
      iApply (wp_cj_s_sconf Φ (mword_of_int (PA + 0x9a))
                (sign_extend' 21 (concat_vec (mword_of_int 5 : mword 11) ('b"0")))
                C2 (K - 6)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi9a [-]").
      iIntros (CID27 Hs27). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (HtgtC4 : add_vec (mword_of_int (PA + 0x9a) : mword 64)
                        (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 5 : mword 11) ('b"0"))))
                      = mword_of_int (PA + 0xa4))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite HtgtC4) in "Hpc".
      iEval (rewrite Hs4pa) in "Hr16". iEval (rewrite Hb5) in "Hr8".
      iDestruct "HK" as "[_ [_ Ht4]]".
      iDestruct (cpu_own_transport CID21 CID27 n eb p C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Ht4" $! CID27 with "[%]"); [wp_next_chain|].
      iApply ("Ht4" $! C2 k0 Cf0 with "[%] Hcg Hpc Hcnt Href0 [Hr16 Hr8] [Hc0] [Hc1 Href1] Hav").
      { split; [exact HC2sp|]. split; [exact HC2s4|]. split; [exact HC2a0 | exact HC2thr]. }
      { iExists (mD !!! Regidx Rs2), u8. iFrame "Hr16 Hr8". }
      { iExists (fnode k0). iExact "Hc0". }
      { rewrite /PF1. iRight. iExists k1, Cf1. iFrame "Hc1 Href1". iPureIntro. exact Hk1lt. } }

    (* ================================================================= *)
    (*  SUCCESS: a page.  Build the pipe, then wire the two files to it.  *)
    (* ================================================================= *)
    iPoseProof (pai_34 with "Htext") as "Hi34".
    iPoseProof (pai_36 with "Htext") as "Hi36".
    iPoseProof (pai_38 with "Htext") as "Hi38".
    iPoseProof (pai_3c with "Htext") as "Hi3c".
    iPoseProof (pai_40 with "Htext") as "Hi40".
    iPoseProof (pai_44 with "Htext") as "Hi44".
    iPoseProof (pai_48 with "Htext") as "Hi48".
    iPoseProof (pai_4c with "Htext") as "Hi4c".
    iPoseProof (pai_50 with "Htext") as "Hi50".
    iDestruct "HK" as "[Hepi _]".
    set (pi := (mF !!! Regidx Ra0 : mword 64)).
    iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (PA + 0x32)) (mword_of_int 49 : mword 8)
              (Cregidx (mword_of_int 2)) Ra0 G1 (K - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite HG1a0; apply eq_vec_false_iff; intro Hc;
                    apply (page_valid_ne_null _ Hpv); rewrite Hc;
                    apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi32 [-]").
    iIntros (CID23 Hs23) "Hcg Hpc".
    assert (Hpp34 : add_vec_int (mword_of_int (PA + 0x32) : mword 64) 2 = mword_of_int (PA + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    (* +0x34 c.sdsp s3,8(sp) *)
    iEval (rewrite HspR1) in "Hr8".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (PA + 0x34)) (mword_of_int 1 : mword 6) Rs3
              G1 (K - 6)%nat u8 b with "Hcg Hpc Hi34 [Hr8] [-]").
    { iEval (rewrite HG1sp). iExact "Hr8". }
    iIntros (CID24 Hs24) "Hcg Hpc Hr8". iEval (rgne) in "Hr8".
    iEval (rewrite HG1sp) in "Hr8".
    assert (HG1s3 : G1 !!! Regidx Rs3 = m !!! Regidx Rs3)
      by (apply HG1thr; vm_compute; first [reflexivity | discriminate]).
    iEval (rewrite HG1s3) in "Hr8".
    assert (Hpp36 : add_vec_int (mword_of_int (PA + 0x34) : mword 64) 2 = mword_of_int (PA + 0x36))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    (* +0x36 c.li s3,1 *)
    iApply (wp_cli_s_sconf Φ (mword_of_int (PA + 0x36)) Rs3 (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) G1 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi36 [-]").
    iIntros (CID25 Hs25) "Hcg Hpc".
    set (G2 := <[Regidx Rs3 := regval_into_reg (mword_of_int 1 : mword 64)]> G1).
    assert (HG2s3 : G2 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /G2; apply upd_eq).
    assert (HG2a0 : G2 !!! Regidx Ra0 = pi)
      by (rewrite /G2 upd_ne; [exact HG1a0 | vm_compute; discriminate]).
    assert (HG2s2 : G2 !!! Regidx Rs2 = pi)
      by (rewrite /G2 upd_ne; [exact HG1s2 | vm_compute; discriminate]).
    assert (HG2s1 : G2 !!! Regidx Rs1 = pf0)
      by (rewrite /G2 upd_ne; [exact HG1s1 | vm_compute; discriminate]).
    assert (HG2s4 : G2 !!! Regidx Rs4 = pf1)
      by (rewrite /G2 upd_ne; [exact HG1s4 | vm_compute; discriminate]).
    assert (HG2sp : G2 !!! Regidx csp_rs1 = spr)
      by (rewrite /G2 upd_ne; [exact HG1sp | vm_compute; discriminate]).
    assert (HG2thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> c <> Rs2 -> c <> Rs3 ->
              G2 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N20 N18 N19.
      rewrite /G2 upd_ne; [| regne]. apply HG1thr; assumption. }
    (* the page becomes a raw [struct pipe] *)
    iDestruct (page_own_pipe_raw _ Hpv with "Hpage") as "Hraw".
    rewrite /pipe_raw.
    iDestruct "Hraw" as "(Hlkw & Hlkn & Hlkc & Hdat & Hnr & Hnw & Hro & Hwo & Hslack)".
    iDestruct "Hlkw" as (vlock) "Hlkw". iDestruct "Hlkn" as (vname) "Hlkn".
    iDestruct "Hlkc" as (vcpu) "Hlkc". iDestruct "Hdat" as (bs) "[%Hbslen Hdat]".
    iDestruct "Hnr" as (vnr) "Hnr". iDestruct "Hnw" as (vnw) "Hnw".
    iDestruct "Hro" as (vro) "Hro". iDestruct "Hwo" as (vwo) "Hwo".
    assert (Hsv32 : trunc32 (G2 !!! Regidx Rs3) = (mword_of_int 1 : mword 32))
      by (rewrite HG2s3; apply bv_eq; vm_compute; reflexivity).
    assert (Hpp3c : add_vec_int (mword_of_int (PA + 0x38) : mword 64) 4 = mword_of_int (PA + 0x3c))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hpp40 : add_vec_int (mword_of_int (PA + 0x3c) : mword 64) 4 = mword_of_int (PA + 0x40))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hpp44 : add_vec_int (mword_of_int (PA + 0x40) : mword 64) 4 = mword_of_int (PA + 0x44))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hpp48 : add_vec_int (mword_of_int (PA + 0x44) : mword 64) 4 = mword_of_int (PA + 0x48))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hpp38 : add_vec_int (mword_of_int (PA + 0x36) : mword 64) 2 = mword_of_int (PA + 0x38))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp38) in "Hpc".
    (* +0x38 sw s3,544(a0)  : pi->readopen = 1 *)
    assert (Hroad : a_popen pi false
                    = add_vec (G2 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 544 : mword 12)))
      by (rewrite HG2a0; reflexivity).
    assert (Hroad' : a_popen pi false
                    = add_vec (rget G2 Ra0) (sign_extend' 64 (mword_of_int 544 : mword 12)))
      by (rgne; exact Hroad).
    iEval (rewrite Hroad') in "Hro".
    iApply (wp_sw_s_sconf Φ (mword_of_int (PA + 0x38)) Rs3 Ra0 (mword_of_int 544 : mword 12)
              G2 (K - 6)%nat vro b with "Hcg Hpc Hi38 Hro [-]").
    iIntros (CID26 Hs26) "Hcg Hpc Hro". iEval (rgne) in "Hro". iEval (rgne) in "Hro".
    iEval (rewrite -Hroad Hsv32) in "Hro".
    iEval (rewrite Hpp3c) in "Hpc".
    (* +0x3c sw s3,548(a0) : pi->writeopen = 1 *)
    assert (Hwoad : a_popen pi true
                    = add_vec (G2 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 548 : mword 12)))
      by (rewrite HG2a0; reflexivity).
    assert (Hwoad' : a_popen pi true
                    = add_vec (rget G2 Ra0) (sign_extend' 64 (mword_of_int 548 : mword 12)))
      by (rgne; exact Hwoad).
    iEval (rewrite Hwoad') in "Hwo".
    iApply (wp_sw_s_sconf Φ (mword_of_int (PA + 0x3c)) Rs3 Ra0 (mword_of_int 548 : mword 12)
              G2 (K - 6)%nat vwo b with "Hcg Hpc Hi3c Hwo [-]").
    iIntros (CID27 Hs27) "Hcg Hpc Hwo". iEval (rgne) in "Hwo". iEval (rgne) in "Hwo".
    iEval (rewrite -Hwoad Hsv32) in "Hwo".
    iEval (rewrite Hpp40) in "Hpc".
    (* +0x40 sw zero,540(a0) : pi->nwrite = 0 *)
    assert (Hnwad : a_pnwrite pi
                    = add_vec (G2 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 540 : mword 12)))
      by (rewrite HG2a0; reflexivity).
    assert (Hnwad' : a_pnwrite pi
                    = add_vec (rget G2 Ra0) (sign_extend' 64 (mword_of_int 540 : mword 12)))
      by (rgne; exact Hnwad).
    iEval (rewrite Hnwad') in "Hnw".
    iApply (wp_sw_zero_s_sconf Φ (mword_of_int (PA + 0x40)) Ra0 (mword_of_int 540 : mword 12)
              G2 (K - 6)%nat vnw b with "Hcg Hpc Hi40 Hnw [-]").
    iIntros (CID28 Hs28) "Hcg Hpc Hnw". iEval (rgne) in "Hnw".
    iEval (rewrite -Hnwad) in "Hnw".
    iEval (rewrite Hpp44) in "Hpc".
    (* +0x44 sw zero,536(a0) : pi->nread = 0 *)
    assert (Hnrad : a_pnread pi
                    = add_vec (G2 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 536 : mword 12)))
      by (rewrite HG2a0; reflexivity).
    assert (Hnrad' : a_pnread pi
                    = add_vec (rget G2 Ra0) (sign_extend' 64 (mword_of_int 536 : mword 12)))
      by (rgne; exact Hnrad).
    iEval (rewrite Hnrad') in "Hnr".
    iApply (wp_sw_zero_s_sconf Φ (mword_of_int (PA + 0x44)) Ra0 (mword_of_int 536 : mword 12)
              G2 (K - 6)%nat vnr b with "Hcg Hpc Hi44 Hnr [-]").
    iIntros (CID29 Hs29) "Hcg Hpc Hnr". iEval (rgne) in "Hnr".
    iEval (rewrite -Hnrad) in "Hnr".
    iEval (rewrite Hpp48) in "Hpc".
    (* +0x48 auipc a1,0x3 ; +0x4c addi a1,a1,472 -- a1 := "pipe" *)
    iApply (wp_auipc_s_sconf Φ (mword_of_int (PA + 0x48)) Ra1 (mword_of_int 3 : mword 20)
              G2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi48 [-]").
    iIntros (CID30 Hs30) "Hcg Hpc".
    set (G3 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (mword_of_int (PA + 0x48) : mword 64)
                     (auipc_off (mword_of_int 3 : mword 20)))]> G2).
    assert (Hpp4c : add_vec_int (mword_of_int (PA + 0x48) : mword 64) 4 = mword_of_int (PA + 0x4c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4c) in "Hpc".
    iApply (wp_addi4_s_sconf Φ (mword_of_int (PA + 0x4c)) Ra1 Ra1 (mword_of_int 0x1d8 : mword 12)
              G3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4c [-]").
    iIntros (CID31 Hs31) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (G4 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (G3 !!! Regidx Ra1) (sign_extend' 64 (mword_of_int 0x1d8 : mword 12)))]> G3).
    assert (HG4a1 : G4 !!! Regidx Ra1 = (mword_of_int pipe_name_str : mword 64)).
    { rewrite /G4 upd_eq /G3 upd_eq. unfold pipe_name_str.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HG4a0 : G4 !!! Regidx Ra0 = pi).
    { rewrite /G4 upd_ne; [| vm_compute; discriminate].
      rewrite /G3 upd_ne; [exact HG2a0 | vm_compute; discriminate]. }
    assert (HG4s1 : G4 !!! Regidx Rs1 = pf0).
    { rewrite /G4 upd_ne; [| vm_compute; discriminate].
      rewrite /G3 upd_ne; [exact HG2s1 | vm_compute; discriminate]. }
    assert (HG4s2 : G4 !!! Regidx Rs2 = pi).
    { rewrite /G4 upd_ne; [| vm_compute; discriminate].
      rewrite /G3 upd_ne; [exact HG2s2 | vm_compute; discriminate]. }
    assert (HG4s3 : G4 !!! Regidx Rs3 = (mword_of_int 1 : mword 64)).
    { rewrite /G4 upd_ne; [| vm_compute; discriminate].
      rewrite /G3 upd_ne; [exact HG2s3 | vm_compute; discriminate]. }
    assert (HG4s4 : G4 !!! Regidx Rs4 = pf1).
    { rewrite /G4 upd_ne; [| vm_compute; discriminate].
      rewrite /G3 upd_ne; [exact HG2s4 | vm_compute; discriminate]. }
    assert (HG4sp : G4 !!! Regidx csp_rs1 = spr).
    { rewrite /G4 upd_ne; [| vm_compute; discriminate].
      rewrite /G3 upd_ne; [exact HG2sp | vm_compute; discriminate]. }
    assert (HG4thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> c <> Rs2 -> c <> Rs3 ->
              G4 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N20 N18 N19.
      rewrite /G4 upd_ne; [| regne]. rewrite /G3 upd_ne; [| regne]. apply HG2thr; assumption. }
    assert (Hpp50 : add_vec_int (mword_of_int (PA + 0x4c) : mword 64) 4 = mword_of_int (PA + 0x50))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    (* +0x50 jal ra,initlock *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (PA + 0x50)) Rra (mword_of_int 0x1fc7c0 : mword 21)
              G4 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi50 [-]").
    iIntros (CID32 Hs32) "Hcg Hpc".
    set (G5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (PA + 0x50) : mword 64) 4)]> G4).
    assert (Htgtil : add_vec (mword_of_int (PA + 0x50) : mword 64)
                       (sign_extend' 64 (mword_of_int 0x1fc7c0 : mword 21))
                     = mword_of_int KernelSyms.initlock)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtil) in "Hpc".
    assert (HG5a0 : G5 !!! Regidx Ra0 = pi)
      by (rewrite /G5 upd_ne; [exact HG4a0 | vm_compute; discriminate]).
    assert (HG5a1 : G5 !!! Regidx Ra1 = (mword_of_int pipe_name_str : mword 64))
      by (rewrite /G5 upd_ne; [exact HG4a1 | vm_compute; discriminate]).
    assert (HG5ra : G5 !!! Regidx Rra = add_vec_int (mword_of_int (PA + 0x50) : mword 64) 4)
      by (rewrite /G5; apply upd_eq).
    iApply (Initlock.wp_initlock_sconf Φ G5 vlock vname vcpu "pipe"%string (K - 6)%nat b p
              ltac:(lia) with "Hcg Htext Hpc [] [Hlkw] [Hlkn] [Hlkc] [-]").
    { iEval (rewrite HG5a1). iExact "Hstr". }
    { iEval (rewrite HG5a0). iExact "Hlkw". }
    { iEval (rewrite HG5a0). iExact "Hlkn". }
    { iEval (rewrite HG5a0). iExact "Hlkc". }
    iIntros (CID33 Hs33 mH) "Hcg Hpc %HcsH Hlkw Hlkn Hlkc".
    assert (Hpc54 : ret_pc (G5 !!! Regidx Rra) = mword_of_int (PA + 0x54))
      by (rewrite HG5ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc54) in "Hpc".
    iEval (rewrite HG5a0) in "Hlkw". iEval (rewrite HG5a0) in "Hlkn".
    iEval (rewrite HG5a0) in "Hlkc".
    (* the pipe is born.  The lock's name field goes INTO the pipe rather than
       being sealed away: it is 8 bytes of the page pipeclose has to free. *)
    iApply fupd_wp.
    iMod (new_pipe ⊤ pi _ bs Hpv Hbslen
            with "Hlkn Hlkw Hlkc Hnr Hnw Hro Hwo Hdat Hslack") as (γpl γp) "(#Hpipe & Hrd & Hwr)".
    iModIntro.

    (* ---- the eight unlocked stores into the two struct files ---- *)
    iPoseProof (pai_54 with "Htext") as "Hi54". iPoseProof (pai_56 with "Htext") as "Hi56".
    iPoseProof (pai_5a with "Htext") as "Hi5a". iPoseProof (pai_5c with "Htext") as "Hi5c".
    iPoseProof (pai_60 with "Htext") as "Hi60". iPoseProof (pai_62 with "Htext") as "Hi62".
    iPoseProof (pai_66 with "Htext") as "Hi66". iPoseProof (pai_68 with "Htext") as "Hi68".
    iPoseProof (pai_6c with "Htext") as "Hi6c". iPoseProof (pai_70 with "Htext") as "Hi70".
    iPoseProof (pai_74 with "Htext") as "Hi74". iPoseProof (pai_78 with "Htext") as "Hi78".
    iPoseProof (pai_7c with "Htext") as "Hi7c". iPoseProof (pai_80 with "Htext") as "Hi80".
    iPoseProof (pai_84 with "Htext") as "Hi84". iPoseProof (pai_88 with "Htext") as "Hi88".
    iPoseProof (pai_8c with "Htext") as "Hi8c". iPoseProof (pai_8e with "Htext") as "Hi8e".
    iPoseProof (pai_90 with "Htext") as "Hi90". iPoseProof (pai_92 with "Htext") as "Hi92".
    assert (HG5sp : G5 !!! Regidx csp_rs1 = spr)
      by (rewrite /G5 upd_ne; [exact HG4sp | vm_compute; discriminate]).
    assert (HG5s1 : G5 !!! Regidx Rs1 = pf0)
      by (rewrite /G5 upd_ne; [exact HG4s1 | vm_compute; discriminate]).
    assert (HG5s2 : G5 !!! Regidx Rs2 = pi)
      by (rewrite /G5 upd_ne; [exact HG4s2 | vm_compute; discriminate]).
    assert (HG5s3 : G5 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /G5 upd_ne; [exact HG4s3 | vm_compute; discriminate]).
    assert (HG5s4 : G5 !!! Regidx Rs4 = pf1)
      by (rewrite /G5 upd_ne; [exact HG4s4 | vm_compute; discriminate]).
    assert (HG5thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> c <> Rs2 -> c <> Rs3 ->
              G5 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N20 N18 N19.
      rewrite /G5 upd_ne; [| regne]. apply HG4thr; assumption. }
    pose proof HcsH as HcsH_cs.
    assert (HHsp : mH !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup HcsH_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HG5sp).
    assert (HHs1 : mH !!! Regidx Rs1 = pf0)
      by (rewrite (callee_saved_lookup HcsH_cs (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HG5s1).
    assert (HHs2 : mH !!! Regidx Rs2 = pi)
      by (rewrite (callee_saved_lookup HcsH_cs (mword_of_int 18) ltac:(vm_compute; reflexivity)); exact HG5s2).
    assert (HHs3 : mH !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite (callee_saved_lookup HcsH_cs (mword_of_int 19) ltac:(vm_compute; reflexivity)); exact HG5s3).
    assert (HHs4 : mH !!! Regidx Rs4 = pf1)
      by (rewrite (callee_saved_lookup HcsH_cs (mword_of_int 20) ltac:(vm_compute; reflexivity)); exact HG5s4).
    assert (HHthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> c <> Rs2 -> c <> Rs3 ->
              mH !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N20 N18 N19.
      rewrite (callee_saved_lookup HcsH_cs c Hcs). apply HG5thr; assumption. }
    iDestruct (sie_cap_gpr_x0 mH (K - 6)%nat b p Rz ltac:(vm_compute; reflexivity) with "Hcg")
      as "[%HHx0 Hcg]".
    iDestruct "Href0" as "[Htok0 Hf0]".
    iDestruct "Hf0" as "(Hty0 & Hrd0 & Hwr0 & Hpp0 & Hip0 & Hoff0 & Hmaj0)".
    iDestruct "Href1" as "[Htok1 Hf1]".
    iDestruct "Hf1" as "(Hty1 & Hrd1 & Hwr1 & Hpp1 & Hip1 & Hoff1 & Hmaj1)".
    (* +0x54 load the file pointer, +0x56 store the field *)
    assert (Hld54 : pf0 = add_vec (mH !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite (_ : mH !!! Regidx Rs1 = pf0); [symmetry; apply addv_sext0 | assumption]. }
    assert (Hld54' : pf0 = add_vec (rget mH Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12)))
      by (rgne; exact Hld54).
    iEval (rewrite Hld54') in "Hc0".
    iApply (wp_cld_s_sconf Φ (mword_of_int (PA + 0x54)) Ra5 Rs1 (mword_of_int 0 : mword 12)
              mH (K - 6)%nat (fnode k0) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi54 Hc0 [-]").
    iIntros (CID34 Hs34) "Hcg Hpc Hc0". iEval (rgne) in "Hc0".
    iEval (rewrite -Hld54) in "Hc0".
    set (N1 := <[Regidx Ra5 := regval_into_reg (fnode k0)]> mH).
    assert (HN1a5 : N1 !!! Regidx Ra5 = fnode k0) by (rewrite /N1; apply upd_eq).
    assert (HN1s1 : N1 !!! Regidx Rs1 = pf0)
      by (rewrite /N1 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN1s4 : N1 !!! Regidx Rs4 = pf1)
      by (rewrite /N1 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN1s2 : N1 !!! Regidx Rs2 = pi)
      by (rewrite /N1 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN1s3 : N1 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /N1 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN1x0 : N1 !!! Regidx Rz = (zero_reg : mword 64))
      by (rewrite /N1 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN1sp : N1 !!! Regidx csp_rs1 = spr)
      by (rewrite /N1 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN1thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> c <> Rs2 -> c <> Rs3 ->
              N1 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs A2 A8 A9 A20 A18 A19. rewrite /N1 upd_ne; [| regne]. auto. }
    assert (Hst56 : add_vec_int (mword_of_int (PA + 0x54) : mword 64) 2 = mword_of_int (PA + 0x56))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hst56) in "Hpc".
    assert (Had56 : a_ftype k0 = add_vec (N1 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite HN1a5. unfold a_ftype. symmetry. apply addv_sext0. }
    assert (Had56' : a_ftype k0 = add_vec (rget N1 Ra5) (sign_extend' 64 (mword_of_int 0 : mword 12)))
      by (rgne; exact Had56).
    iEval (rewrite Had56') in "Hty0".
    assert (Hvv56 : trunc32 (N1 !!! Regidx Rs3) = FD_PIPE)
      by (rewrite HN1s3; unfold FD_PIPE; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_sw_s_sconf Φ (mword_of_int (PA + 0x56)) Rs3 Ra5 (mword_of_int 0 : mword 12)
              N1 (K - 6)%nat (fc_type Cf0) b with "Hcg Hpc Hi56 Hty0 [-]").
    iIntros (CID35 Hs35) "Hcg Hpc Hty0". iEval (rgne) in "Hty0". iEval (rgne) in "Hty0".
    iEval (rewrite -Had56 Hvv56) in "Hty0".
    assert (Hnx5a : add_vec_int (mword_of_int (PA + 0x56) : mword 64) 4 = mword_of_int (PA + 0x5a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hnx5a) in "Hpc".
    (* +0x5a load the file pointer, +0x5c store the field *)
    assert (Hld5a : pf0 = add_vec (N1 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite (_ : N1 !!! Regidx Rs1 = pf0); [symmetry; apply addv_sext0 | assumption]. }
    assert (Hld5a' : pf0 = add_vec (rget N1 Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12)))
      by (rgne; exact Hld5a).
    iEval (rewrite Hld5a') in "Hc0".
    iApply (wp_cld_s_sconf Φ (mword_of_int (PA + 0x5a)) Ra5 Rs1 (mword_of_int 0 : mword 12)
              N1 (K - 6)%nat (fnode k0) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5a Hc0 [-]").
    iIntros (CID36 Hs36) "Hcg Hpc Hc0". iEval (rgne) in "Hc0".
    iEval (rewrite -Hld5a) in "Hc0".
    set (N2 := <[Regidx Ra5 := regval_into_reg (fnode k0)]> N1).
    assert (HN2a5 : N2 !!! Regidx Ra5 = fnode k0) by (rewrite /N2; apply upd_eq).
    assert (HN2s1 : N2 !!! Regidx Rs1 = pf0)
      by (rewrite /N2 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN2s4 : N2 !!! Regidx Rs4 = pf1)
      by (rewrite /N2 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN2s2 : N2 !!! Regidx Rs2 = pi)
      by (rewrite /N2 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN2s3 : N2 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /N2 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN2x0 : N2 !!! Regidx Rz = (zero_reg : mword 64))
      by (rewrite /N2 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN2sp : N2 !!! Regidx csp_rs1 = spr)
      by (rewrite /N2 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN2thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> c <> Rs2 -> c <> Rs3 ->
              N2 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs A2 A8 A9 A20 A18 A19. rewrite /N2 upd_ne; [| regne]. auto. }
    assert (Hst5c : add_vec_int (mword_of_int (PA + 0x5a) : mword 64) 2 = mword_of_int (PA + 0x5c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hst5c) in "Hpc".
    assert (Had5c : a_freadable k0 = add_vec (N2 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 8 : mword 12))).
    { rewrite HN2a5. reflexivity. }
    assert (Had5c' : a_freadable k0 = add_vec (rget N2 Ra5) (sign_extend' 64 (mword_of_int 8 : mword 12)))
      by (rgne; exact Had5c).
    iEval (rewrite Had5c') in "Hrd0".
    assert (Hvv5c : trunc8 (N2 !!! Regidx Rs3) = (mword_of_int 1 : mword 8))
      by (rewrite HN2s3; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_sb_s_sconf Φ (mword_of_int (PA + 0x5c)) Rs3 Ra5 (mword_of_int 8 : mword 12)
              N2 (K - 6)%nat _ b with "Hcg Hpc Hi5c Hrd0 [-]").
    iIntros (CID37 Hs37) "Hcg Hpc Hrd0". iEval (rgne) in "Hrd0". iEval (rgne) in "Hrd0".
    iEval (rewrite -Had5c Hvv5c) in "Hrd0".
    assert (Hnx60 : add_vec_int (mword_of_int (PA + 0x5c) : mword 64) 4 = mword_of_int (PA + 0x60))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hnx60) in "Hpc".
    (* +0x60 load the file pointer, +0x62 store the field *)
    assert (Hld60 : pf0 = add_vec (N2 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite (_ : N2 !!! Regidx Rs1 = pf0); [symmetry; apply addv_sext0 | assumption]. }
    assert (Hld60' : pf0 = add_vec (rget N2 Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12)))
      by (rgne; exact Hld60).
    iEval (rewrite Hld60') in "Hc0".
    iApply (wp_cld_s_sconf Φ (mword_of_int (PA + 0x60)) Ra5 Rs1 (mword_of_int 0 : mword 12)
              N2 (K - 6)%nat (fnode k0) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi60 Hc0 [-]").
    iIntros (CID38 Hs38) "Hcg Hpc Hc0". iEval (rgne) in "Hc0".
    iEval (rewrite -Hld60) in "Hc0".
    set (N3 := <[Regidx Ra5 := regval_into_reg (fnode k0)]> N2).
    assert (HN3a5 : N3 !!! Regidx Ra5 = fnode k0) by (rewrite /N3; apply upd_eq).
    assert (HN3s1 : N3 !!! Regidx Rs1 = pf0)
      by (rewrite /N3 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN3s4 : N3 !!! Regidx Rs4 = pf1)
      by (rewrite /N3 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN3s2 : N3 !!! Regidx Rs2 = pi)
      by (rewrite /N3 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN3s3 : N3 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /N3 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN3x0 : N3 !!! Regidx Rz = (zero_reg : mword 64))
      by (rewrite /N3 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN3sp : N3 !!! Regidx csp_rs1 = spr)
      by (rewrite /N3 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN3thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> c <> Rs2 -> c <> Rs3 ->
              N3 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs A2 A8 A9 A20 A18 A19. rewrite /N3 upd_ne; [| regne]. auto. }
    assert (Hst62 : add_vec_int (mword_of_int (PA + 0x60) : mword 64) 2 = mword_of_int (PA + 0x62))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hst62) in "Hpc".
    assert (Had62 : a_fwritable k0 = add_vec (N3 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 9 : mword 12))).
    { rewrite HN3a5. reflexivity. }
    assert (Had62' : a_fwritable k0 = add_vec (rget N3 Ra5) (sign_extend' 64 (mword_of_int 9 : mword 12)))
      by (rgne; exact Had62).
    iEval (rewrite Had62') in "Hwr0".
    assert (Hvv62 : trunc8 (N3 !!! Regidx Rz) = (mword_of_int 0 : mword 8))
      by (rewrite HN3x0; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_sb_s_sconf Φ (mword_of_int (PA + 0x62)) Rz Ra5 (mword_of_int 9 : mword 12)
              N3 (K - 6)%nat _ b with "Hcg Hpc Hi62 Hwr0 [-]").
    iIntros (CID39 Hs39) "Hcg Hpc Hwr0". iEval (rgne) in "Hwr0". iEval (rgne) in "Hwr0".
    iEval (rewrite -Had62 Hvv62) in "Hwr0".
    assert (Hnx66 : add_vec_int (mword_of_int (PA + 0x62) : mword 64) 4 = mword_of_int (PA + 0x66))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hnx66) in "Hpc".
    (* +0x66 load the file pointer, +0x68 store the field *)
    assert (Hld66 : pf0 = add_vec (N3 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite (_ : N3 !!! Regidx Rs1 = pf0); [symmetry; apply addv_sext0 | assumption]. }
    assert (Hld66' : pf0 = add_vec (rget N3 Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12)))
      by (rgne; exact Hld66).
    iEval (rewrite Hld66') in "Hc0".
    iApply (wp_cld_s_sconf Φ (mword_of_int (PA + 0x66)) Ra5 Rs1 (mword_of_int 0 : mword 12)
              N3 (K - 6)%nat (fnode k0) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi66 Hc0 [-]").
    iIntros (CID40 Hs40) "Hcg Hpc Hc0". iEval (rgne) in "Hc0".
    iEval (rewrite -Hld66) in "Hc0".
    set (N4 := <[Regidx Ra5 := regval_into_reg (fnode k0)]> N3).
    assert (HN4a5 : N4 !!! Regidx Ra5 = fnode k0) by (rewrite /N4; apply upd_eq).
    assert (HN4s1 : N4 !!! Regidx Rs1 = pf0)
      by (rewrite /N4 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN4s4 : N4 !!! Regidx Rs4 = pf1)
      by (rewrite /N4 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN4s2 : N4 !!! Regidx Rs2 = pi)
      by (rewrite /N4 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN4s3 : N4 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /N4 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN4x0 : N4 !!! Regidx Rz = (zero_reg : mword 64))
      by (rewrite /N4 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN4sp : N4 !!! Regidx csp_rs1 = spr)
      by (rewrite /N4 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN4thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> c <> Rs2 -> c <> Rs3 ->
              N4 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs A2 A8 A9 A20 A18 A19. rewrite /N4 upd_ne; [| regne]. auto. }
    assert (Hst68 : add_vec_int (mword_of_int (PA + 0x66) : mword 64) 2 = mword_of_int (PA + 0x68))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hst68) in "Hpc".
    assert (Had68 : a_fpipe k0 = add_vec (N4 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 16 : mword 12))).
    { rewrite HN4a5. reflexivity. }
    assert (Had68' : a_fpipe k0 = add_vec (rget N4 Ra5) (sign_extend' 64 (mword_of_int 16 : mword 12)))
      by (rgne; exact Had68).
    iEval (rewrite Had68') in "Hpp0".
    iApply (wp_sd_s_sconf Φ (mword_of_int (PA + 0x68)) Rs2 Ra5 (mword_of_int 16 : mword 12)
              N4 (K - 6)%nat (fc_pipe Cf0) b with "Hcg Hpc Hi68 Hpp0 [-]").
    iIntros (CID41 Hs41) "Hcg Hpc Hpp0". iEval (rgne) in "Hpp0". iEval (rgne) in "Hpp0".
    iEval (rewrite -Had68 HN4s2) in "Hpp0".
    assert (Hnx6c : add_vec_int (mword_of_int (PA + 0x68) : mword 64) 4 = mword_of_int (PA + 0x6c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hnx6c) in "Hpc".
    (* +0x6c load the file pointer, +0x70 store the field *)
    assert (Hld6c : pf1 = add_vec (N4 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite (_ : N4 !!! Regidx Rs4 = pf1); [symmetry; apply addv_sext0 | assumption]. }
    assert (Hld6c' : pf1 = add_vec (rget N4 Rs4) (sign_extend' 64 (mword_of_int 0 : mword 12)))
      by (rgne; exact Hld6c).
    iEval (rewrite Hld6c') in "Hc1".
    iApply (wp_ld_s_sconf Φ (mword_of_int (PA + 0x6c)) Ra5 Rs4 (mword_of_int 0 : mword 12)
              N4 (K - 6)%nat (fnode k1) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6c Hc1 [-]").
    iIntros (CID42 Hs42) "Hcg Hpc Hc1". iEval (rgne) in "Hc1".
    iEval (rewrite -Hld6c) in "Hc1".
    set (N5 := <[Regidx Ra5 := regval_into_reg (fnode k1)]> N4).
    assert (HN5a5 : N5 !!! Regidx Ra5 = fnode k1) by (rewrite /N5; apply upd_eq).
    assert (HN5s1 : N5 !!! Regidx Rs1 = pf0)
      by (rewrite /N5 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN5s4 : N5 !!! Regidx Rs4 = pf1)
      by (rewrite /N5 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN5s2 : N5 !!! Regidx Rs2 = pi)
      by (rewrite /N5 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN5s3 : N5 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /N5 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN5x0 : N5 !!! Regidx Rz = (zero_reg : mword 64))
      by (rewrite /N5 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN5sp : N5 !!! Regidx csp_rs1 = spr)
      by (rewrite /N5 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN5thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> c <> Rs2 -> c <> Rs3 ->
              N5 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs A2 A8 A9 A20 A18 A19. rewrite /N5 upd_ne; [| regne]. auto. }
    assert (Hst70 : add_vec_int (mword_of_int (PA + 0x6c) : mword 64) 4 = mword_of_int (PA + 0x70))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hst70) in "Hpc".
    assert (Had70 : a_ftype k1 = add_vec (N5 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite HN5a5. unfold a_ftype. symmetry. apply addv_sext0. }
    assert (Had70' : a_ftype k1 = add_vec (rget N5 Ra5) (sign_extend' 64 (mword_of_int 0 : mword 12)))
      by (rgne; exact Had70).
    iEval (rewrite Had70') in "Hty1".
    assert (Hvv70 : trunc32 (N5 !!! Regidx Rs3) = FD_PIPE)
      by (rewrite HN5s3; unfold FD_PIPE; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_sw_s_sconf Φ (mword_of_int (PA + 0x70)) Rs3 Ra5 (mword_of_int 0 : mword 12)
              N5 (K - 6)%nat (fc_type Cf1) b with "Hcg Hpc Hi70 Hty1 [-]").
    iIntros (CID43 Hs43) "Hcg Hpc Hty1". iEval (rgne) in "Hty1". iEval (rgne) in "Hty1".
    iEval (rewrite -Had70 Hvv70) in "Hty1".
    assert (Hnx74 : add_vec_int (mword_of_int (PA + 0x70) : mword 64) 4 = mword_of_int (PA + 0x74))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hnx74) in "Hpc".
    (* +0x74 load the file pointer, +0x78 store the field *)
    assert (Hld74 : pf1 = add_vec (N5 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite (_ : N5 !!! Regidx Rs4 = pf1); [symmetry; apply addv_sext0 | assumption]. }
    assert (Hld74' : pf1 = add_vec (rget N5 Rs4) (sign_extend' 64 (mword_of_int 0 : mword 12)))
      by (rgne; exact Hld74).
    iEval (rewrite Hld74') in "Hc1".
    iApply (wp_ld_s_sconf Φ (mword_of_int (PA + 0x74)) Ra5 Rs4 (mword_of_int 0 : mword 12)
              N5 (K - 6)%nat (fnode k1) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi74 Hc1 [-]").
    iIntros (CID44 Hs44) "Hcg Hpc Hc1". iEval (rgne) in "Hc1".
    iEval (rewrite -Hld74) in "Hc1".
    set (N6 := <[Regidx Ra5 := regval_into_reg (fnode k1)]> N5).
    assert (HN6a5 : N6 !!! Regidx Ra5 = fnode k1) by (rewrite /N6; apply upd_eq).
    assert (HN6s1 : N6 !!! Regidx Rs1 = pf0)
      by (rewrite /N6 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN6s4 : N6 !!! Regidx Rs4 = pf1)
      by (rewrite /N6 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN6s2 : N6 !!! Regidx Rs2 = pi)
      by (rewrite /N6 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN6s3 : N6 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /N6 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN6x0 : N6 !!! Regidx Rz = (zero_reg : mword 64))
      by (rewrite /N6 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN6sp : N6 !!! Regidx csp_rs1 = spr)
      by (rewrite /N6 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN6thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> c <> Rs2 -> c <> Rs3 ->
              N6 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs A2 A8 A9 A20 A18 A19. rewrite /N6 upd_ne; [| regne]. auto. }
    assert (Hst78 : add_vec_int (mword_of_int (PA + 0x74) : mword 64) 4 = mword_of_int (PA + 0x78))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hst78) in "Hpc".
    assert (Had78 : a_freadable k1 = add_vec (N6 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 8 : mword 12))).
    { rewrite HN6a5. reflexivity. }
    assert (Had78' : a_freadable k1 = add_vec (rget N6 Ra5) (sign_extend' 64 (mword_of_int 8 : mword 12)))
      by (rgne; exact Had78).
    iEval (rewrite Had78') in "Hrd1".
    assert (Hvv78 : trunc8 (N6 !!! Regidx Rz) = (mword_of_int 0 : mword 8))
      by (rewrite HN6x0; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_sb_s_sconf Φ (mword_of_int (PA + 0x78)) Rz Ra5 (mword_of_int 8 : mword 12)
              N6 (K - 6)%nat _ b with "Hcg Hpc Hi78 Hrd1 [-]").
    iIntros (CID45 Hs45) "Hcg Hpc Hrd1". iEval (rgne) in "Hrd1". iEval (rgne) in "Hrd1".
    iEval (rewrite -Had78 Hvv78) in "Hrd1".
    assert (Hnx7c : add_vec_int (mword_of_int (PA + 0x78) : mword 64) 4 = mword_of_int (PA + 0x7c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hnx7c) in "Hpc".
    (* +0x7c load the file pointer, +0x80 store the field *)
    assert (Hld7c : pf1 = add_vec (N6 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite (_ : N6 !!! Regidx Rs4 = pf1); [symmetry; apply addv_sext0 | assumption]. }
    assert (Hld7c' : pf1 = add_vec (rget N6 Rs4) (sign_extend' 64 (mword_of_int 0 : mword 12)))
      by (rgne; exact Hld7c).
    iEval (rewrite Hld7c') in "Hc1".
    iApply (wp_ld_s_sconf Φ (mword_of_int (PA + 0x7c)) Ra5 Rs4 (mword_of_int 0 : mword 12)
              N6 (K - 6)%nat (fnode k1) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7c Hc1 [-]").
    iIntros (CID46 Hs46) "Hcg Hpc Hc1". iEval (rgne) in "Hc1".
    iEval (rewrite -Hld7c) in "Hc1".
    set (N7 := <[Regidx Ra5 := regval_into_reg (fnode k1)]> N6).
    assert (HN7a5 : N7 !!! Regidx Ra5 = fnode k1) by (rewrite /N7; apply upd_eq).
    assert (HN7s1 : N7 !!! Regidx Rs1 = pf0)
      by (rewrite /N7 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN7s4 : N7 !!! Regidx Rs4 = pf1)
      by (rewrite /N7 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN7s2 : N7 !!! Regidx Rs2 = pi)
      by (rewrite /N7 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN7s3 : N7 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /N7 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN7x0 : N7 !!! Regidx Rz = (zero_reg : mword 64))
      by (rewrite /N7 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN7sp : N7 !!! Regidx csp_rs1 = spr)
      by (rewrite /N7 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN7thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> c <> Rs2 -> c <> Rs3 ->
              N7 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs A2 A8 A9 A20 A18 A19. rewrite /N7 upd_ne; [| regne]. auto. }
    assert (Hst80 : add_vec_int (mword_of_int (PA + 0x7c) : mword 64) 4 = mword_of_int (PA + 0x80))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hst80) in "Hpc".
    assert (Had80 : a_fwritable k1 = add_vec (N7 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 9 : mword 12))).
    { rewrite HN7a5. reflexivity. }
    assert (Had80' : a_fwritable k1 = add_vec (rget N7 Ra5) (sign_extend' 64 (mword_of_int 9 : mword 12)))
      by (rgne; exact Had80).
    iEval (rewrite Had80') in "Hwr1".
    assert (Hvv80 : trunc8 (N7 !!! Regidx Rs3) = (mword_of_int 1 : mword 8))
      by (rewrite HN7s3; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_sb_s_sconf Φ (mword_of_int (PA + 0x80)) Rs3 Ra5 (mword_of_int 9 : mword 12)
              N7 (K - 6)%nat _ b with "Hcg Hpc Hi80 Hwr1 [-]").
    iIntros (CID47 Hs47) "Hcg Hpc Hwr1". iEval (rgne) in "Hwr1". iEval (rgne) in "Hwr1".
    iEval (rewrite -Had80 Hvv80) in "Hwr1".
    assert (Hnx84 : add_vec_int (mword_of_int (PA + 0x80) : mword 64) 4 = mword_of_int (PA + 0x84))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hnx84) in "Hpc".
    (* +0x84 load the file pointer, +0x88 store the field *)
    assert (Hld84 : pf1 = add_vec (N7 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite (_ : N7 !!! Regidx Rs4 = pf1); [symmetry; apply addv_sext0 | assumption]. }
    assert (Hld84' : pf1 = add_vec (rget N7 Rs4) (sign_extend' 64 (mword_of_int 0 : mword 12)))
      by (rgne; exact Hld84).
    iEval (rewrite Hld84') in "Hc1".
    iApply (wp_ld_s_sconf Φ (mword_of_int (PA + 0x84)) Ra5 Rs4 (mword_of_int 0 : mword 12)
              N7 (K - 6)%nat (fnode k1) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi84 Hc1 [-]").
    iIntros (CID48 Hs48) "Hcg Hpc Hc1". iEval (rgne) in "Hc1".
    iEval (rewrite -Hld84) in "Hc1".
    set (N8 := <[Regidx Ra5 := regval_into_reg (fnode k1)]> N7).
    assert (HN8a5 : N8 !!! Regidx Ra5 = fnode k1) by (rewrite /N8; apply upd_eq).
    assert (HN8s1 : N8 !!! Regidx Rs1 = pf0)
      by (rewrite /N8 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN8s4 : N8 !!! Regidx Rs4 = pf1)
      by (rewrite /N8 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN8s2 : N8 !!! Regidx Rs2 = pi)
      by (rewrite /N8 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN8s3 : N8 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /N8 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN8x0 : N8 !!! Regidx Rz = (zero_reg : mword 64))
      by (rewrite /N8 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN8sp : N8 !!! Regidx csp_rs1 = spr)
      by (rewrite /N8 upd_ne; [assumption | vm_compute; discriminate]).
    assert (HN8thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> c <> Rs2 -> c <> Rs3 ->
              N8 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs A2 A8 A9 A20 A18 A19. rewrite /N8 upd_ne; [| regne]. auto. }
    assert (Hst88 : add_vec_int (mword_of_int (PA + 0x84) : mword 64) 4 = mword_of_int (PA + 0x88))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hst88) in "Hpc".
    assert (Had88 : a_fpipe k1 = add_vec (N8 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 16 : mword 12))).
    { rewrite HN8a5. reflexivity. }
    assert (Had88' : a_fpipe k1 = add_vec (rget N8 Ra5) (sign_extend' 64 (mword_of_int 16 : mword 12)))
      by (rgne; exact Had88).
    iEval (rewrite Had88') in "Hpp1".
    iApply (wp_sd_s_sconf Φ (mword_of_int (PA + 0x88)) Rs2 Ra5 (mword_of_int 16 : mword 12)
              N8 (K - 6)%nat (fc_pipe Cf1) b with "Hcg Hpc Hi88 Hpp1 [-]").
    iIntros (CID49 Hs49) "Hcg Hpc Hpp1". iEval (rgne) in "Hpp1". iEval (rgne) in "Hpp1".
    iEval (rewrite -Had88 HN8s2) in "Hpp1".
    assert (Hnx8c : add_vec_int (mword_of_int (PA + 0x88) : mword 64) 4 = mword_of_int (PA + 0x8c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hnx8c) in "Hpc".
    (* +0x8c c.li a0,0 ; +0x8e/+0x90 restore s2/s3 ; +0x92 jump to the epilogue *)
    iApply (wp_cli_s_sconf Φ (mword_of_int (PA + 0x8c)) Ra0 (mword_of_int 0 : mword 6)
              (zero_reg : mword 64) N8 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi8c [-]").
    iIntros (CID50 Hs50) "Hcg Hpc".
    set (O1 := <[Regidx Ra0 := regval_into_reg (zero_reg : mword 64)]> N8).
    assert (HO1sp : O1 !!! Regidx csp_rs1 = spr)
      by (rewrite /O1 upd_ne; [exact HN8sp | vm_compute; discriminate]).
    assert (Hnx8e : add_vec_int (mword_of_int (PA + 0x8c) : mword 64) 2 = mword_of_int (PA + 0x8e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hnx8e) in "Hpc".
    (* +0x8e c.ldsp s2,16(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (PA + 0x8e)) (mword_of_int 2 : mword 6) Rs2
              O1 (K - 6)%nat (mD !!! Regidx Rs2) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8e [Hr16] [-]").
    { iEval (rewrite HO1sp). iExact "Hr16". }
    iIntros (CID51 Hs51) "Hcg Hpc Hr16".
    iEval (rewrite HO1sp Hs4pa) in "Hr16".
    set (O2 := <[Regidx Rs2 := regval_into_reg (mD !!! Regidx Rs2)]> O1).
    assert (HO2sp : O2 !!! Regidx csp_rs1 = spr)
      by (rewrite /O2 upd_ne; [exact HO1sp | vm_compute; discriminate]).
    assert (Hnx90 : add_vec_int (mword_of_int (PA + 0x8e) : mword 64) 2 = mword_of_int (PA + 0x90))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hnx90) in "Hpc".
    (* +0x90 c.ldsp s3,8(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (PA + 0x90)) (mword_of_int 1 : mword 6) Rs3
              O2 (K - 6)%nat (m !!! Regidx Rs3) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi90 [Hr8] [-]").
    { iEval (rewrite HO2sp). iExact "Hr8". }
    iIntros (CID52 Hs52) "Hcg Hpc Hr8".
    iEval (rewrite HO2sp Hs5pa) in "Hr8".
    set (O3 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> O2).
    assert (HO3sp : O3 !!! Regidx csp_rs1 = spr)
      by (rewrite /O3 upd_ne; [exact HO2sp | vm_compute; discriminate]).
    assert (HO3a0 : O3 !!! Regidx Ra0 = (zero_reg : mword 64)).
    { rewrite /O3 upd_ne; [| vm_compute; discriminate].
      rewrite /O2 upd_ne; [| vm_compute; discriminate].
      rewrite /O1; apply upd_eq. }
    assert (HO3thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 ->
              O3 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs A2 A8 A9 A20.
      destruct (decide (c = Rs3)) as [->|A19]; [rewrite /O3; apply upd_eq|].
      rewrite /O3 upd_ne; [| regne].
      destruct (decide (c = Rs2)) as [->|A18].
      { rewrite /O2 upd_eq.
        apply (HmDthr Rs2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). }
      rewrite /O2 upd_ne; [| regne].
      rewrite /O1 upd_ne; [| regne].
      apply HN8thr; assumption. }
    assert (Hnx92 : add_vec_int (mword_of_int (PA + 0x90) : mword 64) 2 = mword_of_int (PA + 0x92))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hnx92) in "Hpc".
    (* +0x92 c.j +0xb8 *)
    iApply (wp_cj_s_sconf Φ (mword_of_int (PA + 0x92))
              (sign_extend' 21 (concat_vec (mword_of_int 19 : mword 11) ('b"0")))
              O3 (K - 6)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi92 [-]").
    iIntros (CID53 Hs53). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (HtgtD : add_vec (mword_of_int (PA + 0x92) : mword 64)
                      (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 19 : mword 11) ('b"0"))))
                    = mword_of_int (PA + 0xb8))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HtgtD) in "Hpc".
    iDestruct (cpu_own_transport CID21 CID53 n eb p C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hepi" $! CID53 with "[%]"); [wp_next_chain|].
    iApply ("Hepi" $! O3 (zero_reg : mword 64) with "[%] Hcg Hpc Hcnt [Hr16 Hr8] [-]").
    { split; [exact HO3sp|]. split; [exact HO3a0 | exact HO3thr]. }
    { iExists (mD !!! Regidx Rs2), (m !!! Regidx Rs3). iFrame "Hr16 Hr8". }
    rewrite /pipealloc_post. iRight.
    iSplitR; [done|]. iFrame "Hav".
    iExists γpl, γp, pi, k0, k1,
      (MkFContent FD_PIPE (mword_of_int 1 : mword 8) (mword_of_int 0 : mword 8) pi
         (fc_ip Cf0) (fc_off Cf0) (fc_major Cf0)),
      (MkFContent FD_PIPE (mword_of_int 0 : mword 8) (mword_of_int 1 : mword 8) pi
         (fc_ip Cf1) (fc_off Cf1) (fc_major Cf1)).
    iSplitR; [iPureIntro; split; assumption|].
    iSplitR; [iPureIntro; rewrite /pipe_file; cbn; repeat split; reflexivity|].
    iSplitR; [iPureIntro; rewrite /pipe_file; cbn; repeat split; reflexivity|].
    iFrame "Hc0 Hc1 Hpipe Hrd Hwr".
    rewrite /file_ref /file_fields; cbn.
    iFrame "Htok0 Hty0 Hrd0 Hwr0 Hpp0 Hip0 Hoff0 Hmaj0".
    iFrame "Htok1 Hty1 Hrd1 Hwr1 Hpp1 Hip1 Hoff1 Hmaj1".
  Qed.

End ProofPipealloc.

End PipeallocProof.
