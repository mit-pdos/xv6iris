(* ProofUvmdealloc.v -- uvmdealloc() over the SIE-agnostic sconf world.

     uint64 uvmdealloc(pagetable_t pagetable, uint64 oldsz, uint64 newsz) {
       if (newsz >= oldsz) return oldsz;
       if (PGROUNDUP(newsz) < PGROUNDUP(oldsz)) {
         int npages = (PGROUNDUP(oldsz) - PGROUNDUP(newsz)) / PGSIZE;
         uvmunmap(pagetable, PGROUNDUP(newsz), npages, 1);
       }
       return newsz;
     }

   Spec of record: SpecUvmdealloc.v -- stated at the [proc_pt] altitude over
   uvmunmap's contract.  Twenty-nine instructions, a 32-byte ra/s0/s1 frame
   byte-identical to argint's/sys_uptime's, ONE call, and THREE paths that
   join at the single epilogue (+0x26):

     - [newsz >= oldsz]        : +0x0c bgeu TAKEN, s1 = oldsz;
     - the two PGROUNDUPs tie  : +0x22 bltu FALLS,  s1 = newsz;
     - something to unmap      : +0x22 bltu TAKEN -> uvmunmap -> +0x42 c.j.

   Nothing is shrink-wrapped, so the [iAssert]ed epilogue continuation [EPI]
   owns all four frame cells and takes only (the register file at +0x26, the
   return value [res], the post's disjunct at [res]) as wand arguments.

   THE WHOLE CONTENT IS ARITHMETIC.  +0x12..+0x20 compute
   [and_vec (add_vec x (mword_of_int 4095)) (mword_of_int (-4096))] twice,
   which is EXACTLY [ProcPtOwn.pgroundup]; +0x32/+0x34/+0x38 turn the
   difference into [mword_of_int (Z.of_nat (uvmd_np oldsz newsz))].  Per
   claude-notes/durable-notes.md all of that arithmetic is factored into
   [mword]-free top-level [Z] lemmas ([udl_z_*] below), because any goal
   mentioning [bv_unsigned] answers "Cannot find witness" to [lia] under this
   file's transitive [bitvector.tactics] import.

   On the two arms that SKIP the unmap, [uvmd_np oldsz newsz = 0] (the
   quotient is 0 or negative and [Z.to_nat] clamps), so the descriptor the
   spec names is [P] with its derived [ud_data] field renormalised --
   [ProcPtOwn.proc_pt_data_irrel] transports [proc_pt] across that. *)
Set Printing Depth 40.
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import CalleeSaved StackOwn.
Require Import IntrDefs WpSmodeIntr.
Require Import WpLock.
Require Import KallocInv.
Require Import PtTree PtBuild.
Require Import UptTree UserPtTree.
Require Import ProcGeom CpuOwn.
Require Import KvmSpec.
Require Import ProcPt ProcPtOwn.
Require Import WpUvmdeallocDecode.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecUvmunmap.
Require Import SpecUvmdealloc.
Require Import KernelRvcDecode.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §0  Plain-[Z] arithmetic.  Everything [lia] must see lives here, with  *)
(*     no [mword] / [bv_unsigned] anywhere in the statement (the zify     *)
(*     hook rule -- claude-notes/durable-notes.md).                       *)
(*     These belong next to [pgroundup_unsigned] in ProcPtOwn.v.          *)
(* ===================================================================== *)

(* [uvm_maxsz] as a literal, so the two size premises can be fed to [lia]. *)
Lemma udl_z_lt264 (v : Z) : v + 4096 <= 274877898752 -> v + 4095 < 2 ^ 64.
Proof. intros H. change (2 ^ 64) with 18446744073709551616. lia. Qed.

(* PGROUNDUP -- as [pgroundup_unsigned] reads it -- is MONOTONE. *)
Lemma udl_z_pgu_mono (a b : Z) :
  a <= b -> (a + 4095) - (a + 4095) mod 4096 <= (b + 4095) - (b + 4095) mod 4096.
Proof.
  intros Hab.
  pose proof (Z_div_mod_eq_full (a + 4095) 4096) as Ha.
  pose proof (Z_div_mod_eq_full (b + 4095) 4096) as Hb.
  assert (Hd : (a + 4095) / 4096 <= (b + 4095) / 4096)
    by (apply Z.div_le_mono; lia).
  lia.
Qed.

(* ... and never exceeds its argument by a page. *)
Lemma udl_z_pgu_bound (v : Z) :
  0 <= v -> v + 4096 <= 274877898752 ->
  (v + 4095) - (v + 4095) mod 4096 <= 274877898751.
Proof.
  intros H0 H1. pose proof (Z.mod_pos_bound (v + 4095) 4096 ltac:(lia)). lia.
Qed.

Lemma udl_z_tonat0 (q : Z) : q <= 0 -> Z.to_nat q = 0%nat.
Proof. intros H. destruct q as [| pz | pz]; [reflexivity | exfalso; lia | reflexivity]. Qed.

Lemma udl_z_np0 (pu pn : Z) : pu <= pn -> Z.to_nat ((pu - pn) / 4096) = 0%nat.
Proof.
  intros H. apply udl_z_tonat0.
  apply Z.div_le_upper_bound; lia.
Qed.

(* the run length on the arm that DOES unmap: the difference of two
   page-aligned values divides exactly. *)
Lemma udl_z_np_exact (pu pn : Z) :
  pn <= pu -> pu mod 4096 = 0 -> pn mod 4096 = 0 ->
  0 <= (pu - pn) / 4096 /\ (pu - pn) / 4096 * 4096 = pu - pn.
Proof.
  intros Hle Hu Hn.
  assert (Hm : (pu - pn) mod 4096 = 0)
    by (rewrite Zminus_mod Hu Hn; vm_compute; reflexivity).
  pose proof (Z_div_mod_eq_full (pu - pn) 4096) as Hdm.
  split; [apply Z.div_pos; lia | lia].
Qed.

Lemma udl_z_np_lt31 (pu pn : Z) :
  0 <= pn -> pu <= 274877898751 -> (pu - pn) / 4096 < 2147483648.
Proof.
  intros H0 H1.
  apply Z.le_lt_trans with (pu / 4096).
  - apply Z.div_le_mono; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma udl_z_div4096_range (v : Z) :
  0 <= v < 18446744073709551616 -> 0 <= v / 4096 < 18446744073709551616.
Proof.
  intros [H0 H1]. split; [apply Z.div_pos; lia |].
  apply Z.le_lt_trans with v; [| lia]. apply Z.div_le_upper_bound; lia.
Qed.

(* ===================================================================== *)
(* §1  Two [mword] bridges.  [udl_addv_comm] belongs in RiscvExtras.v,    *)
(*     [udl_srli12] next to [subrange_31_0_unsigned] there.               *)
(* ===================================================================== *)

Lemma udl_addv_comm (x y : mword 64) : add_vec x y = add_vec y x.
Proof.
  apply bv_eq. rewrite !add_vec64_unsigned. rewrite Z.add_comm. reflexivity.
Qed.

(* [srli rd,rs,0xc] is unsigned division by the page size. *)
Lemma udl_srli12 (x : mword 64) :
  shift_bits_right x (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int (bv_unsigned x / 4096) : mword 64).
Proof.
  assert (Hr : shift_bits_right x
                 (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
             = shiftr x 12).
  { unfold shift_bits_right. f_equal; vm_compute; reflexivity. }
  rewrite Hr. apply bv_eq.
  unfold shiftr, SailStdpp.Values.with_word, get_word,
    MachineWord.MachineWord.logical_shift_right.
  rewrite bv_shiftr_unsigned.
  assert (H12 : bv_unsigned (MachineWord.MachineWord.N_to_word
                   (MachineWord.MachineWord.Z_idx 64) (MachineWord.MachineWord.Z_idx 12)) = 12).
  { unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus; simpl; lia. }
  rewrite H12. rewrite Z.shiftr_div_pow2; [| lia].
  change (2 ^ 12) with 4096.
  rewrite moi64_unsigned. symmetry. apply bvw64_small.
  apply udl_z_div4096_range.
  pose proof (bv_unsigned_in_range _ x) as Hr64.
  assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616)
    by (vm_compute; reflexivity).
  rewrite Hm in Hr64. exact Hr64.
Qed.

(* ===================================================================== *)
(* §2  The compressed [c.sub rd,rd,rs2] leaf.  Its base-width twin        *)
(*     [wp_sub_s_sconf] is in WpSconfAlu.v; this belongs right next to    *)
(*     it (uvmdealloc is the first caller of the compressed form, just as *)
(*     [udexec_C_SUB] in WpUvmdeallocDecode.v is the first user of the    *)
(*     kernel-side C_SUB expansion).                                      *)
(* ===================================================================== *)

Section WpCsub.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_csub_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sub_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗ instr pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) -∗
    ( sie_cap_gpr γ (<[Regidx rd := regval_into_reg wval]> m) n -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf γ Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) wval m n
              Hrd Hrdsp _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)))
        with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) SUB).
      rewrite (exec_execute_RTYPE_SUB_gpr rs2 rs1 rd s_pc).
      replace (Z.eqb (uint rd) 0) with false
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_sub_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

End WpCsub.

(* ===================================================================== *)
(* THE WHOLE FUNCTION.                                                    *)
(* ===================================================================== *)

Module UvmdeallocProof (Uvmunmap : UVMUNMAP) : UVMDEALLOC.

Section ProofUvmdealloc.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{CID : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Lemma udl_cr5 : creg2reg_idx (Cregidx (mword_of_int 5)) = Regidx Ra3.
  Proof. vm_compute. reflexivity. Qed.
  Lemma udl_cr6 : creg2reg_idx (Cregidx (mword_of_int 6)) = Regidx Ra4.
  Proof. vm_compute. reflexivity. Qed.
  Lemma udl_cr7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx Ra5.
  Proof. vm_compute. reflexivity. Qed.

  Lemma wp_uvmdealloc_sconf
      (γ : gname) (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile)
      (P : uptd) (K : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    : wp_uvmdealloc_sconf_body γ γa Φ mm P K eb p C.
  Proof.
    cbv beta delta [wp_uvmdealloc_sconf_body].
    intros pcE oldsz newsz ret_tgt HK Htp Hroot Hob Hnb.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iIntros "Hcg Hcpu #Htext Hpc Hpt Henv Hcont".

    (* ================================================================= *)
    (* §A  The pure PGROUNDUP arithmetic, once and for all.               *)
    (* ================================================================= *)
    assert (Hmax : uvm_maxsz = 274877898752) by (vm_compute; reflexivity).
    assert (Hobz : bv_unsigned oldsz + 4096 <= 274877898752)
      by (rewrite -uint_unsigned -Hmax; exact Hob).
    assert (Hnbz : bv_unsigned newsz + 4096 <= 274877898752)
      by (rewrite -uint_unsigned -Hmax; exact Hnb).
    assert (Hpuz : bv_unsigned (pgroundup oldsz)
                   = (bv_unsigned oldsz + 4095) - (bv_unsigned oldsz + 4095) mod 4096)
      by (apply pgroundup_unsigned; apply udl_z_lt264; exact Hobz).
    assert (Hpnz : bv_unsigned (pgroundup newsz)
                   = (bv_unsigned newsz + 4095) - (bv_unsigned newsz + 4095) mod 4096)
      by (apply pgroundup_unsigned; apply udl_z_lt264; exact Hnbz).
    assert (Hpumod : bv_unsigned (pgroundup oldsz) mod 4096 = 0)
      by (rewrite Hpuz; apply z_pgd_mod).
    assert (Hpnmod : bv_unsigned (pgroundup newsz) mod 4096 = 0)
      by (rewrite Hpnz; apply z_pgd_mod).
    assert (Hpubnd : bv_unsigned (pgroundup oldsz) <= 274877898751).
    { rewrite Hpuz. apply udl_z_pgu_bound;
        [exact (proj1 (bv_unsigned_in_range _ oldsz)) | exact Hobz]. }
    assert (Hpn0 : 0 <= bv_unsigned (pgroundup newsz))
      by exact (proj1 (bv_unsigned_in_range _ (pgroundup newsz))).

    (* the transport of [proc_pt P] to the zero-length-run descriptor *)
    assert (Hnpdef : uvmd_np oldsz newsz
                     = Z.to_nat ((bv_unsigned (pgroundup oldsz)
                                  - bv_unsigned (pgroundup newsz)) / 4096))
      by reflexivity.

    (* ================================================================= *)
    (* §B  PROLOGUE: the 32-byte ra/s0/s1 frame.                          *)
    (* ================================================================= *)
    iPoseProof (udi_00 with "Htext") as "Hi00".
    iPoseProof (udi_02 with "Htext") as "Hi02".
    iPoseProof (udi_04 with "Htext") as "Hi04".
    iPoseProof (udi_06 with "Htext") as "Hi06".
    iPoseProof (udi_08 with "Htext") as "Hi08".
    iPoseProof (udi_0a with "Htext") as "Hi0a".
    iPoseProof (udi_0c with "Htext") as "Hi0c".
    assert (Hspm : mm !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (mm !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf γ Φ pcE (mword_of_int 32 : mword 6) mm K 4
              ltac:(lia) Hpush with "Hcg Hpc Hi00 [-]").
    iIntros "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> mm).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> mm) with A0.
    assert (HA0sp : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (UD + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (UD + 0x02)) (mword_of_int 3 : mword 6) Rra
              A0 (K - 4)%nat vr24 with "Hcg Hpc Hi02 [Hr24] [-]").
    { iEval (rewrite HA0sp -Hb1). iExact "Hr24". }
    iIntros "Hcg Hpc Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (UD + 0x02) : mword 64) 2 = mword_of_int (UD + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (UD + 0x04)) (mword_of_int 2 : mword 6) Rs0
              A0 (K - 4)%nat vr16 with "Hcg Hpc Hi04 [Hr16] [-]").
    { iEval (rewrite HA0sp -Hb2). iExact "Hr16". }
    iIntros "Hcg Hpc Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (UD + 0x04) : mword 64) 2 = mword_of_int (UD + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (UD + 0x06)) (mword_of_int 1 : mword 6) Rs1
              A0 (K - 4)%nat vr8 with "Hcg Hpc Hi06 [Hr8] [-]").
    { iEval (rewrite HA0sp -Hb3). iExact "Hr8". }
    iIntros "Hcg Hpc Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (UD + 0x06) : mword 64) 2 = mword_of_int (UD + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* normalize the three saved cells to the epilogue's reload shape *)
    assert (HA0ra : A0 !!! Regidx Rra = mm !!! Regidx Rra)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (HA0s0 : A0 !!! Regidx Rs0 = mm !!! Regidx Rs0)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (HA0s1 : A0 !!! Regidx Rs1 = mm !!! Regidx Rs1)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HA0sp HA0ra) in "Hr24".
    iEval (rewrite HA0sp HA0s0) in "Hr16".
    iEval (rewrite HA0sp HA0s1) in "Hr8".
    (* +0x08 c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (UD + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 A0 (K - 4)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi08 [-]").
    iIntros "Hcg Hpc".
    set (A1 := <[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpc0a : add_vec_int (mword_of_int (UD + 0x08) : mword 64) 2 = mword_of_int (UD + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    assert (HA1a1 : A1 !!! Regidx Ra1 = oldsz).
    { rewrite /A1 upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [| reg_neq]. reflexivity. }
    (* +0x0a c.mv s1,a1 : s1 := oldsz *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (UD + 0x0a)) Rs1 Ra1 A1 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0a [-]").
    iIntros "Hcg Hpc".
    iEval (rewrite HA1a1 add_vec_zero_l) in "Hcg".
    set (A2 := <[Regidx Rs1 := regval_into_reg oldsz]> A1).
    change (<[Regidx Rs1 := regval_into_reg oldsz]> A1) with A2.
    assert (Hpc0c : add_vec_int (mword_of_int (UD + 0x0a) : mword 64) 2 = mword_of_int (UD + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    (* the register facts at the first branch *)
    assert (HA2sp : A2 !!! Regidx csp_rs1 = spd).
    { rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [| reg_neq]. exact HA0sp. }
    assert (HA2s1 : A2 !!! Regidx Rs1 = oldsz) by (rewrite /A2 upd_eq; reflexivity).
    assert (HA2a1 : A2 !!! Regidx Ra1 = oldsz)
      by (rewrite /A2 upd_ne; [exact HA1a1 | reg_neq]).
    assert (HA2a2 : A2 !!! Regidx Ra2 = newsz).
    { rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [| reg_neq].
      rewrite /A0 upd_ne; [| reg_neq]. reflexivity. }
    assert (HA2a0 : A2 !!! Regidx Ra0 = page_base (ud_root P)).
    { rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [| reg_neq].
      rewrite /A0 upd_ne; [| reg_neq]. exact Hroot. }
    assert (HA2tp : A2 !!! Regidx Rtp = cid_word).
    { rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [| reg_neq].
      rewrite /A0 upd_ne; [| reg_neq]. exact Htp. }
    assert (HA2thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              A2 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9.
      rewrite /A2 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
      rewrite /A1 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H8; reflexivity].
      rewrite /A0 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H2; reflexivity].
      reflexivity. }

    (* ================================================================= *)
    (* §C  THE EPILOGUE / JOIN at +0x26, taken before the first branch.   *)
    (* ================================================================= *)
    iPoseProof (udi_26 with "Htext") as "Hi26".
    iPoseProof (udi_28 with "Htext") as "Hi28".
    iPoseProof (udi_2a with "Htext") as "Hi2a".
    iPoseProof (udi_2c with "Htext") as "Hi2c".
    iPoseProof (udi_2e with "Htext") as "Hi2e".
    iPoseProof (udi_30 with "Htext") as "Hi30".
    set (EPI := (∀ (mj : regfile) (res : mword 64),
        ⌜ mj !!! Regidx csp_rs1 = spd
          /\ mj !!! Regidx Rs1 = res
          /\ (forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
                mj !!! Regidx c = mm !!! Regidx c) ⌝ -∗
        ⌜ ((uint newsz >= uint oldsz)%Z /\ res = oldsz)
          \/ ((uint newsz < uint oldsz)%Z /\ res = newsz) ⌝ -∗
        sie_cap_gpr γ mj (K - 4)%nat -∗
        cpu_own γ 0%nat eb p C -∗
        pc_is (mword_of_int (UD + 0x26) : mword 64) -∗
        proc_pt (uptd_del_run P (svpn_of (pgroundup newsz)) (uvmd_np oldsz newsz)) -∗
        WP (Loop : expr riscv_lang) {{ Φ }})%I).
    iAssert EPI with "[Hcont Hr24 Hr16 Hr8 Hgap]" as "Hepi".
    { rewrite /EPI.
      iIntros (mj res) "(%Hjsp & %Hjs1 & %Hjthr) %Hpay Hcg Hcpu Hpc Hpt".
      (* +0x26 c.mv a0,s1 *)
      iApply (wp_cmv_s_sconf γ Φ (mword_of_int (UD + 0x26)) Ra0 Rs1 mj (K - 4)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi26 [-]").
      iIntros "Hcg Hpc".
      iEval (rewrite Hjs1 add_vec_zero_l) in "Hcg".
      set (E0 := <[Regidx Ra0 := regval_into_reg res]> mj).
      change (<[Regidx Ra0 := regval_into_reg res]> mj) with E0.
      assert (HE0sp : E0 !!! Regidx csp_rs1 = spd)
        by (rewrite /E0 upd_ne; [exact Hjsp | reg_neq]).
      assert (Hpc28 : add_vec_int (mword_of_int (UD + 0x26) : mword 64) 2
                      = mword_of_int (UD + 0x28))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc28) in "Hpc".
      (* +0x28 c.ldsp ra,24(sp) *)
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (UD + 0x28)) (mword_of_int 3 : mword 6) Rra
                E0 (K - 4)%nat (mm !!! Regidx Rra) (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi28 [Hr24] [-]").
      { iEval (rewrite HE0sp). iExact "Hr24". }
      iIntros "Hcg Hpc Hr24". iEval (rewrite HE0sp) in "Hr24".
      set (E1 := <[Regidx Rra := regval_into_reg (mm !!! Regidx Rra)]> E0).
      change (<[Regidx Rra := regval_into_reg (mm !!! Regidx Rra)]> E0) with E1.
      assert (HE1sp : E1 !!! Regidx csp_rs1 = spd)
        by (rewrite /E1 upd_ne; [exact HE0sp | reg_neq]).
      assert (Hpc2a : add_vec_int (mword_of_int (UD + 0x28) : mword 64) 2
                      = mword_of_int (UD + 0x2a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc2a) in "Hpc".
      (* +0x2a c.ldsp s0,16(sp) *)
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (UD + 0x2a)) (mword_of_int 2 : mword 6) Rs0
                E1 (K - 4)%nat (mm !!! Regidx Rs0) (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi2a [Hr16] [-]").
      { iEval (rewrite HE1sp). iExact "Hr16". }
      iIntros "Hcg Hpc Hr16". iEval (rewrite HE1sp) in "Hr16".
      set (E2 := <[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0)]> E1).
      change (<[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0)]> E1) with E2.
      assert (HE2sp : E2 !!! Regidx csp_rs1 = spd)
        by (rewrite /E2 upd_ne; [exact HE1sp | reg_neq]).
      assert (Hpc2c : add_vec_int (mword_of_int (UD + 0x2a) : mword 64) 2
                      = mword_of_int (UD + 0x2c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc2c) in "Hpc".
      (* +0x2c c.ldsp s1,8(sp) *)
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (UD + 0x2c)) (mword_of_int 1 : mword 6) Rs1
                E2 (K - 4)%nat (mm !!! Regidx Rs1) (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi2c [Hr8] [-]").
      { iEval (rewrite HE2sp). iExact "Hr8". }
      iIntros "Hcg Hpc Hr8". iEval (rewrite HE2sp) in "Hr8".
      set (E3 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> E2).
      change (<[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> E2) with E3.
      assert (HE3sp : E3 !!! Regidx csp_rs1 = spd)
        by (rewrite /E3 upd_ne; [exact HE2sp | reg_neq]).
      assert (Hpc2e : add_vec_int (mword_of_int (UD + 0x2c) : mword 64) 2
                      = mword_of_int (UD + 0x2e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc2e) in "Hpc".
      (* +0x2e c.addi16sp sp,32 -- the frame pop *)
      set (E4 := <[Regidx csp_rs1 := regval_into_reg
          (add_vec (E3 !!! Regidx csp_rs1)
             (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
      assert (Hsp0up : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
      { rewrite /spd /sp0 po_addv_assoc.
        assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                      = mword_of_int 0)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite HAB. apply avi0. }
      assert (Hwv : add_vec (E3 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
        by (rewrite HE3sp; exact Hsp0up).
      assert (Hpop : E3 !!! Regidx csp_rs1
                     = pa_stk (add_vec (E3 !!! Regidx csp_rs1)
                                 (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
      { rewrite Hwv HE3sp. symmetry. exact Hspd4. }
      iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hr24". { iExists _. iEval (rewrite Hb1). iExact "Hr24". }
        iSplitL "Hr16". { iExists _. iEval (rewrite Hb2). iExact "Hr16". }
        iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3). iExact "Hr8". }
        iSplitL "Hgap". { iExists _. iExact "Hgap". }
        done. }
      iEval (rewrite -Hwv) in "Hframe4".
      iApply (wp_caddi16sp_pop_s_sconf γ Φ (mword_of_int (UD + 0x2e))
                (mword_of_int 2 : mword 6) E3 (K - 4)%nat 4 Hpop
                with "Hcg Hpc Hi2e Hframe4 [-]").
      iIntros "Hcg Hpc".
      change (<[Regidx csp_rs1 := regval_into_reg
          (add_vec (E3 !!! Regidx csp_rs1)
             (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
      assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
      iEval (rewrite Hnk) in "Hcg".
      assert (Hpc30 : add_vec_int (mword_of_int (UD + 0x2e) : mword 64) 2
                      = mword_of_int (UD + 0x30))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc30) in "Hpc".
      (* +0x30 c.ret *)
      assert (HE4ra : E4 !!! Regidx Rra = mm !!! Regidx Rra).
      { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
        rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_eq. reflexivity. }
      assert (HE4a0 : E4 !!! Regidx Ra0 = res).
      { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
        rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_ne; [| reg_neq].
        rewrite /E0 upd_eq. reflexivity. }
      assert (HE4sp : E4 !!! Regidx csp_rs1 = mm !!! Regidx csp_rs1)
        by (rewrite /E4 upd_eq; exact Hwv).
      assert (HE4s0 : E4 !!! Regidx Rs0 = mm !!! Regidx Rs0).
      { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
        rewrite /E2 upd_eq. reflexivity. }
      assert (HE4s1 : E4 !!! Regidx Rs1 = mm !!! Regidx Rs1).
      { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_eq. reflexivity. }
      assert (HE4thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
                E4 !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9.
        rewrite /E4 upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H2; reflexivity].
        rewrite /E3 upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
        rewrite /E2 upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H8; reflexivity].
        rewrite /E1 upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        rewrite /E0 upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        apply Hjthr; assumption. }
      iApply (wp_cret_s_sconf γ Φ (mword_of_int (UD + 0x30)) Rra E4 K
                ltac:(vm_compute; discriminate) with "Hcg Hpc Hi30 [-]").
      iIntros "Hcg Hpc".
      assert (Hretf : ret_pc (E4 !!! Regidx Rra) = ret_tgt) by (rewrite HE4ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      iApply ("Hcont" $! E4 with "Hcg Hcpu Hpc [%] [%] Hpt").
      { unfold callee_saved. split_and!;
          first [ exact HE4sp | exact HE4s0 | exact HE4s1
                | apply HE4thr; vm_compute; first [reflexivity | discriminate] ]. }
      { rewrite HE4a0. exact Hpay. } }

    (* ================================================================= *)
    (* §D  +0x0c bgeu a2,a1 : the [newsz >= oldsz] early-out.             *)
    (* ================================================================= *)
    destruct (zopz0zKzJ_u newsz oldsz) eqn:Hcmp1.
    { (* ---- TAKEN: nothing to do, s1 already holds oldsz ---- *)
      assert (Hge : uint oldsz <= uint newsz).
      { unfold zopz0zKzJ_u in Hcmp1. rewrite Z.geb_leb in Hcmp1.
        exact (proj1 (Z.leb_le _ _) Hcmp1). }
      assert (Hcmp1' : zopz0zKzJ_u (A2 !!! Regidx Ra2) (A2 !!! Regidx Ra1) = true)
        by (rewrite HA2a2 HA2a1; exact Hcmp1).
      (* the run is empty *)
      assert (Hple : bv_unsigned (pgroundup oldsz) <= bv_unsigned (pgroundup newsz)).
      { rewrite Hpuz Hpnz. apply udl_z_pgu_mono.
        rewrite -!uint_unsigned. exact Hge. }
      assert (Hnp0 : uvmd_np oldsz newsz = 0%nat)
        by (rewrite Hnpdef; apply udl_z_np0; exact Hple).
      iAssert (proc_pt (uptd_del_run P (svpn_of (pgroundup newsz)) (uvmd_np oldsz newsz)))
        with "[Hpt]" as "Hpt".
      { iEval (rewrite (proc_pt_data_irrel P
                 (uptd_del_run P (svpn_of (pgroundup newsz)) (uvmd_np oldsz newsz))
                 ltac:(rewrite Hnp0; reflexivity)
                 ltac:(rewrite Hnp0; reflexivity)
                 ltac:(rewrite Hnp0; reflexivity))) in "Hpt".
        iExact "Hpt". }
      iApply (wp_bgeu_taken_s_sconf γ Φ (mword_of_int (UD + 0x0c))
                (mword_of_int 26 : mword 13) Ra1 Ra2 A2 (K - 4)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp1' ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi0c [-]").
      iNext. iIntros "Hcg Hpc".
      assert (Htgt26 : add_vec (mword_of_int (UD + 0x0c) : mword 64)
                         (sign_extend' 64 (mword_of_int 26 : mword 13))
                       = mword_of_int (UD + 0x26))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt26) in "Hpc".
      iApply ("Hepi" $! A2 oldsz with "[%] [%] Hcg Hcpu Hpc Hpt").
      { split_and!; [exact HA2sp | exact HA2s1 | exact HA2thr]. }
      { left. split; [apply Z.le_ge; exact Hge | reflexivity]. } }

    (* ---- FALLS: newsz < oldsz ---- *)
    assert (Hlt : uint newsz < uint oldsz).
    { unfold zopz0zKzJ_u in Hcmp1. rewrite Z.geb_leb in Hcmp1.
      exact (proj1 (Z.leb_gt _ _) Hcmp1). }
    assert (Hcmp1' : zopz0zKzJ_u (A2 !!! Regidx Ra2) (A2 !!! Regidx Ra1) = false)
      by (rewrite HA2a2 HA2a1; exact Hcmp1).
    iApply (wp_bgeu_fall_s_sconf γ Φ (mword_of_int (UD + 0x0c))
              (mword_of_int 26 : mword 13) Ra1 Ra2 A2 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hcmp1'
              with "Hcg Hpc Hi0c [-]").
    iIntros "Hcg Hpc".
    assert (Hpc10 : add_vec_int (mword_of_int (UD + 0x0c) : mword 64) 4
                    = mword_of_int (UD + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".

    (* ================================================================= *)
    (* §E  +0x10..+0x20: s1 := newsz, and the two PGROUNDUPs.             *)
    (* ================================================================= *)
    iPoseProof (udi_10 with "Htext") as "Hi10".
    iPoseProof (udi_12 with "Htext") as "Hi12".
    iPoseProof (udi_14 with "Htext") as "Hi14".
    iPoseProof (udi_16 with "Htext") as "Hi16".
    iPoseProof (udi_1a with "Htext") as "Hi1a".
    iPoseProof (udi_1c with "Htext") as "Hi1c".
    iPoseProof (udi_1e with "Htext") as "Hi1e".
    iPoseProof (udi_20 with "Htext") as "Hi20".
    iPoseProof (udi_22 with "Htext") as "Hi22".
    (* +0x10 c.mv s1,a2 : s1 := newsz *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (UD + 0x10)) Rs1 Ra2 A2 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi10 [-]").
    iIntros "Hcg Hpc".
    iEval (rewrite HA2a2 add_vec_zero_l) in "Hcg".
    set (A3 := <[Regidx Rs1 := regval_into_reg newsz]> A2).
    change (<[Regidx Rs1 := regval_into_reg newsz]> A2) with A3.
    assert (Hpc12 : add_vec_int (mword_of_int (UD + 0x10) : mword 64) 2
                    = mword_of_int (UD + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    assert (HA3sp : A3 !!! Regidx csp_rs1 = spd)
      by (rewrite /A3 upd_ne; [exact HA2sp | reg_neq]).
    assert (HA3s1 : A3 !!! Regidx Rs1 = newsz) by (rewrite /A3 upd_eq; reflexivity).
    assert (HA3a1 : A3 !!! Regidx Ra1 = oldsz)
      by (rewrite /A3 upd_ne; [exact HA2a1 | reg_neq]).
    assert (HA3a2 : A3 !!! Regidx Ra2 = newsz)
      by (rewrite /A3 upd_ne; [exact HA2a2 | reg_neq]).
    assert (HA3a0 : A3 !!! Regidx Ra0 = page_base (ud_root P))
      by (rewrite /A3 upd_ne; [exact HA2a0 | reg_neq]).
    assert (HA3tp : A3 !!! Regidx Rtp = cid_word)
      by (rewrite /A3 upd_ne; [exact HA2tp | reg_neq]).
    assert (HA3thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              A3 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9.
      rewrite /A3 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
      apply HA2thr; assumption. }
    (* +0x12 c.lui a5,0x1 : a5 := 4096 *)
    iApply (wp_clui_s_sconf γ Φ (mword_of_int (UD + 0x12)) Ra5
              (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
              A3 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) lui_4096
              with "Hcg Hpc Hi12 [-]").
    iIntros "Hcg Hpc".
    set (A4 := <[Regidx Ra5 := regval_into_reg (mword_of_int 4096 : mword 64)]> A3).
    change (<[Regidx Ra5 := regval_into_reg (mword_of_int 4096 : mword 64)]> A3) with A4.
    assert (Hpc14 : add_vec_int (mword_of_int (UD + 0x12) : mword 64) 2
                    = mword_of_int (UD + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    assert (HA4a5 : A4 !!! Regidx Ra5 = (mword_of_int 4096 : mword 64))
      by (rewrite /A4 upd_eq; reflexivity).
    (* +0x14 c.addi a5,a5,-1 : a5 := 4095 *)
    iApply (wp_caddi_s_sconf γ Φ (mword_of_int (UD + 0x14)) Ra5 (mword_of_int 63 : mword 6)
              A4 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi14 [-]").
    iIntros "Hcg Hpc".
    assert (H4095 : add_vec (A4 !!! Regidx Ra5)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
                    = (mword_of_int 4095 : mword 64))
      by (rewrite HA4a5; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite H4095) in "Hcg".
    set (A5 := <[Regidx Ra5 := regval_into_reg (mword_of_int 4095 : mword 64)]> A4).
    change (<[Regidx Ra5 := regval_into_reg (mword_of_int 4095 : mword 64)]> A4) with A5.
    assert (Hpc16 : add_vec_int (mword_of_int (UD + 0x14) : mword 64) 2
                    = mword_of_int (UD + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    assert (HA5a5 : A5 !!! Regidx Ra5 = (mword_of_int 4095 : mword 64))
      by (rewrite /A5 upd_eq; reflexivity).
    assert (HA5a2 : A5 !!! Regidx Ra2 = newsz).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq]. exact HA3a2. }
    assert (HA5a1 : A5 !!! Regidx Ra1 = oldsz).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq]. exact HA3a1. }
    (* +0x16 add a4,a2,a5 : a4 := newsz + 4095 *)
    iApply (wp_add_s_sconf γ Φ (mword_of_int (UD + 0x16)) Ra4 Ra2 Ra5
              (add_vec newsz (mword_of_int 4095)) A5 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite HA5a2 HA5a5; reflexivity)
              with "Hcg Hpc Hi16 [-]").
    iIntros "Hcg Hpc".
    set (A6 := <[Regidx Ra4 := regval_into_reg (add_vec newsz (mword_of_int 4095))]> A5).
    change (<[Regidx Ra4 := regval_into_reg (add_vec newsz (mword_of_int 4095))]> A5) with A6.
    assert (Hpc1a : add_vec_int (mword_of_int (UD + 0x16) : mword 64) 4
                    = mword_of_int (UD + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* +0x1a c.lui a3,0xfffff : a3 := -4096 *)
    iApply (wp_clui_s_sconf γ Φ (mword_of_int (UD + 0x1a)) Ra3
              (sign_extend' 20 (mword_of_int 63 : mword 6)) (mword_of_int (-4096) : mword 64)
              A6 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) lui_m4096
              with "Hcg Hpc Hi1a [-]").
    iIntros "Hcg Hpc".
    set (A7 := <[Regidx Ra3 := regval_into_reg (mword_of_int (-4096) : mword 64)]> A6).
    change (<[Regidx Ra3 := regval_into_reg (mword_of_int (-4096) : mword 64)]> A6) with A7.
    assert (Hpc1c : add_vec_int (mword_of_int (UD + 0x1a) : mword 64) 2
                    = mword_of_int (UD + 0x1c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    assert (HA7a3 : A7 !!! Regidx Ra3 = (mword_of_int (-4096) : mword 64))
      by (rewrite /A7 upd_eq; reflexivity).
    assert (HA7a4 : A7 !!! Regidx Ra4 = add_vec newsz (mword_of_int 4095)).
    { rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_eq. reflexivity. }
    assert (HA7a5 : A7 !!! Regidx Ra5 = (mword_of_int 4095 : mword 64)).
    { rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_ne; [| reg_neq]. exact HA5a5. }
    assert (HA7a1 : A7 !!! Regidx Ra1 = oldsz).
    { rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_ne; [| reg_neq]. exact HA5a1. }
    (* +0x1c c.and a4,a4,a3 : a4 := PGROUNDUP(newsz) *)
    iEval (rewrite udl_cr5 udl_cr6) in "Hi1c".
    iApply (wp_cand_s_sconf γ Φ (mword_of_int (UD + 0x1c)) Ra4 Ra3 A7 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1c [-]").
    iIntros "Hcg Hpc".
    assert (Hpgun : and_vec (A7 !!! Regidx Ra4) (A7 !!! Regidx Ra3) = pgroundup newsz)
      by (rewrite HA7a4 HA7a3; reflexivity).
    iEval (rewrite Hpgun) in "Hcg".
    set (A8 := <[Regidx Ra4 := regval_into_reg (pgroundup newsz)]> A7).
    change (<[Regidx Ra4 := regval_into_reg (pgroundup newsz)]> A7) with A8.
    assert (Hpc1e : add_vec_int (mword_of_int (UD + 0x1c) : mword 64) 2
                    = mword_of_int (UD + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    assert (HA8a5 : A8 !!! Regidx Ra5 = (mword_of_int 4095 : mword 64))
      by (rewrite /A8 upd_ne; [exact HA7a5 | reg_neq]).
    assert (HA8a1 : A8 !!! Regidx Ra1 = oldsz)
      by (rewrite /A8 upd_ne; [exact HA7a1 | reg_neq]).
    assert (HA8a3 : A8 !!! Regidx Ra3 = (mword_of_int (-4096) : mword 64))
      by (rewrite /A8 upd_ne; [exact HA7a3 | reg_neq]).
    (* +0x1e c.add a5,a5,a1 : a5 := 4095 + oldsz *)
    iApply (wp_cadd_s_sconf γ Φ (mword_of_int (UD + 0x1e)) Ra5 Ra1 A8 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1e [-]").
    iIntros "Hcg Hpc".
    assert (Hsum5 : add_vec (A8 !!! Regidx Ra5) (A8 !!! Regidx Ra1)
                    = add_vec oldsz (mword_of_int 4095))
      by (rewrite HA8a5 HA8a1; apply udl_addv_comm).
    iEval (rewrite Hsum5) in "Hcg".
    set (A9 := <[Regidx Ra5 := regval_into_reg (add_vec oldsz (mword_of_int 4095))]> A8).
    change (<[Regidx Ra5 := regval_into_reg (add_vec oldsz (mword_of_int 4095))]> A8) with A9.
    assert (Hpc20 : add_vec_int (mword_of_int (UD + 0x1e) : mword 64) 2
                    = mword_of_int (UD + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc20) in "Hpc".
    assert (HA9a5 : A9 !!! Regidx Ra5 = add_vec oldsz (mword_of_int 4095))
      by (rewrite /A9 upd_eq; reflexivity).
    assert (HA9a3 : A9 !!! Regidx Ra3 = (mword_of_int (-4096) : mword 64))
      by (rewrite /A9 upd_ne; [exact HA8a3 | reg_neq]).
    (* +0x20 c.and a5,a5,a3 : a5 := PGROUNDUP(oldsz) *)
    iEval (rewrite udl_cr5 udl_cr7) in "Hi20".
    iApply (wp_cand_s_sconf γ Φ (mword_of_int (UD + 0x20)) Ra5 Ra3 A9 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi20 [-]").
    iIntros "Hcg Hpc".
    assert (Hpguo : and_vec (A9 !!! Regidx Ra5) (A9 !!! Regidx Ra3) = pgroundup oldsz)
      by (rewrite HA9a5 HA9a3; reflexivity).
    iEval (rewrite Hpguo) in "Hcg".
    set (A10 := <[Regidx Ra5 := regval_into_reg (pgroundup oldsz)]> A9).
    change (<[Regidx Ra5 := regval_into_reg (pgroundup oldsz)]> A9) with A10.
    assert (Hpc22 : add_vec_int (mword_of_int (UD + 0x20) : mword 64) 2
                    = mword_of_int (UD + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    (* the register facts at the second branch *)
    assert (HA10a5 : A10 !!! Regidx Ra5 = pgroundup oldsz)
      by (rewrite /A10 upd_eq; reflexivity).
    assert (HA10a4 : A10 !!! Regidx Ra4 = pgroundup newsz).
    { rewrite /A10 upd_ne; [| reg_neq]. rewrite /A9 upd_ne; [| reg_neq].
      rewrite /A8 upd_eq. reflexivity. }
    assert (HA10sp : A10 !!! Regidx csp_rs1 = spd).
    { rewrite /A10 upd_ne; [| reg_neq]. rewrite /A9 upd_ne; [| reg_neq].
      rewrite /A8 upd_ne; [| reg_neq]. rewrite /A7 upd_ne; [| reg_neq].
      rewrite /A6 upd_ne; [| reg_neq]. rewrite /A5 upd_ne; [| reg_neq].
      rewrite /A4 upd_ne; [| reg_neq]. exact HA3sp. }
    assert (HA10s1 : A10 !!! Regidx Rs1 = newsz).
    { rewrite /A10 upd_ne; [| reg_neq]. rewrite /A9 upd_ne; [| reg_neq].
      rewrite /A8 upd_ne; [| reg_neq]. rewrite /A7 upd_ne; [| reg_neq].
      rewrite /A6 upd_ne; [| reg_neq]. rewrite /A5 upd_ne; [| reg_neq].
      rewrite /A4 upd_ne; [| reg_neq]. exact HA3s1. }
    assert (HA10a0 : A10 !!! Regidx Ra0 = page_base (ud_root P)).
    { rewrite /A10 upd_ne; [| reg_neq]. rewrite /A9 upd_ne; [| reg_neq].
      rewrite /A8 upd_ne; [| reg_neq]. rewrite /A7 upd_ne; [| reg_neq].
      rewrite /A6 upd_ne; [| reg_neq]. rewrite /A5 upd_ne; [| reg_neq].
      rewrite /A4 upd_ne; [| reg_neq]. exact HA3a0. }
    assert (HA10tp : A10 !!! Regidx Rtp = cid_word).
    { rewrite /A10 upd_ne; [| reg_neq]. rewrite /A9 upd_ne; [| reg_neq].
      rewrite /A8 upd_ne; [| reg_neq]. rewrite /A7 upd_ne; [| reg_neq].
      rewrite /A6 upd_ne; [| reg_neq]. rewrite /A5 upd_ne; [| reg_neq].
      rewrite /A4 upd_ne; [| reg_neq]. exact HA3tp. }
    assert (HA10thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              A10 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9.
      rewrite /A10 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /A9 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /A8 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /A7 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /A6 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /A5 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /A4 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      apply HA3thr; assumption. }

    (* ================================================================= *)
    (* §F  +0x22 bltu a4,a5 : is there anything to unmap?                 *)
    (* ================================================================= *)
    destruct (zopz0zI_u (pgroundup newsz) (pgroundup oldsz)) eqn:Hcmp2.
    2:{ (* ---- FALLS: the two rounded sizes tie; the run is empty ---- *)
      assert (Hple : bv_unsigned (pgroundup oldsz) <= bv_unsigned (pgroundup newsz)).
      { unfold zopz0zI_u in Hcmp2.
        rewrite -!uint_unsigned. exact (proj1 (Z.ltb_ge _ _) Hcmp2). }
      assert (Hnp0 : uvmd_np oldsz newsz = 0%nat)
        by (rewrite Hnpdef; apply udl_z_np0; exact Hple).
      iAssert (proc_pt (uptd_del_run P (svpn_of (pgroundup newsz)) (uvmd_np oldsz newsz)))
        with "[Hpt]" as "Hpt".
      { iEval (rewrite (proc_pt_data_irrel P
                 (uptd_del_run P (svpn_of (pgroundup newsz)) (uvmd_np oldsz newsz))
                 ltac:(rewrite Hnp0; reflexivity)
                 ltac:(rewrite Hnp0; reflexivity)
                 ltac:(rewrite Hnp0; reflexivity))) in "Hpt".
        iExact "Hpt". }
      assert (Hcmp2' : zopz0zI_u (A10 !!! Regidx Ra4) (A10 !!! Regidx Ra5) = false)
        by (rewrite HA10a4 HA10a5; exact Hcmp2).
      iApply (wp_bltu_fall_s_sconf γ Φ (mword_of_int (UD + 0x22))
                (mword_of_int 16 : mword 13) Ra5 Ra4 A10 (K - 4)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hcmp2'
                with "Hcg Hpc Hi22 [-]").
      iIntros "Hcg Hpc".
      assert (Hpc26 : add_vec_int (mword_of_int (UD + 0x22) : mword 64) 4
                      = mword_of_int (UD + 0x26))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc26) in "Hpc".
      iApply ("Hepi" $! A10 newsz with "[%] [%] Hcg Hcpu Hpc Hpt").
      { split_and!; [exact HA10sp | exact HA10s1 | exact HA10thr]. }
      { right. split; [exact Hlt | reflexivity]. } }

    (* ---- TAKEN: PGROUNDUP(newsz) < PGROUNDUP(oldsz) ---- *)
    assert (Hpltz : bv_unsigned (pgroundup newsz) < bv_unsigned (pgroundup oldsz)).
    { unfold zopz0zI_u in Hcmp2.
      rewrite -!uint_unsigned. exact (proj1 (Z.ltb_lt _ _) Hcmp2). }
    assert (Hcmp2' : zopz0zI_u (A10 !!! Regidx Ra4) (A10 !!! Regidx Ra5) = true)
      by (rewrite HA10a4 HA10a5; exact Hcmp2).
    iApply (wp_bltu_taken_s_sconf γ Φ (mword_of_int (UD + 0x22))
              (mword_of_int 16 : mword 13) Ra5 Ra4 A10 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              Hcmp2' ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi22 [-]").
    iNext. iIntros "Hcg Hpc".
    assert (Htgt32 : add_vec (mword_of_int (UD + 0x22) : mword 64)
                       (sign_extend' 64 (mword_of_int 16 : mword 13))
                     = mword_of_int (UD + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt32) in "Hpc".

    (* ================================================================= *)
    (* §G  The run length, as a plain [Z].                                *)
    (* ================================================================= *)
    destruct (udl_z_np_exact (bv_unsigned (pgroundup oldsz)) (bv_unsigned (pgroundup newsz))
                ltac:(lia) Hpumod Hpnmod) as [Hq0 Hqmul].
    assert (Hqz : Z.of_nat (uvmd_np oldsz newsz)
                  = (bv_unsigned (pgroundup oldsz) - bv_unsigned (pgroundup newsz)) / 4096)
      by (rewrite Hnpdef; apply Z2Nat.id; exact Hq0).
    assert (Hqlt : (bv_unsigned (pgroundup oldsz) - bv_unsigned (pgroundup newsz)) / 4096
                   < 2147483648)
      by (apply udl_z_np_lt31; [exact Hpn0 | exact Hpubnd]).

    (* ================================================================= *)
    (* §H  +0x32..+0x3e: npages, do_free = 1, uvmunmap().                 *)
    (* ================================================================= *)
    iPoseProof (udi_32 with "Htext") as "Hi32".
    iPoseProof (udi_34 with "Htext") as "Hi34".
    iPoseProof (udi_36 with "Htext") as "Hi36".
    iPoseProof (udi_38 with "Htext") as "Hi38".
    iPoseProof (udi_3c with "Htext") as "Hi3c".
    iPoseProof (udi_3e with "Htext") as "Hi3e".
    iPoseProof (udi_42 with "Htext") as "Hi42".
    (* +0x32 c.sub a5,a5,a4 *)
    iEval (rewrite udl_cr6 udl_cr7) in "Hi32".
    assert (Hsubv : sub_vec (A10 !!! Regidx Ra5) (A10 !!! Regidx Ra4)
                    = (mword_of_int (bv_unsigned (pgroundup oldsz)
                                     - bv_unsigned (pgroundup newsz)) : mword 64)).
    { rewrite HA10a5 HA10a4. apply bv_eq.
      rewrite sub_vec64_unsigned. symmetry. apply moi64_unsigned. }
    iApply (wp_csub_s_sconf γ Φ (mword_of_int (UD + 0x32)) Ra5 Ra5 Ra4
              (mword_of_int (bv_unsigned (pgroundup oldsz)
                             - bv_unsigned (pgroundup newsz)) : mword 64)
              A10 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hsubv
              with "Hcg Hpc Hi32 [-]").
    iIntros "Hcg Hpc".
    set (B1 := <[Regidx Ra5 := regval_into_reg
        (mword_of_int (bv_unsigned (pgroundup oldsz)
                       - bv_unsigned (pgroundup newsz)) : mword 64)]> A10).
    change (<[Regidx Ra5 := regval_into_reg
        (mword_of_int (bv_unsigned (pgroundup oldsz)
                       - bv_unsigned (pgroundup newsz)) : mword 64)]> A10) with B1.
    assert (Hpc34 : add_vec_int (mword_of_int (UD + 0x32) : mword 64) 2
                    = mword_of_int (UD + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc34) in "Hpc".
    assert (HB1a5 : B1 !!! Regidx Ra5
                    = (mword_of_int (bv_unsigned (pgroundup oldsz)
                                     - bv_unsigned (pgroundup newsz)) : mword 64))
      by (rewrite /B1 upd_eq; reflexivity).
    (* +0x34 c.srli a5,a5,0xc : a5 := npages *)
    iEval (rewrite udl_cr7) in "Hi34".
    iApply (wp_csrli_s_sconf γ Φ (mword_of_int (UD + 0x34)) (Cregidx (mword_of_int 7)) Ra5
              (mword_of_int 12 : mword 6) B1 (K - 4)%nat
              udl_cr7 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi34 [-]").
    iIntros "Hcg Hpc".
    assert (Hnpv : shift_bits_right (B1 !!! Regidx Ra5)
                     (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
                   = (mword_of_int (Z.of_nat (uvmd_np oldsz newsz)) : mword 64)).
    { rewrite HB1a5 udl_srli12 Hqz.
      assert (Hbd : bv_unsigned (mword_of_int (bv_unsigned (pgroundup oldsz)
                                  - bv_unsigned (pgroundup newsz)) : mword 64)
                    = bv_unsigned (pgroundup oldsz) - bv_unsigned (pgroundup newsz)).
      { rewrite moi64_unsigned. apply bvw64_small.
        pose proof (bv_unsigned_in_range _ (pgroundup oldsz)) as Hro.
        assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616)
          by (vm_compute; reflexivity).
        rewrite Hm in Hro. change (2 ^ 64) with 18446744073709551616. lia. }
      rewrite Hbd. reflexivity. }
    iEval (rewrite Hnpv) in "Hcg".
    set (B2 := <[Regidx Ra5 := regval_into_reg
        (mword_of_int (Z.of_nat (uvmd_np oldsz newsz)) : mword 64)]> B1).
    change (<[Regidx Ra5 := regval_into_reg
        (mword_of_int (Z.of_nat (uvmd_np oldsz newsz)) : mword 64)]> B1) with B2.
    assert (Hpc36 : add_vec_int (mword_of_int (UD + 0x34) : mword 64) 2
                    = mword_of_int (UD + 0x36))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc36) in "Hpc".
    (* +0x36 c.li a3,1 : do_free = 1 *)
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (UD + 0x36)) Ra3 (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) B2 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi36 [-]").
    iIntros "Hcg Hpc".
    set (B3 := <[Regidx Ra3 := regval_into_reg (mword_of_int 1 : mword 64)]> B2).
    change (<[Regidx Ra3 := regval_into_reg (mword_of_int 1 : mword 64)]> B2) with B3.
    assert (Hpc38 : add_vec_int (mword_of_int (UD + 0x36) : mword 64) 2
                    = mword_of_int (UD + 0x38))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc38) in "Hpc".
    assert (HB3a5 : B3 !!! Regidx Ra5
                    = (mword_of_int (Z.of_nat (uvmd_np oldsz newsz)) : mword 64)).
    { rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_eq. reflexivity. }
    (* +0x38 sext.w a2,a5 : the count is small, so this is the identity *)
    iApply (wp_addiw_s_sconf γ Φ (mword_of_int (UD + 0x38)) Ra2 Ra5
              (mword_of_int 0 : mword 12) B3 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi38 [-]").
    iIntros "Hcg Hpc".
    assert (Hsext : sign_extend' 64 (subrange_vec_dec
                      (add_vec (B3 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0)
                    = (mword_of_int (Z.of_nat (uvmd_np oldsz newsz)) : mword 64)).
    { rewrite HB3a5. apply sextw_moi; [apply Nat2Z.is_nonneg |].
      rewrite Hqz. exact Hqlt. }
    iEval (rewrite Hsext) in "Hcg".
    set (B4 := <[Regidx Ra2 := regval_into_reg
        (mword_of_int (Z.of_nat (uvmd_np oldsz newsz)) : mword 64)]> B3).
    change (<[Regidx Ra2 := regval_into_reg
        (mword_of_int (Z.of_nat (uvmd_np oldsz newsz)) : mword 64)]> B3) with B4.
    assert (Hpc3c : add_vec_int (mword_of_int (UD + 0x38) : mword 64) 4
                    = mword_of_int (UD + 0x3c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc3c) in "Hpc".
    assert (HB4a4 : B4 !!! Regidx Ra4 = pgroundup newsz).
    { rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
      rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact HA10a4. }
    (* +0x3c c.mv a1,a4 : a1 := PGROUNDUP(newsz) *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (UD + 0x3c)) Ra1 Ra4 B4 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi3c [-]").
    iIntros "Hcg Hpc".
    iEval (rewrite HB4a4 add_vec_zero_l) in "Hcg".
    set (B5 := <[Regidx Ra1 := regval_into_reg (pgroundup newsz)]> B4).
    change (<[Regidx Ra1 := regval_into_reg (pgroundup newsz)]> B4) with B5.
    assert (Hpc3e : add_vec_int (mword_of_int (UD + 0x3c) : mword 64) 2
                    = mword_of_int (UD + 0x3e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc3e) in "Hpc".
    (* +0x3e jal ra,uvmunmap *)
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (UD + 0x3e)) Rra
              (mword_of_int 2096952 : mword 21) B5 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi3e [-]").
    iIntros "Hcg Hpc".
    set (B6 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (UD + 0x3e) : mword 64) 4)]> B5).
    change (<[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (UD + 0x3e) : mword 64) 4)]> B5) with B6.
    assert (Hjmp : add_vec (mword_of_int (UD + 0x3e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096952 : mword 21))
                   = mword_of_int KernelSyms.uvmunmap)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    (* the register facts at uvmunmap's entry *)
    assert (HB6ra : B6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (UD + 0x3e) : mword 64) 4)
      by (rewrite /B6 upd_eq; reflexivity).
    assert (HB6a1 : B6 !!! Regidx Ra1 = pgroundup newsz).
    { rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_eq. reflexivity. }
    assert (HB6a2 : B6 !!! Regidx Ra2
                    = (mword_of_int (Z.of_nat (uvmd_np oldsz newsz)) : mword 64)).
    { rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_ne; [| reg_neq].
      rewrite /B4 upd_eq. reflexivity. }
    assert (HB6a3 : B6 !!! Regidx Ra3 = (mword_of_int 1 : mword 64)).
    { rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_ne; [| reg_neq].
      rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_eq. reflexivity. }
    assert (HB6a0 : B6 !!! Regidx Ra0 = page_base (ud_root P)).
    { rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_ne; [| reg_neq].
      rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
      rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact HA10a0. }
    assert (HB6tp : B6 !!! Regidx Rtp = cid_word).
    { rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_ne; [| reg_neq].
      rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
      rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact HA10tp. }
    assert (HB6sp : B6 !!! Regidx csp_rs1 = spd).
    { rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_ne; [| reg_neq].
      rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
      rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact HA10sp. }
    assert (HB6s1 : B6 !!! Regidx Rs1 = newsz).
    { rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_ne; [| reg_neq].
      rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
      rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact HA10s1. }
    assert (HB6thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              B6 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9.
      rewrite /B6 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /B5 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /B4 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /B3 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /B2 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /B1 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      apply HA10thr; assumption. }
    (* the two pure premises uvmunmap asks about the run *)
    assert (Halign : subrange_vec_dec (B6 !!! Regidx Ra1) 11 0 = (zeros' 12 : mword 12))
      by (rewrite HB6a1; apply pgroundup_low12).
    assert (Hdofree : B6 !!! Regidx Ra3 <> (mword_of_int 0 : mword 64)).
    { rewrite HB6a3. intro He.
      assert (Hc : bv_unsigned (mword_of_int 1 : mword 64)
                   = bv_unsigned (mword_of_int 0 : mword 64)) by (rewrite He; reflexivity).
      vm_compute in Hc. discriminate. }
    assert (Hrange : (uint (B6 !!! Regidx Ra1)
                      + Z.of_nat (uvmd_np oldsz newsz) * 4096 <= uvm_maxsz)%Z).
    { rewrite HB6a1 uint_unsigned Hmax Hqz. lia. }
    (* ---- uvmunmap() ---- *)
    iApply (Uvmunmap.wp_uvmunmap_sconf γ γa Φ B6 P (uvmd_np oldsz newsz) (K - 4)%nat eb p C
              ltac:(lia) HB6tp HB6a0 Halign HB6a2 Hdofree Hrange
              with "Hcg Hcpu Htext Hpc Hpt Henv [-]").
    iIntros (mr) "Hcg Hcpu Hpc %Hcs Hpt".
    iEval (rewrite HB6a1) in "Hpt".
    assert (Hret42 : ret_pc (B6 !!! Regidx Rra) = mword_of_int (UD + 0x42)).
    { rewrite HB6ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret42) in "Hpc".
    (* +0x42 c.j -0x1c : back to the epilogue *)
    assert (Hmrsp : mr !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HB6sp. }
    assert (Hmrs1 : mr !!! Regidx Rs1 = newsz).
    { rewrite (callee_saved_lookup Hcs Rs1 ltac:(vm_compute; reflexivity)).
      exact HB6s1. }
    assert (Hmrthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              mr !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9.
      rewrite (callee_saved_lookup Hcs c Hc). apply HB6thr; assumption. }
    iApply (wp_cj_s_sconf γ Φ (mword_of_int (UD + 0x42))
              (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0")))
              mr (K - 4)%nat ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi42 [-]").
    iNext. iIntros "Hcg Hpc".
    assert (Htgt26 : add_vec (mword_of_int (UD + 0x42) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 2034 : mword 11) ('b"0"))))
                     = mword_of_int (UD + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt26) in "Hpc".
    iApply ("Hepi" $! mr newsz with "[%] [%] Hcg Hcpu Hpc Hpt").
    { split_and!; [exact Hmrsp | exact Hmrs1 | exact Hmrthr]. }
    { right. split; [exact Hlt | reflexivity]. }
  Qed.

End ProofUvmdealloc.

End UvmdeallocProof.
