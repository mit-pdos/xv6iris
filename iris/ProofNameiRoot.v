(* ProofNameiRoot.v -- namei's ROOT CORNER, a thin forward of namex's.

     struct inode *namei(char *path) { char name[DIRSIZ]; return namex(path, 0, name); }

   Eleven instructions, the same eleven the general proof runs
   ([ProofNamei.v]) -- and one step FEWER of ghost work, because on this path
   no memmove executes and the frame's two low slots are therefore not the
   [name[14]] local: they stay two ordinary stack slots from the push to the
   pop.  [addi a2,s0,-32] still computes their address and still hands it to
   namex, and [SpecNamex.wp_namex_root_body] simply does not mention it.

   Everything else is [ProofNamei.v]'s skeleton with namex's ROOT contract in
   place of its general one; see [SpecNamex.wp_namex_root_body]'s header for
   why there are two. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import StackOwn StackBytes.
Require Import CalleeSaved.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfVc.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import ByteBuf.
Require Import DirentEnc.
Require Import PathElems.
Require Import FsBlocks LogInv.
Require Import DiskPtsto BioInv.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import PanicStub.
Require Import CodeNamei.
Require Import SpecNamex.
Require Import SpecNamei.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* the two registers this frame saves *)
Definition nmr_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> (mword_of_int 8 : mword 5) ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Definition nmr_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4.

Lemma nmr_frm (X : mword 64) (u : mword 6) (k : nat) :
  (mword_of_int (wrap64 (uint (mword_of_int (- (8 * Z.of_nat 4)) : mword 64)
                         + uint (zero_extend' 64 (concat_vec u ('b"000")) : mword 64)))
   : mword 64)
  = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 4) (zero_extend' 64 (concat_vec u ('b"000"))) = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. exact H.
Qed.

Lemma nmr_frm1 (X : mword 64) :
  add_vec (pa_stk X 4) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof. apply nmr_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma nmr_frm2 (X : mword 64) :
  add_vec (pa_stk X 4) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof. apply nmr_frm. apply bv_eq; vm_compute; reflexivity. Qed.

(* K_namei_root's single premise, in the three forms the call and the pop want *)
Lemma nmr_kb (K : nat) : (K_namei_root <= K)%nat ->
  (K_namex_root <= K - 4)%nat /\ (4 <= K)%nat /\ ((K - 4) + 4 = K)%nat.
Proof. unfold K_namei_root, K_namex_root. intro H. split_and!; lia. Qed.

(* [c.li a1,0] really writes the zero register's value *)
Lemma nmr_a1_zero : (mword_of_int 0 : mword 64) = (zero_reg : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Module NameiRootProof (NX : NAMEX_ROOT) : NAMEI_ROOT.

Notation NM := KernelSyms.namei (only parsing).

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac namidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].
Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Section ProofNameiRoot.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, ICFG : icfg, !icacheG Σ, !logG Σ,
            !irefslotG Σ, !pavG Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).

  Lemma wp_namei_root
      (gtl : gname) (cn : ic_names) (gfs : fs_names) (gi : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) (dev : mword 32)
      (dqp : dfrac)
      (m : regfile) (n K : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string)
    : wp_namei_root_body gtl cn gfs gi cov logstart nib dev dqp
                         m n K eb p b lks.
  Proof.
    cbv beta delta [wp_namei_root_body].
    intros pcE pv ret_tgt HK Hn Hdev Hnib Hroot Hnib0 Hbelow.
    destruct (nmr_kb K HK) as (Knx & K4 & Kpop).
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hitb2 #Hitbl #Hesc Hisl Hp0 Hp1 Hcont".
    iPoseProof (nmi_00 with "Htext") as "Hi00".
    iPoseProof (nmi_02 with "Htext") as "Hi02".
    iPoseProof (nmi_04 with "Htext") as "Hi04".
    iPoseProof (nmi_06 with "Htext") as "Hi06".
    iPoseProof (nmi_08 with "Htext") as "Hi08".
    iPoseProof (nmi_0c with "Htext") as "Hi0c".
    iPoseProof (nmi_0e with "Htext") as "Hi0e".
    iPoseProof (nmi_12 with "Htext") as "Hi12".
    iPoseProof (nmi_14 with "Htext") as "Hi14".
    iPoseProof (nmi_16 with "Htext") as "Hi16".
    iPoseProof (nmi_18 with "Htext") as "Hi18".
    (* ===== +0x00 c.addi sp,sp,-32 : the four-slot frame ===== *)
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : (m !!! Regidx csp_rs1 : mword 64) = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4) by apply stk_push_32.
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 b
              K4 Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HR1sp : nmr_sp m R1) by (rewrite /nmr_sp /R1 upd_eq; exact Hpush).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (v1) "Hf1". iDestruct "S2" as (v2) "Hf2".
    iDestruct "S3" as (v3) "Hf3". iDestruct "S4" as (v4) "Hf4".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 1)
      by (rewrite HR1sp; apply nmr_frm1).
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 2)
      by (rewrite HR1sp; apply nmr_frm2).
    iEval (rewrite -Hb1) in "Hf1". iEval (rewrite -Hb2) in "Hf2".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2
                    = mword_of_int (NM + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* ===== +0x02 c.sdsp ra,24(sp) ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (NM + 0x02))
              (mword_of_int 3 : mword 6) Rra R1 (K - 4)%nat v1 b
              with "Hcg Hpc Hi02 Hf1").
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (NM + 0x02) : mword 64) 2
                    = mword_of_int (NM + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    (* ===== +0x04 c.sdsp s0,16(sp) ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (NM + 0x04))
              (mword_of_int 2 : mword 6) Rs0 R1 (K - 4)%nat v2 b
              with "Hcg Hpc Hi04 Hf2").
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (NM + 0x04) : mword 64) 2
                    = mword_of_int (NM + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    assert (HR1ra : (R1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s0 : (R1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    iEval (rewrite Hb1; rgne; rewrite HR1ra) in "Hf1".
    iEval (rewrite Hb2; rgne; rewrite HR1s0) in "Hf2".
    (* ===== +0x06 c.addi4spn s0,sp,32 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (NM + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) Rs0
              R1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (HR2s0 : (R2 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite /R2 upd_eq. rewrite HR1sp. apply stk_fp_32. }
    assert (HR2sp : nmr_sp m R2)
      by (rewrite /nmr_sp /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2a0 : (R2 !!! Regidx Ra0 : mword 64) = pv).
    { rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR2ra : (R2 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R2 upd_ne; [exact HR1ra | nz]).
    assert (HR2thr : nmr_thr m R2).
    { intros c Hcs N2 N8.
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (Hpp08 : add_vec_int (mword_of_int (NM + 0x06) : mword 64) 2
                    = mword_of_int (NM + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    (* ===== +0x08 addi a2,s0,-32 : &name[0] (unused on this path) ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (NM + 0x08)) Ra2 Rs0
              (mword_of_int 4064 : mword 12) R2 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi08").
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (R3 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (rget R2 Rs0)
                     (sign_extend' 64 (mword_of_int 4064 : mword 12)))]> R2).
    assert (HR3a0 : (R3 !!! Regidx Ra0 : mword 64) = pv)
      by (rewrite /R3 upd_ne; [exact HR2a0 | nz]).
    assert (HR3ra : (R3 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2ra | nz]).
    assert (HR3sp : nmr_sp m R3)
      by (rewrite /nmr_sp /R3 upd_ne; [exact HR2sp | nz]).
    assert (HR3thr : nmr_thr m R3).
    { intros c Hcs N2 N8. rewrite /R3 upd_ne; [| regne].
      exact (HR2thr c Hcs N2 N8). }
    assert (Hpp0c : add_vec_int (mword_of_int (NM + 0x08) : mword 64) 4
                    = mword_of_int (NM + 0x0c)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    (* ===== +0x0c c.li a1,0 : nameiparent = 0 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (NM + 0x0c)) Ra1
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              R3 (K - 4)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi0c").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (R4 := <[Regidx Ra1 := regval_into_reg (mword_of_int 0 : mword 64)]> R3).
    assert (HR4a1 : (R4 !!! Regidx Ra1 : mword 64) = (zero_reg : mword 64))
      by (rewrite /R4 upd_eq; exact nmr_a1_zero).
    assert (HR4a0 : (R4 !!! Regidx Ra0 : mword 64) = pv)
      by (rewrite /R4 upd_ne; [exact HR3a0 | nz]).
    assert (HR4ra : (R4 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3ra | nz]).
    assert (HR4sp : nmr_sp m R4)
      by (rewrite /nmr_sp /R4 upd_ne; [exact HR3sp | nz]).
    assert (HR4thr : nmr_thr m R4).
    { intros c Hcs N2 N8. rewrite /R4 upd_ne; [| regne].
      exact (HR3thr c Hcs N2 N8). }
    assert (Hpp0e : add_vec_int (mword_of_int (NM + 0x0c) : mword 64) 2
                    = mword_of_int (NM + 0x0e)) by pcw.
    iEval (rewrite Hpp0e) in "Hpc".
    (* ===== +0x0e jal ra,namex ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (NM + 0x0e)) Rra
              (mword_of_int 2096634 : mword 21) R4 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0e").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (R5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (NM + 0x0e) : mword 64) 4)]> R4).
    assert (Htgt : add_vec (mword_of_int (NM + 0x0e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096634 : mword 21))
                   = mword_of_int KernelSyms.namex) by pcw.
    iEval (rewrite Htgt) in "Hpc".
    assert (HR5a1 : (R5 !!! Regidx Ra1 : mword 64) = (zero_reg : mword 64))
      by (rewrite /R5 upd_ne; [exact HR4a1 | nz]).
    assert (HR5a0 : (R5 !!! Regidx Ra0 : mword 64) = pv)
      by (rewrite /R5 upd_ne; [exact HR4a0 | nz]).
    assert (HR5sp : nmr_sp m R5)
      by (rewrite /nmr_sp /R5 upd_ne; [exact HR4sp | nz]).
    assert (HR5ra : (R5 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (NM + 0x0e) : mword 64) 4)
      by (rewrite /R5; apply upd_eq).
    assert (HR5thr : nmr_thr m R5).
    { intros c Hcs N2 N8. rewrite /R5 upd_ne; [| regne].
      exact (HR4thr c Hcs N2 N8). }
    (* the two path bytes, re-addressed at namex's own a0 *)
    iEval (rewrite -HR5a0) in "Hp0".
    iEval (rewrite -HR5a0) in "Hp1".
    iDestruct (cpu_own_transport CID CID7 n eb p b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := b) (CIDa := CID) (CIDb := CID7)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (NX.wp_namex_root gtl cn gfs gi cov logstart nib dev dqp
              R5 n (K - 4)%nat eb p b lks
              Knx Hn Hdev Hnib Hroot Hnib0 HR5a1 Hbelow
              with "Hcg Hcnt Htext Hpc Hpanic Hitb2 Hitbl Hesc Hisl Hp0 Hp1").
    iIntros (CID8 Hq8 mf ipv) "%Hcsp Hcg Hcnt Hpc Hp0 Hp1 Hip".
    destruct Hcsp as (Hcs & Hfa0).
    iEval (rewrite HR5a0) in "Hp0".
    iEval (rewrite HR5a0) in "Hp1".
    assert (Hpc12 : ret_pc (R5 !!! Regidx Rra : mword 64)
                    = mword_of_int (NM + 0x12)) by (rewrite HR5ra; pcw).
    iEval (rewrite Hpc12) in "Hpc".
    pose proof Hcs as Hcs_cs.
    assert (Hmfsp : nmr_sp m mf).
    { rewrite /nmr_sp
        (callee_saved_lookup Hcs_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HR5sp. }
    assert (Hmfthr : nmr_thr m mf).
    { intros c Hcs2 N2 N8.
      rewrite (callee_saved_lookup Hcs_cs c Hcs2).
      exact (HR5thr c Hcs2 N2 N8). }
    (* ===== +0x12 .. +0x14 : the two restores ===== *)
    assert (Hc1 : add_vec (mf !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite Hmfsp; apply nmr_frm1).
    assert (Hc2 : add_vec (mf !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite Hmfsp; apply nmr_frm2).
    iApply (wp_cldsp_s_sconf (mword_of_int (NM + 0x12))
              (mword_of_int 3 : mword 6) Rra mf (K - 4)%nat
              (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi12 [Hf1]").
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID9 Hq9) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> mf).
    assert (HP1sp : nmr_sp m P1)
      by (rewrite /nmr_sp /P1 upd_ne; [exact Hmfsp | nz]).
    assert (HP1thr : nmr_thr m P1).
    { intros c Hcs2 N2 N8. rewrite /P1 upd_ne; [| regne].
      exact (Hmfthr c Hcs2 N2 N8). }
    assert (HP1ra : (P1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1a0 : (P1 !!! Regidx Ra0 : mword 64) = (mf !!! Regidx Ra0 : mword 64))
      by (rewrite /P1 upd_ne; [reflexivity | nz]).
    assert (Hpp14 : add_vec_int (mword_of_int (NM + 0x12) : mword 64) 2
                    = mword_of_int (NM + 0x14)) by pcw.
    iEval (rewrite Hpp14) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (NM + 0x14))
              (mword_of_int 2 : mword 6) Rs0 P1 (K - 4)%nat
              (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi14 [Hf2]").
    { iEval (rewrite HP1sp -Hmfsp Hc2). iExact "Hf2". }
    iIntros (CID10 Hq10) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -Hmfsp Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : nmr_sp m P2)
      by (rewrite /nmr_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : nmr_thr m P2).
    { intros c Hcs2 N2 N8. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hcs2 N2 N8). }
    assert (HP2ra : (P2 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1ra | nz]).
    assert (HP2a0 : (P2 !!! Regidx Ra0 : mword 64) = (mf !!! Regidx Ra0 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1a0 | nz]).
    assert (Hpp16 : add_vec_int (mword_of_int (NM + 0x14) : mword 64) 2
                    = mword_of_int (NM + 0x16)) by pcw.
    iEval (rewrite Hpp16) in "Hpc".
    (* ===== +0x16 c.addi16sp sp,32 : pop ===== *)
    assert (Hwv : add_vec (P2 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                  = sp0)
      by (rewrite HP2sp; apply stk_pop_32).
    assert (Hpopeq : (P2 !!! Regidx csp_rs1 : mword 64)
                     = pa_stk (add_vec (P2 !!! Regidx csp_rs1 : mword 64)
                         (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv HP2sp; reflexivity).
    iAssert (stack_own sp0 4) with "[Hf1 Hf2 Hf3 Hf4]" as "Hstk".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hf1"; [iExists _; iExact "Hf1" |].
      iSplitL "Hf2"; [iExists _; iExact "Hf2" |].
      iSplitL "Hf3"; [iExists _; iExact "Hf3" |].
      iSplitL "Hf4"; [iExists _; iExact "Hf4" |].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (NM + 0x16))
              (mword_of_int 2 : mword 6) P2 (K - 4)%nat 4 b Hpopeq
              with "Hcg Hpc Hi16 Hstk").
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (P3 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P2 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P2).
    iEval (rewrite Kpop) in "Hcg".
    assert (Hpp18 : add_vec_int (mword_of_int (NM + 0x16) : mword 64) 2
                    = mword_of_int (NM + 0x18)) by pcw.
    iEval (rewrite Hpp18) in "Hpc".
    (* ===== +0x18 c.ret ===== *)
    assert (HP3ra : (P3 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2ra | nz]).
    iApply (wp_cret_s_sconf (mword_of_int (NM + 0x18)) Rra P3 K b
              ltac:(nz) with "Hcg Hpc Hi18").
    iIntros (CID12 Hq12) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P3 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP3ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CONTRACT ===== *)
    assert (HP3a0 : (P3 !!! Regidx Ra0 : mword 64) = ipv)
      by (rewrite /P3 upd_ne; [rewrite HP2a0; exact Hfa0 | nz]).
    assert (Csp : (P3 !!! Regidx csp_rs1 : mword 64)
                  = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P3 upd_eq; exact Hwv).
    assert (Cs0 : (P3 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P3 upd_ne; [| nz]. rewrite /P2 upd_eq. reflexivity. }
    assert (Hfin : nmr_thr m P3).
    { intros c Hcs2 N2 N8. rewrite /P3 upd_ne; [| regne].
      exact (HP2thr c Hcs2 N2 N8). }
    assert (Cs1 : (P3 !!! Regidx (mword_of_int 9 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 9 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs2 : (P3 !!! Regidx (mword_of_int 18 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 18 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs3 : (P3 !!! Regidx (mword_of_int 19 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 19 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs4 : (P3 !!! Regidx (mword_of_int 20 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 20 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs5 : (P3 !!! Regidx (mword_of_int 21 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 21 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs6 : (P3 !!! Regidx (mword_of_int 22 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 22 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs7 : (P3 !!! Regidx (mword_of_int 23 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs8 : (P3 !!! Regidx (mword_of_int 24 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs9 : (P3 !!! Regidx (mword_of_int 25 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs10 : (P3 !!! Regidx (mword_of_int 26 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs11 : (P3 !!! Regidx (mword_of_int 27 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    iDestruct (cpu_own_transport CID8 CID12 n eb p b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CID12 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! P3 ipv with "[%] Hcg Hcnt Hpc Hp0 Hp1 Hip").
    split; [| exact HP3a0].
    unfold callee_saved. split_and!; assumption.
  Qed.

End ProofNameiRoot.

End NameiRootProof.
