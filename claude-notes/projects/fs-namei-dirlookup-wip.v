
(* ===================================================================== *)
(*  6.  THE PROOF                                                         *)
(* ===================================================================== *)

Module DirlookupProof (RD : READI) (NC : NAMECMP) (IG : IGET) : DIRLOOKUP.

Notation DL := KernelSyms.dirlookup (only parsing).
Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).
Notation Ra3 := (mword_of_int 13 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Rs3 := (mword_of_int 19 : mword 5).
Notation Rs4 := (mword_of_int 20 : mword 5).
Notation Rs5 := (mword_of_int 21 : mword 5).
Notation Rs6 := (mword_of_int 22 : mword 5).
Notation Rs7 := (mword_of_int 23 : mword 5).

Section ProofDirlookupMain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  Lemma wp_dirlookup_sconf
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) (dev : mword 32)
      (ip : mword 64)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn : dinode)
      (fn : nat -> bv 8)
      (hasp : bool) (pofv : mword 32)
      (pidv : mword 32) (dq dqd dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool)
    : wp_dirlookup_sconf_body gs j gl gu gd gk pd pav pu bn gfs gi cn gtl
                              ga gf cov logstart nib dev ip bm data dn
                              fn hasp pofv pidv dq dqd dqn m K eb C b.
  Proof.
    cbv beta delta [wp_dirlookup_sconf_body].
    intros pcE pj nb pf ret_tgt nrec s HK Htype Hgran Hlg Hbmwf Hbmcov Hszb
           Hinums Hj Hgs Ha0 Hposs Heb.
    pose proof HK as HK'. unfold K_dirlookup in HK'.
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hbio #Hkenv Hidev Hmeta Hmap Hblocks
              Hnm Hpoff Hppid #Hprocs #Hdev #Hgeom #Hdlk Hbslot #Hitb2 #Hitbl
              #Hesc Hislot Hcont".
    iDestruct "Hmeta" as "(Hity & Himaj & Himin & Hinl & Hisz)".
    iEval (rewrite /i_type) in "Hity".
    iEval (rewrite /i_size) in "Hisz".
    iPoseProof (dli_00 with "Htext") as "Hi00".
    iPoseProof (dli_02 with "Htext") as "Hi02".
    iPoseProof (dli_04 with "Htext") as "Hi04".
    iPoseProof (dli_06 with "Htext") as "Hi06".
    iPoseProof (dli_08 with "Htext") as "Hi08".
    iPoseProof (dli_0a with "Htext") as "Hi0a".
    iPoseProof (dli_0c with "Htext") as "Hi0c".
    iPoseProof (dli_0e with "Htext") as "Hi0e".
    iPoseProof (dli_10 with "Htext") as "Hi10".
    iPoseProof (dli_12 with "Htext") as "Hi12".
    iPoseProof (dli_14 with "Htext") as "Hi14".
    iPoseProof (dli_16 with "Htext") as "Hi16".
    iPoseProof (dli_1a with "Htext") as "Hi1a".
    iPoseProof (dli_1c with "Htext") as "Hi1c".
    (* ===== +0x00 c.addi16sp sp,-96 : the 12-slot frame ===== *)
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 12) by apply dlk_push.
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 58 : mword 6) m K 12 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))))]> m).
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /R1 upd_eq; exact Hpush).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as
      "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & _)".
    iDestruct "S1" as (u1) "Hb1". iDestruct "S2" as (u2) "Hb2".
    iDestruct "S3" as (u3) "Hb3". iDestruct "S4" as (u4) "Hb4".
    iDestruct "S5" as (u5) "Hb5". iDestruct "S6" as (u6) "Hb6".
    iDestruct "S7" as (u7) "Hb7". iDestruct "S8" as (u8) "Hb8".
    iDestruct "S9" as (u9) "Hb9".
    iDestruct "S11" as (u11) "Hb11". iDestruct "S12" as (u12) "Hb12".
    assert (Hf1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HR1sp; apply dlk_frm1).
    assert (Hf2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HR1sp; apply dlk_frm2).
    assert (Hf3 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HR1sp; apply dlk_frm3).
    assert (Hf4 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HR1sp; apply dlk_frm4).
    assert (Hf5 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (rewrite HR1sp; apply dlk_frm5).
    assert (Hf6 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 6) by (rewrite HR1sp; apply dlk_frm6).
    assert (Hf7 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (rewrite HR1sp; apply dlk_frm7).
    assert (Hf8 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (rewrite HR1sp; apply dlk_frm8).
    assert (Hf9 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 9) by (rewrite HR1sp; apply dlk_frm9).
    iEval (rewrite -Hf1) in "Hb1". iEval (rewrite -Hf2) in "Hb2".
    iEval (rewrite -Hf3) in "Hb3". iEval (rewrite -Hf4) in "Hb4".
    iEval (rewrite -Hf5) in "Hb5". iEval (rewrite -Hf6) in "Hb6".
    iEval (rewrite -Hf7) in "Hb7". iEval (rewrite -Hf8) in "Hb8".
    iEval (rewrite -Hf9) in "Hb9".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (DL + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    assert (HR1o : forall c : mword 5, c <> csp_rs1 ->
                     R1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc. rewrite /R1 upd_ne;
        [reflexivity
        | intro Hq; apply Hc;
          first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ]]. }
    (* ===== +0x02 .. +0x12 : the nine saves ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (DL + 0x02)) (mword_of_int 11 : mword 6)
              Rra R1 (K - 12)%nat u1 b with "Hcg Hpc Hi02 Hb1").
    iIntros (CID2 Hq2) "Hcg Hpc Hb1".
    iEval (rgne; rewrite (HR1o Rra ltac:(nz)) Hf1) in "Hb1".
    assert (Hpp04 : add_vec_int (mword_of_int (DL + 0x02) : mword 64) 2
                    = mword_of_int (DL + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DL + 0x04)) (mword_of_int 10 : mword 6)
              Rs0 R1 (K - 12)%nat u2 b with "Hcg Hpc Hi04 Hb2").
    iIntros (CID3 Hq3) "Hcg Hpc Hb2".
    iEval (rgne; rewrite (HR1o Rs0 ltac:(nz)) Hf2) in "Hb2".
    assert (Hpp06 : add_vec_int (mword_of_int (DL + 0x04) : mword 64) 2
                    = mword_of_int (DL + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DL + 0x06)) (mword_of_int 9 : mword 6)
              Rs1 R1 (K - 12)%nat u3 b with "Hcg Hpc Hi06 Hb3").
    iIntros (CID4 Hq4) "Hcg Hpc Hb3".
    iEval (rgne; rewrite (HR1o Rs1 ltac:(nz)) Hf3) in "Hb3".
    assert (Hpp08 : add_vec_int (mword_of_int (DL + 0x06) : mword 64) 2
                    = mword_of_int (DL + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DL + 0x08)) (mword_of_int 8 : mword 6)
              Rs2 R1 (K - 12)%nat u4 b with "Hcg Hpc Hi08 Hb4").
    iIntros (CID5 Hq5) "Hcg Hpc Hb4".
    iEval (rgne; rewrite (HR1o Rs2 ltac:(nz)) Hf4) in "Hb4".
    assert (Hpp0a : add_vec_int (mword_of_int (DL + 0x08) : mword 64) 2
                    = mword_of_int (DL + 0x0a)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DL + 0x0a)) (mword_of_int 7 : mword 6)
              Rs3 R1 (K - 12)%nat u5 b with "Hcg Hpc Hi0a Hb5").
    iIntros (CID6 Hq6) "Hcg Hpc Hb5".
    iEval (rgne; rewrite (HR1o Rs3 ltac:(nz)) Hf5) in "Hb5".
    assert (Hpp0c : add_vec_int (mword_of_int (DL + 0x0a) : mword 64) 2
                    = mword_of_int (DL + 0x0c)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DL + 0x0c)) (mword_of_int 6 : mword 6)
              Rs4 R1 (K - 12)%nat u6 b with "Hcg Hpc Hi0c Hb6").
    iIntros (CID7 Hq7) "Hcg Hpc Hb6".
    iEval (rgne; rewrite (HR1o Rs4 ltac:(nz)) Hf6) in "Hb6".
    assert (Hpp0e : add_vec_int (mword_of_int (DL + 0x0c) : mword 64) 2
                    = mword_of_int (DL + 0x0e)) by pcw.
    iEval (rewrite Hpp0e) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DL + 0x0e)) (mword_of_int 5 : mword 6)
              Rs5 R1 (K - 12)%nat u7 b with "Hcg Hpc Hi0e Hb7").
    iIntros (CID8 Hq8) "Hcg Hpc Hb7".
    iEval (rgne; rewrite (HR1o Rs5 ltac:(nz)) Hf7) in "Hb7".
    assert (Hpp10 : add_vec_int (mword_of_int (DL + 0x0e) : mword 64) 2
                    = mword_of_int (DL + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DL + 0x10)) (mword_of_int 4 : mword 6)
              Rs6 R1 (K - 12)%nat u8 b with "Hcg Hpc Hi10 Hb8").
    iIntros (CID9 Hq9) "Hcg Hpc Hb8".
    iEval (rgne; rewrite (HR1o Rs6 ltac:(nz)) Hf8) in "Hb8".
    assert (Hpp12 : add_vec_int (mword_of_int (DL + 0x10) : mword 64) 2
                    = mword_of_int (DL + 0x12)) by pcw.
    iEval (rewrite Hpp12) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DL + 0x12)) (mword_of_int 3 : mword 6)
              Rs7 R1 (K - 12)%nat u9 b with "Hcg Hpc Hi12 Hb9").
    iIntros (CID10 Hq10) "Hcg Hpc Hb9".
    iEval (rgne; rewrite (HR1o Rs7 ltac:(nz)) Hf9) in "Hb9".
    assert (Hpp14 : add_vec_int (mword_of_int (DL + 0x12) : mword 64) 2
                    = mword_of_int (DL + 0x14)) by pcw.
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 c.addi4spn s0,sp,96 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (DL + 0x14))
              (Cregidx (mword_of_int 0)) (mword_of_int 24 : mword 8) Rs0
              R1 (K - 12)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi14").
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))))]> R1).
    assert (HR2s0 : R2 !!! Regidx Rs0 = sp0).
    { rewrite /R2 upd_eq. rewrite HR1sp. apply dlk_fp. }
    assert (HR2a0 : R2 !!! Regidx Ra0 = ip).
    { rewrite /R2 upd_ne; [| nz]. rewrite (HR1o Ra0 ltac:(nz)). exact Ha0. }
    assert (Hpp16 : add_vec_int (mword_of_int (DL + 0x14) : mword 64) 2
                    = mword_of_int (DL + 0x16)) by pcw.
    iEval (rewrite Hpp16) in "Hpc".
    (* ===== +0x16 lh a4,68(a0) : ip->type ===== *)
    iApply (wp_lh_s_sconf (mword_of_int (DL + 0x16)) Ra4 Ra0
              (mword_of_int 68 : mword 12) R2 (K - 12)%nat (di_type dn : mword 16) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi16 [Hity]").
    { iEval (rgne; rewrite HR2a0). iExact "Hity". }
    iIntros (CID12 Hq12) "Hcg Hpc Hity".
    iEval (rgne; rewrite HR2a0) in "Hity".
    set (R3 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (di_type dn : mword 16) : mword 64)]> R2).
    assert (HR3a4 : R3 !!! Regidx Ra4
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /R3; apply upd_eq).
    assert (Hpp1a : add_vec_int (mword_of_int (DL + 0x16) : mword 64) 4
                    = mword_of_int (DL + 0x1a)) by pcw.
    iEval (rewrite Hpp1a) in "Hpc".
    (* ===== +0x1a c.li a5,1 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (DL + 0x1a)) Ra5 (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) R3 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi1a").
    iIntros (CID13 Hq13) "Hcg Hpc".
    set (R4 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> R3).
    assert (HR4a5 : R4 !!! Regidx Ra5 = (mword_of_int 1 : mword 64))
      by (rewrite /R4; apply upd_eq).
    assert (HR4a4 : R4 !!! Regidx Ra4 = (mword_of_int 1 : mword 64)).
    { rewrite /R4 upd_ne; [| nz]. rewrite HR3a4 Htype. unfold T_DIR. pcw. }
    assert (Hpp1c : add_vec_int (mword_of_int (DL + 0x1a) : mword 64) 2
                    = mword_of_int (DL + 0x1c)) by pcw.
    iEval (rewrite Hpp1c) in "Hpc".
    (* ===== +0x1c bne a4,a5 : the panic is refuted by the premise ===== *)
    iApply (wp_bne_fall_s_sconf (mword_of_int (DL + 0x1c))
              (mword_of_int 30 : mword 13) Ra5 Ra4 R4 (K - 12)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HR4a4 HR4a5; apply dlk_neq_refl)
              with "Hcg Hpc Hi1c").
    iIntros (CID14 Hq14) "Hcg Hpc".
    assert (Hpp20 : add_vec_int (mword_of_int (DL + 0x1c) : mword 64) 4
                    = mword_of_int (DL + 0x20)) by pcw.
    iEval (rewrite Hpp20) in "Hpc".
    iPoseProof (dli_20 with "Htext") as "Hi20".
    iPoseProof (dli_22 with "Htext") as "Hi22".
    iPoseProof (dli_24 with "Htext") as "Hi24".
    iPoseProof (dli_26 with "Htext") as "Hi26".
    iPoseProof (dli_28 with "Htext") as "Hi28".
    iPoseProof (dli_2a with "Htext") as "Hi2a".
    iPoseProof (dli_2e with "Htext") as "Hi2e".
    iPoseProof (dli_30 with "Htext") as "Hi30".
    iPoseProof (dli_34 with "Htext") as "Hi34".
    iPoseProof (dli_36 with "Htext") as "Hi36".
    assert (HR4a0 : R4 !!! Regidx Ra0 = ip).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz]. exact HR2a0. }
    assert (HR4a1 : R4 !!! Regidx Ra1 = nb).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite /R2 upd_ne; [| nz]. exact (HR1o Ra1 ltac:(nz)). }
    assert (HR4a2 : R4 !!! Regidx Ra2 = pf).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite /R2 upd_ne; [| nz]. exact (HR1o Ra2 ltac:(nz)). }
    assert (HR4s0 : R4 !!! Regidx Rs0 = sp0).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz]. exact HR2s0. }
    assert (HR4sp : R4 !!! Regidx csp_rs1 = pa_stk sp0 12).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite /R2 upd_ne; [| nz]. exact HR1sp. }
    assert (Hcsa4 : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
    assert (Hcsa5 : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
    assert (HR4o : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                     c <> Rs0 -> R4 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc N2 N8. rewrite /R4 upd_ne; [| dlk_rne2 Hcsa5 Hc].
      rewrite /R3 upd_ne; [| dlk_rne2 Hcsa4 Hc].
      rewrite /R2 upd_ne;
        [ exact (HR1o c N2)
        | intro Hq; apply N8;
          first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ]]. }
    (* ===== +0x20 c.mv s2,a0 : s2 := dp ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (DL + 0x20)) Rs2 Ra0 R4 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi20").
    iIntros (CID15 Hq15) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R5 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R4 !!! Regidx Ra0))]> R4).
    assert (HR5s2 : R5 !!! Regidx Rs2 = ip).
    { rewrite /R5 upd_eq. rewrite HR4a0. apply add_vec_zero_l. }
    assert (Hpp22 : add_vec_int (mword_of_int (DL + 0x20) : mword 64) 2
                    = mword_of_int (DL + 0x22)) by pcw.
    iEval (rewrite Hpp22) in "Hpc".
    (* ===== +0x22 c.mv s5,a1 : s5 := name ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (DL + 0x22)) Rs5 Ra1 R5 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi22").
    iIntros (CID16 Hq16) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R6 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R5 !!! Regidx Ra1))]> R5).
    assert (HR5a1 : R5 !!! Regidx Ra1 = nb)
      by (rewrite /R5 upd_ne; [exact HR4a1 | nz]).
    assert (HR6s5 : R6 !!! Regidx Rs5 = nb).
    { rewrite /R6 upd_eq. rewrite HR5a1. apply add_vec_zero_l. }
    assert (Hpp24 : add_vec_int (mword_of_int (DL + 0x22) : mword 64) 2
                    = mword_of_int (DL + 0x24)) by pcw.
    iEval (rewrite Hpp24) in "Hpc".
    (* ===== +0x24 c.mv s7,a2 : s7 := poff ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (DL + 0x24)) Rs7 Ra2 R6 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi24").
    iIntros (CID17 Hq17) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R7 := <[Regidx Rs7 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R6 !!! Regidx Ra2))]> R6).
    assert (HR6a2 : R6 !!! Regidx Ra2 = pf).
    { rewrite /R6 upd_ne; [| nz]. rewrite /R5 upd_ne; [exact HR4a2 | nz]. }
    assert (HR7s7 : R7 !!! Regidx Rs7 = pf).
    { rewrite /R7 upd_eq. rewrite HR6a2. apply add_vec_zero_l. }
    assert (HR7a0 : R7 !!! Regidx Ra0 = ip).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [exact HR4a0 | nz]. }
    assert (Hpp26 : add_vec_int (mword_of_int (DL + 0x24) : mword 64) 2
                    = mword_of_int (DL + 0x26)) by pcw.
    iEval (rewrite Hpp26) in "Hpc".
    (* ===== +0x26 c.lw a5,76(a0) : dp->size ===== *)
    iApply (wp_clw_s_sconf (mword_of_int (DL + 0x26)) Ra5 Ra0
              (mword_of_int 76 : mword 12) R7 (K - 12)%nat (di_size dn : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi26 [Hisz]").
    { iEval (rgne; rewrite HR7a0). iExact "Hisz". }
    iIntros (CID18 Hq18) "Hcg Hpc Hisz".
    iEval (rgne; rewrite HR7a0) in "Hisz".
    set (R8 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (di_size dn : mword 32) : mword 64)]> R7).
    assert (HR8a5 : R8 !!! Regidx Ra5
                    = (sign_extend' 64 (di_size dn : mword 32) : mword 64))
      by (rewrite /R8; apply upd_eq).
    assert (Hpp28 : add_vec_int (mword_of_int (DL + 0x26) : mword 64) 2
                    = mword_of_int (DL + 0x28)) by pcw.
    iEval (rewrite Hpp28) in "Hpc".
    (* ===== +0x28 c.li s1,0 : off := 0 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (DL + 0x28)) Rs1 (mword_of_int 0 : mword 6)
              (mword_of_int (Z.of_nat 0) : mword 64) R8 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi28").
    iIntros (CID19 Hq19) "Hcg Hpc".
    set (R9 := <[Regidx Rs1 := regval_into_reg
                  (mword_of_int (Z.of_nat 0) : mword 64)]> R8).
    assert (HR9s0 : R9 !!! Regidx Rs0 = sp0).
    { rewrite /R9 upd_ne; [| nz]. rewrite /R8 upd_ne; [| nz].
      rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [exact HR4s0 | nz]. }
    assert (Hpp2a : add_vec_int (mword_of_int (DL + 0x28) : mword 64) 2
                    = mword_of_int (DL + 0x2a)) by pcw.
    iEval (rewrite Hpp2a) in "Hpc".
    (* ===== +0x2a addi s4,s0,-96 : s4 := &de ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (DL + 0x2a)) Rs4 Rs0
              (mword_of_int 4000 : mword 12) R9 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2a").
    iIntros (CID20 Hq20) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R10 := <[Regidx Rs4 := regval_into_reg
                   (add_vec (R9 !!! Regidx Rs0)
                      (sign_extend' 64 (mword_of_int 4000 : mword 12)))]> R9).
    assert (HR10s4 : R10 !!! Regidx Rs4 = pa_stk sp0 12).
    { rewrite /R10 upd_eq. rewrite HR9s0. apply dlk_de_addr. }
    assert (Hpp2e : add_vec_int (mword_of_int (DL + 0x2a) : mword 64) 4
                    = mword_of_int (DL + 0x2e)) by pcw.
    iEval (rewrite Hpp2e) in "Hpc".
    (* ===== +0x2e c.li s3,16 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (DL + 0x2e)) Rs3 (mword_of_int 16 : mword 6)
              (mword_of_int 16 : mword 64) R10 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi2e").
    iIntros (CID21 Hq21) "Hcg Hpc".
    set (R11 := <[Regidx Rs3 := regval_into_reg (mword_of_int 16 : mword 64)]> R10).
    assert (HR11s0 : R11 !!! Regidx Rs0 = sp0).
    { rewrite /R11 upd_ne; [| nz]. rewrite /R10 upd_ne; [exact HR9s0 | nz]. }
    assert (Hpp30 : add_vec_int (mword_of_int (DL + 0x2e) : mword 64) 2
                    = mword_of_int (DL + 0x30)) by pcw.
    iEval (rewrite Hpp30) in "Hpc".
    (* ===== +0x30 addi s6,s0,-94 : s6 := &de.name ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (DL + 0x30)) Rs6 Rs0
              (mword_of_int 4002 : mword 12) R11 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi30").
    iIntros (CID22 Hq22) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R12 := <[Regidx Rs6 := regval_into_reg
                   (add_vec (R11 !!! Regidx Rs0)
                      (sign_extend' 64 (mword_of_int 4002 : mword 12)))]> R11).
    assert (HR12s6 : R12 !!! Regidx Rs6 = pa_add (pa_stk sp0 12) 2).
    { rewrite /R12 upd_eq. rewrite HR11s0. apply dlk_dename_addr. }
    assert (Hpp34 : add_vec_int (mword_of_int (DL + 0x30) : mword 64) 4
                    = mword_of_int (DL + 0x34)) by pcw.
    iEval (rewrite Hpp34) in "Hpc".
    (* ===== +0x34 c.li a0,0 : the "not found" return value ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (DL + 0x34)) Ra0 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) R12 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi34").
    iIntros (CID23 Hq23) "Hcg Hpc".
    set (R13 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> R12).
    assert (Hpp36 : add_vec_int (mword_of_int (DL + 0x34) : mword 64) 2
                    = mword_of_int (DL + 0x36)) by pcw.
    iEval (rewrite Hpp36) in "Hpc".
    (* ---- the register bundle the loop and the tail run on ---- *)
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (HR13 : dlk_regs m sp0 ip nb pf 0 R13).
    { unfold dlk_regs. split_and!.
      - rewrite /R13 upd_ne; [| nz]. rewrite /R12 upd_ne; [| nz].
        rewrite /R11 upd_ne; [| nz]. rewrite /R10 upd_ne; [| nz].
        rewrite /R9 upd_ne; [| nz]. rewrite /R8 upd_ne; [| nz].
        rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
        rewrite /R5 upd_ne; [exact HR4sp | nz].
      - rewrite /R13 upd_ne; [| nz]. rewrite /R12 upd_ne; [| nz].
        exact HR11s0.
      - rewrite /R13 upd_ne; [| nz]. rewrite /R12 upd_ne; [| nz].
        rewrite /R11 upd_ne; [| nz]. rewrite /R10 upd_ne; [| nz].
        rewrite /R9 upd_eq. reflexivity.
      - rewrite /R13 upd_ne; [| nz]. rewrite /R12 upd_ne; [| nz].
        rewrite /R11 upd_ne; [| nz]. rewrite /R10 upd_ne; [| nz].
        rewrite /R9 upd_ne; [| nz]. rewrite /R8 upd_ne; [| nz].
        rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
        exact HR5s2.
      - rewrite /R13 upd_ne; [| nz]. rewrite /R12 upd_ne; [| nz].
        rewrite /R11 upd_eq. reflexivity.
      - rewrite /R13 upd_ne; [| nz]. rewrite /R12 upd_ne; [| nz].
        rewrite /R11 upd_ne; [| nz]. exact HR10s4.
      - rewrite /R13 upd_ne; [| nz]. rewrite /R12 upd_ne; [| nz].
        rewrite /R11 upd_ne; [| nz]. rewrite /R10 upd_ne; [| nz].
        rewrite /R9 upd_ne; [| nz]. rewrite /R8 upd_ne; [| nz].
        rewrite /R7 upd_ne; [| nz]. exact HR6s5.
      - rewrite /R13 upd_ne; [| nz]. exact HR12s6.
      - rewrite /R13 upd_ne; [| nz]. rewrite /R12 upd_ne; [| nz].
        rewrite /R11 upd_ne; [| nz]. rewrite /R10 upd_ne; [| nz].
        rewrite /R9 upd_ne; [| nz]. rewrite /R8 upd_ne; [| nz].
        exact HR7s7.
      - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23.
        rewrite /R13 upd_ne; [| dlk_rne2 Hcsa0 Hc].
        rewrite /R12 upd_ne; [| dlk_xne N22].
        rewrite /R11 upd_ne; [| dlk_xne N19].
        rewrite /R10 upd_ne; [| dlk_xne N20].
        rewrite /R9 upd_ne; [| dlk_xne N9].
        rewrite /R8 upd_ne; [| dlk_rne2 Hcsa5 Hc].
        rewrite /R7 upd_ne; [| dlk_xne N23].
        rewrite /R6 upd_ne; [| dlk_xne N21].
        rewrite /R5 upd_ne; [| dlk_xne N18].
        exact (HR4o c Hc N2 N8). }
    (* ---- the [de] scratch record: two frame slots as sixteen bytes ---- *)
    iDestruct (dlk_slots_bytes sp0 u12 u11 with "Hb12 Hb11") as "[%Hal Hdeb]".
    destruct Hal as [Hal12 Hal11].
    iDestruct (dlk_bytes_name with "Hdeb") as (dolds0) "Hde".
    apply cheat_.
  Qed.

End ProofDirlookupMain.

End DirlookupProof.
