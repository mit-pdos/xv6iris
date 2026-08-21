(* ProofNameiparent.v -- nameiparent over the SIE-agnostic sconf world.

     struct inode*
     nameiparent(char *path, char *name)
     {
       return namex(path, 1, name);
     }

   24 bytes, eleven instructions.  A TWO-slot frame (ra@8, s0@0), the two
   argument moves -- [c.mv a2,a1] then [c.li a1,1], in that order, so a2
   gets the CALLER'S buffer before a1 is clobbered -- ONE [jal namex], and
   the epilogue.  There is no ghost move at all: the name buffer is the
   caller's, so it is threaded verbatim, and [npar := true] turns namex's
   conditional name clause into this contract's unconditional one.

   The pop is a plain [c.addi sp,sp,16], NOT a [c.addi16sp]: 16 fits the
   6-bit signed field, so gcc emits the cheaper form.  Hence
   [wp_caddi_sp_pop_s_sconf] here where a 32-byte frame would want
   [wp_caddi16sp_pop_s_sconf]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots.
Require Import ProcGeom.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import WpUart.
Require Import DiskPtsto.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import DirentEnc.
Require Import PathElems.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheEscrow.
Require Import FileInvDefs.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import CodeNameiparent.
Require Import SpecDirlookup.
Require Import SpecNamex.
Require Import SpecNameiparent.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import ProcDefs.  (* [pprivate], [proc_priv_bare] *)
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  THE PURE SIDE-CONDITIONS, as closed top-level facts -- N4c3's trap 4  *)
(*  (never run [lia] / [vm_compute] inside the whole-function context).   *)
(* ===================================================================== *)

(* the two registers this frame saves *)
Definition npi_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> (mword_of_int 8 : mword 5) ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Definition npi_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2.

(* -16: [c.addi sp,sp,-16], 48 being -16 in a 6-bit signed field *)
Lemma npi_push (X : mword 64) :
  add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))
  = pa_stk X 2.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

(* [c.addi4spn s0,sp,16] lands back at the ENTRY sp *)
Lemma npi_fp (X : mword 64) :
  add_vec (pa_stk X 2) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* the two c.sdsp / c.ldsp displacements off the pushed sp *)
Lemma npi_frm (X : mword 64) (u : mword 6) (k : nat) :
  (mword_of_int (wrap64 (uint (mword_of_int (- (8 * Z.of_nat 2)) : mword 64)
                         + uint (zero_extend' 64 (concat_vec u ('b"000")) : mword 64)))
   : mword 64)
  = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 2) (zero_extend' 64 (concat_vec u ('b"000"))) = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. exact H.
Qed.

Lemma npi_frm1 (X : mword 64) :
  add_vec (pa_stk X 2) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof. apply npi_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma npi_frm2 (X : mword 64) :
  add_vec (pa_stk X 2) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof. apply npi_frm. apply bv_eq; vm_compute; reflexivity. Qed.

(* K_nameiparent's single premise, turned into the three bounds the callee
   and the [sie_cap_gpr] pop want *)
Lemma npi_kb (K : nat) : (K_nameiparent <= K)%nat ->
  (K_namex <= K - 2)%nat /\ (2 <= K)%nat /\ ((K - 2) + 2 = K)%nat.
Proof. intro H. split_and!; lia. Qed.

(* [li a1,1] makes namex's ghost flag TRUE *)
Lemma npi_a1_true :
  eq_vec (mword_of_int 1 : mword 64) (zero_reg : mword 64) = negb true.
Proof. vm_compute. reflexivity. Qed.

Module NameiparentProof (NX : NAMEX) : NAMEIPARENT.

Notation NP := KernelSyms.nameiparent (only parsing).
Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac npidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

Section ProofNameiparentMain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            ICFG : icfg, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE WALK IS THE SET FORM; the counted seal follows it. *)
  Lemma wp_nameiparent_gen
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8)
      (nfun : nat -> bv 8)
      (n : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
    : wp_nameiparent_gen_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
                                ga gf cov logstart bmapstart inodestart nib
                                size dev plen pfun nfun n Sb
                                pidv dq dqb dqs dqpv m K eb b lks Vpr.
  Proof.
    cbv beta delta [wp_nameiparent_gen_body].
    intros pcE pjv pv nb ret_tgt pl L
           HK Hdev Hnib Htlog Htist Hroot Hnib0 Hlg Hsize Hbmap0 Hbmapcov
           Hbmaplog Hinos0 Hcovb Hiregb Hcstr Hplen Hbud Hj Hgs.
    destruct (npi_kb K HK) as (Knx & K2 & Kpop).
    (* N3d trap 1's whole-function fix: fold [proc_addr j] into every
       resource ONCE, and never write [pjv] again. *)
    assert (Hpjd : proc_addr j = pjv) by reflexivity.
    iIntros "Hcg Hcnt Hextc Hclmc #Htext #Hkd Hpc #Hpenv #Hbio #Hlogc #Hkenv #Hitb2 #Hitbl
              #Hesc #Hslks #Hireg #Hropen #Hprocs #Hdev #Hgeom #Hdlk Hbmap Hinos
              #Hbits Hppid Hcwdr Hpath Hname Hbslot Hislot Hlog Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hebb.
    (* depth 0 forces the held set empty, so every [locks_below] the callees
       raise is [locks_below ∅ _], which [lkbelow] closes outright. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    iEval (rewrite -Hpjd) in "Hcg".
    iEval (rewrite -Hpjd) in "Hcnt".
    iEval (rewrite -Hpjd) in "Hclmc".
    iEval (rewrite -Hpjd) in "Hppid".
    iEval (rewrite -Hpjd) in "Hcont".
    iPoseProof (npi_00 with "Htext") as "Hi00".
    iPoseProof (npi_02 with "Htext") as "Hi02".
    iPoseProof (npi_04 with "Htext") as "Hi04".
    iPoseProof (npi_06 with "Htext") as "Hi06".
    iPoseProof (npi_08 with "Htext") as "Hi08".
    iPoseProof (npi_0a with "Htext") as "Hi0a".
    iPoseProof (npi_0c with "Htext") as "Hi0c".
    iPoseProof (npi_10 with "Htext") as "Hi10".
    iPoseProof (npi_12 with "Htext") as "Hi12".
    iPoseProof (npi_14 with "Htext") as "Hi14".
    iPoseProof (npi_16 with "Htext") as "Hi16".
    (* ===== +0x00 c.addi sp,sp,-16 : the two-slot frame ===== *)
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : (m !!! Regidx csp_rs1 : mword 64) = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2) by apply npi_push.
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 48 : mword 6) m K 2 b
              K2 Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    assert (HR1sp : npi_sp m R1) by (rewrite /npi_sp /R1 upd_eq; exact Hpush).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (v1) "Hf1". iDestruct "S2" as (v2) "Hf2".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 1)
      by (rewrite HR1sp; apply npi_frm1).
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk sp0 2)
      by (rewrite HR1sp; apply npi_frm2).
    iEval (rewrite -Hb1) in "Hf1". iEval (rewrite -Hb2) in "Hf2".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2
                    = mword_of_int (NP + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* ===== +0x02 c.sdsp ra,8(sp) ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (NP + 0x02))
              (mword_of_int 1 : mword 6) Rra R1 (K - 2)%nat v1 b
              with "Hcg Hpc Hi02 Hf1").
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (NP + 0x02) : mword 64) 2
                    = mword_of_int (NP + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    (* ===== +0x04 c.sdsp s0,0(sp) ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (NP + 0x04))
              (mword_of_int 0 : mword 6) Rs0 R1 (K - 2)%nat v2 b
              with "Hcg Hpc Hi04 Hf2").
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (NP + 0x04) : mword 64) 2
                    = mword_of_int (NP + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    assert (HR1ra : (R1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s0 : (R1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    iEval (rewrite Hb1; rgne; rewrite HR1ra) in "Hf1".
    iEval (rewrite Hb2; rgne; rewrite HR1s0) in "Hf2".
    (* ===== +0x06 c.addi4spn s0,sp,16 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (NP + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) Rs0
              R1 (K - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    assert (HR2sp : npi_sp m R2)
      by (rewrite /npi_sp /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2a0 : (R2 !!! Regidx Ra0 : mword 64) = pv).
    { rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR2a1 : (R2 !!! Regidx Ra1 : mword 64) = nb).
    { rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR2ra : (R2 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R2 upd_ne; [exact HR1ra | nz]).
    assert (HR2thr : npi_thr m R2).
    { intros c Hcs N2 N8.
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (Hpp08 : add_vec_int (mword_of_int (NP + 0x06) : mword 64) 2
                    = mword_of_int (NP + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    (* ===== +0x08 c.mv a2,a1 -- the CALLER'S buffer, before a1 dies ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (NP + 0x08)) Ra2 Ra1
              R2 (K - 2)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi08").
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (R3 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R2 Ra1))]> R2).
    assert (HR3a2 : (R3 !!! Regidx Ra2 : mword 64) = nb).
    { rewrite /R3 upd_eq. rgne. rewrite HR2a1. apply add_vec_zero_l. }
    assert (HR3a0 : (R3 !!! Regidx Ra0 : mword 64) = pv)
      by (rewrite /R3 upd_ne; [exact HR2a0 | nz]).
    assert (HR3ra : (R3 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2ra | nz]).
    assert (HR3sp : npi_sp m R3)
      by (rewrite /npi_sp /R3 upd_ne; [exact HR2sp | nz]).
    assert (HR3thr : npi_thr m R3).
    { intros c Hcs N2 N8. rewrite /R3 upd_ne; [| regne].
      exact (HR2thr c Hcs N2 N8). }
    assert (Hpp0a : add_vec_int (mword_of_int (NP + 0x08) : mword 64) 2
                    = mword_of_int (NP + 0x0a)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    (* ===== +0x0a c.li a1,1 : nameiparent = 1 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (NP + 0x0a)) Ra1
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              R3 (K - 2)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (R4 := <[Regidx Ra1 := regval_into_reg (mword_of_int 1 : mword 64)]> R3).
    assert (HR4a1 : (R4 !!! Regidx Ra1 : mword 64) = (mword_of_int 1 : mword 64))
      by (rewrite /R4; apply upd_eq).
    assert (HR4a2 : (R4 !!! Regidx Ra2 : mword 64) = nb)
      by (rewrite /R4 upd_ne; [exact HR3a2 | nz]).
    assert (HR4a0 : (R4 !!! Regidx Ra0 : mword 64) = pv)
      by (rewrite /R4 upd_ne; [exact HR3a0 | nz]).
    assert (HR4ra : (R4 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3ra | nz]).
    assert (HR4sp : npi_sp m R4)
      by (rewrite /npi_sp /R4 upd_ne; [exact HR3sp | nz]).
    assert (HR4thr : npi_thr m R4).
    { intros c Hcs N2 N8. rewrite /R4 upd_ne; [| regne].
      exact (HR3thr c Hcs N2 N8). }
    assert (Hpp0c : add_vec_int (mword_of_int (NP + 0x0a) : mword 64) 2
                    = mword_of_int (NP + 0x0c)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    (* ===== +0x0c jal ra,namex ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (NP + 0x0c)) Rra
              (mword_of_int 2096610 : mword 21) R4 (K - 2)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (R5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (NP + 0x0c) : mword 64) 4)]> R4).
    assert (Htgt : add_vec (mword_of_int (NP + 0x0c) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096610 : mword 21))
                   = mword_of_int KernelSyms.namex) by pcw.
    iEval (rewrite Htgt) in "Hpc".
    assert (HR5a1 : (R5 !!! Regidx Ra1 : mword 64) = (mword_of_int 1 : mword 64))
      by (rewrite /R5 upd_ne; [exact HR4a1 | nz]).
    assert (HR5a2 : (R5 !!! Regidx Ra2 : mword 64) = nb)
      by (rewrite /R5 upd_ne; [exact HR4a2 | nz]).
    assert (HR5a0 : (R5 !!! Regidx Ra0 : mword 64) = pv)
      by (rewrite /R5 upd_ne; [exact HR4a0 | nz]).
    assert (HR5sp : npi_sp m R5)
      by (rewrite /npi_sp /R5 upd_ne; [exact HR4sp | nz]).
    assert (HR5ra : (R5 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (NP + 0x0c) : mword 64) 4)
      by (rewrite /R5; apply upd_eq).
    assert (HR5thr : npi_thr m R5).
    { intros c Hcs N2 N8. rewrite /R5 upd_ne; [| regne].
      exact (HR4thr c Hcs N2 N8). }
    (* the path and the name buffer, re-addressed at namex's own registers *)
    iEval (rewrite -HR5a0) in "Hpath".
    iEval (rewrite -HR5a2) in "Hname".
    iDestruct (cpu_own_transport CID CID7 0%nat eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID CID7 eb (proc_addr j)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CID7 eb (proc_addr j)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iDestruct (wp_next_shift (b := true) (CIDa := CID) (CIDb := CID7) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iApply (NX.wp_namex_gen gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
              ga gf cov logstart bmapstart inodestart nib size dev
              plen pfun nfun true n Sb pidv dq dqb dqs dqpv R5 (K - 2)%nat eb b
              _ Vpr Knx Hdev Hnib Htlog Htist Hroot Hnib0 Hlg Hsize Hbmap0 Hbmapcov
              Hbmaplog Hinos0 Hcovb Hiregb Hcstr Hplen Hbud Hj Hgs
              ltac:(rewrite HR5a1; exact npi_a1_true)
              with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio Hlogc Hkenv Hitb2 Hitbl
                    Hesc Hslks Hireg Hropen Hprocs Hdev Hgeom Hdlk Hbmap Hinos
                    Hbits Hppid Hcwdr Hpath Hname Hbslot Hislot Hlog").
    all: try lkbelow.
    iIntros (CID8 Hq8 mf n' Sb' ok nf ipv w)
            "%Hcs Hcg Hcnt Hextc Hclmc Hpc Hbmap Hinos Hppid Hcwdr
             Hpath Hname Hbslot %Hssub %Hwbm %Hbudo Hlog Hok".
    iEval (rewrite HR5a0) in "Hpath".
    iEval (rewrite HR5a2) in "Hname".
    assert (Hpc10 : ret_pc (R5 !!! Regidx Rra : mword 64)
                    = mword_of_int (NP + 0x10)) by (rewrite HR5ra; pcw).
    iEval (rewrite Hpc10) in "Hpc".
    pose proof Hcs as Hcs_cs.
    assert (Hmfsp : npi_sp m mf).
    { rewrite /npi_sp
        (callee_saved_lookup Hcs_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HR5sp. }
    assert (Hmfthr : npi_thr m mf).
    { intros c Hcs2 N2 N8.
      rewrite (callee_saved_lookup Hcs_cs c Hcs2).
      exact (HR5thr c Hcs2 N2 N8). }
    assert (Hmfa0 : (mf !!! Regidx Ra0 : mword 64)
                    = (mf !!! Regidx Ra0 : mword 64)) by reflexivity.
    (* ===== +0x10 .. +0x12 : the two restores ===== *)
    assert (Hc1 : add_vec (mf !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite Hmfsp; apply npi_frm1).
    assert (Hc2 : add_vec (mf !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite Hmfsp; apply npi_frm2).
    iApply (wp_cldsp_s_sconf (mword_of_int (NP + 0x10))
              (mword_of_int 1 : mword 6) Rra mf (K - 2)%nat
              (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi10 [Hf1]").
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID9 Hq9) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> mf).
    assert (HP1sp : npi_sp m P1)
      by (rewrite /npi_sp /P1 upd_ne; [exact Hmfsp | nz]).
    assert (HP1thr : npi_thr m P1).
    { intros c Hcs2 N2 N8. rewrite /P1 upd_ne; [| regne].
      exact (Hmfthr c Hcs2 N2 N8). }
    assert (HP1ra : (P1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1a0 : (P1 !!! Regidx Ra0 : mword 64) = (mf !!! Regidx Ra0 : mword 64))
      by (rewrite /P1 upd_ne; [reflexivity | nz]).
    assert (Hpp12 : add_vec_int (mword_of_int (NP + 0x10) : mword 64) 2
                    = mword_of_int (NP + 0x12)) by pcw.
    iEval (rewrite Hpp12) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (NP + 0x12))
              (mword_of_int 0 : mword 6) Rs0 P1 (K - 2)%nat
              (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi12 [Hf2]").
    { iEval (rewrite HP1sp -Hmfsp Hc2). iExact "Hf2". }
    iIntros (CID10 Hq10) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -Hmfsp Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : npi_sp m P2)
      by (rewrite /npi_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : npi_thr m P2).
    { intros c Hcs2 N2 N8. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hcs2 N2 N8). }
    assert (HP2ra : (P2 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1ra | nz]).
    assert (HP2a0 : (P2 !!! Regidx Ra0 : mword 64) = (mf !!! Regidx Ra0 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1a0 | nz]).
    assert (Hpp14 : add_vec_int (mword_of_int (NP + 0x12) : mword 64) 2
                    = mword_of_int (NP + 0x14)) by pcw.
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 c.addi sp,sp,16 : pop ===== *)
    assert (Hwv : add_vec (P2 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))
                  = sp0)
      by (rewrite HP2sp; apply stk_pop_16).
    assert (Hpop : (P2 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P2 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2)
      by (rewrite Hwv HP2sp; reflexivity).
    iAssert (stack_own (KTR := KT1) sp0 2) with "[Hf1 Hf2]" as "Hstk".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hf1"; [iExists _; iExact "Hf1" |].
      iSplitL "Hf2"; [iExists _; iExact "Hf2" |].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (NP + 0x14))
              (mword_of_int 16 : mword 6) P2 (K - 2)%nat 2 b Hpop
              with "Hcg Hpc Hi14 Hstk").
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (P3 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P2 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> P2).
    iEval (rewrite Kpop) in "Hcg".
    assert (Hpp16 : add_vec_int (mword_of_int (NP + 0x14) : mword 64) 2
                    = mword_of_int (NP + 0x16)) by pcw.
    iEval (rewrite Hpp16) in "Hpc".
    (* ===== +0x16 c.ret ===== *)
    assert (HP3ra : (P3 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2ra | nz]).
    iApply (wp_cret_s_sconf (mword_of_int (NP + 0x16)) Rra P3 K b
              ltac:(nz) with "Hcg Hpc Hi16").
    iIntros (CID12 Hq12) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P3 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP3ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CONTRACT ===== *)
    assert (HP3a0 : (P3 !!! Regidx Ra0 : mword 64) = (mf !!! Regidx Ra0 : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2a0 | nz]).
    assert (Csp : (P3 !!! Regidx csp_rs1 : mword 64)
                  = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P3 upd_eq; exact Hwv).
    assert (Cs0 : (P3 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P3 upd_ne; [| nz]. rewrite /P2 upd_eq. reflexivity. }
    assert (Hfin : npi_thr m P3).
    { intros c Hcs2 N2 N8. rewrite /P3 upd_ne; [| regne].
      exact (HP2thr c Hcs2 N2 N8). }
    assert (Cs1 : (P3 !!! Regidx (mword_of_int 9 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 9 : mword 5) : mword 64))
      by (apply Hfin; npidx).
    assert (Cs2 : (P3 !!! Regidx (mword_of_int 18 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 18 : mword 5) : mword 64))
      by (apply Hfin; npidx).
    assert (Cs3 : (P3 !!! Regidx (mword_of_int 19 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 19 : mword 5) : mword 64))
      by (apply Hfin; npidx).
    assert (Cs4 : (P3 !!! Regidx (mword_of_int 20 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 20 : mword 5) : mword 64))
      by (apply Hfin; npidx).
    assert (Cs5 : (P3 !!! Regidx (mword_of_int 21 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 21 : mword 5) : mword 64))
      by (apply Hfin; npidx).
    assert (Cs6 : (P3 !!! Regidx (mword_of_int 22 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 22 : mword 5) : mword 64))
      by (apply Hfin; npidx).
    assert (Cs7 : (P3 !!! Regidx (mword_of_int 23 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; npidx).
    assert (Cs8 : (P3 !!! Regidx (mword_of_int 24 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; npidx).
    assert (Cs9 : (P3 !!! Regidx (mword_of_int 25 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; npidx).
    assert (Cs10 : (P3 !!! Regidx (mword_of_int 26 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; npidx).
    assert (Cs11 : (P3 !!! Regidx (mword_of_int 27 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; npidx).
    (* the two arms, re-stated at the FINAL register file; [npar = true]
       makes namex's conditional name clause unconditional *)
    iAssert (if ok
             then ⌜(P3 !!! Regidx Ra0 : mword 64) = ipv
                   /\ (exists es e, nameiparent_of pl es e /\ bname 14 nf = e)⌝ ∗
                  inode_held_ty ipv T_DIR ∗ iref_slots 1
             else ⌜(P3 !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64)⌝ ∗
                  iref_slots 2)%I with "[Hok]" as "Hok".
    { destruct ok.
      - iDestruct "Hok" as "[%Hp [Hheld Hsl]]". iFrame "Hheld Hsl".
        iPureIntro. destruct Hp as [Hp1 Hp2].
        split; [rewrite HP3a0; exact Hp1 | exact (Hp2 eq_refl)].
      - iDestruct "Hok" as "[%Hp Hsl]". iFrame "Hsl".
        iPureIntro. rewrite HP3a0. exact Hp. }
    iDestruct (cpu_own_transport CID8 CID12 0%nat eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID8 CID12 eb (proc_addr j)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID8 CID12 eb (proc_addr j)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iSpecialize ("Hcont" $! CID12 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! P3 n' Sb' ok nf ipv w
              with "[%] Hcg Hcnt Hextc Hclmc Hpc Hbmap Hinos Hppid Hcwdr
                    Hpath Hname Hbslot [%] [%] [%] Hlog Hok").
    { unfold callee_saved. split_and!; assumption. }
    { exact Hssub. }
    { exact Hwbm. }
    { exact Hbudo. }
  Qed.


  (* ===================================================================== *)
  (*  THE COUNTED SEAL, at the [log_op] existential's own witness.  The     *)
  (*  budget clause is identical on both sides (no credit anywhere on this  *)
  (*  chain), so the seal is pure plumbing.                                 *)
  (* ===================================================================== *)
  Lemma wp_nameiparent_sconf
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8)
      (nfun : nat -> bv 8)
      (n : nat)
      (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
    : wp_nameiparent_sconf_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
                          ga gf cov logstart bmapstart inodestart nib
                          size dev plen pfun nfun n
                          pidv dq dqb dqs dqpv m K eb b lks Vpr.
  Proof.
    cbv beta delta [wp_nameiparent_sconf_body].
    intros pcE pjv pv nb ret_tgt pl L
           HK Hdev Hnib Htlog Htist Hroot Hnib0 Hlg Hsize Hbmap0 Hbmapcov
           Hbmaplog Hinos0 Hcovb Hiregb Hcstr Hplen Hbud Hj Hgs.
    iIntros "Hcg Hcnt Hextc Hclmc #Htext #Hkd Hpc #Hpenv #Hbio #Hlogc #Hkenv #Hitb2 #Hitbl
              #Hesc #Hslks #Hireg #Hropen #Hprocs #Hdev #Hgeom #Hdlk Hbmap Hinos
              #Hbits Hppid Hcwdr Hpath Hname Hbslot Hislot Hlog Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hebb.
    (* depth 0 forces the held set empty, so every [locks_below] the callees
       raise is [locks_below ∅ _], which [lkbelow] closes outright. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    iDestruct "Hlog" as (Sb0) "Hlog".
    iApply (wp_nameiparent_gen gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
              ga gf cov logstart bmapstart inodestart nib
              size dev plen pfun nfun n Sb0
              pidv dq dqb dqs dqpv m K eb b
              _ Vpr HK Hdev Hnib Htlog Htist Hroot Hnib0 Hlg Hsize Hbmap0 Hbmapcov Hbmaplog Hinos0 Hcovb Hiregb Hcstr Hplen (walk_need_counted L n Hbud) Hj Hgs
              with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio Hlogc Hkenv Hitb2 Hitbl Hesc Hslks Hireg Hropen Hprocs Hdev Hgeom Hdlk Hbmap Hinos Hbits Hppid Hcwdr Hpath Hname Hbslot Hislot Hlog [Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDf) "%Hchain".
    iIntros (mf n' Sb' ok nf ipv w)
      "%Hcs Hcg Hcnt Hextc Hclmc Hpc Hbmap Hinos Hppid Hcwdr
       Hpath Hname Hbslot %Hssub %Hwbm %Hbnd Hlog Hok".
    iSpecialize ("Hcont" $! CIDf with "[%]"); [exact Hchain|].
    (* the counted caller asked for a plain reference; the type witness
       the gen post now carries is dropped here (fs-log.md §G.24) *)
    iAssert (if ok
             then ⌜(mf !!! Regidx (mword_of_int 10 : mword 5) : mword 64) = ipv
                   /\ (exists es e, nameiparent_of pl es e /\ bname 14 nf = e)⌝ ∗
                  inode_held ipv ∗ iref_slots 1
             else ⌜(mf !!! Regidx (mword_of_int 10 : mword 5) : mword 64)
                   = (mword_of_int 0 : mword 64)⌝ ∗ iref_slots 2)%I
      with "[Hok]" as "Hok".
    { destruct ok; [| iExact "Hok"].
      iDestruct "Hok" as "(%Hp & Hip & Hsl)".
      iSplitR; [iPureIntro; exact Hp |]. iSplitR "Hsl"; [| iExact "Hsl"].
      iApply (inode_held_ty_forget with "Hip"). }
    iApply ("Hcont" $! mf n' ok nf ipv
              with "[%] Hcg Hcnt Hextc Hclmc Hpc Hbmap Hinos Hppid Hcwdr
                    Hpath Hname Hbslot [%] [Hlog] Hok").
    { exact Hcs. }
    { split; [exact (walk_spend_counted L n n' w ok Hbud (proj1 Hbnd))
             | exact (proj2 Hbnd)]. }
    { iApply (log_opS_op with "Hlog"). }
  Qed.

End ProofNameiparentMain.

End NameiparentProof.
