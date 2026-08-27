(* ProofNameiTr.v -- namei at the TRACE contract
   (claude-notes/projects/namei-pinned-lookup.md, stage N-3).

     struct inode*
     namei(char *path)
     {
       char name[DIRSIZ];
       return namex(path, 0, name);
     }

   [ProofNamei.wp_namei_gen] byte for byte: the same four-slot frame, the
   same FRAME CARVE (the low two slots ARE [name[14]]), the same eleven
   instructions.  The only difference is the callee's contract --
   [SpecNamexTr.NAMEX_TR] instead of [SpecNamex.NAMEX] -- so this file
   threads the two trace premises into the call, hands the two changed
   postcondition arms back at the final register file, and does nothing
   else.  In particular it fires no hop and owns no [dv] fragment: the
   trace lives entirely inside the walk.

   The [pfun 0 = SLASH] premise (the absolute-path ruling) is relayed
   verbatim; it is namex's, not namei's.

   The frame-carve lemmas and the pure side-conditions are
   [ProofNamei.v]'s, restated here only because that module is sealed to
   [NAMEI] and its internals are not exported.  Read that file's header
   for the carve. *)
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
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import KernelRvcDecode.
Require Import StackOwn StackBytes.
Require Import CalleeSaved.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import WpUart.
Require Import DiskPtsto.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import IcacheEscrow.
Require Import FileInvDefs.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import CodeNamei.
Require Import SpecNameiTr.
Require Import SpecNamexTr.
Require Import ProofNamei.   (* READ-ONLY REUSE: its top-level pure lemmas *)
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.
Require Import ProcDefs.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* [li a1,0] IS namex's namei side: the trace contract fixes the flag at
   [false], so the reflection premise is the one instance that survives. *)
Lemma nami_a1_true :
  eq_vec (mword_of_int 0 : mword 64) (zero_reg : mword 64) = true.
Proof. vm_compute. reflexivity. Qed.

Module NameiTrProof (NX : NAMEX_TR) : NAMEI_TR.

Notation NM := KernelSyms.namei (only parsing).
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
Local Ltac namidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

Section ProofNameiTrMain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---- THE FRAME CARVE: the two low slots ARE [name[14]] ---- *)

  Lemma nam_slots_bytes (sp0 : mword 64) (w1 w2 : bv 64) :
    (pa_stk sp0 4) ↦₈[KT1] w1 -∗ (pa_stk sp0 3) ↦₈[KT1] w2 -∗
    ⌜is_aligned_paddr (Physaddr (pa_stk sp0 4)) 8 = true
     /\ is_aligned_paddr (Physaddr (pa_stk sp0 3)) 8 = true⌝ ∗
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 4) 16.
  Proof.
    assert (E1 : pa_add (pa_stk sp0 4) 8 = pa_stk sp0 3)
      by (rewrite (pa_stk_next sp0 4 ltac:(lia)); reflexivity).
    iIntros "H1 H2".
    iDestruct (slot_bytes_own with "H1") as "[%Ha1 B1]".
    iDestruct (slot_bytes_own with "H2") as "[%Ha2 B2]".
    iSplitR; [done |].
    change 16%nat with (8 + 8)%nat.
    rewrite bytes_own_app E1. iSplitL "B1"; [iExact "B1" | iExact "B2"].
  Qed.

  Lemma nam_bytes_slots (sp0 : mword 64) :
    is_aligned_paddr (Physaddr (pa_stk sp0 4)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 3)) 8 = true ->
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 4) 16 ⊢
    ∃ w1 w2 : bv 64, (pa_stk sp0 4) ↦₈[KT1] w1 ∗ (pa_stk sp0 3) ↦₈[KT1] w2.
  Proof.
    intros Ha1 Ha2.
    assert (E1 : pa_add (pa_stk sp0 4) 8 = pa_stk sp0 3)
      by (rewrite (pa_stk_next sp0 4 ltac:(lia)); reflexivity).
    iIntros "B". change 16%nat with (8 + 8)%nat.
    rewrite bytes_own_app E1. iDestruct "B" as "[B1 B2]".
    iDestruct (bytes_own_slot _ Ha1 with "B1") as (w1) "H1".
    iDestruct (bytes_own_slot _ Ha2 with "B2") as (w2) "H2".
    iExists w1, w2. iFrame.
  Qed.

  Lemma nam_bytes_name (a : mword 64) (N : nat) :
    bytes_own (KTR := KT1) (DfracOwn 1) a N ⊢
    ∃ f : nat -> bv 8, [∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ[KT1] f j.
  Proof. rewrite /bytes_own. exact (bb_any_named (KTR := KT1) a N). Qed.

  Lemma nam_name_bytes (a : mword 64) (N : nat) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ[KT1] f j) ⊢ bytes_own (KTR := KT1) (DfracOwn 1) a N.
  Proof. rewrite /bytes_own. exact (bb_named_any (KTR := KT1) a N f). Qed.

  (* 16 = 14 + 2: namex writes at most fourteen; the two above ride through *)
  Lemma nam_buf_split (a : mword 64) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 16, pa_add a j ↦ₘ[KT1] f j) -∗
    ([∗ list] j ∈ seq 0 14, pa_add a j ↦ₘ[KT1] f j)
    ∗ ([∗ list] j ∈ seq 0 2, pa_add (pa_add a 14) j ↦ₘ[KT1] f (14 + j)%nat).
  Proof.
    change 16%nat with (14 + 2)%nat.
    rewrite (bb_split a 14 2 f). iIntros "[$ $]".
  Qed.

  Lemma nam_buf_join (a : mword 64) (f nf : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 14, pa_add a j ↦ₘ[KT1] nf j) -∗
    ([∗ list] j ∈ seq 0 2, pa_add (pa_add a 14) j ↦ₘ[KT1] f (14 + j)%nat) -∗
    bytes_own (KTR := KT1) (DfracOwn 1) a 16.
  Proof.
    iIntros "H1 H2".
    iDestruct (nam_name_bytes a 14 nf with "H1") as "B1".
    iDestruct (nam_name_bytes (pa_add a 14) 2 (fun j => f (14 + j)%nat)
                 with "H2") as "B2".
    change 16%nat with (14 + 2)%nat.
    rewrite bytes_own_app. iFrame.
  Qed.

  (* THE WRAPPER, AT THE TRACE CONTRACT.  [ProofNamei.wp_namei_gen]'s
     eleven instructions and its frame carve, verbatim; the two trace rows
     are threaded straight into [NX.wp_namex_tr] and its two postcondition
     arms are re-stated at the FINAL register file, which is the only thing
     this file does with them. *)
  Lemma wp_namei_tr
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (ga : gname) (gf : gname)
      (bmapstart : Z)
      (size : Z)
      (plen : nat) (pfun : nat -> bv 8)
      (n : nat) (Sb : gset Z)
      (P : nat -> Z -> iProp Σ) (Pmiss : nat -> Z -> iProp Σ)
      (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
    : wp_namei_tr_body gs j gl gu gd gk pd pav pu bn
                       ga gf bmapstart
                       size plen pfun n Sb P Pmiss
                       pidv dq dqb dqs dqpv m K eb b lks Vpr.
  Proof.
    cbv beta delta [wp_namei_tr_body].
    intros pcE pjv pv ret_tgt pl L
           HK Hroot Hnib0 Hlg Hsize Hbmap0 Hbmapcov
           Hbmaplog Hinos0 Hcovb Hiregb Hcstr Hplen Hpfun0 Hbud Hj Hgs.
    destruct (nam_kb K HK) as (Knx & K4 & Kpop).
    (* N3d trap 1's whole-function fix: fold [proc_addr j] into every
       resource ONCE, and never write [pjv] again. *)
    assert (Hpjd : proc_addr j = pjv) by reflexivity.
    iIntros "Hcg Hcnt Hextc Hclmc #Htext #Hkd Hpc #Hpenv #Hbio #Hlogc #Hkenv #Hitb2 #Hitbl
              #Hesc #Hslks #Hireg #Hropen #Hprocs #Hdev #Hgeom #Hdlk Hbmap Hinos
              #Hbits Hppid Hcwdr Hpath Hbslot Hislot Hlog HP0 Hhops0 Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hebb.
    (* depth 0 forces the held set empty, so every [locks_below] the callees
       raise is [locks_below ∅ _], which [lkbelow] closes outright. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    iEval (rewrite -Hpjd) in "Hcg".
    iEval (rewrite -Hpjd) in "Hcnt".
    iEval (rewrite -Hpjd) in "Hclmc".
    iEval (rewrite -Hpjd) in "Hppid".
    iEval (rewrite -Hpjd) in "Hcont".
    (* ===== +0x00 c.addi sp,sp,-32 : the four-slot frame ===== *)
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : (m !!! Regidx csp_rs1 : mword 64) = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4) by apply stk_push_32.
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 b
              K4 Hpush with "Hcg Hpc []").
    { iApply (nmi_00 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HR1sp : nam_sp m R1) by (rewrite /nam_sp /R1 upd_eq; exact Hpush).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (v1) "Hf1". iDestruct "S2" as (v2) "Hf2".
    iDestruct "S3" as (v3) "Hf3". iDestruct "S4" as (v4) "Hf4".
    (* THE FRAME CARVE: slots 4 and 3 are [name[14]] plus two spare bytes *)
    iDestruct (nam_slots_bytes sp0 v4 v3 with "Hf4 Hf3") as "[%Hal Hbytes]".
    destruct Hal as [Hal4 Hal3].
    iDestruct (nam_bytes_name (pa_stk sp0 4) 16 with "Hbytes") as (nfun) "Hbuf".
    iDestruct (nam_buf_split (pa_stk sp0 4) nfun with "Hbuf") as "[Hname Htail]".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 1)
      by (rewrite HR1sp; apply nam_frm1).
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 2)
      by (rewrite HR1sp; apply nam_frm2).
    iEval (rewrite -Hb1) in "Hf1". iEval (rewrite -Hb2) in "Hf2".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2
                    = mword_of_int (NM + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* ===== +0x02 c.sdsp ra,24(sp) ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (NM + 0x02))
              (mword_of_int 3 : mword 6) Rra R1 (K - 4)%nat v1 b
              with "Hcg Hpc [] Hf1").
    { iApply (nmi_02 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (NM + 0x02) : mword 64) 2
                    = mword_of_int (NM + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    (* ===== +0x04 c.sdsp s0,16(sp) ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (NM + 0x04))
              (mword_of_int 2 : mword 6) Rs0 R1 (K - 4)%nat v2 b
              with "Hcg Hpc [] Hf2").
    { iApply (nmi_04 with "Htext"). }
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
              with "Hcg Hpc []").
    { iApply (nmi_06 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (HR2s0 : (R2 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite /R2 upd_eq. rewrite HR1sp. apply stk_fp_32. }
    assert (HR2sp : nam_sp m R2)
      by (rewrite /nam_sp /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2a0 : (R2 !!! Regidx Ra0 : mword 64) = pv).
    { rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR2ra : (R2 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R2 upd_ne; [exact HR1ra | nz]).
    assert (HR2thr : nam_thr m R2).
    { intros c Hcs N2 N8.
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (Hpp08 : add_vec_int (mword_of_int (NM + 0x06) : mword 64) 2
                    = mword_of_int (NM + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    (* ===== +0x08 addi a2,s0,-32 : &name[0], the frame's low slot ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (NM + 0x08)) Ra2 Rs0
              (mword_of_int 4064 : mword 12) R2 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (nmi_08 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (R3 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (rget R2 Rs0)
                     (sign_extend' 64 (mword_of_int 4064 : mword 12)))]> R2).
    assert (HR3a2 : (R3 !!! Regidx Ra2 : mword 64) = pa_stk sp0 4).
    { rewrite /R3 upd_eq. rgne. rewrite HR2s0. apply nam_buf. }
    assert (HR3a0 : (R3 !!! Regidx Ra0 : mword 64) = pv)
      by (rewrite /R3 upd_ne; [exact HR2a0 | nz]).
    assert (HR3ra : (R3 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2ra | nz]).
    assert (HR3sp : nam_sp m R3)
      by (rewrite /nam_sp /R3 upd_ne; [exact HR2sp | nz]).
    assert (HR3thr : nam_thr m R3).
    { intros c Hcs N2 N8. rewrite /R3 upd_ne; [| regne].
      exact (HR2thr c Hcs N2 N8). }
    assert (Hpp0c : add_vec_int (mword_of_int (NM + 0x08) : mword 64) 4
                    = mword_of_int (NM + 0x0c)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    (* ===== +0x0c c.li a1,0 : nameiparent = 0 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (NM + 0x0c)) Ra1
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              R3 (K - 4)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (nmi_0c with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (R4 := <[Regidx Ra1 := regval_into_reg (mword_of_int 0 : mword 64)]> R3).
    assert (HR4a1 : (R4 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /R4; apply upd_eq).
    assert (HR4a2 : (R4 !!! Regidx Ra2 : mword 64) = pa_stk sp0 4)
      by (rewrite /R4 upd_ne; [exact HR3a2 | nz]).
    assert (HR4a0 : (R4 !!! Regidx Ra0 : mword 64) = pv)
      by (rewrite /R4 upd_ne; [exact HR3a0 | nz]).
    assert (HR4ra : (R4 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3ra | nz]).
    assert (HR4sp : nam_sp m R4)
      by (rewrite /nam_sp /R4 upd_ne; [exact HR3sp | nz]).
    assert (HR4thr : nam_thr m R4).
    { intros c Hcs N2 N8. rewrite /R4 upd_ne; [| regne].
      exact (HR3thr c Hcs N2 N8). }
    assert (Hpp0e : add_vec_int (mword_of_int (NM + 0x0c) : mword 64) 2
                    = mword_of_int (NM + 0x0e)) by pcw.
    iEval (rewrite Hpp0e) in "Hpc".
    (* ===== +0x0e jal ra,namex ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (NM + 0x0e)) Rra
              (mword_of_int 2096634 : mword 21) R4 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (nmi_0e with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (R5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (NM + 0x0e) : mword 64) 4)]> R4).
    assert (Htgt : add_vec (mword_of_int (NM + 0x0e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096634 : mword 21))
                   = mword_of_int KernelSyms.namex) by pcw.
    iEval (rewrite Htgt) in "Hpc".
    assert (HR5a1 : (R5 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /R5 upd_ne; [exact HR4a1 | nz]).
    assert (HR5a2 : (R5 !!! Regidx Ra2 : mword 64) = pa_stk sp0 4)
      by (rewrite /R5 upd_ne; [exact HR4a2 | nz]).
    assert (HR5a0 : (R5 !!! Regidx Ra0 : mword 64) = pv)
      by (rewrite /R5 upd_ne; [exact HR4a0 | nz]).
    assert (HR5sp : nam_sp m R5)
      by (rewrite /nam_sp /R5 upd_ne; [exact HR4sp | nz]).
    assert (HR5ra : (R5 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (NM + 0x0e) : mword 64) 4)
      by (rewrite /R5; apply upd_eq).
    assert (HR5thr : nam_thr m R5).
    { intros c Hcs N2 N8. rewrite /R5 upd_ne; [| regne].
      exact (HR4thr c Hcs N2 N8). }
    (* the path and the carved buffer, re-addressed at namex's own registers *)
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
    iApply (NX.wp_namex_tr gs j gl gu gd gk pd pav pu bn
              ga gf bmapstart size
              plen pfun nfun n Sb P Pmiss pidv dq dqb dqs dqpv R5 (K - 4)%nat eb b
              _ Vpr Knx Hroot Hnib0 Hlg Hsize Hbmap0 Hbmapcov
              Hbmaplog Hinos0 Hcovb Hiregb Hcstr Hplen Hpfun0 Hbud Hj Hgs
              ltac:(rewrite HR5a1; exact nami_a1_true)
              with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio Hlogc Hkenv Hitb2 Hitbl
                    Hesc Hslks Hireg Hropen Hprocs Hdev Hgeom Hdlk Hbmap Hinos
                    Hbits Hppid Hcwdr Hpath Hname Hbslot Hislot Hlog HP0 Hhops0").
    all: try lkbelow.
    iIntros (CID8 Hq8 mf n' Sb' ok nf ipv w)
            "%Hcs Hcg Hcnt Hextc Hclmc Hpc Hbmap Hinos Hppid Hcwdr
             Hpath Hname Hbslot %Hssub %Hwbm %Hbudo Hlog Hok".
    iEval (rewrite HR5a0) in "Hpath".
    iEval (rewrite HR5a2) in "Hname".
    (* THE CARVE, UNDONE: fourteen written bytes plus the two spare ones are
       the two frame words again *)
    iDestruct (nam_buf_join (pa_stk sp0 4) nfun nf with "Hname Htail") as "Hbytes".
    iDestruct (nam_bytes_slots sp0 Hal4 Hal3 with "Hbytes") as (w1 w2) "[Hf4 Hf3]".
    assert (Hpc12 : ret_pc (R5 !!! Regidx Rra : mword 64)
                    = mword_of_int (NM + 0x12)) by (rewrite HR5ra; pcw).
    iEval (rewrite Hpc12) in "Hpc".
    pose proof Hcs as Hcs_cs.
    assert (Hmfsp : nam_sp m mf).
    { rewrite /nam_sp
        (callee_saved_lookup Hcs_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HR5sp. }
    assert (Hmfthr : nam_thr m mf).
    { intros c Hcs2 N2 N8.
      rewrite (callee_saved_lookup Hcs_cs c Hcs2).
      exact (HR5thr c Hcs2 N2 N8). }
    (* ===== +0x12 .. +0x14 : the two restores ===== *)
    assert (Hc1 : add_vec (mf !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite Hmfsp; apply nam_frm1).
    assert (Hc2 : add_vec (mf !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite Hmfsp; apply nam_frm2).
    iApply (wp_cldsp_s_sconf (mword_of_int (NM + 0x12))
              (mword_of_int 3 : mword 6) Rra mf (K - 4)%nat
              (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf1]").
    { iApply (nmi_12 with "Htext"). }
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID9 Hq9) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> mf).
    assert (HP1sp : nam_sp m P1)
      by (rewrite /nam_sp /P1 upd_ne; [exact Hmfsp | nz]).
    assert (HP1thr : nam_thr m P1).
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
              with "Hcg Hpc [] [Hf2]").
    { iApply (nmi_14 with "Htext"). }
    { iEval (rewrite HP1sp -Hmfsp Hc2). iExact "Hf2". }
    iIntros (CID10 Hq10) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -Hmfsp Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : nam_sp m P2)
      by (rewrite /nam_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : nam_thr m P2).
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
    assert (Hpop : (P2 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P2 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv HP2sp; reflexivity).
    iAssert (stack_own (KTR := KT1) sp0 4) with "[Hf1 Hf2 Hf3 Hf4]" as "Hstk".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hf1"; [iExists _; iExact "Hf1" |].
      iSplitL "Hf2"; [iExists _; iExact "Hf2" |].
      iSplitL "Hf3"; [iExists _; iExact "Hf3" |].
      iSplitL "Hf4"; [iExists _; iExact "Hf4" |].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (NM + 0x16))
              (mword_of_int 2 : mword 6) P2 (K - 4)%nat 4 b Hpop
              with "Hcg Hpc [] Hstk").
    { iApply (nmi_16 with "Htext"). }
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
              ltac:(nz) with "Hcg Hpc []").
    { iApply (nmi_18 with "Htext"). }
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
    assert (Hfin : nam_thr m P3).
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
    (* the two arms, re-stated at the FINAL register file.  The pin and the
       failure receipt ride through UNTOUCHED -- this wrapper writes no
       directory byte and fires no hop, so all it does is move the register
       equation from [mf] to [P3]. *)
    iAssert (if ok
             then ∃ iL : Z,
                    ⌜(P3 !!! Regidx Ra0 : mword 64) = ipv⌝ ∗
                    inode_held_at ipv iL ∗ P L iL ∗ iref_slots 1
             else ⌜(P3 !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64)⌝ ∗
                  iref_slots 2 ∗
                  (∃ (k : nat) (d : Z), ⌜(k < L)%nat⌝ ∗
                     ((P k d ∗ nx_hops_from P Pmiss pl k) ∨
                      (Pmiss k d ∗ nx_hops_from P Pmiss pl (S k)))))%I
      with "[Hok]" as "Hok".
    { destruct ok.
      - iDestruct "Hok" as (iL) "[%Hp [Hheld [HPL Hsl]]]".
        iExists iL. iFrame "Hheld HPL Hsl".
        iPureIntro. rewrite HP3a0. exact Hp.
      - iDestruct "Hok" as "[%Hp [Hsl Hrec]]". iFrame "Hsl Hrec".
        iPureIntro. rewrite HP3a0. exact Hp. }
    iDestruct (cpu_own_transport CID8 CID12 0%nat eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID8 CID12 eb (proc_addr j)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID8 CID12 eb (proc_addr j)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iSpecialize ("Hcont" $! CID12 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! P3 n' Sb' ok ipv w
              with "[%] Hcg Hcnt Hextc Hclmc Hpc Hbmap Hinos Hppid Hcwdr
                    Hpath Hbslot [%] [%] [%] Hlog Hok").
    { unfold callee_saved. split_and!; assumption. }
    { exact Hssub. }
    { exact Hwbm. }
    { exact Hbudo. }
  Qed.

End ProofNameiTrMain.

End NameiTrProof.
