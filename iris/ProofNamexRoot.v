(* ProofNamexRoot.v -- namex's ROOT CORNER: [namex("/", 0, name)].

   The regime is the one [SpecNamex.wp_namex_root_body]'s header describes:
   a path of exactly one '/' has no elements, so [skipelem] returns 0 on its
   first call and the walk's body never runs.  What executes is a straight
   line of fifty-two instructions with ONE call in it:

     +0x000            c.addi16sp sp,-96          (12-slot frame)
     +0x002 .. +0x018  the twelve saves (ra, s0..s10)
     +0x01a            c.addi4spn s0,sp,96
     +0x01c .. +0x020  s1 = path, s6 = nameiparent, s5 = name
     +0x022            lbu a4,0(a0)               path[0]
     +0x026            li  a5,47
     +0x02a            beq a4,a5,+0x48            TAKEN  ('/' -> absolute)
     +0x048 .. +0x04c  a1 = 1; a0 = a1; jal iget  == iget(ROOTDEV, ROOTINO)
     +0x050 .. +0x052  s4 = a0; j +0x3c
     +0x03c .. +0x044  s3 = 47, s8 = 13, s9 = 14, s7 = 1
     +0x046            j +0xf4                    into the walk's test
     +0x0f4            lbu a5,0(s1)               path[0], again
     +0x0f8            bne a5,s3,+0x106           FALLS  (it is '/')
     +0x0fc            c.addi s1,s1,1
     +0x0fe            lbu a5,0(s1)               path[1] = NUL
     +0x102            beq a5,s3,+0xfc            FALLS  (NUL is not '/')
     +0x106            c.beqz a5,+0x140           TAKEN  (it IS the NUL)
     +0x140            beq s6,zero,+0x5c          TAKEN  (nameiparent = 0)
     +0x05c .. +0x078  a0 = s4, the twelve restores, the pop and [c.jr ra]

   So this proof takes exactly ONE functor argument, [IGET], and touches no
   resource but the inode cache and the two path bytes.  Everything the walk
   needs and this does not -- the log, the bio cache, the inode region, the
   bitmap, the disk lock, the running process -- is absent from the
   statement, which is the whole point of the corner (see the header of
   [SpecNamex.wp_namex_root_body]).

   RELATION TO [ProofNamex.v].  The prologue, the [beq] arm split, the iget
   call and the shared epilogue are the same code, and the pure facts they
   rest on -- the frame displacements ([ProofDirlookupParts.dlk_*],
   [ProofNamexParts.nx_frm10..12]) and the four byte tests
   ([ProofNamexParts.nx_slash_eq] and friends) -- are read from the two PURE
   parts files rather than restated here; the byte tests were moved into
   [ProofNamexParts.v] for exactly that reason.  What is not shared is the
   proof SCRIPT of the prologue and epilogue: they live inside
   [ProofNamex.wp_namex_gen]'s own [iAssert]ed continuation, which is
   anchored at the running process's [proc_addr j] and at the literal [true]
   crossing a parking walk needs, and neither holds here. *)
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
Require Import RegFile WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfVc.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FsBlocks LogInv.
Require Import DiskPtsto.
Require Import DirentEnc.
Require Import PathElems.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheEscrow.
Require Import ProofDirlookupParts.
Require Import ProofNamexParts.
Require Import CodeNamex.
Require Import SpecIget.
Require Import SpecNamex.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* K_namex_root's single premise, in the three forms the call and the two
   [sie_cap_gpr] carves want. *)
Lemma nxr_kb (K : nat) : (K_namex_root <= K)%nat ->
  (K_iget <= K - 12)%nat /\ (12 <= K)%nat /\ ((K - 12) + 12 = K)%nat.
Proof. unfold K_namex_root, K_iget. intro H. split_and!; lia. Qed.

Module NamexRootProof (IG : IGET) : NAMEX_ROOT.

Notation NX := KernelSyms.namex (only parsing).

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.

Section ProofNamexRoot.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, ICFG : icfg, !icacheG Σ, !logG Σ,
            !irefslotG Σ, !pavG Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Rs8 := (mword_of_int 24 : mword 5).
  Notation Rs9 := (mword_of_int 25 : mword 5).
  Notation Rs10 := (mword_of_int 26 : mword 5).

  Lemma wp_namex_root
      (gtl : gname) (cn : ic_names) (gfs : fs_names) (gi : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) (dev : mword 32)
      (dqp : dfrac)
      (m : regfile) (n K : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string)
    : wp_namex_root_body gtl cn gfs gi cov logstart nib dev dqp
                         m n K eb p b lks.
  Proof.
    cbv beta delta [wp_namex_root_body].
    intros pcE pv ret_tgt HK Hn Hdev Hnib Hroot Hnib0 Ha1 Hbelow.
    destruct (nxr_kb K HK) as (Kig & K12 & Kpop).
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hitb2 #Hitbl #Hesc Hisl Hp0 Hp1 Hcont".
    iPoseProof (nxi_000 with "Htext") as "Hi000".
    iPoseProof (nxi_002 with "Htext") as "Hi002".
    iPoseProof (nxi_004 with "Htext") as "Hi004".
    iPoseProof (nxi_006 with "Htext") as "Hi006".
    iPoseProof (nxi_008 with "Htext") as "Hi008".
    iPoseProof (nxi_00a with "Htext") as "Hi00a".
    iPoseProof (nxi_00c with "Htext") as "Hi00c".
    iPoseProof (nxi_00e with "Htext") as "Hi00e".
    iPoseProof (nxi_010 with "Htext") as "Hi010".
    iPoseProof (nxi_012 with "Htext") as "Hi012".
    iPoseProof (nxi_014 with "Htext") as "Hi014".
    iPoseProof (nxi_016 with "Htext") as "Hi016".
    iPoseProof (nxi_018 with "Htext") as "Hi018".
    iPoseProof (nxi_01a with "Htext") as "Hi01a".
    iPoseProof (nxi_01c with "Htext") as "Hi01c".
    iPoseProof (nxi_01e with "Htext") as "Hi01e".
    iPoseProof (nxi_020 with "Htext") as "Hi020".
    iPoseProof (nxi_022 with "Htext") as "Hi022".
    iPoseProof (nxi_026 with "Htext") as "Hi026".
    iPoseProof (nxi_02a with "Htext") as "Hi02a".
    iPoseProof (nxi_048 with "Htext") as "Hi048".
    iPoseProof (nxi_04a with "Htext") as "Hi04a".
    iPoseProof (nxi_04c with "Htext") as "Hi04c".
    iPoseProof (nxi_050 with "Htext") as "Hi050".
    iPoseProof (nxi_052 with "Htext") as "Hi052".
    iPoseProof (nxi_03c with "Htext") as "Hi03c".
    iPoseProof (nxi_040 with "Htext") as "Hi040".
    iPoseProof (nxi_042 with "Htext") as "Hi042".
    iPoseProof (nxi_044 with "Htext") as "Hi044".
    iPoseProof (nxi_046 with "Htext") as "Hi046".
    iPoseProof (nxi_0f4 with "Htext") as "Hi0f4".
    iPoseProof (nxi_0f8 with "Htext") as "Hi0f8".
    iPoseProof (nxi_0fc with "Htext") as "Hi0fc".
    iPoseProof (nxi_0fe with "Htext") as "Hi0fe".
    iPoseProof (nxi_102 with "Htext") as "Hi102".
    iPoseProof (nxi_106 with "Htext") as "Hi106".
    iPoseProof (nxi_140 with "Htext") as "Hi140".
    iPoseProof (nxi_05c with "Htext") as "Hi05c".
    iPoseProof (nxi_05e with "Htext") as "Hi05e".
    iPoseProof (nxi_060 with "Htext") as "Hi060".
    iPoseProof (nxi_062 with "Htext") as "Hi062".
    iPoseProof (nxi_064 with "Htext") as "Hi064".
    iPoseProof (nxi_066 with "Htext") as "Hi066".
    iPoseProof (nxi_068 with "Htext") as "Hi068".
    iPoseProof (nxi_06a with "Htext") as "Hi06a".
    iPoseProof (nxi_06c with "Htext") as "Hi06c".
    iPoseProof (nxi_06e with "Htext") as "Hi06e".
    iPoseProof (nxi_070 with "Htext") as "Hi070".
    iPoseProof (nxi_072 with "Htext") as "Hi072".
    iPoseProof (nxi_074 with "Htext") as "Hi074".
    iPoseProof (nxi_076 with "Htext") as "Hi076".
    iPoseProof (nxi_078 with "Htext") as "Hi078".
    (* the path's first byte is at [pv] itself *)
    iEval (rewrite pa_add_0) in "Hp0".
    (* ===== +0x000 c.addi16sp sp,-96 : the 12-slot frame ===== *)
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 12) by apply dlk_push.
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 58 : mword 6) m K 12 b
              K12 Hpush with "Hcg Hpc Hi000").
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    pose (R1 := <[Regidx csp_rs1 := regval_into_reg
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
    iDestruct "S9" as (u9) "Hb9". iDestruct "S10" as (u10) "Hb10".
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
    assert (Hf10 : add_vec (R1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                   = pa_stk sp0 10) by (rewrite HR1sp; apply nx_frm10).
    assert (Hf11 : add_vec (R1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 11) by (rewrite HR1sp; apply nx_frm11).
    assert (Hf12 : add_vec (R1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk sp0 12) by (rewrite HR1sp; apply nx_frm12).
    iEval (rewrite -Hf1) in "Hb1".   iEval (rewrite -Hf2) in "Hb2".
    iEval (rewrite -Hf3) in "Hb3".   iEval (rewrite -Hf4) in "Hb4".
    iEval (rewrite -Hf5) in "Hb5".   iEval (rewrite -Hf6) in "Hb6".
    iEval (rewrite -Hf7) in "Hb7".   iEval (rewrite -Hf8) in "Hb8".
    iEval (rewrite -Hf9) in "Hb9".   iEval (rewrite -Hf10) in "Hb10".
    iEval (rewrite -Hf11) in "Hb11". iEval (rewrite -Hf12) in "Hb12".
    assert (Hpp002 : add_vec_int (pcE : mword 64) 2 = mword_of_int (NX + 0x2)) by pcw.
    iEval (rewrite Hpp002) in "Hpc".
    assert (HR1o : forall c : mword 5, c <> csp_rs1 ->
                     R1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc. rewrite /R1 upd_ne;
        [reflexivity
        | intro Hq; apply Hc;
          first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ]]. }
    (* ===== +0x002 .. +0x018 : the TWELVE saves ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x2)) (mword_of_int 11 : mword 6)
              Rra R1 (K - 12)%nat u1 b with "Hcg Hpc Hi002 Hb1").
    iIntros (CID2 Hq2) "Hcg Hpc Hb1".
    iEval (rgne; rewrite (HR1o Rra ltac:(nz)) Hf1) in "Hb1".
    assert (Hpp004 : add_vec_int (mword_of_int (NX + 0x2) : mword 64) 2
                     = mword_of_int (NX + 0x4)) by pcw.
    iEval (rewrite Hpp004) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x4)) (mword_of_int 10 : mword 6)
              Rs0 R1 (K - 12)%nat u2 b with "Hcg Hpc Hi004 Hb2").
    iIntros (CID3 Hq3) "Hcg Hpc Hb2".
    iEval (rgne; rewrite (HR1o Rs0 ltac:(nz)) Hf2) in "Hb2".
    assert (Hpp006 : add_vec_int (mword_of_int (NX + 0x4) : mword 64) 2
                     = mword_of_int (NX + 0x6)) by pcw.
    iEval (rewrite Hpp006) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x6)) (mword_of_int 9 : mword 6)
              Rs1 R1 (K - 12)%nat u3 b with "Hcg Hpc Hi006 Hb3").
    iIntros (CID4 Hq4) "Hcg Hpc Hb3".
    iEval (rgne; rewrite (HR1o Rs1 ltac:(nz)) Hf3) in "Hb3".
    assert (Hpp008 : add_vec_int (mword_of_int (NX + 0x6) : mword 64) 2
                     = mword_of_int (NX + 0x8)) by pcw.
    iEval (rewrite Hpp008) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x8)) (mword_of_int 8 : mword 6)
              Rs2 R1 (K - 12)%nat u4 b with "Hcg Hpc Hi008 Hb4").
    iIntros (CID5 Hq5) "Hcg Hpc Hb4".
    iEval (rgne; rewrite (HR1o Rs2 ltac:(nz)) Hf4) in "Hb4".
    assert (Hpp00a : add_vec_int (mword_of_int (NX + 0x8) : mword 64) 2
                     = mword_of_int (NX + 0xa)) by pcw.
    iEval (rewrite Hpp00a) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0xa)) (mword_of_int 7 : mword 6)
              Rs3 R1 (K - 12)%nat u5 b with "Hcg Hpc Hi00a Hb5").
    iIntros (CID6 Hq6) "Hcg Hpc Hb5".
    iEval (rgne; rewrite (HR1o Rs3 ltac:(nz)) Hf5) in "Hb5".
    assert (Hpp00c : add_vec_int (mword_of_int (NX + 0xa) : mword 64) 2
                     = mword_of_int (NX + 0xc)) by pcw.
    iEval (rewrite Hpp00c) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0xc)) (mword_of_int 6 : mword 6)
              Rs4 R1 (K - 12)%nat u6 b with "Hcg Hpc Hi00c Hb6").
    iIntros (CID7 Hq7) "Hcg Hpc Hb6".
    iEval (rgne; rewrite (HR1o Rs4 ltac:(nz)) Hf6) in "Hb6".
    assert (Hpp00e : add_vec_int (mword_of_int (NX + 0xc) : mword 64) 2
                     = mword_of_int (NX + 0xe)) by pcw.
    iEval (rewrite Hpp00e) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0xe)) (mword_of_int 5 : mword 6)
              Rs5 R1 (K - 12)%nat u7 b with "Hcg Hpc Hi00e Hb7").
    iIntros (CID8 Hq8) "Hcg Hpc Hb7".
    iEval (rgne; rewrite (HR1o Rs5 ltac:(nz)) Hf7) in "Hb7".
    assert (Hpp010 : add_vec_int (mword_of_int (NX + 0xe) : mword 64) 2
                     = mword_of_int (NX + 0x10)) by pcw.
    iEval (rewrite Hpp010) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x10)) (mword_of_int 4 : mword 6)
              Rs6 R1 (K - 12)%nat u8 b with "Hcg Hpc Hi010 Hb8").
    iIntros (CID9 Hq9) "Hcg Hpc Hb8".
    iEval (rgne; rewrite (HR1o Rs6 ltac:(nz)) Hf8) in "Hb8".
    assert (Hpp012 : add_vec_int (mword_of_int (NX + 0x10) : mword 64) 2
                     = mword_of_int (NX + 0x12)) by pcw.
    iEval (rewrite Hpp012) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x12)) (mword_of_int 3 : mword 6)
              Rs7 R1 (K - 12)%nat u9 b with "Hcg Hpc Hi012 Hb9").
    iIntros (CID10 Hq10) "Hcg Hpc Hb9".
    iEval (rgne; rewrite (HR1o Rs7 ltac:(nz)) Hf9) in "Hb9".
    assert (Hpp014 : add_vec_int (mword_of_int (NX + 0x12) : mword 64) 2
                     = mword_of_int (NX + 0x14)) by pcw.
    iEval (rewrite Hpp014) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x14)) (mword_of_int 2 : mword 6)
              Rs8 R1 (K - 12)%nat u10 b with "Hcg Hpc Hi014 Hb10").
    iIntros (CID11 Hq11) "Hcg Hpc Hb10".
    iEval (rgne; rewrite (HR1o Rs8 ltac:(nz)) Hf10) in "Hb10".
    assert (Hpp016 : add_vec_int (mword_of_int (NX + 0x14) : mword 64) 2
                     = mword_of_int (NX + 0x16)) by pcw.
    iEval (rewrite Hpp016) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x16)) (mword_of_int 1 : mword 6)
              Rs9 R1 (K - 12)%nat u11 b with "Hcg Hpc Hi016 Hb11").
    iIntros (CID12 Hq12) "Hcg Hpc Hb11".
    iEval (rgne; rewrite (HR1o Rs9 ltac:(nz)) Hf11) in "Hb11".
    assert (Hpp018 : add_vec_int (mword_of_int (NX + 0x16) : mword 64) 2
                     = mword_of_int (NX + 0x18)) by pcw.
    iEval (rewrite Hpp018) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x18)) (mword_of_int 0 : mword 6)
              Rs10 R1 (K - 12)%nat u12 b with "Hcg Hpc Hi018 Hb12").
    iIntros (CID13 Hq13) "Hcg Hpc Hb12".
    iEval (rgne; rewrite (HR1o Rs10 ltac:(nz)) Hf12) in "Hb12".
    assert (Hpp01a : add_vec_int (mword_of_int (NX + 0x18) : mword 64) 2
                     = mword_of_int (NX + 0x1a)) by pcw.
    iEval (rewrite Hpp01a) in "Hpc".
    (* ===== +0x01a c.addi4spn s0,sp,96 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (NX + 0x1a))
              (Cregidx (mword_of_int 0)) (mword_of_int 24 : mword 8) Rs0
              R1 (K - 12)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi01a").
    iIntros (CID14 Hq14) "Hcg Hpc".
    pose (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))))]> R1).
    assert (HR2s0 : R2 !!! Regidx Rs0 = sp0).
    { rewrite /R2 upd_eq. rewrite HR1sp. apply dlk_fp. }
    assert (HR2sp : R2 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2c : forall c : mword 5, c <> csp_rs1 -> c <> Rs0 ->
                     R2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c N2 N8. rewrite /R2 upd_ne;
        [ exact (HR1o c N2)
        | intro Hq; apply N8;
          first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ]]. }
    assert (Hpp01c : add_vec_int (mword_of_int (NX + 0x1a) : mword 64) 2
                     = mword_of_int (NX + 0x1c)) by pcw.
    iEval (rewrite Hpp01c) in "Hpc".
    (* ===== +0x01c c.mv s1,a0 ===== *)
    assert (HR2a0 : R2 !!! Regidx Ra0 = pv)
      by exact (HR2c Ra0 ltac:(nz) ltac:(nz)).
    assert (HR2a1 : R2 !!! Regidx Ra1 = (m !!! Regidx Ra1 : mword 64))
      by exact (HR2c Ra1 ltac:(nz) ltac:(nz)).
    iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x1c)) Rs1 Ra0 R2 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi01c").
    iIntros (CID15 Hq15) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (R3 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R2 !!! Regidx Ra0))]> R2).
    assert (HR3s1 : R3 !!! Regidx Rs1 = pv).
    { rewrite /R3 upd_eq. rewrite HR2a0. apply add_vec_zero_l. }
    assert (Hpp01e : add_vec_int (mword_of_int (NX + 0x1c) : mword 64) 2
                     = mword_of_int (NX + 0x1e)) by pcw.
    iEval (rewrite Hpp01e) in "Hpc".
    (* ===== +0x01e c.mv s6,a1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x1e)) Rs6 Ra1 R3 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi01e").
    iIntros (CID16 Hq16) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (R4 := <[Regidx Rs6 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R3 !!! Regidx Ra1))]> R3).
    assert (HR3a1 : R3 !!! Regidx Ra1 = (m !!! Regidx Ra1 : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2a1 | nz]).
    assert (HR4s6 : R4 !!! Regidx Rs6 = (zero_reg : mword 64)).
    { rewrite /R4 upd_eq. rewrite HR3a1 Ha1. apply add_vec_zero_l. }
    assert (Hpp020 : add_vec_int (mword_of_int (NX + 0x1e) : mword 64) 2
                     = mword_of_int (NX + 0x20)) by pcw.
    iEval (rewrite Hpp020) in "Hpc".
    (* ===== +0x020 c.mv s5,a2 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x20)) Rs5 Ra2 R4 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi020").
    iIntros (CID17 Hq17) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (R5 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R4 !!! Regidx Ra2))]> R4).
    assert (Hpp022 : add_vec_int (mword_of_int (NX + 0x20) : mword 64) 2
                     = mword_of_int (NX + 0x22)) by pcw.
    iEval (rewrite Hpp022) in "Hpc".
    (* ===== +0x022 lbu a4,0(a0) : the first path byte ===== *)
    assert (HR5a0 : R5 !!! Regidx Ra0 = pv).
    { rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [exact HR2a0 | nz]. }
    iApply (wp_lbu_s_sconf (mword_of_int (NX + 0x22)) Ra4 Ra0
              (mword_of_int 0 : mword 12) R5 (K - 12)%nat SLASH b (dqm := dqp)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi022 [Hp0]").
    { iEval (rgne; rewrite HR5a0 addv_sext0). iExact "Hp0". }
    iIntros (CID18 Hq18) "Hcg Hpc Hp0".
    iEval (rgne; rewrite HR5a0 addv_sext0) in "Hp0".
    pose (R6 := <[Regidx Ra4 := regval_into_reg
                  (zero_extend' 64 (SLASH : mword 8))]> R5).
    assert (HR6a4 : R6 !!! Regidx Ra4
                    = (zero_extend' 64 (SLASH : mword 8) : mword 64))
      by (rewrite /R6; apply upd_eq).
    assert (Hpp026 : add_vec_int (mword_of_int (NX + 0x22) : mword 64) 4
                     = mword_of_int (NX + 0x26)) by pcw.
    iEval (rewrite Hpp026) in "Hpc".
    (* ===== +0x026 li a5,47 ===== *)
    iApply (wp_li4_s_sconf (mword_of_int (NX + 0x26)) Ra5
              (mword_of_int 47 : mword 12) (mword_of_int 47 : mword 64)
              R6 (K - 12)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi026").
    iIntros (CID19 Hq19) "Hcg Hpc".
    pose (R7 := <[Regidx Ra5 := regval_into_reg (mword_of_int 47 : mword 64)]> R6).
    assert (HR7a5 : R7 !!! Regidx Ra5 = (mword_of_int 47 : mword 64))
      by (rewrite /R7; apply upd_eq).
    assert (HR7a4 : R7 !!! Regidx Ra4
                    = (zero_extend' 64 (SLASH : mword 8) : mword 64))
      by (rewrite /R7 upd_ne; [exact HR6a4 | nz]).
    assert (HR7s1 : R7 !!! Regidx Rs1 = pv).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [exact HR3s1 | nz]. }
    assert (HR7s6 : R7 !!! Regidx Rs6 = (zero_reg : mword 64)).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [exact HR4s6 | nz]. }
    assert (HR7s0 : R7 !!! Regidx Rs0 = sp0).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [exact HR2s0 | nz]. }
    assert (HR7sp : R7 !!! Regidx csp_rs1 = pa_stk sp0 12).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [exact HR2sp | nz]. }
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
    assert (Hcsa4 : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
    assert (Hcsa5 : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
    assert (HR7o : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 -> c <> Rs8 ->
              c <> Rs9 -> c <> Rs10 ->
              R7 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
      rewrite /R7 upd_ne; [| dlk_rne2 Hcsa5 Hc].
      rewrite /R6 upd_ne; [| dlk_rne2 Hcsa4 Hc].
      rewrite /R5 upd_ne; [| dlk_xne N21].
      rewrite /R4 upd_ne; [| dlk_xne N22].
      rewrite /R3 upd_ne; [| dlk_xne N9].
      exact (HR2c c N2 N8). }
    assert (Hpp02a : add_vec_int (mword_of_int (NX + 0x26) : mword 64) 4
                     = mword_of_int (NX + 0x2a)) by pcw.
    iEval (rewrite Hpp02a) in "Hpc".
    (* ===== +0x02a beq a4,a5 : TAKEN, the path is absolute ===== *)
    assert (Htgt048 : add_vec (mword_of_int (NX + 0x2a) : mword 64)
              (sign_extend' 64 (mword_of_int 30 : mword 13))
              = mword_of_int (NX + 0x48)) by pcw.
    iApply (wp_beq_taken_s_sconf (mword_of_int (NX + 0x2a))
              (mword_of_int 30 : mword 13) Ra5 Ra4 R7 (K - 12)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HR7a4 HR7a5;
                    exact (nx_slash_eq SLASH eq_refl))
              ltac:(rewrite Htgt048; vm_compute; reflexivity)
              with "Hcg Hpc Hi02a").
    iIntros (CID20 Hq20). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htgt048) in "Hpc".
    (* ===== +0x048 c.li a1,1 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (NX + 0x48)) Ra1 (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) R7 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi048").
    iIntros (CID21 Hq21) "Hcg Hpc".
    pose (A1 := <[Regidx Ra1 := regval_into_reg (mword_of_int 1 : mword 64)]> R7).
    assert (HA1a1 : A1 !!! Regidx Ra1 = (mword_of_int 1 : mword 64))
      by (rewrite /A1; apply upd_eq).
    assert (Hpp04a : add_vec_int (mword_of_int (NX + 0x48) : mword 64) 2
                     = mword_of_int (NX + 0x4a)) by pcw.
    iEval (rewrite Hpp04a) in "Hpc".
    (* ===== +0x04a c.mv a0,a1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x4a)) Ra0 Ra1 A1 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi04a").
    iIntros (CID22 Hq22) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (A2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (A1 !!! Regidx Ra1))]> A1).
    assert (HA2a0 : A2 !!! Regidx Ra0 = (mword_of_int 1 : mword 64)).
    { rewrite /A2 upd_eq. rewrite HA1a1. apply add_vec_zero_l. }
    assert (HA2a1 : A2 !!! Regidx Ra1 = (mword_of_int 1 : mword 64))
      by (rewrite /A2 upd_ne; [exact HA1a1 | nz]).
    assert (Hpp04c : add_vec_int (mword_of_int (NX + 0x4a) : mword 64) 2
                     = mword_of_int (NX + 0x4c)) by pcw.
    iEval (rewrite Hpp04c) in "Hpc".
    (* ===== +0x04c jal ra,iget ===== *)
    assert (Htgtig : add_vec (mword_of_int (NX + 0x4c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094538 : mword 21))
                     = mword_of_int KernelSyms.iget) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (NX + 0x4c)) Rra
              (mword_of_int 2094538 : mword 21) A2 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi04c").
    iIntros (CID23 Hq23) "Hcg Hpc".
    iEval (rewrite Htgtig) in "Hpc".
    pose (A3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (NX + 0x4c) : mword 64) 4)]> A2).
    assert (HA3ra : A3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (NX + 0x4c) : mword 64) 4)
      by (rewrite /A3; apply upd_eq).
    assert (HA3a0 : A3 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64)).
    { rewrite /A3 upd_ne; [| nz]. rewrite HA2a0 Hroot.
      unfold ROOTDEV. pcw. }
    assert (HA3a1 : A3 !!! Regidx Ra1 = (sign_extend' 64 ROOTINO : mword 64)).
    { rewrite /A3 upd_ne; [| nz]. rewrite HA2a1. unfold ROOTINO. pcw. }
    assert (Hrino : bv_unsigned ROOTINO < 16 * Z.of_nat nib).
    { unfold ROOTINO.
      assert (Hu : bv_unsigned (mword_of_int 1 : mword 32) = 1)
        by (vm_compute; reflexivity).
      rewrite Hu. assert (Hnz : 1 <= Z.of_nat nib) by lia. lia. }
    iDestruct (cpu_own_transport CID CID23 n eb p b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := b) (CIDa := CID) (CIDb := CID23)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (IG.wp_iget_sconf gtl cn gfs gi cov logstart nib dev ROOTINO
              A3 n eb p (K - 12)%nat b lks
              Kig Hn Hrino HA3a0 HA3a1 Hbelow
              with "Hcg Hcnt Htext Hpc Hitb2 Hitbl Hesc Hpanic Hisl").
    iIntros (CIDig Hqig mig kig qig) "Hcg Hcnt Hpc %Higp Href".
    destruct Higp as (Hcsig & Hkig & Higa0).
    assert (Hpc050 : ret_pc (A3 !!! Regidx Rra) = mword_of_int (NX + 0x50)).
    { rewrite HA3ra. pcw. }
    iEval (rewrite Hpc050) in "Hpc".
    (* the answer, in the currency the contract speaks *)
    iAssert (inode_held (ientry kig)) with "[Href]" as "Hip".
    { rewrite /inode_held. iExists kig, qig, ROOTINO.
      iSplitR; [done |]. iSplitR; [iPureIntro; exact Hkig |].
      iSplitR; [iPureIntro; rewrite -Hnib; exact Hrino |].
      rewrite -Hdev. iExact "Href". }
    (* ===== +0x050 c.mv s4,a0 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x50)) Rs4 Ra0 mig (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi050").
    iIntros (CIDA1 HqA1) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (A4 := <[Regidx Rs4 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mig !!! Regidx Ra0))]> mig).
    assert (HA4s4 : A4 !!! Regidx Rs4 = ientry kig).
    { rewrite /A4 upd_eq. rewrite Higa0. apply add_vec_zero_l. }
    assert (Hpp052 : add_vec_int (mword_of_int (NX + 0x50) : mword 64) 2
                     = mword_of_int (NX + 0x52)) by pcw.
    iEval (rewrite Hpp052) in "Hpc".
    (* ===== +0x052 c.j +0x3c ===== *)
    assert (Htgt03c : add_vec (mword_of_int (NX + 0x52) : mword 64)
              (sign_extend' 64 (sign_extend' 21
                 (concat_vec (mword_of_int 2037 : mword 11) ('b"0"))))
              = mword_of_int (NX + 0x3c)) by pcw.
    iApply (wp_cj_s_sconf (mword_of_int (NX + 0x52))
              (sign_extend' 21 (concat_vec (mword_of_int 2037 : mword 11) ('b"0")))
              A4 (K - 12)%nat b
              ltac:(rewrite Htgt03c; vm_compute; reflexivity)
              with "Hcg Hpc Hi052").
    iIntros (CIDA2 HqA2). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htgt03c) in "Hpc".
    (* ---- the register facts iget's [callee_saved] carries over ---- *)
    assert (HA4sp : A4 !!! Regidx csp_rs1 = pa_stk sp0 12).
    { rewrite /A4 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsig csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /A3 upd_ne; [| nz]. rewrite /A2 upd_ne; [| nz].
      rewrite /A1 upd_ne; [exact HR7sp | nz]. }
    assert (HA4s0 : A4 !!! Regidx Rs0 = sp0).
    { rewrite /A4 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsig Rs0 ltac:(vm_compute; reflexivity)).
      rewrite /A3 upd_ne; [| nz]. rewrite /A2 upd_ne; [| nz].
      rewrite /A1 upd_ne; [exact HR7s0 | nz]. }
    assert (HA4s1 : A4 !!! Regidx Rs1 = pv).
    { rewrite /A4 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsig Rs1 ltac:(vm_compute; reflexivity)).
      rewrite /A3 upd_ne; [| nz]. rewrite /A2 upd_ne; [| nz].
      rewrite /A1 upd_ne; [exact HR7s1 | nz]. }
    assert (HA4s6 : A4 !!! Regidx Rs6 = (zero_reg : mword 64)).
    { rewrite /A4 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsig Rs6 ltac:(vm_compute; reflexivity)).
      rewrite /A3 upd_ne; [| nz]. rewrite /A2 upd_ne; [| nz].
      rewrite /A1 upd_ne; [exact HR7s6 | nz]. }
    assert (HA4o : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 -> c <> Rs8 ->
              c <> Rs9 -> c <> Rs10 ->
              A4 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
      rewrite /A4 upd_ne; [| dlk_xne N20].
      rewrite (callee_saved_lookup Hcsig c Hc).
      rewrite /A3 upd_ne; [| dlk_rne2 Hcsra Hc].
      rewrite /A2 upd_ne; [| dlk_rne2 Hcsa0 Hc].
      rewrite /A1 upd_ne;
        [ exact (HR7o c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26)
        | dlk_rne2 Hcsa1 Hc ]. }
    (* ===== +0x03c .. +0x044 : the four constants ===== *)
    iApply (wp_li4_s_sconf (mword_of_int (NX + 0x3c)) Rs3
              (mword_of_int 47 : mword 12) (mword_of_int 47 : mword 64)
              A4 (K - 12)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi03c").
    iIntros (CIDK1 HqK1) "Hcg Hpc".
    pose (A5 := <[Regidx Rs3 := regval_into_reg (mword_of_int 47 : mword 64)]> A4).
    assert (HpA040 : add_vec_int (mword_of_int (NX + 0x3c) : mword 64) 4
                     = mword_of_int (NX + 0x40)) by pcw.
    iEval (rewrite HpA040) in "Hpc".
    iApply (wp_cli_s_sconf (mword_of_int (NX + 0x40)) Rs8 (mword_of_int 13 : mword 6)
              (mword_of_int 13 : mword 64) A5 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi040").
    iIntros (CIDK2 HqK2) "Hcg Hpc".
    pose (A6 := <[Regidx Rs8 := regval_into_reg (mword_of_int 13 : mword 64)]> A5).
    assert (HpA042 : add_vec_int (mword_of_int (NX + 0x40) : mword 64) 2
                     = mword_of_int (NX + 0x42)) by pcw.
    iEval (rewrite HpA042) in "Hpc".
    iApply (wp_cli_s_sconf (mword_of_int (NX + 0x42)) Rs9 (mword_of_int 14 : mword 6)
              (mword_of_int 14 : mword 64) A6 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi042").
    iIntros (CIDK3 HqK3) "Hcg Hpc".
    pose (A7 := <[Regidx Rs9 := regval_into_reg (mword_of_int 14 : mword 64)]> A6).
    assert (HpA044 : add_vec_int (mword_of_int (NX + 0x42) : mword 64) 2
                     = mword_of_int (NX + 0x44)) by pcw.
    iEval (rewrite HpA044) in "Hpc".
    iApply (wp_cli_s_sconf (mword_of_int (NX + 0x44)) Rs7 (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) A7 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi044").
    iIntros (CIDK4 HqK4) "Hcg Hpc".
    pose (A8 := <[Regidx Rs7 := regval_into_reg (mword_of_int 1 : mword 64)]> A7).
    assert (HpA046 : add_vec_int (mword_of_int (NX + 0x44) : mword 64) 2
                     = mword_of_int (NX + 0x46)) by pcw.
    iEval (rewrite HpA046) in "Hpc".
    assert (HA8sp : A8 !!! Regidx csp_rs1 = pa_stk sp0 12).
    { rewrite /A8 upd_ne; [| nz]. rewrite /A7 upd_ne; [| nz].
      rewrite /A6 upd_ne; [| nz]. rewrite /A5 upd_ne; [exact HA4sp | nz]. }
    assert (HA8s1 : A8 !!! Regidx Rs1 = pv).
    { rewrite /A8 upd_ne; [| nz]. rewrite /A7 upd_ne; [| nz].
      rewrite /A6 upd_ne; [| nz]. rewrite /A5 upd_ne; [exact HA4s1 | nz]. }
    assert (HA8s3 : A8 !!! Regidx Rs3 = (mword_of_int 47 : mword 64)).
    { rewrite /A8 upd_ne; [| nz]. rewrite /A7 upd_ne; [| nz].
      rewrite /A6 upd_ne; [| nz]. rewrite /A5 upd_eq. reflexivity. }
    assert (HA8s4 : A8 !!! Regidx Rs4 = ientry kig).
    { rewrite /A8 upd_ne; [| nz]. rewrite /A7 upd_ne; [| nz].
      rewrite /A6 upd_ne; [| nz]. rewrite /A5 upd_ne; [exact HA4s4 | nz]. }
    assert (HA8s6 : A8 !!! Regidx Rs6 = (zero_reg : mword 64)).
    { rewrite /A8 upd_ne; [| nz]. rewrite /A7 upd_ne; [| nz].
      rewrite /A6 upd_ne; [| nz]. rewrite /A5 upd_ne; [exact HA4s6 | nz]. }
    assert (HA8o : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 -> c <> Rs8 ->
              c <> Rs9 -> c <> Rs10 ->
              A8 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
      rewrite /A8 upd_ne; [| dlk_xne N23].
      rewrite /A7 upd_ne; [| dlk_xne N25].
      rewrite /A6 upd_ne; [| dlk_xne N24].
      rewrite /A5 upd_ne; [| dlk_xne N19].
      exact (HA4o c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26). }
    (* ===== +0x046 c.j +0xf4 ===== *)
    assert (Htgt0f4 : add_vec (mword_of_int (NX + 0x46) : mword 64)
              (sign_extend' 64 (sign_extend' 21
                 (concat_vec (mword_of_int 87 : mword 11) ('b"0"))))
              = mword_of_int (NX + 0xf4)) by pcw.
    iApply (wp_cj_s_sconf (mword_of_int (NX + 0x46))
              (sign_extend' 21 (concat_vec (mword_of_int 87 : mword 11) ('b"0")))
              A8 (K - 12)%nat b
              ltac:(rewrite Htgt0f4; vm_compute; reflexivity)
              with "Hcg Hpc Hi046").
    iIntros (CIDK5 HqK5). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htgt0f4) in "Hpc".
    (* ===== +0x0f4 lbu a5,0(s1) : path[0] again ===== *)
    iApply (wp_lbu_s_sconf (mword_of_int (NX + 0xf4)) Ra5 Rs1
              (mword_of_int 0 : mword 12) A8 (K - 12)%nat SLASH b (dqm := dqp)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0f4 [Hp0]").
    { iEval (rgne; rewrite HA8s1 addv_sext0). iExact "Hp0". }
    iIntros (CIDW1 HqW1) "Hcg Hpc Hp0".
    iEval (rgne; rewrite HA8s1 addv_sext0) in "Hp0".
    pose (H1 := <[Regidx Ra5 := regval_into_reg
                  (zero_extend' 64 (SLASH : mword 8))]> A8).
    assert (HH1a5 : H1 !!! Regidx Ra5
                    = (zero_extend' 64 (SLASH : mword 8) : mword 64))
      by (rewrite /H1; apply upd_eq).
    assert (HH1s1 : H1 !!! Regidx Rs1 = pv)
      by (rewrite /H1 upd_ne; [exact HA8s1 | nz]).
    assert (HH1s3 : H1 !!! Regidx Rs3 = (mword_of_int 47 : mword 64))
      by (rewrite /H1 upd_ne; [exact HA8s3 | nz]).
    assert (Hpp0f8 : add_vec_int (mword_of_int (NX + 0xf4) : mword 64) 4
                     = mword_of_int (NX + 0xf8)) by pcw.
    iEval (rewrite Hpp0f8) in "Hpc".
    (* ===== +0x0f8 bne a5,s3 : FALLS THROUGH (the byte IS '/') ===== *)
    iApply (wp_bne_fall_s_sconf (mword_of_int (NX + 0xf8))
              (mword_of_int 14 : mword 13) Rs3 Ra5 H1 (K - 12)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HH1a5 HH1s3;
                    exact (nx_nslash_eq SLASH eq_refl))
              with "Hcg Hpc Hi0f8").
    iIntros (CIDW2 HqW2) "Hcg Hpc".
    assert (Hpp0fc : add_vec_int (mword_of_int (NX + 0xf8) : mword 64) 4
                     = mword_of_int (NX + 0xfc)) by pcw.
    iEval (rewrite Hpp0fc) in "Hpc".
    (* ===== +0x0fc c.addi s1,s1,1 ===== *)
    iApply (wp_caddi_s_sconf (mword_of_int (NX + 0xfc)) Rs1
              (mword_of_int 1 : mword 6) H1 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0fc").
    iIntros (CIDW3 HqW3) "Hcg Hpc".
    iEval (rgne; rewrite HH1s1 -(pa_add_0 pv) (nx_addi1 pv 0)) in "Hcg".
    pose (Q1 := <[Regidx Rs1 := regval_into_reg (pa_add pv 1)]> H1).
    assert (HQ1s1 : Q1 !!! Regidx Rs1 = pa_add pv 1)
      by (rewrite /Q1; apply upd_eq).
    assert (HQ1s3 : Q1 !!! Regidx Rs3 = (mword_of_int 47 : mword 64))
      by (rewrite /Q1 upd_ne; [exact HH1s3 | nz]).
    assert (Hpp0fe : add_vec_int (mword_of_int (NX + 0xfc) : mword 64) 2
                     = mword_of_int (NX + 0xfe)) by pcw.
    iEval (rewrite Hpp0fe) in "Hpc".
    (* ===== +0x0fe lbu a5,0(s1) : path[1], the terminator ===== *)
    iApply (wp_lbu_s_sconf (mword_of_int (NX + 0xfe)) Ra5 Rs1
              (mword_of_int 0 : mword 12) Q1 (K - 12)%nat NUL b (dqm := dqp)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0fe [Hp1]").
    { iEval (rgne; rewrite HQ1s1 addv_sext0). iExact "Hp1". }
    iIntros (CIDW4 HqW4) "Hcg Hpc Hp1".
    iEval (rgne; rewrite HQ1s1 addv_sext0) in "Hp1".
    pose (Q2 := <[Regidx Ra5 := regval_into_reg
                  (zero_extend' 64 (NUL : mword 8))]> Q1).
    assert (HQ2a5 : Q2 !!! Regidx Ra5
                    = (zero_extend' 64 (NUL : mword 8) : mword 64))
      by (rewrite /Q2; apply upd_eq).
    assert (HQ2s3 : Q2 !!! Regidx Rs3 = (mword_of_int 47 : mword 64))
      by (rewrite /Q2 upd_ne; [exact HQ1s3 | nz]).
    assert (Hpp102 : add_vec_int (mword_of_int (NX + 0xfe) : mword 64) 4
                     = mword_of_int (NX + 0x102)) by pcw.
    iEval (rewrite Hpp102) in "Hpc".
    (* ===== +0x102 beq a5,s3 : FALLS THROUGH (NUL is not '/') ===== *)
    assert (HNS : NUL <> SLASH).
    { intro Hq. apply (f_equal bv_unsigned) in Hq. vm_compute in Hq.
      discriminate. }
    iApply (wp_beq_fall_s_sconf (mword_of_int (NX + 0x102))
              (mword_of_int 8186 : mword 13) Rs3 Ra5 Q2 (K - 12)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HQ2a5 HQ2s3;
                    exact (nx_slash_ne NUL HNS))
              with "Hcg Hpc Hi102").
    iIntros (CIDW5 HqW5) "Hcg Hpc".
    assert (Hpp106 : add_vec_int (mword_of_int (NX + 0x102) : mword 64) 4
                     = mword_of_int (NX + 0x106)) by pcw.
    iEval (rewrite Hpp106) in "Hpc".
    (* ===== +0x106 c.beqz a5 : TAKEN (it IS the terminator) ===== *)
    assert (Htgt140 : add_vec (mword_of_int (NX + 0x106) : mword 64)
              (sign_extend' 64 (sign_extend' 13
                 (concat_vec (mword_of_int 29 : mword 8) ('b"0"))))
              = mword_of_int (NX + 0x140)) by pcw.
    iApply (wp_cbeqz_taken_s_sconf (mword_of_int (NX + 0x106))
              (mword_of_int 29 : mword 8) (Cregidx (mword_of_int 7)) Ra5
              Q2 (K - 12)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HQ2a5; exact (nx_nul_eq NUL eq_refl))
              ltac:(rewrite Htgt140; vm_compute; reflexivity)
              with "Hcg Hpc Hi106").
    iIntros (CIDW6 HqW6). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htgt140) in "Hpc".
    (* ---- the register bundle the epilogue wants, at [Q2] ---- *)
    assert (HQ2c : forall c : mword 5, c <> Rs1 -> c <> Ra5 ->
              Q2 !!! Regidx c = (A8 !!! Regidx c : mword 64)).
    { intros c N9 N15. rewrite /Q2 upd_ne; [| dlk_xne N15].
      rewrite /Q1 upd_ne; [| dlk_xne N9].
      rewrite /H1 upd_ne; [reflexivity | dlk_xne N15]. }
    assert (HQ2sp : Q2 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite (HQ2c csp_rs1 ltac:(nz) ltac:(nz)); exact HA8sp).
    assert (HQ2s4 : Q2 !!! Regidx Rs4 = ientry kig)
      by (rewrite (HQ2c Rs4 ltac:(nz) ltac:(nz)); exact HA8s4).
    assert (HQ2s6 : Q2 !!! Regidx Rs6 = (zero_reg : mword 64))
      by (rewrite (HQ2c Rs6 ltac:(nz) ltac:(nz)); exact HA8s6).
    assert (HQ2o : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 -> c <> Rs8 ->
              c <> Rs9 -> c <> Rs10 ->
              Q2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
      assert (N15 : c <> Ra5).
      { intro Hq. rewrite Hq in Hc. rewrite Hcsa5 in Hc. discriminate. }
      rewrite (HQ2c c N9 N15).
      exact (HA8o c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26). }
    (* ===== +0x140 beq s6,zero : TAKEN (nameiparent = 0) ===== *)
    assert (Htgt05c : add_vec (mword_of_int (NX + 0x140) : mword 64)
              (sign_extend' 64 (mword_of_int 7964 : mword 13))
              = mword_of_int (NX + 0x5c)) by pcw.
    iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (NX + 0x140))
              (mword_of_int 7964 : mword 13) Rs6 Q2 (K - 12)%nat b
              ltac:(nz)
              ltac:(rgne; rewrite HQ2s6; exact eq_refl)
              ltac:(rewrite Htgt05c; vm_compute; reflexivity)
              with "Hcg Hpc Hi140").
    iIntros (CIDW7 HqW7). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htgt05c) in "Hpc".
    (* ================================================================= *)
    (*  THE EPILOGUE at +0x5c                                             *)
    (* ================================================================= *)
    (* +0x5c c.mv a0,s4 *)
    iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x5c)) Ra0 Rs4 Q2 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi05c").
    iIntros (CIDT0 HqT0) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (P0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (Q2 !!! Regidx Rs4))]> Q2).
    assert (HP0a0 : P0 !!! Regidx Ra0 = ientry kig).
    { rewrite /P0 upd_eq. rewrite HQ2s4. apply add_vec_zero_l. }
    assert (HP0sp : P0 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /P0 upd_ne; [exact HQ2sp | nz]).
    assert (Hqq5e : add_vec_int (mword_of_int (NX + 0x5c) : mword 64) 2
                    = mword_of_int (NX + 0x5e)) by pcw.
    iEval (rewrite Hqq5e) in "Hpc".
    (* +0x5e .. +0x74 : the twelve pops *)
    assert (HT1 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HP0sp; apply dlk_frm1).
    iEval (rewrite -HT1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x5e)) (mword_of_int 11 : mword 6)
              Rra P0 (K - 12)%nat (m !!! Regidx Rra : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi05e Hb1").
    iIntros (CIDT1 HqT1) "Hcg Hpc Hb1".
    pose (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> P0).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /P1 upd_ne; [exact HP0sp | nz]).
    assert (Hqq60 : add_vec_int (mword_of_int (NX + 0x5e) : mword 64) 2
                    = mword_of_int (NX + 0x60)) by pcw.
    iEval (rewrite Hqq60) in "Hpc".
    assert (HT2 : add_vec (P1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HP1sp; apply dlk_frm2).
    iEval (rewrite -HT2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x60)) (mword_of_int 10 : mword 6)
              Rs0 P1 (K - 12)%nat (m !!! Regidx Rs0 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi060 Hb2").
    iIntros (CIDT2 HqT2) "Hcg Hpc Hb2".
    pose (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /P2 upd_ne; [exact HP1sp | nz]).
    assert (Hqq62 : add_vec_int (mword_of_int (NX + 0x60) : mword 64) 2
                    = mword_of_int (NX + 0x62)) by pcw.
    iEval (rewrite Hqq62) in "Hpc".
    assert (HT3 : add_vec (P2 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HP2sp; apply dlk_frm3).
    iEval (rewrite -HT3) in "Hb3".
    iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x62)) (mword_of_int 9 : mword 6)
              Rs1 P2 (K - 12)%nat (m !!! Regidx Rs1 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi062 Hb3").
    iIntros (CIDT3 HqT3) "Hcg Hpc Hb3".
    pose (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /P3 upd_ne; [exact HP2sp | nz]).
    assert (Hqq64 : add_vec_int (mword_of_int (NX + 0x62) : mword 64) 2
                    = mword_of_int (NX + 0x64)) by pcw.
    iEval (rewrite Hqq64) in "Hpc".
    assert (HT4 : add_vec (P3 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HP3sp; apply dlk_frm4).
    iEval (rewrite -HT4) in "Hb4".
    iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x64)) (mword_of_int 8 : mword 6)
              Rs2 P3 (K - 12)%nat (m !!! Regidx Rs2 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi064 Hb4").
    iIntros (CIDT4 HqT4) "Hcg Hpc Hb4".
    pose (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
    assert (HP4sp : P4 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /P4 upd_ne; [exact HP3sp | nz]).
    assert (Hqq66 : add_vec_int (mword_of_int (NX + 0x64) : mword 64) 2
                    = mword_of_int (NX + 0x66)) by pcw.
    iEval (rewrite Hqq66) in "Hpc".
    assert (HT5 : add_vec (P4 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (rewrite HP4sp; apply dlk_frm5).
    iEval (rewrite -HT5) in "Hb5".
    iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x66)) (mword_of_int 7 : mword 6)
              Rs3 P4 (K - 12)%nat (m !!! Regidx Rs3 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi066 Hb5").
    iIntros (CIDT5 HqT5) "Hcg Hpc Hb5".
    pose (P5 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> P4).
    assert (HP5sp : P5 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /P5 upd_ne; [exact HP4sp | nz]).
    assert (Hqq68 : add_vec_int (mword_of_int (NX + 0x66) : mword 64) 2
                    = mword_of_int (NX + 0x68)) by pcw.
    iEval (rewrite Hqq68) in "Hpc".
    assert (HT6 : add_vec (P5 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 6) by (rewrite HP5sp; apply dlk_frm6).
    iEval (rewrite -HT6) in "Hb6".
    iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x68)) (mword_of_int 6 : mword 6)
              Rs4 P5 (K - 12)%nat (m !!! Regidx Rs4 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi068 Hb6").
    iIntros (CIDT6 HqT6) "Hcg Hpc Hb6".
    pose (P6 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> P5).
    assert (HP6sp : P6 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /P6 upd_ne; [exact HP5sp | nz]).
    assert (Hqq6a : add_vec_int (mword_of_int (NX + 0x68) : mword 64) 2
                    = mword_of_int (NX + 0x6a)) by pcw.
    iEval (rewrite Hqq6a) in "Hpc".
    assert (HT7 : add_vec (P6 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (rewrite HP6sp; apply dlk_frm7).
    iEval (rewrite -HT7) in "Hb7".
    iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x6a)) (mword_of_int 5 : mword 6)
              Rs5 P6 (K - 12)%nat (m !!! Regidx Rs5 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi06a Hb7").
    iIntros (CIDT7 HqT7) "Hcg Hpc Hb7".
    pose (P7 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> P6).
    assert (HP7sp : P7 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /P7 upd_ne; [exact HP6sp | nz]).
    assert (Hqq6c : add_vec_int (mword_of_int (NX + 0x6a) : mword 64) 2
                    = mword_of_int (NX + 0x6c)) by pcw.
    iEval (rewrite Hqq6c) in "Hpc".
    assert (HT8 : add_vec (P7 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (rewrite HP7sp; apply dlk_frm8).
    iEval (rewrite -HT8) in "Hb8".
    iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x6c)) (mword_of_int 4 : mword 6)
              Rs6 P7 (K - 12)%nat (m !!! Regidx Rs6 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi06c Hb8").
    iIntros (CIDT8 HqT8) "Hcg Hpc Hb8".
    pose (P8 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> P7).
    assert (HP8sp : P8 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /P8 upd_ne; [exact HP7sp | nz]).
    assert (Hqq6e : add_vec_int (mword_of_int (NX + 0x6c) : mword 64) 2
                    = mword_of_int (NX + 0x6e)) by pcw.
    iEval (rewrite Hqq6e) in "Hpc".
    assert (HT9 : add_vec (P8 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 9) by (rewrite HP8sp; apply dlk_frm9).
    iEval (rewrite -HT9) in "Hb9".
    iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x6e)) (mword_of_int 3 : mword 6)
              Rs7 P8 (K - 12)%nat (m !!! Regidx Rs7 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi06e Hb9").
    iIntros (CIDT9 HqT9) "Hcg Hpc Hb9".
    pose (P9 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7 : mword 64)]> P8).
    assert (HP9sp : P9 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /P9 upd_ne; [exact HP8sp | nz]).
    assert (Hqq70 : add_vec_int (mword_of_int (NX + 0x6e) : mword 64) 2
                    = mword_of_int (NX + 0x70)) by pcw.
    iEval (rewrite Hqq70) in "Hpc".
    assert (HT10 : add_vec (P9 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                   = pa_stk sp0 10) by (rewrite HP9sp; apply nx_frm10).
    iEval (rewrite -HT10) in "Hb10".
    iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x70)) (mword_of_int 2 : mword 6)
              Rs8 P9 (K - 12)%nat (m !!! Regidx Rs8 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi070 Hb10").
    iIntros (CIDT10 HqT10) "Hcg Hpc Hb10".
    pose (P10 := <[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8 : mword 64)]> P9).
    assert (HP10sp : P10 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /P10 upd_ne; [exact HP9sp | nz]).
    assert (Hqq72 : add_vec_int (mword_of_int (NX + 0x70) : mword 64) 2
                    = mword_of_int (NX + 0x72)) by pcw.
    iEval (rewrite Hqq72) in "Hpc".
    assert (HT11 : add_vec (P10 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 11) by (rewrite HP10sp; apply nx_frm11).
    iEval (rewrite -HT11) in "Hb11".
    iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x72)) (mword_of_int 1 : mword 6)
              Rs9 P10 (K - 12)%nat (m !!! Regidx Rs9 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi072 Hb11").
    iIntros (CIDT11 HqT11) "Hcg Hpc Hb11".
    pose (P11 := <[Regidx Rs9 := regval_into_reg (m !!! Regidx Rs9 : mword 64)]> P10).
    assert (HP11sp : P11 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /P11 upd_ne; [exact HP10sp | nz]).
    assert (Hqq74 : add_vec_int (mword_of_int (NX + 0x72) : mword 64) 2
                    = mword_of_int (NX + 0x74)) by pcw.
    iEval (rewrite Hqq74) in "Hpc".
    assert (HT12 : add_vec (P11 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk sp0 12) by (rewrite HP11sp; apply nx_frm12).
    iEval (rewrite -HT12) in "Hb12".
    iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x74)) (mword_of_int 0 : mword 6)
              Rs10 P11 (K - 12)%nat (m !!! Regidx Rs10 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi074 Hb12").
    iIntros (CIDT12 HqT12) "Hcg Hpc Hb12".
    pose (P12 := <[Regidx Rs10 := regval_into_reg (m !!! Regidx Rs10 : mword 64)]> P11).
    assert (HP12sp : P12 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /P12 upd_ne; [exact HP11sp | nz]).
    assert (Hqq76 : add_vec_int (mword_of_int (NX + 0x74) : mword 64) 2
                    = mword_of_int (NX + 0x76)) by pcw.
    iEval (rewrite Hqq76) in "Hpc".
    (* ===== +0x76 c.addi16sp sp,96 : the pop ===== *)
    assert (Hwv : add_vec (P12 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))
                  = sp0)
      by (rewrite HP12sp; apply dlk_pop).
    assert (Hpopeq : (P12 !!! Regidx csp_rs1 : mword 64)
                     = pa_stk (add_vec (P12 !!! Regidx csp_rs1 : mword 64)
                         (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))) 12)
      by (rewrite Hwv HP12sp; reflexivity).
    iEval (rewrite HT1) in "Hb1".   iEval (rewrite HT2) in "Hb2".
    iEval (rewrite HT3) in "Hb3".   iEval (rewrite HT4) in "Hb4".
    iEval (rewrite HT5) in "Hb5".   iEval (rewrite HT6) in "Hb6".
    iEval (rewrite HT7) in "Hb7".   iEval (rewrite HT8) in "Hb8".
    iEval (rewrite HT9) in "Hb9".   iEval (rewrite HT10) in "Hb10".
    iEval (rewrite HT11) in "Hb11". iEval (rewrite HT12) in "Hb12".
    iAssert (stack_own sp0 12) with "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12]"
      as "Hstk".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hb1"; [iExists _; iExact "Hb1" |].
      iSplitL "Hb2"; [iExists _; iExact "Hb2" |].
      iSplitL "Hb3"; [iExists _; iExact "Hb3" |].
      iSplitL "Hb4"; [iExists _; iExact "Hb4" |].
      iSplitL "Hb5"; [iExists _; iExact "Hb5" |].
      iSplitL "Hb6"; [iExists _; iExact "Hb6" |].
      iSplitL "Hb7"; [iExists _; iExact "Hb7" |].
      iSplitL "Hb8"; [iExists _; iExact "Hb8" |].
      iSplitL "Hb9"; [iExists _; iExact "Hb9" |].
      iSplitL "Hb10"; [iExists _; iExact "Hb10" |].
      iSplitL "Hb11"; [iExists _; iExact "Hb11" |].
      iSplitL "Hb12"; [iExists _; iExact "Hb12" |].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (NX + 0x76))
              (mword_of_int 6 : mword 6) P12 (K - 12)%nat 12 b Hpopeq
              with "Hcg Hpc Hi076 Hstk").
    iIntros (CIDT13 HqT13) "Hcg Hpc".
    pose (P13 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P12 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))))]> P12).
    iEval (rewrite Kpop) in "Hcg".
    assert (Hqq78 : add_vec_int (mword_of_int (NX + 0x76) : mword 64) 2
                    = mword_of_int (NX + 0x78)) by pcw.
    iEval (rewrite Hqq78) in "Hpc".
    (* ===== +0x78 c.jr ra ===== *)
    assert (CPra : P13 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)).
    { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
      rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
      rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
      rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_ne; [| nz].
      rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_ne; [| nz].
      rewrite /P3 upd_ne; [| nz]. rewrite /P2 upd_ne; [| nz].
      rewrite /P1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (NX + 0x78)) Rra P13 K b
              ltac:(nz) with "Hcg Hpc Hi078").
    iIntros (CIDT14 HqT14) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P13 !!! Regidx Rra : mword 64) = ret_tgt)
      by (rewrite CPra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== the callee-saved record ===== *)
    assert (CPsp : P13 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite /P13 upd_eq. rewrite Hwv. symmetry. exact Hspm. }
    assert (CPs0 : P13 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
      rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
      rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
      rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_ne; [| nz].
      rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_ne; [| nz].
      rewrite /P3 upd_ne; [| nz]. rewrite /P2 upd_eq. reflexivity. }
    assert (CPs1 : P13 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
      rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
      rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
      rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_ne; [| nz].
      rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_ne; [| nz].
      rewrite /P3 upd_eq. reflexivity. }
    assert (CPs2 : P13 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
      rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
      rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
      rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_ne; [| nz].
      rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_eq. reflexivity. }
    assert (CPs3 : P13 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
      rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
      rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
      rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_ne; [| nz].
      rewrite /P5 upd_eq. reflexivity. }
    assert (CPs4 : P13 !!! Regidx Rs4 = (m !!! Regidx Rs4 : mword 64)).
    { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
      rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
      rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
      rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_eq. reflexivity. }
    assert (CPs5 : P13 !!! Regidx Rs5 = (m !!! Regidx Rs5 : mword 64)).
    { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
      rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
      rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
      rewrite /P7 upd_eq. reflexivity. }
    assert (CPs6 : P13 !!! Regidx Rs6 = (m !!! Regidx Rs6 : mword 64)).
    { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
      rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
      rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_eq. reflexivity. }
    assert (CPs7 : P13 !!! Regidx Rs7 = (m !!! Regidx Rs7 : mword 64)).
    { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
      rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
      rewrite /P9 upd_eq. reflexivity. }
    assert (CPs8 : P13 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64)).
    { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
      rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_eq. reflexivity. }
    assert (CPs9 : P13 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64)).
    { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
      rewrite /P11 upd_eq. reflexivity. }
    assert (CPs10 : P13 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64)).
    { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_eq. reflexivity. }
    assert (CPo : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 -> c <> Rs8 ->
              c <> Rs9 -> c <> Rs10 ->
              P13 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
      rewrite /P13 upd_ne; [| dlk_xne N2].
      rewrite /P12 upd_ne; [| dlk_xne N26].
      rewrite /P11 upd_ne; [| dlk_xne N25].
      rewrite /P10 upd_ne; [| dlk_xne N24].
      rewrite /P9 upd_ne; [| dlk_xne N23].
      rewrite /P8 upd_ne; [| dlk_xne N22].
      rewrite /P7 upd_ne; [| dlk_xne N21].
      rewrite /P6 upd_ne; [| dlk_xne N20].
      rewrite /P5 upd_ne; [| dlk_xne N19].
      rewrite /P4 upd_ne; [| dlk_xne N18].
      rewrite /P3 upd_ne; [| dlk_xne N9].
      rewrite /P2 upd_ne; [| dlk_xne N8].
      rewrite /P1 upd_ne; [| dlk_rne2 Hcsra Hc].
      rewrite /P0 upd_ne;
        [ exact (HQ2o c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26)
        | dlk_rne2 Hcsa0 Hc ]. }
    assert (CPa0 : P13 !!! Regidx Ra0 = ientry kig).
    { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
      rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
      rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
      rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_ne; [| nz].
      rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_ne; [| nz].
      rewrite /P3 upd_ne; [| nz]. rewrite /P2 upd_ne; [| nz].
      rewrite /P1 upd_ne; [exact HP0a0 | nz]. }
    (* the two path bytes, back at the addresses the contract names *)
    iEval (rewrite -(pa_add_0 pv)) in "Hp0".
    iDestruct (cpu_own_transport CIDig CIDT14 n eb p b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CIDT14 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! P13 (ientry kig) with "[%] Hcg Hcnt Hpc Hp0 Hp1 Hip").
    split; [| exact CPa0].
    unfold callee_saved. split_and!;
      first [ exact CPsp | exact CPs0 | exact CPs1 | exact CPs2 | exact CPs3
            | exact CPs4 | exact CPs5 | exact CPs6 | exact CPs7
            | exact CPs8 | exact CPs9 | exact CPs10
            | apply CPo; first [ vm_compute; reflexivity
                               | vm_compute; discriminate ] ].
  Qed.

End ProofNamexRoot.

End NamexRootProof.
