(* ProofSysUnlinkTails.v -- sys_unlink's EXIT blocks, as block lemmas.
   These apply callees' contracts, so they live inside a module functor
   ([design/spec-modules.md]); the functor is NOT ascribed to a signature,
   because it is a parts layer -- [ProofSysUnlink.v] instantiates it beside
   its own callee arguments and the seal happens there.

     ARM A   (+0x170 .. +0x172)  argstr < 0: no begin_op ever ran
                                 a0 = -1 ; j the epilogue
     ARM B   (+0x0e2 .. +0x0ea)  nameiparent returned 0
                                 end_op ; a0 = -1 ; restore s1 ; j epilogue
     [bad:]  (+0x15a .. +0x166)  iunlockput(dp) ; end_op ; a0 = -1 ;
                                 restore s1 ; FALL into the epilogue
     ARM D   (+0x158)            restore s2, then fall into [bad:]
     ARM E   (+0x174 .. +0x17e)  iunlockput(ip) ; restore s2 and s3 ;
                                 j [bad:]
     the three PANICs (+0x0ec, +0x12e, +0x13a) -- auipc / addi / jal, all
     discharged against [SpecPanic], none of which returns.

   THE FRAME CARVE IS ARM-DEPENDENT (sys_open's shape, not sys_link's).
   The prologue pushes only ra and s0; [c.sdsp s1] is at +0x1a, [c.sdsp s2]
   at +0x5c and [c.sdsp s3] at +0x72, so each arm restores exactly the
   subset its own path saved and every OTHER callee-saved slot rides
   through as the caller's junk, at an existential word.  ARM A owns none
   of the three: it branches above all of them, so all of s1, s2 and s3 are
   still the caller's and all three slot contents are junk.

   TWO ENTRIES INTO ONE TAIL, AND THEY ARE TWO LEMMAS, NOT ONE.  ARM D's
   [c.ldsp s2] at +0x158 and ARM E's four instructions at +0x174 both end
   inside [bad:], but they arrive holding different things -- D has never
   locked [ip] and E is still holding it -- so the shared block is
   [su_tail_bad] and each entry is its own lemma applying it.

   WHY [bad:] CALLS THE COUNTED [wp_iunlockput_sconf].  Every route to it
   is ABOVE the zeroing [writei], so no arm here has logged [IBLOCK dp] and
   none of them holds a credit; what they do hold is begin_op's ten less at
   most one walk unit, which leaves [iput_units] with six to spare.  The
   CREDITED form is the success tail's business and is applied in the walk.

   NOTHING HERE SPENDS AN [ilink].  The zeroing at +0x8a..+0xa4 is what
   releases one, and it is below every branch in this file. *)
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
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved KernelText.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import KernelDataInv.
Require Import PrintkArgs.
Require Import SpecPanic.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KallocInv.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecEndOp.
Require Import SpecIput.
Require Import SpecIunlockput.
Require Import CodeSysUnlink.
Require Import ProofSysUnlinkParts.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Local Open Scope Z_scope.

Set Printing Depth 40.

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.

(* ===================================================================== *)
(*  THE THREE PANIC MESSAGES.  Named pure lemmas, never inline [ltac:]     *)
(*  (optimization.md).  Addresses and byte counts measured off the image.  *)
(* ===================================================================== *)
Definition su_nlink_a : Z := 0x800075f0.
Definition su_nlink_s : string := "unlink: nlink < 1".

Lemma su_nlink_nonul : PrintkFmt.nonul su_nlink_s = true.
Proof. vm_compute; reflexivity. Qed.

Lemma su_nlink_nz : eq_vec (mword_of_int su_nlink_a : mword 64) zero_reg = false.
Proof. vm_compute; reflexivity. Qed.

Lemma su_nlink_bytes :
  forall j b, cstring_bytes su_nlink_s !! j = Some b ->
    KernelData.kernel_data !! (su_nlink_a + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 18 (destruct j as [|j];
        [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
  vm_compute in Hj; discriminate.
Qed.

Definition su_readi_a : Z := 0x80007608.
Definition su_readi_s : string := "isdirempty: readi".

Lemma su_readi_nonul : PrintkFmt.nonul su_readi_s = true.
Proof. vm_compute; reflexivity. Qed.

Lemma su_readi_nz : eq_vec (mword_of_int su_readi_a : mword 64) zero_reg = false.
Proof. vm_compute; reflexivity. Qed.

Lemma su_readi_bytes :
  forall j b, cstring_bytes su_readi_s !! j = Some b ->
    KernelData.kernel_data !! (su_readi_a + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 18 (destruct j as [|j];
        [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
  vm_compute in Hj; discriminate.
Qed.

Definition su_writei_a : Z := 0x80007620.
Definition su_writei_s : string := "unlink: writei".

Lemma su_writei_nonul : PrintkFmt.nonul su_writei_s = true.
Proof. vm_compute; reflexivity. Qed.

Lemma su_writei_nz : eq_vec (mword_of_int su_writei_a : mword 64) zero_reg = false.
Proof. vm_compute; reflexivity. Qed.

Lemma su_writei_bytes :
  forall j b, cstring_bytes su_writei_s !! j = Some b ->
    KernelData.kernel_data !! (su_writei_a + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 15 (destruct j as [|j];
        [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
  vm_compute in Hj; discriminate.
Qed.

Lemma su_panic_noff (n : nat) : (n = 0)%nat -> (Z.of_nat n + 2 < 2 ^ 31)%Z.
Proof. intros ->. lia. Qed.

Section SuMsgStr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  Lemma su_nlink_str :
    (kernel_data : iProp Σ) -∗ (mword_of_int su_nlink_a : mword 64) ↦ₛ□ su_nlink_s.
  Proof.
    iIntros "#Hd".
    iApply (kernel_data_string su_nlink_a su_nlink_s _ eq_refl
              ltac:(unfold text_end, su_nlink_a; lia) su_nlink_bytes with "Hd").
  Qed.

  Lemma su_readi_str :
    (kernel_data : iProp Σ) -∗ (mword_of_int su_readi_a : mword 64) ↦ₛ□ su_readi_s.
  Proof.
    iIntros "#Hd".
    iApply (kernel_data_string su_readi_a su_readi_s _ eq_refl
              ltac:(unfold text_end, su_readi_a; lia) su_readi_bytes with "Hd").
  Qed.

  Lemma su_writei_str :
    (kernel_data : iProp Σ) -∗ (mword_of_int su_writei_a : mword 64) ↦ₛ□ su_writei_s.
  Proof.
    iIntros "#Hd".
    iApply (kernel_data_string su_writei_a su_writei_s _ eq_refl
              ltac:(unfold text_end, su_writei_a; lia) su_writei_bytes with "Hd").
  Qed.
End SuMsgStr.

Module SysUnlinkTails (Iunlockput : IUNLOCKPUT) (EndOp : END_OP) (PN : PANIC).

Section ProofSysUnlinkTails.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  (* the three-slot pool, split for a single callee's need and rejoined *)
  Lemma su_bs3 (bn : bio_names) :
    (bslots bn 3 : iProp Σ) ⊣⊢ bslot bn ∗ bslots bn 2.
  Proof. rewrite /bslot. change 3%nat with (1 + 2)%nat. apply bslots_op. Qed.

  (* ================================================================== *)
  (*  ARM A: +0x170 c.li a0,-1 ; +0x172 c.j +0x168                       *)
  (*                                                                     *)
  (*  The argstr arm.  It is entered from the [bltz] at +0x16, ABOVE     *)
  (*  every spill and above begin_op, so it holds no log unit, no        *)
  (*  reference, no file-system resource of any kind -- only the frame.  *)
  (*  Its crossing index is [b], not [true]: two plain instructions and  *)
  (*  the epilogue, and no callee in between.                            *)
  (* ================================================================== *)
  Lemma su_tail_a `{GEN : GenId} `{CID0 : CpuId}
      (m M : regfile) (sp0 : mword 64) (K : nat) (b : bool) (pj : mword 64)
      (w3 w4 w5 w6 w27 w30 : mword 64) (bd bn bp be : nat -> bv 8) :
    (30 <= K)%nat -> ((K - 30) + 30 = K)%nat ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    su_sp sp0 M -> su_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64) ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    (M !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    su_al sp0 ->
    sie_cap_gpr KT1 M (K - 30) b pj -∗
    kernel_text -∗ pc_is (mword_of_int (SU + 0x170)) -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] w3 -∗
    (pa_stk sp0 4) ↦₈[KT1] w4 -∗
    (pa_stk sp0 5) ↦₈[KT1] w5 -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 8) jj ↦ₘ[KT1] bd jj) -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] bn jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 26) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 27) ↦₈[KT1] w27 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ[KT1] be jj) -∗
    (pa_stk sp0 30) ↦₈[KT1] w30 -∗
    wp_next b pj (fun (CIDx : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        sie_cap_gpr KT1 mf K b pj -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK30 Kpop Hsp0 HMsp HMthr HMs1 HMs2 HMs3 Hal.
    iIntros "Hcg #Htext Hpc Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD HbN HbP H27 HbE H30
              Hcont".
    iPoseProof (suli_170 with "Htext") as "Hi170".
    iPoseProof (suli_172 with "Htext") as "Hi172".
    (* ===== +0x170 c.li a0,-1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID0) (mword_of_int (SU + 0x170)) Ra0
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              M (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi170").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> M).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /M1; apply upd_eq).
    assert (HM1sp : su_sp sp0 M1)
      by (rewrite /su_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs1 | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs2 | nz]).
    assert (HM1s3 : (M1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs3 | nz]).
    assert (HM1thr : su_thr m M1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp172 : add_vec_int (mword_of_int (SU + 0x170) : mword 64) 2
                     = mword_of_int (SU + 0x172)) by pcw.
    iEval (rewrite Hpp172) in "Hpc".
    (* ===== +0x172 c.j +0x168 ===== *)
    iApply (wp_cj_s_sconf (CID := CID1) (mword_of_int (SU + 0x172))
              (sign_extend' 21 (concat_vec (mword_of_int 2043 : mword 11) ('b"0")))
              M1 (K - 30)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi172").
    iIntros (CID2 Hq2). iNext. iIntros "Hcg Hpc".
    assert (Htg : add_vec (mword_of_int (SU + 0x172) : mword 64)
                    (sign_extend' 64
                       (sign_extend' 21 (concat_vec (mword_of_int 2043 : mword 11) ('b"0"))))
                  = mword_of_int (SU + 0x168)) by pcw.
    iEval (rewrite Htg) in "Hpc".
    iDestruct (wp_next_shift (b := b) (CIDa := CID0) (CIDb := CID2)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (su_epilogue (CID0 := CID2) m M1 sp0 K b pj
              w3 w4 w5 w6 w27 w30 bd bn bp be
              HK30 Kpop Hsp0 HM1sp HM1thr HM1s1 HM1s2 HM1s3 Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD HbN HbP H27
                    HbE H30 [Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf with "[%] [%] Hcg Hpc").
    { exact Hcsf. }
    { rewrite Ha0f. exact HM1a0. }
  Qed.

  (* ================================================================== *)
  (*  THE THREE PANIC ARMS.                                              *)
  (*                                                                     *)
  (*    +0x0ec  "unlink: nlink < 1"     (the [blez] at +0x7c)             *)
  (*    +0x12e  "isdirempty: readi"     (the short read in the loop)      *)
  (*    +0x13a  "unlink: writei"        (the zeroing's short write)       *)
  (*                                                                     *)
  (*  Three instructions each -- [auipc a0] / [addi a0,a0,off] /          *)
  (*  [jal panic] -- and panic() never returns, so each drops EVERY       *)
  (*  resource its caller was holding.  They are three lemmas and not one *)
  (*  because the decode facts and the [pc_is] equations are per-address; *)
  (*  the [addi] displacement differs too (1488 / 1446 / 1458, the three  *)
  (*  message strings).                                                   *)
  (* ================================================================== *)
  Lemma su_panic_nlink `{GEN : GenId} `{CID0 : CpuId}
      (M : regfile) (K : nat) (n : nat) (eb b : bool) (pj : mword 64)
      (lks : gset string) :
    (panic_stack <= K)%nat ->
    (Z.of_nat n + 2 < 2 ^ 31)%Z ->
    locks_below lks "pr" ->
    sie_cap_gpr KT1 M K b pj -∗
    cpu_own n eb pj b lks -∗
    kernel_text -∗ kernel_data -∗ panic_env -∗
    pc_is (mword_of_int (SU + 0xec)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKp Hn31 Hbelow.
    iIntros "Hcg Hown #Htext #Hkd #Hpenv Hpc".
    iPoseProof (suli_0ec with "Htext") as "Hi0".
    iPoseProof (suli_0f0 with "Htext") as "Hi1".
    iPoseProof (suli_0f4 with "Htext") as "Hi2".
    iApply (wp_auipc_s_sconf (CID := CID0) (mword_of_int (SU + 0xec)) Ra0
              (mword_of_int 2 : mword 20) M K b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0").
    iIntros (CID1 Hq1) "Hcg Hpc".
    pose (P1 := <[Regidx Ra0 := regval_into_reg
                   (add_vec (mword_of_int (SU + 0xec) : mword 64)
                      (auipc_off (mword_of_int 2 : mword 20)))]> M).
    assert (Hp0 : add_vec_int (mword_of_int (SU + 0xec) : mword 64) 4
                  = mword_of_int (SU + 0xf0)) by pcw.
    iEval (rewrite Hp0) in "Hpc".
    iApply (wp_addi4_s_sconf (CID := CID1) (mword_of_int (SU + 0xf0)) Ra0 Ra0
              (mword_of_int 1416 : mword 12) P1 K b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1").
    iIntros (CID2 Hq2) "Hcg Hpc".
    pose (P2 := <[Regidx Ra0 := regval_into_reg
                   (add_vec (rget P1 Ra0)
                      (sign_extend' 64 (mword_of_int 1416 : mword 12)))]> P1).
    assert (Hp1 : add_vec_int (mword_of_int (SU + 0xf0) : mword 64) 4
                  = mword_of_int (SU + 0xf4)) by pcw.
    iEval (rewrite Hp1) in "Hpc".
    iApply (wp_jal_s_sconf (CID := CID2) (mword_of_int (SU + 0xf4)) Rra
              (mword_of_int 2078628 : mword 21) P2 K b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2").
    iIntros (CID3 Hq3) "Hcg Hpc".
    assert (Htgt : add_vec (mword_of_int (SU + 0xf4) : mword 64)
                     (sign_extend' 64 (mword_of_int 2078628 : mword 21))
                   = mword_of_int KernelSyms.panic) by pcw.
    iEval (rewrite Htgt) in "Hpc".
    (* the regfile the spec wants is the POST-JAL one: [wp_jal_s_sconf] wrote
       [ra].  a0 is untouched, but prove it on P3 directly -- deriving it
       across the write with [upd_ne] costs two orders of magnitude more. *)
    pose (P3 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (SU + 0xf4) : mword 64) 4)]> P2).
    assert (Ha0 : P3 !!! Regidx Ra0 = (mword_of_int su_nlink_a : mword 64)) by pcw.
    iPoseProof (su_nlink_str with "Hkd") as "#Hstr".
    iDestruct (cpu_own_transport CID0 CID3 n eb pj b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (PN.wp_panic_sconf KT1 (CID := CID3) P3 K n eb b pj
              (PkAStr DfracDiscarded su_nlink_s) lks
              HKp eq_refl Hn31 Hbelow
              with "Hcg Hown Htext Hkd Hpc Hpenv [Hstr]").
    { rewrite /pk_desc_res Ha0.
      iSplit; [iPureIntro; exact su_nlink_nonul|].
      iSplit; [iPureIntro; exact su_nlink_nz|]. iExact "Hstr". }
  Qed.

  Lemma su_panic_readi `{GEN : GenId} `{CID0 : CpuId}
      (M : regfile) (K : nat) (n : nat) (eb b : bool) (pj : mword 64)
      (lks : gset string) :
    (panic_stack <= K)%nat ->
    (Z.of_nat n + 2 < 2 ^ 31)%Z ->
    locks_below lks "pr" ->
    sie_cap_gpr KT1 M K b pj -∗
    cpu_own n eb pj b lks -∗
    kernel_text -∗ kernel_data -∗ panic_env -∗
    pc_is (mword_of_int (SU + 0x12e)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKp Hn31 Hbelow.
    iIntros "Hcg Hown #Htext #Hkd #Hpenv Hpc".
    iPoseProof (suli_12e with "Htext") as "Hi0".
    iPoseProof (suli_132 with "Htext") as "Hi1".
    iPoseProof (suli_136 with "Htext") as "Hi2".
    iApply (wp_auipc_s_sconf (CID := CID0) (mword_of_int (SU + 0x12e)) Ra0
              (mword_of_int 2 : mword 20) M K b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0").
    iIntros (CID1 Hq1) "Hcg Hpc".
    pose (P1 := <[Regidx Ra0 := regval_into_reg
                   (add_vec (mword_of_int (SU + 0x12e) : mword 64)
                      (auipc_off (mword_of_int 2 : mword 20)))]> M).
    assert (Hp0 : add_vec_int (mword_of_int (SU + 0x12e) : mword 64) 4
                  = mword_of_int (SU + 0x132)) by pcw.
    iEval (rewrite Hp0) in "Hpc".
    iApply (wp_addi4_s_sconf (CID := CID1) (mword_of_int (SU + 0x132)) Ra0 Ra0
              (mword_of_int 1374 : mword 12) P1 K b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1").
    iIntros (CID2 Hq2) "Hcg Hpc".
    pose (P2 := <[Regidx Ra0 := regval_into_reg
                   (add_vec (rget P1 Ra0)
                      (sign_extend' 64 (mword_of_int 1374 : mword 12)))]> P1).
    assert (Hp1 : add_vec_int (mword_of_int (SU + 0x132) : mword 64) 4
                  = mword_of_int (SU + 0x136)) by pcw.
    iEval (rewrite Hp1) in "Hpc".
    iApply (wp_jal_s_sconf (CID := CID2) (mword_of_int (SU + 0x136)) Rra
              (mword_of_int 2078562 : mword 21) P2 K b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2").
    iIntros (CID3 Hq3) "Hcg Hpc".
    assert (Htgt : add_vec (mword_of_int (SU + 0x136) : mword 64)
                     (sign_extend' 64 (mword_of_int 2078562 : mword 21))
                   = mword_of_int KernelSyms.panic) by pcw.
    iEval (rewrite Htgt) in "Hpc".
    (* the regfile the spec wants is the POST-JAL one: [wp_jal_s_sconf] wrote
       [ra].  a0 is untouched, but prove it on P3 directly -- deriving it
       across the write with [upd_ne] costs two orders of magnitude more. *)
    pose (P3 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (SU + 0x136) : mword 64) 4)]> P2).
    assert (Ha0 : P3 !!! Regidx Ra0 = (mword_of_int su_readi_a : mword 64)) by pcw.
    iPoseProof (su_readi_str with "Hkd") as "#Hstr".
    iDestruct (cpu_own_transport CID0 CID3 n eb pj b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (PN.wp_panic_sconf KT1 (CID := CID3) P3 K n eb b pj
              (PkAStr DfracDiscarded su_readi_s) lks
              HKp eq_refl Hn31 Hbelow
              with "Hcg Hown Htext Hkd Hpc Hpenv [Hstr]").
    { rewrite /pk_desc_res Ha0.
      iSplit; [iPureIntro; exact su_readi_nonul|].
      iSplit; [iPureIntro; exact su_readi_nz|]. iExact "Hstr". }
  Qed.

  Lemma su_panic_writei `{GEN : GenId} `{CID0 : CpuId}
      (M : regfile) (K : nat) (n : nat) (eb b : bool) (pj : mword 64)
      (lks : gset string) :
    (panic_stack <= K)%nat ->
    (Z.of_nat n + 2 < 2 ^ 31)%Z ->
    locks_below lks "pr" ->
    sie_cap_gpr KT1 M K b pj -∗
    cpu_own n eb pj b lks -∗
    kernel_text -∗ kernel_data -∗ panic_env -∗
    pc_is (mword_of_int (SU + 0x13a)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKp Hn31 Hbelow.
    iIntros "Hcg Hown #Htext #Hkd #Hpenv Hpc".
    iPoseProof (suli_13a with "Htext") as "Hi0".
    iPoseProof (suli_13e with "Htext") as "Hi1".
    iPoseProof (suli_142 with "Htext") as "Hi2".
    iApply (wp_auipc_s_sconf (CID := CID0) (mword_of_int (SU + 0x13a)) Ra0
              (mword_of_int 2 : mword 20) M K b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0").
    iIntros (CID1 Hq1) "Hcg Hpc".
    pose (P1 := <[Regidx Ra0 := regval_into_reg
                   (add_vec (mword_of_int (SU + 0x13a) : mword 64)
                      (auipc_off (mword_of_int 2 : mword 20)))]> M).
    assert (Hp0 : add_vec_int (mword_of_int (SU + 0x13a) : mword 64) 4
                  = mword_of_int (SU + 0x13e)) by pcw.
    iEval (rewrite Hp0) in "Hpc".
    iApply (wp_addi4_s_sconf (CID := CID1) (mword_of_int (SU + 0x13e)) Ra0 Ra0
              (mword_of_int 1386 : mword 12) P1 K b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1").
    iIntros (CID2 Hq2) "Hcg Hpc".
    pose (P2 := <[Regidx Ra0 := regval_into_reg
                   (add_vec (rget P1 Ra0)
                      (sign_extend' 64 (mword_of_int 1386 : mword 12)))]> P1).
    assert (Hp1 : add_vec_int (mword_of_int (SU + 0x13e) : mword 64) 4
                  = mword_of_int (SU + 0x142)) by pcw.
    iEval (rewrite Hp1) in "Hpc".
    iApply (wp_jal_s_sconf (CID := CID2) (mword_of_int (SU + 0x142)) Rra
              (mword_of_int 2078550 : mword 21) P2 K b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2").
    iIntros (CID3 Hq3) "Hcg Hpc".
    assert (Htgt : add_vec (mword_of_int (SU + 0x142) : mword 64)
                     (sign_extend' 64 (mword_of_int 2078550 : mword 21))
                   = mword_of_int KernelSyms.panic) by pcw.
    iEval (rewrite Htgt) in "Hpc".
    (* the regfile the spec wants is the POST-JAL one: [wp_jal_s_sconf] wrote
       [ra].  a0 is untouched, but prove it on P3 directly -- deriving it
       across the write with [upd_ne] costs two orders of magnitude more. *)
    pose (P3 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (SU + 0x142) : mword 64) 4)]> P2).
    assert (Ha0 : P3 !!! Regidx Ra0 = (mword_of_int su_writei_a : mword 64)) by pcw.
    iPoseProof (su_writei_str with "Hkd") as "#Hstr".
    iDestruct (cpu_own_transport CID0 CID3 n eb pj b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (PN.wp_panic_sconf KT1 (CID := CID3) P3 K n eb b pj
              (PkAStr DfracDiscarded su_writei_s) lks
              HKp eq_refl Hn31 Hbelow
              with "Hcg Hown Htext Hkd Hpc Hpenv [Hstr]").
    { rewrite /pk_desc_res Ha0.
      iSplit; [iPureIntro; exact su_writei_nonul|].
      iSplit; [iPureIntro; exact su_writei_nz|]. iExact "Hstr". }
  Qed.

  (* ================================================================== *)
  (*  ARM B: +0x0e2 jal end_op ; +0x0e6 c.li a0,-1 ;                     *)
  (*         +0x0e8 c.ldsp s1,216(sp) ; +0x0ea c.j +0x168                *)
  (*                                                                     *)
  (*  nameiparent returned 0.  begin_op HAS run, so the arm carries the  *)
  (*  op's remaining units and retires them; it holds no reference (the  *)
  (*  failing walker gave the whole allowance back) and nothing          *)
  (*  inode-shaped.  s2 and s3 are untouched -- both spills are below    *)
  (*  the branch at +0x2e -- so slots 4 and 5 ride through as junk.      *)
  (* ================================================================== *)
  Lemma su_tail_b `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (u : nat) (pidv : mword 32) (dq : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (w4 w5 w6 w27 w30 : mword 64) (bd bnm bp be : nat -> bv 8) :
    (K_end_op <= K - 30)%nat -> (30 <= K)%nat -> ((K - 30) + 30 = K)%nat ->
    log_geom_ok cov logstart ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    su_sp sp0 M -> su_thr m M ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    (M !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    su_al sp0 ->
    sie_cap_gpr KT1 M (K - 30) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SU + 0xe2)) -∗
    panic_env -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    p_pid (proc_addr jx) ↦₄{dq} pidv -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    log_op g u -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] w4 -∗
    (pa_stk sp0 5) ↦₈[KT1] w5 -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 8) jj ↦ₘ[KT1] bd jj) -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] bnm jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 26) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 27) ↦₈[KT1] w27 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ[KT1] be jj) -∗
    (pa_stk sp0 30) ↦₈[KT1] w30 -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
        cpu_own 0 eb (proc_addr jx) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr jx) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        p_pid (proc_addr jx) ↦₄{dq} pidv -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKeo HK30 Kpop Hgeom Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs2 HMs3 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen
              Hpid #Hprocs #Hdev #Hgeo #Hdlk Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
              HbD HbN HbP H27 HbE H30 Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    iPoseProof (suli_0e2 with "Htext") as "Hi0".
    iPoseProof (suli_0e6 with "Htext") as "Hi1".
    iPoseProof (suli_0e8 with "Htext") as "Hi2".
    iPoseProof (suli_0ea with "Htext") as "Hi3".
    (* ===== +0x0e2 jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID0) (mword_of_int (SU + 0xe2)) Rra
              (mword_of_int 2092174 : mword 21) M (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0xe2) : mword 64) 4)]> M).
    assert (Hjeo : add_vec (mword_of_int (SU + 0xe2) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092174 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0xe2) : mword 64) 4)
      by (rewrite /M1; apply upd_eq).
    assert (HM1sp : su_sp sp0 M1)
      by (rewrite /su_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs2 | nz]).
    assert (HM1s3 : (M1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs3 | nz]).
    assert (HM1thr : su_thr m M1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID0 CID1 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := CID1) gs jx gl gu gd gk pd pav pu bn
              g gfs cov logstart dev u pidv dq M1 (K - 30)%nat eb b lks
              HKeo Hgeom Hj Hgl ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hpid Hprocs Hdev Hgeo Hdlk Hop").
    iIntros (CID2 Hq2 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpid".
    assert (Hpce6 : ret_pc (M1 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0xe6)) by (rewrite HM1ra; pcw).
    iEval (rewrite Hpce6) in "Hpc".
    assert (Heosp : su_sp sp0 meo).
    { rewrite /su_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM1sp. }
    assert (Heos2 : (meo !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcseo Rs2 ltac:(vm_compute; reflexivity)).
      exact HM1s2. }
    assert (Heos3 : (meo !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcseo Rs3 ltac:(vm_compute; reflexivity)).
      exact HM1s3. }
    assert (Heothr : su_thr m meo).
    { intros c Hc N2 N8 N9 N18 N19. rewrite (callee_saved_lookup Hcseo c Hc).
      exact (HM1thr c Hc N2 N8 N9 N18 N19). }
    (* ===== +0x0e6 c.li a0,-1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID2) (mword_of_int (SU + 0xe6)) Ra0
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              meo (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi1").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (P1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> meo).
    assert (HP1a0 : (P1 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1sp : su_sp sp0 P1)
      by (rewrite /su_sp /P1 upd_ne; [exact Heosp | nz]).
    assert (HP1s2 : (P1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P1 upd_ne; [exact Heos2 | nz]).
    assert (HP1s3 : (P1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P1 upd_ne; [exact Heos3 | nz]).
    assert (HP1thr : su_thr m P1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P1 upd_ne; [| regne].
      exact (Heothr c Hc N2 N8 N9 N18 N19). }
    assert (Hppe8 : add_vec_int (mword_of_int (SU + 0xe6) : mword 64) 2
                    = mword_of_int (SU + 0xe8)) by pcw.
    iEval (rewrite Hppe8) in "Hpc".
    (* ===== +0x0e8 c.ldsp s1,216(sp) ===== *)
    assert (Hd3 : add_vec (P1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HP1sp; apply su_frm3).
    iApply (wp_cldsp_s_sconf (CID := CID3) (mword_of_int (SU + 0xe8))
              (mword_of_int 27 : mword 6) Rs1 P1 (K - 30)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi2 [Hf3]").
    { iEval (rewrite Hd3). iExact "Hf3". }
    iIntros (CID4 Hq4) "Hcg Hpc Hf3".
    iEval (rewrite Hd3) in "Hf3".
    set (P2 := <[Regidx Rs1 := regval_into_reg
                  (m !!! Regidx Rs1 : mword 64)]> P1).
    assert (HP2s1 : (P2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /P2; apply upd_eq).
    assert (HP2a0 : (P2 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1a0 | nz]).
    assert (HP2sp : su_sp sp0 P2)
      by (rewrite /su_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2s2 : (P2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s2 | nz]).
    assert (HP2s3 : (P2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s3 | nz]).
    assert (HP2thr : su_thr m P2).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hc N2 N8 N9 N18 N19). }
    assert (Hppea : add_vec_int (mword_of_int (SU + 0xe8) : mword 64) 2
                    = mword_of_int (SU + 0xea)) by pcw.
    iEval (rewrite Hppea) in "Hpc".
    (* ===== +0x0ea c.j +0x168 ===== *)
    iApply (wp_cj_s_sconf (CID := CID4) (mword_of_int (SU + 0xea))
              (sign_extend' 21 (concat_vec (mword_of_int 63 : mword 11) ('b"0")))
              P2 (K - 30)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi3").
    iIntros (CID5 Hq5). iNext. iIntros "Hcg Hpc".
    assert (Htg : add_vec (mword_of_int (SU + 0xea) : mword 64)
                    (sign_extend' 64
                       (sign_extend' 21 (concat_vec (mword_of_int 63 : mword 11) ('b"0"))))
                  = mword_of_int (SU + 0x168)) by pcw.
    iEval (rewrite Htg) in "Hpc".
    iDestruct (cpu_own_transport CID2 CID5 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID2 CID5 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID2 CID5 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID5)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (su_epilogue (CID0 := CID5) m P2 sp0 K b (proc_addr jx)
              (m !!! Regidx Rs1 : mword 64) w4 w5 w6 w27 w30 bd bnm bp be
              HK30 Kpop Hsp0 HP2sp HP2thr HP2s1 HP2s2 HP2s3 Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD HbN HbP H27
                    HbE H30 [Hown Htce Hcce Hpid Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
    iDestruct (cpu_own_transport CID5 CIDy 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID5 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID5 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf with "[%] [%] Hcg Hown Htce Hcce Hpc Hpid").
    { exact Hcsf. }
    { rewrite Ha0f. exact HP2a0. }
  Qed.

  (* ================================================================== *)
  (*  THE [bad:] TAIL, +0x15a .. +0x166 -- the shared "-1" exit that      *)
  (*  ARMS C, C', D and E all reach.                                     *)
  (*                                                                     *)
  (*    +0x15a c.mv a0,s1 ; +0x15c jal iunlockput                        *)
  (*    +0x160 jal end_op ; +0x164 c.li a0,-1                             *)
  (*    +0x166 c.ldsp s1,216(sp) ; FALL into the epilogue at +0x168       *)
  (*                                                                     *)
  (*  IT SPENDS NOTHING BUT [iput_units].  Every route here is ABOVE the  *)
  (*  zeroing [writei], so no arm has logged [IBLOCK dp] and none holds a *)
  (*  credit -- the COUNTED [wp_iunlockput_sconf] is what it calls, and   *)
  (*  [SysUnlinkBudget.su_bad_early_closes] is the ledger's word that the *)
  (*  three are there.  It holds no [ilink] either: the release happens   *)
  (*  at the zeroing and every branch into [bad:] is above it.            *)
  (*                                                                     *)
  (*  s2 AND s3 ARE ALREADY WHATEVER THE ENTRY MADE THEM.  ARM D reloads  *)
  (*  s2 at +0x158 and ARM E reloads both at +0x17a/+0x17c before jumping *)
  (*  here, and ARMS C/C' never touched either; so both are the caller's  *)
  (*  by the time this block runs, which is why they are PREMISES and     *)
  (*  their slots ride through at existential words.                      *)
  (* ================================================================== *)
  Lemma su_tail_bad `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used : gset Z)
      (kk : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (u : nat) (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (w4 w5 w6 w27 w30 : mword 64) (bd bnm bp be : nat -> bv 8) :
    (K_iunlockput <= K - 30)%nat -> (K_end_op <= K - 30)%nat ->
    (30 <= K)%nat -> ((K - 30) + 30 = K)%nat ->
    (kk < NINODE)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    cov_below cov size ->
    (iput_units <= u)%nat ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    su_sp sp0 M -> su_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    (M !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    su_al sp0 ->
    sie_cap_gpr KT1 M (K - 30) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SU + 0x15a)) -∗
    panic_env -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrow cn gfs gi cov logstart kk -∗
    ireg_inv gi gfs inodestart nib -∗
    is_sleeplock_gen gil gisl (i_lock (ientry kk)) "inode"%string (ic_tok cn kk) (slh_tok (icfg_isl kk)) -∗
    sleeplocked_q gisl s -∗
    sl_pid (i_lock (ientry kk)) ↦₄ pidv -∗
    ic_deposit cn kk (DepShr s dev inum gy) -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    inode_ref_short kk (qi + s)%Qp qi dev inum -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used -∗
    p_pid (proc_addr jx) ↦₄{dq} pidv -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots bn 3 -∗
    log_op g u -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] w4 -∗
    (pa_stk sp0 5) ↦₈[KT1] w5 -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 8) jj ↦ₘ[KT1] bd jj) -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] bnm jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 26) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 27) ↦₈[KT1] w27 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ[KT1] be jj) -∗
    (pa_stk sp0 30) ↦₈[KT1] w30 -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z),
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
        cpu_own 0 eb (proc_addr jx) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr jx) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        p_pid (proc_addr jx) ↦₄{dq} pidv -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        bitmap_res gfs bmapstart cov logstart size used' -∗
        bslots bn 3 -∗
        iref_slot -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKup HKeo HK30 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk
           Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs1 HMs2
           HMs3 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen
              #Hitab #Hitinv #Hesck #Hireg #Hslkk Hslkd Hslpid Hdep Hidev
              Hiinum Hivalid Hload #Hshot Hkeep Hsbb Hsbi Hbmres Hpid #Hprocs
              #Hdev #Hgeo #Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD HbN HbP
              H27 HbE H30 Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    iPoseProof (suli_15a with "Htext") as "Hi0".
    iPoseProof (suli_15c with "Htext") as "Hi1".
    iPoseProof (suli_160 with "Htext") as "Hi2".
    iPoseProof (suli_164 with "Htext") as "Hi3".
    iPoseProof (suli_166 with "Htext") as "Hi4".
    (* ===== +0x15a c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID0) (mword_of_int (SU + 0x15a)) Ra0 Rs1
              M (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M !!! Regidx Rs1))]> M).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = ientry kk).
    { etransitivity; [ rewrite /M1; apply upd_eq |].
      rewrite add_vec_zero_l. exact HMs1. }
    assert (HM1sp : su_sp sp0 M1)
      by (rewrite /su_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs2 | nz]).
    assert (HM1s3 : (M1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs3 | nz]).
    assert (HM1thr : su_thr m M1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp15c : add_vec_int (mword_of_int (SU + 0x15a) : mword 64) 2
                     = mword_of_int (SU + 0x15c)) by pcw.
    iEval (rewrite Hpp15c) in "Hpc".
    (* ===== +0x15c jal ra,iunlockput ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SU + 0x15c)) Rra
              (mword_of_int 2089842 : mword 21) M1 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0x15c) : mword 64) 4)]> M1).
    assert (Hjup : add_vec (mword_of_int (SU + 0x15c) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089842 : mword 21))
                   = mword_of_int KernelSyms.iunlockput) by pcw.
    iEval (rewrite Hjup) in "Hpc".
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0x15c) : mword 64) 4)
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = ientry kk)
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2sp : su_sp sp0 M2)
      by (rewrite /su_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2s2 : (M2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s2 | nz]).
    assert (HM2s3 : (M2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s3 | nz]).
    assert (HM2thr : su_thr m M2).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID2 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID2 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (Iunlockput.wp_iunlockput_sconf (CID := CID2) gs jx gl gu gd gk
              pd pav pu bn g gfs gi cn gtl gil gisl cov logstart bmapstart
              inodestart nib size dev used kk qi s gy inum dn bm u pidv dq
              dqb dqs M2 (K - 30)%nat eb b lks
              HKup Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog
              Hinb Hcovb Hiu Hj Hgl HM2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hitab Hitinv
                    Hesck Hireg Hslkk Hslkd Hslpid Hdep Hidev Hiinum Hivalid
                    Hload Hshot Hkeep Hsbb Hsbi Hbmres Hpid Hprocs Hdev Hgeo
                    Hdlk Hbsl Hop").
    iIntros (CID3 Hq3 mup n2 used2)
      "%Hcsup Hcg Hown Htce Hcce Hpc Hpid Hsbb Hsbi %Hused2 Hbmres Hbsl %Hn2
       Hop Hislot".
    assert (Hpc160 : ret_pc (M2 !!! Regidx Rra : mword 64)
                     = mword_of_int (SU + 0x160)) by (rewrite HM2ra; pcw).
    iEval (rewrite Hpc160) in "Hpc".
    assert (Hupsp : su_sp sp0 mup).
    { rewrite /su_sp (callee_saved_lookup Hcsup csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM2sp. }
    assert (Hups2 : (mup !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcsup Rs2 ltac:(vm_compute; reflexivity)).
      exact HM2s2. }
    assert (Hups3 : (mup !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcsup Rs3 ltac:(vm_compute; reflexivity)).
      exact HM2s3. }
    assert (Hupthr : su_thr m mup).
    { intros c Hc N2 N8 N9 N18 N19. rewrite (callee_saved_lookup Hcsup c Hc).
      exact (HM2thr c Hc N2 N8 N9 N18 N19). }
    (* ===== +0x160 jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID3) (mword_of_int (SU + 0x160)) Rra
              (mword_of_int 2092048 : mword 21) mup (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (Q1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0x160) : mword 64) 4)]> mup).
    assert (Hjeo : add_vec (mword_of_int (SU + 0x160) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092048 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HQ1ra : (Q1 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0x160) : mword 64) 4)
      by (rewrite /Q1; apply upd_eq).
    assert (HQ1sp : su_sp sp0 Q1)
      by (rewrite /su_sp /Q1 upd_ne; [exact Hupsp | nz]).
    assert (HQ1s2 : (Q1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /Q1 upd_ne; [exact Hups2 | nz]).
    assert (HQ1s3 : (Q1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /Q1 upd_ne; [exact Hups3 | nz]).
    assert (HQ1thr : su_thr m Q1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /Q1 upd_ne; [| regne].
      exact (Hupthr c Hc N2 N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID3 CID4 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := CID4) gs jx gl gu gd gk pd pav pu bn
              g gfs cov logstart dev n2 pidv dq Q1 (K - 30)%nat eb b lks
              HKeo Hgeom Hj Hgl ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hpid Hprocs Hdev Hgeo Hdlk Hop").
    iIntros (CID5 Hq5 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpid".
    assert (Hpc164 : ret_pc (Q1 !!! Regidx Rra : mword 64)
                     = mword_of_int (SU + 0x164)) by (rewrite HQ1ra; pcw).
    iEval (rewrite Hpc164) in "Hpc".
    assert (Heosp : su_sp sp0 meo).
    { rewrite /su_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HQ1sp. }
    assert (Heos2 : (meo !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcseo Rs2 ltac:(vm_compute; reflexivity)).
      exact HQ1s2. }
    assert (Heos3 : (meo !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcseo Rs3 ltac:(vm_compute; reflexivity)).
      exact HQ1s3. }
    assert (Heothr : su_thr m meo).
    { intros c Hc N2 N8 N9 N18 N19. rewrite (callee_saved_lookup Hcseo c Hc).
      exact (HQ1thr c Hc N2 N8 N9 N18 N19). }
    (* ===== +0x164 c.li a0,-1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID5) (mword_of_int (SU + 0x164)) Ra0
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              meo (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi3").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (R1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> meo).
    assert (HR1a0 : (R1 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /R1; apply upd_eq).
    assert (HR1sp : su_sp sp0 R1)
      by (rewrite /su_sp /R1 upd_ne; [exact Heosp | nz]).
    assert (HR1s2 : (R1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /R1 upd_ne; [exact Heos2 | nz]).
    assert (HR1s3 : (R1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /R1 upd_ne; [exact Heos3 | nz]).
    assert (HR1thr : su_thr m R1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /R1 upd_ne; [| regne].
      exact (Heothr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp166 : add_vec_int (mword_of_int (SU + 0x164) : mword 64) 2
                     = mword_of_int (SU + 0x166)) by pcw.
    iEval (rewrite Hpp166) in "Hpc".
    (* ===== +0x166 c.ldsp s1,216(sp) ===== *)
    assert (Hd3 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HR1sp; apply su_frm3).
    iApply (wp_cldsp_s_sconf (CID := CID6) (mword_of_int (SU + 0x166))
              (mword_of_int 27 : mword 6) Rs1 R1 (K - 30)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi4 [Hf3]").
    { iEval (rewrite Hd3). iExact "Hf3". }
    iIntros (CID7 Hq7) "Hcg Hpc Hf3".
    iEval (rewrite Hd3) in "Hf3".
    set (R2 := <[Regidx Rs1 := regval_into_reg
                  (m !!! Regidx Rs1 : mword 64)]> R1).
    assert (HR2s1 : (R2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /R2; apply upd_eq).
    assert (HR2a0 : (R2 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /R2 upd_ne; [exact HR1a0 | nz]).
    assert (HR2sp : su_sp sp0 R2)
      by (rewrite /su_sp /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2s2 : (R2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /R2 upd_ne; [exact HR1s2 | nz]).
    assert (HR2s3 : (R2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /R2 upd_ne; [exact HR1s3 | nz]).
    assert (HR2thr : su_thr m R2).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /R2 upd_ne; [| regne].
      exact (HR1thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp168 : add_vec_int (mword_of_int (SU + 0x166) : mword 64) 2
                     = mword_of_int (SU + 0x168)) by pcw.
    iEval (rewrite Hpp168) in "Hpc".
    (* ===== the epilogue, entered by FALLING THROUGH ===== *)
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID7)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (su_epilogue (CID0 := CID7) m R2 sp0 K b (proc_addr jx)
              (m !!! Regidx Rs1 : mword 64) w4 w5 w6 w27 w30 bd bnm bp be
              HK30 Kpop Hsp0 HR2sp HR2thr HR2s1 HR2s2 HR2s3 Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD HbN HbP H27
                    HbE H30 [Hown Htce Hcce Hpid Hsbb Hsbi Hbmres Hbsl
                             Hislot Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
    iDestruct (cpu_own_transport CID5 CIDy 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID5 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID5 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf used2 with "[%] [%] Hcg Hown Htce Hcce Hpc Hpid
              Hsbb Hsbi Hbmres Hbsl Hislot").
    { exact Hcsf. }
    { rewrite Ha0f. exact HR2a0. }
  Qed.

  (* ================================================================== *)
  (*  ARM D's ENTRY: +0x158 c.ldsp s2,208(sp), then FALL into [bad:].     *)
  (*                                                                     *)
  (*  [dirlookup] returned 0, and the [c.mv s2,a0] at +0x6c has just put  *)
  (*  that 0 in s2 -- so the one instruction the arm owns is the reload   *)
  (*  of the caller's s2 out of the slot the [c.sdsp] at +0x5c filled.    *)
  (*  s3 is untouched: its spill is at +0x72, BELOW this branch.          *)
  (* ================================================================== *)
  Lemma su_tail_d `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used : gset Z)
      (kk : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (u : nat) (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (w5 w6 w27 w30 : mword 64) (bd bnm bp be : nat -> bv 8) :
    (K_iunlockput <= K - 30)%nat -> (K_end_op <= K - 30)%nat ->
    (30 <= K)%nat -> ((K - 30) + 30 = K)%nat ->
    (kk < NINODE)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    cov_below cov size ->
    (iput_units <= u)%nat ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    su_sp sp0 M -> su_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    su_al sp0 ->
    sie_cap_gpr KT1 M (K - 30) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SU + 0x158)) -∗
    panic_env -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrow cn gfs gi cov logstart kk -∗
    ireg_inv gi gfs inodestart nib -∗
    is_sleeplock_gen gil gisl (i_lock (ientry kk)) "inode"%string (ic_tok cn kk) (slh_tok (icfg_isl kk)) -∗
    sleeplocked_q gisl s -∗
    sl_pid (i_lock (ientry kk)) ↦₄ pidv -∗
    ic_deposit cn kk (DepShr s dev inum gy) -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    inode_ref_short kk (qi + s)%Qp qi dev inum -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used -∗
    p_pid (proc_addr jx) ↦₄{dq} pidv -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots bn 3 -∗
    log_op g u -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
    (pa_stk sp0 5) ↦₈[KT1] w5 -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 8) jj ↦ₘ[KT1] bd jj) -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] bnm jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 26) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 27) ↦₈[KT1] w27 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ[KT1] be jj) -∗
    (pa_stk sp0 30) ↦₈[KT1] w30 -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z),
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
        cpu_own 0 eb (proc_addr jx) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr jx) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        p_pid (proc_addr jx) ↦₄{dq} pidv -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        bitmap_res gfs bmapstart cov logstart size used' -∗
        bslots bn 3 -∗
        iref_slot -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKup HKeo HK30 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk
           Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs1 HMs3 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen
              #Hitab #Hitinv #Hesck #Hireg #Hslkk Hslkd Hslpid Hdep Hidev
              Hiinum Hivalid Hload #Hshot Hkeep Hsbb Hsbi Hbmres Hpid #Hprocs
              #Hdev #Hgeo #Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD HbN HbP
              H27 HbE H30 Hcont".
    iPoseProof (suli_158 with "Htext") as "Hi0".
    (* ===== +0x158 c.ldsp s2,208(sp) ===== *)
    assert (Hd4 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 26 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HMsp; apply su_frm4).
    iApply (wp_cldsp_s_sconf (CID := CID0) (mword_of_int (SU + 0x158))
              (mword_of_int 26 : mword 6) Rs2 M (K - 30)%nat
              (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi0 [Hf4]").
    { iEval (rewrite Hd4). iExact "Hf4". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf4".
    iEval (rewrite Hd4) in "Hf4".
    set (M1 := <[Regidx Rs2 := regval_into_reg
                  (m !!! Regidx Rs2 : mword 64)]> M).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1; apply upd_eq).
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M1 upd_ne; [exact HMs1 | nz]).
    assert (HM1s3 : (M1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs3 | nz]).
    assert (HM1sp : su_sp sp0 M1)
      by (rewrite /su_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1thr : su_thr m M1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp15a : add_vec_int (mword_of_int (SU + 0x158) : mword 64) 2
                     = mword_of_int (SU + 0x15a)) by pcw.
    iEval (rewrite Hpp15a) in "Hpc".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID1)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iDestruct (cpu_own_transport CID0 CID1 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    iDestruct (trap_csrs_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (su_tail_bad (CID0 := CID1) gs jx gl gu gd gk pd pav pu bn g gfs gi
              cn gtl gil gisl cov logstart bmapstart inodestart nib size dev
              used kk qi s gy inum dn bm u pidv dq dqb dqs m M1 sp0 K eb b lks
              (m !!! Regidx Rs2 : mword 64) w5 w6 w27 w30 bd bnm bp be
              HKup HKeo HK30 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
              Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HM1sp HM1thr
              HM1s1 HM1s2 HM1s3 Hal
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hitab Hitinv Hesck Hireg Hslkk Hslkd Hslpid Hdep Hidev
                    Hiinum Hivalid Hload Hshot Hkeep Hsbb Hsbi Hbmres Hpid
                    Hprocs Hdev Hgeo Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
                    HbD HbN HbP H27 HbE H30 Hcont").
  Qed.

  (* ================================================================== *)
  (*  ARM E's ENTRY: +0x174 .. +0x17e -- [ip->type == T_DIR] and the      *)
  (*  inlined isdirempty found a live non-dot record.                    *)
  (*                                                                     *)
  (*    +0x174 c.mv a0,s2 ; +0x176 jal iunlockput      (release ip)       *)
  (*    +0x17a c.ldsp s2,208(sp) ; +0x17c c.ldsp s3,200(sp)               *)
  (*    +0x17e c.j +0x15a                              (into [bad:])      *)
  (*                                                                     *)
  (*  THE ONLY ARM HOLDING TWO LOCKED INODES.  It releases [ip] here and  *)
  (*  [dp] in [bad:], so the reference allowance comes back in TWO        *)
  (*  pieces and the log ledger pays [iput_units] twice.  The premise is  *)
  (*  therefore [2 * iput_units <= u] -- six against the nine or ten the  *)
  (*  op still holds, which is [SysUnlinkBudget.su_bad_isdirempty_closes] *)
  (*  read through the COUNTED contract's interval rather than through    *)
  (*  [ip_spend_w]: the counted form is weaker and it is enough, because  *)
  (*  neither free is credited (nothing has logged either inode's block). *)
  (*                                                                     *)
  (*  BOTH SPILLS ARE RELOADED HERE, and that is what lets [bad:] keep    *)
  (*  its s2/s3 equations as premises: +0x5c and +0x72 are both above     *)
  (*  the [c.bnez] at +0x120 that reaches this block.                     *)
  (* ================================================================== *)
  Lemma su_tail_e `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (gil gisl : gname) (gili gisli : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used : gset Z)
      (kk : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (ki : nat) (qip si : Qp) (gyi : gname) (inumi : mword 32)
      (dni : dinode) (bmi : blkmap)
      (u : nat) (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (w6 w27 w30 : mword 64) (bd bnm bp be : nat -> bv 8) :
    (K_iunlockput <= K - 30)%nat -> (K_end_op <= K - 30)%nat ->
    (30 <= K)%nat -> ((K - 30) + 30 = K)%nat ->
    (kk < NINODE)%nat -> (ki < NINODE)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    IBLOCK inumi inodestart ∈ cov ->
    ~ (IBLOCK inumi inodestart ∈ log_region_set logstart) ->
    bv_unsigned inumi < 16 * Z.of_nat nib ->
    cov_below cov size ->
    (2 * iput_units <= u)%nat ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    su_sp sp0 M -> su_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs2 : mword 64) = ientry ki ->
    su_al sp0 ->
    sie_cap_gpr KT1 M (K - 30) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SU + 0x174)) -∗
    panic_env -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrow cn gfs gi cov logstart kk -∗
    ic_escrow cn gfs gi cov logstart ki -∗
    ireg_inv gi gfs inodestart nib -∗
    (* ---- dp, still locked: released in [bad:] ---- *)
    is_sleeplock_gen gil gisl (i_lock (ientry kk)) "inode"%string (ic_tok cn kk) (slh_tok (icfg_isl kk)) -∗
    sleeplocked_q gisl s -∗
    sl_pid (i_lock (ientry kk)) ↦₄ pidv -∗
    ic_deposit cn kk (DepShr s dev inum gy) -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    inode_ref_short kk (qi + s)%Qp qi dev inum -∗
    (* ---- ip, released HERE ---- *)
    is_sleeplock_gen gili gisli (i_lock (ientry ki)) "inode"%string (ic_tok cn ki) (slh_tok (icfg_isl ki)) -∗
    sleeplocked_q gisli si -∗
    sl_pid (i_lock (ientry ki)) ↦₄ pidv -∗
    ic_deposit cn ki (DepShr si dev inumi gyi) -∗
    i_dev (ientry ki) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry ki) ↦₄{DfracOwn (1/2)} inumi -∗
    i_valid (ientry ki) ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart ki inumi dni bmi -∗
    ity_shot gyi (di_type dni) -∗
    inode_ref_short ki (qip + si)%Qp qip dev inumi -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used -∗
    p_pid (proc_addr jx) ↦₄{dq} pidv -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots bn 3 -∗
    log_op g u -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
    (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 8) jj ↦ₘ[KT1] bd jj) -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] bnm jj) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 26) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 27) ↦₈[KT1] w27 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ[KT1] be jj) -∗
    (pa_stk sp0 30) ↦₈[KT1] w30 -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z),
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
        cpu_own 0 eb (proc_addr jx) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr jx) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        p_pid (proc_addr jx) ↦₄{dq} pidv -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        bitmap_res gfs bmapstart cov logstart size used' -∗
        bslots bn 3 -∗
        iref_slots 2 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKup HKeo HK30 Kpop Hkk Hki Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
           Hiblk Hiblog Hinb Hiblki Hiblogi Hinbi Hcovb Hiu Hj Hgl Hlkempty
           Hsp0 HMsp HMthr HMs1 HMs2 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen
              #Hitab #Hitinv #Hesck #Hescki #Hireg
              #Hslkk Hslkd Hslpid Hdep Hidev Hiinum Hivalid Hload #Hshot Hkeep
              #Hslkki Hslkdi Hslpidi Hdepi Hidevi Hiinumi Hivalidi Hloadi
              #Hshoti Hkeepi
              Hsbb Hsbi Hbmres Hpid #Hprocs #Hdev #Hgeo #Hdlk Hbsl Hop
              Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD HbN HbP H27 HbE H30 Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    iPoseProof (suli_174 with "Htext") as "Hi0".
    iPoseProof (suli_176 with "Htext") as "Hi1".
    iPoseProof (suli_17a with "Htext") as "Hi2".
    iPoseProof (suli_17c with "Htext") as "Hi3".
    iPoseProof (suli_17e with "Htext") as "Hi4".
    (* ===== +0x174 c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID0) (mword_of_int (SU + 0x174)) Ra0 Rs2
              M (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M !!! Regidx Rs2))]> M).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = ientry ki).
    { etransitivity; [ rewrite /M1; apply upd_eq |].
      rewrite add_vec_zero_l. exact HMs2. }
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M1 upd_ne; [exact HMs1 | nz]).
    assert (HM1sp : su_sp sp0 M1)
      by (rewrite /su_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1thr : su_thr m M1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp176 : add_vec_int (mword_of_int (SU + 0x174) : mword 64) 2
                     = mword_of_int (SU + 0x176)) by pcw.
    iEval (rewrite Hpp176) in "Hpc".
    (* ===== +0x176 jal ra,iunlockput ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SU + 0x176)) Rra
              (mword_of_int 2089816 : mword 21) M1 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0x176) : mword 64) 4)]> M1).
    assert (Hjup : add_vec (mword_of_int (SU + 0x176) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089816 : mword 21))
                   = mword_of_int KernelSyms.iunlockput) by pcw.
    iEval (rewrite Hjup) in "Hpc".
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0x176) : mword 64) 4)
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = ientry ki)
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2s1 : (M2 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M2 upd_ne; [exact HM1s1 | nz]).
    assert (HM2sp : su_sp sp0 M2)
      by (rewrite /su_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2thr : su_thr m M2).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID2 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID2 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (Iunlockput.wp_iunlockput_sconf (CID := CID2) gs jx gl gu gd gk
              pd pav pu bn g gfs gi cn gtl gili gisli cov logstart bmapstart
              inodestart nib size dev used ki qip si gyi inumi dni bmi u pidv
              dq dqb dqs M2 (K - 30)%nat eb b lks
              HKup Hki Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblki Hiblogi
              Hinbi Hcovb ltac:(unfold iput_units in *; lia) Hj Hgl HM2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hitab Hitinv
                    Hescki Hireg Hslkki Hslkdi Hslpidi Hdepi Hidevi Hiinumi
                    Hivalidi Hloadi Hshoti Hkeepi Hsbb Hsbi Hbmres Hpid Hprocs
                    Hdev Hgeo Hdlk Hbsl Hop").
    iIntros (CID3 Hq3 mup n2 used2)
      "%Hcsup Hcg Hown Htce Hcce Hpc Hpid Hsbb Hsbi %Hused2 Hbmres Hbsl %Hn2
       Hop Hislot".
    assert (Hpc17a : ret_pc (M2 !!! Regidx Rra : mword 64)
                     = mword_of_int (SU + 0x17a)) by (rewrite HM2ra; pcw).
    iEval (rewrite Hpc17a) in "Hpc".
    assert (Hupsp : su_sp sp0 mup).
    { rewrite /su_sp (callee_saved_lookup Hcsup csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM2sp. }
    assert (Hups1 : (mup !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite (callee_saved_lookup Hcsup Rs1 ltac:(vm_compute; reflexivity)).
      exact HM2s1. }
    assert (Hupthr : su_thr m mup).
    { intros c Hc N2 N8 N9 N18 N19. rewrite (callee_saved_lookup Hcsup c Hc).
      exact (HM2thr c Hc N2 N8 N9 N18 N19). }
    (* ===== +0x17a c.ldsp s2,208(sp) ===== *)
    assert (Hd4 : add_vec (mup !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 26 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite Hupsp; apply su_frm4).
    iApply (wp_cldsp_s_sconf (CID := CID3) (mword_of_int (SU + 0x17a))
              (mword_of_int 26 : mword 6) Rs2 mup (K - 30)%nat
              (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi2 [Hf4]").
    { iEval (rewrite Hd4). iExact "Hf4". }
    iIntros (CID4 Hq4) "Hcg Hpc Hf4".
    iEval (rewrite Hd4) in "Hf4".
    set (P1 := <[Regidx Rs2 := regval_into_reg
                  (m !!! Regidx Rs2 : mword 64)]> mup).
    assert (HP1s2 : (P1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1s1 : (P1 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /P1 upd_ne; [exact Hups1 | nz]).
    assert (HP1sp : su_sp sp0 P1)
      by (rewrite /su_sp /P1 upd_ne; [exact Hupsp | nz]).
    assert (HP1thr : su_thr m P1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P1 upd_ne; [| regne].
      exact (Hupthr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp17c : add_vec_int (mword_of_int (SU + 0x17a) : mword 64) 2
                     = mword_of_int (SU + 0x17c)) by pcw.
    iEval (rewrite Hpp17c) in "Hpc".
    (* ===== +0x17c c.ldsp s3,200(sp) ===== *)
    assert (Hd5 : add_vec (P1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 25 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (rewrite HP1sp; apply su_frm5).
    iApply (wp_cldsp_s_sconf (CID := CID4) (mword_of_int (SU + 0x17c))
              (mword_of_int 25 : mword 6) Rs3 P1 (K - 30)%nat
              (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi3 [Hf5]").
    { iEval (rewrite Hd5). iExact "Hf5". }
    iIntros (CID5 Hq5) "Hcg Hpc Hf5".
    iEval (rewrite Hd5) in "Hf5".
    set (P2 := <[Regidx Rs3 := regval_into_reg
                  (m !!! Regidx Rs3 : mword 64)]> P1).
    assert (HP2s3 : (P2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P2; apply upd_eq).
    assert (HP2s2 : (P2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s2 | nz]).
    assert (HP2s1 : (P2 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /P2 upd_ne; [exact HP1s1 | nz]).
    assert (HP2sp : su_sp sp0 P2)
      by (rewrite /su_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : su_thr m P2).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp17e : add_vec_int (mword_of_int (SU + 0x17c) : mword 64) 2
                     = mword_of_int (SU + 0x17e)) by pcw.
    iEval (rewrite Hpp17e) in "Hpc".
    (* ===== +0x17e c.j +0x15a ===== *)
    iApply (wp_cj_s_sconf (CID := CID5) (mword_of_int (SU + 0x17e))
              (sign_extend' 21 (concat_vec (mword_of_int 2030 : mword 11) ('b"0")))
              P2 (K - 30)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi4").
    iIntros (CID6 Hq6). iNext. iIntros "Hcg Hpc".
    assert (Htg : add_vec (mword_of_int (SU + 0x17e) : mword 64)
                    (sign_extend' 64
                       (sign_extend' 21 (concat_vec (mword_of_int 2030 : mword 11) ('b"0"))))
                  = mword_of_int (SU + 0x15a)) by pcw.
    iEval (rewrite Htg) in "Hpc".
    iDestruct (cpu_own_transport CID3 CID6 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID3 CID6 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID3 CID6 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID6)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (su_tail_bad (CID0 := CID6) gs jx gl gu gd gk pd pav pu bn g gfs gi
              cn gtl gil gisl cov logstart bmapstart inodestart nib size dev
              used2 kk qi s gy inum dn bm n2 pidv dq dqb dqs m P2 sp0 K eb b
              lks (m !!! Regidx Rs2 : mword 64) (m !!! Regidx Rs3 : mword 64)
              w6 w27 w30 bd bnm bp be
              HKup HKeo HK30 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
              Hiblk Hiblog Hinb Hcovb ltac:(unfold iput_units in *; lia)
              Hj Hgl Hlkempty Hsp0 HP2sp HP2thr HP2s1 HP2s2 HP2s3 Hal
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hitab Hitinv Hesck Hireg Hslkk Hslkd Hslpid Hdep Hidev
                    Hiinum Hivalid Hload Hshot Hkeep Hsbb Hsbi Hbmres Hpid
                    Hprocs Hdev Hgeo Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
                    HbD HbN HbP H27 HbE H30 [Hislot Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf used3) "%Hcsf %Ha0f Hcg Hown Htce Hcce
              Hpc Hpid Hsbb Hsbi Hbmres Hbsl Hislot2".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iDestruct (iref_slots_combine 1 1 with "Hislot Hislot2") as "Hislots".
    iApply ("Hcont" $! mf used3 with "[%] [%] Hcg Hown Htce Hcce Hpc Hpid
              Hsbb Hsbi Hbmres Hbsl Hislots").
    { exact Hcsf. }
    { exact Ha0f. }
  Qed.

End ProofSysUnlinkTails.

End SysUnlinkTails.
