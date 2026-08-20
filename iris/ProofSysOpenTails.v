(* ProofSysOpenTails.v -- sys_open's FAILURE tails, as block lemmas.  They
   apply callees' contracts, so they live inside a module functor
   ([design/spec-modules.md]); the functor is NOT ascribed to a signature,
   because it is a parts layer -- [ProofSysOpen.v] instantiates it beside its
   own callee arguments and the seal happens there.

   The eight arms of sys_open leave through six blocks, and ARM 0 is not one
   of them: the [bltz a5] at +0x24 targets the EPILOGUE directly (a0 was
   already set to -1 at +0x22), so ARM 0 is [ProofSysOpenParts.so_epilogue]
   applied in the walk with no tail at all.  What is left:

     ARM A-FAIL  (+0xd2 .. +0xda)   create returned 0
                                    end_op; a0 = -1; restore s1; join
     ARM B-FAIL  (+0x10c .. +0x114) namei returned 0
                                    the same four instructions at another
                                    address
     ARM C-FAIL  (+0xfc .. +0x10a)  a T_DIR inode opened for writing
                                    iunlockput(ip); end_op; a0 = -1;
                                    restore s1; join
     ARM D-FAIL  (+0x116 .. +0x124) T_DEVICE with an out-of-range major
                                    ARM C's six instructions, shifted
     ARM E-FAIL  (+0x12e .. +0x13e) filealloc returned 0
                                    ARM C's six plus the s2 reload, because
                                    the [c.sdsp s2] at +0x5e is ABOVE this
                                    branch and below C's and D's
     ARM F-FAIL  (+0x126 .. +0x12c) fdalloc refused
                                    fileclose(f); restore s3; FALL INTO
                                    ARM E-FAIL -- which is why it is the one
                                    tail that applies another one

   SIX BLOCKS, FIVE OF THEM THE SAME SHAPE, AND THEY ARE STILL SEPARATE
   LEMMAS.  Every decode fact ([soi_0d2] vs [soi_10c]) and every [pc_is]
   equation here is per-address, so a shared lemma would take its
   instructions and its pc equations as premises -- more interface than the
   duplication costs.  sys_link's tails file records the same ruling.

   THE REGISTER RELOADS ARE PART OF THE TAILS, NOT OF THE EPILOGUE.  The
   three callee-saved spills are SHRINK-WRAPPED ([c.sdsp s1] at +0x28,
   [sd s2] at +0x5e, [sd s3] at +0x68) and each arm restores exactly the
   subset its own path saved, so which of [M s1 = m s1], [M s2 = m s2],
   [M s3 = m s3] is a PREMISE and which is EARNED by a [c.ldsp] differs per
   tail -- and the frame slot the reload did not touch rides through as the
   caller's junk.

   WHY THE COUNTED [wp_iunlockput_sconf] IS WHAT C, D AND E CALL.  All three
   are entered at the JOIN's budget, which [SysOpenBudget.so_join_exact] puts
   at [iput_units] = three or better on both entry arms, and end_op takes
   [log_op] at any count.  None of them has anything credited to spend: the
   only thing sys_open ever logs is create's dirlink and the O_TRUNC tail,
   and every one of these branches is above the latter and inside (or before)
   the former. *)
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
Require Import RegFile WpNext.
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
Require Import IcacheBoot.
Require Import KallocInv.
Require Import FileInvDefs.
Require Import FileInv.
Require Import ProcInv.
Require Import SpecEndOp.
Require Import SpecIput.
Require Import SpecIunlock.
Require Import SpecIunlockput.
Require Import SpecFileclose.
Require Import CodeSysOpen.
Require Import ProofSysOpenParts.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Set Printing Depth 40.

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.

Module SysOpenTails (Iunlock : IUNLOCK) (Iunlockput : IUNLOCKPUT)
                    (EndOp : END_OP) (Fileclose : FILECLOSE).

Section ProofSysOpenTails.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  (* ================================================================== *)
  (*  ARM A-FAIL: +0xd2 end_op ; +0xd6 a0 = -1 ; +0xd8 restore s1 ;      *)
  (*  +0xda join.  create returned 0 -- nothing was locked and nothing   *)
  (*  was allocated, so this tail moves NO file-system resource at all   *)
  (*  and its continuation is the epilogue's plus the pid cell.          *)
  (*                                                                    *)
  (*  s2 and s3 are untouched on this route (both spills are BELOW the   *)
  (*  branch that reaches here), so their agreement is a premise and     *)
  (*  slots 4 and 5 ride through as the caller's junk.                   *)
  (* ================================================================== *)
  Lemma so_tail_a `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (u : nat) (pidv : mword 32) (dq : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w4 w5 w6 w23 w24 : mword 64)
      (bp : nat -> bv 8) :
    (K_end_op <= K - 24)%nat -> (24 <= K)%nat -> ((K - 24) + 24 = K)%nat ->
    log_geom_ok cov logstart ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    so_sp sp0 M -> so_thr m M ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    (M !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    so_al sp0 ->
    sie_cap_gpr KT1 M (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SO + 0xd2)) -∗
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
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 23) ↦₈[KT1] w23 -∗
    (pa_stk sp0 24) ↦₈[KT1] w24 -∗
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
    intros HKeo HK24 Kpop Hgeom Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs2 HMs3 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen
              Hpid #Hprocs #Hdev #Hgeo #Hdlk Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
              HbP H23 H24 Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    iPoseProof (soi_0d2 with "Htext") as "Hi0".
    iPoseProof (soi_0d6 with "Htext") as "Hi1".
    iPoseProof (soi_0d8 with "Htext") as "Hi2".
    iPoseProof (soi_0da with "Htext") as "Hi3".
    (* ===== +0xd2 jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID0) (mword_of_int (SO + 0xd2)) Rra
              (mword_of_int 2091806 : mword 21) M (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0xd2) : mword 64) 4)]> M).
    assert (Hjeo : add_vec (mword_of_int (SO + 0xd2) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091806 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0xd2) : mword 64) 4)
      by (rewrite /M1; apply upd_eq).
    assert (HM1sp : so_sp sp0 M1)
      by (rewrite /so_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs2 | nz]).
    assert (HM1s3 : (M1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs3 | nz]).
    assert (HM1thr : so_thr m M1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID0 CID1 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := CID1) gs jx gl gu gd gk pd pav pu bn
              g gfs cov logstart dev u pidv dq M1 (K - 24)%nat eb b lks
              HKeo Hgeom Hj Hgl ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hpid Hprocs Hdev Hgeo Hdlk Hop").
    iIntros (CID2 Hq2 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpid".
    assert (Hpcd6 : ret_pc (M1 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0xd6)) by (rewrite HM1ra; pcw).
    iEval (rewrite Hpcd6) in "Hpc".
    assert (Heosp : so_sp sp0 meo).
    { rewrite /so_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM1sp. }
    assert (Heos2 : (meo !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcseo Rs2 ltac:(vm_compute; reflexivity)).
      exact HM1s2. }
    assert (Heos3 : (meo !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcseo Rs3 ltac:(vm_compute; reflexivity)).
      exact HM1s3. }
    assert (Heothr : so_thr m meo).
    { intros c Hc N2 N8 N9 N18 N19. rewrite (callee_saved_lookup Hcseo c Hc).
      exact (HM1thr c Hc N2 N8 N9 N18 N19). }
    (* ===== +0xd6 c.li a0,-1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID2) (mword_of_int (SO + 0xd6)) Ra0
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              meo (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi1").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (P1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> meo).
    assert (HP1a0 : (P1 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1sp : so_sp sp0 P1)
      by (rewrite /so_sp /P1 upd_ne; [exact Heosp | nz]).
    assert (HP1s2 : (P1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P1 upd_ne; [exact Heos2 | nz]).
    assert (HP1s3 : (P1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P1 upd_ne; [exact Heos3 | nz]).
    assert (HP1thr : so_thr m P1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P1 upd_ne; [| regne].
      exact (Heothr c Hc N2 N8 N9 N18 N19). }
    assert (Hppd8 : add_vec_int (mword_of_int (SO + 0xd6) : mword 64) 2
                    = mword_of_int (SO + 0xd8)) by pcw.
    iEval (rewrite Hppd8) in "Hpc".
    (* ===== +0xd8 c.ldsp s1,168(sp) ===== *)
    assert (Hd3 : add_vec (P1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 21 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HP1sp; apply so_frm3).
    iApply (wp_cldsp_s_sconf (CID := CID3) (mword_of_int (SO + 0xd8))
              (mword_of_int 21 : mword 6) Rs1 P1 (K - 24)%nat
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
    assert (HP2sp : so_sp sp0 P2)
      by (rewrite /so_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2s2 : (P2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s2 | nz]).
    assert (HP2s3 : (P2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s3 | nz]).
    assert (HP2thr : so_thr m P2).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hc N2 N8 N9 N18 N19). }
    assert (Hppda : add_vec_int (mword_of_int (SO + 0xd8) : mword 64) 2
                    = mword_of_int (SO + 0xda)) by pcw.
    iEval (rewrite Hppda) in "Hpc".
    (* ===== +0xda c.j +0xca ===== *)
    iApply (wp_cj_s_sconf (CID := CID4) (mword_of_int (SO + 0xda))
              (sign_extend' 21 (concat_vec (mword_of_int 2040 : mword 11) ('b"0")))
              P2 (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi3").
    iIntros (CID5 Hq5). iNext. iIntros "Hcg Hpc".
    assert (Htg : add_vec (mword_of_int (SO + 0xda) : mword 64)
                    (sign_extend' 64
                       (sign_extend' 21 (concat_vec (mword_of_int 2040 : mword 11) ('b"0"))))
                  = mword_of_int (SO + 0xca)) by pcw.
    iEval (rewrite Htg) in "Hpc".
    iDestruct (cpu_own_transport CID2 CID5 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID2 CID5 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID2 CID5 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID5)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (so_epilogue (CID0 := CID5) m P2 sp0 K b (proc_addr jx)
              (m !!! Regidx Rs1 : mword 64) w4 w5 w6 w23 w24 bp
              HK24 Kpop Hsp0 HP2sp HP2thr HP2s1 HP2s2 HP2s3 Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
                    [Hown Htce Hcce Hpid Hcont]").
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
  (*  ARM B-FAIL: ARM A-FAIL's four instructions at +0x10c.  namei       *)
  (*  returned 0, so again nothing is locked and nothing is allocated.   *)
  (*  See ARM A-FAIL's banner for why this is a second lemma rather      *)
  (*  than a second application.                                        *)
  (* ================================================================== *)
  Lemma so_tail_b `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (u : nat) (pidv : mword 32) (dq : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w4 w5 w6 w23 w24 : mword 64)
      (bp : nat -> bv 8) :
    (K_end_op <= K - 24)%nat -> (24 <= K)%nat -> ((K - 24) + 24 = K)%nat ->
    log_geom_ok cov logstart ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    so_sp sp0 M -> so_thr m M ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    (M !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    so_al sp0 ->
    sie_cap_gpr KT1 M (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SO + 0x10c)) -∗
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
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 23) ↦₈[KT1] w23 -∗
    (pa_stk sp0 24) ↦₈[KT1] w24 -∗
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
    intros HKeo HK24 Kpop Hgeom Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs2 HMs3 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen
              Hpid #Hprocs #Hdev #Hgeo #Hdlk Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
              HbP H23 H24 Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    iPoseProof (soi_10c with "Htext") as "Hi0".
    iPoseProof (soi_110 with "Htext") as "Hi1".
    iPoseProof (soi_112 with "Htext") as "Hi2".
    iPoseProof (soi_114 with "Htext") as "Hi3".
    (* ===== +0x10c jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID0) (mword_of_int (SO + 0x10c)) Rra
              (mword_of_int 2091748 : mword 21) M (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x10c) : mword 64) 4)]> M).
    assert (Hjeo : add_vec (mword_of_int (SO + 0x10c) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091748 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x10c) : mword 64) 4)
      by (rewrite /M1; apply upd_eq).
    assert (HM1sp : so_sp sp0 M1)
      by (rewrite /so_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs2 | nz]).
    assert (HM1s3 : (M1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs3 | nz]).
    assert (HM1thr : so_thr m M1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID0 CID1 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID1 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := CID1) gs jx gl gu gd gk pd pav pu bn
              g gfs cov logstart dev u pidv dq M1 (K - 24)%nat eb b lks
              HKeo Hgeom Hj Hgl ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hpid Hprocs Hdev Hgeo Hdlk Hop").
    iIntros (CID2 Hq2 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpid".
    assert (Hpc110 : ret_pc (M1 !!! Regidx Rra : mword 64)
                     = mword_of_int (SO + 0x110)) by (rewrite HM1ra; pcw).
    iEval (rewrite Hpc110) in "Hpc".
    assert (Heosp : so_sp sp0 meo).
    { rewrite /so_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM1sp. }
    assert (Heos2 : (meo !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcseo Rs2 ltac:(vm_compute; reflexivity)).
      exact HM1s2. }
    assert (Heos3 : (meo !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcseo Rs3 ltac:(vm_compute; reflexivity)).
      exact HM1s3. }
    assert (Heothr : so_thr m meo).
    { intros c Hc N2 N8 N9 N18 N19. rewrite (callee_saved_lookup Hcseo c Hc).
      exact (HM1thr c Hc N2 N8 N9 N18 N19). }
    (* ===== +0x110 c.li a0,-1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID2) (mword_of_int (SO + 0x110)) Ra0
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              meo (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi1").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (P1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> meo).
    assert (HP1a0 : (P1 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1sp : so_sp sp0 P1)
      by (rewrite /so_sp /P1 upd_ne; [exact Heosp | nz]).
    assert (HP1s2 : (P1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P1 upd_ne; [exact Heos2 | nz]).
    assert (HP1s3 : (P1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P1 upd_ne; [exact Heos3 | nz]).
    assert (HP1thr : so_thr m P1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P1 upd_ne; [| regne].
      exact (Heothr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp112 : add_vec_int (mword_of_int (SO + 0x110) : mword 64) 2
                     = mword_of_int (SO + 0x112)) by pcw.
    iEval (rewrite Hpp112) in "Hpc".
    (* ===== +0x112 c.ldsp s1,168(sp) ===== *)
    assert (Hd3 : add_vec (P1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 21 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HP1sp; apply so_frm3).
    iApply (wp_cldsp_s_sconf (CID := CID3) (mword_of_int (SO + 0x112))
              (mword_of_int 21 : mword 6) Rs1 P1 (K - 24)%nat
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
    assert (HP2sp : so_sp sp0 P2)
      by (rewrite /so_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2s2 : (P2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s2 | nz]).
    assert (HP2s3 : (P2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s3 | nz]).
    assert (HP2thr : so_thr m P2).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp114 : add_vec_int (mword_of_int (SO + 0x112) : mword 64) 2
                     = mword_of_int (SO + 0x114)) by pcw.
    iEval (rewrite Hpp114) in "Hpc".
    (* ===== +0x114 c.j +0xca ===== *)
    iApply (wp_cj_s_sconf (CID := CID4) (mword_of_int (SO + 0x114))
              (sign_extend' 21 (concat_vec (mword_of_int 2011 : mword 11) ('b"0")))
              P2 (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi3").
    iIntros (CID5 Hq5). iNext. iIntros "Hcg Hpc".
    assert (Htg : add_vec (mword_of_int (SO + 0x114) : mword 64)
                    (sign_extend' 64
                       (sign_extend' 21 (concat_vec (mword_of_int 2011 : mword 11) ('b"0"))))
                  = mword_of_int (SO + 0xca)) by pcw.
    iEval (rewrite Htg) in "Hpc".
    iDestruct (cpu_own_transport CID2 CID5 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID2 CID5 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID2 CID5 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID5)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (so_epilogue (CID0 := CID5) m P2 sp0 K b (proc_addr jx)
              (m !!! Regidx Rs1 : mword 64) w4 w5 w6 w23 w24 bp
              HK24 Kpop Hsp0 HP2sp HP2thr HP2s1 HP2s2 HP2s3 Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
                    [Hown Htce Hcce Hpid Hcont]").
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
  (*  ARM C-FAIL (+0xfc), ARM D-FAIL (+0x116) AND ARM E-FAIL (+0x12e):   *)
  (*  the three arms that hold a LOCKED inode when they give up.         *)
  (*                                                                    *)
  (*    mv a0,s1 ; jal iunlockput ; jal end_op ; c.li a0,-1 ;             *)
  (*    c.ldsp s1,168(sp) ; [ c.ldsp s2,160(sp) ; ] c.j +0xca             *)
  (*                                                                    *)
  (*  C is the T_DIR-opened-for-writing refusal at +0xf2/+0xfa, D the     *)
  (*  out-of-range [major] at +0x5a, E the filealloc failure at +0x66.    *)
  (*  E is the one that also reloads s2, because the [c.sdsp s2] at       *)
  (*  +0x5e is above ITS branch and below the other two.                 *)
  (*                                                                    *)
  (*  ALL THREE CALL THE COUNTED iunlockput.  Nothing credited is in      *)
  (*  hand on any of them: create's dirlink is the only thing sys_open    *)
  (*  logs before the join and the O_TRUNC tail is the only thing after   *)
  (*  it, so what these arms carry is the join's plain count, which       *)
  (*  [SysOpenBudget.so_join_exact] puts at [iput_units] or better.       *)
  (* ================================================================== *)
  Lemma so_tail_c `{GEN : GenId} `{CID0 : CpuId}
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
      (b : bool) (lks : gset string) (w4 w5 w6 w23 w24 : mword 64)
      (bp : nat -> bv 8) :
    (K_iunlockput <= K - 24)%nat -> (K_end_op <= K - 24)%nat ->
    (24 <= K)%nat -> ((K - 24) + 24 = K)%nat ->
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
    so_sp sp0 M -> so_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    (M !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    so_al sp0 ->
    sie_cap_gpr KT1 M (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SO + 0xfc)) -∗
    panic_env -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrow cn gfs gi cov logstart kk -∗
    ireg_inv gi gfs inodestart nib -∗
    ireg_open -∗
    is_sleeplock_gen gil gisl (i_lock (ientry kk)) "inode"%string (ic_tok cn kk) (slh_tok (icfg_isl kk)) -∗
    sleeplocked_q gisl s -∗
    sl_pid (i_lock (ientry kk)) ↦₄ pidv -∗
    ic_deposit cn kk (DepShr s dev inum gy) -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    (* ...AND THE INUM'S FREEZE TOKEN, [SpecIunlockput]'s new premise since
       iclaim-ledger.md §3.9 (RULING A-prime): the payload's A-custody
       conjunct, relayed from the caller's own ilock. *)
    ifreeze_off (bv_unsigned inum) -∗
    inode_ref_short kk (qi + s)%Qp qi dev inum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned inum) -∗
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
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 23) ↦₈[KT1] w23 -∗
    (pa_stk sp0 24) ↦₈[KT1] w24 -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z),
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        ⌜used' ⊆ used⌝ -∗
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
    intros HKup HKeo HK24 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
           Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs1
           HMs2 HMs3 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen
              #Hitab #Hitinv #Hesck #Hireg #Hropen #Hslkk Hslkd Hslpid Hdep Hidev
              Hiinum Hivalid Hload #Hshot Hfrz Hkeep Hru Hsbb Hsbi Hbmres Hpid #Hprocs
              #Hdev #Hgeo #Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
              Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    iPoseProof (soi_0fc with "Htext") as "Hi0".
    iPoseProof (soi_0fe with "Htext") as "Hi1".
    iPoseProof (soi_102 with "Htext") as "Hi2".
    iPoseProof (soi_106 with "Htext") as "Hi3".
    iPoseProof (soi_108 with "Htext") as "Hi4".
    iPoseProof (soi_10a with "Htext") as "Hi5".
    (* ===== +0xfc c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID0) (mword_of_int (SO + 0xfc)) Ra0 Rs1
              M (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M !!! Regidx Rs1))]> M).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = ientry kk).
    { etransitivity; [ rewrite /M1; apply upd_eq |].
      rewrite add_vec_zero_l. exact HMs1. }
    assert (HM1sp : so_sp sp0 M1)
      by (rewrite /so_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs2 | nz]).
    assert (HM1s3 : (M1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs3 | nz]).
    assert (HM1thr : so_thr m M1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp1 : add_vec_int (mword_of_int (SO + 0xfc) : mword 64) 2
                   = mword_of_int (SO + 0xfe)) by pcw.
    iEval (rewrite Hpp1) in "Hpc".
    (* ===== +0xfe jal ra,iunlockput ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SO + 0xfe)) Rra
              (mword_of_int 2089552 : mword 21) M1 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0xfe) : mword 64) 4)]> M1).
    assert (Hjup : add_vec (mword_of_int (SO + 0xfe) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089552 : mword 21))
                   = mword_of_int KernelSyms.iunlockput) by pcw.
    iEval (rewrite Hjup) in "Hpc".
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0xfe) : mword 64) 4)
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = ientry kk)
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2sp : so_sp sp0 M2)
      by (rewrite /so_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2s2 : (M2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s2 | nz]).
    assert (HM2s3 : (M2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s3 | nz]).
    assert (HM2thr : so_thr m M2).
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
              dqb dqs M2 (K - 24)%nat eb b lks
              HKup Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog
              Hinb Hcovb Hiu Hj Hgl HM2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hitab Hitinv
                    Hesck Hireg Hropen Hslkk Hslkd Hslpid Hdep Hidev Hiinum Hivalid
                    Hload Hshot Hfrz [$Hkeep $Hru] Hsbb Hsbi Hbmres Hpid Hprocs Hdev Hgeo
                    Hdlk Hbsl Hop").
    iIntros (CID3 Hq3 mup n2 used2)
      "%Hcsup Hcg Hown Htce Hcce Hpc Hpid Hsbb Hsbi %Hused2 Hbmres Hbsl %Hn2
       Hop Hislot".
    assert (Hpc2 : ret_pc (M2 !!! Regidx Rra : mword 64)
                   = mword_of_int (SO + 0x102)) by (rewrite HM2ra; pcw).
    iEval (rewrite Hpc2) in "Hpc".
    assert (Hupsp : so_sp sp0 mup).
    { rewrite /so_sp (callee_saved_lookup Hcsup csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM2sp. }
    assert (Hups2 : (mup !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcsup Rs2 ltac:(vm_compute; reflexivity)).
      exact HM2s2. }
    assert (Hups3 : (mup !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcsup Rs3 ltac:(vm_compute; reflexivity)).
      exact HM2s3. }
    assert (Hupthr : so_thr m mup).
    { intros c Hc N2 N8 N9 N18 N19. rewrite (callee_saved_lookup Hcsup c Hc).
      exact (HM2thr c Hc N2 N8 N9 N18 N19). }
    (* ===== +0x102 jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID3) (mword_of_int (SO + 0x102)) Rra
              (mword_of_int 2091758 : mword 21) mup (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x102) : mword 64) 4)]> mup).
    assert (Hjeo : add_vec (mword_of_int (SO + 0x102) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091758 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x102) : mword 64) 4)
      by (rewrite /M3; apply upd_eq).
    assert (HM3sp : so_sp sp0 M3)
      by (rewrite /so_sp /M3 upd_ne; [exact Hupsp | nz]).
    assert (HM3s2 : (M3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M3 upd_ne; [exact Hups2 | nz]).
    assert (HM3s3 : (M3 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M3 upd_ne; [exact Hups3 | nz]).
    assert (HM3thr : so_thr m M3).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M3 upd_ne; [| regne].
      exact (Hupthr c Hc N2 N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID3 CID4 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := CID4) gs jx gl gu gd gk pd pav pu bn
              g gfs cov logstart dev n2 pidv dq M3 (K - 24)%nat eb b lks
              HKeo Hgeom Hj Hgl ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hpid Hprocs Hdev Hgeo Hdlk Hop").
    iIntros (CID5 Hq5 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpid".
    assert (Hpc3 : ret_pc (M3 !!! Regidx Rra : mword 64)
                   = mword_of_int (SO + 0x106)) by (rewrite HM3ra; pcw).
    iEval (rewrite Hpc3) in "Hpc".
    assert (Heosp : so_sp sp0 meo).
    { rewrite /so_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM3sp. }
    assert (Heos2 : (meo !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcseo Rs2 ltac:(vm_compute; reflexivity)).
      exact HM3s2. }
    assert (Heos3 : (meo !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcseo Rs3 ltac:(vm_compute; reflexivity)).
      exact HM3s3. }
    assert (Heothr : so_thr m meo).
    { intros c Hc N2 N8 N9 N18 N19. rewrite (callee_saved_lookup Hcseo c Hc).
      exact (HM3thr c Hc N2 N8 N9 N18 N19). }
    (* ===== +0x106 c.li a0,-1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID5) (mword_of_int (SO + 0x106)) Ra0
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              meo (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi3").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (P1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> meo).
    assert (HP1a0 : (P1 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1sp : so_sp sp0 P1)
      by (rewrite /so_sp /P1 upd_ne; [exact Heosp | nz]).
    assert (HP1s2 : (P1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P1 upd_ne; [exact Heos2 | nz]).
    assert (HP1s3 : (P1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P1 upd_ne; [exact Heos3 | nz]).
    assert (HP1thr : so_thr m P1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P1 upd_ne; [| regne].
      exact (Heothr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp4 : add_vec_int (mword_of_int (SO + 0x106) : mword 64) 2
                   = mword_of_int (SO + 0x108)) by pcw.
    iEval (rewrite Hpp4) in "Hpc".
    (* ===== +0x108 c.ldsp s1,168(sp) ===== *)
    assert (Hd3 : add_vec (P1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 21 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HP1sp; apply so_frm3).
    iApply (wp_cldsp_s_sconf (CID := CID6) (mword_of_int (SO + 0x108))
              (mword_of_int 21 : mword 6) Rs1 P1 (K - 24)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi4 [Hf3]").
    { iEval (rewrite Hd3). iExact "Hf3". }
    iIntros (CID7 Hq7) "Hcg Hpc Hf3".
    iEval (rewrite Hd3) in "Hf3".
    set (P2 := <[Regidx Rs1 := regval_into_reg
                  (m !!! Regidx Rs1 : mword 64)]> P1).
    assert (HP2s1 : (P2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /P2; apply upd_eq).
    assert (HP2a0 : (P2 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1a0 | nz]).
    assert (HP2sp : so_sp sp0 P2)
      by (rewrite /so_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2s2 : (P2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s2 | nz]).
    assert (HP2s3 : (P2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s3 | nz]).
    assert (HP2thr : so_thr m P2).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp5 : add_vec_int (mword_of_int (SO + 0x108) : mword 64) 2
                   = mword_of_int (SO + 0x10a)) by pcw.
    iEval (rewrite Hpp5) in "Hpc".
    (* ===== +0x10a c.j +0xca ===== *)
    iApply (wp_cj_s_sconf (CID := CID7) (mword_of_int (SO + 0x10a))
              (sign_extend' 21 (concat_vec (mword_of_int 2016 : mword 11) ('b"0")))
              P2 (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi5").
    iIntros (CID8 Hq8). iNext. iIntros "Hcg Hpc".
    assert (Htg : add_vec (mword_of_int (SO + 0x10a) : mword 64)
                    (sign_extend' 64
                       (sign_extend' 21 (concat_vec (mword_of_int 2016 : mword 11) ('b"0"))))
                  = mword_of_int (SO + 0xca)) by pcw.
    iEval (rewrite Htg) in "Hpc".
    iDestruct (cpu_own_transport CID5 CID8 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID5 CID8 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID5 CID8 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID8)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (so_epilogue (CID0 := CID8) m P2 sp0 K b (proc_addr jx)
              (m !!! Regidx Rs1 : mword 64) w4 w5 w6 w23 w24 bp
              HK24 Kpop Hsp0 HP2sp HP2thr HP2s1 HP2s2 HP2s3 Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
                    [Hown Htce Hcce Hpid Hsbb Hsbi Hbmres Hbsl Hislot Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
    iDestruct (cpu_own_transport CID8 CIDy 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID8 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID8 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf used2 with "[%] [%] [%] Hcg Hown Htce Hcce Hpc Hpid
              Hsbb Hsbi Hbmres Hbsl Hislot").
    { exact Hcsf. }
    { rewrite Ha0f. exact HP2a0. }
    { exact Hused2. }
  Qed.


  (* ---- ARM D-FAIL: ARM C-FAIL's six instructions at +0x116.  The
     [major] bounds test at +0x5a is ONE unsigned compare (see
     [ProofSysOpenParts]'s [so_major_out]), so this is a single arm and
     not a short-circuit pair.  Same six instructions, same ledger, a
     separate lemma for the reason ARM C-FAIL's banner gives. ---- *)
  Lemma so_tail_d `{GEN : GenId} `{CID0 : CpuId}
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
      (b : bool) (lks : gset string) (w4 w5 w6 w23 w24 : mword 64)
      (bp : nat -> bv 8) :
    (K_iunlockput <= K - 24)%nat -> (K_end_op <= K - 24)%nat ->
    (24 <= K)%nat -> ((K - 24) + 24 = K)%nat ->
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
    so_sp sp0 M -> so_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    (M !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    so_al sp0 ->
    sie_cap_gpr KT1 M (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SO + 0x116)) -∗
    panic_env -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrow cn gfs gi cov logstart kk -∗
    ireg_inv gi gfs inodestart nib -∗
    ireg_open -∗
    is_sleeplock_gen gil gisl (i_lock (ientry kk)) "inode"%string (ic_tok cn kk) (slh_tok (icfg_isl kk)) -∗
    sleeplocked_q gisl s -∗
    sl_pid (i_lock (ientry kk)) ↦₄ pidv -∗
    ic_deposit cn kk (DepShr s dev inum gy) -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    (* ...AND THE INUM'S FREEZE TOKEN, [SpecIunlockput]'s new premise since
       iclaim-ledger.md §3.9 (RULING A-prime): the payload's A-custody
       conjunct, relayed from the caller's own ilock. *)
    ifreeze_off (bv_unsigned inum) -∗
    inode_ref_short kk (qi + s)%Qp qi dev inum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned inum) -∗
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
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 23) ↦₈[KT1] w23 -∗
    (pa_stk sp0 24) ↦₈[KT1] w24 -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z),
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        ⌜used' ⊆ used⌝ -∗
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
    intros HKup HKeo HK24 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
           Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs1
           HMs2 HMs3 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen
              #Hitab #Hitinv #Hesck #Hireg #Hropen #Hslkk Hslkd Hslpid Hdep Hidev
              Hiinum Hivalid Hload #Hshot Hfrz Hkeep Hru Hsbb Hsbi Hbmres Hpid #Hprocs
              #Hdev #Hgeo #Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
              Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    iPoseProof (soi_116 with "Htext") as "Hi0".
    iPoseProof (soi_118 with "Htext") as "Hi1".
    iPoseProof (soi_11c with "Htext") as "Hi2".
    iPoseProof (soi_120 with "Htext") as "Hi3".
    iPoseProof (soi_122 with "Htext") as "Hi4".
    iPoseProof (soi_124 with "Htext") as "Hi5".
    (* ===== +0xfc c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID0) (mword_of_int (SO + 0x116)) Ra0 Rs1
              M (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M !!! Regidx Rs1))]> M).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = ientry kk).
    { etransitivity; [ rewrite /M1; apply upd_eq |].
      rewrite add_vec_zero_l. exact HMs1. }
    assert (HM1sp : so_sp sp0 M1)
      by (rewrite /so_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs2 | nz]).
    assert (HM1s3 : (M1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs3 | nz]).
    assert (HM1thr : so_thr m M1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp1 : add_vec_int (mword_of_int (SO + 0x116) : mword 64) 2
                   = mword_of_int (SO + 0x118)) by pcw.
    iEval (rewrite Hpp1) in "Hpc".
    (* ===== +0xfe jal ra,iunlockput ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SO + 0x118)) Rra
              (mword_of_int 2089526 : mword 21) M1 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x118) : mword 64) 4)]> M1).
    assert (Hjup : add_vec (mword_of_int (SO + 0x118) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089526 : mword 21))
                   = mword_of_int KernelSyms.iunlockput) by pcw.
    iEval (rewrite Hjup) in "Hpc".
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x118) : mword 64) 4)
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = ientry kk)
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2sp : so_sp sp0 M2)
      by (rewrite /so_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2s2 : (M2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s2 | nz]).
    assert (HM2s3 : (M2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s3 | nz]).
    assert (HM2thr : so_thr m M2).
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
              dqb dqs M2 (K - 24)%nat eb b lks
              HKup Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog
              Hinb Hcovb Hiu Hj Hgl HM2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hitab Hitinv
                    Hesck Hireg Hropen Hslkk Hslkd Hslpid Hdep Hidev Hiinum Hivalid
                    Hload Hshot Hfrz [$Hkeep $Hru] Hsbb Hsbi Hbmres Hpid Hprocs Hdev Hgeo
                    Hdlk Hbsl Hop").
    iIntros (CID3 Hq3 mup n2 used2)
      "%Hcsup Hcg Hown Htce Hcce Hpc Hpid Hsbb Hsbi %Hused2 Hbmres Hbsl %Hn2
       Hop Hislot".
    assert (Hpc2 : ret_pc (M2 !!! Regidx Rra : mword 64)
                   = mword_of_int (SO + 0x11c)) by (rewrite HM2ra; pcw).
    iEval (rewrite Hpc2) in "Hpc".
    assert (Hupsp : so_sp sp0 mup).
    { rewrite /so_sp (callee_saved_lookup Hcsup csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM2sp. }
    assert (Hups2 : (mup !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcsup Rs2 ltac:(vm_compute; reflexivity)).
      exact HM2s2. }
    assert (Hups3 : (mup !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcsup Rs3 ltac:(vm_compute; reflexivity)).
      exact HM2s3. }
    assert (Hupthr : so_thr m mup).
    { intros c Hc N2 N8 N9 N18 N19. rewrite (callee_saved_lookup Hcsup c Hc).
      exact (HM2thr c Hc N2 N8 N9 N18 N19). }
    (* ===== +0x102 jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID3) (mword_of_int (SO + 0x11c)) Rra
              (mword_of_int 2091732 : mword 21) mup (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x11c) : mword 64) 4)]> mup).
    assert (Hjeo : add_vec (mword_of_int (SO + 0x11c) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091732 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x11c) : mword 64) 4)
      by (rewrite /M3; apply upd_eq).
    assert (HM3sp : so_sp sp0 M3)
      by (rewrite /so_sp /M3 upd_ne; [exact Hupsp | nz]).
    assert (HM3s2 : (M3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M3 upd_ne; [exact Hups2 | nz]).
    assert (HM3s3 : (M3 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M3 upd_ne; [exact Hups3 | nz]).
    assert (HM3thr : so_thr m M3).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M3 upd_ne; [| regne].
      exact (Hupthr c Hc N2 N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID3 CID4 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := CID4) gs jx gl gu gd gk pd pav pu bn
              g gfs cov logstart dev n2 pidv dq M3 (K - 24)%nat eb b lks
              HKeo Hgeom Hj Hgl ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hpid Hprocs Hdev Hgeo Hdlk Hop").
    iIntros (CID5 Hq5 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpid".
    assert (Hpc3 : ret_pc (M3 !!! Regidx Rra : mword 64)
                   = mword_of_int (SO + 0x120)) by (rewrite HM3ra; pcw).
    iEval (rewrite Hpc3) in "Hpc".
    assert (Heosp : so_sp sp0 meo).
    { rewrite /so_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM3sp. }
    assert (Heos2 : (meo !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcseo Rs2 ltac:(vm_compute; reflexivity)).
      exact HM3s2. }
    assert (Heos3 : (meo !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcseo Rs3 ltac:(vm_compute; reflexivity)).
      exact HM3s3. }
    assert (Heothr : so_thr m meo).
    { intros c Hc N2 N8 N9 N18 N19. rewrite (callee_saved_lookup Hcseo c Hc).
      exact (HM3thr c Hc N2 N8 N9 N18 N19). }
    (* ===== +0x106 c.li a0,-1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID5) (mword_of_int (SO + 0x120)) Ra0
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              meo (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi3").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (P1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> meo).
    assert (HP1a0 : (P1 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1sp : so_sp sp0 P1)
      by (rewrite /so_sp /P1 upd_ne; [exact Heosp | nz]).
    assert (HP1s2 : (P1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P1 upd_ne; [exact Heos2 | nz]).
    assert (HP1s3 : (P1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P1 upd_ne; [exact Heos3 | nz]).
    assert (HP1thr : so_thr m P1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P1 upd_ne; [| regne].
      exact (Heothr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp4 : add_vec_int (mword_of_int (SO + 0x120) : mword 64) 2
                   = mword_of_int (SO + 0x122)) by pcw.
    iEval (rewrite Hpp4) in "Hpc".
    (* ===== +0x108 c.ldsp s1,168(sp) ===== *)
    assert (Hd3 : add_vec (P1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 21 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HP1sp; apply so_frm3).
    iApply (wp_cldsp_s_sconf (CID := CID6) (mword_of_int (SO + 0x122))
              (mword_of_int 21 : mword 6) Rs1 P1 (K - 24)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi4 [Hf3]").
    { iEval (rewrite Hd3). iExact "Hf3". }
    iIntros (CID7 Hq7) "Hcg Hpc Hf3".
    iEval (rewrite Hd3) in "Hf3".
    set (P2 := <[Regidx Rs1 := regval_into_reg
                  (m !!! Regidx Rs1 : mword 64)]> P1).
    assert (HP2s1 : (P2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /P2; apply upd_eq).
    assert (HP2a0 : (P2 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1a0 | nz]).
    assert (HP2sp : so_sp sp0 P2)
      by (rewrite /so_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2s2 : (P2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s2 | nz]).
    assert (HP2s3 : (P2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s3 | nz]).
    assert (HP2thr : so_thr m P2).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp5 : add_vec_int (mword_of_int (SO + 0x122) : mword 64) 2
                   = mword_of_int (SO + 0x124)) by pcw.
    iEval (rewrite Hpp5) in "Hpc".
    (* ===== +0x10a c.j +0xca ===== *)
    iApply (wp_cj_s_sconf (CID := CID7) (mword_of_int (SO + 0x124))
              (sign_extend' 21 (concat_vec (mword_of_int 2003 : mword 11) ('b"0")))
              P2 (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi5").
    iIntros (CID8 Hq8). iNext. iIntros "Hcg Hpc".
    assert (Htg : add_vec (mword_of_int (SO + 0x124) : mword 64)
                    (sign_extend' 64
                       (sign_extend' 21 (concat_vec (mword_of_int 2003 : mword 11) ('b"0"))))
                  = mword_of_int (SO + 0xca)) by pcw.
    iEval (rewrite Htg) in "Hpc".
    iDestruct (cpu_own_transport CID5 CID8 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID5 CID8 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID5 CID8 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID8)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (so_epilogue (CID0 := CID8) m P2 sp0 K b (proc_addr jx)
              (m !!! Regidx Rs1 : mword 64) w4 w5 w6 w23 w24 bp
              HK24 Kpop Hsp0 HP2sp HP2thr HP2s1 HP2s2 HP2s3 Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
                    [Hown Htce Hcce Hpid Hsbb Hsbi Hbmres Hbsl Hislot Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
    iDestruct (cpu_own_transport CID8 CIDy 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID8 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID8 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf used2 with "[%] [%] [%] Hcg Hown Htce Hcce Hpc Hpid
              Hsbb Hsbi Hbmres Hbsl Hislot").
    { exact Hcsf. }
    { rewrite Ha0f. exact HP2a0. }
    { exact Hused2. }
  Qed.


  (* ---- ARM E-FAIL: filealloc returned 0, at +0x12e.  ARM C-FAIL's six
     instructions plus the s2 reload at +0x13c -- the [c.sdsp s2] at +0x5e
     is ABOVE this branch and BELOW C's and D's, so this is the one tail
     that EARNS [M s2 = m s2] rather than assuming it, and the one whose
     slot 4 is not caller junk.  ARM F-FAIL falls into it. ---- *)
  Lemma so_tail_e `{GEN : GenId} `{CID0 : CpuId}
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
      (b : bool) (lks : gset string) (w5 w6 w23 w24 : mword 64)
      (bp : nat -> bv 8) :
    (K_iunlockput <= K - 24)%nat -> (K_end_op <= K - 24)%nat ->
    (24 <= K)%nat -> ((K - 24) + 24 = K)%nat ->
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
    so_sp sp0 M -> so_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    so_al sp0 ->
    sie_cap_gpr KT1 M (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SO + 0x12e)) -∗
    panic_env -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrow cn gfs gi cov logstart kk -∗
    ireg_inv gi gfs inodestart nib -∗
    ireg_open -∗
    is_sleeplock_gen gil gisl (i_lock (ientry kk)) "inode"%string (ic_tok cn kk) (slh_tok (icfg_isl kk)) -∗
    sleeplocked_q gisl s -∗
    sl_pid (i_lock (ientry kk)) ↦₄ pidv -∗
    ic_deposit cn kk (DepShr s dev inum gy) -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    (* ...AND THE INUM'S FREEZE TOKEN, [SpecIunlockput]'s new premise since
       iclaim-ledger.md §3.9 (RULING A-prime): the payload's A-custody
       conjunct, relayed from the caller's own ilock. *)
    ifreeze_off (bv_unsigned inum) -∗
    inode_ref_short kk (qi + s)%Qp qi dev inum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned inum) -∗
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
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 23) ↦₈[KT1] w23 -∗
    (pa_stk sp0 24) ↦₈[KT1] w24 -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z),
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        ⌜used' ⊆ used⌝ -∗
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
    intros HKup HKeo HK24 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
           Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs1
           HMs3 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen
              #Hitab #Hitinv #Hesck #Hireg #Hropen #Hslkk Hslkd Hslpid Hdep Hidev
              Hiinum Hivalid Hload #Hshot Hfrz Hkeep Hru Hsbb Hsbi Hbmres Hpid #Hprocs
              #Hdev #Hgeo #Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
              Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    iPoseProof (soi_12e with "Htext") as "Hi0".
    iPoseProof (soi_130 with "Htext") as "Hi1".
    iPoseProof (soi_134 with "Htext") as "Hi2".
    iPoseProof (soi_138 with "Htext") as "Hi3".
    iPoseProof (soi_13a with "Htext") as "Hi4".
    iPoseProof (soi_13c with "Htext") as "Hi6".
    iPoseProof (soi_13e with "Htext") as "Hi7".
    (* ===== +0xfc c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID0) (mword_of_int (SO + 0x12e)) Ra0 Rs1
              M (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M !!! Regidx Rs1))]> M).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = ientry kk).
    { etransitivity; [ rewrite /M1; apply upd_eq |].
      rewrite add_vec_zero_l. exact HMs1. }
    assert (HM1sp : so_sp sp0 M1)
      by (rewrite /so_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1s3 : (M1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs3 | nz]).
    assert (HM1thr : so_thr m M1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp1 : add_vec_int (mword_of_int (SO + 0x12e) : mword 64) 2
                   = mword_of_int (SO + 0x130)) by pcw.
    iEval (rewrite Hpp1) in "Hpc".
    (* ===== +0xfe jal ra,iunlockput ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SO + 0x130)) Rra
              (mword_of_int 2089502 : mword 21) M1 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x130) : mword 64) 4)]> M1).
    assert (Hjup : add_vec (mword_of_int (SO + 0x130) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089502 : mword 21))
                   = mword_of_int KernelSyms.iunlockput) by pcw.
    iEval (rewrite Hjup) in "Hpc".
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x130) : mword 64) 4)
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = ientry kk)
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2sp : so_sp sp0 M2)
      by (rewrite /so_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2s3 : (M2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s3 | nz]).
    assert (HM2thr : so_thr m M2).
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
              dqb dqs M2 (K - 24)%nat eb b lks
              HKup Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog
              Hinb Hcovb Hiu Hj Hgl HM2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hitab Hitinv
                    Hesck Hireg Hropen Hslkk Hslkd Hslpid Hdep Hidev Hiinum Hivalid
                    Hload Hshot Hfrz [$Hkeep $Hru] Hsbb Hsbi Hbmres Hpid Hprocs Hdev Hgeo
                    Hdlk Hbsl Hop").
    iIntros (CID3 Hq3 mup n2 used2)
      "%Hcsup Hcg Hown Htce Hcce Hpc Hpid Hsbb Hsbi %Hused2 Hbmres Hbsl %Hn2
       Hop Hislot".
    assert (Hpc2 : ret_pc (M2 !!! Regidx Rra : mword 64)
                   = mword_of_int (SO + 0x134)) by (rewrite HM2ra; pcw).
    iEval (rewrite Hpc2) in "Hpc".
    assert (Hupsp : so_sp sp0 mup).
    { rewrite /so_sp (callee_saved_lookup Hcsup csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM2sp. }
    assert (Hups3 : (mup !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcsup Rs3 ltac:(vm_compute; reflexivity)).
      exact HM2s3. }
    assert (Hupthr : so_thr m mup).
    { intros c Hc N2 N8 N9 N18 N19. rewrite (callee_saved_lookup Hcsup c Hc).
      exact (HM2thr c Hc N2 N8 N9 N18 N19). }
    (* ===== +0x102 jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID3) (mword_of_int (SO + 0x134)) Rra
              (mword_of_int 2091708 : mword 21) mup (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x134) : mword 64) 4)]> mup).
    assert (Hjeo : add_vec (mword_of_int (SO + 0x134) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091708 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x134) : mword 64) 4)
      by (rewrite /M3; apply upd_eq).
    assert (HM3sp : so_sp sp0 M3)
      by (rewrite /so_sp /M3 upd_ne; [exact Hupsp | nz]).
    assert (HM3s3 : (M3 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M3 upd_ne; [exact Hups3 | nz]).
    assert (HM3thr : so_thr m M3).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M3 upd_ne; [| regne].
      exact (Hupthr c Hc N2 N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID3 CID4 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := CID4) gs jx gl gu gd gk pd pav pu bn
              g gfs cov logstart dev n2 pidv dq M3 (K - 24)%nat eb b lks
              HKeo Hgeom Hj Hgl ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hpid Hprocs Hdev Hgeo Hdlk Hop").
    iIntros (CID5 Hq5 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpid".
    assert (Hpc3 : ret_pc (M3 !!! Regidx Rra : mword 64)
                   = mword_of_int (SO + 0x138)) by (rewrite HM3ra; pcw).
    iEval (rewrite Hpc3) in "Hpc".
    assert (Heosp : so_sp sp0 meo).
    { rewrite /so_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM3sp. }
    assert (Heos3 : (meo !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcseo Rs3 ltac:(vm_compute; reflexivity)).
      exact HM3s3. }
    assert (Heothr : so_thr m meo).
    { intros c Hc N2 N8 N9 N18 N19. rewrite (callee_saved_lookup Hcseo c Hc).
      exact (HM3thr c Hc N2 N8 N9 N18 N19). }
    (* ===== +0x106 c.li a0,-1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID5) (mword_of_int (SO + 0x138)) Ra0
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              meo (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi3").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (P1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> meo).
    assert (HP1a0 : (P1 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1sp : so_sp sp0 P1)
      by (rewrite /so_sp /P1 upd_ne; [exact Heosp | nz]).
    assert (HP1s3 : (P1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P1 upd_ne; [exact Heos3 | nz]).
    assert (HP1thr : so_thr m P1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P1 upd_ne; [| regne].
      exact (Heothr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp4 : add_vec_int (mword_of_int (SO + 0x138) : mword 64) 2
                   = mword_of_int (SO + 0x13a)) by pcw.
    iEval (rewrite Hpp4) in "Hpc".
    (* ===== +0x108 c.ldsp s1,168(sp) ===== *)
    assert (Hd3 : add_vec (P1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 21 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HP1sp; apply so_frm3).
    iApply (wp_cldsp_s_sconf (CID := CID6) (mword_of_int (SO + 0x13a))
              (mword_of_int 21 : mword 6) Rs1 P1 (K - 24)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi4 [Hf3]").
    { iEval (rewrite Hd3). iExact "Hf3". }
    iIntros (CID7 Hq7) "Hcg Hpc Hf3".
    iEval (rewrite Hd3) in "Hf3".
    set (P2 := <[Regidx Rs1 := regval_into_reg
                  (m !!! Regidx Rs1 : mword 64)]> P1).
    assert (HP2s1 : (P2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /P2; apply upd_eq).
    assert (HP2a0 : (P2 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1a0 | nz]).
    assert (HP2sp : so_sp sp0 P2)
      by (rewrite /so_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2s3 : (P2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s3 | nz]).
    assert (HP2thr : so_thr m P2).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp5 : add_vec_int (mword_of_int (SO + 0x13a) : mword 64) 2
                   = mword_of_int (SO + 0x13c)) by pcw.
    iEval (rewrite Hpp5) in "Hpc".
    (* ===== +0x13c c.ldsp s2,160(sp) -- THE ONE INSTRUCTION ARMS C AND D
       DO NOT HAVE.  The [c.sdsp s2] at +0x5e is ABOVE this branch and
       below theirs, so on this arm slot 4 really does hold the entry s2
       and the agreement is EARNED here rather than assumed. ===== *)
    assert (Hd4 : add_vec (P2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 20 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HP2sp; apply so_frm4).
    iApply (wp_cldsp_s_sconf (CID := CID7) (mword_of_int (SO + 0x13c))
              (mword_of_int 20 : mword 6) Rs2 P2 (K - 24)%nat
              (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi6 [Hf4]").
    { iEval (rewrite Hd4). iExact "Hf4". }
    iIntros (CID7b Hq7b) "Hcg Hpc Hf4".
    iEval (rewrite Hd4) in "Hf4".
    set (P3 := <[Regidx Rs2 := regval_into_reg
                  (m !!! Regidx Rs2 : mword 64)]> P2).
    assert (HP3s2 : (P3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P3; apply upd_eq).
    assert (HP3s1 : (P3 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2s1 | nz]).
    assert (HP3s3 : (P3 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2s3 | nz]).
    assert (HP3a0 : (P3 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2a0 | nz]).
    assert (HP3sp : so_sp sp0 P3)
      by (rewrite /so_sp /P3 upd_ne; [exact HP2sp | nz]).
    assert (HP3thr : so_thr m P3).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P3 upd_ne; [| regne].
      exact (HP2thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp6 : add_vec_int (mword_of_int (SO + 0x13c) : mword 64) 2
                   = mword_of_int (SO + 0x13e)) by pcw.
    iEval (rewrite Hpp6) in "Hpc".
    (* ===== +0x10a c.j +0xca ===== *)
    iApply (wp_cj_s_sconf (CID := CID7b) (mword_of_int (SO + 0x13e))
              (sign_extend' 21 (concat_vec (mword_of_int 1990 : mword 11) ('b"0")))
              P3 (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi7").
    iIntros (CID8 Hq8). iNext. iIntros "Hcg Hpc".
    assert (Htg : add_vec (mword_of_int (SO + 0x13e) : mword 64)
                    (sign_extend' 64
                       (sign_extend' 21 (concat_vec (mword_of_int 1990 : mword 11) ('b"0"))))
                  = mword_of_int (SO + 0xca)) by pcw.
    iEval (rewrite Htg) in "Hpc".
    iDestruct (cpu_own_transport CID5 CID8 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID5 CID8 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID5 CID8 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID8)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (so_epilogue (CID0 := CID8) m P3 sp0 K b (proc_addr jx)
              (m !!! Regidx Rs1 : mword 64) (m !!! Regidx Rs2 : mword 64)
              w5 w6 w23 w24 bp
              HK24 Kpop Hsp0 HP3sp HP3thr HP3s1 HP3s2 HP3s3 Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
                    [Hown Htce Hcce Hpid Hsbb Hsbi Hbmres Hbsl Hislot Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
    iDestruct (cpu_own_transport CID8 CIDy 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID8 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID8 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf used2 with "[%] [%] [%] Hcg Hown Htce Hcce Hpc Hpid
              Hsbb Hsbi Hbmres Hbsl Hislot").
    { exact Hcsf. }
    { rewrite Ha0f. exact HP3a0. }
    { exact Hused2. }
  Qed.



  (* ================================================================== *)
  (*  ARM F-FAIL (+0x126 .. +0x12c): fdalloc refused.                    *)
  (*                                                                    *)
  (*    mv a0,s2 ; jal fileclose ; c.ldsp s3,152(sp)                     *)
  (*                                                                    *)
  (*  and then it FALLS INTO ARM E-FAIL -- no [c.j], the block simply    *)
  (*  runs off its end into +0x12e -- which is why this is the one tail  *)
  (*  that applies another one rather than the epilogue.                 *)
  (*                                                                    *)
  (*  THE fileclose IS FREE, AND THAT IS [fileclose_env_none]'s DOING.   *)
  (*  The file it closes is the one filealloc just handed out and        *)
  (*  nothing has typed yet -- [SpecFilealloc]'s post pins               *)
  (*  [fc_type Cf = FD_NONE] -- and fileclose's environment at FD_NONE   *)
  (*  is [emp].  So this arm owns no file system on fileclose's account  *)
  (*  and is not asked for one; it is threaded OPAQUELY here (the        *)
  (*  environment in, its dual out) so that the walk, which is where the *)
  (*  type is known, is the one place that fact is used.  pipealloc's    *)
  (*  two error paths are the same call for the same reason.             *)
  (*                                                                    *)
  (*  s3 IS RESTORED HERE AND NOWHERE ELSE.  The [sd s3,152] at +0x68    *)
  (*  runs only after filealloc succeeded, so ARM F-FAIL is the only     *)
  (*  route into ARM E-FAIL's block that owns slot 5 -- which is exactly *)
  (*  why [so_tail_e] takes [M s3 = m s3] as a premise instead of        *)
  (*  earning it, and why the [c.ldsp s3] sits on THIS side of the       *)
  (*  fall-through.                                                     *)
  (* ================================================================== *)
  Lemma so_tail_f `{GEN : GenId} `{CID0 : CpuId}
      (gfl gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used : gset Z)
      (kk : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (kf : nat) (qf : Qp) (Cf : fcontent)
      (fn : fclose_names) (on : option nat) (us : gset Z)
      (u : nat) (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w6 w23 w24 : mword 64)
      (bp : nat -> bv 8) :
    (K_iunlockput <= K - 24)%nat -> (K_end_op <= K - 24)%nat ->
    (fileclose_stack <= K - 24)%nat ->
    (24 <= K)%nat -> ((K - 24) + 24 = K)%nat ->
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
    so_sp sp0 M -> so_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs2 : mword 64) = fnode kf ->
    so_al sp0 ->
    sie_cap_gpr KT1 M (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SO + 0x126)) -∗
    panic_env -∗
    is_ftable gfl gf -∗
    file_ref gf kf qf Cf -∗
    fileclose_env fn on us 0 eb (proc_addr jx) Cf -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrow cn gfs gi cov logstart kk -∗
    ireg_inv gi gfs inodestart nib -∗
    ireg_open -∗
    is_sleeplock_gen gil gisl (i_lock (ientry kk)) "inode"%string (ic_tok cn kk) (slh_tok (icfg_isl kk)) -∗
    sleeplocked_q gisl s -∗
    sl_pid (i_lock (ientry kk)) ↦₄ pidv -∗
    ic_deposit cn kk (DepShr s dev inum gy) -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    (* ...AND THE INUM'S FREEZE TOKEN, [SpecIunlockput]'s new premise since
       iclaim-ledger.md §3.9 (RULING A-prime): the payload's A-custody
       conjunct, relayed from the caller's own ilock. *)
    ifreeze_off (bv_unsigned inum) -∗
    inode_ref_short kk (qi + s)%Qp qi dev inum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned inum) -∗
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
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 23) ↦₈[KT1] w23 -∗
    (pa_stk sp0 24) ↦₈[KT1] w24 -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z),
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        ⌜used' ⊆ used⌝ -∗
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
        fd_slot -∗
        fileclose_env_out fn on us Cf -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKup HKeo HKfc HK24 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
           Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs1
           HMs2 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hftab Hfref Hfenv
              #Hbio #Hlog Hseam Hgen
              #Hitab #Hitinv #Hesck #Hireg #Hropen #Hslkk Hslkd Hslpid Hdep Hidev
              Hiinum Hivalid Hload #Hshot Hfrz Hkeep Hru Hsbb Hsbi Hbmres Hpid #Hprocs
              #Hdev #Hgeo #Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
              Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    iPoseProof (soi_126 with "Htext") as "Hi0".
    iPoseProof (soi_128 with "Htext") as "Hi1".
    iPoseProof (soi_12c with "Htext") as "Hi2".
    (* ===== +0x126 c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID0) (mword_of_int (SO + 0x126)) Ra0 Rs2
              M (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M !!! Regidx Rs2))]> M).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = fnode kf).
    { etransitivity; [ rewrite /M1; apply upd_eq |].
      rewrite add_vec_zero_l. exact HMs2. }
    assert (HM1sp : so_sp sp0 M1)
      by (rewrite /so_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M1 upd_ne; [exact HMs1 | nz]).
    assert (HM1thr : so_thr m M1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp1 : add_vec_int (mword_of_int (SO + 0x126) : mword 64) 2
                   = mword_of_int (SO + 0x128)) by pcw.
    iEval (rewrite Hpp1) in "Hpc".
    (* ===== +0x128 jal ra,fileclose ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SO + 0x128)) Rra
              (mword_of_int 2092790 : mword 21) M1 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x128) : mword 64) 4)]> M1).
    assert (Hjfc : add_vec (mword_of_int (SO + 0x128) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092790 : mword 21))
                   = mword_of_int KernelSyms.fileclose) by pcw.
    iEval (rewrite Hjfc) in "Hpc".
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x128) : mword 64) 4)
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = fnode kf)
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2sp : so_sp sp0 M2)
      by (rewrite /so_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2s1 : (M2 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M2 upd_ne; [exact HM1s1 | nz]).
    assert (HM2thr : so_thr m M2).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID2 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID2 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (Fileclose.wp_fileclose_sconf (CID := CID2) gfl gf kf qf Cf fn on us
              M2 0%nat eb (proc_addr jx) (K - 24)%nat b lks
              HKfc so_noff0 HM2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hftab Hpenv Hfref Hfenv").
    iIntros (CID3 Hq3 mfc) "Hcg Hown Htce Hcce Hpc %Hcsfc Hfd Hfout".
    assert (Hpc2 : ret_pc (M2 !!! Regidx Rra : mword 64)
                   = mword_of_int (SO + 0x12c)) by (rewrite HM2ra; pcw).
    iEval (rewrite Hpc2) in "Hpc".
    assert (Hfcsp : so_sp sp0 mfc).
    { rewrite /so_sp (callee_saved_lookup Hcsfc csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM2sp. }
    assert (Hfcs1 : (mfc !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite (callee_saved_lookup Hcsfc Rs1 ltac:(vm_compute; reflexivity)).
      exact HM2s1. }
    assert (Hfcthr : so_thr m mfc).
    { intros c Hc N2 N8 N9 N18 N19. rewrite (callee_saved_lookup Hcsfc c Hc).
      exact (HM2thr c Hc N2 N8 N9 N18 N19). }
    (* ===== +0x12c c.ldsp s3,152(sp) ===== *)
    assert (Hd5 : add_vec (mfc !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 19 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (rewrite Hfcsp; apply so_frm5).
    iApply (wp_cldsp_s_sconf (CID := CID3) (mword_of_int (SO + 0x12c))
              (mword_of_int 19 : mword 6) Rs3 mfc (K - 24)%nat
              (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi2 [Hf5]").
    { iEval (rewrite Hd5). iExact "Hf5". }
    iIntros (CID4 Hq4) "Hcg Hpc Hf5".
    iEval (rewrite Hd5) in "Hf5".
    set (P1 := <[Regidx Rs3 := regval_into_reg
                  (m !!! Regidx Rs3 : mword 64)]> mfc).
    assert (HP1s3 : (P1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1s1 : (P1 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /P1 upd_ne; [exact Hfcs1 | nz]).
    assert (HP1sp : so_sp sp0 P1)
      by (rewrite /so_sp /P1 upd_ne; [exact Hfcsp | nz]).
    assert (HP1thr : so_thr m P1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P1 upd_ne; [| regne].
      exact (Hfcthr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp2 : add_vec_int (mword_of_int (SO + 0x12c) : mword 64) 2
                   = mword_of_int (SO + 0x12e)) by pcw.
    iEval (rewrite Hpp2) in "Hpc".
    (* ===== THE FALL-THROUGH INTO ARM E-FAIL ===== *)
    iDestruct (cpu_own_transport CID3 CID4 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID4)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (so_tail_e (CID0 := CID4) gs jx gl gu gd gk pd pav pu bn g gfs gi
              cn gtl gil gisl cov logstart bmapstart inodestart nib size dev
              used kk qi s gy inum dn bm u pidv dq dqb dqs m P1 sp0 K eb b lks
              (m !!! Regidx Rs3 : mword 64) w6 w23 w24 bp
              HKup HKeo HK24 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
              Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HP1sp HP1thr
              HP1s1 HP1s3 Hal
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hitab Hitinv Hesck Hireg Hropen Hslkk Hslkd Hslpid Hdep Hidev
                    Hiinum Hivalid Hload Hshot Hfrz Hkeep Hru Hsbb Hsbi Hbmres Hpid
                    Hprocs Hdev Hgeo Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
                    HbP H23 H24 [Hfd Hfout Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDz) "%Hqz". iIntros (mf used')
      "%Hcsf %Ha0f %Huse Hcg Hown Htce Hcce Hpc Hpid Hsbb Hsbi Hbmres Hbsl
       Hislot".
    iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf used' with "[%] [%] [%] Hcg Hown Htce Hcce Hpc Hpid
              Hsbb Hsbi Hbmres Hbsl Hislot Hfd Hfout").
    { exact Hcsf. }
    { exact Ha0f. }
    { exact Huse. }
  Qed.


  (* ================================================================== *)
  (*  ARM S (+0xb8 .. +0xc8): THE SUCCESS TAIL.                          *)
  (*                                                                    *)
  (*    mv a0,s1 ; jal iunlock ; jal end_op ; mv a0,s3 ;                  *)
  (*    c.ldsp s1,168 ; c.ldsp s2,160 ; c.ldsp s3,152                     *)
  (*                                                                    *)
  (*  and then it FALLS INTO the epilogue at +0xca -- the only arm that   *)
  (*  reloads all three callee-saved registers, because it is the only    *)
  (*  one that reaches the bottom of the function with all three spilled. *)
  (*                                                                    *)
  (*  iunlock, NOT iunlockput, AND THAT IS THE LEDGER SENTENCE OF THE     *)
  (*  WHOLE SYSCALL.  The [+1] inode reference is not released here: it   *)
  (*  has already been parked in [f->ip] as [FileInvDefs.inode_pay] by    *)
  (*  the field stores above, so what comes back out of iunlock is the    *)
  (*  generation-ERASED share [inode_shr k s dev inum] and NOT an         *)
  (*  [iref_slot].  That is the same sentence as sys_chdir's [p->cwd],    *)
  (*  one descriptor further along, and it is why sys_open's allowance is *)
  (*  spend-at-most rather than conserved.                                *)
  (*                                                                    *)
  (*  So this tail moves NO bitmap, NO buffer pool and NO reference       *)
  (*  ledger: iunlock takes none of them and end_op retires whatever the  *)
  (*  operation has left.  The retained parent [inode_ref_short] rides in *)
  (*  the WALK's closure, untouched -- it is not iunlock's business.      *)
  (*                                                                    *)
  (*  a0 IS THE DESCRIPTOR, WRITTEN AFTER end_op.  Unlike every failure   *)
  (*  arm's [c.li a0,-1] this is a [c.mv a0,s3], so the value is a        *)
  (*  PARAMETER here and the walk supplies fdalloc's literal.             *)
  (* ================================================================== *)
  Lemma so_tail_s `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gil gisl : gname)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (kk : nat) (s : Qp) (gy : gname) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (fdw : mword 64)
      (u : nat) (pidv : mword 32) (dq : dfrac)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w6 w23 w24 : mword 64)
      (bp : nat -> bv 8) :
    (K_iunlock <= K - 24)%nat -> (K_end_op <= K - 24)%nat ->
    (24 <= K)%nat -> ((K - 24) + 24 = K)%nat ->
    (kk < NINODE)%nat ->
    log_geom_ok cov logstart ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    so_sp sp0 M -> so_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs3 : mword 64) = fdw ->
    so_al sp0 ->
    sie_cap_gpr KT1 M (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SO + 0xb8)) -∗
    panic_env -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    itable_inv -∗
    ic_escrow cn gfs gi cov logstart kk -∗
    is_sleeplock_gen gil gisl (i_lock (ientry kk)) "inode"%string (ic_tok cn kk) (slh_tok (icfg_isl kk)) -∗
    sleeplocked_q gisl s -∗
    sl_pid (i_lock (ientry kk)) ↦₄ pidv -∗
    ic_deposit cn kk (DepShr s dev inum gy) -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    (* ...AND THE INUM'S FREEZE TOKEN, [SpecIunlockput]'s new premise since
       iclaim-ledger.md §3.9 (RULING A-prime): the payload's A-custody
       conjunct, relayed from the caller's own ilock. *)
    ifreeze_off (bv_unsigned inum) -∗
    p_pid (proc_addr jx) ↦₄{dq} pidv -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    log_op g u -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
    (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 23) ↦₈[KT1] w23 -∗
    (pa_stk sp0 24) ↦₈[KT1] w24 -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = fdw⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
        cpu_own 0 eb (proc_addr jx) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr jx) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        p_pid (proc_addr jx) ↦₄{dq} pidv -∗
        inode_shr kk s dev inum -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKiu HKeo HK24 Kpop Hkk Hgeom Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs1
           HMs3 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen
              #Hitinv #Hesck #Hslkk Hslkd Hslpid Hdep Hidev Hiinum Hivalid
              Hload #Hshot Hfrz Hpid #Hprocs #Hdev #Hgeo #Hdlk Hop Hf1 Hf2 Hf3 Hf4
              Hf5 Hf6 HbP H23 H24 Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    iPoseProof (soi_0b8 with "Htext") as "Hi0".
    iPoseProof (soi_0ba with "Htext") as "Hi1".
    iPoseProof (soi_0be with "Htext") as "Hi2".
    iPoseProof (soi_0c2 with "Htext") as "Hi3".
    iPoseProof (soi_0c4 with "Htext") as "Hi4".
    iPoseProof (soi_0c6 with "Htext") as "Hi5".
    iPoseProof (soi_0c8 with "Htext") as "Hi6".
    (* ===== +0xb8 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID0) (mword_of_int (SO + 0xb8)) Ra0 Rs1
              M (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (M1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M !!! Regidx Rs1))]> M).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = ientry kk).
    { etransitivity; [ rewrite /M1; apply upd_eq |].
      rewrite add_vec_zero_l. exact HMs1. }
    assert (HM1sp : so_sp sp0 M1)
      by (rewrite /so_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1s3 : (M1 !!! Regidx Rs3 : mword 64) = fdw)
      by (rewrite /M1 upd_ne; [exact HMs3 | nz]).
    assert (HM1thr : so_thr m M1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp1 : add_vec_int (mword_of_int (SO + 0xb8) : mword 64) 2
                   = mword_of_int (SO + 0xba)) by pcw.
    iEval (rewrite Hpp1) in "Hpc".
    (* ===== +0xba jal ra,iunlock ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SO + 0xba)) Rra
              (mword_of_int 2089198 : mword 21) M1 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0xba) : mword 64) 4)]> M1).
    assert (Hjiu : add_vec (mword_of_int (SO + 0xba) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089198 : mword 21))
                   = mword_of_int KernelSyms.iunlock) by pcw.
    iEval (rewrite Hjiu) in "Hpc".
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0xba) : mword 64) 4)
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = ientry kk)
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2sp : so_sp sp0 M2)
      by (rewrite /so_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2s3 : (M2 !!! Regidx Rs3 : mword 64) = fdw)
      by (rewrite /M2 upd_ne; [exact HM1s3 | nz]).
    assert (HM2thr : so_thr m M2).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Iunlock.wp_iunlock_sconf (CID := CID2) gs gfs gi cn gil gisl
              cov logstart kk s gy dev inum dn bm pidv dq M2 (K - 24)%nat eb
              (proc_addr jx) b lks
              HKiu Hkk HM2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htext Hpc Hitinv Hesck Hslkk Hslkd Hslpid
                    Hpid Hprocs Hdep Hidev Hiinum Hivalid Hload Hshot Hfrz").
    iIntros (CID3 Hq3 miu) "%Hcsiu Hcg Hown Hpc Hpid Hshr".
    iDestruct (inode_shr_gen_forget with "Hshr") as "Hshr".
    assert (Hpc2 : ret_pc (M2 !!! Regidx Rra : mword 64)
                   = mword_of_int (SO + 0xbe)) by (rewrite HM2ra; pcw).
    iEval (rewrite Hpc2) in "Hpc".
    assert (Hiusp : so_sp sp0 miu).
    { rewrite /so_sp (callee_saved_lookup Hcsiu csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM2sp. }
    assert (Hius3 : (miu !!! Regidx Rs3 : mword 64) = fdw).
    { rewrite (callee_saved_lookup Hcsiu Rs3 ltac:(vm_compute; reflexivity)).
      exact HM2s3. }
    assert (Hiuthr : so_thr m miu).
    { intros c Hc N2 N8 N9 N18 N19. rewrite (callee_saved_lookup Hcsiu c Hc).
      exact (HM2thr c Hc N2 N8 N9 N18 N19). }
    iDestruct (trap_csrs_ext_transport CID0 CID3 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID3 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    (* ===== +0xbe jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID3) (mword_of_int (SO + 0xbe)) Rra
              (mword_of_int 2091826 : mword 21) miu (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0xbe) : mword 64) 4)]> miu).
    assert (Hjeo : add_vec (mword_of_int (SO + 0xbe) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091826 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0xbe) : mword 64) 4)
      by (rewrite /M3; apply upd_eq).
    assert (HM3sp : so_sp sp0 M3)
      by (rewrite /so_sp /M3 upd_ne; [exact Hiusp | nz]).
    assert (HM3s3 : (M3 !!! Regidx Rs3 : mword 64) = fdw)
      by (rewrite /M3 upd_ne; [exact Hius3 | nz]).
    assert (HM3thr : so_thr m M3).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M3 upd_ne; [| regne].
      exact (Hiuthr c Hc N2 N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID3 CID4 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID3 CID4 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := CID4) gs jx gl gu gd gk pd pav pu bn
              g gfs cov logstart dev u pidv dq M3 (K - 24)%nat eb b lks
              HKeo Hgeom Hj Hgl ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hpid Hprocs Hdev Hgeo Hdlk Hop").
    iIntros (CID5 Hq5 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpid".
    assert (Hpc3 : ret_pc (M3 !!! Regidx Rra : mword 64)
                   = mword_of_int (SO + 0xc2)) by (rewrite HM3ra; pcw).
    iEval (rewrite Hpc3) in "Hpc".
    assert (Heosp : so_sp sp0 meo).
    { rewrite /so_sp (callee_saved_lookup Hcseo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM3sp. }
    assert (Heos3 : (meo !!! Regidx Rs3 : mword 64) = fdw).
    { rewrite (callee_saved_lookup Hcseo Rs3 ltac:(vm_compute; reflexivity)).
      exact HM3s3. }
    assert (Heothr : so_thr m meo).
    { intros c Hc N2 N8 N9 N18 N19. rewrite (callee_saved_lookup Hcseo c Hc).
      exact (HM3thr c Hc N2 N8 N9 N18 N19). }
    (* ===== +0xc2 c.mv a0,s3 : THE DESCRIPTOR ===== *)
    iApply (wp_cmv_s_sconf (CID := CID5) (mword_of_int (SO + 0xc2)) Ra0 Rs3
              meo (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi3").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (P1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (meo !!! Regidx Rs3))]> meo).
    assert (HP1a0 : (P1 !!! Regidx Ra0 : mword 64) = fdw).
    { etransitivity; [ rewrite /P1; apply upd_eq |].
      rewrite add_vec_zero_l. exact Heos3. }
    assert (HP1sp : so_sp sp0 P1)
      by (rewrite /so_sp /P1 upd_ne; [exact Heosp | nz]).
    assert (HP1thr : so_thr m P1).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P1 upd_ne; [| regne].
      exact (Heothr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp4 : add_vec_int (mword_of_int (SO + 0xc2) : mword 64) 2
                   = mword_of_int (SO + 0xc4)) by pcw.
    iEval (rewrite Hpp4) in "Hpc".
    (* ===== +0xc4 c.ldsp s1,168(sp) ===== *)
    assert (Hd3 : add_vec (P1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 21 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HP1sp; apply so_frm3).
    iApply (wp_cldsp_s_sconf (CID := CID6) (mword_of_int (SO + 0xc4))
              (mword_of_int 21 : mword 6) Rs1 P1 (K - 24)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi4 [Hf3]").
    { iEval (rewrite Hd3). iExact "Hf3". }
    iIntros (CID7 Hq7) "Hcg Hpc Hf3".
    iEval (rewrite Hd3) in "Hf3".
    set (P2 := <[Regidx Rs1 := regval_into_reg
                  (m !!! Regidx Rs1 : mword 64)]> P1).
    assert (HP2s1 : (P2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /P2; apply upd_eq).
    assert (HP2a0 : (P2 !!! Regidx Ra0 : mword 64) = fdw)
      by (rewrite /P2 upd_ne; [exact HP1a0 | nz]).
    assert (HP2sp : so_sp sp0 P2)
      by (rewrite /so_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : so_thr m P2).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp5 : add_vec_int (mword_of_int (SO + 0xc4) : mword 64) 2
                   = mword_of_int (SO + 0xc6)) by pcw.
    iEval (rewrite Hpp5) in "Hpc".
    (* ===== +0xc6 c.ldsp s2,160(sp) ===== *)
    assert (Hd4 : add_vec (P2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 20 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HP2sp; apply so_frm4).
    iApply (wp_cldsp_s_sconf (CID := CID7) (mword_of_int (SO + 0xc6))
              (mword_of_int 20 : mword 6) Rs2 P2 (K - 24)%nat
              (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi5 [Hf4]").
    { iEval (rewrite Hd4). iExact "Hf4". }
    iIntros (CID8 Hq8) "Hcg Hpc Hf4".
    iEval (rewrite Hd4) in "Hf4".
    set (P3 := <[Regidx Rs2 := regval_into_reg
                  (m !!! Regidx Rs2 : mword 64)]> P2).
    assert (HP3s2 : (P3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P3; apply upd_eq).
    assert (HP3s1 : (P3 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2s1 | nz]).
    assert (HP3a0 : (P3 !!! Regidx Ra0 : mword 64) = fdw)
      by (rewrite /P3 upd_ne; [exact HP2a0 | nz]).
    assert (HP3sp : so_sp sp0 P3)
      by (rewrite /so_sp /P3 upd_ne; [exact HP2sp | nz]).
    assert (HP3thr : so_thr m P3).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P3 upd_ne; [| regne].
      exact (HP2thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp6 : add_vec_int (mword_of_int (SO + 0xc6) : mword 64) 2
                   = mword_of_int (SO + 0xc8)) by pcw.
    iEval (rewrite Hpp6) in "Hpc".
    (* ===== +0xc8 c.ldsp s3,152(sp) ===== *)
    assert (Hd5 : add_vec (P3 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 19 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (rewrite HP3sp; apply so_frm5).
    iApply (wp_cldsp_s_sconf (CID := CID8) (mword_of_int (SO + 0xc8))
              (mword_of_int 19 : mword 6) Rs3 P3 (K - 24)%nat
              (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi6 [Hf5]").
    { iEval (rewrite Hd5). iExact "Hf5". }
    iIntros (CID9 Hq9) "Hcg Hpc Hf5".
    iEval (rewrite Hd5) in "Hf5".
    set (P4 := <[Regidx Rs3 := regval_into_reg
                  (m !!! Regidx Rs3 : mword 64)]> P3).
    assert (HP4s3 : (P4 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P4; apply upd_eq).
    assert (HP4s1 : (P4 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3s1 | nz]).
    assert (HP4s2 : (P4 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3s2 | nz]).
    assert (HP4a0 : (P4 !!! Regidx Ra0 : mword 64) = fdw)
      by (rewrite /P4 upd_ne; [exact HP3a0 | nz]).
    assert (HP4sp : so_sp sp0 P4)
      by (rewrite /so_sp /P4 upd_ne; [exact HP3sp | nz]).
    assert (HP4thr : so_thr m P4).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /P4 upd_ne; [| regne].
      exact (HP3thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp7 : add_vec_int (mword_of_int (SO + 0xc8) : mword 64) 2
                   = mword_of_int (SO + 0xca)) by pcw.
    iEval (rewrite Hpp7) in "Hpc".
    (* ===== THE FALL-THROUGH INTO THE EPILOGUE ===== *)
    iDestruct (cpu_own_transport CID5 CID9 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID5 CID9 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID5 CID9 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID9)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (so_epilogue (CID0 := CID9) m P4 sp0 K b (proc_addr jx)
              (m !!! Regidx Rs1 : mword 64) (m !!! Regidx Rs2 : mword 64)
              (m !!! Regidx Rs3 : mword 64) w6 w23 w24 bp
              HK24 Kpop Hsp0 HP4sp HP4thr HP4s1 HP4s2 HP4s3 Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
                    [Hown Htce Hcce Hpid Hshr Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
    iDestruct (cpu_own_transport CID9 CIDy 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID9 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID9 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf with "[%] [%] Hcg Hown Htce Hcce Hpc Hpid Hshr").
    { exact Hcsf. }
    { rewrite Ha0f. exact HP4a0. }
  Qed.

End ProofSysOpenTails.

End SysOpenTails.
