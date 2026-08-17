(* ============================================================================
   DEV SCRATCH: ip_free_entry -- the WP walk for the ENTRY-CHECK block of the
   reordered iput:  iput +0x3a .. +0x58 (CodeIput pin 4398009).

   THE SPAN IS CALL-FREE (loads/stores/branches/ALU only), so unlike
   IputOfflockDev / IputFreeLockedDev this file needs NO functor parameters:
   nothing here poses a BREAD/LOG_WRITE/BRELSE or lock-call obligation.  The
   FreeLockedDev instantiation happens at INTEGRATION time (ProofIput), where
   this lemma's 0x5a exit is discharged by applying [ip_free_locked].

   ==========================================================================
   STATUS: PROVEN, ADMIT-FREE (2026-08-17).  The whole span 0x3a..0x58 plus
   the 0xcc/0xce/0xd0 detour is walked and the lemma ends in [Qed];
   [Print Assumptions ip_free_entry] reports the platform axioms
   (rv64d reservation / plat_term_write) and functional extensionality, and
   nothing else.  Three findings the scaffold's plan did not have:
     (1) +0x46 [lw s2,4(s1)] must be an ATOMIC UPDATE, not a plain read: the
         window is open there and [ic_held] owns [i_inum] WHOLE.  It is an
         [ic_open_held] / [ic_close_held] round trip that moves nothing.
     (2) For the same reason Exit B cannot be byte-identical to
         [ip_free_locked]'s entry -- see the EXIT B note below and the
         statement site.  ONE flagged repair is owed on FreeLocked's side.
     (3) The scaffold's [dinode_wf] FLAGGED SEAM is a non-issue: it IS
         extractable from the payload ([fe_dinode_wf]).
   ==========================================================================
   EXIT-B RE-SYNCED (2026-08-17) against [ip_free_locked]'s
   post-60cc0136b1 statement: [2 <= u] became [3 <= u] and the companion
   bound [Z.of_nat u + 2 < 2^31] joined the pure block.  (FreeLocked's OTHER
   two changes -- its 0x30 continuation now threading [OFF.ipo_thr] at
   [sie_cap_gpr .. (K-6)] and handing back an [ipool_shape] -- are on its
   POST, which this lemma's Exit B does not mention: Exit B ends in
   [WP Loop] and the integration supplies FreeLocked's own continuation.)
   ==========================================================================

   ---- THE EXACT INSTRUCTION STREAM (CodeIput.v at lane HEAD; LOAD decode
        order is (imm, rs1, rd, unsigned, width); STORE is (imm, rs2, rs1)) --
   0x3a  c.lw  a4, 64(s1)     ; a4 = ip->valid           [ipi_3a]
   0x3c  c.beqz a4, -28       ; !valid -> +0x20 (EXIT A) [ipi_3c]
   0x3e  c.sdsp s2, 16(sp)    ; save s2   (slot pa_stk sp0 4)      [ipi_3e]
   0x40  c.sdsp s4, 0(sp)     ; save s4   (slot pa_stk sp0 6)      [ipi_40]
   0x42  lw    s4, 0(s1)      ; s4 = ip->dev                        [ipi_42]
   0x46  lw    s2, 4(s1)      ; s2 = ip->inum                       [ipi_46]
   0x4a  lh    a4, 74(s1)     ; a4 = ip->nlink                      [ipi_4a]
   0x4e  c.bnez a4, +126      ; nlink!=0 -> +0xcc                   [ipi_4e]
   0x50  c.sdsp s3, 8(sp)     ; save s3   (slot pa_stk sp0 5)       [ipi_50]
   0x52  addi  a5, s1, 16     ; a5 = &ip->lock                      [ipi_52]
   0x56  c.mv  s3, a5         ; s3 = &ip->lock                      [ipi_56]
   0x58  c.mv  a0, a5         ; a0 = &ip->lock; falls into 0x5a     [ipi_58]
   ---- the nlink!=0 detour (also this lemma's obligation) ------------------
   0xcc  c.ldsp s2, 16(sp)    ; restore s2                          [ipi_cc]
   0xce  c.ldsp s4, 0(sp)     ; restore s4                          [ipi_ce]
   0xd0  c.j   -176           ; -> +0x20 (EXIT A)                   [ipi_d0]
   ---------------------------------------------------------------------------

   ---- ENTRY STATE (= wp_iput_gen's state after the taken +0x1c beq, i.e.
        ref==1 under the held itable.lock; NOTHING checked out yet).  The
        valid read at 0x3a is the WINDOW-ENTERING AU exactly as the stale
        walk's +0x3c was (ProofIput.v:1521-1579, pattern reference: pop the
        islot2, ic_open_auth_ref, the loaded/unloaded disjunction, close at
        HELD on the loaded arm / at PARKED on the unloaded one).  NB the NEW
        binary loads valid into a4, NOT a5 -- a5 keeps the ref word across
        the whole span, which is what EXIT A's [ipe_regs]+Ra5 facts encode.

   ---- EXITS ----------------------------------------------------------------
   EXIT A (one continuation, TWO firing sites): pc +0x20, the ip_tail seam.
     * valid==0 (branch at 0x3c): nothing was saved, slots 4/5/6 unchanged,
       payload re-parked from inside the AU (stale pattern ProofIput.v:1598).
     * nlink!=0 (0x4e -> 0xcc/0xce/0xd0): slots 4/6 hold the caller's s2/s4
       (stored, then reloaded -- registers end UNCHANGED, [ipe_regs] holds);
       payload re-parked HELD->PARKED (stale pattern ProofIput.v:1677-1744).
     The continuation is quantified over the exit regfile and the three
     scratch-slot values, so one shape serves both sites.  It hands back the
     UNTOUCHED itable-held bundle + log/bitmap environment; the integration
     feeds it to [ip_tail] (after log_opSe_opS, exactly as wp_iput_gen's
     stale arms do).
   EXIT B: pc +0x5a, BYTE-COMPATIBLE with [FreeLockedDev.ip_free_locked]'s
     ENTRY (IputFreeLockedDev.v:247): the escrow-held state (ic_payload_at at
     generation g1 + live_gen 1/2 + the checkout's i_valid half), the intact
     itable-held bundle, the register facts its premises pose (a0/s1/s2/s3/s4
     + sp), and the frame with s2/s3/s4 saved.  The dinode-dependent pure
     premises (di_type<>0, di_nlink=0, dinode_wf, blkmap_wf, data lengths,
     di_addrs=bm_cells) are HANDED TO the continuation: the body must extract
     them when it opens the payload -- [inode_ok]'s conjuncts carry them
     (stale pattern ProofIput.v:1644-1651, destructure (Hbmwf & Hcovers &
     Hdiaddrs & Htyne & Hszcap & Hholes & Hsized)); di_nlink=0 is decided by
     the 0x4a load + 0x4e fall-through.  The header's [dinode_wf dn] FLAGGED
     SEAM is RESOLVED, not repaired: it IS extractable, from [inode_ok]'s
     [di_addrs dn = bm_cells bm] plus [blkmap_wf]'s direct-cell count (see
     [fe_dinode_wf], the same derivation as IcacheEscrow.v:1519), so neither
     premise list moves.

     ---- THE ONE REAL DIVERGENCE FROM BYTE-COMPATIBILITY (found in the
          grind, 2026-08-17; full argument at the statement site) ----------
     [ip_free_locked]'s entry asks for [islot2 cn Mt ci k] AND
     [inode_ref k q dev inum] AND the escrow-held payload at once.  Those
     three CANNOT coexist: with the payload out the escrow sits on its HELD
     arm, and [IcacheEscrow.ic_held] owns [i_inum] WHOLE by design -- the
     arm's half plus the closer's [q] plus the table's [1/2 - q].  The two
     [i_inum] shares [islot2] and [inode_ref] are stated over are exactly the
     ones the arm swallowed; FreeLocked's own body then DROPS the surplus
     half it gets back at its 0x76 [ic_open_held] (IputFreeLockedDev.v:586),
     which is the fingerprint of the over-count.  Exit B therefore hands
     [iref_tok] + [ic_id] + the pure [ci !! k] fact + a RE-ASSEMBLY WAND that
     turns the half FreeLocked already drops back into the two resources.
     This is a three-line repair on FreeLocked's side and is NOT made here
     (that file is out of this lemma's cone).  Note this is also why 0x46's
     [lw s2,4(s1)] is an ATOMIC UPDATE in the walk below and not a plain
     read: the same fact.

   ---- SYNC NOTES -----------------------------------------------------------
   * [ipe_regs] is a VERBATIM copy of ProofIput.iput_regs (ProofIput.v:350);
     ProofIput is red at lane HEAD and cannot be imported.  At integration,
     replace ipe_regs by iput_regs (they are definitionally identical).
   * Slot addressing uses [pa_stk sp0 i] (StackOwn.v), ip_tail's spelling.
     FreeLockedDev spells the same six cells [add_vec spd (zero_extend' 64
     (concat_vec (mword_of_int i) 'b"000"))]; the bridge equalities are
     wp_iput_gen's Hb1..Hb6 (ProofIput.v:1237-1258), pcw-provable.
   * K-BUDGET: carries (K_itrunc <= K - 6), i.e. K >= 74 -- the SPLICE
     finding; the final iput contract must be at least as strong.
   ========================================================================== *)

From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import DiskPtsto DiskInv.
Require Import BufOwn.
Require Import WpLock.
Require Import SleepLock.
Require Import InodeLock.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpAu4 MinstretInv.
Require Import WpSmodeHalf.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import WpUart.
Require Import BcacheInv BioInv.
Require Import FsBlocks LogInv LogDefs.
Require Import BitmapInv.
Require Import DirView DirLinks FsTree.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeRegion.
Require Import DinodeSlot.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import SpecBread SpecBrelse SpecLogWrite.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import EscrowDefs.
Require Import EscrowInode.
Require Import EscrowDeposit.
Require Import CodeIput.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import SpecAcquire SpecRelease SpecAcquiresleep SpecReleasesleep.
Require Import SpecItrunc SpecIupdate.
Require Import SpecIput.
Local Open Scope Z_scope.

Section FreeEntryDev.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Notation Rra  := (mword_of_int 1 : mword 5).
  Notation Rs0  := (mword_of_int 8 : mword 5).
  Notation Rs1  := (mword_of_int 9 : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
  Notation Ra1  := (mword_of_int 11 : mword 5).
  Notation Ra4  := (mword_of_int 14 : mword 5).
  Notation Ra5  := (mword_of_int 15 : mword 5).
  Notation Rs2  := (mword_of_int 18 : mword 5).
  Notation Rs3  := (mword_of_int 19 : mword 5).
  Notation Rs4  := (mword_of_int 20 : mword 5).
  Notation Rz   := (mword_of_int 0 : mword 5).

  (* VERBATIM copy of ProofIput.iput_regs (:350) -- see SYNC NOTES above. *)
  Definition ipe_regs (m M : regfile) (spd : mword 64) (k : nat) : Prop :=
    M !!! Regidx (mword_of_int 9 : mword 5) = ientry k /\
    M !!! Regidx csp_rs1 = spd /\
    M !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5) /\
    M !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5) /\
    M !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5) /\
    M !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
    M !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
    M !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
    M !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
    M !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
    M !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
    M !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz  := vm_compute; discriminate.
  Local Ltac regne := reg_ne_side.

  (* ---- pure helpers, all VERBATIM from ProofIput (which is red at lane
     HEAD and cannot be imported); at integration they collapse back. ---- *)

  (* ProofIput.ip_sext64_16_inj / ip_nlink_zero (:170-186): the [c.bnez] at
     0x4e falls through exactly on a zero nlink halfword. *)
  Lemma fe_sext64_16_inj (a c : mword 16) :
    (sign_extend' 64 a : mword 64) = sign_extend' 64 c -> a = c.
  Proof. intro H. rewrite -(trunc16_sext64 a) -(trunc16_sext64 c) H. reflexivity. Qed.

  Lemma fe_nlink_zero (w : mword 16) :
    neq_vec (sign_extend' 64 w : mword 64) (zero_reg : mword 64) = false ->
    bv_unsigned w = 0.
  Proof.
    intro H. unfold neq_vec in H. apply negb_false_iff in H.
    apply eq_vec_true_iff in H.
    assert (Hz : (zero_reg : mword 64) = sign_extend' 64 (mword_of_int 0 : mword 16))
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hz in H. apply fe_sext64_16_inj in H.
    rewrite H. vm_compute. reflexivity.
  Qed.

  (* ProofIput.ip_valid_beqz (:270) *)
  Lemma fe_valid_beqz (v : bool) :
    eq_vec (sign_extend' 64 (valid_word v) : mword 64) (zero_reg : mword 64) = negb v.
  Proof. exact (valid_word_eqz v). Qed.

  (* ProofIput.ip_rest_sum / IputFreeLockedDev.ip_rest_sum *)
  Lemma fe_rest_sum (kk : nat) (qt : Qp) (dv nu : mword 32) :
    islot_rest_at kk qt dv nu -∗ ⌜∃ qr : Qp, (1/2)%Qp = (qt + qr)%Qp⌝.
  Proof.
    rewrite /islot_rest_at. destruct (1/2 - qt)%Qp as [q'|] eqn:Et.
    - iIntros "_". iPureIntro. exists q'. by apply Qp.sub_Some in Et.
    - iIntros "[]".
  Qed.

  (* THE HEADER'S FLAGGED SEAM, RESOLVED: [dinode_wf] IS extractable from the
     payload -- [inode_ok]'s [di_addrs dn = bm_cells bm] plus [blkmap_wf]'s
     direct-cell count.  Same derivation as IcacheEscrow.v:1519. *)
  Lemma fe_dinode_wf (cov : gset Z) (logstart : Z) (dn : dinode) (bm : blkmap) :
    blkmap_wf cov logstart bm -> di_addrs dn = bm_cells bm -> dinode_wf dn.
  Proof.
    intros Hwf Hda. rewrite /dinode_wf Hda /bm_cells length_app.
    rewrite (blkmap_wf_dir_len _ _ _ Hwf). reflexivity.
  Qed.

  (* ==========================================================================
     ip_free_entry.  Entry at iput+0x3a: itable.lock HELD, ref==1 known
     (Mt !! k = Some (q, 1)), NOTHING checked out; a5 still carries the ref
     word from the +0x18 load.  [m] is iput's ORIGINAL entry regfile (the
     frame slots and ipe_regs are stated against it, as ip_tail does); [M] is
     the regfile HERE.  Exits: see the header.
     ========================================================================== *)
  Lemma ip_free_entry `{GEN : GenId} `{CID0 : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used : gset Z)
      (k : nat) (q : Qp) (inum : mword 32)
      (Mt : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32))
      (u : nat) (Sb : gset Z) (crb cru : bool) (e0 v : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (vg4 vg5 vg6 : mword 64)
      (m M : regfile) (K : nat) (eb : bool) (lks : gset string) :
    let ip := ientry k in
    let pj := proc_addr j in
    let sp0 := (m !!! Regidx csp_rs1 : mword 64) in
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) in
    (K_iput <= K)%nat ->
    (* SPLICE: itrunc's cone reserve => the final contract carries K >= 74. *)
    (K_itrunc <= K - 6)%nat ->
    (k < NINODE)%nat ->
    (* RE-SYNCED to [ip_free_locked]'s post-60cc0136b1 premise list: [3] (not
       [2]) is what makes itrunc's post leave [1 <= u'], i.e. an [S _] for the
       off-lock flush's [log_opSe γ (S u) Sb e0]; the bound is its companion. *)
    (3 <= u)%nat ->
    (Z.of_nat u + 2 < 2 ^ 31)%Z ->
    (crb = true -> bmapstart ∈ Sb) ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart -> bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    cov_below cov size ->
    icM_wf Mt ->
    ic_ci_wf Mt ci nib dev ->
    (* FREE-PATH GUARD: the +0x1c branch was TAKEN -- this is the last ref. *)
    Mt !! k = Some (q, 1%positive) ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    ipe_regs m M spd k ->
    M !!! Regidx Ra5 = sign_extend' 64 (iref_word Mt k) ->
    locks_below lks "log" ->
    "itable" ∉ lks ->
    sie_cap_gpr M (trap_res eb + (K - 6))%nat false pj -∗
    cpu_own 1 eb pj false ({["itable"]} ∪ lks) -∗
    arm_pay 0 eb pj -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb pj -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.iput + 0x3a) : mword 64) -∗
    panic_env -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    is_lock gtl itable_lock "itable"%string (itable_res2 cn γfs γi cov logstart nib dev) -∗
    itable_inv -∗
    ic_escrow cn γfs γi cov logstart k -∗
    locked gtl cpu_id -∗
    itable_half Mt -∗
    iref_slots_auth -∗
    isl_pool Mt -∗
    ([∗ list] i0 ∈ seq 0 NINODE, islot2 cn Mt ci i0) -∗
    ipool γfs γi cov logstart (region_inums nib ∖ ci_inums ci) -∗
    IcacheRef.inode_ref k q dev inum -∗
    is_sleeplock_gen gil gisl (i_lock ip) "inode"%string (ic_tok cn k)
                     (slh_tok (icfg_isl k)) -∗
    ireg_inv γi γfs inodestart nib -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res γfs bmapstart cov logstart size used -∗
    p_pid pj ↦₄{dq} pidv -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bslots bn 3 -∗
    log_epoch_lb γ v -∗
    log_credit γ cru Sb e0 (IBLOCK inum inodestart) -∗
    log_opSe γ u Sb e0 -∗
    (* the 6-slot frame: ra/s0/s1 already saved by the prologue; 4/5/6 are
       the s2/s3/s4 slots, still holding prologue garbage *)
    pa_stk sp0 1 ↦₈ (m !!! Regidx Rra) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx Rs0) -∗
    pa_stk sp0 3 ↦₈ (m !!! Regidx Rs1) -∗
    pa_stk sp0 4 ↦₈ vg4 -∗
    pa_stk sp0 5 ↦₈ vg5 -∗
    pa_stk sp0 6 ↦₈ vg6 -∗
    (* ===== EXIT A: pc +0x20, the ip_tail seam (valid==0 OR nlink!=0);
       the bundle goes back UNTOUCHED, the payload is re-parked ===== *)
    (∀ (M' : regfile) (vg4' vg5' vg6' : mword 64),
       ⌜ipe_regs m M' spd k⌝ -∗
       ⌜M' !!! Regidx Ra5 = sign_extend' 64 (iref_word Mt k)⌝ -∗
       sie_cap_gpr M' (trap_res eb + (K - 6))%nat false pj -∗
       cpu_own 1 eb pj false ({["itable"]} ∪ lks) -∗
       arm_pay 0 eb pj -∗
       trap_csrs_ext eb -∗
       cpu_claim_ext eb pj -∗
       pc_is (mword_of_int (KernelSyms.iput + 0x20) : mword 64) -∗
       locked gtl cpu_id -∗
       itable_half Mt -∗
       iref_slots_auth -∗
       isl_pool Mt -∗
       ([∗ list] i0 ∈ seq 0 NINODE, islot2 cn Mt ci i0) -∗
       ipool γfs γi cov logstart (region_inums nib ∖ ci_inums ci) -∗
       IcacheRef.inode_ref k q dev inum -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       bitmap_res γfs bmapstart cov logstart size used -∗
       p_pid pj ↦₄{dq} pidv -∗
       bslots bn 3 -∗
       log_epoch_lb γ v -∗
       log_credit γ cru Sb e0 (IBLOCK inum inodestart) -∗
       log_opSe γ u Sb e0 -∗
       pa_stk sp0 1 ↦₈ (m !!! Regidx Rra) -∗
       pa_stk sp0 2 ↦₈ (m !!! Regidx Rs0) -∗
       pa_stk sp0 3 ↦₈ (m !!! Regidx Rs1) -∗
       pa_stk sp0 4 ↦₈ vg4' -∗
       pa_stk sp0 5 ↦₈ vg5' -∗
       pa_stk sp0 6 ↦₈ vg6' -∗
       WP (Loop : expr riscv_lang)) -∗
    (* ===== EXIT B: pc +0x5a, byte-compatible with ip_free_locked's ENTRY
       (IputFreeLockedDev.v:247).  dn/bm/data/g1 are the body's discoveries
       from opening the payload; the pure block is FreeLocked's dn-dependent
       premise list verbatim ===== *)
    (∀ (M5 : regfile) (g1 : gname) (dn : dinode) (bm : blkmap)
       (data : nat -> list (bv 8)),
       ⌜bv_unsigned (di_type dn) <> 0⌝ -∗
       ⌜bv_unsigned (di_nlink dn) = 0⌝ -∗
       ⌜dinode_wf dn⌝ -∗
       ⌜blkmap_wf cov logstart bm⌝ -∗
       ⌜forall i : nat, (i < MAXFILE)%nat -> length (data i) = BSIZE⌝ -∗
       ⌜di_addrs dn = bm_cells bm⌝ -∗
       ⌜spd = M5 !!! Regidx csp_rs1⌝ -∗
       ⌜M5 !!! Regidx Ra0 = (i_lock ip : mword 64)⌝ -∗
       ⌜M5 !!! Regidx Rs1 = (ip : mword 64)⌝ -∗
       ⌜M5 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64)⌝ -∗
       ⌜M5 !!! Regidx Rs3 = (i_lock ip : mword 64)⌝ -∗
       ⌜M5 !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64)⌝ -∗
       (* s5..s11 untouched: what the integration's end-to-end callee_saved
          chain needs beyond FreeLocked's own callee_saved *)
       ⌜M5 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
        M5 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
        M5 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
        M5 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
        M5 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
        M5 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
        M5 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)⌝ -∗
       sie_cap_gpr M5 (trap_res eb + (K - 6))%nat false pj -∗
       cpu_own 1 eb pj false ({["itable"]} ∪ lks) -∗
       arm_pay 0 eb pj -∗
       trap_csrs_ext eb -∗
       cpu_claim_ext eb pj -∗
       pc_is (mword_of_int (KernelSyms.iput + 0x5a) : mword 64) -∗
       locked gtl cpu_id -∗
       itable_half Mt -∗
       iref_slots_auth -∗
       isl_pool Mt -∗
       ipool γfs γi cov logstart (region_inums nib ∖ ci_inums ci) -∗
       (* ================================================================
          THE WINDOW'S i_inum SPLIT -- the ONE place this Exit B is NOT
          byte-identical to [ip_free_locked]'s entry, and it is FORCED, not
          a proof-engineering choice.  See the header's EXIT B note.

          At 0x5a the payload is OUT, so the escrow is on its HELD arm, and
          [IcacheEscrow.ic_held] owns [i_inum] AT DFRAC 1 by design -- "both
          [ic_mid_arm] and [ic_held] are refuted by a FULL [i_inum] cell"
          (IcacheEscrow.v, the §17.3 (A) note above [ic_parked]).  That whole
          cell is the arm's own 1/2 PLUS the closer's [q] PLUS the table's
          [1/2 - q], i.e. exactly the two shares that live inside
          [inode_ref k q dev inum] and inside [islot2 cn Mt ci k]'s
          [islot_rest_at].  So NEITHER of those two resources exists here:
          each is short precisely its [i_inum] share, and no other escrow arm
          accepts "payload out, i_inum at a half" (PARKED holds the payload,
          MID holds [i_inum] whole too, OUT needs a deposit the sleeplock has
          not minted yet, EMPTY needs a dead slot).

          What is handed instead is the pieces that DO exist plus the
          RE-ASSEMBLY WAND.  [ip_free_locked] re-opens the HELD arm at its
          own 0x76 [ic_open_held] regardless, and that returns [i_inum ↦₄
          inum] WHOLE -- whose surplus half its body TODAY DROPS on the floor
          (IputFreeLockedDev.v:586, [iDestruct (word4_pointsto_half_split
          with "Hnfull") as "[Hinh _]"]).  Feeding that dropped half and the
          borrowed [ic_id] to this wand rebuilds both resources exactly.
          FLAGGED SEAM: ip_free_locked's premise list needs the matching
          three-line repair before the two lemmas can be composed.
          ================================================================ *)
       ⌜ci !! k = Some (dev, inum)⌝ -∗
       iref_tok k q -∗
       ic_id cn k (1/2) true dev inum -∗
       (i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
        ic_id cn k (1/2) true dev inum -∗
          ([∗ list] i0 ∈ seq 0 NINODE, islot2 cn Mt ci i0) ∗
          IcacheRef.inode_ident k (DfracOwn q) dev inum) -∗
       ic_payload_at γfs γi cov logstart k inum g1 dn bm -∗
       live_gen k (1/2) g1 -∗
       i_valid (ientry k) ↦₄{DfracOwn (1/2)} (valid_word true) -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       bitmap_res γfs bmapstart cov logstart size used -∗
       p_pid pj ↦₄{dq} pidv -∗
       bslots bn 3 -∗
       log_epoch_lb γ v -∗
       log_credit γ cru Sb e0 (IBLOCK inum inodestart) -∗
       log_opSe γ u Sb e0 -∗
       pa_stk sp0 1 ↦₈ (m !!! Regidx Rra) -∗
       pa_stk sp0 2 ↦₈ (m !!! Regidx Rs0) -∗
       pa_stk sp0 3 ↦₈ (m !!! Regidx Rs1) -∗
       pa_stk sp0 4 ↦₈ (m !!! Regidx Rs2) -∗
       pa_stk sp0 5 ↦₈ (m !!! Regidx Rs3) -∗
       pa_stk sp0 6 ↦₈ (m !!! Regidx Rs4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ip pj sp0 spd HK HKit Hk Hu3 Hubnd Hcrb Hgeom Hsize Hbmpos Hbmcov Hbmlog
           Histpos Hicov Hilog Hnib Hbelow HMwf Hciwf HMk1 Hj Hgl Hregs Ha5
           Hlkbelow Hitnotin.
    iIntros "Hcg Hcnt Hpay Hextc Hclm #Htext #Hkd Hpc #Hpenv #Hbio #Hlctx
             #Hitlk #Hitinv #Hesc Htok Hhalf Hiauth Hipool Hslots Hpool Href
             #Hslk #Hireg Hbms Hins Hbm Hppid #Hprocs #Hdevi #Hdgeom #Hdlock
             Hbslots #Hvlb Hcrd Hop Hr1 Hr2 Hr3 Hg4 Hg5 Hg6 HcA HcB".
    pose proof Hregs as Hregs'.
    destruct Hregs' as (HMs1 & HMsp & _).
    iPoseProof (ipi_3a with "Htext") as "Hi3a".
    iPoseProof (ipi_3c with "Htext") as "Hi3c".
    (* the slot's own share comes out of the lock's big-op, exactly as the
       stale walk's +0x3c does (ProofIput.v:1503-1520) *)
    assert (Hcikex : exists di : mword 32 * mword 32, ci !! k = Some di).
    { destruct Hciwf as [Hdom _].
      assert (Hin : k ∈ dom ci)
        by (rewrite Hdom; apply elem_of_dom; rewrite HMk1; by eexists).
      apply elem_of_dom in Hin. exact Hin. }
    destruct Hcikex as [[cdev cinum] Hcik].
    iDestruct (islots2_acc_upd cn Mt ci k Hk with "Hslots") as "[Hslot Hback]".
    iEval (rewrite /islot2 HMk1 Hcik) in "Hslot".
    iDestruct "Hslot" as "(Hrest & Hiu & Hgid)".
    iDestruct (fe_rest_sum with "Hrest") as %[qr Hsum].
    iDestruct "Href" as "[Hrtok Hrident]".
    iAssert (⌜cdev = dev /\ cinum = inum⌝)%I as %[-> ->].
    { iEval (rewrite /islot_rest_at) in "Hrest".
      destruct (1/2 - q)%Qp as [q'|] eqn:Et; [| iDestruct "Hrest" as "[]"].
      iApply (inode_ident_agree with "Hrest Hrident"). }
    assert (Ert : (1/2 - q)%Qp = Some qr) by (apply Qp.sub_Some; exact Hsum).
    (* ===== +0x3a c.lw a4,64(s1) : the read that ENTERS the window ===== *)
    assert (Hpa3a : add_vec (rget M Rs1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                    = i_valid (ientry k)).
    { rewrite (rget_ne M Rs1 ltac:(nz)) HMs1. reflexivity. }
    iApply (wp_lw_au_s_sconf true (mword_of_int (KernelSyms.iput + 0x3a)) Ra4 Rs1
              (mword_of_int 64 : mword 12) M (trap_res eb + (K - 6))%nat
              (fun w => (∃ v : bool, ⌜w = valid_word v⌝ ∗
                  itable_half Mt ∗ iref_tok k q ∗
                  (if v
                   then i_dev (ientry k) ↦₄{DfracOwn q} dev ∗
                        i_dev (ientry k) ↦₄{DfracOwn qr} dev ∗
                        i_valid (ientry k) ↦₄{DfracOwn (1/2)} (valid_word true) ∗
                        (∃ ga : gname,
                           ic_payload γfs γi cov logstart k inum ga true ∗
                           live_gen k (1/2) ga)
                   else IcacheRef.inode_ident k (DfracOwn q) dev inum ∗
                        islot_rest_at k q dev inum))%I)
              (⊤ ∖ ↑minstretN ∖ ↑icEscN) false
              ltac:(nz) ltac:(rdok) ltac:(solve_ndisj)
              with "Hcg Hpc Hi3a [Hhalf Hrtok Hrident Hrest]").
    { rewrite Hpa3a.
      iInv "Hesc" as ">Hbody" "Hclose".
      iMod (ic_open_auth_ref cn γfs γi cov logstart k
              (⊤ ∖ ↑minstretN ∖ ↑icEscN) Mt q q dev inum
              ltac:(solve_ndisj) HMk1 with "Hitinv Hbody Hhalf Hrtok Hrident")
        as "(Hhalf & Hrtok & Hrident & Harm & _)".
      iDestruct "Harm" as (vld ga) "(Hidv & Hinh & Hvld & Hpayl & Hlvh & Hmt & Hgida)".
      iModIntro. iExists (valid_word vld). iFrame "Hvld". iIntros "Hvld".
      destruct vld.
      - (* LOADED: the payload leaves with us; the FULL inum cell stays *)
        iDestruct "Hrident" as "[Hrd Hrn]".
        iEval (rewrite /islot_rest_at Ert) in "Hrest".
        iDestruct "Hrest" as "[Htd Htn]".
        iDestruct (word4_pointsto_frac_split (i_inum (ientry k)) q qr inum) as "[_ Hjn]".
        iDestruct ("Hjn" with "[$Hrn $Htn]") as "Hn2".
        iEval (rewrite -Hsum) in "Hn2".
        iDestruct (word4_pointsto_half_join with "Hinh Hn2") as "Hnfull".
        iDestruct (word4_pointsto_half_split with "Hvld") as "[Hva Hvb]".
        iMod ("Hclose" with "[Hidv Hnfull Hva Hmt Hgida]") as "_".
        { iApply bi.later_intro. iApply ic_close_held. rewrite /ic_held.
          iExists dev, inum, (valid_word true). iFrame. }
        iModIntro. iExists true. iFrame "Hhalf Hrtok Hrd Htd Hvb".
        iSplitR; [done |]. iExists ga.
        iSplitL "Hpayl"; [iExact "Hpayl" | iExact "Hlvh"].
      - (* UNLOADED: read-only, everything goes straight back *)
        iMod ("Hclose" with "[Hidv Hinh Hvld Hpayl Hlvh Hmt Hgida]") as "_".
        { iApply bi.later_intro. iApply ic_close_parked.
          iApply (ic_mk_parked cn γfs γi cov logstart k dev inum false ga
                    with "Hidv Hinh Hvld Hpayl Hlvh Hmt Hgida"). }
        iModIntro. iExists false. iFrame. done. }
    iIntros (wvld).
    iApply wp_next_off_intro. iIntros "Hcg Hpc HPsi".
    iDestruct "HPsi" as (vv) "(%Hwv & Hhalf & Hrtok & Hrem)".
    subst wvld.
    set (F1 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 (valid_word vv))]> M).
    assert (HF1a4 : F1 !!! Regidx Ra4 = (sign_extend' 64 (valid_word vv) : mword 64))
      by (rewrite /F1; apply upd_eq).
    assert (HF1a5 : F1 !!! Regidx Ra5 = sign_extend' 64 (iref_word Mt k))
      by (rewrite /F1 upd_ne; [exact Ha5 | nz]).
    assert (HF1s1 : F1 !!! Regidx Rs1 = ientry k)
      by (rewrite /F1 upd_ne; [exact HMs1 | nz]).
    assert (HF1regs : ipe_regs m F1 spd k).
    { unfold ipe_regs in Hregs |- *.
      destruct Hregs as (A&B&Cc&Ee&F&G&H&I&Jj&L&N&O).
      repeat split; (rewrite /F1 upd_ne; [| nz]); assumption. }
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.iput + 0x3a) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x3c)) by pcw.
    iEval (rewrite Hpp3c) in "Hpc".
    (* ===== +0x3c c.beqz a4 : !valid goes to the tail (EXIT A) ===== *)
    destruct vv.
    2:{ (* valid == 0 : the window was never entered *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.iput + 0x3c))
                (mword_of_int 242 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                F1 (trap_res eb + (K - 6))%nat false
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HF1a4; exact (fe_valid_beqz false))
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi3c").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpp20b : add_vec (mword_of_int (KernelSyms.iput + 0x3c) : mword 64)
                         (sign_extend' 64 (sign_extend' 13
                            (concat_vec (mword_of_int 242 : mword 8) ('b"0"))))
                       = mword_of_int (KernelSyms.iput + 0x20)) by pcw.
      iEval (rewrite Hpp20b) in "Hpc".
      iDestruct "Hrem" as "[Hrident Hrest]".
      iDestruct ("Hback" $! Mt ci with "[%] [%] [Hrest Hiu Hgid]") as "Hslots";
        [ intros i Hi; reflexivity | intros i Hi; reflexivity | | ].
      { rewrite /islot2 HMk1 Hcik. iFrame. }
      iApply ("HcA" $! F1 vg4 vg5 vg6
                with "[%] [%] Hcg Hcnt Hpay Hextc Hclm Hpc Htok Hhalf Hiauth Hipool
                      Hslots Hpool [Hrtok Hrident] Hbms Hins Hbm Hppid Hbslots Hvlb
                      Hcrd Hop Hr1 Hr2 Hr3 Hg4 Hg5 Hg6").
      { exact HF1regs. }
      { exact HF1a5. }
      { rewrite /IcacheRef.inode_ref. iFrame. } }
    (* ===== valid == 1: fall through, WITH the payload in hand ===== *)
    iDestruct "Hrem" as "(Hrd & Htd & Hvb & (%ga & Hpayl & Hlvh))".
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.iput + 0x3c))
              (mword_of_int 242 : mword 8) (Cregidx (mword_of_int 6)) Ra4
              F1 (trap_res eb + (K - 6))%nat false
              ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HF1a4; exact (fe_valid_beqz true))
              with "Hcg Hpc Hi3c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.iput + 0x3c) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x3e)) by pcw.
    iEval (rewrite Hpp3e) in "Hpc".
    (* the three scratch slots, in [pa_stk] spelling; the bridge equalities are
       wp_iput_gen's Hb4/Hb5/Hb6 (ProofIput.v:1249-1258), pcw-provable *)
    assert (Hb4 : add_vec spd (zero_extend' 64
                    (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spd, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hb5 : add_vec spd (zero_extend' 64
                    (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spd, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hb6 : add_vec spd (zero_extend' 64
                    (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spd, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iPoseProof (ipi_3e with "Htext") as "Hi3e".
    iPoseProof (ipi_40 with "Htext") as "Hi40".
    iPoseProof (ipi_42 with "Htext") as "Hi42".
    assert (HF1sp : F1 !!! Regidx csp_rs1 = spd)
      by (destruct HF1regs as (_ & B & _); exact B).
    assert (HF1s2 : F1 !!! Regidx Rs2 = m !!! Regidx Rs2)
      by (destruct HF1regs as (_ & _ & C & _); exact C).
    assert (HF1s3 : F1 !!! Regidx Rs3 = m !!! Regidx Rs3)
      by (destruct HF1regs as (_ & _ & _ & D & _); exact D).
    assert (HF1s4 : F1 !!! Regidx Rs4 = m !!! Regidx Rs4)
      by (destruct HF1regs as (_ & _ & _ & _ & E & _); exact E).
    assert (HF1hi : F1 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
                    F1 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
                    F1 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
                    F1 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
                    F1 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
                    F1 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
                    F1 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
    { destruct HF1regs as (_&_&_&_&_&G1&G2&G3&G4'&G5&G6&G7).
      split_and!; assumption. }
    (* ===== +0x3e c.sdsp s2,16(sp) ===== *)
    iEval (rewrite -Hb4 -HF1sp) in "Hg4".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iput + 0x3e))
              (mword_of_int 2 : mword 6) Rs2 F1 (trap_res eb + (K - 6))%nat vg4 false
              with "Hcg Hpc Hi3e Hg4").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hg4".
    iEval (rgne) in "Hg4".
    iEval (rewrite HF1s2 HF1sp Hb4) in "Hg4".
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.iput + 0x3e) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x40)) by pcw.
    iEval (rewrite Hpp40) in "Hpc".
    (* ===== +0x40 c.sdsp s4,0(sp) ===== *)
    iEval (rewrite -Hb6 -HF1sp) in "Hg6".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iput + 0x40))
              (mword_of_int 0 : mword 6) Rs4 F1 (trap_res eb + (K - 6))%nat vg6 false
              with "Hcg Hpc Hi40 Hg6").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hg6".
    iEval (rgne) in "Hg6".
    iEval (rewrite HF1s4 HF1sp Hb6) in "Hg6".
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.iput + 0x40) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x42)) by pcw.
    iEval (rewrite Hpp42) in "Hpc".
    (* ===== +0x42 lw s4,0(s1) : ip->dev, a PLAIN read off our own [q] share ===== *)
    assert (Hpa42 : add_vec (rget F1 Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = i_dev (ientry k)).
    { rewrite (rget_ne F1 Rs1 ltac:(nz)) HF1s1. reflexivity. }
    iEval (rewrite -Hpa42) in "Hrd".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.iput + 0x42)) Rs4 Rs1
              (mword_of_int 0 : mword 12) F1 (trap_res eb + (K - 6))%nat dev false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi42 Hrd").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hrd".
    iEval (rewrite Hpa42) in "Hrd".
    set (F2 := <[Regidx Rs4 := regval_into_reg (sign_extend' 64 dev)]> F1).
    assert (HF2s4 : F2 !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64))
      by (rewrite /F2; apply upd_eq).
    assert (HF2s1 : F2 !!! Regidx Rs1 = ientry k)
      by (rewrite /F2 upd_ne; [exact HF1s1 | nz]).
    assert (HF2sp : F2 !!! Regidx csp_rs1 = spd)
      by (rewrite /F2 upd_ne; [exact HF1sp | nz]).
    assert (HF2s2 : F2 !!! Regidx Rs2 = m !!! Regidx Rs2)
      by (rewrite /F2 upd_ne; [exact HF1s2 | nz]).
    assert (HF2s3 : F2 !!! Regidx Rs3 = m !!! Regidx Rs3)
      by (rewrite /F2 upd_ne; [exact HF1s3 | nz]).
    assert (HF2a5 : F2 !!! Regidx Ra5 = sign_extend' 64 (iref_word Mt k))
      by (rewrite /F2 upd_ne; [exact HF1a5 | nz]).
    assert (HF2hi : F2 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
                    F2 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
                    F2 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
                    F2 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
                    F2 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
                    F2 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
                    F2 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
    { destruct HF1hi as (G1&G2&G3&G4'&G5&G6&G7).
      repeat split; (rewrite /F2 upd_ne; [| nz]); assumption. }
    assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.iput + 0x42) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x46)) by pcw.
    iEval (rewrite Hpp46) in "Hpc".
    (* the loaded bundle, at the record we are holding *)
    iEval (rewrite /ic_payload) in "Hpayl".
    iDestruct "Hpayl" as (dn bm) "Hpayl".
    iAssert (ic_payload_at γfs γi cov logstart k inum ga dn bm) with "[Hpayl]" as "Hpayl";
      [ rewrite /ic_payload_at; iExact "Hpayl" |].
    (* ===================================================================
       +0x46 lw s2,4(s1) : ip->inum.  THE REORDER'S NEW AU.  The stale pin
       never read [ip->inum] inside the window (it got dev/inum elsewhere);
       the reordered one does, and by then the escrow's HELD arm owns that
       cell WHOLE -- [ic_held] holds [i_inum] at dfrac 1 by design, since
       "both [ic_mid_arm] and [ic_held] are refuted by a FULL [i_inum] cell"
       (IcacheEscrow.v, §17.3 (A)'s note).  So this load cannot be a plain
       read the way +0x42's [ip->dev] is: it is an ATOMIC UPDATE that
       re-enters the window with [ic_open_held] and closes it right back at
       HELD with [ic_close_held].  Nothing moves; the cell is only borrowed.
       =================================================================== *)
    iPoseProof (ipi_46 with "Htext") as "Hi46".
    assert (Hpa46 : add_vec (rget F2 Rs1) (sign_extend' 64 (mword_of_int 4 : mword 12))
                    = i_inum (ientry k)).
    { rewrite (rget_ne F2 Rs1 ltac:(nz)) HF2s1. reflexivity. }
    iDestruct "Hrtok" as "(Hrfrg & Hrlv & Hrslh)".
    iApply (wp_lw_au_s_sconf false (mword_of_int (KernelSyms.iput + 0x46)) Rs2 Rs1
              (mword_of_int 4 : mword 12) F2 (trap_res eb + (K - 6))%nat
              (fun w => (⌜w = inum⌝ ∗ itable_half Mt ∗ iref_frag k q ∗ live_frac k q ∗
                         live_gen k (1/2) ga ∗ ic_id cn k (1/2) true dev inum ∗
                         ic_payload_at γfs γi cov logstart k inum ga dn bm)%I)
              (⊤ ∖ ↑minstretN ∖ ↑icEscN) false
              ltac:(nz) ltac:(rdok) ltac:(solve_ndisj)
              with "Hcg Hpc Hi46 [Hhalf Hrfrg Hrlv Hlvh Hgid Hpayl]").
    { rewrite Hpa46.
      iInv "Hesc" as ">Hbody" "Hclose".
      iMod (ic_open_held cn γfs γi cov logstart k (⊤ ∖ ↑minstretN ∖ ↑icEscN)
              Mt q ga ga dev inum dn bm ltac:(solve_ndisj) HMk1
              with "Hitinv Hbody Hhalf Hrfrg Hrlv Hlvh Hgid Hpayl")
        as "(Hhalf & Hrfrg & Hrlv & Hlvh & Hgid & Hpayl & Hidv & Hnfull & Hvldx & Hmt & Hgida)".
      iDestruct "Hvldx" as (w0) "Hva".
      iModIntro. iExists inum. iFrame "Hnfull". iIntros "Hnfull".
      iMod ("Hclose" with "[Hidv Hnfull Hva Hmt Hgida]") as "_".
      { iApply bi.later_intro. iApply ic_close_held. rewrite /ic_held.
        iExists dev, inum, w0. iFrame. }
      iModIntro. iFrame. done. }
    iIntros (winum).
    iApply wp_next_off_intro. iIntros "Hcg Hpc HPsi".
    iDestruct "HPsi" as "(%Hwi & Hhalf & Hrfrg & Hrlv & Hlvh & Hgid & Hpayl)".
    subst winum.
    set (F3 := <[Regidx Rs2 := regval_into_reg (sign_extend' 64 inum)]> F2).
    assert (HF3s2 : F3 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /F3; apply upd_eq).
    assert (HF3s1 : F3 !!! Regidx Rs1 = ientry k)
      by (rewrite /F3 upd_ne; [exact HF2s1 | nz]).
    assert (HF3sp : F3 !!! Regidx csp_rs1 = spd)
      by (rewrite /F3 upd_ne; [exact HF2sp | nz]).
    assert (HF3s3 : F3 !!! Regidx Rs3 = m !!! Regidx Rs3)
      by (rewrite /F3 upd_ne; [exact HF2s3 | nz]).
    assert (HF3s4 : F3 !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64))
      by (rewrite /F3 upd_ne; [exact HF2s4 | nz]).
    assert (HF3a5 : F3 !!! Regidx Ra5 = sign_extend' 64 (iref_word Mt k))
      by (rewrite /F3 upd_ne; [exact HF2a5 | nz]).
    assert (HF3hi : F3 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
                    F3 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
                    F3 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
                    F3 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
                    F3 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
                    F3 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
                    F3 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
    { destruct HF2hi as (G1&G2&G3&G4'&G5&G6&G7).
      repeat split; (rewrite /F3 upd_ne; [| nz]); assumption. }
    assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.iput + 0x46) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x4a)) by pcw.
    iEval (rewrite Hpp4a) in "Hpc".
    (* ===== +0x4a lh a4,74(s1) : nlink, a PLAIN read off the held payload ===== *)
    iPoseProof (ipi_4a with "Htext") as "Hi4a".
    iEval (rewrite /ic_payload_at) in "Hpayl".
    iDestruct "Hpayl" as "[Hlk #Hshot]".
    iDestruct "Hlk" as (data)
      "(%Hok & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlk & Hdat & Hmeta & Haddrs & Hind & Hblks)".
    pose proof Hok as Hok'.
    destruct Hok' as (Hbmwf & Hcovers & Hdiaddrs & Htyne & Hszcap & Hholes & Hsized).
    iEval (rewrite /inode_meta) in "Hmeta".
    iDestruct "Hmeta" as "(Hmty & Hmmaj & Hmmin & Hmnl & Hmsz)".
    assert (Hpa4a : add_vec (rget F3 Rs1) (sign_extend' 64 (mword_of_int 74 : mword 12))
                    = i_nlink (ientry k)).
    { rewrite (rget_ne F3 Rs1 ltac:(nz)) HF3s1. reflexivity. }
    iEval (rewrite -Hpa4a) in "Hmnl".
    iApply (wp_lh_s_sconf (mword_of_int (KernelSyms.iput + 0x4a)) Ra4 Rs1
              (mword_of_int 74 : mword 12) F3 (trap_res eb + (K - 6))%nat (di_nlink dn) false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi4a Hmnl").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hmnl".
    iEval (rewrite Hpa4a) in "Hmnl".
    set (F4 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 (di_nlink dn : mword 16))]> F3).
    assert (HF4a4 : F4 !!! Regidx Ra4 = (sign_extend' 64 (di_nlink dn : mword 16) : mword 64))
      by (rewrite /F4; apply upd_eq).
    assert (HF4s1 : F4 !!! Regidx Rs1 = ientry k)
      by (rewrite /F4 upd_ne; [exact HF3s1 | nz]).
    assert (HF4sp : F4 !!! Regidx csp_rs1 = spd)
      by (rewrite /F4 upd_ne; [exact HF3sp | nz]).
    assert (HF4s2 : F4 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /F4 upd_ne; [exact HF3s2 | nz]).
    assert (HF4s3 : F4 !!! Regidx Rs3 = m !!! Regidx Rs3)
      by (rewrite /F4 upd_ne; [exact HF3s3 | nz]).
    assert (HF4s4 : F4 !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64))
      by (rewrite /F4 upd_ne; [exact HF3s4 | nz]).
    assert (HF4a5 : F4 !!! Regidx Ra5 = sign_extend' 64 (iref_word Mt k))
      by (rewrite /F4 upd_ne; [exact HF3a5 | nz]).
    assert (HF4hi : F4 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
                    F4 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
                    F4 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
                    F4 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
                    F4 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
                    F4 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
                    F4 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
    { destruct HF3hi as (G1&G2&G3&G4'&G5&G6&G7).
      repeat split; (rewrite /F4 upd_ne; [| nz]); assumption. }
    assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.iput + 0x4a) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x4e)) by pcw.
    iEval (rewrite Hpp4e) in "Hpc".
    iPoseProof (ipi_4e with "Htext") as "Hi4e".
    (* ===== +0x4e c.bnez a4 : nlink != 0 UNDOES the window (EXIT A) ===== *)
    destruct (neq_vec (sign_extend' 64 (di_nlink dn : mword 16) : mword 64)
                      (zero_reg : mword 64)) eqn:Hnl0.
    { (* nlink != 0 : re-park at PARKED and take the tail through 0xcc/0xce/0xd0.
         Stale pattern ProofIput.v:1677-1744, with the extra twist that the
         window here was entered at 0x3a and re-entered at 0x46. *)
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.iput + 0x4e))
                (mword_of_int 63 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                F4 (trap_res eb + (K - 6))%nat false
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HF4a4; exact Hnl0)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi4e").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hppcc : add_vec (mword_of_int (KernelSyms.iput + 0x4e) : mword 64)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 63 : mword 8) ('b"0"))))
                      = mword_of_int (KernelSyms.iput + 0xcc)) by pcw.
      iEval (rewrite Hppcc) in "Hpc".
      (* ---- the UNDO: HELD -> PARKED, nothing retyped, no generation bump ---- *)
      iApply fupd_wp.
      iInv "Hesc" as ">Hbody" "Hclose".
      iAssert (ic_payload_at γfs γi cov logstart k inum ga dn bm)
        with "[Hdat Hmty Hmmaj Hmmin Hmnl Hmsz Haddrs Hind Hblks Hdlk]" as "Hpayl".
      { rewrite /ic_payload_at.
        iSplitR "Hshot"; [| iExact "Hshot"]. iExists data.
        iSplitR; [iPureIntro; exact Hok |].
        iSplitR; [iPureIntro; exact Hdok |].
        iSplitR; [iPureIntro; exact Hddix |].
        iSplitR; [iPureIntro; exact Hdoc |].
        iSplitR; [iPureIntro; exact Hduq |].
        iSplitL "Hdlk"; [iExact "Hdlk" |]. rewrite /inode_meta. iFrame. }
      iMod (ic_open_held cn γfs γi cov logstart k (⊤ ∖ ↑icEscN)
              Mt q ga ga dev inum dn bm ltac:(solve_ndisj) HMk1
              with "Hitinv Hbody Hhalf Hrfrg Hrlv Hlvh Hgid Hpayl")
        as "(Hhalf & Hrfrg & Hrlv & Hlvh & Hgid & Hpayl & Hidv & Hnfull & Hvldx & Hmt & Hgida)".
      iAssert (iref_tok k q) with "[Hrfrg Hrlv Hrslh]" as "Hrtok".
      { rewrite /iref_tok. iFrame. }
      iDestruct (ic_payload_at_pack with "Hpayl") as "Hpayl".
      iDestruct "Hvldx" as (w0) "Hva".
      iDestruct (word4_pointsto_agree with "Hvb Hva") as %<-.
      iDestruct (word4_pointsto_half_join with "Hvb Hva") as "Hvld".
      (* the FULL inum cell splits back: the arm's half, our q, the table's qr *)
      iDestruct (word4_pointsto_half_split with "Hnfull") as "[Hinh Hn2]".
      iEval (rewrite Hsum) in "Hn2".
      iDestruct (word4_pointsto_frac_split (i_inum (ientry k)) q qr inum with "Hn2")
        as "[Hrn Htn]".
      iMod ("Hclose" with "[Hidv Hinh Hvld Hpayl Hlvh Hmt Hgida]") as "_".
      { iApply bi.later_intro. iApply ic_close_parked.
        iApply (ic_mk_parked cn γfs γi cov logstart k dev inum true ga
                  with "Hidv Hinh Hvld Hpayl Hlvh Hmt Hgida"). }
      iModIntro.
      iDestruct ("Hback" $! Mt ci with "[%] [%] [Htd Htn Hiu Hgid]") as "Hslots";
        [ intros i Hi; reflexivity | intros i Hi; reflexivity | | ].
      { rewrite /islot2 HMk1 Hcik. rewrite /islot_rest_at Ert /IcacheRef.inode_ident.
        iFrame. }
      (* ===== +0xcc c.ldsp s2,16(sp) ; +0xce c.ldsp s4,0(sp) ===== *)
      iPoseProof (ipi_cc with "Htext") as "Hicc".
      iPoseProof (ipi_ce with "Htext") as "Hice".
      iPoseProof (ipi_d0 with "Htext") as "Hid0".
      iEval (rewrite -Hb4 -HF4sp) in "Hg4".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iput + 0xcc))
                (mword_of_int 2 : mword 6) Rs2 F4 (trap_res eb + (K - 6))%nat
                (m !!! Regidx Rs2) false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hicc Hg4").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hg4".
      iEval (rewrite HF4sp Hb4) in "Hg4".
      set (G1 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> F4).
      assert (HG1sp : G1 !!! Regidx csp_rs1 = spd)
        by (rewrite /G1 upd_ne; [exact HF4sp | nz]).
      assert (Hppce : add_vec_int (mword_of_int (KernelSyms.iput + 0xcc) : mword 64) 2
                      = mword_of_int (KernelSyms.iput + 0xce)) by pcw.
      iEval (rewrite Hppce) in "Hpc".
      iEval (rewrite -Hb6 -HG1sp) in "Hg6".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iput + 0xce))
                (mword_of_int 0 : mword 6) Rs4 G1 (trap_res eb + (K - 6))%nat
                (m !!! Regidx Rs4) false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hice Hg6").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hg6".
      iEval (rewrite HG1sp Hb6) in "Hg6".
      set (G2 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4)]> G1).
      assert (Hppd0 : add_vec_int (mword_of_int (KernelSyms.iput + 0xce) : mword 64) 2
                      = mword_of_int (KernelSyms.iput + 0xd0)) by pcw.
      iEval (rewrite Hppd0) in "Hpc".
      (* ===== +0xd0 c.j -176 -> +0x20 ===== *)
      assert (Htgtd0 : add_vec (mword_of_int (KernelSyms.iput + 0xd0) : mword 64)
                         (sign_extend' 64 (sign_extend' 21
                            (concat_vec (mword_of_int 1960 : mword 11) ('b"0"))))
                       = mword_of_int (KernelSyms.iput + 0x20)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.iput + 0xd0))
                (sign_extend' 21 (concat_vec (mword_of_int 1960 : mword 11) ('b"0")))
                G2 (trap_res eb + (K - 6))%nat false
                ltac:(rewrite Htgtd0; vm_compute; reflexivity) with "Hcg Hpc Hid0").
      iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgtd0) in "Hpc".
      assert (HG2regs : ipe_regs m G2 spd k).
      { destruct HF4hi as (P21&P22&P23&P24&P25&P26&P27).
        unfold ipe_regs. split_and!.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact HF4s1.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact HF4sp.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1. apply upd_eq.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact HF4s3.
        - rewrite /G2. apply upd_eq.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact P21.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact P22.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact P23.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact P24.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact P25.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact P26.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact P27. }
      assert (HG2a5 : G2 !!! Regidx Ra5 = sign_extend' 64 (iref_word Mt k)).
      { rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact HF4a5. }
      iApply ("HcA" $! G2 (m !!! Regidx Rs2) vg5 (m !!! Regidx Rs4)
                with "[%] [%] Hcg Hcnt Hpay Hextc Hclm Hpc Htok Hhalf Hiauth Hipool
                      Hslots Hpool [Hrtok Hrd Hrn] Hbms Hins Hbm Hppid Hbslots Hvlb
                      Hcrd Hop Hr1 Hr2 Hr3 Hg4 Hg5 Hg6").
      { exact HG2regs. }
      { exact HG2a5. }
      { rewrite /IcacheRef.inode_ref /IcacheRef.inode_ident. iFrame. } }
    (* ===== nlink == 0: fall through at 0x4e -- the FREE path ===== *)
    iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.iput + 0x4e))
              (mword_of_int 63 : mword 8) (Cregidx (mword_of_int 6)) Ra4
              F4 (trap_res eb + (K - 6))%nat false
              ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HF4a4; exact Hnl0)
              with "Hcg Hpc Hi4e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.iput + 0x4e) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x50)) by pcw.
    iEval (rewrite Hpp50) in "Hpc".
    iPoseProof (ipi_50 with "Htext") as "Hi50".
    iPoseProof (ipi_52 with "Htext") as "Hi52".
    iPoseProof (ipi_56 with "Htext") as "Hi56".
    iPoseProof (ipi_58 with "Htext") as "Hi58".
    (* ===== +0x50 c.sdsp s3,8(sp) ===== *)
    iEval (rewrite -Hb5 -HF4sp) in "Hg5".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iput + 0x50))
              (mword_of_int 1 : mword 6) Rs3 F4 (trap_res eb + (K - 6))%nat vg5 false
              with "Hcg Hpc Hi50 Hg5").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hg5".
    iEval (rgne) in "Hg5".
    iEval (rewrite HF4s3 HF4sp Hb5) in "Hg5".
    assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.iput + 0x50) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x52)) by pcw.
    iEval (rewrite Hpp52) in "Hpc".
    (* ===== +0x52 addi a5,s1,16 ; +0x56 c.mv s3,a5 ; +0x58 c.mv a0,a5 ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iput + 0x52)) Ra5 Rs1
              (mword_of_int 16 : mword 12) F4 (trap_res eb + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi52").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (F5 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (rget F4 Rs1) (sign_extend' 64 (mword_of_int 16 : mword 12)))]> F4).
    assert (HF5a5 : F5 !!! Regidx Ra5 = i_lock (ientry k)).
    { rewrite /F5 upd_eq. unfold regval_into_reg.
      rewrite (rget_ne F4 Rs1 ltac:(nz)) HF4s1. reflexivity. }
    assert (HF5s1 : F5 !!! Regidx Rs1 = ientry k)
      by (rewrite /F5 upd_ne; [exact HF4s1 | nz]).
    assert (HF5sp : F5 !!! Regidx csp_rs1 = spd)
      by (rewrite /F5 upd_ne; [exact HF4sp | nz]).
    assert (HF5s2 : F5 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /F5 upd_ne; [exact HF4s2 | nz]).
    assert (HF5s4 : F5 !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64))
      by (rewrite /F5 upd_ne; [exact HF4s4 | nz]).
    assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.iput + 0x52) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x56)) by pcw.
    iEval (rewrite Hpp56) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iput + 0x56)) Rs3 Ra5
              F5 (trap_res eb + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi56").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (F6 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (F5 !!! Regidx Ra5))]> F5).
    assert (HF6s3 : F6 !!! Regidx Rs3 = i_lock (ientry k)).
    { rewrite /F6 upd_eq. rewrite HF5a5. apply add_vec_zero_l. }
    assert (HF6a5 : F6 !!! Regidx Ra5 = i_lock (ientry k))
      by (rewrite /F6 upd_ne; [exact HF5a5 | nz]).
    assert (HF6s1 : F6 !!! Regidx Rs1 = ientry k)
      by (rewrite /F6 upd_ne; [exact HF5s1 | nz]).
    assert (HF6sp : F6 !!! Regidx csp_rs1 = spd)
      by (rewrite /F6 upd_ne; [exact HF5sp | nz]).
    assert (HF6s2 : F6 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /F6 upd_ne; [exact HF5s2 | nz]).
    assert (HF6s4 : F6 !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64))
      by (rewrite /F6 upd_ne; [exact HF5s4 | nz]).
    assert (Hpp58 : add_vec_int (mword_of_int (KernelSyms.iput + 0x56) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x58)) by pcw.
    iEval (rewrite Hpp58) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iput + 0x58)) Ra0 Ra5
              F6 (trap_res eb + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi58").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (F7 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (F6 !!! Regidx Ra5))]> F6).
    assert (HF7a0 : F7 !!! Regidx Ra0 = i_lock (ientry k)).
    { rewrite /F7 upd_eq. rewrite HF6a5. apply add_vec_zero_l. }
    assert (HF7s1 : F7 !!! Regidx Rs1 = ientry k)
      by (rewrite /F7 upd_ne; [exact HF6s1 | nz]).
    assert (HF7sp : F7 !!! Regidx csp_rs1 = spd)
      by (rewrite /F7 upd_ne; [exact HF6sp | nz]).
    assert (HF7s2 : F7 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /F7 upd_ne; [exact HF6s2 | nz]).
    assert (HF7s3 : F7 !!! Regidx Rs3 = i_lock (ientry k))
      by (rewrite /F7 upd_ne; [exact HF6s3 | nz]).
    assert (HF7s4 : F7 !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64))
      by (rewrite /F7 upd_ne; [exact HF6s4 | nz]).
    assert (HF7hi : F7 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
                    F7 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
                    F7 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
                    F7 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
                    F7 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
                    F7 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
                    F7 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
    { destruct HF4hi as (P21&P22&P23&P24&P25&P26&P27).
      repeat split;
        (rewrite /F7 upd_ne; [| nz]); (rewrite /F6 upd_ne; [| nz]);
        (rewrite /F5 upd_ne; [| nz]); assumption. }
    assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.iput + 0x58) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x5a)) by pcw.
    iEval (rewrite Hpp5a) in "Hpc".
    (* ===== 0x5a: ip_free_locked's ENTRY.  Re-pack the payload, mint the
       re-assembly wand, hand the bundle over. ===== *)
    iAssert (ic_payload_at γfs γi cov logstart k inum ga dn bm)
      with "[Hdat Hmty Hmmaj Hmmin Hmnl Hmsz Haddrs Hind Hblks Hdlk]" as "Hpayl".
    { rewrite /ic_payload_at.
      iSplitR "Hshot"; [| iExact "Hshot"]. iExists data.
      iSplitR; [iPureIntro; exact Hok |].
      iSplitR; [iPureIntro; exact Hdok |].
      iSplitR; [iPureIntro; exact Hddix |].
      iSplitR; [iPureIntro; exact Hdoc |].
      iSplitR; [iPureIntro; exact Hduq |].
      iSplitL "Hdlk"; [iExact "Hdlk" |]. rewrite /inode_meta. iFrame. }
    iAssert (iref_tok k q) with "[Hrfrg Hrlv Hrslh]" as "Hrtok".
    { rewrite /iref_tok. iFrame. }
    iAssert (i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
             ic_id cn k (1/2) true dev inum -∗
               ([∗ list] i0 ∈ seq 0 NINODE, islot2 cn Mt ci i0) ∗
               IcacheRef.inode_ident k (DfracOwn q) dev inum)%I
      with "[Htd Hiu Hback Hrd]" as "Hwand".
    { iIntros "Hn2 Hgid2".
      iEval (rewrite Hsum) in "Hn2".
      iDestruct (word4_pointsto_frac_split (i_inum (ientry k)) q qr inum with "Hn2")
        as "[Hrn Htn]".
      iDestruct ("Hback" $! Mt ci with "[%] [%] [Htd Htn Hiu Hgid2]") as "Hslots";
        [ intros i Hi; reflexivity | intros i Hi; reflexivity | | ].
      { rewrite /islot2 HMk1 Hcik. rewrite /islot_rest_at Ert /IcacheRef.inode_ident.
        iFrame. }
      iSplitL "Hslots"; [iExact "Hslots" |].
      rewrite /IcacheRef.inode_ident. iFrame. }
    iApply ("HcB" $! F7 ga dn bm data
              with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                    Hcg Hcnt Hpay Hextc Hclm Hpc Htok Hhalf Hiauth Hipool Hpool
                    [%] Hrtok Hgid Hwand Hpayl Hlvh Hvb Hbms Hins Hbm Hppid Hbslots
                    Hvlb Hcrd Hop Hr1 Hr2 Hr3 Hg4 Hg5 Hg6").
    { exact Htyne. }
    { exact (fe_nlink_zero (di_nlink dn) Hnl0). }
    { exact (fe_dinode_wf cov logstart dn bm Hbmwf Hdiaddrs). }
    { exact Hbmwf. }
    { exact Hsized. }
    { exact Hdiaddrs. }
    { exact (eq_sym HF7sp). }
    { exact HF7a0. }
    { exact HF7s1. }
    { exact HF7s2. }
    { exact HF7s3. }
    { exact HF7s4. }
    { exact HF7hi. }
    { exact Hcik. }
  Qed.

End FreeEntryDev.
