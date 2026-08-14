(* ProofKexecC.v -- PHASE C of kexec: the user stack (+0x1ae .. +0x2a2).

   This chunk: the SETUP block, +0x1ae .. +0x218 -- myproc, PGROUNDUP(sz),
   the first uvmalloc call (two pages at PTE_W), uvmclear on the guard page,
   the stackbase arithmetic, and the argv[0] test that either enters the
   argv loop at +0x21a or skips straight to its exit at +0x272 with c = 0.
   claude-notes/projects/kexec.md has the design (re-verified against
   CodeKexec.v's decoded ASTs, not just the C).

   Reached through a MODULE APPLICATION, ProofKexecTail.v's reason: [B3 :=
   ProofKexecB3.KexecB3Proof ...] gives this file phase B whole, at the same
   functor arguments B3 itself took, plus [Uvmclear], the one new callee. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RegFile.
Require Import HartTp.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import StackBytes.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeHalf.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import SleepLock.
Require Import WpLock.
Require Import PanicStub.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import FsCrash.
Require Import InodeRegion.
Require Import IcacheEscrow.
Require Import ByteBuf.
Require Import VcGen.
Require Import W32Arith.
Require Import ElfEnc.
Require Import PageGeom.
Require Import ProcGeom.
Require Import ProcInv.
Require Import DiskPtsto.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import DirentEnc.
Require Import PathElems.
Require Import InodeInv.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import KallocInv.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import DinodeEnc.
Require Import DirView.
Require Import DirLinks.
Require Import InodeLock.
Require Import SchedCtx.
Require Import DiskInv.
Require Import PtTree.
Require Import PtBuild.
Require Import ProcPt.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import UmCovered.
Require Import FileInv.
Require Import SpecIput.
Require Import SpecKexec.
Require Import SpecMyproc.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecReadi.
Require Import SpecIunlockput.
Require Import SpecDirlink.
Require Import SpecNamei.
Require Import SpecProcFreepagetable.
Require Import SpecProcPagetable.
Require Import SpecWalkaddr.
Require Import SpecFlags2perm.
Require Import SpecUvmalloc.
Require Import SpecUvmclear.
Require Import SpecStrlen.
Require Import SpecCopyout.
Require Import ProofKexecParts.
Require Import ProofKexecTail.
Require Import ProofKexecSeam.
Require Import ProofKexecB3.
Require Import ProofKforkParts.
Require Import CodeKexec.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Notation KXC := KernelSyms.kexec (only parsing).

Module KexecCProof (Myproc : MYPROC) (BeginOp : BEGIN_OP) (Namei : NAMEI)
                   (Ilock : ILOCK) (Readi : READI) (Iunlockput : IUNLOCKPUT)
                   (EndOp : END_OP) (PFP : PROC_FREEPAGETABLE)
                   (Walkaddr : WALKADDR) (Flags2perm : FLAGS2PERM)
                   (Uvmalloc : UVMALLOC) (Uvmclear : UVMCLEAR)
                   (Strlen : STRLEN) (Copyout : COPYOUT).

Module B3 := ProofKexecB3.KexecB3Proof Myproc BeginOp Namei Ilock Readi
                                       Iunlockput EndOp PFP Walkaddr
                                       Flags2perm Uvmalloc.
Module A := B3.A.
Module TC := ProofKexecTail.KexecTailProofC Myproc BeginOp Namei Ilock Readi
                                            Iunlockput EndOp PFP.

Section KexecCSetup.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Rs8 := (mword_of_int 24 : mword 5).
  Notation Rs9 := (mword_of_int 25 : mword 5).
  Notation Rs10 := (mword_of_int 26 : mword 5).
  Notation Rs11 := (mword_of_int 27 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).

  Local Ltac regne := reg_ne_side.
  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  (* [lui a1,-2 ; add a1,a1,X] computes [X - 8192] -- a pure two's-complement
     identity, no bound on [X] needed, since both sides wrap the same way. *)
  (* [um_covered_z] is PAGE-GRANULAR, so it picks out the SAME set of vpns
     at [x] and at [pgroundup x]: no page boundary lies strictly between
     them (pgroundup rounds up to the very next one), so the strict "<"
     excludes that boundary vpn from both sides alike. Unlike [um_below]
     (anti-monotone in the bound, so [um_below_mono] runs the RIGHT way for
     growing szv to pgroundup szv), [um_covered] is monotone in the bound --
     [um_covered_z_mono] only shrinks it -- so this direction needs its own
     one-liner, off the same [pgroundup_unsigned] bound
     [UmCovered.um_covered_run] already uses. *)
  Local Lemma um_covered_pground (x : mword 64) (um : gmap (mword 27) (mword 64)) :
    (bv_unsigned x <= uvm_maxsz)%Z -> um_covered x um -> um_covered (pgroundup x) um.
  Proof.
    intros Hb Hc vpn Hlt. apply Hc.
    pose proof (bv_unsigned_in_range _ x) as [Hx0 _].
    assert (Hnw64 : (bv_unsigned x + 4095 < 2 ^ 64)%Z).
    { unfold uvm_maxsz in Hb. change (2 ^ 64)%Z with 18446744073709551616%Z. lia. }
    rewrite (pgroundup_unsigned x Hnw64) in Hlt.
    pose proof (Z_div_mod_eq_full (bv_unsigned x + 4095) 4096) as Hdm.
    pose proof (Z.mod_pos_bound (bv_unsigned x + 4095) 4096 ltac:(lia)) as Hmodb.
    lia.
  Qed.

  (* [uvmclear] overwrites exactly ONE existing leaf (the stack guard page) --
     these two are what let [um_below]/[um_covered] survive that edit onto
     the loop invariant's table. Only the KEY matters for [um_below] (any
     value already below the bound stays below it whatever it's overwritten
     with); an insert only ever grows the domain, so [um_covered] transfers
     unconditionally. *)
  Local Lemma kxc_um_below_insert (szv : mword 64) (um : gmap (mword 27) (mword 64))
      (vpn : mword 27) (x : mword 64) :
    um_below szv um -> (bv_unsigned vpn * 4096 < bv_unsigned szv)%Z ->
    um_below szv (<[vpn := x]> um).
  Proof.
    intros Hb Hvpn vpn' w Hl.
    destruct (decide (vpn' = vpn)) as [-> | Hne].
    - exact Hvpn.
    - rewrite lookup_insert_ne in Hl; [| exact (not_eq_sym Hne)]. eapply Hb; exact Hl.
  Qed.

  Local Lemma kxc_um_covered_insert (szv : mword 64) (um : gmap (mword 27) (mword 64))
      (vpn : mword 27) (x : mword 64) :
    um_covered szv um -> um_covered szv (<[vpn := x]> um).
  Proof.
    intros Hc vpn' Hlt.
    destruct (decide (vpn' = vpn)) as [-> | Hne].
    - rewrite lookup_insert. eauto.
    - rewrite lookup_insert_ne; [| exact (not_eq_sym Hne)]. apply Hc; exact Hlt.
  Qed.

  Local Lemma neq_vec64_true (x y : mword 64) : x <> y -> neq_vec x y = true.
  Proof.
    intro Hxy. unfold neq_vec.
    destruct (eq_vec x y) eqn:E; [| reflexivity].
    apply eq_vec_true_iff in E. contradiction.
  Qed.

  Local Lemma zero_reg64 : (zero_reg : mword 64) = mword_of_int 0.
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.

  Local Lemma eq_vec64_false (x y : mword 64) : x <> y -> eq_vec x y = false.
  Proof.
    intro Hxy. destruct (eq_vec x y) eqn:E; [| reflexivity].
    apply eq_vec_true_iff in E. contradiction.
  Qed.

  Local Lemma uvm_maxsz_lit : uvm_maxsz = 274877898752%Z.
  Proof. unfold uvm_maxsz. vm_compute. reflexivity. Qed.

  Local Lemma add_neg8192_eq_sub (x : mword 64) :
    add_vec (mword_of_int (-8192) : mword 64) x
    = sub_vec x (mword_of_int 8192 : mword 64).
  Proof.
    apply bv_eq. rewrite add_vec_unsigned sub_vec_unsigned !moi64_unsigned.
    unfold bv_wrap. change (MachineWord.MachineWord.Z_idx 64) with 64%N.
    rewrite Zplus_mod_idemp_l Zminus_mod_idemp_r. f_equal. lia.
  Qed.

  (* local copies of PrintintArith's [wrap_add3'] / [addv_moi_moi] -- that file
     is deliberately kept OUT of every WP file (its own header: a [Local Open
     Scope Z_scope] that leaks past [Require Import] and breaks [nat]-indexed
     goals like [seq _ _ !! _] elsewhere in this very lemma; confirmed by
     hand -- importing it here turned [seq 0 (S na) !! 0] into a [Z]-indexed
     lookup with no [Lookup] instance). Two immediate offsets off the same
     symbolic base collapse into one: this is what lets [HW2s7] avoid ever
     [vm_compute]-ing a goal that still mentions [sz1] (optimization.md,
     "Conversion and Qed" -- a prior version hung past 10 GB doing exactly
     that). *)
  Local Lemma kxc_wrap_add3' (a b c : Z) :
    bv_wrap 64 (a + bv_wrap 64 b + c) = bv_wrap 64 (a + b + c).
  Proof.
    replace (a + bv_wrap 64 b + c) with (bv_wrap 64 b + (a + c)) by ring.
    rewrite bv_wrap_add_idemp_l. f_equal. ring.
  Qed.

  Local Lemma kxc_addv_moi_moi (x : mword 64) (a b : Z) :
    add_vec (add_vec x (mword_of_int a)) (mword_of_int b) = add_vec x (mword_of_int (a + b)).
  Proof.
    apply bv_eq. rewrite !add_vec64_unsigned !moi64_unsigned.
    rewrite bv_wrap_add_idemp_l !bv_wrap_add_idemp_r.
    rewrite kxc_wrap_add3'. f_equal. ring.
  Qed.

  (* =================================================================== *)
  (*  +0x1ae .. +0x218 -- THE SETUP BLOCK.                                 *)
  (*                                                                       *)
  (*  Owns the ONE exit this range reaches ([kxc_bad_1d6], on uvmalloc's   *)
  (*  failure arm -- block-interface rule 3), and hands its own successor  *)
  (*  a DISJUNCTION over the loop's two possible entries (rule matching    *)
  (*  [ProofKexecB3.kxc_incr]): [kxc_at_21a 0] if [argv[0] <> 0], or        *)
  (*  [kxc_at_272 0] if the loop is skipped outright.                      *)
  (* =================================================================== *)
  Lemma kxc_c_setup
      (jp : nat) (bn : bio_names) (gfs : fs_names) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (size : Z) (used used2 : gset Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
      (m M : regfile) (K : nat) (C : iProp Σ)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (szv : mword 64) :
    (K_kexec <= K)%nat ->
    m !!! Regidx csp_rs1 = sp0 -> m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 -> m !!! Regidx Rs1 = s10 -> m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Rs3 = w5 -> m !!! Regidx Rs4 = w6 -> m !!! Regidx Rs5 = w7 ->
    m !!! Regidx Rs6 = w8 -> m !!! Regidx Rs7 = w9 -> m !!! Regidx Rs8 = w10 ->
    m !!! Regidx Rs9 = w11 -> m !!! Regidx Rs10 = w12 -> m !!! Regidx Rs11 = w13 ->
    (* not used here -- [kxc_c_setup] never reads an argument string -- but
       [alen]/[afun] leave this lemma's own scope for the first time in
       [kxc_at_21a]'s conjuncts, and the argv loop that consumes that state
       needs both facts to call [strlen] on argument [i]. Carrying them from
       here, unconsumed, means the argv loop's own lemmas don't need a
       SEPARATE way to reach back to [SpecKexec]'s contract for them. *)
    (forall i, (i < na)%nat -> (alen i < aslen i)%nat) ->
    (forall i, (i < na)%nat -> bb_cstr (afun i) (alen i)) ->
    (forall i, (i < na)%nat -> (Z.of_nat (alen i) < 4096)%Z) ->
    avf na = (mword_of_int 0 : mword 64) ->
    kernel_text -∗
    kxc_at_1ae jp bn gfs ga gf cov logstart bmapstart inodestart size
               used used2 plen pfun na avf aslen afun pidv V dqb dqs dqa
               M K C sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P szv -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
    ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
       (entry spv szv' : mword 64),
        ⌜callee_saved m mf⌝ -∗
        ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
        sie_cap_gpr mf K true (proc_addr jp) -∗
        cpu_own 0 true (proc_addr jp) C true -∗
        pc_is (ret_pc ra0) -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        ⌜used' ⊆ used⌝ -∗
        bitmap_res gfs bmapstart cov logstart size used' -∗
        kalloc_env ga None -∗
        proc_priv gf (proc_addr jp) pidv V' -∗
        ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
        ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
        ([∗ list] i ∈ seq 0 na,
           [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
        bslots bn 3 -∗
        iref_slots 2 -∗
        WP (Loop : expr riscv_lang)) -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M' : regfile) (P' : uptd) (oldsz sz1 : mword 64),
        ( kxc_at_21a jp bn gfs ga gf cov logstart bmapstart inodestart size
                     used2 plen pfun na avf alen aslen afun pidv V dqb dqs dqa
                     M' K C sp0 ra0 s00 s10 s20 pv av
                     w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P' oldsz sz1 0
          ∨ kxc_at_272 jp bn gfs ga gf cov logstart bmapstart inodestart size
                       used2 plen pfun na avf alen aslen afun pidv V dqb dqs dqa
                       M' K C sp0 ra0 s00 s10 s20 pv av
                       w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P' oldsz sz1 0 ) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hmsp Hmra Hms0 Hms1 Hms2
           Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13
           Halen_bound Halen_cstr Halen_4096 Havf_na.
    unfold K_kexec in HK.
    iIntros "#Htext Hst Hcont Hout".
    rewrite /kxc_at_1ae.
    iDestruct "Hst" as "((%HMsp & %HMs0 & %HMs2 & %HMs6) &
                         (%Hu2 & %Hal) &
                         (%HPtfp & %Hbelow & %Hcov) &
                         Hpc & Hcg & Hcnt & Hirs & Hbm & Hins &
                         Hbits & Hbs & #Hka & Hpt & Hpriv & Hpath & Hargv &
                         Hargs & Helf & Hframe)".
    rewrite /kxc_frameB.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 &
                            Hf9 & Hf10 & Hf11 & Hf12 & Hf13 & Hust & Hph &
                            Hf64 & Hf65 & Hf66 & Hf67 & Hf68)".
    iPoseProof (kxc_1ae with "Htext") as "Hi1ae".
    iPoseProof (kxc_1b2 with "Htext") as "Hi1b2".
    iPoseProof (kxc_1b4 with "Htext") as "Hi1b4".
    iPoseProof (kxc_1b8 with "Htext") as "Hi1b8".
    iPoseProof (kxc_1ba with "Htext") as "Hi1ba".
    iPoseProof (kxc_1bc with "Htext") as "Hi1bc".
    iPoseProof (kxc_1be with "Htext") as "Hi1be".
    iPoseProof (kxc_1c0 with "Htext") as "Hi1c0".
    iPoseProof (kxc_1c4 with "Htext") as "Hi1c4".
    iPoseProof (kxc_1c6 with "Htext") as "Hi1c6".
    iPoseProof (kxc_1c8 with "Htext") as "Hi1c8".
    iPoseProof (kxc_1ca with "Htext") as "Hi1ca".
    iPoseProof (kxc_1cc with "Htext") as "Hi1cc".
    iPoseProof (kxc_1ce with "Htext") as "Hi1ce".
    iPoseProof (kxc_1d2 with "Htext") as "Hi1d2".
    iPoseProof (kxc_1d4 with "Htext") as "Hi1d4".
    iPoseProof (kxc_1f4 with "Htext") as "Hi1f4".
    iPoseProof (kxc_1f6 with "Htext") as "Hi1f6".
    iPoseProof (kxc_1f8 with "Htext") as "Hi1f8".
    iPoseProof (kxc_1fa with "Htext") as "Hi1fa".
    iPoseProof (kxc_1fe with "Htext") as "Hi1fe".
    iPoseProof (kxc_202 with "Htext") as "Hi202".
    iPoseProof (kxc_206 with "Htext") as "Hi206".
    iPoseProof (kxc_20a with "Htext") as "Hi20a".
    iPoseProof (kxc_20c with "Htext") as "Hi20c".
    iPoseProof (kxc_20e with "Htext") as "Hi20e".
    iPoseProof (kxc_210 with "Htext") as "Hi210".
    iPoseProof (kxc_214 with "Htext") as "Hi214".
    iPoseProof (kxc_218 with "Htext") as "Hi218".
    (* ---- +0x1ae: jal ra,myproc ---- *)
    assert (Htmp : add_vec (mword_of_int (KXC + 0x1ae) : mword 64)
                     (sign_extend' 64 (mword_of_int 2084820 : mword 21))
                   = mword_of_int KernelSyms.myproc) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXC + 0x1ae)) Rra
              (mword_of_int 2084820 : mword 21) M (K - 68)%nat true
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htmp; vm_compute; reflexivity)
              with "Hcg Hpc Hi1ae").
    iIntros (CID1 Hs1) "Hcg Hpc". iEval (rewrite Htmp) in "Hpc".
    pose (T0 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXC + 0x1ae) : mword 64) 4)]> M).
    assert (HT0ra : T0 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXC + 0x1ae) : mword 64) 4)
      by (rewrite /T0; apply upd_eq).
    assert (HT0sp : T0 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T0 upd_ne; [exact HMsp | nz]).
    assert (HT0s2 : T0 !!! Regidx Rs2 = szv)
      by (rewrite /T0 upd_ne; [exact HMs2 | nz]).
    assert (HT0s6 : T0 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T0 upd_ne; [exact HMs6 | nz]).
    iDestruct (cpu_own_transport CID0 CID1 0%nat true (proc_addr jp) C true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Myproc.wp_myproc_sconf T0 (K - 68)%nat 0%nat true (proc_addr jp)
              C true ltac:(lia) ltac:(lia) with "Hcg Hcnt Htext Hpc").
    iIntros (CID2 Hs2 ms M1) "%Hmsf Hcg Hcnt Hpc %HM1".
    destruct HM1 as [Hcs1 HM1a0].
    assert (Hpc1b2 : ret_pc (T0 !!! Regidx Rra) = mword_of_int (KXC + 0x1b2))
      by (rewrite HT0ra; pcw).
    iEval (rewrite Hpc1b2) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 68).
    { rewrite (callee_saved_lookup Hcs1 csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HT0sp. }
    assert (HM1s2 : M1 !!! Regidx Rs2 = szv).
    { rewrite (callee_saved_lookup Hcs1 Rs2 ltac:(vm_compute; reflexivity)).
      exact HT0s2. }
    assert (HM1s6 : M1 !!! Regidx Rs6 = page_base P.(ud_root)).
    { rewrite (callee_saved_lookup Hcs1 Rs6 ltac:(vm_compute; reflexivity)).
      exact HT0s6. }
    (* ---- +0x1b2: c.mv s5,a0 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXC + 0x1b2)) Rs5 Ra0
              M1 (K - 68)%nat true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi1b2").
    iIntros (CID3 Hs3) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (T1 := <[Regidx Rs5 := regval_into_reg
                  (add_vec zero_reg (M1 !!! Regidx Ra0))]> M1).
    assert (HT1s5 : T1 !!! Regidx Rs5 = proc_addr jp).
    { rewrite /T1 upd_eq HM1a0. apply add_vec_zero_l. }
    assert (HT1a0 : T1 !!! Regidx Ra0 = proc_addr jp)
      by (rewrite /T1 upd_ne; [exact HM1a0 | nz]).
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T1 upd_ne; [exact HM1sp | nz]).
    assert (HT1s2 : T1 !!! Regidx Rs2 = szv)
      by (rewrite /T1 upd_ne; [exact HM1s2 | nz]).
    assert (HT1s6 : T1 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T1 upd_ne; [exact HM1s6 | nz]).
    assert (Hpp1b4 : add_vec_int (mword_of_int (KXC + 0x1b2) : mword 64) 2
                     = mword_of_int (KXC + 0x1b4)) by pcw.
    iEval (rewrite Hpp1b4) in "Hpc".
    (* ---- +0x1b4: ld s10,72(a0) -- p->sz, via the OLD a0 = p.  Peeled       *)
    (* inline ([proc_priv]/[proc_priv_core]/[proc_fields] unfolded) rather   *)
    (* than through [proc_priv_addrspace]: that accessor's restore wand      *)
    (* asks for the two size-bound facts again, and unfolding once gets     *)
    (* them as ORDINARY (persistent) Coq hypotheses instead, cheaper than    *)
    (* re-deriving them.  [Htfp] stays an OPAQUE bundle throughout -- it is  *)
    (* [tf_page]'s 4096-conjunct big-op, and this file's [iFrame] ban is     *)
    (* about not touching it, not about proc_priv's other four fields. ---- *)
    iEval (rewrite /proc_priv /proc_priv_core) in "Hpriv".
    iDestruct "Hpriv" as "((%Hszb & %Hbel & Hpid & Hfields & Hptat & Htfp &
                           Hcwdref) & Hof)".
    iEval (rewrite /proc_fields) in "Hfields".
    iDestruct "Hfields" as "(Hsz & Hcwd & %Hnl & Hnm)".
    assert (Hpszaddr : add_vec (T1 !!! Regidx Ra0)
                          (sign_extend' 64 (mword_of_int 72 : mword 12))
                        = p_sz (proc_addr jp)) by (rewrite HT1a0; reflexivity).
    iEval (rewrite -Hpszaddr) in "Hsz".
    iApply (wp_ld_s_sconf (mword_of_int (KXC + 0x1b4)) Rs10 Ra0
              (mword_of_int 72 : mword 12) T1 (K - 68)%nat (pv_sz V) true
              (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi1b4 Hsz").
    iIntros (CID4 Hs4) "Hcg Hpc Hsz". iEval (rewrite Hpszaddr) in "Hsz".
    pose (T2 := <[Regidx Rs10 := regval_into_reg (pv_sz V)]> T1).
    assert (HT2s10 : T2 !!! Regidx Rs10 = pv_sz V) by (rewrite /T2; apply upd_eq).
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T2 upd_ne; [exact HT1sp | nz]).
    assert (HT2s2 : T2 !!! Regidx Rs2 = szv)
      by (rewrite /T2 upd_ne; [exact HT1s2 | nz]).
    assert (HT2s5 : T2 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /T2 upd_ne; [exact HT1s5 | nz]).
    assert (HT2s6 : T2 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T2 upd_ne; [exact HT1s6 | nz]).
    assert (Hpp1b8 : add_vec_int (mword_of_int (KXC + 0x1b4) : mword 64) 4
                     = mword_of_int (KXC + 0x1b8)) by pcw.
    iEval (rewrite Hpp1b8) in "Hpc".
    (* reassemble [proc_priv] -- nothing moved, so this is the same block. *)
    iAssert (proc_priv gf (proc_addr jp) pidv V) with
      "[Hpid Hsz Hcwd Hnm Hptat Htfp Hcwdref Hof]" as "Hpriv".
    { rewrite /proc_priv /proc_priv_core /proc_fields.
      iSplitL "Hpid Hsz Hcwd Hnm Hptat Htfp Hcwdref"; [| iExact "Hof"].
      iSplitR; [iPureIntro; exact Hszb |].
      iSplitR; [iPureIntro; exact Hbel |].
      iSplitL "Hpid"; [iExact "Hpid" |].
      iSplitL "Hsz Hcwd Hnm";
        [| iSplitL "Hptat"; [iExact "Hptat" |]; iSplitL "Htfp"; [iExact "Htfp" | iExact "Hcwdref"]].
      iSplitL "Hsz"; [iExact "Hsz" |]. iSplitL "Hcwd"; [iExact "Hcwd" |].
      iSplitR; [iPureIntro; exact Hnl | iExact "Hnm"]. }
    (* ---- +0x1b8: c.lui s3,1 (s3 = 4096) ---- *)
    iApply (wp_clui_s_sconf (mword_of_int (KXC + 0x1b8)) Rs3
              (sign_extend' 20 (mword_of_int 1 : mword 6))
              (mword_of_int 4096 : mword 64) T2 (K - 68)%nat true
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1b8").
    iIntros (CID5 Hs5) "Hcg Hpc".
    pose (T3 := <[Regidx Rs3 := regval_into_reg (mword_of_int 4096 : mword 64)]> T2).
    assert (HT3s3 : T3 !!! Regidx Rs3 = (mword_of_int 4096 : mword 64))
      by (rewrite /T3; apply upd_eq).
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T3 upd_ne; [exact HT2sp | nz]).
    assert (HT3s2 : T3 !!! Regidx Rs2 = szv)
      by (rewrite /T3 upd_ne; [exact HT2s2 | nz]).
    assert (HT3s5 : T3 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /T3 upd_ne; [exact HT2s5 | nz]).
    assert (HT3s6 : T3 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T3 upd_ne; [exact HT2s6 | nz]).
    assert (HT3s10 : T3 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /T3 upd_ne; [exact HT2s10 | nz]).
    assert (Hpp1ba : add_vec_int (mword_of_int (KXC + 0x1b8) : mword 64) 2
                     = mword_of_int (KXC + 0x1ba)) by pcw.
    iEval (rewrite Hpp1ba) in "Hpc".
    (* ---- +0x1ba: c.addi s3,s3,-1 (s3 = 4095) ---- *)
    iApply (wp_caddi_s_sconf (mword_of_int (KXC + 0x1ba)) Rs3
              (mword_of_int 63 : mword 6) T3 (K - 68)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1ba").
    iIntros (CID6 Hs6) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (T4 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (T3 !!! Regidx Rs3)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> T3).
    assert (HT4s3 : T4 !!! Regidx Rs3 = (mword_of_int 4095 : mword 64)).
    { rewrite /T4 upd_eq HT3s3. apply bv_eq; vm_compute; reflexivity. }
    assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T4 upd_ne; [exact HT3sp | nz]).
    assert (HT4s2 : T4 !!! Regidx Rs2 = szv)
      by (rewrite /T4 upd_ne; [exact HT3s2 | nz]).
    assert (HT4s5 : T4 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /T4 upd_ne; [exact HT3s5 | nz]).
    assert (HT4s6 : T4 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T4 upd_ne; [exact HT3s6 | nz]).
    assert (HT4s10 : T4 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /T4 upd_ne; [exact HT3s10 | nz]).
    assert (Hpp1bc : add_vec_int (mword_of_int (KXC + 0x1ba) : mword 64) 2
                     = mword_of_int (KXC + 0x1bc)) by pcw.
    iEval (rewrite Hpp1bc) in "Hpc".
    (* ---- +0x1bc: c.add s3,s3,s2 (s3 = 4095 + szv) ---- *)
    iApply (wp_cadd_s_sconf (mword_of_int (KXC + 0x1bc)) Rs3 Rs2
              T4 (K - 68)%nat true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi1bc").
    iIntros (CID7 Hs7) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (T5 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (T4 !!! Regidx Rs3) (T4 !!! Regidx Rs2))]> T4).
    assert (HT5s3 : T5 !!! Regidx Rs3
                    = add_vec (mword_of_int 4095 : mword 64) szv).
    { rewrite /T5 upd_eq HT4s3 HT4s2. reflexivity. }
    assert (HT5sp : T5 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T5 upd_ne; [exact HT4sp | nz]).
    assert (HT5s5 : T5 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /T5 upd_ne; [exact HT4s5 | nz]).
    assert (HT5s6 : T5 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T5 upd_ne; [exact HT4s6 | nz]).
    assert (HT5s10 : T5 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /T5 upd_ne; [exact HT4s10 | nz]).
    assert (Hpp1be : add_vec_int (mword_of_int (KXC + 0x1bc) : mword 64) 2
                     = mword_of_int (KXC + 0x1be)) by pcw.
    iEval (rewrite Hpp1be) in "Hpc".
    (* ---- +0x1be: c.lui a5,-1 (a5 = 0xFFFF...F000) ---- *)
    iApply (wp_clui_s_sconf (mword_of_int (KXC + 0x1be)) Ra5
              (sign_extend' 20 (mword_of_int 63 : mword 6))
              (mword_of_int (-4096) : mword 64) T5 (K - 68)%nat true
              ltac:(nz) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi1be").
    iIntros (CID8 Hs8) "Hcg Hpc".
    pose (T6 := <[Regidx Ra5 := regval_into_reg (mword_of_int (-4096) : mword 64)]> T5).
    assert (HT6a5 : T6 !!! Regidx Ra5 = (mword_of_int (-4096) : mword 64))
      by (rewrite /T6; apply upd_eq).
    assert (HT6sp : T6 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T6 upd_ne; [exact HT5sp | nz]).
    assert (HT6s3 : T6 !!! Regidx Rs3 = add_vec (mword_of_int 4095 : mword 64) szv)
      by (rewrite /T6 upd_ne; [exact HT5s3 | nz]).
    assert (HT6s5 : T6 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /T6 upd_ne; [exact HT5s5 | nz]).
    assert (HT6s6 : T6 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T6 upd_ne; [exact HT5s6 | nz]).
    assert (HT6s10 : T6 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /T6 upd_ne; [exact HT5s10 | nz]).
    assert (Hpp1c0 : add_vec_int (mword_of_int (KXC + 0x1be) : mword 64) 2
                     = mword_of_int (KXC + 0x1c0)) by pcw.
    iEval (rewrite Hpp1c0) in "Hpc".
    (* ---- +0x1c0: and s3,s3,a5 -- s3 = PGROUNDUP(szv), base-encoded (rd  *)
    (* out of the compressed-AND range) ---- *)
    assert (HPground : and_vec (T6 !!! Regidx Rs3) (T6 !!! Regidx Ra5)
                       = pgroundup szv).
    { rewrite HT6s3 HT6a5 /pgroundup add_vec64_comm. reflexivity. }
    iApply (wp_and_s_sconf (mword_of_int (KXC + 0x1c0)) Rs3 Rs3 Ra5
              (pgroundup szv) T6 (K - 68)%nat true
              ltac:(nz) ltac:(rdok) HPground with "Hcg Hpc Hi1c0").
    iIntros (CID9 Hs9) "Hcg Hpc".
    pose (T7 := <[Regidx Rs3 := regval_into_reg (pgroundup szv)]> T6).
    assert (HT7s3 : T7 !!! Regidx Rs3 = pgroundup szv) by (rewrite /T7; apply upd_eq).
    assert (HT7sp : T7 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T7 upd_ne; [exact HT6sp | nz]).
    assert (HT7s5 : T7 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /T7 upd_ne; [exact HT6s5 | nz]).
    assert (HT7s6 : T7 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T7 upd_ne; [exact HT6s6 | nz]).
    assert (HT7s10 : T7 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /T7 upd_ne; [exact HT6s10 | nz]).
    assert (Hpp1c4 : add_vec_int (mword_of_int (KXC + 0x1c0) : mword 64) 4
                     = mword_of_int (KXC + 0x1c4)) by pcw.
    iEval (rewrite Hpp1c4) in "Hpc".
    (* ---- +0x1c4: c.li a3,4 (PTE_W) ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KXC + 0x1c4)) Ra3
              (mword_of_int 4 : mword 6) (mword_of_int 4 : mword 64)
              T7 (K - 68)%nat true ltac:(nz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi1c4").
    iIntros (CID10 Hs10) "Hcg Hpc".
    pose (T8 := <[Regidx Ra3 := regval_into_reg (mword_of_int 4 : mword 64)]> T7).
    assert (HT8a3 : T8 !!! Regidx Ra3 = (mword_of_int 4 : mword 64))
      by (rewrite /T8; apply upd_eq).
    assert (HT8sp : T8 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T8 upd_ne; [exact HT7sp | nz]).
    assert (HT8s3 : T8 !!! Regidx Rs3 = pgroundup szv)
      by (rewrite /T8 upd_ne; [exact HT7s3 | nz]).
    assert (HT8s5 : T8 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /T8 upd_ne; [exact HT7s5 | nz]).
    assert (HT8s6 : T8 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T8 upd_ne; [exact HT7s6 | nz]).
    assert (HT8s10 : T8 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /T8 upd_ne; [exact HT7s10 | nz]).
    assert (Hpp1c6 : add_vec_int (mword_of_int (KXC + 0x1c4) : mword 64) 2
                     = mword_of_int (KXC + 0x1c6)) by pcw.
    iEval (rewrite Hpp1c6) in "Hpc".
    (* ---- +0x1c6: c.lui a2,2 (a2 = 8192) ---- *)
    iApply (wp_clui_s_sconf (mword_of_int (KXC + 0x1c6)) Ra2
              (sign_extend' 20 (mword_of_int 2 : mword 6))
              (mword_of_int 8192 : mword 64) T8 (K - 68)%nat true
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1c6").
    iIntros (CID11 Hs11) "Hcg Hpc".
    pose (T9 := <[Regidx Ra2 := regval_into_reg (mword_of_int 8192 : mword 64)]> T8).
    assert (HT9a2 : T9 !!! Regidx Ra2 = (mword_of_int 8192 : mword 64))
      by (rewrite /T9; apply upd_eq).
    assert (HT9sp : T9 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T9 upd_ne; [exact HT8sp | nz]).
    assert (HT9a3 : T9 !!! Regidx Ra3 = (mword_of_int 4 : mword 64))
      by (rewrite /T9 upd_ne; [exact HT8a3 | nz]).
    assert (HT9s3 : T9 !!! Regidx Rs3 = pgroundup szv)
      by (rewrite /T9 upd_ne; [exact HT8s3 | nz]).
    assert (HT9s5 : T9 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /T9 upd_ne; [exact HT8s5 | nz]).
    assert (HT9s6 : T9 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T9 upd_ne; [exact HT8s6 | nz]).
    assert (HT9s10 : T9 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /T9 upd_ne; [exact HT8s10 | nz]).
    assert (Hpp1c8 : add_vec_int (mword_of_int (KXC + 0x1c6) : mword 64) 2
                     = mword_of_int (KXC + 0x1c8)) by pcw.
    iEval (rewrite Hpp1c8) in "Hpc".
    (* ---- +0x1c8: c.add a2,a2,s3 (a2 = 8192 + PGROUNDUP(szv) = newsz) ---- *)
    iApply (wp_cadd_s_sconf (mword_of_int (KXC + 0x1c8)) Ra2 Rs3
              T9 (K - 68)%nat true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi1c8").
    iIntros (CID12 Hs12) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (T10 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (T9 !!! Regidx Ra2) (T9 !!! Regidx Rs3))]> T9).
    assert (HT10a2 : T10 !!! Regidx Ra2
                    = add_vec (mword_of_int 8192 : mword 64) (pgroundup szv)).
    { rewrite /T10 upd_eq HT9a2 HT9s3. reflexivity. }
    assert (HT10sp : T10 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T10 upd_ne; [exact HT9sp | nz]).
    assert (HT10a3 : T10 !!! Regidx Ra3 = (mword_of_int 4 : mword 64))
      by (rewrite /T10 upd_ne; [exact HT9a3 | nz]).
    assert (HT10s3 : T10 !!! Regidx Rs3 = pgroundup szv)
      by (rewrite /T10 upd_ne; [exact HT9s3 | nz]).
    assert (HT10s5 : T10 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /T10 upd_ne; [exact HT9s5 | nz]).
    assert (HT10s6 : T10 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T10 upd_ne; [exact HT9s6 | nz]).
    assert (HT10s10 : T10 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /T10 upd_ne; [exact HT9s10 | nz]).
    assert (Hpp1ca : add_vec_int (mword_of_int (KXC + 0x1c8) : mword 64) 2
                     = mword_of_int (KXC + 0x1ca)) by pcw.
    iEval (rewrite Hpp1ca) in "Hpc".
    (* ---- +0x1ca: c.mv a1,s3 (a1 = oldsz arg = PGROUNDUP(szv)) ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXC + 0x1ca)) Ra1 Rs3
              T10 (K - 68)%nat true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi1ca").
    iIntros (CID13 Hs13) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (T11 := <[Regidx Ra1 := regval_into_reg
                  (add_vec zero_reg (T10 !!! Regidx Rs3))]> T10).
    assert (HT11a1 : T11 !!! Regidx Ra1 = pgroundup szv).
    { rewrite /T11 upd_eq HT10s3. apply add_vec_zero_l. }
    assert (HT11a2 : T11 !!! Regidx Ra2
                    = add_vec (mword_of_int 8192 : mword 64) (pgroundup szv))
      by (rewrite /T11 upd_ne; [exact HT10a2 | nz]).
    assert (HT11a3 : T11 !!! Regidx Ra3 = (mword_of_int 4 : mword 64))
      by (rewrite /T11 upd_ne; [exact HT10a3 | nz]).
    assert (HT11sp : T11 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T11 upd_ne; [exact HT10sp | nz]).
    assert (HT11s3 : T11 !!! Regidx Rs3 = pgroundup szv)
      by (rewrite /T11 upd_ne; [exact HT10s3 | nz]).
    assert (HT11s5 : T11 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /T11 upd_ne; [exact HT10s5 | nz]).
    assert (HT11s6 : T11 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T11 upd_ne; [exact HT10s6 | nz]).
    assert (HT11s10 : T11 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /T11 upd_ne; [exact HT10s10 | nz]).
    assert (Hpp1cc : add_vec_int (mword_of_int (KXC + 0x1ca) : mword 64) 2
                     = mword_of_int (KXC + 0x1cc)) by pcw.
    iEval (rewrite Hpp1cc) in "Hpc".
    (* ---- +0x1cc: c.mv a0,s6 (a0 = root arg) ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXC + 0x1cc)) Ra0 Rs6
              T11 (K - 68)%nat true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi1cc").
    iIntros (CID14 Hs14) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (T12 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (T11 !!! Regidx Rs6))]> T11).
    assert (HT12a0 : T12 !!! Regidx Ra0 = page_base P.(ud_root)).
    { rewrite /T12 upd_eq HT11s6. apply add_vec_zero_l. }
    assert (HT12a1 : T12 !!! Regidx Ra1 = pgroundup szv)
      by (rewrite /T12 upd_ne; [exact HT11a1 | nz]).
    assert (HT12a2 : T12 !!! Regidx Ra2
                    = add_vec (mword_of_int 8192 : mword 64) (pgroundup szv))
      by (rewrite /T12 upd_ne; [exact HT11a2 | nz]).
    assert (HT12a3 : T12 !!! Regidx Ra3 = (mword_of_int 4 : mword 64))
      by (rewrite /T12 upd_ne; [exact HT11a3 | nz]).
    assert (HT12sp : T12 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T12 upd_ne; [exact HT11sp | nz]).
    assert (HT12s3 : T12 !!! Regidx Rs3 = pgroundup szv)
      by (rewrite /T12 upd_ne; [exact HT11s3 | nz]).
    assert (HT12s10 : T12 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /T12 upd_ne; [exact HT11s10 | nz]).
    assert (HT12s6 : T12 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T12 upd_ne; [exact HT11s6 | nz]).
    assert (Hpp1ce : add_vec_int (mword_of_int (KXC + 0x1cc) : mword 64) 2
                     = mword_of_int (KXC + 0x1ce)) by pcw.
    iEval (rewrite Hpp1ce) in "Hpc".
    (* ---- +0x1ce: jal ra,uvmalloc ---- *)
    assert (Htuvm : add_vec (mword_of_int (KXC + 0x1ce) : mword 64)
                      (sign_extend' 64 (mword_of_int 2083162 : mword 21))
                    = mword_of_int KernelSyms.uvmalloc) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXC + 0x1ce)) Rra
              (mword_of_int 2083162 : mword 21) T12 (K - 68)%nat true
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htuvm; vm_compute; reflexivity)
              with "Hcg Hpc Hi1ce").
    iIntros (CID15 Hs15) "Hcg Hpc". iEval (rewrite Htuvm) in "Hpc".
    pose (Z0 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXC + 0x1ce) : mword 64) 4)]> T12).
    assert (HZ0ra : Z0 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXC + 0x1ce) : mword 64) 4)
      by (rewrite /Z0; apply upd_eq).
    assert (HZ0a0 : Z0 !!! Regidx Ra0 = page_base P.(ud_root))
      by (rewrite /Z0 upd_ne; [exact HT12a0 | nz]).
    assert (HZ0a1 : Z0 !!! Regidx Ra1 = pgroundup szv)
      by (rewrite /Z0 upd_ne; [exact HT12a1 | nz]).
    assert (HZ0a2 : Z0 !!! Regidx Ra2
                    = add_vec (mword_of_int 8192 : mword 64) (pgroundup szv))
      by (rewrite /Z0 upd_ne; [exact HT12a2 | nz]).
    assert (HZ0a3 : Z0 !!! Regidx Ra3 = (mword_of_int 4 : mword 64))
      by (rewrite /Z0 upd_ne; [exact HT12a3 | nz]).
    assert (HZ0sp : Z0 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /Z0 upd_ne; [exact HT12sp | nz]).
    assert (HZ0s3 : Z0 !!! Regidx Rs3 = pgroundup szv)
      by (rewrite /Z0 upd_ne; [exact HT12s3 | nz]).
    assert (HZ0s10 : Z0 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /Z0 upd_ne; [exact HT12s10 | nz]).
    assert (HZ0s6 : Z0 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /Z0 upd_ne; [exact HT12s6 | nz]).
    (* ---- the tp pin uvmalloc's contract asks for (ProofGrowproc.v's
       recipe): must come AFTER the [jal], since [cid_word] is hart-indexed
       and a pin set up before the crossing names the wrong hart. ---- *)
    pose (Y := tp_pin Z0).
    assert (HYid : tp_pin Y = tp_pin Z0)
      by (rewrite /Y; apply (tp_pin_id (tp_pin Z0) (rget_tp Z0))).
    assert (HYsp0 : Y !!! Regidx csp_rs1 = Z0 !!! Regidx csp_rs1)
      by (rewrite /Y; exact (tp_pin_sp Z0)).
    assert (Hgpreq : sie_cap_gpr Z0 (K - 68)%nat true (proc_addr jp)
                     = sie_cap_gpr Y (K - 68)%nat true (proc_addr jp))
      by (unfold sie_cap_gpr, sie_cap; rewrite HYsp0 HYid; reflexivity).
    iEval (rewrite Hgpreq) in "Hcg".
    assert (HYne : forall r : mword 5, r <> Rtp -> Y !!! Regidx r = Z0 !!! Regidx r).
    { intros r Hr. rewrite /Y. apply (rget_ne Z0 r).
      intro He. injection He as He2. congruence. }
    assert (HYtp : Y !!! Regidx Rtp = cid_word) by (rewrite /Y upd_eq; reflexivity).
    assert (HYra : Y !!! Regidx Rra
                   = add_vec_int (mword_of_int (KXC + 0x1ce) : mword 64) 4)
      by (rewrite (HYne Rra ltac:(nz)); exact HZ0ra).
    assert (HYa0 : Y !!! Regidx Ra0 = page_base P.(ud_root))
      by (rewrite (HYne Ra0 ltac:(nz)); exact HZ0a0).
    assert (HYa1 : Y !!! Regidx Ra1 = pgroundup szv)
      by (rewrite (HYne Ra1 ltac:(nz)); exact HZ0a1).
    assert (HYa2 : Y !!! Regidx Ra2
                   = add_vec (mword_of_int 8192 : mword 64) (pgroundup szv))
      by (rewrite (HYne Ra2 ltac:(nz)); exact HZ0a2).
    assert (HYa3 : Y !!! Regidx Ra3 = (mword_of_int 4 : mword 64))
      by (rewrite (HYne Ra3 ltac:(nz)); exact HZ0a3).
    assert (HYs3 : Y !!! Regidx Rs3 = pgroundup szv)
      by (rewrite (HYne Rs3 ltac:(nz)); exact HZ0s3).
    assert (HYs10 : Y !!! Regidx Rs10 = pv_sz V)
      by (rewrite (HYne Rs10 ltac:(nz)); exact HZ0s10).
    assert (HYs6 : Y !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite (HYne Rs6 ltac:(nz)); exact HZ0s6).
    assert (HYsp : Y !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite HYsp0 HZ0sp; reflexivity).
    iDestruct (cpu_own_transport CID1 CID15 0%nat true (proc_addr jp) C true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    (* ---- the two premises uvmalloc's freshness/size clauses need,        *)
    (* carried straight from [kxc_at_1ae]'s own [um_below]/[um_covered szv] *)
    (* via PGROUNDUP-only-grows-coverage: [pgroundup szv >= szv]. ---- *)
    iDestruct (proc_pt_wf_get with "Hpt") as %HPwf.
    assert (Hmaxszv : (bv_unsigned szv <= uvm_maxsz)%Z)
      by (apply (proc_pt_covered_maxsz P szv HPwf Hcov)).
    assert (Hpground_ge : (bv_unsigned szv <= bv_unsigned (pgroundup szv))%Z).
    { destruct (pgroundup_maxsz szv Hmaxszv) as [[Hge _] _]. exact Hge. }
    assert (Hmaxpground : (bv_unsigned (pgroundup szv) <= uvm_maxsz)%Z).
    { destruct (pgroundup_maxsz szv Hmaxszv) as [[_ Hle] _]. exact Hle. }
    assert (Hcov_pground : um_covered (pgroundup szv) P.(ud_um))
      by (apply (um_covered_pground szv P.(ud_um) Hmaxszv Hcov)).
    assert (Hbelow_pground : um_below (pgroundup szv) P.(ud_um))
      by (apply (um_below_mono szv (pgroundup szv) P.(ud_um) Hpground_ge Hbelow)).
    iApply (Uvmalloc.wp_uvmalloc_sconf ga Y P 4 (K - 68)%nat true
              (proc_addr jp) C true ltac:(lia) HYtp HYa0 HYa3
              ltac:(lia) uvm_perm_ok_22
              ltac:(rewrite HYa1 uint_unsigned; exact Hmaxpground)
              ltac:(right; rewrite HYa1; exact Hcov_pground)
              ltac:(rewrite HYa1 HYa2; intros i Hi Hbnd;
                    apply (um_below_run_fresh (pgroundup szv) P.(ud_um)
                             (S i) i Hbelow_pground Hmaxpground
                             ltac:(rewrite Nat2Z.inj_succ; lia)
                             ltac:(lia))
                    )
              with "Hcg Hcnt Htext Hpc Hpt Hka").

    iIntros (CID16 Hs16 Mu) "Hcg Hcnt Hpc %Hcsu Hpost".
    assert (Hpc1d2 : ret_pc (Y !!! Regidx Rra) = mword_of_int (KXC + 0x1d2))
      by (rewrite HYra; pcw).
    iEval (rewrite Hpc1d2) in "Hpc".
    assert (HMusp : Mu !!! Regidx csp_rs1 = pa_stk sp0 68).
    { rewrite (callee_saved_lookup Hcsu csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HYsp. }
    assert (HMus3 : Mu !!! Regidx Rs3 = pgroundup szv).
    { rewrite (callee_saved_lookup Hcsu Rs3 ltac:(vm_compute; reflexivity)).
      exact HYs3. }
    assert (HMus6 : Mu !!! Regidx Rs6 = page_base P.(ud_root)).
    { rewrite (callee_saved_lookup Hcsu Rs6 ltac:(vm_compute; reflexivity)).
      exact HYs6. }
    iDestruct "Hpost" as "[(%HMua0 & Hptback) | Hsucc]".
    - (* ==================== FAILURE: uvmalloc returned 0 ==================== *)
      (* ---- +0x1d2: c.mv s4,a0 (dead on this arm -- overwritten below by  *)
      (* the tail's own reload -- but the instruction still executes.) ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KXC + 0x1d2)) Rs4 Ra0
                Mu (K - 68)%nat true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi1d2").
      iIntros (CID17 Hs17) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (U0 := <[Regidx Rs4 := regval_into_reg
                    (add_vec zero_reg (Mu !!! Regidx Ra0))]> Mu).
      assert (HU0a0 : U0 !!! Regidx Ra0 = (mword_of_int 0 : mword 64))
        by (rewrite /U0 upd_ne; [exact HMua0 | nz]).
      assert (HU0sp : U0 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /U0 upd_ne; [exact HMusp | nz]).
      assert (HU0s3 : U0 !!! Regidx Rs3 = pgroundup szv)
        by (rewrite /U0 upd_ne; [exact HMus3 | nz]).
      assert (HU0s6 : U0 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /U0 upd_ne; [exact HMus6 | nz]).
      assert (Hpp1d4 : add_vec_int (mword_of_int (KXC + 0x1d2) : mword 64) 2
                       = mword_of_int (KXC + 0x1d4)) by pcw.
      iEval (rewrite Hpp1d4) in "Hpc".
      (* ---- +0x1d4: c.bnez a0,+0x1f4 -- FALLS THROUGH (a0 = 0) ---- *)
      assert (Hcreg : creg2reg_idx (Cregidx (mword_of_int 2)) = Regidx Ra0)
        by (vm_compute; reflexivity).
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (KXC + 0x1d4))
                (mword_of_int 16 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                U0 (K - 68)%nat true Hcreg ltac:(nz)
                ltac:(rewrite (rget_ne U0 Ra0 ltac:(nz)) HU0a0;
                      vm_compute; reflexivity)
                with "Hcg Hpc Hi1d4").
      iIntros (CID18 Hs18) "Hcg Hpc".
      assert (Hpp1d6 : add_vec_int (mword_of_int (KXC + 0x1d4) : mword 64) 2
                       = mword_of_int (KXC + 0x1d6)) by pcw.
      iEval (rewrite Hpp1d6) in "Hpc".
      (* ---- reassemble [kxc_frame_at] for [kxc_bad_1d6] -- the ELF NAMING *)
      (* is lost here, which is fine: the process is being torn down. ---- *)
      iDestruct "Hf65" as (w65_) "Hf65".
      iDestruct "Hf68" as (w68_) "Hf68".
      iDestruct (kxc_stack_of_top5 sp0 av w65_ pv w67 w68_
                   with "Hf64 Hf65 Hf66 Hf67 Hf68") as "Htop5".
      iDestruct (kxc_elf_give sp0 ef Hal with "Helf") as "Aelf".
      iDestruct (kxc_mid_join sp0 with "Hust Aelf Hph") as "Amid50".
      iAssert (stack_own (pa_stk sp0 13) 55) with "[Amid50 Htop5]" as "Hframe55".
      { change 55%nat with (50 + 5)%nat.
        rewrite stack_own_app (pa_stk_assoc sp0 13 50).
        iSplitL "Amid50"; [iExact "Amid50" | iExact "Htop5"]. }
      iEval (rewrite -Hmw5) in "Hf5". iEval (rewrite -Hmw6) in "Hf6".
      iEval (rewrite -Hmw7) in "Hf7". iEval (rewrite -Hmw8) in "Hf8".
      iEval (rewrite -Hmw9) in "Hf9". iEval (rewrite -Hmw10) in "Hf10".
      iEval (rewrite -Hmw11) in "Hf11". iEval (rewrite -Hmw12) in "Hf12".
      iEval (rewrite -Hmw13) in "Hf13".
      iAssert (kxc_frame_at sp0 ra0 s00 s10 s20
                 (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                 (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                 (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11))
        with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10 Hf11 Hf12 Hf13 Hframe55]"
        as "Hframeat".
      { rewrite /kxc_frame_at.
        iSplitL "Hf1"; [iExact "Hf1" |]. iSplitL "Hf2"; [iExact "Hf2" |].
        iSplitL "Hf3"; [iExact "Hf3" |]. iSplitL "Hf4"; [iExact "Hf4" |].
        iSplitL "Hf5"; [iExact "Hf5" |]. iSplitL "Hf6"; [iExact "Hf6" |].
        iSplitL "Hf7"; [iExact "Hf7" |]. iSplitL "Hf8"; [iExact "Hf8" |].
        iSplitL "Hf9"; [iExact "Hf9" |]. iSplitL "Hf10"; [iExact "Hf10" |].
        iSplitL "Hf11"; [iExact "Hf11" |]. iSplitL "Hf12"; [iExact "Hf12" |].
        iSplitL "Hf13"; [iExact "Hf13" | iExact "Hframe55"]. }
      (* ---- [Hcnt] has sat at [CID16] (uvmalloc's own return) since;      *)
      (* [Hcont] is still anchored at THIS lemma's own [CID0] -- both must   *)
      (* be re-anchored at the hart we are actually at before handing        *)
      (* either into [kxc_bad_1d6] (durable-notes' "CHAINING TWO HALVES"). ---- *)
      iDestruct (cpu_own_transport CID16 CID18 0%nat true (proc_addr jp) C true
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      assert (Hcr18 : true = false \/ proc_addr jp = zero_reg ->
                       (CID18 : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_retarget CID0 CID18 true (proc_addr jp) _ Hcr18
                   with "Hcont") as "Hcont".
      iApply (TC.kxc_bad_1d6 jp ga gf bn gfs cov logstart bmapstart inodestart
                size used used2 plen pfun na avf alen aslen afun pidv V
                dqb dqs dqa m U0 K C sp0 ra0 s00 s10 s20 pv av P (pgroundup szv)
                ltac:(unfold K_kexec; lia) Hu2
                Hmsp Hmra Hms0 Hms1 Hms2 HU0sp HU0s3 HU0s6
                Hbelow_pground Hcov_pground
                with "Hcg Hcnt Htext Hpc Hptback Hka Hbm Hins Hbits Hpriv
                      Hpath Hargv Hargs Hbs Hirs Hframeat Hcont").
    - (* ==================== SUCCESS: uvmalloc returned newsz ==================== *)
      iDestruct "Hsucc" as (P') "(%Hext & %Hdomeq & %Hleaf & %HMua0c & Hptnew)".
      (* ---- newsz = PGROUNDUP(szv) + 8192 never wraps and always exceeds  *)
      (* oldsz, which both resolves [HMua0c]'s disjunction (ruling out the  *)
      (* "shrink" arm) and gives the [a0 <> 0] the branch test needs. ---- *)
      assert (Hnewsz_unsigned : bv_unsigned (Y !!! Regidx Ra2)
                                = (8192 + bv_unsigned (pgroundup szv))%Z).
      { rewrite HYa2 add_vec_unsigned.
        assert (H8192 : bv_unsigned (mword_of_int 8192 : mword 64) = 8192%Z)
          by (vm_compute; reflexivity).
        rewrite H8192. change (MachineWord.MachineWord.Z_idx 64) with 64%N.
        apply bvw64_small.
        pose proof (bv_unsigned_in_range _ (pgroundup szv)) as [Hlo _].
        rewrite uvm_maxsz_lit in Hmaxpground.
        assert (Hupper : (8192 + bv_unsigned (pgroundup szv) < 18446744073709551616)%Z)
          by lia.
        assert (Hlower : (0 <= 8192 + bv_unsigned (pgroundup szv))%Z) by lia.
        change (2 ^ 64)%Z with 18446744073709551616%Z.
        exact (conj Hlower Hupper). }
      assert (HMua0eq : Mu !!! Regidx Ra0 = Y !!! Regidx Ra2).
      { destruct HMua0c as [[Hlt Heq] | [Hle Heq]].
        - exfalso. rewrite !uint_unsigned HYa1 Hnewsz_unsigned in Hlt. lia.
        - exact Heq. }
      pose (sz1 := Mu !!! Regidx Ra0).
      assert (HMua0ne : sz1 <> (mword_of_int 0 : mword 64)).
      { intro Habs. rewrite /sz1 HMua0eq in Habs.
        assert (Hz0 : bv_unsigned (mword_of_int 0 : mword 64) = 0%Z)
          by (vm_compute; reflexivity).
        apply (f_equal bv_unsigned) in Habs. rewrite Hnewsz_unsigned Hz0 in Habs.
        pose proof (bv_unsigned_in_range _ (pgroundup szv)) as [Hlo _]. lia. }
      (* ---- the invariant step, both uvmalloc arms folded into one by
         [ProofKexecSeam.kxc_grow_inv] -- kexec's own instance of exactly
         what phase B's phdr loop already needed for this same call. ---- *)
      iDestruct (proc_pt_wf_get with "Hptnew") as %HPwf'.
      assert (Hdomeq' : dom (ud_um P') = dom (ud_um P) ∪
                          vpn_run (svpn_of (pgroundup (pgroundup szv)))
                            (uvma_np (pgroundup szv) (Y !!! Regidx Ra2))).
      { rewrite -HYa1. exact Hdomeq. }
      assert (Harm' : ((bv_unsigned (Y !!! Regidx Ra2) < bv_unsigned (pgroundup szv))%Z
                        /\ sz1 = pgroundup szv)
                       \/ ((bv_unsigned (pgroundup szv) <= bv_unsigned (Y !!! Regidx Ra2))%Z
                           /\ sz1 = Y !!! Regidx Ra2)).
      { right. split; [lia | rewrite /sz1; exact HMua0eq]. }
      assert (Hinv' : um_below sz1 P'.(ud_um) /\ um_covered sz1 P'.(ud_um)).
      { apply (kxc_grow_inv P P' (pgroundup szv) (Y !!! Regidx Ra2) sz1
                 HPwf HPwf' Hbelow_pground Hcov_pground Hext Hdomeq' Harm'). }
      destruct Hinv' as [Hbelow' Hcov'].
      destruct Hext as (Hroot' & Htfp' & _).
      (* ---- +0x1d2: c.mv s4,a0 (s4 = sz1) ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KXC + 0x1d2)) Rs4 Ra0
                Mu (K - 68)%nat true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi1d2").
      iIntros (CID17 Hs17) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (U0 := <[Regidx Rs4 := regval_into_reg (add_vec zero_reg sz1)]> Mu).
      assert (HU0s4 : U0 !!! Regidx Rs4 = sz1).
      { rewrite /U0 upd_eq. apply add_vec_zero_l. }
      assert (HU0a0 : U0 !!! Regidx Ra0 = sz1)
        by (rewrite /U0 upd_ne; [rewrite /sz1; reflexivity | nz]).
      assert (HU0sp : U0 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /U0 upd_ne; [exact HMusp | nz]).
      assert (HU0s6 : U0 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /U0 upd_ne; [exact HMus6 | nz]).
      assert (Hpp1d4 : add_vec_int (mword_of_int (KXC + 0x1d2) : mword 64) 2
                       = mword_of_int (KXC + 0x1d4)) by pcw.
      iEval (rewrite Hpp1d4) in "Hpc".
      (* ---- +0x1d4: c.bnez a0,+0x1f4 -- TAKEN (a0 = sz1 <> 0) ---- *)
      assert (Hcreg : creg2reg_idx (Cregidx (mword_of_int 2)) = Regidx Ra0)
        by (vm_compute; reflexivity).
      assert (Htgt1f4 : add_vec (mword_of_int (KXC + 0x1d4) : mword 64)
                (sign_extend' 64 (sign_extend' 13
                   (concat_vec (mword_of_int 16 : mword 8) ('b"0"))))
              = mword_of_int (KXC + 0x1f4)) by pcw.
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (KXC + 0x1d4))
                (mword_of_int 16 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                U0 (K - 68)%nat true Hcreg ltac:(nz)
                ltac:(rewrite (rget_ne U0 Ra0 ltac:(nz)) HU0a0;
                      apply neq_vec64_true; rewrite zero_reg64; exact HMua0ne)
                ltac:(rewrite Htgt1f4; vm_compute; reflexivity)
                with "Hcg Hpc Hi1d4").
      iIntros (CID18 Hs18). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt1f4) in "Hpc".
      (* ---- the leaf fact [uvmclear] needs, off uvmalloc's own postcond:  *)
      (* the guard page IS the run's first page ([vpn_at vpn0 0 = vpn0]). ---- *)
      assert (Hpground_mod : bv_unsigned (pgroundup szv) mod 4096 = 0)
        by (destruct (pgroundup_maxsz szv Hmaxszv) as [_ Hmod]; exact Hmod).
      assert (Hpground_idem : pgroundup (pgroundup szv) = pgroundup szv).
      { apply pgroundup_id; [exact Hpground_mod |].
        pose proof (bv_unsigned_in_range _ (pgroundup szv)) as [Hlo _].
        rewrite uvm_maxsz_lit in Hmaxpground.
        change (2 ^ 64)%Z with 18446744073709551616%Z.
        lia. }
      assert (Hn2 : uvma_np (pgroundup szv) (Y !!! Regidx Ra2) = 2%nat).
      { unfold uvma_np. rewrite Hpground_idem Hnewsz_unsigned.
        replace (8192 + bv_unsigned (pgroundup szv) - bv_unsigned (pgroundup szv)
                 + 4095)%Z with 12287%Z by lia.
        vm_compute. reflexivity. }
      assert (Hvpn0mem : svpn_of (pgroundup szv)
                          ∈ vpn_run (svpn_of (pgroundup szv))
                              (uvma_np (pgroundup szv) (Y !!! Regidx Ra2))).
      { apply elem_of_vpn_run. exists 0%nat. rewrite Hn2. split; [lia |].
        unfold vpn_at. symmetry. apply avi_0_gen. }
      rewrite HYa1 HYa2 Hpground_idem in Hleaf.
      destruct (Hleaf (svpn_of (pgroundup szv)) Hvpn0mem) as [rleaf Hleafeq].
      assert (Hpermok : uvm_perm_ok
                (Z.land (pte_flags10 (uvm_pte (Z.lor 4 18) rleaf)) 1007)).
      { rewrite (uvm_pte_flags (Z.lor 4 18) rleaf
                   ltac:(change (Z.lor 4 18)%Z with 22%Z; lia)).
        assert (Hz : Z.land (Z.lor (Z.lor 4 18) 1) 1007 = 7%Z) by (vm_compute; reflexivity).
        rewrite Hz. exact uvm_perm_ok_7. }
      (* ---- +0x1f4: c.lui a1,-2 ; +0x1f6: c.add a1,a1,a0 (a1 = sz1 - 8192) ---- *)
      iApply (wp_clui_s_sconf (mword_of_int (KXC + 0x1f4)) Ra1
                (sign_extend' 20 (mword_of_int 62 : mword 6))
                (mword_of_int (-8192) : mword 64) U0 (K - 68)%nat true
                ltac:(nz) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi1f4").
      iIntros (CID19 Hs19) "Hcg Hpc".
      pose (U1 := <[Regidx Ra1 := regval_into_reg (mword_of_int (-8192) : mword 64)]> U0).
      assert (HU1a1 : U1 !!! Regidx Ra1 = (mword_of_int (-8192) : mword 64))
        by (rewrite /U1; apply upd_eq).
      assert (HU1a0 : U1 !!! Regidx Ra0 = sz1)
        by (rewrite /U1 upd_ne; [exact HU0a0 | nz]).
      assert (HU1s4 : U1 !!! Regidx Rs4 = sz1)
        by (rewrite /U1 upd_ne; [exact HU0s4 | nz]).
      assert (HU1sp : U1 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /U1 upd_ne; [exact HU0sp | nz]).
      assert (HU1s6 : U1 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /U1 upd_ne; [exact HU0s6 | nz]).
      assert (Hpp1f6 : add_vec_int (mword_of_int (KXC + 0x1f4) : mword 64) 2
                       = mword_of_int (KXC + 0x1f6)) by pcw.
      iEval (rewrite Hpp1f6) in "Hpc".
      iApply (wp_cadd_s_sconf (mword_of_int (KXC + 0x1f6)) Ra1 Ra0
                U1 (K - 68)%nat true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi1f6").
      iIntros (CID20 Hs20) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (U2 := <[Regidx Ra1 := regval_into_reg
                    (add_vec (U1 !!! Regidx Ra1) (U1 !!! Regidx Ra0))]> U1).
      assert (HU2a1 : U2 !!! Regidx Ra1
                      = add_vec (mword_of_int (-8192) : mword 64) sz1).
      { rewrite /U2 upd_eq HU1a1 HU1a0. reflexivity. }
      assert (Hszu : bv_unsigned sz1 = (8192 + bv_unsigned (pgroundup szv))%Z).
      { rewrite /sz1 HMua0eq. exact Hnewsz_unsigned. }
      assert (HU2eq : U2 !!! Regidx Ra1 = pgroundup szv).
      { rewrite HU2a1 add_neg8192_eq_sub. apply bv_eq.
        rewrite sub_vec_unsigned Hszu.
        assert (H8192 : bv_unsigned (mword_of_int 8192 : mword 64) = 8192%Z)
          by (vm_compute; reflexivity).
        rewrite H8192.
        replace (8192 + bv_unsigned (pgroundup szv) - 8192)%Z
          with (bv_unsigned (pgroundup szv)) by lia.
        unfold bv_wrap. change (MachineWord.MachineWord.Z_idx 64) with 64%N.
        apply Z.mod_small.
        pose proof (bv_unsigned_in_range _ (pgroundup szv)) as [Hlo _].
        rewrite uvm_maxsz_lit in Hmaxpground.
        assert (Hup : (bv_unsigned (pgroundup szv) < 18446744073709551616)%Z) by lia.
        assert (Hdn : (0 <= bv_unsigned (pgroundup szv))%Z) by lia.
        change (bv_modulus 64%N) with 18446744073709551616%Z.
        exact (conj Hdn Hup). }
      assert (HU2a0 : U2 !!! Regidx Ra0 = sz1)
        by (rewrite /U2 upd_ne; [exact HU1a0 | nz]).
      assert (HU2s4 : U2 !!! Regidx Rs4 = sz1)
        by (rewrite /U2 upd_ne; [exact HU1s4 | nz]).
      assert (HU2sp : U2 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /U2 upd_ne; [exact HU1sp | nz]).
      assert (HU2s6 : U2 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /U2 upd_ne; [exact HU1s6 | nz]).
      assert (Hpp1f8 : add_vec_int (mword_of_int (KXC + 0x1f6) : mword 64) 2
                       = mword_of_int (KXC + 0x1f8)) by pcw.
      iEval (rewrite Hpp1f8) in "Hpc".
      (* ---- +0x1f8: c.mv a0,s6 (a0 = root arg) ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KXC + 0x1f8)) Ra0 Rs6
                U2 (K - 68)%nat true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi1f8").
      iIntros (CID21 Hs21) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (U3 := <[Regidx Ra0 := regval_into_reg
                    (add_vec zero_reg (U2 !!! Regidx Rs6))]> U2).
      assert (HU3a0 : U3 !!! Regidx Ra0 = page_base P.(ud_root)).
      { rewrite /U3 upd_eq HU2s6. apply add_vec_zero_l. }
      assert (HU3a1 : U3 !!! Regidx Ra1 = pgroundup szv)
        by (rewrite /U3 upd_ne; [exact HU2eq | nz]).
      assert (HU3s4 : U3 !!! Regidx Rs4 = sz1)
        by (rewrite /U3 upd_ne; [exact HU2s4 | nz]).
      assert (HU3sp : U3 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /U3 upd_ne; [exact HU2sp | nz]).
      assert (Hpp1fa : add_vec_int (mword_of_int (KXC + 0x1f8) : mword 64) 2
                       = mword_of_int (KXC + 0x1fa)) by pcw.
      iEval (rewrite Hpp1fa) in "Hpc".
      (* ---- +0x1fa: jal ra,uvmclear ---- *)
      assert (Htuvc : add_vec (mword_of_int (KXC + 0x1fa) : mword 64)
                        (sign_extend' 64 (mword_of_int 2083584 : mword 21))
                      = mword_of_int KernelSyms.uvmclear) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (KXC + 0x1fa)) Rra
                (mword_of_int 2083584 : mword 21) U3 (K - 68)%nat true
                ltac:(nz) ltac:(rdok)
                ltac:(rewrite Htuvc; vm_compute; reflexivity)
                with "Hcg Hpc Hi1fa").
      iIntros (CID22 Hs22) "Hcg Hpc". iEval (rewrite Htuvc) in "Hpc".
      pose (Z1 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KXC + 0x1fa) : mword 64) 4)]> U3).
      assert (HZ1ra : Z1 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KXC + 0x1fa) : mword 64) 4)
        by (rewrite /Z1; apply upd_eq).
      assert (HZ1a0 : Z1 !!! Regidx Ra0 = page_base P.(ud_root))
        by (rewrite /Z1 upd_ne; [exact HU3a0 | nz]).
      assert (HZ1a1 : Z1 !!! Regidx Ra1 = pgroundup szv)
        by (rewrite /Z1 upd_ne; [exact HU3a1 | nz]).
      assert (HZ1s4 : Z1 !!! Regidx Rs4 = sz1)
        by (rewrite /Z1 upd_ne; [exact HU3s4 | nz]).
      assert (HZ1sp : Z1 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /Z1 upd_ne; [exact HU3sp | nz]).
      iDestruct (cpu_own_transport CID16 CID22 0%nat true (proc_addr jp) C true
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply (Uvmclear.wp_uvmclear_sconf Z1 P' (uvm_pte (Z.lor 4 18) rleaf)
                (K - 68)%nat true (proc_addr jp)
                ltac:(lia) ltac:(rewrite Hroot'; exact HZ1a0)
                ltac:(rewrite HZ1a1 uint_unsigned; rewrite uvm_maxsz_lit in Hmaxpground;
                      change (2 ^ 38)%Z with 274877906944%Z;
                      assert (Hb38 : (bv_unsigned (pgroundup szv) < 274877906944)%Z)
                        by lia;
                      exact Hb38)
                ltac:(rewrite HZ1a1; exact Hleafeq) Hpermok
                with "Hcg Htext Hpc Hptnew").
      iIntros (CID23 Hs23 Z2) "Hcg Hpc %Hcsz2 Hptcl".
      assert (Hpc1fe : ret_pc (Z1 !!! Regidx Rra) = mword_of_int (KXC + 0x1fe))
        by (rewrite HZ1ra; pcw).
      iEval (rewrite Hpc1fe) in "Hpc".
      assert (HZ2sp : Z2 !!! Regidx csp_rs1 = pa_stk sp0 68).
      { rewrite (callee_saved_lookup Hcsz2 csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HZ1sp. }
      assert (HZ2s4 : Z2 !!! Regidx Rs4 = sz1).
      { rewrite (callee_saved_lookup Hcsz2 Rs4 ltac:(vm_compute; reflexivity)).
        exact HZ1s4. }
      assert (HZ2s0 : Z2 !!! Regidx Rs0 = sp0).
      { rewrite (callee_saved_lookup Hcsz2 Rs0 ltac:(vm_compute; reflexivity)).
        rewrite /Z1 upd_ne; [| nz].
        rewrite /U3 upd_ne; [| nz]. rewrite /U2 upd_ne; [| nz].
        rewrite /U1 upd_ne; [| nz]. rewrite /U0 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcsu Rs0 ltac:(vm_compute; reflexivity)).
        rewrite (HYne Rs0 ltac:(nz)).
        rewrite /Z0 upd_ne; [| nz].
        rewrite /T12 upd_ne; [| nz]. rewrite /T11 upd_ne; [| nz].
        rewrite /T10 upd_ne; [| nz]. rewrite /T9 upd_ne; [| nz].
        rewrite /T8 upd_ne; [| nz]. rewrite /T7 upd_ne; [| nz].
        rewrite /T6 upd_ne; [| nz]. rewrite /T5 upd_ne; [| nz].
        rewrite /T4 upd_ne; [| nz]. rewrite /T3 upd_ne; [| nz].
        rewrite /T2 upd_ne; [| nz]. rewrite /T1 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcs1 Rs0 ltac:(vm_compute; reflexivity)).
        rewrite /T0 upd_ne; [| nz].
        exact HMs0. }
      assert (HZ2s5 : Z2 !!! Regidx Rs5 = proc_addr jp).
      { rewrite (callee_saved_lookup Hcsz2 Rs5 ltac:(vm_compute; reflexivity)).
        rewrite /Z1 upd_ne; [| nz].
        rewrite /U3 upd_ne; [| nz]. rewrite /U2 upd_ne; [| nz].
        rewrite /U1 upd_ne; [| nz]. rewrite /U0 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcsu Rs5 ltac:(vm_compute; reflexivity)).
        rewrite (HYne Rs5 ltac:(nz)).
        rewrite /Z0 upd_ne; [| nz].
        rewrite /T12 upd_ne; [| nz]. rewrite /T11 upd_ne; [| nz].
        rewrite /T10 upd_ne; [| nz]. rewrite /T9 upd_ne; [| nz].
        rewrite /T8 upd_ne; [| nz]. rewrite /T7 upd_ne; [| nz].
        rewrite /T6 upd_ne; [| nz]. rewrite /T5 upd_ne; [| nz].
        rewrite /T4 upd_ne; [| nz]. rewrite /T3 upd_ne; [| nz].
        rewrite /T2 upd_ne; [| nz].
        exact HT2s5. }
      assert (HZ2s6 : Z2 !!! Regidx Rs6 = page_base P.(ud_root)).
      { rewrite (callee_saved_lookup Hcsz2 Rs6 ltac:(vm_compute; reflexivity)).
        rewrite /Z1 upd_ne; [| nz]. rewrite /U3 upd_ne; [| nz].
        exact HU2s6. }
      assert (HZ2s10 : Z2 !!! Regidx Rs10 = pv_sz V).
      { rewrite (callee_saved_lookup Hcsz2 Rs10 ltac:(vm_compute; reflexivity)).
        rewrite /Z1 upd_ne; [| nz].
        rewrite /U3 upd_ne; [| nz]. rewrite /U2 upd_ne; [| nz].
        rewrite /U1 upd_ne; [| nz]. rewrite /U0 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcsu Rs10 ltac:(vm_compute; reflexivity)).
        rewrite (HYne Rs10 ltac:(nz)).
        exact HZ0s10. }
      (* ---- +0x1fe / +0x202: stackbase = sz1 - 4096 (two base ADDIs,      *)
      (* -2048 each -- neither fits [c.addi]'s 6-bit range). ---- *)
      iApply (wp_addi4_s_sconf (mword_of_int (KXC + 0x1fe)) Rs7 Rs4
                (mword_of_int 2048 : mword 12) Z2 (K - 68)%nat true
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1fe").
      iIntros (CID24 Hs24) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (W1 := <[Regidx Rs7 := regval_into_reg
                    (add_vec (Z2 !!! Regidx Rs4)
                       (sign_extend' 64 (mword_of_int 2048 : mword 12)))]> Z2).
      assert (HW1s7 : W1 !!! Regidx Rs7 = add_vec sz1 (mword_of_int (-2048) : mword 64)).
      { rewrite /W1 upd_eq HZ2s4. f_equal. }
      assert (HW1sp : W1 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /W1 upd_ne; [exact HZ2sp | nz]).
      assert (HW1s0 : W1 !!! Regidx Rs0 = sp0)
        by (rewrite /W1 upd_ne; [exact HZ2s0 | nz]).
      assert (HW1s4 : W1 !!! Regidx Rs4 = sz1)
        by (rewrite /W1 upd_ne; [exact HZ2s4 | nz]).
      assert (HW1s5 : W1 !!! Regidx Rs5 = proc_addr jp)
        by (rewrite /W1 upd_ne; [exact HZ2s5 | nz]).
      assert (HW1s6 : W1 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /W1 upd_ne; [exact HZ2s6 | nz]).
      assert (HW1s10 : W1 !!! Regidx Rs10 = pv_sz V)
        by (rewrite /W1 upd_ne; [exact HZ2s10 | nz]).
      assert (Hpp202 : add_vec_int (mword_of_int (KXC + 0x1fe) : mword 64) 4
                       = mword_of_int (KXC + 0x202)) by pcw.
      iEval (rewrite Hpp202) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (KXC + 0x202)) Rs7 Rs7
                (mword_of_int 2048 : mword 12) W1 (K - 68)%nat true
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi202").
      iIntros (CID25 Hs25) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (W2 := <[Regidx Rs7 := regval_into_reg
                    (add_vec (W1 !!! Regidx Rs7)
                       (sign_extend' 64 (mword_of_int 2048 : mword 12)))]> W1).
      assert (HW2s7 : W2 !!! Regidx Rs7 = add_vec sz1 (mword_of_int (-4096) : mword 64)).
      { (* [sz1] is SYMBOLIC (uvmalloc's returned size) -- never [vm_compute] a
           goal that still mentions it (optimization.md, "Conversion and Qed":
           a prior version of this step tried [apply bv_eq; vm_compute] here and
           it never terminated -- accelerating memory, no progress, killed past
           10 GB). Reduce the immediate to [mword_of_int] form first (a CLOSED
           fact, safe to compute), then combine both offsets via
           [kxc_addv_moi_moi] and strip the shared [sz1] head with [f_equal];
           only closed integer arithmetic is left, for [ring]. *)
        assert (Hse : sign_extend' 64 (mword_of_int 2048 : mword 12)
                    = (mword_of_int (-2048) : mword 64))
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite /W2 upd_eq HW1s7 Hse kxc_addv_moi_moi.
        f_equal. }
      assert (HW2sp : W2 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /W2 upd_ne; [exact HW1sp | nz]).
      assert (HW2s0 : W2 !!! Regidx Rs0 = sp0)
        by (rewrite /W2 upd_ne; [exact HW1s0 | nz]).
      assert (HW2s4 : W2 !!! Regidx Rs4 = sz1)
        by (rewrite /W2 upd_ne; [exact HW1s4 | nz]).
      assert (HW2s5 : W2 !!! Regidx Rs5 = proc_addr jp)
        by (rewrite /W2 upd_ne; [exact HW1s5 | nz]).
      assert (HW2s6 : W2 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /W2 upd_ne; [exact HW1s6 | nz]).
      assert (HW2s10 : W2 !!! Regidx Rs10 = pv_sz V)
        by (rewrite /W2 upd_ne; [exact HW1s10 | nz]).
      assert (Hpp206 : add_vec_int (mword_of_int (KXC + 0x202) : mword 64) 4
                       = mword_of_int (KXC + 0x206)) by pcw.
      iEval (rewrite Hpp206) in "Hpc".
      (* ---- +0x206: ld a5,-512(s0) -- the spilled [argv] pointer ---- *)
      assert (Hargvslotaddr : add_vec (W2 !!! Regidx Rs0)
                                 (sign_extend' 64 (mword_of_int 3584 : mword 12))
                               = pa_stk sp0 64).
      { rewrite HW2s0. apply kxc_argv_slot. }
      iEval (rewrite -Hargvslotaddr) in "Hf64".
      iApply (wp_ld_s_sconf (mword_of_int (KXC + 0x206)) Ra5 Rs0
                (mword_of_int 3584 : mword 12) W2 (K - 68)%nat av true
                (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi206 Hf64").
      iIntros (CID26 Hs26) "Hcg Hpc Hf64". iEval (rewrite Hargvslotaddr) in "Hf64".
      pose (W3 := <[Regidx Ra5 := regval_into_reg av]> W2).
      assert (HW3a5 : W3 !!! Regidx Ra5 = av) by (rewrite /W3; apply upd_eq).
      assert (HW3sp : W3 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /W3 upd_ne; [exact HW2sp | nz]).
      assert (HW3s0 : W3 !!! Regidx Rs0 = sp0)
        by (rewrite /W3 upd_ne; [exact HW2s0 | nz]).
      assert (HW3s4 : W3 !!! Regidx Rs4 = sz1)
        by (rewrite /W3 upd_ne; [exact HW2s4 | nz]).
      assert (HW3s5 : W3 !!! Regidx Rs5 = proc_addr jp)
        by (rewrite /W3 upd_ne; [exact HW2s5 | nz]).
      assert (HW3s6 : W3 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /W3 upd_ne; [exact HW2s6 | nz]).
      assert (HW3s7 : W3 !!! Regidx Rs7 = add_vec sz1 (mword_of_int (-4096) : mword 64))
        by (rewrite /W3 upd_ne; [exact HW2s7 | nz]).
      assert (HW3s10 : W3 !!! Regidx Rs10 = pv_sz V)
        by (rewrite /W3 upd_ne; [exact HW2s10 | nz]).
      assert (Hpp20a : add_vec_int (mword_of_int (KXC + 0x206) : mword 64) 4
                       = mword_of_int (KXC + 0x20a)) by pcw.
      iEval (rewrite Hpp20a) in "Hpc".
      (* ---- +0x20a: ld a0,0(a5) -- argv[0] ---- *)
      (* this file opens [Z_scope] (line 106) for its arithmetic [assert]s, so
         a bare numeral here defaults to [Z] -- fine where a concrete [nat]
         parameter pins the expected type, but [!!]'s key is a typeclass
         method with no such pin, so it needs [%nat] spelled out explicitly
         (confirmed by hand: without it, "Could not find an instance for
         [Lookup Z Z (list nat)]"). *)
      assert (Hl0 : seq 0%nat (S na) !! 0%nat = Some 0%nat)
        by (rewrite (lookup_seq_lt 0%nat (S na) 0%nat ltac:(lia)); reflexivity).
      iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat Hl0 with "Hargv") as "[Ha0 Hargvback]".
      (* [av] is a bare lemma parameter (not a [pose]d chain like [sz1]), but
         after the scare above, don't risk [vm_compute] on a goal that still
         mentions it either -- unfold [pa_add] to the SAME [add_vec av _]
         head as the LHS, then [f_equal] strips it, leaving a CLOSED equation
         over the two immediates only. *)
      assert (Ha0addr : add_vec (W3 !!! Regidx Ra5)
                          (sign_extend' 64 (mword_of_int 0 : mword 12))
                        = pa_add av (8 * 0)).
      { rewrite HW3a5. unfold pa_add, add_vec_int. f_equal. }
      iEval (rewrite -Ha0addr) in "Ha0".
      iApply (wp_cld_s_sconf (mword_of_int (KXC + 0x20a)) Ra0 Ra5
                (mword_of_int 0 : mword 12) W3 (K - 68)%nat (avf 0%nat) true
                (dqm := dqa) ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi20a Ha0").
      iIntros (CID27 Hs27) "Hcg Hpc Ha0". iEval (rewrite Ha0addr) in "Ha0".
      iDestruct ("Hargvback" with "Ha0") as "Hargv".
      pose (W4 := <[Regidx Ra0 := regval_into_reg (avf 0%nat)]> W3).
      assert (HW4a0 : W4 !!! Regidx Ra0 = avf 0%nat) by (rewrite /W4; apply upd_eq).
      assert (HW4sp : W4 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /W4 upd_ne; [exact HW3sp | nz]).
      assert (HW4s4 : W4 !!! Regidx Rs4 = sz1)
        by (rewrite /W4 upd_ne; [exact HW3s4 | nz]).
      assert (HW4s5 : W4 !!! Regidx Rs5 = proc_addr jp)
        by (rewrite /W4 upd_ne; [exact HW3s5 | nz]).
      assert (HW4s6 : W4 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /W4 upd_ne; [exact HW3s6 | nz]).
      assert (HW4s0 : W4 !!! Regidx Rs0 = sp0)
        by (rewrite /W4 upd_ne; [exact HW3s0 | nz]).
      assert (HW4s7 : W4 !!! Regidx Rs7 = add_vec sz1 (mword_of_int (-4096) : mword 64))
        by (rewrite /W4 upd_ne; [exact HW3s7 | nz]).
      assert (HW4s10 : W4 !!! Regidx Rs10 = pv_sz V)
        by (rewrite /W4 upd_ne; [exact HW3s10 | nz]).
      assert (Hpp20c : add_vec_int (mword_of_int (KXC + 0x20a) : mword 64) 2
                       = mword_of_int (KXC + 0x20c)) by pcw.
      iEval (rewrite Hpp20c) in "Hpc".
      (* ---- +0x20c: c.mv s2,s4 (s2 = sz1) ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KXC + 0x20c)) Rs2 Rs4
                W4 (K - 68)%nat true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi20c").
      iIntros (CID28 Hs28) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (W5 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (W4 !!! Regidx Rs4))]> W4).
      assert (HW5s2 : W5 !!! Regidx Rs2 = sz1).
      { rewrite /W5 upd_eq HW4s4. apply add_vec_zero_l. }
      assert (HW5a0 : W5 !!! Regidx Ra0 = avf 0%nat)
        by (rewrite /W5 upd_ne; [exact HW4a0 | nz]).
      assert (HW5sp : W5 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /W5 upd_ne; [exact HW4sp | nz]).
      assert (HW5s4 : W5 !!! Regidx Rs4 = sz1)
        by (rewrite /W5 upd_ne; [exact HW4s4 | nz]).
      assert (HW5s5 : W5 !!! Regidx Rs5 = proc_addr jp)
        by (rewrite /W5 upd_ne; [exact HW4s5 | nz]).
      assert (HW5s6 : W5 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /W5 upd_ne; [exact HW4s6 | nz]).
      assert (HW5s0 : W5 !!! Regidx Rs0 = sp0)
        by (rewrite /W5 upd_ne; [exact HW4s0 | nz]).
      assert (HW5s7 : W5 !!! Regidx Rs7 = add_vec sz1 (mword_of_int (-4096) : mword 64))
        by (rewrite /W5 upd_ne; [exact HW4s7 | nz]).
      assert (HW5s10 : W5 !!! Regidx Rs10 = pv_sz V)
        by (rewrite /W5 upd_ne; [exact HW4s10 | nz]).
      assert (Hpp20e : add_vec_int (mword_of_int (KXC + 0x20c) : mword 64) 2
                       = mword_of_int (KXC + 0x20e)) by pcw.
      iEval (rewrite Hpp20e) in "Hpc".
      (* ---- +0x20e: c.li s1,0 ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (KXC + 0x20e)) Rs1
                (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                W5 (K - 68)%nat true ltac:(nz) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi20e").
      iIntros (CID29 Hs29) "Hcg Hpc".
      pose (W6 := <[Regidx Rs1 := regval_into_reg (mword_of_int 0 : mword 64)]> W5).
      assert (HW6s1 : W6 !!! Regidx Rs1 = (mword_of_int 0 : mword 64))
        by (rewrite /W6; apply upd_eq).
      assert (HW6a0 : W6 !!! Regidx Ra0 = avf 0%nat)
        by (rewrite /W6 upd_ne; [exact HW5a0 | nz]).
      assert (HW6sp : W6 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /W6 upd_ne; [exact HW5sp | nz]).
      assert (HW6s2 : W6 !!! Regidx Rs2 = sz1)
        by (rewrite /W6 upd_ne; [exact HW5s2 | nz]).
      assert (HW6s4 : W6 !!! Regidx Rs4 = sz1)
        by (rewrite /W6 upd_ne; [exact HW5s4 | nz]).
      assert (HW6s5 : W6 !!! Regidx Rs5 = proc_addr jp)
        by (rewrite /W6 upd_ne; [exact HW5s5 | nz]).
      assert (HW6s6 : W6 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /W6 upd_ne; [exact HW5s6 | nz]).
      assert (HW6s0 : W6 !!! Regidx Rs0 = sp0)
        by (rewrite /W6 upd_ne; [exact HW5s0 | nz]).
      assert (HW6s7 : W6 !!! Regidx Rs7 = add_vec sz1 (mword_of_int (-4096) : mword 64))
        by (rewrite /W6 upd_ne; [exact HW5s7 | nz]).
      assert (HW6s10 : W6 !!! Regidx Rs10 = pv_sz V)
        by (rewrite /W6 upd_ne; [exact HW5s10 | nz]).
      assert (Hpp210 : add_vec_int (mword_of_int (KXC + 0x20e) : mword 64) 2
                       = mword_of_int (KXC + 0x210)) by pcw.
      iEval (rewrite Hpp210) in "Hpc".
      (* ---- +0x210: addi s9,s0,-368 (s9 = pa_stk sp0 46, the ustack base) ---- *)
      iApply (wp_addi4_s_sconf (mword_of_int (KXC + 0x210)) Rs9 Rs0
                (mword_of_int 3728 : mword 12) W6 (K - 68)%nat true
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi210").
      iIntros (CID30 Hs30) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (W7 := <[Regidx Rs9 := regval_into_reg
                    (add_vec (W6 !!! Regidx Rs0)
                       (sign_extend' 64 (mword_of_int 3728 : mword 12)))]> W6).
      assert (HW7s9 : W7 !!! Regidx Rs9 = pa_stk sp0 46).
      { rewrite /W7 upd_eq HW6s0. apply kxc_ustack_base. }
      assert (HW7a0 : W7 !!! Regidx Ra0 = avf 0%nat)
        by (rewrite /W7 upd_ne; [exact HW6a0 | nz]).
      assert (HW7sp : W7 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /W7 upd_ne; [exact HW6sp | nz]).
      assert (HW7s0 : W7 !!! Regidx Rs0 = sp0)
        by (rewrite /W7 upd_ne; [exact HW6s0 | nz]).
      assert (HW7s1 : W7 !!! Regidx Rs1 = (mword_of_int 0 : mword 64))
        by (rewrite /W7 upd_ne; [exact HW6s1 | nz]).
      assert (HW7s2 : W7 !!! Regidx Rs2 = sz1)
        by (rewrite /W7 upd_ne; [exact HW6s2 | nz]).
      assert (HW7s4 : W7 !!! Regidx Rs4 = sz1)
        by (rewrite /W7 upd_ne; [exact HW6s4 | nz]).
      assert (HW7s5 : W7 !!! Regidx Rs5 = proc_addr jp)
        by (rewrite /W7 upd_ne; [exact HW6s5 | nz]).
      assert (HW7s6 : W7 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /W7 upd_ne; [exact HW6s6 | nz]).
      assert (HW7s7 : W7 !!! Regidx Rs7 = add_vec sz1 (mword_of_int (-4096) : mword 64))
        by (rewrite /W7 upd_ne; [exact HW6s7 | nz]).
      assert (HW7s10 : W7 !!! Regidx Rs10 = pv_sz V)
        by (rewrite /W7 upd_ne; [exact HW6s10 | nz]).
      assert (Hpp214 : add_vec_int (mword_of_int (KXC + 0x210) : mword 64) 4
                       = mword_of_int (KXC + 0x214)) by pcw.
      iEval (rewrite Hpp214) in "Hpc".
      (* ---- +0x214: li s8,32 (MAXARG) -- NOT compressed: 32 overflows
         [c.li]'s signed 6-bit range (-32..31), so the compiler emitted the
         4-byte [addi s8,zero,32] instead (confirmed against kernel.asm:
         "02000c13 li s8,32", and [CodeKexec.kxc_214]'s own [instr _ false _]
         says the same). [wp_li4_s_sconf], not [wp_cli_s_sconf]. ---- *)
      iApply (wp_li4_s_sconf (mword_of_int (KXC + 0x214)) Rs8
                (mword_of_int 32 : mword 12) (mword_of_int 32 : mword 64)
                W7 (K - 68)%nat true ltac:(nz) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi214").
      iIntros (CID31 Hs31) "Hcg Hpc".
      pose (W8 := <[Regidx Rs8 := regval_into_reg (mword_of_int 32 : mword 64)]> W7).
      assert (HW8s8 : W8 !!! Regidx Rs8 = (mword_of_int 32 : mword 64))
        by (rewrite /W8; apply upd_eq).
      assert (HW8a0 : W8 !!! Regidx Ra0 = avf 0%nat)
        by (rewrite /W8 upd_ne; [exact HW7a0 | nz]).
      assert (HW8sp : W8 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /W8 upd_ne; [exact HW7sp | nz]).
      assert (HW8s0 : W8 !!! Regidx Rs0 = sp0)
        by (rewrite /W8 upd_ne; [exact HW7s0 | nz]).
      assert (HW8s1 : W8 !!! Regidx Rs1 = (mword_of_int 0 : mword 64))
        by (rewrite /W8 upd_ne; [exact HW7s1 | nz]).
      assert (HW8s2 : W8 !!! Regidx Rs2 = sz1)
        by (rewrite /W8 upd_ne; [exact HW7s2 | nz]).
      assert (HW8s4 : W8 !!! Regidx Rs4 = sz1)
        by (rewrite /W8 upd_ne; [exact HW7s4 | nz]).
      assert (HW8s5 : W8 !!! Regidx Rs5 = proc_addr jp)
        by (rewrite /W8 upd_ne; [exact HW7s5 | nz]).
      assert (HW8s6 : W8 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /W8 upd_ne; [exact HW7s6 | nz]).
      assert (HW8s7 : W8 !!! Regidx Rs7 = add_vec sz1 (mword_of_int (-4096) : mword 64))
        by (rewrite /W8 upd_ne; [exact HW7s7 | nz]).
      assert (HW8s9 : W8 !!! Regidx Rs9 = pa_stk sp0 46)
        by (rewrite /W8 upd_ne; [exact HW7s9 | nz]).
      assert (HW8s10 : W8 !!! Regidx Rs10 = pv_sz V)
        by (rewrite /W8 upd_ne; [exact HW7s10 | nz]).
      assert (Hpp218 : add_vec_int (mword_of_int (KXC + 0x214) : mword 64) 4
                       = mword_of_int (KXC + 0x218)) by pcw.
      iEval (rewrite Hpp218) in "Hpc".
      (* ---- the loop-invariant frame at c = 0: everything below slot 13
         is exactly what [kxc_at_1ae] handed in, untouched. ---- *)
      iAssert (kxc_frameC sp0 ra0 s00 s10 s20 pv av
                 w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 0%nat sz1 alen)
        with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10 Hf11 Hf12 Hf13
               Hust Hph Hf64 Hf65 Hf66 Hf67 Hf68]" as "Hframe0".
      { rewrite /kxc_frameC.
        iSplitL "Hf1"; [iExact "Hf1" |]. iSplitL "Hf2"; [iExact "Hf2" |].
        iSplitL "Hf3"; [iExact "Hf3" |]. iSplitL "Hf4"; [iExact "Hf4" |].
        iSplitL "Hf5"; [iExact "Hf5" |]. iSplitL "Hf6"; [iExact "Hf6" |].
        iSplitL "Hf7"; [iExact "Hf7" |]. iSplitL "Hf8"; [iExact "Hf8" |].
        iSplitL "Hf9"; [iExact "Hf9" |]. iSplitL "Hf10"; [iExact "Hf10" |].
        iSplitL "Hf11"; [iExact "Hf11" |]. iSplitL "Hf12"; [iExact "Hf12" |].
        iSplitL "Hf13"; [iExact "Hf13" |].
        iSplitL "Hust"; [rewrite Nat.sub_0_r; iExact "Hust" |].
        iSplitR; [done |].
        iSplitL "Hph"; [iExact "Hph" |].
        iSplitL "Hf64"; [rewrite Nat.mul_0_r pa_add_0; iExact "Hf64" |].
        iSplitL "Hf65"; [iExact "Hf65" |]. iSplitL "Hf66"; [iExact "Hf66" |].
        iSplitL "Hf67"; [iExact "Hf67" | iExact "Hf68"]. }
      assert (Hcreg8 : creg2reg_idx (Cregidx (mword_of_int 2)) = Regidx Ra0)
        by (vm_compute; reflexivity).
      (* [kxc_at_21a]/[kxc_at_272] state slot 7 as [mword_of_int (uint sz1 -
         4096)], not [add_vec sz1 (mword_of_int (-4096))] like [HW8s7] -- same
         value, different spelling; [sz1] is symbolic so bridge it via
         [bv_eq]/[add_vec_unsigned], never [vm_compute]. *)
      assert (Hs7eq : add_vec sz1 (mword_of_int (-4096) : mword 64)
                    = mword_of_int (uint sz1 - 4096))
        by (apply bv_eq; rewrite add_vec_unsigned moi64_unsigned uint_unsigned
              bv_wrap_add_idemp_r; f_equal; ring).
      (* the loop invariant's own [P] has to be the table AFTER [uvmclear]
         too ([Hptcl], not [P'] alone) -- [uptd_set] only ever touches
         [ud_um], so [ud_root]/[ud_tfp] pass through by construction, and
         [um_below]/[um_covered] survive because the ONE page it overwrites
         ([Hleafeq]'s leaf) was already below [sz1] per [Hbelow']. *)
      assert (Hvpn0eq : svpn_of (Z1 !!! Regidx (mword_of_int 11))
                       = svpn_of (pgroundup szv)) by (rewrite HZ1a1; reflexivity).
      assert (Hvpn0lt : (bv_unsigned (svpn_of (pgroundup szv)) * 4096
                          < bv_unsigned sz1)%Z) by (eapply Hbelow'; exact Hleafeq).
      pose (Pfinal := uptd_set P' (svpn_of (Z1 !!! Regidx (mword_of_int 11)))
                        (pte_clear_u (uvm_pte (Z.lor 4 18) rleaf))).
      assert (HbelowF : um_below sz1 Pfinal.(ud_um)).
      { rewrite /Pfinal /uptd_set /= Hvpn0eq.
        apply kxc_um_below_insert; [exact Hbelow' | exact Hvpn0lt]. }
      assert (HcovF : um_covered sz1 Pfinal.(ud_um)).
      { rewrite /Pfinal /uptd_set /= Hvpn0eq.
        apply kxc_um_covered_insert; exact Hcov'. }
      assert (HrootF : ud_root Pfinal = ud_root P') by (rewrite /Pfinal /uptd_set; reflexivity).
      assert (HtfpF : ud_tfp Pfinal = ud_tfp P') by (rewrite /Pfinal /uptd_set; reflexivity).
      destruct (decide (avf 0%nat = (mword_of_int 0 : mword 64))) as [Heq0 | Hne0].
      + (* ==================== argv[0] = NULL: skip the loop ==================== *)
        assert (Htgt272 : add_vec (mword_of_int (KXC + 0x218) : mword 64)
                  (sign_extend' 64 (sign_extend' 13
                     (concat_vec (mword_of_int 45 : mword 8) ('b"0"))))
                = mword_of_int (KXC + 0x272)) by pcw.
        iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KXC + 0x218))
                  (mword_of_int 45 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                  W8 (K - 68)%nat true Hcreg8 ltac:(nz)
                  ltac:(rewrite (rget_ne W8 Ra0 ltac:(nz)) HW8a0 Heq0;
                        vm_compute; reflexivity)
                  ltac:(rewrite Htgt272; vm_compute; reflexivity)
                  with "Hcg Hpc Hi218").
        iIntros (CID32 Hs32). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htgt272) in "Hpc".
        iSpecialize ("Hout" $! CID32 with "[%]"); [wp_next_chain |].
        iApply ("Hout" $! W8 Pfinal (pv_sz V) sz1). iRight.
        rewrite /kxc_at_272.
        iSplitR.
        { iPureIntro. split_and!;
            [ exact HW8sp | exact HW8s0 | exact HW8s1
            | rewrite HW8s2 /kxc_sp uint_unsigned w32_moi_unsigned; reflexivity
            | exact HW8s4 | exact HW8s5
            | rewrite HrootF Hroot'; exact HW8s6 | rewrite -Hs7eq; exact HW8s7
            | exact HW8s8 | exact HW8s9 | exact HW8s10]. }
        iSplitR.
        (* the stackbase bound at [c = 0] is [kxc_sp]'s base case: the loop has
           not moved [sp] yet, so it reads [uint sz1 - 4096 <= uint sz1].
           [change], not [cbn [kxc_sp]] -- a partial-unfold tactic on a
           [Fixpoint] match is not reliable here (see this file's [kxc_sp_S]). *)
        { iPureIntro. split_and!;
            [ lia | lia | rewrite -HW8a0; exact Heq0
            | change (kxc_sp (uint sz1) alen 0) with (uint sz1); lia ]. }
        iSplitR.
        { iPureIntro. split_and!;
            [rewrite HtfpF Htfp'; exact HPtfp | exact HbelowF | exact HcovF]. }
        iSplitL "Hpc"; [iExact "Hpc" |]. iSplitL "Hcg"; [iExact "Hcg" |].
        iSplitL "Hcnt"; [iExact "Hcnt" |].
        rewrite /kxc_c_res.
        iSplitL "Hirs"; [iExact "Hirs" |]. iSplitL "Hbm"; [iExact "Hbm" |].
        iSplitL "Hins"; [iExact "Hins" |]. iSplitL "Hbits"; [iExact "Hbits" |].
        iSplitL "Hbs"; [iExact "Hbs" |]. iSplitR; [iExact "Hka" |].
        iSplitL "Hptcl"; [iExact "Hptcl" |]. iSplitL "Hpriv"; [iExact "Hpriv" |].
        iSplitL "Hpath"; [iExact "Hpath" |]. iSplitL "Hargv"; [iExact "Hargv" |].
        iSplitL "Hargs"; [iExact "Hargs" |]. iSplitL "Helf"; [iExact "Helf" |].
        iExact "Hframe0".
      + (* ==================== argv[0] <> NULL: enter the loop ==================== *)
        assert (Htgt21a : add_vec_int (mword_of_int (KXC + 0x218) : mword 64) 2
                          = mword_of_int (KXC + 0x21a)) by pcw.
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KXC + 0x218))
                  (mword_of_int 45 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                  W8 (K - 68)%nat true Hcreg8 ltac:(nz)
                  ltac:(rewrite (rget_ne W8 Ra0 ltac:(nz)) HW8a0;
                        apply eq_vec64_false; rewrite zero_reg64; exact Hne0)
                  with "Hcg Hpc Hi218").
        iIntros (CID32 Hs32) "Hcg Hpc".
        iEval (rewrite Htgt21a) in "Hpc".
        iSpecialize ("Hout" $! CID32 with "[%]"); [wp_next_chain |].
        iApply ("Hout" $! W8 Pfinal (pv_sz V) sz1). iLeft.
        rewrite /kxc_at_21a.
        iSplitR.
        { iPureIntro. split_and!;
            [ exact HW8sp | exact HW8s0 | exact HW8s1 | rewrite -HW8a0; reflexivity
            | rewrite HW8s2 /kxc_sp uint_unsigned w32_moi_unsigned; reflexivity
            | exact HW8s4 | exact HW8s5
            | rewrite HrootF Hroot'; exact HW8s6 | rewrite -Hs7eq; exact HW8s7
            | exact HW8s8 | exact HW8s9 | exact HW8s10]. }
        iSplitR.
        { iPureIntro. split_and!;
            [ lia | lia | rewrite -HW8a0; exact Hne0
            | change (kxc_sp (uint sz1) alen 0) with (uint sz1); lia ]. }
        iSplitR.
        { iPureIntro. split_and!;
            [rewrite HtfpF Htfp'; exact HPtfp | exact HbelowF | exact HcovF]. }
        iSplitL "Hpc"; [iExact "Hpc" |]. iSplitL "Hcg"; [iExact "Hcg" |].
        iSplitL "Hcnt"; [iExact "Hcnt" |].
        rewrite /kxc_c_res.
        iSplitL "Hirs"; [iExact "Hirs" |]. iSplitL "Hbm"; [iExact "Hbm" |].
        iSplitL "Hins"; [iExact "Hins" |]. iSplitL "Hbits"; [iExact "Hbits" |].
        iSplitL "Hbs"; [iExact "Hbs" |]. iSplitR; [iExact "Hka" |].
        iSplitL "Hptcl"; [iExact "Hptcl" |]. iSplitL "Hpriv"; [iExact "Hpriv" |].
        iSplitL "Hpath"; [iExact "Hpath" |]. iSplitL "Hargv"; [iExact "Hargv" |].
        iSplitL "Hargs"; [iExact "Hargs" |]. iSplitL "Helf"; [iExact "Helf" |].
        iExact "Hframe0".
  Qed.

End KexecCSetup.

(* =================================================================== *)
(*  THE ARGV LOOP'S THREE [-1] EXITS -- ONE CONNECTOR.                   *)
(*                                                                       *)
(*  +0x358 (the stack-overflow [bltu]), +0x35c (copyout failed) and       *)
(*  +0x26e (MAXARG reached) are THE SAME TWO INSTRUCTIONS at three        *)
(*  addresses -- [c.mv s3,s4] then [c.j +0x1d6] -- so they are one lemma  *)
(*  parameterised by the stub's offset, the jump's immediate, and the     *)
(*  two [instr] facts the call site reads off [CodeKexec].  (Confirmed    *)
(*  against [CodeKexec.kxc_358]/[kxc_35c]/[kxc_26e]: all three are the    *)
(*  compressed [RTYPE (s4, zreg, s3, ADD)], and all three [c.j]s land on  *)
(*  +0x1d6.)                                                             *)
(*                                                                       *)
(*  The instructions are the easy half.  The work is the RESOURCE side:   *)
(*  [kxc_bad_1d6] wants [kxc_frame_at]'s ONE opaque 55-slot region, and   *)
(*  the loop holds the frame as [kxc_frameC] -- ustack SPLIT at [c],      *)
(*  with the [c] already-written slots carrying [kxc_sp]'s recurrence.    *)
(*  [kxc_frameC_collapse] below is that fold, and it is why the ELF       *)
(*  buffer has to come in here too: slots 47..54 are the only part of     *)
(*  the frame [kxc_c_res] holds OUTSIDE [kxc_frameC].                     *)
(*                                                                       *)
(*  ITS OWN SECTION, CLOSED BEFORE [KexecCLoop] OPENS.  A [Local Lemma]   *)
(*  applied from inside a section that fixes [CID0] bakes THAT hart into  *)
(*  its own statement instead of taking a fresh per-call-site implicit,   *)
(*  and these call sites are a dozen [wp_next]s past the entry hart --    *)
(*  the failure is an [iSpecialize: cannot instantiate] whose two sides   *)
(*  print identically.  (kexec.md records the round that cost.)           *)
(* =================================================================== *)
Section KexecCExitM1.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Rs8 := (mword_of_int 24 : mword 5).
  Notation Rs9 := (mword_of_int 25 : mword 5).
  Notation Rs10 := (mword_of_int 26 : mword 5).
  Notation Rs11 := (mword_of_int 27 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  (* [kxc_frameC]'s WRITTEN ustack prefix ([∗list] over [seq 0 c], slot [46-j]
     at index [j]) forgotten back to an opaque [stack_own] -- what a -1-tail
     exit needs (it hands the WHOLE frame back to [proc_freepagetable]'s
     caller, and does not care what argv-loop progress was in it). Slot [j]
     sits at [pa_stk sp0 (46-j)]; the LAST written slot (j = c-1) is the
     SHALLOWEST address in the run, [pa_stk sp0 (47-c)], so induction peels
     from the [seq]'s tail via [seq_S], matching [stack_own_app]'s own
     "shallow slots first" shape with no reassociation needed.
     Plain [induction c], NOT [iInduction]: this is a one-shot entailment,
     not a Löb recursion, and an auto-generated IH fighting the leading
     Coq-level premise is the tell that the plain tactic is wanted. *)
  Local Lemma kxc_ustack_collapse (sp0 : mword 64) (c : nat) (f : nat -> mword 64) :
    (c < 46)%nat ->
    ([∗ list] j ∈ seq 0 c, pa_stk sp0 (46 - j) ↦₈ (f j : mword 64)) -∗
    stack_own (pa_stk sp0 (46 - c)) c.
  Proof.
    induction c as [| c IH]; intro Hc46.
    - rewrite stack_own_0. auto.
    - rewrite seq_S big_sepL_app big_sepL_singleton.
      iIntros "[Hpre Hlast]".
      iDestruct (IH ltac:(lia) with "Hpre") as "Hrest".
      assert (Heq : pa_stk sp0 (46 - c) = pa_stk (pa_stk sp0 (45 - c)) 1).
      { rewrite pa_stk_assoc. f_equal. lia. }
      iEval (rewrite Heq) in "Hlast".
      iDestruct (stack_own_1_intro (pa_stk sp0 (45 - c)) (f c) with "Hlast") as "Hone".
      replace (46 - S c)%nat with (45 - c)%nat by lia.
      replace (S c) with (1 + c)%nat by lia.
      rewrite (stack_own_app (pa_stk sp0 (45 - c)) 1 c).
      iFrame "Hone". rewrite -Heq. iExact "Hrest".
  Qed.

  (* [kxc_frameC] (+ the ELF buffer, the frame's slots 47..54, which
     [kxc_c_res] holds separately) back to [kxc_frame_at]'s uniform shape.
     Three joins, in address order: the ustack's unwritten tail and its
     written prefix rejoin at 14..46 ([kxc_ustack_collapse] + [stack_own_app]),
     [kxc_mid_join] absorbs the ELF slots and the ph/off scratch to reach
     14..63, and [kxc_stack_of_top5] forgets the five pinned top slots.
     The argv slot's own value ([pa_add av (8*c)] rather than [av]) is
     exactly what is forgotten here, which is why this direction needs no
     hypothesis about [c] beyond its being inside the region. *)
  (* [pc + k] on a SYMBOLIC base.  The three call sites differ only in the
     stub's offset, so [pcw]'s [vm_compute] is not available here (its goal
     still mentions [stub]) -- optimization.md's "never [vm_compute] a goal
     containing a symbolic value" applies to a symbolic Z offset just as it
     does to a symbolic [mword]. *)
  Local Lemma avi_moi (z k : Z) :
    add_vec_int (mword_of_int z : mword 64) k = (mword_of_int (z + k) : mword 64).
  Proof.
    change (add_vec_int (mword_of_int z : mword 64) k)
      with (add_vec (mword_of_int z : mword 64) (mword_of_int k : mword 64)).
    apply bv_eq. rewrite add_vec64_unsigned !moi64_unsigned.
    rewrite bv_wrap_add_idemp_l bv_wrap_add_idemp_r. reflexivity.
  Qed.

  (* [stack_own_app]'s join direction with the depth supplied as an EQUATION
     rather than syntactically.  Inside the proofmode the obvious
     [replace 33 with ((33-c)+c)] is wrong: the "goal" a plain [replace] sees
     is the whole [envs_entails], so it rewrites the [33] inside the
     hypothesis's own [33 - c] too and leaves [33 - c + c - c].  Discharging
     the arithmetic in the STATEMENT ([intros ->]) sidesteps that entirely. *)
  Local Lemma stack_own_join (sp : Arch.pa) (n n1 n2 : nat) :
    (n = n1 + n2)%nat ->
    stack_own sp n1 -∗ stack_own (pa_stk sp n1) n2 -∗ stack_own sp n.
  Proof. intros ->. iIntros "A B". rewrite stack_own_app. iSplitL "A"; done. Qed.

  Local Lemma kxc_frameC_collapse
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (c : nat) (sz1 : mword 64) (alen : nat -> nat) (ef : nat -> bv 8) :
    (c <= 33)%nat ->
    (forall i, (i < 8)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (54 - i))) 8 = true) ->
    ([∗ list] j ∈ seq 0 64, pa_add (pa_stk sp0 54) j ↦ₘ ef j) -∗
    kxc_frameC sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 c sz1 alen -∗
    kxc_frame_at sp0 ra0 s00 s10 s20 w5 w6 w7 w8 w9 w10 w11 w12 w13.
  Proof.
    intros Hc33 Hal. iIntros "Helf".
    rewrite /kxc_frameC /kxc_frame_at.
    iIntros "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9 & Hf10 &
              Hf11 & Hf12 & Hf13 & Hust & Hwr & Hph & Hf64 & Hf65 & Hf66 &
              Hf67 & Hf68)".
    iDestruct "Hf65" as (w65_) "Hf65".
    iDestruct "Hf68" as (w68_) "Hf68".
    iDestruct (kxc_stack_of_top5 sp0 (pa_add av (8 * c)) w65_ pv w67 w68_
                 with "Hf64 Hf65 Hf66 Hf67 Hf68") as "Htop5".
    iDestruct (kxc_ustack_collapse sp0 c _ ltac:(lia) with "Hwr") as "Hwr".
    assert (Haddr : pa_stk (pa_stk sp0 13) (33 - c) = pa_stk sp0 (46 - c)).
    { rewrite pa_stk_assoc. f_equal. lia. }
    iEval (rewrite -Haddr) in "Hwr".
    iDestruct (stack_own_join (pa_stk sp0 13) 33 (33 - c) c ltac:(lia)
                 with "Hust Hwr") as "Hust33".
    iDestruct (kxc_elf_give sp0 ef Hal with "Helf") as "Aelf".
    iDestruct (kxc_mid_join sp0 with "Hust33 Aelf Hph") as "Amid50".
    iSplitL "Hf1"; [iExact "Hf1" |]. iSplitL "Hf2"; [iExact "Hf2" |].
    iSplitL "Hf3"; [iExact "Hf3" |]. iSplitL "Hf4"; [iExact "Hf4" |].
    iSplitL "Hf5"; [iExact "Hf5" |]. iSplitL "Hf6"; [iExact "Hf6" |].
    iSplitL "Hf7"; [iExact "Hf7" |]. iSplitL "Hf8"; [iExact "Hf8" |].
    iSplitL "Hf9"; [iExact "Hf9" |]. iSplitL "Hf10"; [iExact "Hf10" |].
    iSplitL "Hf11"; [iExact "Hf11" |]. iSplitL "Hf12"; [iExact "Hf12" |].
    iSplitL "Hf13"; [iExact "Hf13" |].
    change 55%nat with (50 + 5)%nat.
    rewrite stack_own_app (pa_stk_assoc sp0 13 50).
    iSplitL "Amid50"; [iExact "Amid50" | iExact "Htop5"].
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  RE-ASSEMBLY.  The loop body destructs the frame and the resource      *)
  (*  bundle down to individual hypotheses on entry, so every exit and the  *)
  (*  back edge have to put them back.  [iFrame] is not an option at this   *)
  (*  altitude (it does not terminate -- see this project's note), so the   *)
  (*  fold is an explicit [iSplitL] chain; written ONCE here rather than    *)
  (*  five times inside [kxc_argv_step].  Both live in THIS section so the  *)
  (*  loop can use them too.                                               *)
  (* ------------------------------------------------------------------- *)
  Local Lemma kxc_frameC_intro
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 w65 w68 : mword 64)
      (c : nat) (sz1 : mword 64) (alen : nat -> nat) :
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    word_pointsto (pa_stk sp0 4) (DfracOwn 1) s20 -∗
    word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5 -∗
    word_pointsto (pa_stk sp0 6) (DfracOwn 1) w6 -∗
    word_pointsto (pa_stk sp0 7) (DfracOwn 1) w7 -∗
    word_pointsto (pa_stk sp0 8) (DfracOwn 1) w8 -∗
    word_pointsto (pa_stk sp0 9) (DfracOwn 1) w9 -∗
    word_pointsto (pa_stk sp0 10) (DfracOwn 1) w10 -∗
    word_pointsto (pa_stk sp0 11) (DfracOwn 1) w11 -∗
    word_pointsto (pa_stk sp0 12) (DfracOwn 1) w12 -∗
    word_pointsto (pa_stk sp0 13) (DfracOwn 1) w13 -∗
    stack_own (pa_stk sp0 13) (33 - c) -∗
    ([∗ list] j ∈ seq 0 c,
       pa_stk sp0 (46 - j) ↦₈ (mword_of_int (kxc_sp (uint sz1) alen (S j)) : mword 64)) -∗
    stack_own (pa_stk sp0 54) 9 -∗
    word_pointsto (pa_stk sp0 64) (DfracOwn 1) (pa_add av (8 * c)) -∗
    word_pointsto (pa_stk sp0 65) (DfracOwn 1) w65 -∗
    word_pointsto (pa_stk sp0 66) (DfracOwn 1) pv -∗
    word_pointsto (pa_stk sp0 67) (DfracOwn 1) w67 -∗
    word_pointsto (pa_stk sp0 68) (DfracOwn 1) w68 -∗
    kxc_frameC sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 c sz1 alen.
  Proof.
    iIntros "H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13
             Hust Hwr Hph H64 H65 H66 H67 H68".
    rewrite /kxc_frameC.
    iSplitL "H1"; [iExact "H1" |]. iSplitL "H2"; [iExact "H2" |].
    iSplitL "H3"; [iExact "H3" |]. iSplitL "H4"; [iExact "H4" |].
    iSplitL "H5"; [iExact "H5" |]. iSplitL "H6"; [iExact "H6" |].
    iSplitL "H7"; [iExact "H7" |]. iSplitL "H8"; [iExact "H8" |].
    iSplitL "H9"; [iExact "H9" |]. iSplitL "H10"; [iExact "H10" |].
    iSplitL "H11"; [iExact "H11" |]. iSplitL "H12"; [iExact "H12" |].
    iSplitL "H13"; [iExact "H13" |]. iSplitL "Hust"; [iExact "Hust" |].
    iSplitL "Hwr"; [iExact "Hwr" |]. iSplitL "Hph"; [iExact "Hph" |].
    iSplitL "H64"; [iExact "H64" |].
    iSplitL "H65"; [iExists w65; iExact "H65" |].
    iSplitL "H66"; [iExact "H66" |]. iSplitL "H67"; [iExact "H67" |].
    iExists w68. iExact "H68".
  Qed.

  Local Lemma kxc_c_res_intro
      (jp : nat) (bn : bio_names) (gfs : fs_names) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (size : Z) (used2 : gset Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (c : nat) (sz1 : mword 64)
      (alen : nat -> nat) :
    iref_slots 2 -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used2 -∗
    bslots bn 3 -∗
    kalloc_env ga None -∗
    proc_pt P -∗
    proc_priv gf (proc_addr jp) pidv V -∗
    ([∗ list] k ∈ seq 0 (S plen), pa_add pv k ↦ₘ pfun k) -∗
    ([∗ list] k ∈ seq 0 (S na), pa_add av (8 * k) ↦₈{dqa} avf k) -∗
    ([∗ list] k ∈ seq 0 na,
       [∗ list] j ∈ seq 0 (aslen k), pa_add (avf k) j ↦ₘ afun k j) -∗
    ([∗ list] j ∈ seq 0 64, pa_add (pa_stk sp0 54) j ↦ₘ ef j) -∗
    kxc_frameC sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 c sz1 alen -∗
    kxc_c_res jp bn gfs ga gf cov logstart bmapstart inodestart size used2
              plen pfun na avf aslen afun pidv V dqb dqs dqa
              sp0 ra0 s00 s10 s20 pv av
              w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P c sz1 alen.
  Proof.
    iIntros "Hirs Hbm Hins Hbits Hbs Hka Hpt Hpriv Hpath Hargv Hargs Helf Hframe".
    rewrite /kxc_c_res.
    iSplitL "Hirs"; [iExact "Hirs" |]. iSplitL "Hbm"; [iExact "Hbm" |].
    iSplitL "Hins"; [iExact "Hins" |]. iSplitL "Hbits"; [iExact "Hbits" |].
    iSplitL "Hbs"; [iExact "Hbs" |]. iSplitL "Hka"; [iExact "Hka" |].
    iSplitL "Hpt"; [iExact "Hpt" |]. iSplitL "Hpriv"; [iExact "Hpriv" |].
    iSplitL "Hpath"; [iExact "Hpath" |]. iSplitL "Hargv"; [iExact "Hargv" |].
    iSplitL "Hargs"; [iExact "Hargs" |]. iSplitL "Helf"; [iExact "Helf" |].
    iExact "Hframe".
  Qed.

  (* The connector itself.  [m] is kexec's ENTRY register file (the exit's
     [callee_saved m mf] is stated against it) and [M] the file the loop is
     at; only [M]'s sp/s4/s6 matter, because [c.mv s3,s4] is the last
     instruction before the shared tail reloads everything else from the
     frame. *)
  Lemma kxc_c_exit_m1
      (jp : nat) (bn : bio_names) (gfs : fs_names) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (size : Z) (used2 : gset Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
      (m M : regfile) (K : nat) (C : iProp Σ)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (sz1 : mword 64) (c : nat)
      (stub : Z) (jimm : mword 21) :
    (K_kexec <= K)%nat ->
    (c <= 33)%nat ->
    (forall i, (i < 8)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (54 - i))) 8 = true) ->
    m !!! Regidx csp_rs1 = sp0 -> m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 -> m !!! Regidx Rs1 = s10 -> m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Rs3 = w5 -> m !!! Regidx Rs4 = w6 -> m !!! Regidx Rs5 = w7 ->
    m !!! Regidx Rs6 = w8 -> m !!! Regidx Rs7 = w9 -> m !!! Regidx Rs8 = w10 ->
    m !!! Regidx Rs9 = w11 -> m !!! Regidx Rs10 = w12 -> m !!! Regidx Rs11 = w13 ->
    M !!! Regidx csp_rs1 = pa_stk sp0 68 ->
    M !!! Regidx Rs4 = sz1 ->
    M !!! Regidx Rs6 = page_base P.(ud_root) ->
    um_below sz1 P.(ud_um) ->
    um_covered sz1 P.(ud_um) ->
    add_vec (mword_of_int (KXC + stub + 2) : mword 64) (sign_extend' 64 jimm)
      = (mword_of_int (KXC + 0x1d6) : mword 64) ->
    kernel_text -∗
    instr (mword_of_int (KXC + stub) : mword 64) true
          (RTYPE (Regidx Rs4, zreg, Regidx Rs3, ADD)) -∗
    instr (mword_of_int (KXC + stub + 2) : mword 64) true (JAL (jimm, zreg)) -∗
    pc_is (mword_of_int (KXC + stub) : mword 64) -∗
    sie_cap_gpr M (K - 68)%nat true (proc_addr jp) -∗
    cpu_own 0 true (proc_addr jp) C true -∗
    kxc_c_res jp bn gfs ga gf cov logstart bmapstart inodestart size used2
              plen pfun na avf aslen afun pidv V dqb dqs dqa
              sp0 ra0 s00 s10 s20 pv av
              w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P c sz1 alen -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
    ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
       (entry spv szv' : mword 64),
        ⌜callee_saved m mf⌝ -∗
        ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
        sie_cap_gpr mf K true (proc_addr jp) -∗
        cpu_own 0 true (proc_addr jp) C true -∗
        pc_is (ret_pc ra0) -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        ⌜used' ⊆ used2⌝ -∗
        bitmap_res gfs bmapstart cov logstart size used' -∗
        kalloc_env ga None -∗
        proc_priv gf (proc_addr jp) pidv V' -∗
        ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
        ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
        ([∗ list] i ∈ seq 0 na,
           [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
        bslots bn 3 -∗
        iref_slots 2 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hc33 Hal Hmsp Hmra Hms0 Hms1 Hms2
           Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13
           HMsp HMs4 HMs6 Hbelow Hcov Htgt.
    unfold K_kexec in HK.
    iIntros "#Htext Hi1 Hi2 Hpc Hcg Hcnt Hres Hcont".
    rewrite /kxc_c_res.
    iDestruct "Hres" as "(Hirs & Hbm & Hins & Hbits & Hbs & #Hka & Hpt & Hpriv &
                          Hpath & Hargv & Hargs & Helf & Hframe)".
    (* ---- +stub: c.mv s3,s4 -- the size [proc_freepagetable] will free ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXC + stub)) Rs3 Rs4
              M (K - 68)%nat true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi1").
    iIntros (CID1 Hsc1) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (Mt := <[Regidx Rs3 := regval_into_reg
                   (add_vec zero_reg (M !!! Regidx Rs4))]> M).
    assert (HMts3 : Mt !!! Regidx Rs3 = sz1).
    { rewrite /Mt upd_eq HMs4. apply add_vec_zero_l. }
    assert (HMtsp : Mt !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /Mt upd_ne; [exact HMsp | nz]).
    assert (HMts6 : Mt !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /Mt upd_ne; [exact HMs6 | nz]).
    assert (Hppj : add_vec_int (mword_of_int (KXC + stub) : mword 64) 2
                   = mword_of_int (KXC + stub + 2)) by apply avi_moi.
    iEval (rewrite Hppj) in "Hpc".
    (* ---- +stub+2: c.j +0x1d6 -- into the shared [-1] tail ---- *)
    iApply (wp_cj_s_sconf (mword_of_int (KXC + stub + 2)) jimm
              Mt (K - 68)%nat true
              ltac:(rewrite Htgt; vm_compute; reflexivity)
              with "Hcg Hpc Hi2").
    iIntros (CID2 Hsc2). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htgt) in "Hpc".
    (* ---- the frame collapse, and the two hart re-anchorings ---- *)
    iDestruct (kxc_frameC_collapse sp0 ra0 s00 s10 s20 pv av
                 w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 c sz1 alen ef Hc33 Hal
                 with "Helf Hframe") as "Hframeat".
    iEval (rewrite -Hmw5 -Hmw6 -Hmw7 -Hmw8 -Hmw9 -Hmw10 -Hmw11 -Hmw12 -Hmw13)
      in "Hframeat".
    iDestruct (cpu_own_transport CID0 CID2 0%nat true (proc_addr jp) C true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    assert (Hcr2 : true = false \/ proc_addr jp = zero_reg ->
                     (CID2 : CPU) = (CID0 : CPU)) by wp_next_chain.
    iDestruct (wp_next_retarget CID0 CID2 true (proc_addr jp) _ Hcr2
                 with "Hcont") as "Hcont".
    iApply (TC.kxc_bad_1d6 jp ga gf bn gfs cov logstart bmapstart inodestart
              size used2 used2 plen pfun na avf alen aslen afun pidv V
              dqb dqs dqa m Mt K C sp0 ra0 s00 s10 s20 pv av P sz1
              ltac:(unfold K_kexec; lia) ltac:(reflexivity)
              Hmsp Hmra Hms0 Hms1 Hms2 HMtsp HMts3 HMts6 Hbelow Hcov
              with "Hcg Hcnt Htext Hpc Hpt Hka Hbm Hins Hbits Hpriv
                    Hpath Hargv Hargs Hbs Hirs Hframeat Hcont").
  Qed.

End KexecCExitM1.

(* =================================================================== *)
(*  +0x21a .. +0x272 -- THE ARGV LOOP.                                   *)
(*                                                                       *)
(*  One iteration, head to back edge (or one of the three early exits    *)
(*  into [kxc_bad_1d6], or the natural fall-through into [kxc_at_272]).  *)
(*  Mirrors [ProofKexecB3.kxc_ph_step]'s shape: takes the OUTERMOST      *)
(*  kexec exit continuation [Hcont] (fired by an early exit), and        *)
(*  produces ONE output disjunction, [kxc_at_21a (S c) ∨ kxc_at_272      *)
(*  (S c)], wrapped in its own [wp_next] awaiting a (possibly retargeted) *)
(*  copy of [Hcont]'s shape from the caller.                             *)
(* =================================================================== *)
Section KexecCLoop.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Rs8 := (mword_of_int 24 : mword 5).
  Notation Rs9 := (mword_of_int 25 : mword 5).
  Notation Rs10 := (mword_of_int 26 : mword 5).
  Notation Rs11 := (mword_of_int 27 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).

  Local Ltac regne := reg_ne_side.
  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  (* [addiw rd,rs,1] on a small value: mirrors [ProofSafestrcpy.ssc_addiw_m1]'s
     technique (there for [+ (-1)]; here for [+1], so no wraparound to chase --
     the 32-bit and 64-bit truncations are both no-ops given the bound). *)
  Local Lemma kxc_addiw_p1 (n : nat) : (Z.of_nat n < 4096)%Z ->
    sign_extend' 64 (subrange_vec_dec
       (add_vec (mword_of_int (Z.of_nat n) : mword 64)
                (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0)
    = (mword_of_int (Z.of_nat n + 1) : mword 64).
  Proof.
    intro Hn.
    assert (E : (subrange_vec_dec
                   (add_vec (mword_of_int (Z.of_nat n) : mword 64)
                      (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0 : mword 32)
                = (mword_of_int (Z.of_nat n + 1) : mword 32)).
    { apply bv_eq. rewrite subrange_31_0_unsigned add_vec64_unsigned moi64_unsigned.
      assert (H1c : bv_unsigned (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64) = 1%Z)
        by (vm_compute; reflexivity).
      rewrite H1c moi32_unsigned. unfold bv_wrap.
      rewrite (Z.mod_small (Z.of_nat n) 18446744073709551616); [| lia].
      rewrite (Z.mod_small (Z.of_nat n + 1) 18446744073709551616); [| lia].
      reflexivity. }
    rewrite E. apply bv_eq.
    assert (Hrange : (0 <= Z.of_nat n + 1 < 2 ^ 31)%Z)
      by (change (2 ^ 31)%Z with 2147483648%Z; lia).
    rewrite (sext64_moi32_unsigned (Z.of_nat n + 1) Hrange) moi64_unsigned.
    unfold bv_wrap. symmetry. apply Z.mod_small.
    change (bv_modulus 64) with 18446744073709551616%Z. lia.
  Qed.

  (* [andi s2,a5,-16] is the C's [sp -= sp % 16] (SpecKexec.v's own header:
     the two agree only because the operand is non-negative, which is why
     this needs [0<=Y] and not just any [Y]). [sub_land_same_l]
     (Stdlib.ZArith.Zbitwise) gives [Y - Y.&15 = Y.&(Z.lnot 15)] and
     [Z.lnot 15 = -16] exactly; [Z.land_ones] turns the [.&15] into the
     [mod 16] [kxc_round16] wants. The detour through [Z.ones 64] is because
     [and_vec]'s own operand, taken via [bv_unsigned], is the UNSIGNED
     64-bit rendering of [-16] (i.e. [2^64-16]), not [-16] itself. *)
  Local Lemma kxc_round16_land (Y : Z) : (0 <= Y < 18446744073709551616)%Z ->
    Z.land Y 18446744073709551600 = Y - Y mod 16.
  Proof.
    intro HY.
    assert (Hc : (18446744073709551600 = Z.land (-16) (Z.ones 64))%Z)
      by (rewrite Z.land_ones; [vm_compute; reflexivity | lia]).
    rewrite Hc. rewrite (Z.land_comm (-16) (Z.ones 64)). rewrite Z.land_assoc.
    rewrite (Z.land_ones Y 64 ltac:(lia)).
    rewrite (Z.mod_small Y 18446744073709551616 HY).
    assert (H15 : Z.land Y 15 = Y mod 16).
    { change 15%Z with (Z.ones 4). apply Z.land_ones. lia. }
    assert (Hln : (Z.lnot 15 = -16)%Z) by (vm_compute; reflexivity).
    rewrite <- Hln. rewrite <- (Z.sub_land_same_l Y 15). rewrite H15. reflexivity.
  Qed.

  Local Lemma kxc_round16_andi (X : mword 64) :
    and_vec X (sign_extend' 64 (mword_of_int (-16) : mword 12))
    = (mword_of_int (kxc_round16 (bv_unsigned X)) : mword 64).
  Proof.
    apply bv_eq.
    assert (Hm : bv_unsigned (sign_extend' 64 (mword_of_int (-16) : mword 12) : mword 64)
               = 18446744073709551600%Z) by (vm_compute; reflexivity).
    rewrite and_vec64_unsigned Hm moi64_unsigned. unfold kxc_round16.
    pose proof (bv_unsigned_in_range 64 X) as HXr.
    assert (HXr' : (0 <= bv_unsigned X < 18446744073709551616)%Z).
    { change (bv_modulus 64) with 18446744073709551616%Z in HXr. exact HXr. }
    rewrite (kxc_round16_land (bv_unsigned X) HXr').
    unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616%Z.
    symmetry. apply Z.mod_small.
    pose proof (Z.mod_pos_bound (bv_unsigned X) 16 ltac:(lia)) as Hmb.
    pose proof (Z.mod_le (bv_unsigned X) 16 ltac:(lia) ltac:(lia)) as Hle.
    lia.
  Qed.

  (* [kxc_sp] is non-increasing: [kxc_round16 X <= X] always ([X mod 16] is
     non-negative for a positive divisor, regardless of [X]'s own sign), and
     each step only subtracts. So [top] is an upper bound at every index --
     the other half (with [Hspok]'s lower bound) of what makes the ANDI step's
     subtraction not wrap: [93d2a371]'s argument needs both ends. *)
  (* Named so later goals can [rewrite] it -- [simpl] is not reliable here
     (it does not always unfold a [Fixpoint] match the way full conversion
     does), while [reflexivity] on this equation IS exactly that unfolding,
     so it always succeeds. *)
  Local Lemma kxc_sp_S (top : Z) (len : nat -> nat) (i : nat) :
    kxc_sp top len (S i) = kxc_round16 (kxc_sp top len i - (Z.of_nat (len i) + 1)).
  Proof. reflexivity. Qed.

  Local Lemma kxc_sp_le_top (top : Z) (len : nat -> nat) (i : nat) :
    kxc_sp top len i <= top.
  Proof.
    induction i as [| i IH].
    - change (kxc_sp top len 0) with top. lia.
    - rewrite kxc_sp_S. unfold kxc_round16.
      pose proof (Z.mod_pos_bound
                    (kxc_sp top len i - (Z.of_nat (len i) + 1)) 16 ltac:(lia)) as Hb.
      lia.
  Qed.

  (* the address geometry the ustack write needs: [+0x250/+0x254]'s
     [s9 + 8c] (register arithmetic, [add_vec]) against [pa_stk sp0 (46-c)]
     (the resource's own addressing) -- [avi_assoc] already proves
     [add_vec_int] composes correctly under the modular wrap for ANY
     integers, symbolic base included, so no range side-condition is
     needed beyond [c <= k] to make the nat subtraction honest. *)
  Local Lemma kxc_pa_stk_add (sp : mword 64) (k c : nat) :
    (c <= k)%nat ->
    add_vec (pa_stk sp k) (mword_of_int (8 * Z.of_nat c) : mword 64) = pa_stk sp (k - c).
  Proof.
    intro Hle.
    change (add_vec (pa_stk sp k) (mword_of_int (8 * Z.of_nat c) : mword 64))
      with (add_vec_int (pa_stk sp k) (8 * Z.of_nat c)).
    unfold pa_stk at 1. rewrite avi_assoc. unfold pa_stk. f_equal.
    rewrite Nat2Z.inj_sub; [| exact Hle]. lia.
  Qed.

  Lemma kxc_argv_step
      (jp : nat) (bn : bio_names) (gfs : fs_names) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (size : Z) (used2 : gset Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
      (m M : regfile) (K : nat) (C : iProp Σ)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (oldsz sz1 : mword 64) (c : nat) :
    (K_kexec <= K)%nat ->
    (c < na)%nat ->
    (alen c < aslen c)%nat ->
    bb_cstr (afun c) (alen c) ->
    (Z.of_nat (alen c) < 4096)%Z ->
    (8192 <= uint sz1)%Z ->
    (* the ELF buffer's eight slots are 8-aligned.  A fact about [sp0] ALONE,
       constant across the whole loop, so it rides as a Coq-level premise
       rather than as a conjunct of [kxc_at_21a]: only the three [-1] exits
       read it, and only to fold slots 47..54 back into [kxc_frame_at]'s one
       opaque region ([kxc_elf_give]).  [kxc_at_1ae] is where it comes from. *)
    (forall i, (i < 8)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (54 - i))) 8 = true) ->
    m !!! Regidx csp_rs1 = sp0 -> m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 -> m !!! Regidx Rs1 = s10 -> m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Rs3 = w5 -> m !!! Regidx Rs4 = w6 -> m !!! Regidx Rs5 = w7 ->
    m !!! Regidx Rs6 = w8 -> m !!! Regidx Rs7 = w9 -> m !!! Regidx Rs8 = w10 ->
    m !!! Regidx Rs9 = w11 -> m !!! Regidx Rs10 = w12 -> m !!! Regidx Rs11 = w13 ->
    kernel_text -∗
    kxc_at_21a jp bn gfs ga gf cov logstart bmapstart inodestart size used2
               plen pfun na avf alen aslen afun pidv V dqb dqs dqa
               M K C sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P oldsz sz1 c -∗
    (* ---- kexec's OWN continuation: the three early exits close it ---- *)
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
    ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
       (entry spv szv' : mword 64),
        ⌜callee_saved m mf⌝ -∗
        ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
        sie_cap_gpr mf K true (proc_addr jp) -∗
        cpu_own 0 true (proc_addr jp) C true -∗
        pc_is (ret_pc ra0) -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        ⌜used' ⊆ used2⌝ -∗
        bitmap_res gfs bmapstart cov logstart size used' -∗
        kalloc_env ga None -∗
        proc_priv gf (proc_addr jp) pidv V' -∗
        ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
        ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
        ([∗ list] i ∈ seq 0 na,
           [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
        bslots bn 3 -∗
        iref_slots 2 -∗
        WP (Loop : expr riscv_lang)) -∗
    (* ---- THE ONE OUTPUT: continue, or the loop's own natural exit ---- *)
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M' : regfile) (P' : uptd),
        ( kxc_at_21a jp bn gfs ga gf cov logstart bmapstart inodestart size used2
                     plen pfun na avf alen aslen afun pidv V dqb dqs dqa
                     M' K C sp0 ra0 s00 s10 s20 pv av
                     w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P' oldsz sz1 (S c)
          ∨ kxc_at_272 jp bn gfs ga gf cov logstart bmapstart inodestart size used2
                       plen pfun na avf alen aslen afun pidv V dqb dqs dqa
                       M' K C sp0 ra0 s00 s10 s20 pv av
                       w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P' oldsz sz1 (S c) ) -∗
        wp_next (CID0 := CID) true (proc_addr jp) (fun (CIDy : CpuId) =>
          ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
             (entry spv szv' : mword 64),
              ⌜callee_saved m mf⌝ -∗
              ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
              sie_cap_gpr mf K true (proc_addr jp) -∗
              cpu_own 0 true (proc_addr jp) C true -∗
              pc_is (ret_pc ra0) -∗
              sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
              sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
              ⌜used' ⊆ used2⌝ -∗
              bitmap_res gfs bmapstart cov logstart size used' -∗
              kalloc_env ga None -∗
              proc_priv gf (proc_addr jp) pidv V' -∗
              ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
              ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
              ([∗ list] i ∈ seq 0 na,
                 [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
              bslots bn 3 -∗
              iref_slots 2 -∗
              WP (Loop : expr riscv_lang)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hcna Halenlt Hcstr Halen4096 Hsz1ge Hal
           Hmsp Hmra Hms0 Hms1 Hms2 Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13.
    unfold K_kexec in HK.
    iIntros "#Htext Hst Hcont Hout".
    rewrite /kxc_at_21a.
    iDestruct "Hst" as "((%HMsp & %HMs0 & %HMs1 & %HMa0 & %HMs2 & %HMs4 & %HMs5 & %HMs6 &
                          %HMs7 & %HMs8 & %HMs9 & %HMs10) &
                         (%Hcna' & %Hc32 & %Havfc & %Hspok) &
                         (%HPtfp & %Hbelow & %Hcov) &
                         Hpc & Hcg & Hcnt & Hres)".
    rewrite /kxc_c_res.
    iDestruct "Hres" as "(Hirs & Hbm & Hins & Hbits & Hbs & #Hka & Hpt & Hpriv &
                          Hpath & Hargv & Hargs & Helf & Hframe)".
    rewrite /kxc_frameC.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9 &
                            Hf10 & Hf11 & Hf12 & Hf13 & Hust & Hwr & Hph &
                            Hf64 & Hf65e & Hf66 & Hf67 & Hf68e)".
    iDestruct "Hf65e" as (w65) "Hf65". iDestruct "Hf68e" as (w68) "Hf68".
    iPoseProof (kxc_21a with "Htext") as "Hi21a".
    iPoseProof (kxc_21e with "Htext") as "Hi21e".
    iPoseProof (kxc_222 with "Htext") as "Hi222".
    iPoseProof (kxc_226 with "Htext") as "Hi226".
    iPoseProof (kxc_22a with "Htext") as "Hi22a".
    iPoseProof (kxc_22e with "Htext") as "Hi22e".
    iPoseProof (kxc_232 with "Htext") as "Hi232".
    iPoseProof (kxc_236 with "Htext") as "Hi236".
    iPoseProof (kxc_238 with "Htext") as "Hi238".
    iPoseProof (kxc_23c with "Htext") as "Hi23c".
    iPoseProof (kxc_240 with "Htext") as "Hi240".
    iPoseProof (kxc_242 with "Htext") as "Hi242".
    iPoseProof (kxc_244 with "Htext") as "Hi244".
    iPoseProof (kxc_246 with "Htext") as "Hi246".
    iPoseProof (kxc_248 with "Htext") as "Hi248".
    iPoseProof (kxc_24c with "Htext") as "Hi24c".
    iPoseProof (kxc_250 with "Htext") as "Hi250".
    iPoseProof (kxc_254 with "Htext") as "Hi254".
    iPoseProof (kxc_256 with "Htext") as "Hi256".
    iPoseProof (kxc_25a with "Htext") as "Hi25a".
    iPoseProof (kxc_25c with "Htext") as "Hi25c".
    iPoseProof (kxc_260 with "Htext") as "Hi260".
    iPoseProof (kxc_264 with "Htext") as "Hi264".
    iPoseProof (kxc_268 with "Htext") as "Hi268".
    iPoseProof (kxc_26a with "Htext") as "Hi26a".
    iPoseProof (kxc_26e with "Htext") as "Hi26e".
    iPoseProof (kxc_270 with "Htext") as "Hi270".
    iPoseProof (kxc_358 with "Htext") as "Hi358".
    iPoseProof (kxc_35a with "Htext") as "Hi35a".
    iPoseProof (kxc_35c with "Htext") as "Hi35c".
    iPoseProof (kxc_35e with "Htext") as "Hi35e".
    (* ---- argument [c]'s WHOLE string-byte resource, out of [Hargs] --
       [Hargv]'s pointer-table entries at [c]/[S c] are pulled out INLINE,
       right where +0x232/+0x264 read them (kxc_c_setup's own idiom: extract,
       use, restore -- no reason to hold both accessors open at once). ---- *)
    assert (Hlc : seq 0 (S na) !! c = Some c)
      by (rewrite (lookup_seq_lt 0 (S na) c ltac:(lia)); f_equal; lia).
    assert (Hlc1 : seq 0 (S na) !! (S c) = Some (S c))
      by (rewrite (lookup_seq_lt 0 (S na) (S c) ltac:(lia)); f_equal; lia).
    assert (Hlac : seq 0 na !! c = Some c)
      by (rewrite (lookup_seq_lt 0 na c Hcna); f_equal; lia).
    iDestruct (big_sepL_lookup_acc _ _ c c Hlac with "Hargs") as "[Hargc Hargsback]".
    (* ---- +0x21a: jal ra,strlen (a0 = avf c already) ---- *)
    assert (Htstr1 : add_vec (mword_of_int (KXC + 0x21a) : mword 64)
                       (sign_extend' 64 (mword_of_int 2081938 : mword 21))
                     = mword_of_int KernelSyms.strlen) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXC + 0x21a)) Rra
              (mword_of_int 2081938 : mword 21) M (K - 68)%nat true
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htstr1; vm_compute; reflexivity)
              with "Hcg Hpc Hi21a").
    iIntros (CID1 Hs1) "Hcg Hpc". iEval (rewrite Htstr1) in "Hpc".
    pose (Z0 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXC + 0x21a) : mword 64) 4)]> M).
    assert (HZ0ra : Z0 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXC + 0x21a) : mword 64) 4)
      by (rewrite /Z0; apply upd_eq).
    assert (HZ0a0 : Z0 !!! Regidx Ra0 = avf c)
      by (rewrite /Z0 upd_ne; [exact HMa0 | nz]).
    assert (HK2 : (2 <= K - 68)%nat) by lia.
    assert (Halen31 : (Z.of_nat (alen c) < 2 ^ 31)%Z)
      by (change (2 ^ 31)%Z with 2147483648%Z; lia).
    iEval (rewrite -HZ0a0) in "Hargc".
    iApply (Strlen.wp_strlen_sconf Z0 (aslen c) (alen c) (afun c) (K - 68)%nat
              (DfracOwn 1) true (proc_addr jp) HK2 Halenlt Hcstr Halen31
              with "Hcg Htext Hpc Hargc").
    iIntros (CID2 Hs2 T0) "Hcg Hpc Hargc %Hcs0 %HT0a0".
    assert (Hpc21e_ret : ret_pc (Z0 !!! Regidx Rra) = mword_of_int (KXC + 0x21e))
      by (rewrite HZ0ra; pcw).
    iEval (rewrite Hpc21e_ret) in "Hpc".
    assert (HT0sp : T0 !!! Regidx csp_rs1 = pa_stk sp0 68).
    { rewrite (callee_saved_lookup Hcs0 csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HMsp. }
    assert (HT0s0 : T0 !!! Regidx Rs0 = sp0).
    { rewrite (callee_saved_lookup Hcs0 Rs0 ltac:(vm_compute; reflexivity)).
      exact HMs0. }
    assert (HT0s1 : T0 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64)).
    { rewrite (callee_saved_lookup Hcs0 Rs1 ltac:(vm_compute; reflexivity)).
      exact HMs1. }
    assert (HT0s2 : T0 !!! Regidx Rs2
                    = (mword_of_int (kxc_sp (uint sz1) alen c) : mword 64)).
    { rewrite (callee_saved_lookup Hcs0 Rs2 ltac:(vm_compute; reflexivity)).
      exact HMs2. }
    assert (HT0s4 : T0 !!! Regidx Rs4 = sz1).
    { rewrite (callee_saved_lookup Hcs0 Rs4 ltac:(vm_compute; reflexivity)).
      exact HMs4. }
    assert (HT0s5 : T0 !!! Regidx Rs5 = proc_addr jp).
    { rewrite (callee_saved_lookup Hcs0 Rs5 ltac:(vm_compute; reflexivity)).
      exact HMs5. }
    assert (HT0s6 : T0 !!! Regidx Rs6 = page_base P.(ud_root)).
    { rewrite (callee_saved_lookup Hcs0 Rs6 ltac:(vm_compute; reflexivity)).
      exact HMs6. }
    assert (HT0s7 : T0 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64)).
    { rewrite (callee_saved_lookup Hcs0 Rs7 ltac:(vm_compute; reflexivity)).
      exact HMs7. }
    assert (HT0s8 : T0 !!! Regidx Rs8 = (mword_of_int 32 : mword 64)).
    { rewrite (callee_saved_lookup Hcs0 Rs8 ltac:(vm_compute; reflexivity)).
      exact HMs8. }
    assert (HT0s9 : T0 !!! Regidx Rs9 = pa_stk sp0 46).
    { rewrite (callee_saved_lookup Hcs0 Rs9 ltac:(vm_compute; reflexivity)).
      exact HMs9. }
    assert (HT0s10 : T0 !!! Regidx Rs10 = oldsz).
    { rewrite (callee_saved_lookup Hcs0 Rs10 ltac:(vm_compute; reflexivity)).
      exact HMs10. }
    (* ---- +0x21e: addiw a5,a0,1 ---- *)
    iApply (wp_addiw_s_sconf (mword_of_int (KXC + 0x21e)) Ra5 Ra0
              (mword_of_int 1 : mword 12) T0 (K - 68)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi21e").
    iIntros (CID3 Hs3) "Hcg Hpc".
    pose (T1 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (T0 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1 : mword 12)))
                     31 0))]> T0).
    assert (HT1a5 : T1 !!! Regidx Ra5
                    = (mword_of_int (Z.of_nat (alen c) + 1) : mword 64)).
    { rewrite /T1 upd_eq HT0a0. apply (kxc_addiw_p1 (alen c) Halen4096). }
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T1 upd_ne; [exact HT0sp | nz]).
    assert (HT1s0 : T1 !!! Regidx Rs0 = sp0)
      by (rewrite /T1 upd_ne; [exact HT0s0 | nz]).
    assert (HT1s1 : T1 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s1 | nz]).
    assert (HT1s2 : T1 !!! Regidx Rs2
                    = (mword_of_int (kxc_sp (uint sz1) alen c) : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s2 | nz]).
    assert (HT1s4 : T1 !!! Regidx Rs4 = sz1)
      by (rewrite /T1 upd_ne; [exact HT0s4 | nz]).
    assert (HT1s5 : T1 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /T1 upd_ne; [exact HT0s5 | nz]).
    assert (HT1s6 : T1 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T1 upd_ne; [exact HT0s6 | nz]).
    assert (HT1s7 : T1 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s7 | nz]).
    assert (HT1s8 : T1 !!! Regidx Rs8 = (mword_of_int 32 : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s8 | nz]).
    assert (HT1s9 : T1 !!! Regidx Rs9 = pa_stk sp0 46)
      by (rewrite /T1 upd_ne; [exact HT0s9 | nz]).
    assert (HT1s10 : T1 !!! Regidx Rs10 = oldsz)
      by (rewrite /T1 upd_ne; [exact HT0s10 | nz]).
    assert (Hpp222 : add_vec_int (mword_of_int (KXC + 0x21e) : mword 64) 4
                     = mword_of_int (KXC + 0x222)) by pcw.
    iEval (rewrite Hpp222) in "Hpc".
    (* ---- +0x222: sub a5,s2,a5 ---- *)
    iApply (wp_sub_s_sconf (mword_of_int (KXC + 0x222)) Ra5 Rs2 Ra5
              (sub_vec (T1 !!! Regidx Rs2) (T1 !!! Regidx Ra5))
              T1 (K - 68)%nat true ltac:(nz) ltac:(rdok) ltac:(reflexivity)
              with "Hcg Hpc Hi222").
    iIntros (CID4 Hs4) "Hcg Hpc".
    pose (T2 := <[Regidx Ra5 := regval_into_reg
                  (sub_vec (T1 !!! Regidx Rs2) (T1 !!! Regidx Ra5))]> T1).
    assert (HT2a5 : T2 !!! Regidx Ra5
                    = sub_vec (mword_of_int (kxc_sp (uint sz1) alen c) : mword 64)
                              (mword_of_int (Z.of_nat (alen c) + 1) : mword 64)).
    { rewrite /T2 upd_eq HT1s2 HT1a5. reflexivity. }
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T2 upd_ne; [exact HT1sp | nz]).
    assert (HT2s0 : T2 !!! Regidx Rs0 = sp0)
      by (rewrite /T2 upd_ne; [exact HT1s0 | nz]).
    assert (HT2s1 : T2 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
      by (rewrite /T2 upd_ne; [exact HT1s1 | nz]).
    assert (HT2s4 : T2 !!! Regidx Rs4 = sz1)
      by (rewrite /T2 upd_ne; [exact HT1s4 | nz]).
    assert (HT2s5 : T2 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /T2 upd_ne; [exact HT1s5 | nz]).
    assert (HT2s6 : T2 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T2 upd_ne; [exact HT1s6 | nz]).
    assert (HT2s7 : T2 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64))
      by (rewrite /T2 upd_ne; [exact HT1s7 | nz]).
    assert (HT2s8 : T2 !!! Regidx Rs8 = (mword_of_int 32 : mword 64))
      by (rewrite /T2 upd_ne; [exact HT1s8 | nz]).
    assert (HT2s9 : T2 !!! Regidx Rs9 = pa_stk sp0 46)
      by (rewrite /T2 upd_ne; [exact HT1s9 | nz]).
    assert (HT2s10 : T2 !!! Regidx Rs10 = oldsz)
      by (rewrite /T2 upd_ne; [exact HT1s10 | nz]).
    assert (Hpp226 : add_vec_int (mword_of_int (KXC + 0x222) : mword 64) 4
                     = mword_of_int (KXC + 0x226)) by pcw.
    iEval (rewrite Hpp226) in "Hpc".
    (* ---- +0x226: andi s2,a5,-16 (s2 = round16(sp - (len+1)) = kxc_sp(...)(S c)) ----
       THE UNDERFLOW-SAFETY ARGUMENT (93d2a371): the subtraction a5 = s2 - a5
       computed at +0x222 does not wrap mod 2^64. [Hspok] gives the LOWER
       bound (stackbase <= kxc_sp(...)c), [kxc_sp_le_top] the UPPER
       (kxc_sp(...)c <= uint sz1, so its own register never wrapped either),
       and [Halen4096]/[Hsz1ge] bound the length and the stack itself -- so
       [kxc_sp(...)c - (alen c + 1)] is a genuine Z value in [0, 2^64), and
       [sub_vec] computed it exactly (no [bv_wrap] correction needed). *)
    assert (Hspc_range : (0 <= kxc_sp (uint sz1) alen c < 18446744073709551616)%Z).
    { pose proof (kxc_sp_le_top (uint sz1) alen c) as Hle.
      pose proof (bv_unsigned_in_range 64 sz1) as Hsz1r.
      rewrite -uint_unsigned in Hsz1r.
      change (bv_modulus 64) with 18446744073709551616%Z in Hsz1r.
      lia. }
    assert (Hnowrap : (0 <= kxc_sp (uint sz1) alen c - (Z.of_nat (alen c) + 1)
                        < 18446744073709551616)%Z) by lia.
    assert (HT2a5Z : bv_unsigned (T2 !!! Regidx Ra5)
                    = kxc_sp (uint sz1) alen c - (Z.of_nat (alen c) + 1)).
    { rewrite HT2a5 sub_vec64_unsigned !moi64_unsigned. unfold bv_wrap.
      rewrite (Z.mod_small (kxc_sp (uint sz1) alen c) 18446744073709551616 Hspc_range).
      rewrite (Z.mod_small (Z.of_nat (alen c) + 1) 18446744073709551616 ltac:(lia)).
      apply Z.mod_small. exact Hnowrap. }
    iApply (wp_andi_s_sconf (mword_of_int (KXC + 0x226)) Rs2 Ra5
              (mword_of_int 4080 : mword 12)
              (and_vec (T2 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 4080 : mword 12)))
              T2 (K - 68)%nat true ltac:(nz) ltac:(rdok) ltac:(reflexivity)
              with "Hcg Hpc Hi226").
    iIntros (CID5 Hs5) "Hcg Hpc".
    pose (T3 := <[Regidx Rs2 := regval_into_reg
                  (and_vec (T2 !!! Regidx Ra5)
                           (sign_extend' 64 (mword_of_int 4080 : mword 12)))]> T2).
    assert (Himm226 : (sign_extend' 64 (mword_of_int 4080 : mword 12) : mword 64)
                     = (sign_extend' 64 (mword_of_int (-16) : mword 12) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (HT3s2 : T3 !!! Regidx Rs2
                    = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64)).
    { rewrite /T3 upd_eq Himm226 (kxc_round16_andi (T2 !!! Regidx Ra5)) HT2a5Z.
      f_equal. }
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T3 upd_ne; [exact HT2sp | nz]).
    assert (HT3s0 : T3 !!! Regidx Rs0 = sp0)
      by (rewrite /T3 upd_ne; [exact HT2s0 | nz]).
    assert (HT3s1 : T3 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
      by (rewrite /T3 upd_ne; [exact HT2s1 | nz]).
    assert (HT3s4 : T3 !!! Regidx Rs4 = sz1)
      by (rewrite /T3 upd_ne; [exact HT2s4 | nz]).
    assert (HT3s5 : T3 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /T3 upd_ne; [exact HT2s5 | nz]).
    assert (HT3s6 : T3 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T3 upd_ne; [exact HT2s6 | nz]).
    assert (HT3s7 : T3 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64))
      by (rewrite /T3 upd_ne; [exact HT2s7 | nz]).
    assert (HT3s8 : T3 !!! Regidx Rs8 = (mword_of_int 32 : mword 64))
      by (rewrite /T3 upd_ne; [exact HT2s8 | nz]).
    assert (HT3s9 : T3 !!! Regidx Rs9 = pa_stk sp0 46)
      by (rewrite /T3 upd_ne; [exact HT2s9 | nz]).
    assert (HT3s10 : T3 !!! Regidx Rs10 = oldsz)
      by (rewrite /T3 upd_ne; [exact HT2s10 | nz]).
    assert (Hpp22a : add_vec_int (mword_of_int (KXC + 0x226) : mword 64) 4
                     = mword_of_int (KXC + 0x22a)) by pcw.
    iEval (rewrite Hpp22a) in "Hpc".
    (* ---- +0x22a: bltu s2,s7,<fail> -- taken iff the NEW sp underflowed
       stackbase; the FALL-THROUGH arm re-establishes [Hspok] at [S c],
       exactly what the caller needs to enter the next iteration soundly. *)
    assert (Hsz1r64 : (0 <= uint sz1 < 18446744073709551616)%Z).
    { pose proof (bv_unsigned_in_range 64 sz1) as Hr.
      rewrite -uint_unsigned in Hr.
      change (bv_modulus 64) with 18446744073709551616%Z in Hr. exact Hr. }
    assert (HT3s2Z : uint (T3 !!! Regidx Rs2) = kxc_sp (uint sz1) alen (S c)).
    { rewrite HT3s2 uint_unsigned moi64_unsigned. unfold bv_wrap.
      apply Z.mod_small. change (bv_modulus 64) with 18446744073709551616%Z.
      rewrite kxc_sp_S. unfold kxc_round16.
      pose proof (Z.mod_pos_bound
                    (kxc_sp (uint sz1) alen c - (Z.of_nat (alen c) + 1)) 16 ltac:(lia)) as Hmb.
      pose proof (Z.mod_le
                    (kxc_sp (uint sz1) alen c - (Z.of_nat (alen c) + 1)) 16
                    ltac:(lia) ltac:(lia)) as Hle.
      lia. }
    assert (HT3s7Z : uint (T3 !!! Regidx Rs7) = (uint sz1 - 4096)%Z).
    { rewrite HT3s7 uint_unsigned moi64_unsigned. unfold bv_wrap. apply Z.mod_small.
      change (bv_modulus 64) with 18446744073709551616%Z. lia. }
    assert (Hcmp : zopz0zI_u (T3 !!! Regidx Rs2) (T3 !!! Regidx Rs7)
                 = (kxc_sp (uint sz1) alen (S c) <? uint sz1 - 4096)%Z).
    { unfold zopz0zI_u. rewrite HT3s2Z HT3s7Z. reflexivity. }
    destruct (Z_lt_ge_dec (kxc_sp (uint sz1) alen (S c)) (uint sz1 - 4096)) as [Hover | Hok].
    + (* ==== TAKEN: genuine stack overflow.  Into the +0x358 stub, which is
         [c.mv s3,s4 ; c.j +0x1d6] -- [kxc_c_exit_m1].  NOTHING in the frame
         has moved yet at this point (the ustack write is +0x250 and the
         argv-slot bump +0x260), so the frame folds back at [c], unchanged
         from the loop head. ==== *)
      assert (Hcmp_true : zopz0zI_u (T3 !!! Regidx Rs2) (T3 !!! Regidx Rs7) = true)
        by (rewrite Hcmp; apply Z.ltb_lt; exact Hover).
      assert (Htgt358 : add_vec (mword_of_int (KXC + 0x22a) : mword 64)
                          (sign_extend' 64 (mword_of_int 302 : mword 13))
                       = mword_of_int (KXC + 0x358)) by pcw.
      iApply (wp_bltu_taken_s_sconf (mword_of_int (KXC + 0x22a)) (mword_of_int 302 : mword 13)
                Rs7 Rs2 T3 (K - 68)%nat true ltac:(nz) ltac:(nz)
                ltac:(rewrite (rget_ne T3 Rs2 ltac:(nz)) (rget_ne T3 Rs7 ltac:(nz));
                      exact Hcmp_true)
                ltac:(rewrite Htgt358; vm_compute; reflexivity)
                with "Hcg Hpc Hi22a").
      iIntros (CID6 Hs6). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt358) in "Hpc".
      (* [Hargc] is still addressed at [Z0 !!! Ra0] -- the shape the first
         strlen call was handed and returned; put it back on [avf c] before
         [Hargsback] will take it. *)
      iEval (rewrite HZ0a0) in "Hargc".
      iDestruct ("Hargsback" with "Hargc") as "Hargs".
      iDestruct (kxc_frameC_intro sp0 ra0 s00 s10 s20 pv av
                   w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 w65 w68 c sz1 alen
                   with "Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10 Hf11 Hf12 Hf13
                         Hust Hwr Hph Hf64 Hf65 Hf66 Hf67 Hf68") as "Hframe".
      iDestruct (kxc_c_res_intro jp bn gfs ga gf cov logstart bmapstart inodestart
                   size used2 plen pfun na avf aslen afun pidv V dqb dqs dqa
                   sp0 ra0 s00 s10 s20 pv av
                   w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P c sz1 alen
                   with "Hirs Hbm Hins Hbits Hbs Hka Hpt Hpriv Hpath Hargv Hargs
                         Helf Hframe") as "Hres".
      iDestruct (cpu_own_transport CID0 CID6 0%nat true (proc_addr jp) C true
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      assert (Hcr6 : true = false \/ proc_addr jp = zero_reg ->
                       (CID6 : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_retarget CID0 CID6 true (proc_addr jp) _ Hcr6
                   with "Hcont") as "Hcont".
      iApply (kxc_c_exit_m1 (CID0 := CID6) jp bn gfs ga gf cov logstart
                bmapstart inodestart size used2 plen pfun na avf alen aslen afun
                pidv V dqb dqs dqa m T3 K C sp0 ra0 s00 s10 s20 pv av
                w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P sz1 c 0x358
                (sign_extend' 21 (concat_vec (mword_of_int 1854 : mword 11) ('b"0")))
                ltac:(unfold K_kexec; lia) ltac:(lia) Hal
                Hmsp Hmra Hms0 Hms1 Hms2 Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11
                Hmw12 Hmw13 HT3sp HT3s4 HT3s6 Hbelow Hcov ltac:(pcw)
                with "Htext Hi358 Hi35a Hpc Hcg Hcnt Hres Hcont").
    + (* ==== FALL-THROUGH: no overflow -- [Hspok] re-established at [S c]. ==== *)
      assert (Hcmp_false : zopz0zI_u (T3 !!! Regidx Rs2) (T3 !!! Regidx Rs7) = false)
        by (rewrite Hcmp; apply Z.ltb_ge; lia).
      assert (HspokS : (uint sz1 - 4096 <= kxc_sp (uint sz1) alen (S c))%Z) by lia.
      iApply (wp_bltu_fall_s_sconf (mword_of_int (KXC + 0x22a)) (mword_of_int 302 : mword 13)
                Rs7 Rs2 T3 (K - 68)%nat true ltac:(nz) ltac:(nz)
                ltac:(rewrite (rget_ne T3 Rs2 ltac:(nz)) (rget_ne T3 Rs7 ltac:(nz));
                      exact Hcmp_false)
                with "Hcg Hpc Hi22a").
      iIntros (CID7 Hs7) "Hcg Hpc".
      assert (Hpp22e : add_vec_int (mword_of_int (KXC + 0x22a) : mword 64) 4
                       = mword_of_int (KXC + 0x22e)) by pcw.
      iEval (rewrite Hpp22e) in "Hpc".
      (* ---- +0x22e: ld s11,3584(s0) -- reload argv (the spilled slot-64
         pointer table), unchanged since [kxc_c_setup] bumped it. ---- *)
      assert (Hargvslot' : add_vec (T3 !!! Regidx Rs0)
                              (sign_extend' 64 (mword_of_int 3584 : mword 12))
                          = pa_stk sp0 64).
      { rewrite HT3s0. apply kxc_argv_slot. }
      iEval (rewrite -Hargvslot') in "Hf64".
      iApply (wp_ld_s_sconf (mword_of_int (KXC + 0x22e)) Rs11 Rs0
                (mword_of_int 3584 : mword 12) T3 (K - 68)%nat (pa_add av (8 * c)) true
                (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi22e Hf64").
      iIntros (CID8 Hs8) "Hcg Hpc Hf64". iEval (rewrite Hargvslot') in "Hf64".
      pose (T4 := <[Regidx Rs11 := regval_into_reg (pa_add av (8 * c))]> T3).
      assert (HT4s11 : T4 !!! Regidx Rs11 = pa_add av (8 * c)) by (rewrite /T4; apply upd_eq).
      assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /T4 upd_ne; [exact HT3sp | nz]).
      assert (HT4s0 : T4 !!! Regidx Rs0 = sp0)
        by (rewrite /T4 upd_ne; [exact HT3s0 | nz]).
      assert (HT4s1 : T4 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
        by (rewrite /T4 upd_ne; [exact HT3s1 | nz]).
      assert (HT4s2 : T4 !!! Regidx Rs2
                      = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64))
        by (rewrite /T4 upd_ne; [exact HT3s2 | nz]).
      assert (HT4s4 : T4 !!! Regidx Rs4 = sz1)
        by (rewrite /T4 upd_ne; [exact HT3s4 | nz]).
      assert (HT4s5 : T4 !!! Regidx Rs5 = proc_addr jp)
        by (rewrite /T4 upd_ne; [exact HT3s5 | nz]).
      assert (HT4s6 : T4 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /T4 upd_ne; [exact HT3s6 | nz]).
      assert (HT4s7 : T4 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64))
        by (rewrite /T4 upd_ne; [exact HT3s7 | nz]).
      assert (HT4s8 : T4 !!! Regidx Rs8 = (mword_of_int 32 : mword 64))
        by (rewrite /T4 upd_ne; [exact HT3s8 | nz]).
      assert (HT4s9 : T4 !!! Regidx Rs9 = pa_stk sp0 46)
        by (rewrite /T4 upd_ne; [exact HT3s9 | nz]).
      assert (HT4s10 : T4 !!! Regidx Rs10 = oldsz)
        by (rewrite /T4 upd_ne; [exact HT3s10 | nz]).
      assert (Hpp232 : add_vec_int (mword_of_int (KXC + 0x22e) : mword 64) 4
                       = mword_of_int (KXC + 0x232)) by pcw.
      iEval (rewrite Hpp232) in "Hpc".
      (* ---- +0x232: ld s3,0(s11) -- avf c, out of [Hargv] (extract/use/
         restore, same idiom as [kxc_c_setup]'s own argv[0] read). ---- *)
      iDestruct (big_sepL_lookup_acc _ _ c c Hlc with "Hargv") as "[Hac Hargvback]".
      assert (Hz0imm : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                      = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      assert (Havcaddr : add_vec (T4 !!! Regidx Rs11)
                            (sign_extend' 64 (mword_of_int 0 : mword 12))
                        = pa_add av (8 * c)).
      { rewrite HT4s11 Hz0imm. exact (avi0 (pa_add av (8 * c))). }
      iEval (rewrite -Havcaddr) in "Hac".
      iApply (wp_ld_s_sconf (mword_of_int (KXC + 0x232)) Rs3 Rs11
                (mword_of_int 0 : mword 12) T4 (K - 68)%nat (avf c) true
                (dqm := dqa) ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi232 Hac").
      iIntros (CID9 Hs9) "Hcg Hpc Hac". iEval (rewrite Havcaddr) in "Hac".
      iDestruct ("Hargvback" with "Hac") as "Hargv".
      pose (T5 := <[Regidx Rs3 := regval_into_reg (avf c)]> T4).
      assert (HT5s3 : T5 !!! Regidx Rs3 = avf c) by (rewrite /T5; apply upd_eq).
      assert (HT5sp : T5 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /T5 upd_ne; [exact HT4sp | nz]).
      assert (HT5s0 : T5 !!! Regidx Rs0 = sp0)
        by (rewrite /T5 upd_ne; [exact HT4s0 | nz]).
      assert (HT5s1 : T5 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
        by (rewrite /T5 upd_ne; [exact HT4s1 | nz]).
      assert (HT5s2 : T5 !!! Regidx Rs2
                      = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64))
        by (rewrite /T5 upd_ne; [exact HT4s2 | nz]).
      assert (HT5s4 : T5 !!! Regidx Rs4 = sz1)
        by (rewrite /T5 upd_ne; [exact HT4s4 | nz]).
      assert (HT5s5 : T5 !!! Regidx Rs5 = proc_addr jp)
        by (rewrite /T5 upd_ne; [exact HT4s5 | nz]).
      assert (HT5s6 : T5 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /T5 upd_ne; [exact HT4s6 | nz]).
      assert (HT5s7 : T5 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64))
        by (rewrite /T5 upd_ne; [exact HT4s7 | nz]).
      assert (HT5s8 : T5 !!! Regidx Rs8 = (mword_of_int 32 : mword 64))
        by (rewrite /T5 upd_ne; [exact HT4s8 | nz]).
      assert (HT5s9 : T5 !!! Regidx Rs9 = pa_stk sp0 46)
        by (rewrite /T5 upd_ne; [exact HT4s9 | nz]).
      assert (HT5s10 : T5 !!! Regidx Rs10 = oldsz)
        by (rewrite /T5 upd_ne; [exact HT4s10 | nz]).
      assert (HT5s11 : T5 !!! Regidx Rs11 = pa_add av (8 * c))
        by (rewrite /T5 upd_ne; [exact HT4s11 | nz]).
      assert (Hpp236 : add_vec_int (mword_of_int (KXC + 0x232) : mword 64) 4
                       = mword_of_int (KXC + 0x236)) by pcw.
      iEval (rewrite Hpp236) in "Hpc".
      (* ---- +0x236: c.mv a0,s3 -- a0 = avf c, strlen's argument
         (compressed -- [kxc_236]'s own [instr _ true _], confirmed against
         CodeKexec.v; NOT the non-compressed form this was first mistaken
         for). [wp_cmv_s_sconf] already exists in the shared library, no
         new lemma needed. ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KXC + 0x236)) Ra0 Rs3
                T5 (K - 68)%nat true ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi236").
      iIntros (CID10 Hs10) "Hcg Hpc".
      pose (T6 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget T5 Rs3))]> T5).
      assert (HT6a0 : T6 !!! Regidx Ra0 = avf c).
      { rewrite /T6 upd_eq (rget_ne T5 Rs3 ltac:(nz)) HT5s3. apply add_vec_zero_l. }
      assert (HT6sp : T6 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /T6 upd_ne; [exact HT5sp | nz]).
      assert (HT6s0 : T6 !!! Regidx Rs0 = sp0)
        by (rewrite /T6 upd_ne; [exact HT5s0 | nz]).
      assert (HT6s1 : T6 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
        by (rewrite /T6 upd_ne; [exact HT5s1 | nz]).
      assert (HT6s2 : T6 !!! Regidx Rs2
                      = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64))
        by (rewrite /T6 upd_ne; [exact HT5s2 | nz]).
      assert (HT6s3 : T6 !!! Regidx Rs3 = avf c)
        by (rewrite /T6 upd_ne; [exact HT5s3 | nz]).
      assert (HT6s4 : T6 !!! Regidx Rs4 = sz1)
        by (rewrite /T6 upd_ne; [exact HT5s4 | nz]).
      assert (HT6s5 : T6 !!! Regidx Rs5 = proc_addr jp)
        by (rewrite /T6 upd_ne; [exact HT5s5 | nz]).
      assert (HT6s6 : T6 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /T6 upd_ne; [exact HT5s6 | nz]).
      assert (HT6s7 : T6 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64))
        by (rewrite /T6 upd_ne; [exact HT5s7 | nz]).
      assert (HT6s8 : T6 !!! Regidx Rs8 = (mword_of_int 32 : mword 64))
        by (rewrite /T6 upd_ne; [exact HT5s8 | nz]).
      assert (HT6s9 : T6 !!! Regidx Rs9 = pa_stk sp0 46)
        by (rewrite /T6 upd_ne; [exact HT5s9 | nz]).
      assert (HT6s10 : T6 !!! Regidx Rs10 = oldsz)
        by (rewrite /T6 upd_ne; [exact HT5s10 | nz]).
      assert (HT6s11 : T6 !!! Regidx Rs11 = pa_add av (8 * c))
        by (rewrite /T6 upd_ne; [exact HT5s11 | nz]).
      assert (Hpp238 : add_vec_int (mword_of_int (KXC + 0x236) : mword 64) 2
                       = mword_of_int (KXC + 0x238)) by pcw.
      iEval (rewrite Hpp238) in "Hpc".
      (* ---- +0x238: jal ra,strlen (a0 = avf c again) -- the SECOND strlen
         call the C source spells (once for the sp arithmetic at +0x21a,
         again here for copyout's own [len] argument); [Hargc] is still in
         hand, unconsumed -- [Strlen.wp_strlen_sconf]'s own postcondition
         gives it back read-only, and nothing between +0x21a and here
         touched it. ---- *)
      assert (Htstr2 : add_vec (mword_of_int (KXC + 0x238) : mword 64)
                         (sign_extend' 64 (mword_of_int 2081908 : mword 21))
                       = mword_of_int KernelSyms.strlen) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (KXC + 0x238)) Rra
                (mword_of_int 2081908 : mword 21) T6 (K - 68)%nat true
                ltac:(nz) ltac:(rdok)
                ltac:(rewrite Htstr2; vm_compute; reflexivity)
                with "Hcg Hpc Hi238").
      iIntros (CID11 Hs11) "Hcg Hpc". iEval (rewrite Htstr2) in "Hpc".
      pose (Z1 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KXC + 0x238) : mword 64) 4)]> T6).
      assert (HZ1ra : Z1 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KXC + 0x238) : mword 64) 4)
        by (rewrite /Z1; apply upd_eq).
      assert (HZ1a0 : Z1 !!! Regidx Ra0 = avf c)
        by (rewrite /Z1 upd_ne; [exact HT6a0 | nz]).
      (* [Hargc] came back from the FIRST strlen call still addressed at
         [Z0!!!Ra0] (its own postcondition doesn't convert back to [avf c]
         -- SpecStrlen.v's [s] is whatever [a0] held AT THAT CALL) -- bridge
         through [avf c] to reach [Z1!!!Ra0] for this one. *)
      iEval (rewrite HZ0a0) in "Hargc".
      iEval (rewrite -HZ1a0) in "Hargc".
      iApply (Strlen.wp_strlen_sconf Z1 (aslen c) (alen c) (afun c) (K - 68)%nat
                (DfracOwn 1) true (proc_addr jp) HK2 Halenlt Hcstr Halen31
                with "Hcg Htext Hpc Hargc").
      iIntros (CID12 Hs12 T7) "Hcg Hpc Hargc %Hcs1 %HT7a0".
      assert (Hpc23c_ret : ret_pc (Z1 !!! Regidx Rra) = mword_of_int (KXC + 0x23c))
        by (rewrite HZ1ra; pcw).
      iEval (rewrite Hpc23c_ret) in "Hpc".
      assert (HT7sp : T7 !!! Regidx csp_rs1 = pa_stk sp0 68).
      { rewrite (callee_saved_lookup Hcs1 csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HT6sp. }
      assert (HT7s0 : T7 !!! Regidx Rs0 = sp0).
      { rewrite (callee_saved_lookup Hcs1 Rs0 ltac:(vm_compute; reflexivity)).
        exact HT6s0. }
      assert (HT7s1 : T7 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64)).
      { rewrite (callee_saved_lookup Hcs1 Rs1 ltac:(vm_compute; reflexivity)).
        exact HT6s1. }
      assert (HT7s2 : T7 !!! Regidx Rs2
                      = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64)).
      { rewrite (callee_saved_lookup Hcs1 Rs2 ltac:(vm_compute; reflexivity)).
        exact HT6s2. }
      assert (HT7s3 : T7 !!! Regidx Rs3 = avf c).
      { rewrite (callee_saved_lookup Hcs1 Rs3 ltac:(vm_compute; reflexivity)).
        exact HT6s3. }
      assert (HT7s4 : T7 !!! Regidx Rs4 = sz1).
      { rewrite (callee_saved_lookup Hcs1 Rs4 ltac:(vm_compute; reflexivity)).
        exact HT6s4. }
      assert (HT7s5 : T7 !!! Regidx Rs5 = proc_addr jp).
      { rewrite (callee_saved_lookup Hcs1 Rs5 ltac:(vm_compute; reflexivity)).
        exact HT6s5. }
      assert (HT7s6 : T7 !!! Regidx Rs6 = page_base P.(ud_root)).
      { rewrite (callee_saved_lookup Hcs1 Rs6 ltac:(vm_compute; reflexivity)).
        exact HT6s6. }
      assert (HT7s7 : T7 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64)).
      { rewrite (callee_saved_lookup Hcs1 Rs7 ltac:(vm_compute; reflexivity)).
        exact HT6s7. }
      assert (HT7s8 : T7 !!! Regidx Rs8 = (mword_of_int 32 : mword 64)).
      { rewrite (callee_saved_lookup Hcs1 Rs8 ltac:(vm_compute; reflexivity)).
        exact HT6s8. }
      assert (HT7s9 : T7 !!! Regidx Rs9 = pa_stk sp0 46).
      { rewrite (callee_saved_lookup Hcs1 Rs9 ltac:(vm_compute; reflexivity)).
        exact HT6s9. }
      assert (HT7s10 : T7 !!! Regidx Rs10 = oldsz).
      { rewrite (callee_saved_lookup Hcs1 Rs10 ltac:(vm_compute; reflexivity)).
        exact HT6s10. }
      assert (HT7s11 : T7 !!! Regidx Rs11 = pa_add av (8 * c)).
      { rewrite (callee_saved_lookup Hcs1 Rs11 ltac:(vm_compute; reflexivity)).
        exact HT6s11. }
      (* ---- +0x23c: addiw a4,a0,1 (a4 = alen c + 1, copyout's len) ---- *)
      iApply (wp_addiw_s_sconf (mword_of_int (KXC + 0x23c)) Ra4 Ra0
                (mword_of_int 1 : mword 12) T7 (K - 68)%nat true
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi23c").
      iIntros (CID13 Hs13) "Hcg Hpc".
      pose (T8 := <[Regidx Ra4 := regval_into_reg
                    (sign_extend' 64 (subrange_vec_dec
                       (add_vec (T7 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1 : mword 12)))
                       31 0))]> T7).
      assert (HT8a4 : T8 !!! Regidx Ra4 = (mword_of_int (Z.of_nat (alen c) + 1) : mword 64)).
      { rewrite /T8 upd_eq HT7a0. apply (kxc_addiw_p1 (alen c) Halen4096). }
      assert (HT8sp : T8 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /T8 upd_ne; [exact HT7sp | nz]).
      assert (HT8s0 : T8 !!! Regidx Rs0 = sp0)
        by (rewrite /T8 upd_ne; [exact HT7s0 | nz]).
      assert (HT8s5 : T8 !!! Regidx Rs5 = proc_addr jp)
        by (rewrite /T8 upd_ne; [exact HT7s5 | nz]).
      assert (HT8s1 : T8 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
        by (rewrite /T8 upd_ne; [exact HT7s1 | nz]).
      assert (HT8s2 : T8 !!! Regidx Rs2
                      = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64))
        by (rewrite /T8 upd_ne; [exact HT7s2 | nz]).
      assert (HT8s3 : T8 !!! Regidx Rs3 = avf c)
        by (rewrite /T8 upd_ne; [exact HT7s3 | nz]).
      assert (HT8s4 : T8 !!! Regidx Rs4 = sz1)
        by (rewrite /T8 upd_ne; [exact HT7s4 | nz]).
      assert (HT8s6 : T8 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /T8 upd_ne; [exact HT7s6 | nz]).
      assert (HT8s7 : T8 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64))
        by (rewrite /T8 upd_ne; [exact HT7s7 | nz]).
      assert (HT8s8 : T8 !!! Regidx Rs8 = (mword_of_int 32 : mword 64))
        by (rewrite /T8 upd_ne; [exact HT7s8 | nz]).
      assert (HT8s9 : T8 !!! Regidx Rs9 = pa_stk sp0 46)
        by (rewrite /T8 upd_ne; [exact HT7s9 | nz]).
      assert (HT8s10 : T8 !!! Regidx Rs10 = oldsz)
        by (rewrite /T8 upd_ne; [exact HT7s10 | nz]).
      assert (HT8s11 : T8 !!! Regidx Rs11 = pa_add av (8 * c))
        by (rewrite /T8 upd_ne; [exact HT7s11 | nz]).
      assert (Hpp240 : add_vec_int (mword_of_int (KXC + 0x23c) : mword 64) 4
                       = mword_of_int (KXC + 0x240)) by pcw.
      iEval (rewrite Hpp240) in "Hpc".
      (* ---- +0x240: c.mv a3,s3 (a3 = avf c, copyout's src) ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KXC + 0x240)) Ra3 Rs3
                T8 (K - 68)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi240").
      iIntros (CID14 Hs14) "Hcg Hpc".
      pose (T9 := <[Regidx Ra3 := regval_into_reg (add_vec zero_reg (rget T8 Rs3))]> T8).
      assert (HT9a3 : T9 !!! Regidx Ra3 = avf c).
      { rewrite /T9 upd_eq (rget_ne T8 Rs3 ltac:(nz)) HT8s3. apply add_vec_zero_l. }
      assert (HT9sp : T9 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /T9 upd_ne; [exact HT8sp | nz]).
      assert (HT9s0 : T9 !!! Regidx Rs0 = sp0)
        by (rewrite /T9 upd_ne; [exact HT8s0 | nz]).
      assert (HT9s5 : T9 !!! Regidx Rs5 = proc_addr jp)
        by (rewrite /T9 upd_ne; [exact HT8s5 | nz]).
      assert (HT9s1 : T9 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
        by (rewrite /T9 upd_ne; [exact HT8s1 | nz]).
      assert (HT9a4 : T9 !!! Regidx Ra4 = (mword_of_int (Z.of_nat (alen c) + 1) : mword 64))
        by (rewrite /T9 upd_ne; [exact HT8a4 | nz]).
      assert (HT9s2 : T9 !!! Regidx Rs2
                      = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64))
        by (rewrite /T9 upd_ne; [exact HT8s2 | nz]).
      assert (HT9s4 : T9 !!! Regidx Rs4 = sz1)
        by (rewrite /T9 upd_ne; [exact HT8s4 | nz]).
      assert (HT9s6 : T9 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /T9 upd_ne; [exact HT8s6 | nz]).
      assert (HT9s7 : T9 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64))
        by (rewrite /T9 upd_ne; [exact HT8s7 | nz]).
      assert (HT9s8 : T9 !!! Regidx Rs8 = (mword_of_int 32 : mword 64))
        by (rewrite /T9 upd_ne; [exact HT8s8 | nz]).
      assert (HT9s9 : T9 !!! Regidx Rs9 = pa_stk sp0 46)
        by (rewrite /T9 upd_ne; [exact HT8s9 | nz]).
      assert (HT9s10 : T9 !!! Regidx Rs10 = oldsz)
        by (rewrite /T9 upd_ne; [exact HT8s10 | nz]).
      assert (HT9s11 : T9 !!! Regidx Rs11 = pa_add av (8 * c))
        by (rewrite /T9 upd_ne; [exact HT8s11 | nz]).
      assert (Hpp242 : add_vec_int (mword_of_int (KXC + 0x240) : mword 64) 2
                       = mword_of_int (KXC + 0x242)) by pcw.
      iEval (rewrite Hpp242) in "Hpc".
      (* ---- +0x242: c.mv a2,s2 (a2 = new sp, copyout's dstva) ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KXC + 0x242)) Ra2 Rs2
                T9 (K - 68)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi242").
      iIntros (CID15 Hs15) "Hcg Hpc".
      pose (T10 := <[Regidx Ra2 := regval_into_reg (add_vec zero_reg (rget T9 Rs2))]> T9).
      assert (HT10a2 : T10 !!! Regidx Ra2
                      = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64)).
      { rewrite /T10 upd_eq (rget_ne T9 Rs2 ltac:(nz)) HT9s2. apply add_vec_zero_l. }
      assert (HT10sp : T10 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /T10 upd_ne; [exact HT9sp | nz]).
      assert (HT10s0 : T10 !!! Regidx Rs0 = sp0)
        by (rewrite /T10 upd_ne; [exact HT9s0 | nz]).
      assert (HT10s5 : T10 !!! Regidx Rs5 = proc_addr jp)
        by (rewrite /T10 upd_ne; [exact HT9s5 | nz]).
      assert (HT10s1 : T10 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
        by (rewrite /T10 upd_ne; [exact HT9s1 | nz]).
      assert (HT10a3 : T10 !!! Regidx Ra3 = avf c)
        by (rewrite /T10 upd_ne; [exact HT9a3 | nz]).
      assert (HT10a4 : T10 !!! Regidx Ra4 = (mword_of_int (Z.of_nat (alen c) + 1) : mword 64))
        by (rewrite /T10 upd_ne; [exact HT9a4 | nz]).
      assert (HT10s2 : T10 !!! Regidx Rs2
                      = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64))
        by (rewrite /T10 upd_ne; [exact HT9s2 | nz]).
      assert (HT10s4 : T10 !!! Regidx Rs4 = sz1)
        by (rewrite /T10 upd_ne; [exact HT9s4 | nz]).
      assert (HT10s6 : T10 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /T10 upd_ne; [exact HT9s6 | nz]).
      assert (HT10s7 : T10 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64))
        by (rewrite /T10 upd_ne; [exact HT9s7 | nz]).
      assert (HT10s8 : T10 !!! Regidx Rs8 = (mword_of_int 32 : mword 64))
        by (rewrite /T10 upd_ne; [exact HT9s8 | nz]).
      assert (HT10s9 : T10 !!! Regidx Rs9 = pa_stk sp0 46)
        by (rewrite /T10 upd_ne; [exact HT9s9 | nz]).
      assert (HT10s10 : T10 !!! Regidx Rs10 = oldsz)
        by (rewrite /T10 upd_ne; [exact HT9s10 | nz]).
      assert (HT10s11 : T10 !!! Regidx Rs11 = pa_add av (8 * c))
        by (rewrite /T10 upd_ne; [exact HT9s11 | nz]).
      assert (Hpp244 : add_vec_int (mword_of_int (KXC + 0x242) : mword 64) 2
                       = mword_of_int (KXC + 0x244)) by pcw.
      iEval (rewrite Hpp244) in "Hpc".
      (* ---- +0x244: c.mv a1,s4 (a1 = sz1, copyout's psz) ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KXC + 0x244)) Ra1 Rs4
                T10 (K - 68)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi244").
      iIntros (CID16 Hs16) "Hcg Hpc".
      pose (T11 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (rget T10 Rs4))]> T10).
      assert (HT11a1 : T11 !!! Regidx Ra1 = sz1).
      { rewrite /T11 upd_eq (rget_ne T10 Rs4 ltac:(nz)) HT10s4. apply add_vec_zero_l. }
      assert (HT11sp : T11 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /T11 upd_ne; [exact HT10sp | nz]).
      assert (HT11s0 : T11 !!! Regidx Rs0 = sp0)
        by (rewrite /T11 upd_ne; [exact HT10s0 | nz]).
      assert (HT11s5 : T11 !!! Regidx Rs5 = proc_addr jp)
        by (rewrite /T11 upd_ne; [exact HT10s5 | nz]).
      assert (HT11s1 : T11 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
        by (rewrite /T11 upd_ne; [exact HT10s1 | nz]).
      assert (HT11a2 : T11 !!! Regidx Ra2
                      = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64))
        by (rewrite /T11 upd_ne; [exact HT10a2 | nz]).
      assert (HT11a3 : T11 !!! Regidx Ra3 = avf c)
        by (rewrite /T11 upd_ne; [exact HT10a3 | nz]).
      assert (HT11a4 : T11 !!! Regidx Ra4 = (mword_of_int (Z.of_nat (alen c) + 1) : mword 64))
        by (rewrite /T11 upd_ne; [exact HT10a4 | nz]).
      assert (HT11s2 : T11 !!! Regidx Rs2
                      = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64))
        by (rewrite /T11 upd_ne; [exact HT10s2 | nz]).
      assert (HT11s4 : T11 !!! Regidx Rs4 = sz1)
        by (rewrite /T11 upd_ne; [exact HT10s4 | nz]).
      assert (HT11s6 : T11 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /T11 upd_ne; [exact HT10s6 | nz]).
      assert (HT11s7 : T11 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64))
        by (rewrite /T11 upd_ne; [exact HT10s7 | nz]).
      assert (HT11s8 : T11 !!! Regidx Rs8 = (mword_of_int 32 : mword 64))
        by (rewrite /T11 upd_ne; [exact HT10s8 | nz]).
      assert (HT11s9 : T11 !!! Regidx Rs9 = pa_stk sp0 46)
        by (rewrite /T11 upd_ne; [exact HT10s9 | nz]).
      assert (HT11s10 : T11 !!! Regidx Rs10 = oldsz)
        by (rewrite /T11 upd_ne; [exact HT10s10 | nz]).
      assert (HT11s11 : T11 !!! Regidx Rs11 = pa_add av (8 * c))
        by (rewrite /T11 upd_ne; [exact HT10s11 | nz]).
      assert (Hpp246 : add_vec_int (mword_of_int (KXC + 0x244) : mword 64) 2
                       = mword_of_int (KXC + 0x246)) by pcw.
      iEval (rewrite Hpp246) in "Hpc".
      (* ---- +0x246: c.mv a0,s6 (a0 = pagetable root, copyout's pagetable) ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KXC + 0x246)) Ra0 Rs6
                T11 (K - 68)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi246").
      iIntros (CID17 Hs17) "Hcg Hpc".
      pose (T12 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget T11 Rs6))]> T11).
      assert (HT12a0 : T12 !!! Regidx Ra0 = page_base P.(ud_root)).
      { rewrite /T12 upd_eq (rget_ne T11 Rs6 ltac:(nz)) HT11s6. apply add_vec_zero_l. }
      assert (HT12sp : T12 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /T12 upd_ne; [exact HT11sp | nz]).
      assert (HT12s0 : T12 !!! Regidx Rs0 = sp0)
        by (rewrite /T12 upd_ne; [exact HT11s0 | nz]).
      assert (HT12s1 : T12 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
        by (rewrite /T12 upd_ne; [exact HT11s1 | nz]).
      assert (HT12a1 : T12 !!! Regidx Ra1 = sz1)
        by (rewrite /T12 upd_ne; [exact HT11a1 | nz]).
      assert (HT12a2 : T12 !!! Regidx Ra2
                      = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64))
        by (rewrite /T12 upd_ne; [exact HT11a2 | nz]).
      assert (HT12a3 : T12 !!! Regidx Ra3 = avf c)
        by (rewrite /T12 upd_ne; [exact HT11a3 | nz]).
      assert (HT12a4 : T12 !!! Regidx Ra4 = (mword_of_int (Z.of_nat (alen c) + 1) : mword 64))
        by (rewrite /T12 upd_ne; [exact HT11a4 | nz]).
      assert (HT12s2 : T12 !!! Regidx Rs2
                      = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64))
        by (rewrite /T12 upd_ne; [exact HT11s2 | nz]).
      assert (HT12s4 : T12 !!! Regidx Rs4 = sz1)
        by (rewrite /T12 upd_ne; [exact HT11s4 | nz]).
      assert (HT12s5 : T12 !!! Regidx Rs5 = proc_addr jp)
        by (rewrite /T12 upd_ne; [exact HT11s5 | nz]).
      assert (HT12s6 : T12 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /T12 upd_ne; [exact HT11s6 | nz]).
      assert (HT12s7 : T12 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64))
        by (rewrite /T12 upd_ne; [exact HT11s7 | nz]).
      assert (HT12s8 : T12 !!! Regidx Rs8 = (mword_of_int 32 : mword 64))
        by (rewrite /T12 upd_ne; [exact HT11s8 | nz]).
      assert (HT12s9 : T12 !!! Regidx Rs9 = pa_stk sp0 46)
        by (rewrite /T12 upd_ne; [exact HT11s9 | nz]).
      assert (HT12s10 : T12 !!! Regidx Rs10 = oldsz)
        by (rewrite /T12 upd_ne; [exact HT11s10 | nz]).
      assert (HT12s11 : T12 !!! Regidx Rs11 = pa_add av (8 * c))
        by (rewrite /T12 upd_ne; [exact HT11s11 | nz]).
      assert (Hpp248 : add_vec_int (mword_of_int (KXC + 0x246) : mword 64) 2
                       = mword_of_int (KXC + 0x248)) by pcw.
      iEval (rewrite Hpp248) in "Hpc".
      (* ---- +0x248: jal ra,copyout(a0=root,a1=sz1,a2=new sp,a3=avf c,
         a4=alen c+1). [sz1]'s MAXVA bound comes free from the loop
         invariant's OWN [um_covered sz1 P.(ud_um)] (no new premise, unlike
         the two register-tracking gaps): a covered size can never exceed
         [uvm_maxsz] by [proc_pt]'s own well-formedness. ---- *)
      iDestruct (proc_pt_wf_get with "Hpt") as %Hwf.
      pose proof (proc_pt_covered_maxsz P sz1 Hwf Hcov) as Hmax.
      unfold uvm_maxsz in Hmax.
      assert (Hsz1max38 : (uint sz1 <= 2 ^ 38)%Z).
      { rewrite uint_unsigned.
        change (2 ^ 38 - 8192)%Z with 274877898752%Z in Hmax.
        change (2 ^ 38)%Z with 274877906944%Z. lia. }
      assert (Htco238 : add_vec (mword_of_int (KXC + 0x248) : mword 64)
                           (sign_extend' 64 (mword_of_int 2083700 : mword 21))
                         = mword_of_int KernelSyms.copyout) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (KXC + 0x248)) Rra
                (mword_of_int 2083700 : mword 21) T12 (K - 68)%nat true
                ltac:(nz) ltac:(rdok)
                ltac:(rewrite Htco238; vm_compute; reflexivity)
                with "Hcg Hpc Hi248").
      iIntros (CID18 Hs18) "Hcg Hpc". iEval (rewrite Htco238) in "Hpc".
      pose (Z2 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KXC + 0x248) : mword 64) 4)]> T12).
      assert (HZ2ra : Z2 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KXC + 0x248) : mword 64) 4)
        by (rewrite /Z2; apply upd_eq).
      assert (HZ2a0 : Z2 !!! Regidx Ra0 = page_base P.(ud_root))
        by (rewrite /Z2 upd_ne; [exact HT12a0 | nz]).
      assert (HZ2a1 : Z2 !!! Regidx Ra1 = sz1)
        by (rewrite /Z2 upd_ne; [exact HT12a1 | nz]).
      assert (HZ2a4 : Z2 !!! Regidx Ra4 = (mword_of_int (Z.of_nat (alen c) + 1) : mword 64))
        by (rewrite /Z2 upd_ne; [exact HT12a4 | nz]).
      (* [Hargc] came back from the SECOND strlen call addressed at
         [Z1!!!Ra0] -- bridge through [avf c] to reach [Z2!!!Ra3]. *)
      assert (HZ2a3 : Z2 !!! Regidx Ra3 = avf c)
        by (rewrite /Z2 upd_ne; [exact HT12a3 | nz]).
      iEval (rewrite HZ1a0) in "Hargc".
      iEval (rewrite -HZ2a3) in "Hargc".
      (* [Hargc] covers the WHOLE buffer ([seq 0 (aslen c)]), but copyout
         only wants the string plus its NUL ([seq 0 (S (alen c))]) -- split
         off the prefix, hand that to copyout, and recombine once it comes
         back (its own contract: the source buffer is unchanged). *)
      assert (Hsplitlen : (S (alen c) <= aslen c)%nat) by lia.
      assert (Hsplit : seq 0 (aslen c)
                      = seq 0 (S (alen c)) ++ seq (S (alen c)) (aslen c - S (alen c))).
      { rewrite -seq_app. f_equal. lia. }
      iEval (rewrite Hsplit big_sepL_app) in "Hargc".
      iDestruct "Hargc" as "[Hargc1 Hargc2]".
      iApply (Copyout.wp_copyout_sconf ga Z2 P sz1 (S (alen c)) (afun c)
                (K - 68)%nat 0%nat true (proc_addr jp) C true
                ltac:(lia) HZ2a0 HZ2a1
                ltac:(rewrite HZ2a4; f_equal; lia)
                ltac:(change (2 ^ 64)%Z with 18446744073709551616%Z; lia)
                Hsz1max38 ltac:(lia)
                with "Hcg Hcnt Htext Hpc Hpt Hka Hargc1").
      iIntros (CID19 Hs19 T13 Pfinal2) "Hcg Hcnt Hpc Hpt Hargc1 %Hcs2 %Hextsz %Hco_res".
      iCombine "Hargc1 Hargc2" as "Hargc".
      iEval (rewrite -big_sepL_app -Hsplit) in "Hargc".
      (* ---- the page table: [uptd_ext_sz] transports [um_below]/[um_covered]
         across the call by name, same shape as the design note above
         ("copyout MOVES THE DESCRIPTOR AND THE INVARIANT SURVIVES BY
         NAME") -- no new lemma, just the two existing transport facts. ---- *)
      assert (Hext2 : uptd_ext P Pfinal2) by (eapply uptd_ext_sz_ext; exact Hextsz).
      assert (HbelowF2 : um_below sz1 Pfinal2.(ud_um))
        by (eapply um_below_ext_sz; [exact Hbelow | exact Hextsz]).
      assert (HcovF2 : um_covered sz1 Pfinal2.(ud_um)).
      { unfold um_covered.
        apply (um_covered_z_subseteq (bv_unsigned sz1) P.(ud_um) Pfinal2.(ud_um)).
        - destruct Hext2 as (_ & _ & Hsub). exact (subseteq_dom _ _ Hsub).
        - exact Hcov. }
      assert (HrootF2 : Pfinal2.(ud_root) = P.(ud_root))
        by (destruct Hext2 as (Hr & _ & _); exact Hr).
      assert (HtfpF2 : Pfinal2.(ud_tfp) = P.(ud_tfp))
        by (destruct Hext2 as (_ & Ht & _); exact Ht).
      assert (HT13sp : T13 !!! Regidx csp_rs1 = pa_stk sp0 68).
      { rewrite (callee_saved_lookup Hcs2 csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HT12sp. }
      assert (HT13s0 : T13 !!! Regidx Rs0 = sp0).
      { rewrite (callee_saved_lookup Hcs2 Rs0 ltac:(vm_compute; reflexivity)).
        exact HT12s0. }
      assert (HT13s1 : T13 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64)).
      { rewrite (callee_saved_lookup Hcs2 Rs1 ltac:(vm_compute; reflexivity)).
        exact HT12s1. }
      assert (HT13s2 : T13 !!! Regidx Rs2
                      = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64)).
      { rewrite (callee_saved_lookup Hcs2 Rs2 ltac:(vm_compute; reflexivity)).
        exact HT12s2. }
      assert (HT13s4 : T13 !!! Regidx Rs4 = sz1).
      { rewrite (callee_saved_lookup Hcs2 Rs4 ltac:(vm_compute; reflexivity)).
        exact HT12s4. }
      assert (HT13s5 : T13 !!! Regidx Rs5 = proc_addr jp).
      { rewrite (callee_saved_lookup Hcs2 Rs5 ltac:(vm_compute; reflexivity)).
        exact HT12s5. }
      assert (HT13s6 : T13 !!! Regidx Rs6 = page_base P.(ud_root)).
      { rewrite (callee_saved_lookup Hcs2 Rs6 ltac:(vm_compute; reflexivity)).
        exact HT12s6. }
      assert (HT13s7 : T13 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64)).
      { rewrite (callee_saved_lookup Hcs2 Rs7 ltac:(vm_compute; reflexivity)).
        exact HT12s7. }
      assert (HT13s8 : T13 !!! Regidx Rs8 = (mword_of_int 32 : mword 64)).
      { rewrite (callee_saved_lookup Hcs2 Rs8 ltac:(vm_compute; reflexivity)).
        exact HT12s8. }
      assert (HT13s9 : T13 !!! Regidx Rs9 = pa_stk sp0 46).
      { rewrite (callee_saved_lookup Hcs2 Rs9 ltac:(vm_compute; reflexivity)).
        exact HT12s9. }
      assert (HT13s10 : T13 !!! Regidx Rs10 = oldsz).
      { rewrite (callee_saved_lookup Hcs2 Rs10 ltac:(vm_compute; reflexivity)).
        exact HT12s10. }
      assert (HT13s11 : T13 !!! Regidx Rs11 = pa_add av (8 * c)).
      { rewrite (callee_saved_lookup Hcs2 Rs11 ltac:(vm_compute; reflexivity)).
        exact HT12s11. }
      assert (Hpc24c_ret : ret_pc (Z2 !!! Regidx Rra) = mword_of_int (KXC + 0x24c))
        by (rewrite HZ2ra; pcw).
      iEval (rewrite Hpc24c_ret) in "Hpc".
      (* ---- +0x24c: bltz a0,<fail> -- [Hco_res] already IS the comparison
         (copyout's own postcondition gives a0 = 0 or -1 directly), so no
         [zopz0zI_s]-vs-Z detour like the BLTU step needed; each arm closes
         the branch test by [vm_compute] on a now-CONCRETE a0. ---- *)
      destruct Hco_res as [Hcook | Hcofail].
      - (* ==== copyout succeeded: a0 = 0, fall through ==== *)
        iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KXC + 0x24c))
                  (mword_of_int 272 : mword 13) Ra0
                  T13 (K - 68)%nat true ltac:(nz)
                  ltac:(rewrite (rget_ne T13 Ra0 ltac:(nz)) Hcook; vm_compute; reflexivity)
                  with "Hcg Hpc Hi24c").
        iIntros (CID20 Hs20) "Hcg Hpc".
        assert (Hpp250 : add_vec_int (mword_of_int (KXC + 0x24c) : mword 64) 4
                         = mword_of_int (KXC + 0x250)) by pcw.
        iEval (rewrite Hpp250) in "Hpc".
        (* ---- +0x250: slli a5,s1,3 (a5 = 8c) ---- *)
        assert (Hc64 : (0 <= Z.of_nat c)%Z /\ (Z.of_nat c * 8 < 18446744073709551616)%Z)
          by lia.
        iApply (wp_slli_s_sconf (mword_of_int (KXC + 0x250)) Ra5 Rs1
                  (mword_of_int 3 : mword 6) (mword_of_int (8 * Z.of_nat c) : mword 64)
                  T13 (K - 68)%nat true ltac:(nz) ltac:(rdok)
                  ltac:(rewrite (rget_ne T13 Rs1 ltac:(nz)) HT13s1;
                        rewrite (ofile_slli3 (Z.of_nat c) (proj1 Hc64) ltac:(lia));
                        f_equal; lia)
                  with "Hcg Hpc Hi250").
        iIntros (CID22 Hs22) "Hcg Hpc".
        pose (U0 := <[Regidx Ra5 := regval_into_reg (mword_of_int (8 * Z.of_nat c) : mword 64)]> T13).
        assert (HU0a5 : U0 !!! Regidx Ra5 = (mword_of_int (8 * Z.of_nat c) : mword 64))
          by (rewrite /U0; apply upd_eq).
        assert (HU0s2 : U0 !!! Regidx Rs2
                        = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64))
          by (rewrite /U0 upd_ne; [exact HT13s2 | nz]).
        assert (HU0s1 : U0 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
          by (rewrite /U0 upd_ne; [exact HT13s1 | nz]).
        assert (HU0s9 : U0 !!! Regidx Rs9 = pa_stk sp0 46)
          by (rewrite /U0 upd_ne; [exact HT13s9 | nz]).
        assert (HU0s0 : U0 !!! Regidx Rs0 = sp0)
          by (rewrite /U0 upd_ne; [exact HT13s0 | nz]).
        assert (HU0s11 : U0 !!! Regidx Rs11 = pa_add av (8 * c))
          by (rewrite /U0 upd_ne; [exact HT13s11 | nz]).
        (* the rest of the invariant's registers, carried through the U-chain
           even though nothing between here and +0x268 reads them: the back
           edge re-establishes [kxc_at_21a] over ALL of them, and a fact
           omitted at one [pose] costs a scattered batch of asserts later
           rather than one line here (kexec.md's third instance of this). *)
        assert (HU0sp : U0 !!! Regidx csp_rs1 = pa_stk sp0 68)
          by (rewrite /U0 upd_ne; [exact HT13sp | nz]).
        assert (HU0s4 : U0 !!! Regidx Rs4 = sz1)
          by (rewrite /U0 upd_ne; [exact HT13s4 | nz]).
        assert (HU0s5 : U0 !!! Regidx Rs5 = proc_addr jp)
          by (rewrite /U0 upd_ne; [exact HT13s5 | nz]).
        assert (HU0s6 : U0 !!! Regidx Rs6 = page_base P.(ud_root))
          by (rewrite /U0 upd_ne; [exact HT13s6 | nz]).
        assert (HU0s7 : U0 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64))
          by (rewrite /U0 upd_ne; [exact HT13s7 | nz]).
        assert (HU0s8 : U0 !!! Regidx Rs8 = (mword_of_int 32 : mword 64))
          by (rewrite /U0 upd_ne; [exact HT13s8 | nz]).
        assert (HU0s10 : U0 !!! Regidx Rs10 = oldsz)
          by (rewrite /U0 upd_ne; [exact HT13s10 | nz]).
        assert (Hpp254 : add_vec_int (mword_of_int (KXC + 0x250) : mword 64) 4
                         = mword_of_int (KXC + 0x254)) by pcw.
        iEval (rewrite Hpp254) in "Hpc".
        (* ---- +0x254: c.add a5,a5,s9 (a5 = pa_stk sp0 46 + 8c = pa_stk sp0 (46-c)) ---- *)
        iApply (wp_cadd_s_sconf (mword_of_int (KXC + 0x254)) Ra5 Rs9
                  U0 (K - 68)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi254").
        iIntros (CID23 Hs23) "Hcg Hpc".
        pose (U1 := <[Regidx Ra5 := regval_into_reg
                      (add_vec (rget U0 Ra5) (rget U0 Rs9))]> U0).
        assert (HU1a5 : U1 !!! Regidx Ra5 = pa_stk sp0 (46 - c)).
        { rewrite /U1 upd_eq (rget_ne U0 Ra5 ltac:(nz)) (rget_ne U0 Rs9 ltac:(nz))
            HU0a5 HU0s9.
          rewrite add_vec64_comm. apply kxc_pa_stk_add. lia. }
        assert (HU1s2 : U1 !!! Regidx Rs2
                        = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64))
          by (rewrite /U1 upd_ne; [exact HU0s2 | nz]).
        assert (HU1s1 : U1 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
          by (rewrite /U1 upd_ne; [exact HU0s1 | nz]).
        assert (HU1s0 : U1 !!! Regidx Rs0 = sp0)
          by (rewrite /U1 upd_ne; [exact HU0s0 | nz]).
        assert (HU1s11 : U1 !!! Regidx Rs11 = pa_add av (8 * c))
          by (rewrite /U1 upd_ne; [exact HU0s11 | nz]).
        assert (HU1sp : U1 !!! Regidx csp_rs1 = pa_stk sp0 68)
          by (rewrite /U1 upd_ne; [exact HU0sp | nz]).
        assert (HU1s4 : U1 !!! Regidx Rs4 = sz1)
          by (rewrite /U1 upd_ne; [exact HU0s4 | nz]).
        assert (HU1s5 : U1 !!! Regidx Rs5 = proc_addr jp)
          by (rewrite /U1 upd_ne; [exact HU0s5 | nz]).
        assert (HU1s6 : U1 !!! Regidx Rs6 = page_base P.(ud_root))
          by (rewrite /U1 upd_ne; [exact HU0s6 | nz]).
        assert (HU1s7 : U1 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64))
          by (rewrite /U1 upd_ne; [exact HU0s7 | nz]).
        assert (HU1s8 : U1 !!! Regidx Rs8 = (mword_of_int 32 : mword 64))
          by (rewrite /U1 upd_ne; [exact HU0s8 | nz]).
        assert (HU1s9 : U1 !!! Regidx Rs9 = pa_stk sp0 46)
          by (rewrite /U1 upd_ne; [exact HU0s9 | nz]).
        assert (HU1s10 : U1 !!! Regidx Rs10 = oldsz)
          by (rewrite /U1 upd_ne; [exact HU0s10 | nz]).
        assert (Hpp256 : add_vec_int (mword_of_int (KXC + 0x254) : mword 64) 2
                         = mword_of_int (KXC + 0x256)) by pcw.
        iEval (rewrite Hpp256) in "Hpc".
        (* ---- +0x256: sd s2,0(a5) -- ustack[c] := kxc_sp(...)(S c); peel
           the ONE not-yet-written slot off [Hust]'s opaque [stack_own],
           write it, fold it back onto [Hwr]'s already-written prefix. ---- *)
        assert (Hsplit33 : (33 - c = (32 - c) + 1)%nat) by lia.
        iEval (rewrite Hsplit33 (stack_own_app (pa_stk sp0 13) (32 - c) 1)) in "Hust".
        iDestruct "Hust" as "[Hust1 Hust2]".
        iEval (rewrite stack_own_1) in "Hust2".
        iDestruct "Hust2" as (wold) "Hslot".
        assert (Haddreq : pa_stk (pa_stk sp0 13) (32 - c) = pa_stk sp0 (45 - c))
          by (rewrite pa_stk_assoc; f_equal; lia).
        iEval (rewrite Haddreq) in "Hslot".
        assert (Haddreq2 : pa_stk (pa_stk sp0 (45 - c)) 1 = pa_stk sp0 (46 - c))
          by (rewrite pa_stk_assoc; f_equal; lia).
        iEval (rewrite Haddreq2) in "Hslot".
        assert (Hz0imm256 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                           = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
        assert (Hstoreaddr : add_vec (U1 !!! Regidx Ra5)
                                (sign_extend' 64 (mword_of_int 0 : mword 12))
                            = pa_stk sp0 (46 - c)).
        { rewrite HU1a5 Hz0imm256. exact (avi0 (pa_stk sp0 (46 - c))). }
        iEval (rewrite -Hstoreaddr) in "Hslot".
        iApply (wp_sd_s_sconf (mword_of_int (KXC + 0x256)) Rs2 Ra5
                  (mword_of_int 0 : mword 12) U1 (K - 68)%nat wold true
                  with "Hcg Hpc Hi256 Hslot").
        iIntros (CID24 Hs24) "Hcg Hpc Hslot".
        iEval (rewrite Hstoreaddr) in "Hslot".
        (* [storeval] is [rget m rs2] computed ONCE, at the ENTRY hart
           ([CID23], the hart active when [wp_sd_s_sconf] was called) --
           it stays pinned there regardless of which hart the continuation
           resumes on ([CID24]), so the rewrite needs that CID named
           explicitly rather than picking up the ambient (wrong) one. *)
        iEval (rewrite (rget_ne (CID := CID23) U1 Rs2 ltac:(nz)) HU1s2) in "Hslot".
        (* [Hust1] (depth [32-c]) is exactly index [S c]'s own "not yet
           written" region -- rename only. [Hslot] folds onto [Hwr]'s
           already-written prefix via [seq_S], extending it to [S c]. *)
        iAssert ([∗ list] j ∈ seq 0 (S c), pa_stk sp0 (46 - j) ↦₈
                   (mword_of_int (kxc_sp (uint sz1) alen (S j)) : mword 64))%I
          with "[Hwr Hslot]" as "Hwr".
        { rewrite seq_S big_sepL_app big_sepL_singleton. iFrame. }
        assert (Hpp25a : add_vec_int (mword_of_int (KXC + 0x256) : mword 64) 4
                         = mword_of_int (KXC + 0x25a)) by pcw.
        iEval (rewrite Hpp25a) in "Hpc".
        (* ---- +0x25a: c.addi s1,s1,1 (s1 = c+1, the loop's own increment) ---- *)
        iApply (wp_caddi_s_sconf (mword_of_int (KXC + 0x25a)) Rs1
                  (mword_of_int 1 : mword 6) U1 (K - 68)%nat true
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi25a").
        iIntros (CID25 Hs25) "Hcg Hpc".
        pose (U2 := <[Regidx Rs1 := regval_into_reg
                      (add_vec (rget U1 Rs1)
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> U1).
        assert (HU2s1 : U2 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c + 1) : mword 64)).
        { rewrite /U2 upd_eq (rget_ne U1 Rs1 ltac:(nz)) HU1s1.
          apply bv_eq. rewrite add_vec64_unsigned moi64_unsigned.
          assert (H1c : bv_unsigned
                          (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)) : mword 64)
                        = 1%Z) by (vm_compute; reflexivity).
          rewrite H1c moi64_unsigned. unfold bv_wrap.
          rewrite (Z.mod_small (Z.of_nat c) 18446744073709551616); [| lia].
          rewrite (Z.mod_small (Z.of_nat c + 1) 18446744073709551616); [| lia].
          reflexivity. }
        assert (HU2s0 : U2 !!! Regidx Rs0 = sp0)
          by (rewrite /U2 upd_ne; [exact HU1s0 | nz]).
        assert (HU2s2 : U2 !!! Regidx Rs2
                        = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64))
          by (rewrite /U2 upd_ne; [exact HU1s2 | nz]).
        assert (HU2s9 : U2 !!! Regidx Rs9 = pa_stk sp0 46)
          by (rewrite /U2 upd_ne; [exact HU0s9 | nz]).
        assert (HU2s11 : U2 !!! Regidx Rs11 = pa_add av (8 * c))
          by (rewrite /U2 upd_ne; [exact HU1s11 | nz]).
        assert (HU2sp : U2 !!! Regidx csp_rs1 = pa_stk sp0 68)
          by (rewrite /U2 upd_ne; [exact HU1sp | nz]).
        assert (HU2s4 : U2 !!! Regidx Rs4 = sz1)
          by (rewrite /U2 upd_ne; [exact HU1s4 | nz]).
        assert (HU2s5 : U2 !!! Regidx Rs5 = proc_addr jp)
          by (rewrite /U2 upd_ne; [exact HU1s5 | nz]).
        assert (HU2s6 : U2 !!! Regidx Rs6 = page_base P.(ud_root))
          by (rewrite /U2 upd_ne; [exact HU1s6 | nz]).
        assert (HU2s7 : U2 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64))
          by (rewrite /U2 upd_ne; [exact HU1s7 | nz]).
        assert (HU2s8 : U2 !!! Regidx Rs8 = (mword_of_int 32 : mword 64))
          by (rewrite /U2 upd_ne; [exact HU1s8 | nz]).
        assert (HU2s10 : U2 !!! Regidx Rs10 = oldsz)
          by (rewrite /U2 upd_ne; [exact HU1s10 | nz]).
        assert (Hpp25c : add_vec_int (mword_of_int (KXC + 0x25a) : mword 64) 2
                         = mword_of_int (KXC + 0x25c)) by pcw.
        iEval (rewrite Hpp25c) in "Hpc".
        (* ---- +0x25c: addi a5,s11,8 (a5 = &argv[c+1]) ---- *)
        iApply (wp_addi4_s_sconf (mword_of_int (KXC + 0x25c)) Ra5 Rs11
                  (mword_of_int 8 : mword 12) U2 (K - 68)%nat true
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi25c").
        iIntros (CID26' Hs26') "Hcg Hpc".
        pose (U3 := <[Regidx Ra5 := regval_into_reg
                      (add_vec (rget U2 Rs11) (sign_extend' 64 (mword_of_int 8 : mword 12)))]> U2).
        assert (HU3a5 : U3 !!! Regidx Ra5 = pa_add av (8 * S c)).
        { rewrite /U3 upd_eq (rget_ne (CID := CID26') U2 Rs11 ltac:(nz)) HU2s11.
          assert (Hz8se : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
                         = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
          rewrite Hz8se.
          change (add_vec (pa_add av (8 * c)) (mword_of_int 8 : mword 64))
            with (pa_add (pa_add av (8 * c)) 8).
          rewrite pa_add_add.
          assert (Heq89a : (8 * c + 8 = 8 * S c)%nat) by lia.
          rewrite Heq89a. reflexivity. }
        assert (HU3s0 : U3 !!! Regidx Rs0 = sp0)
          by (rewrite /U3 upd_ne; [exact HU2s0 | nz]).
        assert (HU3s11 : U3 !!! Regidx Rs11 = pa_add av (8 * c))
          by (rewrite /U3 upd_ne; [exact HU2s11 | nz]).
        assert (HU3sp : U3 !!! Regidx csp_rs1 = pa_stk sp0 68)
          by (rewrite /U3 upd_ne; [exact HU2sp | nz]).
        assert (HU3s1 : U3 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c + 1) : mword 64))
          by (rewrite /U3 upd_ne; [exact HU2s1 | nz]).
        assert (HU3s2 : U3 !!! Regidx Rs2
                        = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64))
          by (rewrite /U3 upd_ne; [exact HU2s2 | nz]).
        assert (HU3s4 : U3 !!! Regidx Rs4 = sz1)
          by (rewrite /U3 upd_ne; [exact HU2s4 | nz]).
        assert (HU3s5 : U3 !!! Regidx Rs5 = proc_addr jp)
          by (rewrite /U3 upd_ne; [exact HU2s5 | nz]).
        assert (HU3s6 : U3 !!! Regidx Rs6 = page_base P.(ud_root))
          by (rewrite /U3 upd_ne; [exact HU2s6 | nz]).
        assert (HU3s7 : U3 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64))
          by (rewrite /U3 upd_ne; [exact HU2s7 | nz]).
        assert (HU3s8 : U3 !!! Regidx Rs8 = (mword_of_int 32 : mword 64))
          by (rewrite /U3 upd_ne; [exact HU2s8 | nz]).
        assert (HU3s9 : U3 !!! Regidx Rs9 = pa_stk sp0 46)
          by (rewrite /U3 upd_ne; [exact HU2s9 | nz]).
        assert (HU3s10 : U3 !!! Regidx Rs10 = oldsz)
          by (rewrite /U3 upd_ne; [exact HU2s10 | nz]).
        assert (Hpp260 : add_vec_int (mword_of_int (KXC + 0x25c) : mword 64) 4
                         = mword_of_int (KXC + 0x260)) by pcw.
        iEval (rewrite Hpp260) in "Hpc".
        (* ---- +0x260: sd a5,3584(s0) -- spill argv := &argv[c+1] ---- *)
        assert (Hargvslot260 : add_vec (U3 !!! Regidx Rs0)
                                  (sign_extend' 64 (mword_of_int 3584 : mword 12))
                              = pa_stk sp0 64).
        { rewrite HU3s0. apply kxc_argv_slot. }
        iEval (rewrite -Hargvslot260) in "Hf64".
        iApply (wp_sd_s_sconf (mword_of_int (KXC + 0x260)) Ra5 Rs0
                  (mword_of_int 3584 : mword 12) U3 (K - 68)%nat (pa_add av (8 * c)) true
                  with "Hcg Hpc Hi260 Hf64").
        iIntros (CID27' Hs27') "Hcg Hpc Hf64".
        iEval (rewrite Hargvslot260) in "Hf64".
        iEval (rewrite (rget_ne (CID := CID26') U3 Ra5 ltac:(nz)) HU3a5) in "Hf64".
        assert (Hpp264 : add_vec_int (mword_of_int (KXC + 0x260) : mword 64) 4
                         = mword_of_int (KXC + 0x264)) by pcw.
        iEval (rewrite Hpp264) in "Hpc".
        (* ---- +0x264: ld a0,8(s11) -- a0 = avf (S c), next iteration's
           liveness test. [s11] still holds the OLD &argv[c] (never
           reassigned after +0x22e); [Hargv]'s own [S c] entry, extract/
           use/restore. ---- *)
        iDestruct (big_sepL_lookup_acc _ _ (S c) (S c) Hlc1 with "Hargv") as "[Han Hargvback2]".
        assert (Hz8imm : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
                        = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
        assert (Hnextaddr : add_vec (U3 !!! Regidx Rs11)
                               (sign_extend' 64 (mword_of_int 8 : mword 12))
                           = pa_add av (8 * S c)).
        { rewrite HU3s11 Hz8imm.
          change (add_vec (pa_add av (8 * c)) (mword_of_int 8 : mword 64))
            with (pa_add (pa_add av (8 * c)) 8).
          rewrite pa_add_add.
          assert (Heq89a : (8 * c + 8 = 8 * S c)%nat) by lia.
          rewrite Heq89a. reflexivity. }
        iEval (rewrite -Hnextaddr) in "Han".
        iApply (wp_ld_s_sconf (mword_of_int (KXC + 0x264)) Ra0 Rs11
                  (mword_of_int 8 : mword 12) U3 (K - 68)%nat (avf (S c)) true
                  (dqm := dqa) ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi264 Han").
        iIntros (CID28' Hs28') "Hcg Hpc Han". iEval (rewrite Hnextaddr) in "Han".
        iDestruct ("Hargvback2" with "Han") as "Hargv".
        pose (U4 := <[Regidx Ra0 := regval_into_reg (avf (S c))]> U3).
        assert (HU4a0 : U4 !!! Regidx Ra0 = avf (S c)) by (rewrite /U4; apply upd_eq).
        assert (HU4sp : U4 !!! Regidx csp_rs1 = pa_stk sp0 68)
          by (rewrite /U4 upd_ne; [exact HU3sp | nz]).
        assert (HU4s0 : U4 !!! Regidx Rs0 = sp0)
          by (rewrite /U4 upd_ne; [exact HU3s0 | nz]).
        assert (HU4s1 : U4 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c + 1) : mword 64))
          by (rewrite /U4 upd_ne; [exact HU3s1 | nz]).
        assert (HU4s2 : U4 !!! Regidx Rs2
                        = (mword_of_int (kxc_sp (uint sz1) alen (S c)) : mword 64))
          by (rewrite /U4 upd_ne; [exact HU3s2 | nz]).
        assert (HU4s4 : U4 !!! Regidx Rs4 = sz1)
          by (rewrite /U4 upd_ne; [exact HU3s4 | nz]).
        assert (HU4s5 : U4 !!! Regidx Rs5 = proc_addr jp)
          by (rewrite /U4 upd_ne; [exact HU3s5 | nz]).
        assert (HU4s6 : U4 !!! Regidx Rs6 = page_base P.(ud_root))
          by (rewrite /U4 upd_ne; [exact HU3s6 | nz]).
        assert (HU4s7 : U4 !!! Regidx Rs7 = (mword_of_int (uint sz1 - 4096) : mword 64))
          by (rewrite /U4 upd_ne; [exact HU3s7 | nz]).
        assert (HU4s8 : U4 !!! Regidx Rs8 = (mword_of_int 32 : mword 64))
          by (rewrite /U4 upd_ne; [exact HU3s8 | nz]).
        assert (HU4s9 : U4 !!! Regidx Rs9 = pa_stk sp0 46)
          by (rewrite /U4 upd_ne; [exact HU3s9 | nz]).
        assert (HU4s10 : U4 !!! Regidx Rs10 = oldsz)
          by (rewrite /U4 upd_ne; [exact HU3s10 | nz]).
        (* ---- the frame and the resource bundle, both now at [S c]: the
           ustack's unwritten tail is [Hust1] (depth [32-c], i.e. [33-(S c)]),
           its written prefix [Hwr] has just grown to [S c], and slot 64 has
           been bumped to [pa_add av (8 * S c)].  All three arms below hand
           this SAME bundle on -- the two that stay in the function to the
           caller, the MAXARG one to [kxc_c_exit_m1]. ---- *)
        assert (Hdepth : (33 - S c = 32 - c)%nat) by lia.
        iEval (rewrite -Hdepth) in "Hust1".
        iEval (rewrite HZ2a3) in "Hargc".
        iDestruct ("Hargsback" with "Hargc") as "Hargs".
        iDestruct (kxc_frameC_intro sp0 ra0 s00 s10 s20 pv av
                     w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 w65 w68 (S c) sz1 alen
                     with "Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10 Hf11 Hf12 Hf13
                           Hust1 Hwr Hph Hf64 Hf65 Hf66 Hf67 Hf68") as "Hframe".
        iDestruct (kxc_c_res_intro jp bn gfs ga gf cov logstart bmapstart inodestart
                     size used2 plen pfun na avf aslen afun pidv V dqb dqs dqa
                     sp0 ra0 s00 s10 s20 pv av
                     w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef Pfinal2 (S c) sz1 alen
                     with "Hirs Hbm Hins Hbits Hbs Hka Hpt Hpriv Hpath Hargv Hargs
                           Helf Hframe") as "Hres".
        (* the three shared bridges out of [Pfinal2] and the [S c] spelling *)
        assert (HScz : Z.of_nat (S c) = (Z.of_nat c + 1)%Z) by lia.
        assert (HU4s6' : U4 !!! Regidx Rs6 = page_base Pfinal2.(ud_root))
          by (rewrite HrootF2; exact HU4s6).
        assert (HU4s1' : U4 !!! Regidx Rs1
                         = (mword_of_int (Z.of_nat (S c)) : mword 64))
          by (rewrite HScz; exact HU4s1).
        assert (HtfpS : ud_tfp Pfinal2 = ud_tfp (pv_upt V))
          by (rewrite HtfpF2; exact HPtfp).
        (* ---- +0x268: c.beqz a0,+0x272 -- argv[c+1] == 0 ends the loop ---- *)
        assert (Hcreg268 : creg2reg_idx (Cregidx (mword_of_int 2)) = Regidx Ra0)
          by (vm_compute; reflexivity).
        assert (Htgt272' : add_vec (mword_of_int (KXC + 0x268) : mword 64)
                             (sign_extend' 64 (sign_extend' 13
                                (concat_vec (mword_of_int 5 : mword 8) ('b"0"))))
                           = mword_of_int (KXC + 0x272)) by pcw.
        destruct (decide (avf (S c) = (mword_of_int 0 : mword 64))) as [Hz1 | Hnz1].
        * (* ==== argv[c+1] = 0: the loop's NATURAL exit, into +0x272 ==== *)
          iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KXC + 0x268))
                    (mword_of_int 5 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                    U4 (K - 68)%nat true Hcreg268 ltac:(nz)
                    ltac:(rewrite (rget_ne U4 Ra0 ltac:(nz)) HU4a0 Hz1;
                          vm_compute; reflexivity)
                    ltac:(rewrite Htgt272'; vm_compute; reflexivity)
                    with "Hcg Hpc Hi268").
          iIntros (CID29 Hs29). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htgt272') in "Hpc".
          iDestruct (cpu_own_transport CID19 CID29 0%nat true (proc_addr jp) C true
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          assert (Hcr29 : true = false \/ proc_addr jp = zero_reg ->
                           (CID29 : CPU) = (CID0 : CPU)) by wp_next_chain.
          iDestruct (wp_next_retarget CID0 CID29 true (proc_addr jp) _ Hcr29
                       with "Hcont") as "Hcont".
          iSpecialize ("Hout" $! CID29 with "[%]"); [wp_next_chain |].
          iApply ("Hout" $! U4 Pfinal2 with "[Hpc Hcg Hcnt Hres] Hcont").
          iRight. rewrite /kxc_at_272.
          iSplitR.
          { iPureIntro. split_and!;
              [ exact HU4sp | exact HU4s0 | exact HU4s1' | exact HU4s2
              | exact HU4s4 | exact HU4s5 | exact HU4s6' | exact HU4s7
              | exact HU4s8 | exact HU4s9 | exact HU4s10]. }
          iSplitR.
          { iPureIntro. split_and!; [lia | lia | exact Hz1 | exact HspokS]. }
          iSplitR.
          { iPureIntro. split_and!; [exact HtfpS | exact HbelowF2 | exact HcovF2]. }
          iSplitL "Hpc"; [iExact "Hpc" |]. iSplitL "Hcg"; [iExact "Hcg" |].
          iSplitL "Hcnt"; [iExact "Hcnt" | iExact "Hres"].
        * (* ==== argv[c+1] <> 0: fall through to the MAXARG test ==== *)
          iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KXC + 0x268))
                    (mword_of_int 5 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                    U4 (K - 68)%nat true Hcreg268 ltac:(nz)
                    ltac:(rewrite (rget_ne U4 Ra0 ltac:(nz)) HU4a0;
                          apply eq_vec64_false; rewrite zero_reg64; exact Hnz1)
                    with "Hcg Hpc Hi268").
          iIntros (CID29 Hs29) "Hcg Hpc".
          assert (Hpp26a : add_vec_int (mword_of_int (KXC + 0x268) : mword 64) 2
                           = mword_of_int (KXC + 0x26a)) by pcw.
          iEval (rewrite Hpp26a) in "Hpc".
          (* ---- +0x26a: bne s1,s8,+0x21a -- taken (loop back) unless the
             counter has reached MAXARG.  [s1] is [c+1] and [s8] the [li s8,32]
             constant, both far below 2^64, so the word disequality is the
             [nat] one and the branch decides [S c < 32] exactly. ---- *)
          assert (Htgt21a' : add_vec (mword_of_int (KXC + 0x26a) : mword 64)
                               (sign_extend' 64 (mword_of_int 8112 : mword 13))
                             = mword_of_int (KXC + 0x21a)) by pcw.
          destruct (Nat.eq_dec (S c) 32) as [Hmaxarg | Hnomax].
          -- (* ==== argc = MAXARG: fall through into the +0x26e stub ==== *)
             assert (Heq32 : (mword_of_int (Z.of_nat c + 1) : mword 64)
                             = mword_of_int 32) by (rewrite -HScz Hmaxarg; reflexivity).
             iApply (wp_bne_fall_s_sconf (mword_of_int (KXC + 0x26a))
                       (mword_of_int 8112 : mword 13) Rs8 Rs1
                       U4 (K - 68)%nat true ltac:(nz) ltac:(nz)
                       ltac:(rewrite (rget_ne U4 Rs1 ltac:(nz)) (rget_ne U4 Rs8 ltac:(nz))
                                     HU4s1 HU4s8 Heq32;
                             vm_compute; reflexivity)
                       with "Hcg Hpc Hi26a").
             iIntros (CID30 Hs30) "Hcg Hpc".
             assert (Hpp26e : add_vec_int (mword_of_int (KXC + 0x26a) : mword 64) 4
                              = mword_of_int (KXC + 0x26e)) by pcw.
             iEval (rewrite Hpp26e) in "Hpc".
             iDestruct (cpu_own_transport CID19 CID30 0%nat true (proc_addr jp) C true
                          ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
             assert (Hcr30 : true = false \/ proc_addr jp = zero_reg ->
                              (CID30 : CPU) = (CID0 : CPU)) by wp_next_chain.
             iDestruct (wp_next_retarget CID0 CID30 true (proc_addr jp) _ Hcr30
                          with "Hcont") as "Hcont".
             iApply (kxc_c_exit_m1 (CID0 := CID30) jp bn gfs ga gf cov logstart
                       bmapstart inodestart size used2 plen pfun na avf alen aslen
                       afun pidv V dqb dqs dqa m U4 K C sp0 ra0 s00 s10 s20 pv av
                       w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef Pfinal2 sz1 (S c) 0x26e
                       (sign_extend' 21 (concat_vec (mword_of_int 1971 : mword 11) ('b"0")))
                       ltac:(unfold K_kexec; lia) ltac:(lia) Hal
                       Hmsp Hmra Hms0 Hms1 Hms2 Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11
                       Hmw12 Hmw13 HU4sp HU4s4 HU4s6' HbelowF2 HcovF2 ltac:(pcw)
                       with "Htext Hi26e Hi270 Hpc Hcg Hcnt Hres Hcont").
          -- (* ==== argc < MAXARG: the BACK EDGE, to +0x21a at [S c] ==== *)
             assert (Hne32 : (mword_of_int (Z.of_nat c + 1) : mword 64)
                             <> mword_of_int 32).
             { intro Heq. apply (f_equal (@bv_unsigned 64)) in Heq.
               rewrite !moi64_unsigned in Heq. unfold bv_wrap in Heq.
               change (bv_modulus 64) with 18446744073709551616%Z in Heq.
               rewrite !Z.mod_small in Heq; lia. }
             iApply (wp_bne_taken_s_sconf (mword_of_int (KXC + 0x26a))
                       (mword_of_int 8112 : mword 13) Rs8 Rs1
                       U4 (K - 68)%nat true ltac:(nz) ltac:(nz)
                       ltac:(rewrite (rget_ne U4 Rs1 ltac:(nz)) (rget_ne U4 Rs8 ltac:(nz))
                                     HU4s1 HU4s8;
                             apply neq_vec64_true; exact Hne32)
                       ltac:(rewrite Htgt21a'; vm_compute; reflexivity)
                       with "Hcg Hpc Hi26a").
             iIntros (CID30 Hs30). iApply bi.later_intro. iIntros "Hcg Hpc".
             iEval (rewrite Htgt21a') in "Hpc".
             iDestruct (cpu_own_transport CID19 CID30 0%nat true (proc_addr jp) C true
                          ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
             assert (Hcr30 : true = false \/ proc_addr jp = zero_reg ->
                              (CID30 : CPU) = (CID0 : CPU)) by wp_next_chain.
             iDestruct (wp_next_retarget CID0 CID30 true (proc_addr jp) _ Hcr30
                          with "Hcont") as "Hcont".
             iSpecialize ("Hout" $! CID30 with "[%]"); [wp_next_chain |].
             iApply ("Hout" $! U4 Pfinal2 with "[Hpc Hcg Hcnt Hres] Hcont").
             iLeft. rewrite /kxc_at_21a.
             iSplitR.
             { iPureIntro. split_and!;
                 [ exact HU4sp | exact HU4s0 | exact HU4s1' | exact HU4a0
                 | exact HU4s2 | exact HU4s4 | exact HU4s5 | exact HU4s6'
                 | exact HU4s7 | exact HU4s8 | exact HU4s9 | exact HU4s10]. }
             iSplitR.
             { iPureIntro. split_and!; [lia | lia | exact Hnz1 | exact HspokS]. }
             iSplitR.
             { iPureIntro. split_and!; [exact HtfpS | exact HbelowF2 | exact HcovF2]. }
             iSplitL "Hpc"; [iExact "Hpc" |]. iSplitL "Hcg"; [iExact "Hcg" |].
             iSplitL "Hcnt"; [iExact "Hcnt" | iExact "Hres"].
      - (* ==== copyout failed: a0 = -1, into the +0x35c stub and thence the
           shared -1 tail.  The frame is untouched at [c] (the ustack write
           is the NEXT instruction, +0x250), but the page table is copyout's
           [Pfinal2] now, so the connector takes it -- its [ud_root] and the
           two coverage facts came across by name just above. ==== *)
        assert (Hcmp_true35c : zopz0zI_s (rget T13 Ra0) zero_reg = true)
          by (rewrite (rget_ne T13 Ra0 ltac:(nz)) Hcofail; vm_compute; reflexivity).
        assert (Htgt35c : add_vec (mword_of_int (KXC + 0x24c) : mword 64)
                            (sign_extend' 64 (mword_of_int 272 : mword 13))
                          = mword_of_int (KXC + 0x35c)) by pcw.
        iApply (wp_blt_x0_taken_s_sconf (mword_of_int (KXC + 0x24c))
                  (mword_of_int 272 : mword 13) Ra0
                  T13 (K - 68)%nat true ltac:(nz) Hcmp_true35c
                  ltac:(rewrite Htgt35c; vm_compute; reflexivity)
                  with "Hcg Hpc Hi24c").
        iIntros (CID21 Hs21). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htgt35c) in "Hpc".
        (* [Hargc] is addressed at [Z2 !!! Ra3] (copyout's own source
           argument); back onto [avf c] before [Hargsback] will take it. *)
        iEval (rewrite HZ2a3) in "Hargc".
        iDestruct ("Hargsback" with "Hargc") as "Hargs".
        assert (HT13s6' : T13 !!! Regidx Rs6 = page_base Pfinal2.(ud_root))
          by (rewrite HrootF2; exact HT13s6).
        iDestruct (kxc_frameC_intro sp0 ra0 s00 s10 s20 pv av
                     w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 w65 w68 c sz1 alen
                     with "Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10 Hf11 Hf12 Hf13
                           Hust Hwr Hph Hf64 Hf65 Hf66 Hf67 Hf68") as "Hframe".
        iDestruct (kxc_c_res_intro jp bn gfs ga gf cov logstart bmapstart inodestart
                     size used2 plen pfun na avf aslen afun pidv V dqb dqs dqa
                     sp0 ra0 s00 s10 s20 pv av
                     w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef Pfinal2 c sz1 alen
                     with "Hirs Hbm Hins Hbits Hbs Hka Hpt Hpriv Hpath Hargv Hargs
                           Helf Hframe") as "Hres".
        iDestruct (cpu_own_transport CID19 CID21 0%nat true (proc_addr jp) C true
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        assert (Hcr21 : true = false \/ proc_addr jp = zero_reg ->
                         (CID21 : CPU) = (CID0 : CPU)) by wp_next_chain.
        iDestruct (wp_next_retarget CID0 CID21 true (proc_addr jp) _ Hcr21
                     with "Hcont") as "Hcont".
        iApply (kxc_c_exit_m1 (CID0 := CID21) jp bn gfs ga gf cov logstart
                  bmapstart inodestart size used2 plen pfun na avf alen aslen afun
                  pidv V dqb dqs dqa m T13 K C sp0 ra0 s00 s10 s20 pv av
                  w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef Pfinal2 sz1 c 0x35c
                  (sign_extend' 21 (concat_vec (mword_of_int 1852 : mword 11) ('b"0")))
                  ltac:(unfold K_kexec; lia) ltac:(lia) Hal
                  Hmsp Hmra Hms0 Hms1 Hms2 Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11
                  Hmw12 Hmw13 HT13sp HT13s4 HT13s6' HbelowF2 HcovF2 ltac:(pcw)
                  with "Htext Hi35c Hi35e Hpc Hcg Hcnt Hres Hcont").
  Qed.

End KexecCLoop.

End KexecCProof.
