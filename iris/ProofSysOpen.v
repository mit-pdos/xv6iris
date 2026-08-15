(* ProofSysOpen.v -- sys_open's WALK, and the seal.

   THE JOIN AT +0x4a IS ENTERED FROM TWO PLACES (the O_CREATE arm's
   [create] and the else arm's [namei] + [ilock] + the T_DIR refusal), so a
   single straight-through walk cannot be written: the function is proved as
   BLOCK LEMMAS that hand each other one linear exit continuation.

     [so_cont]        the syscall's exit continuation, named once -- five
                      lemmas take it and none of them re-spells it
     [so_tail_pub]    +0xb8: ARM S, and THE PUBLICATION.  [so_tail_s] runs
                      first (its [iunlock] is what hands the travelling
                      share back), and only THEN can [so_publish] mint the
                      payload -- see [ProofSysOpenParts]'s banner: a parked
                      reference and its share are pinned to one fraction by
                      [inode_held_short]'s [qt = qi + Q], so the publisher
                      can only publish at a moment when it holds BOTH.
     [so_stores]      +0x88 .. +0xb4 and the +0x14e itrunc block: the
                      [f->ip] store, the two omode bytes, the O_TRUNC test.
                      Entered from the FD_INODE fall-through AND from the
                      +0x140 FD_DEVICE block's [c.j], which is why it is a
                      lemma and not a straight line.
     [so_alloc]       +0x5e .. +0x84 and the +0x140 block: filealloc,
                      fdalloc, the type test and the two typed store pairs.
                      Entered from the T_DEVICE branch's BOTH arms.
     [so_join]        +0x4a .. +0x5a and ARM D-FAIL.

   THE FUNCTOR takes the seven callees the body applies below the join and
   instantiates [SysOpenTails] internally -- the tails are a parts layer and
   the seal happens here.

   Design: claude-notes/projects/fs-sysfile.md, S7-open. *)
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
Require Import StackOwn StackBytes.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfVc WpSconfBtype.
Require Import WpSmodeIntr WpSmodeHalf.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import PanicStub.
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
Require Import DirView.
Require Import DirLinks.
Require Import FileInvDefs.
Require Import FileInv.
Require Import ProcInv.
Require Import IregLinkNz.
Require Import SpecEndOp.
Require Import SpecIput.
Require Import SpecIunlock.
Require Import SpecIunlockput.
Require Import SpecFileclose.
Require Import SpecFilealloc.
Require Import SpecFdalloc.
Require Import SpecItrunc.
Require Import SpecCreate.
Require Import CodeSysOpen.
Require Import SpecSysOpen.
Require Import SysOpenBudget.
Require Import ProofSysOpenParts.
Require Import ProofSysOpenTails.
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

(* [neq_vec] is [negb (eq_vec ...)], so the two BNE premises are the two
   readings of the type cluster's [so_ty_eq] / [so_ty_ne]. *)
Lemma so_neq_of_eq (x y : mword 64) : eq_vec x y = true -> neq_vec x y = false.
Proof. unfold neq_vec. intro H. rewrite H. reflexivity. Qed.

Lemma so_neq_of_ne (x y : mword 64) : eq_vec x y = false -> neq_vec x y = true.
Proof. unfold neq_vec. intro H. rewrite H. reflexivity. Qed.

Module SysOpenProof (Iunlock : IUNLOCK) (Iunlockput : IUNLOCKPUT)
                    (EndOp : END_OP) (Fileclose : FILECLOSE)
                    (Itrunc : ITRUNC) (Filealloc : FILEALLOC)
                    (Fdalloc : FDALLOC).

Module Tails := SysOpenTails Iunlock Iunlockput EndOp Fileclose.

Section ProofSysOpenBody.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rz  := (mword_of_int 0 : mword 5).

  (* the 1/2 + 1/2 SPLIT at [↦₈] -- [ProofSysOpenParts]' [so_word_half_join]
     read backwards, which is what hands [so_publish] the invariant's half of
     [f->ip] after the [sd s1,24(s2)] wrote the cell whole. *)
  Local Lemma so_ip_split (a w : mword 64) :
    a ↦₈ w -∗ a ↦₈{DfracOwn (1/2)} w ∗ a ↦₈{DfracOwn (1/2)} w.
  Proof.
    iIntros "H".
    iDestruct (bi.equiv_entails_1_1 _ _
                 (word_pointsto_frac_split a (1/2) (1/2) w) with "[H]")
      as "[$ $]".
    { iEval (rewrite Qp.div_2). iExact "H". }
  Qed.

  (* ================================================================== *)
  (*  THE SYSCALL'S EXIT CONTINUATION, NAMED ONCE.                       *)
  (*                                                                    *)
  (*  [SpecSysOpen]'s, minus the two structural cells the body below the *)
  (*  join never touches (sb_ninodes / sb_size) and minus the page-table *)
  (*  report, which is argstr's and is settled above the join.  The two  *)
  (*  ledger clauses are the join's own: the bitmap only SHRINKS past    *)
  (*  +0x4a (itrunc frees, nothing allocates) and the iref count moves by *)
  (*  at most one (the failure arms' [iunlockput] hands a slot back; the *)
  (*  success arm parks it in [f->ip]).                                  *)
  (* ================================================================== *)
  Definition so_cont `{GEN : GenId}
      (gf : gname) (bn : bio_names) (gfs : fs_names)
      (cov : gset Z) (logstart bmapstart inodestart size : Z)
      (used : gset Z) (nsj : nat) (dqb dqs : dfrac)
      (pj : mword 64) (pidv : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb b : bool) (lks : gset string)
      : CpuId -> iProp Σ :=
    fun (CIDx : CpuId) =>
      (∀ (mf : regfile) (used' : gset Z) (ns' : nat),
         ⌜callee_saved m mf⌝ -∗
         ⌜used' ⊆ used⌝ -∗
         ⌜(nsj <= ns')%nat /\ (ns' <= S nsj)%nat⌝ -∗
         sie_cap_gpr mf K b pj -∗
         cpu_own 0 eb pj b lks -∗
         trap_csrs_ext eb -∗
         cpu_claim_ext eb pj -∗
         pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
         sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
         sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
         bitmap_res gfs bmapstart cov logstart size used' -∗
         bslots bn 3 -∗
         iref_slots ns' -∗
         sys_open_post gf pj pidv V (mf !!! Regidx Ra0 : mword 64) -∗
         WP (Loop : expr riscv_lang))%I.

  (* ================================================================== *)
  (*  ARM S (+0xb8) AND THE PUBLICATION.                                 *)
  (*                                                                    *)
  (*  [so_tail_s] walks the seven instructions and returns the           *)
  (*  generation-ERASED share [inode_shr kk s dev inum]; only then are   *)
  (*  the parent and its share in ONE hand and [so_publish] callable.    *)
  (*  What crosses the tail is the six raw pieces of the slot plus the   *)
  (*  retained parent, and what comes back out is [file_ref gf kf 1 C] --  *)
  (*  which [ProcInv.proc_priv_settle] turns into the descriptor.         *)
  (* ================================================================== *)
  Lemma so_tail_pub `{GEN : GenId} `{CID0 : CpuId}
      (gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (size : Z) (dev : mword 32) (used : gset Z)
      (kk : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (kf fd : nat) (l : list nat) (C : fcontent) (pn : fpnames)
      (om voff : mword 32) (nsj : nat)
      (used2 : gset Z)
      (u : nat) (pidv : mword 32) (dqb dqs : dfrac)
      (V : pprivate)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w6 w23 w24 : mword 64)
      (bp : nat -> bv 8) :
    (K_iunlock <= K - 24)%nat -> (K_end_op <= K - 24)%nat ->
    (24 <= K)%nat -> ((K - 24) + 24 = K)%nat ->
    (kk < NINODE)%nat ->
    dev = icfg_dev ->
    bv_unsigned inum < 16 * Z.of_nat icfg_nib ->
    log_geom_ok cov logstart ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    (kf < NFILE)%nat -> (fd < NOFILE)%nat ->
    length (pv_ofile V) = NOFILE ->
    fd_frees (pv_ofile V) = fd :: l ->
    fc_ip C = ientry kk ->
    (fc_type C = FD_INODE \/ fc_type C = FD_DEVICE) ->
    fc_writable C = trunc8 (so_wr_word om) ->
    (bv_unsigned (di_type dn) = T_DIR_z -> om = (mword_of_int 0 : mword 32)) ->
    off_wf voff ->
    used2 ⊆ used ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    so_sp sp0 M -> so_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs3 : mword 64) = (mword_of_int (Z.of_nat fd) : mword 64) ->
    so_al sp0 ->
    sie_cap_gpr M (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ pc_is (mword_of_int (SO + 0xb8)) -∗
    panic_wp_any -∗
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
    inode_ref_short_gen kk (qi + s)%Qp qi dev inum gy -∗
    (* the six raw pieces the walk carries across the tail *)
    fref_tok gf kf 1 -∗
    flive_tok gf kf -∗
    file_fields kf 1 C -∗
    fpay_tok gf kf 1 pn -∗
    a_fip kf ↦₈{DfracOwn (1/2)} (ientry kk) -∗
    a_foff kf ↦₄ voff -∗
    (* the process, split at the descriptor table by fdalloc *)
    proc_priv_core (proc_addr jx) pidv V -∗
    proc_ofiles_owe gf (proc_addr jx)
      (pv_ofile (upd_ofile V fd (fnode kf))) ({[fd]} ∪ ∅) -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    log_op g u -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used2 -∗
    bslots bn 3 -∗
    iref_slots nsj -∗
    fd_slot -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
    (pa_stk sp0 5) ↦₈ (m !!! Regidx Rs3 : mword 64) -∗
    (pa_stk sp0 6) ↦₈ w6 -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ bp jj) -∗
    (pa_stk sp0 23) ↦₈ w23 -∗
    (pa_stk sp0 24) ↦₈ w24 -∗
    wp_next true (proc_addr jx)
      (so_cont gf bn gfs cov logstart bmapstart inodestart size used nsj
               dqb dqs (proc_addr jx) pidv V m K eb b lks) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKiu HKeo HK24 Kpop Hkk Hdevc Hinb Hgeom Hj Hgl Hlkempty Hkf Hfdlt
           Hlen Hfrees Hip Htyor Hwrb Hdir Hwf Hused2 Hsp0 HMsp HMthr HMs1
           HMs3 Hal.
    subst dev.
    iIntros "Hcg Hown Htce Hcce #Htext Hpc #Hpanic #Hbio #Hlog Hseam Hgen
              #Hitinv #Hesck #Hslkk Hslkd Hslpid Hdep Hidev Hiinum Hivalid
              Hload #Hshot Hkeep Hfref Hflive Hflds Hfpn Hfip Hfoff
              Hcore Howe #Hprocs #Hdev #Hgeo #Hdlk Hop Hsbb Hsbi Hbmres Hbsl
              Hisl Hfds Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24 Hcont".
    iDestruct (proc_priv_core_pid with "Hcore") as "[Hpidq Hcback]".
    iApply (Tails.so_tail_s (CID0 := CID0) gs jx gl gu gd gk pd pav pu bn g gfs
              gi cn gil gisl cov logstart icfg_dev kk s gy inum dn bm
              (mword_of_int (Z.of_nat fd) : mword 64) u pidv (DfracOwn (1/4))
              m M sp0 K eb b lks w6 w23 w24 bp
              HKiu HKeo HK24 Kpop Hkk Hgeom Hj Hgl Hlkempty Hsp0 HMsp HMthr
              HMs1 HMs3 Hal
              with "Hcg Hown Htce Hcce Htext Hpc Hpanic Hbio Hlog Hseam Hgen
                    Hitinv Hesck Hslkk Hslkd Hslpid Hdep Hidev Hiinum Hivalid
                    Hload Hshot Hpidq Hprocs Hdev Hgeo Hdlk Hop Hf1 Hf2 Hf3 Hf4
                    Hf5 Hf6 HbP H23 H24
                    [Hkeep Hfref Hflive Hflds Hfpn Hfip Hfoff Hcback Howe Hsbb
                     Hsbi Hbmres Hbsl Hisl Hfds Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc
                                         Hpidq Hshr".
    iDestruct ("Hcback" with "Hpidq") as "Hcore".
    (* ---- THE PUBLICATION: one ghost step ---- *)
    iApply fupd_wp.
    iMod (so_publish ⊤ gf kf kk qi s gy inum (di_type dn) C pn om voff
            ltac:(solve_ndisj) ltac:(solve_ndisj) Hkk Hinb Hip Htyor Hwrb Hdir
            Hwf
            with "Hkeep Hshr Hshot Hfref Hflive Hflds Hfpn Hfip Hfoff")
      as "Href".
    iModIntro.
    iDestruct (proc_priv_settle gf (proc_addr jx) pidv V fd kf 1 C Hfdlt Hlen
                 Hkf with "Hcore Howe Href") as "Hpriv".
    iAssert (sys_open_post gf (proc_addr jx) pidv V (mf !!! Regidx Ra0 : mword 64))
      with "[Hpriv Hfds]" as "Hpost".
    { rewrite /sys_open_post. iSplitR "Hfds"; [| iExact "Hfds"].
      iRight. iExists fd, l, kf.
      iSplitR.
      { iPureIntro. split; [| exact Hfrees]. rewrite Ha0f. reflexivity. }
      iExact "Hpriv". }
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf used2 nsj with "[%] [%] [%] Hcg Hown Htce Hcce Hpc
              Hsbb Hsbi Hbmres Hbsl Hisl Hpost").
    { exact Hcsf. }
    { exact Hused2. }
    { split; lia. }
  Qed.

  (* ---- the two field reads the walk makes into the LOCKED record, as
     accessors: [ic_loaded] is carried whole across the block and opened
     for exactly one halfword at a time. ---- *)
  Local Lemma so_meta_acc (gfs : fs_names) (gi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32) (dn : dinode) (bm : blkmap) :
    ic_loaded gfs gi cov logstart k inum dn bm -∗
    inode_meta (ientry k) dn ∗
    (inode_meta (ientry k) dn -∗ ic_loaded gfs gi cov logstart k inum dn bm).
  Proof.
    iIntros "(%data & %Hok & %Hdok & Hl & Hd & Hm & Ha & Hr & Hb)".
    iFrame "Hm". iIntros "Hm".
    iApply (ic_mk_loaded gfs gi cov logstart k inum dn bm data Hok Hdok
              with "Hl Hd Hm Ha Hr Hb").
  Qed.

  Local Lemma so_type_acc (ip : mword 64) (dn : dinode) :
    inode_meta ip dn -∗
    i_type ip ↦₂ di_type dn ∗ (i_type ip ↦₂ di_type dn -∗ inode_meta ip dn).
  Proof.
    iIntros "(Hty & Hmaj & Hmin & Hnl & Hsz)". iFrame "Hty".
    iIntros "Hty". iFrame "Hty Hmaj Hmin Hnl Hsz".
  Qed.

  Local Lemma so_maj_acc (ip : mword 64) (dn : dinode) :
    inode_meta ip dn -∗
    i_major ip ↦₂ di_major dn ∗ (i_major ip ↦₂ di_major dn -∗ inode_meta ip dn).
  Proof.
    iIntros "(Hty & Hmaj & Hmin & Hnl & Hsz)". iFrame "Hmaj".
    iIntros "Hmaj". iFrame "Hty Hmaj Hmin Hnl Hsz".
  Qed.

  (* ================================================================== *)
  (*  +0x88 .. +0xb4 AND THE +0x14e itrunc BLOCK.                        *)
  (*                                                                    *)
  (*    sd s1,24(s2)          f->ip = ip                                 *)
  (*    lw a5,-180(s0)        the omode word, read ONCE for three masks  *)
  (*    andi/xori/sb          f->readable = !(omode & O_WRONLY)          *)
  (*    andi/snez/sb          f->writable = (omode & 3) != 0             *)
  (*    andi a5,a5,1024 ; c.beqz -> +0xb8                                *)
  (*    lh a4,68(s1) ; c.li a5,2 ; beq -> +0x14e   itrunc(ip)            *)
  (*                                                                    *)
  (*  ENTERED FROM TWO PLACES -- the FD_INODE fall-through at +0x84 and  *)
  (*  the FD_DEVICE block's [c.j] at +0x14c -- which is why the two      *)
  (*  type-dependent cells ([f->type], [f->major], and whether [f->off]  *)
  (*  was zeroed) are PARAMETERS here and not values.                    *)
  (*                                                                    *)
  (*  THE OMODE SLOT IS REJOINED the moment the [lw] gives its cell back: *)
  (*  nothing below reads the frame again, and every exit wants slot 23   *)
  (*  whole.                                                             *)
  (* ================================================================== *)
  Lemma so_stores `{GEN : GenId} `{CID0 : CpuId}
      (gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used : gset Z)
      (kk : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (kf fd : nat) (l : list nat) (pn : fpnames)
      (tyw : mword 32) (rd0 wr0 : bv 8) (pip ipold : mword 64) (maj : bv 16)
      (om voff lo : mword 32) (nsj : nat)
      (u : nat) (pidv : mword 32) (dqb dqs : dfrac)
      (V : pprivate)
      (m N : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w6 w24 : mword 64)
      (bp : nat -> bv 8) :
    (K_iunlock <= K - 24)%nat -> (K_end_op <= K - 24)%nat ->
    (K_itrunc <= K - 24)%nat ->
    (24 <= K)%nat -> ((K - 24) + 24 = K)%nat ->
    (kk < NINODE)%nat ->
    dev = icfg_dev -> nib = icfg_nib ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    cov_below cov size ->
    (2 <= u)%nat ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    (kf < NFILE)%nat -> (fd < NOFILE)%nat ->
    length (pv_ofile V) = NOFILE ->
    fd_frees (pv_ofile V) = fd :: l ->
    (tyw = FD_INODE \/ tyw = FD_DEVICE) ->
    (bv_unsigned (di_type dn) = T_DIR_z -> om = (mword_of_int 0 : mword 32)) ->
    off_wf voff ->
    is_aligned_paddr (Physaddr (pa_stk sp0 23)) 8 = true ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    so_sp sp0 N -> so_thr m N ->
    (N !!! Regidx Rs0 : mword 64) = sp0 ->
    (N !!! Regidx Rs1 : mword 64) = ientry kk ->
    (N !!! Regidx Rs2 : mword 64) = fnode kf ->
    (N !!! Regidx Rs3 : mword 64) = (mword_of_int (Z.of_nat fd) : mword 64) ->
    so_al sp0 ->
    sie_cap_gpr N (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ pc_is (mword_of_int (SO + 0x88)) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
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
    inode_ref_short_gen kk (qi + s)%Qp qi dev inum gy -∗
    (* the fresh slot, six cells PLAIN and [f->ip] WHOLE *)
    fref_tok gf kf 1 -∗
    flive_tok gf kf -∗
    fpay_tok gf kf 1 pn -∗
    a_ftype kf     ↦₄ tyw -∗
    a_freadable kf ↦ₘ rd0 -∗
    a_fwritable kf ↦ₘ wr0 -∗
    a_fpipe kf     ↦₈ pip -∗
    a_fmajor kf    ↦₂ maj -∗
    a_fip kf       ↦₈ ipold -∗
    a_foff kf      ↦₄ voff -∗
    proc_priv_core (proc_addr jx) pidv V -∗
    proc_ofiles_owe gf (proc_addr jx)
      (pv_ofile (upd_ofile V fd (fnode kf))) ({[fd]} ∪ ∅) -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    log_op g u -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used -∗
    bslots bn 3 -∗
    iref_slots nsj -∗
    fd_slot -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
    (pa_stk sp0 5) ↦₈ (m !!! Regidx Rs3 : mword 64) -∗
    (pa_stk sp0 6) ↦₈ w6 -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ bp jj) -∗
    (pa_stk sp0 23) ↦₄ lo -∗
    (pa_add (pa_stk sp0 23) 4) ↦₄ om -∗
    (pa_stk sp0 24) ↦₈ w24 -∗
    wp_next true (proc_addr jx)
      (so_cont gf bn gfs cov logstart bmapstart inodestart size used nsj
               dqb dqs (proc_addr jx) pidv V m K eb b lks) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKiu HKeo HKit HK24 Kpop Hkk Hdevc Hnibc Hinb Hgeom Hsize Hbm0
           Hbmcov Hbmlog Hist0 Hiblk Hiblog Hcovb Hu2 Hj Hgl Hlkempty Hkf
           Hfdlt Hlen Hfrees Htyor Hdir Hwf Hal23 Hsp0 HNsp HNthr HNs0 HNs1
           HNs2 HNs3 Hal.
    subst dev. subst nib.
    (* [2 <= u] as a SHAPE, not an inequality: itrunc's uncredited entry
       level is [it_entry false u2 = S (S u2)], and destructing here is what
       lets the [log_op] hypothesis meet it without a rewrite. *)
    destruct u as [| [| u2]]; [ exfalso; lia | exfalso; lia | ].
    iIntros "Hcg Hown Htce Hcce #Htext Hpc #Hpanic #Hbio #Hlog Hseam Hgen
              #Hitinv #Hesck #Hireg #Hslkk Hslkd Hslpid Hdep Hidev Hiinum
              Hivalid Hload #Hshot Hkeep Hfref Hflive Hfpn Hfty Hfrd Hfwr
              Hfpip Hfmaj Hfip Hfoff Hcore Howe #Hprocs #Hdev #Hgeo #Hdlk Hop
              Hsbb Hsbi Hbmres Hbsl Hisl Hfds Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP
              H23lo H23hi H24 Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    iPoseProof (soi_088 with "Htext") as "Hi88".
    iPoseProof (soi_08c with "Htext") as "Hi8c".
    iPoseProof (soi_090 with "Htext") as "Hi90".
    iPoseProof (soi_094 with "Htext") as "Hi94".
    iPoseProof (soi_098 with "Htext") as "Hi98".
    iPoseProof (soi_09c with "Htext") as "Hi9c".
    iPoseProof (soi_0a0 with "Htext") as "Hia0".
    iPoseProof (soi_0a4 with "Htext") as "Hia4".
    iPoseProof (soi_0a8 with "Htext") as "Hia8".
    iPoseProof (soi_0ac with "Htext") as "Hiac".
    iPoseProof (soi_0ae with "Htext") as "Hiae".
    iPoseProof (soi_0b2 with "Htext") as "Hib2".
    iPoseProof (soi_0b4 with "Htext") as "Hib4".
    (* ===== +0x88 sd s1,24(s2) -- f->ip = ip ===== *)
    iEval (rewrite /a_fip /foff_of) in "Hfip".
    iApply (wp_sd_s_sconf (CID := CID0) (mword_of_int (SO + 0x88)) Rs1 Rs2
              (mword_of_int 24 : mword 12) N (K - 24)%nat ipold b
              with "Hcg Hpc Hi88 [Hfip]").
    { iEval (rgne; rewrite HNs2). iExact "Hfip". }
    iIntros (CID1 Hq1) "Hcg Hpc Hfip".
    iEval (rgne; rewrite HNs2; rgne; rewrite HNs1) in "Hfip".
    assert (Hpp88 : add_vec_int (mword_of_int (SO + 0x88) : mword 64) 4
                    = mword_of_int (SO + 0x8c)) by pcw.
    iEval (rewrite Hpp88) in "Hpc".
    (* ===== +0x8c lw a5,-180(s0) -- the omode word ===== *)
    iApply (wp_lw_s_sconf (CID := CID1) (mword_of_int (SO + 0x8c)) Ra5 Rs0
              (mword_of_int 3916 : mword 12) N (K - 24)%nat om b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8c [H23hi]").
    { iEval (rgne; rewrite HNs0; rewrite so_omode). iExact "H23hi". }
    iIntros (CID2 Hq2) "Hcg Hpc H23hi".
    iEval (rgne; rewrite HNs0; rewrite so_omode) in "H23hi".
    iDestruct (so_omode_join sp0 lo om Hal23 with "H23lo H23hi") as "H23".
    set (N1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 om : mword 64)]> N).
    assert (HN1a5 : (N1 !!! Regidx Ra5 : mword 64) = so_omv om)
      by (rewrite /N1 /so_omv; apply upd_eq).
    assert (HN1sp : so_sp sp0 N1)
      by (rewrite /so_sp /N1 upd_ne; [exact HNsp | nz]).
    assert (HN1s0 : (N1 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /N1 upd_ne; [exact HNs0 | nz]).
    assert (HN1s1 : (N1 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /N1 upd_ne; [exact HNs1 | nz]).
    assert (HN1s2 : (N1 !!! Regidx Rs2 : mword 64) = fnode kf)
      by (rewrite /N1 upd_ne; [exact HNs2 | nz]).
    assert (HN1s3 : (N1 !!! Regidx Rs3 : mword 64)
                    = (mword_of_int (Z.of_nat fd) : mword 64))
      by (rewrite /N1 upd_ne; [exact HNs3 | nz]).
    assert (HN1thr : so_thr m N1).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /N1 upd_ne; [| regne].
      exact (HNthr c Hc N2b N8 N9 N18 N19). }
    assert (Hpp8c : add_vec_int (mword_of_int (SO + 0x8c) : mword 64) 4
                    = mword_of_int (SO + 0x90)) by pcw.
    iEval (rewrite Hpp8c) in "Hpc".
    (* ===== +0x90 andi a4,a5,1 ===== *)
    iApply (wp_andi_s_sconf (CID := CID2) (mword_of_int (SO + 0x90)) Ra4 Ra5
              (mword_of_int 1 : mword 12) (so_and om 1) N1 (K - 24)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HN1a5; reflexivity)
              with "Hcg Hpc Hi90").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (N2 := <[Regidx Ra4 := regval_into_reg (so_and om 1)]> N1).
    assert (HN2a4 : (N2 !!! Regidx Ra4 : mword 64) = so_and om 1)
      by (rewrite /N2; apply upd_eq).
    assert (HN2a5 : (N2 !!! Regidx Ra5 : mword 64) = so_omv om)
      by (rewrite /N2 upd_ne; [exact HN1a5 | nz]).
    assert (HN2s2 : (N2 !!! Regidx Rs2 : mword 64) = fnode kf)
      by (rewrite /N2 upd_ne; [exact HN1s2 | nz]).
    assert (Hpp90 : add_vec_int (mword_of_int (SO + 0x90) : mword 64) 4
                    = mword_of_int (SO + 0x94)) by pcw.
    iEval (rewrite Hpp90) in "Hpc".
    (* ===== +0x94 xori a4,a4,1 ===== *)
    iApply (wp_xori_s_sconf (CID := CID3) (mword_of_int (SO + 0x94)) Ra4 Ra4
              (mword_of_int 1 : mword 12) (so_rd_word om) N2 (K - 24)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HN2a4; reflexivity)
              with "Hcg Hpc Hi94").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (N3 := <[Regidx Ra4 := regval_into_reg (so_rd_word om)]> N2).
    assert (HN3a4 : (N3 !!! Regidx Ra4 : mword 64) = so_rd_word om)
      by (rewrite /N3; apply upd_eq).
    assert (HN3a5 : (N3 !!! Regidx Ra5 : mword 64) = so_omv om)
      by (rewrite /N3 upd_ne; [exact HN2a5 | nz]).
    assert (HN3s2 : (N3 !!! Regidx Rs2 : mword 64) = fnode kf)
      by (rewrite /N3 upd_ne; [exact HN2s2 | nz]).
    assert (Hpp94 : add_vec_int (mword_of_int (SO + 0x94) : mword 64) 4
                    = mword_of_int (SO + 0x98)) by pcw.
    iEval (rewrite Hpp94) in "Hpc".
    (* ===== +0x98 sb a4,8(s2) -- f->readable ===== *)
    iEval (rewrite /a_freadable /foff_of) in "Hfrd".
    iApply (wp_sb_s_sconf (CID := CID4) (mword_of_int (SO + 0x98)) Ra4 Rs2
              (mword_of_int 8 : mword 12) N3 (K - 24)%nat rd0 b
              with "Hcg Hpc Hi98 [Hfrd]").
    { iEval (rgne; rewrite HN3s2). iExact "Hfrd". }
    iIntros (CID5 Hq5) "Hcg Hpc Hfrd".
    iEval (rgne; rewrite HN3s2; rgne; rewrite HN3a4) in "Hfrd".
    assert (Hpp98 : add_vec_int (mword_of_int (SO + 0x98) : mword 64) 4
                    = mword_of_int (SO + 0x9c)) by pcw.
    iEval (rewrite Hpp98) in "Hpc".
    (* ===== +0x9c andi a4,a5,3 ===== *)
    iApply (wp_andi_s_sconf (CID := CID5) (mword_of_int (SO + 0x9c)) Ra4 Ra5
              (mword_of_int 3 : mword 12) (so_and om 3) N3 (K - 24)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HN3a5; reflexivity)
              with "Hcg Hpc Hi9c").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (N4 := <[Regidx Ra4 := regval_into_reg (so_and om 3)]> N3).
    assert (HN4a4 : (N4 !!! Regidx Ra4 : mword 64) = so_and om 3)
      by (rewrite /N4; apply upd_eq).
    assert (HN4a5 : (N4 !!! Regidx Ra5 : mword 64) = so_omv om)
      by (rewrite /N4 upd_ne; [exact HN3a5 | nz]).
    assert (HN4s2 : (N4 !!! Regidx Rs2 : mword 64) = fnode kf)
      by (rewrite /N4 upd_ne; [exact HN3s2 | nz]).
    assert (Hpp9c : add_vec_int (mword_of_int (SO + 0x9c) : mword 64) 4
                    = mword_of_int (SO + 0xa0)) by pcw.
    iEval (rewrite Hpp9c) in "Hpc".
    (* ===== +0xa0 snez a4,a4 ===== *)
    iDestruct (sie_cap_gpr_x0 N4 (K - 24)%nat b (proc_addr jx) Rz
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%HN4x0 Hcg]".
    iApply (wp_sltu_s_sconf (CID := CID6) (mword_of_int (SO + 0xa0)) Ra4 Rz Ra4
              (so_wr_word om) N4 (K - 24)%nat b ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HN4x0; rgne; rewrite HN4a4; reflexivity)
              with "Hcg Hpc Hia0").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (N5 := <[Regidx Ra4 := regval_into_reg (so_wr_word om)]> N4).
    assert (HN5a4 : (N5 !!! Regidx Ra4 : mword 64) = so_wr_word om)
      by (rewrite /N5; apply upd_eq).
    assert (HN5a5 : (N5 !!! Regidx Ra5 : mword 64) = so_omv om)
      by (rewrite /N5 upd_ne; [exact HN4a5 | nz]).
    assert (HN5s2 : (N5 !!! Regidx Rs2 : mword 64) = fnode kf)
      by (rewrite /N5 upd_ne; [exact HN4s2 | nz]).
    assert (Hppa0 : add_vec_int (mword_of_int (SO + 0xa0) : mword 64) 4
                    = mword_of_int (SO + 0xa4)) by pcw.
    iEval (rewrite Hppa0) in "Hpc".
    (* ===== +0xa4 sb a4,9(s2) -- f->writable ===== *)
    iEval (rewrite /a_fwritable /foff_of) in "Hfwr".
    iApply (wp_sb_s_sconf (CID := CID7) (mword_of_int (SO + 0xa4)) Ra4 Rs2
              (mword_of_int 9 : mword 12) N5 (K - 24)%nat wr0 b
              with "Hcg Hpc Hia4 [Hfwr]").
    { iEval (rgne; rewrite HN5s2). iExact "Hfwr". }
    iIntros (CID8 Hq8) "Hcg Hpc Hfwr".
    iEval (rgne; rewrite HN5s2; rgne; rewrite HN5a4) in "Hfwr".
    assert (Hppa4 : add_vec_int (mword_of_int (SO + 0xa4) : mword 64) 4
                    = mword_of_int (SO + 0xa8)) by pcw.
    iEval (rewrite Hppa4) in "Hpc".
    (* ---- the published CONTENT, and the six cells as [file_fields] ---- *)
    set (C := MkFContent tyw (trunc8 (so_rd_word om)) (trunc8 (so_wr_word om))
                pip (ientry kk) maj).
    iDestruct (so_ip_split with "Hfip") as "[Hfip1 Hfip2]".
    iAssert (file_fields kf 1 C) with "[Hfty Hfrd Hfwr Hfpip Hfip1 Hfmaj]"
      as "Hflds".
    { rewrite /file_fields /C; cbn [fc_type fc_readable fc_writable fc_pipe
                                    fc_ip fc_major].
      rewrite /a_ftype /a_freadable /a_fwritable /a_fpipe /a_fip /a_fmajor
              /foff_of.
      iFrame "Hfty Hfrd Hfwr Hfpip Hfip1 Hfmaj". }
    (* ===== +0xa8 andi a5,a5,1024 -- O_TRUNC ===== *)
    iApply (wp_andi_s_sconf (CID := CID8) (mword_of_int (SO + 0xa8)) Ra5 Ra5
              (mword_of_int 1024 : mword 12) (so_and om 1024) N5 (K - 24)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HN5a5; reflexivity)
              with "Hcg Hpc Hia8").
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (N6 := <[Regidx Ra5 := regval_into_reg (so_and om 1024)]> N5).
    assert (HN6a5 : (N6 !!! Regidx Ra5 : mword 64) = so_and om 1024)
      by (rewrite /N6; apply upd_eq).
    assert (HN6sp : so_sp sp0 N6).
    { rewrite /so_sp /N6 upd_ne; [| nz]. rewrite /N5 upd_ne; [| nz].
      rewrite /N4 upd_ne; [| nz]. rewrite /N3 upd_ne; [| nz].
      rewrite /N2 upd_ne; [| nz]. exact HN1sp. }
    assert (HN6s1 : (N6 !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite /N6 upd_ne; [| nz]. rewrite /N5 upd_ne; [| nz].
      rewrite /N4 upd_ne; [| nz]. rewrite /N3 upd_ne; [| nz].
      rewrite /N2 upd_ne; [| nz]. exact HN1s1. }
    assert (HN6s3 : (N6 !!! Regidx Rs3 : mword 64)
                    = (mword_of_int (Z.of_nat fd) : mword 64)).
    { rewrite /N6 upd_ne; [| nz]. rewrite /N5 upd_ne; [| nz].
      rewrite /N4 upd_ne; [| nz]. rewrite /N3 upd_ne; [| nz].
      rewrite /N2 upd_ne; [| nz]. exact HN1s3. }
    assert (HN6thr : so_thr m N6).
    { intros c Hc N2b N8 N9 N18 N19.
      rewrite /N6 upd_ne; [| regne]. rewrite /N5 upd_ne; [| regne].
      rewrite /N4 upd_ne; [| regne]. rewrite /N3 upd_ne; [| regne].
      rewrite /N2 upd_ne; [| regne].
      exact (HN1thr c Hc N2b N8 N9 N18 N19). }
    assert (Hppa8 : add_vec_int (mword_of_int (SO + 0xa8) : mword 64) 4
                    = mword_of_int (SO + 0xac)) by pcw.
    iEval (rewrite Hppa8) in "Hpc".
    (* ===== +0xac c.beqz a5, +0xb8 ===== *)
    destruct (eq_vec (so_and om 1024) (zero_reg : mword 64)) eqn:Htr.
    { (* ---- no O_TRUNC: straight to ARM S ---- *)
      iApply (wp_cbeqz_taken_s_sconf (CID := CID9) (mword_of_int (SO + 0xac))
                (mword_of_int 6 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                N6 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HN6a5; exact Htr)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hiac").
      iIntros (CID10 Hq10). iNext. iIntros "Hcg Hpc".
      assert (Htgac : add_vec (mword_of_int (SO + 0xac) : mword 64)
                        (sign_extend' 64
                           (sign_extend' 13 (concat_vec (mword_of_int 6 : mword 8) ('b"0"))))
                      = mword_of_int (SO + 0xb8)) by pcw.
      iEval (rewrite Htgac) in "Hpc".
      iDestruct (cpu_own_transport CID0 CID10 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (trap_csrs_ext_transport CID0 CID10 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
      iDestruct (cpu_claim_ext_transport CID0 CID10 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
      iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID10)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (so_tail_pub (CID0 := CID10) gf gs jx gl gu gd gk pd pav pu bn g
                gfs gi cn gil gisl cov logstart bmapstart inodestart size
                icfg_dev used kk qi s gy inum dn bm kf fd l C pn om voff nsj
                used (S (S u2)) pidv dqb dqs V m N6 sp0 K eb b lks w6
                (word_of_words lo om) w24 bp
                HKiu HKeo HK24 Kpop Hkk eq_refl Hinb Hgeom Hj Hgl Hlkempty Hkf
                Hfdlt Hlen Hfrees eq_refl Htyor eq_refl Hdir Hwf
                ltac:(reflexivity) Hsp0 HN6sp HN6thr HN6s1 HN6s3 Hal
                with "Hcg Hown Htce Hcce Htext Hpc Hpanic Hbio Hlog Hseam Hgen
                      Hitinv Hesck Hslkk Hslkd Hslpid Hdep Hidev Hiinum Hivalid
                      Hload Hshot Hkeep Hfref Hflive Hflds Hfpn Hfip2 Hfoff
                      Hcore Howe Hprocs Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres
                      Hbsl Hisl Hfds Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
                      Hcont"). }
    (* ---- O_TRUNC set: the type test at +0xb4 ---- *)
    iApply (wp_cbeqz_fall_s_sconf (CID := CID9) (mword_of_int (SO + 0xac))
              (mword_of_int 6 : mword 8) (Cregidx (mword_of_int 7)) Ra5
              N6 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HN6a5; exact Htr)
              with "Hcg Hpc Hiac").
    iIntros (CID10 Hq10) "Hcg Hpc".
    assert (Hppac : add_vec_int (mword_of_int (SO + 0xac) : mword 64) 2
                    = mword_of_int (SO + 0xae)) by pcw.
    iEval (rewrite Hppac) in "Hpc".
    (* ===== +0xae lh a4,68(s1) ===== *)
    iDestruct (so_meta_acc with "Hload") as "[Hmeta Hlback]".
    iDestruct (so_type_acc with "Hmeta") as "[Hity Hmback]".
    iEval (rewrite /i_type) in "Hity".
    iApply (wp_lh_s_sconf (CID := CID10) (mword_of_int (SO + 0xae)) Ra4 Rs1
              (mword_of_int 68 : mword 12) N6 (K - 24)%nat
              (di_type dn : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hiae [Hity]").
    { iEval (rgne; rewrite HN6s1). iExact "Hity". }
    iIntros (CID11 Hq11) "Hcg Hpc Hity".
    iEval (rgne; rewrite HN6s1) in "Hity".
    iDestruct ("Hmback" with "[Hity]") as "Hmeta";
      [iEval (rewrite /i_type); iExact "Hity" |].
    iDestruct ("Hlback" with "Hmeta") as "Hload".
    set (N7 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (di_type dn : mword 16) : mword 64)]> N6).
    assert (HN7a4 : (N7 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /N7; apply upd_eq).
    assert (Hppae : add_vec_int (mword_of_int (SO + 0xae) : mword 64) 4
                    = mword_of_int (SO + 0xb2)) by pcw.
    iEval (rewrite Hppae) in "Hpc".
    (* ===== +0xb2 c.li a5,2 ===== *)
    iApply (wp_cli_s_sconf (CID := CID11) (mword_of_int (SO + 0xb2)) Ra5
              (mword_of_int 2 : mword 6) (mword_of_int 2 : mword 64)
              N7 (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hib2").
    iIntros (CID12 Hq12) "Hcg Hpc".
    set (N8 := <[Regidx Ra5 := regval_into_reg (mword_of_int 2 : mword 64)]> N7).
    assert (HN8a4 : (N8 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /N8 upd_ne; [exact HN7a4 | nz]).
    assert (HN8a5 : (N8 !!! Regidx Ra5 : mword 64) = (mword_of_int 2 : mword 64))
      by (rewrite /N8; apply upd_eq).
    assert (HN8sp : so_sp sp0 N8).
    { rewrite /so_sp /N8 upd_ne; [| nz]. rewrite /N7 upd_ne; [| nz].
      exact HN6sp. }
    assert (HN8s1 : (N8 !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite /N8 upd_ne; [| nz]. rewrite /N7 upd_ne; [| nz]. exact HN6s1. }
    assert (HN8s3 : (N8 !!! Regidx Rs3 : mword 64)
                    = (mword_of_int (Z.of_nat fd) : mword 64)).
    { rewrite /N8 upd_ne; [| nz]. rewrite /N7 upd_ne; [| nz]. exact HN6s3. }
    assert (HN8thr : so_thr m N8).
    { intros c Hc N2b N9b N9 N18 N19.
      rewrite /N8 upd_ne; [| regne]. rewrite /N7 upd_ne; [| regne].
      exact (HN6thr c Hc N2b N9b N9 N18 N19). }
    assert (Hppb2 : add_vec_int (mword_of_int (SO + 0xb2) : mword 64) 2
                    = mword_of_int (SO + 0xb4)) by pcw.
    iEval (rewrite Hppb2) in "Hpc".
    (* ===== +0xb4 beq a4,a5, +0x14e ===== *)
    destruct (decide (di_type dn = (mword_of_int 2 : mword 16))) as [Hfile | Hnf].
    2:{ (* not a regular file: no itrunc, straight to ARM S *)
      iApply (wp_beq_fall_s_sconf (CID := CID12) (mword_of_int (SO + 0xb4))
                (mword_of_int 154 : mword 13) Ra5 Ra4 N8 (K - 24)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HN8a4 HN8a5;
                      exact (so_ty_ne (di_type dn) 2 so_tfile_range Hnf))
                with "Hcg Hpc Hib4").
      iIntros (CID13 Hq13) "Hcg Hpc".
      assert (Hppb4 : add_vec_int (mword_of_int (SO + 0xb4) : mword 64) 4
                      = mword_of_int (SO + 0xb8)) by pcw.
      iEval (rewrite Hppb4) in "Hpc".
      iDestruct (cpu_own_transport CID0 CID13 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (trap_csrs_ext_transport CID0 CID13 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
      iDestruct (cpu_claim_ext_transport CID0 CID13 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
      iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID13)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (so_tail_pub (CID0 := CID13) gf gs jx gl gu gd gk pd pav pu bn g
                gfs gi cn gil gisl cov logstart bmapstart inodestart size
                icfg_dev used kk qi s gy inum dn bm kf fd l C pn om voff nsj
                used (S (S u2)) pidv dqb dqs V m N8 sp0 K eb b lks w6
                (word_of_words lo om) w24 bp
                HKiu HKeo HK24 Kpop Hkk eq_refl Hinb Hgeom Hj Hgl Hlkempty Hkf
                Hfdlt Hlen Hfrees eq_refl Htyor eq_refl Hdir Hwf
                ltac:(reflexivity) Hsp0 HN8sp HN8thr HN8s1 HN8s3 Hal
                with "Hcg Hown Htce Hcce Htext Hpc Hpanic Hbio Hlog Hseam Hgen
                      Hitinv Hesck Hslkk Hslkd Hslpid Hdep Hidev Hiinum Hivalid
                      Hload Hshot Hkeep Hfref Hflive Hflds Hfpn Hfip2 Hfoff
                      Hcore Howe Hprocs Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres
                      Hbsl Hisl Hfds Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
                      Hcont"). }
    (* ---- T_FILE: the +0x14e itrunc block ---- *)
    iPoseProof (soi_14e with "Htext") as "Hi14e".
    iPoseProof (soi_150 with "Htext") as "Hi150".
    iPoseProof (soi_154 with "Htext") as "Hi154".
    iApply (wp_beq_taken_s_sconf (CID := CID12) (mword_of_int (SO + 0xb4))
              (mword_of_int 154 : mword 13) Ra5 Ra4 N8 (K - 24)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HN8a4 HN8a5;
                    exact (so_ty_eq (di_type dn) 2 so_tfile_range Hfile))
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hib4").
    iIntros (CID13 Hq13). iNext. iIntros "Hcg Hpc".
    assert (Htgb4 : add_vec (mword_of_int (SO + 0xb4) : mword 64)
                      (sign_extend' 64 (mword_of_int 154 : mword 13))
                    = mword_of_int (SO + 0x14e)) by pcw.
    iEval (rewrite Htgb4) in "Hpc".
    (* ===== +0x14e c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID13) (mword_of_int (SO + 0x14e)) Ra0 Rs1
              N8 (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi14e").
    iIntros (CID14 Hq14) "Hcg Hpc".
    set (P1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (N8 !!! Regidx Rs1))]> N8).
    assert (HP1a0 : (P1 !!! Regidx Ra0 : mword 64) = ientry kk).
    { etransitivity; [ rewrite /P1; apply upd_eq |].
      rewrite add_vec_zero_l. exact HN8s1. }
    assert (HP1sp : so_sp sp0 P1)
      by (rewrite /so_sp /P1 upd_ne; [exact HN8sp | nz]).
    assert (HP1s1 : (P1 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /P1 upd_ne; [exact HN8s1 | nz]).
    assert (HP1s3 : (P1 !!! Regidx Rs3 : mword 64)
                    = (mword_of_int (Z.of_nat fd) : mword 64))
      by (rewrite /P1 upd_ne; [exact HN8s3 | nz]).
    assert (HP1thr : so_thr m P1).
    { intros c Hc N2b N9b N9 N18 N19. rewrite /P1 upd_ne; [| regne].
      exact (HN8thr c Hc N2b N9b N9 N18 N19). }
    assert (Hpp14e : add_vec_int (mword_of_int (SO + 0x14e) : mword 64) 2
                     = mword_of_int (SO + 0x150)) by pcw.
    iEval (rewrite Hpp14e) in "Hpc".
    (* ===== +0x150 jal ra,itrunc ===== *)
    iApply (wp_jal_s_sconf (CID := CID14) (mword_of_int (SO + 0x150)) Rra
              (mword_of_int 2089184 : mword 21) P1 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi150").
    iIntros (CID15 Hq15) "Hcg Hpc".
    set (P2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x150) : mword 64) 4)]> P1).
    assert (Hjit : add_vec (mword_of_int (SO + 0x150) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089184 : mword 21))
                   = mword_of_int KernelSyms.itrunc) by pcw.
    iEval (rewrite Hjit) in "Hpc".
    assert (HP2ra : (P2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x150) : mword 64) 4)
      by (rewrite /P2; apply upd_eq).
    assert (HP2a0 : (P2 !!! Regidx Ra0 : mword 64) = ientry kk)
      by (rewrite /P2 upd_ne; [exact HP1a0 | nz]).
    assert (HP2sp : so_sp sp0 P2)
      by (rewrite /so_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2s1 : (P2 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /P2 upd_ne; [exact HP1s1 | nz]).
    assert (HP2s3 : (P2 !!! Regidx Rs3 : mword 64)
                    = (mword_of_int (Z.of_nat fd) : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s3 | nz]).
    assert (HP2thr : so_thr m P2).
    { intros c Hc N2b N9b N9 N18 N19. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hc N2b N9b N9 N18 N19). }
    iDestruct (cpu_own_transport CID0 CID15 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID15 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID15 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    (* the locked record, opened whole for the one callee that rewrites it *)
    iDestruct (so_loaded_open with "Hload")
      as (data) "(%Hok & %Hdok & Hlnk & Hat & Hmeta & Hmap & Hblk)".
    destruct Hok as (Hbwf & Hbcov & Haddrs & Htynz & Hszcap & Hholes & Hsized).
    iDestruct (proc_priv_core_pid with "Hcore") as "[Hpidq Hcback]".
    iApply (Itrunc.wp_itrunc_sconf (CID := CID15) gs jx gl gu gd gk pd pav pu
              bn g gfs gi cov logstart bmapstart inodestart icfg_nib size
              icfg_dev used (ientry kk) inum dn dn bm data u2 pidv
              (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqb dqs
              P2 (K - 24)%nat eb b lks
              HKit Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog Hinb
              Htynz (di_type_stable_refl dn) (di_nlink_stable_refl dn Htynz)
              Hbwf Hcovb Hsized Haddrs Hj Hgl HP2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hpc Hpanic Hbio Hlog Hidev Hiinum
                    Hmeta Hmap Hblk Hsbb Hsbi Hbmres Hireg Hat Hpidq Hprocs
                    Hdev Hgeo Hdlk Hbsl Hop").
    iIntros (CID16 Hq16 mit) "%Hcsit Hcg Hown Htce Hcce Hpc Hpidq Hidev Hiinum
                              Hsbb Hsbi Hmeta Hmap Hblk Hbmres Hat Hbsl Hop".
    iDestruct "Hop" as (u3) "[%Hu3 Hop]".
    iDestruct ("Hcback" with "Hpidq") as "Hcore".
    assert (Hpcit : ret_pc (P2 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0x154)) by (rewrite HP2ra; pcw).
    iEval (rewrite Hpcit) in "Hpc".
    assert (Hitsp : so_sp sp0 mit).
    { rewrite /so_sp (callee_saved_lookup Hcsit csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HP2sp. }
    assert (Hits1 : (mit !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite (callee_saved_lookup Hcsit Rs1 ltac:(vm_compute; reflexivity)).
      exact HP2s1. }
    assert (Hits3 : (mit !!! Regidx Rs3 : mword 64)
                    = (mword_of_int (Z.of_nat fd) : mword 64)).
    { rewrite (callee_saved_lookup Hcsit Rs3 ltac:(vm_compute; reflexivity)).
      exact HP2s3. }
    assert (Hitthr : so_thr m mit).
    { intros c Hc N2b N9b N9 N18 N19. rewrite (callee_saved_lookup Hcsit c Hc).
      exact (HP2thr c Hc N2b N9b N9 N18 N19). }
    (* ---- THE O_TRUNC BRIDGE: rebuild [ic_loaded] at the truncated record ---- *)
    assert (Htynd : bv_unsigned (di_type dn) <> T_DIR_z).
    { rewrite Hfile. unfold T_DIR_z. vm_compute. discriminate. }
    iDestruct (so_trunc_loaded gfs gi cov logstart kk inum dn Htynz Htynd
                 with "Hat Hmeta Hmap Hblk") as "Hload".
    (* ===== +0x154 c.j +0xb8 ===== *)
    iApply (wp_cj_s_sconf (CID := CID16) (mword_of_int (SO + 0x154))
              (sign_extend' 21 (concat_vec (mword_of_int 1970 : mword 11) ('b"0")))
              mit (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi154").
    iIntros (CID17 Hq17). iNext. iIntros "Hcg Hpc".
    assert (Htg154 : add_vec (mword_of_int (SO + 0x154) : mword 64)
                       (sign_extend' 64
                          (sign_extend' 21 (concat_vec (mword_of_int 1970 : mword 11) ('b"0"))))
                     = mword_of_int (SO + 0xb8)) by pcw.
    iEval (rewrite Htg154) in "Hpc".
    iDestruct (cpu_own_transport CID16 CID17 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID16 CID17 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID16 CID17 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID17)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (so_tail_pub (CID0 := CID17) gf gs jx gl gu gd gk pd pav pu bn g
              gfs gi cn gil gisl cov logstart bmapstart inodestart size
              icfg_dev used kk qi s gy inum (di_trunc dn) bm_empty kf fd l C pn
              om voff nsj (used ∖ bm_blocks bm) u3 pidv dqb dqs V m mit sp0 K
              eb b lks w6 (word_of_words lo om) w24 bp
              HKiu HKeo HK24 Kpop Hkk eq_refl Hinb Hgeom Hj Hgl Hlkempty Hkf
              Hfdlt Hlen Hfrees eq_refl Htyor eq_refl Hdir Hwf
              ltac:(set_solver) Hsp0 Hitsp Hitthr Hits1 Hits3 Hal
              with "Hcg Hown Htce Hcce Htext Hpc Hpanic Hbio Hlog Hseam Hgen
                    Hitinv Hesck Hslkk Hslkd Hslpid Hdep Hidev Hiinum Hivalid
                    Hload Hshot Hkeep Hfref Hflive Hflds Hfpn Hfip2 Hfoff
                    Hcore Howe Hprocs Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres
                    Hbsl Hisl Hfds Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
                    Hcont").
  Qed.

End ProofSysOpenBody.

End SysOpenProof.
