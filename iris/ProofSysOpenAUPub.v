(* ProofSysOpenAUPub.v -- ARM S (+0xb8) AND THE PUBLICATION, at the ARMED
   post: [ProofSysOpen.so_tail_pub] with [SpecSysOpen.sys_open_post]
   replaced by [SpecSysOpenAU.open_post_ok_plain]'s success arm.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the open AU
   prover).  A PARALLEL block beside the landed one; the failure tails
   ([ProofSysOpenTails]) are reused VERBATIM, because none of them moves an
   fs-abstract resource -- only this one does.

   ==== THE ONE ADDITION: THE DESCRIPTOR IS TYPED =======================

   The landed tail hands back [FdSlots.fd_frags_any], the bundle at an
   EXISTENTIAL state list.  [SpecSysOpenAU.open_fd_ok] asks for it at an
   EXPLICIT list whose row at the new descriptor is
   [FdOpen (om_readable vom) (om_writable vom) t] -- and that is not new
   work but a STRENGTHENING OF AN EXISTING OUTPUT: [ProofSysOpenParts.
   so_publish] already computes exactly that state ([stpub], with
   [fdstate_ok inum C stpub]), and [ProcInv.proc_priv_settle] already moves
   the descriptor's fragment to it.  All this block does is open the bundle
   with [fd_frags_acc] instead of [fd_frags_any_acc] -- so the row survives
   -- and read [stpub]'s shape off [fdstate_ok_inj].

   THE MODE BITS come from [ProofSysOpenAUBits]: the two cells the stores
   wrote are [(om & 1) xor 1] and [0 <u (om & 3)], which ARE the contract's
   [om_readable] / [om_writable] of the caller's own trapframe word.

   THE ARM ITSELF IS THE CALLER'S.  Which of the three success arms
   (DEVICE / FILE / DIR) is being delivered depends on [di_type dn], which
   the STORE block above knows and this block does not -- so the arm
   arrives as a wand from [open_fd_ok] to [open_post_ok_plain] and this
   block only earns its antecedent. *)
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
Require Import InstrBytes.
Require Import RegFile WpNext.
Require Import WpMmodeLeafBase.
Require Import StackOwn.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import WpLock.
Require Import WpSconfMem.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import SpecPanic.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import BioInv.
(* THE PAYLOAD'S OWN VOCABULARY (durable-disk 2b-inode-3): [top_frag],
   [fs_gamma_L], [era_node] / [inode_rec_local].  IMPORTED BEFORE
   [FsBlocks] on purpose -- the [FsState*] stack exports [fs_view] and
   [byte_range], both of which have live twins below, and the LAST import
   wins (durable-notes, "AND WHERE THAT IMPORT COLLIDES, PUT IT EARLY"). *)
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import FileOffProtocol.   (* [proto_store_free]: the free off cell is the free word (r25 item 24) *)
Require Import OffBox.   (* [off_rows] -- the fd box birth borrows the inode's rows (r25 item 33) *)
Require Import DirView.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecArgint.
Require Import SpecEndOp.
Require Import SpecIunlock.
Require Import SpecIunlockput.
Require Import SpecFileclose.
Require Import SpecFdalloc.
Require Import SpecItrunc.
Require Import ProofSysOpenParts.
Require Import ProofSysOpenTails.
Require Import SieCapCtx.   (* [sie_cap_gpr_own_ctx_acc]: the off box birth borrows the running token (r25) *)
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Local Open Scope Z_scope.

Require Import FsBytesGamma.
Require Import SpecSysOpenAU.
Require Import ProofSysOpenAUBits.
Require Import ProofSysOpenAUParts.
Require Import FsAbs.
Require Import TsoCtx.

Local Open Scope Z_scope.

Set Printing Depth 40.

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.

Module SysOpenAUPub (Iunlock : IUNLOCK) (Iunlockput : IUNLOCKPUT)
                    (EndOp : END_OP) (Fileclose : FILECLOSE).

Module Tails := SysOpenTails Iunlock Iunlockput EndOp Fileclose.

Section ProofSysOpenAUPub.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Lemma so_tail_pub_au `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (pd pav pu : mword 64)
      (gil gisl : gname)
      (kk : nat) (qi s : Qp) (gy : gname) (loy tly : nat) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (kf fd : nat) (l : list nat) (C : fcontent) (pn : fpnames)
      (om voff : mword 32) (nsj : nat)
      (u : nat) (pidv : mword 32) (dqb dqs : dfrac)
      (U : ustate) (sts : list fdstate)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w6 w23 w24 : mword 64)
      (bp : nat -> bv 8)
      (* ---- the AU side ---- *)
      (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (t : fdtype) :
    qi = s ->   (* r25 shapes: the parked ident fraction IS the travelling share (so_publish) *)
    (K_iunlock <= K - 24)%nat -> (K_end_op <= K - 24)%nat ->
    (24 <= K)%nat -> ((K - 24) + 24 = K)%nat ->
    (kk < NINODE)%nat ->
    bv_unsigned inum < 16 * Z.of_nat icfg_nib ->
    log_geom_ok fsc_cov fsc_logst ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    (kf < NFILE)%nat -> (fd < NOFILE)%nat ->
    length (pv_ofile (us_V U)) = NOFILE ->
    fd_frees (pv_ofile (us_V U)) = fd :: l ->
    fc_ip C = ientry kk ->
    (fc_type C = FD_INODE \/ fc_type C = FD_DEVICE) ->
    fc_writable C = trunc8 (so_wr_word om) ->
    (* ...and the READABLE cell, which nothing used to ask for: it is what
       the published descriptor's [FdSlots.FdOpen] reports as its read flag,
       so the tail now has to carry it down to [so_publish] alongside the
       writable one. *)
    fc_readable C = trunc8 (so_rd_word om) ->
    (bv_unsigned (di_type dn) = T_DIR_z -> om = (mword_of_int 0 : mword 32)) ->
    (* the owner's ruling (2026-08-29), exactly as the landed twin carries
       it.  On THIS lane the caller does not have to earn it: the store
       block already ties the type word to the inode's type in both
       directions ([so_stores_au]'s [Htd]/[Hti]), because the AU's [t] is
       read off the same test. *)
    (fc_type C = FD_INODE -> bv_unsigned (di_type dn) <> FsImg.T_DEVICE_z) ->
    (fc_type C = FD_INODE -> off_wf voff) ->
    (* ---- the AU side: the omode word IS the caller's argument, and the
       descriptor's type is the one the published content names ---- *)
    om = arg_int32 vom ->
    (fc_type C = FD_INODE /\ t = FdInode (bv_unsigned inum))
    \/ (fc_type C = FD_DEVICE /\ t = FdDevice (bv_unsigned (fc_major C))) ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    so_sp sp0 M -> so_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs3 : mword 64) = (mword_of_int (Z.of_nat fd) : mword 64) ->
    so_al sp0 ->
    sie_cap_gpr KT1 M (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SO + 0xb8)) -∗
    panic_env -∗
    bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
    log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
    fs_crash_seam fsc_cov fsc_logst -∗
    gen_cert -∗
    itable_inv -∗
    ic_escrow fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kk -∗
    is_sleeplock_genl gil gisl (i_lock (ientry kk)) "inode"%string (ic_slp fsc_ic kk) (slh_tok (icfg_isl kk)) -∗
    sleeplocked_q gisl s (i_lock (ientry kk)) pidv -∗
    ⌜(loy <= tly)%nat⌝ -∗
    IcacheRef.cred_floor loy tly -∗
    IcacheInv.iref_claims -∗
    ic_tx_dep fsc_ic kk s icfg_dev inum gy loy -∗
    off_rows off_cfg kk cur_ctx -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} icfg_dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    (* the payload's freeze token (§3.9, RULING A-prime), relayed to
       [so_tail_s]'s iunlock *)
    ifreeze_off (bv_unsigned inum) -∗
    (∃ loK tlK : nat,
       ⌜(loK <= tlK)%nat⌝ ∗ IcacheRef.cred_floor loK tlK ∗
       IcacheRef.inode_ref_short_genlo kk (qi + s)%Qp qi icfg_dev inum gy loK) -∗
    (* its PROVENANCE UNIT (item 7a-wire): the parent parks in the fd slot's
       [cinv] as [IcacheRef.inode_held_short], and that is one of the unit's
       two rest homes, so it travels with [Hkeep] the whole way. *)
    runit_any (bv_unsigned inum) -∗
    (* the six raw pieces the walk carries across the tail *)
    fref_tok gf kf 1 -∗
    flive_tok kf -∗
    file_fields kf 1 C -∗
    fpay_tok gf kf 1 pn -∗
    (* the fd's off cell, TYPE-INDEXED (r25 item 24): the inode arm stored
       zero into the free cell and holds the word at the running context;
       the device arm never touches [f->off] and carries the free cell *)
    (if bool_decide (fc_type C = FD_INODE) then a_foff kf ↦₄ voff else off_free kf 1) -∗
    (* THE UNTYPED SLOT'S OWN UNIT, released when [so_open_slot] took the
       reference apart and handed straight back to the ledger here: the
       publication below parks the walk's inode in this same entry, so the
       entry ends up holding exactly what it held before. *)
    iref_slot -∗
    (* the process, split at the descriptor table by fdalloc *)
    proc_priv_core (proc_addr jx) pidv U -∗
    proc_ofiles_owe gf (pv_fdg (us_V U)) (proc_addr jx)
      (pv_ofile (upd_ofile (us_V U) fd (fnode kf))) ({[fd]} ∪ ∅) -∗
    procs_inv gs -∗
    dev_inv fsc_uart fsc_disk -∗
    disk_geom fsc_disk pd pav pu -∗
    is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
    log_opb icfg_log u -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
    bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
    bslots 3 -∗
    iref_slots nsj -∗
    fd_slot -∗
    (* the descriptor-state fragments, threaded exactly as the fd unit above
       is: sys_open spends one access, at the settle. *)
    fd_frags (pv_fdg (us_V U)) sts -∗
    (* ...and the descriptor's own AUTHORITY, at [FdClosed]: fdalloc handed
       it out when it made the cell non-null, and the settle below moves it
       to the new file's type. *)
    fd_st_auth (pv_fdg (us_V U)) fd FdClosed -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
    (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 23) ↦₈[KT1] w23 -∗
    (pa_stk sp0 24) ↦₈[KT1] w24 -∗
    (* ---- THE ARM, as a wand: which of the three success arms is being
       delivered is the STORE block's knowledge (it read [ip->type]), not
       this block's.  All this block earns is the antecedent. ---- *)
    (∀ r : mword 64,
       open_fd_ok gf (proc_addr jx) pidv U
         (om_readable vom) (om_writable vom) t sts r -∗
       open_post_ok_plain (fs_gamma_L fsc_fs) gf (proc_addr jx) pidv vom
         P Φo Φt sts U r) -∗
    wp_next true (proc_addr jx)
      (so_cont_au gf nsj
               dqb dqs (proc_addr jx) pidv vom U sts P Pmiss Φo Φt m K eb b lks) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hqs HKiu HKeo HK24 Kpop Hkk Hinb Hgeom Hj Hgl Hlkempty Hkf Hfdlt
           Hlen Hfrees Hip Htyor Hwrb Hrdw Hdir Hdvw Hwf Hom Htyt Hsp0 HMsp HMthr
           HMs1 HMs3 Hal.
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen
              #Hitinv #Hesck #Hslkk Hslkd %Hley #Hfly #Hclaimsy Hdep Hoffr Hidev Hiinum Hivalid
              Hload #Hshot Hfrz Hkeep Hru Hfref Hflive Hflds Hfpn Hfoff
              Hiru Hcore Howe #Hprocs #Hdev #Hgeo #Hdlk Hop Hsbb Hsbi #Hbmres Hbsl
              Hisl Hfds Hfrag Hauth Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
              Harm Hcont".
    iDestruct (proc_priv_core_bare_acc with "Hcore") as "[Hpbare Hcback]".
    (* ---- THE BIRTH OF THE FD'S OFF BOX (r25 item 24), under the lock:
           the landed twin's block verbatim -- on the FD_INODE arm the
           stored [f->off] word is deposited into a fresh box registered in
           the inode's rows; on the FD_DEVICE arm the word simply joins the
           visibility-free tier. ---- *)
    iApply fupd_wp.
    iDestruct (sie_cap_gpr_own_ctx_acc with "Hcg") as "[Hrun Hcgb]".
    iRename "Hoffr" into "Hrows".
    iAssert (|={⊤}=> own_context cur_ctx ∗ off_rows off_cfg kk cur_ctx ∗
               ∃ γb : box_names,
                 if bool_decide (fc_type C = FD_INODE)
                 then off_fd kf 1 γb C else off_free kf 1)%I
      with "[Hrun Hrows Hfoff]" as ">(Hrun & Hrows & %γb & Hcoff)".
    { destruct (bool_decide (fc_type C = FD_INODE)) eqn:Hbd.
      - apply bool_decide_eq_true_1 in Hbd.
        iMod (so_deposit ⊤ kk kf C ltac:(solve_ndisj) Hkk Hip Hbd
                with "Hrun [Hfoff] Hrows") as "(Hrun & Hrows & %γb & Hfd)".
        { iExists voff. iFrame "Hfoff". iPureIntro. exact (Hwf Hbd). }
        iModIntro. iFrame "Hrun Hrows". iExists γb. iExact "Hfd".
      - iModIntro. iFrame "Hrun Hrows". iExists inhabitant. iExact "Hfoff". }
    iDestruct ("Hcgb" with "Hrun") as "Hcg".
    iRename "Hrows" into "Hoffr".
    iModIntro.
    iApply (Tails.so_tail_s (CID0 := CID0) gs jx gl pd pav pu
              gil gisl kk s gy loy tly inum dn bm
              (mword_of_int (Z.of_nat fd) : mword 64) u pidv (DfracOwn (1/4))
              m M sp0 K eb b lks w6 w23 w24 bp U
              HKiu HKeo HK24 Kpop Hkk Hgeom Hj Hgl Hlkempty Hsp0 HMsp HMthr
              HMs1 HMs3 Hal
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hitinv Hesck Hslkk Hslkd [//] Hfly Hclaimsy Hdep Hoffr Hidev Hiinum Hivalid
                    Hload Hshot Hfrz Hpbare Hprocs Hdev Hgeo Hdlk Hop Hf1 Hf2 Hf3
                    Hf4
                    Hf5 Hf6 HbP H23 H24
                    [Hkeep Hru Hfref Hflive Hflds Hfpn Hcoff Hiru Hcback Howe
                     Hsbb Hsbi Hbsl Hisl Hfds Hfrag Hauth Harm Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc
                                         Hpbare Hshr".
    iDestruct ("Hcback" with "Hpbare") as "Hcore".
    (* ---- THE PUBLICATION: one ghost step ---- *)
    (* the two mode cells are C bools, and THAT is what the descriptor's
       [FdOpen rb wb] will claim: [f->readable] is [!(omode & O_WRONLY)] and
       [f->writable] the [snez], both a bit by construction. *)
    destruct (so_rd_byte_bool om) as [rb Hrdb].
    destruct (so_wr_byte_bool om) as [wb Hwdb].
    iApply fupd_wp.
    (* A6.146: the retained parent arrives GENLO with its credential. *)
    iDestruct "Hkeep" as (loK tlK) "(%HleK & #HflK & Hkeep)".
    iMod (so_publish ⊤ gf kf kk qi s gy inum (di_type dn) C pn γb om rb wb
            loK tlK
            Hqs ltac:(solve_ndisj) Hkk Hinb Hip Htyor Hwrb
            ltac:(rewrite Hrdw; exact Hrdb) ltac:(rewrite Hwrb; exact Hwdb)
            Hdir Hdvw HleK
            with "HflK Hkeep Hru Hshr Hshot Hfref Hflive Hflds Hfpn Hcoff")
      as (stpub) "[%Hokpub Href]".
    (* the descriptor's ghost state: the file is FD_INODE or FD_DEVICE, so
       the descriptor sys_open returns is OPEN at that type -- [stpub] is the
       state the publish minted, and [Hokpub] ties it to the file. *)
    (* THE ONE GHOST STEP: the descriptor fdalloc opened is now OPEN, at the
       new file's type.  fdalloc handed out its authority at [FdClosed] and
       the matching fragment comes out of the bundle -- which is why
       sys_open's contract takes [fd_frags_any] at all. *)
    (* AT THE CALLER'S OWN BUNDLE (the landed row since 34375379c): the
       row the settle writes SURVIVES into the receipt
       ([SpecSysOpenAU.open_fd_ok]'s [⌜sts !! fd = Some FdClosed⌝] and its
       [<[fd := ...]> sts]), and the loan's authority is what identifies
       that row -- the landed twin's [fd_st_agree] step. *)
    iRename "Hfrag" into "Hfrags".
    iDestruct (fd_frags_len with "Hfrags") as %Hlensts.
    assert (Hstqe : is_Some (sts !! fd))
      by (apply lookup_lt_is_Some_2; rewrite Hlensts; exact Hfdlt).
    destruct Hstqe as [stq Hstq].
    iDestruct (fd_frags_acc (pv_fdg (us_V U)) sts fd stq Hstq with "Hfrags")
      as "[Hfr Hfrback]".
    iDestruct (fd_st_agree (pv_fdg (us_V U)) fd FdClosed stq with "Hauth Hfr")
      as "%Hstqcl".
    iMod (proc_priv_settle gf (proc_addr jx) pidv U fd kf 1 stpub FdClosed stq
                 Hfdlt Hlen Hkf (fdstate_ok_open _ C stpub Hokpub (or_intror Htyor))
                 with "Hcore Howe Href Hauth Hfr") as "[Hpriv Hfr]".
    iDestruct ("Hfrback" $! stpub with "Hfr") as "Hfrags".
    iModIntro.
    (* [stpub] IS the typed state the contract names: the two mode cells
       hold the caller's own omode bits ([ProofSysOpenAUBits]) and the type
       is [Htyt]'s, so [fdstate_ok_inj] pins it. *)
    assert (Hstok : fdstate_ok inum C
                      (FdOpen (om_readable vom) (om_writable vom) t)).
    { assert (Hrd : fc_readable C
                    = ((if om_readable vom
                        then mword_of_int 1 else mword_of_int 0) : mword 8))
        by (rewrite Hrdw Hom; apply soau_rd_byte).
      assert (Hwr : fc_writable C
                    = ((if om_writable vom
                        then mword_of_int 1 else mword_of_int 0) : mword 8))
        by (rewrite Hwrb Hom; apply soau_wr_byte).
      destruct Htyt as [[Hct ->] | [Hct ->]]; cbn; by repeat split. }
    assert (Hpub : stpub = FdOpen (om_readable vom) (om_writable vom) t)
      by exact (fdstate_ok_inj inum C stpub _ Hokpub Hstok).
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iDestruct (iref_slots_combine nsj 1 with "Hisl Hiru") as "Hisl".
    replace (nsj + 1)%nat with (S nsj) by lia.
    iApply ("Hcont" $! mf (S nsj) with "[%] [%] Hcg Hown Htce Hcce Hpc
              Hsbb Hsbi Hbsl Hisl [Hpriv Hfds Hfrags Harm]").
    { exact Hcsf. }
    { reflexivity. }
    (* THE ARM: the success side of [open_arms_plain], at the caller's own
       wand and the descriptor this walk installed. *)
    rewrite /open_arms_plain. iFrame "Hfds". iRight.
    iApply "Harm". rewrite /open_fd_ok.
    iExists fd, l, kf.
    iSplitR.
    { iPureIntro. split_and!.
      - rewrite Ha0f; reflexivity.
      - exact Hfrees.
      - rewrite <- Hstqcl in Hstq. exact Hstq. }
    rewrite -Hpub. iFrame "Hpriv Hfrags".
  Qed.

  (* ---- the two field reads the walk makes into the LOCKED record, as
     accessors: [ic_loaded] is carried whole across the block and opened
     for exactly one halfword at a time. ---- *)

End ProofSysOpenAUPub.

End SysOpenAUPub.
