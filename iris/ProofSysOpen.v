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
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import ByteBuf.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr WpSmodeHalf.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import SpecPanic.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
(* THE PAYLOAD'S OWN VOCABULARY (durable-disk 2b-inode-3): [top_frag],
   [fs_gamma_L], [era_node] / [inode_rec_local].  IMPORTED BEFORE
   [FsBlocks] on purpose -- the [FsState*] stack exports [fs_view] and
   [byte_range], both of which have live twins below, and the LAST import
   wins (durable-notes, "AND WHERE THAT IMPORT COLLIDES, PUT IT EARLY"). *)
Require Import FsStateEra.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import DinodeSlot.
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KvmSpec.
Require Import DirView.
Require Import FileInvDefs.
Require Import FileInv.
Require Import UserPtTree.
Require Import ProcInv.
Require Import SpecArgint.
Require Import SpecArgstr.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIput.
Require Import SpecIlock.
Require Import SpecIunlock.
Require Import SpecIunlockput.
Require Import SpecFileclose.
Require Import SpecFilealloc.
Require Import SpecFdalloc.
Require Import SpecItrunc.
Require Import SpecPrintk.
Require Import SpecDirlink.
Require Import SpecNamex.
Require Import SpecNamei.
Require Import SpecCreate.
Require Import CodeSysOpen.
Require Import SpecSysOpen.
Require Import SysOpenBudget.
Require Import ProofKforkParts.       (* [proc_priv_tfp_valid], argint's premise *)
Require Import ProofSysOpenParts.
Require Import ProofSysOpenTails.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
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

(* [neq_vec] is [negb (eq_vec ...)], so the two BNE premises are the two
   readings of the type cluster's [so_ty_eq] / [so_ty_ne]. *)
Lemma so_neq_of_eq (x y : mword 64) : eq_vec x y = true -> neq_vec x y = false.
Proof. unfold neq_vec. intro H. rewrite H. reflexivity. Qed.

Lemma so_neq_of_ne (x y : mword 64) : eq_vec x y = false -> neq_vec x y = true.
Proof. unfold neq_vec. intro H. rewrite H. reflexivity. Qed.

(* WHAT SURVIVES namei's WALK, in the ledger's own vocabulary.  The SET-form
   contract reports [n - (walk_spend w + (if ok then 0 else 1)) <= n'] and
   the join needs [iput_units]; [SysOpenBudget.so_armC_closes] is the same
   fact at the exact figures.  Kept as a plain [nat] lemma because a hot
   [lia] inside a syscall-altitude Iris goal is what durable-notes warns
   about. *)
Lemma so_bud_iput (n' : nat) (w ok : bool) :
  ((MAXOPBLOCKS - (walk_spend w + (if ok then 0%nat else 1%nat)))%nat <= n')%nat ->
  (iput_units <= n')%nat.
Proof. unfold walk_spend, iput_units, MAXOPBLOCKS. destruct w, ok; lia. Qed.

Module SysOpenProof (Argint : ARGINT) (Argstr : ARGSTR) (BeginOp : BEGIN_OP)
                    (Create : CREATE) (Namei : NAMEI) (Ilock : ILOCK)
                    (Iunlock : IUNLOCK) (Iunlockput : IUNLOCKPUT)
                    (EndOp : END_OP) (Fileclose : FILECLOSE)
                    (Itrunc : ITRUNC) (Filealloc : FILEALLOC)
                    (Fdalloc : FDALLOC) : SYSOPEN.

Module Tails := SysOpenTails Iunlock Iunlockput EndOp Fileclose.

Section ProofSysOpenBody.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rz  := (mword_of_int 0 : mword 5).

  (* THE 1/2 + 1/2 SPLIT at [↦₈] IS GONE.  It used to hand [so_publish] the
     off-borrow invariant's half of [f->ip] after the [sd s1,24(s2)] wrote the
     cell whole; the invariant keeps no fraction of that cell since the
     off-borrow ruling (FileInvDefs.v's header, tso-port.md §0.16′), so the
     stored cell goes into [file_fields] whole and nothing is split. *)

  (* ================================================================== *)
  (*  THE SYSCALL'S EXIT CONTINUATION, NAMED ONCE.                       *)
  (*                                                                    *)
  (*  [SpecSysOpen]'s, minus the two structural cells the body below the *)
  (*  join never touches (sb_ninodes / sb_size) and minus the page-table *)
  (*  report, which is argstr's and is settled above the join.  The one  *)
  (*  ledger clause is the join's own: the iref count moves by at most   *)
  (*  one (the failure arms' [iunlockput] hands a slot back; the success *)
  (*  arm parks it in [f->ip]).  Nothing bitmap-shaped crosses: the pool *)
  (*  lives in the persistent [bitmap_inv] the whole walk carries.        *)
  (* ================================================================== *)
  (* Peel the one unit sys_open holds back for [fileclose]'s loan (see the
     [iref_slots nsj] row on [so_alloc]): the block takes it, and folds it
     back before it returns, so the ledger is an equality either way. *)
  Local Lemma so_iref_take (n : nat) :
    (1 <= n)%nat -> iref_slots n -∗ iref_slot ∗ iref_slots (n - 1).
  Proof.
    intros Hn. rewrite /iref_slot.
    replace n with (1 + (n - 1))%nat at 1 by lia.
    iIntros "H". iApply (iref_slots_split with "H").
  Qed.

  Definition so_cont `{GEN : GenId} `{XI : CurCtx}
      (gf : gname) (bn : bio_names) (gfs : fs_names)
      (cov : gset Z) (logstart bmapstart inodestart size : Z)
      (nsj : nat) (dqb dqs : dfrac)
      (pj : mword 64) (pidv : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb b : bool) (lks : gset string)
      : CpuId -> iProp Σ :=
    fun (CIDx : CpuId) =>
      (∀ (mf : regfile) (ns' : nat),
         ⌜callee_saved m mf⌝ -∗
         (* EXACTLY ONE MORE THAN WENT IN, on every arm.  The success arm
            releases the untyped slot's own unit ([so_open_slot]) and parks
            the walk's inode in [f->ip]; every failure arm iputs that inode
            instead.  Either way one unit comes back and nothing is spent,
            which is what lets [SpecSysOpen] promise the whole allowance
            back and hence what makes sys_open wireable into the dispatch. *)
         ⌜ns' = S nsj⌝ -∗
         sie_cap_gpr KT1 mf K b pj -∗
         cpu_own 0 eb pj b lks -∗
         trap_csrs_ext KT1 eb -∗
         cpu_claim_ext eb pj -∗
         pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
         sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
         sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
         bslots 3 -∗
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
  Lemma so_tail_pub `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (size : Z) (dev : mword 32)
      (kk : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (kf fd : nat) (l : list nat) (C : fcontent) (pn : fpnames)
      (om voff : mword 32) (nsj : nat)
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
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    itable_inv -∗
    ic_escrow cn gfs gi cov logstart kk -∗
    is_sleeplock_gen gil gisl (i_lock (ientry kk)) "inode"%string (ic_tok cn kk) (slh_tok (icfg_isl kk)) -∗
    sleeplocked_q gisl s (i_lock (ientry kk)) pidv -∗
    ic_deposit cn kk (DepShr s dev inum gy) -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    (* the payload's freeze token (§3.9, RULING A-prime), relayed to
       [so_tail_s]'s iunlock *)
    ifreeze_off (bv_unsigned inum) -∗
    inode_ref_short_gen kk (qi + s)%Qp qi dev inum gy -∗
    (* its PROVENANCE UNIT (item 7a-wire): the parent parks in the fd slot's
       [cinv] as [IcacheRef.inode_held_short], and that is one of the unit's
       two rest homes, so it travels with [Hkeep] the whole way. *)
    runit_any (bv_unsigned inum) -∗
    (* the six raw pieces the walk carries across the tail *)
    fref_tok gf kf 1 -∗
    flive_tok gf kf -∗
    file_fields kf 1 C -∗
    fpay_tok gf kf 1 pn -∗
    a_foff kf ↦₄ voff -∗
    (* THE UNTYPED SLOT'S OWN UNIT, released when [so_open_slot] took the
       reference apart and handed straight back to the ledger here: the
       publication below parks the walk's inode in this same entry, so the
       entry ends up holding exactly what it held before. *)
    iref_slot -∗
    (* the process, split at the descriptor table by fdalloc *)
    proc_priv_core (proc_addr jx) pidv V -∗
    proc_ofiles_owe gf (proc_addr jx)
      (pv_ofile (upd_ofile V fd (fnode kf))) ({[fd]} ∪ ∅) -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (λ ξ : CtxId, disk_res (XI := ξ) gd pd pav pu) -∗
    log_op g u -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_inv gfs bmapstart cov logstart size -∗
    bslots 3 -∗
    iref_slots nsj -∗
    fd_slot -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
    (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 23) ↦₈[KT1] w23 -∗
    (pa_stk sp0 24) ↦₈[KT1] w24 -∗
    wp_next true (proc_addr jx)
      (so_cont gf bn gfs cov logstart bmapstart inodestart size nsj
               dqb dqs (proc_addr jx) pidv V m K eb b lks) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKiu HKeo HK24 Kpop Hkk Hdevc Hinb Hgeom Hj Hgl Hlkempty Hkf Hfdlt
           Hlen Hfrees Hip Htyor Hwrb Hdir Hwf Hsp0 HMsp HMthr HMs1
           HMs3 Hal.
    subst dev.
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen
              #Hitinv #Hesck #Hslkk Hslkd Hdep Hidev Hiinum Hivalid
              Hload #Hshot Hfrz Hkeep Hru Hfref Hflive Hflds Hfpn Hfoff
              Hiru Hcore Howe #Hprocs #Hdev #Hgeo #Hdlk Hop Hsbb Hsbi #Hbmres Hbsl
              Hisl Hfds Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24 Hcont".
    iDestruct (proc_priv_core_bare_acc with "Hcore") as "[Hpbare Hcback]".
    iApply (Tails.so_tail_s (CID0 := CID0) gs jx gl gu gd gk pd pav pu bn g gfs
              gi cn gil gisl cov logstart icfg_dev kk s gy inum dn bm
              (mword_of_int (Z.of_nat fd) : mword 64) u pidv (DfracOwn (1/4))
              m M sp0 K eb b lks w6 w23 w24 bp V
              HKiu HKeo HK24 Kpop Hkk Hgeom Hj Hgl Hlkempty Hsp0 HMsp HMthr
              HMs1 HMs3 Hal
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hitinv Hesck Hslkk Hslkd Hdep Hidev Hiinum Hivalid
                    Hload Hshot Hfrz Hpbare Hprocs Hdev Hgeo Hdlk Hop Hf1 Hf2 Hf3
                    Hf4
                    Hf5 Hf6 HbP H23 H24
                    [Hkeep Hru Hfref Hflive Hflds Hfpn Hfoff Hiru Hcback Howe
                     Hsbb Hsbi Hbsl Hisl Hfds Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc
                                         Hpbare Hshr".
    iDestruct ("Hcback" with "Hpbare") as "Hcore".
    (* ---- THE PUBLICATION: one ghost step ---- *)
    iApply fupd_wp.
    iMod (so_publish ⊤ gf kf kk qi s gy inum (di_type dn) C pn om voff
            ltac:(solve_ndisj) ltac:(solve_ndisj) Hkk Hinb Hip Htyor Hwrb Hdir
            Hwf
            with "Hkeep Hru Hshr Hshot Hfref Hflive Hflds Hfpn Hfoff")
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
    iDestruct (iref_slots_combine nsj 1 with "Hisl Hiru") as "Hisl".
    replace (nsj + 1)%nat with (S nsj) by lia.
    iApply ("Hcont" $! mf (S nsj) with "[%] [%] Hcg Hown Htce Hcce Hpc
              Hsbb Hsbi Hbsl Hisl Hpost").
    { exact Hcsf. }
    { reflexivity. }
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
    iIntros "H".
    iDestruct (ic_loaded_open with "H") as (data)
      "(%Hok & %Hrl & %Hdok & %Hddix & %Hdoc & %Hduq & Hl & Hd & Hm & Ha & Hr &
        Hb & Hv & Hw & Ht)".
    iFrame "Hm". iIntros "Hm".
    iApply (ic_mk_loaded gfs gi cov logstart k inum dn bm data Hok Hrl Hdok Hddix
              Hdoc Hduq with "Hl Hd Hm Ha Hr Hb Hv Hw Ht").
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
  Lemma so_stores `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
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
    sie_cap_gpr KT1 N (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SO + 0x88)) -∗
    panic_env -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    itable_inv -∗
    ic_escrow cn gfs gi cov logstart kk -∗
    ireg_inv gi gfs inodestart nib -∗
    is_sleeplock_gen gil gisl (i_lock (ientry kk)) "inode"%string (ic_tok cn kk) (slh_tok (icfg_isl kk)) -∗
    sleeplocked_q gisl s (i_lock (ientry kk)) pidv -∗
    ic_deposit cn kk (DepShr s dev inum gy) -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    (* the payload's freeze token (§3.9, RULING A-prime), relayed to
       [so_tail_s]'s iunlock *)
    ifreeze_off (bv_unsigned inum) -∗
    inode_ref_short_gen kk (qi + s)%Qp qi dev inum gy -∗
    (* its PROVENANCE UNIT (item 7a-wire): the parent parks in the fd slot's
       [cinv] as [IcacheRef.inode_held_short], and that is one of the unit's
       two rest homes, so it travels with [Hkeep] the whole way. *)
    runit_any (bv_unsigned inum) -∗
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
    (* the untyped slot's own unit, on its way back to the ledger -- see
       [so_tail_pub]'s row for why the entry ends up owing nothing *)
    iref_slot -∗
    proc_priv_core (proc_addr jx) pidv V -∗
    proc_ofiles_owe gf (proc_addr jx)
      (pv_ofile (upd_ofile V fd (fnode kf))) ({[fd]} ∪ ∅) -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (λ ξ : CtxId, disk_res (XI := ξ) gd pd pav pu) -∗
    log_op g u -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_inv gfs bmapstart cov logstart size -∗
    bslots 3 -∗
    iref_slots nsj -∗
    fd_slot -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
    (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 23) ↦₄[KT1] lo -∗
    (pa_add (pa_stk sp0 23) 4) ↦₄[KT1] om -∗
    (pa_stk sp0 24) ↦₈[KT1] w24 -∗
    wp_next true (proc_addr jx)
      (so_cont gf bn gfs cov logstart bmapstart inodestart size nsj
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
    iIntros "Hcg Hown Htce Hcce #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen
              #Hitinv #Hesck #Hireg #Hslkk Hslkd Hdep Hidev Hiinum
              Hivalid Hload #Hshot Hfrz Hkeep Hru Hfref Hflive Hfpn Hfty Hfrd Hfwr
              Hfpip Hfmaj Hfip Hfoff Hiru Hcore Howe #Hprocs #Hdev #Hgeo #Hdlk Hop
              Hsbb Hsbi #Hbmres Hbsl Hisl Hfds Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP
              H23lo H23hi H24 Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* ===== +0x88 sd s1,24(s2) -- f->ip = ip ===== *)
    iEval (rewrite /a_fip /foff_of) in "Hfip".
    iApply (wp_sd_s_sconf (kt := KT1) (ktd := KT0) (CID := CID0) (mword_of_int (SO + 0x88)) Rs1 Rs2
              (mword_of_int 24 : mword 12) N (K - 24)%nat ipold b
              with "Hcg Hpc [] [Hfip]").
    { iApply (soi_088 with "Htext"). }
    { iEval (rgne; rewrite HNs2). iExact "Hfip". }
    iIntros (CID1 Hq1) "Hcg Hpc Hfip".
    iEval (rgne; rewrite HNs2; rgne; rewrite HNs1) in "Hfip".
    assert (Hpp88 : add_vec_int (mword_of_int (SO + 0x88) : mword 64) 4
                    = mword_of_int (SO + 0x8c)) by pcw.
    iEval (rewrite Hpp88) in "Hpc".
    (* ===== +0x8c lw a5,-180(s0) -- the omode word ===== *)
    iApply (wp_lw_s_sconf (CID := CID1) (mword_of_int (SO + 0x8c)) Ra5 Rs0
              (mword_of_int 3916 : mword 12) N (K - 24)%nat om b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [H23hi]").
    { iApply (soi_08c with "Htext"). }
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
              with "Hcg Hpc []").
    { iApply (soi_090 with "Htext"). }
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
              with "Hcg Hpc []").
    { iApply (soi_094 with "Htext"). }
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
    iApply (wp_sb_s_sconf (kt := KT1) (ktd := KT0) (CID := CID4) (mword_of_int (SO + 0x98)) Ra4 Rs2
              (mword_of_int 8 : mword 12) N3 (K - 24)%nat rd0 b
              with "Hcg Hpc [] [Hfrd]").
    { iApply (soi_098 with "Htext"). }
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
              with "Hcg Hpc []").
    { iApply (soi_09c with "Htext"). }
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
              with "Hcg Hpc []").
    { iApply (soi_0a0 with "Htext"). }
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
    iApply (wp_sb_s_sconf (kt := KT1) (ktd := KT0) (CID := CID7) (mword_of_int (SO + 0xa4)) Ra4 Rs2
              (mword_of_int 9 : mword 12) N5 (K - 24)%nat wr0 b
              with "Hcg Hpc [] [Hfwr]").
    { iApply (soi_0a4 with "Htext"). }
    { iEval (rgne; rewrite HN5s2). iExact "Hfwr". }
    iIntros (CID8 Hq8) "Hcg Hpc Hfwr".
    iEval (rgne; rewrite HN5s2; rgne; rewrite HN5a4) in "Hfwr".
    assert (Hppa4 : add_vec_int (mword_of_int (SO + 0xa4) : mword 64) 4
                    = mword_of_int (SO + 0xa8)) by pcw.
    iEval (rewrite Hppa4) in "Hpc".
    (* ---- the published CONTENT, and the six cells as [file_fields] ---- *)
    set (C := MkFContent tyw (trunc8 (so_rd_word om)) (trunc8 (so_wr_word om))
                pip (ientry kk) maj).
    iAssert (file_fields kf 1 C) with "[Hfty Hfrd Hfwr Hfpip Hfip Hfmaj]"
      as "Hflds".
    { rewrite /file_fields /C; cbn [fc_type fc_readable fc_writable fc_pipe
                                    fc_ip fc_major].
      rewrite /a_ftype /a_freadable /a_fwritable /a_fpipe /a_fip /a_fmajor
              /foff_of.
      iFrame "Hfty Hfrd Hfwr Hfpip Hfip Hfmaj". }
    (* ===== +0xa8 andi a5,a5,1024 -- O_TRUNC ===== *)
    iApply (wp_andi_s_sconf (CID := CID8) (mword_of_int (SO + 0xa8)) Ra5 Ra5
              (mword_of_int 1024 : mword 12) (so_and om 1024) N5 (K - 24)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HN5a5; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_0a8 with "Htext"). }
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
                with "Hcg Hpc []").
      { iApply (soi_0ac with "Htext"). }
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
                icfg_dev kk qi s gy inum dn bm kf fd l C pn om voff nsj
                (S (S u2)) pidv dqb dqs V m N6 sp0 K eb b lks w6
                (word_of_words lo om) w24 bp
                HKiu HKeo HK24 Kpop Hkk eq_refl Hinb Hgeom Hj Hgl Hlkempty Hkf
                Hfdlt Hlen Hfrees eq_refl Htyor eq_refl Hdir Hwf
                Hsp0 HN6sp HN6thr HN6s1 HN6s3 Hal
                with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                      Hitinv Hesck Hslkk Hslkd Hdep Hidev Hiinum Hivalid
                      Hload Hshot Hfrz Hkeep Hru Hfref Hflive Hflds Hfpn Hfoff
                      Hiru Hcore Howe Hprocs Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres
                      Hbsl Hisl Hfds Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
                      Hcont"). }
    (* ---- O_TRUNC set: the type test at +0xb4 ---- *)
    iApply (wp_cbeqz_fall_s_sconf (CID := CID9) (mword_of_int (SO + 0xac))
              (mword_of_int 6 : mword 8) (Cregidx (mword_of_int 7)) Ra5
              N6 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HN6a5; exact Htr)
              with "Hcg Hpc []").
    { iApply (soi_0ac with "Htext"). }
    iIntros (CID10 Hq10) "Hcg Hpc".
    assert (Hppac : add_vec_int (mword_of_int (SO + 0xac) : mword 64) 2
                    = mword_of_int (SO + 0xae)) by pcw.
    iEval (rewrite Hppac) in "Hpc".
    (* ===== +0xae lh a4,68(s1) ===== *)
    iDestruct (so_meta_acc with "Hload") as "[Hmeta Hlback]".
    iDestruct (so_type_acc with "Hmeta") as "[Hity Hmback]".
    iEval (rewrite /i_type) in "Hity".
    iApply (wp_lh_s_sconf (CID := CID10) (kt := KT1) (ktd := KT0) (mword_of_int (SO + 0xae)) Ra4 Rs1
              (mword_of_int 68 : mword 12) N6 (K - 24)%nat
              (di_type dn : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hity]").
    { iApply (soi_0ae with "Htext"). }
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
              with "Hcg Hpc []").
    { iApply (soi_0b2 with "Htext"). }
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
                with "Hcg Hpc []").
      { iApply (soi_0b4 with "Htext"). }
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
                icfg_dev kk qi s gy inum dn bm kf fd l C pn om voff nsj
                (S (S u2)) pidv dqb dqs V m N8 sp0 K eb b lks w6
                (word_of_words lo om) w24 bp
                HKiu HKeo HK24 Kpop Hkk eq_refl Hinb Hgeom Hj Hgl Hlkempty Hkf
                Hfdlt Hlen Hfrees eq_refl Htyor eq_refl Hdir Hwf
                Hsp0 HN8sp HN8thr HN8s1 HN8s3 Hal
                with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                      Hitinv Hesck Hslkk Hslkd Hdep Hidev Hiinum Hivalid
                      Hload Hshot Hfrz Hkeep Hru Hfref Hflive Hflds Hfpn Hfoff
                      Hiru Hcore Howe Hprocs Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres
                      Hbsl Hisl Hfds Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
                      Hcont"). }
    (* ---- T_FILE: the +0x14e itrunc block ---- *)
    iApply (wp_beq_taken_s_sconf (CID := CID12) (mword_of_int (SO + 0xb4))
              (mword_of_int 154 : mword 13) Ra5 Ra4 N8 (K - 24)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HN8a4 HN8a5;
                    exact (so_ty_eq (di_type dn) 2 so_tfile_range Hfile))
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_0b4 with "Htext"). }
    iIntros (CID13 Hq13). iNext. iIntros "Hcg Hpc".
    assert (Htgb4 : add_vec (mword_of_int (SO + 0xb4) : mword 64)
                      (sign_extend' 64 (mword_of_int 154 : mword 13))
                    = mword_of_int (SO + 0x14e)) by pcw.
    iEval (rewrite Htgb4) in "Hpc".
    (* ===== +0x14e c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID13) (mword_of_int (SO + 0x14e)) Ra0 Rs1
              N8 (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_14e with "Htext"). }
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
              (mword_of_int 2089098 : mword 21) P1 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_150 with "Htext"). }
    iIntros (CID15 Hq15) "Hcg Hpc".
    set (P2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x150) : mword 64) 4)]> P1).
    assert (Hjit : add_vec (mword_of_int (SO + 0x150) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089098 : mword 21))
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
      as (data) "(%Hok & %Hrl & %Hdok & Hlnk & Hat & Hmeta & Hmap & Hblk & Hdv & Hfv
                  & Htop)".
    destruct Hok as (Hbwf & Hbcov & Haddrs & Htynz & Hszcap & Hholes & Hsized).
    iDestruct (proc_priv_core_bare_acc with "Hcore") as "[Hpbare Hcback]".
    iApply (Itrunc.wp_itrunc_sconf (CID := CID15) gs jx gl gu gd gk pd pav pu
              bn g gfs gi cov logstart bmapstart inodestart icfg_nib size
              icfg_dev (ientry kk) inum dn dn bm data u2 pidv
              (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqb dqs
              P2 (K - 24)%nat eb b lks V
              HKit Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog Hinb
              Htynz (di_type_stable_refl dn) (di_nlink_stable_refl dn Htynz)
              Hbwf Hcovb Hsized Haddrs Hj Hgl HP2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hidev Hiinum
                    Hmeta Hmap Hblk Hsbb Hsbi Hbmres Hireg Hat Hpbare Hprocs
                    Hdev Hgeo Hdlk Hbsl Hop").
    iIntros (CID16 Hq16 mit) "%Hcsit Hcg Hown Htce Hcce Hpc Hpbare Hidev Hiinum
                              Hsbb Hsbi Hmeta Hmap Hblk Hat Hbsl Hop".
    iDestruct "Hop" as (u3) "[%Hu3 Hop]".
    iDestruct ("Hcback" with "Hpbare") as "Hcore".
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
    (* THE MOVER (namei-pinned-lookup.md §9 W3, itrunc's row): O_TRUNC zeroed
       this inode's bytes and truncated its record, so the hold moves with
       them.  The fragment is WHOLE, so this is one free own-update. *)
    iApply fupd_wp.
    iMod (dvw_set_rt ⊤ _ _ _ _ (bv_unsigned inum) (dv_of dn data)
            (dv_of (di_trunc dn) (fun _ => replicate BSIZE (bv_0 8)))
            (fv_of dn data)
            (fv_of (di_trunc dn) (fun _ => replicate BSIZE (bv_0 8)))
            ltac:(solve_ndisj) with "Hireg Hdv Hfv") as "[Hdv Hfv]".
    iModIntro.
    (* itrunc MOVED the record and every block, so the era's abstract value
       is retagged at the truncated node before the seal (durable-disk
       2b-inode-3).  [ftopN] alone is opened. *)
    iApply fupd_wp.
    iMod (ireg_top_retag ⊤ gfs (bv_unsigned inum)
            (era_node dn bm data)
            (era_node (di_trunc dn) bm_empty (fun _ => replicate BSIZE (bv_0 8)))
            ltac:(solve_ndisj) with "[] Htop") as "Htop";
      [iApply (ireg_inv_ftop with "Hireg") |].
    iModIntro.
    iDestruct (so_trunc_loaded gfs gi cov logstart kk inum dn Htynz Htynd Hrl
                 with "Hat Hmeta Hmap Hblk Hdv Hfv Htop") as "Hload".
    (* ===== +0x154 c.j +0xb8 ===== *)
    iApply (wp_cj_s_sconf (CID := CID16) (mword_of_int (SO + 0x154))
              (sign_extend' 21 (concat_vec (mword_of_int 1970 : mword 11) ('b"0")))
              mit (K - 24)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_154 with "Htext"). }
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
    (* Fix the fact before elaborating the large application: an inline
       [ltac:(set_solver)] here sees its unresolved evars and the whole
       function context. *)
    iApply (so_tail_pub (CID0 := CID17) gf gs jx gl gu gd gk pd pav pu bn g
              gfs gi cn gil gisl cov logstart bmapstart inodestart size
              icfg_dev kk qi s gy inum (di_trunc dn) bm_empty kf fd l C pn
              om voff nsj u3 pidv dqb dqs V m mit sp0 K
              eb b lks w6 (word_of_words lo om) w24 bp
              HKiu HKeo HK24 Kpop Hkk eq_refl Hinb Hgeom Hj Hgl Hlkempty Hkf
              Hfdlt Hlen Hfrees eq_refl Htyor eq_refl Hdir Hwf
              Hsp0 Hitsp Hitthr Hits1 Hits3 Hal
              with "Hcg Hown Htce Hcce Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hitinv Hesck Hslkk Hslkd Hdep Hidev Hiinum Hivalid
                    Hload Hshot Hfrz Hkeep Hru Hfref Hflive Hflds Hfpn Hfoff
                    Hiru Hcore Howe Hprocs Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres
                    Hbsl Hisl Hfds Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23 H24
                    Hcont").
  Qed.

  (* ================================================================== *)
  (*  +0x5e .. +0x84 AND THE +0x140 FD_DEVICE BLOCK.                     *)
  (*                                                                    *)
  (*    c.sdsp s2,160 ; jal filealloc ; c.mv s2,a0 ; c.beqz -> +0x12e    *)
  (*    c.sdsp s3,152 ; jal fdalloc   ; c.mv s3,a0 ; bltz  -> +0x126     *)
  (*    lh a4,68(s1) ; c.li a5,3 ; beq -> +0x140                         *)
  (*    c.li a5,2 ; sw a5,0(s2) ; sw zero,32(s2)      [FD_INODE]         *)
  (*    +0x140: sw a4,0(s2) ; lh a5,70(s1) ; sh a5,36(s2) ; c.j +0x88    *)
  (*                                                                    *)
  (*  THE TWO SHRINK-WRAPPED SPILLS LIVE HERE, which is what makes ARMs  *)
  (*  E-FAIL and F-FAIL differ from D-FAIL at all: slot 4 holds the       *)
  (*  caller's s2 from +0x5e on, and slot 5 the caller's s3 from +0x68.   *)
  (*                                                                    *)
  (*  [so_open_slot] RUNS AFTER fdalloc, NOT AFTER filealloc: ARM F-FAIL  *)
  (*  hands the whole [file_ref] to [fileclose], so the slot may not be   *)
  (*  broken into cells until the descriptor is installed.                *)
  (* ================================================================== *)
  Lemma so_alloc `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gfl gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (kk : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (om lo : mword 32) (nsj : nat)
      (u : nat) (pidv : mword 32) (dqb dqs : dfrac)
      (V : pprivate)
      (m N : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w4 w5 w6 w24 : mword 64)
      (bp : nat -> bv 8) :
    (K_sys_open <= K)%nat ->
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
    (iput_units <= u)%nat ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    (bv_unsigned (di_type dn) = T_DIR_z -> om = (mword_of_int 0 : mword 32)) ->
    is_aligned_paddr (Physaddr (pa_stk sp0 23)) 8 = true ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    so_sp sp0 N -> so_thr m N ->
    (N !!! Regidx Rs0 : mword 64) = sp0 ->
    (N !!! Regidx Rs1 : mword 64) = ientry kk ->
    (N !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    (N !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    so_al sp0 ->
    (* the block takes [fileclose]'s loan off the top of the allowance
       ([so_iref_take]); see the [iref_slots nsj] row below. *)
    (1 <= nsj)%nat ->
    sie_cap_gpr KT1 N (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SO + 0x5e)) -∗
    panic_env -∗
    is_ftable gfl gf -∗
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
    sleeplocked_q gisl s (i_lock (ientry kk)) pidv -∗
    ic_deposit cn kk (DepShr s dev inum gy) -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    (* the payload's freeze token (§3.9, RULING A-prime), relayed to
       [so_tail_s]'s iunlock *)
    ifreeze_off (bv_unsigned inum) -∗
    inode_ref_short_gen kk (qi + s)%Qp qi dev inum gy -∗
    (* its PROVENANCE UNIT (item 7a-wire): the parent parks in the fd slot's
       [cinv] as [IcacheRef.inode_held_short], and that is one of the unit's
       two rest homes, so it travels with [Hkeep] the whole way. *)
    runit_any (bv_unsigned inum) -∗
    proc_priv gf (proc_addr jx) pidv V -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (λ ξ : CtxId, disk_res (XI := ξ) gd pd pav pu) -∗
    log_op g u -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_inv gfs bmapstart cov logstart size -∗
    bslots 3 -∗
    (* ONE OF THESE IS [fileclose]'s LOAN.  The D-FAIL tail closes the file
       it just allocated, and [SpecFileclose] borrows an iref unit across
       the call -- see the note on its [iref_slot] row.  The block takes it
       off the top of the allowance ([so_iref_take], hence the [1 <= nsj]
       premise) and either spends it on that loan and gets it back from
       fileclose, or never touches it; either way it is folded back in
       before the block returns, which is why [so_cont]'s ledger is an
       equality. *)
    iref_slots nsj -∗
    fd_slot -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] w4 -∗
    (pa_stk sp0 5) ↦₈[KT1] w5 -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 23) ↦₄[KT1] lo -∗
    (pa_add (pa_stk sp0 23) 4) ↦₄[KT1] om -∗
    (pa_stk sp0 24) ↦₈[KT1] w24 -∗
    wp_next true (proc_addr jx)
      (so_cont gf bn gfs cov logstart bmapstart inodestart size nsj
               dqb dqs (proc_addr jx) pidv V m K eb b lks) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hkk Hdevc Hnibc Hinb Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk
           Hiblog Hcovb Hiu Hj Hgl Hlkempty Hdir Hal23 Hsp0 HNsp HNthr HNs0
           HNs1 HNs2 HNs3 Hal Hnspos.
    destruct (so_kb K HK) as (HKcr & HKna & HKai & HKas & HKbo & HKeo & HKil &
                              HKiu & HKit & HKip & HKup & HKfc & HKfa & HKfd &
                              HK10 & HK24 & Kpop).
    assert (Hu2 : (2 <= u)%nat) by (revert Hiu; unfold iput_units; lia).
    subst dev. subst nib.
    iIntros "Hcg Hown Htce Hcce #Htext #Hdata Hpc #Hpe #Hftab #Hbio #Hlog
              Hseam Hgen #Hitab #Hitinv #Hesck #Hireg #Hropen #Hslkk Hslkd Hdep
              Hidev Hiinum Hivalid Hload #Hshot Hfrz Hkeep Hru Hpriv #Hprocs #Hdev #Hgeo
              #Hdlk Hop Hsbb Hsbi #Hbmres Hbsl Hisl Hfds Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
              HbP H23lo H23hi H24 Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* [fileclose]'s loan, off the top of the allowance *)
    iDestruct (so_iref_take nsj Hnspos with "Hisl") as "[Hires Hisl]".
    (* ===== +0x5e c.sdsp s2,160(sp) ===== *)
    assert (Hd4 : add_vec (N !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 20 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HNsp; apply so_frm4).
    iApply (wp_csdsp_s_sconf (CID := CID0) (mword_of_int (SO + 0x5e))
              (mword_of_int 20 : mword 6) Rs2 N (K - 24)%nat w4 b
              with "Hcg Hpc [] [Hf4]").
    { iApply (soi_05e with "Htext"). }
    { iEval (rewrite Hd4). iExact "Hf4". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf4".
    iEval (rewrite Hd4; rgne; rewrite HNs2) in "Hf4".
    assert (Hpp5e : add_vec_int (mword_of_int (SO + 0x5e) : mword 64) 2
                    = mword_of_int (SO + 0x60)) by pcw.
    iEval (rewrite Hpp5e) in "Hpc".
    (* ===== +0x60 jal ra,filealloc ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SO + 0x60)) Rra
              (mword_of_int 2092812 : mword 21) N (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_060 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x60) : mword 64) 4)]> N).
    assert (Hjfa : add_vec (mword_of_int (SO + 0x60) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092812 : mword 21))
                   = mword_of_int KernelSyms.filealloc) by pcw.
    iEval (rewrite Hjfa) in "Hpc".
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x60) : mword 64) 4)
      by (rewrite /M1; apply upd_eq).
    assert (HM1sp : so_sp sp0 M1)
      by (rewrite /so_sp /M1 upd_ne; [exact HNsp | nz]).
    assert (HM1s0 : (M1 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M1 upd_ne; [exact HNs0 | nz]).
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M1 upd_ne; [exact HNs1 | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [exact HNs2 | nz]).
    assert (HM1s3 : (M1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M1 upd_ne; [exact HNs3 | nz]).
    assert (HM1thr : so_thr m M1).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /M1 upd_ne; [| regne].
      exact (HNthr c Hc N2b N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Filealloc.wp_filealloc_sconf (CID := CID2) gfl gf M1 0%nat eb
              (proc_addr jx) (K - 24)%nat b lks HKfa so_noff0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htext Hpc Hftab Hfds").
    iIntros (CID3 Hq3 mfa) "Hcg Hown Hpc %Hcsfa Hfapost".
    assert (Hpcfa : ret_pc (M1 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0x64)) by (rewrite HM1ra; pcw).
    iEval (rewrite Hpcfa) in "Hpc".
    iDestruct (trap_csrs_ext_transport CID0 CID3 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID3 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    assert (Hfasp : so_sp sp0 mfa).
    { rewrite /so_sp (callee_saved_lookup Hcsfa csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM1sp. }
    assert (Hfas0 : (mfa !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsfa Rs0 ltac:(vm_compute; reflexivity)).
      exact HM1s0. }
    assert (Hfas1 : (mfa !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite (callee_saved_lookup Hcsfa Rs1 ltac:(vm_compute; reflexivity)).
      exact HM1s1. }
    assert (Hfas2 : (mfa !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcsfa Rs2 ltac:(vm_compute; reflexivity)).
      exact HM1s2. }
    assert (Hfas3 : (mfa !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcsfa Rs3 ltac:(vm_compute; reflexivity)).
      exact HM1s3. }
    assert (Hfathr : so_thr m mfa).
    { intros c Hc N2b N8 N9 N18 N19. rewrite (callee_saved_lookup Hcsfa c Hc).
      exact (HM1thr c Hc N2b N8 N9 N18 N19). }
    (* ===== +0x64 c.mv s2,a0 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID3) (mword_of_int (SO + 0x64)) Rs2 Ra0
              mfa (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_064 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M2 := <[Regidx Rs2 := regval_into_reg
                  (add_vec zero_reg (mfa !!! Regidx Ra0))]> mfa).
    assert (HM2s2 : (M2 !!! Regidx Rs2 : mword 64)
                    = (mfa !!! Regidx Ra0 : mword 64)).
    { etransitivity; [ rewrite /M2; apply upd_eq |]. apply add_vec_zero_l. }
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = (mfa !!! Regidx Ra0 : mword 64))
      by (rewrite /M2 upd_ne; [reflexivity | nz]).
    assert (HM2sp : so_sp sp0 M2)
      by (rewrite /so_sp /M2 upd_ne; [exact Hfasp | nz]).
    assert (HM2s0 : (M2 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M2 upd_ne; [exact Hfas0 | nz]).
    assert (HM2s1 : (M2 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M2 upd_ne; [exact Hfas1 | nz]).
    assert (HM2s3 : (M2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M2 upd_ne; [exact Hfas3 | nz]).
    assert (HM2thr : so_thr m M2).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /M2 upd_ne; [| regne].
      exact (Hfathr c Hc N2b N8 N9 N18 N19). }
    assert (Hpp64 : add_vec_int (mword_of_int (SO + 0x64) : mword 64) 2
                    = mword_of_int (SO + 0x66)) by pcw.
    iEval (rewrite Hpp64) in "Hpc".
    (* ===== +0x66 c.beqz a0, +0x12e  [ARM E-FAIL] ===== *)
    rewrite /filealloc_post.
    iDestruct "Hfapost" as "[[%Hz Hfds] | (%kf & %Cf & [%Hkf [%Hfn %Hty0]] & Href)]".
    { (* ---- filealloc refused ---- *)
      iApply (wp_cbeqz_taken_s_sconf (CID := CID4) (mword_of_int (SO + 0x66))
                (mword_of_int 100 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                M2 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HM2a0 Hz;
                      exact (proj2 (eq_vec_true_iff _ _) eq_refl))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_066 with "Htext"). }
      iIntros (CID5 Hq5). iNext. iIntros "Hcg Hpc".
      assert (Htg66 : add_vec (mword_of_int (SO + 0x66) : mword 64)
                        (sign_extend' 64
                           (sign_extend' 13 (concat_vec (mword_of_int 100 : mword 8) ('b"0"))))
                      = mword_of_int (SO + 0x12e)) by pcw.
      iEval (rewrite Htg66) in "Hpc".
      iDestruct (so_omode_join sp0 lo om Hal23 with "H23lo H23hi") as "H23".
      iDestruct (proc_priv_bare_acc with "Hpriv") as "[Hpbare Hpback]".
      iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeep".
      iDestruct (cpu_own_transport CID3 CID5 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (trap_csrs_ext_transport CID3 CID5 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
      iDestruct (cpu_claim_ext_transport CID3 CID5 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
      iApply (Tails.so_tail_e (CID0 := CID5) gs jx gl gu gd gk pd pav pu bn g
                gfs gi cn gtl gil gisl cov logstart bmapstart inodestart
                icfg_nib size icfg_dev kk qi s gy inum dn bm u pidv
                (DfracOwn (1/4)) dqb dqs m M2 sp0 K eb b lks w5 w6
                (word_of_words lo om) w24 bp V
                HKup HKeo HK24 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
                Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HM2sp HM2thr
                HM2s1 HM2s3 Hal
                with "Hcg Hown Htce Hcce Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                      Hitab Hitinv Hesck Hireg Hropen Hslkk Hslkd Hdep Hidev
                      Hiinum Hivalid Hload Hshot Hfrz Hkeep Hru Hsbb Hsbi Hbmres Hpbare
                      Hprocs Hdev Hgeo Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
                      HbP H23 H24 [Hpback Hfds Hisl Hires Hcont]").
      iEval (rewrite /wp_next).
      iIntros (CIDy) "%Hqy". iIntros (mf)
        "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc Hpbare Hsbb Hsbi
         Hbsl Hislot".
      iDestruct ("Hpback" with "Hpbare") as "Hpriv".
      (* the loan was never spent on this arm: fold it back beside the unit
         the tail's iput released. *)
      iDestruct (iref_slots_combine (nsj - 1) 1 with "Hisl Hires") as "Hisl".
      iDestruct (iref_slots_combine (nsj - 1 + 1) 1 with "Hisl Hislot") as "Hisl".
      replace (nsj - 1 + 1 + 1)%nat with (S nsj) by lia.
      iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf (S nsj) with "[%] [%] Hcg Hown Htce Hcce
                Hpc Hsbb Hsbi Hbsl Hisl [Hpriv Hfds]").
      { exact Hcsf. }
      { reflexivity. }
      { rewrite /sys_open_post. iSplitR "Hfds"; [| iExact "Hfds"].
        iLeft. iSplitR; [iPureIntro; exact Ha0f | iExact "Hpriv"]. } }
    (* ---- filealloc succeeded ---- *)
    iApply (wp_cbeqz_fall_s_sconf (CID := CID4) (mword_of_int (SO + 0x66))
              (mword_of_int 100 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              M2 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HM2a0 Hfn; exact (fnode_nonzero kf Hkf))
              with "Hcg Hpc []").
    { iApply (soi_066 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    assert (Hpp66 : add_vec_int (mword_of_int (SO + 0x66) : mword 64) 2
                    = mword_of_int (SO + 0x68)) by pcw.
    iEval (rewrite Hpp66) in "Hpc".
    assert (HM2s2f : (M2 !!! Regidx Rs2 : mword 64) = fnode kf)
      by (rewrite HM2s2; exact Hfn).
    (* ===== +0x68 c.sdsp s3,152(sp) ===== *)
    assert (Hd5 : add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 19 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (rewrite HM2sp; apply so_frm5).
    iApply (wp_csdsp_s_sconf (CID := CID5) (mword_of_int (SO + 0x68))
              (mword_of_int 19 : mword 6) Rs3 M2 (K - 24)%nat w5 b
              with "Hcg Hpc [] [Hf5]").
    { iApply (soi_068 with "Htext"). }
    { iEval (rewrite Hd5). iExact "Hf5". }
    iIntros (CID6 Hq6) "Hcg Hpc Hf5".
    iEval (rewrite Hd5; rgne; rewrite HM2s3) in "Hf5".
    assert (Hpp68 : add_vec_int (mword_of_int (SO + 0x68) : mword 64) 2
                    = mword_of_int (SO + 0x6a)) by pcw.
    iEval (rewrite Hpp68) in "Hpc".
    (* ===== +0x6a jal ra,fdalloc ===== *)
    iApply (wp_jal_s_sconf (CID := CID6) (mword_of_int (SO + 0x6a)) Rra
              (mword_of_int 2095604 : mword 21) M2 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_06a with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (M3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x6a) : mword 64) 4)]> M2).
    assert (Hjfd : add_vec (mword_of_int (SO + 0x6a) : mword 64)
                     (sign_extend' 64 (mword_of_int 2095604 : mword 21))
                   = mword_of_int KernelSyms.fdalloc) by pcw.
    iEval (rewrite Hjfd) in "Hpc".
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x6a) : mword 64) 4)
      by (rewrite /M3; apply upd_eq).
    assert (HM3a0 : (M3 !!! Regidx Ra0 : mword 64) = fnode kf)
      by (rewrite /M3 upd_ne; [rewrite HM2a0 Hfn; reflexivity | nz]).
    assert (HM3sp : so_sp sp0 M3)
      by (rewrite /so_sp /M3 upd_ne; [exact HM2sp | nz]).
    assert (HM3s0 : (M3 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M3 upd_ne; [exact HM2s0 | nz]).
    assert (HM3s1 : (M3 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M3 upd_ne; [exact HM2s1 | nz]).
    assert (HM3s2 : (M3 !!! Regidx Rs2 : mword 64) = fnode kf)
      by (rewrite /M3 upd_ne; [exact HM2s2f | nz]).
    assert (HM3s3 : (M3 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s3 | nz]).
    assert (HM3thr : so_thr m M3).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /M3 upd_ne; [| regne].
      exact (HM2thr c Hc N2b N8 N9 N18 N19). }
    iDestruct (proc_priv_split with "Hpriv") as "[Hcore Hofiles]".
    iDestruct (proc_ofiles_owe_empty gf (proc_addr jx) (pv_ofile V)) as "Hoeq".
    iDestruct (bi.equiv_entails_1_2 _ _ (proc_ofiles_owe_empty gf (proc_addr jx)
                 (pv_ofile V)) with "Hofiles") as "Howe".
    iDestruct (proc_ofiles_owe_len with "Howe") as %Hlen.
    iDestruct (cpu_own_transport CID3 CID7 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Fdalloc.wp_fdalloc_sconf (CID := CID7) gf kf ∅ M3 (K - 24)%nat
              0%nat eb (proc_addr jx) pidv V b lks HM3a0 Hkf so_noff0 HKfd
              with "Hcg Hown Htext Hdata Hpc Hcore Howe").
    iIntros (CID8 Hq8 mfd) "%Hcsfd Hcg Hown Hpc Hcore Hfdpost".
    assert (Hpcfd : ret_pc (M3 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0x6e)) by (rewrite HM3ra; pcw).
    iEval (rewrite Hpcfd) in "Hpc".
    iDestruct (trap_csrs_ext_transport CID3 CID8 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID3 CID8 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    assert (Hfdsp : so_sp sp0 mfd).
    { rewrite /so_sp (callee_saved_lookup Hcsfd csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM3sp. }
    assert (Hfds0 : (mfd !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsfd Rs0 ltac:(vm_compute; reflexivity)).
      exact HM3s0. }
    assert (Hfds1 : (mfd !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite (callee_saved_lookup Hcsfd Rs1 ltac:(vm_compute; reflexivity)).
      exact HM3s1. }
    assert (Hfds2 : (mfd !!! Regidx Rs2 : mword 64) = fnode kf).
    { rewrite (callee_saved_lookup Hcsfd Rs2 ltac:(vm_compute; reflexivity)).
      exact HM3s2. }
    assert (Hfds3 : (mfd !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcsfd Rs3 ltac:(vm_compute; reflexivity)).
      exact HM3s3. }
    assert (Hfdthr : so_thr m mfd).
    { intros c Hc N2b N8 N9 N18 N19. rewrite (callee_saved_lookup Hcsfd c Hc).
      exact (HM3thr c Hc N2b N8 N9 N18 N19). }
    (* ===== +0x6e c.mv s3,a0 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID8) (mword_of_int (SO + 0x6e)) Rs3 Ra0
              mfd (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_06e with "Htext"). }
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (M4 := <[Regidx Rs3 := regval_into_reg
                  (add_vec zero_reg (mfd !!! Regidx Ra0))]> mfd).
    assert (HM4s3 : (M4 !!! Regidx Rs3 : mword 64)
                    = (mfd !!! Regidx Ra0 : mword 64)).
    { etransitivity; [ rewrite /M4; apply upd_eq |]. apply add_vec_zero_l. }
    assert (HM4a0 : (M4 !!! Regidx Ra0 : mword 64) = (mfd !!! Regidx Ra0 : mword 64))
      by (rewrite /M4 upd_ne; [reflexivity | nz]).
    assert (HM4sp : so_sp sp0 M4)
      by (rewrite /so_sp /M4 upd_ne; [exact Hfdsp | nz]).
    assert (HM4s0 : (M4 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M4 upd_ne; [exact Hfds0 | nz]).
    assert (HM4s1 : (M4 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M4 upd_ne; [exact Hfds1 | nz]).
    assert (HM4s2 : (M4 !!! Regidx Rs2 : mword 64) = fnode kf)
      by (rewrite /M4 upd_ne; [exact Hfds2 | nz]).
    assert (HM4thr : so_thr m M4).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /M4 upd_ne; [| regne].
      exact (Hfdthr c Hc N2b N8 N9 N18 N19). }
    assert (Hpp6e : add_vec_int (mword_of_int (SO + 0x6e) : mword 64) 2
                    = mword_of_int (SO + 0x70)) by pcw.
    iEval (rewrite Hpp6e) in "Hpc".
    (* ===== +0x70 bltz a0, +0x126  [ARM F-FAIL] ===== *)
    rewrite /fdalloc_post.
    iDestruct "Hfdpost" as "[[[%Hm1 %Hnofd] Howe] | (%fd & %ll & [%Hfdv %Hfrees] & Howe & Hfds)]".
    { (* ---- fdalloc refused ---- *)
      iApply (wp_blt_x0_taken_s_sconf (CID := CID9) (mword_of_int (SO + 0x70))
                (mword_of_int 182 : mword 13) Ra0 M4 (K - 24)%nat b ltac:(nz)
                ltac:(rgne; rewrite HM4a0 Hm1; exact so_m1_neg)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_070 with "Htext"). }
      iIntros (CID10 Hq10). iNext. iIntros "Hcg Hpc".
      assert (Htg70 : add_vec (mword_of_int (SO + 0x70) : mword 64)
                        (sign_extend' 64 (mword_of_int 182 : mword 13))
                      = mword_of_int (SO + 0x126)) by pcw.
      iEval (rewrite Htg70) in "Hpc".
      iDestruct (so_omode_join sp0 lo om Hal23 with "H23lo H23hi") as "H23".
      iDestruct (proc_priv_core_bare_acc with "Hcore") as "[Hpbare Hcback]".
      iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeep".
      iDestruct (cpu_own_transport CID8 CID10 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (trap_csrs_ext_transport CID8 CID10 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
      iDestruct (cpu_claim_ext_transport CID8 CID10 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
      iApply (Tails.so_tail_f (CID0 := CID10) gfl gf gs jx gl gu gd gk pd pav
                pu bn g gfs gi cn gtl gil gisl cov logstart bmapstart
                inodestart icfg_nib size icfg_dev kk qi s gy inum dn bm
                kf 1%Qp Cf inhabitant None u pidv
                (DfracOwn (1/4)) dqb dqs m M4 sp0 K eb b lks w6
                (word_of_words lo om) w24 bp V
                HKup HKeo HKfc HK24 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog
                Hist0 Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HM4sp
                HM4thr HM4s1 HM4s2 Hal
                with "Hcg Hown Htce Hcce Htext Hdata Hpc Hpe Hftab Href
                      [] Hbio Hlog Hseam Hgen
                      Hitab Hitinv Hesck Hireg Hropen Hslkk Hslkd Hdep Hidev
                      Hiinum Hivalid Hload Hshot Hfrz Hkeep Hru Hsbb Hsbi Hbmres Hpbare
                      Hprocs Hdev Hgeo Hdlk Hbsl Hires Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
                      HbP H23 H24 [Hcback Howe Hisl Hcont]").
      { iApply (fileclose_env_none _ _ _ _ _ Cf Hty0). }
      iEval (rewrite /wp_next).
      iIntros (CIDy) "%Hqy". iIntros (mf)
        "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc Hpbare Hsbb Hsbi
         Hbsl Hislot Hfds Hfout".
      iDestruct ("Hcback" with "Hpbare") as "Hcore".
      iDestruct (proc_priv_join with "Hcore Howe") as "Hpriv".
      (* [so_tail_f] hands back TWO: the loan fileclose repaid and the unit
         iput released.  With the one taken off the top, that is [S nsj]. *)
      iDestruct (iref_slots_combine (nsj - 1) 2 with "Hisl Hislot") as "Hisl".
      replace (nsj - 1 + 2)%nat with (S nsj) by lia.
      iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf (S nsj) with "[%] [%] Hcg Hown Htce Hcce
                Hpc Hsbb Hsbi Hbsl Hisl [Hpriv Hfds]").
      { exact Hcsf. }
      { reflexivity. }
      { rewrite /sys_open_post. iSplitR "Hfds"; [| iExact "Hfds"].
        iLeft. iSplitR; [iPureIntro; exact Ha0f | iExact "Hpriv"]. } }
    (* ---- fdalloc installed the descriptor ---- *)
    assert (Hfdlt : (fd < NOFILE)%nat).
    { rewrite -Hlen. exact (fd_frees_head_lt _ _ _ Hfrees). }
    iApply (wp_blt_x0_fall_s_sconf (CID := CID9) (mword_of_int (SO + 0x70))
              (mword_of_int 182 : mword 13) Ra0 M4 (K - 24)%nat b ltac:(nz)
              ltac:(rgne; rewrite HM4a0 Hfdv;
                    exact (so_nonneg _ (so_fd_range fd Hfdlt)))
              with "Hcg Hpc []").
    { iApply (soi_070 with "Htext"). }
    iIntros (CID10 Hq10) "Hcg Hpc".
    assert (Hpp70 : add_vec_int (mword_of_int (SO + 0x70) : mword 64) 4
                    = mword_of_int (SO + 0x74)) by pcw.
    iEval (rewrite Hpp70) in "Hpc".
    assert (HM4s3f : (M4 !!! Regidx Rs3 : mword 64)
                     = (mword_of_int (Z.of_nat fd) : mword 64))
      by (rewrite HM4s3; exact Hfdv).
    (* ---- THE FRESH SLOT, OPENED: six cells plain, [f->ip] WHOLE ---- *)
    iApply fupd_wp.
    iMod (so_open_slot ⊤ gf kf Cf ltac:(solve_ndisj) Hty0 with "Href")
      as (pn voff) "(%Hwf & Hiru & Hfref & Hflive & Hfpn & Hfty & Hfrd & Hfwr
                    & Hfpip & Hfmaj & Hfip & Hfoff)".
    iModIntro.
    (* the loan is not spent on this arm -- the file is about to be PUBLISHED,
       not closed -- so fold it back before the stores block, which is where
       [so_tail_pub] expects the ledger whole. *)
    iDestruct (iref_slots_combine (nsj - 1) 1 with "Hisl Hires") as "Hisl".
    replace (nsj - 1 + 1)%nat with nsj by lia.
    (* ===== +0x74 lh a4,68(s1) ===== *)
    iDestruct (so_meta_acc with "Hload") as "[Hmeta Hlback]".
    iDestruct (so_type_acc with "Hmeta") as "[Hity Hmback]".
    iEval (rewrite /i_type) in "Hity".
    iApply (wp_lh_s_sconf (CID := CID10) (kt := KT1) (ktd := KT0) (mword_of_int (SO + 0x74)) Ra4 Rs1
              (mword_of_int 68 : mword 12) M4 (K - 24)%nat
              (di_type dn : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hity]").
    { iApply (soi_074 with "Htext"). }
    { iEval (rgne; rewrite HM4s1). iExact "Hity". }
    iIntros (CID11 Hq11) "Hcg Hpc Hity".
    iEval (rgne; rewrite HM4s1) in "Hity".
    iDestruct ("Hmback" with "[Hity]") as "Hmeta";
      [iEval (rewrite /i_type); iExact "Hity" |].
    iDestruct ("Hlback" with "Hmeta") as "Hload".
    set (M5 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (di_type dn : mword 16) : mword 64)]> M4).
    assert (HM5a4 : (M5 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /M5; apply upd_eq).
    assert (Hpp74 : add_vec_int (mword_of_int (SO + 0x74) : mword 64) 4
                    = mword_of_int (SO + 0x78)) by pcw.
    iEval (rewrite Hpp74) in "Hpc".
    (* ===== +0x78 c.li a5,3 ===== *)
    iApply (wp_cli_s_sconf (CID := CID11) (mword_of_int (SO + 0x78)) Ra5
              (mword_of_int 3 : mword 6) (mword_of_int 3 : mword 64)
              M5 (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (soi_078 with "Htext"). }
    iIntros (CID12 Hq12) "Hcg Hpc".
    set (M6 := <[Regidx Ra5 := regval_into_reg (mword_of_int 3 : mword 64)]> M5).
    assert (HM6a4 : (M6 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /M6 upd_ne; [exact HM5a4 | nz]).
    assert (HM6a5 : (M6 !!! Regidx Ra5 : mword 64) = (mword_of_int 3 : mword 64))
      by (rewrite /M6; apply upd_eq).
    assert (HM6sp : so_sp sp0 M6).
    { rewrite /so_sp /M6 upd_ne; [| nz]. rewrite /M5 upd_ne; [| nz].
      exact HM4sp. }
    assert (HM6s0 : (M6 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite /M6 upd_ne; [| nz]. rewrite /M5 upd_ne; [| nz]. exact HM4s0. }
    assert (HM6s1 : (M6 !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite /M6 upd_ne; [| nz]. rewrite /M5 upd_ne; [| nz]. exact HM4s1. }
    assert (HM6s2 : (M6 !!! Regidx Rs2 : mword 64) = fnode kf).
    { rewrite /M6 upd_ne; [| nz]. rewrite /M5 upd_ne; [| nz]. exact HM4s2. }
    assert (HM6s3 : (M6 !!! Regidx Rs3 : mword 64)
                    = (mword_of_int (Z.of_nat fd) : mword 64)).
    { rewrite /M6 upd_ne; [| nz]. rewrite /M5 upd_ne; [| nz]. exact HM4s3f. }
    assert (HM6thr : so_thr m M6).
    { intros c Hc N2b N8 N9 N18 N19.
      rewrite /M6 upd_ne; [| regne]. rewrite /M5 upd_ne; [| regne].
      exact (HM4thr c Hc N2b N8 N9 N18 N19). }
    assert (Hpp78 : add_vec_int (mword_of_int (SO + 0x78) : mword 64) 2
                    = mword_of_int (SO + 0x7a)) by pcw.
    iEval (rewrite Hpp78) in "Hpc".
    (* ===== +0x7a beq a4,a5, +0x140 ===== *)
    destruct (decide (di_type dn = (mword_of_int 3 : mword 16))) as [Hdev3 | Hnd3].
    { (* ---- T_DEVICE: the +0x140 block ---- *)
      iApply (wp_beq_taken_s_sconf (CID := CID12) (mword_of_int (SO + 0x7a))
                (mword_of_int 198 : mword 13) Ra5 Ra4 M6 (K - 24)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HM6a4 HM6a5;
                      exact (so_ty_eq (di_type dn) 3 so_tdev_range Hdev3))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_07a with "Htext"). }
      iIntros (CID13 Hq13). iNext. iIntros "Hcg Hpc".
      assert (Htg7a : add_vec (mword_of_int (SO + 0x7a) : mword 64)
                        (sign_extend' 64 (mword_of_int 198 : mword 13))
                      = mword_of_int (SO + 0x140)) by pcw.
      iEval (rewrite Htg7a) in "Hpc".
      (* ===== +0x140 sw a4,0(s2) -- f->type = FD_DEVICE ===== *)
      assert (Had140 : a_ftype kf
                       = add_vec (M6 !!! Regidx Rs2 : mword 64)
                           (sign_extend' 64 (mword_of_int 0 : mword 12))).
      { rewrite HM6s2. unfold a_ftype. symmetry. apply addv_sext0. }
      assert (Had140' : a_ftype kf
                        = add_vec (rget M6 Rs2)
                            (sign_extend' 64 (mword_of_int 0 : mword 12)))
        by (rgne; exact Had140).
      iEval (rewrite Had140') in "Hfty".
      assert (Hvv140 : trunc32 (M6 !!! Regidx Ra4 : mword 64) = FD_DEVICE).
      { rewrite HM6a4 Hdev3. unfold FD_DEVICE.
        apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_sw_s_sconf (CID := CID13) (mword_of_int (SO + 0x140)) Ra4 Rs2
                (mword_of_int 0 : mword 12) M6 (K - 24)%nat (fc_type Cf) b
                with "Hcg Hpc [] Hfty").
      { iApply (soi_140 with "Htext"). }
      iIntros (CID14 Hq14) "Hcg Hpc Hfty".
      iEval (rgne) in "Hfty". iEval (rgne) in "Hfty".
      iEval (rewrite -Had140 Hvv140) in "Hfty".
      assert (Hpp140 : add_vec_int (mword_of_int (SO + 0x140) : mword 64) 4
                       = mword_of_int (SO + 0x144)) by pcw.
      iEval (rewrite Hpp140) in "Hpc".
      (* ===== +0x144 lh a5,70(s1) -- ip->major ===== *)
      iDestruct (so_meta_acc with "Hload") as "[Hmeta Hlback]".
      iDestruct (so_maj_acc with "Hmeta") as "[Himaj Hmback]".
      iEval (rewrite /i_major) in "Himaj".
      iApply (wp_lh_s_sconf (CID := CID14) (kt := KT1) (ktd := KT0) (mword_of_int (SO + 0x144)) Ra5 Rs1
                (mword_of_int 70 : mword 12) M6 (K - 24)%nat
                (di_major dn : mword 16) b ltac:(nz) ltac:(rdok)
                with "Hcg Hpc [] [Himaj]").
      { iApply (soi_144 with "Htext"). }
      { iEval (rgne; rewrite HM6s1). iExact "Himaj". }
      iIntros (CID15 Hq15) "Hcg Hpc Himaj".
      iEval (rgne; rewrite HM6s1) in "Himaj".
      iDestruct ("Hmback" with "[Himaj]") as "Hmeta";
        [iEval (rewrite /i_major); iExact "Himaj" |].
      iDestruct ("Hlback" with "Hmeta") as "Hload".
      set (M7 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (di_major dn : mword 16) : mword 64)]> M6).
      assert (HM7a5 : (M7 !!! Regidx Ra5 : mword 64)
                      = (sign_extend' 64 (di_major dn : mword 16) : mword 64))
        by (rewrite /M7; apply upd_eq).
      assert (HM7sp : so_sp sp0 M7)
        by (rewrite /so_sp /M7 upd_ne; [exact HM6sp | nz]).
      assert (HM7s0 : (M7 !!! Regidx Rs0 : mword 64) = sp0)
        by (rewrite /M7 upd_ne; [exact HM6s0 | nz]).
      assert (HM7s1 : (M7 !!! Regidx Rs1 : mword 64) = ientry kk)
        by (rewrite /M7 upd_ne; [exact HM6s1 | nz]).
      assert (HM7s2 : (M7 !!! Regidx Rs2 : mword 64) = fnode kf)
        by (rewrite /M7 upd_ne; [exact HM6s2 | nz]).
      assert (HM7s3 : (M7 !!! Regidx Rs3 : mword 64)
                      = (mword_of_int (Z.of_nat fd) : mword 64))
        by (rewrite /M7 upd_ne; [exact HM6s3 | nz]).
      assert (HM7thr : so_thr m M7).
      { intros c Hc N2b N8 N9 N18 N19. rewrite /M7 upd_ne; [| regne].
        exact (HM6thr c Hc N2b N8 N9 N18 N19). }
      assert (Hpp144 : add_vec_int (mword_of_int (SO + 0x144) : mword 64) 4
                       = mword_of_int (SO + 0x148)) by pcw.
      iEval (rewrite Hpp144) in "Hpc".
      (* ===== +0x148 sh a5,36(s2) -- f->major = ip->major ===== *)
      iEval (rewrite /a_fmajor /foff_of) in "Hfmaj".
      iApply (wp_sh_s_sconf (CID := CID15) (kt := KT1) (ktd := KT0) (mword_of_int (SO + 0x148)) Ra5 Rs2
                (mword_of_int 36 : mword 12) M7 (K - 24)%nat (fc_major Cf) b
                with "Hcg Hpc [] [Hfmaj]").
      { iApply (soi_148 with "Htext"). }
      { iEval (rgne; rewrite HM7s2). iExact "Hfmaj". }
      iIntros (CID16 Hq16) "Hcg Hpc Hfmaj".
      iEval (rgne; rewrite HM7s2; rgne; rewrite HM7a5;
             rewrite trunc16_sext64) in "Hfmaj".
      assert (Hpp148 : add_vec_int (mword_of_int (SO + 0x148) : mword 64) 4
                       = mword_of_int (SO + 0x14c)) by pcw.
      iEval (rewrite Hpp148) in "Hpc".
      (* ===== +0x14c c.j +0x88 ===== *)
      iApply (wp_cj_s_sconf (CID := CID16) (mword_of_int (SO + 0x14c))
                (sign_extend' 21 (concat_vec (mword_of_int 1950 : mword 11) ('b"0")))
                M7 (K - 24)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_14c with "Htext"). }
      iIntros (CID17 Hq17). iNext. iIntros "Hcg Hpc".
      assert (Htg14c : add_vec (mword_of_int (SO + 0x14c) : mword 64)
                         (sign_extend' 64
                            (sign_extend' 21 (concat_vec (mword_of_int 1950 : mword 11) ('b"0"))))
                       = mword_of_int (SO + 0x88)) by pcw.
      iEval (rewrite Htg14c) in "Hpc".
      iDestruct (cpu_own_transport CID8 CID17 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (trap_csrs_ext_transport CID8 CID17 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
      iDestruct (cpu_claim_ext_transport CID8 CID17 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
      iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID17)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (so_stores (CID0 := CID17) gf gs jx gl gu gd gk pd pav pu bn g
                gfs gi cn gil gisl cov logstart bmapstart inodestart icfg_nib
                size icfg_dev kk qi s gy inum dn bm kf fd ll pn FD_DEVICE
                (fc_readable Cf) (fc_writable Cf) (fc_pipe Cf) (fc_ip Cf)
                (di_major dn) om voff lo nsj u pidv dqb dqs V m M7 sp0 K eb b
                lks w6 w24 bp
                HKiu HKeo HKit HK24 Kpop Hkk eq_refl eq_refl Hinb Hgeom Hsize
                Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog Hcovb Hu2 Hj Hgl
                Hlkempty Hkf Hfdlt Hlen Hfrees (or_intror eq_refl) Hdir Hwf
                Hal23 Hsp0 HM7sp HM7thr HM7s0 HM7s1 HM7s2 HM7s3 Hal
                with "Hcg Hown Htce Hcce Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                      Hitinv Hesck Hireg Hslkk Hslkd Hdep Hidev Hiinum
                      Hivalid Hload Hshot Hfrz Hkeep Hru Hfref Hflive Hfpn Hfty Hfrd
                      Hfwr Hfpip Hfmaj Hfip Hfoff Hiru Hcore Howe Hprocs Hdev Hgeo
                      Hdlk Hop Hsbb Hsbi Hbmres Hbsl Hisl Hfds Hf1 Hf2 Hf3 Hf4
                      Hf5 Hf6 HbP H23lo H23hi H24 Hcont"). }
    (* ---- not a device: the FD_INODE pair ---- *)
    iApply (wp_beq_fall_s_sconf (CID := CID12) (mword_of_int (SO + 0x7a))
              (mword_of_int 198 : mword 13) Ra5 Ra4 M6 (K - 24)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HM6a4 HM6a5;
                    exact (so_ty_ne (di_type dn) 3 so_tdev_range Hnd3))
              with "Hcg Hpc []").
    { iApply (soi_07a with "Htext"). }
    iIntros (CID13 Hq13) "Hcg Hpc".
    assert (Hpp7a : add_vec_int (mword_of_int (SO + 0x7a) : mword 64) 4
                    = mword_of_int (SO + 0x7e)) by pcw.
    iEval (rewrite Hpp7a) in "Hpc".
    (* ===== +0x7e c.li a5,2 ===== *)
    iApply (wp_cli_s_sconf (CID := CID13) (mword_of_int (SO + 0x7e)) Ra5
              (mword_of_int 2 : mword 6) (mword_of_int 2 : mword 64)
              M6 (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (soi_07e with "Htext"). }
    iIntros (CID14 Hq14) "Hcg Hpc".
    set (M8 := <[Regidx Ra5 := regval_into_reg (mword_of_int 2 : mword 64)]> M6).
    assert (HM8a5 : (M8 !!! Regidx Ra5 : mword 64) = (mword_of_int 2 : mword 64))
      by (rewrite /M8; apply upd_eq).
    assert (HM8sp : so_sp sp0 M8)
      by (rewrite /so_sp /M8 upd_ne; [exact HM6sp | nz]).
    assert (HM8s0 : (M8 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M8 upd_ne; [exact HM6s0 | nz]).
    assert (HM8s1 : (M8 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /M8 upd_ne; [exact HM6s1 | nz]).
    assert (HM8s2 : (M8 !!! Regidx Rs2 : mword 64) = fnode kf)
      by (rewrite /M8 upd_ne; [exact HM6s2 | nz]).
    assert (HM8s3 : (M8 !!! Regidx Rs3 : mword 64)
                    = (mword_of_int (Z.of_nat fd) : mword 64))
      by (rewrite /M8 upd_ne; [exact HM6s3 | nz]).
    assert (HM8thr : so_thr m M8).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /M8 upd_ne; [| regne].
      exact (HM6thr c Hc N2b N8 N9 N18 N19). }
    assert (Hpp7e : add_vec_int (mword_of_int (SO + 0x7e) : mword 64) 2
                    = mword_of_int (SO + 0x80)) by pcw.
    iEval (rewrite Hpp7e) in "Hpc".
    (* ===== +0x80 sw a5,0(s2) -- f->type = FD_INODE ===== *)
    assert (Had80 : a_ftype kf
                    = add_vec (M8 !!! Regidx Rs2 : mword 64)
                        (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite HM8s2. unfold a_ftype. symmetry. apply addv_sext0. }
    assert (Had80' : a_ftype kf
                     = add_vec (rget M8 Rs2)
                         (sign_extend' 64 (mword_of_int 0 : mword 12)))
      by (rgne; exact Had80).
    iEval (rewrite Had80') in "Hfty".
    assert (Hvv80 : trunc32 (M8 !!! Regidx Ra5 : mword 64) = FD_INODE).
    { rewrite HM8a5. unfold FD_INODE. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_sw_s_sconf (CID := CID14) (mword_of_int (SO + 0x80)) Ra5 Rs2
              (mword_of_int 0 : mword 12) M8 (K - 24)%nat (fc_type Cf) b
              with "Hcg Hpc [] Hfty").
    { iApply (soi_080 with "Htext"). }
    iIntros (CID15 Hq15) "Hcg Hpc Hfty".
    iEval (rgne) in "Hfty". iEval (rgne) in "Hfty".
    iEval (rewrite -Had80 Hvv80) in "Hfty".
    assert (Hpp80 : add_vec_int (mword_of_int (SO + 0x80) : mword 64) 4
                    = mword_of_int (SO + 0x84)) by pcw.
    iEval (rewrite Hpp80) in "Hpc".
    (* ===== +0x84 sw zero,32(s2) -- f->off = 0 ===== *)
    iEval (rewrite /a_foff /foff_of) in "Hfoff".
    iApply (wp_sw_zero_s_sconf (kt := KT1) (ktd := KT0) (CID := CID15) (mword_of_int (SO + 0x84)) Rs2
              (mword_of_int 32 : mword 12) M8 (K - 24)%nat voff b
              with "Hcg Hpc [] [Hfoff]").
    { iApply (soi_084 with "Htext"). }
    { iEval (rgne; rewrite HM8s2). iExact "Hfoff". }
    iIntros (CID16 Hq16) "Hcg Hpc Hfoff".
    iEval (rgne; rewrite HM8s2) in "Hfoff".
    assert (Hpp84 : add_vec_int (mword_of_int (SO + 0x84) : mword 64) 4
                    = mword_of_int (SO + 0x88)) by pcw.
    iEval (rewrite Hpp84) in "Hpc".
    iDestruct (cpu_own_transport CID8 CID16 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID8 CID16 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID8 CID16 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID16)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (so_stores (CID0 := CID16) gf gs jx gl gu gd gk pd pav pu bn g
              gfs gi cn gil gisl cov logstart bmapstart inodestart icfg_nib
              size icfg_dev kk qi s gy inum dn bm kf fd ll pn FD_INODE
              (fc_readable Cf) (fc_writable Cf) (fc_pipe Cf) (fc_ip Cf)
              (fc_major Cf) om (mword_of_int 0 : mword 32) lo nsj u pidv dqb
              dqs V m M8 sp0 K eb b lks w6 w24 bp
              HKiu HKeo HKit HK24 Kpop Hkk eq_refl eq_refl Hinb Hgeom Hsize
              Hbm0 Hbmcov Hbmlog Hist0 Hiblk Hiblog Hcovb Hu2 Hj Hgl Hlkempty
              Hkf Hfdlt Hlen Hfrees (or_introl eq_refl) Hdir off_wf_zero
              Hal23 Hsp0 HM8sp HM8thr HM8s0 HM8s1 HM8s2 HM8s3 Hal
              with "Hcg Hown Htce Hcce Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                    Hitinv Hesck Hireg Hslkk Hslkd Hdep Hidev Hiinum
                    Hivalid Hload Hshot Hfrz Hkeep Hru Hfref Hflive Hfpn Hfty Hfrd
                    Hfwr Hfpip Hfmaj Hfip Hfoff Hiru Hcore Howe Hprocs Hdev Hgeo
                    Hdlk Hop Hsbb Hsbi Hbmres Hbsl Hisl Hfds Hf1 Hf2 Hf3 Hf4
                    Hf5 Hf6 HbP H23lo H23hi H24 Hcont").
  Qed.

  (* ================================================================== *)
  (*  THE JOIN AT +0x4a, AND ARM D-FAIL.                                 *)
  (*                                                                    *)
  (*    lh a4,68(s1) ; c.li a5,3 ; bne -> +0x5e                          *)
  (*    lhu a4,70(s1) ; c.li a5,9 ; bltu 9 <u a4 -> +0x116               *)
  (*                                                                    *)
  (*  ENTERED FROM BOTH ARMS with [ip] LOCKED: the O_CREATE arm's create *)
  (*  and the else arm's namei/ilock/T_DIR refusal.  Everything it needs *)
  (*  about which arm ran is in ONE pure premise -- [di_type = T_DIR ->  *)
  (*  om = 0], which is [so_pay_witness]'s second half and the theorem   *)
  (*  of this walk.                                                     *)
  (*                                                                    *)
  (*  THE [major] BOUNDS CHECK IS ONE UNSIGNED TEST, NOT TWO: the [lhu]  *)
  (*  zero-extends, so a negative [short] lands at or above 0x8000 > 9   *)
  (*  and the single [bltu] decides both halves of the C's disjunction.  *)
  (* ================================================================== *)
  Lemma so_join `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gfl gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (kk : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (om lo : mword 32) (nsj : nat)
      (u : nat) (pidv : mword 32) (dqb dqs : dfrac)
      (V : pprivate)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w4 w5 w6 w24 : mword 64)
      (bp : nat -> bv 8) :
    (K_sys_open <= K)%nat ->
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
    (iput_units <= u)%nat ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    (bv_unsigned (di_type dn) = T_DIR_z -> om = (mword_of_int 0 : mword 32)) ->
    is_aligned_paddr (Physaddr (pa_stk sp0 23)) 8 = true ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    so_sp sp0 M -> so_thr m M ->
    (M !!! Regidx Rs0 : mword 64) = sp0 ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    (M !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    so_al sp0 ->
    (* the block takes [fileclose]'s loan off the top of the allowance
       ([so_iref_take]); see the [iref_slots nsj] row below. *)
    (1 <= nsj)%nat ->
    sie_cap_gpr KT1 M (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SO + 0x4a)) -∗
    panic_env -∗
    is_ftable gfl gf -∗
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
    sleeplocked_q gisl s (i_lock (ientry kk)) pidv -∗
    ic_deposit cn kk (DepShr s dev inum gy) -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    (* the payload's freeze token (§3.9, RULING A-prime), relayed to
       [so_tail_s]'s iunlock *)
    ifreeze_off (bv_unsigned inum) -∗
    inode_ref_short_gen kk (qi + s)%Qp qi dev inum gy -∗
    (* its PROVENANCE UNIT (item 7a-wire): the parent parks in the fd slot's
       [cinv] as [IcacheRef.inode_held_short], and that is one of the unit's
       two rest homes, so it travels with [Hkeep] the whole way. *)
    runit_any (bv_unsigned inum) -∗
    proc_priv gf (proc_addr jx) pidv V -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (λ ξ : CtxId, disk_res (XI := ξ) gd pd pav pu) -∗
    log_op g u -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_inv gfs bmapstart cov logstart size -∗
    bslots 3 -∗
    (* THE ALLOWANCE, PASSED STRAIGHT DOWN.  This block spends nothing of
       its own; [so_alloc] below is what takes [fileclose]'s loan off the
       top, which is where the [1 <= nsj] premise goes. *)
    iref_slots nsj -∗
    fd_slot -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] w4 -∗
    (pa_stk sp0 5) ↦₈[KT1] w5 -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 23) ↦₄[KT1] lo -∗
    (pa_add (pa_stk sp0 23) 4) ↦₄[KT1] om -∗
    (pa_stk sp0 24) ↦₈[KT1] w24 -∗
    wp_next true (proc_addr jx)
      (so_cont gf bn gfs cov logstart bmapstart inodestart size nsj
               dqb dqs (proc_addr jx) pidv V m K eb b lks) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hkk Hdevc Hnibc Hinb Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk
           Hiblog Hcovb Hiu Hj Hgl Hlkempty Hdir Hal23 Hsp0 HMsp HMthr HMs0
           HMs1 HMs2 HMs3 Hal Hnspos.
    pose proof HK as HKfull.
    destruct (so_kb K HK) as (HKcr & HKna & HKai & HKas & HKbo & HKeo & HKil &
                              HKiu & HKit & HKip & HKup & HKfc & HKfa & HKfd &
                              HK10 & HK24 & Kpop).
    subst dev. subst nib.
    iIntros "Hcg Hown Htce Hcce #Htext #Hdata Hpc #Hpe #Hftab #Hbio #Hlog
              Hseam Hgen #Hitab #Hitinv #Hesck #Hireg #Hropen #Hslkk Hslkd Hdep
              Hidev Hiinum Hivalid Hload #Hshot Hfrz Hkeep Hru Hpriv #Hprocs #Hdev #Hgeo
              #Hdlk Hop Hsbb Hsbi #Hbmres Hbsl Hisl Hfds Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
              HbP H23lo H23hi H24 Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* ===== +0x4a lh a4,68(s1) ===== *)
    iDestruct (so_meta_acc with "Hload") as "[Hmeta Hlback]".
    iDestruct (so_type_acc with "Hmeta") as "[Hity Hmback]".
    iEval (rewrite /i_type) in "Hity".
    iApply (wp_lh_s_sconf (CID := CID0) (kt := KT1) (ktd := KT0) (mword_of_int (SO + 0x4a)) Ra4 Rs1
              (mword_of_int 68 : mword 12) M (K - 24)%nat
              (di_type dn : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hity]").
    { iApply (soi_04a with "Htext"). }
    { iEval (rgne; rewrite HMs1). iExact "Hity". }
    iIntros (CID1 Hq1) "Hcg Hpc Hity".
    iEval (rgne; rewrite HMs1) in "Hity".
    iDestruct ("Hmback" with "[Hity]") as "Hmeta";
      [iEval (rewrite /i_type); iExact "Hity" |].
    iDestruct ("Hlback" with "Hmeta") as "Hload".
    set (M1 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (di_type dn : mword 16) : mword 64)]> M).
    assert (HM1a4 : (M1 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /M1; apply upd_eq).
    assert (Hpp4a : add_vec_int (mword_of_int (SO + 0x4a) : mword 64) 4
                    = mword_of_int (SO + 0x4e)) by pcw.
    iEval (rewrite Hpp4a) in "Hpc".
    (* ===== +0x4e c.li a5,3 ===== *)
    iApply (wp_cli_s_sconf (CID := CID1) (mword_of_int (SO + 0x4e)) Ra5
              (mword_of_int 3 : mword 6) (mword_of_int 3 : mword 64)
              M1 (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (soi_04e with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M2 := <[Regidx Ra5 := regval_into_reg (mword_of_int 3 : mword 64)]> M1).
    assert (HM2a4 : (M2 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1a4 | nz]).
    assert (HM2a5 : (M2 !!! Regidx Ra5 : mword 64) = (mword_of_int 3 : mword 64))
      by (rewrite /M2; apply upd_eq).
    assert (HM2sp : so_sp sp0 M2).
    { rewrite /so_sp /M2 upd_ne; [| nz]. rewrite /M1 upd_ne; [| nz].
      exact HMsp. }
    assert (HM2s0 : (M2 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite /M2 upd_ne; [| nz]. rewrite /M1 upd_ne; [| nz]. exact HMs0. }
    assert (HM2s1 : (M2 !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite /M2 upd_ne; [| nz]. rewrite /M1 upd_ne; [| nz]. exact HMs1. }
    assert (HM2s2 : (M2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /M2 upd_ne; [| nz]. rewrite /M1 upd_ne; [| nz]. exact HMs2. }
    assert (HM2s3 : (M2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /M2 upd_ne; [| nz]. rewrite /M1 upd_ne; [| nz]. exact HMs3. }
    assert (HM2thr : so_thr m M2).
    { intros c Hc N2b N8 N9 N18 N19.
      rewrite /M2 upd_ne; [| regne]. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2b N8 N9 N18 N19). }
    assert (Hpp4e : add_vec_int (mword_of_int (SO + 0x4e) : mword 64) 2
                    = mword_of_int (SO + 0x50)) by pcw.
    iEval (rewrite Hpp4e) in "Hpc".
    (* ===== +0x50 bne a4,a5, +0x5e ===== *)
    destruct (decide (di_type dn = (mword_of_int 3 : mword 16))) as [Hdev3 | Hnd3].
    2:{ (* ---- not a device: the [major] test is skipped ---- *)
      iApply (wp_bne_taken_s_sconf (CID := CID2) (mword_of_int (SO + 0x50))
                (mword_of_int 14 : mword 13) Ra5 Ra4 M2 (K - 24)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HM2a4 HM2a5;
                      exact (so_neq_of_ne _ _
                               (so_ty_ne (di_type dn) 3 so_tdev_range Hnd3)))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_050 with "Htext"). }
      iIntros (CID3 Hq3). iNext. iIntros "Hcg Hpc".
      assert (Htg50 : add_vec (mword_of_int (SO + 0x50) : mword 64)
                        (sign_extend' 64 (mword_of_int 14 : mword 13))
                      = mword_of_int (SO + 0x5e)) by pcw.
      iEval (rewrite Htg50) in "Hpc".
      iDestruct (cpu_own_transport CID0 CID3 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (trap_csrs_ext_transport CID0 CID3 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
      iDestruct (cpu_claim_ext_transport CID0 CID3 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
      iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID3)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (so_alloc (CID0 := CID3) gfl gf gs jx gl gu gd gk pd pav pu bn g
                gfs gi cn gtl gil gisl cov logstart bmapstart inodestart
                icfg_nib size icfg_dev kk qi s gy inum dn bm om lo nsj u
                pidv dqb dqs V m M2 sp0 K eb b lks w4 w5 w6 w24 bp
                HKfull Hkk eq_refl eq_refl Hinb Hgeom Hsize Hbm0 Hbmcov Hbmlog
                Hist0 Hiblk Hiblog Hcovb Hiu Hj Hgl Hlkempty Hdir Hal23 Hsp0
                HM2sp HM2thr HM2s0 HM2s1 HM2s2 HM2s3 Hal Hnspos
                with "Hcg Hown Htce Hcce Htext Hdata Hpc Hpe Hftab Hbio Hlog
                      Hseam Hgen Hitab Hitinv Hesck Hireg Hropen Hslkk Hslkd
                      Hdep Hidev Hiinum Hivalid Hload Hshot Hfrz Hkeep Hru Hpriv Hprocs
                      Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres Hbsl Hisl Hfds Hf1
                      Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23lo H23hi H24 Hcont"). }
    (* ---- T_DEVICE: the [major] bounds test ---- *)
    iApply (wp_bne_fall_s_sconf (CID := CID2) (mword_of_int (SO + 0x50))
              (mword_of_int 14 : mword 13) Ra5 Ra4 M2 (K - 24)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HM2a4 HM2a5;
                    exact (so_neq_of_eq _ _
                             (so_ty_eq (di_type dn) 3 so_tdev_range Hdev3)))
              with "Hcg Hpc []").
    { iApply (soi_050 with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc".
    assert (Hpp50 : add_vec_int (mword_of_int (SO + 0x50) : mword 64) 4
                    = mword_of_int (SO + 0x54)) by pcw.
    iEval (rewrite Hpp50) in "Hpc".
    (* ===== +0x54 lhu a4,70(s1) -- ip->major, ZERO extended ===== *)
    iDestruct (so_meta_acc with "Hload") as "[Hmeta Hlback]".
    iDestruct (so_maj_acc with "Hmeta") as "[Himaj Hmback]".
    iEval (rewrite /i_major) in "Himaj".
    iApply (wp_lhu_s_sconf (CID := CID3) (kt := KT1) (ktd := KT0) (mword_of_int (SO + 0x54)) Ra4 Rs1
              (mword_of_int 70 : mword 12) M2 (K - 24)%nat
              (di_major dn : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Himaj]").
    { iApply (soi_054 with "Htext"). }
    { iEval (rgne; rewrite HM2s1). iExact "Himaj". }
    iIntros (CID4 Hq4) "Hcg Hpc Himaj".
    iEval (rgne; rewrite HM2s1) in "Himaj".
    iDestruct ("Hmback" with "[Himaj]") as "Hmeta";
      [iEval (rewrite /i_major); iExact "Himaj" |].
    iDestruct ("Hlback" with "Hmeta") as "Hload".
    set (M3 := <[Regidx Ra4 := regval_into_reg
                  (zero_extend' 64 (di_major dn : mword 16) : mword 64)]> M2).
    assert (HM3a4 : (M3 !!! Regidx Ra4 : mword 64)
                    = (zero_extend' 64 (di_major dn : mword 16) : mword 64))
      by (rewrite /M3; apply upd_eq).
    assert (Hpp54 : add_vec_int (mword_of_int (SO + 0x54) : mword 64) 4
                    = mword_of_int (SO + 0x58)) by pcw.
    iEval (rewrite Hpp54) in "Hpc".
    (* ===== +0x58 c.li a5,9 ===== *)
    iApply (wp_cli_s_sconf (CID := CID4) (mword_of_int (SO + 0x58)) Ra5
              (mword_of_int 9 : mword 6) (mword_of_int 9 : mword 64)
              M3 (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (soi_058 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (M4 := <[Regidx Ra5 := regval_into_reg (mword_of_int 9 : mword 64)]> M3).
    assert (HM4a4 : (M4 !!! Regidx Ra4 : mword 64)
                    = (zero_extend' 64 (di_major dn : mword 16) : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3a4 | nz]).
    assert (HM4a5 : (M4 !!! Regidx Ra5 : mword 64) = (mword_of_int 9 : mword 64))
      by (rewrite /M4; apply upd_eq).
    assert (HM4sp : so_sp sp0 M4).
    { rewrite /so_sp /M4 upd_ne; [| nz]. rewrite /M3 upd_ne; [| nz].
      exact HM2sp. }
    assert (HM4s0 : (M4 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite /M4 upd_ne; [| nz]. rewrite /M3 upd_ne; [| nz]. exact HM2s0. }
    assert (HM4s1 : (M4 !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite /M4 upd_ne; [| nz]. rewrite /M3 upd_ne; [| nz]. exact HM2s1. }
    assert (HM4s2 : (M4 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /M4 upd_ne; [| nz]. rewrite /M3 upd_ne; [| nz]. exact HM2s2. }
    assert (HM4s3 : (M4 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /M4 upd_ne; [| nz]. rewrite /M3 upd_ne; [| nz]. exact HM2s3. }
    assert (HM4thr : so_thr m M4).
    { intros c Hc N2b N8 N9 N18 N19.
      rewrite /M4 upd_ne; [| regne]. rewrite /M3 upd_ne; [| regne].
      exact (HM2thr c Hc N2b N8 N9 N18 N19). }
    assert (Hpp58 : add_vec_int (mword_of_int (SO + 0x58) : mword 64) 2
                    = mword_of_int (SO + 0x5a)) by pcw.
    iEval (rewrite Hpp58) in "Hpc".
    (* ===== +0x5a bltu a5,a4, +0x116  [ARM D-FAIL] ===== *)
    destruct (Z_lt_le_dec 9 (bv_unsigned (di_major dn))) as [Hout | Hin].
    { (* ---- the major is out of range ---- *)
      iApply (wp_bltu_taken_s_sconf (CID := CID5) (mword_of_int (SO + 0x5a))
                (mword_of_int 188 : mword 13) Ra4 Ra5 M4 (K - 24)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HM4a4 HM4a5;
                      exact (so_major_out (di_major dn) Hout))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_05a with "Htext"). }
      iIntros (CID6 Hq6). iNext. iIntros "Hcg Hpc".
      assert (Htg5a : add_vec (mword_of_int (SO + 0x5a) : mword 64)
                        (sign_extend' 64 (mword_of_int 188 : mword 13))
                      = mword_of_int (SO + 0x116)) by pcw.
      iEval (rewrite Htg5a) in "Hpc".
      iDestruct (so_omode_join sp0 lo om Hal23 with "H23lo H23hi") as "H23".
      iDestruct (proc_priv_bare_acc with "Hpriv") as "[Hpbare Hpback]".
      iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeep".
      iDestruct (cpu_own_transport CID0 CID6 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (trap_csrs_ext_transport CID0 CID6 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
      iDestruct (cpu_claim_ext_transport CID0 CID6 eb (proc_addr jx)
                   ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
      iApply (Tails.so_tail_d (CID0 := CID6) gs jx gl gu gd gk pd pav pu bn g
                gfs gi cn gtl gil gisl cov logstart bmapstart inodestart
                icfg_nib size icfg_dev kk qi s gy inum dn bm u pidv
                (DfracOwn (1/4)) dqb dqs m M4 sp0 K eb b lks w4 w5 w6
                (word_of_words lo om) w24 bp V
                HKup HKeo HK24 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
                Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HM4sp HM4thr
                HM4s1 HM4s2 HM4s3 Hal
                with "Hcg Hown Htce Hcce Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                      Hitab Hitinv Hesck Hireg Hropen Hslkk Hslkd Hdep Hidev
                      Hiinum Hivalid Hload Hshot Hfrz Hkeep Hru Hsbb Hsbi Hbmres Hpbare
                      Hprocs Hdev Hgeo Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
                      HbP H23 H24 [Hpback Hfds Hisl Hcont]").
      iEval (rewrite /wp_next).
      iIntros (CIDy) "%Hqy". iIntros (mf)
        "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc Hpbare Hsbb Hsbi
         Hbsl Hislot".
      iDestruct ("Hpback" with "Hpbare") as "Hpriv".
      (* the loan was never spent on this arm: fold it back beside the unit
         the tail's iput released. *)
      iDestruct (iref_slots_combine nsj 1 with "Hisl Hislot") as "Hisl".
      replace (nsj + 1)%nat with (S nsj) by lia.
      iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf (S nsj) with "[%] [%] Hcg Hown Htce Hcce
                Hpc Hsbb Hsbi Hbsl Hisl [Hpriv Hfds]").
      { exact Hcsf. }
      { reflexivity. }
      { rewrite /sys_open_post. iSplitR "Hfds"; [| iExact "Hfds"].
        iLeft. iSplitR; [iPureIntro; exact Ha0f | iExact "Hpriv"]. } }
    (* ---- the major is a legal device index ---- *)
    iApply (wp_bltu_fall_s_sconf (CID := CID5) (mword_of_int (SO + 0x5a))
              (mword_of_int 188 : mword 13) Ra4 Ra5 M4 (K - 24)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HM4a4 HM4a5;
                    exact (so_major_in (di_major dn) Hin))
              with "Hcg Hpc []").
    { iApply (soi_05a with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc".
    assert (Hpp5a : add_vec_int (mword_of_int (SO + 0x5a) : mword 64) 4
                    = mword_of_int (SO + 0x5e)) by pcw.
    iEval (rewrite Hpp5a) in "Hpc".
    iDestruct (cpu_own_transport CID0 CID6 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID0 CID6 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport CID0 CID6 eb (proc_addr jx)
                 ltac:(rewrite Hb; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID6)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (so_alloc (CID0 := CID6) gfl gf gs jx gl gu gd gk pd pav pu bn g
              gfs gi cn gtl gil gisl cov logstart bmapstart inodestart
              icfg_nib size icfg_dev kk qi s gy inum dn bm om lo nsj u
              pidv dqb dqs V m M4 sp0 K eb b lks w4 w5 w6 w24 bp
              HKfull Hkk eq_refl eq_refl Hinb Hgeom Hsize Hbm0 Hbmcov Hbmlog
              Hist0 Hiblk Hiblog Hcovb Hiu Hj Hgl Hlkempty Hdir Hal23 Hsp0
              HM4sp HM4thr HM4s0 HM4s1 HM4s2 HM4s3 Hal Hnspos
              with "Hcg Hown Htce Hcce Htext Hdata Hpc Hpe Hftab Hbio Hlog
                    Hseam Hgen Hitab Hitinv Hesck Hireg Hropen Hslkk Hslkd
                    Hdep Hidev Hiinum Hivalid Hload Hshot Hfrz Hkeep Hru Hpriv Hprocs
                    Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres Hbsl Hisl Hfds Hf1
                    Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23lo H23hi H24 Hcont").
  Qed.

  (* the per-slot projection out of the boot family, at the copy the
     syscall's contract names ([ProofSysMkdir.md_esc_acc]'s twin). *)
  Local Lemma so_esc_acc (cn : ic_names) (gfs : fs_names) (gi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) :
    (k < NINODE)%nat ->
    (ic_escrows cn gfs gi cov logstart -∗ ic_escrow cn gfs gi cov logstart k
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_escrows.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  (* ...and the entry's sleeplock out of the same boot family.  The O_CREATE
     arm never needs either: [create_locked] carries both names itself.  It
     is the else arm, which locks an inode namei merely NAMED, that has to
     project them. *)
  Local Lemma so_slk_acc (cn : ic_names) (k : nat) :
    (k < NINODE)%nat ->
    (ic_sleeplocks cn -∗
     ∃ gil gisl : gname,
       is_sleeplock_gen gil gisl (i_lock (ientry k)) "inode"%string
                        (ic_tok cn k) (slh_tok (icfg_isl k))
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_sleeplocks.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  (* ilock's ONE bread reference, carved out of the syscall's three. *)
  Local Lemma so_bs3 :
    (bslots 3 : iProp Σ) ⊣⊢ bslot ∗ bslots 2.
  Proof. rewrite /bslot. change 3%nat with (1 + 2)%nat. apply bslots_op. Qed.

  (* the cwd goes out to namei and comes back UNCHANGED, so
     [proc_priv_nocwd_cwd_pid]'s functional update is the identity. *)
  Local Lemma so_upd_cwd_id (V : pprivate) : upd_cwd V (pv_cwd V) = V.
  Proof. destruct V; reflexivity. Qed.

  (* ================================================================== *)
  (*  THE SYSCALL'S OWN EXIT CONTINUATION, at the process state argstr    *)
  (*  has already grown.  [so_cont] is this one WEAKENED to the join's    *)
  (*  two extra clauses; the adapter that turns this into that is inside  *)
  (*  [so_entry_c] and is three lines of arithmetic.                      *)
  (* ================================================================== *)
  Definition so_cont0 `{GEN : GenId} `{XI : CurCtx}
      (gf : gname) (bn : bio_names) (gfs : fs_names)
      (cov : gset Z) (logstart bmapstart inodestart size ninodes : Z)
      (ns : nat) (dqb dqs dqbs dqn : dfrac)
      (pj : mword 64) (pidv : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb b : bool) (lks : gset string)
      : CpuId -> iProp Σ :=
    fun (CIDx : CpuId) =>
      (∀ (mf : regfile) (ns' : nat),
         ⌜callee_saved m mf⌝ -∗
         (* THE WHOLE ALLOWANCE COMES BACK.  Every reference sys_open makes
            is either parked in the file entry it published -- which released
            its own unit to pay for it ([so_open_slot]) -- or iput before the
            syscall returns.  Nothing is spent for good, which is what lets
            the dispatch lend [IREFSPARE] and get [IREFSPARE] back. *)
         ⌜ns' = ns⌝ -∗
         sie_cap_gpr KT1 mf K b pj -∗
         cpu_own 0 eb pj b lks -∗
         trap_csrs_ext KT1 eb -∗
         cpu_claim_ext eb pj -∗
         pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
         sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
         sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
         sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
         sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
         bslots 3 -∗
         iref_slots ns' -∗
         sys_open_post gf pj pidv V (mf !!! Regidx Ra0 : mword 64) -∗
         WP (Loop : expr riscv_lang))%I.

  (* ================================================================== *)
  (*  THE O_CREATE ARM: +0x38 .. +0x48, AND ARM A-FAIL.                   *)
  (*                                                                    *)
  (*    c.li a3,0 ; c.li a2,0 ; c.li a1,2 ; addi a0,s0,-176 ;             *)
  (*    jal create ; c.mv s1,a0 ; c.beqz a0 -> +0xd2                      *)
  (*                                                                    *)
  (*  THE FLOOR IS THE WALK.  create's [ok = true] arm promises
      [iput_units <= u'] and nothing better, and [iput_units] is EXACTLY
      what each of ARMs D/E/F spends on its [iunlockput]
      ([SysOpenBudget.so_join_exact]); without that floor the arm reaches
      the join with a bare [u' <= u] whose corner is zero.                *)
  (*                                                                    *)
  (*  AND THE WITNESS IS FREE HERE.  create was called with T_FILE, so its
      report ([di_type dn = ty] on the made arm,
      [di_type dn ∈ {T_FILE, T_DEVICE}] on the found one) refutes T_DIR
      outright and the join's [di_type = T_DIR -> om = 0] premise is
      vacuous -- [so_tdir_zne] at a literal.  The else arm is where that
      premise is EARNED.                                                  *)
  (* ================================================================== *)
  Lemma so_entry_c `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gfl gf ga gpr : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32)
      (plen : nat) (bp : nat -> bv 8)
      (om lo : mword 32) (ns : nat) (Sb : gset Z)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (V : pprivate)
      (m N : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w4 w5 w6 w24 : mword 64) :
    (K_sys_open <= K)%nat ->
    dev = icfg_dev -> nib = icfg_nib -> g = icfg_log ->
    inodestart = icfg_ist -> dev = ROOTDEV -> (0 < nib)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    cov_below cov size ->
    bitmap_geom_ok cov logstart bmapstart size ->
    ireg_blocks_ok inodestart nib cov logstart ->
    bb_cstr bp plen ->
    (plen < 128)%nat ->
    1 < ninodes -> ninodes <= 16 * Z.of_nat nib -> ninodes < 2 ^ 31 ->
    16 * Z.of_nat nib <= 2 ^ 16 ->
    printk_gen_contract (kt := KT1) gpr gu gd ->
    (sys_open_slots <= ns)%nat ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    eb = true ->
    lks = ∅ ->
    is_aligned_paddr (Physaddr (pa_stk sp0 23)) 8 = true ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    so_sp sp0 N -> so_thr m N ->
    (N !!! Regidx Rs0 : mword 64) = sp0 ->
    (N !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    (N !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    so_al sp0 ->
    sie_cap_gpr KT1 N (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SO + 0x38)) -∗
    printk_env gpr gu gd -∗
    is_ftable gfl gf -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    kalloc_env ga None -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn gfs gi cov logstart -∗
    ic_sleeplocks cn -∗
    ireg_inv gi gfs inodestart nib -∗
    (* RULING B (iclaim-ledger.md §3.2): the sealed regime, threaded on to
       [SpecCreate] -> [SpecIalloc] -> [InodeRegion.ireg_claim_au].  It is
       on THIS arm only: [so_entry_n] is the arm that does not create. *)
    ireg_open -∗
    sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    bitmap_inv gfs bmapstart cov logstart size -∗
    proc_priv gf (proc_addr jx) pidv V -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (λ ξ : CtxId, disk_res (XI := ξ) gd pd pav pu) -∗
    log_opS g MAXOPBLOCKS Sb -∗
    bslots 3 -∗
    iref_slots ns -∗
    fd_slot -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] w4 -∗
    (pa_stk sp0 5) ↦₈[KT1] w5 -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 23) ↦₄[KT1] lo -∗
    (pa_add (pa_stk sp0 23) 4) ↦₄[KT1] om -∗
    (pa_stk sp0 24) ↦₈[KT1] w24 -∗
    wp_next true (proc_addr jx)
      (so_cont0 gf bn gfs cov logstart bmapstart inodestart size ninodes ns
                dqb dqs dqbs dqn (proc_addr jx) pidv V m K eb b lks) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hdevc Hnibc Hlogc Histc HdevR Hnib0 Hgeom Hsize Hbm0 Hbmcov
           Hbmlog Hist0 Hcovb Hbmgeo Hiregb Hpcstr Hplen Hni1 Hni2 Hni3 Hush
           Hprkc Hnsb Hj Hgl Heb Hlkempty Hal23 Hsp0 HNsp HNthr HNs0 HNs2 HNs3
           Hal.
    pose proof HK as HKfull.
    destruct (so_kb K HK) as (HKcr & HKna & HKai & HKas & HKbo & HKeo & HKil &
                              HKiu & HKit & HKip & HKup & HKfc & HKfa & HKfd &
                              HK10 & HK24 & Kpop).
    iIntros "Hcg Hown Htce Hcce #Htext #Hdata Hpc #Hpre #Hftab #Hbio
              #Hlog Hseam Hgen #Hkenv #Hitab #Hitinv #Hescrows #Hslks #Hireg
              #Hropen
              Hsbn Hsbi Hsbs Hsbb #Hbmres Hpriv #Hprocs #Hdev #Hgeo #Hdlk HopS
              Hbsl Hisl Hfds Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23lo H23hi H24
              Hcont".
    iPoseProof (printk_env_panic with "Hpre") as "#Hpe".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* ===== +0x38 c.li a3,0 -- minor ===== *)
    iApply (wp_cli_s_sconf (CID := CID0) (mword_of_int (SO + 0x38)) Ra3
              (mword_of_int 0 : mword 6)
              (sign_extend' 64 (mword_of_int 0 : mword 16)) N (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (soi_038 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (N1 := <[Regidx Ra3 := regval_into_reg
                  (sign_extend' 64 (mword_of_int 0 : mword 16))]> N).
    assert (HN1a3 : (N1 !!! Regidx Ra3 : mword 64)
                    = (sign_extend' 64 (mword_of_int 0 : mword 16)))
      by (rewrite /N1; apply upd_eq).
    assert (Hpp38 : add_vec_int (mword_of_int (SO + 0x38) : mword 64) 2
                    = mword_of_int (SO + 0x3a)) by pcw.
    iEval (rewrite Hpp38) in "Hpc".
    (* ===== +0x3a c.li a2,0 -- major ===== *)
    iApply (wp_cli_s_sconf (CID := CID1) (mword_of_int (SO + 0x3a)) Ra2
              (mword_of_int 0 : mword 6)
              (sign_extend' 64 (mword_of_int 0 : mword 16)) N1 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (soi_03a with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (N2 := <[Regidx Ra2 := regval_into_reg
                  (sign_extend' 64 (mword_of_int 0 : mword 16))]> N1).
    assert (HN2a2 : (N2 !!! Regidx Ra2 : mword 64)
                    = (sign_extend' 64 (mword_of_int 0 : mword 16)))
      by (rewrite /N2; apply upd_eq).
    assert (HN2a3 : (N2 !!! Regidx Ra3 : mword 64)
                    = (sign_extend' 64 (mword_of_int 0 : mword 16)))
      by (rewrite /N2 upd_ne; [exact HN1a3 | nz]).
    assert (Hpp3a : add_vec_int (mword_of_int (SO + 0x3a) : mword 64) 2
                    = mword_of_int (SO + 0x3c)) by pcw.
    iEval (rewrite Hpp3a) in "Hpc".
    (* ===== +0x3c c.li a1,2 -- T_FILE ===== *)
    iApply (wp_cli_s_sconf (CID := CID2) (mword_of_int (SO + 0x3c)) Ra1
              (mword_of_int 2 : mword 6)
              (sign_extend' 64 (SpecCreate.T_FILE : mword 16)) N2 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (soi_03c with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (N3 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64 (SpecCreate.T_FILE : mword 16))]> N2).
    assert (HN3a1 : (N3 !!! Regidx Ra1 : mword 64)
                    = (sign_extend' 64 (SpecCreate.T_FILE : mword 16)))
      by (rewrite /N3; apply upd_eq).
    assert (HN3a2 : (N3 !!! Regidx Ra2 : mword 64)
                    = (sign_extend' 64 (mword_of_int 0 : mword 16)))
      by (rewrite /N3 upd_ne; [exact HN2a2 | nz]).
    assert (HN3a3 : (N3 !!! Regidx Ra3 : mword 64)
                    = (sign_extend' 64 (mword_of_int 0 : mword 16)))
      by (rewrite /N3 upd_ne; [exact HN2a3 | nz]).
    assert (HN3s0 : (N3 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite /N3 upd_ne; [| nz]. rewrite /N2 upd_ne; [| nz].
      rewrite /N1 upd_ne; [| nz]. exact HNs0. }
    assert (Hpp3c : add_vec_int (mword_of_int (SO + 0x3c) : mword 64) 2
                    = mword_of_int (SO + 0x3e)) by pcw.
    iEval (rewrite Hpp3c) in "Hpc".
    (* ===== +0x3e addi a0,s0,-176 -- the path buffer ===== *)
    iApply (wp_addi4_s_sconf (CID := CID3) (mword_of_int (SO + 0x3e)) Ra0 Rs0
              (mword_of_int 3920 : mword 12) N3 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_03e with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (N4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (N3 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3920 : mword 12)))]> N3).
    assert (HN4a0 : (N4 !!! Regidx Ra0 : mword 64) = pa_stk sp0 22).
    { etransitivity; [ rewrite /N4; apply upd_eq |].
      rewrite HN3s0. apply so_bufpath. }
    assert (HN4a1 : (N4 !!! Regidx Ra1 : mword 64)
                    = (sign_extend' 64 (SpecCreate.T_FILE : mword 16)))
      by (rewrite /N4 upd_ne; [exact HN3a1 | nz]).
    assert (HN4a2 : (N4 !!! Regidx Ra2 : mword 64)
                    = (sign_extend' 64 (mword_of_int 0 : mword 16)))
      by (rewrite /N4 upd_ne; [exact HN3a2 | nz]).
    assert (HN4a3 : (N4 !!! Regidx Ra3 : mword 64)
                    = (sign_extend' 64 (mword_of_int 0 : mword 16)))
      by (rewrite /N4 upd_ne; [exact HN3a3 | nz]).
    assert (Hpp3e : add_vec_int (mword_of_int (SO + 0x3e) : mword 64) 4
                    = mword_of_int (SO + 0x42)) by pcw.
    iEval (rewrite Hpp3e) in "Hpc".
    (* ===== +0x42 jal ra,create ===== *)
    iApply (wp_jal_s_sconf (CID := CID4) (mword_of_int (SO + 0x42)) Rra
              (mword_of_int 2095708 : mword 21) N4 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_042 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (N5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x42) : mword 64) 4)]> N4).
    assert (Hjcr : add_vec (mword_of_int (SO + 0x42) : mword 64)
                     (sign_extend' 64 (mword_of_int 2095708 : mword 21))
                   = mword_of_int KernelSyms.create) by pcw.
    iEval (rewrite Hjcr) in "Hpc".
    assert (HN5ra : (N5 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x42) : mword 64) 4)
      by (rewrite /N5; apply upd_eq).
    assert (HN5a0 : (N5 !!! Regidx Ra0 : mword 64) = pa_stk sp0 22)
      by (rewrite /N5 upd_ne; [exact HN4a0 | nz]).
    assert (HN5a1 : (N5 !!! Regidx Ra1 : mword 64)
                    = (sign_extend' 64 (SpecCreate.T_FILE : mword 16)))
      by (rewrite /N5 upd_ne; [exact HN4a1 | nz]).
    assert (HN5a2 : (N5 !!! Regidx Ra2 : mword 64)
                    = (sign_extend' 64 (mword_of_int 0 : mword 16)))
      by (rewrite /N5 upd_ne; [exact HN4a2 | nz]).
    assert (HN5a3 : (N5 !!! Regidx Ra3 : mword 64)
                    = (sign_extend' 64 (mword_of_int 0 : mword 16)))
      by (rewrite /N5 upd_ne; [exact HN4a3 | nz]).
    assert (HN5sp : so_sp sp0 N5).
    { rewrite /so_sp /N5 upd_ne; [| nz]. rewrite /N4 upd_ne; [| nz].
      rewrite /N3 upd_ne; [| nz]. rewrite /N2 upd_ne; [| nz].
      rewrite /N1 upd_ne; [| nz]. exact HNsp. }
    assert (HN5s0 : (N5 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite /N5 upd_ne; [| nz]. rewrite /N4 upd_ne; [| nz]. exact HN3s0. }
    assert (HN5s2 : (N5 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /N5 upd_ne; [| nz]. rewrite /N4 upd_ne; [| nz].
      rewrite /N3 upd_ne; [| nz]. rewrite /N2 upd_ne; [| nz].
      rewrite /N1 upd_ne; [| nz]. exact HNs2. }
    assert (HN5s3 : (N5 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /N5 upd_ne; [| nz]. rewrite /N4 upd_ne; [| nz].
      rewrite /N3 upd_ne; [| nz]. rewrite /N2 upd_ne; [| nz].
      rewrite /N1 upd_ne; [| nz]. exact HNs3. }
    assert (HN5thr : so_thr m N5).
    { intros c Hc N2b N8 N9 N18 N19.
      rewrite /N5 upd_ne; [| regne]. rewrite /N4 upd_ne; [| regne].
      rewrite /N3 upd_ne; [| regne]. rewrite /N2 upd_ne; [| regne].
      rewrite /N1 upd_ne; [| regne].
      exact (HNthr c Hc N2b N8 N9 N18 N19). }
    iDestruct (so_buf_split (pa_stk sp0 22) bp plen Hplen with "HbP")
      as "[Hbufk Hbufrest]".
    iDestruct (cpu_own_transport CID0 CID5 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Create.wp_create_sconf (CID := CID5) gs jx gl gu gd gk pd pav pu bn
              g gfs gi cn gtl ga gf gpr cov logstart bmapstart inodestart nib
              ninodes size dev plen bp
              SpecCreate.T_FILE (mword_of_int 0) (mword_of_int 0)
              V MAXOPBLOCKS Sb ns pidv dqb dqs dqbs dqn
              N5 (K - 24)%nat eb b lks
              HKcr Hdevc Hnibc Hlogc Histc HdevR Hnib0 Hgeom Hsize Hbm0 Hbmcov
              Hbmlog Hist0 Hcovb Hbmgeo Hiregb Hpcstr
              ltac:(assert (E31 : (2 ^ 31 = 2147483648)%Z)
                      by (vm_compute; reflexivity); lia)
              Hni1 Hni2 Hni3 Hush
              ltac:(rewrite SpecCreate.T_FILE_value; lia)
              SpecCreate.T_FILE_ty_ok Hprkc
              ltac:(unfold create_units; lia) Hnsb Hj Hgl
              HN5a1 HN5a2 HN5a3 Heb
              with "Hcg Hown Htext Hpc Hdata Hpre Hbio Hlog Hkenv Hitab
                    Hitinv Hescrows Hslks Hireg Hropen Hsbn Hsbi Hsbs Hsbb
                    Hbmres
                    Hpriv [Hbufk] Hprocs Hdev Hgeo Hdlk Hbsl Hisl HopS").
    { iEval (rewrite HN5a0). iExact "Hbufk". }
    iIntros (CID6 Hq6 mcr ok made kk qi ss gy inum dn bm u1 Sb1 ns1)
      "%Hcscr Hcg Hown Hpc Hsbn Hsbi Hsbs Hsbb Hpriv Hbufk Hbsl
       %Hns1 Hisl %Hu1 HopS Hok".
    iEval (rewrite HN5a0) in "Hbufk".
    assert (Hpccr : ret_pc (N5 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0x46)) by (rewrite HN5ra; pcw).
    iEval (rewrite Hpccr) in "Hpc".
    (* the buffer, joined and renamed: nothing below reads it *)
    iDestruct (so_buf_join (pa_stk sp0 22) bp plen Hplen with "Hbufk Hbufrest")
      as "HbA".
    iDestruct (so_bytes_name (pa_stk sp0 22) 128 with "HbA") as (bp1) "HbP".
    assert (Hcrsp : so_sp sp0 mcr).
    { rewrite /so_sp (callee_saved_lookup Hcscr csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HN5sp. }
    assert (Hcrs0 : (mcr !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcscr Rs0 ltac:(vm_compute; reflexivity)).
      exact HN5s0. }
    assert (Hcrs2 : (mcr !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcscr Rs2 ltac:(vm_compute; reflexivity)).
      exact HN5s2. }
    assert (Hcrs3 : (mcr !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcscr Rs3 ltac:(vm_compute; reflexivity)).
      exact HN5s3. }
    assert (Hcrthr : so_thr m mcr).
    { intros c Hc N2b N8 N9 N18 N19. rewrite (callee_saved_lookup Hcscr c Hc).
      exact (HN5thr c Hc N2b N8 N9 N18 N19). }
    (* ===== +0x46 c.mv s1,a0 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID6) (mword_of_int (SO + 0x46)) Rs1 Ra0
              mcr (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_046 with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (P1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec zero_reg (mcr !!! Regidx Ra0))]> mcr).
    assert (HP1s1 : (P1 !!! Regidx Rs1 : mword 64) = (mcr !!! Regidx Ra0 : mword 64)).
    { etransitivity; [ rewrite /P1; apply upd_eq |]. apply add_vec_zero_l. }
    assert (HP1a0 : (P1 !!! Regidx Ra0 : mword 64) = (mcr !!! Regidx Ra0 : mword 64))
      by (rewrite /P1 upd_ne; [reflexivity | nz]).
    assert (HP1sp : so_sp sp0 P1)
      by (rewrite /so_sp /P1 upd_ne; [exact Hcrsp | nz]).
    assert (HP1s0 : (P1 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /P1 upd_ne; [exact Hcrs0 | nz]).
    assert (HP1s2 : (P1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P1 upd_ne; [exact Hcrs2 | nz]).
    assert (HP1s3 : (P1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P1 upd_ne; [exact Hcrs3 | nz]).
    assert (HP1thr : so_thr m P1).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /P1 upd_ne; [| regne].
      exact (Hcrthr c Hc N2b N8 N9 N18 N19). }
    assert (Hpp46 : add_vec_int (mword_of_int (SO + 0x46) : mword 64) 2
                    = mword_of_int (SO + 0x48)) by pcw.
    iEval (rewrite Hpp46) in "Hpc".
    (* ===== +0x48 c.beqz a0, +0xd2  [ARM A-FAIL] ===== *)
    destruct ok.
    2:{ (* ---- create refused: nothing is locked and nothing is held ---- *)
      iDestruct "Hok" as "%Hcra0".
      iApply (wp_cbeqz_taken_s_sconf (CID := CID7) (mword_of_int (SO + 0x48))
                (mword_of_int 69 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                P1 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HP1a0 Hcra0; exact so_eqz_zero)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_048 with "Htext"). }
      iIntros (CID8 Hq8). iNext. iIntros "Hcg Hpc".
      assert (Htg48 : add_vec (mword_of_int (SO + 0x48) : mword 64)
                        (sign_extend' 64
                           (sign_extend' 13 (concat_vec (mword_of_int 69 : mword 8) ('b"0"))))
                      = mword_of_int (SO + 0xd2)) by pcw.
      iEval (rewrite Htg48) in "Hpc".
      iDestruct (so_omode_join sp0 lo om Hal23 with "H23lo H23hi") as "H23".
      iDestruct (proc_priv_bare_acc with "Hpriv") as "[Hpbare Hpback]".
      iDestruct (cpu_own_transport CID6 CID8 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (log_opS_op with "HopS") as "Hop".
      iApply (Tails.so_tail_a (CID0 := CID8) gs jx gl gu gd gk pd pav pu bn g
                gfs cov logstart dev u1 pidv (DfracOwn (1/4)) m P1 sp0 K eb b
                lks w4 w5 w6 (word_of_words lo om) w24 bp1 V
                HKeo HK24 Kpop Hgeom Hj Hgl Hlkempty Hsp0 HP1sp HP1thr HP1s2
                HP1s3 Hal
                with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                      Hpbare Hprocs Hdev Hgeo Hdlk Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
                      HbP H23 H24 [Hpback Hfds Hisl Hsbn Hsbi Hsbs Hsbb
                      Hbsl Hcont]").
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      iEval (rewrite /wp_next).
      iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc
                                           Hpbare".
      iDestruct ("Hpback" with "Hpbare") as "Hpriv".
      iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf ns1 with "[%] [%] Hcg Hown Htce Hcce Hpc
                Hsbn Hsbi Hsbs Hsbb Hbsl Hisl [Hpriv Hfds]").
      { exact Hcsf. }
      { unfold sys_open_slots, create_slots in *. lia. }
      { rewrite /sys_open_post. iSplitR "Hfds"; [| iExact "Hfds"].
        iLeft. iSplitR; [iPureIntro; exact Ha0f | iExact "Hpriv"]. } }
    (* ---- create SUCCEEDED: the locked inode, straight to the join ---- *)
    iDestruct "Hok" as "[%Hokf Hlocked]".
    destruct Hokf as (Hcra0 & Hkk & Hinum & Hrep).
    assert (Hipnz : ientry kk <> (zero_reg : mword 64))
      by (apply ientry_ne_zero; lia).
    (* THE WITNESS, and on this arm it is free: create was called with
       T_FILE, so the record it reports is never a directory. *)
    assert (Htyne : di_type dn <> (mword_of_int 1 : mword 16)).
    { destruct made.
      - destruct Hrep as (Hty & _). rewrite Hty. unfold SpecCreate.T_FILE.
        intro Hc. apply (f_equal bv_unsigned) in Hc. by vm_compute in Hc.
      - destruct Hrep as (_ & [Hty | Hty]); rewrite Hty;
          [unfold SpecCreate.T_FILE | unfold SpecCreate.T_DEVICE];
          intro Hc; apply (f_equal bv_unsigned) in Hc; by vm_compute in Hc. }
    assert (Hdirw : bv_unsigned (di_type dn) = T_DIR_z ->
                    om = (mword_of_int 0 : mword 32)).
    { intro Hc. exfalso. exact (so_tdir_zne (di_type dn) Htyne Hc). }
    destruct (Hiregb inum ltac:(lia)) as [Hibcov Hiblog].
    iDestruct (so_esc_acc cn gfs gi cov logstart kk ltac:(lia)
                 with "Hescrows") as "#Hesc".
    iDestruct "Hlocked" as (gil gisl)
      "(Hslk & Hslkd & Hdep & Hidev & Hiinum & Hivalid & Hload &
        Hshot & Hfrz & Href & Hru)".
    iApply (wp_cbeqz_fall_s_sconf (CID := CID7) (mword_of_int (SO + 0x48))
              (mword_of_int 69 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              P1 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HP1a0 Hcra0;
                    apply (proj2 (eq_vec_false_iff _ _)); exact Hipnz)
              with "Hcg Hpc []").
    { iApply (soi_048 with "Htext"). }
    iIntros (CID8 Hq8) "Hcg Hpc".
    assert (Hpp48 : add_vec_int (mword_of_int (SO + 0x48) : mword 64) 2
                    = mword_of_int (SO + 0x4a)) by pcw.
    iEval (rewrite Hpp48) in "Hpc".
    assert (HP1s1i : (P1 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite HP1s1; exact Hcra0).
    iDestruct (log_opS_op with "HopS") as "Hop".
    iDestruct (cpu_own_transport CID6 CID8 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    (* ---- THE ADAPTER: the syscall's exit continuation, weakened to the
       join's extra clause: the iref arithmetic is create's [S ns1 <= ns]
       plus the join's [ns1 <= ns' <= S ns1]. ---- *)
    iAssert (wp_next true (proc_addr jx)
               (so_cont gf bn gfs cov logstart bmapstart inodestart size
                        ns1 dqb dqs (proc_addr jx) pidv V m K eb b lks))
      with "[Hcont Hsbn Hsbs]" as "Hcontj".
    { iEval (rewrite /wp_next). iIntros (CIDz) "%Hqz".
      iEval (rewrite /so_cont). iIntros (mf ns2) "%Hcsf %Hns2".
      iIntros "Hcg Hown Htce Hcce Hpc Hsbb Hsbi Hbsl Hisl Hpost".
      iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf ns2 with "[%] [%] Hcg Hown Htce Hcce Hpc
                Hsbn Hsbi Hsbs Hsbb Hbsl Hisl Hpost").
      { exact Hcsf. }
      { cbn in Hns1.
        unfold sys_open_slots, create_slots in *. lia. } }
    iApply (so_join (CID0 := CID8) gfl gf gs jx gl gu gd gk pd pav pu bn g
              gfs gi cn gtl gil gisl cov logstart bmapstart inodestart nib
              size dev kk qi ss gy inum dn bm om lo ns1 u1 pidv dqb dqs
              V m P1 sp0 K eb b lks w4 w5 w6 w24 bp1
              HKfull Hkk Hdevc Hnibc ltac:(lia) Hgeom Hsize Hbm0 Hbmcov Hbmlog
              Hist0 Hibcov Hiblog Hcovb
              ltac:(exact (proj2 (proj2 Hu1) eq_refl)) Hj Hgl Hlkempty Hdirw
              Hal23 Hsp0 HP1sp HP1thr HP1s0 HP1s1i HP1s2 HP1s3 Hal ltac:(cbn in Hns1; unfold sys_open_slots, create_slots in *; lia)
              with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hftab Hbio Hlog
                    Hseam Hgen Hitab Hitinv Hesc Hireg Hropen Hslk Hslkd Hdep
                    Hidev Hiinum Hivalid Hload Hshot Hfrz Href Hru Hpriv Hprocs
                    Hdev
                    Hgeo Hdlk Hop Hsbb Hsbi Hbmres Hbsl Hisl Hfds Hf1 Hf2 Hf3
                    Hf4 Hf5 Hf6 HbP H23lo H23hi H24 Hcontj").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
  Qed.

  (* ================================================================== *)
  (*  THE else ARM: +0xdc .. +0xfa, AND ARMS B-FAIL AND C-FAIL.          *)
  (*                                                                    *)
  (*    addi a0,s0,-176 ; jal namei ; c.mv s1,a0 ; c.beqz a0 -> +0x10c   *)
  (*    jal ilock ; lh a4,68(s1) ; c.li a5,1 ; bne -> +0x4a              *)
  (*    lw a5,-180(s0) ; c.beqz a5 -> +0x5e                              *)
  (*                                                                    *)
  (*  TWO BLOCK EXITS, NOT ONE.  The [bne] at +0xf2 leaves for the JOIN   *)
  (*  at +0x4a (the inode is not a directory); the [c.beqz] at +0xfa      *)
  (*  leaves for +0x5e -- [so_alloc], SKIPPING the T_DEVICE test, because *)
  (*  gcc knows a T_DIR inode cannot be a T_DEVICE.  Both are ordinary    *)
  (*  lemma applications, so the linear-exit problem of a chained pair    *)
  (*  never arises.                                                      *)
  (*                                                                    *)
  (*  BLOCKER 2's ANSWER IS FOUR LINES, and it is this arm's whole ghost  *)
  (*  content.  namei hands back [inode_held], which is generation-FREE;  *)
  (*  [so_publish] twenty instructions later needs the parent and the     *)
  (*  share ilock consumed at ONE named generation.  So: shed the         *)
  (*  reference ([inode_ref_shed]), NAME the share's generation           *)
  (*  ([inode_shr_gen_intro]) and the retained parent's                   *)
  (*  ([inode_ref_short_gen_intro]), and PIN the two together             *)
  (*  ([inode_ref_short_shr_gen_agree], which is [live_gen_agree] at the  *)
  (*  pointer-free altitude).  ilock then reports [ity_shot] and its      *)
  (*  deposit at that same [g].  The O_CREATE arm needs none of this --   *)
  (*  [create_locked] hands the parent back generation-NAMED already.     *)
  (*                                                                    *)
  (*  AND THE T_DIR WITNESS IS *EARNED* HERE.  On the [bne]-taken route   *)
  (*  the type is not T_DIR and [so_tdir_zne] makes the join's premise    *)
  (*  vacuous; on the fall-through the [c.beqz] at +0xfa forces           *)
  (*  [omode = O_RDONLY = 0] ([so_omode_eqz]), which is exactly           *)
  (*  [so_dir_forced]'s hypothesis -- and through [so_pay_witness] that   *)
  (*  is what says a WRITABLE fd never names a directory.                 *)
  (* ================================================================== *)
  Lemma so_entry_n `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gfl gf ga gpr : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32)
      (plen : nat) (bp : nat -> bv 8)
      (om lo : mword 32) (ns : nat) (Sb : gset Z)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (V : pprivate)
      (m N : regfile) (sp0 : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (w4 w5 w6 w24 : mword 64) :
    (K_sys_open <= K)%nat ->
    dev = icfg_dev -> nib = icfg_nib -> g = icfg_log ->
    inodestart = icfg_ist -> dev = ROOTDEV -> (0 < nib)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    cov_below cov size ->
    bitmap_geom_ok cov logstart bmapstart size ->
    ireg_blocks_ok inodestart nib cov logstart ->
    bb_cstr bp plen ->
    (plen < 128)%nat ->
    1 < ninodes -> ninodes <= 16 * Z.of_nat nib -> ninodes < 2 ^ 31 ->
    16 * Z.of_nat nib <= 2 ^ 16 ->
    printk_gen_contract (kt := KT1) gpr gu gd ->
    (sys_open_slots <= ns)%nat ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    eb = true ->
    lks = ∅ ->
    is_aligned_paddr (Physaddr (pa_stk sp0 23)) 8 = true ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    so_sp sp0 N -> so_thr m N ->
    (N !!! Regidx Rs0 : mword 64) = sp0 ->
    (N !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    (N !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    so_al sp0 ->
    sie_cap_gpr KT1 N (K - 24) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jx) -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SO + 0xdc)) -∗
    printk_env gpr gu gd -∗
    is_ftable gfl gf -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    kalloc_env ga None -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn gfs gi cov logstart -∗
    ic_sleeplocks cn -∗
    ireg_inv gi gfs inodestart nib -∗
    ireg_open -∗
    sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    bitmap_inv gfs bmapstart cov logstart size -∗
    proc_priv gf (proc_addr jx) pidv V -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (λ ξ : CtxId, disk_res (XI := ξ) gd pd pav pu) -∗
    log_opS g MAXOPBLOCKS Sb -∗
    bslots 3 -∗
    iref_slots ns -∗
    fd_slot -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] w4 -∗
    (pa_stk sp0 5) ↦₈[KT1] w5 -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 22) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 23) ↦₄[KT1] lo -∗
    (pa_add (pa_stk sp0 23) 4) ↦₄[KT1] om -∗
    (pa_stk sp0 24) ↦₈[KT1] w24 -∗
    wp_next true (proc_addr jx)
      (so_cont0 gf bn gfs cov logstart bmapstart inodestart size ninodes ns
                dqb dqs dqbs dqn (proc_addr jx) pidv V m K eb b lks) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hdevc Hnibc Hlogc Histc HdevR Hnib0 Hgeom Hsize Hbm0 Hbmcov
           Hbmlog Hist0 Hcovb Hbmgeo Hiregb Hpcstr Hplen Hni1 Hni2 Hni3 Hush
           Hprkc Hnsb Hj Hgl Heb Hlkempty Hal23 Hsp0 HNsp HNthr HNs0 HNs2 HNs3
           Hal.
    pose proof HK as HKfull.
    destruct (so_kb K HK) as (HKcr & HKna & HKai & HKas & HKbo & HKeo & HKil &
                              HKiu & HKit & HKip & HKup & HKfc & HKfa & HKfd &
                              HK10 & HK24 & Kpop).
    assert (Hns3 : (3 <= ns)%nat)
      by (revert Hnsb; unfold sys_open_slots, create_slots; lia).
    iIntros "Hcg Hown Htce Hcce #Htext #Hdata Hpc #Hpre #Hftab #Hbio
              #Hlog Hseam Hgen #Hkenv #Hitab #Hitinv #Hescrows #Hslks #Hireg #Hropen
              Hsbn Hsbi Hsbs Hsbb #Hbmres Hpriv #Hprocs #Hdev #Hgeo #Hdlk HopS
              Hbsl Hisl Hfds Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23lo H23hi H24
              Hcont".
    iPoseProof (printk_env_panic with "Hpre") as "#Hpe".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* ===== +0xdc addi a0,s0,-176 -- the path buffer ===== *)
    iApply (wp_addi4_s_sconf (CID := CID0) (mword_of_int (SO + 0xdc)) Ra0 Rs0
              (mword_of_int 3920 : mword 12) N (K - 24)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_0dc with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (N1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (N !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3920 : mword 12)))]> N).
    assert (HN1a0 : (N1 !!! Regidx Ra0 : mword 64) = pa_stk sp0 22).
    { etransitivity; [ rewrite /N1; apply upd_eq |].
      rewrite HNs0. apply so_bufpath. }
    assert (HN1sp : so_sp sp0 N1)
      by (rewrite /so_sp /N1 upd_ne; [exact HNsp | nz]).
    assert (HN1s0 : (N1 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /N1 upd_ne; [exact HNs0 | nz]).
    assert (HN1s2 : (N1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /N1 upd_ne; [exact HNs2 | nz]).
    assert (HN1s3 : (N1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /N1 upd_ne; [exact HNs3 | nz]).
    assert (HN1thr : so_thr m N1).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /N1 upd_ne; [| regne].
      exact (HNthr c Hc N2b N8 N9 N18 N19). }
    assert (Hppdc : add_vec_int (mword_of_int (SO + 0xdc) : mword 64) 4
                    = mword_of_int (SO + 0xe0)) by pcw.
    iEval (rewrite Hppdc) in "Hpc".
    (* ===== +0xe0 jal ra,namei ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SO + 0xe0)) Rra
              (mword_of_int 2091160 : mword 21) N1 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_0e0 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (N2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0xe0) : mword 64) 4)]> N1).
    assert (Hjna : add_vec (mword_of_int (SO + 0xe0) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091160 : mword 21))
                   = mword_of_int KernelSyms.namei) by pcw.
    iEval (rewrite Hjna) in "Hpc".
    assert (HN2ra : (N2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0xe0) : mword 64) 4)
      by (rewrite /N2; apply upd_eq).
    assert (HN2a0 : (N2 !!! Regidx Ra0 : mword 64) = pa_stk sp0 22)
      by (rewrite /N2 upd_ne; [exact HN1a0 | nz]).
    assert (HN2sp : so_sp sp0 N2)
      by (rewrite /so_sp /N2 upd_ne; [exact HN1sp | nz]).
    assert (HN2s0 : (N2 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /N2 upd_ne; [exact HN1s0 | nz]).
    assert (HN2s2 : (N2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /N2 upd_ne; [exact HN1s2 | nz]).
    assert (HN2s3 : (N2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /N2 upd_ne; [exact HN1s3 | nz]).
    assert (HN2thr : so_thr m N2).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /N2 upd_ne; [| regne].
      exact (HN1thr c Hc N2b N8 N9 N18 N19). }
    (* ---- the process, carved for namei: the BLOCK and the cwd REFERENCE,
       and the two-slot allowance the walk takes EXACTLY.  [p->cwd] is one of
       the block's own cells now, so namei borrows it for its own load and
       nothing here carries it. ---- *)
    (* three-way now: [FirstTok.first_tok] parks beside the reference. *)
    iDestruct (proc_priv_split_cwd gf (proc_addr jx) pidv V with "Hpriv")
      as "[Hpnc [Href Hftok]]".
    iEval (rewrite proc_priv_nocwd_bare) in "Hpnc".
    iDestruct "Hpnc" as "[Hpbare Hofiles]".
    iDestruct (cwd_ref_held with "Href") as "Hcwdref".
    iDestruct (iref_slots_split 2 (ns - 2) with "[Hisl]") as "[Hir2 Hirr]".
    { replace (2 + (ns - 2))%nat with ns by lia. iExact "Hisl". }
    iDestruct (so_buf_split (pa_stk sp0 22) bp plen Hplen with "HbP")
      as "[Hbufk Hbufrest]".
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Namei.wp_namei_gen (CID := CID2) gs jx gl gu gd gk pd pav pu bn
              g gfs gi cn gtl ga gf cov logstart bmapstart inodestart nib
              size dev plen bp MAXOPBLOCKS Sb
              pidv (DfracOwn (1/4)) dqb dqs (DfracOwn 1)
              N2 (K - 24)%nat eb b lks V
              HKna Hdevc Hnibc Hlogc Histc HdevR Hnib0 Hgeom Hsize Hbm0 Hbmcov
              Hbmlog Hist0 Hcovb Hiregb Hpcstr
              ltac:(exact (proj2 (so_len_range plen Hplen)))
              ltac:(apply so_namei_need) Hj Hgl
              with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hkenv Hitab Hitinv
                    Hescrows Hslks Hireg Hropen Hprocs Hdev Hgeo Hdlk Hsbb Hsbi
                    Hbmres Hpbare Hcwdref [Hbufk] Hbsl Hir2 HopS").
    (* namei is eb-generic now; sys_open is still at [eb = true]. *)
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iEval (rewrite HN2a0). iExact "Hbufk". }
    iIntros (CID3 Hq3 mna n1 Sb1 ok ipv w1)
      "%Hcsna Hcg Hown _ _ Hpc Hsbb Hsbi Hpbare Hcwdref
       Hbufk Hbsl %HSb1 %Hw1 %Hn1 HopS Hres".
    iEval (rewrite HN2a0) in "Hbufk".
    assert (Hpcna : ret_pc (N2 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0xe4)) by (rewrite HN2ra; pcw).
    iEval (rewrite Hpcna) in "Hpc".
    (* the buffer, joined and renamed: nothing below reads it *)
    iDestruct (so_buf_join (pa_stk sp0 22) bp plen Hplen with "Hbufk Hbufrest")
      as "HbA".
    iDestruct (so_bytes_name (pa_stk sp0 22) 128 with "HbA") as (bp1) "HbP".
    assert (Hnasp : so_sp sp0 mna).
    { rewrite /so_sp (callee_saved_lookup Hcsna csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HN2sp. }
    assert (Hnas0 : (mna !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsna Rs0 ltac:(vm_compute; reflexivity)).
      exact HN2s0. }
    assert (Hnas2 : (mna !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcsna Rs2 ltac:(vm_compute; reflexivity)).
      exact HN2s2. }
    assert (Hnas3 : (mna !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcsna Rs3 ltac:(vm_compute; reflexivity)).
      exact HN2s3. }
    assert (Hnathr : so_thr m mna).
    { intros c Hc N2b N8 N9 N18 N19. rewrite (callee_saved_lookup Hcsna c Hc).
      exact (HN2thr c Hc N2b N8 N9 N18 N19). }
    (* ===== +0xe4 c.mv s1,a0 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID3) (mword_of_int (SO + 0xe4)) Rs1 Ra0
              mna (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_0e4 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (P1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec zero_reg (mna !!! Regidx Ra0))]> mna).
    assert (HP1s1 : (P1 !!! Regidx Rs1 : mword 64) = (mna !!! Regidx Ra0 : mword 64)).
    { etransitivity; [ rewrite /P1; apply upd_eq |]. apply add_vec_zero_l. }
    assert (HP1a0 : (P1 !!! Regidx Ra0 : mword 64) = (mna !!! Regidx Ra0 : mword 64))
      by (rewrite /P1 upd_ne; [reflexivity | nz]).
    assert (HP1sp : so_sp sp0 P1)
      by (rewrite /so_sp /P1 upd_ne; [exact Hnasp | nz]).
    assert (HP1s0 : (P1 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /P1 upd_ne; [exact Hnas0 | nz]).
    assert (HP1s2 : (P1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P1 upd_ne; [exact Hnas2 | nz]).
    assert (HP1s3 : (P1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P1 upd_ne; [exact Hnas3 | nz]).
    assert (HP1thr : so_thr m P1).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /P1 upd_ne; [| regne].
      exact (Hnathr c Hc N2b N8 N9 N18 N19). }
    assert (Hppe4 : add_vec_int (mword_of_int (SO + 0xe4) : mword 64) 2
                    = mword_of_int (SO + 0xe6)) by pcw.
    iEval (rewrite Hppe4) in "Hpc".
    (* ===== +0xe6 c.beqz a0, +0x10c  [ARM B-FAIL] ===== *)
    destruct ok.
    2:{ (* ---- namei refused: nothing is locked and the two slots come back ---- *)
      iDestruct "Hres" as "[%Hnaz Hir2b]".
      iApply (wp_cbeqz_taken_s_sconf (CID := CID4) (mword_of_int (SO + 0xe6))
                (mword_of_int 19 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                P1 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HP1a0 Hnaz; exact so_eqz_zero)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_0e6 with "Htext"). }
      iIntros (CID5 Hq5). iNext. iIntros "Hcg Hpc".
      assert (Htge6 : add_vec (mword_of_int (SO + 0xe6) : mword 64)
                        (sign_extend' 64
                           (sign_extend' 13 (concat_vec (mword_of_int 19 : mword 8) ('b"0"))))
                      = mword_of_int (SO + 0x10c)) by pcw.
      iEval (rewrite Htge6) in "Hpc".
      (* the process, put back whole and then re-carved for the tail's pid *)
      iDestruct (cwd_ref_of_held with "Hcwdref") as "Href".
      iCombine "Hpbare Hofiles" as "Hpnc".
    iEval (rewrite -proc_priv_nocwd_bare) in "Hpnc".
      iDestruct (proc_priv_split_cwd gf (proc_addr jx) pidv V
                   with "[Hpnc Href Hftok]") as "Hpriv";
        [iSplitL "Hpnc"; [iExact "Hpnc" | iFrame "Href Hftok"] |].
      iDestruct (proc_priv_bare_acc with "Hpriv") as "[Hpbare Hpback2]".
      iDestruct (iref_slots_combine 2 (ns - 2) with "Hir2b Hirr") as "Hisl".
      assert (Hnsb2 : (2 + (ns - 2))%nat = ns) by lia.
      iEval (rewrite Hnsb2) in "Hisl".
      iDestruct (so_omode_join sp0 lo om Hal23 with "H23lo H23hi") as "H23".
      iDestruct (log_opS_op with "HopS") as "Hop".
      iDestruct (cpu_own_transport CID3 CID5 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (Tails.so_tail_b (CID0 := CID5) gs jx gl gu gd gk pd pav pu bn g
                gfs cov logstart dev n1 pidv (DfracOwn (1/4)) m P1 sp0 K eb b
                lks w4 w5 w6 (word_of_words lo om) w24 bp1 V
                HKeo HK24 Kpop Hgeom Hj Hgl Hlkempty Hsp0 HP1sp HP1thr HP1s2
                HP1s3 Hal
                with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen
                      Hpbare Hprocs Hdev Hgeo Hdlk Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6
                      HbP H23 H24 [Hpback2 Hfds Hisl Hsbn Hsbi Hsbs Hsbb
                      Hbsl Hcont]").
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      iEval (rewrite /wp_next).
      iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc
                                           Hpbare".
      iDestruct ("Hpback2" with "Hpbare") as "Hpriv".
      iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf ns with "[%] [%] Hcg Hown Htce Hcce Hpc
                Hsbn Hsbi Hsbs Hsbb Hbsl Hisl [Hpriv Hfds]").
      { exact Hcsf. }
      { unfold sys_open_slots, create_slots in *. lia. }
      { rewrite /sys_open_post. iSplitR "Hfds"; [| iExact "Hfds"].
        iLeft. iSplitR; [iPureIntro; exact Ha0f | iExact "Hpriv"]. } }
    (* ---- namei RESOLVED: the reference, shed and generation-named ---- *)
    iDestruct "Hres" as "(%Hnaip & Hheldip & Hir1)".
    iDestruct (inode_held_ne_zero with "Hheldip") as %Hipnz.
    iApply (wp_cbeqz_fall_s_sconf (CID := CID4) (mword_of_int (SO + 0xe6))
              (mword_of_int 19 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              P1 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HP1a0 Hnaip;
                    apply (proj2 (eq_vec_false_iff _ _)); exact Hipnz)
              with "Hcg Hpc []").
    { iApply (soi_0e6 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    assert (Hppe6 : add_vec_int (mword_of_int (SO + 0xe6) : mword 64) 2
                    = mword_of_int (SO + 0xe8)) by pcw.
    iEval (rewrite Hppe6) in "Hpc".
    (* ===== BLOCKER 2's FOUR LINES ===== *)
    iDestruct "Hheldip" as (kk qq inum) "(%Hipe & %Hkk & %Hinumc & Hrefip & Hru)".
    iEval (rewrite -Hdevc) in "Hrefip".
    assert (Hinb : bv_unsigned inum < 16 * Z.of_nat nib)
      by (rewrite Hnibc; exact Hinumc).
    destruct (Hiregb inum Hinb) as [Hiblk Hiblog].
    iEval (rewrite inode_ref_shed) in "Hrefip".
    iDestruct "Hrefip" as "[Hkeep Hshr]".
    iEval (rewrite inode_shr_gen_intro) in "Hshr".
    iDestruct "Hshr" as (gy) "Hshr".
    iEval (rewrite inode_ref_short_gen_intro) in "Hkeep".
    iDestruct "Hkeep" as (gp) "Hkeep".
    iDestruct (inode_ref_short_shr_gen_agree with "Hkeep Hshr") as %->.
    iDestruct (so_esc_acc cn gfs gi cov logstart kk Hkk with "Hescrows")
      as "#Hesck".
    iDestruct (so_slk_acc cn kk Hkk with "Hslks") as (gil gisl) "#Hslkk".
    iDestruct (so_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
    (* the reference ledger at the join: namei took two and gave one back *)
    iDestruct (iref_slots_combine 1 (ns - 2) with "Hir1 Hirr") as "Hisl".
    assert (Hnsj : (1 + (ns - 2))%nat = (ns - 1)%nat) by lia.
    iEval (rewrite Hnsj) in "Hisl".
    assert (Hiu : (iput_units <= n1)%nat)
      by exact (so_bud_iput _ w1 true (proj1 Hn1)).
    rewrite Hnaip Hipe in HP1s1.
    rewrite Hnaip Hipe in HP1a0.
    (* ===== +0xe8 jal ra,ilock  (a0 is STILL namei's return) ===== *)
    iApply (wp_jal_s_sconf (CID := CID5) (mword_of_int (SO + 0xe8)) Rra
              (mword_of_int 2088964 : mword 21) P1 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_0e8 with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (P2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0xe8) : mword 64) 4)]> P1).
    assert (Hjil : add_vec (mword_of_int (SO + 0xe8) : mword 64)
                     (sign_extend' 64 (mword_of_int 2088964 : mword 21))
                   = mword_of_int KernelSyms.ilock) by pcw.
    iEval (rewrite Hjil) in "Hpc".
    assert (HP2ra : (P2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0xe8) : mword 64) 4)
      by (rewrite /P2; apply upd_eq).
    assert (HP2a0 : (P2 !!! Regidx Ra0 : mword 64) = ientry kk)
      by (rewrite /P2 upd_ne; [exact HP1a0 | nz]).
    assert (HP2sp : so_sp sp0 P2)
      by (rewrite /so_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2s0 : (P2 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /P2 upd_ne; [exact HP1s0 | nz]).
    assert (HP2s1 : (P2 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /P2 upd_ne; [exact HP1s1 | nz]).
    assert (HP2s2 : (P2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s2 | nz]).
    assert (HP2s3 : (P2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1s3 | nz]).
    assert (HP2thr : so_thr m P2).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hc N2b N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID3 CID6 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Ilock.wp_ilock_sconf (CID := CID6) gs jx gl gu gd gk pd pav pu bn
              gfs gi cn gil gisl cov logstart inodestart nib
              kk (qq/2)%Qp gy PlainK dev inum pidv (DfracOwn (1/4)) dqs
              P2 (K - 24)%nat eb b lks V
              HKil Hkk Hgeom Hist0 Hiblk Hinb Hj Hgl HP2a0
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hitinv Hesck Hireg
                    Hslkk Hshr Hru Hsbi Hpbare Hprocs Hdev Hgeo Hdlk Hbs1").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iIntros (CID7 Hq7 mil dn bm fl)
      "%Hcsil Hcg Hown _ _ Hpc Hpbare Hsbi Hbs1 Hslkd Hdep
       Hidev Hiinum Hivalid Hload #Hshot Hfrz %Hfl Hru %Hilkp".
    assert (Hpcil : ret_pc (P2 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0xec)) by (rewrite HP2ra; pcw).
    iEval (rewrite Hpcil) in "Hpc".
    iDestruct (so_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
      [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
    (* the process, put back whole: everything below wants [proc_priv] *)
    iDestruct (cwd_ref_of_held with "Hcwdref") as "Href".
    iCombine "Hpbare Hofiles" as "Hpnc".
    iEval (rewrite -proc_priv_nocwd_bare) in "Hpnc".
    iDestruct (proc_priv_split_cwd gf (proc_addr jx) pidv V
                 with "[Hpnc Href Hftok]") as "Hpriv";
      [iSplitL "Hpnc"; [iExact "Hpnc" | iFrame "Href Hftok"] |].
    assert (Hilsp : so_sp sp0 mil).
    { rewrite /so_sp (callee_saved_lookup Hcsil csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HP2sp. }
    assert (Hils0 : (mil !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsil Rs0 ltac:(vm_compute; reflexivity)).
      exact HP2s0. }
    assert (Hils1 : (mil !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite (callee_saved_lookup Hcsil Rs1 ltac:(vm_compute; reflexivity)).
      exact HP2s1. }
    assert (Hils2 : (mil !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcsil Rs2 ltac:(vm_compute; reflexivity)).
      exact HP2s2. }
    assert (Hils3 : (mil !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcsil Rs3 ltac:(vm_compute; reflexivity)).
      exact HP2s3. }
    assert (Hilthr : so_thr m mil).
    { intros c Hc N2b N8 N9 N18 N19. rewrite (callee_saved_lookup Hcsil c Hc).
      exact (HP2thr c Hc N2b N8 N9 N18 N19). }
    (* ===== +0xec lh a4,68(s1) -- ip->type ===== *)
    iDestruct (so_meta_acc with "Hload") as "[Hmeta Hlback]".
    iDestruct (so_type_acc with "Hmeta") as "[Hity Hmback]".
    iEval (rewrite /i_type) in "Hity".
    iApply (wp_lh_s_sconf (CID := CID7) (kt := KT1) (ktd := KT0) (mword_of_int (SO + 0xec)) Ra4 Rs1
              (mword_of_int 68 : mword 12) mil (K - 24)%nat
              (di_type dn : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hity]").
    { iApply (soi_0ec with "Htext"). }
    { iEval (rgne; rewrite Hils1). iExact "Hity". }
    iIntros (CID8 Hq8) "Hcg Hpc Hity".
    iEval (rgne; rewrite Hils1) in "Hity".
    iDestruct ("Hmback" with "[Hity]") as "Hmeta";
      [iEval (rewrite /i_type); iExact "Hity" |].
    iDestruct ("Hlback" with "Hmeta") as "Hload".
    set (Q1 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (di_type dn : mword 16) : mword 64)]> mil).
    assert (HQ1a4 : (Q1 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /Q1; apply upd_eq).
    assert (Hppec : add_vec_int (mword_of_int (SO + 0xec) : mword 64) 4
                    = mword_of_int (SO + 0xf0)) by pcw.
    iEval (rewrite Hppec) in "Hpc".
    (* ===== +0xf0 c.li a5,1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID8) (mword_of_int (SO + 0xf0)) Ra5
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              Q1 (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (soi_0f0 with "Htext"). }
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (Q2 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> Q1).
    assert (HQ2a4 : (Q2 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /Q2 upd_ne; [exact HQ1a4 | nz]).
    assert (HQ2a5 : (Q2 !!! Regidx Ra5 : mword 64) = (mword_of_int 1 : mword 64))
      by (rewrite /Q2; apply upd_eq).
    assert (HQ2sp : so_sp sp0 Q2).
    { rewrite /so_sp /Q2 upd_ne; [| nz]. rewrite /Q1 upd_ne; [| nz].
      exact Hilsp. }
    assert (HQ2s0 : (Q2 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite /Q2 upd_ne; [| nz]. rewrite /Q1 upd_ne; [| nz]. exact Hils0. }
    assert (HQ2s1 : (Q2 !!! Regidx Rs1 : mword 64) = ientry kk).
    { rewrite /Q2 upd_ne; [| nz]. rewrite /Q1 upd_ne; [| nz]. exact Hils1. }
    assert (HQ2s2 : (Q2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /Q2 upd_ne; [| nz]. rewrite /Q1 upd_ne; [| nz]. exact Hils2. }
    assert (HQ2s3 : (Q2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /Q2 upd_ne; [| nz]. rewrite /Q1 upd_ne; [| nz]. exact Hils3. }
    assert (HQ2thr : so_thr m Q2).
    { intros c Hc N2b N8 N9 N18 N19.
      rewrite /Q2 upd_ne; [| regne]. rewrite /Q1 upd_ne; [| regne].
      exact (Hilthr c Hc N2b N8 N9 N18 N19). }
    assert (Hppf0 : add_vec_int (mword_of_int (SO + 0xf0) : mword 64) 2
                    = mword_of_int (SO + 0xf2)) by pcw.
    iEval (rewrite Hppf0) in "Hpc".
    (* ===== +0xf2 bne a4,a5, +0x4a  -- the JOIN ===== *)
    destruct (decide (di_type dn = (mword_of_int 1 : mword 16))) as [Hty | Hty].
    2:{ (* ---- NOT a directory: straight to the join at +0x4a ---- *)
      iApply (wp_bne_taken_s_sconf (CID := CID9) (mword_of_int (SO + 0xf2))
                (mword_of_int 8024 : mword 13) Ra5 Ra4 Q2 (K - 24)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HQ2a4 HQ2a5;
                      exact (so_neq_of_ne _ _
                               (so_ty_ne (di_type dn) 1 so_tdir_range Hty)))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_0f2 with "Htext"). }
      iIntros (CID10 Hq10). iNext. iIntros "Hcg Hpc".
      assert (Htgf2 : add_vec (mword_of_int (SO + 0xf2) : mword 64)
                        (sign_extend' 64 (mword_of_int 8024 : mword 13))
                      = mword_of_int (SO + 0x4a)) by pcw.
      iEval (rewrite Htgf2) in "Hpc".
      assert (Hdirw : bv_unsigned (di_type dn) = T_DIR_z ->
                      om = (mword_of_int 0 : mword 32)).
      { intro Hc. exfalso. exact (so_tdir_zne (di_type dn) Hty Hc). }
      iDestruct (log_opS_op with "HopS") as "Hop".
      iDestruct (cpu_own_transport CID7 CID10 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      (* THE ADAPTER, the else arm's copy: the iref interval widens from
         the join's [nsj <= ns' <= S nsj] to the syscall's, namei having
         spent one of the three. *)
      iAssert (wp_next true (proc_addr jx)
                 (so_cont gf bn gfs cov logstart bmapstart inodestart size
                          (ns - 1)%nat dqb dqs (proc_addr jx) pidv V m K eb b lks))
        with "[Hcont Hsbn Hsbs]" as "Hcontj".
      { iEval (rewrite /wp_next). iIntros (CIDz) "%Hqz".
        iEval (rewrite /so_cont). iIntros (mf ns2) "%Hcsf %Hns2".
        iIntros "Hcg Hown Htce Hcce Hpc Hsbb Hsbi Hbsl Hisl Hpost".
        iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf ns2 with "[%] [%] Hcg Hown Htce Hcce Hpc
                  Hsbn Hsbi Hsbs Hsbb Hbsl Hisl Hpost").
        { exact Hcsf. }
        { unfold sys_open_slots, create_slots in *. lia. } }
      iApply (so_join (CID0 := CID10) gfl gf gs jx gl gu gd gk pd pav pu bn g
                gfs gi cn gtl gil gisl cov logstart bmapstart inodestart nib
                size dev kk (qq/2)%Qp (qq/2)%Qp gy inum dn bm om lo
                (ns - 1)%nat n1 pidv dqb dqs V m Q2 sp0 K eb b lks w4 w5 w6 w24
                bp1
                HKfull Hkk Hdevc Hnibc Hinb Hgeom Hsize Hbm0 Hbmcov Hbmlog
                Hist0 Hiblk Hiblog Hcovb Hiu Hj Hgl Hlkempty Hdirw
                Hal23 Hsp0 HQ2sp HQ2thr HQ2s0 HQ2s1 HQ2s2 HQ2s3 Hal ltac:(unfold sys_open_slots, create_slots in *; lia)
                with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hftab Hbio Hlog
                      Hseam Hgen Hitab Hitinv Hesck Hireg Hropen Hslkk Hslkd
                      Hdep Hidev Hiinum Hivalid Hload Hshot Hfrz Hkeep Hru Hpriv Hprocs
                      Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres Hbsl Hisl Hfds Hf1
                      Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23lo H23hi H24 Hcontj").
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. } }
    (* ---- IT IS A DIRECTORY: the omode test decides ---- *)
    iApply (wp_bne_fall_s_sconf (CID := CID9) (mword_of_int (SO + 0xf2))
              (mword_of_int 8024 : mword 13) Ra5 Ra4 Q2 (K - 24)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HQ2a4 HQ2a5;
                    exact (so_neq_of_eq _ _
                             (so_ty_eq (di_type dn) 1 so_tdir_range Hty)))
              with "Hcg Hpc []").
    { iApply (soi_0f2 with "Htext"). }
    iIntros (CID10 Hq10) "Hcg Hpc".
    assert (Hppf2 : add_vec_int (mword_of_int (SO + 0xf2) : mword 64) 4
                    = mword_of_int (SO + 0xf6)) by pcw.
    iEval (rewrite Hppf2) in "Hpc".
    (* ===== +0xf6 lw a5,-180(s0) -- the omode word ===== *)
    iApply (wp_lw_s_sconf (CID := CID10) (mword_of_int (SO + 0xf6)) Ra5 Rs0
              (mword_of_int 3916 : mword 12) Q2 (K - 24)%nat om b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [H23hi]").
    { iApply (soi_0f6 with "Htext"). }
    { iEval (rgne; rewrite HQ2s0; rewrite so_omode). iExact "H23hi". }
    iIntros (CID11 Hq11) "Hcg Hpc H23hi".
    iEval (rgne; rewrite HQ2s0; rewrite so_omode) in "H23hi".
    set (Q3 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 om : mword 64)]> Q2).
    assert (HQ3a5 : (Q3 !!! Regidx Ra5 : mword 64) = so_omv om)
      by (rewrite /Q3 /so_omv; apply upd_eq).
    assert (HQ3sp : so_sp sp0 Q3)
      by (rewrite /so_sp /Q3 upd_ne; [exact HQ2sp | nz]).
    assert (HQ3s0 : (Q3 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /Q3 upd_ne; [exact HQ2s0 | nz]).
    assert (HQ3s1 : (Q3 !!! Regidx Rs1 : mword 64) = ientry kk)
      by (rewrite /Q3 upd_ne; [exact HQ2s1 | nz]).
    assert (HQ3s2 : (Q3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /Q3 upd_ne; [exact HQ2s2 | nz]).
    assert (HQ3s3 : (Q3 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /Q3 upd_ne; [exact HQ2s3 | nz]).
    assert (HQ3thr : so_thr m Q3).
    { intros c Hc N2b N8 N9 N18 N19. rewrite /Q3 upd_ne; [| regne].
      exact (HQ2thr c Hc N2b N8 N9 N18 N19). }
    assert (Hppf6 : add_vec_int (mword_of_int (SO + 0xf6) : mword 64) 4
                    = mword_of_int (SO + 0xfa)) by pcw.
    iEval (rewrite Hppf6) in "Hpc".
    (* ===== +0xfa c.beqz a5, +0x5e -- NOT the join: [so_alloc] ===== *)
    destruct (decide (om = (mword_of_int 0 : mword 32))) as [Hom0 | Homnz].
    { (* ---- O_RDONLY on a directory: the T_DEVICE test is SKIPPED ---- *)
      iApply (wp_cbeqz_taken_s_sconf (CID := CID11) (mword_of_int (SO + 0xfa))
                (mword_of_int 178 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                Q3 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HQ3a5 Hom0;
                      apply (proj2 (eq_vec_true_iff _ _)); exact so_omv_zero)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_0fa with "Htext"). }
      iIntros (CID12 Hq12). iNext. iIntros "Hcg Hpc".
      assert (Htgfa : add_vec (mword_of_int (SO + 0xfa) : mword 64)
                        (sign_extend' 64
                           (sign_extend' 13 (concat_vec (mword_of_int 178 : mword 8) ('b"0"))))
                      = mword_of_int (SO + 0x5e)) by pcw.
      iEval (rewrite Htgfa) in "Hpc".
      iDestruct (log_opS_op with "HopS") as "Hop".
      iDestruct (cpu_own_transport CID7 CID12 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iAssert (wp_next true (proc_addr jx)
                 (so_cont gf bn gfs cov logstart bmapstart inodestart size
                          (ns - 1)%nat dqb dqs (proc_addr jx) pidv V m K eb b lks))
        with "[Hcont Hsbn Hsbs]" as "Hcontj".
      { iEval (rewrite /wp_next). iIntros (CIDz) "%Hqz".
        iEval (rewrite /so_cont). iIntros (mf ns2) "%Hcsf %Hns2".
        iIntros "Hcg Hown Htce Hcce Hpc Hsbb Hsbi Hbsl Hisl Hpost".
        iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf ns2 with "[%] [%] Hcg Hown Htce Hcce Hpc
                  Hsbn Hsbi Hsbs Hsbb Hbsl Hisl Hpost").
        { exact Hcsf. }
        { unfold sys_open_slots, create_slots in *. lia. } }
      iApply (so_alloc (CID0 := CID12) gfl gf gs jx gl gu gd gk pd pav pu bn g
                gfs gi cn gtl gil gisl cov logstart bmapstart inodestart nib
                size dev kk (qq/2)%Qp (qq/2)%Qp gy inum dn bm om lo
                (ns - 1)%nat n1 pidv dqb dqs V m Q3 sp0 K eb b lks w4 w5 w6 w24
                bp1
                HKfull Hkk Hdevc Hnibc Hinb Hgeom Hsize Hbm0 Hbmcov Hbmlog
                Hist0 Hiblk Hiblog Hcovb Hiu Hj Hgl Hlkempty
                ltac:(intros _; exact Hom0)
                Hal23 Hsp0 HQ3sp HQ3thr HQ3s0 HQ3s1 HQ3s2 HQ3s3 Hal ltac:(unfold sys_open_slots, create_slots in *; lia)
                with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hftab Hbio Hlog
                      Hseam Hgen Hitab Hitinv Hesck Hireg Hropen Hslkk Hslkd
                      Hdep Hidev Hiinum Hivalid Hload Hshot Hfrz Hkeep Hru Hpriv Hprocs
                      Hdev Hgeo Hdlk Hop Hsbb Hsbi Hbmres Hbsl Hisl Hfds Hf1
                      Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23lo H23hi H24 Hcontj").
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. } }
    (* ---- a directory opened for writing: ARM C-FAIL at +0xfc ---- *)
    iApply (wp_cbeqz_fall_s_sconf (CID := CID11) (mword_of_int (SO + 0xfa))
              (mword_of_int 178 : mword 8) (Cregidx (mword_of_int 7)) Ra5
              Q3 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HQ3a5;
                    apply (proj2 (eq_vec_false_iff _ _)); intro Hc;
                    apply Homnz; apply so_omode_eqz;
                    apply (proj2 (eq_vec_true_iff _ _)); exact Hc)
              with "Hcg Hpc []").
    { iApply (soi_0fa with "Htext"). }
    iIntros (CID12 Hq12) "Hcg Hpc".
    assert (Hppfa : add_vec_int (mword_of_int (SO + 0xfa) : mword 64) 2
                    = mword_of_int (SO + 0xfc)) by pcw.
    iEval (rewrite Hppfa) in "Hpc".
    iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeepe".
    iDestruct (proc_priv_bare_acc with "Hpriv") as "[Hpbare Hpback2]".
    iDestruct (so_omode_join sp0 lo om Hal23 with "H23lo H23hi") as "H23".
    iDestruct (log_opS_op with "HopS") as "Hop".
    iDestruct (cpu_own_transport CID7 CID12 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Tails.so_tail_c (CID0 := CID12) gs jx gl gu gd gk pd pav pu bn g
              gfs gi cn gtl gil gisl cov logstart bmapstart inodestart nib
              size dev kk (qq/2)%Qp (qq/2)%Qp gy inum dn bm n1 pidv
              (DfracOwn (1/4)) dqb dqs m Q3 sp0 K eb b lks w4 w5 w6
              (word_of_words lo om) w24 bp1 V
              HKup HKeo HK24 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
              Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HQ3sp HQ3thr
              HQ3s1 HQ3s2 HQ3s3 Hal
              with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlog Hseam Hgen Hitab
                    Hitinv Hesck Hireg Hropen Hslkk Hslkd Hdep Hidev Hiinum
                    Hivalid Hload Hshot Hfrz Hkeepe Hru Hsbb Hsbi Hbmres Hpbare Hprocs
                    Hdev Hgeo Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbP H23
                    H24 [Hpback2 Hfds Hisl Hsbn Hsbs Hcont]").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf)
      "%Hcsf %Ha0f Hcg Hown Htce Hcce Hpc Hpbare Hsbb Hsbi Hbsl
       Hislot".
    iDestruct ("Hpback2" with "Hpbare") as "Hpriv".
    iEval (rewrite /iref_slot) in "Hislot".
    iDestruct (iref_slots_combine 1 (ns - 1) with "Hislot Hisl") as "Hisl".
    assert (Hnsc : (1 + (ns - 1))%nat = ns) by lia.
    iEval (rewrite Hnsc) in "Hisl".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf ns with "[%] [%] Hcg Hown Htce Hcce Hpc
              Hsbn Hsbi Hsbs Hsbb Hbsl Hisl [Hpriv Hfds]").
    { exact Hcsf. }
    { unfold sys_open_slots, create_slots in *. lia. }
    { rewrite /sys_open_post. iSplitR "Hfds"; [| iExact "Hfds"].
      iLeft. iSplitR; [iPureIntro; exact Ha0f | iExact "Hpriv"]. }
  Qed.

  (* ================================================================== *)
  (*  +0x00 .. +0x36 : THE ENTRY, ARM 0, AND THE O_CREATE SPLIT --       *)
  (*  AND THE SEAL.                                                     *)
  (*                                                                    *)
  (*    c.addi16sp sp,-192 ; c.sdsp ra,184 ; c.sdsp s0,176 ;             *)
  (*    c.addi4spn s0,sp,192                                            *)
  (*    addi a1,s0,-180 ; c.li a0,1 ; jal argint                        *)
  (*    li a2,128 ; addi a1,s0,-176 ; c.li a0,0 ; jal argstr            *)
  (*    c.mv a5,a0 ; c.li a0,-1 ; bltz a5 -> +0xca      [ARM 0]         *)
  (*    c.sdsp s1,168 ; jal begin_op                                    *)
  (*    lw a5,-180(s0) ; andi a5,a5,512 ; c.beqz -> +0xdc               *)
  (*                                                                    *)
  (*  ARM 0 IS NOT A TAIL.  a0 was set to -1 at +0x22 BEFORE the branch, *)
  (*  so the [bltz] targets the epilogue directly and the arm is         *)
  (*  [so_epilogue] applied here -- no block of its own, and no          *)
  (*  transaction either: it branches ABOVE begin_op.                    *)
  (*                                                                    *)
  (*  THE OMODE SLOT IS SPLIT HERE, and this is the ONE four-byte view   *)
  (*  of a frame slot sys_open needs: argint's destination is the UPPER  *)
  (*  word of slot 23 ([s0-180]), the lower word being the [int fd] gcc  *)
  (*  never spilled, which rides through arbitrary and is rejoined at    *)
  (*  every exit.  [Hal23] -- the split's own alignment side condition,  *)
  (*  which slot 23 is outside [so_al]'s range for -- comes off the      *)
  (*  carve's points-to itself, [word_pointsto_aligned_p].               *)
  (*                                                                    *)
  (*  THE SHRINK-WRAPPED s1 SAVE IS WHAT MAKES THE CARVE ARM-DEPENDENT:  *)
  (*  [c.sdsp s1,168] is BELOW ARM 0's branch, so ARM 0 leaves slot 3    *)
  (*  holding the carve's junk while every block past +0x28 has the      *)
  (*  entry value of s1 in it.                                          *)
  (*                                                                    *)
  (*  AND THE SPLIT AT +0x36 NEEDS NOTHING SEMANTIC.  Both blocks below  *)
  (*  take [omode] opaquely -- the O_CREATE arm never reads it again and *)
  (*  the else arm's own [c.beqz] is what decides it -- so the branch is *)
  (*  an ordinary [destruct] on the mask's [eq_vec] and no bit lemma is  *)
  (*  spent here.                                                       *)
  (* ================================================================== *)
  Lemma wp_sys_open_sconf `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gfl gf ga gpr : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (ninodes : Z) (size : Z) (dev : mword 32)
      (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v vom : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
    wp_sys_open_sconf_body gfl gf ga gpr gs j gl gu gd gk pd pav pu bn g gfs
                           gi cn gtl cov logstart bmapstart inodestart nib
                           ninodes size dev ns dqb dqs dqbs dqn v vom
                           pid V m K eb b lks.
  Proof.
    cbv beta zeta delta [wp_sys_open_sconf_body].
    intros HK Hdevc Hnibc Hlogc Histc HdevR Hnib0 Hgeom Hsize
           Hbm0 Hbmcov Hbmlog Hist0 Hcovb Hbmgeo Hiregb Hni1 Hni2 Hni3 Hush
           Hprkc Hnsb Hj Hgl Heb Hargv Hargvom.
    pose proof HK as HKfull.
    destruct (so_kb K HK) as (HKcr & HKna & HKai & HKas & HKbo & HKeo & HKil &
                              HKiu & HKit & HKip & HKup & HKfc & HKfa & HKfd &
                              HK10 & HK24 & Kpop).
    set (sp0 := m !!! Regidx csp_rs1).
    iIntros "Hcg Hown _ _ #Htext #Hdata Hpc #Hpre #Hftab #Hbio #Hlog
             Hseam Hgen #Hdev #Hgeo #Hdlk Hbsl #Hitab #Hitinv #Hescrows #Hslks
             #Hireg #Hropen Hsbn Hsbi Hsbs Hsbb #Hbmres #Hkenv #Hprocs Hisl
             Hfds Hpriv Hcont".
    iPoseProof (printk_env_panic with "Hpre") as "#Hpe".
    iDestruct (cpu_own_zero_empty with "Hown") as "[%Hlkempty Hown]".
    assert (Hlb : forall r : string, locks_below lks r).
    { intro r. rewrite Hlkempty. apply locks_below_empty. }
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* ===== +0x00 c.addi16sp sp,-192 ===== *)
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int SO : mword 64)
              (mword_of_int 52 : mword 6) m K 24 b
              ltac:(lia) (so_push sp0) with "Hcg Hpc []").
    { iApply (soi_000 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec sp0 (sign_extend' 64
                     (caddi16sp_imm (mword_of_int 52 : mword 6))))]> m).
    assert (HM1sp : so_sp sp0 M1).
    { unfold so_sp. etransitivity; [ rewrite /M1; apply upd_eq | apply so_push ]. }
    assert (HM1thr : so_thr m M1).
    { intros c Hc N2 N8 N9 N18 N19.
      rewrite /M1 upd_ne; [reflexivity | congruence]. }
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s0 : (M1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s3 : (M1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (Hpp02 : add_vec_int (mword_of_int SO : mword 64) 2
                    = mword_of_int (SO + 0x02))
      by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* the carve: sixteen of the twenty-four slots ARE [char path[128]] *)
    iDestruct (so_frame_carve sp0 with "Hframe")
      as "(%Hal & [%u1 Hf1] & [%u2 Hf2] & [%u3 Hf3] & [%u4 Hf4] & [%u5 Hf5] &
           [%u6 Hf6] & Hbytes & [%u23 H23] & [%u24 H24])".
    iDestruct (ctx_word_pointsto_aligned_p with "H23") as %Hal23.
    iDestruct (so_omode_split sp0 u23 with "H23") as "[H23lo H23hi]".
    assert (Hc1 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 23 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HM1sp; apply so_frm1).
    assert (Hc2 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 22 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HM1sp; apply so_frm2).
    (* ===== +0x02 c.sdsp ra,184(sp) ===== *)
    iEval (rewrite -Hc1) in "Hf1".
    iApply (wp_csdsp_s_sconf (mword_of_int (SO + 0x02))
              (mword_of_int 23 : mword 6) Rra M1 (K - 24)%nat u1 b
              with "Hcg Hpc [] Hf1").
    { iApply (soi_002 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    iEval (rgne; rewrite Hc1 HM1ra) in "Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (SO + 0x02) : mword 64) 2
                    = mword_of_int (SO + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    (* ===== +0x04 c.sdsp s0,176(sp) ===== *)
    iEval (rewrite -Hc2) in "Hf2".
    iApply (wp_csdsp_s_sconf (mword_of_int (SO + 0x04))
              (mword_of_int 22 : mword 6) Rs0 M1 (K - 24)%nat u2 b
              with "Hcg Hpc [] Hf2").
    { iApply (soi_004 with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    iEval (rgne; rewrite Hc2 HM1s0) in "Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (SO + 0x04) : mword 64) 2
                    = mword_of_int (SO + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    (* ===== +0x06 c.addi4spn s0,sp,192 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (SO + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 48 : mword 8) Rs0
              M1 (K - 24)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (soi_006 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 48 : mword 8))))]> M1).
    assert (HM2s0 : (M2 !!! Regidx Rs0 : mword 64) = sp0).
    { etransitivity; [ rewrite /M2; apply upd_eq |].
      rewrite HM1sp. apply so_fp. }
    assert (HM2sp : so_sp sp0 M2)
      by (rewrite /so_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2s1 : (M2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s1 | nz]).
    assert (HM2s2 : (M2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s2 | nz]).
    assert (HM2s3 : (M2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s3 | nz]).
    assert (HM2thr : so_thr m M2).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp08 : add_vec_int (mword_of_int (SO + 0x06) : mword 64) 2
                    = mword_of_int (SO + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    (* ===== +0x08 addi a1,s0,-180 -- &omode ===== *)
    iApply (wp_addi4_s_sconf (CID := CID4) (mword_of_int (SO + 0x08)) Ra1 Rs0
              (mword_of_int 3916 : mword 12) M2 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_008 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (M3 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (M2 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3916 : mword 12)))]> M2).
    assert (HM3a1 : (M3 !!! Regidx Ra1 : mword 64) = pa_add (pa_stk sp0 23) 4).
    { etransitivity; [ rewrite /M3; apply upd_eq |].
      rewrite HM2s0. apply so_omode. }
    assert (HM3sp : so_sp sp0 M3)
      by (rewrite /so_sp /M3 upd_ne; [exact HM2sp | nz]).
    assert (HM3s0 : (M3 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M3 upd_ne; [exact HM2s0 | nz]).
    assert (HM3s1 : (M3 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s1 | nz]).
    assert (HM3s2 : (M3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s2 | nz]).
    assert (HM3s3 : (M3 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s3 | nz]).
    assert (HM3thr : so_thr m M3).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M3 upd_ne; [| regne].
      exact (HM2thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp0c : add_vec_int (mword_of_int (SO + 0x08) : mword 64) 4
                    = mword_of_int (SO + 0x0c)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    (* ===== +0x0c c.li a0,1 -- syscall argument ONE ===== *)
    iApply (wp_cli_s_sconf (CID := CID5) (mword_of_int (SO + 0x0c)) Ra0
              (mword_of_int 1 : mword 6)
              (mword_of_int (Z.of_nat 1) : mword 64) M3 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (soi_00c with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (M4 := <[Regidx Ra0 := regval_into_reg
                  (mword_of_int (Z.of_nat 1) : mword 64)]> M3).
    assert (HM4a0 : (M4 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 1) : mword 64))
      by (rewrite /M4; apply upd_eq).
    assert (HM4a1 : (M4 !!! Regidx Ra1 : mword 64) = pa_add (pa_stk sp0 23) 4)
      by (rewrite /M4 upd_ne; [exact HM3a1 | nz]).
    assert (HM4sp : so_sp sp0 M4)
      by (rewrite /so_sp /M4 upd_ne; [exact HM3sp | nz]).
    assert (HM4s0 : (M4 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M4 upd_ne; [exact HM3s0 | nz]).
    assert (HM4s1 : (M4 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3s1 | nz]).
    assert (HM4s2 : (M4 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3s2 | nz]).
    assert (HM4s3 : (M4 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3s3 | nz]).
    assert (HM4thr : so_thr m M4).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M4 upd_ne; [| regne].
      exact (HM3thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp0e : add_vec_int (mword_of_int (SO + 0x0c) : mword 64) 2
                    = mword_of_int (SO + 0x0e)) by pcw.
    iEval (rewrite Hpp0e) in "Hpc".
    (* ===== +0x0e jal ra,argint ===== *)
    iApply (wp_jal_s_sconf (CID := CID6) (mword_of_int (SO + 0x0e)) Rra
              (mword_of_int 2086660 : mword 21) M4 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_00e with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (M5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x0e) : mword 64) 4)]> M4).
    assert (Hjai : add_vec (mword_of_int (SO + 0x0e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2086660 : mword 21))
                   = mword_of_int KernelSyms.argint) by pcw.
    iEval (rewrite Hjai) in "Hpc".
    assert (HM5ra : (M5 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x0e) : mword 64) 4)
      by (rewrite /M5; apply upd_eq).
    assert (HM5a0 : (M5 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 1) : mword 64))
      by (rewrite /M5 upd_ne; [exact HM4a0 | nz]).
    assert (HM5a1 : (M5 !!! Regidx Ra1 : mword 64) = pa_add (pa_stk sp0 23) 4)
      by (rewrite /M5 upd_ne; [exact HM4a1 | nz]).
    assert (HM5sp : so_sp sp0 M5)
      by (rewrite /so_sp /M5 upd_ne; [exact HM4sp | nz]).
    assert (HM5s0 : (M5 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M5 upd_ne; [exact HM4s0 | nz]).
    assert (HM5s1 : (M5 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M5 upd_ne; [exact HM4s1 | nz]).
    assert (HM5s2 : (M5 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M5 upd_ne; [exact HM4s2 | nz]).
    assert (HM5s3 : (M5 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M5 upd_ne; [exact HM4s3 | nz]).
    assert (HM5thr : so_thr m M5).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M5 upd_ne; [| regne].
      exact (HM4thr c Hc N2 N8 N9 N18 N19). }
    (* ===== argint(1, &omode) ===== *)
    iDestruct (proc_priv_tfp_valid with "Hpriv") as %Hpv.
    iDestruct (proc_priv_tf gf (proc_addr j) pid V with "Hpriv") as "(Htf & Hpage & Hback)".
    iEval (rewrite -HM5a1) in "H23hi".
    iDestruct (cpu_own_transport CID0 CID7 0 eb (proc_addr j) b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Argint.wp_argint_sconf M5 (K - 24)%nat 0%nat eb (proc_addr j) 1%nat
              (ud_tfp (pv_upt V)) (pv_tf V) vom (word_hi u23) (DfracOwn (1/4))
              b lks so_arg1_lt HM5a0 Hargvom so_noff0 HKai Hpv
              with "Hcg Hown Htext Hdata Hpc Htf Hpage H23hi").
    iIntros (CID8 Hq8 mai) "%Hcsai Hcg Hown Hpc Htf Hpage H23hi".
    iEval (rewrite HM5a1) in "H23hi".
    iDestruct ("Hback" with "Htf Hpage") as "Hpriv".
    assert (Hpc12 : ret_pc (M5 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0x12)) by (rewrite HM5ra; pcw).
    iEval (rewrite Hpc12) in "Hpc".
    assert (Haisp : so_sp sp0 mai).
    { rewrite /so_sp (callee_saved_lookup Hcsai csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM5sp. }
    assert (Hais0 : (mai !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsai Rs0 ltac:(vm_compute; reflexivity)).
      exact HM5s0. }
    assert (Hais1 : (mai !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64)).
    { rewrite (callee_saved_lookup Hcsai Rs1 ltac:(vm_compute; reflexivity)).
      exact HM5s1. }
    assert (Hais2 : (mai !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcsai Rs2 ltac:(vm_compute; reflexivity)).
      exact HM5s2. }
    assert (Hais3 : (mai !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcsai Rs3 ltac:(vm_compute; reflexivity)).
      exact HM5s3. }
    assert (Haithr : so_thr m mai).
    { intros c Hc N2 N8 N9 N18 N19. rewrite (callee_saved_lookup Hcsai c Hc).
      exact (HM5thr c Hc N2 N8 N9 N18 N19). }
    (* ===== +0x12 li a2,128 ===== *)
    iApply (wp_li4_s_sconf (CID := CID8) (mword_of_int (SO + 0x12)) Ra2
              (mword_of_int 128 : mword 12)
              (mword_of_int (Z.of_nat 128) : mword 64) mai (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (soi_012 with "Htext"). }
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (M6 := <[Regidx Ra2 := regval_into_reg
                  (mword_of_int (Z.of_nat 128) : mword 64)]> mai).
    assert (HM6a2 : (M6 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M6; apply upd_eq).
    assert (HM6sp : so_sp sp0 M6)
      by (rewrite /so_sp /M6 upd_ne; [exact Haisp | nz]).
    assert (HM6s0 : (M6 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M6 upd_ne; [exact Hais0 | nz]).
    assert (HM6s1 : (M6 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M6 upd_ne; [exact Hais1 | nz]).
    assert (HM6s2 : (M6 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M6 upd_ne; [exact Hais2 | nz]).
    assert (HM6s3 : (M6 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M6 upd_ne; [exact Hais3 | nz]).
    assert (HM6thr : so_thr m M6).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M6 upd_ne; [| regne].
      exact (Haithr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp16 : add_vec_int (mword_of_int (SO + 0x12) : mword 64) 4
                    = mword_of_int (SO + 0x16)) by pcw.
    iEval (rewrite Hpp16) in "Hpc".
    (* ===== +0x16 addi a1,s0,-176 -- the path buffer ===== *)
    iApply (wp_addi4_s_sconf (CID := CID9) (mword_of_int (SO + 0x16)) Ra1 Rs0
              (mword_of_int 3920 : mword 12) M6 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_016 with "Htext"). }
    iIntros (CID10 Hq10) "Hcg Hpc".
    set (M7 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (M6 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3920 : mword 12)))]> M6).
    assert (HM7a1 : (M7 !!! Regidx Ra1 : mword 64) = pa_stk sp0 22).
    { etransitivity; [ rewrite /M7; apply upd_eq |].
      rewrite HM6s0. apply so_bufpath. }
    assert (HM7a2 : (M7 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M7 upd_ne; [exact HM6a2 | nz]).
    assert (HM7sp : so_sp sp0 M7)
      by (rewrite /so_sp /M7 upd_ne; [exact HM6sp | nz]).
    assert (HM7s0 : (M7 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M7 upd_ne; [exact HM6s0 | nz]).
    assert (HM7s1 : (M7 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M7 upd_ne; [exact HM6s1 | nz]).
    assert (HM7s2 : (M7 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M7 upd_ne; [exact HM6s2 | nz]).
    assert (HM7s3 : (M7 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M7 upd_ne; [exact HM6s3 | nz]).
    assert (HM7thr : so_thr m M7).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M7 upd_ne; [| regne].
      exact (HM6thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp1a : add_vec_int (mword_of_int (SO + 0x16) : mword 64) 4
                    = mword_of_int (SO + 0x1a)) by pcw.
    iEval (rewrite Hpp1a) in "Hpc".
    (* ===== +0x1a c.li a0,0 -- syscall argument ZERO ===== *)
    iApply (wp_cli_s_sconf (CID := CID10) (mword_of_int (SO + 0x1a)) Ra0
              (mword_of_int 0 : mword 6)
              (mword_of_int (Z.of_nat 0) : mword 64) M7 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (soi_01a with "Htext"). }
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (M8 := <[Regidx Ra0 := regval_into_reg
                  (mword_of_int (Z.of_nat 0) : mword 64)]> M7).
    assert (HM8a0 : (M8 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 0) : mword 64))
      by (rewrite /M8; apply upd_eq).
    assert (HM8a1 : (M8 !!! Regidx Ra1 : mword 64) = pa_stk sp0 22)
      by (rewrite /M8 upd_ne; [exact HM7a1 | nz]).
    assert (HM8a2 : (M8 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M8 upd_ne; [exact HM7a2 | nz]).
    assert (HM8sp : so_sp sp0 M8)
      by (rewrite /so_sp /M8 upd_ne; [exact HM7sp | nz]).
    assert (HM8s0 : (M8 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M8 upd_ne; [exact HM7s0 | nz]).
    assert (HM8s1 : (M8 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M8 upd_ne; [exact HM7s1 | nz]).
    assert (HM8s2 : (M8 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M8 upd_ne; [exact HM7s2 | nz]).
    assert (HM8s3 : (M8 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M8 upd_ne; [exact HM7s3 | nz]).
    assert (HM8thr : so_thr m M8).
    { intros c Hc N2 N8b N9 N18 N19. rewrite /M8 upd_ne; [| regne].
      exact (HM7thr c Hc N2 N8b N9 N18 N19). }
    assert (Hpp1c : add_vec_int (mword_of_int (SO + 0x1a) : mword 64) 2
                    = mword_of_int (SO + 0x1c)) by pcw.
    iEval (rewrite Hpp1c) in "Hpc".
    (* ===== +0x1c jal ra,argstr ===== *)
    iApply (wp_jal_s_sconf (CID := CID11) (mword_of_int (SO + 0x1c)) Rra
              (mword_of_int 2086702 : mword 21) M8 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_01c with "Htext"). }
    iIntros (CID12 Hq12) "Hcg Hpc".
    set (M9 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x1c) : mword 64) 4)]> M8).
    assert (Hjas : add_vec (mword_of_int (SO + 0x1c) : mword 64)
                     (sign_extend' 64 (mword_of_int 2086702 : mword 21))
                   = mword_of_int KernelSyms.argstr) by pcw.
    iEval (rewrite Hjas) in "Hpc".
    assert (HM9ra : (M9 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x1c) : mword 64) 4)
      by (rewrite /M9; apply upd_eq).
    assert (HM9a0 : (M9 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 0) : mword 64))
      by (rewrite /M9 upd_ne; [exact HM8a0 | nz]).
    assert (HM9a1 : (M9 !!! Regidx Ra1 : mword 64) = pa_stk sp0 22)
      by (rewrite /M9 upd_ne; [exact HM8a1 | nz]).
    assert (HM9a2 : (M9 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M9 upd_ne; [exact HM8a2 | nz]).
    assert (HM9sp : so_sp sp0 M9)
      by (rewrite /so_sp /M9 upd_ne; [exact HM8sp | nz]).
    assert (HM9s0 : (M9 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M9 upd_ne; [exact HM8s0 | nz]).
    assert (HM9s1 : (M9 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M9 upd_ne; [exact HM8s1 | nz]).
    assert (HM9s2 : (M9 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M9 upd_ne; [exact HM8s2 | nz]).
    assert (HM9s3 : (M9 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M9 upd_ne; [exact HM8s3 | nz]).
    assert (HM9thr : so_thr m M9).
    { intros c Hc N2 N8b N9 N18 N19. rewrite /M9 upd_ne; [| regne].
      exact (HM8thr c Hc N2 N8b N9 N18 N19). }
    (* ===== argstr(0, path, MAXPATH) ===== *)
    iDestruct (so_bytes_name (pa_stk sp0 22) 128 with "Hbytes") as (bf0) "Hbuf".
    iDestruct (cpu_own_transport CID8 CID12 0 eb (proc_addr j) b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Argstr.wp_argstr_sconf (CID := CID12) ga gf M9 (K - 24)%nat 0%nat
              eb (proc_addr j) 0%nat v pid V 128%nat bf0 b lks
              so_arg0_lt HM9a0 Hargv so_noff0 HKas HM9a2 so_maxpath_lt
              (Hlb "kmem"%string)
              with "Hcg Hown Htext Hdata Hpc Hpriv Hkenv [Hbuf]").
    { iEval (rewrite HM9a1). iExact "Hbuf". }
    iIntros (CID13 Hq13 mas P' bf) "%Hcsas %Hupt Hcg Hown Hpc Hpriv Hbuf %Hfsr".
    iEval (rewrite HM9a1) in "Hbuf".
    assert (Hpc20 : ret_pc (M9 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0x20)) by (rewrite HM9ra; pcw).
    iEval (rewrite Hpc20) in "Hpc".
    assert (Hassp : so_sp sp0 mas).
    { rewrite /so_sp (callee_saved_lookup Hcsas csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM9sp. }
    assert (Hass0 : (mas !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsas Rs0 ltac:(vm_compute; reflexivity)).
      exact HM9s0. }
    assert (Hass1 : (mas !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64)).
    { rewrite (callee_saved_lookup Hcsas Rs1 ltac:(vm_compute; reflexivity)).
      exact HM9s1. }
    assert (Hass2 : (mas !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcsas Rs2 ltac:(vm_compute; reflexivity)).
      exact HM9s2. }
    assert (Hass3 : (mas !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcsas Rs3 ltac:(vm_compute; reflexivity)).
      exact HM9s3. }
    assert (Hasthr : so_thr m mas).
    { intros c Hc N2 N8b N9 N18 N19. rewrite (callee_saved_lookup Hcsas c Hc).
      exact (HM9thr c Hc N2 N8b N9 N18 N19). }
    (* ===== +0x20 c.mv a5,a0 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID13) (mword_of_int (SO + 0x20)) Ra5 Ra0
              mas (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_020 with "Htext"). }
    iIntros (CID14 Hq14) "Hcg Hpc".
    set (R1 := <[Regidx Ra5 := regval_into_reg
                  (add_vec zero_reg (mas !!! Regidx Ra0))]> mas).
    assert (HR1a5 : (R1 !!! Regidx Ra5 : mword 64) = (mas !!! Regidx Ra0 : mword 64)).
    { etransitivity; [ rewrite /R1; apply upd_eq |]. apply add_vec_zero_l. }
    assert (Hpp22 : add_vec_int (mword_of_int (SO + 0x20) : mword 64) 2
                    = mword_of_int (SO + 0x22)) by pcw.
    iEval (rewrite Hpp22) in "Hpc".
    (* ===== +0x22 c.li a0,-1 -- BEFORE the branch: ARM 0's return value ===== *)
    iApply (wp_cli_s_sconf (CID := CID14) (mword_of_int (SO + 0x22)) Ra0
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              R1 (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (soi_022 with "Htext"). }
    iIntros (CID15 Hq15) "Hcg Hpc".
    set (R2 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> R1).
    assert (HR2a0 : (R2 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /R2; apply upd_eq).
    assert (HR2a5 : (R2 !!! Regidx Ra5 : mword 64) = (mas !!! Regidx Ra0 : mword 64))
      by (rewrite /R2 upd_ne; [exact HR1a5 | nz]).
    assert (HR2sp : so_sp sp0 R2).
    { rewrite /so_sp /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz].
      exact Hassp. }
    assert (HR2s0 : (R2 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz]. exact Hass0. }
    assert (HR2s1 : (R2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz]. exact Hass1. }
    assert (HR2s2 : (R2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz]. exact Hass2. }
    assert (HR2s3 : (R2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz]. exact Hass3. }
    assert (HR2thr : so_thr m R2).
    { intros c Hc N2 N8b N9 N18 N19.
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [| regne].
      exact (Hasthr c Hc N2 N8b N9 N18 N19). }
    assert (Hpp24 : add_vec_int (mword_of_int (SO + 0x22) : mword 64) 2
                    = mword_of_int (SO + 0x24)) by pcw.
    iEval (rewrite Hpp24) in "Hpc".
    (* ===== +0x24 bltz a5, +0xca  [ARM 0] ===== *)
    destruct Hfsr as [(pk & Hpk & Hpcstr & Hpr) | Hpr].
    2:{ (* ---- ARM 0: the string did not fetch.  No begin_op, no s1 save ---- *)
      iApply (wp_blt_x0_taken_s_sconf (CID := CID15) (mword_of_int (SO + 0x24))
                (mword_of_int 166 : mword 13) Ra5 R2 (K - 24)%nat b
                ltac:(nz) ltac:(rgne; rewrite HR2a5 Hpr; exact so_m1_neg)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (soi_024 with "Htext"). }
      iApply bi.later_intro. iIntros (CID16 Hq16) "Hcg Hpc".
      assert (Htg24 : add_vec (mword_of_int (SO + 0x24) : mword 64)
                        (sign_extend' 64 (mword_of_int 166 : mword 13))
                      = mword_of_int (SO + 0xca)) by pcw.
      iEval (rewrite Htg24) in "Hpc".
      iDestruct (so_omode_join sp0 (word_lo u23) (arg_int32 vom) Hal23
                   with "H23lo H23hi") as "H23".
      iDestruct (cpu_own_transport CID13 CID16 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID16)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (so_epilogue (CID0 := CID16) m R2 sp0 K b (proc_addr j) u3 u4 u5 u6
                (word_of_words (word_lo u23) (arg_int32 vom)) u24 bf
                HK24 Kpop ltac:(reflexivity) HR2sp HR2thr HR2s1 HR2s2 HR2s3 Hal
                with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hbuf H23 H24
                      [Hown Hpriv Hisl Hfds Hbsl Hsbn Hsbi Hsbs Hsbb
                       Hcont]").
      iEval (rewrite /wp_next).
      iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
      iDestruct (cpu_own_transport CID16 CIDy 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf ns P' with "[%] [%] Hcg Hown [] [] Hpc Hbsl
                Hsbn Hsbi Hsbs Hsbb [%] Hisl [Hpriv Hfds]").
      { exact Hcsf. }
      { exact Hupt. }
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      { split; lia. }
      { rewrite /sys_open_post. iSplitR "Hfds"; [| iExact "Hfds"].
        iLeft. iSplitR; [| iExact "Hpriv"]. iPureIntro.
        rewrite Ha0f. exact HR2a0. } }
    (* ---- the string fetched: the [bltz] falls through ---- *)
    iApply (wp_blt_x0_fall_s_sconf (CID := CID15) (mword_of_int (SO + 0x24))
              (mword_of_int 166 : mword 13) Ra5 R2 (K - 24)%nat b
              ltac:(nz)
              ltac:(rgne; rewrite HR2a5 Hpr; exact (so_nonneg _ (so_len_range pk Hpk)))
              with "Hcg Hpc []").
    { iApply (soi_024 with "Htext"). }
    iIntros (CID16 Hq16) "Hcg Hpc".
    assert (Hpp28 : add_vec_int (mword_of_int (SO + 0x24) : mword 64) 4
                    = mword_of_int (SO + 0x28)) by pcw.
    iEval (rewrite Hpp28) in "Hpc".
    (* ===== +0x28 c.sdsp s1,168(sp) -- the SHRINK-WRAPPED save ===== *)
    assert (Hc3 : add_vec (R2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 21 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HR2sp; apply so_frm3).
    iEval (rewrite -Hc3) in "Hf3".
    iApply (wp_csdsp_s_sconf (mword_of_int (SO + 0x28))
              (mword_of_int 21 : mword 6) Rs1 R2 (K - 24)%nat u3 b
              with "Hcg Hpc [] Hf3").
    { iApply (soi_028 with "Htext"). }
    iIntros (CID17 Hq17) "Hcg Hpc Hf3".
    iEval (rgne; rewrite Hc3 HR2s1) in "Hf3".
    assert (Hpp2a : add_vec_int (mword_of_int (SO + 0x28) : mword 64) 2
                    = mword_of_int (SO + 0x2a)) by pcw.
    iEval (rewrite Hpp2a) in "Hpc".
    (* ===== +0x2a jal ra,begin_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID17) (mword_of_int (SO + 0x2a)) Rra
              (mword_of_int 2091820 : mword 21) R2 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_02a with "Htext"). }
    iIntros (CID18 Hq18) "Hcg Hpc".
    set (R3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x2a) : mword 64) 4)]> R2).
    assert (Hjbo : add_vec (mword_of_int (SO + 0x2a) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091820 : mword 21))
                   = mword_of_int KernelSyms.begin_op) by pcw.
    iEval (rewrite Hjbo) in "Hpc".
    assert (HR3ra : (R3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x2a) : mword 64) 4)
      by (rewrite /R3; apply upd_eq).
    assert (HR3sp : so_sp sp0 R3)
      by (rewrite /so_sp /R3 upd_ne; [exact HR2sp | nz]).
    assert (HR3s0 : (R3 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /R3 upd_ne; [exact HR2s0 | nz]).
    assert (HR3s2 : (R3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2s2 | nz]).
    assert (HR3s3 : (R3 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2s3 | nz]).
    assert (HR3thr : so_thr m R3).
    { intros c Hc N2 N8b N9 N18 N19. rewrite /R3 upd_ne; [| regne].
      exact (HR2thr c Hc N2 N8b N9 N18 N19). }
    iDestruct (proc_priv_bare_acc gf (proc_addr j) pid (upd_upt V P') with "Hpriv")
      as "[Hpbare Hpback0]".
    iDestruct (cpu_own_transport CID13 CID18 0 eb (proc_addr j) b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (BeginOp.wp_begin_op_sconf (CID := CID18) gs j gl bn g gfs cov
              logstart dev pid (DfracOwn (1/4)) R3 (K - 24)%nat eb b lks
              (upd_upt V P') HKbo Hj Hgl (Hlb "log"%string)
              with "Hcg Hown [] [] Htext Hpc Hlog Hpbare Hprocs").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iIntros (CID19 Hq19 mbo) "%Hcsbo Hcg Hown _ _ Hpc Hpbare Hop".
    assert (Hpc2e : ret_pc (R3 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0x2e)) by (rewrite HR3ra; pcw).
    iEval (rewrite Hpc2e) in "Hpc".
    iDestruct ("Hpback0" with "Hpbare") as "Hpriv".
    iDestruct "Hop" as (Sb0) "HopS".
    assert (Hbosp : so_sp sp0 mbo).
    { rewrite /so_sp (callee_saved_lookup Hcsbo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HR3sp. }
    assert (Hbos0 : (mbo !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsbo Rs0 ltac:(vm_compute; reflexivity)).
      exact HR3s0. }
    assert (Hbos2 : (mbo !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcsbo Rs2 ltac:(vm_compute; reflexivity)).
      exact HR3s2. }
    assert (Hbos3 : (mbo !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcsbo Rs3 ltac:(vm_compute; reflexivity)).
      exact HR3s3. }
    assert (Hbothr : so_thr m mbo).
    { intros c Hc N2 N8b N9 N18 N19. rewrite (callee_saved_lookup Hcsbo c Hc).
      exact (HR3thr c Hc N2 N8b N9 N18 N19). }
    (* ===== +0x2e lw a5,-180(s0) -- the omode word ===== *)
    iApply (wp_lw_s_sconf (CID := CID19) (mword_of_int (SO + 0x2e)) Ra5 Rs0
              (mword_of_int 3916 : mword 12) mbo (K - 24)%nat (arg_int32 vom) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [H23hi]").
    { iApply (soi_02e with "Htext"). }
    { iEval (rgne; rewrite Hbos0; rewrite so_omode). iExact "H23hi". }
    iIntros (CID20 Hq20) "Hcg Hpc H23hi".
    iEval (rgne; rewrite Hbos0; rewrite so_omode) in "H23hi".
    set (S1 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (arg_int32 vom) : mword 64)]> mbo).
    assert (HS1a5 : (S1 !!! Regidx Ra5 : mword 64) = so_omv (arg_int32 vom))
      by (rewrite /S1 /so_omv; apply upd_eq).
    assert (HS1sp : so_sp sp0 S1)
      by (rewrite /so_sp /S1 upd_ne; [exact Hbosp | nz]).
    assert (HS1s0 : (S1 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /S1 upd_ne; [exact Hbos0 | nz]).
    assert (HS1s2 : (S1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /S1 upd_ne; [exact Hbos2 | nz]).
    assert (HS1s3 : (S1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /S1 upd_ne; [exact Hbos3 | nz]).
    assert (HS1thr : so_thr m S1).
    { intros c Hc N2 N8b N9 N18 N19. rewrite /S1 upd_ne; [| regne].
      exact (Hbothr c Hc N2 N8b N9 N18 N19). }
    assert (Hpp32 : add_vec_int (mword_of_int (SO + 0x2e) : mword 64) 4
                    = mword_of_int (SO + 0x32)) by pcw.
    iEval (rewrite Hpp32) in "Hpc".
    (* ===== +0x32 andi a5,a5,512 -- O_CREATE ===== *)
    iApply (wp_andi_s_sconf (CID := CID20) (mword_of_int (SO + 0x32)) Ra5 Ra5
              (mword_of_int 512 : mword 12) (so_and (arg_int32 vom) 512)
              S1 (K - 24)%nat b ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HS1a5; reflexivity) with "Hcg Hpc []").
    { iApply (soi_032 with "Htext"). }
    iIntros (CID21 Hq21) "Hcg Hpc".
    set (S2 := <[Regidx Ra5 := regval_into_reg
                  (so_and (arg_int32 vom) 512)]> S1).
    assert (HS2a5 : (S2 !!! Regidx Ra5 : mword 64) = so_and (arg_int32 vom) 512)
      by (rewrite /S2; apply upd_eq).
    assert (HS2sp : so_sp sp0 S2)
      by (rewrite /so_sp /S2 upd_ne; [exact HS1sp | nz]).
    assert (HS2s0 : (S2 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /S2 upd_ne; [exact HS1s0 | nz]).
    assert (HS2s2 : (S2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1s2 | nz]).
    assert (HS2s3 : (S2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1s3 | nz]).
    assert (HS2thr : so_thr m S2).
    { intros c Hc N2 N8b N9 N18 N19. rewrite /S2 upd_ne; [| regne].
      exact (HS1thr c Hc N2 N8b N9 N18 N19). }
    assert (Hpp36 : add_vec_int (mword_of_int (SO + 0x32) : mword 64) 4
                    = mword_of_int (SO + 0x36)) by pcw.
    iEval (rewrite Hpp36) in "Hpc".
    (* ---- THE ADAPTER: the syscall's continuation, at the post-argstr
       process state.  [P'] is argstr's report and [upd_upt] is where it
       lands; everything below the split speaks [so_cont0]. ---- *)
    iAssert (wp_next (CID0 := CID21) true (proc_addr j)
               (so_cont0 gf bn gfs cov logstart bmapstart inodestart size
                         ninodes ns dqb dqs dqbs dqn (proc_addr j) pid
                         (upd_upt V P') m K eb b lks))
      with "[Hcont]" as "Hcont0".
    { iEval (rewrite /wp_next). iIntros (CIDz) "%Hqz".
      iEval (rewrite /so_cont0). iIntros (mf ns2) "%Hcsf %Hns2".
      iIntros "Hcg Hown Htce Hcce Hpc Hsbn Hsbi Hsbs Hsbb Hbsl Hisl
               Hpost".
      iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf ns2 P' with "[%] [%] Hcg Hown Htce Hcce Hpc
                Hbsl Hsbn Hsbi Hsbs Hsbb [%] Hisl Hpost").
      { exact Hcsf. }
      { exact Hupt. }
      { exact Hns2. } }
    (* ===== +0x36 c.beqz a5, +0xdc -- the O_CREATE SPLIT ===== *)
    destruct (eq_vec (so_and (arg_int32 vom) 512) (zero_reg : mword 64))
      eqn:Hoc.
    { (* ---- no O_CREATE: the else arm at +0xdc ---- *)
      iApply (wp_cbeqz_taken_s_sconf (CID := CID21) (mword_of_int (SO + 0x36))
                (mword_of_int 83 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                S2 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HS2a5; exact Hoc)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_036 with "Htext"). }
      iIntros (CID22 Hq22). iNext. iIntros "Hcg Hpc".
      assert (Htg36 : add_vec (mword_of_int (SO + 0x36) : mword 64)
                        (sign_extend' 64
                           (sign_extend' 13 (concat_vec (mword_of_int 83 : mword 8) ('b"0"))))
                      = mword_of_int (SO + 0xdc)) by pcw.
      iEval (rewrite Htg36) in "Hpc".
      iDestruct (cpu_own_transport CID19 CID22 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (wp_next_shift (b := true) (CIDa := CID21) (CIDb := CID22)
                   ltac:(wp_next_chain) with "Hcont0") as "Hcont0".
      iApply (so_entry_n (CID0 := CID22) gfl gf ga gpr gs j gl gu gd gk pd pav
                pu bn g gfs gi cn gtl cov logstart bmapstart inodestart nib
                ninodes size dev pk bf (arg_int32 vom) (word_lo u23) ns Sb0
                pid dqb dqs dqbs dqn (upd_upt V P') m S2 sp0 K eb b lks
                u4 u5 u6 u24
                HKfull Hdevc Hnibc Hlogc Histc HdevR Hnib0 Hgeom Hsize Hbm0
                Hbmcov Hbmlog Hist0 Hcovb Hbmgeo Hiregb Hpcstr Hpk Hni1 Hni2
                Hni3 Hush Hprkc Hnsb Hj Hgl Heb Hlkempty Hal23
                ltac:(reflexivity) HS2sp HS2thr HS2s0 HS2s2 HS2s3 Hal
                with "Hcg Hown [] [] Htext Hdata Hpc Hpre Hftab Hbio
                      Hlog Hseam Hgen Hkenv Hitab Hitinv Hescrows Hslks Hireg Hropen
                      Hsbn Hsbi Hsbs Hsbb Hbmres Hpriv Hprocs Hdev Hgeo Hdlk
                      HopS Hbsl Hisl Hfds Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hbuf H23lo
                      H23hi H24 Hcont0").
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. } }
    (* ---- O_CREATE: the create arm at +0x38 ---- *)
    iApply (wp_cbeqz_fall_s_sconf (CID := CID21) (mword_of_int (SO + 0x36))
              (mword_of_int 83 : mword 8) (Cregidx (mword_of_int 7)) Ra5
              S2 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HS2a5; exact Hoc)
              with "Hcg Hpc []").
    { iApply (soi_036 with "Htext"). }
    iIntros (CID22 Hq22) "Hcg Hpc".
    assert (Hpp38 : add_vec_int (mword_of_int (SO + 0x36) : mword 64) 2
                    = mword_of_int (SO + 0x38)) by pcw.
    iEval (rewrite Hpp38) in "Hpc".
    iDestruct (cpu_own_transport CID19 CID22 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (wp_next_shift (b := true) (CIDa := CID21) (CIDb := CID22)
                 ltac:(wp_next_chain) with "Hcont0") as "Hcont0".
    iApply (so_entry_c (CID0 := CID22) gfl gf ga gpr gs j gl gu gd gk pd pav
              pu bn g gfs gi cn gtl cov logstart bmapstart inodestart nib
              ninodes size dev pk bf (arg_int32 vom) (word_lo u23) ns Sb0
              pid dqb dqs dqbs dqn (upd_upt V P') m S2 sp0 K eb b lks
              u4 u5 u6 u24
              HKfull Hdevc Hnibc Hlogc Histc HdevR Hnib0 Hgeom Hsize Hbm0
              Hbmcov Hbmlog Hist0 Hcovb Hbmgeo Hiregb Hpcstr Hpk Hni1 Hni2
              Hni3 Hush Hprkc Hnsb Hj Hgl Heb Hlkempty Hal23
              ltac:(reflexivity) HS2sp HS2thr HS2s0 HS2s2 HS2s3 Hal
              with "Hcg Hown [] [] Htext Hdata Hpc Hpre Hftab Hbio
                    Hlog Hseam Hgen Hkenv Hitab Hitinv Hescrows Hslks Hireg
                    Hropen
                    Hsbn Hsbi Hsbs Hsbb Hbmres Hpriv Hprocs Hdev Hgeo Hdlk
                    HopS Hbsl Hisl Hfds Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hbuf H23lo
                    H23hi H24 Hcont0").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
  Qed.

End ProofSysOpenBody.

End SysOpenProof.
