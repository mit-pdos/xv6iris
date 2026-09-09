(* SpecSysChdir.v -- the public interface of sys_chdir(), stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

     uint64 sys_chdir(void) {
       char path[MAXPATH];
       struct inode *ip;
       struct proc *p = myproc();

       begin_op();
       if (argstr(0, path, MAXPATH) < 0 || (ip = namei(path)) == 0) {
         end_op();
         return -1;
       }
       ilock(ip);
       if (ip->type != T_DIR) { iunlockput(ip); end_op(); return -1; }
       iunlock(ip);
       iput(p->cwd);
       end_op();
       p->cwd = ip;
       return 0;
     }

   @ KernelSyms.sys_chdir, 128 bytes / 45 instructions (CodeSysChdir.v).
   A TWENTY-slot frame: ra@152, s0@144 (the frame pointer), s1@136 (the
   inode, saved only on the path that has one) and s2@128 (the proc), with
   the low sixteen slots -- sp+0 .. sp+127 -- being the [char path[128]]
   local.  [addi a1,s0,-160] / [addi a0,s0,-160] are that buffer's address.

   ==== WHAT THIS CONTRACT IS ABOUT =====================================

   sys_chdir is the SECOND writer of [p->cwd] (kexit is the first), and the
   only one that installs a reference rather than retiring one.  The whole
   contract is the accounting of that swap, and [ProcInv.proc_priv_cwd_pid]
   is the accessor it was written for: the cell and the pid quarter come out
   TOGETHER, because begin_op / namei / ilock / iput / end_op each want
   [p_pid pj |->4{dq} _] while the cwd cell has to stay out from the
   [ld a0,336(s2)] that reads the pointer iput destroys to the
   [sd s1,336(s2)] that installs the new one.

   THE REFERENCE LEDGER CLOSES AT TWO ON EVERY ARM, which is why
   [iref_slots 2] goes in and comes back out unchanged:

   * namei takes two units (its walk holds at most two references at once)
     and, on success, hands back ONE -- the second is spent against the
     reference it returns;
   * the success arm's [iput(p->cwd)] destroys the OLD working directory and
     frees that unit, so the process still owns exactly one parked unit, now
     against [ip];
   * the not-a-directory arm's [iunlockput(ip)] destroys the reference namei
     just made and frees ITS unit, and [p->cwd] never moved;
   * the two failure arms of the [||] never made a reference at all.

   So on all four arms the caller gets [iref_slots 2] back, and the
   invariant "a live process's [p->cwd] has one unit parked in the itable"
   is preserved rather than merely restored.

   ==== THE LOG LEDGER IS THE SET FORM, AND IT HAS TO BE ================

   begin_op mints [LogInv.log_op g MAXOPBLOCKS] = ten units, and end_op
   retires whatever is left, so nothing log-shaped crosses this interface.
   What DOES matter is that the ten units cover the whole body, and the
   COUNTED namei contract does not deliver that: its premise is
   [(L + 1) * iput_units <= n] and its spend is the same figure, so at a
   three-component path it would demand twelve of the ten, and even at
   L = 2 it would hand back one where the following [iput] needs three.
   The SET form -- [SpecNameiEra.wp_namei_era], the era trace walk this
   contract's proof runs, over [LogInv.log_opSt] -- prices the walk at
   [SpecNamex.walk_need L <= 4] regardless of depth and spends at most
   one, which leaves nine for an [iput] that needs three.  That is the
   whole reason this proof threads [log_opS] rather than [log_op]: chdir is
   the first syscall whose path length is unbounded and whose tail still
   has to pay for an inode free.

   NO LINK RESOURCE APPEARS HERE (design/fs-icache.md 20.18 ruling 1).
   sys_chdir writes no directory record -- it reads a type field and swaps a
   pointer -- so there is no count to move and no [IcacheEscrow.dlinks]
   obligation to carry.

   ==== WHAT ITS CALLER MUST HOLD ======================================

   [eb = true] is namei's premise, inherited verbatim: the walker runs with
   the interrupt base enabled, and every acquire inside it mints its own
   pay.  The [trap_csrs_ext] / [cpu_claim_ext] complement is threaded
   anyway, uniformly with begin_op / iput / end_op, and is [emp] there.

   THE CROSSING IS THE LITERAL [true]: this function sleeps in five of its
   callees, so it may return on a hart other than the one it was called on.

   DETERMINISM: none is claimed, and none is available.  Which of the four
   arms runs is a function of the FILE SYSTEM -- whether the user string
   faults, whether the path resolves, whether what it resolves to is a
   directory -- and no caller of this contract knows any of that.  The
   postcondition is therefore the honest disjunction [SpecNamei]'s own
   two-armed result forces, keyed by the returned a0.

   ==== ONE CONTRACT ====================================================

   [Module Type SYSCHDIR] is sys_chdir's only seal.  Its body is the
   whole-function FRAME below plus ONE caller INPUT ([chdir_au_pre]) and
   ONE armed OUTPUT ([chdir_arms], keyed on a0).  The blanket
   [sys_chdir_post] is a CONSEQUENCE of the arms ([chdir_arms_landed])
   rather than a second conjunct -- it carries [proc_priv], which every
   arm already carries -- and it survives as the shape the friendly
   packaging above this contract states ([FsSyscalls] section 4, whose
   functor calls this seal at the trivial families and converts through
   that one bridge).

   ==== WHAT THE CALLER HANDS IN, AND WHAT IT BUYS =====================

   [chdir_au_pre] is the walk-only bundle at the commit mask [appE]:
   [SysOpenDefs.namei_walk_pre_era] handed down unfired, plus
   [SysOpenDefs.aopen_commit_at], open's plain read-only observation,
   fired under the node's lock exactly where the walk tests [T_DIR].
   sys_chdir MINTS NO VOCABULARY OF ITS OWN: every piece it names is the
   open family's, which is why the pieces live in [SysOpenDefs] and only
   the bundle, the arms and the frame live here.

   What it buys is the inum.  A blanket-only success arm is
   [∃ ipv z, proc_priv .. (us_cwi (us_cwd U ipv) z)]: [z] is the real inum
   of the installed inode, but nothing above the icache could say WHICH
   inode that was.  Here [z] IS the walk's cursor, so a caller that
   supplied a cursor it understands learns where its cwd went.

   THE START: the walk premise is [namei_walk_pre_era] at
   [pv_cwi (us_V U)], the calling process's cwd inum at entry, so a
   relative chdir's walk starts where the block says it does.

   ==== THE ARMS ========================================================

   ret 0  -- [chdir_post_ok]: the walk landed on a DIRECTORY, observed as
             such, and the block's cwd moved to it -- pointer and inum
             both, the inum being the walk's own cursor [i].
   ret -1 -- [chdir_post_fail], the three-way fold with the block back
             unchanged on every arm:
             (i)   nothing fs-visible happened (argstr failed): the whole
                   bundle comes back;
             (ii)  the walk died: [namei_walk_dead_era]'s refund shape
                   beside the unfired commit;
             (iii) the walk landed and the node was OBSERVED to be
                   something other than a directory -- the cursor [P L i]
                   and the receipt [Fo.(pf_recv) av i a] at that node.
 *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRefDefs.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecDirlink.    (* [ic_sleeplocks], [ireg_blocks_ok] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Require Import PathElems.       (* [path_elems] *)
Require Import FsTree.          (* [fname] *)
Require Import FsBytesGamma.    (* [fs_gamma_L]: the live Γ *)
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import SysOpenDefs.   (* [namei_walk_pre_era], [namei_walk_dead_era],
                                   [aopen_commit_at] *)
Require Import PieceFam.        (* [pfam]: a one-shot piece's receipt beside its refund *)
Require Import FsAbsDefs.           (* LAST (FsAbs's own rule) *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* sys_chdir's own frame is 160 bytes -- TWENTY slots ([c.addi16sp sp,-160]
   at +0x00), of which sixteen are the [path] buffer.  Its deepest callee is
   namei (106); iunlockput wants 64, argstr 60, iput 60, end_op 58, ilock
   44, begin_op 26, iunlock 26, myproc 10. *)
Notation K_sys_chdir := (136%nat) (only parsing).
Section SpecSysChdir.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.
  (* [GenId], for [ProcInv.proc_priv]'s own index: the private block now
     carries [FirstTok.first_tok], whose boot arm names [gen_cert].  The
     definitions below mention the block, so the section has to bind it. *)
  Context `{GEN : GenId}.

  (* sys_chdir's result, keyed by the returned a0.  The -1 arm gives the
     process block back at the working directory it came in with; the 0 arm
     gives it back with a NEW one, whose reference is the one namei made and
     ilock/iunlock left intact.  [ipv] is existential because the entry the
     path resolves to is not something the caller named. *)
  Definition sys_chdir_post (γf : gname) (pa : mword 64) (pid : mword 32)
      (U : ustate) (r : mword 64) : iProp Σ :=
    (⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ proc_priv γf pa pid U
     ∨ ∃ (ipv : mword 64) (z : Z),
         ⌜r = (zero_reg : mword 64)⌝ ∗
         (* ...at the pointer AND its inum.  [z] is existential
            here as [ipv] is; it is the REAL inum of the installed inode --
            the one [ProcInv.cwd_ref_at] ties the pointer to.  The ARMS
            below name it: it is the walk's own cursor. *)
         proc_priv γf pa pid (us_cwi (us_cwd U ipv) z))%I.

End SpecSysChdir.

(* ===================================================================== *)
(*  THE BUNDLE AND THE ARMS                                               *)
(* ===================================================================== *)

Section SysChdirArms.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  (* everything the caller hands in, at the commit mask [appE]:
     open's walk premise at the process's cwd inum, and open's plain
     observation commit *)
  Definition chdir_au_pre Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) : iProp Σ :=
    (namei_walk_pre_era γfs cw P Pmiss
     ∗ pf_at (aopen_commit_at Γ appE) Fo)%I.

  (* ret -1: the three-way fold -- (i) nothing fs-visible happened (argstr
     failed: the bundle back whole), (ii) the walk died (the era refund
     beside the unfired commit), (iii) the walk landed and the node was
     observed to be something other than a directory *)
  Definition chdir_post_fail Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) : iProp Σ :=
    (chdir_au_pre Γ γfs cw P Pmiss Fo
     ∨ (∃ pl : list (bv 8),
          (namei_walk_dead_era γfs P Pmiss pl
             ∗ pf_at (aopen_commit_at Γ appE) Fo)
          ∨ (∃ (i : Z) (av : aview) (a : anode),
               P (length (path_elems pl)) i
               ∗ ⌜arow_at av i a⌝ ∗ Fo.(pf_recv) av i a
               ∗ ⌜forall (e : gmap fname Z) (nl : nat),
                    a <> MkAnode (ADir e) nl⌝)))%I.

  (* ret 0: the walk landed on a DIRECTORY, observed as such, and the
     block's cwd moved to it -- pointer and inum both, the inum being the
     walk's own cursor [i] *)
  Definition chdir_post_ok Γ (γf : gname) (pj : mword 64) (pid : mword 32)
      (P : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (U : ustate) : iProp Σ :=
    (∃ (ipv : mword 64) (pl : list (bv 8)) (i : Z)
       (e : gmap fname Z) (nl : nat) (av : aview),
       P (length (path_elems pl)) i
       ∗ ⌜arow_at av i (MkAnode (ADir e) nl)⌝
       ∗ Fo.(pf_recv) av i (MkAnode (ADir e) nl)
       ∗ proc_priv γf pj pid (us_cwi (us_cwd U ipv) i))%I.

  (* the armed disjunction the continuation receives, keyed on a0, at the
     block the syscall returns ([us_upt U P']) *)
  Definition chdir_arms Γ (γfs : fs_names) (γf : gname)
      (pj : mword 64) (pid : mword 32) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (U : ustate) (r : mword 64) : iProp Σ :=
    ((⌜r = (mword_of_int (-1) : mword 64)⌝
      ∗ proc_priv γf pj pid U
      ∗ chdir_post_fail Γ γfs cw P Pmiss Fo)
     ∨ (⌜r = (zero_reg : mword 64)⌝
        ∗ chdir_post_ok Γ γf pj pid P Fo U))%I.

  (* THE PROCESS-NAMEABLE HALF OF THE ARMS: chdir's RECEIPT.  What the arms
     above give the DISPATCHER is [proc_priv] at the block whose cwd moved;
     what they give the PROCESS is this -- the walk cursor, the observed
     directory row and the observation's receipt, read at the working
     directory the call resumes at.  It names no kernel ghost: no
     [proc_priv], no [pv_cwd] pointer, no [ProcInv] record at all, which is
     what makes it statable at the U-mode key ([UexecSG.spost_at], branch 9)
     where the only thing the process holds about its cwd is [cw'].

     THE TWO ARMS ARE THE ARMS', keyed on the same a0: a failed chdir
     resumes at the directory it came in with and hands the whole bundle
     back ([chdir_post_fail]); a successful one resumes at the inum the walk
     reached, which is the receipt's whole content -- [cw' = i] is what
     SHARPENS [UsysMemOk.usys_cwd_ok]'s chdir row (which says only that a
     FAILED chdir does not move) into "the directory you named is the
     directory you are in".  [chdir_arms_split] is the tie. *)
  Definition chdir_receipt Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (r : mword 64) (cw' : Z) : iProp Σ :=
    ((⌜r = (mword_of_int (-1) : mword 64)⌝
      ∗ ⌜cw' = cw⌝
      ∗ chdir_post_fail Γ γfs cw P Pmiss Fo)
     ∨ (⌜r = (zero_reg : mword 64)⌝
        ∗ ∃ (pl : list (bv 8)) (i : Z) (e : gmap fname Z) (nl : nat)
            (av : aview),
            ⌜cw' = i⌝
            ∗ P (length (path_elems pl)) i
            ∗ ⌜arow_at av i (MkAnode (ADir e) nl)⌝
            ∗ Fo.(pf_recv) av i (MkAnode (ADir e) nl)))%I.

  (* THE SPLIT: the arms as the kernel's half beside the receipt.  The
     dispatcher keeps [proc_priv] at the block the call leaves -- which is
     the block itself on the failure arm and the block with the cwd pointer
     and inum written on the success arm -- and the pure disjunction that
     says which; the process gets the receipt, read at the inum the block
     now carries.  The arms are not weakened: everything they hold appears
     on the right of this wand.

     THE PREMISE IS THE CONTRACT'S OWN INSTANTIATION.  [chdir_arms] takes
     [cw] and [U] independently and relates them nowhere, so its failure arm
     cannot say by itself that the call resumes at [cw]; [wp_sys_chdir_body]
     instantiates the arms at [cw := pv_cwi (us_V U)] and the dispatcher's
     arm therefore has this equation by [reflexivity]. *)
  Lemma chdir_arms_split Γ (γfs : fs_names) (γf : gname)
      (pj : mword 64) (pid : mword 32) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (U : ustate) (r : mword 64) :
    pv_cwi (us_V U) = cw ->
    chdir_arms Γ γfs γf pj pid cw P Pmiss Fo U r ⊢
      ∃ U' : ustate,
        ⌜(r = (mword_of_int (-1) : mword 64) /\ U' = U)
         \/ (r = (zero_reg : mword 64)
             /\ exists (ipv : mword 64) (i : Z), U' = us_cwi (us_cwd U ipv) i)⌝
        ∗ proc_priv γf pj pid U'
        ∗ chdir_receipt Γ γfs cw P Pmiss Fo r (pv_cwi (us_V U')).
  Proof.
    intros Hcw. rewrite /chdir_arms /chdir_post_ok /chdir_receipt.
    iIntros "[(%Hr & Hpriv & Hfail) | (%Hr & H)]".
    - iExists U.
      iSplitR; [ iPureIntro; left; exact (conj Hr eq_refl) | ].
      iFrame "Hpriv". iLeft.
      iSplitR; [ iPureIntro; exact Hr | ].
      iSplitR; [ iPureIntro; exact Hcw | ].
      iExact "Hfail".
    - iDestruct "H" as (ipv pl i e nl av) "(HP & %Harow & HFo & Hpriv)".
      iExists (us_cwi (us_cwd U ipv) i).
      iSplitR;
        [ iPureIntro; right; split; [ exact Hr | exists ipv, i; reflexivity ] | ].
      iFrame "Hpriv". iRight.
      iSplitR; [ iPureIntro; exact Hr | ].
      iExists pl, i, e, nl, av.
      iSplitR; [ iPureIntro; reflexivity | ].
      iFrame "HP". iSplitR; [ iPureIntro; exact Harow | ]. iExact "HFo".
  Qed.

  (* THE RETURN BLANKET, READ OFF THE ARMS.  It is a consequence and not a
     second conjunct: [sys_chdir_post] carries [proc_priv], and each arm
     already carries it.  This is the bridge [FsSyscalls]'s friendly
     packaging is stated over. *)
  Lemma chdir_arms_landed Γ (γfs : fs_names) (γf : gname)
      (pj : mword 64) (pid : mword 32) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (U : ustate) (r : mword 64) :
    chdir_arms Γ γfs γf pj pid cw P Pmiss Fo U r ⊢
      sys_chdir_post γf pj pid U r.
  Proof.
    rewrite /chdir_arms /chdir_post_ok /sys_chdir_post.
    iIntros "[(%Hr & Hpriv & _) | (%Hr & H)]".
    - iLeft. iFrame "Hpriv". by iPureIntro.
    - iRight. iDestruct "H" as (ipv pl i e nl av) "(_ & _ & _ & Hpriv)".
      iExists ipv, i. iFrame "Hpriv". by iPureIntro.
  Qed.

End SysChdirArms.

(* big-op bodies behind definitions: sealed, per the family convention *)
Global Typeclasses Opaque chdir_au_pre chdir_post_fail chdir_post_ok
  chdir_arms chdir_receipt.

(* ===================================================================== *)
(*  THE WHOLE-FUNCTION FRAME, abstracted over the caller's bundle and the *)
(*  armed post.  There is no second body: this frame is the only one, and *)
(*  the body below instantiates it.                                       *)
(* ===================================================================== *)

(* [ARMS] is on the block and the returned a0 and REPLACES a blanket-only
   [sys_chdir_post], which it implies ([chdir_arms_landed]).  The binder
   list is [(mf, P')]: the image does not move (the header). *)
Definition wp_sys_chdir_frame
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)                          (* ftable, kalloc      *)
    (gs : list gname) (j : nat) (gl : gname)            (* the running process *)
    (pd pav pu : mword 64)                              (* disk fabric + lock  *)
    (dqb dqs : dfrac)
    (v : mword 64)                                      (* syscall argument 0  *)
    (pid : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (EXTRA : iProp Σ) (ARMS : ustate -> mword 64 -> iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_chdir in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_chdir <= K)%nat ->
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  (* ---- the block-layer geometry, threaded verbatim to namei / iput ---- *)
  log_geom_ok fsc_cov fsc_logst ->
  0 < fsc_size <= BPB ->
  0 <= fsc_bmapstart ->
  fsc_bmapstart ∈ fsc_cov ->
  ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
  0 <= icfg_ist ->
  cov_below fsc_cov fsc_size ->
  ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* namei's own premise, inherited: the walker runs with the base enabled *)
  eb = true ->
  (* argstr reads syscall argument 0 out of the trapframe page *)
  pv_tf (us_V U) !! tf_arg_idx 0 = Some v ->
  sie_cap_gpr KT1 m K b pj -∗
  (* entered with no lock held: depth pinned at zero *)
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  (* ---- the block layer ---- *)
  bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
  log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
  fs_crash_seam fsc_cov fsc_logst -∗
  gen_cert -∗
  dev_inv fsc_uart fsc_disk -∗
  disk_geom fsc_disk pd pav pu -∗
  is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
  bslots 3 -∗
  (* ---- the inode cache, and the region iput's truncate arm frees into ---- *)
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
  ic_sleeplocks fsc_ic -∗
  ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
  (* the sealed regime, riding [ireg_inv]'s channel; see the header *)
  ireg_open -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  (* argstr's page-table side, and namei's (iget's ipool arm allocates) *)
  kalloc_env fsc_kalloc None -∗
  (* the running-thread bundle *)
  procs_inv gs -∗
  (* ---- the process, and the reference allowance its walk needs ---- *)
  iref_slots 2 -∗
  proc_priv γf pj pid U -∗
  (* ---- THE CALLER'S BUNDLE (the one addition to the premise list) ---- *)
  EXTRA -∗
  (* the crossing is the literal [true]: sys_chdir parks in five callees *)
  wp_next true pj (fun (CID : CpuId) =>
  (* THE IMAGE DOES NOT MOVE (the header): only the descriptor
     grows, so the binders are [(mf, P')] and the block returns at
     [us_upt U P'] -- no [M']. *)
  ∀ (mf : regfile) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      bslots 3 -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
      (* the allowance, whole: the header's reference ledger *)
      iref_slots 2 -∗
      (* the armed post on the final process state and the returned a0
         (implies [sys_chdir_post], through [chdir_arms_landed]) *)
      ARMS (us_upt U P') (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE ONE BODY.  The abstract state is read at the LIVE Γ,
   [fs_gamma_L fsc_fs]; the walk starts at the block's own cwd inum. *)
Definition wp_sys_chdir_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)
    (gs : list gname) (j : nat) (gl : gname)
    (pd pav pu : mword 64)
    (dqb dqs : dfrac)
    (v : mword 64)
    (pid : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (P Pmiss : nat -> Z -> iProp Σ)
    (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) :=
  let Γfs := fs_gamma_L fsc_fs in
  wp_sys_chdir_frame γf gs j gl pd pav pu dqb dqs
    v pid U m K eb b lks
    (chdir_au_pre Γfs fsc_fs (pv_cwi (us_V U)) P Pmiss Fo)
    (chdir_arms Γfs fsc_fs γf (proc_addr j) pid (pv_cwi (us_V U)) P Pmiss Fo).

(* ===================================================================== *)
(*  ONE MODULE TYPE                                                       *)
(* ===================================================================== *)

(* There is no parallel statement and no second proof against the code: a
   client that wants the blanket-only reading takes [chdir_arms_landed],
   which is what [FsSyscalls]'s friendly packaging does. *)
Module Type SYSCHDIR.
  Parameter wp_sys_chdir :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (dqb dqs : dfrac)
      (v : mword 64)
      (pid : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)),
      wp_sys_chdir_body γf gs j gl pd pav pu dqb dqs
        v pid U m K eb b lks P Pmiss Fo.
End SYSCHDIR.
