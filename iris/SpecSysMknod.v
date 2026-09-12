(* SpecSysMknod.v -- THE contract of sys_mknod(), stated independently of
   its proof.  Requires only the definitional layer, its callees' SPECS and
   the abstract-state vocabulary -- never a whole-function proof file -- so
   every function proof can be checked in parallel.

     uint64 sys_mknod(void) {
       struct inode *ip;
       char path[MAXPATH];
       int major, minor;

       begin_op();
       argint(1, &major);
       argint(2, &minor);
       if ((argstr(0, path, MAXPATH)) < 0 ||
           (ip = create(path, T_DEVICE, major, minor)) == 0) {
         end_op();
         return -1;
       }
       iunlockput(ip);
       end_op();
       return 0;
     }

   @ KernelSyms.sys_mknod, 96 bytes / 32 instructions (CodeSysMknod.v).
   A TWENTY-slot frame: ra@152 (slot 1), s0@144 (slot 2, the frame
   pointer), the [char path[128]] local in slots 18 down to 3
   ([addi aN,s0,-144]), **the two [int] locals sharing slot 19** -- [minor]
   in its low word at [s0-152], [major] in its high word at [s0-148] --
   and slot 20 unused padding.  As in sys_mkdir, [ip] never leaves a0, so
   no callee-saved register beyond ra and s0 is ever touched.

   ==== ONE CONTRACT ====================================================

   [Module Type SYSMKNOD] is sys_mknod's only seal.  Its body is the
   whole-function FRAME below plus ONE caller INPUT ([mknod_au_at], the
   atomic-update bundle at the path the caller passed) and ONE armed
   OUTPUT ([mknod_arms], keyed on the returned a0).  The landed return blanket [sys_mknod_ret] is a
   consequence of the arms ([mknod_arms_ret]) rather than a second
   conjunct, because the arms already split on the two words a0 can hold.
   A STABLE form is a DERIVED corollary ([wp_sys_mknod_stable_body], proved
   from the seal in ProofSysMknod.v) and never a second proof against the
   code.

   ==== WHAT THE CALLER HANDS IN =======================================

   [mknod_au_pre] is the one-shot bundle of this syscall's linearization
   instants, at the commit mask [appE]:

     - [FsAbsEra.ep_start] AT THE PATH -- nameiparent's PARENT PREFIX
       ([npar_elems pl = removelast (path_elems pl)]: create
       resolves with nameiparent, which fires dirlookup on every element
       but the last, and the LAST element is the created NAME, tied in the
       post by [last (path_elems pl) = Some nm]).  WHICH path is fixed by
       the READING of trapframe argument 0: sys_mknod reads its path out of
       USER memory, and [ArgPath.arg_path_of M pv pl] says the bytes of
       [pl] ARE the calling process's bytes at that pointer, with the NUL
       after them.  So the caller-facing bundle [mknod_au_at] is that
       reading's guarded wand -- one path's worth of walk for a caller that
       knows its own image, which is what a PINNED cursor is -- and the
       success arm's [pl] is tied to the same reading rather than merely
       exposed.  The START is [FsAbsStart.um_start_of cw pl] -- ROOTINO on
       an absolute fetch, the calling process's cwd inum on a relative
       one.
     - [acre_commit_at] -- the success commit, two-phase, fired around the
       parent-row retag at dirlink's successful entry write.
     - [dlookup_commit_at] -- the read-only observation, fired at create's
       own exists-lookup when the name is already there.
     - [cre_child_unfired] -- the child's two legs: the row APPEARS at
       nlink 1, and the unarm fires instead if the parent's entry write
       fails.  THE UNARM IS THE UNDO OF THAT ARM: its inum is the one the
       arm's receipt names ([FsAbsCreateFire.aunarm_of_arm]), which is the
       inum [ialloc] just returned and hence one the view did not have.
       The code never unarms anything else.

   All four are shaped at the AUTHORITY ([FsAbsMknodFire]'s header says why
   an [astate]-shaped commit cannot be discharged against
   [InodeRegion.ftop_body] at all: [abs_view] is not injective, so no
   give-back wand can be paid).

   ==== THE ARMS ========================================================

   ret 0  -- [mknod_post_ok]: create's ARM C-OK read at [T_DEVICE]
             ([SpecCreate.cre_ok_arms_dev]) at the fetched path, under an
             [exists i] beside the region bound create's own post states.  A [ret = 0] is a RECEIPT UNCONDITIONALLY: the era
             walk takes a relative start ([FsAbsStart.ep_start] -- the
             trace deferred in the START INUM), so the proof calls ONE
             create contract for every fetched string and there is no
             absolute-path escape disjunct.  That is what makes the
             theorem say anything about init's "console" and "sh"
             (relative, cwd = ROOTINO).
   ret -1 -- [mknod_post_fail]: nothing fs-visible happened (argstr
             failed) and the whole bundle comes back unspent, or
             create's failure fold read at [T_DEVICE]
             ([SpecCreate.cre_fail_arms_dev]) under an [exists pl] (the
             walk died,
             or create failed at the parent -- either the
             exists-observation fired at a name the parent already held,
             or no abstract observation is available to report).
             DETERMINISM: none is claimed, and none is available.

   ==== THE THREE SYSCALL ARGUMENTS ====================================

   TWO C LOCALS IN ONE FRAME SLOT, AND A HALFWORD READ OUT OF AN [int].
   argint writes a 4-byte cell; the [lh a3,-152(s0)] / [lh a2,-148(s0)] at
   +0x32 / +0x36 then read the LOW HALFWORD of each, because create's
   [short major, short minor] parameters are narrower than the [int]
   locals.  So the walk splits slot 19 into two words
   ([InstrBytes.word_pointsto_split4]) and each word into two halfwords,
   and rejoins on the way to the epilogue.  What reaches the CONTRACT is
   [SysMknodDefs.dev_arg] of the trapframe words -- the low sixteen bits
   read unsigned -- so the caller's receipts speak about the numbers IT
   passed.  What the caller must supply is only that trapframe words
   [tf_arg_idx 0], [1] and [2] exist (argraw's premise, spelled through
   [pv_tf V]).

   BOTH argint RETURN VALUES ARE IGNORED by the C, and [SpecArgint]'s post
   claims nothing about a0, so there is nothing to discard and no arm to
   refute: an out-of-range index would have panicked inside argraw, which
   is why the index premises are [i < NARG] here rather than a branch.

   ==== THE LEDGERS, AND WHAT THEY REST ON ==============================

   Identical to sys_mkdir's, and for identical reasons.  begin_op mints ten
   units, create takes the whole reservation in SET form, end_op retires
   the rest; the [iunlockput(ip)] at +0x46 runs BEFORE end_op and is
   payable only out of create's residue, which is what the [ok = true]
   floor [(iput_units <= u')%nat] in create's post exists for.  This arm is
   the NON-directory one, so it closes with slack
   ([CreateBudget.cr_budget_file]) where sys_mkdir's closes exactly; the
   clause is the same clause.

   The reference ledger is likewise sys_mkdir's: create keeps one slot out
   on success -- its post states that as the equation [S ns' = ns] -- and
   the [iunlockput] hands it back, so every arm ends at [ns].

   ==== WHAT ITS CALLER MUST HOLD ======================================

   create's premise set, unchanged: the printk credential pair ialloc's
   out-of-inodes arm needs, all FOUR superblock cells, and mkfs's inode
   geometry including the [ushort] tie [16 * nib <= 2^16].  [eb = true] is
   create's premise inherited verbatim; the [trap_csrs_ext] /
   [cpu_claim_ext] complement is threaded but is [emp] there.

   THE CROSSING IS THE LITERAL [true]: this function sleeps in begin_op,
   argstr's fault path, create and end_op, so it may return on a hart other
   than the one it was called on.  (The two argint calls do NOT park --
   their own crossing is at [b] -- but the function's is the join of all
   five.)

   THE IMAGE DOES NOT MOVE.  This syscall only READS user memory (argstr,
   through fetchstr and copyinstr); the pages it faults in on the way were
   already in the block's view, as lazy pages reading 0, so vmfault does
   not move it either.  Only the DESCRIPTOR grows, and the block comes back
   at the image it was handed.

   ==== NOTHING ABOUT DURABILITY =======================================

   No durable clause of any kind appears below -- no [flushed], no
   snapshot, no batch (design/fs-syscall-specs.md section 5: durability is
   three GLOBAL principles a consumer applies only at crash points, and the
   per-node certificates live in FsDurSyscall.v).  And nothing about the
   intermediate states create passes through: the child is minted (free
   record -> device record, unreachable orphan) STRICTLY BEFORE the entry
   insert, and that mint is an ordinary state change a concurrent observer
   may see -- which is what the child's two legs make the caller answer
   for.

   BINDERS: one instance path per scope -- [fileG] is bound and
   [icacheG]/[icfg] resolve only through its fields (the SpecCreate
   header's argument, inherited); the FsAbs carriers resolve their
   [fsTopG]/[fsLinkG] through [xv6G]'s fields.  The live Gamma is
   [FsBytesGamma.fs_gamma_L fsc_fs]; its gname tie to [ftop_body]'s
   authority is definitional ([FsAbs.ftop_gamma_top], by reflexivity). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
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
Require Import SpecPrintk.      (* [printk_env], [printk_gen_contract] *)
Require Import SpecDirlink.     (* [ic_sleeplocks], [ireg_blocks_ok] *)
Require Import SpecCreate.      (* [create_slots], [create_units], [T_DEVICE] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Require Import FsTree.
Require Import FsBytesGamma.
Require Import SysMknodDefs.   (* [dev_arg]: the device numbers' reading *)
Require Import FsAbsEra.         (* [ep_start]: the parent-prefix walk
                                    one-shot AT ONE PATH                 *)
Require Import FsAbsMknodFire.   (* the commits and the walk premise     *)
Require Import ArgPath.          (* [arg_path_of]: the reading of
                                    trapframe argument 0, shared with
                                    sys_exec and sys_open               *)
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import PieceFam.        (* [pfam]: a one-shot piece's receipt beside its refund *)
Require Import FsAbs.            (* LAST (FsAbs's own rule)              *)
Require Import PathElems.        (* [path_elems]                         *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* sys_mknod's own frame is 160 bytes -- TWENTY slots ([c.addi16sp sp,-160]
   at +0x00), of which sixteen are the [path] buffer and one holds the two
   [int] locals.  Its deepest callee is create (114); iunlockput wants 64,
   argstr 60, end_op 58, begin_op 26, argint 18. *)
Notation K_sys_mknod := (144%nat) (only parsing).

Section SysMknodRet.
  Context `{!riscvGS Σ, FSC : fscfg}.

  (* sys_mknod's result: 0, or -1.  Nothing else reaches the caller -- the
     inode create returned was iunlockput inside, and [proc_priv] comes back
     at the SAME record but for argstr's page-table growth, which is relayed
     separately.  It is the arms' [_ret] reading, below. *)
  Definition sys_mknod_ret (r : mword 64) : Prop :=
    r = (zero_reg : mword 64) \/ r = (mword_of_int (-1) : mword 64).

End SysMknodRet.

Section SysMknod.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* everything the AU caller hands in, AT THE PATH IT PASSED, at the
     commit mask [appE].  The walk is the parent-prefix one-shot at that
     one path ([FsAbsEra.ep_start], which is [npar_walk_pre_era]'s body
     there -- [FsAbsMknodFire.np_start_of_mknod] is the rename), so a
     caller whose cursor is PINNED can hand it in and the receipt below
     says the device node was created at THIS path's parent, under THIS
     path's last element. *)
  Definition mknod_au_pre Γ (γfs : fs_names) (cw : Z) (pl : list (bv 8))
      (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) : iProp Σ :=
    (ep_start γfs cw P Pmiss pl
     ∗ pf_at (acre_commit_at Γ appE (ADev ma mi)) Fok
     ∗ pf_at (dlookup_commit_at Γ appE) Fex
     (* ...and the CHILD's two legs, unfired *)
     ∗ cre_child_unfired Γ (ADev ma mi) Farm Fun)%I.

  (* ...AND THE SYSCALL TIER: the same bundle under the reading of
     trapframe argument 0, which is the string sys_mknod [argstr]s and
     create walks.  [SpecSysExec.sys_exec_au_pre] states exec's walk piece
     under exactly this guard, and [SysOpenDefs.open_au_plain_at] open's.
     It is ONE walk: the wand is linear and the reading is a function of
     [(M, pv)] ([ArgPath.arg_path_of_uniq]).  THE COMMITS STAY OUTSIDE IT,
     because argstr can fail and then no [pl] satisfies the reading at all
     (an image with no NUL at or after [pv] has no reading) -- so the
     failure fold's "nothing happened" arm has to hand the commits back on
     the nose, which is what [mknod_stable_fail]'s first arm consumes.
     Only the walk is path-shaped anyway: a commit is keyed by an inum and
     a view, never by a string. *)
  Definition mknod_au_at Γ (γfs : fs_names) (cw : Z)
      (M : gmap Z (bv 8)) (pv : mword 64) (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) : iProp Σ :=
    ((∀ pl : list (bv 8), ⌜arg_path_of M pv pl⌝ -∗ ep_start γfs cw P Pmiss pl)
     ∗ pf_at (acre_commit_at Γ appE (ADev ma mi)) Fok
     ∗ pf_at (dlookup_commit_at Γ appE) Fex
     ∗ cre_child_unfired Γ (ADev ma mi) Farm Fun)%I.

  (* ...and the INSTANCE, the step sys_mknod's proof takes once argstr has
     answered: at the path it read, the walk wand fires. *)
  Lemma mknod_au_at_inst Γ (γfs : fs_names) (cw : Z)
      (M : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    arg_path_of M pv pl ->
    mknod_au_at Γ γfs cw M pv ma mi P Pmiss Farm Fun Fok Fex -∗
    mknod_au_pre Γ γfs cw pl ma mi P Pmiss Farm Fun Fok Fex.
  Proof.
    iIntros (Hpl) "(Hw & Hok & Hex & Hch)". rewrite /mknod_au_pre.
    iFrame "Hok Hex Hch". iApply ("Hw" $! pl with "[%]"). exact Hpl.
  Qed.

  (* THE GENERIC SUPPLIER'S ONE LINE: a family that tracks nothing owes the
     walk at EVERY string ([npar_walk_pre_era], what [FsAbsInvFire]
     discharges), and that form instantiates to the one-path bundle. *)
  Lemma mknod_au_at_of_all Γ (γfs : fs_names) (cw : Z)
      (M : gmap Z (bv 8)) (pv : mword 64) (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    npar_walk_pre_era γfs cw P Pmiss -∗
    pf_at (acre_commit_at Γ appE (ADev ma mi)) Fok -∗
    pf_at (dlookup_commit_at Γ appE) Fex -∗
    cre_child_unfired Γ (ADev ma mi) Farm Fun -∗
    mknod_au_at Γ γfs cw M pv ma mi P Pmiss Farm Fun Fok Fex.
  Proof.
    iIntros "Hw Hok Hex Hch". rewrite /mknod_au_at. iFrame "Hok Hex Hch".
    iIntros (pl) "_". iApply (np_start_of_mknod γfs cw P Pmiss pl with "Hw").
  Qed.

  Lemma mknod_au_pre_of_all Γ (γfs : fs_names) (cw : Z) (pl : list (bv 8))
      (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    npar_walk_pre_era γfs cw P Pmiss -∗
    pf_at (acre_commit_at Γ appE (ADev ma mi)) Fok -∗
    pf_at (dlookup_commit_at Γ appE) Fex -∗
    cre_child_unfired Γ (ADev ma mi) Farm Fun -∗
    mknod_au_pre Γ γfs cw pl ma mi P Pmiss Farm Fun Fok Fex.
  Proof.
    iIntros "Hw Hok Hex Hch". rewrite /mknod_au_pre. iFrame "Hok Hex Hch".
    iApply (np_start_of_mknod γfs cw P Pmiss pl with "Hw").
  Qed.

  (* ret 0's real arm: create's ARM C-OK read at [T_DEVICE]
     ([SpecCreate.cre_ok_arms_dev]) at the fetched path, beside the region
     bound create's own post already states.  [made] does not key it: at a
     device type the found arm cannot succeed ([cre_made_of_ne_file]), so
     the fresh arm is the only one a zero return can come from. *)
  Definition mknod_post_ok Γ (M : gmap Z (bv 8)) (pv : mword 64) (ma mi : Z)
      (P : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) : iProp Σ :=
    (∃ (pl : list (bv 8)) (i : Z),
       (* ...AND [pl] IS THE CALLER'S OWN ARGUMENT 0: the node
          [ADev ma mi] was created under THIS path's last element, in the
          directory THIS path's parent prefix resolves to. *)
       ⌜arg_path_of M pv pl⌝ ∗
       ⌜0 < i < 16 * Z.of_nat icfg_nib⌝ ∗
       ∃ (av : aview) (d : Z) (nm : fname) (ents : gmap fname Z) (nl : nat),
         ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
         ⌜cre_pre av d nm ents nl i (ADev ma mi)⌝ ∗
         P (length (npar_elems pl)) d ∗
         pf_at (dlookup_commit_at Γ appE) Fex ∗
         Fok.(pf_recv) av d nm i ∗
         (* ...AND THE CHILD'S OWN LEG: the row APPEARED at this inum before
            the parent's entry went in, so the ARM's receipt rides beside
            [cre_pre]; the UNARM comes home unfired. *)
         cre_arm_fired Farm i ∗ pf_at (aunarm_of_arm Γ appE Farm) Fun)%I.

  (* ret -1's two-way fold: nothing fs-visible happened (argstr failed)
     and the whole bundle comes back, or create's own failure fold (the
     walk died, or create failed at the parent). *)
  Definition mknod_post_fail Γ (γfs : fs_names) (cw : Z)
      (M : gmap Z (bv 8)) (pv : mword 64) (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) : iProp Σ :=
    (mknod_au_at Γ γfs cw M pv ma mi P Pmiss Farm Fun Fok Fex
     ∨ (∃ pl : list (bv 8),
          ⌜arg_path_of M pv pl⌝ ∗
          (* create's own failure fold read at [T_DEVICE]
             ([SpecCreate.cre_fail_arms_dev]): the walk died and everything
             is whole, or the cursor comes home with the exists observation
             fired (ARM F-BAD) or not, and the child's legs whole or the
             do-then-undo PAIR (ruling Q-h). *)
          ((npar_walk_dead_era γfs P Pmiss pl
              ∗ pf_at (acre_commit_at Γ appE (ADev ma mi)) Fok
              ∗ pf_at (dlookup_commit_at Γ appE) Fex
              ∗ cre_child_unfired Γ (ADev ma mi) Farm Fun)
           ∨ (∃ d : Z,
                P (length (npar_elems pl)) d
                ∗ pf_at (acre_commit_at Γ appE (ADev ma mi)) Fok
                ∗ ((∃ (av : aview) (i : Z) (nm : fname)
                      (ents : gmap fname Z) (nl : nat),
                      ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
                      ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ ∗
                      ⌜ents !! nm = Some i⌝ ∗
                      Fex.(pf_recv) av d nm i)
                   ∨ pf_at (dlookup_commit_at Γ appE) Fex)
                ∗ (cre_child_unfired Γ (ADev ma mi) Farm Fun
                   ∨ ∃ i : Z, cre_child_pair Farm Fun i)))))%I.

  (* the armed disjunction the continuation receives, keyed on a0.  NO
     ESCAPE on the [ret = 0] arm: the walk takes the relative start, so a
     success is a RECEIPT whatever the fetched string looked like.  See
     the header. *)
  Definition mknod_arms Γ (γfs : fs_names) (cw : Z)
      (M : gmap Z (bv 8)) (pv : mword 64) (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (r : mword 64) : iProp Σ :=
    ((⌜r = (zero_reg : mword 64)⌝
      ∗ mknod_post_ok Γ M pv ma mi P Farm Fun Fok Fex)
     ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝
        ∗ mknod_post_fail Γ γfs cw M pv ma mi P Pmiss Farm Fun Fok Fex))%I.

  (* the return blanket, read off the arms: the arms already split on the
     two words a0 can hold, so the blanket is a consequence and not a
     second conjunct of the continuation *)
  Lemma mknod_arms_ret Γ (γfs : fs_names) (cw : Z)
      (M : gmap Z (bv 8)) (pv : mword 64) (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) (r : mword 64) :
    mknod_arms Γ γfs cw M pv ma mi P Pmiss Farm Fun Fok Fex r ⊢ ⌜sys_mknod_ret r⌝.
  Proof.
    rewrite /mknod_arms /sys_mknod_ret.
    iIntros "[[%Hr _] | [%Hr _]]"; iPureIntro; [left | right]; exact Hr.
  Qed.

  (* =================================================================== *)
  (*  THE STABLE COROLLARY'S VOCABULARY.  Derived from the seal in         *)
  (*  ProofSysMknod.v; the note at the bottom of this file says why a      *)
  (*  form keyed on the FETCHED STRING is not derivable from any AU form.  *)
  (* =================================================================== *)

  (* THE CLIENT'S CHAIN SHARE, PERSISTENT.  [FsAbs.apn_pin] at
     [DfracDiscarded] instead of [DfracOwn q], and the flavour is forced by
     the SHAPE of this contract rather than chosen: the bundle carries TWO
     commits, exactly one of which fires on any run, and the other comes
     back REFUNDED -- as a closure at whatever receipt it was built with.
     A fractional share handed into both is therefore stranded inside the
     refunded one on every arm (write's stable form dodges this by having a
     single commit; read's by refuting its refund arm with [0 <= n], and
     neither dodge exists here: argstr can fail).  A DISCARDED share is
     copied into both, returned to the client for free, and costs the
     client exactly what the corollary's name claims -- the chain
     directories' rows never move again.  The PARENT is not among them:
     [mkr_chain] pins [ds !!! j] for [j < |ps|] and the parent is
     [ds !!! |ps|], so the success retag is untouched -- by construction
     rather than by a side condition. *)
  Definition mkr_pin Γ (avc : aview) (d : Z) : iProp Σ :=
    (∃ a : anode, ⌜avc !! d = Some a⌝ ∗ nview_dq Γ DfracDiscarded d a)%I.

  Definition mkr_chain Γ (avc : aview) (ds : list Z)
      (ps : list fname) : iProp Σ :=
    ([∗ list] j ↦ _ ∈ ps, mkr_pin Γ avc (ds !!! j))%I.

  Global Instance mkr_pin_persistent Γ avc d : Persistent (mkr_pin Γ avc d).
  Proof. rewrite /mkr_pin /nview_dq /top_frag_q. apply _. Qed.

  Global Instance mkr_chain_persistent Γ avc ds ps :
    Persistent (mkr_chain Γ avc ds ps).
  Proof. rewrite /mkr_chain. apply _. Qed.

  (* THE ENRICHED RECEIPT, and it is the whole of what the pins buy: at the
     instant the receipt fires, the client's run is a run OF THE LIVE VIEW
     -- so [apath_at av root ps = Some (ds !!! |ps|)] holds THERE
     ([FsAbs.arun_apath_tot]), not merely in the client's remembered [avc].
     That is what makes the parent inum the arms expose comparable with the
     client's own [ds !!! |ps|]: on [d = ds !!! |ps|] -- a comparison the
     client makes itself, on data the arm hands it -- the create landed in
     the directory its path names, under a name absent from that directory
     at that instant ([cre_pre]'s second conjunct). *)
  Definition mkr_recv (root : Z) (ps : list fname) (ds : list Z)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ)
      : aview -> Z -> fname -> Z -> iProp Σ :=
    fun av d nm i => (⌜arun av root ps ds⌝ ∗ Φ av d nm i)%I.

  (* ...and the PAIR the arms are read at: the run rides the RECEIPT, the
     refund is the client's own (the enrichment costs it nothing). *)
  Definition mkr_fam (root : Z) (ps : list fname) (ds : list Z)
      (F : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ) :=
    MkPfam (mkr_recv root ps ds F.(pf_recv)) F.(pf_refund).

  (* ret 0: [mknod_post_ok] with the cursor gone (the stable form owes
     the walk nothing -- see the derivation) and the instant's run stated
     purely beside the client's own receipt.  The lookup commit comes back
     AT THE CLIENT'S OWN [Fex], not at the enriched one: the enrichment is
     a conjunct, so the refund weakens back. *)
  Definition mknod_stable_ok Γ (ma mi : Z) (root : Z)
      (ps : list fname) (ds : list Z)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) : iProp Σ :=
    (∃ (pl : list (bv 8)) (av : aview) (d i : Z) (nm : fname)
       (ents : gmap fname Z) (nl : nat),
       ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
       ⌜cre_pre av d nm ents nl i (ADev ma mi)⌝ ∗
       ⌜0 < i < 16 * Z.of_nat icfg_nib⌝ ∗
       ⌜arun av root ps ds⌝ ∗
       pf_at (dlookup_commit_at Γ appE) Fex ∗
       Fok.(pf_recv) av d nm i ∗
       (* the child's row APPEARED at this inum *)
       cre_arm_fired Farm i ∗ pf_at (aunarm_of_arm Γ appE Farm) Fun)%I.

  (* ret -1: TWO arms where the AU form has three folds, and the collapse
     is the cursor's disappearance -- "the walk died at hop k" and "nothing
     fs-visible happened" are the same statement once the residue is the
     bundle itself.  The surviving distinction is the one a client can act
     on: either NOTHING FIRED (both commits back, unspent), or the
     exists-observation fired at a name the parent already held. *)
  Definition mknod_stable_fail Γ (ma mi : Z) (root : Z)
      (ps : list fname) (ds : list Z)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) : iProp Σ :=
    ((pf_at (acre_commit_at Γ appE (ADev ma mi)) Fok
      ∗ pf_at (dlookup_commit_at Γ appE) Fex
      (* the child's legs: whole, or the do-then-undo PAIR (ruling Q-h) --
         "nothing fired" and "the walk died" collapse into one arm here, and
         the [fail:] tail lands in it too *)
      ∗ (cre_child_unfired Γ (ADev ma mi) Farm Fun
         ∨ ∃ ic : Z, cre_child_pair Farm Fun ic))
     ∨ (∃ (pl : list (bv 8)) (av : aview) (d i : Z) (nm : fname)
          (ents : gmap fname Z) (nl : nat),
          ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
          ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ ∗
          ⌜ents !! nm = Some i⌝ ∗
          ⌜arun av root ps ds⌝ ∗
          pf_at (acre_commit_at Γ appE (ADev ma mi)) Fok ∗
          Fex.(pf_recv) av d nm i
          (* ...and the child's legs: whole, or the do-then-undo PAIR
             (ruling Q-h) *)
          ∗ (cre_child_unfired Γ (ADev ma mi) Farm Fun
             ∨ ∃ ic : Z, cre_child_pair Farm Fun ic)))%I.

  Definition mknod_stable_arms Γ (ma mi : Z) (root : Z)
      (ps : list fname) (ds : list Z)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (r : mword 64) : iProp Σ :=
    ((⌜r = (zero_reg : mword 64)⌝
      ∗ mknod_stable_ok Γ ma mi root ps ds Farm Fun Fok Fex)
     ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝
        ∗ mknod_stable_fail Γ ma mi root ps ds Farm Fun Fok Fex))%I.

End SysMknod.

(* big-op bodies behind Definitions at syscall altitude: seal them, or an
   [iFrame] near a consumer resolves instances through the whole hop family
   (durable-notes; optimization.md, "a big-op body is the predictor") *)
Global Typeclasses Opaque mknod_au_pre mknod_au_at mknod_post_ok
  mknod_post_fail mknod_arms mkr_chain mknod_stable_ok
  mknod_stable_fail mknod_stable_arms.

(* ===================================================================== *)
(*  THE WHOLE-FUNCTION FRAME, abstracted over the caller's bundle and the *)
(*  armed post.  There is no second body: this frame is the only one, and *)
(*  the two bodies below instantiate it.                                  *)
(* ===================================================================== *)

Definition wp_sys_mknod_frame
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)             (* ftable, kalloc, printk *)
    (gs : list gname) (j : nat) (gl : gname)            (* the running process *)
    (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (ns : nat)                                          (* the iref ledger     *)
    (dqb dqs dqbs dqn : dfrac)
    (v0 v1 v2 : mword 64)                    (* syscall arguments 0 / 1 / 2 *)
    (pid : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (EXTRA : iProp Σ) (ARMS : mword 64 -> iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_mknod in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_mknod <= K)%nat ->
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  (* ---- the block-layer geometry, threaded verbatim to create / iunlockput ---- *)
  log_geom_ok fsc_cov fsc_logst ->
  0 < fsc_size <= BPB ->
  0 <= fsc_bmapstart ->
  fsc_bmapstart ∈ fsc_cov ->
  ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
  0 <= icfg_ist ->
  cov_below fsc_cov fsc_size ->
  bitmap_geom_ok fsc_cov fsc_logst fsc_bmapstart fsc_size ->
  ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
  (* ---- ialloc's three geometry premises, and mkfs's [ushort] tie ---- *)
  1 < fsc_ninodes ->
  fsc_ninodes <= 16 * Z.of_nat icfg_nib ->
  fsc_ninodes < 2 ^ 31 ->
  16 * Z.of_nat icfg_nib <= 2 ^ 16 ->
  (* ---- ialloc's no-inodes arm calls printk, not panic ---- *)
  printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk ->
  (* ---- the reference allowance create's walk needs ---- *)
  (create_slots <= ns)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* create's own premise, inherited: the body runs with the base enabled *)
  eb = true ->
  (* THE THREE SYSCALL ARGUMENTS, read out of the trapframe page
     [proc_priv] carries: argstr takes 0, and the two argints take 1 and 2.
     The VALUES do not reach the postcondition -- [major] and [minor] are
     consumed inside create and the inode is dropped -- so all the caller
     owes is that the words exist. *)
  pv_tf (us_V U) !! tf_arg_idx 0 = Some v0 ->
  pv_tf (us_V U) !! tf_arg_idx 1 = Some v1 ->
  pv_tf (us_V U) !! tf_arg_idx 2 = Some v2 ->
  sie_cap_gpr KT1 m K b pj -∗
  (* ENTERED WITH NO LOCK HELD: the depth is pinned at ZERO, so
     [CpuOwn.cpu_own_zero_empty] DERIVES [lks = ∅] and every order goal the
     five callees raise is [locks_below ∅ _]. *)
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, THREADED.  [emp] at [eb = true] -- which this
     contract's own premise forces -- so no caller gains an obligation. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* ---- the two persistent credentials ialloc's printk arm needs ---- *)
  printk_env fsc_printk fsc_uart fsc_disk -∗
  (* ---- the block layer ---- *)
  bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
  log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
  fs_crash_seam fsc_cov fsc_logst -∗
  gen_cert -∗
  dev_inv fsc_uart fsc_disk -∗
  disk_geom fsc_disk pd pav pu -∗
  is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
  bslots 3 -∗
  (* ---- the inode cache, and the region ialloc claims out of ---- *)
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
  ic_sleeplocks fsc_ic -∗
  ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
  (* ...AND THE SEALED REGIME (iclaim-ledger.md §3.2, RULING B).  Persistent,
     borrowed and never spent; it rides the SAME channel [ireg_inv] does,
     down to [SpecCreate] -> [SpecIalloc] -> [InodeRegion.ireg_claim_au],
     the one mover that mints a [c] column.  Its producer is the boot
     chain's ([IcacheRefDefs.ity_shoot] on fsinit's returned [ireg_boot]), which
     terminates at the EXISTING [LinkForkretNF.wp_forkret_nf_ax] IOU -- no
     new axiom, and a premise pulls nothing into [Print Assumptions]. *)
  ireg_open -∗
  (* ---- the FOUR superblock cells (create reads all of them) ---- *)
  sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  (* argstr's page-table side, and create's (iget's ipool arm allocates) *)
  kalloc_env fsc_kalloc None -∗
  (* the running-thread bundle *)
  procs_inv gs -∗
  (* ---- the process, whole, and the reference allowance ---- *)
  iref_slots ns -∗
  proc_priv γf pj pid U -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b]: sys_mknod sleeps (begin_op,
     argstr's fault path, create and end_op all park), so it can return on
     another hart whatever SIE was doing. *)
  (* ---- THE AU SIDE (the one addition to the premise list) ---- *)
  EXTRA -∗
  wp_next true pj (fun (CID : CpuId) =>
  (* THE IMAGE DOES NOT MOVE (the landed row, [SpecSysMknod]'s note):
     sys_mknod only READS user memory (argstr), so the binders are
     [(mf, ns', P')] and the block returns at [us_upt U P'] -- no [M']. *)
  ∀ (mf : regfile) (ns' : nat) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      (* the page table may have GROWN: argstr's fetchstr faults user pages
         in.  [uptd_ext_sz] is argstr's own report, relayed. *)
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      bslots 3 -∗
      sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
      (* NO ORDERING on the free pool: create both ALLOCATES and FREES. *)
      (* the allowance, spend-at-most: see the header's reference ledger *)
      (* THE LEDGER CLOSES, EXACTLY.  This used to be create's interval
         passed through; create states its figure exactly now (every failure
         arm returns the ledger whole, every success arm keeps ONE out), and
         this function's [iunlockput] is what hands that one back -- so all
         three arms end where they started.  A client can therefore
         re-establish its own [create_slots <= ns] and call again, which the
         interval could not support (FsSyscalls.v's note (S3)). *)
      ⌜ns' = ns⌝ -∗
      iref_slots ns' -∗
      proc_priv γf pj pid (us_upt U P') -∗
      (* the armed post on the returned a0 (implies [sys_mknod_ret]) *)
      ARMS (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE CONTRACT'S BODY.  The abstract state is read at the LIVE Γ,
   [fs_gamma_L fsc_fs]; the device numbers are the syscall arguments' own
   low halfwords ([SysMknodDefs.dev_arg]), so the caller's receipts
   speak about the numbers IT passed. *)
Definition wp_sys_mknod_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)
    (gs : list gname) (j : nat) (gl : gname)
    (pd pav pu : mword 64)
    (ns : nat)
    (dqb dqs dqbs dqn : dfrac)
    (v0 v1 v2 : mword 64)
    (pid : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (P Pmiss : nat -> Z -> iProp Σ)
    (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
    (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :=
  let Γfs := fs_gamma_L fsc_fs in
  let ma := dev_arg v1 in
  let mi := dev_arg v2 in
  wp_sys_mknod_frame γf gs j gl pd pav pu ns dqb dqs dqbs dqn
    v0 v1 v2 pid U m K eb b lks
    (mknod_au_at Γfs fsc_fs (pv_cwi (us_V U)) (us_M U) v0 ma mi
       P Pmiss Farm Fun Fok Fex)
    (mknod_arms Γfs fsc_fs (pv_cwi (us_V U)) (us_M U) v0 ma mi
       P Pmiss Farm Fun Fok Fex).

(* ===================================================================== *)
(*  THE STABLE COROLLARY'S BODY                                           *)
(* ===================================================================== *)

(* The client names a chain it holds persistently -- a root [root], the
   path elements [ps] of the directory it expects to create in, and the run
   [ds] of that chain through its own view [avc] -- and its own two
   receipts.  Every FIRED receipt then reports the run AT THE INSTANT.
   Nothing is claimed about the fetched string: see the note at the bottom
   of this file, which is the reason a form keyed on that string is not
   what this one derives.

   NOT A PARAMETER: the path itself.  [ps]/[ds] are the client's CHAIN, and
   [root] is deliberately free -- an absolute expectation instantiates it
   at [FsImg.ROOTINO], a relative one at the cwd's inum, and neither is
   tied to the fetched string by anything (that is the point of the note).
   Note also that [ps = []] -- init's own [mknod("console", 1, 1)] -- is a
   legal instance: the chain is empty, [arun av root [] [root]] holds for
   free, and the corollary degenerates to the AU form with the cursor
   erased.  It is a DEEP path that pays for the pins. *)
Definition wp_sys_mknod_stable_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)
    (gs : list gname) (j : nat) (gl : gname)
    (pd pav pu : mword 64)
    (ns : nat)
    (dqb dqs dqbs dqn : dfrac)
    (v0 v1 v2 : mword 64)
    (pid : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (root : Z) (avc : aview) (ds : list Z) (ps : list fname)
    (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
    (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :=
  let Γfs := fs_gamma_L fsc_fs in
  let ma := dev_arg v1 in
  let mi := dev_arg v2 in
  arun avc root ps ds ->
  wp_sys_mknod_frame γf gs j gl pd pav pu ns dqb dqs dqbs dqn
    v0 v1 v2 pid U m K eb b lks
    (mkr_chain Γfs avc ds ps
     ∗ pf_at (acre_commit_at Γfs appE (ADev ma mi)) Fok
     ∗ pf_at (dlookup_commit_at Γfs appE) Fex
     ∗ cre_child_unfired Γfs (ADev ma mi) Farm Fun)%I
    (mknod_stable_arms Γfs ma mi root ps ds Farm Fun Fok Fex).

(* ONE MODULE TYPE.  There is no parallel statement for the walk, the
   commits or the arms, and no second proof against the code: a client that
   wants the STABLE reading takes the derived corollary
   [wp_sys_mknod_stable_body] (ProofSysMknod.wp_sys_mknod_stable_of). *)
Module Type SYSMKNOD.
  Parameter wp_sys_mknod :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v0 v1 v2 : mword 64)
      (pid : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)),
      wp_sys_mknod_body γf gs j gl pd pav pu ns dqb dqs dqbs dqn
        v0 v1 v2 pid U m K eb b lks P Pmiss Farm Fun Fok Fex.
End SYSMKNOD.

(* ===================================================================== *)
(*  THE NOTE: WHY A STABLE FORM KEYED ON THE FETCHED STRING IS NOT        *)
(*  DERIVABLE                                                             *)
(* ===================================================================== *)

(* A stable form could try to key its receipts on the FETCHED STRING --
   "either [path_elems pl = path_elems pl0] and the receipt is at [dpar],
   or it did not match and the receipt is unlocated".  That key is NOT
   DERIVABLE FROM ANY AU FORM OF THIS SHAPE, and the obstruction is
   structural rather than a gap in a proof:

   - The walk's cursor family is the ONLY channel from the syscall's
     interior back to the client, and its members take [(k, d)] -- an index
     and an inum.  The cursor predicate is fixed when the contract is
     instantiated, which is BEFORE the fetched string exists
     ([npar_walk_pre_era] is a one-shot universally quantified over [pl]),
     so no cursor can mention [pl].
   - Therefore the located branch of any match key must be an alternative
     whose OTHER branch is entered when a hop's name misses the client's
     chain -- and what a hop knows at that moment ("this name is not
     [ps !!! k]") is a fact about the fetched string, which the cursor
     cannot record.  Recording it as [emp] makes the disjunction
     [⌜located⌝ ∨ True], which carries nothing.
   - A ghost carried through the cursor does not break the wall either: the
     value it would have to carry is the fetched path, the hops that must
     compare against it are proved BEFORE the one-shot fires (they are
     [⊢]-facts of the cursor), and the arm's own [pl] is bound by a
     DIFFERENT existential from the cursor's -- nothing ties the two.

   So the honest content of a stable mknod is not "the walk was mine" but
   "MY TREE HELD AT THE INSTANT", which is what the form above states and
   what the two [_at_pinned] seeds were landed to buy.  The client is left
   holding the comparison the corollary cannot make for it: the parent inum
   is exposed on the arm, [ds !!! |ps|] is the client's own, and equality
   of the two is decidable where it matters.

   WHAT THE NOTE ASKED FOR IS NOW IN THE AU FORM, and it is exactly the
   USER-MEMORY TIE it names: [ArgPath.arg_path_of] is a premise at a lower
   altitude ([SpecFetchstr]'s "they came from user memory", turned into
   "and these are the bytes"), not a stronger corollary here.  So the AU
   form above IS keyed on the fetched string, while the STABLE corollary is
   not -- deliberately: its client names a CHAIN it holds persistently and
   need not know its own image at all, and the obstruction above is about
   deriving a string key from the cursor family, which is still where the
   cursor cannot go. *)

