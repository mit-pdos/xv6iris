(* SpecSysUnlink.v -- the public interface of sys_unlink(), stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

     uint64 sys_unlink(void) {
       struct inode *ip, *dp;
       struct dirent de;
       char name[DIRSIZ], path[MAXPATH];
       uint off;

       if (argstr(0, path, MAXPATH) < 0) return -1;

       begin_op();
       if ((dp = nameiparent(path, name)) == 0) { end_op(); return -1; }

       ilock(dp);

       // Cannot unlink "." or "..".
       if (namecmp(name, ".") == 0 || namecmp(name, "..") == 0)
         goto bad;

       if ((ip = dirlookup(dp, name, &off)) == 0)
         goto bad;
       ilock(ip);

       if (ip->nlink < 1) panic("unlink: nlink < 1");
       if (ip->type == T_DIR && !isdirempty(ip)) {
         iunlockput(ip);
         goto bad;
       }

       memset(&de, 0, sizeof(de));
       if (writei(dp, 0, (uint64)&de, off, sizeof(de)) != sizeof(de))
         panic("unlink: writei");
       if (ip->type == T_DIR) { dp->nlink--; iupdate(dp); }
       iunlockput(dp);

       ip->nlink--;
       iupdate(ip);
       iunlockput(ip);

       end_op();
       return 0;

      bad:
       iunlockput(dp);
       end_op();
       return -1;
     }

   @ KernelSyms.sys_unlink, 384 bytes / 129 instructions (CodeSysUnlink.v),
   the LARGEST function in sysfile.c and the last one proven.  A THIRTY slot
   frame ([c.addi16sp sp,-240] at +0x00, [c.addi4spn s0,sp,240] at +0x06),
   carved -- numbering slots from the top, [pa_stk sp0 n] = sp0 - 8n:

     slot  1  (s0-8)    ra
     slot  2  (s0-16)   s0, the frame pointer (= the ENTRY sp)
     slot  3  (s0-24)   s1 = dp  -- saved LATE, at +0x1a
     slot  4  (s0-32)   s2 = ip  -- saved LATER, at +0x5c
     slot  5  (s0-40)   s3       -- saved LATER STILL, at +0x72
     slots 6..7         dead
     slots 7..8         [struct dirent de] -- writei's, [addi s3,s0,-64]
     slots 9..10        [char name[DIRSIZ]] -- [addi a1,s0,-80]
     slots 11..26       [char path[MAXPATH]] -- [addi a1,s0,-208]
     slot 27            [uint off] in its UPPER word, [s0-212]
     slots 28..29       [struct dirent de] -- isdirempty's, [addi a2,s0,-232]
     slot 30            dead (the frame's bottom)

   THE TWO [de] BUFFERS ARE DIFFERENT SLOTS, and that is not an accident of
   the carve: gcc INLINED isdirempty (see below), and the two [de]s have
   disjoint live ranges, so it gave each its own storage.

   [s3] is DUAL-USE -- isdirempty's loop counter [off] at +0x104..+0x128,
   then the address [&de] at +0x8a -- which is why it is saved before
   [ilock(ip)] and reloaded on every arm at or below the isdirempty test.

   THE THREE REGISTER SAVES ARE SHRINK-WRAPPED, SO THE FRAME CARVE IS
   ARM-DEPENDENT (sys_open's shape, not sys_link's): the prologue pushes
   only ra and s0; [c.sdsp s1,216] is at +0x1a, AFTER the [argstr < 0]
   branch, [c.sdsp s2,208] at +0x5c after BOTH namecmp guards, and
   [c.sdsp s3,200] at +0x72 after dirlookup succeeded.  Each exit restores
   exactly the subset its own path saved: ARM A (+0x170) restores nothing,
   ARM B (+0xe8) restores s1, the [bad:] tail (+0x166) restores s1, ARM D
   (+0x158) restores s2 then falls into [bad:], ARM E (+0x17a) restores s2
   and s3 then falls into [bad:], and the success tail (+0xda) restores all
   three.  Nothing about the two buffers reaches this contract: they are
   carved out of [stack_own] with [StackBytes.slotsn_bytes_own].

   ==== isdirempty HAS NO SYMBOL ========================================

   [grep -i isdirempty kernel-rocq/*.v] is EMPTY and [KernelSyms.v] names
   only [sys_unlink]: gcc folded the whole helper into
   sys_unlink+0x0f8..+0x12c.  So there is no [CodeIsdirempty.v], no
   contract, no coverage row and there never will be -- the loop is a BLOCK
   LEMMA inside [ProofSysUnlinkPure], and its invariant is a fact about that
   block.  Two consequences reach this interface:

   * THE LOOP SPENDS NO LOG BUDGET WHATEVER.  Its body is [readi], whose
     contract takes no [log_op], no [log_ctx] and no [γ : log_names] at all
     ([SpecReadi.v]'s "READI MODIFIES NOTHING" banner), so however many
     records the directory has, no arm's figure depends on its size.  That
     is what makes the whole ledger parameter-free in the directory.
   * ITS SHORT-READ ARM IS A PANIC.  [readi] is EXACT, so
     [!= sizeof(de)] is reachable only where 16 does not divide the
     directory's size; the arm needs no multiple-of-16 invariant, it is
     discharged against [SpecPanic] and never returns.

   ==== WHAT THIS CONTRACT IS ABOUT =====================================

   sys_unlink is the kernel's ONLY record-DELETING path, and the walk is
   where the fragment campaign's delete half is finally spent.  Three facts,
   because they are what the walk is:

   * THE ZEROING RELEASES A FRAGMENT.  [memset(&de,0,16)] then
     [writei(dp,0,&de,off,16)] at +0x8a..+0xa4 is the exact inverse of
     dirlink's append: [FsStateEra.ent_toks_unlink] fires CALLER-SIDE on the
     record [dirlookup] found and RELEASES one [FsStateLink.link_tok] at
     [ip], which the [ip->nlink--; iupdate(ip)] at +0xbe..+0xca then
     CONSUMES through [SpecIupdate.wp_iupdate_unlink].  Nothing else crosses
     this interface in either direction.
   * ITS HOME-LIVE PREMISE COMES FROM THE PAYLOAD, NOT FROM A GUARD.
     The release wants [di_nlink dp <> 0] of the HOME, and unlike
     create and namex sys_unlink has no [nlink == 0] re-check to walk.  What
     supplies it is [DirView.dir_orphan_clean] (fs-fragments-campaign.md,
     PASS 2): an ORPHANED directory's live records are exactly "." and "..",
     the two [namecmp] guards at +0x44 / +0x58 say the matched record is
     neither, and [dirlookup]'s found arm says the record is live -- so the
     home cannot be orphaned.  The clause is a property of THIS binary and
     of no earlier one: it was refuted by sys_link's unguarded [dirlink]
     until f60ff58 gave sys_link create's orphan re-check.
   * THE T_DIR ARM's [dp->nlink--] SPENDS THE CHILD's ".." FRAGMENT.  The
     only fragment of [dp]'s register in the system lives inside [ip]'s own
     [ent_toks], at the index of [ip]'s "..", and [DirView.dir_dots_ix]
     beside [FsStateEra.ent_toks_era_borrow_at] is what names it.  That clause is guarded on [T_DIR] AND [di_nlink ip <> 0], and
     the liveness is the kernel's own [if (ip->nlink < 1) panic] at +0x7c --
     walked before the zeroing, like the two namecmp refusals.  In exchange
     the clause HANDS BACK [2 <= dir_nrec (di_size ip)], so the isdirempty
     loop never has to establish a record count.

   ==== THE REFERENCE LEDGER CLOSES AT TWO ON EVERY ARM =================

   [iref_slots 2] goes in and comes back out unchanged.  TWO, not sys_link's
   three, and the difference is structural: sys_link runs its SECOND resolve
   with [ip] already held, while sys_unlink's ONE resolve runs holding
   nothing.  The peak is therefore [max(the walker's own two, dp + ip)] = 2.

   * nameiparent takes two units and hands ONE back on success (the second
     pays for [dp]);
   * [dirlookup]'s found arm produces [ip] out of the remaining unit and its
     not-found arm returns that unit unspent;
   * every arm releases what it made -- [iunlockput(dp)] at [bad:],
     [iunlockput(ip)] then [iunlockput(dp)] on the isdirempty refusal, both
     on the success arm -- and the argstr arm makes no reference at all.

   ==== THE LOG LEDGER IS THE SET FORM, AND THE ZEROING PAYS FOR THE TAIL =

   begin_op mints [LogInv.log_op g MAXOPBLOCKS] = ten units and end_op
   retires whatever is left, so nothing log-shaped crosses this interface.
   The whole ledger is machine-checked in [SysUnlinkBudget.v]; three facts
   about it, because they decide the contract's premises:

   * ONE WALK, AND IT RUNS FIRST.  Nothing is held while [nameiparent] runs,
     so the ledger below it is parameterised by ONE reported boolean and
     enters at nine or ten -- never sys_link's seven.  The COUNTED walker is
     hopeless here for sys_chdir's reason: [(L+1) * iput_units] demands
     twelve of the ten at a three-component path.
   * THE ZEROING PAYS FOR THE WHOLE TAIL.  [SpecWritei.wi16_post]'s
     MEMBERSHIP TRIO at [tot = 16] puts [IBLOCK dp] in the op's set, so both
     the T_DIR [iupdate(dp)] and the [iunlockput(dp)] behind it run
     CREDITED.  Only [ip]'s own flush is uncredited, and it has to be:
     [dirlookup] and the isdirempty loop are pure reads, so nothing logs
     [IBLOCK ip] before it.  Relaying [wi16_spend] ALONE busts the worst
     corner by one -- [SysUnlinkBudget.su_ok_busts_without_the_membership_trio].
   * NO CORRELATION CLAUSE IS NEEDED.  [su_ok_uncorrelated] closes the T_DIR
     arm at [crb = false] together with [w1 = true] -- the nine-unit,
     uncredited-bitmap corner [SysLinkBudget.sl_corr] exists to exclude --
     and [su_ok_corner_is_exact] says it lands there at EXACTLY
     [iput_units].

   ==== WHAT ITS CALLER MUST HOLD ======================================

   [eb = true] is nameiparent's premise, inherited verbatim.  The
   [trap_csrs_ext] / [cpu_claim_ext] complement is threaded anyway,
   uniformly with begin_op / ilock / writei / iupdate / iunlockput / end_op,
   and is [emp] there.

   THE CROSSING IS THE LITERAL [true]: this function parks in every one of
   its ten distinct callees, so it may return on a hart other than the one
   it was called on.

   THE BITMAP IS NOT MONOTONE, in either direction: the zeroing [writei] can
   ALLOCATE (its contract cannot refute an allocating write even though the
   record it overwrites is inside the directory's existing size) and every
   [iunlockput] can FREE (itrunc, under a link-count-zero inode -- which is
   exactly what a successful unlink of the last link produces); the bitmap
   is an invariant, so the contract says nothing about it.

   DETERMINISM: none is claimed, and none is available.  Which of the six
   arms runs is a function of the FILE SYSTEM and of the user's path, and no
   caller of this contract knows any of that.  The postcondition is the
   honest disjunction on the returned a0.

   ==== ONE CONTRACT ====================================================

   [Module Type SYSUNLINK] is sys_unlink's only seal.  Its body is the
   whole-function FRAME below plus ONE caller INPUT ([unlink_au_pre], the
   atomic-update bundle) and ONE armed OUTPUT ([unlink_arms], keyed on the
   returned a0).  The landed return blanket [sys_unlink_ret] is a
   consequence of the arms ([unlink_arms_ret]) rather than a second
   conjunct, because the arms already split on the two words a0 can hold.
   There is no stable corollary and no parallel form.

   THERE IS ONE RETURN CONTINUATION, [sys_unlink_closer], and it takes the
   armed post [ARMS] where a blanket-only reading would put
   ⌜sys_unlink_ret⌝ -- which the arms imply.  It is named rather than
   spelled inline for optimization.md's reason ("Seal a whole-function
   proof's continuation"): inline it is fifteen rows, and a mid-walk dump
   of [Delta] measured it at 879 printed characters -- 7.5 % of the Iris
   context inside W3 and 13-15 % inside W5, at EVERY step of the walk, in
   every block lemma, plus one more copy inside each block's own seam
   continuation.  It stays TRANSPARENT on purpose (same section's rule 1):
   the tails apply it with [iApply ("Hcont" $! ...)], which unifies through
   a transparent constant and fails through an opaque one.  It is defined
   OUTSIDE any [Section] because it is a premise of the contract below and
   its rows are applied at the hart the caller picks.

   ==== WHAT THE CALLER HANDS IN =======================================

   [unlink_au_pre] is the one-shot bundle of this syscall's linearization
   instants, at the commit mask [appE]: the nameiparent PARENT-PREFIX walk
   premise ([FsAbsEraMknod.npar_walk_pre_era], reused verbatim -- it is
   nameiparent-generic) and [SysUnlinkDefs]'s four commits.  That file's
   header carries the delta's two-instant shape, [unl_pre]'s side
   conditions and why the pair reads as one delta anyway.

   ==== THE ARMS ========================================================

   ret 0  -- [unlink_post_ok]: the fetched path (existential, as always:
             no premise can pin user bytes), the cursor [P Lp d] at the
             parent, [unl_pre] restated purely at instant 1 beside the
             caller's own receipts [Fent]/[Ftgt], the instant-2 target
             pin, the region bound on [t], and the two observation
             commits refunded (the found fact is subsumed by [unl_pre],
             so firing [Fex] would be a second receipt at an earlier
             instant).
   ret -1 -- [unlink_post_fail], residue returned per arm:
             (i)   nothing fs-visible happened (argstr failed): the
                   whole bundle back unspent;
             (ii)  the walk died at hop [k]: [npar_walk_dead_era]'s
                   refund shape, all four commits back;
             (iii) the walk delivered the parent ([P Lp d] back, both
                   delta commits back) and the transaction refused:
                   (a) THE NAME IS A DOT -- refused BY NAME, before any
                       lookup: a PURE fact about the fetched string
                       ([last (path_elems pl)] is [DOT] or [DOTDOT]),
                       both observation commits refunded (the kernel
                       looked at nothing abstract);
                   (b) GONE -- dirlookup ran and MISSED: the miss
                       observation [Fmiss] FIRED at the instant, with
                       the parent's row and the absent name stated
                       purely beside it;
                   (c) DIR NON-EMPTY -- dirlookup FOUND [t] and
                       isdirempty refuted emptiness: the found
                       observation [Fex] FIRED, at the instant where
                       BOTH locks are held, so the same [av] purely
                       carries the parent's row, the entry, the
                       target's dir row and its non-dots witness;
                   (d) no abstract observation to report -- the k = Lp
                       deaths (namex's type test and nlink guard at the
                       parent's own level, and "unlink of /"), with both
                       observation commits refunded.  -1 deliberately
                       does not say which arm (DETERMINISM: none).

   ==== NOTHING ABOUT DURABILITY =======================================

   No durable clause of any kind appears below (design/fs-syscall-specs.md
   section 5); the per-syscall certificates are [FsDurSyscall]'s and the
   composition is the consumer's.
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
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Require Import SysUnlinkDefs.  (* THE STATEMENT LEAF: the delta's side
                                    conditions and the four commits *)
Require Import PathElems.       (* [path_elems], [SLASH] *)
Require Import FsTree.          (* [fname], [DOT], [DOTDOT] *)
Require Import FsBytesGamma.    (* [fs_gamma_L]: the live Γ *)
Require Import SysMknodDefs.  (* [npar_elems]                  *)
Require Import FsAbsEraMknod.   (* the era walk-premise pair, reused
                                   verbatim (nameiparent-generic) *)
Require Import FsAbsMknodFire.  (* [dlookup_commit_at]; the [_at] mold *)
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import PieceFam.        (* [pfam]: a one-shot piece's receipt beside its refund *)
Require Import FsAbsDefs.           (* LAST (FsAbs's own rule) *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* sys_unlink's own frame is 240 bytes -- THIRTY slots ([c.addi16sp sp,-240]
   at +0x00) -- over its deepest callee, nameiparent (104).  Every other
   callee fits under that: dirlookup 90, readi 78, writei 78, iunlockput 64,
   argstr 60, end_op 58, ilock 44, iupdate 44, begin_op 26, namecmp 4,
   memset 2. *)
Notation K_sys_unlink := (144%nat) (only parsing).
(* THE REFERENCE ALLOWANCE.  Two, and TWO is what the single resolve buys:
   see the header's reference ledger, and [SysUnlinkBudget]'s section 6. *)
Definition sys_unlink_slots : nat := 2%nat.

(* sys_unlink's result, as the honest disjunction on a0.  Unlike sys_link
   there is no shared [c.mv a0,a5]: each arm writes its own literal with a
   [c.li] -- 0 at +0xd8 on the success arm, -1 at +0xe6 (ARM B), +0x164
   ([bad:]) and +0x170 (ARM A). *)
Definition sys_unlink_ret (r : mword 64) : Prop :=
  r = (mword_of_int (-1) : mword 64) \/ r = (zero_reg : mword 64).
(* THE RETURN CONTINUATION, NAMED ONCE, AND IT TAKES THE ARMED POST.
   [ARMS] sits where a blanket-only reading would put ⌜sys_unlink_ret⌝ --
   which the arms imply ([unlink_arms_ret]), so there is one closer and not
   two.  Why it is named at all, and why it is transparent and outside every
   [Section], is in the header's ONE CONTRACT block. *)
Definition sys_unlink_closer
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (gf : gname) (pj : mword 64) (pid : mword 32) (U : ustate)
    (m : regfile) (ret_tgt : mword 64) (K : nat) (eb b : bool)
    (lks : gset string) (dqb dqs dqbs : dfrac)
    (ARMS : mword 64 -> iProp Σ)
 : iProp Σ :=
  (* THE IMAGE DOES NOT MOVE.  This syscall only READS user memory (argstr,
     through fetchstr and copyinstr); the pages it faults in on the way were
     already in the block's view, as lazy pages reading 0, so vmfault does
     not move it either.  Only the DESCRIPTOR grows, and the block comes
     back at the image it was handed. *)
  (∀ (mf : regfile) (P' : uptd),
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
      sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
      (* NO ORDERING on the free pool: the zeroing's writei can ALLOCATE and
         every iunlockput can FREE (itrunc).  See the header. *)
      (* the allowance, whole: see the header's reference ledger *)
      iref_slots sys_unlink_slots -∗
      (* the process block, at the same everything but the page table *)
      proc_priv gf pj pid (us_upt U P') -∗
      (* the armed post on the returned a0 (implies [sys_unlink_ret],
         through [unlink_arms_ret]) *)
      ARMS (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang))%I.

(* ===================================================================== *)
(*  THE BUNDLE AND THE ARMS                                               *)
(* ===================================================================== *)

Section SysUnlinkArms.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  (* Everything the caller hands in, at the commit mask [appE].  The walk
     premise is [FsAbsEraMknod.npar_walk_pre_era]
     REUSED VERBATIM (it is nameiparent-generic -- the one-shot
     ∀ pl r with only the SLASH -> ROOTINO tie, the hop family at the
     era lend over the parent prefix [npar_elems pl]; it is what
     [FsAbsStart.ep_start] instantiates to at the fetched string). *)
  Definition unlink_au_pre Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fent : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Ftgt : pfam Σ (aview -> Z -> iProp Σ))
      (Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fmiss : pfam Σ (aview -> Z -> fname -> iProp Σ)) : iProp Σ :=
    (npar_walk_pre_era γfs cw P Pmiss
     ∗ pf_at (uent_commit_at Γ appE) Fent
     ∗ pf_at (utgt_commit_at Γ appE) Ftgt
     ∗ pf_at (dlookup_commit_at Γ appE) Fex
     ∗ pf_at (dmiss_commit_at Γ appE) Fmiss)%I.

  (* ret 0: the fetched path, the cursor at the parent, [unl_pre]
     restated purely at instant 1, BOTH fired receipts, the instant-2
     pin on the target's row (its lock is held across the gap), the
     region bound on the target, and the two observation commits
     refunded. *)
  Definition unlink_post_ok Γ (P : nat -> Z -> iProp Σ)
      (Fent : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Ftgt : pfam Σ (aview -> Z -> iProp Σ))
      (Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fmiss : pfam Σ (aview -> Z -> fname -> iProp Σ)) : iProp Σ :=
    (∃ (pl : list (bv 8)) (av0 av1 : aview) (d t : Z) (nm : fname)
       (ents : gmap fname Z) (nl : nat) (a : anode),
       ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
       ⌜unl_pre av0 d nm ents nl t a⌝ ∗
       ⌜0 < t < 16 * Z.of_nat icfg_nib⌝ ∗
       ⌜av1 !! t = Some a⌝ ∗
       P (length (npar_elems pl)) d ∗
       pf_at (dlookup_commit_at Γ appE) Fex ∗
       pf_at (dmiss_commit_at Γ appE) Fmiss ∗
       Fent.(pf_recv) av0 d nm t ∗
       Ftgt.(pf_recv) av1 t)%I.

  (* ret -1: the header's fold -- (i) bundle back, (ii) walk dead,
     (iii) refused at the parent with the observation each refusal IS *)
  Definition unlink_post_fail Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fent : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Ftgt : pfam Σ (aview -> Z -> iProp Σ))
      (Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fmiss : pfam Σ (aview -> Z -> fname -> iProp Σ)) : iProp Σ :=
    (unlink_au_pre Γ γfs cw P Pmiss Fent Ftgt Fex Fmiss
     ∨ (∃ pl : list (bv 8),
          (npar_walk_dead_era γfs P Pmiss pl
             ∗ pf_at (uent_commit_at Γ appE) Fent
             ∗ pf_at (utgt_commit_at Γ appE) Ftgt
             ∗ pf_at (dlookup_commit_at Γ appE) Fex
             ∗ pf_at (dmiss_commit_at Γ appE) Fmiss)
          ∨ (∃ d : Z,
               P (length (npar_elems pl)) d
               ∗ pf_at (uent_commit_at Γ appE) Fent
               ∗ pf_at (utgt_commit_at Γ appE) Ftgt
               ∗ ((* (iii-a) the name is a dot: refused BY NAME, before
                     any lookup -- pure, both observations refunded *)
                  (∃ nm : fname,
                     ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
                     ⌜nm = DOT \/ nm = DOTDOT⌝ ∗
                     pf_at (dlookup_commit_at Γ appE) Fex ∗
                     pf_at (dmiss_commit_at Γ appE) Fmiss)
                  ∨ (* (iii-b) gone: the miss observation FIRED *)
                  (∃ (av : aview) (nm : fname) (ents : gmap fname Z)
                     (nl : nat),
                     ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
                     ⌜arow_at av d (MkAnode (ADir ents) nl)⌝ ∗
                     ⌜ents !! nm = None⌝ ∗
                     Fmiss.(pf_recv) av d nm ∗
                     pf_at (dlookup_commit_at Γ appE) Fex)
                  ∨ (* (iii-c) dir non-empty: the found observation
                       FIRED, both rows pinned at the one instant *)
                  (∃ (av : aview) (t : Z) (nm : fname)
                     (ents est : gmap fname Z) (nl nlt : nat),
                     ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
                     ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ ∗
                     ⌜ents !! nm = Some t⌝ ∗
                     ⌜av !! t = Some (MkAnode (ADir est) nlt)⌝ ∗
                     ⌜~ dots_only est⌝ ∗
                     Fex.(pf_recv) av d nm t ∗
                     pf_at (dmiss_commit_at Γ appE) Fmiss)
                  ∨ (* (iii-d) no abstract observation to report: the
                       k = Lp deaths (parent-level type/nlink guards,
                       "unlink of /") -- everything back *)
                  (pf_at (dlookup_commit_at Γ appE) Fex ∗
                   pf_at (dmiss_commit_at Γ appE) Fmiss)))))%I.

  (* the armed disjunction the continuation receives, keyed on a0
     (implies the landed [sys_unlink_ret]) *)
  Definition unlink_arms Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fent : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Ftgt : pfam Σ (aview -> Z -> iProp Σ))
      (Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fmiss : pfam Σ (aview -> Z -> fname -> iProp Σ))
      (r : mword 64) : iProp Σ :=
    ((⌜r = (zero_reg : mword 64)⌝
      ∗ unlink_post_ok Γ P Fent Ftgt Fex Fmiss)
     ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝
        ∗ unlink_post_fail Γ γfs cw P Pmiss Fent Ftgt Fex Fmiss))%I.

  (* the return blanket, read off the arms: the pure conjunct
     [SpecSysUnlink.sys_unlink_closer] carries, implied *)
  Lemma unlink_arms_ret Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fent : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Ftgt : pfam Σ (aview -> Z -> iProp Σ))
      (Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fmiss : pfam Σ (aview -> Z -> fname -> iProp Σ)) (r : mword 64) :
    unlink_arms Γ γfs cw P Pmiss Fent Ftgt Fex Fmiss r ⊢ ⌜sys_unlink_ret r⌝.
  Proof.
    rewrite /unlink_arms /sys_unlink_ret.
    iIntros "[[%Hr _] | [%Hr _]]"; iPureIntro; [right | left]; exact Hr.
  Qed.

End SysUnlinkArms.

(* big-op bodies behind definitions: seal them (durable-notes;
   optimization.md, "a big-op body is the predictor"). *)
Global Typeclasses Opaque unlink_au_pre unlink_post_ok unlink_post_fail
  unlink_arms.

(* ===================================================================== *)
(*  THE WHOLE-FUNCTION FRAME, abstracted over the caller's bundle and the *)
(*  armed post.  There is no second body: this frame is the only one, and *)
(*  the body below instantiates it.                                       *)
(* ===================================================================== *)

Definition wp_sys_unlink_frame
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)      (* ftable, kalloc, printk   *)
    (gs : list gname) (j : nat) (gl : gname)     (* the running process *)
    (pd pav pu : mword 64)                       (* disk fabric + lock  *)
    (dqb dqs dqbs : dfrac)
    (v0 : mword 64)                              (* syscall argument 0  *)
    (pid : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (EXTRA : iProp Σ) (ARMS : mword 64 -> iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_unlink in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_unlink <= K)%nat ->
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  (* ---- the block-layer geometry ---- *)
  log_geom_ok fsc_cov fsc_logst ->
  0 < fsc_size <= BPB ->
  0 <= fsc_bmapstart ->
  fsc_bmapstart ∈ fsc_cov ->
  ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
  0 <= icfg_ist ->
  cov_below fsc_cov fsc_size ->
  bitmap_geom_ok fsc_cov fsc_logst fsc_bmapstart fsc_size ->
  ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
  (* mkfs's [ushort] geometry, the landed contract's premise verbatim *)
  16 * Z.of_nat icfg_nib <= 2 ^ 16 ->
  (* ---- balloc's out-of-blocks arm calls printk, not panic ---- *)
  printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* nameiparent's own premise, inherited *)
  eb = true ->
  (* argstr reads syscall argument 0 out of the trapframe page *)
  pv_tf (us_V U) !! tf_arg_idx 0 = Some v0 ->
  sie_cap_gpr KT1 m K b pj -∗
  (* entered with no lock held: depth pinned at zero *)
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
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
  (* ---- the inode cache, and the region the two flushes write ---- *)
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
  ic_sleeplocks fsc_ic -∗
  ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
  (* the sealed regime, riding [ireg_inv]'s channel (the landed
     contract's row and reason: this contract reaches iput's freezer) *)
  ireg_open -∗
  (* ---- the three superblock cells ---- *)
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  kalloc_env fsc_kalloc None -∗
  procs_inv gs -∗
  (* ---- the process, and the reference allowance the walk needs ---- *)
  iref_slots sys_unlink_slots -∗
  proc_priv γf pj pid U -∗
  (* ---- THE CALLER'S BUNDLE (the one addition to the premise list) ---- *)
  EXTRA -∗
  (* the return continuation, named: see [sys_unlink_closer] above.  The
     crossing is the literal [true]: sys_unlink parks in all ten callees. *)
  wp_next true pj (fun (CID : CpuId) =>
    sys_unlink_closer (CID := CID) γf pj pid U m ret_tgt K eb b lks
                      dqb dqs dqbs ARMS) -∗
  WP (Loop : expr riscv_lang).

(* THE CONTRACT.  The abstract state is read at the LIVE Γ,
   [fs_gamma_L fsc_fs] -- the gname tie to [ftop_body]'s authority is
   definitional ([FsAbs.ftop_gamma_top]). *)
Definition wp_sys_unlink_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)
    (gs : list gname) (j : nat) (gl : gname)
    (pd pav pu : mword 64)
    (dqb dqs dqbs : dfrac)
    (v0 : mword 64)
    (pid : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (P Pmiss : nat -> Z -> iProp Σ)
    (Fent : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
    (Ftgt : pfam Σ (aview -> Z -> iProp Σ))
    (Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
    (Fmiss : pfam Σ (aview -> Z -> fname -> iProp Σ)) :=
  let Γfs := fs_gamma_L fsc_fs in
  wp_sys_unlink_frame γf gs j gl pd pav pu dqb dqs dqbs
    v0 pid U m K eb b lks
    (unlink_au_pre Γfs fsc_fs (pv_cwi (us_V U)) P Pmiss Fent Ftgt Fex Fmiss)
    (unlink_arms Γfs fsc_fs (pv_cwi (us_V U)) P Pmiss Fent Ftgt Fex Fmiss).

(* ===================================================================== *)
(*  ONE MODULE TYPE                                                       *)
(* ===================================================================== *)

(* There is no parallel statement for the walk, the commits or the arms,
   and no second proof against the code.  No stable corollary is sealed:
   unlink retags BOTH the parent and the target, so both would refuse a
   client pin; the stable reading arrives with the tree layer's
   exclusivity fact, where [delta_unlink_split] makes the two instants one
   delta. *)
Module Type SYSUNLINK.
  Parameter wp_sys_unlink :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (dqb dqs dqbs : dfrac)
      (v0 : mword 64)
      (pid : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fent : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Ftgt : pfam Σ (aview -> Z -> iProp Σ))
      (Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fmiss : pfam Σ (aview -> Z -> fname -> iProp Σ)),
      wp_sys_unlink_body γf gs j gl pd pav pu dqb dqs dqbs
        v0 pid U m K eb b lks P Pmiss Fent Ftgt Fex Fmiss.
End SYSUNLINK.
