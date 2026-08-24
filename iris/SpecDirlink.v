(* SpecDirlink.v -- the public interface of dirlink.

     int
     dirlink(struct inode *dp, char *name, uint inum)
     {
       int off;
       struct dirent de;
       struct inode *ip;

       if((ip = dirlookup(dp, name, 0)) != 0){
         iput(ip);
         return -1;
       }
       for(off = 0; off < dp->size; off += sizeof(de)){
         if(readi(dp, 0, (uint64)&de, off, sizeof(de)) != sizeof(de))
           panic("dirlink read");
         if(de.inum == 0)
           break;
       }
       strncpy(de.name, name, DIRSIZ);
       de.inum = inum;
       if(writei(dp, 0, (uint64)&de, off, sizeof(de)) != sizeof(de))
         return -1;
       return 0;
     }

   170 bytes.  Geometry VERIFIED off CodeDirlink.v: [addi sp,sp,-80] /
   [addi s0,sp,80], so [&de = s0-80] ([addi s4,s0,-80] at +0x2a, and the
   [lhu a5,-80(s0)] free test at +0x42, the [sh s6,-80(s0)] inum store at
   +0x7c, the [addi a2,s0,-80] writei source at +0x84) and
   [&de.name = s0-78] ([addi a0,s0,-78] at +0x74, strncpy's destination);
   [li a2,14] at +0x70 is DIRSIZ; the callee at +0x78 is **strncpy**
   (0x80000dd6), not safestrcpy.  THREE registers are saved LAZILY (s1 at
   +0x1c, s3/s4 at +0x24/+0x26) and the two early exits skip their
   restores.

   The return value is computed BRANCHLESSLY at +0x90..+0x96:
   [addi a0,a0,-16; sltu a0,zero,a0; subw a0,zero,a0], i.e.
   [a0 = -(writei(...) != 16)].

   ---- WHY THE CONTRACT IS THE UNION OF THREE ---------------------------

   dirlink is the campaign's widest precondition: it calls dirlookup (hence
   readi, namecmp and iget), iput on the found arm, and readi/strncpy/writei
   on the other.  So it threads dirlookup's bundle, writei's log +
   inode-region + bitmap bundle, and iput's itrunc geometry, all at once.
   It runs INSIDE A TRANSACTION (writei's bmap can allocate).

   TWO PREMISES ARE QUANTIFIED OVER RECORDS RATHER THAN NAMED, because the
   record dirlookup stops at is not known until it stops:

   - [DirView.dir_inums_ok] -- iget's argument bound (see SpecDirlookup.v).
     Since fs-icache.md §15(a) a caller gets it out of the icache: it is
     the conjunct [DirView.dir_ok icfg_nib dn data] riding in
     [IcacheEscrow.ic_loaded];
   - [ireg_blocks_ok] -- iput's [IBLOCK inum inodestart] membership facts,
     stated for EVERY inum the region covers rather than for the one child.
     That is strictly the better shape: it is a fact about the superblock
     layout, provable once, instead of a fact about a directory's contents.

   ---- THE GRANULARITY PREMISE IS GONE (fs-icache.md §15(b)) -----------

   [16 | di_size dn] used to be a premise here too, refuting
   panic("dirlink read") at +0x60 (the [bne a0,s3] at +0x3e).  It is not a
   system invariant -- dirlink's OWN short-write arm is what breaks it (see
   the APPEND arm below: on [tot < 16] the new size is [16*k0 + tot]) -- so
   the short-readi turn is now a LIVE panic arm, discharged with
   [SpecPanic]'s own contract, and no caller owes granularity.  A dirlink on a
   directory a previous short write corrupted therefore PANICS rather than
   returning; that is what the C does, and it is the honest post-state.

   ---- THE ARMS ---------------------------------------------------------

   FOUND (the name is already there): a0 = -1, the directory's data, block
   map and metadata are UNCHANGED, the child reference dirlookup minted has
   been spent by iput ([used' <= used], iput's spend-at-most budget), and
   the ledger unit comes back.

   APPEND: [dir_first data nrec s = None], and writei ran at
   [off = 16 * dir_slot data nrec] -- the first FREE record, or [nrec]
   itself when every record is live, which is where the scan's own [s1]
   lands.  TWO failures answer [a0 = -1 /\ tot < 16]: a SHORT WRITE (bmap
   out of blocks), and writei's OWN -1 return.  The second is the FULL
   DIRECTORY and nothing else -- [off <= size] because the slot is at most
   [nrec], so writei's first reason ([size < off]) is dead, and its second
   ([MAXFILE*BSIZE < off + 16]) forces [off = size = MAXFILE*BSIZE], since
   [off] and [MAXFILE*BSIZE] are both multiples of sixteen and
   [size <= MAXFILE*BSIZE].  It returns with EVERYTHING unchanged at
   [tot = 0], which is what this arm's [tot = 0] corner already says, so it
   needs no arm of its own: [wi_dinode] is the IDENTITY there (the append
   offset is in range, so the size does not move, and the map is the one
   [di_addrs] already names).

   (Until D₀-a this contract carried a premise [size + 16 <= MAXFILE*BSIZE]
   that killed writei's -1 return outright.  It was UNSUPPLIABLE: it is a
   fact about [dp], the record nameiparent finds at RUN TIME, which no
   caller's contract has a word for -- and dirlink itself destroys the
   proposition by growing the directory, so it is not even preservable.  See
   projects/fs-sysfile.md, the eleventh stop.)

   On [tot = 16] the window holds [dirent_bytes (de_of_name inum s)] --
   strncpy NUL-pads, so the stored record IS [DirentEnc.de_of_name] -- and
   the size is raised by writei's own [wi_dinode].

   ---- THE RANGE CLAUSE IS EXACT (fs-icache.md §15.1(i), retrofitted) ----

   writei's postcondition concedes a DISTURBED REGION of up to BSIZE
   unspecified bytes above the written window, because a user copy that
   faults part-way is committed without advancing [tot].  dirlink writes
   from a KERNEL buffer ([user = false]), where either_copyin cannot fail
   at all, and SpecWritei now says so: [user = false -> dist = 0].  So the
   clause below is TWO-way, not three-way, and the third arm -- the SHORT
   write, [tot < 16] -- differs from the old file in exactly the [tot]
   bytes it wrote and NOWHERE ELSE.

   That is what a writer needs to re-park [DirView.dir_ok] over a
   middle-slot link: under the old clause the write could have clobbered
   up to 64 FOLLOWING records with arbitrary bytes and dir-wf was
   underivable (§15.1(i)).  [DirView.dir_ok_dirlink] is the derivation the
   tightened clause unlocks; create (fs-sysfile S5) is its first caller.

   ---- THE LINKED INUM'S RANGE PREMISE ---------------------------------

   [bv_unsigned inum < 16 * nib] on the mword-16 argument is NOT used by
   dirlink's own proof -- the [sh] stores sixteen bits whatever they are.
   It is here for the WRITER: [dir_ok] over the new directory needs every
   live record's inum inside the inode region, and the record dirlink just
   stored carries [inum].  (On a one-byte short write the stored halfword
   is [inum mod 256], which the premise still bounds -- the free slot's
   old high byte is zero.  See [dir_ok_dirlink].)  Stating it now keeps
   S5 from having to reopen this contract.  It is free for every caller:
   create's inum comes from ialloc, whose payout carries exactly this
   bound.

   NOTE ON THE NAME.  [s] is DEFINED as [bname 14 fn], the canonical view of
   the caller's own buffer, so the design's two extra caller obligations
   ("length s <= 14", "nonul s") are NOT premises: they are
   [DirentEnc.bname_length_le] and [DirentEnc.cut_nul_nonul], free.  What
   makes the stored record exactly [de_of_name inum s] is that strncpy's
   post ([SpecStrncpy.snc_post]) forces [bview 14 h = name_pad (bname 14 fn)]
   on both of its arms -- [DirView.snc_bview] is that step.

   THE BUDGET.  writei's [wi_cost off 16] is SEVEN whenever [16 | off]: the
   sixteen bytes never straddle a block, because 1024 = 64*16.  iput wants
   three.  So one constant, [dirlink_units = 7], covers both arms, and the
   postcondition is spend-at-most -- and that is what the COUNTED contract
   takes.

   THE SET-FORM CONTRACT TAKES [dl_need] INSTEAD, and it has to.  Seven is
   not a bound create can meet: its mkdir chain runs its second and third
   [dirlink]s with SIX and FIVE units in hand, so the constant makes the
   whole allocate half unprovable at every path length.  [dl_need crb ind]
   is what the call really wants -- the append arm's [wi16_need] or the
   found arm's [iput_units], whichever is larger -- and it is FOUR wherever
   the append stays inside the directory's direct blocks, which is every
   dirlink create makes on the CHILD.  The two booleans are not new
   parameters: they are [dl16_post]'s own [crb] and [ind], read off the
   entry set and the append slot, so the premise says exactly what the
   postcondition already accounts.                                        *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import ProcDefs.  (* [proc_priv_bare] *)
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import KernelDataInv.
Require Import SpecPrintk.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import DirView.
Require Import DirLinks.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import SpecBmap.
(* [iput_units], for [dl_need]: the found arm spends an iput and the set-form
   premise has to dominate it.  SpecIput requires no Spec file, so this adds
   no cycle. *)
Require Import SpecIput.
Require Import SpecWritei.
Require Import SpecDirlookup.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

Local Open Scope Z_scope.

(* dirlink's own frame is 80 bytes (10 slots); its deepest callee is
   dirlookup (90); writei wants 78.

   90, and dirlookup's dominant chain is now bmap's, not copyout's: printk's
   real stack need (48, printk_stack) dominates bmap (64), which dominates
   balloc's out-of-blocks arm (58), which dominates bmap's own callers,
   readi (78) and dirlookup (90) -- SpecReadi.v / SpecDirlookup.v have the
   arithmetic.  writei also grew (78, dominated by the same bmap chain, not
   the copyout one), but stays under dirlookup, so dirlookup alone still
   fixes this number: 10 + 90 = 100. *)
Notation K_dirlink := (110%nat) (only parsing).
(* writei's [wi_cost off 16] at a 16-aligned [off] (= 7), which dominates
   iput's 3. *)
Definition dirlink_units : nat := 7%nat.

(* ---- WHAT A dirlink ACTUALLY SPENDS, AND WHAT IT ACTUALLY NEEDS.
   These two were [CreateBudget]'s, and they moved here for the reason
   [SpecWritei.wi16_spend] / [wi16_need] moved to their own seam: the
   contract now EXPOSES the figure, so the contract has to own it.
   [dl_spend] IS [wi16_spend] -- dirlink's one writei is the sixteen-byte
   window, and dirlookup, readi and the free-slot scan log nothing. *)
Definition dl_spend (crb crd cru al ind : bool) : nat :=
  wi16_spend crb crd cru al ind.

Definition dl_need (crb ind : bool) : nat :=
  Nat.max (wi16_need crb ind) iput_units.

Lemma dl_need_values :
  dl_need false false = 4%nat /\ dl_need true false = 4%nat /\
  dl_need true true = 5%nat /\ dl_need false true = 6%nat.
Proof. vm_compute. lia. Qed.

(* THE THREE READINGS THE PROOF USES.  Its three callees want, in order:
   dirlookup NOTHING, writei [wi_cost_bmonly (16*k0) 16] = four, and the
   found arm's iput [iput_units] = three -- and [dl_need] dominates both
   numbers at every pair of booleans, which is what makes the relaxed
   premise still sufficient. *)
Lemma dl_need_le (crb ind : bool) : (dl_need crb ind <= dirlink_units)%nat.
Proof. destruct crb, ind; vm_compute; lia. Qed.

Lemma dl_need_iput (crb ind : bool) : (iput_units <= dl_need crb ind)%nat.
Proof. unfold dl_need. lia. Qed.

Lemma dl_need_wi (crb ind : bool) : (4 <= dl_need crb ind)%nat.
Proof. destruct crb, ind; vm_compute; lia. Qed.

(* ...AND THE TWO MONOTONICITIES A CALLER DISCHARGES ITS PREMISE WITH.
   The need FALLS when the bitmap block is already in the op's set and
   RISES when the append runs through the indirect block, so a caller that
   knows neither may always supply [dl_need false true] = six, and a
   caller that knows the block is direct (create's links on the fresh
   child, whose slot 0 and slot 1 are both in block 0) supplies four. *)
Lemma dl_need_crb (crb ind : bool) : (dl_need crb ind <= dl_need false ind)%nat.
Proof. destruct crb, ind; vm_compute; lia. Qed.

Lemma dl_need_ind (crb ind : bool) : (dl_need crb ind <= dl_need crb true)%nat.
Proof. destruct crb, ind; vm_compute; lia. Qed.

(* ---- WHAT A *FAILING* APPEND SPENDS, AND WHY IT IS NOT [dl_spend].
   TWO routes reach [tot = 0].  The cheap one is writei's own -1 return (the
   FULL DIRECTORY, see the header): it answers before its loop and spends
   NOTHING.  The other is the bmap-out-of-blocks break -- writei's remaining
   break, the part-way [either_copyin], cannot happen here ([user = false])
   and is the one that log_writes before it leaves.  So the loop broke
   BEFORE its own [log_write] and the only log_writes that ran are bmap's
   (the bitmap block and the bzero'ed block, on the arm where it allocated
   one -- an allocated INDIRECT block followed by a failed data block is
   exactly that arm) and the trailing [iupdate]: [dl_spend] minus its
   data-block term, i.e. strictly less than the success arm.  That is the
   larger of the two, so it is the one the constant has to cover.

   THIS CONSTANT IS NOT THAT NUMBER, and the difference is the point.  The
   credit-aware figure IS available at zero now
   ([SpecWritei.wi16_spend_any], which is what the walk relays this clause
   from), but it is a figure and this clause is a CONSTANT -- and four is
   the honest maximum of that figure ([wi16_spend_le4]), reached by an
   allocating INDIRECT window at an unpaid bitmap block.  So no constant
   does better, and the per-call variation is what a caller would have to
   read instead.  Four buys create's non-directory [fail:] entry (+0xc4)
   and the first of its mkdir entries; the two INTERIOR mkdir entries run
   with six in hand and need three, which every DIRECT window (and every
   window at an already-logged bitmap block) provably gives --
   [CreateBudget.cr_fail_mkdir_closes] / [_ind] are that arithmetic.
   THE COLLAPSE HAS SINCE LANDED (D₀-b), so [dl16_post] no longer states
   this constant at all: its spend clause is the credit-aware figure,
   UNGUARDED, exactly as [SpecWritei.wi16_post] / [wi16_spend_any] are
   split.  What survives here is the constant itself, which
   [CreateBudget]'s [cr_fail_closes_at_zero] / [cr_fail_mkdir_at_zero_
   busts] are stated at, together with the two bridges a caller that
   prefers the constant to the figure still reaches it by. *)
Definition dl0_spend : nat := 4%nat.

(* the provenance, as an equation rather than as a comment: it IS writei's
   coarse allowance for a window that straddles one block. *)
Lemma dl0_spend_bmonly : dl0_spend = wi_cost_bmonly 0 16.
Proof. vm_compute. reflexivity. Qed.

(* ...and it dominates the credit-aware figure at every boolean, which is
   what lets the walk relay THIS clause off writei's honest one. *)
Lemma dl0_spend_covers (crb crd cru al ind : bool) :
  (wi16_spend crb crd cru al ind <= dl0_spend)%nat.
Proof. unfold dl0_spend. exact (wi16_spend_le4 crb crd cru al ind). Qed.

(* ...in the shape the walk relays it in: writei's honest [tot = 0] bound
   ([SpecWritei.wi16_spend_any]) landed on this clause's constant. *)
Lemma dl0_of_spend (ncount n' : nat) (crb crd cru al ind : bool) :
  ((ncount - wi16_spend crb crd cru al ind)%nat <= n')%nat ->
  ((ncount - dl0_spend)%nat <= n')%nat.
Proof.
  intro H. pose proof (dl0_spend_covers crb crd cru al ind). lia.
Qed.

Lemma dl0_spend_lt : (dl0_spend < dirlink_units)%nat.
Proof. vm_compute. lia. Qed.

(* ===================================================================== *)
(*  THE SIXTEEN-BYTE SEAM AT dirlink's OWN WINDOW (GR-3 stage 3).         *)
(*                                                                        *)
(*  dirlink's single [writei] call is [n = 16] at [off = 16 * k0], the     *)
(*  append slot -- EXACTLY the shape [SpecWritei.wi16_post] exposes, and   *)
(*  [CreateBudget.dl_spend] IS [wi16_spend], so create's ledger connects   *)
(*  with no bridge.  This is that fact re-stated at dirlink's binders.     *)
(*                                                                        *)
(*  THE CREDIT BOOLEANS ARE READ AT THE ENTRY SET [Sb], and that is not a  *)
(*  weakening: dirlookup's [readi] prefix and the free-slot scan LOG        *)
(*  NOTHING, so the set the writei call actually runs at IS [Sb].          *)
(*                                                                        *)
(*  GUARDED BY THE APPEND ARM ALONE -- [found = false] -- AND THEN SPLIT   *)
(*  THE WAY writei SPLITS IT, because create PRICES THE FAILING APPEND     *)
(*  TOO.  The old guard was [tot = 16], i.e. the success append: on every  *)
(*  route into create's [fail:] the only surviving budget clause was then  *)
(*  the counted [ncount - dirlink_units], and seven from the eight-or-nine *)
(*  create reaches its first dirlink with leaves less than [iput_units]    *)
(*  for the tail's first [iunlockput] -- create's failure arm was          *)
(*  UNPAYABLE ([CreateBudget.cr_fail_counted_busts]).  Nothing forced that *)
(*  guard, and nothing forces a [tot]-split at all:                       *)
(*                                                                        *)
(*    THE SPEND    -- UNGUARDED, the credit-aware figure, relayed from     *)
(*                    [SpecWritei.wi16_spend_any].  One expression bounds  *)
(*                    every arm: the -1 return spends nothing, the bmap    *)
(*                    break leaves the data-block term unspent, and the    *)
(*                    success append spends the figure exactly.  A         *)
(*                    constant here ([dl0_spend]) would be four, and the   *)
(*                    two INTERIOR mkdir entries reach their dirlink with  *)
(*                    six in hand against an [iput_units] of three -- so   *)
(*                    the per-call VARIATION, not the maximum, is what     *)
(*                    they need ([CreateBudget.cr_fail_mkdir_closes]).     *)
(*    THE ATOMICITY -- [tot = 0 \/ tot = 16], relayed VERBATIM from        *)
(*                    [SpecWritei.wi16_atomic] at this call's single-block *)
(*                    window ([dl_wi_blocks]).  It is not a convenience:   *)
(*                    create's [fail:] arm must re-park the PARENT's       *)
(*                    [DirLinks.dir_links] before it can [iunlockput] the  *)
(*                    parent, and at [0 < tot < 16] there is no re-park at *)
(*                    all -- [dir_link_at_dirlink] wants a ticket for the  *)
(*                    record the partial write left ([2 <= tot], and the   *)
(*                    only [ilink] in hand is the one the [fail:] flush    *)
(*                    spends), [dir_links_dirlink_nop] wants [tot = 0],    *)
(*                    and at [tot = 1] the record goes live at [inum mod   *)
(*                    256], for which no fragment exists anywhere          *)
(*                    (DirLinks' S5i note).  That is not a proof gap: a    *)
(*                    live record naming an inode whose [nlink] the arm    *)
(*                    then zeroes would BREAK (L1), so the arm is true     *)
(*                    only where the write was all-or-nothing.  Writei's   *)
(*                    seven exits are why it always is.                    *)
(*    [0 < tot]    -- the MEMBERSHIP trio alone, and its guard is not      *)
(*                    inherited but forced: at [tot = 0] writei never      *)
(*                    log_wrote the target block, so nothing PUTS it in    *)
(*                    [Sb'] -- it is in there only if the caller had       *)
(*                    already logged it, which is [crd] and is the         *)
(*                    caller's fact, not this contract's.                  *)
(*                                                                        *)
(*  This mirrors [SpecWritei.wi16_post] / [wi16_spend_any] exactly, which  *)
(*  is what makes the relay two [exact]s.                                  *)
(*                                                                        *)
(*  The FOUND arm carries nothing beyond the counted net-zero clause -- it *)
(*  spends only iput, which create prices with [CreateBudget.ip_spend].    *)
(*                                                                        *)
(*  [k0] is the append slot, i.e. the body's own [let k0 := dir_slot data  *)
(*  nrec], taken as a parameter here for the same reason the arms take     *)
(*  [16 * k0]: it is a function of the ENTRY [data] and [dn], not of the   *)
(*  post's binders.                                                        *)
(* ===================================================================== *)
Definition dl16_post (bmapstart : Z) (dinum : mword 32) (inodestart : Z)
    (ncount n' k0 tot : nat) (found : bool) (bm bm' : blkmap)
    (Sb Sb' : gset Z) : Prop :=
  found = false ->
  let off := (16 * k0)%nat in
  let fbn := (off `div` BSIZE)%nat in
  let al := bmap_alloced bm bm' fbn in
  let ind := bmap_ind fbn in
  let crb := bool_decide (bmapstart ∈ Sb) in
  let crd := bool_decide (wi_tgt_blk bm' off ∈ Sb) in
  let cru := bool_decide (IBLOCK dinum inodestart ∈ Sb) in
  ((ncount - wi16_spend crb crd cru al ind)%nat <= n')%nat
  /\ (tot = 0%nat \/ tot = 16%nat)
  /\ ((0 < tot)%nat ->
        wi_tgt_blk bm' off ∈ Sb'
        /\ IBLOCK dinum inodestart ∈ Sb'
        /\ (al = true -> bmapstart ∈ Sb')).

(* iput's two block-membership premises, for EVERY inum the inode region
   covers rather than for the one child dirlookup happens to return.  See
   the header.

   HOISTED to [InodeInv.v] (fs-namei N5) once ialloc and ireclaim became
   its third and fourth consumers -- a Spec file must not require another
   function's Spec, and InodeInv is the lowest file that sees both
   [IBLOCK] and [log_region_set].  This transparent alias keeps every
   existing spelling ([ireg_blocks_ok ...] unqualified, and
   [SpecDirlink.ireg_blocks_ok ...] qualified) working unchanged; new
   contracts should name [InodeInv.ireg_blocks_ok] directly. *)
Definition ireg_blocks_ok (inodestart : Z) (nib : nat)
    (cov : gset Z) (logstart : Z) : Prop :=
  InodeInv.ireg_blocks_ok inodestart nib cov logstart.

(* [ic_sleeplocks] lived here, as a second, byte-identical copy of
   [SpecFileclose]'s.  Both are retired into [IcacheEscrow.ic_sleeplocks],
   beside [ic_tok], which is what they are built from.

   THIS FILE'S COPY IS THE ONE THAT MATTERED.  [FsReady.v] required
   *SpecDirlink* to reach it, and SpecDirlink reaches [ProcInv] through
   [SpecWritei] (writei takes the process block for its user-memory copy) --
   so one misplaced definition put the whole process layer inside the
   dependency cone of [fs_ready], and made the file system look as though it
   depended on process abstractions.  It does not.  See
   [IcacheEscrow.ic_sleeplocks]. *)

Definition wp_dirlink_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γi : gname)
    (cn : ic_names) (gtl : gname)                     (* the icache + itable *)
    (γa : gname) (γf : gname) (γpr : gname)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
    (bmapstart : Z) (size : Z) (dev : mword 32)
    (ip : mword 64) (dinum : mword 32)                (* the DIRECTORY       *)
    (bm : blkmap) (data : nat -> list (bv 8))
    (dn dn0 : dinode)
    (fn : nat -> bv 8)                                (* the caller's name   *)
    (inum : mword 16)                                 (* the LINKED inum     *)
    (ncount : nat)
    (pidv : mword 32) (dq dqd dqn dqs dqb dqbs dqf : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.dirlink in
  let pj := proc_addr j in
  let nb := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let nrec := dir_nrec (bv_unsigned (di_size dn)) in
  let s := bname 14 fn in
  let k0 := dir_slot data nrec in
  (K_dirlink <= K)%nat ->
  (* ---- dirlookup's premises (NO granularity -- see the header) ---- *)
  di_type dn = T_DIR ->
  bm_covers bm (bv_unsigned (di_size dn)) ->
  bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  dir_inums_ok data nrec nib ->
  (* ---- THE BORROWED LICENCE, RELAYED TO THE INNER dirlookup (R13(ii),
     fs-fragments.md §7.1/§7.5.6).  dirlink's own lookup is where the name
     it is about to link is checked for, and that lookup's [iget] on the
     FOUND arm needs a licence.  So the two things dirlookup borrows travel
     one level up: the pure disjunction (verbatim -- see SpecDirlookup's
     header for why it is a disjunction and not "the home is live"), and the
     ticket list, over the PRE-state and handed back VERBATIM on both arms.
     The record dirlookup's licence (c) wants is the one this contract
     already takes, [dinode_at γi dinum dn0]; its nonzero type follows from
     [Htype] and [di_type_stable] and costs no premise.  §20.18 ruling 1 is
     untouched: this is a BORROW, not an obligation -- no [dir_links]
     obligation at dirlink, and the re-park at the post-state stays exactly
     where it was, at the caller. ---- *)
  (bv_unsigned (di_nlink dn) <> 0
   \/ (s <> dot_name /\ s <> dotdot_name)) ->
  dir_orphan_clean dn data ->
  (* NO "THE APPEND FITS" PREMISE.  It used to sit here, killing writei's
     own -1 return; it was unsuppliable (see the header) and the return is
     routed through the [tot = 0] corner of the append arm instead. *)
  (* ---- writei's premises ---- *)
  (* TYPE STABILITY (fs-icache.md §19.6 Part 1, fs-sysfile S5d): writei's
     new premise, travelling.  dirlink's own [Htype] fixes [di_type dn] at
     T_DIR but says nothing about the region's stale [dn0]; the caller
     holds the two as ONE record ([IcacheEscrow.ic_loaded]'s single
     [dinode_at]) and discharges by [InodeRegion.di_type_stable_refl]. *)
  di_type_stable dn dn0 ->
  (* NLINK STABILITY (fs-icache.md §20.6, fs-sysfile S5f): the link
     ledger's twin of the premise above, travelling for the same reason --
     the record the REGION holds at the iupdate below is the stale [dn0].
     [InodeRegion.di_nlink_stable_refl] discharges it at any caller that
     holds the two as ONE record with a nonzero type. *)
  di_nlink_stable dn dn0 ->
  log_geom_ok cov logstart ->
  blkmap_wf cov logstart bm ->
  blk_holes_zero bm data ->
  di_addrs dn = bm_cells bm ->
  bv_unsigned (di_size dn) < 2 ^ 31 ->
  0 <= inodestart ->
  IBLOCK dinum inodestart ∈ cov ->
  ~ (IBLOCK dinum inodestart ∈ log_region_set logstart) ->
  bv_unsigned dinum < 16 * Z.of_nat nib ->
  (* ---- THE LINKED CHILD'S OWN RANGE (unused here, owed to the writer) ----
     the premise above is the DIRECTORY's inum; this one is the inum being
     linked, and it is what lets a caller re-park [DirView.dir_ok] over the
     record dirlink stores.  See the header. *)
  bv_unsigned inum < 16 * Z.of_nat nib ->
  bitmap_geom_ok cov logstart bmapstart size ->
  printk_gen_contract (kt := KT1) γpr γu γd ->
  (* ---- iput's premises (itrunc's geometry) ---- *)
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  cov_below cov size ->
  ireg_blocks_ok inodestart nib cov logstart ->
  (* ENOUGH BUDGET for either arm -- see the header *)
  (dirlink_units <= ncount)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = dp *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* a2 = inum, as a ZERO-extended halfword: the [sh s6,-80(s0)] at +0x7c
     stores exactly the low sixteen bits, and every caller's inum is a real
     inode number. *)
  m !!! Regidx (mword_of_int 12 : mword 5)
    = (zero_extend' 64 (inum : mword 16) : mword 64) ->
  (* PARKING PREMISE *)
  eb = true ->
  (* the order premise, at the LOWEST rank this cone touches; every
     higher one follows by [locks_below_mono]. *)
  locks_below lks "log" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  kernel_data -∗
  printk_env γpr γu γd -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  kalloc_env γa None -∗
  (* ---- THE LOCKED DIRECTORY ---- *)
  i_dev ip ↦₄{dqd} dev -∗
  i_inum ip ↦₄{dqf} dinum -∗
  inode_meta ip dn -∗
  inode_map γfs ip bm -∗
  inode_blocks γfs bm data -∗
  (* ---- THE CALLER'S 14-BYTE NAME BUFFER (namecmp's f, strncpy's src) ---- *)
  ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ[KT1]{dqn} fn i) -∗
  (* ---- the superblock cells and the bitmap ---- *)
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  bitmap_inv γfs bmapstart cov logstart size -∗
  (* ---- the inode region and the directory's own (stale) record ---- *)
  ireg_inv γi γfs inodestart nib -∗
  (* ...AND THE SEALED REGIME (iclaim-ledger.md §3.2, RULING B; §6′ RULING G).
     Persistent, borrowed and never spent; it rides the SAME channel
     [ireg_inv] does.  It is here because this contract reaches iput, whose
     free path FREEZES the inode, and §2.3's boot-shelter clause makes a
     freezer exhibit the regime it freezes under.  A runtime caller hands
     [SpecIput] the LEFT arm of its borrowed disjunction and discards what
     comes back; only ireclaim, which freezes before the seal is fired,
     lends [ireg_boot] instead. *)
  ireg_open -∗
  dinode_at γi dinum dn0 -∗
  (* ---- the caller's own pid cell ---- *)
  proc_priv_bare pj pidv Vpr -∗
  (* ---- the running-thread bundle and the disk fabric ---- *)
  procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  bslots 3 -∗
  (* ---- THE ICACHE ---- *)
  is_itable2 gtl cn γfs γi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn γfs γi cov logstart -∗
  ic_sleeplocks cn -∗
  iref_slot -∗
  (* the borrowed ticket list, over the PRE-state *)
  IcacheEscrow.dlinks γfs (bv_unsigned dinum) dn bm data -∗
  (* ---- THIS OPERATION'S RESERVATION ---- *)
  log_op γ ncount -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP,
     and a park moves the hart with interrupts off, so the crossing has
     nothing to do with SIE.  Spelled [b] the two coincide at the only
     instance the [eb = true] premise admits, which is why this went
     unnoticed; once [eb = false] is reachable the [b] form would promise
     the caller it comes back on the hart it called from. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (found : bool)
    (bm' : blkmap) (data' : nat -> list (bv 8)) (dn' dn0' : dinode)
    (n' : nat)
    (tot : nat),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      pc_is ret_tgt -∗
      (* ---- everything comes back, at the possibly-updated indices ---- *)
      i_dev ip ↦₄{dqd} dev -∗
      i_inum ip ↦₄{dqf} dinum -∗
      inode_meta ip dn' -∗
      inode_map γfs ip bm' -∗
      inode_blocks γfs bm' data' -∗
      ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ[KT1]{dqn} fn i) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      dinode_at γi dinum dn0' -∗
      proc_priv_bare pj pidv Vpr -∗
      bslots 3 -∗
      (* NET ZERO on the ledger: dirlookup's iget spends one and iput
         returns one on the found arm; nothing is spent on the other. *)
      iref_slot -∗
      (* ...and the borrow, back VERBATIM -- at the PRE-state's [dn]/[data],
         which is what R13(ii) admits and what the caller's own re-park
         movers ([DirLinks.dir_link_at_dirlink] and its siblings) take. *)
      IcacheEscrow.dlinks γfs (bv_unsigned dinum) dn bm data -∗
      (* at most [dirlink_units] gone, and none gained *)
      ⌜((ncount - dirlink_units)%nat <= n')%nat /\ (n' <= ncount)%nat⌝ -∗
      log_op γ n' -∗
      (* ---- THE TWO [inode_ok] CONJUNCTS A RE-PARKER NEEDS, AS
         PRESERVATIONS (fs-sysfile S5a finding 2; the cap, D₀-a repair 3b) --
         [InodeLock.inode_ok] has seven conjuncts and the arms below
         re-establish five of them ([blkmap_wf], [bm_covers],
         [di_addrs = bm_cells], [blk_holes_zero], and [di_type <> 0] through
         [dn' = wi_dinode dn ...]).  The other two are writei's own two
         preservation clauses (SpecWritei.v:661), relayed here VERBATIM,
         guard included, because NEITHER is recoverable at this seam:
         [InodeInv.inode_sized] because the range clause below is about
         [file_byte], a per-BYTE view that pins no block's LENGTH, and the
         SIZE CAP because the arithmetic that used to recover it
         ([16*k0 + tot <= size + 16], [ProofCreateParts.cr_size_cap]) needed
         "the append fits" -- the premise the eleventh stop retired.

         Relayed, the cap costs a caller nothing: the antecedent is about
         its OWN entry record, and it is a conjunct of the [inode_ok] the
         caller is about to rebuild.  Both are free inside [ProofDirlink]:
         writei hands them over, and the found arm has [dn' = dn],
         [data' = data]. *)
      ⌜bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
       bv_unsigned (di_size dn') <= Z.of_nat MAXFILE * Z.of_nat BSIZE⌝ -∗
      ⌜inode_sized data -> inode_sized data'⌝ -∗
      (* ---- THE TWO ARMS ---- *)
      ⌜if found
        then (* the name was already there: iput spent the child *)
          dir_first data nrec s <> None
          /\ mf !!! Regidx (mword_of_int 10 : mword 5)
             = (mword_of_int (-1) : mword 64)
          /\ bm' = bm /\ data' = data /\ dn' = dn /\ dn0' = dn0
          /\ tot = 0%nat
        else (* the append, through writei at [16*k0] *)
          dir_first data nrec s = None
          /\ blkmap_wf cov logstart bm'
          /\ blk_holes_zero bm' data'
          /\ di_addrs dn' = bm_cells bm'
          /\ bv_unsigned (di_size dn') < 2 ^ 31
          /\ bm_covers bm' (bv_unsigned (di_size dn'))
          /\ dn' = wi_dinode dn bm' (16 * k0)%nat tot
          (* THE FLUSHED RECORD, AS A PRESERVATION (D₀-a repair 3b).  The
             success and short-write arms run writei's trailing [iupdate],
             so the REGION's record becomes the metadata one and [dn0' = dn']
             outright; writei's own -1 return (the full directory -- see the
             header) runs no iupdate at all and answers [dn0' = dn0],
             [dn' = dn].  Nothing here relates [dn0] to [dn], so the honest
             clause is the implication -- and it is free for every caller,
             because a caller holds the two as ONE record
             ([IcacheEscrow.ic_loaded]'s single [dinode_at]; it is the same
             fact [InodeRegion.di_type_stable_refl] discharges the type
             premise from), and a caller that did not could not re-park
             either way. *)
          /\ (dn0 = dn -> dn0' = dn')
          /\ (tot <= 16)%nat
          (* THE RANGE CLAUSE: the record's bytes in the window and NOTHING
             ELSE.  writei's disturbed region is empty on the kernel arm --
             see the header, and fs-icache.md §15.1(i). *)
          /\ (forall x : nat,
                file_byte data' x
                = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat)
                  then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
                  else file_byte data x)
          (* the branchless return: 0 exactly when all sixteen went in *)
          /\ ((mf !!! Regidx (mword_of_int 10 : mword 5)
                 = (mword_of_int 0 : mword 64) /\ tot = 16%nat)
              \/ (mf !!! Regidx (mword_of_int 10 : mword 5)
                    = (mword_of_int (-1) : mword 64) /\ (tot < 16)%nat))⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  ...AND THE CONTRACT COMES IN TWO FORMS (fs-icache.md section 18       *)
(*  clause 1, writei's pattern verbatim).  [wp_dirlink_sconf] above is    *)
(*  the COUNTED form; this is the SET form, and the counted one is        *)
(*  DERIVED from it -- [log_op] IS [∃ Sb, log_opS] -- at whatever set the *)
(*  existential was hiding, so no existing caller moves.                  *)
(* ===================================================================== *)
Definition wp_dirlink_gen_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γi : gname)
    (cn : ic_names) (gtl : gname)                     (* the icache + itable *)
    (γa : gname) (γf : gname) (γpr : gname)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
    (bmapstart : Z) (size : Z) (dev : mword 32)
    (ip : mword 64) (dinum : mword 32)                (* the DIRECTORY       *)
    (bm : blkmap) (data : nat -> list (bv 8))
    (dn dn0 : dinode)
    (fn : nat -> bv 8)                                (* the caller's name   *)
    (inum : mword 16)                                 (* the LINKED inum     *)
    (ncount : nat) (Sb : gset Z)
    (pidv : mword 32) (dq dqd dqn dqs dqb dqbs dqf : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.dirlink in
  let pj := proc_addr j in
  let nb := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let nrec := dir_nrec (bv_unsigned (di_size dn)) in
  let s := bname 14 fn in
  let k0 := dir_slot data nrec in
  (K_dirlink <= K)%nat ->
  (* ---- dirlookup's premises (NO granularity -- see the header) ---- *)
  di_type dn = T_DIR ->
  bm_covers bm (bv_unsigned (di_size dn)) ->
  bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  dir_inums_ok data nrec nib ->
  (* ---- THE BORROWED LICENCE, RELAYED TO THE INNER dirlookup (R13(ii),
     fs-fragments.md §7.1/§7.5.6).  dirlink's own lookup is where the name
     it is about to link is checked for, and that lookup's [iget] on the
     FOUND arm needs a licence.  So the two things dirlookup borrows travel
     one level up: the pure disjunction (verbatim -- see SpecDirlookup's
     header for why it is a disjunction and not "the home is live"), and the
     ticket list, over the PRE-state and handed back VERBATIM on both arms.
     The record dirlookup's licence (c) wants is the one this contract
     already takes, [dinode_at γi dinum dn0]; its nonzero type follows from
     [Htype] and [di_type_stable] and costs no premise.  §20.18 ruling 1 is
     untouched: this is a BORROW, not an obligation -- no [dir_links]
     obligation at dirlink, and the re-park at the post-state stays exactly
     where it was, at the caller. ---- *)
  (bv_unsigned (di_nlink dn) <> 0
   \/ (s <> dot_name /\ s <> dotdot_name)) ->
  dir_orphan_clean dn data ->
  (* NO "THE APPEND FITS" PREMISE.  It used to sit here, killing writei's
     own -1 return; it was unsuppliable (see the header) and the return is
     routed through the [tot = 0] corner of the append arm instead. *)
  (* ---- writei's premises ---- *)
  (* TYPE STABILITY (fs-icache.md §19.6 Part 1, fs-sysfile S5d): writei's
     new premise, travelling.  dirlink's own [Htype] fixes [di_type dn] at
     T_DIR but says nothing about the region's stale [dn0]; the caller
     holds the two as ONE record ([IcacheEscrow.ic_loaded]'s single
     [dinode_at]) and discharges by [InodeRegion.di_type_stable_refl]. *)
  di_type_stable dn dn0 ->
  (* NLINK STABILITY (fs-icache.md §20.6, fs-sysfile S5f): the link
     ledger's twin of the premise above, travelling for the same reason --
     the record the REGION holds at the iupdate below is the stale [dn0].
     [InodeRegion.di_nlink_stable_refl] discharges it at any caller that
     holds the two as ONE record with a nonzero type. *)
  di_nlink_stable dn dn0 ->
  log_geom_ok cov logstart ->
  blkmap_wf cov logstart bm ->
  blk_holes_zero bm data ->
  di_addrs dn = bm_cells bm ->
  bv_unsigned (di_size dn) < 2 ^ 31 ->
  0 <= inodestart ->
  IBLOCK dinum inodestart ∈ cov ->
  ~ (IBLOCK dinum inodestart ∈ log_region_set logstart) ->
  bv_unsigned dinum < 16 * Z.of_nat nib ->
  (* ---- THE LINKED CHILD'S OWN RANGE (unused here, owed to the writer) ----
     the premise above is the DIRECTORY's inum; this one is the inum being
     linked, and it is what lets a caller re-park [DirView.dir_ok] over the
     record dirlink stores.  See the header. *)
  bv_unsigned inum < 16 * Z.of_nat nib ->
  bitmap_geom_ok cov logstart bmapstart size ->
  printk_gen_contract (kt := KT1) γpr γu γd ->
  (* ---- iput's premises (itrunc's geometry) ---- *)
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  cov_below cov size ->
  ireg_blocks_ok inodestart nib cov logstart ->
  (* ENOUGH BUDGET for either arm, AT THE HONEST FIGURE (see the header).
     [crb] and [ind] are [dl16_post]'s own two booleans, read off the entry
     set and the append slot -- so this premise is not a new interface, it
     is the postcondition's accounting stated as an entry condition.  A
     caller with nothing to claim supplies [dl_need_crb]/[dl_need_ind] and
     is back at six; the COUNTED contract supplies [dl_need_le] and is back
     at seven, which is why its own statement did not move. *)
  (dl_need (bool_decide (bmapstart ∈ Sb))
           (bmap_ind ((16 * k0) `div` BSIZE)%nat) <= ncount)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = dp *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* a2 = inum, as a ZERO-extended halfword: the [sh s6,-80(s0)] at +0x7c
     stores exactly the low sixteen bits, and every caller's inum is a real
     inode number. *)
  m !!! Regidx (mword_of_int 12 : mword 5)
    = (zero_extend' 64 (inum : mword 16) : mword 64) ->
  (* PARKING PREMISE *)
  eb = true ->
  (* the order premise, at the LOWEST rank this cone touches; every
     higher one follows by [locks_below_mono]. *)
  locks_below lks "log" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  kernel_data -∗
  printk_env γpr γu γd -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  kalloc_env γa None -∗
  (* ---- THE LOCKED DIRECTORY ---- *)
  i_dev ip ↦₄{dqd} dev -∗
  i_inum ip ↦₄{dqf} dinum -∗
  inode_meta ip dn -∗
  inode_map γfs ip bm -∗
  inode_blocks γfs bm data -∗
  (* ---- THE CALLER'S 14-BYTE NAME BUFFER (namecmp's f, strncpy's src) ---- *)
  ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ[KT1]{dqn} fn i) -∗
  (* ---- the superblock cells and the bitmap ---- *)
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  bitmap_inv γfs bmapstart cov logstart size -∗
  (* ---- the inode region and the directory's own (stale) record ---- *)
  ireg_inv γi γfs inodestart nib -∗
  (* ...AND THE SEALED REGIME (iclaim-ledger.md §3.2, RULING B; §6′ RULING G).
     Persistent, borrowed and never spent; it rides the SAME channel
     [ireg_inv] does.  It is here because this contract reaches iput, whose
     free path FREEZES the inode, and §2.3's boot-shelter clause makes a
     freezer exhibit the regime it freezes under.  A runtime caller hands
     [SpecIput] the LEFT arm of its borrowed disjunction and discards what
     comes back; only ireclaim, which freezes before the seal is fired,
     lends [ireg_boot] instead. *)
  ireg_open -∗
  dinode_at γi dinum dn0 -∗
  (* ---- the caller's own pid cell ---- *)
  proc_priv_bare pj pidv Vpr -∗
  (* ---- the running-thread bundle and the disk fabric ---- *)
  procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  bslots 3 -∗
  (* ---- THE ICACHE ---- *)
  is_itable2 gtl cn γfs γi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn γfs γi cov logstart -∗
  ic_sleeplocks cn -∗
  iref_slot -∗
  (* the borrowed ticket list, over the PRE-state *)
  IcacheEscrow.dlinks γfs (bv_unsigned dinum) dn bm data -∗
  (* ---- THIS OPERATION'S RESERVATION ---- *)
  log_opS γ ncount Sb -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP,
     and a park moves the hart with interrupts off, so the crossing has
     nothing to do with SIE.  Spelled [b] the two coincide at the only
     instance the [eb = true] premise admits, which is why this went
     unnoticed; once [eb = false] is reachable the [b] form would promise
     the caller it comes back on the hart it called from. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (found : bool)
    (bm' : blkmap) (data' : nat -> list (bv 8)) (dn' dn0' : dinode)
    (n' : nat) (Sb' : gset Z)
    (tot : nat),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      pc_is ret_tgt -∗
      (* ---- everything comes back, at the possibly-updated indices ---- *)
      i_dev ip ↦₄{dqd} dev -∗
      i_inum ip ↦₄{dqf} dinum -∗
      inode_meta ip dn' -∗
      inode_map γfs ip bm' -∗
      inode_blocks γfs bm' data' -∗
      ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ[KT1]{dqn} fn i) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      dinode_at γi dinum dn0' -∗
      proc_priv_bare pj pidv Vpr -∗
      bslots 3 -∗
      (* NET ZERO on the ledger: dirlookup's iget spends one and iput
         returns one on the found arm; nothing is spent on the other. *)
      iref_slot -∗
      (* ...and the borrow, back VERBATIM -- at the PRE-state's [dn]/[data],
         which is what R13(ii) admits and what the caller's own re-park
         movers ([DirLinks.dir_link_at_dirlink] and its siblings) take. *)
      IcacheEscrow.dlinks γfs (bv_unsigned dinum) dn bm data -∗
      (* at most [dirlink_units] gone, and none gained *)
      ⌜((ncount - dirlink_units)%nat <= n')%nat /\ (n' <= ncount)%nat⌝ -∗
      (* THE SET ONLY GROWS.  No ceiling -- SpecWritei's header's reason
         applies verbatim: no obligation anywhere consumes one. *)
      ⌜Sb ⊆ Sb'⌝ -∗
      (* ...and on the success-append arm, the credit-aware spend and the
         membership trio create's next call needs.  ADDITIVE -- the counted
         [dirlink_units] clause above is untouched. *)
      ⌜dl16_post bmapstart dinum inodestart ncount n' k0 tot found
                 bm bm' Sb Sb'⌝ -∗
      (* ...and the FOUND arm's OWN spend, which the counted
         [dirlink_units] above does not price finely enough for a caller
         that cannot REFUTE the arm.  create can (it holds [ilock(dp)]
         across its own [dirlookup] miss and reads the miss back out of
         [dir_first]); sys_link cannot -- it never looks the name up
         before linking it -- and seven from the nine its two walks and
         its mint can leave is two, against an [iput_units] of three
         ([SysLinkBudget.sl_found_busts_by_one]).  ADDITIVE, and honest at
         the constant: the found arm writes NOTHING, it is dirlookup's hit
         plus the [iput] of the child, whose credited worst case is
         exactly [iput_units] ([sl_found_honest]) -- and three is the
         LARGEST constant that closes sys_link's arm
         ([sl_found_at_four_busts] refutes four). *)
      ⌜found = true -> ((ncount - iput_units)%nat <= n')%nat⌝ -∗
      log_opS γ n' Sb' -∗
      (* ---- THE TWO [inode_ok] CONJUNCTS A RE-PARKER NEEDS, AS
         PRESERVATIONS (fs-sysfile S5a finding 2; the cap, D₀-a repair 3b) --
         [InodeLock.inode_ok] has seven conjuncts and the arms below
         re-establish five of them ([blkmap_wf], [bm_covers],
         [di_addrs = bm_cells], [blk_holes_zero], and [di_type <> 0] through
         [dn' = wi_dinode dn ...]).  The other two are writei's own two
         preservation clauses (SpecWritei.v:661), relayed here VERBATIM,
         guard included, because NEITHER is recoverable at this seam:
         [InodeInv.inode_sized] because the range clause below is about
         [file_byte], a per-BYTE view that pins no block's LENGTH, and the
         SIZE CAP because the arithmetic that used to recover it
         ([16*k0 + tot <= size + 16], [ProofCreateParts.cr_size_cap]) needed
         "the append fits" -- the premise the eleventh stop retired.

         Relayed, the cap costs a caller nothing: the antecedent is about
         its OWN entry record, and it is a conjunct of the [inode_ok] the
         caller is about to rebuild.  Both are free inside [ProofDirlink]:
         writei hands them over, and the found arm has [dn' = dn],
         [data' = data]. *)
      ⌜bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
       bv_unsigned (di_size dn') <= Z.of_nat MAXFILE * Z.of_nat BSIZE⌝ -∗
      ⌜inode_sized data -> inode_sized data'⌝ -∗
      (* ---- THE TWO ARMS ---- *)
      ⌜if found
        then (* the name was already there: iput spent the child *)
          dir_first data nrec s <> None
          /\ mf !!! Regidx (mword_of_int 10 : mword 5)
             = (mword_of_int (-1) : mword 64)
          /\ bm' = bm /\ data' = data /\ dn' = dn /\ dn0' = dn0
          /\ tot = 0%nat
        else (* the append, through writei at [16*k0] *)
          dir_first data nrec s = None
          /\ blkmap_wf cov logstart bm'
          /\ blk_holes_zero bm' data'
          /\ di_addrs dn' = bm_cells bm'
          /\ bv_unsigned (di_size dn') < 2 ^ 31
          /\ bm_covers bm' (bv_unsigned (di_size dn'))
          /\ dn' = wi_dinode dn bm' (16 * k0)%nat tot
          (* THE FLUSHED RECORD, AS A PRESERVATION (D₀-a repair 3b).  The
             success and short-write arms run writei's trailing [iupdate],
             so the REGION's record becomes the metadata one and [dn0' = dn']
             outright; writei's own -1 return (the full directory -- see the
             header) runs no iupdate at all and answers [dn0' = dn0],
             [dn' = dn].  Nothing here relates [dn0] to [dn], so the honest
             clause is the implication -- and it is free for every caller,
             because a caller holds the two as ONE record
             ([IcacheEscrow.ic_loaded]'s single [dinode_at]; it is the same
             fact [InodeRegion.di_type_stable_refl] discharges the type
             premise from), and a caller that did not could not re-park
             either way. *)
          /\ (dn0 = dn -> dn0' = dn')
          /\ (tot <= 16)%nat
          (* THE RANGE CLAUSE: the record's bytes in the window and NOTHING
             ELSE.  writei's disturbed region is empty on the kernel arm --
             see the header, and fs-icache.md §15.1(i). *)
          /\ (forall x : nat,
                file_byte data' x
                = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat)
                  then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
                  else file_byte data x)
          (* the branchless return: 0 exactly when all sixteen went in *)
          /\ ((mf !!! Regidx (mword_of_int 10 : mword 5)
                 = (mword_of_int 0 : mword 64) /\ tot = 16%nat)
              \/ (mf !!! Regidx (mword_of_int 10 : mword 5)
                    = (mword_of_int (-1) : mword 64) /\ (tot < 16)%nat))⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type DIRLINK.
  Parameter wp_dirlink_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γa : gname) (γf : gname) (γpr : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (bmapstart : Z) (size : Z) (dev : mword 32)
      (ip : mword 64) (dinum : mword 32)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn dn0 : dinode)
      (fn : nat -> bv 8)
      (inum : mword 16)
      (ncount : nat)
      (pidv : mword 32) (dq dqd dqn dqs dqb dqbs dqf : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate),
      wp_dirlink_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl
                            γa γf γpr cov logstart inodestart nib bmapstart
                            size dev ip dinum bm data dn dn0 fn inum
                            ncount pidv dq dqd dqn dqs dqb dqbs dqf
                            m K eb b lks Vpr.

  (* the SET-FORM contract; [wp_dirlink_sconf] above is its instance with
     the set forgotten, kept as its own parameter so that every existing
     caller is unchanged (wp_writei_gen / wp_bmap_gen's pattern) *)
  Parameter wp_dirlink_gen :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γa : gname) (γf : gname) (γpr : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (bmapstart : Z) (size : Z) (dev : mword 32)
      (ip : mword 64) (dinum : mword 32)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn dn0 : dinode)
      (fn : nat -> bv 8)
      (inum : mword 16)
      (ncount : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqd dqn dqs dqb dqbs dqf : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate),
      wp_dirlink_gen_body γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl
                          γa γf γpr cov logstart inodestart nib bmapstart
                          size dev ip dinum bm data dn dn0 fn inum
                          ncount Sb pidv dq dqd dqn dqs dqb dqbs dqf
                          m K eb b lks Vpr.
End DIRLINK.
