(* SpecNamex.v -- the public interface of namex, fs.c's path walker.

     static struct inode*
     namex(char *path, int nameiparent, char *name)
     {
       struct inode *ip, *next;

       if ( *path == '/' )
         ip = iget(ROOTDEV, ROOTINO);
       else
         ip = idup(myproc()->cwd);

       while((path = skipelem(path, name)) != 0){
         ilock(ip);
         if(ip->type != T_DIR){
           iunlockput(ip);
           return 0;
         }
         if(nameiparent && *path == '\0'){
           // Stop one level early.
           iunlock(ip);
           return ip;
         }
         if((next = dirlookup(ip, name, 0)) == 0){
           iunlockput(ip);
           return 0;
         }
         iunlockput(ip);
         ip = next;
       }
       if(nameiparent){
         iput(ip);
         return 0;
       }
       return ip;
     }

   318 bytes, width 3.  skipelem is INLINED -- there is no [skipelem] symbol
   in the image -- so the loop below is namex's own, and [PathElems.v] models
   it directly.

   ---- THE CONTROL FLOW, READ OFF CodeNamex.v -------------------------------

   Register assignment (all verified against the decode):
     s1 (x9)  = path, the moving pointer       s2 (x18) = the element scanner
     s4 (x20) = ip                             s5 (x21) = name
     s6 (x22) = nameiparent                    s7 (x23) = 1  (T_DIR)
     s3 (x19) = 47 ('/')                       s8 (x24) = 13, s9 (x25) = 14
     s10(x26) = len                            s0 = sp + 96 (12-slot frame)

     +0x00..0x1a  prologue: 96-byte frame, ra + s0..s10 saved, s0 = sp+96
     +0x1c..0x2a  s1=path, s6=nameiparent, s5=name; [lbu a4,0(a0)];
                  [li a5,47]; [beq a4,a5,+0x48]        -- THE ARM SPLIT
     +0x2e..0x3a  jal myproc; [ld a0,336(a0)] (p->cwd); jal idup; s4 = a0
     +0x3c..0x46  s3=47, s8=13, s9=14, s7=1; [c.j +0xe4]  -- into the loop
     +0x48..0x52  [li a1,1]; [mv a0,a1]  == iget(1,1); jal iget; s4 = a0;
                  [c.j +0x3c]                          -- rejoins at +0x3c
     +0xe4..0xf6  while ( *s1=='/' ) s1++;  if ( *s1==0 ) goto +0x130
     +0xf8..0x102 THE DEAD BLOCK: re-loads *s1 and re-tests it against '/'
                  and 0, both of which were just decided at +0xe8/+0xf2 and
                  +0xf6.  Both branches go to the len = 0 block at +0x116
                  and neither is taken.
     +0x104..0x114 s2 = s1; do s2++ while ( *s2 != '/' && *s2 != 0 )
     +0x8c..0x94  a2 = s2 - s1; s10 = sext.w a2; [bge s8,s10,+0x11c]
                    -- s8 = 13, so len <= 13 takes the SHORT branch
     +0x98..0xa2  LONG: memmove(name, s1, 14) -- NO terminator -- ; s1 = s2
     +0x116..0x11a the len = 0 entry (dead, see above): s2=s1, s10=0, a2=0
     +0x11c..0x12e SHORT: memmove(name, s1, len); name[len] = 0; s1 = s2;
                  [c.j +0xa4]
     +0xa4..0xb2  skipelem's TRAILING while ( *s1=='/' ) s1++
     +0xb6..0xc0  jal ilock(s4); [lh a5,68(s4)]; [bne a5,s7,+0x54]
     +0x54..0x5a  jal iunlockput(s4); s4 = 0                 -- NOT A DIR
     +0xc4..0xcc  [beq s6,zero,+0xce]; [lbu a5,0(s1)]; [beqz a5,+0x7a]
     +0x7a..0x80  jal iunlock(s4); [c.j +0x5c]            -- NAMEIPARENT HIT
     +0xce..0xda  [li a2,0]; a1 = s5; a0 = s4; jal dirlookup; s2 = a0;
                  [beqz a0,+0x82]
     +0x82..0x8a  jal iunlockput(s4); s4 = s2 (= 0); [c.j +0x5c]   -- MISS
     +0xdc..0xe2  jal iunlockput(s4); s4 = s2       -- and FALL INTO +0xe4
     +0x130..0x13c [beq s6,zero,+0x5c] (namei: return ip);
                  jal iput(s4); s4 = 0; [c.j +0x5c]   -- nameiparent of "/"
     +0x5c..0x78  a0 = s4; epilogue; ret

   Every [jal] target was resolved numerically against KernelSyms:
   myproc 0x80001906, idup 0x800031a6, iget 0x80002f6a, memmove 0x80000d28
   (both call sites), ilock 0x800031dc, iunlock 0x8000328a, iunlockput
   0x800033e8 (both call sites), dirlookup 0x8000377c, iput 0x8000335e.

   ---- WHAT IT SPEAKS IN ----------------------------------------------------

   THE LOOP CURRENCY IS [IcacheRef.inode_held] -- the pointer-keyed,
   slot/fraction/inum-existential form that [ProcInv.cwd_ref] already is.  Both
   starting arms produce exactly that (iget's postcondition IS a reference at
   an existential fraction; idup's mint likewise), and both wrappers hand it
   straight on.  Nothing in namex's contract names a slot.

   THE PATH is a byte buffer at [a0] described by a naming function [pfun] and
   a length [plen] with [ByteBuf.bb_cstr pfun plen]; the MODEL is the byte list
   [pl := DirentEnc.bview plen pfun], and [PathElems.path_elems pl] is the list
   of elements the loop consumes.  namex reads indices 0..plen inclusive and
   never past the terminator, so [S plen] bytes of FULL ownership is (memmove reads the path as its
   source, and its contract demands DfracOwn 1 there -- N4c2 finding A)
   exactly right.

   THE NAME BUFFER is 14 caller-owned bytes at [a2], written by the two
   memmoves.  It comes back holding an UNSPECIFIED naming function [nf] --
   the short branch leaves bytes above [len] untouched -- and on the
   nameiparent success arm the one fact that matters,
   [DirentEnc.bname 14 nf = e], holds with [e] the LAST element
   ([PathElems.nameiparent_of]).  That clause is [PathElems.skipelem_name_view]
   and it covers BOTH memmove shapes, including the long branch's
   unterminated 14-byte copy.

   ---- SCOPE RULING: THE POSTCONDITION IS RESOURCE-SHAPED -------------------

   Success is [a0 = ip <> 0] with [inode_held ip]; failure is [a0 = 0] with
   every loaned resource back and NO inode resource retained.  There is NO
   path -> inode functional statement: each dirlookup is atomic under its own
   directory's lock and no stable global tree exists between iterations under
   concurrency, so the honest refinement would be a ghost trace ("there was a
   sequence of atomic lookups, each finding element i in the then-current
   contents of directory i-1"), which earns nothing at this altitude.  It is
   RECORDED as a future frontier beside DirView's [gmap name inum] view.  The
   name-buffer clause IS functional, because it is locally produced.

   ---- THE PREMISES -------------------------------------------------------

   (1) [dev = icfg_dev], [nib = icfg_nib] -- ProofKexit's pattern.  The second
       is what N4a's [DirView.dir_ok_dir] wants: the [dir_ok icfg_nib dn data]
       conjunct now rides inside [IcacheEscrow.ic_loaded], so namex destructs
       dirlookup's [dir_inums_ok] premise straight out of ilock's
       postcondition at a directory it could not have named in advance.
       namex needs NO granularity fact (fs-icache.md §15(b)).

   (2) [dev = ROOTDEV] and [0 < nib].  The absolute arm's [li a1,1] /
       [mv a0,a1] is literally [iget(1, 1)], so the cache's device must BE
       ROOTDEV for that reference to be one this cache can hold, and iget's
       [bv_unsigned ROOTINO < 16 * nib] needs a non-empty inode region.

   (3) [SpecDirlink.ireg_blocks_ok inodestart nib cov logstart] -- N3's
       finding 2, and it is exactly right here: ilock, iput and iunlockput all
       want [IBLOCK inum inodestart ∈ cov] (and iput its log-region
       complement) at inums namex learns only at run time, and a fact about
       the superblock LAYOUT discharges all of them.

   (4) THE BUDGET IS LINEAR IN THE ELEMENT COUNT.  Every turn of the loop
       spends at most one [iput_units] interval (the iunlockput at +0xdc, or
       the one at +0x82 / +0x54 that ends the walk), and the nameiparent-of-
       "/" arm spends one more at +0x136; ilock and dirlookup take no log
       reservation at all.  Hence [(L + 1) * iput_units <= n] in, with
       [L = length (path_elems pl)], and the matching spend-at-most interval
       out.  Partial correctness needs no measure; [PathElems.skipelem_decr]
       exists if one is ever wanted.

   (5) THE LEDGER IS TWO SLOTS IN.  The starting arm spends one (iget's mint,
       or idup's), and each turn peaks at one more (dirlookup's iget, returned
       by the following iunlockput).  Success returns ONE (the walk's own
       reference is still alive, in [inode_held]); every failure arm returns
       BOTH, which is the resource statement of "no inode resource retained".

   (6) The parking premise [eb = true] -- ilock, dirlookup and iput all sleep.

   THE WORKING DIRECTORY is taken UNCONDITIONALLY ([p_cwd pj ↦₈{dqc} cwdv] and
   [inode_held cwdv], both handed back untouched) even though only the relative
   arm reads it: every caller holds it inside [ProcInv.proc_priv] anyway
   ([ProcInv.proc_priv_cwd] is the accessor), and a two-armed precondition keyed
   on the first path byte would buy nothing.

   ---- THE PANIC ARMS ------------------------------------------------------

   All inherited, none new: ilock's "ilock: no type", iget's "iget: no
   inodes", dirlookup's "dirlookup not DIR" (refuted by the [lh a5,68(s4)]
   test namex performs at +0xbc) and its now-live "dirlookup read"
   granularity arm.  [panic_wp_any] is threaded and nothing else is owed.

   namex enters and returns at noff 0. *)
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
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import PanicStub.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import ByteBuf.
Require Import DirentEnc.
Require Import PathElems.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KallocInv.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import SpecIput.
Require Import SpecDirlookup.
Require Import SpecDirlink.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.

Local Open Scope Z_scope.

(* namex's own frame is 96 bytes (12 slots); its deepest callee is dirlookup
   at 90 (iunlockput wants 64, iput 60, ilock 44, iunlock 26, iget 16, idup
   14, myproc 10, memmove 2).

   90, and dirlookup's dominant chain is now bmap's, not copyout's --
   SpecDirlink.v's header has the arithmetic.  Nothing else in namex's list
   moved. *)
Definition K_namex : nat := 102%nat.

(* ===================================================================== *)
(*  THE WALK'S LEDGER FIGURES (fs-log.md §G.24/§G.25)                     *)
(*                                                                        *)
(*  WHAT THE WALK SPENDS is ONE unit for the whole walk, not one per      *)
(*  level: every per-level [iunlockput] runs [crz := true] on the inode   *)
(*  block (the receipt minted at the +0xce nlink guard) and [crb := w]    *)
(*  on the bitmap, so the only thing a freeing level can fail to absorb   *)
(*  is THE bitmap block -- and whoever pays for it first puts it in the   *)
(*  op's set, which is what [w] reports.  Definitionally                  *)
(*  [CreateBudget.np_spend].                                              *)
(*                                                                        *)
(*  THE FAILURE ARMS COST ONE MORE, and honestly so: [L_notdir] (+0x54)   *)
(*  runs BEFORE the nlink guard and [L_nlink] (+0x7a) runs AT it, so      *)
(*  neither is downstream of a mint and neither can be credited, and      *)
(*  [L_done]'s [iput] (+0x140) is at an inode this walk never locked.     *)
(*  All three are TERMINAL, so the walk pays it at most once -- and the   *)
(*  SUCCESS arms pay it never: namei returns at +0x140 without an iput    *)
(*  and nameiparent returns through [L_par] (+0x84), which calls          *)
(*  [iunlock].  That asymmetry is why the figure is indexed by [ok], and  *)
(*  it is what makes create's row [CreateBudget.cr_uw w] exact: create    *)
(*  proceeds only on success.                                            *)
(*                                                                        *)
(*  WHAT THE WALK MUST HAVE IN HAND is likewise NOT linear: one iput's    *)
(*  worth, plus the single unit the walk may spend before the deepest     *)
(*  level runs.  [walk_need 0 = iput_units] because the loop body never   *)
(*  runs at an empty path -- which is what keeps the counted contract's   *)
(*  own premise sufficient at every path length.                          *)
(* ===================================================================== *)
Definition walk_spend (w : bool) : nat := if w then 1%nat else 0%nat.

Definition walk_need (L : nat) : nat :=
  match L with O => iput_units | S _ => S iput_units end.

Lemma walk_need_counted (L n : nat) :
  ((L + 1) * iput_units <= n)%nat -> (walk_need L <= n)%nat.
Proof. destruct L; unfold walk_need, iput_units; lia. Qed.

Lemma walk_spend_counted (L n n' : nat) (w ok : bool) :
  ((L + 1) * iput_units <= n)%nat ->
  ((n - (walk_spend w + (if ok then 0%nat else 1%nat)))%nat <= n')%nat ->
  ((n - (L + 1) * iput_units)%nat <= n')%nat.
Proof. destruct w, ok; unfold walk_spend, iput_units; lia. Qed.

(* The two immediates of the absolute arm, read off [li a1,1] at +0x48 and
   the [mv a0,a1] at +0x4a that makes the device argument the same word.

   HOISTED (N5d): both now live in [InodeInv.v], beside [sb_ninodes], because
   [SpecFsinit] owes the boot tie [icfg_dev = ROOTDEV] and a Spec file must
   not require another function's Spec.  These are ABBREVIATIONS, not new
   definitions: [ROOTDEV] here and [InodeInv.ROOTDEV] are the SAME constant,
   so the qualified uses in SpecNamei / SpecNameiparent and the bare
   [unfold ROOTDEV] / [unfold ROOTINO] in ProofNamex still work unchanged. *)
Notation ROOTDEV := InodeInv.ROOTDEV.
Notation ROOTINO := InodeInv.ROOTINO.

(* THE CONTRACT'S CONTINUATION, NAMED.  Spelled out it is twenty wands over the
   whole loaned bundle plus the two-armed result; namex's whole-function proof
   carries it as a spatial hypothesis for ~4000 proofmode steps and restates it
   inside its loop invariant, and every step re-embeds it in the proof term
   twice (claude-notes/optimization.md, "RULE ONE" and "WHY Qed IS EXPENSIVE").
   Named, it is one constant applied to its arguments.

   TRANSPARENT ON PURPOSE -- do NOT add [Typeclasses Opaque].  The proofmode
   unifies [iApply ("Hcont" $! mf ...)] through a transparent constant but NOT
   through an opaque one, so sealing it forces an
   [iEval (rewrite /namex_post) in "Hcont"] at every use site, and that rewrite
   is itself context-proportional: measured +48% on the whole file (5:36 ->
   8:38).  Contrast [SpecUservec.uservec_post], which IS sealed -- that one is
   unfolded once, at the return, and never applied under a wand. *)
Definition namex_post
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (pj pv nb ret_tgt : mword 64) (pl : list (bv 8))
    (m : regfile) (K : nat) (b eb : bool) (lks : gset string)
    (g : log_names) (gfs : fs_names) (bn : bio_names)
    (cov : gset Z) (logstart bmapstart inodestart size : Z)
    (used : gset Z) (cwdv : mword 64)
    (plen : nat) (pfun : nat -> bv 8)
    (npar : bool) (n : nat) (pidv : mword 32)
    (dq dqb dqs dqc : dfrac) : iProp Σ :=
  (∀ (mf : regfile) (n' : nat) (used' : gset Z)
     (ok : bool) (nf : nat -> bv 8) (ipv : mword 64),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      pc_is ret_tgt -∗
      (* EVERYTHING LOANED COMES BACK *)
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      ⌜used' ⊆ used⌝ -∗
      bitmap_res gfs bmapstart cov logstart size used' -∗
      p_pid pj ↦₄{dq} pidv -∗
      p_cwd pj ↦₈{dqc} cwdv -∗
      inode_held cwdv -∗
      ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
      (* the name buffer, at an UNSPECIFIED naming function -- the short
         branch leaves the bytes above [len] alone *)
      ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ nf i) -∗
      bslots bn 3 -∗
      ⌜((n - (length (path_elems pl) + 1) * iput_units)%nat <= n')%nat
       /\ (n' <= n)%nat⌝ -∗
      log_op g n' -∗
      (* THE TWO ARMS *)
      (if ok
       then ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = ipv
             /\ (npar = true ->
                 exists es e, nameiparent_of pl es e /\ bname 14 nf = e)⌝ ∗
            inode_held ipv ∗
            iref_slots 1
       else ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
             = (mword_of_int 0 : mword 64)⌝ ∗
            iref_slots 2) -∗
      WP (Loop : expr riscv_lang))%I.

(* THE SET-FORM CONTINUATION (fs-sysfile GR-2b, retrofit 6).  Verbatim
   [namex_post] except that the ledger clause remembers the caller's set and
   promises only to GROW it.  Stated as a separate definition rather than by
   parameterising [namex_post], so the counted continuation -- which every
   existing caller's [iApply ("Hcont" ...)] unifies against transparently --
   is byte-identical.  The counted form is recovered from this one by
   [LogInv.log_opS_op] at the seal, never the other way round. *)
Definition namex_postS
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (pj pv nb ret_tgt : mword 64) (pl : list (bv 8))
    (m : regfile) (K : nat) (b eb : bool) (lks : gset string)
    (g : log_names) (gfs : fs_names) (bn : bio_names)
    (cov : gset Z) (logstart bmapstart inodestart size : Z)
    (used : gset Z) (cwdv : mword 64)
    (plen : nat) (pfun : nat -> bv 8)
    (npar : bool) (n : nat) (Sb : gset Z) (pidv : mword 32)
    (dq dqb dqs dqc : dfrac) : iProp Σ :=
  (∀ (mf : regfile) (n' : nat) (used' Sb' : gset Z)
     (ok : bool) (nf : nat -> bv 8) (ipv : mword 64) (w : bool),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      pc_is ret_tgt -∗
      (* EVERYTHING LOANED COMES BACK *)
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      ⌜used' ⊆ used⌝ -∗
      bitmap_res gfs bmapstart cov logstart size used' -∗
      p_pid pj ↦₄{dq} pidv -∗
      p_cwd pj ↦₈{dqc} cwdv -∗
      inode_held cwdv -∗
      ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
      (* the name buffer, at an UNSPECIFIED naming function -- the short
         branch leaves the bytes above [len] alone *)
      ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ nf i) -∗
      bslots bn 3 -∗
      (* THE SET ONLY GROWS.  What the walk MUST do is not LOSE the
         caller's set across the loop, which against the counted contract
         is impossible (GR-2a finding 1). *)
      ⌜Sb ⊆ Sb'⌝ -∗
      (* THE PAID-BITMAP REPORT.  [w] is "the walk paid for the bitmap
         block", and it comes with the membership -- which is exactly what
         create's FIRST dirlink then claims as its own [crb]
         (CreateBudget's mkdir row: at [w = true] the walk's unit comes off
         the top and that dirlink gives it straight back). *)
      ⌜w = true -> bmapstart ∈ Sb'⌝ -∗
      ⌜((n - (walk_spend w + (if ok then 0%nat else 1%nat)))%nat <= n')%nat
       /\ (n' <= n)%nat⌝ -∗
      log_opS g n' Sb' -∗
      (* THE TWO ARMS.  The success arm's reference is BUNDLED when the
         walk was a nameiparent one: that return is [L_par], reached only
         through the +0xc4 type test, so the walk KNOWS the record is a
         directory and hands the fact on at the reference's own generation
         (fs-icache §17.6's one-shot).  create performs no parent type test
         of its own -- fs-sysfile's Blocker B -- and this is what closes
         it.  namei's return is the plain form: nothing tested its type. *)
      (if ok
       then ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = ipv
             /\ (npar = true ->
                 exists es e, nameiparent_of pl es e /\ bname 14 nf = e)⌝ ∗
            (if npar then inode_held_ty ipv T_DIR else inode_held ipv) ∗
            iref_slots 1
       else ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
             = (mword_of_int 0 : mword 64)⌝ ∗
            iref_slots 2) -∗
      WP (Loop : expr riscv_lang))%I.

Definition wp_namex_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (gs : list gname) (j : nat) (gl : gname)           (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)   (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names) (gtl : gname)                      (* the icache + itable *)
    (ga : gname) (gf : gname)                          (* kalloc, file table  *)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (used : gset Z)
    (cwdv : mword 64)                                  (* p->cwd, untouched   *)
    (plen : nat) (pfun : nat -> bv 8)                  (* the path buffer     *)
    (nfun : nat -> bv 8)                               (* the name buffer, in *)
    (npar : bool)                                      (* the a1 flag         *)
    (n : nat)
    (pidv : mword 32) (dq dqb dqs dqc : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.namex in
  let pj := proc_addr j in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in   (* a0 = path *)
  let nb := m !!! Regidx (mword_of_int 12 : mword 5) in   (* a2 = name *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let pl := bview plen pfun in
  let L := length (path_elems pl) in
  (K_namex <= K)%nat ->
  (* (1) the cache's identity -- see the header.  THE REGION'S TWO TIES
     ride here too (fs-log.md §G.25): the walk MINTS the group receipt at
     its nlink guard and cashes it at every per-level iunlockput, and
     [InodeRegion]'s vocabulary is ambient -- [icfg_log] and [icfg_ist] --
     so a contract that threads its own [g] and [inodestart] meets it only
     through a pure equation.  True at boot by [IcacheRef.icfg_alloc]. *)
  dev = icfg_dev ->
  nib = icfg_nib ->
  g = icfg_log ->
  inodestart = icfg_ist ->
  (* (2) the absolute arm's two immediates *)
  dev = ROOTDEV ->
  (0 < nib)%nat ->
  (* (3) the fs geometry: iput's / itrunc's, threaded verbatim *)
  log_geom_ok cov logstart ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  0 <= inodestart ->
  cov_below cov size ->
  (* the LAYOUT fact that discharges ilock's / iput's per-inum block
     membership at inums namex learns only at run time (N3's finding 2) *)
  ireg_blocks_ok inodestart nib cov logstart ->
  (* the path really is a NUL-terminated string of length [plen] *)
  bb_cstr pfun plen ->
  (* the length fits int: the sext.w at +0x90 truncates [len = s2 - s1], and
     without this bound the [blt]-against-13 stops deciding [len <= 13] (and
     the short branch fails memmove's own 2^32 bound).  SpecFetchstr's
     header records the identical premise for strlen's [subw]. *)
  (Z.of_nat plen < 2 ^ 31)%Z ->
  (* (4) the budget, linear in the element count *)
  ((L + 1) * iput_units <= n)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* a1 = nameiparent, reflected into a ghost boolean the way dirlookup's
     [poff] is *)
  eq_vec (m !!! Regidx (mword_of_int 11 : mword 5)) zero_reg = negb npar ->
  (* (6) PARKING PREMISE *)
  eb = true ->
  (* ORDER PREMISE: same cone, same bound, as the _gen body below. *)
  locks_below lks "log" ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view gfs gd dev cov) -∗
  log_ctx g bn gfs cov logstart dev -∗
  kalloc_env ga None -∗
  (* ---- THE ICACHE'S PERSISTENT SET.  The FAMILIES, not the singletons:
     namex's slots are dirlookup's outputs and cannot be named in advance,
     which is the same reason iget takes [ic_escrows] and dirlink defined
     [ic_sleeplocks]. ---- *)
  is_itable2 gtl cn gfs gi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn gfs gi cov logstart -∗
  ic_sleeplocks cn -∗
  ireg_inv gi gfs inodestart nib -∗
  (* ---- the running-thread bundle and the disk fabric ---- *)
  procs_inv gs -∗
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  (* ---- iput's / itrunc's own resources ---- *)
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_res gfs bmapstart cov logstart size used -∗
  (* ---- the caller's own pid cell (acquiresleep records it) ---- *)
  p_pid pj ↦₄{dq} pidv -∗
  (* ---- THE WORKING DIRECTORY: cell and reference, both handed back ---- *)
  p_cwd pj ↦₈{dqc} cwdv -∗
  inode_held cwdv -∗
  (* ---- THE PATH: [plen] content bytes and the terminator ---- *)
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
  (* ---- THE NAME BUFFER: fourteen bytes, WRITTEN ---- *)
  ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ nfun i) -∗
  (* ---- three buffer slots (iput's itrunc arm forces three) ---- *)
  bslots bn 3 -∗
  (* ---- the ledger: see (5) in the header ---- *)
  iref_slots 2 -∗
  (* ---- this operation's reservation ---- *)
  log_op g n -∗
  (* the continuation is SEALED as [namex_post]; see its header *)
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two coincide at the only instance
     the [eb = true] premise admits, which is why this went unnoticed; once
     [eb = false] is reachable the [b] form would promise the caller it
     comes back on the hart it called from, which a park makes false. *)
  wp_next true pj (fun (CIDc : CpuId) =>
    namex_post (CID := CIDc) pj pv nb ret_tgt pl m K b eb lks
               g gfs bn cov logstart bmapstart inodestart size used cwdv
               plen pfun npar n pidv dq dqb dqs dqc) -∗
  WP (Loop : expr riscv_lang).

(* =====================================================================  *)
(*  THE SET-FORM CONTRACT (fs-sysfile GR-2b, retrofit 6)                  *)
(*                                                                        *)
(*  namex's four log sites are ALL iput or iunlockput calls (three         *)
(*  iunlockputs in the loop, one iput on the nameiparent-of-"/" arm;       *)
(*  ilock and dirlookup take no reservation at all), so against the        *)
(*  counted [SpecIput] post the caller's set was lost at the FIRST turn    *)
(*  of the loop.  With 4b landed, each of those calls carries              *)
(*  [Sb ⊆ Sb'] across, and the loop threads a GROWING set.                *)
(*                                                                        *)
(*  NO CREDITS.  namex discovers its inums as it walks, so it can make no  *)
(*  honest [crb]/[cru] claim about them; it calls iput/iunlockput          *)
(*  UNCREDITED and the budget clause is the counted one verbatim.  This    *)
(*  contract adds monotonicity and nothing else -- which is exactly what   *)
(*  create needs of it, since create's own credited calls are the dirlink  *)
(*  and iupdate ones, not namex's.                                        *)
(* ===================================================================== *)
Definition wp_namex_gen_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (gs : list gname) (j : nat) (gl : gname)           (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)   (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names) (gtl : gname)                      (* the icache + itable *)
    (ga : gname) (gf : gname)                          (* kalloc, file table  *)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (used : gset Z)
    (cwdv : mword 64)                                  (* p->cwd, untouched   *)
    (plen : nat) (pfun : nat -> bv 8)                  (* the path buffer     *)
    (nfun : nat -> bv 8)                               (* the name buffer, in *)
    (npar : bool)                                      (* the a1 flag         *)
    (n : nat) (Sb : gset Z)
    (pidv : mword 32) (dq dqb dqs dqc : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.namex in
  let pj := proc_addr j in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in   (* a0 = path *)
  let nb := m !!! Regidx (mword_of_int 12 : mword 5) in   (* a2 = name *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let pl := bview plen pfun in
  let L := length (path_elems pl) in
  (K_namex <= K)%nat ->
  (* (1) the cache's identity -- see the header.  THE REGION'S TWO TIES
     ride here too (fs-log.md §G.25): the walk MINTS the group receipt at
     its nlink guard and cashes it at every per-level iunlockput, and
     [InodeRegion]'s vocabulary is ambient -- [icfg_log] and [icfg_ist] --
     so a contract that threads its own [g] and [inodestart] meets it only
     through a pure equation.  True at boot by [IcacheRef.icfg_alloc]. *)
  dev = icfg_dev ->
  nib = icfg_nib ->
  g = icfg_log ->
  inodestart = icfg_ist ->
  (* (2) the absolute arm's two immediates *)
  dev = ROOTDEV ->
  (0 < nib)%nat ->
  (* (3) the fs geometry: iput's / itrunc's, threaded verbatim *)
  log_geom_ok cov logstart ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  0 <= inodestart ->
  cov_below cov size ->
  (* the LAYOUT fact that discharges ilock's / iput's per-inum block
     membership at inums namex learns only at run time (N3's finding 2) *)
  ireg_blocks_ok inodestart nib cov logstart ->
  (* the path really is a NUL-terminated string of length [plen] *)
  bb_cstr pfun plen ->
  (* the length fits int: the sext.w at +0x90 truncates [len = s2 - s1], and
     without this bound the [blt]-against-13 stops deciding [len <= 13] (and
     the short branch fails memmove's own 2^32 bound).  SpecFetchstr's
     header records the identical premise for strlen's [subw]. *)
  (Z.of_nat plen < 2 ^ 31)%Z ->
  (* (4) THE BUDGET IS NOT LINEAR ANY MORE (fs-log.md §G.24): the walk
     needs one iput's worth plus the single unit it may spend, whatever
     the path length.  The counted contract's premise implies this one at
     both shapes ([walk_need_counted]), which is what keeps
     [wp_namex_sconf] byte-stable. *)
  (walk_need L <= n)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* a1 = nameiparent, reflected into a ghost boolean the way dirlookup's
     [poff] is *)
  eq_vec (m !!! Regidx (mword_of_int 11 : mword 5)) zero_reg = negb npar ->
  (* (6) PARKING PREMISE *)
  eb = true ->
  (* (7) ORDER PREMISE.  namex's cone bottoms out at itable.lock (2) --
     iget/iput/idup all state their bound there; ilock's "sleep lock" (6)
     and the bcache/log ranks above it follow by [locks_below_mono]. *)
  locks_below lks "log" ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view gfs gd dev cov) -∗
  log_ctx g bn gfs cov logstart dev -∗
  kalloc_env ga None -∗
  (* ---- THE ICACHE'S PERSISTENT SET.  The FAMILIES, not the singletons:
     namex's slots are dirlookup's outputs and cannot be named in advance,
     which is the same reason iget takes [ic_escrows] and dirlink defined
     [ic_sleeplocks]. ---- *)
  is_itable2 gtl cn gfs gi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn gfs gi cov logstart -∗
  ic_sleeplocks cn -∗
  ireg_inv gi gfs inodestart nib -∗
  (* ---- the running-thread bundle and the disk fabric ---- *)
  procs_inv gs -∗
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  (* ---- iput's / itrunc's own resources ---- *)
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_res gfs bmapstart cov logstart size used -∗
  (* ---- the caller's own pid cell (acquiresleep records it) ---- *)
  p_pid pj ↦₄{dq} pidv -∗
  (* ---- THE WORKING DIRECTORY: cell and reference, both handed back ---- *)
  p_cwd pj ↦₈{dqc} cwdv -∗
  inode_held cwdv -∗
  (* ---- THE PATH: [plen] content bytes and the terminator ---- *)
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
  (* ---- THE NAME BUFFER: fourteen bytes, WRITTEN ---- *)
  ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ nfun i) -∗
  (* ---- three buffer slots (iput's itrunc arm forces three) ---- *)
  bslots bn 3 -∗
  (* ---- the ledger: see (5) in the header ---- *)
  iref_slots 2 -∗
  (* ---- this operation's reservation, SET FORM ---- *)
  log_opS g n Sb -∗
  (* the continuation is SEALED as [namex_post]; see its header *)
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two coincide at the only instance
     the [eb = true] premise admits, which is why this went unnoticed; once
     [eb = false] is reachable the [b] form would promise the caller it
     comes back on the hart it called from, which a park makes false. *)
  wp_next true pj (fun (CIDc : CpuId) =>
    namex_postS (CID := CIDc) pj pv nb ret_tgt pl m K b eb lks
                g gfs bn cov logstart bmapstart inodestart size used cwdv
                plen pfun npar n Sb pidv dq dqb dqs dqc) -∗
  WP (Loop : expr riscv_lang).

Module Type NAMEX.
  Parameter wp_namex_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (cwdv : mword 64)
      (plen : nat) (pfun : nat -> bv 8)
      (nfun : nat -> bv 8)
      (npar : bool)
      (n : nat)
      (pidv : mword 32) (dq dqb dqs dqc : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_namex_sconf_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
                          ga gf cov logstart bmapstart inodestart nib
                          size dev used cwdv plen pfun nfun npar n
                          pidv dq dqb dqs dqc m K eb b lks.
  (* the set-form contract; [wp_namex_sconf] is this at the [log_op]
     existential's own witness, with the grown set forgotten again. *)
  Parameter wp_namex_gen :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (cwdv : mword 64)
      (plen : nat) (pfun : nat -> bv 8)
      (nfun : nat -> bv 8)
      (npar : bool)
      (n : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqb dqs dqc : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_namex_gen_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
                        ga gf cov logstart bmapstart inodestart nib
                        size dev used cwdv plen pfun nfun npar n Sb
                        pidv dq dqb dqs dqc m K eb b lks.
End NAMEX.

(* ===================================================================== *)
(*  THE ROOT CORNER: [namex("/", 0, name)]                                *)
(*                                                                        *)
(*  WHY A SECOND CONTRACT AND NOT AN INSTANCE OF THE FIRST.  The general  *)
(*  contract above is a contract about a WALK: it takes the whole file-   *)
(*  system fabric (the bio cache, the log, the inode region, the bitmap,  *)
(*  the disk lock) and an OPEN transaction [log_op], it names the RUNNING *)
(*  process (for [myproc()->cwd] on the relative arm, and because the     *)
(*  walk can SLEEP), and it demands [eb = true].  None of that holds of   *)
(*  the one caller that matters at BOOT.                                  *)
(*                                                                        *)
(*  [userinit] runs before there is a current process, before [fsinit]    *)
(*  has read the superblock and before any transaction exists, and it     *)
(*  calls [namei("/")].  A path of exactly one '/' has NO elements, so    *)
(*  [skipelem] returns 0 on the first call and the walk's body never      *)
(*  runs: the executed code is the prologue, the [*path == '/'] test, the *)
(*  [iget(ROOTDEV, ROOTINO)] that arm makes, the four constant loads, the *)
(*  leading-separator skip (one turn), the [nameiparent] test at +0x140,  *)
(*  and the shared epilogue.  Nothing reads a disk block, nothing takes a *)
(*  sleeplock, nothing can park -- so this contract is the ICACHE and     *)
(*  nothing else, at an arbitrary [eb] / [b] / interrupt state, with no   *)
(*  process named anywhere in it.                                         *)
(*                                                                        *)
(*  So the two are not a cross-product to be collapsed: they are two      *)
(*  disjoint REGIMES of the same code, and the corner's whole point is    *)
(*  that it assumes strictly less.  What it shares with the general       *)
(*  contract -- the currency ([IcacheRef.inode_held]), the frame          *)
(*  geometry, the epilogue -- it shares verbatim.                         *)
(*                                                                        *)
(*  THE PATH IS TWO BYTES AT AN ARBITRARY [dfrac].  namex reads index 0   *)
(*  twice (at +0x22 and +0xf4) and index 1 once (at +0xfe) and never      *)
(*  writes either, and the [name] buffer is untouched because no memmove  *)
(*  runs -- which is why the buffer does not appear here at all.  The     *)
(*  fraction is a parameter because [userinit]'s "/" is a .rodata string  *)
(*  literal, i.e. [KernelDataInv.kernel_data]'s [↦ₘ□].                    *)
(* ===================================================================== *)

(* 12 slots for namex's own frame, over iget's 16. *)
Definition K_namex_root : nat := 28%nat.

Definition wp_namex_root_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, ICFG : icfg, !icacheG Σ, !logG Σ,
      !irefslotG Σ, !pavG Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (gtl : gname) (cn : ic_names) (gfs : fs_names) (gi : gname)
    (cov : gset Z) (logstart : Z) (nib : nat) (dev : mword 32)
    (dqp : dfrac)
    (m : regfile) (n K : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.namex in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in    (* a0 = path *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_namex_root <= K)%nat ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  dev = icfg_dev ->
  nib = icfg_nib ->
  dev = ROOTDEV ->
  (0 < nib)%nat ->
  (* a1 = 0: this is the [namei] side, so the +0x140 test takes the
     "return ip" branch rather than nameiparent's iput. *)
  m !!! Regidx (mword_of_int 11 : mword 5) = (zero_reg : mword 64) ->
  (* iget acquires and releases "itable" internally *)
  locks_below lks "itable" ->
  sie_cap_gpr m K b p -∗
  cpu_own n eb p C b lks -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  is_itable2 gtl cn gfs gi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn gfs gi cov logstart -∗
  iref_slot -∗
  (* the path: [pv] holds '/' and [pv+1] holds the terminator *)
  pa_add pv 0 ↦ₘ{dqp} SLASH -∗
  pa_add pv 1 ↦ₘ{dqp} NUL -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (ipv : mword 64),
      ⌜ callee_saved m mr
        /\ mr !!! Regidx (mword_of_int 10 : mword 5) = ipv ⌝ -∗
      sie_cap_gpr mr K b p -∗
      cpu_own n eb p C b lks -∗
      pc_is ret_tgt -∗
      pa_add pv 0 ↦ₘ{dqp} SLASH -∗
      pa_add pv 1 ↦ₘ{dqp} NUL -∗
      inode_held ipv -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type NAMEX_ROOT.
  Parameter wp_namex_root :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, ICFG : icfg, !icacheG Σ, !logG Σ,
             !irefslotG Σ, !pavG Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (gtl : gname) (cn : ic_names) (gfs : fs_names) (gi : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) (dev : mword 32)
      (dqp : dfrac)
      (m : regfile) (n K : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (b : bool) (lks : gset string),
      wp_namex_root_body gtl cn gfs gi cov logstart nib dev dqp
                         m n K eb p C b lks.
End NAMEX_ROOT.
