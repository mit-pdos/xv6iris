(* CreateBudget.v -- THE OP-WIDE LEDGER OF create, ARM BY ARM, MACHINE
   CHECKED (fs-icache.md section 18 clause 1; fs-sysfile S5a).

   Section 18 named create as the consumer that forces budget-bearing fs
   contracts into SET FORM, and left the arithmetic to this stage.  Here
   it is, in the shape [WriteiBudget] set for writei: the pure accounting
   first, as functions of OBSERVABLE booleans, and the contracts after.

   ==== THE VERDICT ======================================================

   **xv6 is log-sound at create.**  The op's distinct-block set is at most
   SIX --

     IBLOCK(ip)      ialloc's claim, ip's iupdate, and the iupdate inside
                     every dirlink on ip
     IBLOCK(dp)      dp's nlink++ iupdate and the iupdate inside
                     dirlink(dp, name)
     bmapstart       THE bitmap block -- there is exactly one
                     ([WriteiBudget.one_bitmap_block])
     ip's block 0    the new directory's first data block
     dp's block      the block the new entry lands in
     dp's indirect   only when the parent is past NDIRECT blocks

   -- against MAXOPBLOCKS = 10, and every one of create's twelve logging
   calls either introduces one of those six or ABSORBS against a block one
   of its predecessors already logged.  Nothing goes in
   claude-notes/kernel-defects.md.

   ==== WHAT THE ARITHMETIC SHOWS THE CONTRACTS MUST DO ==================

   The counted sums are hopeless: [4 * dirlink_units = 28] on its own.
   But so is the SET FORM AS LANDED, and that is this file's real finding.
   [wp_writei_gen] threads [log_opS] and promises [Sb ⊆ Sb'], but its
   spend bound is still the LOOSE per-call constant
   ([ncount - wi_cost_bmonly off n <= n']), and

     10 - 1(ialloc) - 1(iupdate) - 4 - 4 - 4  <  0,

   so three dirlinks do not fit even in set form.  What closes it is
   ABSORPTION CREDITS in the spend bound -- the same device [SpecBmap]
   already carries for the bitmap block ([bmap_cost cr al ind], honest
   because of the premise [cr = true -> bmapstart ∈ Sb]), extended to the
   two other blocks a dirlink logs: the DATA block it writes and the
   DIRECTORY's own inode block.  With those three booleans the ledger
   closes with room, and the TIGHTEST arm -- the late failure, which runs
   two iunlockputs after a dirlink that spent everything it was allowed --
   closes at EXACTLY [iput_units].

   The three booleans, the honesty premises they owe, and the four files
   the retrofit touches are written up in projects/fs-sysfile.md's S5a
   section.  Nothing in this file is a contract; it is the arithmetic the
   contracts will be checked against, landed first and on purpose. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import InodeInv.
Require Import SpecBmap.
Require Import SpecIput.
Require Import SpecWritei.
Require Import SpecDirlink.

Local Open Scope nat_scope.

(* ===================================================================== *)
(*  1. WHAT EACH OF create's LOGGING CALLEES SPENDS                       *)
(* ===================================================================== *)

(* ---- ialloc: ONE log_write, of the claimed inode's home block.  The
   inum is chosen by the scan, so no caller can ever credit it: the spend
   is unconditional. *)
Definition ia_spend : nat := 1.

(* ---- iupdate: ONE log_write, of [IBLOCK inum inodestart].  Straight
   line, so the set growth is DETERMINATE (that is [wp_iupdate_gen], S3m
   surprise 1) -- and a caller that has already logged that block can
   ABSORB, which is the credit this file needs and that contract does not
   yet offer.  [cru] is "IBLOCK inum inodestart ∈ Sb". *)
Definition iu_spend (cru : bool) : nat := if cru then 0 else 1.

(* ---- writei at a 16-ALIGNED SIXTEEN-BYTE WINDOW, which is the only
   shape dirlink ever runs (1024 = 64 * 16, so the record never
   straddles): bmap's arm-wise cost, plus writei's own [log_write] of the
   target block -- free when balloc just [bzero]ed it ([al]) or when the
   caller had already logged it ([crd]) -- plus the trailing iupdate.

     [crb] : bmapstart ∈ Sb          (SpecBmap's [cr], verbatim)
     [crd] : the target block ∈ Sb
     [cru] : IBLOCK dinum inodestart ∈ Sb
     [al]  : bmap allocated something ([SpecBmap.bmap_alloced bm bm' fbn])
     [ind] : the window is on the indirect path ([SpecBmap.bmap_ind fbn]) *)
Definition wi16_spend (crb crd cru al ind : bool) : nat :=
  bmap_cost crb al ind + (if (al || crd)%bool then 0 else 1) + iu_spend cru.

(* ...and what must be IN HAND on entry.  Credits do NOT lower this:
   [log_write]'s contract takes [log_opS (S u)] on BOTH arms (a unit in
   hand even to absorb) and so does iupdate's.  bmap's own requirement is
   [SpecBmap.bmap_need]. *)
Definition wi16_need (crb ind : bool) : nat := bmap_need crb ind + 2.

Lemma wi16_need_value_dir : wi16_need false false = 4.
Proof. reflexivity. Qed.

(* For comparison with the LANDED loose bound: whenever the sixteen bytes
   sit inside one block (which 16-alignment guarantees, since
   1024 = 64 * 16), [wi_blocks off 16 = 1] and [wi_cost_bmonly off 16 = 4]
   -- the same number [wi16_need false false] gives.  THE NEED WAS NEVER
   THE PROBLEM; the SPEND bound is. *)
Lemma wi16_need_matches_landed (off : nat) :
  wi_blocks off 16 = 1%nat ->
  wi16_need false false = wi_cost_bmonly off 16.
Proof.
  intros H. unfold wi16_need, bmap_need, wi_cost_bmonly.
  rewrite H. reflexivity.
Qed.

(* ---- dirlink: dirlookup and readi log NOTHING, so a dirlink spends
   either its writei (the append arm) or its iput (the found arm). *)
Definition dl_spend (crb crd cru al ind : bool) : nat :=
  wi16_spend crb crd cru al ind.

Definition dl_need (crb ind : bool) : nat :=
  Nat.max (wi16_need crb ind) iput_units.

Lemma dl_need_values :
  dl_need false false = 4 /\ dl_need true false = 4 /\
  dl_need true true = 5 /\ dl_need false true = 6.
Proof. vm_compute. lia. Qed.

(* ---- iput (through iunlockput): NOTHING unless it frees, and a free
   spends only what it cannot absorb -- itrunc's [bfree]s all hit THE
   bitmap block and its final iupdate hits [IBLOCK inum]. *)
Definition ip_spend (crb cru freed : bool) : nat :=
  if freed then (if crb then 0 else 1) + iu_spend cru else 0.

Definition ip_need : nat := iput_units.

Lemma ip_need_value : ip_need = 3.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  2. THE LEDGER, ARM BY ARM                                             *)
(* ===================================================================== *)

(* create's caller runs ONE begin_op..end_op around the whole body, so
   every arm starts here. *)
Definition cr_u0 : nat := MAXOPBLOCKS.

Lemma cr_u0_value : cr_u0 = 10.
Proof. reflexivity. Qed.

(* ---- ARM C-OK-DIR, the mkdir success path: the longest arm, and the one
   section 18 was written for.  In order (decode offsets in brackets):

     [+0x84]  ialloc                     -- IBLOCK(ip) is new
     [+0xa0]  iupdate(ip)                -- IBLOCK(ip) ∈ Sb, absorbs
     [+0xdc]  dirlink(ip, ".")           -- allocates ip's block 0:
                                            bmapstart and the block are new
     [+0xf0]  dirlink(ip, "..")          -- SAME block, same inode block,
                                            bitmap already paid: absorbs whole
     [+0x102] dirlink(dp, name)          -- worst case: the parent grows,
                                            and grows through its INDIRECT
     [+0x116] iupdate(dp)                -- ABSORBS: the writei inside
                                            dirlink(dp, name) has already
                                            flushed dp's inode block

   It closes at EXACTLY [iput_units], with [iunlockput(dp)] at +0xbe as
   the last claim on the ledger.                                          *)
Theorem cr_budget_mkdir :
  let u1 := cr_u0 - ia_spend in
  let u2 := u1 - iu_spend true in
  let u3 := u2 - dl_spend false false false true false in
  let u4 := u3 - dl_spend true true true false false in
  let u5 := u4 - dl_spend true false false true true in
  let u6 := u5 - iu_spend true in
  (* every call had what it needed IN HAND when it ran ... *)
  ia_spend <= cr_u0 /\
  1 <= u1 /\
  dl_need false false <= u2 /\
  dl_need true false <= u3 /\
  dl_need true true <= u4 /\
  1 <= u5 /\
  (* ... and the parent's iunlockput at +0xbe closes the arm, EXACTLY *)
  ip_need <= u6 /\ u6 = 3.
Proof. vm_compute. lia. Qed.

(* ---- ARM C-OK-FILE, the non-directory success path.  Shorter, but the
   ONE dirlink pays for the bitmap block itself -- nothing preceded it --
   which is why [dl_need false true] (six) is the largest requirement
   anywhere in create.

     [+0x84]  ialloc / [+0xa0] iupdate(ip) / [+0xb4] dirlink(dp, name)
     [+0xbe]  iunlockput(dp)                                                *)
Theorem cr_budget_file :
  let u1 := cr_u0 - ia_spend in
  let u2 := u1 - iu_spend true in
  let u3 := u2 - dl_spend false false false true true in
  ia_spend <= cr_u0 /\
  1 <= u1 /\
  dl_need false true <= u2 /\
  ip_need <= u3.
Proof. vm_compute. lia. Qed.

(* ---- ARM FAIL, entered from the LAST dirlink of the mkdir path: the
   tightest arm in create.  It runs

     [+0x11c] ip->nlink = 0 / [+0x122] iupdate(ip)   -- absorbs
     [+0x128] iunlockput(ip)   -- nlink is 0 and this is the last
                                  reference, so iput FREES: itrunc's
                                  bfrees hit the bitmap (paid) and its
                                  iupdate hits IBLOCK(ip) (paid)
     [+0x12e] iunlockput(dp)   -- dp has links, so iput frees NOTHING

   and it closes at EXACTLY [iput_units].  This is the arm that makes
   credited iput accounting non-optional: with iput's landed
   spend-at-most-three, [iunlockput(ip)] is allowed to leave zero and the
   [iunlockput(dp)] that follows cannot be called at all. *)
Theorem cr_budget_fail_late :
  let u1 := cr_u0 - ia_spend in
  let u2 := u1 - iu_spend true in
  let u3 := u2 - dl_spend false false false true false in
  let u4 := u3 - dl_spend true true true false false in
  let u5 := u4 - dl_spend true false false true true in
  let u6 := u5 - iu_spend true in
  let u7 := u6 - ip_spend true true true in
  ip_need <= u6 /\ ip_need <= u7 /\ u7 = 3.
Proof. vm_compute. lia. Qed.

(* ---- ARM FAIL entered EARLY (the "." link failed): strictly slacker *)
Theorem cr_budget_fail_early :
  let u1 := cr_u0 - ia_spend in
  let u2 := u1 - iu_spend true in
  let u3 := u2 - dl_spend false false false true false in
  let u4 := u3 - iu_spend true in
  let u5 := u4 - ip_spend true true true in
  ip_need <= u4 /\ ip_need <= u5.
Proof. vm_compute. lia. Qed.

(* ---- ARMS N / F-OK / F-BAD / A-FAIL: nothing is logged at all before
   them, so the two iunlockputs of F-BAD are the only requirement. *)
Theorem cr_budget_found :
  ip_need <= cr_u0 /\ ip_need <= cr_u0 - ip_spend true true false.
Proof. vm_compute. lia. Qed.

(* ===================================================================== *)
(*  3. WHAT THE LANDED (UNCREDITED) CONTRACTS GIVE, AND WHY IT IS NOT     *)
(*     ENOUGH -- the refutations, machine checked                        *)
(* ===================================================================== *)

(* THE LOOSE SPEND BOUND BUSTS ON THE THIRD dirlink.  With
   [wi_cost_bmonly] as the per-call allowance and no absorption credit,
   the mkdir path has nothing left for the parent's link. *)
Theorem cr_budget_loose_busts :
  let u1 := cr_u0 - ia_spend in
  let u2 := u1 - 1 in                              (* uncredited iupdate *)
  let u3 := u2 - dl_need false false in            (* dirlink "." at full allowance *)
  let u4 := u3 - dl_need false false in            (* dirlink ".." at full allowance *)
  u4 < dl_need false false.
Proof. vm_compute. lia. Qed.

(* ...AND THE COUNTED FORM IS FURTHER OUT STILL: four dirlinks at
   [dirlink_units] is 28 against 10, which is section 18's opening
   sentence as an inequality. *)
Theorem cr_budget_counted_busts :
  cr_u0 < 4 * dirlink_units.
Proof. vm_compute. lia. Qed.

(* THE CREDIT ON THE DATA BLOCK IS LOAD BEARING, not decorative: without
   it, [dirlink(ip, "..")] pays a second time for the block
   [dirlink(ip, ".")] already logged, and while the mkdir arm survives
   that, the LATE FAIL arm's second iunlockput does not. *)
Theorem cr_budget_needs_data_credit :
  let u1 := cr_u0 - ia_spend in
  let u2 := u1 - iu_spend true in
  let u3 := u2 - dl_spend false false false true false in
  let u4 := u3 - dl_spend true false true false false in   (* crd := false *)
  let u5 := u4 - dl_spend true false false true true in
  let u6 := u5 - iu_spend true in
  let u7 := u6 - ip_spend true true true in
  u7 < ip_need.
Proof. vm_compute. lia. Qed.

(* THE CREDIT ON THE INODE BLOCK IS LOAD BEARING TOO: an uncredited
   iupdate inside every dirlink costs three more units across the mkdir
   arm, and the late fail arm again runs out. *)
Theorem cr_budget_needs_inode_credit :
  let u1 := cr_u0 - ia_spend in
  let u2 := u1 - iu_spend false in                          (* cru := false *)
  let u3 := u2 - dl_spend false false false true false in
  let u4 := u3 - dl_spend true true false false false in    (* cru := false *)
  let u5 := u4 - dl_spend true false false true true in
  let u6 := u5 - iu_spend false in                          (* cru := false *)
  u6 < ip_need.
Proof. vm_compute. lia. Qed.
