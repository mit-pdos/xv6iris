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

   THE SIX SURVIVE nameiparent (fs-sysfile "BLOCKER A, RESOLVED";
   fs-log.md §G.5).  create's walk is a thirteenth logging call and it is
   now on the list below ([np_spend]), but it adds no SEVENTH block: a
   level that frees writes only [bmapstart] -- already one of the six --
   and the freed inode's own block, which is in the group's header
   already, since the unlink that armed the free had to run inside this
   same op window to have emptied it.  That is what [crz] claims and what
   the region's zero receipt proves.  So the walk's whole contribution to
   the ledger is at most ONE unit on a block that was already priced.

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

(* ---- writei at a 16-ALIGNED SIXTEEN-BYTE WINDOW: [wi16_spend] /
   [wi16_need] MOVED to SpecWritei.v (GR-3 stage-3, W1) -- the contract
   itself now exposes the figure ([SpecWritei.wi16_post]), so the
   definitions live at the seam and this file uses them by import.
   [SpecWritei.wi16_spend] inlines [iu_spend]'s if, definitionally equal
   to the shape this file's lemmas were proven at. *)


(* ---- dirlink: dirlookup and readi log NOTHING, so a dirlink spends
   either its writei (the append arm) or its iput (the found arm).
   [dl_spend] / [dl_need] / [dl_need_values] MOVED to SpecDirlink.v (D₀
   pre-stage 1) for the reason [wi16_spend] moved to SpecWritei.v: the
   set-form contract's budget premise is now stated AT [dl_need], because
   the constant [dirlink_units = 7] makes the mkdir chain below
   unsatisfiable -- dirlinks #2 and #3 run with six and five in hand.  The
   definitions live at the seam and this file uses them by import. *)

(* ---- iput (through iunlockput): NOTHING unless it frees, and a free
   spends only what it cannot absorb -- itrunc's [bfree]s all hit THE
   bitmap block and its final iupdate hits [IBLOCK inum]. *)
Definition ip_spend (crb cru freed : bool) : nat :=
  if freed then (if crb then 0 else 1) + iu_spend cru else 0.

Definition ip_need : nat := iput_units.

Lemma ip_need_value : ip_need = 3.
Proof. reflexivity. Qed.

(* ---- nameiparent (fs-log.md §G.5): create's FIRST call, and until group
   absorption it was not on this list at all.  Under group absorption the
   whole walk spends AT MOST ONE unit -- THE bitmap block -- because every
   per-level [iunlockput] runs credited on the inode block ([crz], minted
   at namex's +0xce nlink guard and cashed by the region's receipt), so
   the only thing a freeing level can fail to absorb is the bitmap; and
   the first level that does pay puts [bmapstart] in the op's set, so
   every later level absorbs that too.  (The trio's post does not expose
   this figure YET -- see fs-log.md §G.20 for what still blocks it -- so,
   exactly as when this file was written, the arithmetic lands first and
   the contract is checked against it.)

   [w] is the ONE observable the walk's post exposes: "it paid", which is
   the same fact as [bmapstart ∈ Sb'] afterwards.  It is what makes the
   arms below close, and it is why the row does not simply subtract one:
   whoever pays for the bitmap first, the other absorbs, so the walk's
   unit is create's own first [dirlink]'s unit and not a second one.
   That is the team's refutation of BLOCKER A as an inequality. *)
Definition np_spend (w : bool) : nat := if w then 1 else 0.

Lemma np_spend_le1 (w : bool) : np_spend w <= 1.
Proof. destruct w; vm_compute; lia. Qed.

(* ===================================================================== *)
(*  2. THE LEDGER, ARM BY ARM                                             *)
(* ===================================================================== *)

(* create's caller runs ONE begin_op..end_op around the whole body, so
   every arm starts here. *)
Definition cr_u0 : nat := MAXOPBLOCKS.

Lemma cr_u0_value : cr_u0 = 10.
Proof. reflexivity. Qed.

(* ...and what is left when [nameiparent] -- create's first call, and the
   only one that runs before the body -- hands the parent back.  Every arm
   below is stated at THIS level and quantifies over [w]; at [w = false]
   the arm is the landed one verbatim. *)
Definition cr_uw (w : bool) : nat := cr_u0 - np_spend w.

Lemma cr_uw_values : cr_uw false = 10 /\ cr_uw true = 9.
Proof. vm_compute. lia. Qed.

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
   the last claim on the ledger -- AND IT STILL DOES with the walk's row in
   front of it, at either value of [w].  That is the whole content of
   §G.5's "the zero-slack chains tolerate exactly this": at [w = true] the
   walk's unit comes off the top, and the FIRST dirlink -- the one that
   allocates ip's block 0 and was paying for the bitmap itself -- runs at
   [crb := true] and gives it straight back.  Zero net.               *)
Theorem cr_budget_mkdir (w : bool) :
  let u1 := cr_uw w - ia_spend in
  let u2 := u1 - iu_spend true in
  let u3 := u2 - dl_spend w false false true false in
  let u4 := u3 - dl_spend true true true false false in
  let u5 := u4 - dl_spend true false false true true in
  let u6 := u5 - iu_spend true in
  (* every call had what it needed IN HAND when it ran ... *)
  ia_spend <= cr_uw w /\
  1 <= u1 /\
  dl_need w false <= u2 /\
  dl_need true false <= u3 /\
  dl_need true true <= u4 /\
  1 <= u5 /\
  (* ... and the parent's iunlockput at +0xbe closes the arm, EXACTLY *)
  ip_need <= u6 /\ u6 = 3.
Proof. destruct w; vm_compute; lia. Qed.

(* ---- ARM C-OK-FILE, the non-directory success path.  Shorter, but the
   ONE dirlink pays for the bitmap block itself -- nothing preceded it --
   which is why [dl_need false true] (six) is the largest requirement
   anywhere in create.

     [+0x84]  ialloc / [+0xa0] iupdate(ip) / [+0xb4] dirlink(dp, name)
     [+0xbe]  iunlockput(dp)                                                *)
Theorem cr_budget_file (w : bool) :
  let u1 := cr_uw w - ia_spend in
  let u2 := u1 - iu_spend true in
  let u3 := u2 - dl_spend w false false true true in
  ia_spend <= cr_uw w /\
  1 <= u1 /\
  dl_need w true <= u2 /\
  ip_need <= u3.
Proof. destruct w; vm_compute; lia. Qed.

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
Theorem cr_budget_fail_late (w : bool) :
  let u1 := cr_uw w - ia_spend in
  let u2 := u1 - iu_spend true in
  let u3 := u2 - dl_spend w false false true false in
  let u4 := u3 - dl_spend true true true false false in
  let u5 := u4 - dl_spend true false false true true in
  let u6 := u5 - iu_spend true in
  let u7 := u6 - ip_spend true true true in
  ip_need <= u6 /\ ip_need <= u7 /\ u7 = 3.
Proof. destruct w; vm_compute; lia. Qed.

(* ---- ARM FAIL entered EARLY (the "." link failed): strictly slacker *)
Theorem cr_budget_fail_early (w : bool) :
  let u1 := cr_uw w - ia_spend in
  let u2 := u1 - iu_spend true in
  let u3 := u2 - dl_spend w false false true false in
  let u4 := u3 - iu_spend true in
  let u5 := u4 - ip_spend true true true in
  ip_need <= u4 /\ ip_need <= u5.
Proof. destruct w; vm_compute; lia. Qed.

(* ---- ARM FAIL entered from the NON-DIRECTORY dirlink (+0xc4, the copy
   gcc made for the [type != T_DIR] arm).  It is [cr_budget_file]'s chain
   with the fail tail spliced onto it instead of [iunlockput(dp)]:

     [+0x134] iupdate(ip)      -- IBLOCK(ip) has been in Sb since ialloc
     [+0x13a] iunlockput(ip)   -- nlink was just zeroed and this is the
                                  last reference, so iput FREES; the
                                  bitmap and IBLOCK(ip) are both paid
     [+0x140] iunlockput(dp)   -- dp has links, so iput frees NOTHING

   Both tail claims are ZERO ([iu_spend true = 0] and
   [ip_spend true true true = 0]), so the arm closes on
   [cr_budget_file]'s last conjunct and nothing else -- which is why it
   is strictly slacker than [cr_budget_fail_late], whose three dirlinks
   ran first. *)
Theorem cr_budget_fail_file (w : bool) :
  let u1 := cr_uw w - ia_spend in
  let u2 := u1 - iu_spend true in
  let u3 := u2 - dl_spend w false false true true in
  let u4 := u3 - iu_spend true in
  let u5 := u4 - ip_spend true true true in
  ia_spend <= cr_uw w /\
  1 <= u1 /\
  dl_need w true <= u2 /\
  ip_need <= u3 /\ ip_need <= u4 /\ ip_need <= u5.
Proof. destruct w; vm_compute; lia. Qed.

(* ---- ARMS N / F-OK / F-BAD / A-FAIL: nothing is logged at all before
   them, so the two iunlockputs of F-BAD are the only requirement. *)
Theorem cr_budget_found (w : bool) :
  ip_need <= cr_uw w /\ ip_need <= cr_uw w - ip_spend true true false.
Proof. destruct w; vm_compute; lia. Qed.

(* ...AND THE SAME ARMS AT THE FIGURE THEY CAN ACTUALLY CLAIM.
   [cr_budget_found] above is stated at [ip_spend true true false], i.e.
   with BOTH absorption credits in hand -- and on these arms create holds
   NEITHER: nothing has been logged yet, so [crb] and [cru] are both
   [false], and [crz] is out too (it is minted from a NONZERO nlink
   observation, which ARM G is the negation of).  The honest per-call
   figure is [SpecIput.ip_spend_w w false false], which is [ip_bm w + 1],
   i.e. at most two.  The arms still close with room, and that -- not the
   credited zero -- is what the walk cites. *)
Theorem cr_budget_found_w (w wg wf : bool) :
  let u1 := cr_uw w in
  let u2 := u1 - ip_spend_w wg false false in
  (* ARM N: nothing is called at all *)
  (* ARM G / A-FAIL: ONE uncredited iunlockput *)
  ip_need <= u1 /\
  (* ARM F-BAD: iunlockput(dp) then iunlockput(ip), both uncredited *)
  ip_need <= u2 /\ ip_need <= u2 - ip_spend_w wf false false.
Proof. destruct w, wg, wf; vm_compute; lia. Qed.

(* ===================================================================== *)
(*  3. WHAT THE LANDED (UNCREDITED) CONTRACTS GIVE, AND WHY IT IS NOT     *)
(*     ENOUGH -- the refutations, machine checked                        *)
(* ===================================================================== *)

(* THE RULING'S REFUTATION, machine-checked (GR-3 stage-3): FINDING 6's
   candidate 1 -- exposing only the bitmap amortization, i.e. bounding
   each single-block call by [wi_cost_bmonly - bm_pot] -- cannot close
   the mkdir arm either: the three dirlinks would bound at 4/3/3 where
   the true vector spends are 3/0/3, and the chain leaves less than
   [iput_units] for the closing iunlockput.  The [bm_pot] device credits
   only the BITMAP block; this arm's arithmetic lives on the [crd]/[cru]
   absorptions, which no bitmap-only figure expresses.  This is why
   [SpecWritei.wi16_post] exposes the full [wi16_spend] figure. *)
Lemma wi16_bmonly_amort_insufficient :
  let amort (inS : bool) : nat :=
    (wi_cost_bmonly 0 16 - (if inS then 1 else 0))%nat in
  (cr_u0 - ia_spend - iu_spend true
     - amort false - amort true - amort true < iput_units)%nat.
Proof. vm_compute. lia. Qed.

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

(* ===================================================================== *)
(*  3b. THE [fail:] TAIL AND THE DIRLINK THAT ENTERS IT (D₀ increment 3   *)
(*      finding 2, machine-checked and now landed against the repaired    *)
(*      [SpecDirlink.dl16_post]).                                         *)
(*                                                                        *)
(*  Every route into create's [fail:] at +0x12e is entered by a dirlink   *)
(*  that returned -1, i.e. by a SHORT OR EMPTY append -- and the arm's    *)
(*  first act after the (absorbing) [iupdate(ip)] is [iunlockput(ip)],    *)
(*  which needs [ip_need] IN HAND.  So the entering dirlink's spend bound *)
(*  is what decides whether create's failure arm is payable at all.       *)
(* ===================================================================== *)

(* THE REFUTATION THE REPAIR ANSWERS.  Before it, [dl16_post] was guarded
   by [tot = 16] -- the SUCCESS append -- so on every route into [fail:]
   the only surviving clause was the counted per-call constant
   [dirlink_units = 7], and create's first dirlink runs with eight or nine
   in hand.  Seven from those leaves TWO, and the tail's first
   [iunlockput] wants three. *)
Theorem cr_fail_counted_busts (w : bool) :
  let u1 := cr_uw w - ia_spend in       (* ialloc, unconditional 1        *)
  let u2 := u1 - iu_spend true in       (* iupdate(ip), absorbs           *)
  let u3 := u2 - dirlink_units in       (* THE FAILING dirlink            *)
  let u4 := u3 - iu_spend true in       (* fail: iupdate(ip), absorbs     *)
  u4 < ip_need.
Proof. destruct w; vm_compute; lia. Qed.

(* ...and it is the SPEND bound and nothing else: the counted constant is
   affordable as an ENTRY requirement at every arm ([dl_need false true]
   is six against eight), and even at the very top of the op there is room
   for a whole [dirlink_units] with an iput to spare. *)
Theorem cr_fail_would_fit_at_u0 : ip_need <= cr_u0 - dirlink_units.
Proof. vm_compute. lia. Qed.

(* THE REPAIR'S FIRST CLAUSE, at [0 < tot] -- the short write (1..15) as
   well as the success one.  The entering dirlink reports the credit-aware
   [dl_spend], and the tail closes at EVERY value of the reported
   booleans, [w] included. *)
Theorem cr_fail_closes_with_credit (w crd cru al ind : bool) :
  ip_need <= cr_uw w - ia_spend - iu_spend true - dl_spend w crd cru al ind.
Proof. destruct w, crd, cru, al, ind; vm_compute; lia. Qed.

(* THE REPAIR'S SECOND CLAUSE, at [tot = 0], AT THE FIGURE DIRLINK CAN
   ACTUALLY PROVE ([SpecDirlink.dl0_spend] = writei's coarse four; the
   honest spend is smaller and no contract exposes it).  It closes the two
   routes whose failing dirlink is create's FIRST logging dirlink:
     +0xc4  the non-directory link (ARM FAIL's non-dir entry), and
     +0xf2  the mkdir path's [dirlink(ip, ".")].                        *)
Theorem cr_fail_closes_at_zero (w : bool) :
  ip_need <= cr_uw w - ia_spend - iu_spend true - dl0_spend.
Proof. destruct w; vm_compute; lia. Qed.

(* ...AND WHAT IT DOES NOT CLOSE, which is the gap this stage records
   rather than fixes.  The mkdir path's INTERIOR entries (+0x106's
   [dirlink(ip, "..")] and +0x118's [dirlink(dp, name)]) both run with SIX
   in hand -- at either value of [w], since the first dirlink hands the
   walk's unit straight back -- and four from six leaves two.  THREE would
   close both, and three is what the honest [tot = 0] spend is
   ([bmap_cost] + [iupdate], i.e. [dl_spend] without its data-block term):
   the missing step is writei's post exposing the SPEND half of
   [SpecWritei.wi16_post] at [tot = 0], not anything dirlink can do.  The
   T_DIR sub-branch is parked, so no landed arm depends on this. *)
Theorem cr_fail_mkdir_at_zero_busts (w : bool) :
  let u1 := cr_uw w - ia_spend in
  let u2 := u1 - iu_spend true in
  let u3 := u2 - dl_spend w false false true false in    (* dirlink(ip,".")  *)
  let u4 := u3 - dl_spend true true true false false in  (* dirlink(ip,"..") *)
  (* both interior entries sit at six ... *)
  u3 = 6 /\ u4 = 6 /\
  (* ... where the proven figure busts ... *)
  u3 - dl0_spend < ip_need /\ u4 - dl0_spend < ip_need /\
  (* ... and the honest one would not. *)
  ip_need <= u3 - 3 /\ ip_need <= u4 - 3.
Proof. destruct w; vm_compute; lia. Qed.

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
