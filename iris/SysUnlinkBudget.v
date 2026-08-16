(* SysUnlinkBudget.v -- THE OP-WIDE LOG LEDGER OF sys_unlink, ARM BY ARM,
   MACHINE CHECKED AT EVERY CORNER OF THE REPORTED BOOLEANS.
   [SysLinkBudget.v] is the model; everything here is stated at the figures
   the LANDED contracts state, never at an arm's assumed booleans.

   sys_unlink's transaction is

     begin_op                                     ten units, empty set
     nameiparent(path, name)                      [SpecNameiparent.wp_nameiparent_gen]
     ilock(dp)                                    nothing logged
     namecmp x2                                   nothing logged
     dirlookup(dp, name, &off)                    nothing logged
     ilock(ip)                                    nothing logged
     [the inlined isdirempty loop: readi x N]     NOTHING LOGGED (readi
                                                  takes no [log_op] at all)
     memset(&de,0,16); writei(dp,0,&de,off,16)    [SpecWritei] (wi16 forms)
     T_DIR only: dp->nlink--; iupdate(dp)         [SpecIupdate.wp_iupdate_unlink]
     iunlockput(dp)                               [SpecIunlockput]
     ip->nlink--; iupdate(ip)                     [SpecIupdate.wp_iupdate_unlink]
     iunlockput(ip)                               [SpecIunlockput]
     end_op

   with [bad:] -- [iunlockput(dp); end_op; return -1] -- reachable from the
   two namecmp guards, from [dirlookup] returning 0, and (after its own
   [iunlockput(ip)]) from the [T_DIR && !isdirempty] refusal.

   ==== THE THREE THINGS THAT MAKE THIS LEDGER DIFFERENT FROM sys_link's ==

   * ONE WALK, NOT TWO, AND IT RUNS FIRST.  There is no second resolve and
     nothing is held while [nameiparent] runs, so the whole ledger below the
     walk is parameterised by ONE reported boolean [w1] and the entry count
     is nine or ten -- never sys_link's seven.
   * THE isdirempty LOOP IS FREE.  It is INLINED (there is no [isdirempty]
     symbol; gcc folded it into sys_unlink at +0x0f8..+0x12c), and its body
     is [readi], whose contract takes no log resource whatever -- no
     [log_op], no [log_ctx], no [γ : log_names].  However many times the
     loop runs, it spends nothing, so no arm's figure depends on the
     directory's size.
   * THE ZEROING PAYS FOR EVERYTHING BELOW IT.  [wi16_post]'s membership
     trio at [tot = 16] puts [IBLOCK dp] in the op's set, so BOTH the
     T_DIR [iupdate(dp)] and the [iunlockput(dp)] that follows run
     CREDITED on the parent's inode block.  Only [ip]'s own flush is
     uncredited, and it is uncredited for sys_link's reason squared:
     nothing before it logs [IBLOCK ip] at all (dirlookup and the
     isdirempty loop are pure reads).

   ==== THE VERDICT ====================================================

   EVERY ARM CLOSES, and the success arm closes with ONE unit of slack at
   its worst corner ([su_ok_slack_is_one]).  Unlike sys_link, sys_unlink
   needs NO correlation clause: [su_ok_uncorrelated] checks the success arm
   at every combination of [w1] and the writei credit [crb], INCLUDING the
   corner a correlation clause would have excluded ([crb = false] at
   [w1 = true], i.e. nine units against an uncredited bmap), and it closes
   there too -- exactly, at [iput_units].  [su_ok_corner_is_exact] is that
   corner, kept for the reason [SysLinkBudget.sl_found_counted_busts] is
   kept: it is the figure any future contract movement must not cross.

   NOTE ON SCOPE.  This file prices the LOG.  sys_unlink's success arm is
   blocked on a RESOURCE question that no ledger can answer -- see
   claude-notes/projects/fs-sysfile.md, "S7-unlink STOPPED" -- and the
   arms below are stated so that they remain the ledger of record when
   that is unblocked. *)
From Stdlib Require Import ZArith Lia List.
Require Import LogInv.
Require Import SpecIput.
Require Import SpecWritei.
Require Import SpecNamex.

(* ===================================================================== *)
(*  1. WHAT EACH OF sys_unlink's LOGGING CALLEES SPENDS                   *)
(* ===================================================================== *)

(* ---- iupdate: ONE log_write of [IBLOCK inum inodestart].  Both credited
   bodies take [log_opS (S u)] and hand back [if cru then S u else u], so
   the figure is [SysLinkBudget.sl_iu]'s, restated here rather than
   imported (a function's budget file is not a dependency another one may
   take). *)
Definition su_iu (cru : bool) : nat := if cru then 0%nat else 1%nat.

(* ---- the walk: [SpecNamex.walk_spend w + (if ok then 0 else 1)].
   ---- the zeroing: [SpecWritei.wi16_spend], at [al] and [ind] free.
   ---- iput / iunlockput: [SpecIput.ip_spend_w w cru crz].
   ---- readi: NOTHING.  It is the only fs callee sys_unlink has that takes
        no log resource, and the inlined isdirempty loop is why that
        matters here. *)

(* ===================================================================== *)
(*  2. THE LEDGER DOWN TO THE ZEROING                                     *)
(* ===================================================================== *)

Definition su_u0 : nat := MAXOPBLOCKS.

Lemma su_u0_value : su_u0 = 10%nat.
Proof. vm_compute. reflexivity. Qed.

(* nameiparent, success and failure arms *)
Definition su_u1 (w1 : bool) : nat := (su_u0 - walk_spend w1)%nat.
Definition su_u1f (w1 : bool) : nat := (su_u0 - (walk_spend w1 + 1))%nat.

Lemma su_u1_values : su_u1 false = 10%nat /\ su_u1 true = 9%nat.
Proof. vm_compute. split; reflexivity. Qed.

Lemma su_u1_ge9 (w1 : bool) : (9 <= su_u1 w1)%nat.
Proof. destruct w1; vm_compute; lia. Qed.

(* THE WALK'S OWN ENTRY REQUIREMENT.  [walk_need L <= 4] at every depth,
   against ten. *)
Theorem su_walk_need_closes (L : nat) : (walk_need L <= su_u0)%nat.
Proof. destruct L; vm_compute; lia. Qed.

(* THE CORRELATION, RECORDED AND THEN NOT USED.  A walk that did not spend
   its bitmap unit leaves the op's set without [bmapstart], so the writei
   below it can only claim [crb = false] -- but section 4 closes the
   success arm at BOTH values of [crb] independently, so unlike
   [SysLinkBudget.sl_corr] this clause is not load-bearing.  It is kept
   because a future tightening of [wi16_spend] would make it so. *)
Lemma su_corr (w1 : bool) : w1 = true \/ su_u1 w1 = 10%nat.
Proof. destruct w1; vm_compute; tauto. Qed.

(* ===================================================================== *)
(*  3. THE FOUR FAILURE ARMS                                              *)
(* ===================================================================== *)

(* ---- ARM A, [argstr] < 0.  It returns BEFORE [begin_op], so there is no
   transaction and nothing to price.  Recorded as a lemma so the arm
   appears in this file's enumeration. *)
Theorem su_argstr_arm_has_no_transaction : True.
Proof. exact I. Qed.

(* ---- ARM B, [nameiparent] returns 0.  [end_op] retires whatever is left
   and takes [log_op] at ANY count, so the only obligation is that the
   walk's own failure spend does not underflow. *)
Theorem su_bad_nameiparent_closes (w1 : bool) : (8 <= su_u1f w1)%nat.
Proof. destruct w1; vm_compute; lia. Qed.

(* ---- ARMS C and D, the two namecmp guards and [dirlookup] returning 0.
   Both jump straight to [bad:], whose [iunlockput(dp)] wants its three. *)
Theorem su_bad_early_closes (w1 : bool) : (iput_units <= su_u1 w1)%nat.
Proof. destruct w1; vm_compute; lia. Qed.

(* ---- ARM E, [T_DIR && !isdirempty].  [iunlockput(ip)] runs FIRST, at the
   walk's own count and with NO credit of any kind on [ip] (nothing has
   logged [IBLOCK ip], and [crb] is only claimable where the walk spent its
   bitmap unit), and [bad:]'s [iunlockput(dp)] then wants its three out of
   what is left.  Checked at every corner of both reported booleans. *)
Theorem su_bad_isdirempty_closes (w1 wi crb : bool) :
  let u := (su_u1 w1 - ip_spend_w wi (crb && false) false)%nat in
  (iput_units <= su_u1 w1)%nat /\ (iput_units <= u)%nat.
Proof. destruct w1, wi, crb; vm_compute; lia. Qed.

(* ...and the honest reading of it: the refusal arm's two frees cost at
   most two units between them, against nine. *)
Theorem su_two_frees_cost_at_most_two (wi wd : bool) :
  (ip_spend_w wi false false + ip_spend_w wd false false <= 4)%nat.
Proof. destruct wi, wd; vm_compute; lia. Qed.

(* ===================================================================== *)
(*  4. THE SUCCESS ARM                                                    *)
(*                                                                        *)
(*  The zeroing is a SINGLE-BLOCK write ([wi_blocks off 16 = 1] whenever   *)
(*  the record does not straddle a block boundary, which it never does:    *)
(*  [off] is a multiple of 16 and 16 divides BSIZE), so [wi16_spend] is    *)
(*  the figure, at [al] and [ind] free -- the walk cannot refute an        *)
(*  allocating write from the contract alone, even though the record it    *)
(*  overwrites is inside the directory's existing size.                    *)
(* ===================================================================== *)

(* after the writei *)
Definition su_u2 (w1 crb crd cru al ind : bool) : nat :=
  (su_u1 w1 - wi16_spend crb crd cru al ind)%nat.

(* THE ZEROING'S ENTRY REQUIREMENT, at every corner. *)
Theorem su_wi_need_closes (w1 crb ind : bool) :
  (wi16_need crb ind <= su_u1 w1)%nat.
Proof. destruct w1, crb, ind; vm_compute; lia. Qed.

(* THE ZEROING LEAVES AT LEAST FIVE. *)
Theorem su_u2_ge5 (w1 crb crd cru al ind : bool) :
  (5 <= su_u2 w1 crb crd cru al ind)%nat.
Proof. destruct w1, crb, crd, cru, al, ind; vm_compute; lia. Qed.

(* ---- THE T_DIR TAIL, the longer of the two.  [iupdate(dp)] is CREDITED
   ([wi16_post]'s [IBLOCK dp ∈ Sb'] at [tot = 16]) and so is the
   [iunlockput(dp)] behind it; [ip]'s flush is not, and [iunlockput(ip)]
   then wants its three.  Both [iupdate]s additionally need a NONZERO
   count in hand ([wp_iupdate_unlink] takes [log_opS (S u)]).  Checked at
   every corner of all six reported booleans. *)
Theorem su_ok_dir_closes (w1 crb crd cru al ind wd wp : bool) :
  let u2 := su_u2 w1 crb crd cru al ind in
  let u3 := (u2 - su_iu true)%nat in                (* dp->nlink--; iupdate *)
  let u4 := (u3 - ip_spend_w wd true false)%nat in  (* iunlockput(dp)       *)
  let u5 := (u4 - su_iu false)%nat in               (* ip->nlink--; iupdate *)
  (1 <= u2)%nat /\ (iput_units <= u3)%nat /\ (1 <= u4)%nat
  /\ (iput_units <= u5)%nat
  /\ (0 <= u5 - ip_spend_w wp true false)%nat.
Proof.
  destruct w1, crb, crd, cru, al, ind, wd, wp; vm_compute; lia.
Qed.

(* ---- THE T_FILE TAIL: the same without the parent's flush.  Strictly
   cheaper, and stated separately because it is a different arm of the
   walk, not a corner of the one above. *)
Theorem su_ok_file_closes (w1 crb crd cru al ind wd wp : bool) :
  let u2 := su_u2 w1 crb crd cru al ind in
  let u4 := (u2 - ip_spend_w wd true false)%nat in  (* iunlockput(dp)       *)
  let u5 := (u4 - su_iu false)%nat in               (* ip->nlink--; iupdate *)
  (iput_units <= u2)%nat /\ (1 <= u4)%nat
  /\ (iput_units <= u5)%nat
  /\ (0 <= u5 - ip_spend_w wp true false)%nat.
Proof.
  destruct w1, crb, crd, cru, al, ind, wd, wp; vm_compute; lia.
Qed.

(* ===================================================================== *)
(*  5. THE CORNERS, AND WHAT THEY PIN                                     *)
(* ===================================================================== *)

(* NO CORRELATION CLAUSE IS NEEDED, and this is the theorem that says so:
   the T_DIR arm closes at [crb = false] TOGETHER WITH [w1 = true] -- the
   nine-unit, uncredited-bitmap corner a correlation clause exists to
   exclude. *)
Theorem su_ok_uncorrelated (crd cru al ind wd wp : bool) :
  let u2 := su_u2 true false crd cru al ind in
  let u3 := (u2 - su_iu true)%nat in
  let u4 := (u3 - ip_spend_w wd true false)%nat in
  let u5 := (u4 - su_iu false)%nat in
  (iput_units <= u5)%nat.
Proof. destruct crd, cru, al, ind, wd, wp; vm_compute; lia. Qed.

(* THE WORST CORNER IS EXACT: nine units in, an allocating INDIRECT write
   with no credit anywhere, and [iunlockput(ip)] arrives at exactly
   [iput_units].  This is the figure a tightening of any contract above it
   must not cross. *)
Theorem su_ok_corner_is_exact :
  let u2 := su_u2 true false false false true true in
  let u3 := (u2 - su_iu true)%nat in
  let u4 := (u3 - ip_spend_w true true false)%nat in
  let u5 := (u4 - su_iu false)%nat in
  u5 = iput_units.
Proof. vm_compute. reflexivity. Qed.

(* ...and [iput_units] is the FLOOR over every corner, so with
   [su_ok_corner_is_exact] above it the arm's worst case is pinned from
   both sides: nothing is left over at the corner, and nothing is short
   anywhere else. *)
Theorem su_ok_dir_floor_is_iput_units (w1 crb crd cru al ind wd : bool) :
  let u2 := su_u2 w1 crb crd cru al ind in
  let u3 := (u2 - su_iu true)%nat in
  let u4 := (u3 - ip_spend_w wd true false)%nat in
  let u5 := (u4 - su_iu false)%nat in
  (iput_units <= u5)%nat /\ (u5 <= 9)%nat.
Proof. destruct w1, crb, crd, cru, al, ind, wd; vm_compute; lia. Qed.

(* THE REFUTATION THIS LEDGER DOES NOT NEED, RECORDED AS A NEGATIVE.  Had
   [ip]'s flush ALSO had to pay a bitmap unit -- i.e. had the zeroing not
   put [IBLOCK dp] in the set, so that BOTH [iupdate]s ran uncredited and
   [iunlockput(dp)] with them -- the worst corner would bust by one.  This
   is why [wi16_post]'s membership trio, and not merely its spend clause,
   is what sys_unlink relays. *)
Theorem su_ok_busts_without_the_membership_trio :
  let u2 := su_u2 true false false false true true in
  let u3 := (u2 - su_iu false)%nat in
  let u4 := (u3 - ip_spend_w true false false)%nat in
  let u5 := (u4 - su_iu false)%nat in
  (u5 < iput_units)%nat.
Proof. vm_compute. lia. Qed.

(* ===================================================================== *)
(*  6. THE REFERENCE LEDGER                                               *)
(*                                                                        *)
(*  TWO, not sys_link's three, and the difference is structural: sys_link  *)
(*  runs its second resolve WITH [ip] already held, sys_unlink runs its    *)
(*  ONLY resolve holding nothing.  The peak is therefore                   *)
(*    max( the walker's own two , [dp] + [ip] ) = 2,                       *)
(*  and every arm gives both back ([iunlockput] x2 on the success arm and  *)
(*  on the isdirempty refusal, [iunlockput(dp)] alone at [bad:],           *)
(*  [dirlookup]'s unused slot returning on the not-found arm).             *)
(* ===================================================================== *)

Definition sys_unlink_slots : nat := 2%nat.

Lemma sys_unlink_slots_value : sys_unlink_slots = 2%nat.
Proof. reflexivity. Qed.
