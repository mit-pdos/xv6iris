(* SysLinkBudget.v -- THE OP-WIDE LOG LEDGER OF sys_link, ARM BY ARM,
   MACHINE CHECKED AT EVERY CORNER OF THE REPORTED BOOLEANS.
   [CreateBudget.v] is the model; everything here is stated at the figures
   the LANDED contracts state, never at an arm's assumed booleans.

   sys_link's transaction is

     begin_op                                     ten units, empty set
     namei(old)          success                  [SpecNamei.wp_namei_gen]
     ip->nlink++; iupdate(ip)                     [SpecIupdate.wp_iupdate_link]
     iunlock(ip)                                  nothing logged
     nameiparent(new, name)                       [SpecNameiparent.wp_nameiparent_gen]
     ilock(dp)                                    nothing logged
     dirlink(dp, name, ip->inum)                  [SpecDirlink.wp_dirlink_gen]
     iunlockput(dp); iput(ip)                     [SpecIunlockput] / [SpecIput]
     end_op

   with [bad:] -- [ilock(ip); ip->nlink--; iupdate(ip); iunlockput(ip)] --
   reachable from the nameiparent failure and from either dirlink failure.

   THE CORRELATION CLAUSE.  Neither walk takes a bitmap credit, so both may
   report [w = true] and spend a unit; but a walk that DID spend it reports
   [bmapstart ∈ Sb'], so at the one corner where the dirlink runs
   UNCREDITED both [walk_spend]s were zero and the count is two higher.
   That is [sl_corr], and every arm below is checked at both corners --
   the same device [ProofCreate]'s mkdir arm needed ("`bmapstart ∈ Sb3 \/
   9 <= n3`", fs-sysfile step 1a).

   THE VERDICT.  Every arm closes, and three of them EXACTLY.  The one
   that decided a contract is dirlink's FOUND arm: it is payable only
   because [SpecDirlink]'s post states the found arm's own spend
   ([found = true -> ncount - iput_units <= n']).  Against the counted
   [dirlink_units] alone it is unpayable at every corner --
   [sl_found_counted_busts] / [sl_found_counted_busts_by_one] are that
   refutation, kept for the reason [CreateBudget.cr_fail_counted_busts] is
   kept -- and [sl_found_at_four_busts] is why three, not four, is the
   figure the clause had to state. *)
From Stdlib Require Import ZArith Lia List.
Require Import LogInv.
Require Import SpecIput.
Require Import SpecWritei.
Require Import SpecDirlink.
Require Import SpecNamex.

(* ===================================================================== *)
(*  1. WHAT EACH OF sys_link's LOGGING CALLEES SPENDS                     *)
(* ===================================================================== *)

(* ---- iupdate: ONE log_write of [IBLOCK inum inodestart].  Both of the
   credited bodies ([wp_iupdate_link], [wp_iupdate_unlink]) take
   [log_opS (S u)] and hand back [if cru then S u else u], so the figure is
   [CreateBudget.iu_spend]'s, restated here rather than imported (a
   function's budget file is not a dependency another one may take). *)
Definition sl_iu (cru : bool) : nat := if cru then 0%nat else 1%nat.

(* ---- the two walks: [SpecNamex.walk_spend w + (if ok then 0 else 1)].
   ---- dirlink: [SpecDirlink.dl_spend] = [SpecWritei.wi16_spend] on the
        APPEND arm, and [dirlink_units] and nothing else on the FOUND arm.
   ---- iput / iunlockput: [SpecIput.ip_spend_w w cru crz]. *)

(* ===================================================================== *)
(*  2. THE LEDGER DOWN TO THE dirlink                                     *)
(* ===================================================================== *)

Definition sl_u0 : nat := MAXOPBLOCKS.

Lemma sl_u0_value : sl_u0 = 10%nat.
Proof. vm_compute. reflexivity. Qed.

(* namei(old), success arm *)
Definition sl_u1 (w1 : bool) : nat := (sl_u0 - walk_spend w1)%nat.

(* [ip->nlink++; iupdate(ip)] -- UNCREDITED, and that is forced: namei
   never locks the inode it returns, so nothing puts [IBLOCK ip] in the
   op's set before this flush.  (Everything AFTER it may claim
   [cru := true], which is what pays for the [bad:] arm's flush.) *)
Definition sl_u2 (w1 : bool) : nat := (sl_u1 w1 - sl_iu false)%nat.

(* nameiparent(new), success and failure arms *)
Definition sl_u3 (w1 w2 : bool) : nat := (sl_u2 w1 - walk_spend w2)%nat.
Definition sl_u3f (w1 w2 : bool) : nat := (sl_u2 w1 - (walk_spend w2 + 1))%nat.

Lemma sl_u3_values :
  sl_u3 false false = 9%nat /\ sl_u3 true false = 8%nat /\
  sl_u3 false true = 8%nat  /\ sl_u3 true true = 7%nat.
Proof. vm_compute. repeat split. Qed.

Lemma sl_u3_ge7 (w1 w2 : bool) : (7 <= sl_u3 w1 w2)%nat.
Proof. destruct w1, w2; vm_compute; lia. Qed.

(* THE CORRELATION CLAUSE, as arithmetic: the dirlink runs uncredited on
   the bitmap block only where NEITHER walk paid for it, and there the
   count is nine. *)
Lemma sl_corr (w1 w2 : bool) :
  (w1 = true \/ w2 = true) \/ sl_u3 w1 w2 = 9%nat.
Proof. destruct w1, w2; vm_compute; tauto. Qed.

(* ===================================================================== *)
(*  3. THE ARMS THAT CLOSE                                                *)
(* ===================================================================== *)

(* ---- ARM E ([bad:] entered from nameiparent returning 0).  The flush is
   CREDITED -- the [++] put [IBLOCK ip] in the set -- so it costs nothing,
   and the tail's iunlockput has its three. *)
Theorem sl_bad1_closes (w1 w2 : bool) :
  (1 <= sl_u3f w1 w2)%nat /\
  (iput_units <= sl_u3f w1 w2 - sl_iu true)%nat.
Proof. destruct w1, w2; vm_compute; lia. Qed.

(* ---- dirlink's ENTRY requirement, at both corners of [sl_corr]. *)
Theorem sl_dl_need_credited (w1 w2 ind : bool) :
  (dl_need true ind <= sl_u3 w1 w2)%nat.
Proof. destruct w1, w2, ind; vm_compute; lia. Qed.

Theorem sl_dl_need_uncredited (ind : bool) :
  (dl_need false ind <= sl_u3 false false)%nat.
Proof. destruct ind; vm_compute; lia. Qed.

(* ---- ARM G, the success append ([found = false], [tot = 16]).  The
   following [iunlockput(dp)] is credited on the inode block by
   [dl16_post]'s membership trio at [0 < tot], and [iput(ip)] then closes
   the arm EXACTLY. *)
Theorem sl_ok_closes_credited (w1 w2 crd al ind wd : bool) :
  let u4 := (sl_u3 w1 w2 - wi16_spend true crd false al ind)%nat in
  (iput_units <= u4)%nat /\
  (iput_units <= u4 - ip_spend_w wd true false)%nat.
Proof. destruct w1, w2, crd, al, ind, wd; vm_compute; lia. Qed.

Theorem sl_ok_closes_uncredited (crd al ind wd : bool) :
  let u4 := (sl_u3 false false - wi16_spend false crd false al ind)%nat in
  (iput_units <= u4)%nat /\
  (iput_units <= u4 - ip_spend_w wd true false)%nat.
Proof. destruct crd, al, ind, wd; vm_compute; lia. Qed.

(* ---- ARM F-0, the EMPTY append ([found = false], [tot = 0]: writei's own
   -1 return on a full directory, or the bmap out-of-blocks break).
   [dl16_post]'s spend clause is UNGUARDED inside [found = false], so the
   credit-aware figure still applies -- but there is no membership, so the
   [iunlockput(dp)] that follows is uncredited on the inode block.  At the
   credited corner [crb = true] forces [w = false] by [SpecIput]'s own
   report clause, which is what keeps this arm alive. *)
Theorem sl_fail0_closes_credited (w1 w2 crd al ind : bool) :
  let u4 := (sl_u3 w1 w2 - wi16_spend true crd false al ind)%nat in
  let u5 := (u4 - ip_spend_w false false false)%nat in
  (iput_units <= u4)%nat /\ (1 <= u5)%nat /\
  (iput_units <= u5 - sl_iu true)%nat.
Proof. destruct w1, w2, crd, al, ind; vm_compute; lia. Qed.

Theorem sl_fail0_closes_uncredited (crd al ind wd : bool) :
  let u4 := (sl_u3 false false - wi16_spend false crd false al ind)%nat in
  let u5 := (u4 - ip_spend_w wd false false)%nat in
  (iput_units <= u4)%nat /\ (1 <= u5)%nat /\
  (iput_units <= u5 - sl_iu true)%nat.
Proof. destruct crd, al, ind, wd; vm_compute; lia. Qed.

(* ===================================================================== *)
(*  4. ARM F-FOUND, AND THE CONTRACT IT DECIDED                           *)
(*                                                                        *)
(*  [link(old, new)] with [new] ALREADY PRESENT makes [dirlink]'s          *)
(*  [dirlookup] match, so it [iput]s the child and returns -1 without      *)
(*  writing anything.  sys_link cannot refute that arm the way create      *)
(*  does (create holds [ilock(dp)] across its OWN [dirlookup] miss and     *)
(*  reads the miss back out of [dir_first] -- [ProofCreate.v]'s three      *)
(*  [destruct found] sites all leave through [exfalso]; sys_link never     *)
(*  looks [name] up before linking it), so the arm has to be PAID FOR.     *)
(*                                                                        *)
(*  [dl16_post] is guarded by [found = false], so what pays for it is      *)
(*  [SpecDirlink]'s SEPARATE found-arm clause                              *)
(*  [found = true -> ncount - iput_units <= n'].                           *)
(* ===================================================================== *)

(* THE REFUTATION THAT CLAUSE ANSWERS.  Against the counted
   [dirlink_units = 7] alone the arm is unpayable at every corner. *)
Theorem sl_found_counted_busts (w1 w2 : bool) :
  (sl_u3 w1 w2 - dirlink_units < iput_units)%nat.
Proof. destruct w1, w2; vm_compute; lia. Qed.

(* ...and it busts AT THE BEST CORNER BY EXACTLY ONE UNIT, which is why no
   rearrangement of the ledger above it could have paid for it: nine is the
   most the two walks and the mint can leave, and seven from nine is two. *)
Theorem sl_found_counted_busts_by_one :
  (sl_u3 false false - dirlink_units)%nat = 2%nat /\ iput_units = 3%nat.
Proof. vm_compute. split; reflexivity. Qed.

(* THE CLAUSE AS LANDED.  A found-arm spend at the CONSTANT [iput_units]
   closes the arm at every corner -- exactly, at the credited one, where
   [crb = true] forces the [iunlockput(dp)] report [w = false]. *)
Theorem sl_found_closes_at_iput_units_credited (w1 w2 : bool) :
  let u4 := (sl_u3 w1 w2 - iput_units)%nat in
  let u5 := (u4 - ip_spend_w false false false)%nat in
  (iput_units <= u4)%nat /\ (1 <= u5)%nat /\
  (iput_units <= u5 - sl_iu true)%nat.
Proof. destruct w1, w2; vm_compute; lia. Qed.

Theorem sl_found_closes_at_iput_units_uncredited (wd : bool) :
  let u4 := (sl_u3 false false - iput_units)%nat in
  let u5 := (u4 - ip_spend_w wd false false)%nat in
  (iput_units <= u4)%nat /\ (1 <= u5)%nat /\
  (iput_units <= u5 - sl_iu true)%nat.
Proof. destruct wd; vm_compute; lia. Qed.

(* ...and THREE is the largest constant that would have worked: FOUR busts
   again, which is what pinned the clause's figure. *)
Theorem sl_found_at_four_busts :
  let u4 := (sl_u3 true true - 4)%nat in
  (iput_units <= u4)%nat /\ (iput_units > u4 - ip_spend_w false false false)%nat.
Proof. vm_compute. lia. Qed.

(* ...and the HONEST figure is at or below it: dirlink's found arm logs
   nothing but its own iput, whose credited worst case is [ip_spend_w]. *)
Theorem sl_found_honest (wf cruf : bool) :
  (ip_spend_w wf cruf false <= iput_units)%nat.
Proof. destruct wf, cruf; vm_compute; lia. Qed.
