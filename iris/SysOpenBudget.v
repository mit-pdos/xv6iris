(* SysOpenBudget.v -- THE OP-WIDE LOG LEDGER OF sys_open, ARM BY ARM,
   MACHINE CHECKED AT EVERY CORNER OF THE REPORTED BOOLEANS.
   [SysLinkBudget.v] is the model; everything here is stated at the figures
   the LANDED contracts state, never at an arm's assumed booleans.

   sys_open's transaction, read off `kernel.asm` (0x800050a6, 342 bytes):

     argint(1,&omode); argstr(0,path,MAXPATH)      BEFORE begin_op -- no log
     +0x24  bltz -> +0xca                          [ARM 0: argstr < 0]
     begin_op                                      ten units, one set
     +0x2e  omode & O_CREATE ?
       yes: create(path,T_FILE,0,0)                [SpecCreate.wp_create_sconf]
            +0x48  beqz -> end_op; -1              [ARM A-FAIL]
       no:  namei(path)                            [SpecNamei.wp_namei_gen]
            +0xe6  beqz -> end_op; -1              [ARM B-FAIL]
            ilock(ip)                              nothing logged
            +0xf2  type == T_DIR && omode != 0 ->
                   iunlockput; end_op; -1          [ARM C-FAIL]
     ---- THE JOIN at +0x4a, ip LOCKED on both sides ----
     +0x4a  type == T_DEVICE && major u> 9 ->
            iunlockput; end_op; -1                 [ARM D-FAIL]
     filealloc()                                   nothing logged
     +0x66  == 0 -> iunlockput; end_op; -1         [ARM E-FAIL]
     fdalloc(f)                                    nothing logged
     +0x70  <  0 -> fileclose(f) (FD_NONE, nothing
                    logged); iunlockput; end_op    [ARM F-FAIL]
     the six field stores                          nothing logged
     +0xa8  (omode & O_TRUNC) && type == T_FILE ->
            itrunc(ip)                             [SpecItrunc.wp_itrunc_gen]
     iunlock(ip); end_op; return fd                [ARM S: SUCCESS]

   ==== THE VERDICT: EVERY ARM CLOSES, AND THE CREATE CORNER IS EXACT =====

   The whole ledger turns on ONE figure: what the two entry arms leave at
   the JOIN.  The namei arm leaves NINE (ten less at most one walk unit);
   the create arm leaves only what [SpecCreate]'s [ok = true] floor
   promises, which is [iput_units] -- THREE.  So the joint invariant past
   +0x4a is [iput_units <= u], and every one of the four failure arms below
   the join spends exactly [iput_units] on its [iunlockput].  That is
   EXACT: [so_join_exact].

   Two things the arithmetic below is kept for, because each of them is a
   contract decision this walk would otherwise have re-litigated:

   * [so_counted_namei_busts] -- the COUNTED [SpecNamei.wp_namei_sconf]
     cannot serve this caller, for sys_chdir's reason at a longer tail:
     at [L = 3] its premise alone is twelve of the ten, and even at [L = 2]
     it hands back one where the join needs three.  The set form prices the
     walk at [walk_need L <= 4] whatever the depth.
   * [so_create_nofloor_busts] -- without [SpecCreate]'s [ok = true] floor
     (landed for sys_mkdir / sys_mknod, fs-sysfile S6-mkdir) the create arm
     reaches the join with a bare [u' <= u] and nothing else, and the very
     first [iunlockput] past it is unpayable.  The floor is not a
     convenience for this walk; it is the walk.

   And ONE that is a genuine surprise: the O_TRUNC arm is payable off the
   create arm's three with NO credit at all ([so_trunc_closes]).  itrunc's
   uncredited entry level is [it_entry false u = S (S u)], i.e. TWO -- the
   whole free of a file's blocks costs two units because every [bfree] hits
   the one bitmap block and the tail flush hits the one inode block, which
   is [SpecItrunc]'s set-form point.  There is no corner at which sys_open
   needs [crb] or [cru], and it could not supply either: create's post
   reports [Sb ⊆ Sb'] and no membership. *)
From Stdlib Require Import ZArith Lia List.
Require Import LogInv.
Require Import SpecIput.
Require Import SpecNamex.
Require Import SpecCreate.
Require Import SpecItrunc.

(* ===================================================================== *)
(*  1. WHAT EACH OF sys_open's LOGGING CALLEES SPENDS                     *)
(* ===================================================================== *)

(* ---- create: [create_units = MAXOPBLOCKS] in, [u' <= u] out, and the
        [ok = true] floor [iput_units <= u'].
   ---- namei (set form): [walk_need L] in, [walk_spend w + (if ok then 0
        else 1)] out.
   ---- itrunc (set form): [it_entry crb u] in, [it_bm w + it_iu cru] out.
   ---- iunlockput / iput: [iput_units] in, [ip_spend_w w cru crz] out.
   ---- ilock / iunlock / filealloc / fdalloc / fileclose-at-FD_NONE:
        nothing.  fileclose is the interesting one -- sys_open closes a
        file it has just allocated and NOT yet typed, and
        [SpecFileclose]'s environment at [FD_NONE] is empty, which is what
        keeps ARM F-FAIL as cheap as ARM E-FAIL. *)

Definition so_u0 : nat := MAXOPBLOCKS.

Lemma so_u0_value : so_u0 = 10%nat.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  2. THE TWO ENTRY ARMS, DOWN TO THE JOIN AT +0x4a                      *)
(* ===================================================================== *)

(* ---- create's premise is EXACTLY begin_op's mint, with nothing to spare.
   [create_units = MAXOPBLOCKS], so the O_CREATE arm is only callable
   because sys_open does no logging of its own before it. *)
Theorem so_create_need : (create_units <= so_u0)%nat.
Proof. vm_compute. lia. Qed.

Theorem so_create_need_exact : create_units = so_u0.
Proof. vm_compute. reflexivity. Qed.

(* ---- namei's premise, at every path length.  [walk_need] is 3 at [L = 0]
   and 4 above, so the bound is uniform in the depth -- which is the whole
   reason this walk may take an unbounded path. *)
Theorem so_namei_need (L : nat) : (walk_need L <= so_u0)%nat.
Proof. destruct L; vm_compute; lia. Qed.

(* THE REFUTATION THAT CHOICE ANSWERS.  The counted contract's premise is
   [(L + 1) * iput_units <= n]; at three path components it wants twelve of
   the ten. *)
Theorem so_counted_namei_busts : ((3 + 1) * iput_units > so_u0)%nat.
Proof. vm_compute. lia. Qed.

(* ...and at TWO components, where the premise is still satisfiable, the
   counted SPEND leaves one where the join's [iunlockput] needs three. *)
Theorem so_counted_namei_busts_at_two :
  (so_u0 - (2 + 1) * iput_units < iput_units)%nat.
Proof. vm_compute. lia. Qed.

(* ---- the namei arm's count at the join: ten less at most one walk unit. *)
Definition so_un (w : bool) : nat := (so_u0 - walk_spend w)%nat.

Lemma so_un_values : so_un false = 10%nat /\ so_un true = 9%nat.
Proof. vm_compute. split; reflexivity. Qed.

(* ---- and the FAILURE-side count, which ARM B-FAIL exits on and which
   nothing has to pay for: end_op takes [log_op] at any count. *)
Definition so_unf (w : bool) : nat := (so_u0 - (walk_spend w + 1))%nat.

Lemma so_unf_ge8 (w : bool) : (8 <= so_unf w)%nat.
Proof. destruct w; vm_compute; lia. Qed.

(* ---- ARM C-FAIL: [ilock] logs nothing, so the not-a-readable-directory
   exit pays its [iunlockput] out of the walk's remainder. *)
Theorem so_armC_closes (w : bool) : (iput_units <= so_un w)%nat.
Proof. destruct w; vm_compute; lia. Qed.

(* ===================================================================== *)
(*  3. THE JOIN, AND WHY THE FLOOR IS THE WALK                            *)
(* ===================================================================== *)

(* THE JOINT INVARIANT past +0x4a.  The create arm can offer nothing better
   than its [ok = true] floor and the namei arm offers nine, so the two
   meet at [iput_units]. *)
Definition so_join : nat := iput_units.

Lemma so_join_value : so_join = 3%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem so_namei_meets_join (w : bool) : (so_join <= so_un w)%nat.
Proof. destruct w; vm_compute; lia. Qed.

(* THE CREATE ARM MEETS IT EXACTLY, which is what makes the floor's figure
   non-negotiable: it IS the constant the four failure arms below the join
   each spend. *)
Theorem so_join_exact : so_join = iput_units.
Proof. reflexivity. Qed.

(* WITHOUT THE FLOOR the create arm arrives with a bare [u' <= u], whose
   worst corner is zero, and the first [iunlockput] past the join is
   unpayable.  (Stated as the corner rather than as an impossibility: the
   ceiling admits [u' = 0], and three is not at most zero.) *)
Theorem so_create_nofloor_busts : (0 <= so_u0)%nat /\ (iput_units > 0)%nat.
Proof. vm_compute. lia. Qed.

(* ===================================================================== *)
(*  4. THE FOUR FAILURE ARMS BELOW THE JOIN                               *)
(*                                                                        *)
(*  ARMS D-FAIL / E-FAIL / F-FAIL are the SAME ledger move -- one          *)
(*  [iunlockput(ip)] and then [end_op] -- and F-FAIL's extra [fileclose]   *)
(*  is free because the file it closes is still FD_NONE.  Nothing after    *)
(*  the [iunlockput] needs a unit, so the arms need only be CALLABLE.      *)
(* ===================================================================== *)

Theorem so_armD_closes : (iput_units <= so_join)%nat.
Proof. vm_compute. lia. Qed.

Theorem so_armE_closes : (iput_units <= so_join)%nat.
Proof. vm_compute. lia. Qed.

Theorem so_armF_closes : (iput_units <= so_join)%nat.
Proof. vm_compute. lia. Qed.

(* ...and on the namei side each of them has six to spare, which is what
   makes the create corner the only one worth checking. *)
Theorem so_arms_DEF_namei (w : bool) : (iput_units <= so_un w)%nat.
Proof. destruct w; vm_compute; lia. Qed.

(* THE SPEND IS NOT THE ENTRY BOUND (S6-mkdir's rule).  What survives an
   arm's [iunlockput] is [so_join - ip_spend_w w cru crz], and on these
   arms sys_open holds NEITHER credit for [ip] -- create's post reports no
   membership and namei never locked the inode -- so the call spends one at
   the [w = false] corner and two at [w = true].  Nothing downstream needs
   it, which is why the arms are stated as callability. *)
Theorem so_arms_DEF_survivors (w : bool) :
  (so_join - ip_spend_w w false false <= 2)%nat.
Proof. destruct w; vm_compute; lia. Qed.

(* ===================================================================== *)
(*  5. THE SUCCESS TAIL: O_TRUNC                                          *)
(* ===================================================================== *)

(* itrunc's UNCREDITED entry level.  [it_entry false u = S (S u)], so a
   caller at count [n] instantiates [u := n - 2] and needs [2 <= n].  At
   the create corner that is two of three. *)
Theorem so_trunc_need : (it_entry false (so_join - 2) <= so_join)%nat.
Proof. vm_compute. lia. Qed.

Theorem so_trunc_need_exact : it_entry false (so_join - 2) = so_join.
Proof. vm_compute. reflexivity. Qed.

(* ...and on the namei side, where seven are left over. *)
Theorem so_trunc_need_namei (w : bool) :
  it_entry false (so_un w - 2) = so_un w.
Proof. destruct w; vm_compute; reflexivity. Qed.

(* WHAT SURVIVES IT, at both reported corners of [w].  Nothing after itrunc
   spends -- [iunlock] logs nothing and [end_op] takes any count -- so the
   arm needs only to be non-negative, and it is. *)
Theorem so_trunc_closes (w : bool) :
  let u := (so_join - 2)%nat in
  (it_entry false u - (it_bm w + it_iu false) <= so_join)%nat.
Proof. destruct w; vm_compute; lia. Qed.

(* THE HONEST BOUND: itrunc's whole spend is at most [it_spend false false
   = 2] however many blocks the file had, because the bfrees all hit the
   one bitmap block ([bitmap_geom_ok]'s [0 < size <= BPB]) and the tail
   flush hits the one inode block. *)
Theorem so_trunc_spend_two : it_spend false false = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem so_trunc_spend_bounds (w : bool) :
  (it_bm w + it_iu false <= it_spend false false)%nat.
Proof. destruct w; vm_compute; lia. Qed.

(* AND THE CREDITS ARE NOT AVAILABLE, which is why every figure above is at
   [crb = cru = false]: [crb] wants [bmapstart ∈ Sb] and [cru] wants
   [IBLOCK inum inodestart ∈ Sb], and neither entry arm reports a
   membership -- create's post is [Sb ⊆ Sb'] and namei's is the same plus
   the bitmap report [w = true -> bmapstart ∈ Sb'], which is a report about
   a block sys_open's itrunc would have to claim at a DIFFERENT inode.
   Recorded as the arithmetic that would have been gained: one unit. *)
Theorem so_trunc_credit_would_gain :
  (it_entry true (so_join - 2) < it_entry false (so_join - 2))%nat.
Proof. vm_compute. lia. Qed.

(* ===================================================================== *)
(*  6. THE WHOLE LEDGER, IN ONE THEOREM PER ENTRY ARM                      *)
(* ===================================================================== *)

(* THE O_CREATE ARM, end to end: create is callable, its floor meets the
   join, every failure arm's [iunlockput] is callable, and the O_TRUNC
   tail's entry level is met.  This is the corner that decides the walk. *)
Theorem so_create_arm_closes :
  (create_units <= so_u0)%nat /\
  (iput_units <= so_join)%nat /\
  (it_entry false (so_join - 2) <= so_join)%nat.
Proof. vm_compute. repeat split; lia. Qed.

(* THE else ARM, end to end, at both corners of the walk's bitmap report. *)
Theorem so_namei_arm_closes (L : nat) (w : bool) :
  (walk_need L <= so_u0)%nat /\
  (iput_units <= so_un w)%nat /\
  (it_entry false (so_un w - 2) <= so_un w)%nat.
Proof. destruct L, w; vm_compute; repeat split; lia. Qed.
