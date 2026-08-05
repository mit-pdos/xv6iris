(* ====================================================================== *)
(* FsCrash.v -- THE FILE SYSTEM'S CRASH PREDICATE [P_fs]: the pure         *)
(* recovery relation, the ghosts that carry it across a power cycle, and   *)
(* the escrow [P_fs] itself -- the value the adequacy client will fix the  *)
(* fixed layer's [RiscvPtsto.riscv_crash_pred] at.                         *)
(*                                                                        *)
(* Design: claude-notes/design/fs-log.md, "Stage 4 -- the crash side" and  *)
(* its stage-4 architecture, items 3-6; claude-notes/design/crash.md for   *)
(* [crash_inv]/[riscv_crash_pred] and the [Pc] adequacy parameter.         *)
(*                                                                        *)
(* WHAT IS IN HERE, IN ONE PARAGRAPH.  The FS's durable meaning is a       *)
(* relation between two things: the PHYSICAL disk (call it [P] -- the      *)
(* block view of the machine's own [v_disk]) and the COMMITTED state       *)
(* ([D] -- what recovery would produce from [P] right now).  [fs_recovery] *)
(* is that relation, read off [P] alone: decode the on-disk log header at  *)
(* [logstart]; if it says [n] blocks with write set [W], then [D] is the   *)
(* home blocks of [P] with [W[i]] overwritten by log slot [i]; at [n = 0]  *)
(* it is just the home blocks.  [P_fs] is an escrow over a pure record     *)
(* (P, D, the committed history) asserting exactly that, plus the halves   *)
(* of the ghosts that make it usable: a [ghost_var] TIE whose other half   *)
(* mirrors the machine's [v_disk] from inside [state_interp], and a        *)
(* MONO-LIST of committed [D]s whose persistent lower bounds are the       *)
(* durability receipts [sys_sync] will hand out.                          *)
(*                                                                        *)
(* THE TIE IS NOW THE MACHINE LAYER'S (phase C2a, LANDED).                 *)
(* [RiscvPtsto.riscv_crash_pred] is INDEXED by the disk image and           *)
(* [crash_inv]'s body is [∃ dk, disk_tie dk ∗ riscv_crash_pred dk], so the  *)
(* tie's two halves are [state_interp]'s conjunct and the invariant's own   *)
(* sibling -- the DMA completion holds both and moves them mechanically.    *)
(* [P_fs] therefore does NOT own a tie half: it is a PREDICATE ON [dk],     *)
(* and the machine layer guarantees that [dk] is the real disk.  The block  *)
(* view [fs_blocks dk] is where the FS's own vocabulary starts.            *)
(*                                                                          *)
(* WHAT IS DELIBERATELY *NOT* IN HERE (phases C2b/D):                       *)
(*  - the generation SWAP protocol (the checked-out arm's era binding) --  *)
(*    the arm exists here, the protocol is phase D's.                      *)
(*  - the per-call-site permit fupds (each WAL write kind re-establishing  *)
(*    [fs_rec_wf] at the new [P]) -- phase C2's.                           *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import own ghost_var invariants.
Require Import RiscvModelBytes.
Require Import VirtioModel.
Require Import RiscvPtsto.
Require Import WpLock.
Require Import LogInv.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. THE PURE LAYER.                                                     *)
(* ====================================================================== *)

(* ---------------------------------------------------------------------- *)
(* 1a. The BLOCK VIEW of the disk.                                         *)
(*                                                                         *)
(* The machine's disk is a TOTAL byte function [v_disk : Z -> bv 8]        *)
(* (VirtioModel.v).  Everything above the driver talks in 1024-byte        *)
(* BLOCKS, so the FS's view of the disk is the total block function        *)
(* below -- block [b] is the [BSIZE] bytes at [b * BSIZE].                 *)
(*                                                                         *)
(* TOTAL, not a [gmap] over a range, and that is a deliberate choice: the  *)
(* other half of the tie is destined for [state_interp], which lives in    *)
(* [RiscvPtsto.v] -- BELOW every FS constant.  A finite block map would    *)
(* need the FS's disk size down there (design/fs-log.md's own rule: no FS  *)
(* constant appears below [SystemAdequacy]), or a fresh fixed-layer        *)
(* parameter.  A total function needs neither, and the places that really  *)
(* are finite -- the durable home map [fr_D], the history -- stay [gmap].  *)
(* When the [state_interp] conjunct lands, [fs_blocks] moves down to       *)
(* VirtioModel.v verbatim (it is iris-free and uses only [disk_read]).     *)
(* ---------------------------------------------------------------------- *)

Definition BSIZE : nat := 1024%nat.     (* xv6 kernel/fs.h *)

Definition fs_blocks (dk : Z -> bv 8) : Z -> list (bv 8) :=
  fun b => disk_read dk (b * Z.of_nat BSIZE) BSIZE.

Lemma fs_blocks_length (dk : Z -> bv 8) (b : Z) :
  length (fs_blocks dk b) = BSIZE.
Proof. rewrite /fs_blocks /disk_read length_fmap length_seq //. Qed.

(* a byte outside the written range reads through *)
Lemma disk_write_out (dk : Z -> bv 8) (off : Z) (bs : list (bv 8)) (a : Z) :
  a < off \/ off + Z.of_nat (length bs) <= a ->
  disk_write dk off bs a = dk a.
Proof.
  intros [Hlt|Hge]; rewrite /disk_write.
  - rewrite (proj2 (Z.leb_gt off a)); [reflexivity|lia].
  - destruct (off <=? a) eqn:Hle; [|reflexivity].
    rewrite (lookup_ge_None_2 bs (Z.to_nat (a - off))); [reflexivity|].
    apply Z.leb_le in Hle. lia.
Qed.

(* THE TWO FACTS THE DMA COMPLETION'S MECHANICAL TIE UPDATE NEEDS (C2): a
   one-block write moves exactly that block of the view. *)
Lemma fs_blocks_write_eq (dk : Z -> bv 8) (b : Z) (bs : list (bv 8)) :
  length bs = BSIZE ->
  fs_blocks (disk_write dk (b * Z.of_nat BSIZE) bs) b = bs.
Proof.
  intros Hlen. rewrite /fs_blocks.
  pose proof (disk_read_write dk (b * Z.of_nat BSIZE) bs) as H.
  rewrite Hlen in H. exact H.
Qed.

Lemma fs_blocks_write_ne (dk : Z -> bv 8) (b c : Z) (bs : list (bv 8)) :
  length bs = BSIZE -> c <> b ->
  fs_blocks (disk_write dk (b * Z.of_nat BSIZE) bs) c = fs_blocks dk c.
Proof.
  intros Hlen Hne. rewrite /fs_blocks /disk_read.
  apply list_fmap_ext. intros j x Hx.
  apply lookup_seq in Hx as [-> Hjlt].
  apply disk_write_out. rewrite Hlen /BSIZE. rewrite /BSIZE in Hjlt.
  destruct (Z.lt_total c b) as [Hlt|[->|Hgt]]; [| congruence |]; [left|right]; lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* 1b. The FULL header decode.                                             *)
(*                                                                         *)
(* [struct logheader] is [int n; int block[LOGBLOCKS];] -- a run of         *)
(* little-endian 32-bit words.  [LogInv.hdr_n] already decodes the FIRST    *)
(* one (all stages 1-3 ever needed); this is the whole thing, and           *)
(* [hdr_dec_n] is the bridge that says the two agree on it.                 *)
(*                                                                         *)
(* TOTAL and junk-tolerant by construction: a short block simply assembles  *)
(* fewer bytes ([take]/[drop] never fail), so no well-formedness premise    *)
(* rides on the decoder and a garbage header decodes to SOMETHING rather    *)
(* than to nothing.  That matters: recovery must be defined at every        *)
(* physical disk, including one a crash left mid-write.                     *)
(* ---------------------------------------------------------------------- *)

Definition le_word (bs : list (bv 8)) (i : nat) : Z :=
  assemble_bytes (take 4 (drop (4 * i)%nat bs)).

Definition hdr_dec (bs : list (bv 8)) : nat * list Z :=
  let n := Z.to_nat (le_word bs 0) in
  (n, (fun i => le_word bs (S i)) <$> seq 0 n).

Lemma le_word_0 (bs : list (bv 8)) : le_word bs 0 = hdr_n bs.
Proof. rewrite /le_word /hdr_n Nat.mul_0_r drop_0 //. Qed.

(* THE BRIDGING LEMMA: the full decoder's [n] IS [LogInv.hdr_n]. *)
Lemma hdr_dec_n (bs : list (bv 8)) : Z.of_nat (hdr_dec bs).1 = hdr_n bs.
Proof.
  rewrite /hdr_dec /= le_word_0. apply Z2Nat.id, hdr_n_nonneg.
Qed.

Lemma hdr_dec_length (bs : list (bv 8)) :
  length (hdr_dec bs).2 = (hdr_dec bs).1.
Proof. rewrite /hdr_dec /= length_fmap length_seq //. Qed.

Lemma hdr_dec_zero (bs : list (bv 8)) :
  hdr_n bs = 0 -> hdr_dec bs = (0%nat, []).
Proof. intros Hn. rewrite /hdr_dec le_word_0 Hn //. Qed.

(* ---------------------------------------------------------------------- *)
(* 1c. The recovery relation.                                              *)
(*                                                                         *)
(* Stated in LogInv's own geometry vocabulary ([log_hdr_bno],               *)
(* [log_slot_bno], [log_region_set]), so the log proofs and this file       *)
(* cannot drift apart on where the log lives.                              *)
(* ---------------------------------------------------------------------- *)

(* the HOME blocks: the covered range minus the log's own storage *)
Definition fs_home_set (cov : gset Z) (logstart : Z) : gset Z :=
  cov ∖ log_region_set logstart.

(* a total block view, restricted to a finite set of block numbers *)
Definition fs_restrict (P : Z -> list (bv 8)) (s : gset Z)
    : gmap Z (list (bv 8)) :=
  set_to_map (fun b => (b, P b)) s.

Lemma fs_restrict_lookup_Some (P : Z -> list (bv 8)) (s : gset Z)
    (b : Z) (v : list (bv 8)) :
  fs_restrict P s !! b = Some v <-> b ∈ s /\ v = P b.
Proof.
  rewrite /fs_restrict lookup_set_to_map; last by intros y y' _ _ ?.
  split.
  - intros (x & Hx & Hf). injection Hf as Hb Hv. subst. done.
  - intros [Hb ->]. exists b. done.
Qed.

Lemma fs_restrict_dom (P : Z -> list (bv 8)) (s : gset Z) :
  dom (fs_restrict P s) = s.
Proof.
  apply set_eq. intros b. rewrite elem_of_dom. split.
  - intros [v Hv]. by apply fs_restrict_lookup_Some in Hv as [? _].
  - intros Hb. eexists. apply fs_restrict_lookup_Some. done.
Qed.

(* INSTALLING the on-disk log over the home map: entry [i] of the write set
   takes its content from log slot [i].  A [foldr] over the INDEX list
   rather than over [W] itself, because the content's block number
   ([log_slot_bno logstart i]) is a function of the index. *)
Definition fs_install (P : Z -> list (bv 8)) (logstart : Z) (W : list Z)
    (D : gmap Z (list (bv 8))) : gmap Z (list (bv 8)) :=
  foldr (fun i m =>
           match W !! i with
           | Some b => <[ b := P (log_slot_bno logstart i) ]> m
           | None => m
           end) D (seq 0 (length W)).

Lemma fs_install_nil (P : Z -> list (bv 8)) (logstart : Z)
    (D : gmap Z (list (bv 8))) :
  fs_install P logstart [] D = D.
Proof. reflexivity. Qed.

(* THE RECOVERY RELATION.  [D] is what a reboot would find, read off the
   physical disk [P] alone: the header block decides whether the log is
   live, and the whole thing is a FUNCTION of [P] (see [fs_recovery_det]). *)
Definition fs_recovery (P : Z -> list (bv 8)) (D : gmap Z (list (bv 8)))
    (cov : gset Z) (logstart : Z) : Prop :=
  D = fs_install P logstart (hdr_dec (P (log_hdr_bno logstart))).2
        (fs_restrict P (fs_home_set cov logstart)).

Lemma fs_recovery_det (P : Z -> list (bv 8)) D1 D2 cov logstart :
  fs_recovery P D1 cov logstart -> fs_recovery P D2 cov logstart -> D1 = D2.
Proof. intros -> ->. reflexivity. Qed.

Lemma fs_recovery_total (P : Z -> list (bv 8)) cov logstart :
  exists D, fs_recovery P D cov logstart.
Proof. eexists. reflexivity. Qed.

(* THE CLEAN-IMAGE COROLLARY (stage 2's [initlog] precondition, and what a
   freshly mkfs'ed disk satisfies): at [n = 0] recovery is the identity on
   the home blocks. *)
Lemma fs_recovery_clean (P : Z -> list (bv 8)) D cov logstart :
  hdr_n (P (log_hdr_bno logstart)) = 0 ->
  fs_recovery P D cov logstart <->
  D = fs_restrict P (fs_home_set cov logstart).
Proof.
  intros Hn. rewrite /fs_recovery (hdr_dec_zero _ Hn) /= fs_install_nil //.
Qed.

(* ---------------------------------------------------------------------- *)
(* 1d. The record the escrow is over, and its well-formedness.             *)
(* ---------------------------------------------------------------------- *)

Record fs_rec := MkFsRec {
  (* the DURABLE home map: what recovery produces from the PHYSICAL disk
     right now.  The physical disk itself is no longer a field: it is the
     crash predicate's INDEX (phase C2a), which the machine layer's tie pins
     to the real [v_disk]. *)
  fr_D : gmap Z (list (bv 8));
  (* the committed HISTORY, oldest first; [fr_D] is its last element.  The
     mono-list's persistent lower bounds over this are the durability
     RECEIPTS ([fs_receipt]) sys_sync will hand out (phase D). *)
  fr_hist : list (gmap Z (list (bv 8)));
}.

Definition fs_rec_wf (r : fs_rec) (P : Z -> list (bv 8))
    (cov : gset Z) (logstart : Z) : Prop :=
  fs_recovery P (fr_D r) cov logstart /\
  last (fr_hist r) = Some (fr_D r).

Lemma fs_rec_wf_hist_ne r P cov logstart :
  fs_rec_wf r P cov logstart -> fr_hist r <> [].
Proof. intros [_ Hlast] Hnil. rewrite Hnil in Hlast. discriminate. Qed.

(* ====================================================================== *)
(* 2. THE GHOSTS.                                                         *)
(* ====================================================================== *)

(* The committed history's algebra: a mono-list of durable home maps.  Only
   the ALGEBRA-level [mono_list] exists in this Iris (there is no
   [base_logic.lib.mono_list]), so the [own] wrappers are spelled out. *)
Notation fs_histO := (leibnizO (gmap Z (list (bv 8)))).
Notation fs_histR := (mono_listR fs_histO).

(* The TIE needs no class here at all any more: it is the MACHINE layer's
   ([RiscvPtsto.riscv_fstie_name], over the raw disk image), and [P_fs] is a
   predicate on that image rather than an owner of a half.  The FS BOOT TOKEN
   reuses [WpLock.lock_tok_excl] rather than minting a [ghost_varG Σ bool]
   (which WOULD be ambiguous against [riscvF_parkGS]). *)
Class fsCrashG (Σ : gFunctors) := FsCrashG {
  fscrash_histG :: inG Σ fs_histR;
}.

Definition fsCrashΣ : gFunctors := #[ GFunctor fs_histR ].

Global Instance subG_fsCrashΣ Σ : subG fsCrashΣ Σ -> fsCrashG Σ.
Proof. solve_inG. Qed.

(* The gname record [P_fs] is parameterized by.  It stays a PARAMETER rather
   than being read off the fixed layer, because [riscv_crash_pred] is a FIELD
   of [riscvFixedGS] and [P_fs] is what instantiates it -- naming the record
   inside itself would be circular.  Adequacy's obligation is discharged at
   [Pc := fun dk => ∃ γs, P_fs γs … dk], whose existential is exactly
   [P_fs_alloc]'s. *)
Record fs_crash_names := MkFsCrashNames {
  fcn_hist : gname;   (* the committed history, a mono-list *)
}.

Section fs_crash.
  Context `{!fsCrashG Σ, !lockG Σ}.

  (* -------------------------------------------------------------------- *)
  (* 2a. the committed-history mono-list                                   *)
  (* -------------------------------------------------------------------- *)

  Definition fs_hist_auth (γ : gname)
      (l : list (gmap Z (list (bv 8)))) : iProp Σ :=
    own γ (●ML (l : list fs_histO)).

  Definition fs_hist_lb (γ : gname)
      (l : list (gmap Z (list (bv 8)))) : iProp Σ :=
    own γ (◯ML (l : list fs_histO)).

  Global Instance fs_hist_lb_persistent γ l : Persistent (fs_hist_lb γ l).
  Proof. rewrite /fs_hist_lb. apply _. Qed.

  Lemma fs_hist_alloc (l : list (gmap Z (list (bv 8)))) :
    ⊢ |==> ∃ γ : gname, fs_hist_auth γ l ∗ fs_hist_lb γ l.
  Proof.
    iMod (own_alloc (●ML (l : list fs_histO) ⋅ ◯ML (l : list fs_histO)))
      as (γ) "[Ha Hf]".
    { apply mono_list_both_valid_L. reflexivity. }
    iModIntro. iExists γ. iFrame.
  Qed.

  Lemma fs_hist_snapshot γ l :
    fs_hist_auth γ l -∗ fs_hist_auth γ l ∗ fs_hist_lb γ l.
  Proof.
    rewrite /fs_hist_auth /fs_hist_lb -own_op -mono_list_auth_lb_op.
    iIntros "$".
  Qed.

  Lemma fs_hist_valid γ l l' :
    fs_hist_auth γ l -∗ fs_hist_lb γ l' -∗ ⌜l' `prefix_of` l⌝.
  Proof.
    rewrite /fs_hist_auth /fs_hist_lb. iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro. by apply mono_list_both_valid_L in Hv.
  Qed.

  Lemma fs_hist_update γ l l' :
    l `prefix_of` l' -> fs_hist_auth γ l ==∗ fs_hist_auth γ l'.
  Proof.
    intros Hpre. rewrite /fs_hist_auth. iIntros "Ha".
    iApply (own_update with "Ha"). by apply mono_list_update.
  Qed.

  (* -------------------------------------------------------------------- *)
  (* 2b. the FS BOOT TOKEN (phase D's generation swap)                     *)
  (*                                                                       *)
  (* One-shot and per-era: the era boot bundle will carry it, and the arm  *)
  (* of [P_fs] that is CHECKED OUT holds it.  A later generation swaps ITS *)
  (* token in using the recorded pure picture -- abandonment, not          *)
  (* revocation, exactly the crash layer's own pattern.  In C1 this is a   *)
  (* DEFINITION plus its exclusivity; the protocol is phase D's.           *)
  (* -------------------------------------------------------------------- *)

  Definition fs_boot_tok (γg : gname) : iProp Σ := lock_tok_excl γg.

  Lemma fs_boot_tok_alloc : ⊢ |==> ∃ γg : gname, fs_boot_tok γg.
  Proof. rewrite /fs_boot_tok. iApply lock_tok_excl_alloc. Qed.

  Lemma fs_boot_tok_excl γg : fs_boot_tok γg -∗ fs_boot_tok γg -∗ False.
  Proof. rewrite /fs_boot_tok. iApply lock_tok_excl_exclusive. Qed.

  Global Instance fs_boot_tok_timeless γg : Timeless (fs_boot_tok γg).
  Proof. rewrite /fs_boot_tok. apply _. Qed.

  (* -------------------------------------------------------------------- *)
  (* 2c. the tie's CLIENT-SIDE half and the receipts                       *)
  (* -------------------------------------------------------------------- *)

  (* A DURABILITY RECEIPT: persistent evidence that [D] was, at some point,
     the committed state.  (The lower bound records the whole prefix, so a
     receipt also pins everything committed before it -- which is what makes
     two receipts comparable, phase D's sys_sync.) *)
  Definition fs_receipt (γs : fs_crash_names)
      (D : gmap Z (list (bv 8))) : iProp Σ :=
    (∃ l : list (gmap Z (list (bv 8))), fs_hist_lb (fcn_hist γs) (l ++ [D]))%I.

  Global Instance fs_receipt_persistent γs D : Persistent (fs_receipt γs D).
  Proof. rewrite /fs_receipt. apply _. Qed.

  (* ==================================================================== *)
  (* 3. [P_fs] -- THE CRASH PREDICATE.                                     *)
  (* ==================================================================== *)

  (* The generation arm (design/fs-log.md stage-4 item 3): the record is
     either AT REST or CHECKED OUT by the era whose one-shot FS boot token
     sits in it.  In C1 the swap protocol does not exist, so the at-rest arm
     is [emp] and every allocation lands there; phase D gives the
     checked-out arm its era binding (and the at-rest arm whatever the swap
     needs to recognize a stale generation). *)
  Definition fs_arm : iProp Σ :=
    (emp ∨ ∃ γg : gname, fs_boot_tok γg)%I.

  (* THE CRASH PREDICATE, i.e. the intended value of
     [RiscvPtsto.riscv_crash_pred] (the adequacy [Pc] parameter).  It is a
     PREDICATE ON THE DISK IMAGE [dk], and the machine layer's tie
     ([RiscvPtsto.disk_tie], whose other half is [state_interp]'s fixed
     conjunct) is what guarantees that [dk] is the REAL disk -- so nothing
     here has to own a ghost about it.  Read it as: there is a pure record
     [r] such that
       - the committed history is [fr_hist r] (its lower bounds are the
         receipts already handed out), and
       - [r] is WELL FORMED AT [dk]: recovery of the physical disk's block
         view is the last committed state.
     Everything a client ever learns at a crash comes out of the second
     conjunct; the index is what makes it a statement about the REAL disk
     rather than about a ghost. *)
  Definition P_fs (γs : fs_crash_names) (cov : gset Z) (logstart : Z)
      (dk : Z -> bv 8) : iProp Σ :=
    (∃ r : fs_rec,
       fs_hist_auth (fcn_hist γs) (fr_hist r) ∗
       ⌜fs_rec_wf r (fs_blocks dk) cov logstart⌝ ∗
       fs_arm)%I.

  (* -------------------------------------------------------------------- *)
  (* 3a. what [P_fs] SAYS                                                   *)
  (* -------------------------------------------------------------------- *)

  (* THE HEADLINE.  At the disk image the machine layer's tie pins, the crash
     predicate says the REAL disk recovers to the last committed state.  This
     is the fact a crash-time client (recovery, sys_sync) consumes. *)
  Lemma P_fs_recovers γs cov logstart dk :
    P_fs γs cov logstart dk -∗
      ⌜exists (D : gmap Z (list (bv 8)))
              (h : list (gmap Z (list (bv 8)))),
         fs_recovery (fs_blocks dk) D cov logstart /\
         h <> [] /\ last h = Some D⌝.
  Proof.
    rewrite /P_fs.
    iIntros "Hp". iDestruct "Hp" as (r) "(_ & %Hwf & _)".
    iPureIntro. exists (fr_D r), (fr_hist r).
    destruct Hwf as [Hrec Hlast].
    split_and!; [exact Hrec | | exact Hlast].
    intros Hnil. rewrite Hnil in Hlast. discriminate.
  Qed.

  (* a receipt is honest: what it names really was committed *)
  Lemma P_fs_receipt_committed γs cov logstart dk D :
    P_fs γs cov logstart dk -∗ fs_receipt γs D -∗
      ⌜exists r : fs_rec,
         fs_rec_wf r (fs_blocks dk) cov logstart /\ D ∈ fr_hist r⌝.
  Proof.
    rewrite /P_fs /fs_receipt.
    iIntros "Hp Hr". iDestruct "Hp" as (r) "(Hauth & %Hwf & _)".
    iDestruct "Hr" as (l) "Hlb".
    iDestruct (fs_hist_valid with "Hauth Hlb") as %[k Hk].
    iPureIntro. exists r. split; [exact Hwf|].
    rewrite Hk -app_assoc elem_of_app elem_of_app.
    right. left. apply elem_of_list_singleton. reflexivity.
  Qed.

  (* -------------------------------------------------------------------- *)
  (* 3b. ALLOCATION -- mkfs's obligation, discharged                        *)
  (* -------------------------------------------------------------------- *)

  (* [P_fs] holds INITIALLY, from nothing but the pure fact that the pristine
     disk recovers to [D0].  This IS the shape of adequacy's [HPc] premise
     ([RiscvAdequacy.riscv_system_adequacy]): a build-from-nothing entailment
     UNDER AN UPDATE, because a crash predicate that owns ghosts is never
     provable from nothing.  The client instantiates
     [Pc := fun dk => ∃ γs, P_fs γs cov logstart dk] and discharges the
     obligation with this lemma. *)
  Lemma P_fs_alloc (dk0 : Z -> bv 8) (D0 : gmap Z (list (bv 8)))
      (cov : gset Z) (logstart : Z) :
    fs_recovery (fs_blocks dk0) D0 cov logstart ->
    ⊢ |==> ∃ γs : fs_crash_names,
        P_fs γs cov logstart dk0 ∗ fs_receipt γs D0.
  Proof.
    intros Hrec.
    iMod (fs_hist_alloc [D0]) as (γh) "[Hauth #Hlb]".
    iModIntro. iExists (MkFsCrashNames γh).
    iSplitL "Hauth".
    - rewrite /P_fs. iExists (MkFsRec D0 [D0]).
      iFrame "Hauth".
      iSplitR.
      { iPureIntro. rewrite /fs_rec_wf /=. split; [exact Hrec | reflexivity]. }
      rewrite /fs_arm. by iLeft.
    - rewrite /fs_receipt /=. iExists []. iExact "Hlb".
  Qed.

  (* The mkfs corollary: a freshly formatted disk has an EMPTY on-disk log,
     so its committed state is just its home blocks and no recovery
     hypothesis has to be assumed at all. *)
  Lemma P_fs_alloc_clean (dk0 : Z -> bv 8) (cov : gset Z) (logstart : Z) :
    hdr_n (fs_blocks dk0 (log_hdr_bno logstart)) = 0 ->
    ⊢ |==> ∃ γs : fs_crash_names,
        P_fs γs cov logstart dk0 ∗
        fs_receipt γs (fs_restrict (fs_blocks dk0)
                         (fs_home_set cov logstart)).
  Proof.
    intros Hn. iApply P_fs_alloc.
    by apply (fs_recovery_clean (fs_blocks dk0) _ cov logstart Hn).
  Qed.

End fs_crash.
