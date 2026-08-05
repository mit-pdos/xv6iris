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
From iris.base_logic.lib Require Import own ghost_var ghost_map mono_nat invariants.
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
(* 1c'. THE LOG-REGION MIRROR's MEANING (phase C2b/D1).                     *)
(*                                                                          *)
(* [RiscvPtsto.log_mirror] is the SHAPE; this is what makes a recorded       *)
(* picture true of a disk.  It is the bridge the three WAL write kinds pass  *)
(* to each other, and the reason it must exist at all is that a crash permit *)
(* is a STATELESS view shift: no single [bwrite] can re-derive "the on-disk  *)
(* header is clean" or "the log slots hold the logged values" -- those are   *)
(* facts the PREVIOUS writes established.                                    *)
(* ---------------------------------------------------------------------- *)

Definition log_mirror_ok (M : log_mirror) (P : Z -> list (bv 8)) (ls : Z)
    : Prop :=
  lm_hdr M = hdr_dec (P (log_hdr_bno ls)) /\
  forall i, (i < LOGBLOCKS)%nat -> lm_slots M i = P (log_slot_bno ls i).

(* the mirror of a given disk, as a function -- what a swap installs and what
   every WAL fupd re-establishes at the post-write image *)
Definition mirror_of (P : Z -> list (bv 8)) (ls : Z) : log_mirror :=
  MkLogMirror (hdr_dec (P (log_hdr_bno ls)))
              (fun i => P (log_slot_bno ls i)).

Lemma mirror_of_ok (P : Z -> list (bv 8)) (ls : Z) :
  log_mirror_ok (mirror_of P ls) P ls.
Proof. split; [reflexivity | intros i _; reflexivity]. Qed.

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
  (* THE SWAP COUNTER's gname (phase C2b/D1).  Adequacy allocates it and
     hands the AUTH to the client, so it can only be a parameter here; the
     seam equation the client carries is [fcn_swap γs = riscv_swap_name],
     exactly like [VirtioProto]'s [dn_img γ = disk_img_name]. *)
  fcn_swap : gname;
  (* The GENERATION REGISTRY and the STARTED counter, likewise as parameters
     with seam equations ([fcn_reg γs = riscv_registry_name],
     [fcn_start γs = riscv_start_name]).  They cannot be read off
     [riscvFixedGS] here: [riscv_crash_pred] is a FIELD of that record and
     [P_fs] is what instantiates it, so naming the record inside [P_fs] would
     be circular.  The CLASSES are taken as bare Section constraints below
     rather than bundled into [fsCrashG], so that resolution picks the SAME
     Σ slots the fixed record's own fields were built from -- two sibling
     class fields would be different slots whose resources cannot interact
     (the trap DiskImg.v's header records). *)
  fcn_reg   : gname;
  fcn_start : gname;
}.

Section fs_crash.
  Context `{!fsCrashG Σ, !lockG Σ}.
  (* bare constraints, deliberately not [fsCrashG] fields -- see
     [fs_crash_names] above *)
  Context `{!ghost_mapG Σ nat riscvEraGS, !mono_natG Σ,
            !ghost_varG Σ log_mirror}.

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

  (* ==================================================================== *)
  (* THE GENERATION ARM (phase C2b/D1): AT REST, or CHECKED OUT by an era.  *)
  (*                                                                        *)
  (* The counter [c] is the whole identification mechanism.  [c = 0] is at   *)
  (* rest (no era has ever taken custody); [c = S g''] means generation      *)
  (* [g''] holds custody, and the arm then carries that era's registry       *)
  (* element, its started certificate, and HALF of its log-region mirror --  *)
  (* the other half being era-side, in the log layer.                        *)
  (*                                                                        *)
  (* THE SQUEEZE.  A WAL write's fupd arrives with its own swap receipt      *)
  (* [swap_lb (S g)] (so [S g <= c], which both refutes the at-rest arm and  *)
  (* gives [g <= g'']) and, threaded in by the DMA completion, the           *)
  (* started-generations auth at [g + 1] (so [S g'' <= g + 1], i.e.          *)
  (* [g'' <= g]).  Hence [g'' = g]; [era_registered] agreement at the shared *)
  (* key gives [E'' = E]; and the mirror gname is identified, so the two     *)
  (* halves meet.  Retiring an arm needs NO identification -- only the       *)
  (* upper bound -- which is why a fresh era can always swap.                *)
  (* ==================================================================== *)

  (* the registry element and the started certificate, at the PARAMETER
     gnames.  Both persistent, as their fixed-layer twins are. *)
  Definition fs_era_reg (γs : fs_crash_names) (g : nat) (E : riscvEraGS)
      : iProp Σ := (g ↪[fcn_reg γs]□ E)%I.
  Definition fs_started (γs : fs_crash_names) (g : nat) : iProp Σ :=
    mono_nat_lb_own (fcn_start γs) (S g).

  Global Instance fs_era_reg_persistent γs g E : Persistent (fs_era_reg γs g E).
  Proof. rewrite /fs_era_reg. apply _. Qed.
  Global Instance fs_started_persistent γs g : Persistent (fs_started γs g).
  Proof. rewrite /fs_started. apply _. Qed.

  Definition fs_custody (γs : fs_crash_names) (ls : Z) (dk : Z -> bv 8)
      (g'' : nat) : iProp Σ :=
    (∃ (E'' : riscvEraGS) (M : log_mirror),
       fs_era_reg γs g'' E'' ∗ fs_started γs g'' ∗
       ghost_var (era_mirror_name E'') (1/2) M ∗
       ⌜log_mirror_ok M (fs_blocks dk) ls⌝)%I.

  Definition fs_arm (γs : fs_crash_names) (ls : Z) (dk : Z -> bv 8)
      : iProp Σ :=
    (∃ c : nat,
       mono_nat_auth_own (fcn_swap γs) 1 c ∗
       (⌜c = 0%nat⌝ ∨ ∃ g'' : nat, ⌜c = S g''⌝ ∗ fs_custody γs ls dk g''))%I.

  (* the at-rest arm, as adequacy mints it *)
  Lemma fs_arm_at_rest γs ls dk :
    mono_nat_auth_own (fcn_swap γs) 1 0%nat ⊢ fs_arm γs ls dk.
  Proof.
    iIntros "Ha". rewrite /fs_arm. iExists 0%nat. iFrame "Ha". by iLeft.
  Qed.

  (* the upper bound RETIREMENT needs, and it is all it needs: whatever arm is
     there, its generation is at most the ambient one.  No identification --
     which is exactly why a fresh era can always swap, including after a
     crash that stranded the previous era's mirror half. *)
  Local Lemma fs_custody_started γs ls dk g'' :
    fs_custody γs ls dk g'' -∗ fs_started γs g'' ∗ fs_custody γs ls dk g''.
  Proof.
    rewrite /fs_custody. iIntros "H".
    iDestruct "H" as (E M) "(#Hr & #Hs & Hm & %Hok)".
    iSplitR; [iExact "Hs"|].
    iExists E, M. iFrame "Hr Hs Hm". iPureIntro. exact Hok.
  Qed.

  Local Lemma fs_arm_le γs ls dk (g n c : nat) :
    n = (g + 1)%nat ->
    mono_nat_auth_own (fcn_start γs) 1 n -∗
    (⌜c = 0%nat⌝ ∨ ∃ g'' : nat, ⌜c = S g''⌝ ∗ fs_custody γs ls dk g'') -∗
    ⌜(c <= S g)%nat⌝ ∗ mono_nat_auth_own (fcn_start γs) 1 n ∗
    (⌜c = 0%nat⌝ ∨ ∃ g'' : nat, ⌜c = S g''⌝ ∗ fs_custody γs ls dk g'').
  Proof.
    intros ->. iIntros "Hsa Hd".
    iDestruct "Hd" as "[%Hc0 | Hc]".
    { iFrame "Hsa". iSplitR; [iPureIntro; lia|]. by iLeft. }
    iDestruct "Hc" as (g'') "[%Hc Hcust]".
    iDestruct (fs_custody_started with "Hcust") as "[#Hst Hcust]".
    rewrite /fs_started.
    iDestruct (mono_nat_lb_own_valid with "Hsa Hst") as %[_ Hle].
    iFrame "Hsa". iSplitR; [iPureIntro; lia|].
    iRight. iExists g''. iSplitR; [done|]. iExact "Hcust".
  Qed.

  (* ==================================================================== *)
  (* THE SWAP: retire whatever arm is there, install THIS era's custody.    *)
  (* It rides a write fupd (initlog's final write_head), so it takes the    *)
  (* started auth the completion threaded in and hands it straight back.    *)
  (* ==================================================================== *)
  Lemma fs_arm_swap (γs : fs_crash_names) (ls : Z) (dk : Z -> bv 8)
      (g : nat) (E : riscvEraGS) (n : nat) (M : log_mirror) :
    n = (g + 1)%nat ->
    log_mirror_ok M (fs_blocks dk) ls ->
    fs_era_reg γs g E -∗ fs_started γs g -∗
    mono_nat_auth_own (fcn_start γs) 1 n -∗
    ghost_var (era_mirror_name E) (1/2) M -∗
    fs_arm γs ls dk ==∗
      fs_arm γs ls dk ∗ mono_nat_auth_own (fcn_start γs) 1 n ∗
      mono_nat_lb_own (fcn_swap γs) (S g).
  Proof.
    intros Hn Hok. iIntros "#Hreg #Hst Hsa Hmir Harm".
    rewrite {1}/fs_arm. iDestruct "Harm" as (c) "[Hc Hrest]".
    iDestruct (fs_arm_le γs ls dk g n c Hn with "Hsa Hrest")
      as "(%Hle & Hsa & _)".
    iMod (mono_nat_own_update (S g) with "Hc") as "[Hc #Hlb]"; [lia|].
    iModIntro. iFrame "Hsa Hlb".
    rewrite /fs_arm. iExists (S g). iFrame "Hc". iRight.
    iExists g. iSplitR; [done|].
    rewrite /fs_custody. iExists E, M. iFrame "Hreg Hst Hmir".
    iPureIntro. exact Hok.
  Qed.

  (* ==================================================================== *)
  (* THE ACCESSOR every WAL write's fupd runs on: the SQUEEZE, then the     *)
  (* mirror's two halves meet, then the arm re-closes at the POST-write     *)
  (* image with the updated picture.                                       *)
  (* ==================================================================== *)
  Lemma fs_arm_acc (γs : fs_crash_names) (ls : Z) (dk : Z -> bv 8)
      (g : nat) (E : riscvEraGS) (n : nat) (M0 : log_mirror) :
    n = (g + 1)%nat ->
    fs_era_reg γs g E -∗ mono_nat_lb_own (fcn_swap γs) (S g) -∗
    mono_nat_auth_own (fcn_start γs) 1 n -∗
    ghost_var (era_mirror_name E) (1/2) M0 -∗
    fs_arm γs ls dk -∗
      ⌜log_mirror_ok M0 (fs_blocks dk) ls⌝ ∗
      mono_nat_auth_own (fcn_start γs) 1 n ∗
      (∀ (dk' : Z -> bv 8) (M' : log_mirror),
         ⌜log_mirror_ok M' (fs_blocks dk') ls⌝ ==∗
           fs_arm γs ls dk' ∗ ghost_var (era_mirror_name E) (1/2) M').
  Proof.
    intros Hn. iIntros "#Hreg #Hswlb Hsa Hmir Harm".
    rewrite {1}/fs_arm. iDestruct "Harm" as (c) "[Hc Hrest]".
    (* ABOVE: the arm's generation is at most the ambient one *)
    iDestruct (fs_arm_le γs ls dk g n c Hn with "Hsa Hrest")
      as "(%Hup & Hsa & Hrest)".
    (* BELOW: our own swap receipt says it is at least ours *)
    iDestruct (mono_nat_lb_own_valid with "Hc Hswlb") as %[_ Hlow].
    (* so the at-rest arm is refuted and the generations coincide *)
    destruct c as [|c']; [exfalso; lia|].
    iDestruct "Hrest" as "[%Hc0 | Hc2]"; [discriminate|].
    iDestruct "Hc2" as (g'') "[%Hceq Hcust]".
    assert (Hgg : g'' = g) by lia. subst g''.
    rewrite /fs_custody. iDestruct "Hcust" as (E'' M) "(#Hreg2 & #Hst2 & Hmir2 & %Hok)".
    (* the registry pins the era record, hence the mirror's gname *)
    rewrite /fs_era_reg.
    iDestruct (ghost_map_elem_agree with "Hreg Hreg2") as %<-.
    iDestruct (ghost_var_agree with "Hmir Hmir2") as %<-.
    iFrame "Hsa". iSplitR; [iPureIntro; exact Hok|].
    iIntros (dk' M') "%Hok'".
    iMod (ghost_var_update_halves M' with "Hmir Hmir2") as "[Hmir Hmir2]".
    iModIntro. iFrame "Hmir".
    assert (Hcg : c' = g) by lia. subst c'.
    rewrite /fs_arm. iExists (S g). iFrame "Hc". iRight.
    iExists g. iSplitR; [done|].
    rewrite /fs_custody. iExists E, M'. iFrame "Hreg Hst2 Hmir2".
    iPureIntro. exact Hok'.
  Qed.

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
       fs_arm γs logstart dk)%I.

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
  Lemma P_fs_alloc (γsw γreg γst : gname) (dk0 : Z -> bv 8)
      (D0 : gmap Z (list (bv 8))) (cov : gset Z) (logstart : Z) :
    fs_recovery (fs_blocks dk0) D0 cov logstart ->
    mono_nat_auth_own γsw 1 0%nat ⊢ |==> ∃ γs : fs_crash_names,
      ⌜fcn_swap γs = γsw /\ fcn_reg γs = γreg /\ fcn_start γs = γst⌝ ∗
      P_fs γs cov logstart dk0 ∗ fs_receipt γs D0.
  Proof.
    intros Hrec. iIntros "Hsw".
    iMod (fs_hist_alloc [D0]) as (γh) "[Hauth #Hlb]".
    iModIntro. iExists (MkFsCrashNames γh γsw γreg γst).
    iSplitR; [iPureIntro; done|].
    iSplitL "Hauth Hsw".
    - rewrite /P_fs. iExists (MkFsRec D0 [D0]).
      iFrame "Hauth".
      iSplitR.
      { iPureIntro. rewrite /fs_rec_wf /=. split; [exact Hrec | reflexivity]. }
      iApply fs_arm_at_rest. iExact "Hsw".
    - rewrite /fs_receipt /=. iExists []. iExact "Hlb".
  Qed.

  (* The mkfs corollary: a freshly formatted disk has an EMPTY on-disk log,
     so its committed state is just its home blocks and no recovery
     hypothesis has to be assumed at all. *)
  Lemma P_fs_alloc_clean (γsw γreg γst : gname) (dk0 : Z -> bv 8)
      (cov : gset Z) (logstart : Z) :
    hdr_n (fs_blocks dk0 (log_hdr_bno logstart)) = 0 ->
    mono_nat_auth_own γsw 1 0%nat ⊢ |==> ∃ γs : fs_crash_names,
      ⌜fcn_swap γs = γsw /\ fcn_reg γs = γreg /\ fcn_start γs = γst⌝ ∗
      P_fs γs cov logstart dk0 ∗
      fs_receipt γs (fs_restrict (fs_blocks dk0)
                       (fs_home_set cov logstart)).
  Proof.
    intros Hn. iApply P_fs_alloc.
    by apply (fs_recovery_clean (fs_blocks dk0) _ cov logstart Hn).
  Qed.

End fs_crash.
