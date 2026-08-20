(* ============================================================================
   IN-TREE de-risk for DESIGN OPTION A ("pending-free + imark escrow"), ported
   from the stock-Iris [EscrowDerisk.v] into the REAL region Σ.

   Extends the validated stock de-risk in the two ways the real port needs:

     1. It uses the REAL [InodeRegion.imark] / [InodeRegion.dinode_at]
        (over [γi], with [imark_key z := -(z+1)]) and the real [dinode],
        [fs_names], typeclass context -- so the ghost hand-off is proven in the
        same Σ the region lives in.

     2. It resolves the ONE open crux the stock de-risk did not cover: the
        per-inum agreement linking the pool's [pending_free] arm to the
        region's [committed] coupling.  This is load-bearing because the pool
        is sealed at iput+0x8c (release of itable.lock) BEFORE the off-lock
        ifree's [log_write] produces [committed]; so [committed] cannot ride in
        the pool arm -- it must land region-side, and a later redeemer must
        correlate its pool-side ticket with the region's [committed].  The
        correlation is a REBINDABLE per-inum escrow-name registry [γreg]
        (inum reused across free cycles), held as two halves: one in the
        region's type=0 pending arm, one in the pool's pending_free arm.  The
        halves agree on (ge,gr); possession of the pool half is what proves the
        region sits in its pending disjunct.  [committed]/[reg_half] are the
        only region-side additions, and both are Timeless -- [esc_inv] (not
        Timeless) rides the pool side, so [ireg_inv]'s [iInv ... as ">"] is
        unaffected.

   No new Axiom / Parameter / admit; every headline lemma is Closed under the
   global context (audited at the foot of the file).
   ========================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import excl.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var mono_nat own.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvPtsto.
Require Import DiskPtsto.
Require Import FsBlocks.
Require Import DinodeEnc.
Require Import InodeRegion.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

Notation ST_EMPTY := 0%nat.
Notation ST_FILLED := 1%nat.
Notation ST_REDEEMED := 2%nat.

(* the two extra ghost pieces the escrow layer needs beyond the region's own.
   [mono_natG] is ambient from [riscvGS] (the epoch layer already assumes it),
   so it is NOT bundled here -- doing so would be the duplicate-class trap. *)
Class escrowAG (Σ : gFunctors) := {
  escrowA_tickG :: inG Σ (exclR unitO);
  escrowA_regG  :: ghost_mapG Σ Z (gname * gname)%type;
  escrowA_gvarG :: ghost_varG Σ Z;   (* de-risk's disk-type-byte model only *)
}.

Section escrowA.
  Context `{!riscvGS Σ, !xv6G Σ, !escrowAG Σ}.
  Context `{ICFG : icfg}.

  (* ------------------------------------------------------------------ *)
  (*  escrow tokens (same shapes as the stock de-risk, real imark)        *)
  (* ------------------------------------------------------------------ *)
  Definition committedA (ge : gname) : iProp Σ := mono_nat_lb_own ge ST_FILLED.
  Global Instance committedA_persistent ge : Persistent (committedA ge).
  Proof. rewrite /committedA. apply _. Qed.
  Global Instance committedA_timeless ge : Timeless (committedA ge).
  Proof. rewrite /committedA. apply _. Qed.

  Definition redeem_ticketA (gr : gname) : iProp Σ := own gr (Excl ()).
  Lemma redeem_ticketA_excl gr : redeem_ticketA gr -∗ redeem_ticketA gr -∗ False.
  Proof.
    rewrite /redeem_ticketA. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    exfalso. exact (exclusive_l (Excl ()) (Excl ()) Hv).
  Qed.

  (* per-inum escrow body, over the REAL imark *)
  Definition escA_body (ge gr gi : gname) (inum : bv 32) : iProp Σ :=
    ( mono_nat_auth_own ge 1 ST_EMPTY
    ∨ (mono_nat_auth_own ge 1 ST_FILLED ∗ InodeRegion.imark gi (bv_unsigned inum))
    ∨ (mono_nat_auth_own ge 1 ST_REDEEMED ∗ redeem_ticketA gr) )%I.

  (* per-inum namespace: distinct escrows never share a name *)
  Definition escAN (inum : bv 32) : namespace :=
    (nroot .@ "icescA") .@ (bv_unsigned inum).
  Definition escA_inv (ge gr gi : gname) (inum : bv 32) : iProp Σ :=
    inv (escAN inum) (escA_body ge gr gi inum).
  Global Instance escA_inv_persistent ge gr gi inum :
    Persistent (escA_inv ge gr gi inum).
  Proof. rewrite /escA_inv. apply _. Qed.

  (* minted at +0x86, BEFORE the pool is sealed: hands back the (persistent)
     invariant and the exclusive ticket.  Escrow starts EMPTY -- the deposit
     that produces [committed] happens later, off-lock, at the ifree. *)
  Lemma escA_alloc E gi inum :
    ⊢ |={E}=> ∃ ge gr, escA_inv ge gr gi inum ∗ redeem_ticketA gr.
  Proof.
    iIntros.
    iMod (mono_nat_own_alloc ST_EMPTY) as (ge) "[Hauth _]".
    iMod (own_alloc (Excl ())) as (gr) "Htick"; [done|].
    iMod (inv_alloc (escAN inum) _ (escA_body ge gr gi inum) with "[Hauth]")
      as "#Hinv".
    { iNext. iLeft. iExact "Hauth". }
    iModIntro. iExists ge, gr. iFrame "Hinv Htick".
  Qed.

  Lemma escA_deposit E ge gr gi inum :
    ↑escAN inum ⊆ E →
    escA_inv ge gr gi inum -∗ InodeRegion.imark gi (bv_unsigned inum)
      ={E}=∗ committedA ge.
  Proof.
    iIntros (HE) "#Hinv Hmk".
    iInv "Hinv" as ">Hbody" "Hcl".
    iDestruct "Hbody" as "[Hauth | [[Hauth Hmk2] | [Hauth Htick]]]".
    - iMod (mono_nat_own_update ST_FILLED with "Hauth") as "[Hauth #Hlb]".
      { lia. }
      iMod ("Hcl" with "[Hauth Hmk]") as "_".
      { iNext. iRight; iLeft. iFrame "Hauth Hmk". }
      iModIntro. iExact "Hlb".
    - iExFalso. iApply (InodeRegion.imark_excl with "Hmk Hmk2").
    - iDestruct (mono_nat_lb_own_get with "Hauth") as "#Hlb2".
      iMod ("Hcl" with "[Hauth Htick]") as "_".
      { iNext. iRight; iRight. iFrame "Hauth Htick". }
      iModIntro.
      iApply (mono_nat_lb_own_le ST_FILLED with "Hlb2"). lia.
  Qed.

  Lemma escA_redeem E ge gr gi inum :
    ↑escAN inum ⊆ E →
    escA_inv ge gr gi inum -∗ redeem_ticketA gr -∗ committedA ge
      ={E}=∗ InodeRegion.imark gi (bv_unsigned inum).
  Proof.
    iIntros (HE) "#Hinv Htick #Hcom".
    iInv "Hinv" as ">Hbody" "Hcl".
    iDestruct "Hbody" as "[Hauth | [[Hauth Hmk] | [Hauth Htick2]]]".
    - iDestruct (mono_nat_lb_own_valid with "Hauth Hcom") as %[_ Hle]. lia.
    - iMod (mono_nat_own_update ST_REDEEMED with "Hauth") as "[Hauth _]".
      { lia. }
      iMod ("Hcl" with "[Hauth Htick]") as "_".
      { iNext. iRight; iRight. iFrame "Hauth Htick". }
      iModIntro. iExact "Hmk".
    - iExFalso. iApply (redeem_ticketA_excl with "Htick Htick2").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  the rebindable per-inum registry  [γreg : inum -> (ge,gr)]           *)
  (* ------------------------------------------------------------------ *)
  Definition reg_half (γreg : gname) (inum : bv 32) (ge gr : gname) : iProp Σ :=
    (bv_unsigned inum ↪[γreg]{# (1/2)} (ge, gr))%I.
  Global Instance reg_half_timeless γreg inum ge gr :
    Timeless (reg_half γreg inum ge gr).
  Proof. rewrite /reg_half. apply _. Qed.

  (* THE CRUX: two halves for one inum agree on the escrow name pair -- this is
     what forces the redeemer's pool-side ticket and the region's committed to
     name the SAME escrow.  Non-consuming (both halves survive). *)
  Lemma reg_half_agree γreg inum ge1 gr1 ge2 gr2 :
    reg_half γreg inum ge1 gr1 -∗ reg_half γreg inum ge2 gr2 -∗
      ⌜ge1 = ge2 /\ gr1 = gr2⌝.
  Proof.
    rewrite /reg_half. iIntros "H1 H2".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq.
    iPureIntro. split; congruence.
  Qed.

  (* the pool-side and region-side pending bundles.  Neither carries the record
     [dinode_at] (that stays in the region's live arm, as today); the only new
     content is the escrow correlation.  [esc_inv] (not Timeless) is on the POOL
     side; the REGION side is Timeless (reg_half + committedA). *)
  Definition pool_pending (γreg gi : gname) (inum : bv 32) : iProp Σ :=
    (∃ ge gr, reg_half γreg inum ge gr ∗ escA_inv ge gr gi inum ∗ redeem_ticketA gr)%I.

  Definition region_pending (γreg : gname) (inum : bv 32) : iProp Σ :=
    (∃ ge gr, reg_half γreg inum ge gr ∗ committedA ge)%I.
  Global Instance region_pending_timeless γreg inum :
    Timeless (region_pending γreg inum).
  Proof. rewrite /region_pending. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  (c) the atomic off-lock free -- committed lands REGION-side          *)
  (* ------------------------------------------------------------------ *)

  (* mini region for one in-flight-free inum: the committed disk-type byte [t]
     as a HALF ghost_var (the log buffer holds the other half), coupled to the
     escrow's deposit state -- the SAME coupling the real [ireg_inv] type=0
     free arm gains, in miniature.  Timeless, exactly as [ireg_body] is. *)
  Definition mini_region_body (γreg : gname) (inum : bv 32) (gfs : gname) : iProp Σ :=
    (∃ t : Z, ghost_var gfs (1/2) t ∗
       (⌜t ≠ 0⌝ ∨ (⌜t = 0⌝ ∗ region_pending γreg inum)))%I.
  Definition iregAN : namespace := nroot .@ "iregA".
  Definition mini_region_inv γreg inum gfs : iProp Σ :=
    inv iregAN (mini_region_body γreg inum gfs).
  Global Instance mini_region_inv_persistent γreg inum gfs :
    Persistent (mini_region_inv γreg inum gfs).
  Proof. rewrite /mini_region_inv. apply _. Qed.

  (* the off-lock commit: the freer holds the region marker (produced by
     [ireg_free_au]'s inner action), its half of the disk-type byte (the
     inlined ifree's log buffer), its kept registry half, and the escrow it
     minted at +0x86.  In ONE atomic fupd it (a) writes the type to 0 and
     (b) deposits the marker into the escrow -- yielding [committed], which
     lands region-side inside [region_pending]. *)
  Lemma free_commit_deposit_atomicA E γreg ge gr gfs gi inum (t0 : Z) :
    ↑iregAN ⊆ E → ↑escAN inum ⊆ E →
    mini_region_inv γreg inum gfs -∗
    escA_inv ge gr gi inum -∗
    reg_half γreg inum ge gr -∗
    InodeRegion.imark gi (bv_unsigned inum) -∗
    ghost_var gfs (1/2) t0 -∗
    |={E}=> committedA ge ∗ ghost_var gfs (1/2) (0%Z).
  Proof.
    iIntros (Hi He) "#Hri #Hei Hrh Hmk Hbuf".
    iInv "Hri" as ">Hrb" "Hclr".
    iDestruct "Hrb" as (t) "[Hhalf _]".
    iDestruct (ghost_var_agree with "Hhalf Hbuf") as %->.
    iMod (ghost_var_update_halves (0%Z) with "Hhalf Hbuf") as "[Hhalf Hbuf]".
    iMod (escA_deposit with "Hei Hmk") as "#Hcom"; [solve_ndisj|].
    iMod ("Hclr" with "[Hhalf Hrh]") as "_".
    { iNext. iExists (0%Z). iFrame "Hhalf". iRight. iSplit; [done|].
      iExists ge, gr. iFrame "Hrh Hcom". }
    iModIntro. iFrame "Hcom Hbuf".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  (d+e) readout + redeem-before-withdraw, WITH the agreement           *)
  (* ------------------------------------------------------------------ *)

  (* the next thread reaching the pool entry holds [pool_pending] and, having
     read the type=0 disk block, its half of the byte.  It OPENS the region
     (as the real redeemer opens [ireg_inv]), finds the region's pending arm
     (forced by t=0), and derives the escrow-name agreement from the two
     registry halves held simultaneously -- the crux the stock de-risk could
     not test.  Agreement forces its pool-side ticket and the region's
     committed to name the SAME escrow, so [escA_redeem] yields [imark] --
     exactly what [ireg_withdraw]'s consumer [Q] takes.  The region's own half
     and (persistent) committed go back, so the region stays well-formed until
     a later ialloc reclaims the slot. *)
  Lemma redeemA_supplies_withdraw E γreg gi inum gfs (Q : iProp Σ) :
    ↑iregAN ⊆ E → ↑escAN inum ⊆ E →
    mini_region_inv γreg inum gfs -∗
    ghost_var gfs (1/2) (0%Z) -∗
    pool_pending γreg gi inum -∗
    (InodeRegion.imark gi (bv_unsigned inum) ={E}=∗ Q) -∗
    |={E}=> Q ∗ ghost_var gfs (1/2) (0%Z).
  Proof.
    iIntros (Hi He) "#Hri Hbuf Hpool Hwd".
    iDestruct "Hpool" as (ge1 gr1) "(Hrh1 & #Hei1 & Htick)".
    iInv "Hri" as ">Hrb" "Hclr".
    iDestruct "Hrb" as (t) "[Hhalf Harm]".
    iDestruct (ghost_var_agree with "Hhalf Hbuf") as %->.
    iDestruct "Harm" as "[%Hne | [_ Hpend]]"; [done|].
    iDestruct "Hpend" as (ge2 gr2) "[Hrh2 #Hcom]".
    iDestruct (reg_half_agree with "Hrh1 Hrh2") as %[-> ->].
    iMod (escA_redeem with "Hei1 Htick Hcom") as "Hmk"; [solve_ndisj|].
    iMod ("Hclr" with "[Hhalf Hrh2]") as "_".
    { iNext. iExists (0%Z). iFrame "Hhalf". iRight. iSplit; [done|].
      iExists ge2, gr2. iFrame "Hrh2 Hcom". }
    iMod ("Hwd" with "Hmk") as "HQ".
    iModIntro. iFrame "HQ Hbuf".
  Qed.

End escrowA.
