(* KexecPtImage.v -- kexec's page borrow, at the NAMED image.

   THE PROBLEM.  kexec's loadseg loop reads a file page straight into a
   page of the NEW address space.  The way ProofKexecB2.v does it today
   loses the bytes: it holds the ∃-weakened table [proc_pt_any P], borrows
   the page ANONYMOUSLY ([proc_pt_page_acc] -> [page_named]), names the
   bytes with [SpecKexecB2.kxc_page_take], lets readi overwrite the first
   [nn] of them, and then re-anonymises with [kxc_page_give] before the
   accessor's wand folds back to [proc_pt_any P].  Nothing downstream can
   say what the loaded address space CONTAINS, which is exactly what the
   exec AU contract has to say.

   WHAT THIS FILE ADDS.  The same borrow at the PRECISE table
   [ProcPtOwn.proc_pt P M]: the page goes out already named by [M] (a
   mapped page's 4096 bytes are all recorded there, since [umem_own] pins
   [dom M = uva_dom P]), and the closer takes it back at NEW bytes and
   moves [M] by exactly the [umem_write] those bytes make.

   IT IS NOT NEW OWNERSHIP -- it is the existing [proc_ptm_window] /
   [proc_ptm_page_write] pair, re-stated one view over.  [proc_pt] and
   [proc_ptm] own the same resource ([ProcPtOwn] §5c'), so the whole proof
   is the round trip [proc_ptm_of_pt] / [proc_pt_of_ptm] with the write
   pushed through both halves: the lazy witness [Mz] is an ∃ that the
   round trip must re-supply, and [umem_write_mono] is what says the
   submap relation survives the write.  Stating it here rather than in
   ProcPtOwn.v keeps that 5.7k-line file (and its ~260 consumers) untouched.

   THE THREE FORMS, in the order loadseg wants them:
     [proc_pt_window]           -- [n] bytes at [off] inside a mapped page;
     [proc_pt_page_borrow]      -- the whole page, back at ANY [g];
     [proc_pt_page_load]        -- the whole page, back at the
                                   [SpecReadi.rd_delivered] shape
                                   ([if j < nn then new j else old j]),
                                   moving [M] by the [nn]-byte write only;
     [proc_pt_page_load_split]  -- the same, carved at [nn] the way
                                   [kxc_page_take] / [kxc_page_give] carve
                                   it, so readi's [seq 0 nn] destination
                                   and its untouched tail are separate. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap sets bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import KallocInv.
Require Import KMap.
Require Import PageGeom.
Require Import ByteBuf.
Require Import TsoCtx.
Require Import PtTree.
Require Import PtBuild.
Require Import UptTree.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import UmCovered.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 Two pure facts about [umem_write] that the view crossing needs.     *)
(* ===================================================================== *)

(* the write is MONOTONE in the map -- the lazy view's backed submap stays
   a submap after both sides take the same write.  [umem_write] is a
   fold of [insert]s at addresses that do not depend on the map, so this
   is [insert_mono] once per step. *)
Lemma umem_write_mono (M Mz : gmap Z (bv 8)) (a : Z) (n : nat)
    (bs : nat -> bv 8) :
  M ⊆ Mz -> umem_write M a n bs ⊆ umem_write Mz a n bs.
Proof.
  intros Hsub. induction n as [| k IH]; [exact Hsub |].
  cbn [umem_write]. apply insert_mono. exact IH.
Qed.

(* ...and it only reads its source below [n] *)
Lemma umem_write_ext (M : gmap Z (bv 8)) (a : Z) (n : nat)
    (bs cs : nat -> bv 8) :
  (forall j, (j < n)%nat -> bs j = cs j) ->
  umem_write M a n bs = umem_write M a n cs.
Proof.
  induction n as [| k IH]; intros He; [reflexivity |].
  cbn [umem_write]. rewrite (IH ltac:(intros j Hj; apply He; lia)).
  rewrite (He k ltac:(lia)). reflexivity.
Qed.

Section KexecPtImage.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* ------------------------------------------------------------------ *)
  (* §2 The mapped view's two book-keeping facts.                        *)
  (* ------------------------------------------------------------------ *)

  Lemma proc_pt_dom (P : uptd) (M : gmap Z (bv 8)) :
    proc_pt P M -∗ ⌜dom M = uva_dom P⌝.
  Proof.
    rewrite /proc_pt. iIntros "(_ & _ & Hm)".
    iApply (umem_own_dom with "Hm").
  Qed.

  (* ...and its CONVERSE at the top: above a PAGE-ALIGNED [um_below]
     bound, the image has no key at all.  This is what makes the stack
     page uvmalloc is about to add all zeros ([KexecBuilt.kx_page_zero_grow]
     asks for exactly this freshness premise).  The alignment hypothesis is
     load-bearing: [um_below] bounds the page BASE, so without it a mapped
     page could straddle the bound. *)
  Lemma proc_pt_fresh_above (P : uptd) (M : gmap Z (bv 8)) (szv : mword 64) :
    bv_unsigned szv `mod` 4096 = 0 ->
    um_below szv P.(ud_um) ->
    proc_pt P M -∗ ⌜forall a : Z, (bv_unsigned szv <= a)%Z -> M !! a = None⌝.
  Proof.
    intros Halign Hbel. iIntros "Hpt".
    iDestruct (proc_pt_dom with "Hpt") as %Hdom.
    iPureIntro. intros a Ha.
    destruct (M !! a) as [b |] eqn:E; [exfalso | reflexivity].
    assert (Hin : a ∈ dom M) by (apply elem_of_dom; exists b; exact E).
    rewrite Hdom in Hin.
    apply elem_of_uva_dom in Hin as (vpn & w & j & Hl & Hj & ->).
    pose proof (Hbel vpn w Hl) as Hlt.
    pose proof (Z.div_mod (bv_unsigned szv) 4096 ltac:(lia)) as Hdm.
    rewrite Halign in Hdm.
    assert (Hq : (bv_unsigned vpn < bv_unsigned szv / 4096)%Z) by lia.
    lia.
  Qed.

  (* ...and the same fact at EVERY page-aligned bound at or above the
     [um_below] size, extracted ONCE.  The phdr loop needs the freshness at
     the NEXT segment's [vaddr] -- which it only knows is above the running
     [sz] under the walk's own guard, i.e. after the resource is gone -- so
     the bound has to be universally quantified inside the ⌜⌝. *)
  Lemma proc_pt_fresh_above_z (P : uptd) (M : gmap Z (bv 8)) (szv : mword 64) :
    um_below szv P.(ud_um) ->
    proc_pt P M -∗
    ⌜forall bnd : Z, (bnd `mod` 4096 = 0)%Z ->
       (bv_unsigned szv <= bnd)%Z ->
       forall a : Z, (bnd <= a)%Z -> M !! a = None⌝.
  Proof.
    intros Hbel. iIntros "Hpt".
    iDestruct (proc_pt_dom with "Hpt") as %Hdom.
    iPureIntro. intros bnd Halign Hge a Ha.
    destruct (M !! a) as [b |] eqn:E; [exfalso | reflexivity].
    assert (Hin : a ∈ dom M) by (apply elem_of_dom; exists b; exact E).
    rewrite Hdom in Hin.
    apply elem_of_uva_dom in Hin as (vpn & w & j & Hl & Hj & ->).
    pose proof (Hbel vpn w Hl) as Hlt.
    (* the page BASE is a multiple of 4096 strictly below [bnd], and [bnd]
       is one too, so the whole page is below it *)
    pose proof (Z.div_mod bnd 4096 ltac:(lia)) as Hdm. rewrite Halign in Hdm.
    lia.
  Qed.

  (* every byte of a MAPPED page is recorded in [M] -- what turns the
     total lookup [M !!! va] the accessor names into a real [Some] *)
  Lemma proc_pt_page_bytes (P : uptd) (M : gmap Z (bv 8))
      (vpn : mword 27) (w : mword 64) :
    P.(ud_um) !! vpn = Some w ->
    proc_pt P M -∗
    ⌜forall j, (j < 4096)%nat ->
       M !! (bv_unsigned vpn * 4096 + Z.of_nat j)%Z
       = Some (M !!! (bv_unsigned vpn * 4096 + Z.of_nat j)%Z)⌝.
  Proof.
    intros Hl. iIntros "Hpt".
    iDestruct (proc_pt_dom with "Hpt") as %Hdom.
    iPureIntro. intros j Hj.
    assert (Hs : is_Some (M !! (bv_unsigned vpn * 4096 + Z.of_nat j)%Z)).
    { apply (proj2 (umem_own_lookup_is_Some P M _ Hdom)).
      exists vpn, w, j. split_and!; [exact Hl | exact Hj | reflexivity]. }
    destruct Hs as [bb Hbb]. rewrite Hbb lookup_total_alt Hbb. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §3 THE WINDOW, at the mapped view.                                  *)
  (* ------------------------------------------------------------------ *)
  Lemma proc_pt_window (P : uptd) (M : gmap Z (bv 8))
      (vpn : mword 27) (w : mword 64) (off n : nat) :
    proc_pt_wf P -> P.(ud_um) !! vpn = Some w -> (off + n <= 4096)%nat ->
    kmap_static_claims -∗ proc_pt P M -∗
      ([∗ list] j ∈ seq 0 n,
         (pa_add (pa_add (page_base (pte_ppn w)) off) j : Arch.pa)
           ↦ₘ (M !!! ((bv_unsigned vpn * 4096 + Z.of_nat off) + Z.of_nat j)%Z)) ∗
      (∀ bs : nat -> bv 8,
         ([∗ list] j ∈ seq 0 n,
            (pa_add (pa_add (page_base (pte_ppn w)) off) j : Arch.pa) ↦ₘ bs j) -∗
         proc_pt P (umem_write M (bv_unsigned vpn * 4096 + Z.of_nat off)%Z n bs)).
  Proof.
    intros Hwf Hl Hn. iIntros "#Hb Hpt".
    iDestruct (proc_pt_dom with "Hpt") as %Hdom.
    (* the page's bytes are all in [M] -- used for the window's [is_Some]
       side conditions and for the [Mz]-vs-[M] naming agreement *)
    assert (Hsome : forall j, (j < 4096)%nat ->
              is_Some (M !! (bv_unsigned vpn * 4096 + Z.of_nat j)%Z)).
    { intros j Hj. apply (proj2 (umem_own_lookup_is_Some P M _ Hdom)).
      exists vpn, w, j. split_and!; [exact Hl | exact Hj | reflexivity]. }
    iDestruct (proc_ptm_of_pt P 0 M with "Hpt") as "(_ & Hpt)".
    iDestruct "Hpt" as (Mz) "[%Hsub Hpt]".
    assert (Hagree : forall j, (j < 4096)%nat ->
              Mz !!! (bv_unsigned vpn * 4096 + Z.of_nat j)%Z
              = M !!! (bv_unsigned vpn * 4096 + Z.of_nat j)%Z).
    { intros j Hj. destruct (Hsome j Hj) as [bb Hbb].
      rewrite !lookup_total_alt Hbb.
      rewrite (lookup_weaken M Mz _ bb Hbb Hsub). reflexivity. }
    assert (Hidx : forall k : nat,
              ((bv_unsigned vpn * 4096 + Z.of_nat off) + Z.of_nat k)%Z
              = (bv_unsigned vpn * 4096 + Z.of_nat (off + k)%nat)%Z)
      by (intros k; rewrite Nat2Z.inj_add; lia).
    iDestruct (proc_ptm_window P 0 Mz vpn w off n Hwf Hl Hn with "Hb Hpt")
      as "[Hwin Hback]".
    iSplitL "Hwin".
    - iApply (big_sepL_mono with "Hwin"). intros i j Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite !Hidx (Hagree (off + i)%nat ltac:(lia)). reflexivity.
    - iIntros (bs) "Hw".
      iDestruct ("Hback" $! bs with "Hw") as "Hpt".
      iApply (proc_pt_of_ptm P 0
                (umem_write M (bv_unsigned vpn * 4096 + Z.of_nat off)%Z n bs)
                (umem_write Mz (bv_unsigned vpn * 4096 + Z.of_nat off)%Z n bs)
                (umem_write_mono M Mz _ n bs Hsub) with "Hpt").
      rewrite (umem_write_dom M (bv_unsigned vpn * 4096 + Z.of_nat off)%Z n bs
                 ltac:(intros j Hj; rewrite Hidx; apply Hsome; lia)).
      exact Hdom.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §4 THE WHOLE PAGE, back at anything.                                *)
  (* ------------------------------------------------------------------ *)
  Lemma proc_pt_page_borrow (P : uptd) (M : gmap Z (bv 8))
      (vpn : mword 27) (w : mword 64) (base : Z) :
    proc_pt_wf P -> P.(ud_um) !! vpn = Some w ->
    base = (bv_unsigned vpn * 4096)%Z ->
    kmap_static_claims -∗ proc_pt P M -∗
      ([∗ list] j ∈ seq 0 4096,
         (pa_add (page_base (pte_ppn w)) j : Arch.pa)
           ↦ₘ (M !!! (base + Z.of_nat j)%Z)) ∗
      (∀ g : nat -> bv 8,
         ([∗ list] j ∈ seq 0 4096,
            (pa_add (page_base (pte_ppn w)) j : Arch.pa) ↦ₘ g j) -∗
         proc_pt P (umem_write M base 4096 g)).
  Proof.
    intros Hwf Hl ->. iIntros "#Hb Hpt".
    assert (Hb0 : (bv_unsigned vpn * 4096 + Z.of_nat 0)%Z
                  = (bv_unsigned vpn * 4096)%Z) by lia.
    iDestruct (proc_pt_window P M vpn w 0 4096 Hwf Hl ltac:(lia)
                 with "Hb Hpt") as "[Hpg Hback]".
    iEval (rewrite Hb0 pa_add_0) in "Hpg".
    iEval (rewrite Hb0 pa_add_0) in "Hback".
    iFrame "Hpg". iIntros (g) "Hp". iApply ("Hback" $! g with "Hp").
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §5 THE LOADSEG FORM.  readi writes the first [nn] bytes and leaves   *)
  (* the tail alone, so the page comes back at [rd_delivered]'s shape --  *)
  (* and [M] then moves by the [nn]-byte write ONLY ([umem_write_split]   *)
  (* is the whole content of that step).                                  *)
  (* ------------------------------------------------------------------ *)
  Lemma proc_pt_page_load (P : uptd) (M : gmap Z (bv 8))
      (vpn : mword 27) (w : mword 64) (base : Z) (nn : nat) :
    proc_pt_wf P -> P.(ud_um) !! vpn = Some w ->
    base = (bv_unsigned vpn * 4096)%Z -> (nn <= 4096)%nat ->
    kmap_static_claims -∗ proc_pt P M -∗
      ([∗ list] j ∈ seq 0 4096,
         (pa_add (page_base (pte_ppn w)) j : Arch.pa)
           ↦ₘ (M !!! (base + Z.of_nat j)%Z)) ∗
      (∀ new : nat -> bv 8,
         ([∗ list] j ∈ seq 0 4096,
            (pa_add (page_base (pte_ppn w)) j : Arch.pa)
              ↦ₘ (if decide (j < nn)%nat
                  then new j else M !!! (base + Z.of_nat j)%Z)) -∗
         proc_pt P (umem_write M base nn new)).
  Proof.
    intros Hwf Hl Hbase Hnn. iIntros "#Hb Hpt".
    iDestruct (proc_pt_page_bytes P M vpn w Hl with "Hpt") as %Hbytes.
    rewrite <- Hbase in Hbytes.
    iDestruct (proc_pt_page_borrow P M vpn w base Hwf Hl Hbase with "Hb Hpt")
      as "[Hpg Hback]".
    iFrame "Hpg". iIntros (new) "Hp".
    (* the whole-page write collapses to the [nn]-byte one: the tail was
       handed back at the bytes [M] already recorded ([umem_write_split]),
       and below [nn] the [decide] picks [new] ([umem_write_ext]) *)
    assert (Heq : umem_write M base 4096
                    (fun j : nat => if decide (j < nn)%nat
                                    then new j else M !!! (base + Z.of_nat j)%Z)
                  = umem_write M base nn new).
    { rewrite (umem_write_split M base 4096 0 nn
                 (fun j : nat => if decide (j < nn)%nat
                                 then new j else M !!! (base + Z.of_nat j)%Z)
                 ltac:(lia)
                 ltac:(intros j Hj Hout; cbn beta;
                       rewrite decide_False; [apply Hbytes; lia | lia])).
      replace (base + Z.of_nat 0)%Z with base by lia.
      apply umem_write_ext. intros j Hj. cbn beta.
      rewrite Nat.add_0_l decide_True; [reflexivity | lia]. }
    iDestruct ("Hback" $! (fun j : nat => if decide (j < nn)%nat
                                          then new j
                                          else M !!! (base + Z.of_nat j)%Z)
                 with "Hp") as "Hpt".
    rewrite Heq. iExact "Hpt".
  Qed.

  (* the same borrow CARVED AT [nn] -- readi's destination and the tail it
     never touches, exactly the split [kxc_page_take] performs on the
     anonymous page.  The tail goes out and comes back at the same names,
     so the caller has nothing to say about it. *)
  Lemma proc_pt_page_load_split (P : uptd) (M : gmap Z (bv 8))
      (vpn : mword 27) (w : mword 64) (base : Z) (nn : nat) :
    proc_pt_wf P -> P.(ud_um) !! vpn = Some w ->
    base = (bv_unsigned vpn * 4096)%Z -> (nn <= 4096)%nat ->
    kmap_static_claims -∗ proc_pt P M -∗
      ([∗ list] j ∈ seq 0 nn,
         (pa_add (page_base (pte_ppn w)) j : Arch.pa)
           ↦ₘ (M !!! (base + Z.of_nat j)%Z)) ∗
      ([∗ list] j ∈ seq 0 (4096 - nn),
         (pa_add (pa_add (page_base (pte_ppn w)) nn) j : Arch.pa)
           ↦ₘ (M !!! (base + Z.of_nat (nn + j)%nat)%Z)) ∗
      (∀ new : nat -> bv 8,
         ([∗ list] j ∈ seq 0 nn,
            (pa_add (page_base (pte_ppn w)) j : Arch.pa) ↦ₘ new j) -∗
         ([∗ list] j ∈ seq 0 (4096 - nn),
            (pa_add (pa_add (page_base (pte_ppn w)) nn) j : Arch.pa)
              ↦ₘ (M !!! (base + Z.of_nat (nn + j)%nat)%Z)) -∗
         proc_pt P (umem_write M base nn new)).
  Proof.
    intros Hwf Hl Hbase Hnn. iIntros "#Hb Hpt".
    iDestruct (proc_pt_page_load P M vpn w base nn Hwf Hl Hbase Hnn
                 with "Hb Hpt") as "[Hpg Hback]".
    rewrite (bb_split3 (page_base (pte_ppn w)) nn (4096 - nn) 0 4096
               (fun j => M !!! (base + Z.of_nat j)%Z) (DfracOwn 1)
               ltac:(lia)).
    iDestruct "Hpg" as "(HA & HB & _)".
    iFrame "HA HB". iIntros (new) "HA HB".
    iApply ("Hback" $! new with "[HA HB]").
    rewrite (bb_split3 (page_base (pte_ppn w)) nn (4096 - nn) 0 4096
               (fun j => if decide (j < nn)%nat
                         then new j else M !!! (base + Z.of_nat j)%Z)
               (DfracOwn 1) ltac:(lia)).
    iSplitL "HA"; [| iSplitL "HB"].
    - iApply (big_sepL_mono with "HA"). intros i j Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite decide_True; [reflexivity | lia].
    - iApply (big_sepL_mono with "HB"). intros i j Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite decide_False; [reflexivity | lia].
    - by rewrite big_sepL_nil.
  Qed.

  (* the same split with the page's OWN byte name supplied by the caller.
     [SpecKexecB2.kxc_page_take] hands the anonymous page out under an
     ∃-bound [f] and the whole loadseg block is written against that name;
     this is the same statement with [f] a parameter constrained to be
     [M]'s bytes, so the block reads unchanged and only the closer's
     conclusion gains the [umem_write]. *)
  Lemma proc_pt_page_load_split_f (P : uptd) (M : gmap Z (bv 8))
      (vpn : mword 27) (w : mword 64) (base : Z) (nn : nat) (f : nat -> bv 8) :
    proc_pt_wf P -> P.(ud_um) !! vpn = Some w ->
    base = (bv_unsigned vpn * 4096)%Z -> (nn <= 4096)%nat ->
    (forall j : nat, (j < 4096)%nat -> f j = M !!! (base + Z.of_nat j)%Z) ->
    kmap_static_claims -∗ proc_pt P M -∗
      ([∗ list] j ∈ seq 0 nn,
         (pa_add (page_base (pte_ppn w)) j : Arch.pa) ↦ₘ f j) ∗
      ([∗ list] j ∈ seq 0 (4096 - nn),
         (pa_add (pa_add (page_base (pte_ppn w)) nn) j : Arch.pa)
           ↦ₘ f (nn + j)%nat) ∗
      (∀ new : nat -> bv 8,
         ([∗ list] j ∈ seq 0 nn,
            (pa_add (page_base (pte_ppn w)) j : Arch.pa) ↦ₘ new j) -∗
         ([∗ list] j ∈ seq 0 (4096 - nn),
            (pa_add (pa_add (page_base (pte_ppn w)) nn) j : Arch.pa)
              ↦ₘ f (nn + j)%nat) -∗
         proc_pt P (umem_write M base nn new)).
  Proof.
    intros Hwf Hl Hbase Hnn Hf. iIntros "#Hb Hpt".
    iDestruct (proc_pt_page_load_split P M vpn w base nn Hwf Hl Hbase Hnn
                 with "Hb Hpt") as "(HA & HB & Hback)".
    iSplitL "HA".
    { iApply (big_sepL_mono with "HA"). intros i j Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite (Hf i ltac:(lia)). reflexivity. }
    iSplitL "HB".
    { iApply (big_sepL_mono with "HB"). intros i j Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite (Hf (nn + i)%nat ltac:(lia)). reflexivity. }
    iIntros (new) "HA HB". iApply ("Hback" $! new with "HA [HB]").
    iApply (big_sepL_mono with "HB"). intros i j Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
    rewrite (Hf (nn + i)%nat ltac:(lia)). reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §5b THE WALK BRACKET, at the named image.  loadseg calls walkaddr    *)
  (* between the two halves of the page borrow, and [ProcPtOwn]'s pair    *)
  (* ([proc_pt_acc_rep0] / [proc_pt_rebuild]) is stated at the            *)
  (* ∃-weakened tier, so replaying it would drop the image the borrow is  *)
  (* there to keep.  These are the same two proofs with [umem_own P M]    *)
  (* in place of [proc_pt_own P] -- the bytes ride through untouched,     *)
  (* which is exactly why the tree half can be opened at all.  ([ProcPtOwn]
     already has the [proc_ptm] pair, [proc_ptm_acc_rep0] /               *)
  (* [proc_ptm_rebuild]; this is its [proc_pt] twin.) *)
  (* ------------------------------------------------------------------ *)
  (* [proc_ptm]'s well-formedness projection, the twin of [proc_pt_wf_get]
     -- ProcPtOwn has the [proc_pt_any] one only. *)
  Lemma proc_ptm_wf_get (P : uptd) (sz : Z) (M : gmap Z (bv 8)) :
    proc_ptm P sz M ⊢ ⌜proc_pt_wf P⌝.
  Proof. rewrite /proc_ptm. iIntros "(%Hwf & _)". iPureIntro. exact Hwf. Qed.

  Lemma proc_pt_acc_rep0_m (P : uptd) (M : gmap Z (bv 8)) :
    proc_pt P M ⊢ ∃ t m_ad, ⌜pt_rep0 t m_ad⌝ ∗
      ⌜upt_ad_view P.(ud_tfp) P.(ud_um) m_ad⌝ ∗
      ⌜pt_base t = P.(ud_root)⌝ ∗ ⌜proc_pt_wf P⌝ ∗
      ptree_own 2 (DfracOwn 1) t ∗ umem_own P M.
  Proof.
    rewrite /proc_pt. iIntros "(%Hwf & Ht & Hm)".
    iDestruct "Ht" as (t) "(%Hspec & Ht)".
    destruct (upt_spec_rep0 P.(ud_root) P.(ud_tfp) P.(ud_um) t Hspec)
      as (m_ad & Hrep & Hview).
    iExists t, m_ad.
    iSplitR; [iPureIntro; exact Hrep |].
    iSplitR; [iPureIntro; exact Hview |].
    iSplitR; [iPureIntro; exact (proj1 Hspec) |].
    iSplitR; [iPureIntro; exact Hwf |].
    iFrame "Ht Hm".
  Qed.

  Lemma proc_pt_rebuild_m (P : uptd) (M : gmap Z (bv 8)) (t' : ptree)
      (m_ad : gmap (mword 27) (mword 64)) :
    proc_pt_wf P -> upt_ad_view P.(ud_tfp) P.(ud_um) m_ad ->
    pt_rep0 t' m_ad -> pt_base t' = P.(ud_root) ->
    ptree_own 2 (DfracOwn 1) t' -∗ umem_own P M -∗ proc_pt P M.
  Proof.
    intros Hwf Hview Hrep Hbase. iIntros "Ht Hm".
    rewrite /proc_pt. iSplitR; [iPureIntro; exact Hwf |].
    iSplitL "Ht"; [| iFrame "Hm"].
    rewrite /pt_frame. iExists t'. iFrame "Ht". iPureIntro.
    exact (upt_spec_of_rep0 P.(ud_root) P.(ud_tfp) P.(ud_um) m_ad t'
             (proj1 Hwf) Hview Hrep Hbase).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §6 THE COVERED CROSSING -- [proc_pt] and [proc_ptm] at the SAME map. *)
  (*                                                                     *)
  (* kexec builds an address space in which EVERY page below the running  *)
  (* size is mapped ([um_covered], which every seam of the cone carries), *)
  (* and there the lazy view has nothing left to be lazy about: its zero  *)
  (* filler set is empty and [umem_lazy P sz M] is [umem_own P M] on the  *)
  (* nose.  That is what lets the cone thread ONE image [M] through both  *)
  (* the loader (which speaks [proc_pt], §3-§5) and the _mem contracts    *)
  (* copyout / uvmalloc / the commit speak ([proc_ptm]), with no [∃]      *)
  (* re-supplied at the crossing -- the map that goes out is the map that *)
  (* comes back.                                                         *)
  (* ------------------------------------------------------------------ *)

  (* every live va of a covered space is a MAPPED va.  Pure; the [2^38]
     bound is [uvm_maxsz]'s, and is what makes [svpn_of] read the vpn
     back out of the address. *)
  Lemma uva_live_mapped_covered (P : uptd) (sz : Z) :
    (sz <= 274877906944)%Z -> um_covered_z sz P.(ud_um) ->
    forall va : Z, uva_live sz va -> uva_mapped P va.
  Proof.
    intros Hsz Hcov va Hlv. unfold uva_live, UserPtTree.pgroundup in Hlv.
    pose proof (Z.div_mod va 4096 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound va 4096 ltac:(lia)) as Hmb.
    pose proof (Z.div_mod (sz + 4095) 4096 ltac:(lia)) as Hds.
    pose proof (Z.mod_pos_bound (sz + 4095) 4096 ltac:(lia)) as Hsb.
    (* the page base is a multiple of 4096 strictly below [pgroundup sz],
       hence strictly below [sz] itself *)
    assert (Hlt : (4096 * (va / 4096) < sz)%Z) by lia.
    assert (Hb : (0 <= va < 274877906944)%Z) by lia.
    assert (Hu : bv_unsigned (svpn_of (mword_of_int va : mword 64)) = (va / 4096)%Z).
    { assert (Hmod : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
      assert (Hui : uint (mword_of_int va : mword 64) = va).
      { rewrite uint_unsigned moi64_unsigned. apply bv_wrap_small. lia. }
      rewrite (svpn_of_unsigned_lo (mword_of_int va) ltac:(rewrite Hui; lia)).
      rewrite Hui Z.shiftr_div_pow2; [| lia]. reflexivity. }
    destruct (Hcov (svpn_of (mword_of_int va : mword 64)) ltac:(rewrite Hu; lia))
      as [w Hw].
    exists (svpn_of (mword_of_int va : mword 64)), w, (Z.to_nat (va `mod` 4096)).
    split_and!; [exact Hw | lia |]. rewrite Hu Z2Nat.id; lia.
  Qed.

  (* ...and the crossing itself, at the map the caller names. *)
  Lemma proc_pt_ptm_live (P : uptd) (sz : Z) (M : gmap Z (bv 8)) :
    (forall va : Z, uva_live sz va -> uva_mapped P va) ->
    proc_pt P M ⊣⊢ proc_ptm P sz M.
  Proof.
    intros Hlm. rewrite /proc_pt /proc_ptm. iSplit.
    - iIntros "(%Hwf & Ht & Hm)". iSplitR; [done |]. iFrame "Ht".
      iDestruct "Hm" as "[%Hdom Hm]". iExists M.
      iSplitR; [iPureIntro; reflexivity |].
      iSplitR.
      { iPureIntro. intros va. rewrite <- elem_of_dom, Hdom, elem_of_uva_dom.
        split; [by left |]. intros [Hm | Hl]; [exact Hm | exact (Hlm va Hl)]. }
      iSplitR; [iPureIntro; intros va Hnm Hl; destruct (Hnm (Hlm va Hl)) |].
      iSplitR; [iPureIntro; exact Hdom |]. iExact "Hm".
    - iIntros "(%Hwf & Ht & Hm)". iSplitR; [done |]. iFrame "Ht".
      iDestruct (umem_lazy_dom with "Hm") as %Hdm.
      assert (Hdom : dom M = uva_dom P).
      { apply set_eq. intros va. rewrite elem_of_dom (Hdm va) elem_of_uva_dom.
        split; [intros [Hm | Hl]; [exact Hm | exact (Hlm va Hl)] | by left]. }
      iApply (umem_own_of_lazy P sz M M (reflexivity _) Hdom with "Hm").
  Qed.

  (* the same, with the bound supplied by the caller. *)
  Lemma proc_pt_ptm_covered (P : uptd) (szv : mword 64) (M : gmap Z (bv 8)) :
    (bv_unsigned szv <= 274877906944)%Z -> um_covered szv P.(ud_um) ->
    proc_pt P M ⊣⊢ proc_ptm P (uint szv) M.
  Proof.
    intros Hsz Hcov. rewrite uint_unsigned.
    apply (proc_pt_ptm_live P (bv_unsigned szv) M).
    exact (uva_live_mapped_covered P (bv_unsigned szv) Hsz Hcov).
  Qed.

  (* the spelling the cone actually uses: coverage alone, with the size
     bound read off it ([UmCovered.proc_pt_covered_maxsz] -- a covered
     space cannot reach past [uvm_maxsz], because there are only 2^27
     user vpns), so a call site needs nothing but its seam's own
     [proc_pt_wf] / [um_covered] pair. *)
  Lemma proc_pt_ptm_cov (P : uptd) (szv : mword 64) (M : gmap Z (bv 8)) :
    proc_pt_wf P -> um_covered szv P.(ud_um) ->
    proc_pt P M ⊣⊢ proc_ptm P (uint szv) M.
  Proof.
    intros Hwf Hcov.
    assert (Hb : (bv_unsigned szv <= uvm_maxsz)%Z)
      by exact (proc_pt_covered_maxsz P szv Hwf Hcov).
    rewrite uvm_maxsz_val in Hb.
    exact (proc_pt_ptm_covered P szv M ltac:(lia) Hcov).
  Qed.

  (* the two directions as ENTAILMENTS, which is the form a call site
     wants: [iDestruct] then unifies the size and the map against the
     hypothesis it already holds, and the coverage side condition arrives
     as an [ltac:] argument. *)
  Lemma proc_pt_to_ptm_cov (P : uptd) (szv : mword 64) (M : gmap Z (bv 8)) :
    proc_pt_wf P -> um_covered szv P.(ud_um) ->
    proc_pt P M -∗ proc_ptm P (uint szv) M.
  Proof. intros Hwf Hcov. rewrite (proc_pt_ptm_cov P szv M Hwf Hcov). auto. Qed.

  Lemma proc_ptm_to_pt_cov (P : uptd) (szv : mword 64) (M : gmap Z (bv 8)) :
    proc_pt_wf P -> um_covered szv P.(ud_um) ->
    proc_ptm P (uint szv) M -∗ proc_pt P M.
  Proof. intros Hwf Hcov. rewrite (proc_pt_ptm_cov P szv M Hwf Hcov). auto. Qed.

End KexecPtImage.
