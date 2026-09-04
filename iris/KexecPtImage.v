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
Require Import UserPtTree.
Require Import ProcPtOwn.
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

End KexecPtImage.
