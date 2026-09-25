(* ===================================================================== *)
(* UkFreeHandler.v -- THE FREE HANDLER: the taint pays any disciplined    *)
(* tree, once, generic in the application's taint predicate.             *)
(*                                                                        *)
(* Design: claude-notes/design/program-specs.md SS3.4c, SS3.4e.  Every   *)
(* law of [UkHandler.ep_iface] has a taint arm; the instance must prove   *)
(* [ei_taint_pays : forall held t, safe_fds held t -> ei_taint held -*    *)
(* tree_pay N P t].  [UkFileIface.fif_taint_pays] proved it for the file *)
(* application's taint, and what its proof actually spends is not the    *)
(* file application at all: a PERSISTENT taint [T] with the two boxed    *)
(* readings [T -* app_taint] (the kill credential the close leaf takes)   *)
(* and [T -* app_sup] (the supply the write, read and open leaves take   *)
(* their deposit laws from), the exit payload, the ledger with every     *)
(* held standard slot open, and the handles of the held tail             *)
(* descriptors.  This file is that proof over an abstract [T]; the       *)
(* pipeline's instance ([UkPipeIface]) spends it at [echo_taint], and    *)
(* the file instance is to be repointed at [file_taint] (another lane).  *)
(*                                                                        *)
(*   [fh_taint T held]   the taint at the held descriptors                *)
(*   [fh_taint_pays]     safe_fds held t -> fh_taint T held -* tree_pay t  *)
(*                                                                        *)
(* The four free leaves are the application-generic ones: the QUIET      *)
(* write ([UkRunSys.wp_uk_ecall_quiet]), the read with the kernel's      *)
(* count bound ([wp_uk_ecall_read], lane rdbound), the close of a        *)
(* standard slot or a handle ([wp_uk_ecall_close_std] / [_close]), and   *)
(* the open ([wp_uk_ecall_open]: a fresh handle above the standard       *)
(* slots, or a standard slot re-opened, or -1).                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import ProgTree UkTree UkStub.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith UmodeAbi UserBits.
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs.
Require Import FdSlots UserFd.
Require Import UserHeap UserPerm UserPtTree.
Require Import ProcGeom.
Require Import CtxIdDefs.
Require Import UexecSlot UexecRet UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst UexecExecMint.
Require Import UsysMemOk.
Require Import AppCfg AppInv.
Require Import UkCatTree.                (* [bvs_moi_small] *)
Local Open Scope Z_scope.
Import Defs.

(* the answer -1, as a word *)
Lemma fh_m1 : bv_signed (mword_of_int (-1) : mword 64) = -1.
Proof. vm_compute. reflexivity. Qed.

(* every held descriptor is an open standard slot of the ledger [l] or a
   handle of [hm] *)
Definition fh_held_ok (held : gset Z) (l : list fdstate) (hm : gmap Z fdstate) : Prop :=
  forall fd, fd ∈ held -> (0 <= fd < Z.of_nat NOFILE)
    /\ ((fd < Z.of_nat NSTD /\ exists st, l !! Z.to_nat fd = Some st /\ st <> FdClosed)
        \/ (Z.of_nat NSTD <= fd /\ is_Some (hm !! fd))).

Section UkFreeHandler.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  (* the two ghost-variable classes [UkTree]'s holes take, bound here as
     [UkHandler] binds them, so an instance that binds them itself (the
     pipeline's) and one that takes them off the [xv6G] bundle (the file's)
     both unify with these laws *)
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{PS : UexecSG.uprogSG Σ}.

  (* THE TAINT, persistent *)
  Context (T : iProp Σ) `{T_pers : !Persistent T}.

  (* the process, and ANY program instance with its five stubs *)
  Context (N : uk_names Σ) (P : uprog Σ).
  Context `{HNc : !ukn_const N}.
  Hypothesis Hsr : ⊢ stub_law N (up_code P) 5 (up_read P).
  Hypothesis Hsw : ⊢ stub_law N (up_code P) 16 (up_write P).
  Hypothesis Hso : ⊢ stub_law N (up_code P) 15 (up_open P).
  Hypothesis Hsc : ⊢ stub_law N (up_code P) 21 (up_close P).
  Hypothesis Hse : ⊢ exit_stub_law N (up_code P) (up_exit P).

  Local Notation γfd := (ukn_fd N).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* THE TAINT at the held descriptors: the flag and its two readings, the
     payload, the ledger and the handles *)
  Definition fh_taint (held : gset Z) : iProp Σ :=
    (T ∗ □ (T -∗ app_taint) ∗ □ (T -∗ app_sup) ∗ ukn_pay N (-1)
     ∗ ∃ (l : list fdstate) (hm : gmap Z fdstate),
         UserFd.ustd γfd l ∗ ⌜fh_held_ok held l hm⌝
         ∗ [∗ map] fd ↦ st ∈ hm, UserFd.ufd γfd (Z.to_nat fd) st)%I.

  (* a handle the kernel handed back is none the taint holds *)
  Lemma fh_hm_fresh (hm : gmap Z fdstate) (k : nat) (st : fdstate) :
    ([∗ map] fd ↦ st ∈ hm, UserFd.ufd γfd (Z.to_nat fd) st) -∗ UserFd.ufd γfd k st -∗
    ⌜hm !! Z.of_nat k = None⌝ ∗ ([∗ map] fd ↦ st ∈ hm, UserFd.ufd γfd (Z.to_nat fd) st)
    ∗ UserFd.ufd γfd k st.
  Proof using .
    iIntros "Hm Hh".
    destruct (hm !! Z.of_nat k) as [st' |] eqn:E; [| by iFrame].
    iDestruct (big_sepM_lookup_acc _ _ _ _ E with "Hm") as "[Hx _]".
    rewrite Nat2Z.id. iDestruct "Hx" as "[Hx _]". iDestruct "Hh" as "[Hh _]".
    iDestruct (ghost_map_elem_ne with "Hx Hh") as %Hne. by destruct Hne.
  Qed.

  (* the exit: the exit stub law, and the payload *)
  Lemma fh_exit_pay (s : Z) : ukn_pay N (-1) -∗ ex_obl N P s.
  Proof using HNc Hse.
    iIntros "Hpay" (h m avail) "_ Hcode Hrun".
    iPoseProof Hse as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "#Hi Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m).
    assert (Hnum : usysno m1 = USYS_exit).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 2 : mword 64)).
      vm_compute; reflexivity. }
    iApply (wp_uk_ecall_exit N h1 m1 (mword_of_int (up_exit P + 2)) avail Hnum
              with "Hi [Hpay] Hrun").
    by rewrite (ukn_const_eq (N := N) (uexitst m1) (-1)).
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  the four free leaves                                                *)
  (* ------------------------------------------------------------------- *)

  Lemma fh_t_write (held : gset Z) (fd : Z) (bs : list (bv 8)) (K : Z -> iProp Σ) :
    fh_taint held -∗ (∀ x, fh_taint held -∗ K x) -∗ wr_obl N P fd bs K.
  Proof using Hsw T_pers.
    iIntros "Ht HK" (h m avail ua tx dq f) "%Hf %Ha0 %Ha1 %Ha2 Hcode Hsrc Hrun Hcont".
    iAssert (T ∗ □ (T -∗ app_taint) ∗ □ (T -∗ app_sup))%I as "(#HT & #Hkc & #Hsc)".
    { iDestruct "Ht" as "(#HT & #Hkc & #Hsc & _)". iFrame "HT Hkc Hsc". }
    iPoseProof ("Hsc" with "HT") as "#Hsup".
    iPoseProof ("Hkc" with "HT") as "#Hk".
    iPoseProof (udepw_law_of_sup_write with "Hsup Hk") as "#Hlaw".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    assert (Hnum : usysno m1 = 16).
    { unfold m1, usysno. rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 16 : mword 64)).
      vm_compute; reflexivity. }
    iPoseProof Hsw as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Al6 #Hi Hrun Hret".
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int (up_write P + 2) : mword 64) 4))
                     2 = true) by (rewrite E6; exact Al6).
    iApply (wp_uk_ecall_quiet N h1 m1 (mword_of_int (up_write P + 2)) 16 avail Hnum
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(lia) ltac:(discriminate)
              Hal4 with "Hi Hrun [Hlaw]").
    { iApply (udepw_of_law with "Hlaw"). }
    iIntros (h2 ret) "Hrun". iEval (rewrite E6) in "Hrun".
    iApply ("Hret" $! h2 ret with "Hrun"). iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "[HK Ht] Hsrc Hrun").
    iApply ("HK" with "Ht").
  Qed.

  Lemma fh_t_read (held : gset Z) (fd : Z) (n : nat) (K : rd_ans -> iProp Σ) :
    fh_taint held -∗ (∀ x, fh_taint held -∗ K x) -∗ rd_obl N P fd n K.
  Proof using Hsr T_pers.
    iIntros "Ht HK" (h m avail a f) "%Ha0 %Ha1 %Ha2 Hcode Hbuf Hrun Hcont".
    iAssert (T ∗ □ (T -∗ app_taint) ∗ □ (T -∗ app_sup))%I as "(#HT & #Hkc & #Hsc)".
    { iDestruct "Ht" as "(#HT & #Hkc & #Hsc & _)". iFrame "HT Hkc Hsc". }
    iPoseProof ("Hsc" with "HT") as "#Hsup".
    iPoseProof ("Hkc" with "HT") as "#Hk".
    iPoseProof (udepw_law_of_sup_read with "Hsup Hk") as "#Hlaw".
    set (m1 := <[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m).
    assert (Hnum : usysno m1 = USYS_read).
    { unfold m1, usysno. rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 5 : mword 64)).
      vm_compute; reflexivity. }
    assert (Ha1r : m1 !!! Regidx (mword_of_int 11) = (mword_of_int a : mword 64)).
    { rewrite <- Ha1. exact (upd_ne m (Regidx a7_idx) (Regidx (mword_of_int 11)) _
                               ltac:(vm_compute; discriminate)). }
    assert (Hcnt : bv_signed (subrange_vec_dec (m1 !!! Regidx (mword_of_int 12)) 31 0
                              : mword 32) = Z.of_nat n).
    { unfold m1. rewrite (upd_ne m (Regidx a7_idx) (Regidx (mword_of_int 12)) _
                            ltac:(vm_compute; discriminate)).
      exact Ha2. }
    iPoseProof Hsr as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Al6 #Hi Hrun Hret".
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int (up_read P + 2) : mword 64) 4))
                     2 = true) by (rewrite E6; exact Al6).
    iApply (wp_uk_ecall_read N h1 m1 (mword_of_int (up_read P + 2)) a n f avail
              Hnum Ha1r Hcnt Hal4 with "Hi Hbuf Hrun [Hlaw]").
    { iApply (udepw_of_law with "Hlaw"). }
    iIntros (h2 ret gb) "%Hb Hbuf Hrun". iEval (rewrite E6) in "Hrun".
    iApply ("Hret" $! h2 ret with "Hrun"). iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret gb with "[%] [HK Ht] Hbuf Hrun"); [exact Hb |].
    iApply ("HK" with "Ht").
  Qed.

  Lemma fh_t_close (held : gset Z) (fd : Z) (K : Z -> iProp Σ) :
    fd ∈ held ->
    fh_taint held -∗ (∀ x, fh_taint (held ∖ {[fd]}) -∗ K x) -∗ cl_obl N P fd K.
  Proof using Hsc T_pers.
    intros Hin. iIntros "Ht HK" (h m avail) "%Ha0 Hcode Hrun Hcont".
    iDestruct "Ht" as "(#HT & #Hkc & #Hsc & Hpay & %l & %hm & Hstd & %Hok & Hhm)".
    iPoseProof ("Hkc" with "HT") as "#Hk".
    iPoseProof (udepw_law_of_sup_close with "Hk") as "#Hlaw".
    destruct (Hok fd Hin) as [[H0 Hlt] Hc].
    destruct (Z_of_nat_complete fd H0) as [k ->].
    set (m1 := <[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m).
    assert (Hnum : usysno m1 = USYS_close).
    { unfold m1, usysno. rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 21 : mword 64)).
      vm_compute; reflexivity. }
    assert (Ha0r : bv_signed (trunc32 (m1 !!! Regidx (mword_of_int 10))) = Z.of_nat k).
    { unfold m1. rewrite (upd_ne m (Regidx a7_idx) (Regidx (mword_of_int 10)) _
                            ltac:(vm_compute; discriminate)).
      exact Ha0. }
    iPoseProof Hsc as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Al6 #Hi Hrun Hret".
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int (up_close P + 2) : mword 64) 4))
                     2 = true) by (rewrite E6; exact Al6).
    destruct Hc as [(Hs & st & Hl & Hne) | (Hs & [st Hst])].
    - rewrite Nat2Z.id in Hl.
      iApply (wp_uk_ecall_close_std N h1 m1 (mword_of_int (up_close P + 2)) l k st avail
                Hnum Ha0r ltac:(unfold NSTD in *; lia) Hl Hne Hal4
                with "Hi Hrun [Hlaw] Hstd").
      { iApply udepw_cl_of_udepw. iApply (udepw_of_law with "Hlaw"). }
      iIntros (h2 ret) "_ Hstd Hrun". iEval (rewrite E6) in "Hrun".
      iApply ("Hret" $! h2 ret with "Hrun"). iIntros (h3) "Hrun".
      iApply ("Hcont" $! h3 ret with "[-Hrun] Hrun").
      iApply "HK". rewrite /fh_taint. iFrame "HT Hkc Hsc Hpay".
      iExists (<[k := FdClosed]> l), hm. iFrame "Hstd Hhm". iPureIntro.
      intros x Hx. apply elem_of_difference in Hx as [Hx Hnx].
      destruct (Hok x Hx) as [Hb Hc]. split; [exact Hb |].
      destruct Hc as [(Hs' & st' & Hl' & Hne') | Hc]; [left | by right].
      split; [exact Hs' |]. exists st'. split; [| exact Hne'].
      rewrite list_lookup_insert_ne; [exact Hl' |].
      intros Heq0. apply Hnx. apply elem_of_singleton. lia.
    - iDestruct (big_sepM_delete _ _ _ _ Hst with "Hhm") as "[Hh Hhm]".
      rewrite Nat2Z.id.
      iApply (wp_uk_ecall_close N h1 m1 (mword_of_int (up_close P + 2)) k st avail
                Hnum Ha0r Hal4 with "Hi Hrun [Hlaw] Hh").
      { iApply udepw_cl_of_udepw. iApply (udepw_of_law with "Hlaw"). }
      iIntros (h2 ret) "_ Hrun". iEval (rewrite E6) in "Hrun".
      iApply ("Hret" $! h2 ret with "Hrun"). iIntros (h3) "Hrun".
      iApply ("Hcont" $! h3 ret with "[-Hrun] Hrun").
      iApply "HK". rewrite /fh_taint. iFrame "HT Hkc Hsc Hpay".
      iExists l, (delete (Z.of_nat k) hm). iFrame "Hstd Hhm". iPureIntro.
      intros x Hx. apply elem_of_difference in Hx as [Hx Hnx].
      destruct (Hok x Hx) as [Hb Hc]. split; [exact Hb |].
      destruct Hc as [Hc | (Hs' & Hsm)]; [by left | right]. split; [exact Hs' |].
      rewrite lookup_delete_ne; [exact Hsm |].
      intros Heq0. apply Hnx. apply elem_of_singleton. done.
  Qed.

  Lemma fh_t_open (held : gset Z) (p : list (bv 8)) (mo : Z) (K : Z -> iProp Σ) :
    fh_taint held -∗
    (∀ x, ((⌜x = -1⌝ ∗ fh_taint held) ∨ (⌜0 <= x⌝ ∗ fh_taint ({[x]} ∪ held))) -∗ K x) -∗
    op_obl N P p mo K.
  Proof using Hso T_pers.
    iIntros "Ht HK" (h m avail pv tx f) "%Hf %Ha0 %Ha1 Hcode Hp Hrun Hcont".
    iDestruct "Ht" as "(#HT & #Hkc & #Hsc & Hpay & %l & %hm & Hstd & %Hok & Hhm)".
    iPoseProof ("Hsc" with "HT") as "#Hsup".
    iPoseProof (udepw_law_of_sup 15 ltac:(by left) with "Hsup") as "#Hlaw".
    iAssert (⌜length l = NSTD⌝ ∗ UserFd.ustd γfd l)%I with "[Hstd]" as "[%Hlen Hstd]".
    { rewrite /UserFd.ustd. iDestruct "Hstd" as "[%H $]". done. }
    set (m1 := <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m).
    assert (Hnum : usysno m1 = USYS_open).
    { unfold m1, usysno. rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 15 : mword 64)).
      vm_compute; reflexivity. }
    iPoseProof Hso as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Al6 #Hi Hrun Hret".
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int (up_open P + 2) : mword 64) 4))
                     2 = true) by (rewrite E6; exact Al6).
    iApply (wp_uk_ecall_open N h1 m1 (mword_of_int (up_open P + 2)) l avail Hnum Hal4
              with "Hi Hrun [Hlaw] Hstd").
    { iApply (udepw_of_law with "Hlaw"). }
    iIntros (h2 ret) "Hans Hrun". iEval (rewrite E6) in "Hrun".
    iApply ("Hret" $! h2 ret with "Hrun"). iIntros (h3) "Hrun".
    iDestruct "Hans" as "[Hal | [%Hr Hstd]]".
    - iDestruct "Hal" as (fd rd wr t) "[%Hb Hal]". destruct Hb as (Hr & Hfdlt & _).
      assert (Hsig : bv_signed ret = Z.of_nat fd).
      { rewrite Hr. apply bvs_moi_small. unfold NOFILE in Hfdlt.
        assert (E : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity). lia. }
      iApply ("Hcont" $! h3 ret with "[%] [-Hp Hrun] Hp Hrun").
      { right. split; [rewrite Hsig; unfold NOFILE in *; lia | rewrite Hsig; exact Hr]. }
      rewrite Hsig. iApply "HK". iRight. iSplit; [iPureIntro; lia |].
      rewrite /fh_taint. iFrame "HT Hkc Hsc Hpay".
      rewrite /ualloc /ualloc_at /ustd_after.
      iDestruct "Hal" as "[Hstd Hat]".
      destruct (fd_lowest_closed l) as [k0 |] eqn:Elc.
      + iDestruct "Hat" as %->.
        pose proof (fd_lowest_closed_is_closed l k0 Elc) as Hk0.
        assert (Hk0l : (k0 < NSTD)%nat)
          by (rewrite <- Hlen; exact (lookup_lt_Some _ _ _ Hk0)).
        iExists (<[k0 := FdOpen rd wr t]> l), hm. iFrame "Hstd Hhm". iPureIntro.
        intros x Hx. apply elem_of_union in Hx as [Hx | Hx].
        * apply elem_of_singleton in Hx as ->. split; [unfold NSTD, NOFILE in *; lia |].
          left. split; [unfold NSTD in *; lia |]. exists (FdOpen rd wr t).
          rewrite Nat2Z.id list_lookup_insert; [split; [done | discriminate] |].
          rewrite <- Hlen in Hk0l. rewrite Hlen. unfold NSTD in *; lia.
        * destruct (Hok x Hx) as [Hb Hc]. split; [exact Hb |].
          destruct Hc as [(Hs' & st' & Hl' & Hne') | Hc]; [left | by right].
          split; [exact Hs' |].
          destruct (decide (Z.to_nat x = k0)) as [-> | Hne].
          -- exists (FdOpen rd wr t). rewrite list_lookup_insert; [split; [done | discriminate] |].
             exact (lookup_lt_Some _ _ _ Hk0).
          -- exists st'. rewrite list_lookup_insert_ne; [split; [exact Hl' | exact Hne'] |].
             congruence.
      + iDestruct "Hat" as "[%Hhi Hh]".
        iDestruct (fh_hm_fresh with "Hhm Hh") as "(%Hfr & Hhm & Hh)".
        iExists l, (<[Z.of_nat fd := FdOpen rd wr t]> hm). iFrame "Hstd". iSplit.
        * iPureIntro. intros x Hx. apply elem_of_union in Hx as [Hx | Hx].
          -- apply elem_of_singleton in Hx as ->. split; [unfold NOFILE in *; lia |].
             right. split; [lia |]. rewrite lookup_insert. by eexists.
          -- destruct (Hok x Hx) as [Hb Hc]. split; [exact Hb |].
             destruct Hc as [Hc | (Hs' & Hsm)]; [by left | right]. split; [exact Hs' |].
             destruct (decide (x = Z.of_nat fd)) as [-> |];
               [rewrite lookup_insert; by eexists | rewrite lookup_insert_ne; [exact Hsm | congruence]].
        * rewrite big_sepM_insert; [| exact Hfr]. rewrite Nat2Z.id. iFrame "Hh Hhm".
    - iApply ("Hcont" $! h3 ret with "[%] [-Hp Hrun] Hp Hrun").
      { left. rewrite Hr. exact fh_m1. }
      rewrite Hr fh_m1. iApply "HK". iLeft. iSplit; [done |].
      rewrite /fh_taint. iFrame "HT Hkc Hsc Hpay". iExists l, hm. by iFrame.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  ...and by coinduction, the whole tree                               *)
  (* ------------------------------------------------------------------- *)
  Definition fh_tinv (t : proc) : iProp Σ :=
    (∃ held : gset Z, ⌜safe_fds held t⌝ ∗ fh_taint held)%I.

  Lemma fh_taint_pays (held : gset Z) (t : proc) :
    safe_fds held t -> fh_taint held -∗ tree_pay N P t.
  Proof using HNc Hsr Hsw Hso Hsc Hse T_pers.
    intros Hs. iIntros "Ht".
    iApply (tree_pay_coind N P fh_tinv with "[] [Ht]"); last first.
    { iExists held. by iFrame. }
    iIntros "!>" (t') "(%hd & %Hs' & Ht)".
    apply safe_fds_unfold in Hs'.
    destruct t' as [v | t'' | e k]; [destruct v | |].
    - simpl in Hs' |- *. iExists hd. by iFrame.
    - destruct e as [p mo | fd | fd n | fd bs | s]; simpl in Hs' |- *.
      + destruct Hs' as [Hso' Hsm].
        iApply (fh_t_open hd p mo with "Ht").
        iIntros (x) "[[-> Ht] | [%Hx Ht]]".
        * iExists hd. by iFrame.
        * iExists ({[x]} ∪ hd). iFrame "Ht". iPureIntro. by apply Hso'.
      + destruct Hs' as [Hin Hk].
        iApply (fh_t_close hd fd with "Ht"); [exact Hin |].
        iIntros (x) "Ht". iExists (hd ∖ {[fd]}). iFrame "Ht". iPureIntro. apply Hk.
      + destruct Hs' as [_ Hk].
        iApply (fh_t_read hd fd n with "Ht").
        iIntros (x) "Ht". iExists hd. iFrame "Ht". iPureIntro. apply Hk.
      + iApply (fh_t_write hd fd bs with "Ht").
        iIntros (x) "Ht". iExists hd. iFrame "Ht". iPureIntro. apply Hs'.
      + iDestruct "Ht" as "(_ & _ & _ & Hpay & _)". iApply (fh_exit_pay with "Hpay").
  Qed.

End UkFreeHandler.
