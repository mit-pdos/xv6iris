(* ===================================================================== *)
(* UexecSecc.v -- THE UNIVERSE: the generic per-process slot for an      *)
(* ARBITRARY binary running under a syscall mask, built WITHOUT the      *)
(* application's taint (design/seccomp.md SS5 as amended by SS9).        *)
(*                                                                       *)
(* A key is IN THE UNIVERSE when its mask clears the six namespace-      *)
(* writing numbers [secc_B] and every row of its table is one the        *)
(* universe can pay for without the taint: no inode row (without open   *)
(* none can arrive), a pipe row only at a pipe whose queue fragment is   *)
(* parked with NO protocol ([wild_pipe]), and console / closed rows for  *)
(* free.  [secc_key] is that, persistent; every syscall row preserves it *)
(* (SS2 below), and every deposit a key in the universe owes is paid out *)
(* of it (SS3) -- except the console, which the era credential pays.     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import Xv6Cameras.
Require Import IrefSlots.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UexecSlot.
Require Import UexecWp.
Require Import UexecRet.
Require Import UexecExecInst.   (* the class INSTANCE [uexecSG_xv6]: [xv6_sbundle] *)
Require Import FsAbsInvFire.    (* [fsabs_chdir_pre] / [fsabs_exec_half] *)
Require Import FsAbsEra.        (* [ex_start] / [ax_hops_triv] *)
Require Import SpecFileread.    (* [fileread_in] *)
Require Import SpecFilewrite.   (* [filewrite_in] *)
Require Import SpecFileclose.   (* [fileclose_cpay] / [fileclose_cpays] *)
Require Import SpecKexec.       (* [kexec_image_ok] / [exec_key_ok] / [exec_slot_pre] *)
Require Import SpecSysExec.     (* [sys_exec_au_pre] *)
Require Import PipeNames.       (* [pipe_names] / [pn_queue] *)
Require Import PipeQueue.       (* [pipe_qfrag] and the links *)
Require Import PipeReg.         (* [pipe_reg] / [pipe_row_reg] *)
Require Import UsysMemOk.
Require Import UserPerm.
Require Import ChildTok.
Require Import ExecEntry.       (* [image_entry_taint] *)
Require Import PieceFam.        (* [pfam_triv] *)
Require Import Xv6G.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

Require Import UexecSG.

(* ===================================================================== *)
(*  1.  PURE: the blocked set and the mask condition                      *)
(* ===================================================================== *)

(* kill, open, mknod, unlink, link, mkdir: the numbers a masked process
   must not reach (design SS1) *)
Definition secc_B : list Z := [6; 15; 17; 18; 19; 20].

Definition secc_masked (m : mword 64) : Prop :=
  forall n, n ∈ secc_B -> Z.testbit (bv_unsigned m) n = false.

(* the six numbers, spelled out: what a [decide] chain wants *)
Lemma secc_notin_cases (n : Z) :
  n ∉ secc_B ->
  n <> 6 /\ n <> 15 /\ n <> 17 /\ n <> 18 /\ n <> 19 /\ n <> 20.
Proof.
  intros H.
  split_and!; intros ->; apply H; rewrite elem_of_list_In; cbn; tauto.
Qed.

(* a blocked number IS the unknown-number call *)
Lemma usys_eff_masked (m : mword 64) (tf : list (mword 64)) :
  secc_masked m -> usys_num tf ∈ secc_B -> usys_eff m tf = 0.
Proof.
  intros Hm Hin. apply usys_eff_blocked. exact (Hm _ Hin).
Qed.

(* ...so the EFFECTIVE number of a masked frame is never one of the six *)
Lemma usys_eff_masked_notin (m : mword 64) (tf : list (mword 64)) :
  secc_masked m -> usys_eff m tf ∉ secc_B.
Proof.
  intros Hm. unfold usys_eff.
  destruct (Z.testbit (bv_unsigned m) (usys_num tf)) eqn:Hb.
  - intros Hin. rewrite (Hm _ Hin) in Hb. discriminate Hb.
  - rewrite elem_of_list_In. cbn. lia.
Qed.

Lemma uvis_num_masked (W : uvis) :
  secc_masked (uvis_secc W) -> uvis_num W ∉ secc_B.
Proof. intros Hm. exact (usys_eff_masked_notin _ _ Hm). Qed.

(* sys_seccomp ANDs the mask, so a masked mask stays masked *)
Lemma secc_masked_and (m x : mword 64) :
  secc_masked m -> secc_masked (and_vec m x).
Proof.
  intros Hm n Hn. rewrite and_vec64_unsigned Z.land_spec (Hm n Hn).
  reflexivity.
Qed.

(* ...along the mask row, at every number *)
Lemma secc_masked_secc_ok (n : Z) (tf : list (mword 64)) (m m' r : mword 64) :
  secc_masked m -> usys_secc_ok n tf m m' r -> secc_masked m'.
Proof.
  intros Hm H. unfold usys_secc_ok in H.
  destruct (decide (n = USYS_seccomp)) as [_ | _].
  - destruct H as [-> _]. exact (secc_masked_and m _ Hm).
  - subst m'. exact Hm.
Qed.

Section UexecSecc.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId}.

  (* =================================================================== *)
  (*  2.  THE KEY                                                        *)
  (* =================================================================== *)

  Definition seccN : namespace := nroot .@ "secc".

  (* THE WILD PIPE: the queue fragment parked with NO protocol.  Every
     link the universe owes on it opens this, lends the fragment and puts
     it back moved (SS3). *)
  Definition wild_pipe (γp : pipe_names) : iProp Σ :=
    inv seccN (∃ s : pipe_st, pipe_qfrag (pn_queue γp) s).

  Global Instance wild_pipe_persistent γp : Persistent (wild_pipe γp).
  Proof using . rewrite /wild_pipe. apply _. Qed.

  Definition secc_row (st : fdstate) : iProp Σ :=
    (match st with
     | FdOpen _ _ (FdInode _ _ _) => False
     | FdOpen _ _ (FdPipe γp) => wild_pipe γp
     | _ => True
     end)%I.

  Global Instance secc_row_persistent st : Persistent (secc_row st).
  Proof using . rewrite /secc_row. destruct st as [| ? ? [| |]]; apply _. Qed.

  Definition secc_rows (sts : list fdstate) : iProp Σ :=
    ([∗ list] st ∈ sts, secc_row st)%I.

  Global Instance secc_rows_persistent sts : Persistent (secc_rows sts).
  Proof using . rewrite /secc_rows. apply _. Qed.

  (* NOT TIMELESS, and it cannot be: [wild_pipe] is an invariant. *)
  Definition secc_key (W : uvis) : iProp Σ :=
    (⌜secc_masked (uvis_secc W)⌝ ∗ secc_rows (uvis_fd W))%I.

  Global Instance secc_key_persistent W : Persistent (secc_key W).
  Proof using . rewrite /secc_key. apply _. Qed.

  (* the key reads two components and no others *)
  Lemma secc_key_cong (W W' : uvis) :
    uvis_fd W' = uvis_fd W -> uvis_secc W' = uvis_secc W ->
    secc_key W -∗ secc_key W'.
  Proof using . intros Hf Hs. rewrite /secc_key Hf Hs. auto. Qed.

  (* ---- the rows, one at a time ---- *)

  Lemma secc_rows_lookup (sts : list fdstate) (i : nat) :
    secc_rows sts -∗ secc_row (sts !!! i).
  Proof using .
    iIntros "#H". destruct (sts !! i) as [st |] eqn:Hi.
    - rewrite (list_lookup_total_correct _ _ _ Hi).
      iApply (big_sepL_lookup with "H"). exact Hi.
    - rewrite (list_lookup_total_alt sts i) Hi /=. done.
  Qed.

  (* THE ROW THE SYSCALL'S ARGUMENT NAMES *)
  Lemma secc_rows_at_key (v : mword 64) (sts : list fdstate) :
    secc_rows sts -∗ secc_row (fd_st_of_key v sts).
  Proof using .
    iIntros "#H". rewrite /fd_st_of_key.
    destruct (decide _) as [_ | _]; [ | done ].
    destruct (sts !! _) as [st |] eqn:Hi; cbn [default]; [ | done ].
    iApply (big_sepL_lookup with "H"). exact Hi.
  Qed.

  Lemma secc_key_at_arg (W : uvis) (v : mword 64) :
    secc_key W -∗ secc_row (fd_st_of_key v (uvis_fd W)).
  Proof using .
    iIntros "[_ #H]". iApply (secc_rows_at_key with "H").
  Qed.

  Lemma secc_rows_insert (sts : list fdstate) (i : nat) (st : fdstate) :
    secc_rows sts -∗ secc_row st -∗ secc_rows (<[i := st]> sts).
  Proof using .
    iIntros "#H #Hs". rewrite /secc_rows.
    destruct (sts !! i) as [st0 |] eqn:Hi.
    - iDestruct (big_sepL_insert_acc with "H") as "[_ Hk]"; [ exact Hi | ].
      iApply ("Hk" with "Hs").
    - rewrite list_insert_ge; [ iExact "H" | ].
      exact (proj1 (lookup_ge_None _ _) Hi).
  Qed.

  (* ---- 2a. preservation along the descriptor row ---- *)

  (* every number but open and pipe: close clears a row, dup copies one,
     the rest keep the table *)
  Lemma secc_rows_fd_ok (n : Z) (tf : list (mword 64)) (r : mword 64)
      (sts sts' : list fdstate) :
    n <> USYS_open -> n <> USYS_pipe ->
    usys_fd_ok n tf r sts sts' ->
    secc_rows sts -∗ secc_rows sts'.
  Proof using .
    intros Ho Hp H. iIntros "#Hr". unfold usys_fd_ok in H.
    destruct (decide (n = USYS_close)) as [_ | _].
    { destruct H as [H _]. destruct (decide (uint r = 0)) as [_ | _]; subst sts';
        [ iApply (secc_rows_insert with "Hr"); done | iExact "Hr" ]. }
    destruct (decide (n = USYS_dup)) as [_ | _].
    { destruct H as [(fd1 & _ & _ & _ & ->) | (_ & -> & _)]; [ | iExact "Hr" ].
      iApply (secc_rows_insert with "Hr").
      iApply (secc_rows_lookup with "Hr"). }
    destruct (decide (n = USYS_open)) as [He | _]; [ exfalso; exact (Ho He) | ].
    destruct (decide (n = USYS_pipe)) as [He | _]; [ exfalso; exact (Hp He) | ].
    subst sts'. iExact "Hr".
  Qed.

  (* pipe: two rows at the NEW name, given that name's wild pipe *)
  Lemma secc_rows_pipe (sts : list fdstate) (a b : nat) (γp : pipe_names) :
    wild_pipe γp -∗ secc_rows sts -∗
    secc_rows (<[b := FdOpen false true (FdPipe γp)]>
                 (<[a := FdOpen true false (FdPipe γp)]> sts)).
  Proof using .
    iIntros "#Hw #Hr".
    iApply (secc_rows_insert _ b (FdOpen false true (FdPipe γp)) with "[] Hw").
    iApply (secc_rows_insert _ a (FdOpen true false (FdPipe γp)) with "Hr Hw").
  Qed.

  (* ...and a pipe that failed moved nothing *)
  Lemma usys_fd_ok_pipe_fail (tf : list (mword 64)) (r : mword 64)
      (sts sts' : list fdstate) :
    uint r <> 0 -> usys_fd_ok USYS_pipe tf r sts sts' -> sts' = sts.
  Proof using .
    intros Hr H. unfold usys_fd_ok in H.
    destruct (decide (USYS_pipe = USYS_close)) as [He | _]; [ discriminate He | ].
    destruct (decide (USYS_pipe = USYS_dup)) as [He | _]; [ discriminate He | ].
    destruct (decide (USYS_pipe = USYS_open)) as [He | _]; [ discriminate He | ].
    destruct (decide (USYS_pipe = USYS_pipe)) as [_ | Hc]; [ | contradiction (Hc eq_refl) ].
    destruct (decide (uint r = 0)) as [He | _]; [ contradiction (Hr He) | ].
    exact (proj2 H).
  Qed.

  (* ---- 2b. the key at the fork child's and the exec'd image's keys ---- *)

  (* fork: the child's key is [bump_at] at the parent's table and mask *)
  Lemma secc_key_fork_child (W : uvis) (r : mword 64) (M' : gmap Z (bv 8))
      (π' : gmap (mword 27) uperm) (szv' : Z) (cw' : Z) (g' : gname)
      (cs' : gset gname) (pid' : mword 32) (lz' : bool) :
    secc_key W -∗
    secc_key (bump_at W r M' π' szv' (uvis_fd W) cw' g' cs' pid' lz' (uvis_secc W)).
  Proof using . apply secc_key_cong; reflexivity. Qed.

  (* exec, arm (a): [kexec_image_ok] pins the table, [exec_slot_pre] the mask *)
  Lemma secc_key_exec_image (W W' : uvis) (f : ElfFile.elf_bytes) (na : nat)
      (alen : nat -> nat) (afun : nat -> nat -> bv 8) :
    kexec_image_ok f na alen afun (uvis_fd W) W' ->
    uvis_secc W' = uvis_secc W ->
    secc_key W -∗ secc_key W'.
  Proof using .
    intros Hok Hs. apply secc_key_cong; [ exact (kexec_image_ok_fd _ _ _ _ _ _ Hok) | exact Hs ].
  Qed.

  (* ...arm (b), the non-loadable resume *)
  Lemma secc_key_exec_key (W W' : uvis) (na : nat) (alen : nat -> nat) :
    exec_key_ok na alen (uvis_fd W) W' ->
    uvis_secc W' = uvis_secc W ->
    secc_key W -∗ secc_key W'.
  Proof using .
    intros Hok Hs. apply secc_key_cong; [ exact (exec_key_ok_fd _ _ _ _ Hok) | exact Hs ].
  Qed.

  (* ...and at the generalised taint entry's own two pins *)
  Lemma secc_key_of_pins (W' : uvis) (sts : list fdstate) (secc : mword 64) :
    uvis_fd W' = sts -> uvis_secc W' = secc ->
    secc_rows sts -∗ ⌜secc_masked secc⌝ -∗ secc_key W'.
  Proof using .
    intros Hf Hs. iIntros "#Hr %Hm". rewrite /secc_key Hf Hs.
    iSplit; [ done | iExact "Hr" ].
  Qed.

  (* =================================================================== *)
  (*  3.  THE LINKS OUT OF A WILD PIPE, at the trivial protocol          *)
  (* =================================================================== *)

  (* [PipeProto.pipe_clink_of_inv]'s mould, with no protocol to keep *)
  Lemma wild_clink (γp : pipe_names) (w : bool) :
    wild_pipe γp -∗ pipe_clink (pn_queue γp) w emp.
  Proof using .
    iIntros "#Hinv". rewrite /pipe_clink /wild_pipe. iIntros (s) "Ha".
    iInv "Hinv" as (s0) ">Hf" "Hclose".
    iDestruct (pipe_queue_agree with "Ha Hf") as %<-.
    iMod (pipe_queue_update _ _ _ (pst_close w s0) with "Ha Hf") as "[Ha Hf]".
    iMod ("Hclose" with "[Hf]") as "_"; [ iNext; iExists _; iExact "Hf" | ].
    iModIntro. iFrame "Ha".
  Qed.

  (* ...which IS the registration *)
  Lemma wild_reg (γp : pipe_names) : wild_pipe γp -∗ pipe_reg γp.
  Proof using .
    iIntros "#Hw". rewrite /pipe_reg. iIntros "!>" (w).
    rewrite /pipe_cpay. iLeft. iApply (wild_clink with "Hw").
  Qed.

  Lemma secc_row_reg (st : fdstate) : secc_row st -∗ pipe_row_reg st.
  Proof using .
    rewrite /secc_row /pipe_row_reg.
    destruct st as [| ? ? [| γp |]]; try (by iIntros "_").
    iIntros "#Hw". iApply (wild_reg with "Hw").
  Qed.

  Lemma secc_rows_regs (sts : list fdstate) :
    secc_rows sts -∗ [∗ list] st ∈ sts, pipe_row_reg st.
  Proof using .
    rewrite /secc_rows. iIntros "#H". iApply (big_sepL_impl with "H").
    iIntros "!>" (k st _) "#Hs". iApply (secc_row_reg with "Hs").
  Qed.

  Lemma wild_rlink (γp : pipe_names) (Φ : bv 8 -> iProp Σ) :
    wild_pipe γp -∗ □ (∀ b, Φ b) -∗ pipe_rlink (pn_queue γp) Φ.
  Proof using .
    iIntros "#Hinv #HΦ". rewrite /pipe_rlink /wild_pipe. iIntros (s b) "_ %Hb Ha".
    iInv "Hinv" as (s0) ">Hf" "Hclose".
    iDestruct (pipe_queue_agree with "Ha Hf") as %<-.
    iMod (pipe_queue_update _ _ _ (pst_read s0) with "Ha Hf") as "[Ha Hf]".
    iMod ("Hclose" with "[Hf]") as "_"; [ iNext; iExists _; iExact "Hf" | ].
    iModIntro. iFrame "Ha". iApply "HΦ".
  Qed.

  Lemma wild_wlink (γp : pipe_names) (b : bv 8) (Φ : iProp Σ) :
    wild_pipe γp -∗ □ Φ -∗ pipe_wlink (pn_queue γp) b Φ.
  Proof using .
    iIntros "#Hinv #HΦ". rewrite /pipe_wlink /wild_pipe. iIntros (s) "_ _ Ha".
    iInv "Hinv" as (s0) ">Hf" "Hclose".
    iDestruct (pipe_queue_agree with "Ha Hf") as %<-.
    iMod (pipe_queue_update _ _ _ (pst_write b s0) with "Ha Hf") as "[Ha Hf]".
    iMod ("Hclose" with "[Hf]") as "_"; [ iNext; iExists _; iExact "Hf" | ].
    iModIntro. iFrame "Ha". iExact "HΦ".
  Qed.

  (* an observation at a trivial payload moves nothing and needs nothing *)
  Lemma triv_rolink (γ : gname) : ⊢ pipe_rolink γ (fun _ => True%I).
  Proof using . rewrite /pipe_rolink. iIntros (s) "_ Ha". iModIntro. iFrame "Ha". Qed.

  Lemma triv_wolink (γ : gname) : ⊢ pipe_wolink γ (fun _ => True%I).
  Proof using . rewrite /pipe_wolink. iIntros (s) "_ Ha". iModIntro. iFrame "Ha". Qed.

  (* THE READ CHAIN at the trivial cursor and observation, at any count *)
  Lemma wild_rchain (γp : pipe_names) (acc : list (bv 8)) (cnt : nat) :
    wild_pipe γp -∗
    pipe_rchain (pn_queue γp) (fun _ => True%I) (fun _ _ => True%I) acc cnt.
  Proof using .
    iIntros "#Hw". iInduction cnt as [| cnt] "IH" forall (acc); cbn [pipe_rchain];
      [ done | ].
    iSplit; [ done | iSplit; [ iApply triv_rolink | ] ].
    iApply (wild_rlink with "Hw"). iIntros "!>" (b). iApply "IH".
  Qed.

  (* THE WRITE CHAIN, likewise *)
  Lemma wild_wchain (γp : pipe_names) (M : gmap Z (bv 8)) (ua : mword 64)
      (j cnt : nat) :
    wild_pipe γp -∗
    pipe_wchain (pn_queue γp) M ua (fun _ => True%I) (fun _ _ => True%I) j cnt.
  Proof using .
    iIntros "#Hw". iInduction cnt as [| cnt] "IH" forall (j); cbn [pipe_wchain];
      [ done | ].
    iSplit; [ done | iSplit; [ iApply triv_wolink | ] ].
    iIntros (b) "_". iApply (wild_wlink with "Hw"). iModIntro. iApply "IH".
  Qed.

  (* ---- the deposit rows the universe pays out of them ---- *)

  (* read's row at a pipe descriptor *)
  Lemma wild_fileread_in (γp : pipe_names) (rb wb : bool) (n : Z) (P : iProp Σ) :
    wild_pipe γp -∗
    fileread_in (FdOpen rb wb (FdPipe γp)) n (pfam_triv (fun _ _ _ _ => True%I))
      (fun _ _ => True%I) (fun _ => True%I) (fun _ => True%I) (fun _ _ => True%I) P.
  Proof using .
    iIntros "#Hw". rewrite /fileread_in. iIntros "HP".
    destruct rb; [ | iExact "HP" ].
    iFrame "HP". rewrite /pipe_rpay. iLeft. iApply (wild_rchain with "Hw").
  Qed.

  (* write's row at a pipe descriptor *)
  Lemma wild_filewrite_in (γp : pipe_names) (rb wb : bool) (n : Z)
      (pmv : gmap (mword 27) uperm) (sz : Z) (lz : bool)
      (M : gmap Z (bv 8)) (ua : mword 64) :
    wild_pipe γp -∗
    filewrite_in pmv sz lz (FdOpen rb wb (FdPipe γp)) n M ua
      (fun _ => True%I) (fun _ _ => True%I).
  Proof using .
    iIntros "#Hw". rewrite /filewrite_in.
    destruct wb; [ | done ].
    rewrite /pipe_wpay. iLeft. iApply (wild_wchain with "Hw").
  Qed.

  (* close's row at ANY row of the universe *)
  Lemma secc_fileclose_cpay (st : fdstate) :
    secc_row st -∗ fileclose_cpay st True.
  Proof using .
    iIntros "#Hs". iApply fileclose_cpay_of_reg_true.
    iApply (secc_row_reg with "Hs").
  Qed.

  (* ...and exit's, every row of the table *)
  Lemma secc_fileclose_cpays (sts : list fdstate) :
    secc_rows sts -∗ fileclose_cpays sts.
  Proof using .
    iIntros "#H". iApply fileclose_cpays_of_regs. iApply (secc_rows_regs with "H").
  Qed.

  (* ...at the key, at the row the argument names *)
  Lemma secc_key_close_cpay (W : uvis) (v : mword 64) :
    secc_key W -∗ fileclose_cpay (fd_st_of_key v (uvis_fd W)) True.
  Proof using .
    iIntros "#Hk". iApply secc_fileclose_cpay. iApply (secc_key_at_arg with "Hk").
  Qed.

  (* EXIT'S BUNDLE ROW at a key in the universe: the table's close
     payments, out of the rows' registrations *)
  Lemma secc_sbundle_exit (X : uvis -d> iPropO Σ) (W : uvis) (Q : Z -> iProp Σ) :
    secc_key W -∗
    |==> ∃ f : xfam, ⌜kf_xpay f = Q⌝ ∗ xv6_sbundle X USYS_exit f W.
  Proof using .
    iIntros "[_ #Hr]". iApply (xv6_sbundle_exit_regs X W Q).
    iApply (secc_rows_regs with "Hr").
  Qed.

End UexecSecc.
