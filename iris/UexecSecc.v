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
Require FsAbsEra.               (* [ex_start] / [ax_hops_triv] *)
Require Import SpecSysRead.     (* [sys_rw_count] *)
Require Import SpecSysChdir.    (* [chdir_au_pre] *)
Require Import WpUart.
Require Import AppInv.
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
Require Import UserExec UserPtTree RegFile.
Require Import UmodeRegs.       (* [uv_regs_u_regs] *)
Require Import UmodeText.       (* [user_ptm_inv_x_pt] *)
Require Import ConsoleInv.      (* [CONSOLE] *)
Require Import ChildTok.
Require Import ExecEntry.       (* [image_entry_taint] *)
Require Import PieceFam.        (* [pfam_triv] *)
Require Import FsAbsDefs.       (* LAST (FsAbs's own rule) *)
Require Import FsBytesGamma.    (* [fs_gamma_L] *)
Require Import ProcAvail.       (* [pavG] *)
Require Import Xv6G.
Require Import FsCfg.
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

  (* =================================================================== *)
  (*  4.  THE CONSOLE ROWS, AS ONE PAYER                                 *)
  (*                                                                     *)
  (*  The only rows the universe cannot pay out of its key: a read or a  *)
  (*  write at the console moves the application's console history, and  *)
  (*  what pays for that is the era credential (SS5 below).  Named, so    *)
  (*  the minter is stated over the payer and the credential enters once. *)
  (* =================================================================== *)
  Definition secc_cons_pay : iProp Σ :=
    (□ ((∀ (wb : bool) (mj n : Z) (P : iProp Σ),
           fileread_in (FdOpen true wb (FdDevice mj)) n
             (pfam_triv (fun _ _ _ _ => True%I)) (fun _ _ => True%I)
             (fun _ => True%I) (fun _ => True%I) (fun _ _ => True%I) P)
        ∧ (∀ (rb : bool) (mj n : Z) (pmv : gmap (mword 27) uperm) (sz : Z)
             (lz : bool) (M : gmap Z (bv 8)) (ua : mword 64),
             filewrite_in pmv sz lz (FdOpen rb true (FdDevice mj)) n M ua
               (fun _ => True%I) (fun _ _ => True%I))))%I.

  Global Instance secc_cons_pay_persistent : Persistent secc_cons_pay.
  Proof using . rewrite /secc_cons_pay. apply _. Qed.

  (* READ'S ROW at any row of the universe *)
  Lemma secc_fileread_in (st : fdstate) (n : Z) (P : iProp Σ) :
    secc_cons_pay -∗ secc_row st -∗
    fileread_in st n (pfam_triv (fun _ _ _ _ => True%I)) (fun _ _ => True%I)
      (fun _ => True%I) (fun _ => True%I) (fun _ _ => True%I) P.
  Proof using .
    iIntros "#Hc #Hs".
    destruct st as [| rb wb [i γo om | γp | mj]].
    - rewrite /fileread_in. iIntros "HP". iExact "HP".
    - rewrite /secc_row. iDestruct "Hs" as "[]".
    - iApply (wild_fileread_in with "Hs").
    - destruct rb; [ | rewrite /fileread_in; iIntros "HP"; iExact "HP" ].
      iDestruct "Hc" as "[Hr _]". iApply "Hr".
  Qed.

  (* WRITE'S ROW, likewise *)
  Lemma secc_filewrite_in (st : fdstate) (n : Z)
      (pmv : gmap (mword 27) uperm) (sz : Z) (lz : bool)
      (M : gmap Z (bv 8)) (ua : mword 64) :
    secc_cons_pay -∗ secc_row st -∗
    filewrite_in pmv sz lz st n M ua (fun _ => True%I) (fun _ _ => True%I).
  Proof using .
    iIntros "#Hc #Hs".
    destruct st as [| rb wb [i γo om | γp | mj]].
    - rewrite /filewrite_in. done.
    - rewrite /secc_row. iDestruct "Hs" as "[]".
    - iApply (wild_filewrite_in with "Hs").
    - destruct wb; [ | rewrite /filewrite_in; done ].
      iDestruct "Hc" as "[_ Hw]". iApply "Hw".
  Qed.

  (* =================================================================== *)
  (*  5.  THE BUNDLE AT EVERY NUMBER A MASKED KEY CAN REACH              *)
  (* =================================================================== *)

  (* THE UNIVERSE'S FAMILIES: the point, at the trivial payload.  Every
     receipt, cursor and refund is [True]; the child's payload is too, and
     the lend is [emp]. *)
  Definition secc_fam := xfam_at (Σ := Σ) (fun _ : Z => True%I) xfam_pt.

  Lemma secc_fam_xpay : sexit_pay secc_fam = (fun _ => True%I).
  Proof using . reflexivity. Qed.
  Lemma secc_fam_fpay : sfork_pay secc_fam = (fun _ => True%I).
  Proof using . reflexivity. Qed.
  Lemma secc_fam_lend : sfork_lend secc_fam = emp%I.
  Proof using . reflexivity. Qed.

  (* the recursion's shape: a slot at every key in the universe *)
  Definition secc_slots : iProp Σ :=
    (□ (∀ W : uvis, secc_key W -∗ my_pay (uvis_gen W) (fun _ => True%I) -∗
                    uslot W))%I.

  (* EXEC: the bundle needs NO credential.  The walk and the commit are
     the closed generic ones ([FsAbsInvFire.fsabs_exec_half], exactly
     [UexecExecInst.xv6_sbundle_of_supply]'s exec branch), and both slot
     wands are answered from the recursion at the NEW key, which is in the
     universe by the exec's own two pins: the table is the caller's
     ([kexec_image_ok] / [exec_key_ok]) and so is the mask. *)
  Lemma secc_sbundle_exec (W : uvis) :
    secc_key W -∗ my_pay (uvis_gen W) (fun _ => True%I) -∗ secc_slots -∗
    exec_sbundle uslot secc_fam W.
  Proof using .
    rewrite /secc_slots. iIntros "#Hk #Hpay #IH".
    rewrite /exec_sbundle /secc_fam /xfam_at /xfam_pt /xfam_exec /xfam_exec_at /=.
    iSplitR; [ iExact "Hpay" | ].
    iDestruct (fsabs_exec_half (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W))
      as "[#Hwalk #Hcommit]".
    rewrite /sys_exec_au_pre.
    iSplitR;
      [ iIntros (pl) "_";
        rewrite /FsAbsEra.ex_start /FsAbsEra.ex_hops_from;
        iIntros (r) "_"; iModIntro; iSplit;
        [ done | iApply FsAbsEra.ax_hops_triv ] | ].
    iSplitR; [iExact "Hcommit" |].
    rewrite /pf_at. cbn [pf_recv pf_refund]. iSplit; [| done].
    rewrite /sys_exec_slot_pre. iIntros (pl na alen afun) "_ _".
    rewrite /exec_slot_pre. iSplitR.
    + iIntros (av' i ff nl W') "_ _ _ %Hok _ _ %Hscw _ _ Hp".
      iApply ("IH" with "[] Hp").
      iApply (secc_key_exec_image W W' ff na alen afun Hok Hscw with "Hk").
    + iIntros (av' i a W') "_ _ _ %Hkey _ _ %Hscw _ _ Hp".
      iApply ("IH" with "[] Hp").
      iApply (secc_key_exec_key W W' na alen Hkey Hscw with "Hk").
  Qed.

  Lemma secc_sbundle (n : Z) (W : uvis) :
    n ∉ secc_B ->
    secc_cons_pay -∗ secc_key W -∗ my_pay (uvis_gen W) (fun _ => True%I) -∗
    secc_slots -∗
    |==> sbundle_at uslot n secc_fam W.
  Proof using .
    intros Hnb.
    destruct (secc_notin_cases n Hnb) as (H6 & H15 & H17 & H18 & H19 & H20).
    rewrite /secc_slots. iIntros "#Hc #Hk #Hpay #IH". rewrite /sbundle_at /= /xv6_sbundle.
    destruct (decide (n = USYS_exec)) as [_ | _];
      [ iModIntro; iApply (secc_sbundle_exec with "Hk Hpay IH") | ].
    rewrite /secc_fam /xfam_at /xfam_pt /xfam_exec /xfam_exec_at /=.
    destruct (decide (n = 5)) as [_ | _].
    { iModIntro. iApply (secc_fileread_in with "Hc").
      iApply (secc_key_at_arg with "Hk"). }
    destruct (decide (n = 9)) as [_ | _];
      [ iModIntro; iApply fsabs_chdir_pre | ].
    destruct (decide (n = 15)) as [He | _]; [ exfalso; exact (H15 He) | ].
    destruct (decide (n = 16)) as [_ | _].
    { iModIntro. iApply (secc_filewrite_in with "Hc").
      iApply (secc_key_at_arg with "Hk"). }
    destruct (decide (n = 17)) as [He | _]; [ exfalso; exact (H17 He) | ].
    destruct (decide (n = 18)) as [He | _]; [ exfalso; exact (H18 He) | ].
    destruct (decide (n = 19)) as [He | _]; [ exfalso; exact (H19 He) | ].
    destruct (decide (n = 20)) as [He | _]; [ exfalso; exact (H20 He) | ].
    destruct (decide (n = 6)) as [He | _]; [ exfalso; exact (H6 He) | ].
    destruct (decide (n = 21)) as [_ | _];
      [ iModIntro; iApply (secc_key_close_cpay with "Hk") | ].
    destruct (decide (n = USYS_exit)) as [_ | _];
      [ iModIntro; iDestruct "Hk" as "[_ Hr]";
        iApply (secc_fileclose_cpays with "Hr") | ].
    by iModIntro.
  Qed.

  (* =================================================================== *)
  (*  6.  THE RETURN                                                     *)
  (* =================================================================== *)

  (* a slot's body is a WP, so it absorbs an update: what lets pipe's
     resume ALLOCATE the new name's wild pipe before the recursion is
     applied at the resume key *)
  Lemma uslot_fupd (W : uvis) : (|={⊤}=> uslot W) -∗ uslot W.
  Proof using .
    rewrite {2}(uslot_unfold W). iIntros "H".
    iIntros (h xi C pt Rfd Rut HRut) "%H1 %H2 %H3 Hb".
    rewrite /wp_triv. iApply fupd_wp. iMod "H". iModIntro.
    iEval (rewrite (uslot_unfold W)) in "H".
    iApply ("H" $! h xi C pt Rfd Rut HRut with "[%] [%] [%] Hb");
      [ exact H1 | exact H2 | exact H3 ].
  Qed.

  (* THE RESUME at a returning number: the key stays in the universe *)
  Lemma secc_ret_cont (n : Z) (W : uvis) :
    n = uvis_num W -> n ∉ secc_B ->
    secc_key W -∗ my_pay (uvis_gen W) (fun _ => True%I) -∗ secc_slots -∗
    uexec_ret_cont_F uslot n secc_fam W.
  Proof using .
    intros Hn Hnb. destruct (secc_notin_cases n Hnb) as (_ & H15 & _).
    rewrite /secc_slots. iIntros "#Hk #Hpay #IH". iDestruct "Hk" as "[%Hm #Hr]".
    rewrite /uexec_ret_cont_F /uexec_ret_cont_gen.
    iIntros (r M' π' szv' fdv' cw' g' cs' lz' secc' _ Hfd _ _ Hg _ _ Hsc) "_ Hpost".
    rewrite (usys_gen_ok_quiet _ _ _ Hg).
    assert (Hm' : secc_masked secc') by exact (secc_masked_secc_ok _ _ _ _ _ Hm Hsc).
    iAssert (∀ fdv'' : list fdstate, ⌜fdv'' = fdv'⌝ -∗ secc_rows fdv'' -∗
               uslot (bump W r M' π' szv' fdv' cw' (uvis_gen W) cs' lz' secc'))%I
      as "Hgo".
    { iIntros (fdv'') "-> #Hr'". iApply ("IH" with "[] [Hpay]").
      - rewrite /secc_key. cbn [uvis_fd uvis_secc bump bump_at].
        iSplit; [ iPureIntro; exact Hm' | iExact "Hr'" ].
      - cbn [uvis_gen bump bump_at]. iExact "Hpay". }
    destruct (decide (n = USYS_pipe)) as [Hp | Hnp].
    - (* PIPE: the post hands the new name's fragment; park it wild *)
      rewrite Hp in Hfd. iEval (rewrite Hp) in "Hpost".
      iDestruct (spost_at_pipe_elim with "Hpost") as "Hpost".
      destruct (decide (uint r = 0)) as [Hr0 | Hr0].
      + iDestruct ("Hpost" with "[%]") as (a b γp) "[%Hsh Hf]"; [ exact Hr0 | ].
        destruct Hsh as (_ & _ & _ & ->).
        iApply uslot_fupd.
        iMod (inv_alloc seccN ⊤ (∃ s : pipe_st, pipe_qfrag (pn_queue γp) s)
                with "[Hf]") as "#Hw"; [ iNext; iExists _; iExact "Hf" | ].
        iModIntro. iApply ("Hgo" with "[//]").
        iApply (secc_rows_pipe with "Hw Hr").
      + iApply ("Hgo" $! (uvis_fd W) with "[%] Hr").
        symmetry. exact (usys_fd_ok_pipe_fail _ _ _ _ Hr0 Hfd).
    - iApply ("Hgo" $! fdv' with "[//]").
      iApply (secc_rows_fd_ok n (uvis_tf W) r (uvis_fd W) fdv' H15 Hnp Hfd with "Hr").
  Qed.

  (* ...and at wait, whose answer row the universe does not read *)
  Lemma secc_wait (n : Z) (W : uvis) :
    n = USYS_wait ->
    secc_key W -∗ my_pay (uvis_gen W) (fun _ => True%I) -∗ secc_slots -∗
    uexec_wait_F uslot n secc_fam W.
  Proof using .
    intros Hn. rewrite /secc_slots. iIntros "#Hk #Hpay #IH". iDestruct "Hk" as "[%Hm #Hr]".
    rewrite /uexec_wait_F /uexec_ret_cont_gen.
    iIntros (r M' π' szv' fdv' cw' g' cs' lz' secc' _ Hfd _ _ Hg _ _ Hsc) "_ _".
    rewrite (usys_gen_ok_quiet _ _ _ Hg).
    rewrite Hn in Hfd.
    rewrite (usys_fd_ok_quiet USYS_wait _ _ _ _ ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate) Hfd).
    iApply ("IH" with "[] [Hpay]").
    - rewrite /secc_key. cbn [uvis_fd uvis_secc bump bump_at].
      iSplit; [ iPureIntro; exact (secc_masked_secc_ok _ _ _ _ _ Hm Hsc) | iExact "Hr" ].
    - cbn [uvis_gen bump bump_at]. iExact "Hpay".
  Qed.

  (* ...and at fork: both legs are the recursion, at the parent's
     resume key and at the child's (the same table, the same mask), the
     child's payload is the trivial one and the lend is [emp] *)
  Lemma secc_fork (W : uvis) :
    secc_key W -∗ my_pay (uvis_gen W) (fun _ => True%I) -∗ secc_slots -∗
    uexec_fork_F uslot W secc_fam.
  Proof using .
    rewrite /secc_slots. iIntros "#Hk #Hpay #IH".
    rewrite /uexec_fork_F secc_fam_fpay secc_fam_lend /uexec_fork_parent_F.
    iSplitL.
    { iIntros (r fdv' cw' cs') "_ %Hfd _ _". subst fdv'.
      iApply ("IH" with "[] [Hpay]").
      - iApply (secc_key_cong with "Hk"); reflexivity.
      - cbn [uvis_gen bump bump_at]. iExact "Hpay". }
    iSplitR; [ iIntros "!> _"; done | ].
    iSplitR; [ done | ].
    iIntros (fdv' cw' g' pidc) "_ Hp %Hfd _ _". subst fdv'.
    iApply ("IH" with "[] [Hp]").
    - iApply (secc_key_fork_child with "Hk").
    - cbn [uvis_gen bump bump_at]. iExact "Hp".
  Qed.

  (* THE WHOLE RETURN at a key in the universe, at every cause *)
  Lemma secc_ret (sc : mword 64) (W : uvis) :
    secc_cons_pay -∗ secc_key W -∗ my_pay (uvis_gen W) (fun _ => True%I) -∗
    secc_slots -∗ |==> uexec_ret sc W.
  Proof using .
    rewrite /secc_slots. iIntros "#Hc #Hk #Hpay #IH".
    iPoseProof "Hk" as "[%Hm _]".
    pose proof (uvis_num_masked W Hm) as Hnb.
    assert (Hxb : USYS_exit ∉ secc_B)
      by (rewrite elem_of_list_In; cbn; unfold USYS_exit; lia).
    rewrite /uexec_ret /uexec_ret_F.
    iAssert (uexec_pay_dep (SG := uexecSG_xv6) sc W secc_fam) as "Hpd".
    { iApply (uexec_pay_dep_triv (SG := uexecSG_xv6) sc W secc_fam secc_fam_xpay with "Hpay"). }
    destruct (decide (sc = uecall_scause)) as [_ | _].
    - cbv zeta.
      destruct (decide (uvis_num W = USYS_exit)) as [Hx | Hnx].
      { iMod (secc_sbundle (uvis_num W) W Hnb with "Hc Hk Hpay IH") as "Hb".
        iModIntro. iExists secc_fam. iFrame "Hpd Hb". }
      destruct (decide (uvis_num W = USYS_fork)) as [_ | _].
      { iModIntro. iExists secc_fam. iFrame "Hpd".
        iApply (secc_fork with "Hk Hpay IH"). }
      destruct (decide (uvis_num W = USYS_wait)) as [Hw | _].
      { iMod (secc_sbundle (uvis_num W) W Hnb with "Hc Hk Hpay IH") as "Hb".
        iModIntro. iExists secc_fam. iFrame "Hpd Hb".
        iApply (secc_wait (uvis_num W) W Hw with "Hk Hpay IH"). }
      iMod (secc_sbundle (uvis_num W) W Hnb with "Hc Hk Hpay IH") as "Hb".
      iModIntro. iExists secc_fam. iFrame "Hpd Hb".
      iApply (secc_ret_cont (uvis_num W) W eq_refl Hnb with "Hk Hpay IH").
    - (* THE KILL ARM at its RIGHT disjunct: the process's own payment at
         the trivial payload, beside the exit bundle *)
      iMod (secc_sbundle USYS_exit W Hxb with "Hc Hk Hpay IH") as "Hb".
      iModIntro. iExists secc_fam. iFrame "Hpd".
      rewrite /uexec_kill_arm_F. iSplit.
      + iApply (ukill_cred_at_of_owed with "[] Hb").
        rewrite /ChildTok.kill_owed. iExists (fun _ => True%I).
        iSplit; [ iExact "Hpay" | done ].
      + iApply ("IH" with "Hk Hpay").
  Qed.

  (* =================================================================== *)
  (*  7.  THE MINTER, over the console payer                             *)
  (* =================================================================== *)

  (* [UexecRet.uslot_of_creds]'s Loeb, at the universe: the slot at a key
     in the universe hands back, at every trap, a return whose every arm
     is the same family at a key in the universe. *)
  Lemma useccomp_mint_of_cons :
    secc_cons_pay -∗ □ uexec_wp -∗
    □ (∀ W : uvis, □ secc_key W -∗ my_pay (uvis_gen W) (fun _ => True%I) -∗ uslot W).
  Proof using .
    iIntros "#Hc #Hwp". iLöb as "IH".
    iModIntro. iIntros (W) "#Hk #Hpay".
    rewrite uslot_unfold.
    iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm %Hlz Hb".
    rewrite /uvb /uvb_F.
    iDestruct "Hb" as
      "(#Hamb & Hur & %Hsz & Hpt & Hfrag & Hcfg & Hg & Hpc & Hrut & Hk')".
    iDestruct (user_ptm_inv_x_pt with "Hpt") as (Mp) "Hpt".
    iDestruct (uv_regs_u_regs with "Hur Hg Hpc") as (ms_v sc_v stval_v sepc_v) "[%Hms Hregs]".
    iDestruct "Hamb" as "(Hhw & Hmi & Hwi)".
    iPoseProof "Hwp" as "Hwp0".
    iEval (rewrite uexec_wp_unfold /uexec_F) in "Hwp0".
    iApply ("Hwp0" $! h xi C pt Rut HRut Mp (tf_resume_gpr0 (uvis_tf W))
              ms_v sc_v stval_v sepc_v (tf_resume_pc (uvis_tf W))
              with "[] [] Hhw Hmi Hwi Hregs Hpt Hcfg Hrut [Hk' Hfrag]");
      [ iPureIntro; exact Hlo | iPureIntro; exact Hms | ].
    rewrite /ukont_F /ukb_F.
    iNext. iIntros "[Hframe _]".
    iDestruct (user_trap_frame_trapped C pt Rut (uvis_sz W) (uvis_perm W)
                 (uvis_fd W) (uvis_cwd W) (uvis_gen W) (uvis_ch W) (uvis_pid W)
                 (uvis_lazy W) (uvis_secc W)
                 with "Hframe")
      as (W' sc stv)
         "[%Hperm [%Hszw [%Hfdw [%Hcww [%Hgnw [%Hchw [%Hpidw [%Hlzw [%Hscw Htm]]]]]]]]]".
    iMod (secc_ret sc W' with "Hc [] [] []") as "Hret".
    { iApply (secc_key_cong W W' Hfdw Hscw with "Hk"). }
    { rewrite Hgnw. iExact "Hpay". }
    { rewrite /secc_slots. iModIntro. iIntros (W'') "#Hk'' Hp''".
      iApply ("IH" with "Hk'' Hp''"). }
    iApply ("Hk'" $! W' sc stv with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [Htm Hfrag Hret]");
      [ exact Hperm | exact Hszw | exact Hfdw | exact Hcww | exact Hgnw
      | exact Hchw | exact Hpidw | exact Hlzw | exact Hscw | ].
    rewrite Hfdw. iFrame "Htm Hfrag". iExact "Hret".
  Qed.

  (* ...AND THE GENERALISED TAINT ENTRY IT ANSWERS (design SS9): at a
     table in the universe and a masked mask, the exec's two pins put the
     new key in the universe, so the minter's family IS the entry -- at
     any escape [T], which it never reads.  This is what the seccomp
     program's own [exec(x)] hands [ExecBundle.exec_bundle_of]. *)
  Lemma useccomp_image_entry_taint (T : iProp Σ) (sts : list fdstate)
      (secc : mword 64) :
    secc_masked secc ->
    □ (∀ W : uvis, □ secc_key W -∗ my_pay (uvis_gen W) (fun _ => True%I) -∗ uslot W) -∗
    secc_rows sts -∗
    image_entry_taint T sts secc (fun _ => True%I) uslot.
  Proof using .
    intros Hm. iIntros "#Hmint #Hr". rewrite /image_entry_taint.
    iIntros "!>" (W') "_ %Hfd %Hsc Hp".
    iApply ("Hmint" with "[] Hp").
    iModIntro. iApply (secc_key_of_pins W' sts secc Hfd Hsc with "Hr").
    iPureIntro. exact Hm.
  Qed.

End UexecSecc.
