(* ===================================================================== *)
(*  UShEchoPay.v -- THE SHELL'S FORKED CHILD RUNS /echo ON THE PAID ENTRY  *)
(*  (lane IO-LEAF, step 4, M3b core).                                     *)
(*                                                                       *)
(*  [UShEcho.v] built sh's exec supply at the TRIVIAL payload and the      *)
(*  FREE write law: the child's exit owed nothing and echo's four writes  *)
(*  were paid by the flagged deposit.  Here the same assembly is done at  *)
(*  the payload sh's fork CHOSE ([UkShFork.ushf_wq I]: the era's          *)
(*  credential after echo's block, or the block still owed) and the      *)
(*  credential sh LENT ([Wc I 3], the line's block owed at the era's      *)
(*  input [I]), so that echo's bytes go through the era's write link      *)
(*  ([UEchoOut.echo_uexec_slot_at]) and what the child hands back through *)
(*  its exit is the shell's next prompt credential.                      *)
(*                                                                       *)
(*  THE ERA IS A RECORD (lane LINK-GEN-3).  What this file needs of it is *)
(*  [LinkRec] plus [StageRec]: the era's LEND opened into a STAGE, the    *)
(*  cursor at offset zero and -- persistently -- what the block's end     *)
(*  pays.  The loop's credential family [Wc] is a PARAMETER with three    *)
(*  laws, and the linear resource [Hold I] that rides beside it is what   *)
(*  crosses echo's walk on the cursor ([StageRec.cur_hold]): at the file  *)
(*  application that is sh's own deed fraction ([UShRound.sh_hold]), and  *)
(*  at echo it is [emp].                                                  *)
(*                                                                       *)
(*  Terms.  The LEND is what sh's fork hands the child; the REFUND is     *)
(*  what a failed exec hands back ([UkRunExecRef.udepw_at_refR], at the   *)
(*  supplier's own shape: the ledger fragment and the lend, whole).  The  *)
(*  loop's credential family is the TIGHT one ([EchoLinksLine.ewc_lcred]) *)
(*  -- the loose [EchoLinks.ewc_cred] admits a wire the credential cannot *)
(*  re-derive after a child has written (SH-LINE-CRED's finding).         *)
(*                                                                       *)
(*  WHERE THE fd 1 ROW COMES FROM.  echo's paid entry needs the child's   *)
(*  fd 1 to be the console, a fact about the TABLE the exec channel       *)
(*  carries verbatim; the shell's slot carries the row for its own table  *)
(*  ([UkSh.ush_fd1p]) and the child's table is its parent's, so the       *)
(*  supply takes the ledger fragment INTO the deposit, reads the row off  *)
(*  the table's authority there ([UserFd.ustd_agree]), and refunds the    *)
(*  fragment on the failing arm.                                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import Xv6Cameras Xv6G FdSlots IrefSlots ProcAvail FileInvDefs.
Require Import ProcGeom.          (* [NOFILE] *)
Require Import UexecSlot UexecRet.
Require Import UkRun.
Require Import UserFd.
Require Import ChildTok.
Require Import ElfFile ElfUser.
Require Import PageGeom.          (* [PGSIZE] *)
Require Import UmodeAbi.
Require Import FsImg.
Require Import FsEchoPin.
Require Import SpecKexec.
Require Import ExecEntry.         (* [image_entry] / [image_entry_taint] *)
Require Import FsAbsDefs.         (* [anode] / [MkAnode] / [AFile] *)
Require Import ExecRun.           (* THE U-TIER EXEC RULE this supply is an
                                     instance of *)
Require Import UShKernel.
Require Import KexecDefs.
Require Import UexecExecInst.
Require Import UCodeEcho.         (* [echo_img_sub] / [echo_data_sub] *)
Require Import UkSh UkShFork UkShEcho.
Require Import LineWords.         (* [last_ws] / [wl_line_pos] *)
Require Import EchoDisc.
Require Import EchoOut.           (* [era_pin] / [turn] / [ps_lb] *)
Require Import EchoLinks.         (* [echo_links] / [wr_blk] *)
Require Import EchoLinksLine.     (* [ewc_lcred] and the lend's two ends *)
Require Import LinkRec.           (* the era's link record *)
Require Import StageRec.          (* the cursor / stage record *)
Require Import UEchoOut.          (* [echo_uexec_slot_at_at] / [out_argv_at] *)
Require Import UShEcho.           (* the pinned bundle's inputs *)
Require Import UShEchoOut.        (* [echo_out_argv_of_image] *)
Require Import UShPanic.          (* [ush_execfail_law_holds]: the exec-failed diagnostic's law (M4b(2)) *)
Require User.EchoSyms.

(* ECHO'S .rodata IS IN THE EXEC IMAGE, as its text is: the image is the
   text map, the data map and the zero pages, and the two dumped maps
   agree where they meet (a closed computation, the shape of
   [UShKernel.sh_union_comm_bool]), so the data half is the left component
   of the commuted union. *)
Lemma echo_union_comm_bool :
  bool_decide (EchoInstrs.echo_bytes ∪ EchoData.echo_data
               = EchoData.echo_data ∪ EchoInstrs.echo_bytes) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma echo_data_of_elf_image (M : gmap Z (bv 8)) :
  uimg_sub (elf_image ElfUser.echo_elf) M -> echo_data_sub M.
Proof.
  intros H. rewrite ElfUser.echo_elf_image in H.
  apply UShKernel.uimg_sub_union_l in H.
  rewrite (bool_decide_eq_true_1 _ echo_union_comm_bool) in H.
  exact (UShKernel.uimg_sub_union_l _ _ _ H).
Qed.

Section UShEchoPayGen.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ}.
  Context {L : LinkRec Σ} (St : StageRec L).

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  (* =================================================================== *)
  (*  1.  ECHO'S PAID ENTRY AT THE EXEC CHANNEL                            *)
  (*                                                                      *)
  (*  [UShEcho.echo_slot_of_kexec] at the paid constructor: the exec       *)
  (*  channel's image fact gives every row [UEchoOut.echo_uexec_slot_at_at]*)
  (*  asks about the key, the argument vector is the line's two tokens    *)
  (*  ([UShEchoOut.echo_out_argv_of_image]), fd 1 is the console (the     *)
  (*  caller's row, off the table the channel carries verbatim), and the  *)
  (*  lend -- the block owed at [I], pinned -- is exactly the turn bundle  *)
  (*  echo's first byte needs.  A TAINTED lend (the era's discipline       *)
  (*  already broken) buys the generic slot instead.                      *)
  (*                                                                      *)
  (*  THE THREE [Wc] LAWS.  [Hwc3] opens the lend (the era's pin, the      *)
  (*  block-owed family and the resource that rides beside it), [Hwc0]     *)
  (*  closes it at the block's end, and [Hwct] is its taint arm.  They are *)
  (*  what makes the SAME assembly serve [EchoLinksLine.ewc_lcred] and     *)
  (*  [UShRound]'s [Wcf I p := Wcl I p ∗ sh_hold I].                       *)
  (* =================================================================== *)
  Lemma echo_slot_of_kexec_at_at
      (Wc : list (bv 8) -> nat -> iProp Σ)
      (Hold : list (bv 8) -> iProp Σ)
      (na : nat) (alen : nat -> nat)
      (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis)
      (I : list (bv 8)) (v : era_pins) :
    (forall I0 : list (bv 8), Timeless (Hold I0)) ->
    (forall (I0 : list (bv 8)) (v0 : era_pins),
       ck_lineok (sk_cur St) I0 ->
       ⊢ lk_pin L (S gen_id) v0 -∗ lk_post L (S gen_id) v0 I0 (sk_code St I0) -∗
         Hold I0 -∗ Wc I0 0%nat) ->
    (forall (I0 : list (bv 8)) (v0 : era_pins),
       ⊢ lk_pin L (S gen_id) v0 -∗ lk_T L -∗ Wc I0 0%nat) ->
    line_ok (last_ws I) ->
    kexec_image_ok ElfUser.echo_elf na alen afun sts W' ->
    kexec_sz ElfUser.echo_elf - PGSIZE + 96
      <= kxc_sp_final (kexec_sz ElfUser.echo_elf) alen na ->
    length sts = NOFILE ->
    uvis_lazy W' = false ->
    na = length (last_ws I) ->
    (forall i : nat, (i < length (last_ws I))%nat ->
       alen i = UkShEcho.echo_alen (last_ws I) i) ->
    (forall i j : nat, (i < length (last_ws I))%nat ->
       (j < UkShEcho.echo_alen (last_ws I) i)%nat ->
       afun i j
       = wl_line (last_ws I)
           !!! (UkShEcho.echo_off (last_ws I) i + j)%nat) ->
    UkSh.ush_fd1p (take NSTD sts) ->
    (⊢ app_taint -∗ lk_T L) ->
    (* THE INPUTS THE ERA'S CURSOR IS ABOUT (the program stream): the
       stage the lend opens into is the one whose block is the LINE's own
       alternative, and an era with more than one line shape says which
       inputs those are ([StageRec.ck_lineok]). *)
    ck_lineok (sk_cur St) I ->
    ⊢ lk_pin L (S gen_id) v -∗
      lk_links L -∗
      UkRun.urun_nopipe sts -∗
      udep (PS := uprogSG_free) -∗
      □ (∀ (R : iProp Σ) (W : uvis),
           lk_T L -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
           □ (app_taint -∗ R) -∗ uslot W) -∗
      my_pay (uvis_gen W') (fun _ : Z => UkShFork.ushf_wq Wc I) -∗
      lk_lpr L (S gen_id) v I 3%nat -∗
      Hold I -∗
      uslot W'.
  Proof using St ghost_varG0 ghost_varG1 ufdG0.
    intros HTl Hwc0 Hwct Hokws Hok Hroom Hfdl Hlzf Hna Halen Hafun
           Hfd1 Hkt Hlok.
    iIntros "#Hpin #Hlk #Hnpw #Hdep #Hgen Hmp Hc HR".
    destruct (echo_kexec_pages na alen afun sts W' Hok)
      as (Hpc & Hsub & Hx & Hwr & Hrp).
    destruct (echo_kexec_entry_rows na alen afun sts W' Hok Hroom Hfdl Hwr Hrp)
      as (Hroom96 & Hal8 & Hstkrow & Hargsrow & Havd & Havs
          & Hfdlen & Hstop).
    pose proof (echo_out_argv_of_image (last_ws I) na alen afun sts W'
                  Hokws Hok Hna Halen Hafun) as Hargv.
    (* the child's fd 1, off the channel's table *)
    assert (Hfd : uvis_fd W' = sts)
      by (destruct Hok as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _); exact H).
    destruct Hfd1 as [rb Hl1]. rewrite <- Hfd in Hl1.
    iAssert (UkRun.urun_nopipe (uvis_fd W')) as "#Hnpw'";
      [ rewrite Hfd; iExact "Hnpw" | ].
    assert (Hsub2 : echo_data_sub (uvis_M W')).
    { destruct Hok as (_ & _ & _ & _ & _ & Himg & _).
      exact (echo_data_of_elf_image _ Himg). }
    (* THE LEND: the stage and the cursor at offset zero, or the taint *)
    rewrite (lk_lpr_S3 L (S gen_id) v I 0%nat).
    iDestruct (lk_lend_of_blk0 L (S gen_id) v I 0%nat with "Hc") as "Hlend".
    iDestruct (sk_lend_stage St (S gen_id) v I Hlok with "Hlend")
      as "[Hstg | #HT]"; last first.
    { (* a tainted lend: the generic slot, and the kill wand from the taint *)
      iApply ("Hgen" $! (UkShFork.ushf_wq Wc I) W' with "HT Hmp []").
      iIntros "!> #Hk". rewrite /UkShFork.ushf_wq. iRight.
      iApply (Hwct I v with "Hpin"). iApply Hkt. iExact "Hk". }
    iDestruct "Hstg" as (st) "(%Hok0 & %Halt & Hcur & #Hpost)".
    rewrite /echo_out_argv in Hargv. rewrite <- Halt in Hargv.
    iApply (echo_uexec_slot_at_at (PS := uprogSG_free)
              (cur_hold (sk_cur St) (Hold I) (HTl I))
              W' v st (last_ws I) rb
              (fun _ : Z => UkShFork.ushf_wq Wc I)
              Halt
              ltac:(intros x y; reflexivity)
              (line_ok_ge2 (last_ws I) Hokws)
              Hok0 Hargv Hl1 Hpc Hsub Hsub2 Hx Hroom96 Hal8 Hstkrow Hargsrow
              Havd Havs Hfdlen Hstop Hlzf
              with "[] Hpin Hlk Hnpw' Hdep Hmp [Hcur HR]").
    - (* THE BLOCK'S END PAYS THE EXIT: the output's own length on, the
         choice filed, the credential is the shell's next prompt's -- and
         the resource that rode the cursor comes back with it *)
      iIntros "!> [Hc HR]". rewrite /UkShFork.ushf_wq. iRight.
      iApply (Hwc0 I v Hlok with "Hpin [Hc] HR").
      iApply ("Hpost" with "Hc").
    - (* ...and its first byte is where the lend stands *)
      iFrame "Hcur HR".
  Qed.

  (* =================================================================== *)
  (*  2.  THE ASSEMBLY: sh's pinned bundle pays its exec supply, PAID      *)
  (*                                                                      *)
  (*  [UShEcho]'s section 7 at the paid entry.  IT IS AN INSTANCE OF THE   *)
  (*  U-TIER RULE ([ExecRun.udepw_at_refR_of_sup], lane EX-4) and what is  *)
  (*  left here is sh's own supply: the node it malloc'd read off the lent *)
  (*  heap, the PIN as (W)'s supplier ([ExecRun.exec_walk_of_pin]), the    *)
  (*  resolving arm [echo_slot_of_kexec_at_at] as (E), the taint arm at    *)
  (*  the chosen payload, and the refund -- the ledger fragment and the    *)
  (*  lend, WHOLE (which is why the lend is never split here).             *)
  (*                                                                      *)
  (*  THIS IS WHAT [UShRound.Hchild_echo] IS ONE APPLICATION OF, at        *)
  (*  [Wc := Wcf] and [Hold := sh_hold].                                   *)
  (* =================================================================== *)
  (* ...AT THE ERA'S OWN GUARD (the PROGRAM STREAM).  [line_ok] is ECHO's
     reading of "this input is one my supply is about", and it is the whole
     reading only because that era has ONE line shape; an era with three
     says which of its inputs the ECHO child runs at, and the guard is then
     the conjunction it can prove from the child law's own box.  The two
     premises below are what the body actually spends [line_ok] on: the
     argument vector's readings, and the stage the lend opens into. *)
  Lemma sh_exec_sup_echo_wq_holds_at_D
      (D : list (bv 8) -> Prop)
      (Wc : list (bv 8) -> nat -> iProp Σ)
      (Hold : list (bv 8) -> iProp Σ) :
    (forall I0 : list (bv 8), Timeless (Hold I0)) ->
    (forall I0 : list (bv 8),
       ⊢ Wc I0 3%nat -∗ ∃ v : era_pins,
           lk_pin L (S gen_id) v ∗ lk_lpr L (S gen_id) v I0 3%nat
           ∗ Hold I0) ->
    (forall (I0 : list (bv 8)) (v0 : era_pins),
       ⊢ lk_pin L (S gen_id) v0 -∗ lk_lpr L (S gen_id) v0 I0 3%nat -∗
         Hold I0 -∗ Wc I0 3%nat) ->
    (forall (I0 : list (bv 8)) (v0 : era_pins),
       ck_lineok (sk_cur St) I0 ->
       ⊢ lk_pin L (S gen_id) v0 -∗ lk_post L (S gen_id) v0 I0 (sk_code St I0) -∗
         Hold I0 -∗ Wc I0 0%nat) ->
    (forall (I0 : list (bv 8)) (v0 : era_pins),
       ⊢ lk_pin L (S gen_id) v0 -∗ lk_T L -∗ Wc I0 0%nat) ->
    (⊢ app_taint -∗ lk_T L) ->
    (* the guard's two readings: the line the child runs is admissible... *)
    (forall I0 : list (bv 8), D I0 -> line_ok (last_ws I0)) ->
    (* ...and the era's own reading of its admissible lines: at echo's
       instance [ck_lineok] is [True] and this is [fun _ _ => I]. *)
    (forall I0 : list (bv 8), D I0 -> ck_lineok (sk_cur St) I0) ->
    ⊢ lk_links L -∗ udep (PS := uprogSG_free) -∗ sh_echo_slot (lk_T L) -∗
      UkShEcho.sh_exec_sup_echo_wq_at D Wc.
  Proof using St ghost_varG0 ghost_varG1 ufdG0.
    intros HTl Hwc3 Hwc3b Hwc0 Hwct Hkt Hdok Hlok.
    iIntros "#Hlk #Hdep (#Hinv & #Hcl & #Hgen)".
    rewrite /UkShEcho.sh_exec_sup_echo_wq_at. iIntros "!>" (I) "%HDI".
    pose proof (Hdok I HDI) as Hokws.
    rewrite /UkShEcho.sh_exec_sup_echo.
    iIntros "!>" (N' m pc s0 t g ld)
      "%Hpeq %Ha0 %Ha1 %Hbytes %Hfd1 Hstd #Hcmd Hcr".
    (* the lend, opened: the era's pin, the block-owed family and the
       resource that rides beside it *)
    iDestruct (Hwc3 I with "Hcr") as (v) "(#Hpin & Hcr & HR)".
    (* ---- THE TAINT ARM: the generic slot at the chosen payload.  It names
       no key, so it is built before the deposit's own ∀. ---- *)
    iAssert (image_entry_taint (lk_T L)
               (fun _ : Z => UkShFork.ushf_wq Wc I) uslot)%I as "#Hgen'".
    { rewrite /image_entry_taint. iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! (UkShFork.ushf_wq Wc I) W' with "HT Hmp []").
      iIntros "!> #Hk". rewrite /UkShFork.ushf_wq. iRight.
      iApply (Hwct I v with "Hpin"). iApply Hkt. iExact "Hk". }
    (* ---- ...AND THE REST IS THE U-TIER RULE (lane EX-4). ---- *)
    iApply (udepw_at_refR_of_sup N' m pc
              (mword_of_int s0) (mword_of_int (t + 8))
              FsImg.ROOTINO (lk_T L) echo_pl ElfUser.echo_elf 1%nat
              (UserFd.ustd (ukn_fd N') ld
               ∗ lk_lpr L (S gen_id) v I 3%nat ∗ Hold I)%I
              _ echo_elf_loadable Ha0 Ha1 with "[] [] [Hstd Hcr HR]").
    (* THE REFUND IS THE LEND, WHOLE *)
    { iIntros "!> ($ & Hc & HR)". iApply (Hwc3b I v with "Hpin Hc HR"). }
    { rewrite Hpeq. iExact "Hgen'". }
    rewrite /uexec_sup_run.
    iIntros (M pm sz fdv cs pidv) "#Hnpw Hheap Hufd".
    iDestruct (UkRun.urun_rows_nopipe _ _ with "Hnpw") as "#Hnp0".
    iAssert (⌜ echo_node_img (last_ws I) M s0 t g ⌝)%I as %Himg.
    { iApply (echo_node_img_of_cmd (last_ws I) _ _ _ M pm sz s0 t g Hokws
                with "Hheap Hcmd"). }
    iDestruct (ufd_auth_len with "Hufd") as %Hlen.
    iDestruct (ustd_agree (ukn_fd N') fdv ld with "Hufd Hstd") as %Hl.
    assert (Hfd1' : UkSh.ush_fd1p (take NSTD fdv)) by (rewrite Hl; exact Hfd1).
    iFrame "Hheap Hufd".
    iSplitR "Hstd Hcr HR".
    { iPureIntro.
      exact (sh_echo_path_of_holds (last_ws I) Hokws M s0 t g Himg Hbytes). }
    iSplitR "Hstd Hcr HR".
    { iApply (exec_walk_of_pin FsEchoPin.era0_echo_pins (lk_T L) FsImg.ROOTINO
                echo_pl [FsImg.ROOTINO; FsEchoPin.ECHO_INO]
                FsEchoPin.ECHO_INO
                (MkAnode (AFile ElfUser.echo_elf) 1%nat) sh_echo_pin_resolves
                with "Hcl Hinv"). }
    iSplitR "Hstd Hcr HR".
    { rewrite Hpeq. rewrite /image_entry. iModIntro.
      iIntros (na alen afun W') "%Hok %Hcwd0 %Hlzf _ _ %Hargs Hmp [_ [Hc HR]]".
      destruct (echo_args_det_holds (last_ws I) Hokws M s0 t g na alen afun
                  Himg Hbytes Hargs) as (Hna & Halen & Hafun).
      iApply (echo_slot_of_kexec_at_at Wc Hold na alen afun fdv W' I v
                HTl Hwc0 Hwct Hokws Hok
                (echo_room_of_det (last_ws I) na alen Hokws Hna Halen)
                Hlen Hlzf Hna Halen Hafun Hfd1' Hkt (Hlok I HDI)
                with "Hpin Hlk Hnp0 Hdep Hgen Hmp Hc HR"). }
    iFrame "Hstd Hcr HR".
  Qed.

  (* the landed name: echo's guard IS [line_ok] *)
  Lemma sh_exec_sup_echo_wq_holds_at
      (Wc : list (bv 8) -> nat -> iProp Σ)
      (Hold : list (bv 8) -> iProp Σ) :
    (forall I0 : list (bv 8), Timeless (Hold I0)) ->
    (forall I0 : list (bv 8),
       ⊢ Wc I0 3%nat -∗ ∃ v : era_pins,
           lk_pin L (S gen_id) v ∗ lk_lpr L (S gen_id) v I0 3%nat
           ∗ Hold I0) ->
    (forall (I0 : list (bv 8)) (v0 : era_pins),
       ⊢ lk_pin L (S gen_id) v0 -∗ lk_lpr L (S gen_id) v0 I0 3%nat -∗
         Hold I0 -∗ Wc I0 3%nat) ->
    (forall (I0 : list (bv 8)) (v0 : era_pins),
       ck_lineok (sk_cur St) I0 ->
       ⊢ lk_pin L (S gen_id) v0 -∗ lk_post L (S gen_id) v0 I0 (sk_code St I0) -∗
         Hold I0 -∗ Wc I0 0%nat) ->
    (forall (I0 : list (bv 8)) (v0 : era_pins),
       ⊢ lk_pin L (S gen_id) v0 -∗ lk_T L -∗ Wc I0 0%nat) ->
    (⊢ app_taint -∗ lk_T L) ->
    (forall I0 : list (bv 8),
       line_ok (last_ws I0) -> ck_lineok (sk_cur St) I0) ->
    ⊢ lk_links L -∗ udep (PS := uprogSG_free) -∗ sh_echo_slot (lk_T L) -∗
      UkShEcho.sh_exec_sup_echo_wq Wc.
  Proof using St ghost_varG0 ghost_varG1 ufdG0.
    intros HTl Hwc3 Hwc3b Hwc0 Hwct Hkt Hlok.
    exact (sh_exec_sup_echo_wq_holds_at_D (fun I => line_ok (last_ws I))
             Wc Hold HTl Hwc3 Hwc3b Hwc0 Hwct Hkt
             (fun I0 H => H) Hlok).
  Qed.

  (* =================================================================== *)
  (*  3.  THE CHILD LAW AT THE FRAMED FAMILY                              *)
  (*                                                                      *)
  (*  The supply above and [UShPanic.ush_execfail_law_hold_at], at the ONE *)
  (*  family the campaign instantiates: [Wcf I p := Wcl I p ∗ Hold I]      *)
  (*  ([UShRound]'s, with [Hold := sh_hold]).  At that family the four     *)
  (*  [Wc] laws are the RECORD's own, so a caller supplies only [Hold]'s   *)
  (*  timelessness and its taint arm -- both of which [sh_hold] has by     *)
  (*  construction (its right disjunct IS the taint).                      *)
  (* =================================================================== *)
  Local Lemma lkw_wc3 (Hold : list (bv 8) -> iProp Σ) (I0 : list (bv 8)) :
    ⊢ (lk_lcred L (S gen_id) I0 3%nat ∗ Hold I0) -∗
      ∃ v : era_pins,
        lk_pin L (S gen_id) v ∗ lk_lpr L (S gen_id) v I0 3%nat ∗ Hold I0.
  Proof using .
    rewrite /lk_lcred. iIntros "[H HR]". iDestruct "H" as (v) "[#Hp Hc]".
    iExists v. iFrame "Hp Hc HR".
  Qed.

  Local Lemma lkw_wc3b (Hold : list (bv 8) -> iProp Σ) (I0 : list (bv 8))
      (v0 : era_pins) :
    ⊢ lk_pin L (S gen_id) v0 -∗ lk_lpr L (S gen_id) v0 I0 3%nat -∗
      Hold I0 -∗ (lk_lcred L (S gen_id) I0 3%nat ∗ Hold I0).
  Proof using .
    iIntros "#Hp Hc HR". iFrame "HR". rewrite /lk_lcred. iExists v0.
    iFrame "Hp Hc".
  Qed.

  Local Lemma lkw_wc0 (Hold : list (bv 8) -> iProp Σ) (I0 : list (bv 8))
      (v0 : era_pins) :
    ck_lineok (sk_cur St) I0 ->
    ⊢ lk_pin L (S gen_id) v0 -∗ lk_post L (S gen_id) v0 I0 (sk_code St I0) -∗
      Hold I0 -∗ (lk_lcred L (S gen_id) I0 0%nat ∗ Hold I0).
  Proof using St.
    intro Hlok. iIntros "#Hp Hc HR". iFrame "HR".
    iApply (lk_lcred_of_post_a L (S gen_id) I0 (sk_code St I0) v0 (sk_apr0 St I0 Hlok)
              with "Hp Hc").
  Qed.

  Local Lemma lkw_wct (Hold : list (bv 8) -> iProp Σ)
      (Hht : forall I0 : list (bv 8), ⊢ lk_T L -∗ Hold I0)
      (I0 : list (bv 8)) (v0 : era_pins) :
    ⊢ lk_pin L (S gen_id) v0 -∗ lk_T L -∗
      (lk_lcred L (S gen_id) I0 0%nat ∗ Hold I0).
  Proof using .
    iIntros "#Hp #HT". iSplitL.
    - iApply (lk_lcred_taint L (S gen_id) I0 0%nat v0 with "Hp HT").
    - iApply Hht. iExact "HT".
  Qed.

  (* THE EXEC-FAILED DIAGNOSTIC IS A PREMISE AND NOT A CONSEQUENCE (lane
     LINK-GEN-2).  [UkShEcho.ush_execfail_law_wq Wc] asks for
     [UkShDiag.ush_execfail_law], i.e. [ush_execfail_law_at alt_execfail 17],
     at EVERY input; [UShPanic.ush_execfail_law_hold_at] gives
     [ush_execfail_law_at (lk_exfb L I) (length (lk_exfb L I) - 2)].  At
     echo those coincide; at the file they do not, because [FileLinksLine.
     fexfb LCat = alt_execcat].  So the law comes in as a hypothesis, and
     what has to change before a second era can discharge it is
     [UkShEcho.ush_execfail_law_wq] itself -- the diagnostic must be a
     parameter there, exactly as [UkShDiag.ush_execfail_law_at] already
     makes it one. *)
  Lemma ushf_child_law_hold_at (Hold : list (bv 8) -> iProp Σ) :
    (forall I0 : list (bv 8), Timeless (Hold I0)) ->
    (forall I0 : list (bv 8), ⊢ lk_T L -∗ Hold I0) ->
    (⊢ app_taint -∗ lk_T L) ->
    (* the era's own reading of its admissible lines ([StageRec.ck_lineok]) *)
    (forall I0 : list (bv 8),
       line_ok (last_ws I0) -> ck_lineok (sk_cur St) I0) ->
    ⊢ lk_links L -∗ udep (PS := uprogSG_free) -∗ sh_echo_slot (lk_T L) -∗
      UkShEcho.ush_execfail_law_wq (PS := uprogSG_free)
        (fun I p => lk_lcred L (S gen_id) I p ∗ Hold I)%I -∗
      UkShFork.ushf_child_law (PS := uprogSG_free)
        (fun I p => lk_lcred L (S gen_id) I p ∗ Hold I)%I.
  Proof using St ghost_varG0 ghost_varG1 ufdG0.
    intros HTl Hht Hkt Hlok. iIntros "#Hlk #Hdep #Hslot #Hxlw".
    iPoseProof (sh_exec_sup_echo_wq_holds_at
                  (fun I p => lk_lcred L (S gen_id) I p ∗ Hold I)%I Hold
                  HTl (lkw_wc3 Hold) (lkw_wc3b Hold) (lkw_wc0 Hold)
                  (lkw_wct Hold Hht) Hkt Hlok
                  with "Hlk Hdep Hslot") as "Hsup".
    iApply (UkShEcho.ushf_child_law_holds (PS := uprogSG_free) (fun k H => H)
              (fun I p => lk_lcred L (S gen_id) I p ∗ Hold I)%I
              with "Hxlw Hsup").
  Qed.

  (* ...AND ITS DISCHARGE, AT THE PARAMETERIZED CARRIER (lane LINK-GEN-4).
     [UShPanic.ush_execfail_law_hold_at] delivers the law at [lk_exfb L I]
     and its own index, so at [UkShEcho.ush_execfail_law_wq_at] there is
     NOTHING to prove -- no equation, at any era.  THIS is what
     [UShRound.Hexecfail] should be stated at. *)
  Lemma ush_execfail_law_wq_at_hold (Hold : list (bv 8) -> iProp Σ) :
    ⊢ lk_links L -∗
      UkShEcho.ush_execfail_law_wq_at (PS := uprogSG_free)
        (lk_exfb L) (fun I => (length (lk_exfb L I) - 2)%nat)
        (fun I p => lk_lcred L (S gen_id) I p ∗ Hold I)%I.
  Proof using .
    iIntros "#Hlk". rewrite /UkShEcho.ush_execfail_law_wq_at.
    iIntros "!>" (I).
    iApply (UShPanic.ush_execfail_law_hold_at (PS := uprogSG_free) L Hold I
              with "Hlk").
  Qed.

  (* ...and the LANDED carrier, which still names the constants: an era
     whose exec-failed bytes are [alt_execfail] at every input answers it.
     echo does; the file does NOT (`fexfb LCat = alt_execcat`), which is
     the lane's open item. *)
  Lemma ush_execfail_law_wq_hold_at (Hold : list (bv 8) -> iProp Σ) :
    (forall I0 : list (bv 8), lk_exfb L I0 = alt_execfail) ->
    ⊢ lk_links L -∗
      UkShEcho.ush_execfail_law_wq (PS := uprogSG_free)
        (fun I p => lk_lcred L (S gen_id) I p ∗ Hold I)%I.
  Proof using .
    intros Hxb. iIntros "#Hlk".
    iApply (UkShEcho.ush_execfail_law_wq_of_at (PS := uprogSG_free)
              (lk_exfb L) (fun I => (length (lk_exfb L I) - 2)%nat) _
              Hxb ltac:(intro I; cbn beta; rewrite (Hxb I) UShPanic.alt_execfail_len; reflexivity)).
    iApply (ush_execfail_law_wq_at_hold Hold with "Hlk").
  Qed.

End UShEchoPayGen.

(* ===================================================================== *)
(*  THE ECHO INSTANCE, DEFINITIONALLY (LinkRec's pattern).                *)
(*                                                                       *)
(*  At echo the resource that rides the cursor is [emp] -- there is no    *)
(*  deed -- and [Wc] is the loop's tight family, so the three laws are    *)
(*  [EchoLinksLine]'s own.                                               *)
(* ===================================================================== *)
Section UShEchoPayEcho.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{HPT : !Persistent T} `{HTT : !Timeless T}.

  Local Notation LE := (echo_link_inst T γ).
  Local Notation SE := (echo_stage_inst T γ).
  (* the loop's credential family, at the era's pin *)
  Local Notation Wc := (EchoLinksLine.ewc_lcred T γ (S gen_id)).
  Local Notation Wq := (UkShFork.ushf_wq Wc).

  Local Lemma ei_hold_tl (I0 : list (bv 8)) : Timeless (emp%I : iProp Σ).
  Proof using . apply _. Qed.

  Local Lemma ei_wc3 (I0 : list (bv 8)) :
    ⊢ Wc I0 3%nat -∗ ∃ v : era_pins,
        lk_pin LE (S gen_id) v ∗ lk_lpr LE (S gen_id) v I0 3%nat ∗ emp.
  Proof using .
    rewrite /EchoLinksLine.ewc_lcred. iIntros "H".
    iDestruct "H" as (v) "[#Hpin Hc]". iExists v. by iFrame "Hpin Hc".
  Qed.

  Local Lemma ei_wc3b (I0 : list (bv 8)) (v0 : era_pins) :
    ⊢ lk_pin LE (S gen_id) v0 -∗ lk_lpr LE (S gen_id) v0 I0 3%nat -∗
      emp -∗ Wc I0 3%nat.
  Proof using .
    iIntros "#Hpin Hc _". rewrite /EchoLinksLine.ewc_lcred.
    iExists v0. iFrame "Hpin Hc".
  Qed.

  Local Lemma ei_wc0 (I0 : list (bv 8)) (v0 : era_pins) :
    True ->
    ⊢ lk_pin LE (S gen_id) v0 -∗ lk_post LE (S gen_id) v0 I0 0%nat -∗
      emp -∗ Wc I0 0%nat.
  Proof using HPT.
    intros _. iIntros "#Hpin Hc _".
    iApply (lk_lcred_of_post_a LE (S gen_id) I0 0%nat v0
              (sk_apr0 SE I0 I) with "Hpin Hc").
  Qed.

  Local Lemma ei_wct (I0 : list (bv 8)) (v0 : era_pins) :
    ⊢ lk_pin LE (S gen_id) v0 -∗ lk_T LE -∗ Wc I0 0%nat.
  Proof using HPT.
    iApply (lk_lcred_taint LE (S gen_id) I0 0%nat v0).
  Qed.

  Definition echo_slot_of_kexec_at (na : nat) (alen : nat -> nat)
      (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis)
      (I : list (bv 8)) (v : era_pins) :
    line_ok (last_ws I) ->
    kexec_image_ok ElfUser.echo_elf na alen afun sts W' ->
    kexec_sz ElfUser.echo_elf - PGSIZE + 96
      <= kxc_sp_final (kexec_sz ElfUser.echo_elf) alen na ->
    length sts = NOFILE ->
    uvis_lazy W' = false ->
    na = length (last_ws I) ->
    (forall i : nat, (i < length (last_ws I))%nat ->
       alen i = UkShEcho.echo_alen (last_ws I) i) ->
    (forall i j : nat, (i < length (last_ws I))%nat ->
       (j < UkShEcho.echo_alen (last_ws I) i)%nat ->
       afun i j
       = wl_line (last_ws I)
           !!! (UkShEcho.echo_off (last_ws I) i + j)%nat) ->
    UkSh.ush_fd1p (take NSTD sts) ->
    (⊢ app_taint -∗ T) ->
    (* the line guard, [True] at echo's cursor *)
    True ->
    ⊢ era_pin γ (S gen_id) v -∗
      EchoLinks.echo_links T γ -∗
      UkRun.urun_nopipe sts -∗
      udep (PS := uprogSG_free) -∗
      □ (∀ (R : iProp Σ) (W : uvis),
           T -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
           □ (app_taint -∗ R) -∗ uslot W) -∗
      my_pay (uvis_gen W') (fun _ : Z => Wq I) -∗
      EchoLinksLine.ewc_lpr T v I 3%nat -∗
      emp -∗
      uslot W'
    := echo_slot_of_kexec_at_at SE Wc (fun _ => emp)%I na alen afun sts W' I v
         ei_hold_tl ei_wc0 ei_wct.

  Definition sh_exec_sup_echo_wq_holds :
    (⊢ app_taint -∗ T) ->
    ⊢ EchoLinks.echo_links T γ -∗ udep (PS := uprogSG_free) -∗
      sh_echo_slot T -∗ UkShEcho.sh_exec_sup_echo_wq Wc
    := fun Hkt =>
         sh_exec_sup_echo_wq_holds_at SE Wc (fun _ => emp)%I
           ei_hold_tl ei_wc3 ei_wc3b ei_wc0 ei_wct Hkt (fun _ _ => I).
  (* ...and the line guard is [True] at echo's cursor, so the instance
     above needs nothing: [ck_lineok echo_cur_inst = fun _ => True]. *)

  (* =================================================================== *)
  (*  THE BODY'S TWO LAWS AT THE TIGHT FAMILY -- the witnesses             *)
  (* =================================================================== *)
  (* a killed child pays the credential with the taint, at any pin *)
  Lemma ushf_kill_law_holds (v : era_pins) :
    (⊢ app_taint -∗ T) ->
    ⊢ era_pin γ (S gen_id) v -∗ UkShFork.ushf_kill_law Wc.
  Proof.
    intros Hkt. iIntros "#Hpin". rewrite /UkShFork.ushf_kill_law.
    iIntros "!>" (n) "#Hk".
    iApply (EchoLinksLine.ewc_lcred_taint T γ (S gen_id) n 0%nat v
              with "Hpin [Hk]").
    iApply Hkt. iExact "Hk".
  Qed.

  (* ...and the paid child's walk, out of the supply above: the closed form
     that says the composition exists *)
  Lemma ushf_child_law_holds_at :
    (⊢ app_taint -∗ T) ->
    ⊢ EchoLinks.echo_links T γ -∗ udep (PS := uprogSG_free) -∗
      sh_echo_slot T -∗
      UkShFork.ushf_child_law (PS := uprogSG_free) Wc.
  Proof.
    intros Hkt. iIntros "#Hlk #Hdep #Hslot".
    iPoseProof (sh_exec_sup_echo_wq_holds Hkt with "Hlk Hdep Hslot") as "Hsup".
    iAssert (UkShEcho.ush_execfail_law_wq (PS := uprogSG_free) Wc) as "Hxlw".
    { rewrite /UkShEcho.ush_execfail_law_wq. iIntros "!>" (I).
      iApply (UShPanic.ush_execfail_law_holds (PS := uprogSG_free) T γ I
                with "Hlk"). }
    iApply (UkShEcho.ushf_child_law_holds (PS := uprogSG_free) (fun k H => H) Wc
              with "Hxlw Hsup").
  Qed.

End UShEchoPayEcho.
