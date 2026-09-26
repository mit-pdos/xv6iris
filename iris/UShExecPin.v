(* ===================================================================== *)
(* UShExecPin.v -- sh's EXEC OF A PINNED PROGRAM AT A CALLER'S ENTRY,     *)
(* ONCE FOR EVERY WORD LIST, AND THE FILTER STAGES' INSTANCES (cut G7,    *)
(* claude-notes/design/grep-pipes.md SS4).                                *)
(*                                                                        *)
(* [UShCatFStage.sh_exec_sup_catf_of_entry] ([cat f] at the pipe) was one *)
(* instance of a supply that names no program: the node read off the lent *)
(* heap, the PIN as the walk's supplier ([ExecRun.exec_walk_of_pin]), the *)
(* resolving arm as the caller's entry, the taint arm at the chosen       *)
(* payload.  [sh_exec_sup_x_of_entry] is that supply at ANY exec'able     *)
(* word list whose argv[0] a pin resolves; the pin comes from the         *)
(* program's SLOT ([sh_pin_slot], [UShCatPay.sh_cat_slot]'s body at an    *)
(* abstract pin).                                                        *)
(*                                                                        *)
(* THE FILTER STAGES read it at their program ([filt_elf], [filt_pl],     *)
(* [filt_pins]): /cat at [FCat], /grep at [FGrep w] -- and sh's           *)
(* [exec %s failed] at the stage's argv[0] ([filt_execfail_bytes]).       *)
(*                                                                        *)
(* THE REBASE.  The parser names a stage's argv by the LINE's offsets     *)
(* ([UkShPipesLex.ushq_rebase] of the stage's own tokens); the exec arm   *)
(* at a word list reads it from offset 0 of the stage's own byte          *)
(* function.  The two argv vectors agree field by field                   *)
(* ([ush_args_rebase]), and a node is read only field by field            *)
(* ([ush_cmd_exec_ext]), so the node sh holds IS the word list's node at  *)
(* the shifted base -- no function extensionality.                        *)
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
Require Import RegFile.
Require Import ProcGeom.
Require Import UexecSlot UexecRet UexecSG UexecExecInst.
Require Import UkRun UkRunLeaf.
Require Import UserHeap.
Require Import UserFd UserCwd.
Require Import ChildTok.
Require Import ElfFile ElfUser ElfLoadable.
Require Import UmodeArith UmodeAbi.
Require Import PathElems ArgPath.
Require Import FsCfg.
Require Import FsImg FsImgCheck.
Require Import FsAbsDefs FsAbsEra.
Require Import AppCfg AppInv.
Require Import FsCatPin FsGrepPin FsSeccPin.
Require Import FileFsPure.
Require Import PinnedExec.
Require Import ExecEntry ExecArgs ExecRun ExecWords.
Require Import SpecKexec.      (* [kexec_loadable] *)
Require Import LineWords EchoDisc.
Require Import PipeDisc PipesDisc.
Require Import UkSh UkShRun UkShMain UkShDiag.
Require Import UkShEcho.
Require Import UShEcho UShEchoPipePay UShCatPay UShCat UShGrep.
Require UShSecc.
Require Import UkShPipesLex.
Require UkShDiagAt.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE FILTER STAGES' PROGRAMS                                       *)
(* ===================================================================== *)

(* grep's path, as cat's ([UShCatPay.cat_pl]) *)
Definition grep_pl : list (bv 8) := FsImgCheck.fname_grep.

Lemma grep_path_elems : path_elems grep_pl = FsGrepPin.grep_path.
Proof using . vm_compute. reflexivity. Qed.

Lemma sh_grep_pin_resolves :
  pin_resolves FsGrepPin.era0_grep_pins FsImg.ROOTINO grep_pl
    [FsImg.ROOTINO; FsGrepPin.GREP_INO] FsGrepPin.GREP_INO
    ElfUser.grep_elf 1%nat.
Proof using .
  split_and!.
  - unfold FsAbsEra.um_start_of.
    destruct (decide (grep_pl !! 0%nat = Some PathElems.SLASH)); reflexivity.
  - rewrite grep_path_elems. reflexivity.
  - intros v Hv. destruct Hv as (_ & Hnode & Hrun).
    rewrite grep_path_elems. split.
    + exact Hrun.
    + rewrite Hnode. rewrite FsGrepPin.grep_bytes_elf. reflexivity.
Qed.

(* /seccomp's path is its command word [seccomp] (seccomp lane S4): sh
   execs the word, resolved at the root *)
Definition secc_pl : list (bv 8) := FileDisc.cmd_seccomp.

Lemma secc_path_elems : path_elems secc_pl = FsSeccPin.secc_path.
Proof using . vm_compute. reflexivity. Qed.

Lemma sh_secc_pin_resolves :
  pin_resolves FsSeccPin.era0_secc_pins FsImg.ROOTINO secc_pl
    [FsImg.ROOTINO; FsSeccPin.SECC_INO] FsSeccPin.SECC_INO
    ElfUser.seccomp_elf 1%nat.
Proof using .
  split_and!.
  - unfold FsAbsEra.um_start_of.
    destruct (decide (secc_pl !! 0%nat = Some PathElems.SLASH)); reflexivity.
  - rewrite secc_path_elems. reflexivity.
  - intros v Hv. destruct Hv as (_ & Hnode & Hrun).
    rewrite secc_path_elems. split.
    + exact Hrun.
    + rewrite Hnode. rewrite FsSeccPin.secc_bytes_elf. reflexivity.
Qed.

(* the image, the path, the inode and the pin of a stage's program *)
Definition filt_elf (F : filt) : list (bv 8) :=
  match F with FCat => ElfUser.cat_elf | FGrep _ => ElfUser.grep_elf end.
Definition filt_pl (F : filt) : list (bv 8) :=
  match F with FCat => UShCatPay.cat_pl | FGrep _ => grep_pl end.
Definition filt_ino (F : filt) : Z :=
  match F with FCat => FsCatPin.CAT_INO | FGrep _ => FsGrepPin.GREP_INO end.
Definition filt_pins (F : filt) : aview -> Prop :=
  match F with FCat => FsCatPin.era0_cat_pins | FGrep _ => FsGrepPin.era0_grep_pins end.

Lemma filt_pin_resolves (F : filt) :
  pin_resolves (filt_pins F) FsImg.ROOTINO (filt_pl F)
    [FsImg.ROOTINO; filt_ino F] (filt_ino F) (filt_elf F) 1%nat.
Proof using . destruct F; [exact UShCatPay.sh_cat_pin_resolves | exact sh_grep_pin_resolves]. Qed.

Lemma filt_elf_loadable (F : filt) : kexec_loadable (filt_elf F).
Proof using . destruct F; [exact UShCat.cat_elf_loadable | exact UShGrep.grep_elf_loadable]. Qed.

(* argv[0] of a stage's words is its program's path *)
Lemma filt_words_head (F : filt) : filt_words F !!! 0%nat = filt_pl F.
Proof using . destruct F; vm_compute; reflexivity. Qed.

(* sh's [exec %s failed] at a stage, with the prompt after it *)
Definition filt_alt (F : filt) : list (bv 8) := filt_dg_exec F ++ u_prompt.

Lemma filt_dg_exec_len (F : filt) :
  length (filt_dg_exec F) = (13 + length (filt_words F !!! 0%nat))%nat.
Proof using . destruct F; vm_compute; reflexivity. Qed.

Lemma filt_alt_lookup (F : filt) (p : nat) (b : bv 8) :
  (p < 13 + length (filt_words F !!! 0%nat))%nat -> filt_alt F !! p = Some b ->
  filt_dg_exec F !! p = Some b.
Proof using .
  intros Hp Hb. rewrite -filt_dg_exec_len in Hp. unfold filt_alt in Hb.
  by rewrite lookup_app_l in Hb.
Qed.

(* sh's [exec cat failed], around the command's name *)
Lemma catf_execfail_bytes : UkShDiagAt.ush_execfail_bytes alt_execR FileDisc.fd_w_cat.
Proof using .
  rewrite /UkShDiagAt.ush_execfail_bytes. split_and!.
  - vm_compute. lia.
  - intros j Hj.
    assert (Hl : (j < length alt_execR)%nat) by (vm_compute in Hj |- *; lia).
    exact (list_lookup_lookup_total_lt alt_execR j Hl).
  - intros j Hj.
    apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x12b8)
             (fun i : nat => alt_execR !!! i) 0%nat 5%nat);
      [vm_compute; reflexivity | lia].
  - intros j Hj.
    assert (Hj3 : (j < 3)%nat) by (vm_compute in Hj; lia).
    destruct j as [| [| [| j]]]; try lia; vm_compute; reflexivity.
  - intros j Hj.
    apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x12b8)
             (fun i : nat => alt_execR !!! (i + 1)%nat) 7%nat 8%nat);
      [vm_compute; reflexivity | lia].
Qed.

(* ...and [exec grep failed] *)
Lemma grep_execfail_bytes : UkShDiagAt.ush_execfail_bytes (filt_alt (FGrep [])) FileDisc.fd_w_grep.
Proof using .
  rewrite /UkShDiagAt.ush_execfail_bytes. split_and!.
  - vm_compute. lia.
  - intros j Hj.
    assert (Hl : (j < length (filt_alt (FGrep [])))%nat) by (vm_compute in Hj |- *; lia).
    exact (list_lookup_lookup_total_lt _ j Hl).
  - intros j Hj.
    apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x12b8)
             (fun i : nat => filt_alt (FGrep []) !!! i) 0%nat 5%nat);
      [vm_compute; reflexivity | lia].
  - intros j Hj.
    assert (Hj4 : (j < 4)%nat) by (vm_compute in Hj; lia).
    destruct j as [| [| [| [| j]]]]; try lia; vm_compute; reflexivity.
  - intros j Hj.
    apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x12b8)
             (fun i : nat => filt_alt (FGrep []) !!! (i + 2)%nat) 7%nat 8%nat);
      [vm_compute; reflexivity | lia].
Qed.

Lemma filt_execfail_bytes (F : filt) :
  UkShDiagAt.ush_execfail_bytes (filt_alt F) (filt_words F !!! 0%nat).
Proof using .
  destruct F as [| w]; [exact catf_execfail_bytes |].
  exact grep_execfail_bytes.
Qed.

(* ===================================================================== *)
(*  2.  THE REBASE: a node read field by field                            *)
(* ===================================================================== *)

(* two argv entries that agree field by field *)
Definition uarg_eqv (x y : uarg) : Prop :=
  UserHeap.ua_ptr x = UserHeap.ua_ptr y /\ UserHeap.ua_len x = UserHeap.ua_len y /\ forall j : nat, UserHeap.ua_bytes x j = UserHeap.ua_bytes y j.

Lemma ush_args_rebase (s0 : Z) (g : nat -> bv 8) (c : nat) (toks : list (nat * nat)) :
  Forall2 uarg_eqv (UkShMain.ush_args s0 g (ushq_rebase c toks))
    (UkShMain.ush_args (s0 + Z.of_nat c) (fun j : nat => g (c + j)%nat) toks).
Proof using .
  induction toks as [| [a b] toks IH]; [constructor |].
  cbn [ushq_rebase map UkShMain.ush_args fst snd]. constructor; [| exact IH].
  unfold uarg_eqv. cbn. split_and!.
  - lia.
  - lia.
  - intros j. f_equal. lia.
Qed.

Section ext.
  Context `{!riscvGS Σ}.

  Lemma big_sepL_Forall2_equiv {A : Type} (R : A -> A -> Prop) (Φ : nat -> A -> iProp Σ)
      (l l' : list A) :
    (forall i x y, R x y -> Φ i x ⊣⊢ Φ i y) -> Forall2 R l l' ->
    ([∗ list] i ↦ x ∈ l, Φ i x) ⊣⊢ ([∗ list] i ↦ x ∈ l', Φ i x).
  Proof using .
    intros HΦ H. revert Φ HΦ. induction H as [| x y l l' Hxy Hl IH]; intros Φ HΦ; [done |].
    rewrite !big_sepL_cons. rewrite (HΦ 0%nat x y Hxy).
    rewrite (IH (fun i => Φ (S i))); [done |]. intros i. apply HΦ.
  Qed.

  Lemma ustr_ext (g : gname) (dq : dfrac) (a : Z) (n : nat) (f f' : nat -> bv 8) :
    (forall j, f j = f' j) -> ustr g dq a n f ⊣⊢ ustr g dq a n f'.
  Proof using .
    intros Hf. rewrite /ustr /ubytesq.
    assert (E : (forall j : nat, (j < n)%nat -> f j <> ubyte0)
                <-> (forall j : nat, (j < n)%nat -> f' j <> ubyte0)).
    { split; intros H j Hj; [rewrite -Hf | rewrite Hf]; exact (H j Hj). }
    rewrite (bi.pure_iff _ _ E).
    by setoid_rewrite Hf.
  Qed.

  Lemma ush_str_ext (g : gname) (x y : uarg) : uarg_eqv x y -> ush_str g x ⊣⊢ ush_str g y.
  Proof using .
    intros (Hp & Hl & Hb). rewrite /ush_str Hp Hl. by rewrite (ustr_ext g _ _ _ _ _ Hb).
  Qed.

  Lemma uargv_ext (g : gname) (av : Z) (args args' : list uarg) :
    Forall2 uarg_eqv args args' -> uargv g av args ⊣⊢ uargv g av args'.
  Proof using .
    intros H. rewrite /uargv (Forall2_length H).
    rewrite (big_sepL_Forall2_equiv uarg_eqv
               (fun i x => uwordq g DfracDiscarded (av + 8 * Z.of_nat i) (mword_of_int (UserHeap.ua_ptr x))
                           ∗ ustr g DfracDiscarded (UserHeap.ua_ptr x) (UserHeap.ua_len x) (UserHeap.ua_bytes x))%I
               args args'); [done | | exact H].
    intros i x y (Hp & Hl & Hb). rewrite Hp Hl. by rewrite (ustr_ext g _ _ _ _ _ Hb).
  Qed.

  (* THE NODE IS READ FIELD BY FIELD *)
  Lemma ush_cmd_exec_ext (g : gname) (t : Z) (args args' : list uarg) :
    Forall2 uarg_eqv args args' -> ush_cmd g t (UExec args) ⊣⊢ ush_cmd g t (UExec args').
  Proof using .
    intros H. cbn [ush_cmd ush_ty]. rewrite (uargv_ext g _ _ _ H) (Forall2_length H).
    rewrite (big_sepL_Forall2_equiv uarg_eqv (fun _ x => ush_str g x) args args'); [done | | exact H].
    intros _ x y Hxy. exact (ush_str_ext g x y Hxy).
  Qed.

  (* ...so the node the parser built for a stage's words at their line
     offset [c] IS the word list's node at the shifted base *)
  Lemma ush_cmd_rebase (g : gname) (t s0 : Z) (gs : nat -> bv 8) (c : nat)
      (ws : list (list (bv 8))) :
    ush_cmd g t (UExec (UkShMain.ush_args s0 gs (ushq_rebase c (wl_toks ws))))
    ⊣⊢ ush_cmd g t (UkShEcho.echo_cmd ws (s0 + Z.of_nat c) (fun j : nat => gs (c + j)%nat)).
  Proof using . exact (ush_cmd_exec_ext g t _ _ (ush_args_rebase s0 gs c (wl_toks ws))). Qed.

  Lemma ush_cmd_rebase_l (g : gname) (t s0 : Z) (gs : nat -> bv 8) (c : nat)
      (ws : list (list (bv 8))) :
    ush_cmd g t (UExec (UkShMain.ush_args s0 gs (ushq_rebase c (wl_toks ws))))
    ⊢ ush_cmd g t (UkShEcho.echo_cmd ws (s0 + Z.of_nat c) (fun j : nat => gs (c + j)%nat)).
  Proof using . rewrite ush_cmd_rebase. reflexivity. Qed.
End ext.

(* ===================================================================== *)
(*  3.  THE SUPPLY, AT ANY PINNED PROGRAM                                 *)
(* ===================================================================== *)

Section UShExecPin.
  Context `{HRg : !riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.

  (* a program's SLOT: the file system's invariant, its pin (or the
     taint) at every running view, and the generic taint continuation --
     [UShCatPay.sh_cat_slot] at an abstract pin *)
  Definition sh_pin_slot (pins : aview -> Prop) (T : iProp Σ) : iProp Σ :=
    (app_inv fsc_fs
     ∗ □ (∀ v : aview, app_pred app_run v -∗
                         app_pred app_run v
                         ∗ (⌜pins v⌝ ∨ T))
     ∗ □ (∀ (R : iProp Σ) (W : uvis),
            T -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
            □ (app_taint -∗ R) -∗ uslot W))%I.

  Global Instance sh_pin_slot_persistent pins T : Persistent (sh_pin_slot pins T).
  Proof using . rewrite /sh_pin_slot. apply _. Qed.

  Lemma sh_pin_slot_cat (T : iProp Σ) : UShCatPay.sh_cat_slot T -∗ sh_pin_slot FsCatPin.era0_cat_pins T.
  Proof using . rewrite /UShCatPay.sh_cat_slot /sh_pin_slot. iIntros "$". Qed.

  (* grep's, and where it comes from: the claim's fixed part pins grep *)
  Definition sh_grep_slot (T : iProp Σ) : iProp Σ := sh_pin_slot FsGrepPin.era0_grep_pins T.

  Lemma sh_grep_slot_of_fs_pure_holds (T : iProp Σ) :
    UShCatPay.sh_cat_slot_of_fs_pure T -∗ sh_grep_slot T.
  Proof using .
    iIntros "(#Hinv & #Hcl & #Hgen)". rewrite /sh_grep_slot /sh_pin_slot.
    iFrame "Hinv Hgen". iIntros "!>" (v) "Hv".
    iDestruct ("Hcl" $! v with "Hv") as "[$ [%Hpure | HT]]".
    - iLeft. iPureIntro. exact (FileFsPure.file_fs_pure_grep v Hpure).
    - iRight. iExact "HT".
  Qed.

  (* /seccomp's (seccomp lane S4): the claim's fixed part pins it too *)
  Definition sh_secc_slot (T : iProp Σ) : iProp Σ := sh_pin_slot FsSeccPin.era0_secc_pins T.

  Global Instance sh_secc_slot_persistent T : Persistent (sh_secc_slot T).
  Proof using . rewrite /sh_secc_slot. apply _. Qed.

  Lemma sh_secc_slot_of_fs_pure_holds (T : iProp Σ) :
    UShCatPay.sh_cat_slot_of_fs_pure T -∗ sh_secc_slot T.
  Proof using .
    iIntros "(#Hinv & #Hcl & #Hgen)". rewrite /sh_secc_slot /sh_pin_slot.
    iFrame "Hinv Hgen". iIntros "!>" (v) "Hv".
    iDestruct ("Hcl" $! v with "Hv") as "[$ [%Hpure | HT]]".
    - iLeft. iPureIntro. exact (FileFsPure.file_fs_pure_secc v Hpure).
    - iRight. iExact "HT".
  Qed.

  (* a stage's program's slot, from the two *)
  Lemma sh_filt_slot (F : filt) (T : iProp Σ) :
    UShCatPay.sh_cat_slot T -∗ sh_grep_slot T -∗ sh_pin_slot (filt_pins F) T.
  Proof using .
    iIntros "#Hc #Hg". destruct F; [iApply (sh_pin_slot_cat with "Hc") | iExact "Hg"].
  Qed.

  (* THE SLOTS OF A LINE's STAGE PROGRAMS: the pin of every filter stage's
     program -- /cat's alone on an all-cat line *)
  Definition sh_stage_slots (fs : list filt) (T : iProp Σ) : iProp Σ :=
    □ (∀ F : filt, ⌜F ∈ fs⌝ -∗ sh_pin_slot (filt_pins F) T).

  Global Instance sh_stage_slots_persistent fs T : Persistent (sh_stage_slots fs T).
  Proof using . rewrite /sh_stage_slots. apply _. Qed.

  Lemma sh_stage_slots_of (fs : list filt) (T : iProp Σ) :
    UShCatPay.sh_cat_slot T -∗ sh_grep_slot T -∗ sh_stage_slots fs T.
  Proof using .
    iIntros "#Hc #Hg !>" (F _). iApply (sh_filt_slot F T with "Hc Hg").
  Qed.

  Lemma sh_stage_slots_cats (n : nat) (T : iProp Σ) :
    UShCatPay.sh_cat_slot T -∗ sh_stage_slots (FileDisc.cats n) T.
  Proof using .
    iIntros "#Hc !>" (F HF). unfold FileDisc.cats in HF.
    apply elem_of_replicate in HF as [-> _]. iApply (sh_pin_slot_cat with "Hc").
  Qed.

  Lemma sh_stage_slot_at (fs : list filt) (F : filt) (T : iProp Σ) :
    F ∈ fs -> sh_stage_slots fs T -∗ sh_pin_slot (filt_pins F) T.
  Proof using . iIntros (HF) "#Hs". iApply ("Hs" $! F with "[//]"). Qed.

  (* THE SUPPLY: sh's exec of the words [ws] (argv[0] the pinned path
     [pl]) at the caller's entry, at every image the exec can produce; the
     ledger fragment is spent at the exec, the lend is the entry's pay *)
  Lemma sh_exec_sup_x_of_entry (Fd : list fdstate -> Prop) (ws : list (list (bv 8)))
      (pl : list (bv 8)) (pins : aview -> Prop) (hops : list Z) (ino : Z) (elf : list (bv 8))
      (T : iProp Σ) `{!Persistent T} `{!Timeless T} (Qv Cr : iProp Σ) :
    exec_ok ws -> ws !!! 0%nat = pl -> kexec_loadable elf ->
    pin_resolves pins FsImg.ROOTINO pl hops ino elf 1%nat ->
    □ (∀ (M : gmap Z (bv 8)) (s0 t : Z) (gn : nat -> bv 8)
         (sts : list fdstate) (cs : gset gname) (pidv : mword 32),
         ⌜UShEcho.echo_node_img ws M s0 t gn⌝ -∗
         ⌜UkShEcho.echo_argv_bytes ws gn⌝ -∗
         ⌜length sts = NOFILE⌝ -∗
         ⌜Fd (take NSTD sts)⌝ -∗
         UkRun.urun_nopipe sts -∗
         image_entry elf M (mword_of_int (t + 8) : mword 64)
           sts FsImg.ROOTINO ProcDefs.secc_all cs pidv (fun _ : Z => Qv) Cr uslot) -∗
    □ (app_taint -∗ Qv) -∗
    sh_pin_slot pins T -∗
    UkShEcho.sh_exec_sup_echo_at (SG := uexecSG_xv6) Fd ws (fun _ : Z => Qv) Cr.
  Proof using .
    intros Hok Hhead Hload Hres.
    iIntros "#Hent #Hkt (#Hinv & #Hcl & #Hgen)".
    rewrite /UkShEcho.sh_exec_sup_echo_at.
    iIntros "!>" (N' m pc s0 t gn ld) "%Hpeq %Ha0 %Ha1 %Hbytes %Hrows Hstd #Hcmd Hcr".
    iAssert (∀ sts, image_entry_taint T sts ProcDefs.secc_all (fun _ : Z => Qv) uslot)%I as "#Hgen'".
    { iIntros (sts). iApply image_entry_taint_intro. iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! Qv W' with "HT Hmp Hkt"). }
    iApply (udepw_at_refR_of_sup N' m pc (mword_of_int s0) (mword_of_int (t + 8))
              FsImg.ROOTINO T pl elf 1%nat
              (UserFd.ustd (ukn_fd N') ld ∗ Cr)%I
              _ Hload Ha0 Ha1 with "[] [] [Hstd Hcr]").
    { iIntros "!> H". iExact "H". }
    { rewrite Hpeq. iExact "Hgen'". }
    rewrite /uexec_sup_run.
    iIntros (M pm sz fdv chs pidv) "#Hnpw Hheap Hufd".
    iDestruct (UkRun.urun_rows_nopipe _ _ with "Hnpw") as "#Hnp0".
    iAssert (⌜UShEcho.echo_node_img ws M s0 t gn⌝)%I as %Himg.
    { iApply (UShEcho.echo_node_img_of_cmd_x ws _ _ _ M pm sz s0 t gn Hok with "Hheap Hcmd"). }
    iDestruct (ufd_auth_len with "Hufd") as %Hflen.
    iDestruct (ustd_agree (ukn_fd N') fdv ld with "Hufd Hstd") as %Hl.
    iFrame "Hheap Hufd".
    iSplitR "Hstd Hcr".
    { iPureIntro. rewrite -Hhead.
      exact (UShEcho.sh_exec_path_of_x_holds ws Hok M s0 t gn Himg Hbytes). }
    iSplitR "Hstd Hcr".
    { iApply (exec_walk_of_pin pins T FsImg.ROOTINO pl hops ino (MkAnode (AFile elf) 1%nat) Hres
                with "Hcl Hinv"). }
    iSplitR "Hstd Hcr"; [ | iFrame "Hstd Hcr" ].
    rewrite Hpeq.
    iPoseProof ("Hent" $! M s0 t gn fdv chs pidv with "[%] [%] [%] [%] Hnp0") as "#He";
      [ exact Himg | exact Hbytes | exact Hflen | rewrite Hl; exact Hrows | ].
    iApply (UShEchoPipePay.image_entry_pay_mono elf M
              (mword_of_int (t + 8) : mword 64) fdv FsImg.ROOTINO ProcDefs.secc_all chs pidv
              (fun _ : Z => Qv) Cr (UserFd.ustd (ukn_fd N') ld ∗ Cr)%I uslot with "[] He").
    iIntros "!> [_ Hc]". iExact "Hc".
  Qed.

  (* ...AT THE PARENT'S VIEW (seccomp lane S4): the ledger the exec spends
     names the table's view [v], and the entry is asked for only at a
     table under it -- which is how a [seccomp x] child learns its rows *)
  Lemma sh_exec_sup_x_of_entry_v (Fd : list fdstate -> Prop) (ws : list (list (bv 8)))
      (pl : list (bv 8)) (pins : aview -> Prop) (hops : list Z) (ino : Z) (elf : list (bv 8))
      (T : iProp Σ) `{!Persistent T} `{!Timeless T} (Qv Cr : iProp Σ) (v : list fdstate) :
    exec_ok ws -> ws !!! 0%nat = pl -> kexec_loadable elf ->
    pin_resolves pins FsImg.ROOTINO pl hops ino elf 1%nat ->
    □ (∀ (M : gmap Z (bv 8)) (s0 t : Z) (gn : nat -> bv 8)
         (sts : list fdstate) (cs : gset gname) (pidv : mword 32),
         ⌜UShEcho.echo_node_img ws M s0 t gn⌝ -∗
         ⌜UkShEcho.echo_argv_bytes ws gn⌝ -∗
         ⌜length sts = NOFILE⌝ -∗
         ⌜Fd (take NSTD sts)⌝ -∗
         ⌜tab_le sts v⌝ -∗
         UkRun.urun_nopipe sts -∗
         image_entry elf M (mword_of_int (t + 8) : mword 64)
           sts FsImg.ROOTINO ProcDefs.secc_all cs pidv (fun _ : Z => Qv) Cr uslot) -∗
    □ (app_taint -∗ Qv) -∗
    sh_pin_slot pins T -∗
    UkShEcho.sh_exec_sup_echo_at_v (SG := uexecSG_xv6) Fd ws (fun _ : Z => Qv) Cr v.
  Proof using .
    intros Hok Hhead Hload Hres.
    iIntros "#Hent #Hkt (#Hinv & #Hcl & #Hgen)".
    rewrite /UkShEcho.sh_exec_sup_echo_at_v.
    iIntros "!>" (N' m pc s0 t gn ld) "%Hpeq %Ha0 %Ha1 %Hbytes %Hrows Hstd #Hcmd Hcr".
    iAssert (∀ sts, image_entry_taint T sts ProcDefs.secc_all (fun _ : Z => Qv) uslot)%I as "#Hgen'".
    { iIntros (sts). iApply image_entry_taint_intro. iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! Qv W' with "HT Hmp Hkt"). }
    iApply (udepw_at_refR_of_sup N' m pc (mword_of_int s0) (mword_of_int (t + 8))
              FsImg.ROOTINO T pl elf 1%nat
              (UserFd.ustd_at (ukn_fd N') ld v ∗ Cr)%I
              _ Hload Ha0 Ha1 with "[] [] [Hstd Hcr]").
    { iIntros "!> H". iExact "H". }
    { rewrite Hpeq. iExact "Hgen'". }
    rewrite /uexec_sup_run.
    iIntros (M pm sz fdv chs pidv) "#Hnpw Hheap Hufd".
    iDestruct (UkRun.urun_rows_nopipe _ _ with "Hnpw") as "#Hnp0".
    iAssert (⌜UShEcho.echo_node_img ws M s0 t gn⌝)%I as %Himg.
    { iApply (UShEcho.echo_node_img_of_cmd_x ws _ _ _ M pm sz s0 t gn Hok with "Hheap Hcmd"). }
    iDestruct (ufd_auth_len with "Hufd") as %Hflen.
    iDestruct (ustd_at_agree (ukn_fd N') fdv ld v with "Hufd Hstd") as %Hl.
    iDestruct (ustd_at_tab (ukn_fd N') fdv ld v with "Hufd Hstd") as %Htab.
    iFrame "Hheap Hufd".
    iSplitR "Hstd Hcr".
    { iPureIntro. rewrite -Hhead.
      exact (UShEcho.sh_exec_path_of_x_holds ws Hok M s0 t gn Himg Hbytes). }
    iSplitR "Hstd Hcr".
    { iApply (exec_walk_of_pin pins T FsImg.ROOTINO pl hops ino (MkAnode (AFile elf) 1%nat) Hres
                with "Hcl Hinv"). }
    iSplitR "Hstd Hcr"; [ | iFrame "Hstd Hcr" ].
    rewrite Hpeq.
    iPoseProof ("Hent" $! M s0 t gn fdv chs pidv with "[%] [%] [%] [%] [%] Hnp0") as "#He";
      [ exact Himg | exact Hbytes | exact Hflen | rewrite Hl; exact Hrows | exact Htab | ].
    iApply (UShEchoPipePay.image_entry_pay_mono elf M
              (mword_of_int (t + 8) : mword 64) fdv FsImg.ROOTINO ProcDefs.secc_all chs pidv
              (fun _ : Z => Qv) Cr (UserFd.ustd_at (ukn_fd N') ld v ∗ Cr)%I uslot with "[] He").
    iIntros "!> [_ Hc]". iExact "Hc".
  Qed.

  (* ...AT A FILTER STAGE's program *)
  Lemma sh_exec_sup_filt_of_entry (Fd : list fdstate -> Prop) (F : filt)
      (T : iProp Σ) `{!Persistent T} `{!Timeless T} (Qv Cr : iProp Σ) :
    exec_ok (filt_words F) ->
    □ (∀ (M : gmap Z (bv 8)) (s0 t : Z) (gn : nat -> bv 8)
         (sts : list fdstate) (cs : gset gname) (pidv : mword 32),
         ⌜UShEcho.echo_node_img (filt_words F) M s0 t gn⌝ -∗
         ⌜UkShEcho.echo_argv_bytes (filt_words F) gn⌝ -∗
         ⌜length sts = NOFILE⌝ -∗
         ⌜Fd (take NSTD sts)⌝ -∗
         UkRun.urun_nopipe sts -∗
         image_entry (filt_elf F) M (mword_of_int (t + 8) : mword 64)
           sts FsImg.ROOTINO ProcDefs.secc_all cs pidv (fun _ : Z => Qv) Cr uslot) -∗
    □ (app_taint -∗ Qv) -∗
    sh_pin_slot (filt_pins F) T -∗
    UkShEcho.sh_exec_sup_echo_at (SG := uexecSG_xv6) Fd (filt_words F) (fun _ : Z => Qv) Cr.
  Proof using .
    intros Hok. iIntros "#Hent #Hkt #Hslot".
    iApply (sh_exec_sup_x_of_entry Fd (filt_words F) (filt_pl F) (filt_pins F)
              [FsImg.ROOTINO; filt_ino F] (filt_ino F) (filt_elf F) T Qv Cr Hok
              (filt_words_head F) (filt_elf_loadable F) (filt_pin_resolves F)
              with "Hent Hkt Hslot").
  Qed.
End UShExecPin.
