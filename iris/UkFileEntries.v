(* ===================================================================== *)
(* UkFileEntries.v -- THE FILE APPLICATION'S PROGRAM ENTRIES FROM THE     *)
(* TREE ROUTE (program-specs cut 5, lane E): the entries the round        *)
(* consumes, reproduced as corollaries of the entries at a handler        *)
(* parameter ([UkTreeEntry]) at the file application's instance          *)
(* ([UkFileIface.file_iface]) and its exit wand ([fif_exit_k]).           *)
(*                                                                        *)
(* Design: claude-notes/design/program-specs.md SS3.4e.  Nothing here is  *)
(* consumed yet; the round still applies the landed entries.              *)
(*                                                                        *)
(* THE INTERFACE AT A CONSTANT PAYLOAD.  [file_iface] exists only at a   *)
(* record whose payload is status-independent (its [ukn_const N] binder: *)
(* the free handler and the exit spend the payload at the kill status),  *)
(* so the entries are [UkTreeEntry]'s [_c] forms, whose interface reads   *)
(* the pay fact, and the record's constancy is [ukn_const_of_eq] off it   *)
(* and the constancy of [Q] every landed entry states.                    *)
(*                                                                        *)
(* THE REGISTRY IS BORN AT THE ENTRY.  [file_iface] is indexed by its    *)
(* registry's name, and nothing the round lends carries one, so each      *)
(* corollary allocates it inside the slot ([UexecRet.uslot_bupd]) and     *)
(* hands its whole pool to the environment beside the landed payment.    *)
(* That is the one CLASS the statements gain ([fifRegG]).                 *)
(*                                                                        *)
(* WHAT IS HERE: cat f at the landed statement plus two pure facts      *)
(* (section 2); echo at the console at the file application's record     *)
(* (section 3: the landed entry is generic in the era's link record, and *)
(* the exit glue has to hand the round's deed back); and echo > f at the  *)
(* instance's WRITE MODE, where the core holds no deed (section 4, lane   *)
(* DEED-SPLIT).                                                           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras Xv6G FdSlots IrefSlots ProcAvail FileInvDefs.
Require Import ProcGeom.              (* [NOFILE] *)
Require Import UserPerm UexecSlot UexecRet UexecSG.
Require Import UserHeap UkRun.
Require Import UserFd UserCwd.
Require Import ChildTok.
Require Import ElfFile ElfUser.
Require Import UmodeArith UmodeAbi.
Require Import SpecKexec.             (* [kexec_image_ok] and its readings *)
Require Import ExecEntry.             (* [image_entry] / [image_entry_of_at] *)
Require Import UexecExecInst.         (* THE INSTANCES: [uexecSG_xv6] *)
Require Import UkAbi.                 (* [uka_argc] *)
Require Import UCodeEcho UCodeCat.
From User Require EchoInstrs EchoData.
Require Import UEchoKernel.           (* [uvis_sp] / [uvis_av] / [uvis_argc], [echo_args] *)
Require Import UShKernel.             (* [uimg_sub_union_l] *)
Require Import LineWords EchoDisc ExecWords.
Require Import UkShEcho.              (* [echo_argv_bytes] / [echo_alen] / [echo_off] *)
Require Import UShEcho.               (* echo's key geometry *)
Require Import UEchoOut.              (* [echo_out_argv] *)
Require Import UShEchoOut.            (* [echo_out_argv_of_image] *)
Require Import UShCat.                (* cat's key geometry and [cat_entry_run] *)
Require Import FsImgCheck.            (* [fname_f] *)
Require Import ProgTree UkTree UkStub UkHandler.
Require Import UkEcho UkEchoTree.
Require Import UkCatMain UkCatTree.
Require Import UkTreeEntry.           (* the argv bridges, the .rodata fact *)
Require Import CtxIdDefs.
Require User.EchoSyms User.CatSyms.
Require Import AppCfg AppInv AppFile AppFileCons FileOpen FsCfg FsImg.
Require Import EchoOut.               (* [ps_lb] / [cs_lb] and their comparisons *)
Require Import FileState FileDisc FileOut.
Require Import LineModel LineModelInst LineModelLinks.
Require Import FileLinks FileLinksLine FileLinkGen FileHooks.
Require Import GenLinksLine.          (* [gwc_blk] / [gwc_post] *)
Require Import ConsoleInv.             (* [CONSOLE] *)
Require Import UkConsOut ProgTreeFile.
Require Import UCatOut UCatLend.      (* [cch], [catq_cat], [cat_lend] *)
Require Import FsInitPin FsShPin FsEchoPin FsCatPin.   (* the four image inodes *)
Require Import UkFileDev FileWrite UEchoFile.         (* [file_out], [ef_pay], [ef_exit] *)
Require Import UkFileIface.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  2.  cat f FROM THE TREE                                                *)
(* ===================================================================== *)

Section UkFileEntriesCat.
  (* cat's entry binders (the deleted [UCatKernel]'s), and the registry's
     class *)
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context `{!fifRegG Σ}.
  Context (g : file_gn).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = fecl g).

  Local Instance fe_cat_code_persistent (N : uk_names Σ) :
    Persistent (up_code (cat_prog N)).
  Proof using . simpl. apply _. Qed.

End UkFileEntriesCat.

(* ===================================================================== *)
(*  3.  echo AT THE CONSOLE FROM THE TREE, at the file application        *)
(*                                                                       *)
(*  The landed entry the round runs echo at the console on is            *)
(*  [UShEchoPay.echo_slot_of_kexec_at_at] (through                        *)
(*  [sh_exec_sup_echo_wq_holds_at_D], which [UShRound.Hchild_echo] is    *)
(*  one application of), and it is GENERIC in the era's link record: no  *)
(*  application's instance can reproduce it.  What the tree route gives  *)
(*  is its image slot at the FILE application's record                   *)
(*  ([FileLinkInst.file_link_inst_at]: the lend is [gwc_blk] at the      *)
(*  state-pinned parameters, the block's end [gwc_post] there), with the *)
(*  resource that rides beside the cursor -- sh's deed fraction, the     *)
(*  round's [Hold] -- handed in and handed BACK at the exit.             *)
(*                                                                       *)
(*  The handing back is the point: the core's deed is, at this round,    *)
(*  sh's own and must come back for the round's next prompt credential.  *)
(*  So the glue passes the deed to the round's wand beside the post.      *)
(* ===================================================================== *)

Section UkFileEntriesEcho.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context `{!fifRegG Σ}.
  Context (g : file_gn).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = fecl g).

  Local Instance fe_echo_code_persistent (N : uk_names Σ) :
    Persistent (up_code (echo_prog N)).
  Proof using . simpl. apply _. Qed.

End UkFileEntriesEcho.

(* ===================================================================== *)
(*  4.  echo > f FROM THE TREE                                             *)
(*                                                                       *)
(*  At the WRITE MODE of the instance (lane DEED-SPLIT: the entry device *)
(*  is `f` held for writing, [UkFileIface.fif_wr]) the core holds no     *)
(*  deed, so the redirect child's lend -- the era's credential [Wq] and   *)
(*  the cursor [efq] at no chunk, whose [file_wq] carries the child's     *)
(*  whole share -- is exactly what the environment needs: the cursor is  *)
(*  the write device at chunk 0, [Wq] rides in the exit wand            *)
(*  ([UkFileIface.fif_exit_k_redir]), and the core's deed and cred are    *)
(*  [emp]/[True].  The statement is the landed one's plus what the free   *)
(*  handler and the instance's core read (listed at the lemma).          *)
(* ===================================================================== *)

(* the line's pure facts the tree route reads off [line_ok] *)
Lemma efe_drop1_ne (ws : list (list (bv 8))) : EchoDisc.line_ok ws -> drop 1 ws <> [].
Proof.
  intros Hl Hd. pose proof (line_ok_ge2 ws Hl) as H2.
  apply (f_equal length) in Hd. rewrite length_drop in Hd. simpl in Hd. lia.
Qed.

Lemma efe_words_nn (ws : list (list (bv 8))) :
  EchoDisc.line_ok ws -> Forall (fun w => w <> []) (drop 1 ws).
Proof.
  intros Hl.
  pose proof (line_ok_wf ws Hl) as Hwf. unfold wl_wf in Hwf.
  apply (Forall_drop _ 1) in Hwf.
  apply (proj2 (Forall_forall (fun w : list (bv 8) => w <> []) (drop 1 ws))).
  intros w Hw Heq. subst w.
  pose proof (wl_word_pos [] (proj1 (Forall_forall _ _) Hwf [] Hw)) as H. simpl in H. lia.
Qed.

Lemma efe_args_chunks_short (n : nat) (args : list (list (bv 8))) :
  (1 <= n)%nat -> Forall (fun a => (length a <= n)%nat) args ->
  Forall (fun ch => (length ch <= n)%nat) (echo_args_chunks args).
Proof.
  intros Hn. induction args as [| a rest IH]; intros Hf; [constructor |].
  apply Forall_cons_1 in Hf as [Ha Hr].
  destruct rest as [| a' rest'].
  - cbn [echo_args_chunks]. constructor; [exact Ha |].
    constructor; [simpl; lia | constructor].
  - change (echo_args_chunks (a :: a' :: rest'))
      with (a :: [wl_sp] :: echo_args_chunks (a' :: rest')).
    constructor; [exact Ha |]. constructor; [simpl; lia |]. exact (IH Hr).
Qed.

Lemma efe_chunks_short (ws : list (list (bv 8))) :
  EchoDisc.line_ok ws ->
  Forall (fun ch => (length ch <= EchoDisc.line_max)%nat) (echo_chunks ws).
Proof.
  intros Hl. unfold echo_chunks.
  apply efe_args_chunks_short; [unfold EchoDisc.line_max; lia |].
  apply Forall_lookup. intros k w Hk. rewrite lookup_drop in Hk.
  pose proof (wl_off_lt_line ws (1 + k) w (length w) Hk ltac:(lia)) as H.
  destruct Hl as (_ & _ & _ & _ & Hlen). lia.
Qed.

Section UkFileEntriesRedir.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context `{!fifRegG Σ}.
  Context (g : file_gn).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = fecl g).

  Local Instance fe_redir_code_persistent (N : uk_names Σ) :
    Persistent (up_code (echo_prog N)).
  Proof using . simpl. apply _. Qed.

End UkFileEntriesRedir.
