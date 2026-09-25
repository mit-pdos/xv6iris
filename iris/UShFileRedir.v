(* ===================================================================== *)
(*  UShFileRedir.v -- THE REDIRECT CHILD'S OPEN, AT THE FILE CLAIM        *)
(*                                                                       *)
(*  What the union's round ([UShURound] / [UShURoundDefs]) takes from the *)
(*  retired file round, moved here verbatim when that was deleted (union  *)
(*  cut C9h): the model-free pure facts about [FileDisc.fsm] and the      *)
(*  words' line length, and the redirect child's open -- its receipt      *)
(*  [redir_K] / [redir_Kf], the receipt read against the claim            *)
(*  ([redir_K_inum], [redir_K']), and sh's open stub walked into the      *)
(*  kernel's create corollary ([Hopen_hand]).  All of it is about         *)
(*  [AppFile.file_pred] at a [file_gn]; the claim equation is a section   *)
(*  parameter.                                                           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserChildren.
Require Import UmodeAbi.
Require Import ProcGeom.
Require Import UexecRet.
Require Import ExecEntry.
Require Import UkRun UkRunSys.
Require Import UkRunLeaf.                (* [wp_uk_cli] / [wp_uk_cjr]: the stub *)
Require Import UexecExecInst.            (* THE INSTANCES *)
Require Import WpUart.
Require Import FsCfg.
Require Import FsImg.
Require Import FsImgCheck.
Require Import FsInitPin.                (* [INIT_INO] *)
Require Import FsShPin.                  (* [SH_INO] *)
Require Import FsEchoPin.                (* [ECHO_INO] *)
Require Import FsCatPin.                 (* [CAT_INO] *)
Require Import FsGrepPin.                (* [GREP_INO] *)
Require Import AppFileCons.              (* the claim's readings *)
Require Import AppCfg.
Require Import AppInv.
Require Import LineWords.
Require Import EchoDisc.
Require Import EchoOut.
Require Import FileDisc.
Require Import FileOutPure.
Require Import FileState.
Require Import AppEcho.
Require Import AppFile.
Require FileDisc.                        (* [uname] *)
Require Import FileOut.
Require Import FileLinks.
Require Import FileOpen.                 (* [fdq], [file_open_pay] *)
Require Import FileWrite.                (* [file_wq]: what the ran exit reads back *)
Require Import UEchoFile.                (* [ef_pay] / [efq]: echo at a file *)
Require Import FsAbsDefs.                (* [anode] / [MkAnode] / [AFile] *)
Require Import ExecRun.                  (* [udepw_at_refR_of_sup]: the U-tier exec rule *)
Require Import UkShRedirBody.            (* [ushs_fd1f], [sh_redir_child_law] *)
Require Import UkShRedirChild.           (* the redirect child's walk, 0x9c0 to its exits *)
Require Import ExecWords.                (* [exec_ok]: a word list sh can exec *)
Require Import UkShDiagAt.               (* [ush_execfail_bytes] *)
Require Import UShCat.                   (* [cat_elf_loadable] *)
Require Import UShCatPay.                (* [sh_cat_slot], [cat_pl], [sh_cat_pin_resolves] *)
Require Import UserOff.
Require Import ElfUser.
Require Import UkSh.
Require Import UkShDiag.
Require Import UkShLoop.
Require Import UShLexRedir.  (* [ush_line_lexable_redir_holds] -- the
                                redirect line's lexability, PROVED *)
Require Import UCodeShK.
Require Import UkShRedirAns.
Require Import UkShEcho.
Require Import UkShFork.
Require Import UkFileOpen.
Require Import SysOpenDefs.              (* [om_readable] / [om_writable] *)
Require Import LinkRec.                  (* the era's link record *)
Require Import FileLinksLine.            (* [fline] / [fexfb] -- the era's line *)
Require Import FileHooks.         (* S0 of [FileLinksLine], moved *)
Require Import StageRec.                 (* [ck_lineok] / [sk_apr0] *)
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenLinksLine.
Require Import UShLineHold.              (* [ush_wb_inp_hold] *)
Require Import UShPanicHold.             (* the prompt law with a frame; [ksh_w_mono] *)
Require Import UShLine.
Require Import UShEcho.
Require Import UShPanic.          (* the panic and exec-failed laws at a record *)
Require Import UShKernel.
Require Import UInitSh.
Require Import UCatOut.                  (* [cat_tie] -- the pure round tie *)
Require Import UCatLend.          (* [catq_cat] / [cat_lend] *)
Require UkFileIface.                     (* [fifRegG]: the binder below needs it in scope *)
Require FileDeltas.                      (* [f_bytes_typed_short] *)
Require Import CtxIdDefs.
Local Open Scope Z_scope.
Import Defs.

(* a panic alternative moves no file, at any line *)
Lemma fsm_panic (s : fstate) (l : uline) (a : ralt) :
  ralt_panic a = true -> fsm s l a = s.
Proof using .
  intro H. destruct l as [ws | ws Nf | Nf | ws | ws];
    [ reflexivity | | reflexivity | reflexivity | reflexivity ].
  destruct a; try reflexivity; cbn [ralt_panic] in H; discriminate H.
Qed.

(* the line's silent alternative moves no file -- at a redirect line this
   IS the model fix of RULING HOLD-POS ([RFSilent]'s effect is identity) *)
Lemma fsm_fnoc (s : fstate) (l : uline) : fsm s l (ralt_dec (fnoc_of l)) = s.
Proof using .
  destruct l as [ws | ws Nf | Nf | ws | ws]; cbn [fnoc_of];
    [ reflexivity | by rewrite (ralt_dec_enc RFSilent)
    | reflexivity | reflexivity | reflexivity ].
Qed.

(* the words' line after the command fits a C int (the console write's
   count) -- [UkPipeEntries.pe_line_len], restated here to keep the round
   off the pipeline's cone *)
Lemma ush_line_len (ws : list (list (bv 8))) :
  EchoDisc.line_ok ws -> Z.of_nat (length (wl_line (drop 1 ws))) < 2 ^ 31.
Proof using .
  intros Hok. pose proof (EchoDisc.line_ok_len ws Hok) as Hl.
  unfold EchoDisc.line_max in Hl.
  assert (Hcn : forall (w : list (bv 8)) (r : list (list (bv 8))),
             (length (wl_line r) <= length (wl_line (w :: r)))%nat).
  { intros w r. rewrite !wl_line_length wl_body_cons length_app.
    destruct r as [| w' r'].
    - cbn. lia.
    - rewrite wl_tail_cons. cbn [length]. lia. }
  assert (Hle : (length (wl_line (drop 1 ws)) <= length (wl_line ws))%nat).
  { destruct ws as [| w r]; [reflexivity |].
    replace (drop 1 (w :: r)) with r by reflexivity. apply Hcn. }
  lia.
Qed.

Section UShFileRedir.
  (* the retired file round's binder list VERBATIM (durable-notes: a
     shorter list makes Coq synthesise an instance and the elaboration
     explodes).  NO [uexecSG] and NO [uprogSG] SECTION VARIABLE. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  (* NO [ghost_varG Σ Z] BINDER (2026-09-22; durable-notes, "A section
     variable of a class type is a LOCAL INSTANCE").  The binder list
     this was copied from declared one, and it was a SECOND instance beside
     [Xv6Cameras.offbox_offG] (through [xv6G]): the redirect and cat
     children had to be pinned at [offbox_offG] for the kernel's [ucwd],
     while the echo child, the kill law and the panic law elaborated at the
     section variable -- and the round, which feeds all five to one lemma,
     hung on the mismatch.  With the binder gone there is one instance in
     scope and the explicit [(ghost_varG0 := offbox_offG)] pins below name
     it. *)
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  (* the tree route's device registry ([UkFileIface]): the three entries
     the children run allocate it inside their slot *)
  Context `{HfifR : !UkFileIface.fifRegG Σ}.

  (* the era's record: [FileOut]'s gname pair, and the deed's names *)
  Context (g : file_gn) (r : file_names).
  Context (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r).

  Local Notation T := (file_taint (fgn_cl g)).
  (* ---- the redirect child's open receipt, on both arms ---- *)
  (* [UkShRedirAns.ush_open_ans2]'s two payload slots, at this claim.  [K]
     is the fd arm's -- the descriptor's TYPE, `f` present and EMPTY at it,
     AND the program's own half of the offset shadow at ZERO, which is what
     lane OFF-LINK's publish hands out and what K1's entry asks for.  [Kf]
     is the [-1] arm's and is NOT [emp]: the create may have fired before
     [filealloc] failed. *)
  (* RESTATED BY THE KERNEL STREAM at the kernel's own payload.  It was
     [∃ i γo om, ⌜ty = FdInode i γo om⌝ ∗ fown r (Some (i, [])) ∗ uoff γo 0]:
     the mode existential is right, but the TAINT ARM was missing, and the
     open leaf cannot drop it -- a tainted claim promises nothing about the
     file system and cannot refute the kernel's [FdDevice] arm
     ([FileOpen]'s note at [file_open_fd_K]).  [UkFileOpen.redir_K OffHeld]
     IS that statement, and it is what
     [UkFileOpen.wp_uk_ecall_open_create_deed_d] at [OffHeld] hands back. *)
  (* ...at the deed's map [s] the call was made at (cut W2) and the name
     [nm] the line redirects to (cut W3): the fd arm leaves the deed at
     [s] with [nm] present and empty *)
  Definition redir_K (nm : list (bv 8)) (s : dst) (ty : fdtype) : iProp Σ :=
    UkFileOpen.redir_K OffHeld (fgn_cl g) r nm s ty.

  (* ...AND THE [-1] ARM'S, WITH THE TAINT (the PROGRAM STREAM): the
     kernel's own payload is [FileOpen.file_open_pay], whose third arm is
     the era's taint -- a failed open at a tainted application hands back
     no deed, and a [Kf] without that arm cannot be produced. *)
  Definition redir_Kf (nm : list (bv 8)) (s : dst) : iProp Σ :=
    (fown r s
     ∨ (⌜s !! nm = None⌝
        ∗ ∃ i : Z, fown r (<[nm := (i, [])]> s))
     ∨ T)%I.

  (* ---- WHAT THE OPEN'S RECEIPT SAYS ABOUT THE INODE (the PROGRAM
          STREAM, item (3)'s first premise).  K1's entry takes four
          inequalities -- `f`'s inode is not /init's, sh's, /echo's or
          cat's -- and they are the CLAIM's fact and not the open's: the
          deed pins `f`'s row, the image inodes' rows are pinned by
          [FileFsPure.file_fs_pure], and the contents differ by LENGTH.
          [AppFileCons.file_deed_inum_acc] is that reading; this is the one
          invariant opening that turns the receipt into it. ---- *)
  Lemma redir_K_inum (nm : list (bv 8)) (s : dst) (ty : fdtype) (E : coPset) :
    ↑appN ⊆ E ->
    app_inv fsc_fs -∗ redir_K nm s ty ={E}=∗
      redir_K nm s ty ∗
      ((∃ (i : Z) (γo : gname),
          ⌜ty = FdInode i γo OffHeld⌝
          ∗ ⌜i <> INIT_INO /\ i <> SH_INO /\ i <> ECHO_INO
             /\ i <> CAT_INO /\ i <> GREP_INO⌝)
       ∨ T).
  Proof using Heq.
    intros HE. iIntros "#Hinv HK".
    rewrite /redir_K /UkFileOpen.redir_K /FileOpen.file_open_fd_K.
    iDestruct "HK" as "[HK | #HT]"; last first.
    { iModIntro. iSplitR; [ by iRight | by iRight ]. }
    iDestruct "HK" as (i γo) "(%Hty & [Hd Htk] & Hpub)".
    iMod (inv_acc E appN with "Hinv") as "[Hbody Hclose]"; [ exact HE | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I0) "(>Hka & Hp & >%Hdom & #Hx)".
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iDestruct "Hp" as ">Hp".
    iDestruct (AppFileCons.file_deed_inum_acc (fgn_cl g) r _
                 (<[nm := (i, [])]> s) nm i []
                 (lookup_insert _ _ _)
                 ltac:(cbn [length]; rewrite /EchoDisc.line_max; lia)
                 with "Hd Hp") as "(Hp & Hd & Hres)".
    iMod ("Hclose" with "[Hka Hp Hx]") as "_".
    { iNext. rewrite /app_body. iExists I0. iFrame "Hka Hx".
      iSplitL; [ | by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names]. iExact "Hp". }
    iModIntro. iSplitL "Hd Htk Hpub".
    { iLeft. iExists i, γo. iFrame "Hpub Hd Htk". by iPureIntro. }
    iDestruct "Hres" as "[%Hne | #Ht]"; [ | by iRight ].
    iLeft. iExists i, γo. iSplitR; by iPureIntro.
  Qed.

  (* ---- NOT A HYPOTHESIS ANY MORE (the PROGRAM STREAM): sh's open STUB,
          walked into the kernel's create corollary at [OffHeld].

          THE STATEMENT HAD TO BE FIXED FIRST, and that is the whole of
          what was wrong with it: [ush_open_call2] was handed [a0 = file],
          an ADDRESS, and NOTHING about the bytes there or about the cwd,
          while the kernel resolves a PATH -- so as stated the hypothesis
          was not provable by anyone, and assuming it assumed something
          false.  It now takes the name as the image the ecall reads, the
          three path facts, and the ledger's own answer (fd 1 is the lowest
          closed slot, which is true of the redirect child's table because
          it closed fd 1 before calling).  Every one of them is a fact the
          CALLER has: sh's cwd is the root for the whole era, and the
          line's bytes are in its own buffer at the lexed offset.

          The walk is usys.S's three-instruction stub, [UShConsK.
          sh_open_console_leaf_holds]'s mould with the file leaf in the
          middle: [c.li a7,15] at 0xcc6, [ecall] at 0xcc8, [c.jr ra] at
          0xccc. ---- *)
  (* ---- NOT A HYPOTHESIS ANY MORE (the PROGRAM STREAM): sh's open STUB,
          walked into the kernel's create corollary at [OffHeld].

          THE STATEMENT HAD TO BE FIXED FIRST: [ush_open_call2] was handed
          [a0 = file], an ADDRESS, and NOTHING about the bytes there or
          about the cwd, while the kernel resolves a PATH -- so as stated
          nobody could prove it.  It now takes the name as the image the
          ecall reads, the three path facts, and the ledger's own answer
          (fd 1 is the lowest closed slot, true of the redirect child's
          table because it closed fd 1 before calling).  Every one is a
          fact the CALLER has: sh's cwd is the root for the whole era and
          the line's bytes are in its own buffer at the lexed offset.

          AND THE DEPOSIT INSTANCE HAD TO BE NAMED: [UkFileOpen]'s create
          corollary was at the AMBIENT [uprogSG_gen] while sh's redirect
          child runs at [uprogSG_free], whose record shares neither field
          -- so it now takes the instance per lemma, and this walk names
          [uprogSG_free].

          The walk itself is usys.S's three-instruction stub, [UShConsK.
          sh_open_console_leaf_holds]'s mould with the file leaf in the
          middle: [c.li a7,15] at 0xcc6, [ecall] at 0xcc8, [c.jr ra] at
          0xccc. ---- *)
  Local Lemma sh_open_stub_pc : User.ShSyms.open = 0xcc6.
  Proof using .
    destruct UCodeShK.shk_syms_pins as (_&_&_&_&_&H&_&_&_&_). exact H.
  Qed.

  Local Lemma ucallee_saved_a0a7 (m : regfile) (rv : mword 64) :
    ucallee_saved m
      (<[Regidx (mword_of_int 10 : mword 5) := rv]>
         (<[Regidx (mword_of_int 17 : mword 5)
            := (mword_of_int 15 : mword 64)]> m)).
  Proof using .
    intros rr Hrr.
    destruct (decide (rr = (mword_of_int 10 : mword 5))) as [-> | Hne0].
    { exfalso. vm_compute in Hrr. discriminate Hrr. }
    destruct (decide (rr = (mword_of_int 17 : mword 5))) as [-> | Hne7].
    { exfalso. vm_compute in Hrr. discriminate Hrr. }
    rewrite (upd_ne _ (Regidx (mword_of_int 10 : mword 5)) (Regidx rr) rv
               ltac:(intro He; apply Hne0; injection He as He'; by rewrite He')).
    rewrite (upd_ne m (Regidx (mword_of_int 17 : mword 5)) (Regidx rr)
               (mword_of_int 15 : mword 64)
               ltac:(intro He; apply Hne7; injection He as He'; by rewrite He')).
    reflexivity.
  Qed.

  (* ...AND THE DEED IS HANDED AT THE CALL (stretch 9): the call resource
     is built from PERSISTENT facts alone, so the child can hold it across
     the parse with its lend whole, and the deed flows lend -> call ->
     receipt ([UkShRedirAns.ush_open_call2]'s [Dd]). *)
  Lemma Hopen_hand (N : uk_names Σ) (file : Z) (l : list fdstate) (s0 : dst)
      (ls : list fwline) (ws : wordline) (jo : option Z) (nm : list (bv 8)) :
    FileDisc.uname nm ->
    (nm, ws) ∈ ls -> EchoDisc.line_ok ws ->
    app_inv fsc_fs -∗ file_cons_cred (fgn_cl g) r jo -∗ fl_lb (fgn_cl g) ls -∗
    (* ...AND THE CWD'S CAMERA IS PINNED TOO (the PROGRAM STREAM's rule,
       one class further out than the deposit): [UserCwd.ucwd] takes a
       [ghost_varG Σ Z], [UkShRedirAns]'s section has its own and the
       KERNEL's files read the one the whole-system record carries
       ([Xv6Cameras.offbox_offG] off [Xv6G.xv6_offbox]).  Both are in scope
       here, resolution picks the section variable, and the two print
       identically -- so the open leaf's [ucwd] and this call's are not the
       same proposition unless this says which. *)
    UkShRedirAns.ush_open_call2 (PS := uprogSG_free) (SG := uexecSG_xv6)
      (ghost_varG0 := offbox_offG) (A := unit)
      N FsImg.ROOTINO file 1537 nm l (redir_K nm s0) (fun _ => fown r s0)
      (fun _ => redir_Kf nm s0).
  Proof using Heq.
    intros Hu Hin Hokw. iIntros "#Hinv #Hmade #Hlb".
    rewrite /UkShRedirAns.ush_open_call2.
    iIntros (h m av Img pl u) "%Ha0 %Ha1 %Hpath %Hnp %Hstart %Hlast %Hfdl
             #Himg Hown #Hcode Hcwd Hstd Hrun Hcont".
    rewrite sh_open_stub_pc.
    (* ---- 0xcc6  c.li a7,15 ---- *)
    iApply (wp_uk_cli (PS := uprogSG_free) (SG := uexecSG_xv6)
              (ghost_varG0 := offbox_offG) N h m (mword_of_int 0xcc6)
              (mword_of_int 15 : mword 6) (mword_of_int 17 : mword 5) av
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (UCodeShK.uis_shk_cc6 with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0xcc6 : mword 64) 2
                 = mword_of_int 0xcc8)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx (mword_of_int 17 : mword 5)
                   := regval_into_reg
                        (sign_extend' 64 (mword_of_int 15 : mword 6)
                         : mword 64)]> m
                 = <[Regidx (mword_of_int 17 : mword 5)
                     := (mword_of_int 15 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx (mword_of_int 17 : mword 5)
                 := (mword_of_int 15 : mword 64)]> m).
    assert (Ha0' : m1 !!! Regidx (mword_of_int 10 : mword 5)
                   = (mword_of_int file : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx (mword_of_int 17 : mword 5))
                 (Regidx (mword_of_int 10 : mword 5))
                 (mword_of_int 15 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha0. }
    assert (Ha1' : m1 !!! Regidx (mword_of_int 11 : mword 5)
                   = (mword_of_int 1537 : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx (mword_of_int 17 : mword 5))
                 (Regidx (mword_of_int 11 : mword 5))
                 (mword_of_int 15 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha1. }
    (* ---- 0xcc8  ecall -- the DEED's create corollary at [OffHeld] ---- *)
    iApply (UkFileOpen.wp_uk_ecall_open_create_deed_d (PSx := uprogSG_free)
              N OffHeld h1 m1 (mword_of_int 0xcc8) l av (fgn_cl g) r jo
              nm s0
              ls ws FsImg.ROOTINO Img (mword_of_int file : mword 64) pl
              Hu Heq
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx (mword_of_int 17 : mword 5))
                               (mword_of_int 15 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              Hpath Ha0'
              ltac:(rewrite Ha1'; vm_compute; reflexivity)
              ltac:(rewrite Ha1'; vm_compute; reflexivity)
              Hnp Hstart Hlast Hin Hokw
              with "[] Himg Hrun Hcwd Hstd Hinv Hmade Hlb Hown [Hcont]").
    { iApply (UCodeShK.uis_shk_cc8 with "Hcode"). }
    iIntros (h2 rv) "Hans Hcwd Hrun".
    (* ---- 0xccc  c.jr ra ---- *)
    assert (E1 : add_vec_int (mword_of_int 0xcc8 : mword 64) 4
                 = mword_of_int 0xccc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    set (m2 := <[Regidx (mword_of_int 10 : mword 5) := rv]> m1).
    assert (Hra : m2 !!! Regidx (mword_of_int 1 : mword 5)
                  = m !!! Regidx (mword_of_int 1 : mword 5)).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx (mword_of_int 10 : mword 5))
                  (Regidx (mword_of_int 1 : mword 5)) rv
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx (mword_of_int 17 : mword 5))
                  (Regidx (mword_of_int 1 : mword 5))
                  (mword_of_int 15 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr (PS := uprogSG_free) (SG := uexecSG_xv6)
              (ghost_varG0 := offbox_offG) N h2 m2 (mword_of_int 0xccc)
              (mword_of_int 1 : mword 5)
              (ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))) av
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (UCodeShK.uis_shk_ccc with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 m2 rv with "[%] [%] Hcwd [Hans] Hrun").
    - exact (ucallee_saved_a0a7 m rv).
    - unfold m2.
      exact (upd_eq m1 (Regidx (mword_of_int 10 : mword 5)) rv).
    - (* THE ANSWER, AT THE TWO ARMS THE REDIRECT CHILD READS *)
      rewrite /UkShRedirAns.ush_open_ans2.
      iDestruct "Hans" as "[[%Hm1 [Hstd Hpay]] | Hfd]".
      + iRight. iSplitR; [ by iPureIntro | ]. iFrame "Hstd".
        rewrite /redir_Kf /FileOpen.file_open_pay. iExact "Hpay".
      + iDestruct "Hfd" as (fd ty) "([%Hrv %Hlt] & Hal & HK)".
        iDestruct (UserFd.ualloc_std (ukn_fd N) l fd 1%nat _ Hfdl with "Hal")
          as "[%Hfd1 Hstd]".
        iLeft. iExists ty. iSplitR.
        { iPureIntro. rewrite Hrv Hfd1. reflexivity. }
        iSplitL "Hstd".
        { iEval (rewrite Ha1') in "Hstd".
          iEval (vm_compute om_readable) in "Hstd".
          iEval (vm_compute om_writable) in "Hstd".
          iExact "Hstd". }
        rewrite /redir_K. iExact "HK".
  Qed.

  (* THE OPEN'S RECEIPT, READ: the deed at `f` present and empty, the
     program's half of the offset at 0, and the claim's fact that `f`'s
     inode is none of the image's ([redir_K_inum]'s conclusion beside the
     receipt).  What the redirect child's exec supply lends. *)
  Definition redir_K' (nm : list (bv 8)) (s : dst) (ty : fdtype) : iProp Σ :=
    (redir_K nm s ty
     ∗ ((∃ (i : Z) (γo : gname),
           ⌜ty = FdInode i γo OffHeld⌝
           ∗ ⌜i <> INIT_INO /\ i <> SH_INO /\ i <> ECHO_INO
              /\ i <> CAT_INO /\ i <> GREP_INO⌝)
        ∨ T))%I.
End UShFileRedir.

