(* ===================================================================== *)
(* UkTreeEntry.v -- THE TWO PROGRAM ENTRIES AT A HANDLER PARAMETER:       *)
(* [ExecEntry.image_entry] for echo and for cat with the tree paid by an  *)
(* ENVIRONMENT ([UkHandler.env_res]) through an interface the caller      *)
(* supplies at the record the entry mints.                                *)
(*                                                                        *)
(* Design: claude-notes/design/program-specs.md SS3.4e (cut 5, lane C).  *)
(* Each entry is built exactly the way the landed ones are                *)
(* ([UEchoFile.efile_image_entry], [UCatKernel.cat_image_entry]):         *)
(* [image_entry_of_at] -> the caller's argument reading is a function of  *)
(* the node sh built ([UShEcho.echo_args_det_holds]) -> the key's         *)
(* geometry ([echo_kexec_pages] / [echo_kexec_entry_rows], cat's twins)  *)
(* -> the slot's constructor ([UkRun.uslot_of_urun_ro] /                  *)
(* [UShCat.cat_entry_run]) -> the program's entry at the tree paid by the *)
(* environment ([UkEchoTree.wp_kecho_start_env] /                         *)
(* [UkCatTree.wp_kcat_start_env]).  What is NEW here is only the pure     *)
(* bridge from the key's reading of argv to the LINE's words: both trees  *)
(* read [drop 1 argv] ([ProgTree.echo_tree_tail] / [cat_tree_tail]), and *)
(* the key's argv from argv[1] on IS the line's words                     *)
(* ([echo_argv_tail] off [UEchoOut.echo_out_argv], [cat_argv_words] off   *)
(* [UShCat.cat_key_args_holds]) -- so the entries conclude at the tree of *)
(* the line, [echo_tree ws] / [cat_tree ws], and no program stream is     *)
(* named.                                                                 *)
(*                                                                        *)
(* The interface is quantified over the minted record                     *)
(* ([I : forall N', ep_iface N' (prog N')], and in the [_c] forms over the *)
(* payload equation too: [I N' (Hpq : ukn_pay N' = Q)], since an instance  *)
(* whose free handler pays the exit needs [ukn_const N'] -- lane F)        *)
(* because the record is what                                             *)
(* the constructor allocates; the caller's environment resources are       *)
(* handed over at that record, given its payload, the ledger of the       *)
(* standard streams at the exec channel's table and the working           *)
(* directory's half at the caller's [cw] -- the two process halves the    *)
(* constructor mints beside the run.  No [Q]-constancy premise: the       *)
(* tree's exit hole is paid by the interface ([ei_exit]), never by        *)
(* [ukn_const].                                                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
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
Require Import UShGrep.               (* grep's key geometry and [grep_entry_run] *)
Require Import FsImgCheck.            (* [fname_f] *)
Require Import ProgTree UkTree UkHandler.
Require Import UkEcho UkEchoTree.
Require Import UkCatMain UkCatTree.
Require Import UCodeGrep GrepTree UkGrepLoop UkGrepTree.
Require Import CtxIdDefs.
Require User.EchoSyms User.CatSyms User.GrepSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  0.  THE ARGV BRIDGES (pure): the key's reading names the line's words *)
(* ===================================================================== *)

(* an argument's bytes, as a tree names them, are a word when the length
   and every byte agree *)
Lemma uarg_bytes_eq (g : uarg) (w : list (bv 8)) :
  ua_len g = length w ->
  (forall j : nat, (j < length w)%nat -> ua_bytes g j = w !!! j) ->
  uarg_bytes g = w.
Proof.
  intros Hl Hb. apply list_eq. intros j.
  destruct (decide (j < length w)%nat) as [Hj | Hj].
  - unfold uarg_bytes.
    rewrite (map_seq_lookup (ua_bytes g) (ua_len g) j ltac:(lia)).
    rewrite (Hb j Hj). symmetry. exact (list_lookup_lookup_total_lt w j Hj).
  - rewrite lookup_ge_None_2; [| rewrite uarg_bytes_length; lia].
    rewrite lookup_ge_None_2; [reflexivity | lia].
Qed.

(* ---- echo: [UEchoOut.out_argv_at] pins argv[i] (i >= 1) at the line's
   own alternative, where the word sits ([UEchoFile.ef_word_bytes]'s
   argument, at the tree's reading of the argument) ---- *)
Lemma echo_word_bytes (ws : list (list (bv 8))) (i : nat) (w : list (bv 8))
    (g : uarg) :
  (1 <= i)%nat -> ws !! i = Some w ->
  ua_len g = length (ws !!! i) ->
  (forall j : nat, (j < ua_len g)%nat ->
     line_alts_of ws !!! 0%nat !! (out_cur ws i + j)%nat
     = Some (ua_bytes g j)) ->
  uarg_bytes g = w.
Proof.
  intros Hi Hw Hlen Hby.
  assert (Hwt : ws !!! i = w) by (apply list_lookup_total_correct; exact Hw).
  rewrite Hwt in Hlen.
  assert (Hd : drop 1 ws !! (i - 1)%nat = Some w)
    by (rewrite ws_drop; [exact Hw | exact Hi]).
  apply uarg_bytes_eq; [exact Hlen |].
  intros j Hj.
  pose proof (Hby j ltac:(lia)) as Hbj.
  rewrite (alt0_out ws (out_cur ws i + j)%nat
             (out_cur_lt ws i w j Hi Hw ltac:(lia))) in Hbj.
  apply list_lookup_total_correct in Hbj.
  rewrite <- Hbj. unfold out_cur.
  exact (wl_line_word (drop 1 ws) (i - 1)%nat w j Hd Hj).
Qed.

(* THE ECHO BRIDGE: the key's argv from argv[1] on is the line's words
   from its second on *)
Lemma echo_argv_tail (ws : list (list (bv 8))) (args : list uarg) :
  UEchoOut.echo_out_argv ws args ->
  map uarg_bytes (drop 1 args) = drop 1 ws.
Proof.
  intros [Hlen Hargs].
  apply list_eq. intros i.
  change (map uarg_bytes (drop 1 args)) with (uarg_bytes <$> drop 1 args).
  rewrite list_lookup_fmap !lookup_drop.
  destruct (decide (1 + i < length args)%nat) as [Hlt | Hge].
  - destruct (lookup_lt_is_Some_2 args (1 + i)%nat Hlt) as [g Hg].
    destruct (lookup_lt_is_Some_2 ws (1 + i)%nat ltac:(lia)) as [w Hw].
    rewrite Hg Hw. cbn [fmap option_fmap option_map]. f_equal.
    destruct (Hargs (1 + i)%nat g ltac:(lia) Hg) as [Hgl Hgb].
    exact (echo_word_bytes ws (1 + i)%nat w g ltac:(lia) Hw Hgl Hgb).
  - rewrite lookup_ge_None_2; [| lia].
    rewrite lookup_ge_None_2; [reflexivity | lia].
Qed.

(* ---- cat: the key's reading of EVERY argument ([UShCat.cat_key_args]),
   through the node's determinacy ([echo_args_det]), is the line's word
   at that index ---- *)
Lemma cat_argv_words (ws : list (list (bv 8))) (args : list uarg)
    (alen : nat -> nat) (afun : nat -> nat -> bv 8) :
  length args = length ws ->
  (forall i : nat, (i < length ws)%nat -> alen i = UkShEcho.echo_alen ws i) ->
  (forall i j : nat, (i < length ws)%nat -> (j < UkShEcho.echo_alen ws i)%nat ->
     afun i j = wl_line ws !!! (UkShEcho.echo_off ws i + j)%nat) ->
  (forall (i : nat) (g : uarg), args !! i = Some g ->
     ua_len g = alen i
     /\ forall j : nat, (j < alen i)%nat -> ua_bytes g j = afun i j) ->
  map uarg_bytes args = ws.
Proof.
  intros Hlen Halen Hafun Hkey.
  apply list_eq. intros i.
  change (map uarg_bytes args) with (uarg_bytes <$> args).
  rewrite list_lookup_fmap.
  destruct (decide (i < length ws)%nat) as [Hlt | Hge].
  - destruct (lookup_lt_is_Some_2 args i ltac:(lia)) as [g Hg].
    destruct (lookup_lt_is_Some_2 ws i Hlt) as [w Hw].
    rewrite Hg Hw. cbn [fmap option_fmap option_map]. f_equal.
    destruct (Hkey i g Hg) as [Hgl Hgb].
    assert (Hwt : ws !!! i = w) by (apply list_lookup_total_correct; exact Hw).
    assert (Hal : alen i = length w)
      by (rewrite (Halen i Hlt); unfold UkShEcho.echo_alen; rewrite Hwt; reflexivity).
    apply uarg_bytes_eq; [rewrite Hgl; exact Hal |].
    intros j Hj.
    rewrite (Hgb j ltac:(lia)).
    rewrite (Hafun i j Hlt ltac:(unfold UkShEcho.echo_alen; rewrite Hwt; lia)).
    unfold UkShEcho.echo_off.
    exact (wl_line_word ws i w j Hw Hj).
  - rewrite lookup_ge_None_2; [| lia].
    rewrite lookup_ge_None_2; [reflexivity | lia].
Qed.

(* ...and the line `cat f`, as the landed entry pins it: two words, the
   second the one-byte name [FsImgCheck.fname_f] *)
Lemma cat_f_tail (ws : list (list (bv 8))) :
  length ws = 2%nat ->
  UkShEcho.echo_alen ws 1%nat = 1%nat ->
  (forall j : nat, (j < 1)%nat ->
     wl_line ws !!! (UkShEcho.echo_off ws 1%nat + j)%nat
     = FsImgCheck.fname_f !!! j) ->
  drop 1 ws = [FsImgCheck.fname_f].
Proof.
  intros Hws2 Halen1 Hfname.
  destruct ws as [| w0 [| w1 [| w2 r]]]; cbn in Hws2; try (exfalso; lia).
  unfold UkShEcho.echo_alen in Halen1. cbn in Halen1.
  destruct w1 as [| b [| b' r']]; cbn in Halen1; try (exfalso; lia).
  cbn [drop]. f_equal.
  pose proof (Hfname 0%nat ltac:(lia)) as Hf.
  unfold UkShEcho.echo_off in Hf.
  rewrite (wl_line_word [w0; [b]] 1%nat [b] 0%nat eq_refl ltac:(cbn; lia)) in Hf.
  change ([b] !!! 0%nat) with b in Hf.
  rewrite Hf. reflexivity.
Qed.

(* ===================================================================== *)
(*  1.  THE ENTRIES                                                       *)
(* ===================================================================== *)

(* echo's .rodata is in the exec image, as its text is
   ([UShEchoPay.echo_data_of_elf_image], restated: that file is above the
   file cone and this one is not) *)
Lemma tree_echo_union_comm_bool :
  bool_decide (EchoInstrs.echo_bytes ∪ EchoData.echo_data
               = EchoData.echo_data ∪ EchoInstrs.echo_bytes) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tree_echo_data_of_elf_image (M : gmap Z (bv 8)) :
  uimg_sub (elf_image ElfUser.echo_elf) M -> echo_data_sub M.
Proof.
  intros H. rewrite ElfUser.echo_elf_image in H.
  apply UShKernel.uimg_sub_union_l in H.
  rewrite (bool_decide_eq_true_1 _ tree_echo_union_comm_bool) in H.
  exact (UShKernel.uimg_sub_union_l _ _ _ H).
Qed.

Section UkTreeEntry.
  (* THE KERNEL'S INSTANCE IS AMBIENT ([uexecSG_xv6]) and the program
     deposit instance is a section variable, as in [UShCat] / [UCatKernel]
     (durable-notes: two instances of one class in one application wedge). *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{PS : UexecSG.uprogSG Σ}.

  (* ------------------------------------------------------------------- *)
  (*  1a. echo                                                            *)
  (* ------------------------------------------------------------------- *)

  (* [UEchoFile.efile_image_entry]'s mould with the payment replaced by an
     interface: whoever enters echo at the channel with the line's tree
     conforming to an environment [E] over the devices [ds], and the
     environment's resources at the minted record, has the entry.

     THE INTERFACE MAY READ THE PAYLOAD EQUATION (lane F, cut 5): an
     instance whose free handler pays the exit at every status needs
     [ukn_const N'], which only [ukn_pay N' = Q] at a constant [Q] gives --
     and the record is minted inside the entry, so the equation is the only
     handle on it.  [I] takes it; [echo_image_entry_env] below is the
     equation-free reading, a corollary. *)
  Lemma echo_image_entry_env_c (ws : list (list (bv 8))) (M : gmap Z (bv 8))
      (s0 t : Z) (g : nat -> bv 8) (sts : list fdstate)
      (cw : Z) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (Pay : iProp Σ)
      {Dp : list nat} (I : forall N' : uk_names Σ, ukn_pay N' = Q -> ep_ifaceP (Dp := Dp) N' (echo_prog N'))
      (E : penv) (ds : gset nat) :
    EchoDisc.line_ok ws ->
    UShEcho.echo_node_img ws M s0 t g ->
    UkShEcho.echo_argv_bytes ws g ->
    length sts = NOFILE ->
    conforms E (echo_tree ws) ->
    safe_fds (dom (pe_fd E)) (echo_tree ws) ->
    dp_in Dp ds ->
    □ (∀ (N' : uk_names Σ) (Hpq : ukn_pay N' = Q),
         UserFd.ustd (ukn_fd N') (take NSTD sts) -∗
         UserCwd.ucwd (ukn_cwd N') cw -∗
         Pay -∗
         env_res N' (echo_prog N') (I N' Hpq) E ds) -∗
    UkRun.urun_nopipe sts -∗
    udep -∗
    image_entry ElfUser.echo_elf M (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q Pay uslot.
  Proof using .
    intros Hline Himg Hbytes Hfdl Hc Hs Hdp.
    iIntros "#Henv #Hnpw #Hdep".
    iApply image_entry_of_at. iIntros "!>" (na alen afun) "%Hargs".
    destruct (UShEcho.echo_args_det_holds ws Hline M s0 t g na alen afun
                Himg Hbytes Hargs) as (Hna & Halen & Hafun).
    rewrite /image_entry_at. iIntros "!>" (W') "%Hokk %Hcwv %Hlzf _ _ Hmp HPay".
    destruct (UShEcho.echo_kexec_pages na alen afun sts W' Hokk)
      as (Hpc & Hsub & Hx & Hwr & Hrp).
    destruct (UShEcho.echo_kexec_entry_rows na alen afun sts W' Hokk
                (UShEcho.echo_room_of_det ws na alen Hline Hna Halen) Hfdl
                Hwr Hrp)
      as (Hroom96 & Hal8 & Hstkrow & Hargsrow & Havd & Havs & Hfdlen & Hstop).
    pose proof (echo_out_argv_of_image ws na alen afun sts W'
                  Hline Hokk Hna Halen Hafun) as Hargv.
    pose proof (kexec_image_ok_fd _ _ _ _ _ _ Hokk) as Hfd.
    assert (Hsub2 : echo_data_sub (uvis_M W')).
    { pose proof Hokk as Hok2.
      unfold kexec_image_ok in Hok2. cbv zeta in Hok2.
      destruct Hok2 as (_ & _ & _ & _ & _ & Himg' & _).
      exact (tree_echo_data_of_elf_image _ Himg'). }
    assert (Hsp0 : 0 <= uint (uvis_sp W')) by lia.
    assert (Hargc0 : 0 <= uvis_argc W')
      by exact (proj1 (uka_argc _ _ _ _ _ _ Hargsrow)).
    (* the key's argv names the line's tree *)
    assert (Htree : echo_tree (map uarg_bytes
                                 (echo_args (uvis_M W') (uvis_av W')
                                    (Z.to_nat (uvis_argc W'))))
                    = echo_tree ws).
    { apply echo_tree_tail. rewrite <- map_drop.
      exact (echo_argv_tail ws _ Hargv). }
    assert (Hc' : conforms E
                    (echo_tree (map uarg_bytes
                                  (echo_args (uvis_M W') (uvis_av W')
                                     (Z.to_nat (uvis_argc W'))))))
      by (rewrite Htree; exact Hc).
    assert (Hs' : safe_fds (dom (pe_fd E))
                    (echo_tree (map uarg_bytes
                                  (echo_args (uvis_M W') (uvis_av W')
                                     (Z.to_nat (uvis_argc W'))))))
      by (rewrite Htree; exact Hs).
    (* the two register facts, as the landed entries state them *)
    assert (Ha0 : tf_resume_gpr0 (uvis_tf W') !!! Regidx (mword_of_int 10 : mword 5)
                  = mword_of_int (Z.of_nat (length (echo_args (uvis_M W') (uvis_av W')
                                                      (Z.to_nat (uvis_argc W')))))).
    { rewrite echo_args_length. rewrite (Z2Nat.id (uvis_argc W') Hargc0).
      unfold uvis_argc. symmetry. apply moi_of_uint. }
    assert (Ha1 : tf_resume_gpr0 (uvis_tf W') !!! Regidx (mword_of_int 11 : mword 5)
                  = mword_of_int (uvis_av W')).
    { unfold uvis_av. symmetry. apply moi_of_uint. }
    iAssert (UkRun.urun_nopipe (uvis_fd W')) as "#Hnpw'";
      [ rewrite Hfd; iExact "Hnpw" | ].
    iApply (uslot_of_urun_ro W' 12 Q Hal8
              ltac:(unfold uvis_sp in Hroom96; lia) Hstkrow Hfdlen Hstop Hlzf
              with "Hdep Hnpw' Hmp").
    iIntros (N' h) "%Hpayeq %Hsz _ #Ht Hstd Hcwf _ _ #HA Hrun".
    rewrite Hpc.
    iApply (wp_kecho_start_env N' (I N' Hpayeq) E ds h (tf_resume_gpr0 (uvis_tf W'))
              (uvis_av W')
              (echo_args (uvis_M W') (uvis_av W') (Z.to_nat (uvis_argc W')))
              0 Hc' Hs' Hdp Ha0 Ha1
              with "[Hstd Hcwf HPay] [] [] [] Hrun").
    { iApply ("Henv" $! N' Hpayeq with "[Hstd] [Hcwf] HPay");
        [ rewrite <- Hfd; iExact "Hstd" | rewrite <- Hcwv; iExact "Hcwf" ]. }
    { iApply (echo_code_of_text (ukn_t N') (uvis_M W') (uvis_perm W') Hsub Hx
                with "Ht"). }
    { iApply (echo_rodata_of_text (ukn_t N') (uvis_M W') (uvis_perm W')
                Hsub2 Hx with "Ht"). }
    { iApply (echo_uargv_of_area (ukn_d N') (uvis_M W') (uvis_perm W')
                (uvis_sz W') (uvis_av W') (uint (uvis_sp W')) (uvis_argc W')
                Hsp0 Hargsrow Havd Havs with "HA"). }
  Qed.

  (* ...and at an interface that does not read the equation (lane C's
     statement, unchanged) *)
  Lemma echo_image_entry_env (ws : list (list (bv 8))) (M : gmap Z (bv 8))
      (s0 t : Z) (g : nat -> bv 8) (sts : list fdstate)
      (cw : Z) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (Pay : iProp Σ)
      {Dp : list nat} (I : forall N' : uk_names Σ, ep_ifaceP (Dp := Dp) N' (echo_prog N'))
      (E : penv) (ds : gset nat) :
    EchoDisc.line_ok ws ->
    UShEcho.echo_node_img ws M s0 t g ->
    UkShEcho.echo_argv_bytes ws g ->
    length sts = NOFILE ->
    conforms E (echo_tree ws) ->
    safe_fds (dom (pe_fd E)) (echo_tree ws) ->
    dp_in Dp ds ->
    □ (∀ N' : uk_names Σ,
         ⌜ukn_pay N' = Q⌝ -∗
         UserFd.ustd (ukn_fd N') (take NSTD sts) -∗
         UserCwd.ucwd (ukn_cwd N') cw -∗
         Pay -∗
         env_res N' (echo_prog N') (I N') E ds) -∗
    UkRun.urun_nopipe sts -∗
    udep -∗
    image_entry ElfUser.echo_elf M (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q Pay uslot.
  Proof using .
    intros Hline Himg Hbytes Hfdl Hc Hs Hdp.
    iIntros "#Henv #Hnpw #Hdep".
    iApply (echo_image_entry_env_c ws M s0 t g sts cw cs pidv Q Pay
              (fun N' _ => I N') E ds Hline Himg Hbytes Hfdl Hc Hs Hdp
              with "[] Hnpw Hdep").
    iIntros "!>" (N' Hpq) "Hstd Hcwf HPay".
    iApply ("Henv" $! N' with "[%] Hstd Hcwf HPay"). exact Hpq.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  1b. cat                                                             *)
  (* ------------------------------------------------------------------- *)

  (* [UCatKernel.cat_image_entry]'s mould with the payment replaced by an
     interface, at the tree of the LINE: the key's argv is the line's
     words ([cat_argv_words]), so no word of the line is pinned here --
     the entry holds at [cat_tree ws] for any admissible line.  The
     interface may read the payload equation ([echo_image_entry_env_c]'s
     note); [cat_image_entry_env] is the equation-free corollary. *)
  Lemma cat_image_entry_env_c (ws : list (list (bv 8))) (Mn : gmap Z (bv 8))
      (sv t : Z) (gn : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (Pay : iProp Σ)
      {Dp : list nat} (I : forall N' : uk_names Σ, ukn_pay N' = Q -> ep_ifaceP (Dp := Dp) N' (cat_prog N'))
      (E : penv) (ds : gset nat) :
    exec_ok ws ->
    UShEcho.echo_node_img ws Mn sv t gn ->
    UkShEcho.echo_argv_bytes ws gn ->
    length sts = NOFILE ->
    conforms E (cat_tree ws) ->
    safe_fds (dom (pe_fd E)) (cat_tree ws) ->
    dp_in Dp ds ->
    □ (∀ (N' : uk_names Σ) (Hpq : ukn_pay N' = Q),
         UserFd.ustd (ukn_fd N') (take NSTD sts) -∗
         UserCwd.ucwd (ukn_cwd N') cw -∗
         Pay -∗
         env_res N' (cat_prog N') (I N' Hpq) E ds) -∗
    UkRun.urun_nopipe sts -∗
    udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q Pay uslot.
  Proof using .
    intros Hok Himg Hbytes Hfdl Hc Hs Hdp.
    iIntros "#Henv #Hnpw #Hdep".
    iApply image_entry_of_at. iIntros "!>" (na alen afun) "%Hargs".
    destruct (UShCat.cat_args_det_holds ws Hok Mn sv t gn na alen afun
                Himg Hbytes Hargs) as (Hna & Halen & Hafun).
    pose proof (UShCat.cat_room_of_det_x ws na alen Hok Hna Halen) as Hroom.
    rewrite /image_entry_at.
    iIntros "!>" (W') "%Hokk %Hcwv %Hlzf _ _ Hmp HPay".
    destruct (UShCat.cat_kexec_pages na alen afun sts W' Hokk)
      as (Hpc & Hsub & Hsub2 & Hx & Hdw & Hbufb & Hwr & Hrp).
    destruct (UShCat.cat_kexec_entry_rows na alen afun sts W' Hokk Hroom
                Hfdl Hwr Hrp)
      as (Hroom336 & Hal8 & Hszv & Hstkrow & Hargsrow & Havd & Havs
          & Hfdlen & Hstop).
    pose proof (UShCat.cat_kexec_bufrow na alen afun sts W' Hokk Hroom
                  Hdw Hbufb) as Hbuf.
    pose proof (UShCat.cat_kexec_argnz na alen afun sts W' Hokk Hroom)
      as Hnz.
    pose proof (kexec_image_ok_fd _ na alen afun sts W' Hokk) as Hfd.
    assert (Hargc0 : 0 <= uvis_argc W')
      by exact (proj1 (uka_argc _ _ _ _ _ _ Hargsrow)).
    assert (Hptr : forall (j : nat) (ga : uarg),
              UShCat.cat_args W' !! j = Some ga -> UserHeap.ua_ptr ga <> 0).
    { intros j ga Hj.
      assert (Hlt : (j < Z.to_nat (uvis_argc W'))%nat).
      { pose proof (lookup_lt_Some _ _ _ Hj) as Hl.
        rewrite /UShCat.cat_args echo_args_length in Hl. exact Hl. }
      rewrite /UShCat.cat_args (echo_args_lookup (uvis_M W') (uvis_av W')
                                  (Z.to_nat (uvis_argc W')) j Hlt) in Hj.
      injection Hj as <-. cbn [UserHeap.ua_ptr echo_arg].
      exact (Hnz j Hlt). }
    (* ---- THE KEY'S OWN READING OF THE LINE ---- *)
    assert (Hno : forall i j : nat, (i < na)%nat -> (j < alen i)%nat ->
              afun i j <> ubyte0).
    { intros i j Hi Hj.
      rewrite (Hafun i j ltac:(lia)
                 ltac:(rewrite <- (Halen i ltac:(lia)); exact Hj)).
      apply (UShEcho.line_nonul_x ws _ Hok).
      exact (UkShEcho.echo_off_lt_x ws i j Hok ltac:(lia)
               ltac:(rewrite <- (Halen i ltac:(lia)); lia)). }
    destruct (UShCat.cat_key_args_holds na alen afun sts W' Hokk Hno)
      as [Hargcna Hkey].
    assert (Hwords : map uarg_bytes (UShCat.cat_args W') = ws).
    { apply (cat_argv_words ws _ alen afun).
      - rewrite /UShCat.cat_args echo_args_length Hargcna Hna. reflexivity.
      - exact Halen.
      - exact Hafun.
      - intros i ga Hga.
        assert (Hlt : (i < na)%nat).
        { pose proof (lookup_lt_Some _ _ _ Hga) as Hl.
          rewrite /UShCat.cat_args echo_args_length Hargcna in Hl. exact Hl. }
        rewrite /UShCat.cat_args
                (echo_args_lookup (uvis_M W') (uvis_av W')
                   (Z.to_nat (uvis_argc W')) i ltac:(rewrite Hargcna; exact Hlt))
          in Hga.
        injection Hga as <-. exact (Hkey i Hlt). }
    assert (Hc' : conforms E (cat_tree (map uarg_bytes (UShCat.cat_args W'))))
      by (rewrite Hwords; exact Hc).
    assert (Hs' : safe_fds (dom (pe_fd E))
                    (cat_tree (map uarg_bytes (UShCat.cat_args W'))))
      by (rewrite Hwords; exact Hs).
    iAssert (UkRun.urun_nopipe (uvis_fd W')) as "#Hnpw'";
      [ rewrite Hfd; iExact "Hnpw" | ].
    iApply (UShCat.cat_entry_run W' Q Hpc Hsub Hsub2 Hx Hroom336 Hal8
              Hstkrow Hbuf Hargsrow Havd Havs Hfdlen Hstop Hlzf
              with "Hdep Hnpw' Hmp").
    iIntros (N' h) "%Hpayeq Hstd Hcwf #Hcode #Hro #Hargv _ Hbuf' Hrun".
    assert (Ha0 : tf_resume_gpr0 (uvis_tf W') !!! Regidx (mword_of_int 10 : mword 5)
                  = mword_of_int (Z.of_nat (length (UShCat.cat_args W')))).
    { rewrite /UShCat.cat_args echo_args_length.
      rewrite (Z2Nat.id (uvis_argc W') Hargc0).
      unfold uvis_argc. symmetry. apply moi_of_uint. }
    assert (Ha1 : tf_resume_gpr0 (uvis_tf W') !!! Regidx (mword_of_int 11 : mword 5)
                  = mword_of_int (uvis_av W')).
    { unfold uvis_av. symmetry. apply moi_of_uint. }
    iApply (wp_kcat_start_env N' (I N' Hpayeq) E ds h (tf_resume_gpr0 (uvis_tf W'))
              (uvis_av W') (UShCat.cat_args W') (fun _ : nat => ubyte0) 0%nat
              Hc' Hs' Hdp Hptr Ha0 Ha1
              with "[Hstd Hcwf HPay] Hcode Hro Hargv Hbuf' Hrun").
    iApply ("Henv" $! N' Hpayeq with "[Hstd] [Hcwf] HPay");
      [ rewrite <- Hfd; iExact "Hstd" | rewrite <- Hcwv; iExact "Hcwf" ].
  Qed.

  (* ...and at an interface that does not read the equation (lane C's
     statement, unchanged) *)
  Lemma cat_image_entry_env (ws : list (list (bv 8))) (Mn : gmap Z (bv 8))
      (sv t : Z) (gn : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (Pay : iProp Σ)
      {Dp : list nat} (I : forall N' : uk_names Σ, ep_ifaceP (Dp := Dp) N' (cat_prog N'))
      (E : penv) (ds : gset nat) :
    exec_ok ws ->
    UShEcho.echo_node_img ws Mn sv t gn ->
    UkShEcho.echo_argv_bytes ws gn ->
    length sts = NOFILE ->
    conforms E (cat_tree ws) ->
    safe_fds (dom (pe_fd E)) (cat_tree ws) ->
    dp_in Dp ds ->
    □ (∀ N' : uk_names Σ,
         ⌜ukn_pay N' = Q⌝ -∗
         UserFd.ustd (ukn_fd N') (take NSTD sts) -∗
         UserCwd.ucwd (ukn_cwd N') cw -∗
         Pay -∗
         env_res N' (cat_prog N') (I N') E ds) -∗
    UkRun.urun_nopipe sts -∗
    udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q Pay uslot.
  Proof using .
    intros Hok Himg Hbytes Hfdl Hc Hs Hdp.
    iIntros "#Henv #Hnpw #Hdep".
    iApply (cat_image_entry_env_c ws Mn sv t gn sts cw cs pidv Q Pay
              (fun N' _ => I N') E ds Hok Himg Hbytes Hfdl Hc Hs Hdp
              with "[] Hnpw Hdep").
    iIntros "!>" (N' Hpq) "Hstd Hcwf HPay".
    iApply ("Henv" $! N' with "[%] Hstd Hcwf HPay"). exact Hpq.
  Qed.

  (* ...and at the line `cat f` the landed entry pins (SS3.4e's plan):
     [cat_image_entry_env] through [ProgTree.cat_tree_tail]. *)
  Lemma cat_image_entry_env_f (ws : list (list (bv 8))) (Mn : gmap Z (bv 8))
      (sv t : Z) (gn : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (Pay : iProp Σ)
      {Dp : list nat} (I : forall N' : uk_names Σ, ep_ifaceP (Dp := Dp) N' (cat_prog N'))
      (E : penv) (ds : gset nat) :
    exec_ok ws ->
    UShEcho.echo_node_img ws Mn sv t gn ->
    UkShEcho.echo_argv_bytes ws gn ->
    length sts = NOFILE ->
    length ws = 2%nat ->
    UkShEcho.echo_alen ws 1%nat = 1%nat ->
    (forall j : nat, (j < 1)%nat ->
       wl_line ws !!! (UkShEcho.echo_off ws 1%nat + j)%nat
       = FsImgCheck.fname_f !!! j) ->
    conforms E (cat_tree [sb "cat"; FsImgCheck.fname_f]) ->
    safe_fds (dom (pe_fd E)) (cat_tree [sb "cat"; FsImgCheck.fname_f]) ->
    dp_in Dp ds ->
    □ (∀ N' : uk_names Σ,
         ⌜ukn_pay N' = Q⌝ -∗
         UserFd.ustd (ukn_fd N') (take NSTD sts) -∗
         UserCwd.ucwd (ukn_cwd N') cw -∗
         Pay -∗
         env_res N' (cat_prog N') (I N') E ds) -∗
    UkRun.urun_nopipe sts -∗
    udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q Pay uslot.
  Proof using .
    intros Hok Himg Hbytes Hfdl Hws2 Halen1 Hfname Hc Hs Hdp.
    assert (Htail : cat_tree ws = cat_tree [sb "cat"; FsImgCheck.fname_f]).
    { apply cat_tree_tail. rewrite (cat_f_tail ws Hws2 Halen1 Hfname). reflexivity. }
    rewrite <- Htail in Hc, Hs.
    iIntros "#Henv #Hnpw #Hdep".
    iApply (cat_image_entry_env ws Mn sv t gn sts cw cs pidv Q Pay I E ds
              Hok Himg Hbytes Hfdl Hc Hs Hdp with "Henv Hnpw Hdep").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  1c. grep                                                            *)
  (* ------------------------------------------------------------------- *)

  (* [cat_image_entry_env_c] at grep (claude-notes/design/grep-pipes.md
     SS3.5, cut G6): the same bridge from the key's argv to the LINE's
     words, at [UkGrepTree.wp_kgrep_start_env].  Two differences:
       - NO [safe_fds] premise: grep's tree is safe at every held set
         ([GrepTree.grep_tree_safe]), which the program's entry discharges;
       - THE FRAME IS THE LINE'S NEED, [UShGrep.grep_need ws] words
         (grep's matcher recurses on the pattern), and the key's argv
         reading the line's words is what makes [grep_stack] of the key's
         vector that need. *)
  Lemma grep_image_entry_env_c (ws : list (list (bv 8))) (Mn : gmap Z (bv 8))
      (sv t : Z) (gn : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (Pay : iProp Σ)
      {Dp : list nat} (I : forall N' : uk_names Σ, ukn_pay N' = Q -> ep_ifaceP (Dp := Dp) N' (grep_prog N'))
      (E : penv) (ds : gset nat) :
    exec_ok ws ->
    UShEcho.echo_node_img ws Mn sv t gn ->
    UkShEcho.echo_argv_bytes ws gn ->
    length sts = NOFILE ->
    conforms E (grep_tree ws) ->
    dp_in Dp ds ->
    □ (∀ (N' : uk_names Σ) (Hpq : ukn_pay N' = Q),
         UserFd.ustd (ukn_fd N') (take NSTD sts) -∗
         UserCwd.ucwd (ukn_cwd N') cw -∗
         Pay -∗
         env_res N' (grep_prog N') (I N' Hpq) E ds) -∗
    UkRun.urun_nopipe sts -∗
    udep -∗
    image_entry ElfUser.grep_elf Mn (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q Pay uslot.
  Proof using .
    intros Hok Himg Hbytes Hfdl Hc Hdp.
    iIntros "#Henv #Hnpw #Hdep".
    iApply image_entry_of_at. iIntros "!>" (na alen afun) "%Hargs".
    destruct (UShGrep.grep_args_det_holds ws Hok Mn sv t gn na alen afun
                Himg Hbytes Hargs) as (Hna & Halen & Hafun).
    pose proof (UShGrep.grep_room_of_det_x ws na alen Hok Hna Halen) as Hroom.
    rewrite /image_entry_at.
    iIntros "!>" (W') "%Hokk %Hcwv %Hlzf _ _ Hmp HPay".
    destruct (UShGrep.grep_kexec_pages na alen afun sts W' Hokk)
      as (Hpc & Hsub & Hsub2 & Hx & Hdw & Hbufb & Hwr & Hrp).
    destruct (UShGrep.grep_kexec_entry_rows na alen afun sts W'
                (UShGrep.grep_need ws) Hokk Hroom Hfdl Hwr Hrp)
      as (HroomK & Hal8 & Hszv & Hstkrow & Hargsrow & Havd & Havs
          & Hfdlen & Hstop).
    pose proof (UShGrep.grep_kexec_bufrow na alen afun sts W'
                  (UShGrep.grep_need ws) Hokk Hroom Hdw Hbufb) as Hbuf.
    pose proof (UShGrep.grep_kexec_argnz na alen afun sts W'
                  (UShGrep.grep_need ws) Hokk Hroom) as Hnz.
    pose proof (kexec_image_ok_fd _ na alen afun sts W' Hokk) as Hfd.
    assert (Hargc0 : 0 <= uvis_argc W')
      by exact (proj1 (uka_argc _ _ _ _ _ _ Hargsrow)).
    assert (Hptr : forall (j : nat) (ga : uarg),
              UShGrep.grep_args W' !! j = Some ga -> UserHeap.ua_ptr ga <> 0).
    { intros j ga Hj.
      assert (Hlt : (j < Z.to_nat (uvis_argc W'))%nat).
      { pose proof (lookup_lt_Some _ _ _ Hj) as Hl.
        rewrite /UShGrep.grep_args echo_args_length in Hl. exact Hl. }
      rewrite /UShGrep.grep_args (echo_args_lookup (uvis_M W') (uvis_av W')
                                    (Z.to_nat (uvis_argc W')) j Hlt) in Hj.
      injection Hj as <-. cbn [UserHeap.ua_ptr echo_arg].
      exact (Hnz j Hlt). }
    (* ---- THE KEY'S OWN READING OF THE LINE ---- *)
    assert (Hno : forall i j : nat, (i < na)%nat -> (j < alen i)%nat ->
              afun i j <> ubyte0).
    { intros i j Hi Hj.
      rewrite (Hafun i j ltac:(lia)
                 ltac:(rewrite <- (Halen i ltac:(lia)); exact Hj)).
      apply (UShEcho.line_nonul_x ws _ Hok).
      exact (UkShEcho.echo_off_lt_x ws i j Hok ltac:(lia)
               ltac:(rewrite <- (Halen i ltac:(lia)); lia)). }
    destruct (UShGrep.grep_key_args_holds na alen afun sts W' Hokk Hno)
      as [Hargcna Hkey].
    assert (Hwords : map uarg_bytes (UShGrep.grep_args W') = ws).
    { apply (cat_argv_words ws _ alen afun).
      - rewrite /UShGrep.grep_args echo_args_length Hargcna Hna. reflexivity.
      - exact Halen.
      - exact Hafun.
      - intros i ga Hga.
        assert (Hlt : (i < na)%nat).
        { pose proof (lookup_lt_Some _ _ _ Hga) as Hl.
          rewrite /UShGrep.grep_args echo_args_length Hargcna in Hl. exact Hl. }
        rewrite /UShGrep.grep_args
                (echo_args_lookup (uvis_M W') (uvis_av W')
                   (Z.to_nat (uvis_argc W')) i ltac:(rewrite Hargcna; exact Hlt))
          in Hga.
        injection Hga as <-. exact (Hkey i Hlt). }
    assert (Hc' : conforms E (grep_tree (map uarg_bytes (UShGrep.grep_args W'))))
      by (rewrite Hwords; exact Hc).
    (* the frame is the key's own need *)
    assert (Hneed : (grep_stack (UShGrep.grep_args W') <= UShGrep.grep_need ws)%nat)
      by (rewrite UShGrep.grep_stack_need Hwords; lia).
    iAssert (UkRun.urun_nopipe (uvis_fd W')) as "#Hnpw'";
      [ rewrite Hfd; iExact "Hnpw" | ].
    iApply (UShGrep.grep_entry_run W' Q (UShGrep.grep_need ws) Hpc Hsub Hsub2
              Hx HroomK Hal8 Hstkrow Hbuf Hargsrow Havd Havs Hfdlen Hstop Hlzf
              with "Hdep Hnpw' Hmp").
    iIntros (N' h) "%Hpayeq Hstd Hcwf #Hcode #Hro #Hargv _ Hbuf' Hrun".
    assert (Ha0 : tf_resume_gpr0 (uvis_tf W') !!! Regidx (mword_of_int 10 : mword 5)
                  = mword_of_int (Z.of_nat (length (UShGrep.grep_args W')))).
    { rewrite /UShGrep.grep_args echo_args_length.
      rewrite (Z2Nat.id (uvis_argc W') Hargc0).
      unfold uvis_argc. symmetry. apply moi_of_uint. }
    assert (Ha1 : tf_resume_gpr0 (uvis_tf W') !!! Regidx (mword_of_int 11 : mword 5)
                  = mword_of_int (uvis_av W')).
    { unfold uvis_av. symmetry. apply moi_of_uint. }
    iApply (wp_kgrep_start_env N' (I N' Hpayeq) E ds h (tf_resume_gpr0 (uvis_tf W'))
              (uvis_av W') (UShGrep.grep_args W') (fun _ : nat => ubyte0)
              (UShGrep.grep_need ws)
              Hc' Hdp Hptr Ha0 Ha1 Hneed
              with "[Hstd Hcwf HPay] Hcode Hro Hargv Hbuf' Hrun").
    iApply ("Henv" $! N' Hpayeq with "[Hstd] [Hcwf] HPay");
      [ rewrite <- Hfd; iExact "Hstd" | rewrite <- Hcwv; iExact "Hcwf" ].
  Qed.

  (* ...and at an interface that does not read the equation *)
  Lemma grep_image_entry_env (ws : list (list (bv 8))) (Mn : gmap Z (bv 8))
      (sv t : Z) (gn : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (Pay : iProp Σ)
      {Dp : list nat} (I : forall N' : uk_names Σ, ep_ifaceP (Dp := Dp) N' (grep_prog N'))
      (E : penv) (ds : gset nat) :
    exec_ok ws ->
    UShEcho.echo_node_img ws Mn sv t gn ->
    UkShEcho.echo_argv_bytes ws gn ->
    length sts = NOFILE ->
    conforms E (grep_tree ws) ->
    dp_in Dp ds ->
    □ (∀ N' : uk_names Σ,
         ⌜ukn_pay N' = Q⌝ -∗
         UserFd.ustd (ukn_fd N') (take NSTD sts) -∗
         UserCwd.ucwd (ukn_cwd N') cw -∗
         Pay -∗
         env_res N' (grep_prog N') (I N') E ds) -∗
    UkRun.urun_nopipe sts -∗
    udep -∗
    image_entry ElfUser.grep_elf Mn (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q Pay uslot.
  Proof using .
    intros Hok Himg Hbytes Hfdl Hc Hdp.
    iIntros "#Henv #Hnpw #Hdep".
    iApply (grep_image_entry_env_c ws Mn sv t gn sts cw cs pidv Q Pay
              (fun N' _ => I N') E ds Hok Himg Hbytes Hfdl Hc Hdp
              with "[] Hnpw Hdep").
    iIntros "!>" (N' Hpq) "Hstd Hcwf HPay".
    iApply ("Henv" $! N' with "[%] Hstd Hcwf HPay"). exact Hpq.
  Qed.

End UkTreeEntry.
