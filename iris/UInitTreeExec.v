(* ===================================================================== *)
(* UInitTreeExec.v -- /INIT'S EXEC SUPPLY FOR /sh, PAID FROM THE TAINT    *)
(* (lane TL-8, deliverable D3; design/user-tree.md section 9.6(4)).       *)
(*                                                                       *)
(* [UInitSh.init_exec_sup_of_sh_slot] is ECHO's producer of              *)
(* [UkInit.init_exec_sup_lend]: it builds the exec'd shell's OWN entry    *)
(* theorem out of sh's slot, and its Coq-level premise is the ten console *)
(* laws ([UInitSh.cons_cred_holds]).  Under a TREE application sh is not  *)
(* verified against the claim at all -- section 9.2, section 9.3(5): a    *)
(* live owner's exec goes through the taint arm -- so none of that        *)
(* machinery arises here.  This file pays the supply TREE-NATIVELY:       *)
(*                                                                       *)
(*   (W)  the walk is [ExecRun.exec_walk_of_taint]: every cursor is       *)
(*        [True], the observation opens nothing and the node the walk     *)
(*        reports is identified only by the taint;                       *)
(*   (E)  the entry is [ExecRun.image_entry_of_taint] at the GENERIC      *)
(*        slot, which the taint buys through [AppTree.tree_sup_of_taint]  *)
(*        ([AppInv.app_sup]) and [UexecExecMint.uslot_mint_all] -- the    *)
(*        output licence and the kill credential being free at this       *)
(*        record's interface, exactly as [UInitTree.tree_init_deps]       *)
(*        already reads them;                                            *)
(*   (L)  loadability is [ElfLoadable.sh_elf_loadable], by computation;   *)
(*   the refund is the lend as it went in ([UkInit.init_lend_ref]), by    *)
(*   framing -- a failed exec hands /init's child back what pays its      *)
(*   diagnostic and its exit.                                            *)
(*                                                                       *)
(* WHAT THE CREDENTIAL [Cns] IS, AND WHY IT IS [True] (lane TL-9;         *)
(* design/user-tree.md section 9.8).                                      *)
(* [UkInit.init_cons_sup cn T Cns st Cr] is the supply as a WAND from the *)
(* credential /init's own console dance leaves, beside [box (T -* Cns)].  *)
(* The dance is landed at [Cns := True]                                   *)
(* ([UInitTreeBoot.tree_init_cons_dance_all]) with the era's DEED as its  *)
(* linear credential, and [UInitKernel.init_boot_con] takes ONE [Cns] for *)
(* both -- so the supply has to be payable from nothing.                  *)
(*                                                                       *)
(* WHAT MADE THAT POSSIBLE, AND WHAT IT REPLACES.  Lane TL-8 REFUTED the  *)
(* statement at the shapes it then had, and the refutation was a token    *)
(* count: the node ([UkInit.init_exec_sup_pos]) is handed the round's     *)
(* credential ([UkInit.init_lend_cred]), whose closed row at this record  *)
(* is the era's UNSPENT LICENCE ([UInitTree.tree_cc]'s [cc_wb]) -- and    *)
(* with the node's conclusion UPDATE-FREE there was nowhere inside its    *)
(* own construction where that licence could be minted into the taint,    *)
(* while outside it the supply is a [box].  The owner's ruling for TL-9   *)
(* is section 9.4's, one premise over: the node gets an UPDATE DOOR       *)
(* ([UkInit.init_exec_sup_pos] ends in [|==> UkRunExecRef.                *)
(* udepw_at_refR_ids ...]), which ECHO discharges with one [iModIntro]    *)
(* ([UInitSh.init_exec_sup_of_sh_slot]) and which this file discharges by *)
(* reading the taint off the lend's three arms                            *)
(* ([UInitTree.tree_lend_taint]) -- minting on the closed row, which is   *)
(* the row where the banner was never written and the licence is still    *)
(* unspent.  The lend goes back on its taint arm, so the deposit's REFUND *)
(* ([UkInit.init_lend_ref]) is untouched.                                 *)
(*                                                                       *)
(* The wand form from the taint is kept beside it                         *)
(* ([tree_init_exec_sup_lend]); both are the ONE body of                  *)
(* [tree_init_exec_sup_pos].                                              *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import UartNames.             (* [cons_licence] / [cons_licence_triv] *)
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.           (* [uheap_text] *)
Require Import UmodeAbi.           (* [uimg_sub] *)
Require Import UserConsole.        (* [ucons_pay] / [upos] and the record *)
Require Import UexecSlot UexecRet.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import UexecExecMint.      (* [uslot_mint_all] *)
Require Import ExecEntry.          (* [image_entry_taint] *)
Require Import ExecRun.            (* the deposit out of the supply *)
Require Import ElfLoadable.        (* [sh_elf_loadable] *)
Require Import UkRun.
Require Import UCodeInit.          (* [init_rodata] / [init_ro] *)
Require Import UkInit.
Require Import UInitSh.            (* [init_sh_pl] / [init_sh_path_of] *)
Require Import LinkUserinit.       (* [UG.uexec_wp_gen]: the generic user WP *)
Require Import SpecKexec.          (* [kexec_image_ok] / [exec_slot_pre] *)
Require Import InitBoot.           (* [init_boot_bytes] *)
Require Import UInitCons.          (* [init_cons_fd] *)
Require Import UInitKernel.        (* [init_boot_con] / [init_boot_pay] *)
Require Import UInitBoot.          (* [init_boot_room]: echo's arithmetic *)
Require Import AppCfg AppInv.
Require Import FsCfg.
Require Import FsTree.
Require Import FsAbsDefs.          (* [absnode] / [ADir] *)
Require Import TreeView.           (* [ttree] / [tv_nodes] *)
Require Import AppTree.            (* the licence, the taint and the claim *)
Require Import UInitTree.          (* [tree_cc] *)
Require Import UInitTreeBoot.      (* TL-7's dance, at [Cns := True] *)
Require Import FsConsPin.          (* [fname_console] *)
Require FsImg.
Require ElfUser.

Local Open Scope Z_scope.

Section UInitTreeExec.
  (* THE KERNEL'S INSTANCE IS AMBIENT ([UInitSh.v]'s rule): no local
     [Context {SG}] / [Context {PS}].  Everything stated below names no
     [psok], so there is no [uprogSG] instance to pin either. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* the console ring's cameras: the POSITION /init lends the shell across
     the exec is stated over them ([UserConsole.upos]) *)
  Context `{!uartGhostG Σ}.
  Context `{!treeG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  (* =================================================================== *)
  (*  1.  THE GENERIC SLOT, OFF THE TAINT                                 *)
  (*                                                                     *)
  (*  [UInitBoot]'s own assembly of [UexecExecMint.uslot_mint_all], one   *)
  (*  application over.  The supply is the taint's                        *)
  (*  ([AppTree.tree_sup_of_taint]); the two other credentials the mint   *)
  (*  takes are FREE at this record's interface -- the output licence     *)
  (*  because the claim claims no console ([WpUart.cons_licence_triv])    *)
  (*  and the kill credential because a kill costs this application       *)
  (*  nothing ([RiscvPtsto.kill_cred_triv]).  Those are the same two      *)
  (*  readings [UInitTree.tree_init_deps] already makes.                  *)
  (* =================================================================== *)
  Lemma tree_gen_slot (c : tree_fixed) (r : tree_names) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    riscv_cons_res = cons_res_triv ->
    app_taint = kill_cred_triv ->
    tree_taint c -∗
    □ (∀ (R : iProp Σ) (W : uvis),
         my_pay (uvis_gen W) (fun _ => R)%I -∗
         □ (app_taint -∗ R) -∗ uslot W).
  Proof using .
    intros Heq Hcons Hkill. iIntros "#Ht".
    iAssert (AppInv.app_sup) as "#Hsup".
    { rewrite /AppInv.app_sup Heq.
      cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iApply (tree_sup_of_taint c r with "Ht"). }
    iAssert (app_taint)%I as "#Hkc";
      [ rewrite Hkill /kill_cred_triv; done | ].
    iPoseProof LinkUserinit.UG.uexec_wp_gen as "#Hwp".
    iApply (uslot_mint_all with "Hsup Hkc Hwp").
  Qed.

  (* ...AND THE TAINT ARM OF AN ENTRY, which is that mint at the payload
     the lease names.  [UserConsole.ucons_pay_eta] is why the constant
     family the generic mint is stated at IS this payload, and
     [ucons_pay_taint] is what the arm's own kill row costs: nothing, once
     the taint is in hand.  NOTE THE TAINT IS AN ARGUMENT HERE -- the
     statement is closed, and that is what makes it usable at a round
     whose lend has not been read yet. *)
  Lemma tree_image_entry_taint (c : tree_fixed) (r : tree_names)
      (cn : cons_names) (γ : gname) (Rd : nat -> iProp Σ) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    riscv_cons_res = cons_res_triv ->
    app_taint = kill_cred_triv ->
    ⊢ image_entry_taint (tree_taint c)
        (ucons_pay cn γ (tree_taint c) Rd) uslot.
  Proof using .
    intros Heq Hcons Hkill.
    (* the key's all-parked row (lane OFF-HAND-4, S2) is not read here:
       the generic slot is quantified over every key *)
    rewrite /image_entry_taint. iIntros "!>" (W') "#HT Hmp".
    iDestruct (tree_gen_slot c r Heq Hcons Hkill with "HT") as "#Hgen".
    iApply ("Hgen" $! (ucons_pay cn γ (tree_taint c) Rd (-1)) W'
              with "[Hmp] []").
    - rewrite ucons_pay_eta. iExact "Hmp".
    - iModIntro. iIntros "_". iApply (ucons_pay_taint with "HT").
  Qed.

  (* =================================================================== *)
  (*  2.  THE EXEC SUPPLY ITSELF                                          *)
  (*                                                                     *)
  (*  [UInitSh.init_exec_sup_of_sh_slot]'s tree twin, and it is short     *)
  (*  because NOTHING of the exec'd image is claimed: the walk is the     *)
  (*  taint's, the entry is the generic slot, and the only reading left   *)
  (*  is /init's own -- the path `sh` out of its read-only image, which   *)
  (*  is where a0 points ([UInitSh.init_sh_path_of], a fact about /init   *)
  (*  and not about the shell).  The identity fragments and the           *)
  (*  descriptor row the node is handed are not read at all here: they    *)
  (*  are what a VERIFIED entry constructor reads, and there is none.     *)
  (* =================================================================== *)
  (* ---- 2a.  THE NODE, WITH THE TAINT ALREADY IN HAND ------------------ *)
  (*  THE WHOLE BODY LIVES HERE, and the two supplies below differ only in *)
  (*  where they get the taint from: the wand form reads it off the        *)
  (*  credential the caller hands it, and the CLOSED form mints it out of  *)
  (*  the round's own lend ([UInitTree.tree_lend_taint]) through the update *)
  (*  door the node's conclusion now carries ([UkInit.init_exec_sup_pos],  *)
  (*  lane TL-9).                                                          *)
  Lemma tree_init_exec_sup_pos (c : tree_fixed) (r : tree_names)
      (cn : cons_names) (stc : fdstate) (γ : gname) (np : nat) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    riscv_cons_res = cons_res_triv ->
    app_taint = kill_cred_triv ->
    tree_taint c -∗
    UkInit.init_exec_sup_pos cn (tree_taint c) stc (tree_cc c) γ np.
  Proof using .
    intros Heq Hcons Hkill. iIntros "#HT".
    rewrite /UkInit.init_exec_sup_pos.
    iIntros (N m pc l)
      "%Hpeq %Ha0 %Ha1 #Hro #Hargv Hstd Hrow Hcred Hpos Hlease Hchf Hpidf".
    (* THE DOOR IS FREE HERE: the taint is a premise of this lemma, so
       nothing is spent to open the update. *)
    iModIntro.
    iAssert (image_entry_taint (tree_taint c) (ukn_pay N) uslot) as "#Hgen".
    { rewrite Hpeq.
      iApply (tree_image_entry_taint c r cn γ
                (UkInit.init_rd (cc_rd (tree_cc c)) (cc_wbn (tree_cc c)))
                Heq Hcons Hkill). }
    iApply (udepw_at_refR_ids_of_sup_ids N m pc
              (mword_of_int 0x9a8) (mword_of_int 0x1000)
              FsImg.ROOTINO (tree_taint c) UInitSh.init_sh_pl
              ElfUser.sh_elf 1%nat
              (UserFd.ustd (ukn_fd N) l ∗ upos γ np
                 ∗ ucons_pay cn γ (tree_taint c) (cc_rd (tree_cc c)) (-1)
                 ∗ UkInit.init_lend_cred (tree_taint c) stc
                     (cc_wp (tree_cc c)) (cc_wbn (tree_cc c)) l np)%I
              _ sh_elf_loadable Ha0 Ha1
              with "[] Hgen [Hstd Hpos Hlease Hcred]").
    (* ---- THE REFUND IS THE LEND ITSELF ([UkInit.init_lend_ref]): what
           went into the deposit comes back at the shapes it went in at,
           which is what pays the child's diagnostic and its exit. ---- *)
    { iIntros "!> (Hstd & Hps & Hls & Hcred)".
      rewrite /UkInit.init_lend_ref. iFrame "Hstd Hps Hls Hcred". }
    rewrite /uexec_sup_run_ids.
    iIntros (M pm sz fdv cs pidv) "#Hnpw Hheap Hufd Hids".
    (* /init's own image reading, off the lent heap *)
    iAssert (⌜uimg_sub UCodeInit.init_ro M⌝)%I as %Hsro.
    { iIntros (a b Hb). rewrite /UCodeInit.init_rodata /utext_img.
      iDestruct (big_sepM_lookup _ _ a b Hb with "Hro") as "Hb".
      iDestruct (uheap_text with "Hheap Hb") as %(HM & _ & _).
      iPureIntro. exact HM. }
    iFrame "Hheap Hufd Hids".
    iSplitR; [ iPureIntro; exact (UInitSh.init_sh_path_of M Hsro) | ].
    iSplitR; [ iApply (exec_walk_of_taint with "HT") | ].
    (* the taint arm takes nothing about the exec'ing table's offsets
       (design/app-file.md section 3, fact 4, after lane OFF-HAND-6) *)
    iSplitR "Hstd Hpos Hlease Hcred";
      [ iApply (image_entry_of_taint _ _ _ _ _ _ _ _ _ _ _ with "HT Hgen") | ].
    iFrame "Hstd Hpos Hlease Hcred".
  Qed.

  (* ---- 2b.  THE SUPPLY AS A WAND FROM THE TAINT ----------------------- *)
  Lemma tree_init_exec_sup_lend (c : tree_fixed) (r : tree_names)
      (cn : cons_names) (stc : fdstate) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    riscv_cons_res = cons_res_triv ->
    app_taint = kill_cred_triv ->
    tree_taint c -∗
    UkInit.init_exec_sup_lend cn (tree_taint c) stc (tree_cc c).
  Proof using .
    intros Heq Hcons Hkill. iIntros "#HT".
    rewrite /UkInit.init_exec_sup_lend. iIntros "!>" (γ np).
    iApply (tree_init_exec_sup_pos c r cn stc γ np Heq Hcons Hkill with "HT").
  Qed.

  (* ---- 2c.  ...AND THE SUPPLY FROM NOTHING, WHICH IS WHAT THE UPDATE
         DOOR BUYS (lane TL-9; design/user-tree.md 9.8).

     THIS IS THE STATEMENT LANE TL-8 REFUTED, and what changed is not the
     token count but where the tokens may be spent.  The node is handed
     the round's credential ([UkInit.init_lend_cred]) and its conclusion
     is an UPDATE now, so the credential can be turned into the taint
     INSIDE the node: the console row reads it ([UInitTree.tree_cc_wp]),
     the closed row MINTS it ([UInitTree.tree_cc_wbn_mint] -- the row where
     the banner was never written, so the era's licence is still unspent),
     and the taint arm hands it over.  [UInitTree.tree_lend_taint] is all
     three, and the lend it gives back is what the deposit's REFUND still
     needs ([UkInit.init_lend_ref]) -- which is why the mint had to run
     here and not before the node.

     WHAT IT COSTS THE ERA: nothing that the dance does not already pay.
     The taint is persistent once minted, so the [box] over this supply
     re-derives it per round from whatever credential that round carries;
     and on the rounds where the banner HAS run the credential is already
     the taint and the mint does not fire at all. *)
  Lemma tree_init_exec_sup_lend_of_lend (c : tree_fixed) (r : tree_names)
      (cn : cons_names) (stc : fdstate) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    riscv_cons_res = cons_res_triv ->
    app_taint = kill_cred_triv ->
    ⊢ UkInit.init_exec_sup_lend cn (tree_taint c) stc (tree_cc c).
  Proof using .
    intros Heq Hcons Hkill.
    rewrite /UkInit.init_exec_sup_lend. iIntros "!>" (γ np).
    rewrite /UkInit.init_exec_sup_pos.
    iIntros (N m pc l)
      "%Hpeq %Ha0 %Ha1 #Hro #Hargv Hstd Hrow Hcred Hpos Hlease Hchf Hpidf".
    iMod (tree_lend_taint c stc l np with "Hcred") as "[Hcred #HT]".
    iDestruct (tree_init_exec_sup_pos c r cn stc γ np Heq Hcons Hkill
                 with "HT") as "Hnode".
    rewrite /UkInit.init_exec_sup_pos.
    iApply ("Hnode" $! N m pc l with "[//] [//] [//] Hro Hargv Hstd Hrow
                                      Hcred Hpos Hlease Hchf Hpidf").
  Qed.

  (* ...AND THE SUPPLY AS /INIT'S WALK TAKES IT, AT [Cns := True] (lane
     TL-9).  Both halves of [UkInit.init_cons_sup] are one line: the wand
     from the credential asks for nothing, because the supply is closed
     ([tree_init_exec_sup_lend_of_lend]), and the law that pays the
     credential under the taint is [True]'s.

     WHY [Cns := True] IS THE ONE THAT MATTERS.  [Cns] is what /init's own
     console dance has to LEAVE ([UInitKernel.init_boot_pay]'s first
     conjunct), and TL-7's dance is landed at [True]
     ([UInitTreeBoot.tree_init_cons_dance_all]) with the era's DEED as its
     linear credential.  At [Cns := tree_taint c] the dance's leaves would
     have to mint the taint as well, i.e. spend a second licence in the
     same [*]-separated payload as [cc_wbn 0] -- and [App.al_pow] files one
     licence per power-on.  That is TL-8's wall (9.7(4)), and this
     statement is what retires it. *)
  Lemma tree_init_cons_sup (c : tree_fixed) (r : tree_names)
      (cn : cons_names) (stc : fdstate) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    riscv_cons_res = cons_res_triv ->
    app_taint = kill_cred_triv ->
    ⊢ UkInit.init_cons_sup cn (tree_taint c) True stc (tree_cc c).
  Proof using .
    intros Heq Hcons Hkill. rewrite /UkInit.init_cons_sup. iSplit.
    - iIntros "!> _".
      iApply (tree_init_exec_sup_lend_of_lend c r cn stc Heq Hcons Hkill).
    - iIntros "!> _". done.
  Qed.

  (* =================================================================== *)
  (*  3.  WHAT THE SUPPLY BUYS: /INIT'S WHOLE ENTRY SLOT AT THE TREE      *)
  (*                                                                     *)
  (*  [UInitKernel.init_boot_con] at this claim, with every premise of    *)
  (*  its list discharged.  Three are the tree's own -- the deposits      *)
  (*  ([UInitTree.tree_init_deps]), the kill row                          *)
  (*  ([UInitTree.tree_init_kill_law], section 9.5(2)) and the exec       *)
  (*  supply above -- and the rest is echo's assembly reused VERBATIM,    *)
  (*  which is what section 9.5(5) predicted: the room arithmetic         *)
  (*  ([UInitBoot.init_boot_room]), the ledger's length and its head, the *)
  (*  nopipe fact and [psok] at the free instance.                        *)
  (*                                                                     *)
  (*  So nothing between /init's entry and its boot bundle is echo's any  *)
  (*  more.  What D4 still owes is recorded at the two lemmas below.      *)
  (* =================================================================== *)
  Lemma tree_init_boot_con (c : tree_fixed) (r : tree_names) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    riscv_cons_res = cons_res_triv ->
    app_taint = kill_cred_triv ->
    ⊢ □ (∀ W' : uvis,
           ⌜kexec_image_ok ElfUser.init_elf 1%nat (fun _ => 5%nat)
              (fun _ => init_boot_bytes) fdt0 W'⌝ -∗
           ⌜uvis_cwd W' = FsImg.ROOTINO⌝ -∗
           ⌜uvis_lazy W' = false⌝ -∗
           ⌜uvis_secc W' = ProcDefs.secc_all⌝ -∗
           my_pay (uvis_gen W') (fun _ => True)%I -∗
           UInitKernel.init_boot_pay (PS := uprogSG_free) (tree_taint c)
             True fsc_cons init_cons_fd (tree_cc c) -∗
           uslot W').
  Proof using .
    intros Heq Hcons Hkill.
    iApply (UInitKernel.init_boot_con (PS := uprogSG_free)
              (tree_taint c) True%I init_cons_fd (tree_cc c) fsc_cons
              1%nat (fun _ => 5%nat) (fun _ => init_boot_bytes) fdt0 0%nat
              init_cons_fd_ne
              (tree_init_kill_law c init_cons_fd)
              (init_boot_room 0%nat ltac:(vm_compute; discriminate))
              fdt0_length eq_refl (fdv_nopipe_closed _)
              (fun k H => H)
              with "[] [] []").
    - iApply (tree_init_deps c r Heq Hcons Hkill).
    - iApply (udep_free).
    - iApply (tree_init_cons_sup c r fsc_cons init_cons_fd Heq Hcons Hkill).
  Qed.

  (* the read family is trivial at this record, so the boot bundle's third
     conjunct costs nothing *)
  Lemma tree_cc_rd_triv (c : tree_fixed) (n : nat) : ⊢ cc_rd (tree_cc c) n.
  Proof using . exact (bi.True_intro _). Qed.

  (* ...AND THE PAYLOAD THE SLOT IS SPENT AT.  Six conjuncts, and only TWO
     of them cost the era anything: the console dance and the banner-owed
     credential [cc_wbn 0].  The banner law and the two diagnostics are
     [UInitTree]'s, off the deposits, and the read credential is [True].

     ONLY ONE OF THE TWO COSTS A LICENCE NOW (lane TL-9), and that is what
     retires TL-8's wall (section 9.7(4)).  The dance is taken AS TL-7
     LANDED IT, at [Cns := True] ([UInitTreeBoot.tree_init_cons_dance_all]),
     whose linear credential is the era's DEED and not the taint -- so the
     era's single licence ([AppTree.tree_licence_mint], one row per
     power-on) goes where the design always said it goes: into [cc_wbn 0],
     the banner-owed credential, which is what makes the banner the mint
     (section 9.5(3)).  [UInitTree.tree_cc_wbn_of_turn] is the one step. *)
  Lemma tree_init_boot_pay (c : tree_fixed) (r : tree_names)
      (cn : cons_names) (stc : fdstate) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    riscv_cons_res = cons_res_triv ->
    app_taint = kill_cred_triv ->
    UInitKernel.init_cons_dance_all (PS := uprogSG_free) (tree_taint c)
      True%I stc -∗
    ucons_reader cn 0%nat -∗
    tree_turn c -∗
    UInitKernel.init_boot_pay (PS := uprogSG_free) (tree_taint c)
      True cn stc (tree_cc c).
  Proof using .
    intros Heq Hcons Hkill. iIntros "Hdn Hrd Htn".
    iDestruct (tree_cc_wbn_of_turn c 0%nat with "Htn") as "Hbn".
    iDestruct (tree_init_deps c r Heq Hcons Hkill) as "#Hdp".
    rewrite /UInitKernel.init_boot_pay.
    iSplitL "Hdn"; [ iExact "Hdn" | ].
    iSplitL "Hrd"; [ iExact "Hrd" | ].
    iSplitR; [ iApply tree_cc_rd_triv | ].
    iSplitL "Hbn"; [ iExact "Hbn" | ].
    iSplitR.
    - iIntros "!>" (n N') "Hwb".
      iDestruct (tree_kinit_ban_law c stc N' with "Hdp") as "#Hbl".
      iApply ("Hbl" with "Hwb").
    - iApply (tree_kinit_diag_law c stc with "Hdp").
  Qed.

  (* =================================================================== *)
  (*  4.  /INIT'S ENTRY SLOT AT THE TREE CLAIM, EVERY PREMISE PAID        *)
  (*      (lane TL-9; design/user-tree.md section 9.8)                    *)
  (*                                                                     *)
  (*  [UInitKernel.init_boot_con] APPLIED, at the payload                 *)
  (*  [tree_init_boot_pay] builds -- so this is /init's whole walk at the *)
  (*  tree claim, from the era's own resources and nothing else:          *)
  (*                                                                     *)
  (*    the era's first DEED ([AppTree.tree_boot]'s), which pays the      *)
  (*      console dance (TL-7) -- in LIVE, because the dance's mknod      *)
  (*      moves it;                                                       *)
  (*    the era's one LICENCE ([App.app_turn]), which pays [cc_wbn 0] --  *)
  (*      the banner-owed credential, i.e. the mint at the banner's first *)
  (*      byte (section 9.5(3));                                          *)
  (*    the kernel's READER token, born with the console ring at boot;    *)
  (*    and the claim itself.                                            *)
  (*                                                                     *)
  (*  The exec of /sh needs NOTHING further: at [Cns := True] the supply  *)
  (*  is closed ([tree_init_cons_sup]) and mints the taint out of the     *)
  (*  round's own credential when the round reaches the exec.             *)
  (*                                                                     *)
  (*  WHAT IS STILL BETWEEN THIS AND A BEHAVIOURAL [tree_Hinit_boot], and *)
  (*  it is not this file's to fix.  [InitBoot.init_boot_bundle] is the   *)
  (*  PINNED exec of /init itself, and                                    *)
  (*  [PinnedExec.pinned_exec_bundle_boot] (PinnedExec.v:537) takes its   *)
  (*  pin law under a [box] -- a walk reads the claim once per hop.  The  *)
  (*  tree claim pays such a law only from a FROZEN deed                  *)
  (*  ([TreeExec.exec_walk_of_own], TreeExec.v:89, takes                  *)
  (*  [AppTree.tree_pin]), and [AppTree.tree_freeze] is one-way -- so     *)
  (*  freezing the era's one boot deed to pay the boot walk leaves the    *)
  (*  dance below with no live deed for its mknod.  Independently,        *)
  (*  [AppTree.tree_boot] (AppTree.v:2546) quantifies the deed's subtree  *)
  (*  EXISTENTIALLY and [App.al_programs] (App.v:371) hands [Hinit_boot]  *)
  (*  no image premise, so nothing identifies that subtree with the one   *)
  (*  that resolves "/init" to [ElfUser.init_elf].  Both are recorded in  *)
  (*  design/user-tree.md section 9.8.                                    *)
  (* =================================================================== *)
  Lemma tree_init_boot_uslot (c : tree_fixed) (r : tree_names) (g : gname)
      (t : ttree) (e : gmap fname Z) (W' : uvis) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    riscv_cons_res = cons_res_triv ->
    app_taint = kill_cred_triv ->
    (* THE ONE IMAGE FACT /INIT'S SETUP NEEDS, and it is about the deed's
       own tree: the root is a directory and it has no [console] entry
       yet, which is the arm TL-7's dance is landed on. *)
    tv_nodes t !! FsImg.ROOTINO = Some (ADir e) ->
    e !! fname_console = None ->
    (* ...and the key the kernel resumes <init> at *)
    kexec_image_ok ElfUser.init_elf 1%nat (fun _ => 5%nat)
      (fun _ => init_boot_bytes) fdt0 W' ->
    uvis_cwd W' = FsImg.ROOTINO ->
    uvis_lazy W' = false ->
    uvis_secc W' = ProcDefs.secc_all ->
    app_inv fsc_fs -∗
    tree_own r g FsImg.ROOTINO t -∗
    tree_turn c -∗
    ucons_reader fsc_cons 0%nat -∗
    my_pay (uvis_gen W') (fun _ => True)%I -∗
    uslot W'.
  (* the dance's leaves reach two more of the section's classes than this
     file's other statements do *)
  Proof using GEN fileG0 ghost_varG0 riscvGS0 treeG0 uartGhostG0 ufdG0 xv6G0 Σ.
    intros Heq Hcons Hkill Hd He Hok Hcw Hlz Hscf.
    iIntros "#Hinv Hown Htn Hrd Hmp".
    iDestruct (tree_init_boot_con c r Heq Hcons Hkill) as "#Hcon".
    iApply ("Hcon" $! W' with "[%] [%] [%] [%] Hmp [Hown Htn Hrd]");
      [ exact Hok | exact Hcw | exact Hlz | exact Hscf | ].
    iApply (tree_init_boot_pay c r fsc_cons init_cons_fd Heq Hcons Hkill
              with "[Hown] Hrd Htn").
    iApply (tree_init_cons_dance_all c r g t e Heq Hd He with "Hinv Hown").
  Qed.

End UInitTreeExec.
