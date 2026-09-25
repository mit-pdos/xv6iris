(* ===================================================================== *)
(* TreeExec.v -- PIN-FREE exec: EX-2's SUCCESSOR, AT AN OWNED SUBTREE.    *)
(*                                                                       *)
(* design/user-tree.md section 4 item 2, lane TL-3 deliverable 1.  The    *)
(* whole-file-system pin ([FsShPin], echo's era) is how a verified        *)
(* program has so far answered exec's (W) -- “the file this path names is *)
(* THIS image” -- and design/user-exec.md's EX-2 refuted the other route  *)
(* (a held [FsAbs.nview] share: custody of a live inode is total, nothing *)
(* crosses an ecall).  THE THIRD ROUTE is this one: the program holds a   *)
(* FROZEN DEED on a subtree of the live namespace, and the file it execs  *)
(* is a row of its own tree.  Nothing about the REST of the file system   *)
(* is claimed -- other processes may create, write and unlink outside the *)
(* deed's subtree and the walk still answers.                            *)
(*                                                                       *)
(* WHAT IT IS MADE OF, and there is nothing else in this file:            *)
(*   - [TreeObs.tree_pin_claim_law]: the deed, as the [□] claim law;      *)
(*   - [TreeObs.tree_pin_resolves_file]: the deed, as an absnode pin;     *)
(*   - [ExecRun.exec_walk_of_abs_pin]: the pin, as (W) at the node's      *)
(*     CONTENT (the link count is not pinned by a tree claim and is never *)
(*     spent by exec -- PinnedObs section 10, ExecRun section 6).         *)
(*                                                                       *)
(* WHY THE RULE IS [ExecRun.wp_uk_ecall_exec_run_abs] AND NOT             *)
(* [wp_uk_ecall_exec_run].  The landed rule names an [anode] -- the row   *)
(* WITH its link count -- and the tree claim cannot pin one: two views    *)
(* the claim admits may differ in the terminal row's [nlink] (a hard link *)
(* OUTSIDE the subtree changes it and the subtree does not move), so      *)
(* there is no [nl] at which [exec_walk_of] could be stated.  The         *)
(* content-level rule is the landed one with that count dropped, and      *)
(* [ExecBundle.v] is untouched (its (W.iii) is a parameter of both).      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import UserCwd.
Require Import UexecRet UsysMemOk.
Require Import UkRun UkRunSys.
Require Import ElfFile.          (* [elf_bytes] *)
Require Import PathElems.        (* [path_elems] / [SLASH] *)
Require Import FsTree.           (* [fname] / [fs_proper] *)
Require Import FsImg.            (* [ROOTINO] *)
Require Import SpecKexec.        (* [kexec_loadable] *)
Require Import AppCfg AppInv.
Require Import FsCfg.            (* [fsc_fs] *)
Require Import ExecEntry.        (* [image_entry] / [image_entry_taint] *)
Require Import ExecRun.          (* [exec_walk_of_abs], the content-level rule *)
Require Import FsAbsEra.         (* [um_start_of] *)
Require Import TreeView.
Require Import AppTree.
Require Import TreeObs.
Require Import FsAbsDefs.
Import Defs.

Local Open Scope Z_scope.

Section TreeExec.
  (* [ExecRun]'s binder list plus the tree application's own class *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!treeG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  (* ------------------------------------------------------------------ *)
  (*  1.  (W), OUT OF A FROZEN DEED                                       *)
  (* ------------------------------------------------------------------ *)

  (* THE LEMMA THE DESIGN PAGE PROMISED (section 4 item 2), at the shapes
     the landed seam forces.  Everything on the left is the program's own
     knowledge: its deed, the era's record equation, and the PURE fact that
     the path it is about to pass resolves INSIDE its tree to a file. *)
  Lemma exec_walk_of_own (c : tree_fixed) (r : tree_names) (g : gname)
      (root d i : Z) (t : ttree) (f : elf_bytes)
      (cw : Z) (pl : list (bv 8)) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    fs_proper (path_elems pl) ->
    um_start_of cw pl = d ->
    d ∈ dom (tv_nodes t) ->
    resolves_from t d pl = Some (i, AFile f) ->
    tree_pin r g root t -∗
    app_inv fsc_fs -∗
    exec_walk_of_abs cw (tree_taint c) pl (AFile f).
  Proof using .
    intros Heq Hp Hstart Hd Hres. iIntros "#Hpin #Hinv".
    iDestruct (tree_pin_claim_law c r g root t Heq with "Hpin") as "#Hcl".
    iApply (exec_walk_of_abs_pin (fun v => subtree v root = Some t)
              (tree_taint c) cw pl (resolve_hops t d pl) i (AFile f)
              (tree_pin_resolves_file root d i t f cw pl Hp Hstart Hd Hres)
              with "Hcl Hinv").
  Qed.

  (* ...AND AT AN ABSOLUTE PATH UNDER "/", which is the shape a boot
     process's deed ([AppTree.tree_boot]) takes: the era's first owner
     holds "/" and execs "/init"'s successor by its absolute name. *)
  Lemma exec_walk_of_own_root (c : tree_fixed) (r : tree_names) (g : gname)
      (i : Z) (t : ttree) (f : elf_bytes) (cw : Z) (pl : list (bv 8)) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    fs_proper (path_elems pl) ->
    pl !! 0%nat = Some SLASH ->
    FsImg.ROOTINO ∈ dom (tv_nodes t) ->
    resolves_from t FsImg.ROOTINO pl = Some (i, AFile f) ->
    tree_pin r g FsImg.ROOTINO t -∗
    app_inv fsc_fs -∗
    exec_walk_of_abs cw (tree_taint c) pl (AFile f).
  Proof using .
    intros Heq Hp Hsl Hd Hres.
    exact (exec_walk_of_own c r g FsImg.ROOTINO FsImg.ROOTINO i t f cw pl Heq
             Hp (um_start_of_slash cw pl Hsl) Hd Hres).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2.  THE CONSUMER TEST: A PROGRAM EXECS A FILE OF ITS OWN SUBTREE    *)
  (*                                                                      *)
  (*  [ExecRun.wp_uk_ecall_exec_pin_test] with the WHOLE-FS PIN REPLACED  *)
  (*  BY A DEED.  Everything a new program's author writes is here and    *)
  (*  nothing else: the deed, the era's record equation, the pure         *)
  (*  resolution inside its own tree, the path reading off its image, the *)
  (*  loadability by computation, and the exec'd program's own entry      *)
  (*  theorem.  NO [app_pred] pin of the file system, and no claim about  *)
  (*  any row outside the deed's subtree.                                 *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_uk_ecall_exec_own_test (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (pv av : mword 64)
      (c : tree_fixed) (r : tree_names) (g : gname)
      (root cw i : Z) (t : ttree) (f : elf_bytes)
      (pl : list (bv 8)) (Pay R : iProp Σ) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    usysno m = USYS_exec ->
    m !!! Regidx a0_idx = pv ->
    m !!! Regidx a1_idx = av ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (* (L), decided ([ElfLoadable.kexec_loadable_of_b]) *)
    kexec_loadable f ->
    (* (W)'s content, PURELY: the path starts where the start rule says,
       that row is in the program's own tree, and the tree resolves it to
       this image *)
    fs_proper (path_elems pl) ->
    um_start_of cw pl = root ->
    root ∈ dom (tv_nodes t) ->
    resolves_from t root pl = Some (i, AFile f) ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    (* THE DEED, FROZEN: "I own the subtree [t] at [root], and I will never
       move it again" ([AppTree.tree_freeze] is the one-way trade) *)
    tree_pin r g root t -∗
    app_inv fsc_fs -∗
    uexec_path_reading N pv pl -∗
    (* (E): the exec'd program's own theorem, at the caller's readings *)
    (* ...at the exec'ing process's table, which the entry may read for
       whether it holds a pipe row (design/pipe.md, "The exit path") *)
    □ (∀ (M : gmap Z (bv 8)) (fdv : list fdstate) (cs : gset gname)
         (pidv : mword 32),
         urun_rows N fdv -∗
         image_entry f M av fdv cw ProcDefs.secc_all cs pidv (ukn_pay N) Pay uslot) -∗
    image_entry_taint (tree_taint c) (ukn_pay N) uslot -∗
    □ (Pay -∗ R) -∗
    Pay -∗
    (∀ h' : CpuId,
       UserCwd.ucwd (ukn_cwd N) cw -∗ R -∗
       urun N h'
         (<[Regidx (mword_of_int 10) := (mword_of_int (-1) : mword 64)]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Ha0 Ha1 Hal4 Hload Hp Hstart Hd Hres.
    iIntros "#Hi Hrun Hcwd #Hpin #Hinv #Hrd #Hcon #Hgen #Hrf HPay Hcont".
    iApply (wp_uk_ecall_exec_run_abs N h m pc avail cw (tree_taint c) pv av
              pl f Pay R Hn Ha0 Ha1 Hal4 Hload
              with "Hi Hrun Hcwd Hrf Hgen [HPay] Hcont").
    rewrite /uexec_sup_run_abs. iIntros (M pm sz fdv cs pidv) "#Hnp Hheap Hufd".
    iDestruct ("Hrd" $! M pm sz with "Hheap") as %Hpath.
    iFrame "Hheap Hufd". iSplitR; [ by iPureIntro | ].
    iSplitR "HPay"; [ | iSplitR; [ iApply ("Hcon" with "Hnp") | iExact "HPay" ] ].
    iApply (exec_walk_of_own c r g root root i t f cw pl Heq Hp Hstart Hd Hres
              with "Hpin Hinv").
  Qed.

End TreeExec.
