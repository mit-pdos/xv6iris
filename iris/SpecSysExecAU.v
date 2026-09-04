(* SpecSysExecAU.v -- sys_exec's ATOMIC-UPDATE contract: [SpecKexecAU]'s
   bundle and arms lifted to the syscall boundary, where the arguments
   are READ OFF THE USER IMAGE rather than handed in.  A STATEMENT FILE.

   Design of record: SpecKexecAU.v's header (the exec AU: the walk, the
   one observation, the caller's own u-mode WP for the program observed)
   and claude-notes/design/user-wp-slot.md (the slot, and the trap
   contract's exec arm this level feeds).

   ==== WHAT THIS CONTRACT IS ==========================================

   A PARALLEL FORM beside [SpecSysExec.wp_sys_exec_sconf] (R10: the
   landed contract does not move): the same frame row for row -- the
   block-layer geometry relayed to kexec, the two trapframe arguments,
   [eb = true], the fabric, the process -- with the bundle [EXTRA] after
   the process block and the armed post in place of the landed
   [sys_exec_post].

   THE ONE THING THIS LEVEL ADDS: the argument vector is not a
   parameter.  sys_exec [fetchaddr]s each [argv[i]] out of the user's
   image at trapframe argument 1 and [fetchstr]s each string into a
   kernel page, then calls kexec with what it read.  So the arguments
   kexec sees are a READING of the user image at the argv pointer,
   [exec_args_of (us_M U) v1 na alen afun] (section 1), and the
   caller's WP premise is quantified over every reading the image
   admits ([sys_exec_slot_pre]): a caller that knows its own argv
   (init: ["sh"] at a known address of its own image) instantiates it
   once; the success arm then names the reading kexec ran at.

   THE CONTINUATION keeps the landed shape: [(mf, P', M')] with the
   page-table growth report and an EXISTENTIAL image, exactly as
   [SpecSysExec] states it today (milestone J item 1's staging).  The
   U-mode side's row for exec's failure is [r = -1 /\ M' = M]
   ([UsysMemOk]); tightening this frame's failure arm to same-M is the
   landed contract's own open item and is not taken here -- the AU form
   parallels, it does not overtake.

   ==== THE ARMS ========================================================

   ret = argc: [SpecKexecAU.exec_post_ok] at the block after the
   copy-ins' growth ([us_upt U P']), at the reading [na alen afun] the
   success arm exhibits.  Its arm (a) hands back [uslot (exec_key U' sts
   na)] -- THE PROPOSITION THE DISPATCH DEPOSITS for the new process --
   and arm (b) the refunds.
   ret = -1: the landed failure equation on the block ([us_V U' =
   us_upt-ed V]) beside [SpecKexecAU.exec_post_fail]'s three-way fold,
   plus a FOURTH disjunct this level owns: sys_exec failed BEFORE kexec
   (a bad path or argv pointer, too many arguments, out of kernel
   pages), with the whole bundle back unspent -- indistinguishable from
   kexec's (i) by the return value, so folded into the same [∨].

   ==== WHAT THE PROVER OWES ===========================================

   1. The argv reading: [fetchaddr]/[fetchstr]'s posts relate the words
      and bytes they copied to [us_M U] at [v1] -- [exec_args_of] is
      exactly the conjunction of those posts over the loop.
   2. [SpecKexecAU]'s contract at the reading, with the bundle
      specialized by [sys_exec_slot_pre]'s ∀.
   3. The kfree/kalloc bookkeeping of the landed proof, verbatim.

   BINDERS: SpecSysExec's plus [ufdG] (the slot). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import Xv6Cameras.
Require Import BioDefs.
Require Import LogInv.
Require Import BitmapInv.
Require Import InodeInv.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecDirlink.    (* [ic_sleeplocks], [ireg_blocks_ok] *)
Require Import ByteBuf.        (* [bb_cstr]                          *)
Require Import FsBlocks.       (* [fs_names]                         *)
Require Import FsTree.         (* [fname]                            *)
Require Import PathElems.
Require Import SpecKexec.      (* [MAXARG], [kexec_ok]               *)
Require Import SpecSysExec.    (* the landed frame this file parallels: [K_sys_exec] *)
Require Import ElfFile.        (* [elf_bytes]                        *)
Require Import UmodeAbi.
Require Import UserFd.         (* [ufdG]                             *)
Require Import UexecSlot.      (* [uvis]                             *)
Require Import UexecRet.       (* [uslot]                            *)
Require Import SpecSysOpenAU.  (* [open_walk_pre_era], [aopen_commit_at] *)
Require Import SpecKexecAU.    (* [exec_slot_pre], [exec_post_ok], [exec_post_fail] *)
Require Import FsAbsInv.       (* [fsabsE]                           *)
Require Import FsAbs.          (* LAST (FsAbs's own rule)            *)
Require Import FsBytesGamma.   (* [fs_gamma_L]                       *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE ARGUMENT VECTOR, AS A READING OF THE USER IMAGE               *)
(* ===================================================================== *)

(* the eight-byte little-endian word at [a] in the (lazy) image [M] *)
Definition uimg_word_at (M : gmap Z (bv 8)) (a : Z) (w : mword 64) : Prop :=
  forall k, (k < 8)%nat ->
    M !! (a + Z.of_nat k) = bv_to_little_endian 8 8 (bv_unsigned w) !! k.

(* THE READING sys_exec performs: [argv[0 .. na)] are non-null pointers
   read at [av + 8 i], [argv[na]] is NULL, and each pointer names a
   NUL-terminated string of [alen i] characters ([bb_cstr]: non-NUL
   below, NUL at [alen i]) whose bytes are [afun i].  The bound
   [na < MAXARG] and the per-argument page bound are kexec's own
   premises; here they are what makes the reading one kexec accepts, so
   they ride in the predicate rather than the frame. *)
Definition exec_args_of (M : gmap Z (bv 8)) (av : mword 64)
    (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8) : Prop :=
  (na < MAXARG)%nat
  /\ (exists avf : nat -> mword 64,
        (forall i, (i <= na)%nat ->
           uimg_word_at M (bv_unsigned av + 8 * Z.of_nat i) (avf i))
        /\ (forall i, (i < na)%nat -> avf i <> (mword_of_int 0 : mword 64))
        /\ avf na = (mword_of_int 0 : mword 64)
        /\ (forall i, (i < na)%nat ->
              bb_cstr (afun i) (alen i)
              /\ (Z.of_nat (alen i) < 4096)%Z
              /\ (forall j, (j <= alen i)%nat ->
                    M !! (bv_unsigned (avf i) + Z.of_nat j) = Some (afun i j)))).

(* ===================================================================== *)
(*  2.  THE BUNDLE AND THE ARMS AT THE SYSCALL BOUNDARY                   *)
(* ===================================================================== *)

Section SysExecAU.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  (* the caller's WP, for every argument reading the image admits *)
  Definition sys_exec_slot_pre (Φo : aview -> Z -> anode -> iProp Σ)
      (M : gmap Z (bv 8)) (av : mword 64) (sts : list fdstate) : iProp Σ :=
    (∀ (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8),
       ⌜exec_args_of M av na alen afun⌝ -∗
       exec_slot_pre Φo na alen afun sts)%I.

  Definition sys_exec_au_pre Γ (γfs : fs_names)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (M : gmap Z (bv 8)) (av : mword 64) (sts : list fdstate) : iProp Σ :=
    (open_walk_pre_era γfs P Pmiss
     ∗ aopen_commit_at Γ fsabsE Φo
     ∗ sys_exec_slot_pre Φo M av sts)%I.

  (* ret = -1: sys_exec's own early exits (the whole bundle back) folded
     with kexec's three-way fold at the reading it ran at *)
  Definition sys_exec_post_fail Γ (γfs : fs_names)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (M : gmap Z (bv 8)) (av : mword 64) (sts : list fdstate) : iProp Σ :=
    (sys_exec_au_pre Γ γfs P Pmiss Φo M av sts
     ∨ (∃ (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8),
          ⌜exec_args_of M av na alen afun⌝ ∗
          exec_post_fail Γ γfs P Pmiss Φo na alen afun sts))%I.

  (* the armed disjunction on the block after the copy-ins' growth [V]
     and the returned a0; [M] is the image the arguments were read from *)
  Definition sys_exec_arms Γ (γfs : fs_names) (γf : gname)
      (pj : mword 64) (pid : mword 32)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (M : gmap Z (bv 8)) (av : mword 64) (sts : list fdstate)
      (V : pprivate) (r : mword 64) : iProp Σ :=
    (∃ U' : ustate,
       proc_priv γf pj pid U' ∗
       ((⌜r = (mword_of_int (-1) : mword 64) /\ us_V U' = V⌝
         ∗ sys_exec_post_fail Γ γfs P Pmiss Φo M av sts)
        ∨ (∃ (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8),
             ⌜exec_args_of M av na alen afun⌝ ∗
             exec_post_ok Γ P Φo na alen afun sts (MkUstate V M) U' r)))%I.

  (* SANITY: the arms imply the landed [SpecSysExec.sys_exec_post] *)
  Lemma sys_exec_arms_landed Γ (γfs : fs_names) (γf : gname)
      (pj : mword 64) (pid : mword 32)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (M : gmap Z (bv 8)) (av : mword 64) (sts : list fdstate)
      (V : pprivate) (r : mword 64) :
    sys_exec_arms Γ γfs γf pj pid P Pmiss Φo M av sts V r ⊢
      sys_exec_post γf pj pid V r.
  Proof.
    rewrite /sys_exec_arms /sys_exec_post.
    iIntros "H". iDestruct "H" as (U') "[Hp [[[%Hr %HV] _] | H]]".
    - iExists U', 0%nat, (fun _ => 0%nat),
        (mword_of_int 0), (mword_of_int 0), (mword_of_int 0).
      iFrame "Hp". iPureIntro. left. split; [exact Hr | exact HV].
    - iDestruct "H" as (na alen afun) "[_ H]".
      iDestruct (exec_arms_landed Γ γfs P Pmiss Φo na alen afun sts
                   (MkUstate V M) U' r with "[H]") as %(entry & spv & szv' & Hok).
      { rewrite /exec_arms. iRight. iExact "H". }
      iExists U', na, alen, entry, spv, szv'. iFrame "Hp". iPureIntro. exact Hok.
  Qed.

End SysExecAU.

Global Typeclasses Opaque sys_exec_au_pre sys_exec_post_fail sys_exec_arms.

(* ===================================================================== *)
(*  3.  THE MACHINE CONTRACT: SpecSysExec's frame + the AU                *)
(* ===================================================================== *)

Definition wp_sys_exec_au_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ, !ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)                           (* ftable, kalloc      *)
    (gs : list gname) (j : nat) (gl : gname)            (* the running process *)
    (pd pav pu : mword 64)                              (* disk fabric + lock  *)
    (dqb dqs : dfrac)
    (v0 v1 : mword 64)                        (* syscall arguments 0 and 1 *)
    (pid : mword 32) (U : ustate) (sts : list fdstate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (P Pmiss : nat -> Z -> iProp Σ)
    (Φo : aview -> Z -> anode -> iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_exec in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let Γfs := fs_gamma_L fsc_fs in
  (K_sys_exec <= K)%nat ->
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  log_geom_ok fsc_cov fsc_logst ->
  0 < fsc_size <= BPB ->
  0 <= fsc_bmapstart ->
  fsc_bmapstart ∈ fsc_cov ->
  ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
  0 <= icfg_ist ->
  cov_below fsc_cov fsc_size ->
  ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  eb = true ->
  pv_tf (us_V U) !! tf_arg_idx 0 = Some v0 ->
  pv_tf (us_V U) !! tf_arg_idx 1 = Some v1 ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  fs_fabric gs pd pav pu -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  bslots 3 -∗
  kalloc_env fsc_kalloc None -∗
  iref_slots 2 -∗
  proc_priv γf pj pid U -∗
  (* ---- THE AU SIDE (the one addition to the landed premise list): the
     arguments are read off THIS image at argument 1 ---- *)
  sys_exec_au_pre Γfs fsc_fs P Pmiss Φo (us_M U) v1 sts -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (P' : uptd) (M' : gmap Z (bv 8)),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt (us_V U)) P'⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
      bslots 3 -∗
      kalloc_env fsc_kalloc None -∗
      iref_slots 2 -∗
      (* the armed post: the block after the copy-ins' growth, the
         arguments as read off the entry image, and -- on success at a
         loadable file -- the caller's slot at the resume key *)
      sys_exec_arms Γfs fsc_fs γf pj pid P Pmiss Φo (us_M U) v1 sts
        (upd_upt (us_V U) P')
        (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  4.  THE SEAL                                                          *)
(* ===================================================================== *)

Module Type SYSEXEC_AU.
  Parameter wp_sys_exec_au :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ, !ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (dqb dqs : dfrac)
      (v0 v1 : mword 64)
      (pid : mword 32) (U : ustate) (sts : list fdstate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ),
      wp_sys_exec_au_body γf gs j gl pd pav pu dqb dqs v0 v1 pid U sts
        m K eb b lks P Pmiss Φo.
End SYSEXEC_AU.
