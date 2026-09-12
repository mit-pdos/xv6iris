(* SpecSysExec.v -- sys_exec's ONE CONTRACT [SYSEXEC]: [SpecKexec]'s
   bundle and arms lifted to the syscall boundary, where the arguments
   are READ OFF THE USER IMAGE rather than handed in.  A STATEMENT FILE.

   Design of record: SpecKexec.v's header (the exec AU: the walk, the
   one observation, the caller's own u-mode WP for the program observed)
   and claude-notes/design/user-wp-slot.md (the slot, and the trap
   contract's exec arm this level feeds).

   ==== WHAT THIS CONTRACT IS ==========================================

   THE ONLY CONTRACT sys_exec has, and the only seal the dispatcher may
   take: [SysExecDefs.v] below is the vocabulary leaf
   ([K_sys_exec], [sys_exec_post]).  The frame is that file's own premise
   list row for row -- the block-layer geometry relayed to kexec, the two
   trapframe arguments, [eb = true], the fabric, the process -- with the
   bundle [EXTRA] after the process block and the armed post in the pure
   slot ([sys_exec_arms_landed] reads [sys_exec_post] back out of it).

   THE ONE THING THIS LEVEL ADDS: the path and the argument vector are
   not parameters.  sys_exec [argstr]s the path out of the user's image
   at trapframe argument 0, [fetchaddr]s each [argv[i]] at trapframe
   argument 1 and [fetchstr]s each string into a kernel page, then calls
   kexec with what it read.  So the caller's WP premise is quantified
   over what kexec may be handed ([sys_exec_slot_pre]) -- but GUARDED by
   what the image says it read, so a caller whose image it knows is owed
   the bundle at ONE path and ONE vector; the success arm names what it
   ran at.

   THE PATH IS READ, IN THE SHARED VOCABULARY.  The premise on it is
   [exec_path_of (us_M U) v0 pl] -- [ArgPath.arg_path_of], which open's
   and mknod's contracts state their own path arguments at too -- the
   bytes of [pl] ARE the process's bytes at argument 0, with
   the NUL after them -- so a caller that knows its own image and its own
   argument 0 (init: "/init" at a known address) instantiates the bundle
   at ONE path, which is what a pinned caller's cursor needs.  It is
   [SpecArgstr]'s postcondition read through
   [SpecFetchstr.fetchstr_got] to [SpecCopyinstr.copyinstr_got], and
   [exec_path_of_bview] ([ArgPath]'s) is the one step.

   THE ARGV VECTOR IS READ THE SAME WAY.  The premise on it is
   [exec_args_of (us_M U) v1 na alen afun] below: the SHAPE kexec wants
   ([exec_args_shape]: below MAXARG, NUL-terminated strings within a
   page), and, beside it, the pointers -- [argv[i]] is the process's own
   word at [v1 + 8 i], non-NULL below [na] and NULL at [na], each naming
   its string's bytes in the image.  It is [SpecFetchaddr.fetchaddr_got]
   at each pointer and [SpecFetchstr.fetchstr_got] at each string, both
   relayed by sys_exec's fill loop; the NULL at [na] IS the loop's exit
   test.  So a caller that knows its own image is owed the bundle at the
   one vector it passed, which is what a pinned caller's ROOM premise
   needs ([PinnedExec]).  [exec_args_of_shape] projects the shape back
   out where a consumer wants only that.

   THE CONTINUATION binds [(mf, P', M')] with the page-table growth
   report and an EXISTENTIAL image (milestone J item 1's staging).  The
   U-mode side's row for exec's failure is [r = -1 /\ M' = M]
   ([UsysMemOk]); tightening this frame's failure arm to same-M is an
   open item, recorded and not taken.

   ==== THE ARMS ========================================================

   ret = argc: [SpecKexec.exec_post_ok] at the block after the
   copy-ins' growth ([us_upt U P']), at the reading [na alen afun] the
   success arm exhibits.  Its arm (a) hands back [S (exec_key U' sts
   na)] -- THE PROPOSITION THE DISPATCH DEPOSITS for the new process, at
   the slot predicate [S] the whole contract is parametric in (SpecKexec
   header) -- and arm (b) the refunds.
   ret = -1: the landed failure equation on the block ([us_V U' =
   us_upt-ed V]) beside [SpecKexec.exec_post_fail]'s three-way fold,
   plus a FOURTH disjunct this level owns: sys_exec failed BEFORE kexec
   (a bad path or argv pointer, too many arguments, out of kernel
   pages), with the whole bundle back unspent -- indistinguishable from
   kexec's (i) by the return value, so folded into the same [∨].

   ==== WHERE THE PROOF PAYS EACH PIECE ================================

   1. The path reading: [exec_path_of] is [argstr]'s
      [SpecFetchstr.fetchstr_got] at trapframe argument 0, turned into a
      list by [exec_path_of_bview].  The argv reading: both halves of
      [exec_args_of] are the fill loop's own invariants read at the
      break -- the shape is [ProofSysExecParts.sx_ok] plus the loop's
      [i < 32], the pointers and strings are [sx_avok], and the
      terminating NULL is the [c.beqz] that left the loop.
   2. [SpecKexec.KEXEC] at that reading, with the bundle specialized by
      [sys_exec_slot_pre]'s ∀.
   3. The kfree/kalloc bookkeeping, shared with the blocks in
      [ProofSysExecParts].

   BINDERS: SysExecDefs's plus [ufdG] (the slot). *)
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
Require Import IcacheRefDefs.
Require Import IcacheInv.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecDirlink.    (* [ic_sleeplocks], [ireg_blocks_ok] *)
Require Import ByteBuf.        (* [bb_cstr]                          *)
Require Import SpecCopyin.     (* [uimg_word_at]: the image's word at an address *)
Require Import SpecCopyinstr.  (* [copyinstr_got]: the path's content *)
Require Import PathElems.      (* [path_elems]                       *)
Require Import DirentEnc.      (* [bview]                            *)
Require Import ArgPath.        (* [arg_path_of]: the path argument, read
                                  off the caller's own image -- exec's
                                  [exec_path_of] is its alias below *)
Require Import FsAbsEra.       (* [ex_start]: the walk at ONE path    *)
Require Import FsBlocks.       (* [fs_names]                         *)
Require Import KexecDefs.      (* [MAXARG], [kexec_ok]               *)
Require Import SysExecDefs.    (* the vocabulary leaf: [K_sys_exec], [sys_exec_post] *)
Require Import UserFd.         (* [ufdG]                             *)
Require Import ChildTok.       (* [my_pay]: the exec wand's pay fact *)
Require Import UexecSlot.      (* [uvis]                             *)
Require Import SysOpenDefs.  (* [namei_walk_pre_era], [aopen_commit_at] *)
Require Import SpecKexec.    (* [exec_slot_pre], [exec_post_ok], [exec_post_fail] *)
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import PieceFam.        (* [pfam]: a one-shot piece's receipt beside its refund *)
Require Import FsAbsDefs.          (* LAST (FsAbs's own rule)            *)
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

(* the eight-byte little-endian word at [a] in the (lazy) image [M] is
   [SpecCopyin.uimg_word_at], beside [copyin_got]: one image-reading
   vocabulary, at bytes and at words. *)

(* THE SHAPE of an argument vector kexec accepts (its own premises):
   below MAXARG, each argument a NUL-terminated string of [alen i]
   characters ([bb_cstr]: non-NUL below, NUL at [alen i]) shorter than a
   page.  This is what the WP premise is quantified over today (header). *)
Definition exec_args_shape (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) : Prop :=
  (na < MAXARG)%nat
  /\ (forall i, (i < na)%nat -> bb_cstr (afun i) (alen i))
  /\ (forall i, (i < na)%nat -> (Z.of_nat (alen i) < 4096)%Z).

(* THE READING sys_exec performs: the shape, and [argv[0 .. na)] non-null
   pointers read at [av + 8 i], [argv[na]] NULL, each pointer naming its
   string's bytes in the image.

   EVERY INDEX IS THE MACHINE'S OWN, [uint (add_vec_int p j)] -- modulo
   2^64 -- because that is what the copy loop's cursor does and what
   [SpecCopyinstr.copyinstr_got] hands over, so path and argument are one
   reading at two arguments and neither owes a no-wrap side condition.
   That applies to the POINTER index too: a user may pass an [av] near the
   top of the address space, and [argv[i]] is then read at the wrapped
   address.  Inside one word the eight bytes ARE consecutive in [Z]
   ([SpecCopyin.uimg_word_at]) -- [fetchaddr]'s own range test is what
   rules that wrap out, and it holds on the only arm that promises a
   value. *)
Definition exec_args_of (M : gmap Z (bv 8)) (av : mword 64)
    (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8) : Prop :=
  exec_args_shape na alen afun
  /\ (exists avf : nat -> mword 64,
        (forall i, (i <= na)%nat ->
           uimg_word_at M (uint (add_vec_int av (8 * Z.of_nat i))) (avf i))
        /\ (forall i, (i < na)%nat -> avf i <> (mword_of_int 0 : mword 64))
        /\ avf na = (mword_of_int 0 : mword 64)
        /\ (forall i, (i < na)%nat ->
              copyinstr_got M (avf i) (afun i) (alen i))).

Lemma exec_args_of_shape (M : gmap Z (bv 8)) (av : mword 64)
    (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8) :
  exec_args_of M av na alen afun -> exec_args_shape na alen afun.
Proof. intros [H _]. exact H. Qed.

(* THE PATH, THE SAME PAIR ONE ARGUMENT OVER, AND IT IS SHARED.  sys_exec
   [argstr]s the path at trapframe argument 0 into a kernel page and hands
   kexec the buffer; the bundle's walk premise is therefore stated AT ONE
   [pl] ([FsAbsEra.ex_start]) under a guard on that string, and not at
   every path.  THE GUARD IS THE READING, and the reading is not exec's:
   every path-taking syscall asks the same pure question of its own
   argument word, so it lives in [ArgPath.v] -- [arg_path_of M pv pl], the
   shape ([arg_path_shape]: NUL-free, int-sized) beside the tie to the
   image (byte [j] of [pl] is the process's byte at [pv + j], counted the
   copy loop's way, with a NUL just past the end), together with its
   [bview] suppliers and its uniqueness.  open and mknod state their
   bundles and receipts over the very same definition ([SysOpenDefs.v],
   [SpecSysMknod.v]).

   The six names below are exec's ALIASES for it, kept because this
   contract, [SysExecDefs], [PinnedExec] and sh's and init's program-side
   suppliers all read in exec's vocabulary; they are parsing-only
   notations, so a goal prints the shared name. *)
Notation exec_path_shape := arg_path_shape (only parsing).
Notation exec_path_of := arg_path_of (only parsing).
Notation exec_path_of_shape := arg_path_of_shape (only parsing).
Notation exec_path_shape_bview := arg_path_shape_bview (only parsing).
Notation exec_path_of_bview := arg_path_of_bview (only parsing).
Notation exec_path_of_uniq := arg_path_of_uniq (only parsing).

(* ===================================================================== *)
(*  2.  THE BUNDLE AND THE ARMS AT THE SYSCALL BOUNDARY                   *)
(* ===================================================================== *)

Section SysExecAU.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  (* the caller's WP, for every argument vector the process's own image at
     [av] holds ([exec_args_of]) and every path it holds at [pv]
     ([exec_path_of]) *)
  (* A PIECE, so its two families stay BARE: [S] is what the wand
     concludes at and [Φo] is the observation receipt it consumes. *)
  (* ...and over the PATHS it may have fetched, at the same guard the walk
     premise carries, because the cursor the slot wand consumes is at the
     last hop of THAT path ([exec_slot_pre]'s [Pfin]). *)
  (* ...AND THE CALLER'S WORKING DIRECTORY, threaded to [exec_slot_pre]'s
     two rows (2026-09-12, the coordinator): the syscall's bundle is stated
     at the same [cw] the boot's is ([SpecKexec.exec_au_pre]), so both hand
     the slot wands the inum the resumed key carries. *)
  Definition sys_exec_slot_pre (S : uvis -> iProp Σ) (Q : Z -> iProp Σ)
      (P : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ) (cw : Z)
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate) : iProp Σ :=
    (∀ (pl : list (bv 8)) (na : nat) (alen : nat -> nat)
       (afun : nat -> nat -> bv 8),
       ⌜exec_path_of M pv pl⌝ -∗ ⌜exec_args_of M av na alen afun⌝ -∗
       exec_slot_pre S Q (P (length (path_elems pl))) Φo cw na alen afun sts)%I.

  (* Both one-shot pieces at their pairs ([SpecKexec.exec_au_pre]'s
     shape, at the argument-shape-quantified slot wand). *)
  Definition sys_exec_au_pre (Fs : pfam Σ (uvis -> iProp Σ)) Γ
      (γfs : fs_names) (cw : Z) (Q : Z -> iProp Σ)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate) : iProp Σ :=
    ((∀ pl : list (bv 8), ⌜exec_path_of M pv pl⌝ -∗ ex_start γfs cw P Pmiss pl)
     ∗ pf_at (aopen_commit_at Γ appE) Fo
     ∗ pf_at (fun S => sys_exec_slot_pre S Q P Fo.(pf_recv) cw M pv av sts) Fs)%I.

  (* non-expansive in the slot predicate, as [SpecKexec.exec_au_pre_ne]:
     what UexecExecInst.v's instance at the fixpoint variable needs *)
  Lemma sys_exec_slot_pre_ne (n : nat) (S S' : uvis -d> iPropO Σ)
      (Q : Z -> iProp Σ) (P : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ) (cw : Z)
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate) :
    S ≡{n}≡ S' ->
    sys_exec_slot_pre S Q P Φo cw M pv av sts
    ≡{n}≡ sys_exec_slot_pre S' Q P Φo cw M pv av sts.
  Proof.
    intros HS. rewrite /sys_exec_slot_pre.
    apply bi.forall_ne; intros pl.
    apply bi.forall_ne; intros na. apply bi.forall_ne; intros alen.
    apply bi.forall_ne; intros afun. apply bi.wand_ne; [reflexivity |].
    apply bi.wand_ne; [reflexivity |].
    exact (exec_slot_pre_ne n S S' Q (P (length (path_elems pl)))
             Φo cw na alen afun sts HS).
  Qed.

  Lemma sys_exec_au_pre_ne (n : nat) (S S' : uvis -d> iPropO Σ) (Rs : iProp Σ)
      Γ (γfs : fs_names) (cw : Z) (Q : Z -> iProp Σ)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate) :
    S ≡{n}≡ S' ->
    sys_exec_au_pre (MkPfam S Rs) Γ γfs cw Q P Pmiss Fo M pv av sts
    ≡{n}≡ sys_exec_au_pre (MkPfam S' Rs) Γ γfs cw Q P Pmiss Fo M pv av sts.
  Proof.
    intros HS. rewrite /sys_exec_au_pre /pf_at. cbn [pf_recv pf_refund].
    by rewrite (sys_exec_slot_pre_ne n S S' Q P Fo.(pf_recv) cw M pv av sts HS).
  Qed.

  (* ret = -1: sys_exec's own early exits (the whole bundle back) folded
     with kexec's three-way fold at the reading it ran at *)
  Definition sys_exec_post_fail (Fs : pfam Σ (uvis -> iProp Σ)) Γ (γfs : fs_names) (cw : Z)
      (Q : Z -> iProp Σ)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate) : iProp Σ :=
    (sys_exec_au_pre Fs Γ γfs cw Q P Pmiss Fo M pv av sts
     ∨ (∃ (pl : list (bv 8)) (na : nat) (alen : nat -> nat)
          (afun : nat -> nat -> bv 8),
          ⌜exec_path_of M pv pl⌝ ∗ ⌜exec_args_of M av na alen afun⌝ ∗
          exec_post_fail Fs Γ γfs cw Q P Pmiss Fo pl na alen afun sts))%I.

  (* the armed disjunction on the block after the copy-ins' growth [V]
     and the returned a0; [M] is the image the arguments were read from *)
  Definition sys_exec_arms (Fs : pfam Σ (uvis -> iProp Σ)) Γ (γfs : fs_names) (cw : Z) (γf : gname)
      (pj : mword 64) (pid : mword 32) (Q : Z -> iProp Σ)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate)
      (* the two WAIT-EXIT readings the resume key is built at -- exec keeps
         the caller's identity and its children ([SpecKexec.exec_key]) *)
      (gn : gname) (cs : gset gname)
      (V : pprivate) (r : mword 64) : iProp Σ :=
    (∃ U' : ustate,
       proc_priv γf pj pid U' ∗
       ((⌜r = (mword_of_int (-1) : mword 64) /\ us_V U' = V /\ us_M U' = M⌝
         ∗ sys_exec_post_fail Fs Γ γfs cw Q P Pmiss Fo M pv av sts)
        ∨ (∃ (pl : list (bv 8)) (na : nat) (alen : nat -> nat)
             (afun : nat -> nat -> bv 8),
             ⌜exec_path_of M pv pl⌝ ∗ ⌜exec_args_of M av na alen afun⌝ ∗
             exec_post_ok Fs Γ Q P Fo pl na alen afun sts gn cs pid
               (MkUstate V M) U' r)))%I.

  (* SANITY: the arms imply the landed [SysExecDefs.sys_exec_post] *)
  Lemma sys_exec_arms_landed (Fs : pfam Σ (uvis -> iProp Σ)) Γ (γfs : fs_names) (cw : Z) (γf : gname)
      (pj : mword 64) (pid : mword 32) (Q : Z -> iProp Σ)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate)
      (gn : gname) (cs : gset gname)
      (V : pprivate) (r : mword 64) :
    sys_exec_arms Fs Γ γfs cw γf pj pid Q P Pmiss Fo M pv av sts gn cs V r ⊢
      sys_exec_post γf pj pid V r.
  Proof.
    rewrite /sys_exec_arms /sys_exec_post.
    iIntros "H". iDestruct "H" as (U') "[Hp [[(%Hr & %HV & _) _] | H]]".
    - iExists U', 0%nat, (fun _ => 0%nat),
        (mword_of_int 0), (mword_of_int 0), (mword_of_int 0).
      iFrame "Hp". iPureIntro. left. split; [exact Hr | exact HV].
    - iDestruct "H" as (pl na alen afun) "[_ [_ H]]".
      iDestruct (exec_arms_landed Fs Γ γfs cw Q P Pmiss Fo pl na alen afun sts gn cs
                   pid (MkUstate V M) U' r with "[H]") as %(entry & spv & szv' & Hok).
      { rewrite /exec_arms. iRight. iExact "H". }
      iExists U', na, alen, entry, spv, szv'. iFrame "Hp". iPureIntro. exact Hok.
  Qed.

End SysExecAU.

Global Typeclasses Opaque sys_exec_au_pre sys_exec_post_fail sys_exec_arms.

(* ===================================================================== *)
(*  3.  THE MACHINE CONTRACT: SysExecDefs's frame + the AU                *)
(* ===================================================================== *)

Definition wp_sys_exec_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (Fs : pfam Σ (uvis -> iProp Σ))                  (* the slot predicate the caller's WP concludes at *)
    (γf : gname)                           (* ftable, kalloc      *)
    (gs : list gname) (j : nat) (gl : gname)            (* the running process *)
    (pd pav pu : mword 64)                              (* disk fabric + lock  *)
    (dqb dqs : dfrac)
    (v0 v1 : mword 64)                        (* syscall arguments 0 and 1 *)
    (pid : mword 32) (U : ustate) (sts : list fdstate)
    (gn : gname) (cs : gset gname)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (Q : Z -> iProp Σ)
    (P Pmiss : nat -> Z -> iProp Σ)
    (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) :=
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
  (* ---- THE BUNDLE, the one addition to the premise list the vocabulary
     leaf's header describes: the arguments are read off THIS image at
     argument 1 ---- *)
  (* THE PAY FACT RIDES IN WITH THE BUNDLE -- see [SpecKexec]'s note; this
     contract relays it to kexec and does nothing else with it. *)
  my_pay gn Q -∗
  sys_exec_au_pre Fs Γfs fsc_fs (pv_cwi (us_V U)) Q P Pmiss Fo (us_M U) v0 v1 sts -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (P' : uptd) (M' : gmap Z (bv 8)),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
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
      sys_exec_arms Fs Γfs fsc_fs (pv_cwi (us_V U)) γf pj pid Q P Pmiss Fo (us_M U) v0 v1 sts
        gn cs (upd_upt (us_V U) P')
        (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  4.  THE SEAL                                                          *)
(* ===================================================================== *)

Module Type SYSEXEC.
  Parameter wp_sys_exec_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (Fs : pfam Σ (uvis -> iProp Σ))
      (γf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (dqb dqs : dfrac)
      (v0 v1 : mword 64)
      (pid : mword 32) (U : ustate) (sts : list fdstate)
      (gn : gname) (cs : gset gname)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (Q : Z -> iProp Σ)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)),
      wp_sys_exec_sconf_body Fs γf gs j gl pd pav pu dqb dqs v0 v1 pid U sts
        gn cs m K eb b lks Q P Pmiss Fo.
End SYSEXEC.
