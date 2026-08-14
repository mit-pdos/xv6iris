(* SpecKexecB3.v -- the public interface phase C will consume out of
   ProofKexecB3.v once it needs it: [kxc_b2] (the loop path) and [kxc_b2z]
   (the [elf.phnum = 0] path), phase B WHOLE -- both of phase B1's outputs,
   landing at +0x1ae, phase C's entry.  Stated independently of the proof
   that produces them, so requiring THIS file (fast, no [Qed] in it) is
   what phase C pays for, instead of requiring ProofKexecB3.v outright and
   serializing the two phases' builds.

   Same move as SpecKexecB2.v, one phase seam over: see that file's header
   and claude-notes/design/spec-modules.md.  Neither [kxc_b2] nor
   [kxc_b2z]'s STATEMENT mentions any of [KexecB3Proof]'s eleven functor
   arguments (Myproc, ... Uvmalloc) or [B3]'s own [B2]/[A] -- those are only
   in the PROOFS -- so [KEXECB3] below needs no functor parameters either.

   As of this writing ProofKexecC.v does not yet consume [kxc_b2]/
   [kxc_b2z] (the argv loop that will is still in progress -- see
   claude-notes/projects/kexec.md's checkpoint), so [KexecCProof] does not
   yet take a [(B3 : KEXECB3)] argument.  This file exists so that when
   that work resumes, the natural next step is to add that abstract
   argument -- never to reintroduce [Require Import ProofKexecB3.]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RegFile.
Require Import HartTp.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import StackBytes.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeHalf.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import SleepLock.
Require Import WpLock.
Require Import PanicStub.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import FsCrash.
Require Import InodeRegion.
Require Import IcacheEscrow.
Require Import ByteBuf.
Require Import VcGen.
Require Import W32Arith.
Require Import ElfEnc.
Require Import PageGeom.
Require Import ProcGeom.
Require Import ProcInv.
Require Import DiskPtsto.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import DirentEnc.
Require Import PathElems.
Require Import InodeInv.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import KallocInv.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import DinodeEnc.
Require Import DirView.
Require Import DirLinks.
Require Import InodeLock.
Require Import SchedCtx.
Require Import DiskInv.
Require Import PtTree.
Require Import PtBuild.
Require Import ProcPt.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import UmCovered.
Require Import FileInv.
Require Import SpecIput.
Require Import SpecKexec.
Require Import SpecMyproc.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecReadi.
Require Import SpecIunlockput.
Require Import SpecDirlink.
Require Import SpecNamei.
Require Import SpecProcFreepagetable.
Require Import SpecProcPagetable.
Require Import SpecWalkaddr.
Require Import SpecFlags2perm.
Require Import SpecUvmalloc.
Require Import ProofKexecParts.
Require Import ProofKexecTail.
Require Import ProofKexecSeam.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Notation KXB := KernelSyms.kexec (only parsing).

Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Rs3 := (mword_of_int 19 : mword 5).
Notation Rs4 := (mword_of_int 20 : mword 5).
Notation Rs5 := (mword_of_int 21 : mword 5).
Notation Rs6 := (mword_of_int 22 : mword 5).
Notation Rs7 := (mword_of_int 23 : mword 5).
Notation Rs8 := (mword_of_int 24 : mword 5).
Notation Rs9 := (mword_of_int 25 : mword 5).
Notation Rs10 := (mword_of_int 26 : mword 5).
Notation Rs11 := (mword_of_int 27 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).

(* ===================================================================== *)
(*  [kxc_b2] -- PHASE B2 WHOLE, THE LOOP PATH.  Statement copied verbatim  *)
(*  from ProofKexecB3.v; see that file for the design. *)
(* ===================================================================== *)
Definition kxc_b2_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      !fsCrashG Σ, !irefslotG Σ, !iregG Σ} `{GEN : GenId} `{CID0 : CpuId}
    (gs : list gname) (jp : nat) (gl : gname)
    (gu : uart_names) (gd : disk_names) (gk : gname) (pd pav pu : mword 64)
    (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names) (gtl : gname) (gilf gislf : gname) (ga gf : gname)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32) (used used2 : gset Z)
    (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
    (dnf : dinode) (bmf : blkmap) (n2 : nat)
    (plen : nat) (pfun : nat -> bv 8)
    (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
    (afun : nat -> nat -> bv 8)
    (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
    (m M : regfile) (K : nat) (C : iProp Σ)
    (sp0 ra0 s00 s10 s20 pv av w67 : mword 64)
    (ef : nat -> bv 8) (P : uptd) (i : nat) (szv : mword 64) :=
  (K_kexec <= K)%nat ->
  (kf < NINODE)%nat ->
  log_geom_ok cov logstart ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  0 <= inodestart ->
  cov_below cov size ->
  ireg_blocks_ok inodestart nib cov logstart ->
  (jp < NPROC)%nat ->
  gs !! jp = Some gl ->
  dev = icfg_dev ->
  m !!! Regidx csp_rs1 = sp0 ->
  m !!! Regidx Rra = ra0 ->
  m !!! Regidx Rs0 = s00 ->
  m !!! Regidx Rs1 = s10 ->
  m !!! Regidx Rs2 = s20 ->
  kernel_text -∗
  panic_wp_any -∗
  fs_fabric gs gu gd gk pd pav pu bn g gfs gi cn gtl
            cov logstart inodestart nib dev -∗
  kxc_at_12c jp bn g gfs gi cn ga gf cov logstart bmapstart inodestart nib
             size dev used used2 kf qf sf gyf inumf dnf bmf gilf gislf n2
             plen pfun na avf aslen afun pidv V dqb dqs dqa m M K C
             sp0 ra0 s00 s10 s20 pv av
             (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
             (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
             (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
             w67 ef P i szv -∗
  wp_next true (proc_addr jp) (fun (CID : CpuId) =>
    ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
      (entry spv szv' : mword 64),
        ⌜callee_saved m mf⌝ -∗
        ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
        sie_cap_gpr mf K true (proc_addr jp) -∗
        cpu_own 0 true (proc_addr jp) C true ∅ -∗
        pc_is (ret_pc ra0) -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        ⌜used' ⊆ used⌝ -∗
        bitmap_res gfs bmapstart cov logstart size used' -∗
        kalloc_env ga None -∗
        proc_priv gf (proc_addr jp) pidv V' -∗
        ([∗ list] k ∈ seq 0 (S plen), pa_add pv k ↦ₘ pfun k) -∗
        ([∗ list] k ∈ seq 0 (S na), pa_add av (8 * k) ↦₈{dqa} avf k) -∗
        ([∗ list] k ∈ seq 0 na,
           [∗ list] j ∈ seq 0 (aslen k), pa_add (avf k) j ↦ₘ afun k j) -∗
        bslots bn 3 -∗
        iref_slots 2 -∗
        WP (Loop : expr riscv_lang)) -∗
  wp_next true (proc_addr jp) (fun (CID : CpuId) =>
    ∀ (M' : regfile) (used3 : gset Z) (P' : uptd) (szv' : mword 64),
      kxc_at_1ae jp bn gfs ga gf cov logstart bmapstart inodestart size
                 used used3 plen pfun na avf aslen afun pidv V dqb dqs dqa
                 M' K C sp0 ra0 s00 s10 s20 pv av
                 (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                 (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                 (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                 w67 ef P' szv' -∗
      wp_next (CID0 := CID) true (proc_addr jp) (fun (CIDy : CpuId) =>
        ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
          (entry spv szv2 : mword 64),
            ⌜callee_saved m mf⌝ -∗
            ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv2 na alen⌝ -∗
            sie_cap_gpr mf K true (proc_addr jp) -∗
            cpu_own 0 true (proc_addr jp) C true ∅ -∗
            pc_is (ret_pc ra0) -∗
            sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
            sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
            ⌜used' ⊆ used⌝ -∗
            bitmap_res gfs bmapstart cov logstart size used' -∗
            kalloc_env ga None -∗
            proc_priv gf (proc_addr jp) pidv V' -∗
            ([∗ list] k ∈ seq 0 (S plen), pa_add pv k ↦ₘ pfun k) -∗
            ([∗ list] k ∈ seq 0 (S na), pa_add av (8 * k) ↦₈{dqa} avf k) -∗
            ([∗ list] k ∈ seq 0 na,
               [∗ list] j ∈ seq 0 (aslen k), pa_add (avf k) j ↦ₘ afun k j) -∗
            bslots bn 3 -∗
            iref_slots 2 -∗
            WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  [kxc_b2z] -- PHASE B2 WHOLE, THE [elf.phnum = 0] PATH.  Statement      *)
(*  copied verbatim from ProofKexecB3.v. *)
(* ===================================================================== *)
Definition kxc_b2z_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      !fsCrashG Σ, !irefslotG Σ, !iregG Σ} `{GEN : GenId} `{CID0 : CpuId}
    (gs : list gname) (jp : nat) (gl : gname)
    (gu : uart_names) (gd : disk_names) (gk : gname) (pd pav pu : mword 64)
    (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names) (gtl : gname) (gilf gislf : gname) (ga gf : gname)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32) (used used2 : gset Z)
    (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
    (dnf : dinode) (bmf : blkmap) (n2 : nat)
    (plen : nat) (pfun : nat -> bv 8)
    (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
    (afun : nat -> nat -> bv 8)
    (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
    (m M : regfile) (K : nat) (C : iProp Σ)
    (sp0 ra0 s00 s10 s20 pv av w67 : mword 64)
    (ef : nat -> bv 8) (P : uptd) :=
  (K_kexec <= K)%nat ->
  (kf < NINODE)%nat ->
  log_geom_ok cov logstart ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  0 <= inodestart ->
  cov_below cov size ->
  ireg_blocks_ok inodestart nib cov logstart ->
  (jp < NPROC)%nat ->
  gs !! jp = Some gl ->
  kernel_text -∗
  panic_wp_any -∗
  fs_fabric gs gu gd gk pd pav pu bn g gfs gi cn gtl
            cov logstart inodestart nib dev -∗
  kxc_at_1a2 jp bn g gfs gi cn ga gf cov logstart bmapstart inodestart nib
             size dev used used2 kf qf sf gyf inumf dnf bmf gilf gislf n2
             plen pfun na avf aslen afun pidv V dqb dqs dqa m M K C
             sp0 ra0 s00 s10 s20 pv av
             (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
             (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
             (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
             w67 ef P -∗
  wp_next true (proc_addr jp) (fun (CID : CpuId) =>
    ∀ (M' : regfile) (used3 : gset Z),
      kxc_at_1ae jp bn gfs ga gf cov logstart bmapstart inodestart size
                 used used3 plen pfun na avf aslen afun pidv V dqb dqs dqa
                 M' K C sp0 ra0 s00 s10 s20 pv av
                 (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
                 (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
                 (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
                 w67 ef P (mword_of_int 0 : mword 64) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type KEXECB3.
  Parameter kxc_b2 :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
        !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
        !fsCrashG Σ, !irefslotG Σ, !iregG Σ} `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname) (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gilf gislf : gname) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used used2 : gset Z)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap) (n2 : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
      (m M : regfile) (K : nat) (C : iProp Σ)
      (sp0 ra0 s00 s10 s20 pv av w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (i : nat) (szv : mword 64),
    kxc_b2_body gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl gilf gislf
      ga gf cov logstart bmapstart inodestart nib size dev used used2
      kf qf sf gyf inumf dnf bmf n2 plen pfun na avf alen aslen afun
      pidv V dqb dqs dqa m M K C sp0 ra0 s00 s10 s20 pv av w67
      ef P i szv.

  Parameter kxc_b2z :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
        !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
        !fsCrashG Σ, !irefslotG Σ, !iregG Σ} `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname) (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gilf gislf : gname) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used used2 : gset Z)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap) (n2 : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
      (m M : regfile) (K : nat) (C : iProp Σ)
      (sp0 ra0 s00 s10 s20 pv av w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd),
    kxc_b2z_body gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl gilf gislf
      ga gf cov logstart bmapstart inodestart nib size dev used used2
      kf qf sf gyf inumf dnf bmf n2 plen pfun na avf alen aslen afun
      pidv V dqb dqs dqa m M K C sp0 ra0 s00 s10 s20 pv av w67 ef P.
End KEXECB3.
