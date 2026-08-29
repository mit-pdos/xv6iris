(* ProofSysWriteAUStable.v -- the stable corollary, DERIVED from the AU form
   and nothing else: [SYSWRITE_AU_ERA -> SYSWRITE_AU_ERA_STABLE].

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the write AU
   prover).  [SpecSysWriteAU]'s header is explicit that this is owed "as a
   DERIVATION from [wp_sys_write_au] + the agreement seed, never as a second
   walk", and this file is that: NO instruction is stepped, no invariant is
   opened, and the whole proof is fourteen lines of assembly.

   ==== WHERE IT LANDS, AND WHY THAT IS THE HONEST ANSWER ===============

   IN THE ESCAPE ARM, exactly as the frozen header predicts.  The ok arm of
   [write_stable_arms_at] is

       ∃ off0 bss, ⌜off0 ≤ |bs0|⌝ ∗ ⌜|concat bss| = n⌝ ∗ ⌜|bss| ≤ wchunks n⌝
                   ∗ (wri_receipts_chained … ∨ wri_receipts …) ∗ …

   and the AU form delivers the right disjunct with [off0 := 0].  The
   CHAINED disjunct is not derivable and the reason is structural, not a
   gap in this proof: the per-chunk instants promise nothing about how one
   chunk's offset relates to the next -- [f->off] is read and advanced
   OUTSIDE any lock on a SHARED struct file, so "chunk k+1 starts where
   chunk k ended" is not a truth of the concurrent kernel and no derivation
   can manufacture it.  That is precisely why the escape disjunct is in the
   statement (open question 2), and it is what makes the sealed form
   provable today instead of merely stated.

   ==== THE CLIENT'S SHARE IS FRAMED, NOT USED ==========================

   [nview Γ q i (MkAnode (AFile bs0) nl)] rides in the ambient context
   across the call and comes back on both arms.  The agreement seed
   ([FsAbsWriteFire.awrite_commit_at_pinned]) is NOT invoked here: it is
   what a client uses to BUILD a bundle whose receipts already carry the
   agreement, and this derivation is deliberately generic in [Φw].

   AND THE FORM IS STILL VACUOUS AGAINST A LIVE INUM, which is the frozen
   header's own caveat sharpened by [FsAbsSeam]'s finding 3: a held
   [nview] share pins its row against every mover, and this call's OWN
   chunk retags are movers -- so a client presenting a share of the row it
   is writing is refuted by the payload arms outright.  The statement is
   future-facing; the tree layer's cross-syscall EXCLUSIVITY fact is the
   premise it is waiting for, and when that exists the form is re-cut at
   it (a new parallel form; R10).  Sealing it now costs fourteen lines and
   fixes the shape.

   BINDERS: [SpecSysWriteAUEra]'s section list VERBATIM. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
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
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import IrefSlots.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import SpecArgfd.
Require Import SpecSysRead.
Require Import ConsoleInv.
Require Import FsBlocks.
Require Import InodeInv.
Require Import SpecFilewrite.
Require Import SpecSysWrite.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import FsBytesGamma.
Require Import Xv6G.
Require Import FsCfg.
Require Import SpecSysWriteAU.
Require Import FsAbsWriteFire.
Require Import SpecSysWriteAUEra.
Require Import FsAbs.          (* LAST (FsAbs's own rule) *)
Import Defs.

Local Open Scope Z_scope.

Set Printing Depth 40.

Module SysWriteAUStable (W : SYSWRITE_AU_ERA) : SYSWRITE_AU_ERA_STABLE.

Section ProofStable.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_sys_write_au_era_stable
      (γf : gname) (γs : list gname) (j : nat) (γlp : gname)
      (fn : fwrite_names) (pidv : mword 32) (U : ustate) (v v2 : mword 64)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (fd : nat) (fv : mword 64) (rb : bool) (i : Z)
      (q : Qp) (bs0 : list (bv 8)) (nl : nat)
      (Φw : nat -> aview -> nat -> list (bv 8) -> iProp Σ)
    : wp_sys_write_au_era_stable_body γf γs j γlp fn pidv U v v2 m K eb b
        lks fd fv rb i q bs0 nl Φw.
  Proof.
    pose proof (W.wp_sys_write_au_era γf γs j γlp fn pidv U v v2 m K eb b
                  lks fd fv rb i Φw) as HW.
    cbv beta delta [wp_sys_write_au_era_body wp_sys_write_au_frame] in HW.
    cbv beta delta [wp_sys_write_au_era_stable_body wp_sys_write_au_frame].
    intros Gfs nn pcE pj ret_tgt Hav Hj Hgs Hlens Hfj Hfprocs
           Harg0 Harg1 Harg2 Hwp Hdq Heb Hargfd.
    iIntros "Hcg Hcpu Htext Hdata Hpc Hpenv Hpriv Hkenv Hprocs Henv
             Hcaps Htbl Hfdst [Hn Hbundle] Hcont".
    iApply (HW Hav Hj Hgs Hlens Hfj Hfprocs Harg0 Harg1 Harg2 Hwp Hdq Heb
              Hargfd
              with "Hcg Hcpu Htext Hdata Hpc Hpenv Hpriv Hkenv Hprocs Henv
                    Hcaps Htbl Hfdst Hbundle").
    iIntros (CID' Hchain mf r P')
      "%Hcs %Hupt %Hra Hcg Hcpu Hpc Hpriv Hkenv Hout Hfdst Harms".
    iSpecialize ("Hcont" $! CID' with "[%]"); [exact Hchain |].
    iApply ("Hcont" $! mf r P'
              with "[%] [%] [%] Hcg Hcpu Hpc Hpriv Hkenv Hout Hfdst
                    [Hn Harms]").
    { exact Hcs. }
    { exact Hupt. }
    { exact Hra. }
    (* THE ONLY REAL STEP: the client's share is framed back, and the ok
       arm takes the ESCAPE disjunct at [off0 := 0].  The chained disjunct
       is not derivable -- see the header. *)
    rewrite /write_stable_arms_at /write_arms_at. iFrame "Hn".
    iDestruct "Harms" as "[[%Hok Hpost] | [[%Hm1 Hpost] | [%Hnf Hpost]]]".
    - iLeft. iSplitR; [by iPureIntro |].
      rewrite /write_post_ok_at.
      iDestruct "Hpost" as (bss) "(%Htot & %Hlen & Hrs & Hcm)".
      iExists 0%nat, bss.
      iSplitR; [iPureIntro; lia |].
      iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |].
      iSplitL "Hrs"; [iRight; iExact "Hrs" |]. iExact "Hcm".
    - iRight. iLeft. iSplitR; [by iPureIntro |]. iExact "Hpost".
    - iRight. iRight. iSplitR; [by iPureIntro |]. iExact "Hpost".
  Qed.

End ProofStable.

End SysWriteAUStable.
