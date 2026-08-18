(* SpecKexecB2.v -- the public interface ProofKexecB3.v actually consumes
   out of ProofKexecB2.v: [kxc_ls] (the inlined loadseg loop) and
   [kxc_bad324] (the shared [bad:] tail six of kexec's eight [bad:] entries
   fall into), stated independently of the proof that produces them, plus
   the WHOLE of [KexecB2Frame]/[KexecB2Res] -- the frame algebra
   ([kxc_frameBpin] and the moves around it) and the fourteen-resource
   bundle ([kxc_res] and its peel/seal/take/give lemmas) their statements
   are phrased over.  Requiring THIS file -- fast, no expensive [Qed] in it
   (these two sections were always cheap; the ~2200 lines / ~2 min
   ProofKexecB2.v's own header measures is [kxc_ls]'s loop induction and
   [kxc_bad324]'s resource shuffle, in the sections that stay behind) -- is
   what phase B3 pays for, instead of requiring ProofKexecB2.v outright and
   serializing the two phases' builds.

   Both sections move WHOLESALE, not just their two headline [Definition]s:
   ProofKexecB3.v turns out to call several of the small algebra lemmas
   around them too (unqualified, the same way it calls [kxc_frameBpin]/
   [kxc_res] themselves) -- [kxc_slot63_split], [kxc_frameB_of_Bpin],
   [kxc_load_peel], [kxc_load_seal], [kxc_open_intro], [kxc_ph_take],
   [kxc_ph_give], [kxc_win8] -- and cherry-picking only the two
   [Definition]s left the rest stranded in ProofKexecB2.v, unreachable.
   Moving the two [Section]s here verbatim, Context and all, also lets
   Coq's own section-discharge decide each lemma's REAL minimal typeclass
   set (e.g. [kxc_frameBpin] turns out not to need [sieG Σ] at all, despite
   [KexecB2Frame]'s [Context] declaring it) rather than a hand-written
   guess -- which is what the first cut of this file got wrong.

   This is claude-notes/design/spec-modules.md's Spec/Proof decoupling
   pattern, applied within one function's OWN phase split rather than
   across a caller/callee edge -- the same move ProofKexecTail.v already
   made for the phase A / phase B seam (see that file's header): pull out
   exactly what the next phase consumes, so the two phases meet through a
   small shared/abstract interface instead of one requiring the other's
   whole proof outright.

   Neither [kxc_ls] nor [kxc_bad324]'s STATEMENT mentions any of
   [KexecB2Proof]'s nine functor arguments (Myproc, BeginOp, ... Walkaddr)
   -- those are only in the PROOFS, called through internal lemmas this
   file does not expose -- so [KEXECB2] below needs no functor parameters
   of its own. *)
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
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import StackBytes.
Require Import CalleeSaved.
Require Import InstrBytes.
Require Import KernelText.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import SleepLock.
Require Import WpLock.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import FsCrash.
Require Import InodeRegion.
Require Import FsTree.
Require Import IcacheEscrow.
Require Import ByteBuf.
Require Import W32Arith.
Require Import ElfEnc.
Require Import PageGeom.
Require Import ProcGeom.
Require Import ProcInv.
Require Import DiskPtsto.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
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
Require Import ProcInv.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import UmCovered.
Require Import FileInvDefs.
Require Import SpecIput.
Require Import SpecKexec.
Require Import SpecDirlink.
Require Import ProofKexecParts.
Require Import ProofKexecTail.
Require Import ProofKexecSeam.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Notation KXB := KernelSyms.kexec (only parsing).

(* Register-number notations, shared by [kxc_bad324_body] and [kxc_ls_body]
   below -- pure parser sugar (matches ProofKexecB2.v's own per-section
   [Notation]s), not a [let]: keeps the elaborated body IDENTICAL in shape
   to ProofKexecB2.v's original statement, so [cbv delta] unfolds it back
   to exactly the goal the original proof script expects. *)
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
(*  THE FRAME WITH slot 65 PINNED -- verbatim from ProofKexecB2.v's        *)
(*  [KexecB2Frame] section (only the [Definition]; the three moves        *)
(*  between it and its neighbours are proof-internal, not part of what    *)
(*  B3 consumes). *)
(* ===================================================================== *)
(* Verbatim from ProofKexecB2.v's [Section KexecB2Frame] -- Context and
   all, so that Coq's own section-discharge decides each lemma's real
   minimal typeclass set instead of a hand-written guess.  (The first cut
   of this file hand-wrote [kxc_frameBpin]'s signature and got it wrong --
   included [sieG Σ], which the body never uses, and ProofKexecB3.v's
   [Section KexecB3Ph] calls it with only [riscvGS Σ] in scope.) *)
Section KexecB2Frame.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  (* slots 55..62 are [ph]'s seven words and the unused one; slot 63 is [off],
     split out and PINNED for the reason the header gives. *)
  Lemma kxc_slot63_split (sp0 : mword 64) :
    stack_own (KTR := KT1) (pa_stk sp0 54) 9 ⊣⊢
    stack_own (KTR := KT1) (pa_stk sp0 54) 8 ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 63) (DfracOwn 1) w).
  Proof.
    rewrite (kxc_slots_asc sp0 9 54) (kxc_slots_asc sp0 8 54).
    cbn [seq big_opL Nat.add].
    iSplit.
    - iIntros "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _)". iFrame.
    - iIntros "((H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _) & H9)". iFrame.
  Qed.

  Definition kxc_frameBpin (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w63 w65 w67 : mword 64) : iProp Σ :=
    (word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) s10 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) s20 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) w5 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) w6 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 7) (DfracOwn 1) w7 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 8) (DfracOwn 1) w8 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 9) (DfracOwn 1) w9 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 10) (DfracOwn 1) w10 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 11) (DfracOwn 1) w11 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 12) (DfracOwn 1) w12 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 13) (DfracOwn 1) w13 ∗
     stack_own (KTR := KT1) (pa_stk sp0 13) 33 ∗
     stack_own (KTR := KT1) (pa_stk sp0 54) 8 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 63) (DfracOwn 1) w63 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 64) (DfracOwn 1) av ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 65) (DfracOwn 1) w65 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 66) (DfracOwn 1) pv ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 67) (DfracOwn 1) w67 ∗
     (∃ w68, word_pointsto (KTR := KT1) (pa_stk sp0 68) (DfracOwn 1) w68))%I.

  (* the two directions between it and [kxc_frameB] *)
  Lemma kxc_frameBpin_of_B (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64) :
    kxc_frameB sp0 ra0 s00 s10 s20 pv av w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ⊢
    ∃ w63 w65, kxc_frameBpin sp0 ra0 s00 s10 s20 pv av
                        w5 w6 w7 w8 w9 w10 w11 w12 w13 w63 w65 w67.
  Proof.
    rewrite /kxc_frameB /kxc_frameBpin.
    iIntros "(A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 &
              A13 & Aust & Aph & A64 & (%w65 & A65) & A66 & A67 & A68)".
    rewrite kxc_slot63_split. iDestruct "Aph" as "(Aph & (%w63 & A63))".
    iExists w63, w65.
    iSplitL "A1"; [iExact "A1" |]. iSplitL "A2"; [iExact "A2" |].
    iSplitL "A3"; [iExact "A3" |]. iSplitL "A4"; [iExact "A4" |].
    iSplitL "A5"; [iExact "A5" |]. iSplitL "A6"; [iExact "A6" |].
    iSplitL "A7"; [iExact "A7" |]. iSplitL "A8"; [iExact "A8" |].
    iSplitL "A9"; [iExact "A9" |]. iSplitL "A10"; [iExact "A10" |].
    iSplitL "A11"; [iExact "A11" |]. iSplitL "A12"; [iExact "A12" |].
    iSplitL "A13"; [iExact "A13" |]. iSplitL "Aust"; [iExact "Aust" |].
    iSplitL "Aph"; [iExact "Aph" |]. iSplitL "A63"; [iExact "A63" |].
    iSplitL "A64"; [iExact "A64" |].
    iSplitL "A65"; [iExact "A65" |]. iSplitL "A66"; [iExact "A66" |].
    iSplitL "A67"; [iExact "A67" | iExact "A68"].
  Qed.

  Lemma kxc_frameB_of_Bpin (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w63 w65 w67 : mword 64) :
    kxc_frameBpin sp0 ra0 s00 s10 s20 pv av
                 w5 w6 w7 w8 w9 w10 w11 w12 w13 w63 w65 w67 ⊢
    kxc_frameB sp0 ra0 s00 s10 s20 pv av w5 w6 w7 w8 w9 w10 w11 w12 w13 w67.
  Proof.
    rewrite /kxc_frameB /kxc_frameBpin.
    iIntros "(A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 &
              A13 & Aust & Aph & A63 & A64 & A65 & A66 & A67 & A68)".
    iSplitL "A1"; [iExact "A1" |]. iSplitL "A2"; [iExact "A2" |].
    iSplitL "A3"; [iExact "A3" |]. iSplitL "A4"; [iExact "A4" |].
    iSplitL "A5"; [iExact "A5" |]. iSplitL "A6"; [iExact "A6" |].
    iSplitL "A7"; [iExact "A7" |]. iSplitL "A8"; [iExact "A8" |].
    iSplitL "A9"; [iExact "A9" |]. iSplitL "A10"; [iExact "A10" |].
    iSplitL "A11"; [iExact "A11" |]. iSplitL "A12"; [iExact "A12" |].
    iSplitL "A13"; [iExact "A13" |]. iSplitL "Aust"; [iExact "Aust" |].
    iSplitR "A64 A65 A66 A67 A68".
    { rewrite kxc_slot63_split.
      iSplitL "Aph"; [iExact "Aph" | by iExists w63]. }
    iSplitL "A64"; [iExact "A64" |].
    iSplitL "A65"; [by iExists w65 |]. iSplitL "A66"; [iExact "A66" |].
    iSplitL "A67"; [iExact "A67" | iExact "A68"].
  Qed.

  (* ...and the move the [bad:] tail makes: slots 5,7..13 lose their values,
     the elf run goes back into the middle [stack_own], and what is left is
     exactly [kxc_frameA6] at slot 6. *)
  Lemma kxc_frameBpin_to_A6 (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w63 w65 w67 : mword 64)
      (ef : nat -> bv 8) :
    (forall i, (i < 8)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (54 - i))) 8 = true) ->
    kxc_frameBpin sp0 ra0 s00 s10 s20 pv av
                 w5 w6 w7 w8 w9 w10 w11 w12 w13 w63 w65 w67 -∗
    ([∗ list] j ∈ seq 0 64, pa_add (pa_stk sp0 54) j ↦ₘ[KT1] ef j) -∗
    kxc_frameA6 sp0 ra0 s00 s10 s20 pv av w6.
  Proof.
    intro Hal. rewrite /kxc_frameBpin /kxc_frameA6.
    iIntros "(A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 &
              A13 & Aust & Aph0 & A63 & A64 & A65 & A66 & A67 & A68) Helf".
    iAssert (stack_own (KTR := KT1) (pa_stk sp0 54) 9) with "[Aph0 A63]" as "Aph".
    { rewrite kxc_slot63_split.
      iSplitL "Aph0"; [iExact "Aph0" | by iExists w63]. }
    iDestruct (kxc_elf_give sp0 ef Hal with "Helf") as "Aelf".
    iSplitL "A1"; [iExact "A1" |]. iSplitL "A2"; [iExact "A2" |].
    iSplitL "A3"; [iExact "A3" |]. iSplitL "A4"; [iExact "A4" |].
    iSplitL "A5"; [by iExists w5 |]. iSplitL "A6"; [iExact "A6" |].
    iSplitL "A7"; [by iExists w7 |]. iSplitL "A8"; [by iExists w8 |].
    iSplitL "A9"; [by iExists w9 |]. iSplitL "A10"; [by iExists w10 |].
    iSplitL "A11"; [by iExists w11 |]. iSplitL "A12"; [by iExists w12 |].
    iSplitL "A13"; [by iExists w13 |].
    iSplitR "A64 A65 A66 A67 A68".
    { iApply (kxc_mid_join sp0 with "Aust Aelf Aph"). }
    iSplitL "A64"; [iExact "A64" |]. iSplitL "A65"; [by iExists w65 |].
    iSplitL "A66"; [iExact "A66" |]. iSplitL "A67"; [by iExists w67 |].
    iExact "A68".
  Qed.

End KexecB2Frame.

(* ===================================================================== *)
(*  WHAT THE TWO LOOPS CARRY UNCHANGED -- verbatim from ProofKexecB2.v's   *)
(*  [KexecB2Res] section. *)
(* ===================================================================== *)
Section KexecB2Res.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId}.

  Definition kxc_res
      (jp : nat) (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (size : Z) (dev : mword 32) (used2 : gset Z)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap) (gilf gislf : gname) (n2 : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w63 w65 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) : iProp Σ :=
    (kxc_open gfs gi cn cov logstart dev pidv kf qf sf gyf inumf dnf bmf
              gilf gislf ∗
     log_op g n2 ∗
     iref_slots 1 ∗
     sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) ∗
     sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) ∗
     bitmap_res gfs bmapstart cov logstart size used2 ∗
     bslots bn 3 ∗
     proc_pt P ∗
     proc_priv gf (proc_addr jp) pidv V ∗
     ([∗ list] k ∈ seq 0 (S plen), pa_add pv k ↦ₘ[KT1] pfun k) ∗
     ([∗ list] k ∈ seq 0 (S na), pa_add av (8 * k) ↦₈[KT1]{dqa} avf k) ∗
     ([∗ list] k ∈ seq 0 na,
        [∗ list] j ∈ seq 0 (aslen k), pa_add (avf k) j ↦ₘ afun k j) ∗
     ([∗ list] j ∈ seq 0 64, pa_add (pa_stk sp0 54) j ↦ₘ[KT1] ef j) ∗
     kxc_frameBpin sp0 ra0 s00 s10 s20 pv av
                  w5 w6 w7 w8 w9 w10 w11 w12 w13 w63 w65 w67)%I.

  (* ------------------------------------------------------------------ *)
  (*  [ic_loaded] PEELED FOR readi, AND SEALED AGAIN.                    *)
  (*  Three call sites in this file want the same six pieces out of the  *)
  (*  one resource ilock published, and the re-assembly is the same      *)
  (*  eight-way [iSplitL] every time.                                     *)
  (* ------------------------------------------------------------------ *)
  Lemma kxc_load_peel (gfs : fs_names) (gi : gname) (cov : gset Z)
      (logstart : Z) (kf : nat) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap) :
    ic_loaded gfs gi cov logstart kf inumf dnf bmf ⊢
    ∃ datl : nat -> list (bv 8),
      ⌜inode_ok cov logstart dnf bmf datl⌝ ∗
      ⌜dir_ok icfg_nib dnf datl⌝ ∗
      ⌜dir_dots_ix (bv_unsigned inumf) dnf datl⌝ ∗
      ⌜dir_orphan_clean dnf datl⌝ ∗
      ⌜dir_uniq dnf datl⌝ ∗
      dir_links (bv_unsigned inumf) dnf datl ∗
      dinode_at gi inumf dnf ∗
      inode_meta (ientry kf) dnf ∗
      inode_map gfs (ientry kf) bmf ∗
      inode_blocks gfs bmf datl.
  Proof.
    rewrite /ic_loaded /inode_map.
    iIntros "(%datl & %Hok & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlk & Hdiat & Hmeta &
              Haddrs & Hind & Hbl)".
    iExists datl.
    iSplitR; [iPureIntro; exact Hok |].
    iSplitR; [iPureIntro; exact Hdok |].
    iSplitR; [iPureIntro; exact Hddix |].
    iSplitR; [iPureIntro; exact Hdoc |].
    iSplitR; [iPureIntro; exact Hduq |].
    iSplitL "Hdlk"; [iExact "Hdlk" |]. iSplitL "Hdiat"; [iExact "Hdiat" |].
    iSplitL "Hmeta"; [iExact "Hmeta" |].
    iSplitR "Hbl"; [| iExact "Hbl"].
    iSplitL "Haddrs"; [iExact "Haddrs" | iExact "Hind"].
  Qed.

  Lemma kxc_load_seal (gfs : fs_names) (gi : gname) (cov : gset Z)
      (logstart : Z) (kf : nat) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap) (datl : nat -> list (bv 8)) :
    inode_ok cov logstart dnf bmf datl ->
    dir_ok icfg_nib dnf datl ->
    dir_dots_ix (bv_unsigned inumf) dnf datl ->
    dir_orphan_clean dnf datl ->
    dir_uniq dnf datl ->
    dir_links (bv_unsigned inumf) dnf datl -∗
    dinode_at gi inumf dnf -∗
    inode_meta (ientry kf) dnf -∗
    inode_map gfs (ientry kf) bmf -∗
    inode_blocks gfs bmf datl -∗
    ic_loaded gfs gi cov logstart kf inumf dnf bmf.
  Proof.
    intros Hok Hdok Hddix Hdoc Hduq. rewrite /ic_loaded /inode_map.
    iIntros "Hdlk Hdiat Hmeta [Haddrs Hind] Hbl". iExists datl.
    iSplitR; [iPureIntro; exact Hok |].
    iSplitR; [iPureIntro; exact Hdok |].
    iSplitR; [iPureIntro; exact Hddix |].
    iSplitR; [iPureIntro; exact Hdoc |].
    iSplitR; [iPureIntro; exact Hduq |].
    iSplitL "Hdlk"; [iExact "Hdlk" |]. iSplitL "Hdiat"; [iExact "Hdiat" |].
    iSplitL "Hmeta"; [iExact "Hmeta" |].
    iSplitL "Haddrs"; [iExact "Haddrs" |].
    iSplitL "Hind"; [iExact "Hind" | iExact "Hbl"].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  A PAGE, AS readi's DESTINATION.                                     *)
  (*  [KallocInv.page_own] is 4096 anonymous bytes; readi wants the first  *)
  (*  [nn] of them NAMED (its post is stated over the old contents), and   *)
  (*  the giveback wants them anonymous again.                            *)
  (* ------------------------------------------------------------------ *)
  Lemma kxc_page_take (q : mword 64) (nn : nat) :
    (nn <= 4096)%nat ->
    page_own q ⊢
    ∃ f : nat -> bv 8,
      ([∗ list] j ∈ seq 0 nn, pa_add q j ↦ₘ f j) ∗
      ([∗ list] j ∈ seq 0 (4096 - nn), pa_add (pa_add q nn) j ↦ₘ f (nn + j)%nat).
  Proof.
    intro Hn. rewrite /page_own.
    iIntros "H". iDestruct (bb_any_named q 4096 with "H") as (f) "H".
    iExists f. rewrite (bb_split3 q nn (4096 - nn) 0 4096 f ltac:(lia)).
    iDestruct "H" as "(A & B & _)". iSplitL "A"; [iExact "A" | iExact "B"].
  Qed.

  Lemma kxc_page_give (q : mword 64) (nn : nat) (f h : nat -> bv 8) :
    (nn <= 4096)%nat ->
    ([∗ list] j ∈ seq 0 nn, pa_add q j ↦ₘ h j) -∗
    ([∗ list] j ∈ seq 0 (4096 - nn), pa_add (pa_add q nn) j ↦ₘ f (nn + j)%nat) -∗
    page_own q.
  Proof.
    intro Hn. iIntros "A B". rewrite /page_own.
    iApply (bb_named_any q 4096 (fun j => if decide (j < nn)%nat then h j
                                          else f j)).
    rewrite (bb_split3 q nn (4096 - nn) 0 4096
               (fun j => if decide (j < nn)%nat then h j else f j) ltac:(lia)).
    iSplitL "A".
    { iApply (big_sepL_mono with "A"). intros ii jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite decide_True; [reflexivity | lia]. }
    iSplitR "".
    { iApply (big_sepL_mono with "B"). intros ii jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite decide_False; [reflexivity | lia]. }
    by rewrite big_sepL_nil.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  [kxc_open], re-sealed.  The ten resources go back exactly as ilock  *)
  (*  published them; readi borrows three of them and returns all three.  *)
  (* ------------------------------------------------------------------ *)
  Lemma kxc_open_intro (gfs : fs_names) (gi : gname) (cn : ic_names)
      (cov : gset Z) (logstart : Z) (dev pidv : mword 32)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap) (gilf gislf : gname) :
    is_sleeplock_gen gilf gislf (i_lock (ientry kf)) "inode"%string (ic_tok cn kf) (slh_tok (icfg_isl kf)) -∗
    sleeplocked_q gislf sf -∗
    sl_pid (i_lock (ientry kf)) ↦₄ pidv -∗
    ic_deposit cn kf (DepShr sf dev inumf gyf) -∗
    i_dev (ientry kf) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kf) ↦₄{DfracOwn (1/2)} inumf -∗
    i_valid (ientry kf) ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart kf inumf dnf bmf -∗
    ity_shot gyf (di_type dnf) -∗
    (* ...and the payload's freeze token (§3.9, RULING A-prime) *)
    ifreeze_off (bv_unsigned inumf) -∗
    inode_ref_short kf (qf + sf)%Qp qf dev inumf -∗
    kxc_open gfs gi cn cov logstart dev pidv kf qf sf gyf inumf dnf bmf
             gilf gislf.
  Proof.
    rewrite /kxc_open.
    iIntros "A B C D E F G H I I2 J".
    iSplitL "A"; [iExact "A" |]. iSplitL "B"; [iExact "B" |].
    iSplitL "C"; [iExact "C" |]. iSplitL "D"; [iExact "D" |].
    iSplitL "E"; [iExact "E" |]. iSplitL "F"; [iExact "F" |].
    iSplitL "G"; [iExact "G" |]. iSplitL "H"; [iExact "H" |].
    iSplitL "I"; [iExact "I" |]. iSplitL "I2"; [iExact "I2" | iExact "J"].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE [ph] BUFFER AND THE [off] CELL, out of the frame's middle       *)
  (*  [stack_own] and back.                                               *)
  (*                                                                      *)
  (*  [kxc_frameB]'s [stack_own (pa_stk sp0 54) 9] is slots 55..63: the    *)
  (*  56-byte [struct proghdr] (slots 55..61, base slot 61), the unused    *)
  (*  word at slot 62, and [off] at slot 63.  The phdr loop writes [off]   *)
  (*  at +0x12c and reads five fields out of [ph] after the readi, so it   *)
  (*  needs all three separately -- and it hands them back before the      *)
  (*  back edge, because [kxc_at_12c] carries the chunk whole.             *)
  (* ------------------------------------------------------------------ *)
  Lemma kxc_ph_slots_of_stack (sp0 : mword 64) :
    stack_own (KTR := KT1) (pa_stk sp0 54) 9 ⊢
    ([∗ list] i ∈ seq 0 7,
       ∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 (61 - i)) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 62) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 63) (DfracOwn 1) w).
  Proof.
    rewrite (kxc_slots_asc sp0 9 54). cbn [seq big_opL].
    iIntros "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _)".
    cbn [Nat.add Nat.sub].
    iSplitR "H8 H9"; [| iSplitL "H8"; [iExact "H8" | iExact "H9"]].
    iFrame "H7 H6 H5 H4 H3 H2 H1".
  Qed.

  Lemma kxc_stack_of_ph_slots (sp0 : mword 64) (w62 w63 : mword 64) :
    ([∗ list] i ∈ seq 0 7,
       ∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 (61 - i)) (DfracOwn 1) w) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 62) (DfracOwn 1) w62 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 63) (DfracOwn 1) w63 -∗
    stack_own (KTR := KT1) (pa_stk sp0 54) 9.
  Proof.
    iIntros "H A B".
    rewrite (kxc_slots_asc sp0 9 54). cbn [seq big_opL Nat.add Nat.sub].
    iDestruct "H" as "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & _)".
    iFrame "H7 H6 H5 H4 H3 H2 H1". iSplitL "A"; [by iExists w62 |].
    iSplitL "B"; [by iExists w63 | done].
  Qed.

  (* ...and the byte view of the seven, with the per-slot alignment kept as
     a PURE side product -- a byte run does not carry alignment and
     [bytes_own_slotsn] demands it back.  [kxc_elf_take]'s twin. *)
  Lemma kxc_ph_take (sp0 : mword 64) :
    ([∗ list] i ∈ seq 0 7,
       ∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 (61 - i)) (DfracOwn 1) w) ⊢
    ⌜forall i, (i < 7)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (61 - i))) 8 = true⌝ ∗
    ∃ f : nat -> bv 8,
      [∗ list] j ∈ seq 0 56, pa_add (pa_stk sp0 61) j ↦ₘ[KT1] f j.
  Proof.
    iIntros "H".
    iDestruct (kxc_slots_ph sp0 with "H") as "[%Hal Hb]".
    iSplitR; [iPureIntro; exact Hal |].
    iApply (bb_any_named (KTR := KT1) (pa_stk sp0 61) 56). rewrite /bytes_own /byte_any.
    iExact "Hb".
  Qed.

  Lemma kxc_ph_give (sp0 : mword 64) (h : nat -> bv 8) :
    (forall i, (i < 7)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (61 - i))) 8 = true) ->
    ([∗ list] j ∈ seq 0 56, pa_add (pa_stk sp0 61) j ↦ₘ[KT1] h j) ⊢
    [∗ list] i ∈ seq 0 7,
      ∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 (61 - i)) (DfracOwn 1) w.
  Proof.
    intro Hal. iIntros "Hh".
    iApply (kxc_bytes_ph sp0 Hal). rewrite /bytes_own.
    iApply (bb_named_any with "Hh").
  Qed.

  (* An 8-byte READ window into a named run -- [ProofKexecSeam.kxc_win2] and
     [kxc_win4] at the width the three [ld]s of ph.vaddr / ph.filesz /
     ph.memsz use. *)
  Lemma kxc_win8 (a : mword 64) (f : nat -> bv 8) (o r n : nat) :
    (o + 8 + r)%nat = n ->
    is_aligned_paddr (Physaddr (pa_add a o)) 8 = true ->
    ([∗ list] j ∈ seq 0 n, pa_add a j ↦ₘ[KT1] f j) ⊢
    (pa_add a o ↦₈[KT1] (Z_to_bv 64 (le_at f o 8) : mword 64)) ∗
    ((pa_add a o ↦₈[KT1] (Z_to_bv 64 (le_at f o 8) : mword 64)) -∗
       [∗ list] j ∈ seq 0 n, pa_add a j ↦ₘ[KT1] f j).
  Proof.
    intros Hn Hal.
    rewrite (bb_split3 (KTR := KT1) a o 8 r n f Hn).
    iIntros "(Hpre & Hmid & Hsuf)".
    iSplitL "Hmid".
    { iApply (word_pointsto_intro (KTR := KT1) _ _ _ Hal).
      iApply (big_sepL_mono with "Hmid"). intros ii jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite (le_at_nth_byte 64 f o 8 ii ltac:(lia) Hlt). reflexivity. }
    iIntros "Hw".
    iDestruct (word_pointsto_bytes with "Hw") as "Hw".
    iSplitL "Hpre"; [iExact "Hpre" |]. iSplitR "Hsuf"; [| iExact "Hsuf"].
    iApply (big_sepL_mono with "Hw"). intros ii jj Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
    rewrite (le_at_nth_byte 64 f o 8 ii ltac:(lia) Hlt). reflexivity.
  Qed.

End KexecB2Res.

(* ===================================================================== *)
(*  [kxc_bad324] -- THE TAIL SIX OF KEXEC'S EIGHT [bad:] ENTRIES SHARE.    *)
(*  Statement copied verbatim from ProofKexecB2.v; see that file for the   *)
(*  design (which size is freed, why no threading clause is needed). *)
(* ===================================================================== *)
Definition kxc_bad324_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ} `{GEN : GenId} `{CID0 : CpuId}
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
    (m Mt : regfile) (K : nat)
    (sp0 ra0 s00 s10 s20 pv av w63 w67 : mword 64)
    (ef : nat -> bv 8) (P : uptd) (szf : mword 64) (lks : gset string) :=
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
  bv_unsigned inumf < 16 * Z.of_nat nib ->
  (iput_units <= n2)%nat ->
  (jp < NPROC)%nat ->
  gs !! jp = Some gl ->
  used2 ⊆ used ->
  m !!! Regidx csp_rs1 = sp0 ->
  m !!! Regidx Rra = ra0 ->
  m !!! Regidx Rs0 = s00 ->
  m !!! Regidx Rs1 = s10 ->
  m !!! Regidx Rs2 = s20 ->
  (* ---- the register state at +0x324 ---- *)
  Mt !!! Regidx csp_rs1 = pa_stk sp0 68 ->
  Mt !!! Regidx Rs0 = sp0 ->
  Mt !!! Regidx Rs4 = ientry kf ->
  Mt !!! Regidx Rs6 = page_base P.(ud_root) ->
  (* ---- the frame's elf run, and the size to free ---- *)
  (forall j, (j < 8)%nat ->
     is_aligned_paddr (Physaddr (pa_stk sp0 (54 - j))) 8 = true) ->
  um_below szf P.(ud_um) ->
  um_covered szf P.(ud_um) ->
  sie_cap_gpr KT1 Mt (K - 68)%nat true (proc_addr jp) -∗
  cpu_own 0 true (proc_addr jp) true lks -∗
  kernel_text -∗
  pc_is (mword_of_int (KXB + 0x324) : mword 64) -∗
  fs_fabric gs gu gd gk pd pav pu bn g gfs gi cn gtl
            cov logstart inodestart nib dev -∗
  kxc_open gfs gi cn cov logstart dev pidv kf qf sf gyf inumf dnf bmf
           gilf gislf -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_res gfs bmapstart cov logstart size used2 -∗
  kalloc_env ga None -∗
  proc_pt P -∗
  proc_priv gf (proc_addr jp) pidv V -∗
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
  ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
  ([∗ list] i ∈ seq 0 na,
     [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
  ([∗ list] j ∈ seq 0 64, pa_add (pa_stk sp0 54) j ↦ₘ[KT1] ef j) -∗
  bslots bn 3 -∗
  iref_slots 1 -∗
  log_op g n2 -∗
  kxc_frameBpin sp0 ra0 s00 s10 s20 pv av
    (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
    (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
    (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
    w63 szf w67 -∗
  (* ---- kexec's own continuation, which [kxc_bad64] closes ---- *)
  wp_next true (proc_addr jp) (fun (CID : CpuId) =>
    ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
      (entry spv szv' : mword 64),
        ⌜callee_saved m mf⌝ -∗
        ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
        sie_cap_gpr KT1 mf K true (proc_addr jp) -∗
        cpu_own 0 true (proc_addr jp) true lks -∗
        pc_is (ret_pc ra0) -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        ⌜used' ⊆ used⌝ -∗
        bitmap_res gfs bmapstart cov logstart size used' -∗
        kalloc_env ga None -∗
        proc_priv gf (proc_addr jp) pidv V' -∗
        ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
        ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
        ([∗ list] i ∈ seq 0 na,
           [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
        bslots bn 3 -∗
        iref_slots 2 -∗
        WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  [kxc_ls] -- THE INLINED loadseg PAGE LOOP.  Statement copied           *)
(*  verbatim from ProofKexecB2.v; see that file for the design (the fuel,  *)
(*  why the base case is vacuous, what the invariant does and does not     *)
(*  carry). *)
(* ===================================================================== *)
Definition kxc_ls_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ} `{GEN : GenId} `{CID0 : CpuId}
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
    (m : regfile) (K : nat)
    (sp0 ra0 s00 s10 s20 pv av w63 w65 w67 : mword 64)
    (ef : nat -> bv 8) (P : uptd)
    (ip : nat) (va : mword 64) (fz po : Z) (lks : gset string) :=
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
  bv_unsigned inumf < 16 * Z.of_nat nib ->
  (iput_units <= n2)%nat ->
  (jp < NPROC)%nat ->
  gs !! jp = Some gl ->
  used2 ⊆ used ->
  dev = icfg_dev ->
  m !!! Regidx csp_rs1 = sp0 ->
  m !!! Regidx Rra = ra0 ->
  m !!! Regidx Rs0 = s00 ->
  m !!! Regidx Rs1 = s10 ->
  m !!! Regidx Rs2 = s20 ->
  (forall j, (j < 8)%nat ->
     is_aligned_paddr (Physaddr (pa_stk sp0 (54 - j))) 8 = true) ->
  um_below w65 P.(ud_um) ->
  um_covered w65 P.(ud_um) ->
  (0 <= fz < 2 ^ 32)%Z ->
  (0 <= po < 2 ^ 32)%Z ->
  (* ---- THE FUEL, and the cursor under it ---- *)
  forall (W : nat) (Ml : regfile) (ii : Z),
  (0 <= ii < 2 ^ 32)%Z ->
  (2 ^ 32 - (po + ii) `mod` 2 ^ 32 <= Z.of_nat W)%Z ->
  (w32_uarg ii < w32_uarg fz)%Z ->
  Ml !!! Regidx csp_rs1 = pa_stk sp0 68 ->
  Ml !!! Regidx Rs0 = sp0 ->
  Ml !!! Regidx Rs1 = sign_extend' 64 (mword_of_int ii : mword 32) ->
  Ml !!! Regidx Rs3 = sign_extend' 64 (mword_of_int fz : mword 32) ->
  Ml !!! Regidx Rs4 = ientry kf ->
  Ml !!! Regidx Rs5 = (mword_of_int 4096 : mword 64) ->
  Ml !!! Regidx Rs6 = page_base P.(ud_root) ->
  Ml !!! Regidx Rs7 = sign_extend' 64 (mword_of_int po : mword 32) ->
  Ml !!! Regidx Rs8 = va ->
  Ml !!! Regidx Rs9 = (mword_of_int 4096 : mword 64) ->
  Ml !!! Regidx Rs10 = (mword_of_int (Z.of_nat ip) : mword 64) ->
  Ml !!! Regidx Rs11 = (mword_of_int 56 : mword 64) ->
  sie_cap_gpr KT1 Ml (K - 68)%nat true (proc_addr jp) -∗
  cpu_own 0 true (proc_addr jp) true lks -∗
  kernel_text -∗
  pc_is (mword_of_int (KXB + 0xf6) : mword 64) -∗
  fs_fabric gs gu gd gk pd pav pu bn g gfs gi cn gtl
            cov logstart inodestart nib dev -∗
  kalloc_env ga None -∗
  kxc_res jp bn g gfs gi cn gf cov logstart bmapstart inodestart size dev
          used2 kf qf sf gyf inumf dnf bmf gilf gislf n2 plen pfun na avf
          aslen afun pidv V dqb dqs dqa sp0 ra0 s00 s10 s20 pv av
          (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
          (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
          (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
          w63 w65 w67 ef P -∗
  (* ---- kexec's OWN continuation.  Convention 3: this block owns its
     [bad:] exit (+0x0ea -> +0x324) and discharges it against the
     contract rather than handing it out; the ONE output below therefore
     hands the continuation BACK, which is what keeps the single linear
     [wp_next] enough for both. ---- *)
  wp_next true (proc_addr jp) (fun (CID : CpuId) =>
    ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
      (entry spv szv' : mword 64),
        ⌜callee_saved m mf⌝ -∗
        ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
        sie_cap_gpr KT1 mf K true (proc_addr jp) -∗
        cpu_own 0 true (proc_addr jp) true lks -∗
        pc_is (ret_pc ra0) -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        ⌜used' ⊆ used⌝ -∗
        bitmap_res gfs bmapstart cov logstart size used' -∗
        kalloc_env ga None -∗
        proc_priv gf (proc_addr jp) pidv V' -∗
        ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
        ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
        ([∗ list] i ∈ seq 0 na,
           [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
        bslots bn 3 -∗
        iref_slots 2 -∗
        WP (Loop : expr riscv_lang)) -∗
  (* ---- THE ONE OUTPUT: +0x116, the segment is in memory.  s1 and s2
     are dead there (+0x116 reloads s2 from slot 65 and the phdr loop
     never reads s1 again), so the state is the entry state with the
     cursor dropped. ---- *)
  wp_next true (proc_addr jp) (fun (CID : CpuId) =>
    ∀ (Mx : regfile),
      ⌜Mx !!! Regidx csp_rs1 = pa_stk sp0 68 /\
        Mx !!! Regidx Rs0 = sp0 /\
        Mx !!! Regidx Rs4 = ientry kf /\
        Mx !!! Regidx Rs5 = (mword_of_int 4096 : mword 64) /\
        Mx !!! Regidx Rs6 = page_base P.(ud_root) /\
        Mx !!! Regidx Rs9 = (mword_of_int 4096 : mword 64) /\
        Mx !!! Regidx Rs10 = (mword_of_int (Z.of_nat ip) : mword 64) /\
        Mx !!! Regidx Rs11 = (mword_of_int 56 : mword 64)⌝ -∗
      sie_cap_gpr KT1 Mx (K - 68)%nat true (proc_addr jp) -∗
      cpu_own 0 true (proc_addr jp) true lks -∗
      pc_is (mword_of_int (KXB + 0x116) : mword 64) -∗
      kxc_res jp bn g gfs gi cn gf cov logstart bmapstart inodestart size dev
              used2 kf qf sf gyf inumf dnf bmf gilf gislf n2 plen pfun na avf
              aslen afun pidv V dqb dqs dqa sp0 ra0 s00 s10 s20 pv av
              (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
              (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
              (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
              w63 w65 w67 ef P -∗
      wp_next (CID0 := CID) true (proc_addr jp) (fun (CIDy : CpuId) =>
        ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
          (entry spv szv' : mword 64),
            ⌜callee_saved m mf⌝ -∗
            ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
            sie_cap_gpr KT1 mf K true (proc_addr jp) -∗
            cpu_own 0 true (proc_addr jp) true lks -∗
            pc_is (ret_pc ra0) -∗
            sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
            sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
            ⌜used' ⊆ used⌝ -∗
            bitmap_res gfs bmapstart cov logstart size used' -∗
            kalloc_env ga None -∗
            proc_priv gf (proc_addr jp) pidv V' -∗
            ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
            ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
            ([∗ list] i ∈ seq 0 na,
               [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
            bslots bn 3 -∗
            iref_slots 2 -∗
            WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type KEXECB2.
  Parameter kxc_bad324 :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
        !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
        !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ} `{GEN : GenId} `{CID0 : CpuId}
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
      (m Mt : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av w63 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (szf : mword 64) (lks : gset string),
    kxc_bad324_body gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl gilf gislf
      ga gf cov logstart bmapstart inodestart nib size dev used used2
      kf qf sf gyf inumf dnf bmf n2 plen pfun na avf alen aslen afun
      pidv V dqb dqs dqa m Mt K sp0 ra0 s00 s10 s20 pv av w63 w67
      ef P szf lks.

  Parameter kxc_ls :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
        !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
        !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ} `{GEN : GenId} `{CID0 : CpuId}
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
      (m : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av w63 w65 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd)
      (ip : nat) (va : mword 64) (fz po : Z) (lks : gset string),
    kxc_ls_body gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl gilf gislf
      ga gf cov logstart bmapstart inodestart nib size dev used used2
      kf qf sf gyf inumf dnf bmf n2 plen pfun na avf alen aslen afun
      pidv V dqb dqs dqa m K sp0 ra0 s00 s10 s20 pv av w63 w65 w67
      ef P ip va fz po lks.
End KEXECB2.
