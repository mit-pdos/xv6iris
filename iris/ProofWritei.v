(* ProofWritei.v -- writei over the SIE-agnostic sconf world.

     int writei(struct inode *ip, int user_src, uint64 src, uint off, uint n)
     {
       uint tot, m;  struct buf *bp;
       if(off > ip->size || off + n < off)  return -1;
       if(off + n > MAXFILE*BSIZE)          return -1;
       for(tot = 0; tot < n; tot += m, off += m, src += m){
         uint addr = bmap(ip, off/BSIZE);
         if(addr == 0) break;
         bp = bread(ip->dev, addr);
         m = min(n - tot, BSIZE - off%BSIZE);
         if(either_copyin(bp->data + (off % BSIZE), user_src, src, m) == -1) {
           brelse(bp);  break; }
         log_write(bp);  brelse(bp);
       }
       if(off > ip->size) ip->size = off;
       iupdate(ip);
       return tot;
     }

   The proof's shape, the frame discipline and the [either_copyin == -1]
   arm (kernel defect D1, now fixed in fs.c) are documented in the block
   immediately above [Module WriteiProof] below. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import DiskPtsto DiskInv.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
Require Import ByteCursor.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import WpUart.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeRegion.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import CodeWritei.
Require Import SpecPanic.
Require Import SpecBmap SpecBread SpecBrelse SpecLogWrite SpecEitherCopyin
        SpecIupdate.
Require Import ProofWriteiParts.
Require Import BitmapInv.
Require Import KernelDataInv.
Require Import SpecPrintk.
Require Import SpecWritei.
(* the loop's ledger algebra: bm_pot, wi_inv_bud/wi_inv_spent, the two step
   lemmas, wi_inv_enter/wi_inv_exit and the two iteration bounds.  Section 10
   of WriteiBudget.v is written to BE this file's budget reasoning. *)
Require Import WriteiBudget.
From Kernel Require KernelSyms.
(* The [set_solver] override.  EXPORT, not Import: this import is         *)
(* deliberately "dead" -- the file compiles without it, just far slower --  *)
(* and the nightly dead-import sweep skips [Require Export] lines.         *)
(* It has to be HERE rather than inherited: [Require Export] only          *)
(* propagates through an unbroken chain of Exports, and this tree's        *)
(* intermediate files use [Require Import], so nothing downstream inherits *)
(* it.  See FastSetSolver.v.                                              *)
Require Export FastSetSolver.
Require Import ProcAvail.
Local Open Scope Z_scope.

(* a whole-function WP goal is enormous; keep a failing tactic's error
   printable (claude-notes/durable-notes.md) *)
Set Printing Depth 40.

(* ===================================================================== *)
(*  THE SHAPE OF THE PROOF.  Five lemmas, entered right to left in the    *)
(*  file and left to right at run time:                                   *)
(*                                                                        *)
(*    wi_ret   +0xdc .. +0xec   pop the seven unconditionally-saved       *)
(*                              registers, ret, discharge the contract.   *)
(*                              BOTH -1 arms and the normal arm end here. *)
(*    wi_join  +0xd2 .. +0xda   iupdate, a0 := tot, restore s3.  THREE    *)
(*                              paths join here.                          *)
(*    wi_size  +0xbc .. +0xd0   the size test, the store, and the five    *)
(*                              conditional restores (+0xc8 / +0xf2).     *)
(*    wi_loop  +0x82 head, +0x4c body, +0xb0 failure tail.  Fuel          *)
(*                              induction on the straddled-block count.   *)
(*    wp_writei_sconf           +0x00 .. +0x4a, the two -1 exits, and the *)
(*                              n = 0 arm at +0xee.                       *)
(*                                                                        *)
(*  EVERY CALLEE-SAVED REGISTER IS SAVED, so there is no register-        *)
(*  threading invariant at all: [callee_saved m mf] falls out of the      *)
(*  thirteen restores plus the [addi sp,sp,112].  What replaces it is the *)
(*  FRAME in three strengths -- [wi_fr7] (the seven unconditional slots   *)
(*  pinned), [wi_fr8] (s3's slot too, after +0x032) and [wi_fr13] (all    *)
(*  thirteen, inside the loop).  bmap's s4 lesson applies verbatim: every *)
(*  restore precedes the join at +0xd2.                                   *)
(*                                                                        *)
(*  THE PRE-FRAME EXIT at +0x000..+0x002 is the one genuinely new shape:  *)
(*  it tests [off > ip->size] and leaves through a bare [li a0,-1; ret]   *)
(*  at +0xfe BEFORE the prologue has run, so it holds no frame at all and *)
(*  [callee_saved] comes from the two caller-saved writes alone.          *)
(*                                                                        *)
(*  THE COUPLING THAT MAKES THE LOOP WORK is [wi_held_content]: the       *)
(*  block's own [fsblock] half, borrowed out of [inode_blocks] with       *)
(*  [inode_blocks_acc], against the bio handle's machinery half pins the  *)
(*  buffer's bytes to [data fbn].  The copy then splices [m] bytes into   *)
(*  that list ([wi_splice]) and log_write re-indexes the payload at the   *)
(*  result, which is one step of the postcondition's range clause         *)
(*  ([wi_file_byte_splice] / [wi_range_step]).                            *)
(*                                                                        *)
(*  THE [either_copyin == -1] ARM (kernel defect D1, now FIXED in fs.c).  *)
(*  The old code did [brelse(bp); break;] with the buffer holding a       *)
(*  PARTIALLY copied chunk, and [SpecBrelse] wants [bio_locked] -- the    *)
(*  traveling bytes EQUAL to the payload's logical content -- which was   *)
(*  unobtainable, because re-indexing the payload needs the log lock's    *)
(*  authority.  fs.c now calls [log_write(bp)] first, and that call IS    *)
(*  the missing step: it takes [bio_held] at the spliced bytes and hands  *)
(*  back [bio_locked] at them plus the [fsblock] re-indexed.  The arm is  *)
(*  therefore the success arm's sequence verbatim at the other pair of    *)
(*  pcs (+0xb0 / +0xb2 / +0xb6 / +0xb8); only the bookkeeping differs --  *)
(*  [tot] is NOT advanced, so the chunk becomes the postcondition's       *)
(*  bounded DISTURBED REGION ([dist], [dstb]; see SpecWritei.v).          *)
(*                                                                        *)
(*  ...AND THE ARM IS DEAD ON THE KERNEL PATH (fs-icache.md §15.1(i)).    *)
(*  [SpecEitherCopyin]'s post is [r = 0 \/ r = -1] only when [user]; the  *)
(*  kernel arm returns a bare [r = 0].  The normalisation [Hnorm] that    *)
(*  merges the two posts therefore carries [user = true] on its -1        *)
(*  disjunct, and that single conjunct is the whole proof of the new      *)
(*  postcondition clause [user = false -> dist = 0]: the only site that   *)
(*  instantiates [dist] nonzero is this break, and it has [user = true].  *)
(*  Everywhere else [dist] is the literal [0%nat].                        *)
(* ===================================================================== *)
Module WriteiProof (BM : BMAP) (BR : BREAD) (BL : BRELSE) (LW : LOG_WRITE)
                   (EC : EITHER_COPYIN) (IU : IUPDATE) : WRITEI.

Notation WI := KernelSyms.writei.

Notation Rra  := (mword_of_int 1  : mword 5).
Notation Rs0  := (mword_of_int 8  : mword 5).
Notation Rs1  := (mword_of_int 9  : mword 5).
Notation Rs2  := (mword_of_int 18 : mword 5).
Notation Rs3  := (mword_of_int 19 : mword 5).
Notation Rs4  := (mword_of_int 20 : mword 5).
Notation Rs5  := (mword_of_int 21 : mword 5).
Notation Rs6  := (mword_of_int 22 : mword 5).
Notation Rs7  := (mword_of_int 23 : mword 5).
Notation Rs8  := (mword_of_int 24 : mword 5).
Notation Rs9  := (mword_of_int 25 : mword 5).
Notation Rs10 := (mword_of_int 26 : mword 5).
Notation Rs11 := (mword_of_int 27 : mword 5).
Notation Ra0  := (mword_of_int 10 : mword 5).
Notation Ra1  := (mword_of_int 11 : mword 5).
Notation Ra2  := (mword_of_int 12 : mword 5).
Notation Ra3  := (mword_of_int 13 : mword 5).
Notation Ra4  := (mword_of_int 14 : mword 5).
Notation Ra5  := (mword_of_int 15 : mword 5).

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac widx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

(* ===================================================================== *)
(*  THE SET SHAPES, PROVED ONCE, WHERE THE CONTEXT IS THREE VARIABLES     *)
(*                                                                        *)
(*  [set_solver] runs [set_unfold] over the WHOLE hypothesis context, and *)
(*  inside this file's proofs that context is several hundred hypotheses  *)
(*  of Iris proofmode state, register-threading facts and mword           *)
(*  equalities: a single call did not terminate in fifteen minutes in     *)
(*  ProofBmap's interior, and the failure reads exactly like a hang.      *)
(*  (S3l's trap; ProofBmap.v carries the same block for the same reason.) *)
(*  Every set obligation the budget retrofit discharges is one of these   *)
(*  four shapes, so each is proved once here and applied BY NAME.         *)
(*  NEVER write [set_solver] inside a function-proof lemma in this file.  *)
(* ===================================================================== *)
Lemma wiset_add_r (A D : gset Z) : A ⊆ A ∪ D.
Proof. set_solver. Qed.

(* monotonicity through one more union: what every call that grows the op's
   set needs in order to keep the public [Sb ⊆ Sb'] promise *)
Lemma wiset_sub_add_r (A B D : gset Z) : A ⊆ B -> A ⊆ B ∪ D.
Proof. set_solver. Qed.

(* the bitmap block is in the set once anything has allocated -- carried
   forward across the rest of the loop, which only ever grows the set *)
Lemma wiset_in_add_r (x : Z) (B D : gset Z) : x ∈ B -> x ∈ B ∪ D.
Proof. set_solver. Qed.

Lemma wiset_in_sing_r (x : Z) (B : gset Z) : x ∈ B ∪ {[x]}.
Proof. set_solver. Qed.

(* membership travels along an inclusion -- the one shape the sixteen-byte
   receipt needs that the four above do not give *)
Lemma wiset_in_mono (x : Z) (A B : gset Z) : A ⊆ B -> x ∈ A -> x ∈ B.
Proof. set_solver. Qed.

(* ===================================================================== *)
(*  THE SIXTEEN-BYTE SEAM (GR-3 stage 3).  [SpecWritei.wi16_post] is the  *)
(*  EXPOSED fact; the two definitions below are how the walk carries it.  *)
(*                                                                        *)
(*  [wi16_pre] is [wi16_post] as it stands AT THE JOIN -- before the       *)
(*  trailing iupdate, so without iupdate's own term and without the        *)
(*  [IBLOCK] membership -- stated at the count IN HAND (the [S u] of       *)
(*  [wi_size]/[wi_join]).  [wi16_pre_join] crosses the flush.              *)
(*                                                                        *)
(*  ITS GUARD IS THE SINGLE-BLOCK SHAPE ALONE.  The spend bound holds at   *)
(*  EVERY [tot] ([SpecWritei.wi16_spend_any]) -- every break arm leaves    *)
(*  the ledger at a sub-figure of the same expression -- and so does the   *)
(*  granularity fact ([wi16_atomic]); only the two MEMBERSHIPS need        *)
(*  [0 < tot], because the bmap break logs nothing of writei's own.  The   *)
(*  three exits carry all three facts in this one receipt, which is why    *)
(*  [wi_size] and [wi_join] take no further premise.                       *)
(*                                                                        *)
(*  [wi16_fresh] is what the LOOP carries: when the whole write fits in    *)
(*  one block the loop runs exactly one iteration, so at the top of any    *)
(*  iteration nothing has moved yet.  It is re-established rather than     *)
(*  preserved -- [wi_blocks off n = 1] pins the fuel at 1, which makes     *)
(*  the back edge unreachable ([wi_blocks_pos]) -- which is why the        *)
(*  multi-block ledger above it does not have to be strengthened at all.   *)
(* ===================================================================== *)
Definition wi16_pre (bms : Z) (ncount ucur off n tot : nat)
    (bm bm' : blkmap) (Sb Sc : gset Z) : Prop :=
  wi_blocks off n = 1%nat ->
  let fbn := (off `div` BSIZE)%nat in
  let al := bmap_alloced bm bm' fbn in
  let ind := bmap_ind fbn in
  let crb := bool_decide (bms ∈ Sb) in
  let crd := bool_decide (wi_tgt_blk bm' off ∈ Sb) in
  ((ncount - (bmap_cost crb al ind
              + (if (al || crd)%bool then 0 else 1)))%nat <= ucur)%nat
  /\ (tot = 0%nat \/ tot = n)
  /\ ((0 < tot)%nat ->
        wi_tgt_blk bm' off ∈ Sc
        /\ (al = true -> bms ∈ Sc)).

Definition wi16_fresh (off n tot ncount nI : nat) (bm bmI : blkmap)
    (Sb SI : gset Z) : Prop :=
  wi_blocks off n = 1%nat ->
  tot = 0%nat /\ bmI = bm /\ nI = ncount /\ SI = Sb.

(* THE FLUSH, crossed.  iupdate's credited contract returns [S u] when the
   inode block was already in the op's set and [u] otherwise, and the
   entry-set [cru] of [wi16_spend] is FALSE whenever the running set's is
   -- which is the only direction the arithmetic needs. *)
Lemma wi16_pre_spend (bms : Z) (inum : mword 32) (inodestart : Z)
    (ncount u off n tot : nat) (bm bm' : blkmap) (Sb Sc : gset Z) :
  Sb ⊆ Sc ->
  wi16_pre bms ncount (S u) off n tot bm bm' Sb Sc ->
  wi16_spend_any bms inum inodestart ncount
    (if bool_decide (IBLOCK inum inodestart ∈ Sc) then S u else u)%nat
    off n bm bm' Sb.
Proof.
  intros Hsub Hpre. unfold wi16_spend_any, wi16_pre in *.
  intros Hb1. specialize (Hpre Hb1). cbv zeta in Hpre |- *.
  destruct Hpre as (H1 & _ & _).
  unfold wi16_spend.
  remember (bmap_cost (bool_decide (bms ∈ Sb))
              (bmap_alloced bm bm' (off `div` BSIZE)%nat)
              (bmap_ind (off `div` BSIZE)%nat)) as BC eqn:HBC.
  remember (if (bmap_alloced bm bm' (off `div` BSIZE)%nat
                || bool_decide (wi_tgt_blk bm' off ∈ Sb))%bool
            then 0 else 1)%nat as LW eqn:HLW.
  destruct (bool_decide (IBLOCK inum inodestart ∈ Sc)) eqn:Hc.
  - destruct (bool_decide (IBLOCK inum inodestart ∈ Sb)); lia.
  - assert (Hnb : bool_decide (IBLOCK inum inodestart ∈ Sb) = false).
    { apply bool_decide_eq_false_2. intros Hin.
      rewrite (bool_decide_eq_true_2 _ (wiset_in_mono _ Sb Sc Hsub Hin)) in Hc.
      discriminate Hc. }
    rewrite Hnb. lia.
Qed.

(* the granularity fact is carried by the receipt itself and crosses the
   flush untouched -- neither the count nor the set appears in it *)
Lemma wi16_pre_atomic (bms : Z) (ncount ucur off n tot : nat)
    (bm bm' : blkmap) (Sb Sc : gset Z) :
  wi16_pre bms ncount ucur off n tot bm bm' Sb Sc ->
  wi16_atomic off n tot.
Proof.
  intros Hpre Hb1. specialize (Hpre Hb1). cbv zeta in Hpre.
  destruct Hpre as (_ & H & _). exact H.
Qed.

Lemma wi16_pre_join (bms : Z) (inum : mword 32) (inodestart : Z)
    (ncount u off n tot : nat) (bm bm' : blkmap) (Sb Sc : gset Z) :
  Sb ⊆ Sc ->
  wi16_pre bms ncount (S u) off n tot bm bm' Sb Sc ->
  wi16_post bms inum inodestart ncount
    (if bool_decide (IBLOCK inum inodestart ∈ Sc) then S u else u)%nat
    off n tot bm bm' Sb (Sc ∪ {[IBLOCK inum inodestart]}).
Proof.
  intros Hsub Hpre.
  pose proof (wi16_pre_spend bms inum inodestart ncount u off n tot
                bm bm' Sb Sc Hsub Hpre) as Hsp.
  unfold wi16_post, wi16_spend_any, wi16_pre in *.
  intros Htot Hb1. specialize (Hpre Hb1). specialize (Hsp Hb1).
  cbv zeta in Hpre, Hsp |- *.
  destruct Hpre as (_ & _ & Hmem). destruct (Hmem Htot) as (H2 & H3).
  split_and!.
  - exact Hsp.
  - exact (wiset_in_add_r _ _ _ H2).
  - exact (wiset_in_sing_r _ _).
  - intros Ha. exact (wiset_in_add_r _ _ _ (H3 Ha)).
Qed.

(* THE SEAM's arithmetic, once, over four numbers: bmap's arm-wise spend
   and writei's own [log_write] composed into [wi16_pre]'s first conjunct.
   [crlw] is the boolean log_write actually ran at, and the third premise
   is the honesty fact that it fired whenever the figure charges nothing
   for it (SpecBmap clause (d), through clause (e) on the direct path). *)
Lemma wi16_spend_step (ncount nB nL BC : nat) (al crd crlw : bool) :
  (ncount <= nB + BC)%nat ->
  (nB <= nL + (if crlw then 0 else 1))%nat ->
  ((al || crd)%bool = true -> crlw = true) ->
  ((ncount - (BC + (if (al || crd)%bool then 0 else 1)))%nat <= nL)%nat.
Proof.
  intros H1 H2 H3. destruct al, crd, crlw; cbn in H2, H3 |- *;
    first [ lia | (specialize (H3 eq_refl); discriminate H3) ].
Qed.

(* CLAUSE (e) AT WORK.  [WriteiBudget.wi_ad_of_alloced] reads [bmap_alloced]
   as [bmap_ad] on the INDIRECT path only (there an allocating call had to
   allocate the data block, because an absent indirect block forces the
   entry to zero).  On the direct path the same reading is a frame fact
   about the indirect slot, which is what [SpecBmap]'s clause (e) states. *)
Lemma wi_ad_of_alloced_dir (bm bm' : blkmap) (fbn : nat) :
  bm_ind bm' = bm_ind bm ->
  bmap_alloced bm bm' fbn = true ->
  bmap_ad bm bm' fbn = true.
Proof.
  intros Hind Hal. unfold bmap_alloced in Hal.
  assert (Hai : bmap_ai bm bm' = false).
  { unfold bmap_ai. apply bool_decide_eq_false_2. intros [H1 H2].
    rewrite Hind in H2. exact (H2 H1). }
  rewrite Hai in Hal. exact Hal.
Qed.

(* ...and the two paths as one, which is what the seam actually applies *)
Lemma wi_ad_of_alloced_any (cov : gset Z) (logstart : Z) (bm bm' : blkmap)
    (fbn : nat) :
  blkmap_wf cov logstart bm ->
  (fbn < MAXFILE)%nat ->
  bv_unsigned (blkmap_get bm' fbn) <> 0 ->
  (bmap_ind fbn = false -> bm_ind bm' = bm_ind bm) ->
  bmap_alloced bm bm' fbn = true ->
  bmap_ad bm bm' fbn = true.
Proof.
  intros Hwf Hlt Hnz He Hal. destruct (bmap_ind fbn) eqn:Hind.
  - exact (wi_ad_of_alloced cov logstart bm bm' fbn Hwf Hlt Hnz Hind Hal).
  - exact (wi_ad_of_alloced_dir bm bm' fbn (He eq_refl) Hal).
Qed.

(* ===================================================================== *)
(*  Vocabulary: the frame in three strengths, and the continuation.       *)
(* ===================================================================== *)
Section WriteiDefs.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}.

  (* the CALLER's buffer tier -- see this function's spec for why it is not
     [KT1].  A KtierLe HYPOTHESIS in the section beats [ktier_le_refl] at
     instance search, so every OTHER leaf in this file has to name its own
     datum tier out loud (the blanket [(ktd := KT1)] below). *)
  Context {ktb : ktier}.
  Context `{!KtierLe ktb KT1}.
  (* writei's 112-byte frame.  Slot k sits at [sp0 - 8k], i.e. at
     [sp_new + (112 - 8k)]:
       1 ra@104   2 s0@96   3 s1@88   4 s2@80   5 s3@72   6 s4@64
       7 s5@56    8 s6@48   9 s7@40  10 s8@32  11 s9@24  12 s10@16
      13 s11@8   14 (offset 0, never written)                          *)

  (* the SEVEN unconditional saves (+0x008..+0x014), which is all the join
     at +0xd6 may assume: the other seven slots are written only on the
     paths that got that far. *)
  Definition wi_fr7 (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈[KT1] (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈[KT1] v) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈[KT1] v) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 7 ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 8 ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 9 ↦₈[KT1] (m !!! Regidx Rs7 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 10 ↦₈[KT1] v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 11 ↦₈[KT1] v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 12 ↦₈[KT1] v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 13 ↦₈[KT1] v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 14 ↦₈[KT1] v))%I.

  (* ...plus s3's slot, pinned from +0x032 to the [c.ldsp s3] at +0xd4 *)
  Definition wi_fr8 (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈[KT1] (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈[KT1] v) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 7 ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 8 ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 9 ↦₈[KT1] (m !!! Regidx Rs7 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 10 ↦₈[KT1] v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 11 ↦₈[KT1] v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 12 ↦₈[KT1] v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 13 ↦₈[KT1] v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 14 ↦₈[KT1] v))%I.

  (* ...and all thirteen, which is what the loop holds (+0x038..+0x040) *)
  Definition wi_fr13 (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈[KT1] (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 7 ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 8 ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 9 ↦₈[KT1] (m !!! Regidx Rs7 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 10 ↦₈[KT1] (m !!! Regidx Rs8 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 11 ↦₈[KT1] (m !!! Regidx Rs9 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 12 ↦₈[KT1] (m !!! Regidx Rs10 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 13 ↦₈[KT1] (m !!! Regidx Rs11 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 14 ↦₈[KT1] v))%I.

  Lemma wi_fr7_of8 (m : regfile) : wi_fr8 m -∗ wi_fr7 m.
  Proof.
    rewrite /wi_fr8 /wi_fr7.
    iIntros "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & HA & HB & HC & HD & HE)".
    iSplitL "H1"; [iExact "H1"|]. iSplitL "H2"; [iExact "H2"|].
    iSplitL "H3"; [iExact "H3"|]. iSplitL "H4"; [iExact "H4"|].
    iSplitL "H5"; [iExists _; iExact "H5"|].
    iSplitL "H6"; [iExact "H6"|]. iSplitL "H7"; [iExact "H7"|].
    iSplitL "H8"; [iExact "H8"|]. iSplitL "H9"; [iExact "H9"|].
    iSplitL "HA"; [iExact "HA"|]. iSplitL "HB"; [iExact "HB"|].
    iSplitL "HC"; [iExact "HC"|]. iSplitL "HD"; [iExact "HD"|]. iExact "HE".
  Qed.

  (* ===================================================================== *)
  (*  THE SOURCE AND THE PID SHARE THAT RIDES WITH IT (S3p)                 *)
  (*                                                                        *)
  (*  SpecWritei's premise is ONE bracket, [if user then proc_priv else      *)
  (*  buffer ∗ p_pid], and not the pair it used to be.  THE PID FRACTION IS  *)
  (*  THE KERNEL ARM'S.  bread/brelse/bmap/iupdate each want a share of      *)
  (*  [p->pid] at a universally quantified dfrac either way, but on the USER *)
  (*  arm writei holds the whole [proc_priv] block and BORROWS the quarter   *)
  (*  out of it ([ProcInv.proc_priv_pid]); it has to, because that accessor  *)
  (*  CONSUMES the block and returns a wand, so nobody can hold both at      *)
  (*  once.  Asking for both was what made the user arm uncallable, and      *)
  (*  filewrite is what found it -- [SpecReadi.v]:244-267 is the same repair *)
  (*  one stage earlier, for the same reason, found by fileread.             *)
  (*                                                                        *)
  (*  [wi_q] is the dfrac the borrow carries and [wi_src_pid] is the borrow: *)
  (*  ONE lemma serving BOTH arms, so no call site case-splits on [user].    *)
  (*  either_copyin takes the block and never the fraction, so the borrow is *)
  (*  always closed before the copy and re-opened after it.                  *)
  (* ===================================================================== *)
  Definition wi_q (user : bool) (dq : dfrac) : dfrac :=
    if user then DfracOwn (1/4) else dq.

  Lemma wi_src_pid (γf : gname) (j : nat) (pidv : mword 32) (dq : dfrac)
      (user : bool) (Vc : pprivate) (srcb : mword 64) (n : nat)
      (bytes : nat -> bv 8) :
    (if user
     then proc_priv_core (proc_addr j) pidv Vc
     else ([∗ list] i ∈ seq 0 n, pa_add srcb i ↦ₘ[ktb] bytes i) ∗
          p_pid (proc_addr j) ↦₄{dq} pidv) -∗
      p_pid (proc_addr j) ↦₄{wi_q user dq} pidv ∗
      (p_pid (proc_addr j) ↦₄{wi_q user dq} pidv -∗
       (if user
        then proc_priv_core (proc_addr j) pidv Vc
        else ([∗ list] i ∈ seq 0 n, pa_add srcb i ↦ₘ[ktb] bytes i) ∗
             p_pid (proc_addr j) ↦₄{dq} pidv)).
  Proof.
    rewrite /wi_q. destruct user.
    - iIntros "Hp". iDestruct (proc_priv_core_pid with "Hp") as "[Hq Hback]".
      iSplitL "Hq"; [iExact "Hq"|]. iIntros "Hq". iApply ("Hback" with "Hq").
    - iIntros "Hd". iDestruct "Hd" as "[Hb Hq]". iSplitL "Hq"; [iExact "Hq"|].
      iIntros "Hq". iSplitL "Hb"; [iExact "Hb"|]. iExact "Hq".
  Qed.

  (* THE CONTINUATION, named so it is not re-traversed by every proofmode
     split (claude-notes/optimization.md). *)
  Definition wi_cont `{GEN : GenId} `{CID0 : CpuId}
      (γfs : fs_names) (γi : gname) (bn : bio_names) (γ : log_names)
      (γf : gname)
      (cov : gset Z) (logstart inodestart : Z) (nib : nat) (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn dn0 : dinode)
      (user : bool) (off n : nat) (src_bytes : nat -> bv 8)
      (V : pprivate) (ncount : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac) (A : bm_alloc) (j : nat)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) : iProp Σ :=
    wp_next true (proc_addr j) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (tot : nat) (bm' : blkmap) (data' : nat -> list (bv 8))
        (dn' dn0' : dinode) (n' : nat)
        (wrote : nat -> bv 8) (dist : nat) (dstb : nat -> bv 8) (P' : uptd)
        (Sb' : gset Z),
        ⌜callee_saved m mf⌝ -∗
        ⌜blkmap_wf cov logstart bm'⌝ -∗
        ⌜blk_holes_zero bm' data'⌝ -∗
        ⌜di_addrs dn' = bm_cells bm'⌝ -∗
        ⌜bv_unsigned (di_size dn') < 2 ^ 31⌝ -∗
        ⌜bm_covers bm' (bv_unsigned (di_size dn'))⌝ -∗
        ⌜bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
         bv_unsigned (di_size dn') <= Z.of_nat MAXFILE * Z.of_nat BSIZE⌝ -∗
        ⌜inode_sized data -> inode_sized data'⌝ -∗
        ⌜(dist <= BSIZE)%nat⌝ -∗
        ⌜(tot = n)%nat -> dist = 0%nat⌝ -∗
        ⌜user = false -> dist = 0%nat⌝ -∗
        ⌜forall k : nat,
           file_byte data' k
           = if decide ((off <= k)%nat /\ (k < off + tot)%nat)
             then wrote (k - off)%nat
             else if decide ((off + tot <= k)%nat /\ (k < off + tot + dist)%nat)
                  then dstb (k - (off + tot))%nat
                  else file_byte data k⌝ -∗
        ⌜user = false -> forall i : nat, (i < tot)%nat -> wrote i = src_bytes i⌝ -∗
        ⌜(mf !!! Regidx Ra0 = (mword_of_int (-1) : mword 64)
          /\ (bv_unsigned (di_size dn) < Z.of_nat off
              \/ (MAXFILE * BSIZE < off + n)%nat)
          /\ tot = 0%nat /\ dist = 0%nat
          /\ bm' = bm /\ data' = data /\ dn' = dn /\ dn0' = dn0
          /\ n' = ncount)
         \/ (mf !!! Regidx Ra0 = (mword_of_int (Z.of_nat tot) : mword 64)
             /\ (tot <= n)%nat
             /\ dn' = wi_dinode dn bm' off tot
             /\ dn0' = dn')⌝ -∗
        ⌜((ncount - wi_cost_bmonly off n)%nat <= n')%nat /\ (n' <= ncount)%nat⌝ -∗
        ⌜Sb ⊆ Sb'⌝ -∗
        (* THE SIXTEEN-BYTE SEAM, in the shape the public contract exposes *)
        ⌜wi16_post (ba_bms A) inum inodestart ncount n' off n tot bm bm' Sb Sb'⌝ -∗
        ⌜wi16_spend_any (ba_bms A) inum inodestart ncount n' off n bm bm' Sb⌝ -∗
        ⌜wi16_atomic off n tot⌝ -∗
        ⌜uptd_ext (pv_upt V) P'⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr j) -∗
        cpu_own 0 eb (proc_addr j) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr j) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        i_dev ip ↦₄{dqd} dev -∗
        i_inum ip ↦₄{dqn} inum -∗
        inode_meta ip dn' -∗
        inode_map γfs ip bm' -∗
        inode_blocks γfs bm' data' -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        bm_alloc_res γfs cov logstart A -∗
        dinode_at γi inum dn0' -∗
        (* the source goes back the way it came, and the pid share with it *)
        (if user
         then proc_priv_core (proc_addr j) pidv (upd_upt V P')
         else ([∗ list] i ∈ seq 0 n,
                 pa_add (m !!! Regidx Ra2 : mword 64) i ↦ₘ[ktb] (src_bytes i)) ∗
              p_pid (proc_addr j) ↦₄{dq} pidv) -∗
        bslots bn 3 -∗
        log_opS γ n' Sb' -∗
        WP (Loop : expr riscv_lang))%I.

End WriteiDefs.

(* the sp relation: inside the frame sp is 112 below its entry value *)
Definition wi_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1
  = add_vec (m !!! Regidx csp_rs1 : mword 64)
      (sign_extend' 64 (caddi16sp_imm (mword_of_int 57 : mword 6))).

(* ===================================================================== *)
(*  +0xd6 .. +0xe6 : THE RETURN.                                          *)
(* ===================================================================== *)
Section WriteiRet.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}.

  (* the CALLER's buffer tier -- see this function's spec for why it is not
     [KT1].  A KtierLe HYPOTHESIS in the section beats [ktier_le_refl] at
     instance search, so every OTHER leaf in this file has to name its own
     datum tier out loud (the blanket [(ktd := KT1)] below). *)
  Context {ktb : ktier}.
  Context `{!KtierLe ktb KT1}.
  Local Lemma wi_ret `{GEN : GenId} `{CID0 : CpuId} 
      (γfs : fs_names) (γi : gname) (bn : bio_names) (γ : log_names)
      (γf : gname)
      (cov : gset Z) (logstart inodestart : Z) (nib : nat) (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (bm bm' : blkmap) (data data' : nat -> list (bv 8))
      (dn dn' dn0 dn0' : dinode)
      (user : bool) (off n tot : nat) (src_bytes wrote : nat -> bv 8)
      (dist : nat) (dstb : nat -> bv 8)
      (V : pprivate) (P' : uptd) (ncount n' : nat) (Sb Sb' : gset Z)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac) (A : bm_alloc) (j : nat)
      (m M : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) :
    (K_writei <= K)%nat ->
    wi_sp m M ->
    (* the six registers this block does NOT restore are already back *)
    M !!! Regidx Rs1  = (m !!! Regidx Rs1  : mword 64) ->
    M !!! Regidx Rs3  = (m !!! Regidx Rs3  : mword 64) ->
    M !!! Regidx Rs8  = (m !!! Regidx Rs8  : mword 64) ->
    M !!! Regidx Rs9  = (m !!! Regidx Rs9  : mword 64) ->
    M !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64) ->
    M !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64) ->
    (* ...and the answer is in a0 *)
    blkmap_wf cov logstart bm' ->
    blk_holes_zero bm' data' ->
    di_addrs dn' = bm_cells bm' ->
    bv_unsigned (di_size dn') < 2 ^ 31 ->
    bm_covers bm' (bv_unsigned (di_size dn')) ->
    (bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
     bv_unsigned (di_size dn') <= Z.of_nat MAXFILE * Z.of_nat BSIZE) ->
    (inode_sized data -> inode_sized data') ->
    (dist <= BSIZE)%nat ->
    ((tot = n)%nat -> dist = 0%nat) ->
    (user = false -> dist = 0%nat) ->
    (forall k : nat,
       file_byte data' k
       = if decide ((off <= k)%nat /\ (k < off + tot)%nat)
         then wrote (k - off)%nat
         else if decide ((off + tot <= k)%nat /\ (k < off + tot + dist)%nat)
              then dstb (k - (off + tot))%nat
              else file_byte data k) ->
    (user = false -> forall i : nat, (i < tot)%nat -> wrote i = src_bytes i) ->
    ((M !!! Regidx Ra0 = (mword_of_int (-1) : mword 64)
      /\ (bv_unsigned (di_size dn) < Z.of_nat off
          \/ (MAXFILE * BSIZE < off + n)%nat)
      /\ tot = 0%nat /\ dist = 0%nat
      /\ bm' = bm /\ data' = data /\ dn' = dn /\ dn0' = dn0
      /\ n' = ncount)
     \/ (M !!! Regidx Ra0 = (mword_of_int (Z.of_nat tot) : mword 64)
         /\ (tot <= n)%nat
         /\ dn' = wi_dinode dn bm' off tot
         /\ dn0' = dn')) ->
    ((ncount - wi_cost_bmonly off n)%nat <= n')%nat -> (n' <= ncount)%nat ->
    Sb ⊆ Sb' ->
    wi16_post (ba_bms A) inum inodestart ncount n' off n tot bm bm' Sb Sb' ->
    wi16_spend_any (ba_bms A) inum inodestart ncount n' off n bm bm' Sb ->
    wi16_atomic off n tot ->
    uptd_ext (pv_upt V) P' ->
    sie_cap_gpr KT1 M (K - 14)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (WI + 0xdc) : mword 64) -∗
    wi_fr7 m -∗
    i_dev ip ↦₄{dqd} dev -∗
    i_inum ip ↦₄{dqn} inum -∗
    inode_meta ip dn' -∗
    inode_map γfs ip bm' -∗
    inode_blocks γfs bm' data' -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bm_alloc_res γfs cov logstart A -∗
    dinode_at γi inum dn0' -∗
    (if user
     then proc_priv_core (proc_addr j) pidv (upd_upt V P')
     else ([∗ list] i ∈ seq 0 n,
             pa_add (m !!! Regidx Ra2 : mword 64) i ↦ₘ[ktb] (src_bytes i)) ∗
          p_pid (proc_addr j) ↦₄{dq} pidv) -∗
    bslots bn 3 -∗
    log_opS γ n' Sb' -∗
    wi_cont (ktb := ktb) (CID0 := CID0) γfs γi bn γ γf cov logstart inodestart nib dev ip inum
            bm data dn dn0 user off n src_bytes V ncount Sb
            pidv dq dqd dqn dqs A j
            m K eb b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp Hs1 Hs3 Hs8 Hs9 Hs10 Hs11
           Hwf' Hhz' Hadr' Hsz' Hcov' Hcap' Hsized' Hdb Hd0 Hdk Hrange Hker Harm
           Hlo Hhi Hsbsub Hwi16 Hwiany Hwiat Hext.
    pose proof HK as HK'. 
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc Hframe Hidev Hinum
              Hmeta Hmap Hblocks Hsb Hba Hdn Hsrc Hsl Hop Hcont".
    iDestruct (CpuOwn.cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    iPoseProof (wri_dc with "Htext") as "Hid6".
    iPoseProof (wri_de with "Htext") as "Hid8".
    iPoseProof (wri_e0 with "Htext") as "Hida".
    iPoseProof (wri_e2 with "Htext") as "Hidc".
    iPoseProof (wri_e4 with "Htext") as "Hide".
    iPoseProof (wri_e6 with "Htext") as "Hie0".
    iPoseProof (wri_e8 with "Htext") as "Hie2".
    iPoseProof (wri_ea with "Htext") as "Hie4".
    iPoseProof (wri_ec with "Htext") as "Hie6".
    rewrite /wi_fr7.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9
                            & HfA & HfB & HfC & HfD & HfE)".
    (* the seven loaded slots, at the addresses the [c.ldsp]s form *)
    assert (Hc1 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hc2 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hc4 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hc6 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hc7 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 7).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hc8 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hc9 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 9).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    (* ===== +0xd6 c.ldsp ra,104(sp) ===== *)
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0xdc)) (mword_of_int 13 : mword 6) Rra
              M (K - 14)%nat (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hid6 [Hf1]").
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> M).
    assert (HP1sp : wi_sp m P1)
      by (rewrite /wi_sp /P1 upd_ne; [exact Hsp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xdc) : mword 64) 2
                  = mword_of_int (WI + 0xde)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xd8 c.ldsp s0,96(sp) ===== *)
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0xde)) (mword_of_int 12 : mword 6) Rs0
              P1 (K - 14)%nat (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hid8 [Hf2]").
    { iEval (rewrite HP1sp -Hsp Hc2). iExact "Hf2". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -Hsp Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : wi_sp m P2)
      by (rewrite /wi_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xde) : mword 64) 2
                  = mword_of_int (WI + 0xe0)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xda c.ldsp s2,80(sp) ===== *)
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0xe0)) (mword_of_int 10 : mword 6) Rs2
              P2 (K - 14)%nat (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hida [Hf4]").
    { iEval (rewrite HP2sp -Hsp Hc4). iExact "Hf4". }
    iIntros (CID3 Hq3) "Hcg Hpc Hf4".
    iEval (rewrite HP2sp -Hsp Hc4) in "Hf4".
    set (P3 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P2).
    assert (HP3sp : wi_sp m P3)
      by (rewrite /wi_sp /P3 upd_ne; [exact HP2sp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xe0) : mword 64) 2
                  = mword_of_int (WI + 0xe2)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xdc c.ldsp s4,64(sp) ===== *)
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0xe2)) (mword_of_int 8 : mword 6) Rs4
              P3 (K - 14)%nat (m !!! Regidx Rs4 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hidc [Hf6]").
    { iEval (rewrite HP3sp -Hsp Hc6). iExact "Hf6". }
    iIntros (CID4 Hq4) "Hcg Hpc Hf6".
    iEval (rewrite HP3sp -Hsp Hc6) in "Hf6".
    set (P4 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> P3).
    assert (HP4sp : wi_sp m P4)
      by (rewrite /wi_sp /P4 upd_ne; [exact HP3sp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xe2) : mword 64) 2
                  = mword_of_int (WI + 0xe4)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xde c.ldsp s5,56(sp) ===== *)
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0xe4)) (mword_of_int 7 : mword 6) Rs5
              P4 (K - 14)%nat (m !!! Regidx Rs5 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hide [Hf7]").
    { iEval (rewrite HP4sp -Hsp Hc7). iExact "Hf7". }
    iIntros (CID5 Hq5) "Hcg Hpc Hf7".
    iEval (rewrite HP4sp -Hsp Hc7) in "Hf7".
    set (P5 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> P4).
    assert (HP5sp : wi_sp m P5)
      by (rewrite /wi_sp /P5 upd_ne; [exact HP4sp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xe4) : mword 64) 2
                  = mword_of_int (WI + 0xe6)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xe0 c.ldsp s6,48(sp) ===== *)
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0xe6)) (mword_of_int 6 : mword 6) Rs6
              P5 (K - 14)%nat (m !!! Regidx Rs6 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hie0 [Hf8]").
    { iEval (rewrite HP5sp -Hsp Hc8). iExact "Hf8". }
    iIntros (CID6 Hq6) "Hcg Hpc Hf8".
    iEval (rewrite HP5sp -Hsp Hc8) in "Hf8".
    set (P6 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> P5).
    assert (HP6sp : wi_sp m P6)
      by (rewrite /wi_sp /P6 upd_ne; [exact HP5sp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xe6) : mword 64) 2
                  = mword_of_int (WI + 0xe8)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xe2 c.ldsp s7,40(sp) ===== *)
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0xe8)) (mword_of_int 5 : mword 6) Rs7
              P6 (K - 14)%nat (m !!! Regidx Rs7 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hie2 [Hf9]").
    { iEval (rewrite HP6sp -Hsp Hc9). iExact "Hf9". }
    iIntros (CID7 Hq7) "Hcg Hpc Hf9".
    iEval (rewrite HP6sp -Hsp Hc9) in "Hf9".
    set (P7 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7 : mword 64)]> P6).
    assert (HP7sp : wi_sp m P7)
      by (rewrite /wi_sp /P7 upd_ne; [exact HP6sp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xe8) : mword 64) 2
                  = mword_of_int (WI + 0xea)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xe4 c.addi16sp sp,112 : pop ===== *)
    assert (Hwv : add_vec (P7 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 7 : mword 6)))
                  = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite HP7sp. apply bv_eq.
      rewrite !add_vec64_unsigned bv_wrap_add_idemp_l.
      assert (Hz : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 57 : mword 6)) : mword 64)
                   = 18446744073709551504) by (vm_compute; reflexivity).
      assert (Hz2 : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 7 : mword 6)) : mword 64)
                    = 112) by (vm_compute; reflexivity).
      rewrite Hz Hz2.
      replace (bv_unsigned (m !!! Regidx csp_rs1 : mword 64) + 18446744073709551504 + 112)
        with (bv_unsigned (m !!! Regidx csp_rs1 : mword 64) + 18446744073709551616) by ring.
      rewrite -bv_wrap_add_idemp_r.
      assert (Hm0 : bv_wrap 64 18446744073709551616 = 0) by (vm_compute; reflexivity).
      rewrite Hm0 Z.add_0_r.
      apply bv_wrap_small. apply bv_unsigned_in_range. }
    assert (Hpop : (P7 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P7 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 7 : mword 6)))) 14).
    { rewrite Hwv HP7sp. unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iAssert (stack_own (KTR := KT1) (m !!! Regidx csp_rs1 : mword 64) 14)
      with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 HfA HfB HfC HfD HfE]" as "Hstk".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hf1"; [iExists _; iExact "Hf1"|].
      iSplitL "Hf2"; [iExists _; iExact "Hf2"|].
      iSplitL "Hf3"; [iExact "Hf3"|].
      iSplitL "Hf4"; [iExists _; iExact "Hf4"|].
      iSplitL "Hf5"; [iExact "Hf5"|].
      iSplitL "Hf6"; [iExists _; iExact "Hf6"|].
      iSplitL "Hf7"; [iExists _; iExact "Hf7"|].
      iSplitL "Hf8"; [iExists _; iExact "Hf8"|].
      iSplitL "Hf9"; [iExists _; iExact "Hf9"|].
      iSplitL "HfA"; [iExact "HfA"|].
      iSplitL "HfB"; [iExact "HfB"|].
      iSplitL "HfC"; [iExact "HfC"|].
      iSplitL "HfD"; [iExact "HfD"|].
      iSplitL "HfE"; [iExact "HfE"|].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (WI + 0xea))
              (mword_of_int 7 : mword 6) P7 (K - 14)%nat 14 b Hpop
              with "Hcg Hpc Hie4 Hstk").
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (P8 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P7 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 7 : mword 6))))]> P7).
    assert (Hnk : ((K - 14) + 14)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xea) : mword 64) 2
                  = mword_of_int (WI + 0xec)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xe6 c.ret ===== *)
    assert (HP8ra : P8 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
      rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
      rewrite /P2 upd_ne; [| nz]. rewrite /P1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (WI + 0xec)) Rra P8 K b ltac:(nz)
              with "Hcg Hpc Hie6").
    iIntros (CID9 Hq9) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P8 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP8ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CONTRACT ===== *)
    assert (Csp : P8 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P8 upd_eq; exact Hwv).
    assert (Cs0 : P8 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
      rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
      rewrite /P2 upd_eq. reflexivity. }
    assert (Cs2 : P8 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
      rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_eq. reflexivity. }
    assert (Cs4 : P8 !!! Regidx Rs4 = (m !!! Regidx Rs4 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
      rewrite /P4 upd_eq. reflexivity. }
    assert (Cs5 : P8 !!! Regidx Rs5 = (m !!! Regidx Rs5 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_eq. reflexivity. }
    assert (Cs6 : P8 !!! Regidx Rs6 = (m !!! Regidx Rs6 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_eq. reflexivity. }
    assert (Cs7 : P8 !!! Regidx Rs7 = (m !!! Regidx Rs7 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_eq. reflexivity. }
    assert (Cother : forall c : mword 5,
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs2 -> c <> Rs4 -> c <> Rs5 ->
              c <> Rs6 -> c <> Rs7 -> c <> Rra ->
              P8 !!! Regidx c = (M !!! Regidx c : mword 64)).
    { intros c N2 N8 N18 N20 N21 N22 N23 N1.
      rewrite /P8 upd_ne; [| congruence]. rewrite /P7 upd_ne; [| congruence].
      rewrite /P6 upd_ne; [| congruence]. rewrite /P5 upd_ne; [| congruence].
      rewrite /P4 upd_ne; [| congruence]. rewrite /P3 upd_ne; [| congruence].
      rewrite /P2 upd_ne; [| congruence]. rewrite /P1 upd_ne; [| congruence].
      reflexivity. }
    assert (Cs1 : P8 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite (Cother Rs1); [exact Hs1 | nz | nz | nz | nz | nz | nz | nz | nz]. }
    assert (Cs3 : P8 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (Cother Rs3); [exact Hs3 | nz | nz | nz | nz | nz | nz | nz | nz]. }
    assert (Cs8 : P8 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64)).
    { rewrite (Cother Rs8); [exact Hs8 | nz | nz | nz | nz | nz | nz | nz | nz]. }
    assert (Cs9 : P8 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64)).
    { rewrite (Cother Rs9); [exact Hs9 | nz | nz | nz | nz | nz | nz | nz | nz]. }
    assert (Cs10 : P8 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64)).
    { rewrite (Cother Rs10); [exact Hs10 | nz | nz | nz | nz | nz | nz | nz | nz]. }
    assert (Cs11 : P8 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64)).
    { rewrite (Cother Rs11); [exact Hs11 | nz | nz | nz | nz | nz | nz | nz | nz]. }
    assert (Ca0 : P8 !!! Regidx Ra0 = (M !!! Regidx Ra0 : mword 64)).
    { rewrite (Cother Ra0); [reflexivity | nz | nz | nz | nz | nz | nz | nz | nz]. }
   iDestruct (cpu_own_transport CID0 CID9 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (IntrDefs.trap_csrs_ext_transport CID0 CID9 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (IntrDefs.cpu_claim_ext_transport CID0 CID9 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    rewrite /wi_cont.
    iSpecialize ("Hcont" $! CID9 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! P8 tot bm' data' dn' dn0' n' wrote dist dstb P' Sb'
              with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hcnt Hextc Hextm Hpc Hidev Hinum Hmeta Hmap Hblocks Hsb Hba Hdn
                    Hsrc Hsl Hop").
    { unfold callee_saved. split_and!; assumption. }
    { exact Hwf'. }
    { exact Hhz'. }
    { exact Hadr'. }
    { exact Hsz'. }
    { exact Hcov'. }
    { exact Hcap'. }
    { exact Hsized'. }
    { exact Hdb. }
    { exact Hd0. }
    { exact Hdk. }
    { exact Hrange. }
    { exact Hker. }
    { rewrite Ca0. exact Harm. }
    { split; assumption. }
    { exact Hsbsub. }
    { exact Hwi16. }
    { exact Hwiany. }
    { exact Hwiat. }
    { exact Hext. }
  Qed.

End WriteiRet.

(* ===================================================================== *)
(*  +0xcc .. +0xd4 : iupdate, a0 := tot, restore s3.  THREE PATHS JOIN.   *)
(* ===================================================================== *)
Section WriteiJoin.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}.

  (* the CALLER's buffer tier -- see this function's spec for why it is not
     [KT1].  A KtierLe HYPOTHESIS in the section beats [ktier_le_refl] at
     instance search, so every OTHER leaf in this file has to name its own
     datum tier out loud (the blanket [(ktd := KT1)] below). *)
  Context {ktb : ktier}.
  Context `{!KtierLe ktb KT1}.
  Local Lemma wi_join `{GEN : GenId} `{CID0 : CpuId} 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (γfs : fs_names) (γi : gname) (bn : bio_names) (γ : log_names)
      (γf : gname)
      (cov : gset Z) (logstart inodestart : Z) (nib : nat) (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (bm bm' : blkmap) (data data' : nat -> list (bv 8))
      (dn dn' dn0 : dinode)
      (user : bool) (off n tot : nat) (src_bytes wrote : nat -> bv 8)
      (dist : nat) (dstb : nat -> bv 8)
      (V : pprivate) (P' : uptd) (ncount u : nat) (Sb SbC : gset Z)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac) (A : bm_alloc)
      (m M : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) :
    (K_writei <= K)%nat ->
    log_geom_ok cov logstart ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    bv_unsigned (di_type dn) <> 0 ->
    (* §19.6 Part 1: iupdate's type-stability premise, travelling. *)
    di_type_stable dn dn0 ->
    di_nlink_stable dn dn0 ->
    di_addrs dn' = bm_cells bm' ->
    blkmap_wf cov logstart bm' ->
    blk_holes_zero bm' data' ->
    bv_unsigned (di_size dn') < 2 ^ 31 ->
    bm_covers bm' (bv_unsigned (di_size dn')) ->
    (* the +0x2a guard's cap, and [inode_sized] carried across the loop --
       the two [inode_ok] conjuncts a re-parking caller needs.  See
       SpecWritei.v's header. *)
    (off + tot <= MAXFILE * BSIZE)%nat ->
    (inode_sized data -> inode_sized data') ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    wi_sp m M ->
    M !!! Regidx Rs5 = ip ->
    M !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64) ->
    M !!! Regidx Rs1  = (m !!! Regidx Rs1  : mword 64) ->
    M !!! Regidx Rs8  = (m !!! Regidx Rs8  : mword 64) ->
    M !!! Regidx Rs9  = (m !!! Regidx Rs9  : mword 64) ->
    M !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64) ->
    M !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64) ->
    (dist <= BSIZE)%nat ->
    ((tot = n)%nat -> dist = 0%nat) ->
    (user = false -> dist = 0%nat) ->
    (forall k : nat,
       file_byte data' k
       = if decide ((off <= k)%nat /\ (k < off + tot)%nat)
         then wrote (k - off)%nat
         else if decide ((off + tot <= k)%nat /\ (k < off + tot + dist)%nat)
              then dstb (k - (off + tot))%nat
              else file_byte data k) ->
    (user = false -> forall i : nat, (i < tot)%nat -> wrote i = src_bytes i) ->
    (tot <= n)%nat ->
    dn' = wi_dinode dn bm' off tot ->
    ((ncount - wi_cost_bmonly off n)%nat <= u)%nat -> (u <= ncount)%nat ->
    (* AT THE COUNT IN HAND, not at the one iupdate leaves: the credited
       flush GIVES A UNIT BACK when the inode block was already logged, so
       the returned count can be [S u] and the public [n' <= ncount] needs
       the bound one higher.  Every caller has it -- it is the [nI <= ncount]
       the loop invariant carries, at the value [wi_inv_exit] is read off. *)
    (S u <= ncount)%nat ->
    (* the op's logged set has only grown since entry; iupdate grows it once
       more, by this inum's inode block *)
    Sb ⊆ SbC ->
    (* the sixteen-byte receipt, as it stands BEFORE the flush *)
    wi16_pre (ba_bms A) ncount (S u) off n tot bm bm' Sb SbC ->
    uptd_ext (pv_upt V) P' ->
    locks_below lks "log" ->
    sie_cap_gpr KT1 M (K - 14)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (WI + 0xd2) : mword 64) -∗
    panic_env -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    wi_fr8 m -∗
    i_dev ip ↦₄{dqd} dev -∗
    i_inum ip ↦₄{dqn} inum -∗
    inode_meta ip dn' -∗
    inode_map γfs ip bm' -∗
    inode_blocks γfs bm' data' -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bm_alloc_res γfs cov logstart A -∗
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn0 -∗
    (if user
     then proc_priv_core (proc_addr j) pidv (upd_upt V P')
     else ([∗ list] i ∈ seq 0 n,
             pa_add (m !!! Regidx Ra2 : mword 64) i ↦ₘ[ktb] (src_bytes i)) ∗
          p_pid (proc_addr j) ↦₄{dq} pidv) -∗
    bslots bn 3 -∗
    log_opS γ (S u) SbC -∗
    wi_cont (ktb := ktb) (CID0 := CID0) γfs γi bn γ γf cov logstart inodestart nib dev ip inum
            bm data dn dn0 user off n src_bytes V ncount Sb
            pidv dq dqd dqn dqs A j
            m K eb b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hgeom Hist Hicov Hilog Hnib Hdtnz Hstab Hnlk Hadr Hwf' Hhz' Hsz' Hcov'
           Hrngt Hsized'
           Hj Hgl Hsp Hs5 Hs3 Hs1 Hs8 Hs9 Hs10 Hs11 Hdb Hd0 Hdk Hrange Hker Htotn Hdneq
           Hlo Hhi Hhi1 Hsbsub Hwi16 Hext Hlkbelow.
    pose proof HK as HK'. 
    iIntros "Hcg Hcnt Hextc Hextm #Htext #Hkd Hpc #Hpenv #Hbio #Hlctx #Hprocs
              #Hdevi #Hdgeom #Hdlock Hframe Hidev Hinum
              Hmeta Hmap Hblocks Hsb Hba #Hireg Hdn Hsrc Hsl Hop Hcont".
    iDestruct (CpuOwn.cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    iPoseProof (wri_d2 with "Htext") as "Hicc".
    iPoseProof (wri_d4 with "Htext") as "Hice".
    iPoseProof (wri_d8 with "Htext") as "Hid2".
    iPoseProof (wri_da with "Htext") as "Hid4".
    (* ===== +0xcc c.mv a0,s5 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (WI + 0xd2)) Ra0 Rs5
              M (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hicc").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (T0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget M Rs5))]> M).
    assert (HT0a0 : T0 !!! Regidx Ra0 = ip).
    { rewrite /T0 upd_eq. rgne. rewrite Hs5. apply add_vec_zero_l. }
    assert (HT0sp : wi_sp m T0) by (rewrite /wi_sp /T0 upd_ne; [exact Hsp | nz]).
    assert (HT0s3 : T0 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /T0 upd_ne; [exact Hs3 | nz]).
    assert (HT0s1 : T0 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /T0 upd_ne; [exact Hs1 | nz]).
    assert (HT0s8 : T0 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /T0 upd_ne; [exact Hs8 | nz]).
    assert (HT0s9 : T0 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /T0 upd_ne; [exact Hs9 | nz]).
    assert (HT0s10 : T0 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /T0 upd_ne; [exact Hs10 | nz]).
    assert (HT0s11 : T0 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64))
      by (rewrite /T0 upd_ne; [exact Hs11 | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xd2) : mword 64) 2
                  = mword_of_int (WI + 0xd4)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xce jal ra,iupdate ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (WI + 0xd4)) Rra
              (mword_of_int 2095532 : mword 21) T0 (K - 14)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hice").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (T1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (WI + 0xd4) : mword 64) 4)]> T0).
    assert (Htgt : add_vec (mword_of_int (WI + 0xd4) : mword 64)
                     (sign_extend' 64 (mword_of_int 2095532 : mword 21))
                   = mword_of_int KernelSyms.iupdate) by pcw.
    iEval (rewrite Htgt) in "Hpc".
    assert (HT1a0 : T1 !!! Regidx Ra0 = ip)
      by (rewrite /T1 upd_ne; [exact HT0a0 | nz]).
    assert (HT1sp : wi_sp m T1) by (rewrite /wi_sp /T1 upd_ne; [exact HT0sp | nz]).
    assert (HT1ra : T1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (WI + 0xd4) : mword 64) 4)
      by (rewrite /T1; apply upd_eq).
    assert (HT1s3 : T1 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s3 | nz]).
    assert (HT1s1 : T1 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s1 | nz]).
    assert (HT1s8 : T1 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s8 | nz]).
    assert (HT1s9 : T1 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s9 | nz]).
    assert (HT1s10 : T1 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s10 | nz]).
    assert (HT1s11 : T1 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s11 | nz]).
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (IntrDefs.trap_csrs_ext_transport CID0 CID2 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (IntrDefs.cpu_claim_ext_transport CID0 CID2 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID2) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKiu : (K_iupdate <= K - 14)%nat) by (lia).
    assert (Hdirlen : length (bm_dir bm') = NDIRECT)
      by exact (blkmap_wf_dir_len cov logstart bm' Hwf').
    iDestruct (wi_slots_split bn 2 1 with "Hsl") as "[Hsl2 Hsl1]".
    (* THE SET-FORM iupdate: the flush is the last thing writei logs, and
       the set it grows by is exactly this inum's inode block.  Threading it
       (rather than taking the counted form, which re-hides the set behind
       an existential) is what lets the public contract promise its caller
       [Sb ⊆ Sb'] past the flush. *)
    (* BORROW the pid share for iupdate and give it straight back.  ONE
       lemma serves both arms: on the user arm the quarter comes out of
       [proc_priv] and goes back into it; on the kernel arm it is the
       caller's own share, riding with the buffer. *)
    iDestruct (wi_src_pid γf j pidv dq user (upd_upt V P')
                 (m !!! Regidx Ra2 : mword 64) n src_bytes with "Hsrc")
      as "[Hppid Hsrcback]".
    (* THE CREDITED FLUSH.  [wp_iupdate_gen] is this at [cru := false]; the
       sixteen-byte contract needs the credit itself, because [wi16_spend]
       charges nothing for a flush whose block the op had already logged.
       The credit is a DECIDABLE READ of the running set, so no case split
       reaches the walk -- only the returned count carries the [if]. *)
    iApply fupd_wp. iMod (log_epoch_lb_0 γ) as "#Hlb0". iModIntro.
    (* THE CREDIT, IN ITS OWN-SET FORM (fs-log.md §G.4): credgen takes a
       RESOURCE now, and [log_credit_own] converts the decidable read.  The
       birth epoch is opened for it and re-closed by iupdate's own post. *)
    iDestruct (log_opS_named with "Hop") as (e0) "Hop".
    iPoseProof (log_credit_own γ (bool_decide (IBLOCK inum inodestart ∈ SbC))
                  SbC e0 (IBLOCK inum inodestart)
                  ltac:(intros Hc; exact (proj1 (bool_decide_eq_true _) Hc)))
      as "#Hcrdu".
    iApply (IU.wp_iupdate_credgen γs j γl γu γd γk pd pav pu bn γ γfs γi
              cov logstart inodestart nib dev ip inum dn' dn0 bm' u SbC
              (bool_decide (IBLOCK inum inodestart ∈ SbC)) e0 0%nat
              pidv (wi_q user dq) dqd dqn dqs T1 (K - 14)%nat eb b lks
              HKiu
              Hgeom Hist Hicov Hilog Hnib
              (* §19.6 Part 1: the flushed [dn'] keeps [dn]'s type ([Hdneq]),
                 and [Hstab] is writei's own premise about [dn] vs [dn0]. *)
              ltac:(rewrite Hdneq; exact Hstab)
              ltac:(rewrite Hdneq; exact Hnlk)
              (* §3.1's TYPE NARROWING: writei flushes a LIVE record --
                 [wi_dinode] keeps [dn]'s type ([Hdneq]) and writei's own
                 [Hdtnz] says that type is nonzero. *)
              ltac:(rewrite Hdneq; exact Hdtnz)
              Hadr Hdirlen Hj Hgl HT1a0
              with "Hcg Hcnt Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hlctx Hidev Hinum Hmeta Hmap
                    Hsb Hireg Hdn Hppid Hprocs Hdevi Hdgeom
                    Hdlock Hsl2 Hlb0 Hcrdu Hop").
    all: try lkbelow.
    iIntros (CID3 Hq3 mI) "%Hcs1 Hcg Hcnt Hextc Hextm Hpc Hppid Hidev Hinum
                           Hmeta Hmap Hsb Hdn Hsl2 Hop Hwit".
    (* the borrow closes: nothing below wi_join wants the fraction *)
    iDestruct ("Hsrcback" with "Hppid") as "Hsrc".
    (* §16.4: iupdate's payout is conditional on the flushed record's type.
       [dn'] is [wi_dinode dn …], which keeps [dn]'s type, so this is the
       ALLOCATED branch and the fragment comes back as such. *)
    assert (Hdt' : bv_unsigned (di_type dn') <> 0)
      by (rewrite Hdneq; exact Hdtnz).
    iDestruct (ireg_out_alloc_inv γi inum dn' Hdt' with "Hdn") as "Hdn".
    assert (Hpcd2 : ret_pc (T1 !!! Regidx Rra : mword 64)
                    = mword_of_int (WI + 0xd8)) by (rewrite HT1ra; pcw).
    iEval (rewrite Hpcd2) in "Hpc".
    iDestruct (wi_slots_join bn 2 1 with "Hsl2 Hsl1") as "Hsl".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmIsp : wi_sp m mI).
    { rewrite /wi_sp
        (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HT1sp. }
    assert (HmIs3 : mI !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs3 ltac:(vm_compute; reflexivity));
          exact HT1s3).
    assert (HmIs1 : mI !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HT1s1).
    assert (HmIs8 : mI !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs8 ltac:(vm_compute; reflexivity));
          exact HT1s8).
    assert (HmIs9 : mI !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs9 ltac:(vm_compute; reflexivity));
          exact HT1s9).
    assert (HmIs10 : mI !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs10 ltac:(vm_compute; reflexivity));
          exact HT1s10).
    assert (HmIs11 : mI !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs11 ltac:(vm_compute; reflexivity));
          exact HT1s11).
    (* ===== +0xd2 c.mv a0,s3 : the return value ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (WI + 0xd8)) Ra0 Rs3
              mI (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hid2").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (T2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mI Rs3))]> mI).
    assert (HT2a0 : T2 !!! Regidx Ra0 = (mword_of_int (Z.of_nat tot) : mword 64)).
    { rewrite /T2 upd_eq. rgne. rewrite HmIs3. apply add_vec_zero_l. }
    assert (HT2sp : wi_sp m T2) by (rewrite /wi_sp /T2 upd_ne; [exact HmIsp | nz]).
    assert (HT2s1 : T2 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /T2 upd_ne; [exact HmIs1 | nz]).
    assert (HT2s8 : T2 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /T2 upd_ne; [exact HmIs8 | nz]).
    assert (HT2s9 : T2 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /T2 upd_ne; [exact HmIs9 | nz]).
    assert (HT2s10 : T2 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /T2 upd_ne; [exact HmIs10 | nz]).
    assert (HT2s11 : T2 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64))
      by (rewrite /T2 upd_ne; [exact HmIs11 | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xd8) : mword 64) 2
                  = mword_of_int (WI + 0xda)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xd4 c.ldsp s3,72(sp) ===== *)
    rewrite /wi_fr8.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9
                            & HfA & HfB & HfC & HfD & HfE)".
    assert (Hc5 : add_vec (T2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0xda)) (mword_of_int 9 : mword 6) Rs3
              T2 (K - 14)%nat (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hid4 [Hf5]").
    { iEval (rewrite Hc5). iExact "Hf5". }
    iIntros (CID5 Hq5) "Hcg Hpc Hf5".
    iEval (rewrite Hc5) in "Hf5".
    set (T3 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> T2).
    assert (HT3sp : wi_sp m T3) by (rewrite /wi_sp /T3 upd_ne; [exact HT2sp | nz]).
    assert (HT3s3 : T3 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /T3; apply upd_eq).
    assert (HT3a0 : T3 !!! Regidx Ra0 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /T3 upd_ne; [exact HT2a0 | nz]).
    assert (HT3s1 : T3 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /T3 upd_ne; [exact HT2s1 | nz]).
    assert (HT3s8 : T3 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /T3 upd_ne; [exact HT2s8 | nz]).
    assert (HT3s9 : T3 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /T3 upd_ne; [exact HT2s9 | nz]).
    assert (HT3s10 : T3 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /T3 upd_ne; [exact HT2s10 | nz]).
    assert (HT3s11 : T3 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64))
      by (rewrite /T3 upd_ne; [exact HT2s11 | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xda) : mword 64) 2
                  = mword_of_int (WI + 0xdc)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== into the return block ===== *)
    iAssert (wi_fr7 m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 HfA HfB HfC HfD HfE]"
      as "Hframe".
    { rewrite /wi_fr7.
      iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
      iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
      iSplitL "Hf5"; [iExists _; iExact "Hf5"|].
      iSplitL "Hf6"; [iExact "Hf6"|]. iSplitL "Hf7"; [iExact "Hf7"|].
      iSplitL "Hf8"; [iExact "Hf8"|]. iSplitL "Hf9"; [iExact "Hf9"|].
      iSplitL "HfA"; [iExact "HfA"|]. iSplitL "HfB"; [iExact "HfB"|].
      iSplitL "HfC"; [iExact "HfC"|]. iSplitL "HfD"; [iExact "HfD"|].
      iExact "HfE". }
    iDestruct (cpu_own_transport CID3 CID5 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (IntrDefs.trap_csrs_ext_transport CID3 CID5 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (IntrDefs.cpu_claim_ext_transport CID3 CID5 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    assert (Hdwf' : dinode_wf dn').
    { rewrite /dinode_wf Hadr /bm_cells length_app Hdirlen /=.
      unfold NDIRECT. lia. }
    iApply (wi_ret (CID0 := CID5) γfs γi bn γ γf cov logstart inodestart nib
              dev ip inum
              bm bm' data data' dn dn' dn0 dn'
              user off n tot src_bytes wrote dist dstb V P' ncount
              (if bool_decide (IBLOCK inum inodestart ∈ SbC) then S u else u)%nat
              Sb (SbC ∪ {[IBLOCK inum inodestart]})
              pidv dq dqd dqn dqs A j m T3 K eb b lks
              HK HT3sp HT3s1 HT3s3 HT3s8 HT3s9 HT3s10 HT3s11
              Hwf' Hhz'
              Hadr Hsz' Hcov'
              ltac:(intros Hc; rewrite Hdneq;
                    exact (wi_size_cap bm' dn off tot Hrngt Hc))
              Hsized'
              Hdb Hd0 Hdk Hrange Hker
              ltac:(right; split_and!;
                    [exact HT3a0 | exact Htotn | exact Hdneq | reflexivity])
              ltac:(case_bool_decide; lia) ltac:(case_bool_decide; lia)
              (wiset_sub_add_r Sb SbC {[IBLOCK inum inodestart]} Hsbsub)
              (wi16_pre_join (ba_bms A) inum inodestart ncount u off n tot
                 bm bm' Sb SbC Hsbsub Hwi16)
              (* the same receipt read for its unguarded halves: the spend
                 across the flush, and the granularity fact it carries *)
              (wi16_pre_spend (ba_bms A) inum inodestart ncount u off n tot
                 bm bm' Sb SbC Hsbsub Hwi16)
              (wi16_pre_atomic (ba_bms A) ncount (S u) off n tot
                 bm bm' Sb SbC Hwi16)
              Hext
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hframe Hidev Hinum
                    Hmeta Hmap Hblocks Hsb Hba Hdn Hsrc Hsl Hop [Hcont]").
    iApply (wp_next_shift (b := true) (CIDa := CID2) (CIDb := CID5) ltac:(wp_next_chain)
              with "Hcont").
  Qed.

End WriteiJoin.

(* ===================================================================== *)
(*  +0xb6 .. +0xcc : the size test, the store, the five restores.         *)
(*  Both arms restore s1/s8..s11 and reach the join at +0xcc, which is    *)
(*  bmap's s4 lesson at five registers instead of one.                    *)
(* ===================================================================== *)
Section WriteiSize.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}.

  (* the CALLER's buffer tier -- see this function's spec for why it is not
     [KT1].  A KtierLe HYPOTHESIS in the section beats [ktier_le_refl] at
     instance search, so every OTHER leaf in this file has to name its own
     datum tier out loud (the blanket [(ktd := KT1)] below). *)
  Context {ktb : ktier}.
  Context `{!KtierLe ktb KT1}.
  Local Lemma wi_size `{GEN : GenId} `{CID0 : CpuId} 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (γfs : fs_names) (γi : gname) (bn : bio_names) (γ : log_names)
      (γf : gname)
      (cov : gset Z) (logstart inodestart : Z) (nib : nat) (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (bm bm' : blkmap) (data data' : nat -> list (bv 8))
      (dn dn0 : dinode)
      (user : bool) (off n tot : nat) (src_bytes wrote : nat -> bv 8)
      (dist : nat) (dstb : nat -> bv 8)
      (V : pprivate) (P' : uptd) (ncount u : nat) (Sb SbC : gset Z)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac) (A : bm_alloc)
      (m M : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) :
    (K_writei <= K)%nat ->
    log_geom_ok cov logstart ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    bv_unsigned (di_type dn) <> 0 ->
    (* §19.6 Part 1: iupdate's type-stability premise, travelling. *)
    di_type_stable dn dn0 ->
    di_nlink_stable dn dn0 ->
    blkmap_wf cov logstart bm' ->
    blk_holes_zero bm' data' ->
    (* COVERAGE, in the two halves the loop leaves it in: at the OLD size
       (the caller's premise, carried across every bmap call) and at the
       byte offset the write reached.  [wi_covers_final] joins them at
       whichever of the two [wi_dinode] installs. *)
    bm_covers bm' (bv_unsigned (di_size dn)) ->
    bm_covers bm' (Z.of_nat (off + tot)) ->
    bv_unsigned (di_size dn) < 2 ^ 31 ->
    Z.of_nat (off + tot) < 2 ^ 31 ->
    (* the +0x2a guard's cap, and [inode_sized] carried across the loop --
       forwarded to [wi_join].  See SpecWritei.v's header. *)
    (off + tot <= MAXFILE * BSIZE)%nat ->
    (inode_sized data -> inode_sized data') ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    wi_sp m M ->
    M !!! Regidx Rs5 = ip ->
    M !!! Regidx Rs2 = (mword_of_int (Z.of_nat (off + tot)) : mword 64) ->
    M !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64) ->
    (dist <= BSIZE)%nat ->
    ((tot = n)%nat -> dist = 0%nat) ->
    (user = false -> dist = 0%nat) ->
    (forall k : nat,
       file_byte data' k
       = if decide ((off <= k)%nat /\ (k < off + tot)%nat)
         then wrote (k - off)%nat
         else if decide ((off + tot <= k)%nat /\ (k < off + tot + dist)%nat)
              then dstb (k - (off + tot))%nat
              else file_byte data k) ->
    (user = false -> forall i : nat, (i < tot)%nat -> wrote i = src_bytes i) ->
    (tot <= n)%nat ->
    ((ncount - wi_cost_bmonly off n)%nat <= u)%nat -> (u <= ncount)%nat ->
    (* at the count IN HAND -- see [wi_join]'s premise of the same shape *)
    (S u <= ncount)%nat ->
    Sb ⊆ SbC ->
    (* the sixteen-byte receipt, travelling to the join unchanged *)
    wi16_pre (ba_bms A) ncount (S u) off n tot bm bm' Sb SbC ->
    uptd_ext (pv_upt V) P' ->
    locks_below lks "log" ->
    sie_cap_gpr KT1 M (K - 14)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (WI + 0xbc) : mword 64) -∗
    panic_env -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    wi_fr13 m -∗
    i_dev ip ↦₄{dqd} dev -∗
    i_inum ip ↦₄{dqn} inum -∗
    inode_meta ip dn -∗
    inode_map γfs ip bm' -∗
    inode_blocks γfs bm' data' -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bm_alloc_res γfs cov logstart A -∗
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn0 -∗
    (if user
     then proc_priv_core (proc_addr j) pidv (upd_upt V P')
     else ([∗ list] i ∈ seq 0 n,
             pa_add (m !!! Regidx Ra2 : mword 64) i ↦ₘ[ktb] (src_bytes i)) ∗
          p_pid (proc_addr j) ↦₄{dq} pidv) -∗
    bslots bn 3 -∗
    log_opS γ (S u) SbC -∗
    wi_cont (ktb := ktb) (CID0 := CID0) γfs γi bn γ γf cov logstart inodestart nib dev ip inum
            bm data dn dn0 user off n src_bytes V ncount Sb
            pidv dq dqd dqn dqs A j
            m K eb b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hgeom Hist Hicov Hilog Hnib Hdtnz Hstab Hnlk Hwf' Hhz' HcovS HcovT Hszlt Hofflt
           Hrngt Hsized'
           Hj Hgl Hsp Hs5 Hs2 Hs3 Hdb Hd0 Hdk Hrange Hker Htotn Hlo Hhi Hhi1 Hsbsub
           Hwi16 Hext Hlkbelow.
    pose proof HK as HK'. 
    change (2 ^ 31)%Z with 2147483648%Z in Hszlt, Hofflt.
    (* the coverage the join needs: whichever size [wi_dinode] installs is
       covered, because both candidates are *)
    assert (Hcovf : bm_covers bm' (bv_unsigned (di_size (wi_dinode dn bm' off tot))))
      by exact (ProofWriteiParts.wi_covers_final bm' dn off tot
                  ltac:(clear -Hofflt; lia) HcovS HcovT).
    iIntros "Hcg Hcnt Hextc Hextm #Htext #Hkd Hpc #Hpenv #Hbio #Hlctx #Hprocs
              #Hdevi #Hdgeom #Hdlock Hframe Hidev Hinum
              Hmeta Hmap Hblocks Hsb Hba #Hireg Hdn Hsrc Hsl Hop Hcont".
    iDestruct (CpuOwn.cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    iPoseProof (wri_bc with "Htext") as "Hib6".
    iPoseProof (wri_c0 with "Htext") as "Hiba".
    iPoseProof (wri_c4 with "Htext") as "Hibe".
    iPoseProof (wri_c8 with "Htext") as "Hic2".
    iPoseProof (wri_ca with "Htext") as "Hic4".
    iPoseProof (wri_cc with "Htext") as "Hic6".
    iPoseProof (wri_ce with "Htext") as "Hic8".
    iPoseProof (wri_d0 with "Htext") as "Hica".
    iPoseProof (wri_f2 with "Htext") as "Hiec".
    iPoseProof (wri_f4 with "Htext") as "Hiee".
    iPoseProof (wri_f6 with "Htext") as "Hif0".
    iPoseProof (wri_f8 with "Htext") as "Hif2".
    iPoseProof (wri_fa with "Htext") as "Hif4".
    iPoseProof (wri_fc with "Htext") as "Hif6".
    rewrite /wi_fr13.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9
                            & HfA & HfB & HfC & HfD & HfE)".
    rewrite /inode_meta.
    iDestruct "Hmeta" as "(Hmt & Hmj & Hmn & Hml & Hmz)".
    (* ===== +0xb6 lw a5,76(s5) : a5 := ip->size ===== *)
    assert (Hszadr : add_vec (rget M Rs5) (sign_extend' 64 (mword_of_int 76 : mword 12))
                     = i_size ip).
    { rgne. rewrite Hs5. reflexivity. }
    iEval (rewrite -Hszadr) in "Hmz".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (WI + 0xbc)) Ra5 Rs5
              (mword_of_int 76 : mword 12) M (K - 14)%nat (di_size dn : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hib6 Hmz").
    iIntros (CIDz1 Hqz1) "Hcg Hpc Hmz".
    iEval (rewrite Hszadr) in "Hmz".
    set (M0 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (di_size dn : mword 32))]> M).
    assert (HM0a5 : M0 !!! Regidx Ra5 = (sign_extend' 64 (di_size dn : mword 32) : mword 64))
      by (rewrite /M0; apply upd_eq).
    assert (HM0s5 : M0 !!! Regidx Rs5 = ip)
      by (rewrite /M0 upd_ne; [exact Hs5 | nz]).
    assert (HM0s2 : M0 !!! Regidx Rs2 = (mword_of_int (Z.of_nat (off + tot)) : mword 64))
      by (rewrite /M0 upd_ne; [exact Hs2 | nz]).
    assert (HM0s3 : M0 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /M0 upd_ne; [exact Hs3 | nz]).
    assert (HM0sp : wi_sp m M0) by (rewrite /wi_sp /M0 upd_ne; [exact Hsp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xbc) : mword 64) 4
                  = mword_of_int (WI + 0xc0)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* the two unsigned readings the [bgeu] compares *)
    assert (Hszu : bv_unsigned (sign_extend' 64 (di_size dn : mword 32) : mword 64)
                   = bv_unsigned (di_size dn))
      by (apply wi_sext32_unsigned; exact Hszlt).
    assert (Hoffu : bv_unsigned (mword_of_int (Z.of_nat (off + tot)) : mword 64)
                    = Z.of_nat (off + tot)).
    { apply moi64_small. split; [apply Nat2Z.is_nonneg |].
      change (2 ^ 64)%Z with 18446744073709551616%Z. lia. }
    (* ===== +0xba bgeu a5,s2 : is the file already this long? ===== *)
    destruct (Z_le_gt_dec (Z.of_nat (off + tot)) (bv_unsigned (di_size dn)))
      as [Hge | Hlt].
    - (* ---------- IT IS: skip the store, restore, jump to +0xcc -------- *)
      assert (Hdsz : di_size (wi_dinode dn bm' off tot) = di_size dn).
      { rewrite /wi_dinode. cbn [di_size].
        case_decide as Hd; [| reflexivity].
        exfalso. exact (Z.lt_irrefl _ (Z.le_lt_trans _ _ _ Hge Hd)). }
      iApply (wp_bgeu_taken_s_sconf (mword_of_int (WI + 0xc0))
                (mword_of_int 50 : mword 13) Rs2 Ra5 M0 (K - 14)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HM0a5 HM0s2; apply bc_geu;
                      rewrite Hszu Hoffu; exact Hge)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hiba").
      iApply bi.later_intro. iIntros (CIDz2 Hqz2) "Hcg Hpc".
      assert (Htgtec : add_vec (mword_of_int (WI + 0xc0) : mword 64)
                         (sign_extend' 64 (mword_of_int 50 : mword 13))
                       = mword_of_int (WI + 0xf2)) by pcw.
      iEval (rewrite Htgtec) in "Hpc".
      set (QB0 := M0).
      assert (HQB0sp : wi_sp m QB0) by exact HM0sp.
      assert (HQB0s5 : QB0 !!! Regidx Rs5 = ip) by exact HM0s5.
      assert (HQB0s3 : QB0 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
        by exact HM0s3.
    assert (HcQB1 : add_vec (QB0 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HQB0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0xf2)) (mword_of_int 11 : mword 6) Rs1
              QB0 (K - 14)%nat (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hiec [Hf3]").
    { iEval (rewrite HcQB1). iExact "Hf3". }
    iIntros (CIDQB1 HqQB1) "Hcg Hpc Hf3".
    iEval (rewrite HcQB1) in "Hf3".
    set (QB1 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> QB0).
    assert (HQB1sp : wi_sp m QB1) by (rewrite /wi_sp /QB1 upd_ne; [exact HQB0sp | nz]).
    assert (HQB1s5 : QB1 !!! Regidx Rs5 = ip)
      by (rewrite /QB1 upd_ne; [exact HQB0s5 | nz]).
    assert (HQB1s3 : QB1 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QB1 upd_ne; [exact HQB0s3 | nz]).
    assert (HQB1Rs1 : QB1 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QB1; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xf2) : mword 64) 2
                  = mword_of_int (WI + 0xf4)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HcQB2 : add_vec (QB1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10).
    { rewrite HQB1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0xf4)) (mword_of_int 4 : mword 6) Rs8
              QB1 (K - 14)%nat (m !!! Regidx Rs8 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hiee [HfA]").
    { iEval (rewrite HcQB2). iExact "HfA". }
    iIntros (CIDQB2 HqQB2) "Hcg Hpc HfA".
    iEval (rewrite HcQB2) in "HfA".
    set (QB2 := <[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8 : mword 64)]> QB1).
    assert (HQB2sp : wi_sp m QB2) by (rewrite /wi_sp /QB2 upd_ne; [exact HQB1sp | nz]).
    assert (HQB2s5 : QB2 !!! Regidx Rs5 = ip)
      by (rewrite /QB2 upd_ne; [exact HQB1s5 | nz]).
    assert (HQB2s3 : QB2 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QB2 upd_ne; [exact HQB1s3 | nz]).
    assert (HQB2Rs1 : QB2 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QB2 upd_ne; [exact HQB1Rs1 | nz]).
    assert (HQB2Rs8 : QB2 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /QB2; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xf4) : mword 64) 2
                  = mword_of_int (WI + 0xf6)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HcQB3 : add_vec (QB2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 11).
    { rewrite HQB2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0xf6)) (mword_of_int 3 : mword 6) Rs9
              QB2 (K - 14)%nat (m !!! Regidx Rs9 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hif0 [HfB]").
    { iEval (rewrite HcQB3). iExact "HfB". }
    iIntros (CIDQB3 HqQB3) "Hcg Hpc HfB".
    iEval (rewrite HcQB3) in "HfB".
    set (QB3 := <[Regidx Rs9 := regval_into_reg (m !!! Regidx Rs9 : mword 64)]> QB2).
    assert (HQB3sp : wi_sp m QB3) by (rewrite /wi_sp /QB3 upd_ne; [exact HQB2sp | nz]).
    assert (HQB3s5 : QB3 !!! Regidx Rs5 = ip)
      by (rewrite /QB3 upd_ne; [exact HQB2s5 | nz]).
    assert (HQB3s3 : QB3 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QB3 upd_ne; [exact HQB2s3 | nz]).
    assert (HQB3Rs1 : QB3 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QB3 upd_ne; [exact HQB2Rs1 | nz]).
    assert (HQB3Rs8 : QB3 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /QB3 upd_ne; [exact HQB2Rs8 | nz]).
    assert (HQB3Rs9 : QB3 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /QB3; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xf6) : mword 64) 2
                  = mword_of_int (WI + 0xf8)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HcQB4 : add_vec (QB3 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 12).
    { rewrite HQB3sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0xf8)) (mword_of_int 2 : mword 6) Rs10
              QB3 (K - 14)%nat (m !!! Regidx Rs10 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hif2 [HfC]").
    { iEval (rewrite HcQB4). iExact "HfC". }
    iIntros (CIDQB4 HqQB4) "Hcg Hpc HfC".
    iEval (rewrite HcQB4) in "HfC".
    set (QB4 := <[Regidx Rs10 := regval_into_reg (m !!! Regidx Rs10 : mword 64)]> QB3).
    assert (HQB4sp : wi_sp m QB4) by (rewrite /wi_sp /QB4 upd_ne; [exact HQB3sp | nz]).
    assert (HQB4s5 : QB4 !!! Regidx Rs5 = ip)
      by (rewrite /QB4 upd_ne; [exact HQB3s5 | nz]).
    assert (HQB4s3 : QB4 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QB4 upd_ne; [exact HQB3s3 | nz]).
    assert (HQB4Rs1 : QB4 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QB4 upd_ne; [exact HQB3Rs1 | nz]).
    assert (HQB4Rs8 : QB4 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /QB4 upd_ne; [exact HQB3Rs8 | nz]).
    assert (HQB4Rs9 : QB4 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /QB4 upd_ne; [exact HQB3Rs9 | nz]).
    assert (HQB4Rs10 : QB4 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /QB4; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xf8) : mword 64) 2
                  = mword_of_int (WI + 0xfa)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HcQB5 : add_vec (QB4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 13).
    { rewrite HQB4sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0xfa)) (mword_of_int 1 : mword 6) Rs11
              QB4 (K - 14)%nat (m !!! Regidx Rs11 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hif4 [HfD]").
    { iEval (rewrite HcQB5). iExact "HfD". }
    iIntros (CIDQB5 HqQB5) "Hcg Hpc HfD".
    iEval (rewrite HcQB5) in "HfD".
    set (QB5 := <[Regidx Rs11 := regval_into_reg (m !!! Regidx Rs11 : mword 64)]> QB4).
    assert (HQB5sp : wi_sp m QB5) by (rewrite /wi_sp /QB5 upd_ne; [exact HQB4sp | nz]).
    assert (HQB5s5 : QB5 !!! Regidx Rs5 = ip)
      by (rewrite /QB5 upd_ne; [exact HQB4s5 | nz]).
    assert (HQB5s3 : QB5 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QB5 upd_ne; [exact HQB4s3 | nz]).
    assert (HQB5Rs1 : QB5 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QB5 upd_ne; [exact HQB4Rs1 | nz]).
    assert (HQB5Rs8 : QB5 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /QB5 upd_ne; [exact HQB4Rs8 | nz]).
    assert (HQB5Rs9 : QB5 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /QB5 upd_ne; [exact HQB4Rs9 | nz]).
    assert (HQB5Rs10 : QB5 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /QB5 upd_ne; [exact HQB4Rs10 | nz]).
    assert (HQB5Rs11 : QB5 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64))
      by (rewrite /QB5; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xfa) : mword 64) 2
                  = mword_of_int (WI + 0xfc)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0xf6 c.j +0xcc ===== *)
      iApply (wp_cj_s_sconf (mword_of_int (WI + 0xfc))
                (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0")))
                QB5 (K - 14)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hif6").
      iIntros (CIDz3 Hqz3). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htgtcc : add_vec (mword_of_int (WI + 0xfc) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 2027 : mword 11) ('b"0"))))
              = mword_of_int (WI + 0xd2)) by pcw.
      iEval (rewrite Htgtcc) in "Hpc".
      iAssert (inode_meta ip (wi_dinode dn bm' off tot))
        with "[Hmt Hmj Hmn Hml Hmz]" as "Hmeta".
      { rewrite /inode_meta /wi_dinode.
        cbn [di_type di_major di_minor di_nlink di_size].
        rewrite -/(di_size (wi_dinode dn bm' off tot)).
        iSplitL "Hmt"; [iExact "Hmt"|]. iSplitL "Hmj"; [iExact "Hmj"|].
        iSplitL "Hmn"; [iExact "Hmn"|]. iSplitL "Hml"; [iExact "Hml"|].
        rewrite Hdsz. iExact "Hmz". }
      iAssert (wi_fr8 m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 HfA HfB HfC HfD HfE]"
        as "Hframe".
      { rewrite /wi_fr8.
        iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
        iSplitL "Hf3"; [iExists _; iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
        iSplitL "Hf5"; [iExact "Hf5"|]. iSplitL "Hf6"; [iExact "Hf6"|].
        iSplitL "Hf7"; [iExact "Hf7"|]. iSplitL "Hf8"; [iExact "Hf8"|].
        iSplitL "Hf9"; [iExact "Hf9"|].
        iSplitL "HfA"; [iExists _; iExact "HfA"|].
        iSplitL "HfB"; [iExists _; iExact "HfB"|].
        iSplitL "HfC"; [iExists _; iExact "HfC"|].
        iSplitL "HfD"; [iExists _; iExact "HfD"|]. iExact "HfE". }
      iDestruct (cpu_own_transport CID0 CIDz3 0 eb (proc_addr j) b 
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (IntrDefs.trap_csrs_ext_transport CID0 CIDz3 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (IntrDefs.cpu_claim_ext_transport CID0 CIDz3 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
      iApply (wi_join (CID0 := CIDz3) γs j γl γu γd γk pd pav pu γfs γi bn γ γf
                cov logstart inodestart nib dev ip inum bm bm' data data' dn
                (wi_dinode dn bm' off tot) dn0 user off n tot src_bytes wrote
                dist dstb V P' ncount u Sb SbC pidv dq dqd dqn dqs A m QB5 K eb b lks
                HK Hgeom Hist Hicov Hilog Hnib Hdtnz Hstab Hnlk eq_refl Hwf' Hhz'
                ltac:(rewrite Hdsz; change (2 ^ 31)%Z with 2147483648%Z; exact Hszlt)
                Hcovf Hrngt Hsized'
                Hj Hgl HQB5sp HQB5s5 HQB5s3
                HQB5Rs1 HQB5Rs8 HQB5Rs9 HQB5Rs10 HQB5Rs11
                Hdb Hd0 Hdk Hrange Hker Htotn eq_refl Hlo Hhi Hhi1 Hsbsub Hwi16 Hext Hlkbelow
                with "Hcg Hcnt Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hlctx Hprocs Hdevi
                      Hdgeom Hdlock Hframe Hidev Hinum Hmeta
                      Hmap Hblocks Hsb Hba Hireg Hdn Hsrc Hsl Hop [Hcont]").
      iApply (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CIDz3) ltac:(wp_next_chain)
                with "Hcont").
    - (* ---------- IT IS NOT: store the new size, restore, fall through -- *)
      assert (Hltz : bv_unsigned (di_size dn) < Z.of_nat (off + tot)) by lia.
      assert (Hdsz : di_size (wi_dinode dn bm' off tot)
                     = (mword_of_int (Z.of_nat (off + tot)) : mword 32)).
      { rewrite /wi_dinode. cbn [di_size].
        case_decide as Hd; [reflexivity | exfalso; exact (Hd Hltz)]. }
      iApply (wp_bgeu_fall_s_sconf (mword_of_int (WI + 0xc0))
                (mword_of_int 50 : mword 13) Rs2 Ra5 M0 (K - 14)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HM0a5 HM0s2; apply bc_ltu;
                      rewrite Hszu Hoffu; exact Hltz)
                with "Hcg Hpc Hiba").
      iIntros (CIDz2 Hqz2) "Hcg Hpc".
      assert (Hpp : add_vec_int (mword_of_int (WI + 0xc0) : mword 64) 4
                    = mword_of_int (WI + 0xc4)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0xbe sw s2,76(s5) : ip->size := off ===== *)
      assert (Hszadr0 : add_vec (rget M0 Rs5) (sign_extend' 64 (mword_of_int 76 : mword 12))
                        = i_size ip).
      { rgne. rewrite HM0s5. reflexivity. }
      iEval (rewrite -Hszadr0) in "Hmz".
      iApply (wp_sw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (WI + 0xc4)) Rs2 Rs5
                (mword_of_int 76 : mword 12) M0 (K - 14)%nat (di_size dn : mword 32) b
                with "Hcg Hpc Hibe Hmz").
      iIntros (CIDz3 Hqz3) "Hcg Hpc Hmz".
      iEval (rewrite Hszadr0) in "Hmz".
      assert (Hstv : trunc32 (rget M0 Rs2) = (mword_of_int (Z.of_nat (off + tot)) : mword 32)).
      { rgne. rewrite HM0s2. apply trunc32_mword_of_int. }
      iEval (rewrite Hstv) in "Hmz".
      assert (Hpp : add_vec_int (mword_of_int (WI + 0xc4) : mword 64) 4
                    = mword_of_int (WI + 0xc8)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      set (QA0 := M0).
      assert (HQA0sp : wi_sp m QA0) by exact HM0sp.
      assert (HQA0s5 : QA0 !!! Regidx Rs5 = ip) by exact HM0s5.
      assert (HQA0s3 : QA0 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
        by exact HM0s3.
    assert (HcQA1 : add_vec (QA0 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HQA0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0xc8)) (mword_of_int 11 : mword 6) Rs1
              QA0 (K - 14)%nat (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hic2 [Hf3]").
    { iEval (rewrite HcQA1). iExact "Hf3". }
    iIntros (CIDQA1 HqQA1) "Hcg Hpc Hf3".
    iEval (rewrite HcQA1) in "Hf3".
    set (QA1 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> QA0).
    assert (HQA1sp : wi_sp m QA1) by (rewrite /wi_sp /QA1 upd_ne; [exact HQA0sp | nz]).
    assert (HQA1s5 : QA1 !!! Regidx Rs5 = ip)
      by (rewrite /QA1 upd_ne; [exact HQA0s5 | nz]).
    assert (HQA1s3 : QA1 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QA1 upd_ne; [exact HQA0s3 | nz]).
    assert (HQA1Rs1 : QA1 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QA1; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xc8) : mword 64) 2
                  = mword_of_int (WI + 0xca)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HcQA2 : add_vec (QA1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10).
    { rewrite HQA1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0xca)) (mword_of_int 4 : mword 6) Rs8
              QA1 (K - 14)%nat (m !!! Regidx Rs8 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hic4 [HfA]").
    { iEval (rewrite HcQA2). iExact "HfA". }
    iIntros (CIDQA2 HqQA2) "Hcg Hpc HfA".
    iEval (rewrite HcQA2) in "HfA".
    set (QA2 := <[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8 : mword 64)]> QA1).
    assert (HQA2sp : wi_sp m QA2) by (rewrite /wi_sp /QA2 upd_ne; [exact HQA1sp | nz]).
    assert (HQA2s5 : QA2 !!! Regidx Rs5 = ip)
      by (rewrite /QA2 upd_ne; [exact HQA1s5 | nz]).
    assert (HQA2s3 : QA2 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QA2 upd_ne; [exact HQA1s3 | nz]).
    assert (HQA2Rs1 : QA2 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QA2 upd_ne; [exact HQA1Rs1 | nz]).
    assert (HQA2Rs8 : QA2 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /QA2; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xca) : mword 64) 2
                  = mword_of_int (WI + 0xcc)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HcQA3 : add_vec (QA2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 11).
    { rewrite HQA2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0xcc)) (mword_of_int 3 : mword 6) Rs9
              QA2 (K - 14)%nat (m !!! Regidx Rs9 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hic6 [HfB]").
    { iEval (rewrite HcQA3). iExact "HfB". }
    iIntros (CIDQA3 HqQA3) "Hcg Hpc HfB".
    iEval (rewrite HcQA3) in "HfB".
    set (QA3 := <[Regidx Rs9 := regval_into_reg (m !!! Regidx Rs9 : mword 64)]> QA2).
    assert (HQA3sp : wi_sp m QA3) by (rewrite /wi_sp /QA3 upd_ne; [exact HQA2sp | nz]).
    assert (HQA3s5 : QA3 !!! Regidx Rs5 = ip)
      by (rewrite /QA3 upd_ne; [exact HQA2s5 | nz]).
    assert (HQA3s3 : QA3 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QA3 upd_ne; [exact HQA2s3 | nz]).
    assert (HQA3Rs1 : QA3 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QA3 upd_ne; [exact HQA2Rs1 | nz]).
    assert (HQA3Rs8 : QA3 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /QA3 upd_ne; [exact HQA2Rs8 | nz]).
    assert (HQA3Rs9 : QA3 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /QA3; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xcc) : mword 64) 2
                  = mword_of_int (WI + 0xce)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HcQA4 : add_vec (QA3 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 12).
    { rewrite HQA3sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0xce)) (mword_of_int 2 : mword 6) Rs10
              QA3 (K - 14)%nat (m !!! Regidx Rs10 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hic8 [HfC]").
    { iEval (rewrite HcQA4). iExact "HfC". }
    iIntros (CIDQA4 HqQA4) "Hcg Hpc HfC".
    iEval (rewrite HcQA4) in "HfC".
    set (QA4 := <[Regidx Rs10 := regval_into_reg (m !!! Regidx Rs10 : mword 64)]> QA3).
    assert (HQA4sp : wi_sp m QA4) by (rewrite /wi_sp /QA4 upd_ne; [exact HQA3sp | nz]).
    assert (HQA4s5 : QA4 !!! Regidx Rs5 = ip)
      by (rewrite /QA4 upd_ne; [exact HQA3s5 | nz]).
    assert (HQA4s3 : QA4 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QA4 upd_ne; [exact HQA3s3 | nz]).
    assert (HQA4Rs1 : QA4 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QA4 upd_ne; [exact HQA3Rs1 | nz]).
    assert (HQA4Rs8 : QA4 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /QA4 upd_ne; [exact HQA3Rs8 | nz]).
    assert (HQA4Rs9 : QA4 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /QA4 upd_ne; [exact HQA3Rs9 | nz]).
    assert (HQA4Rs10 : QA4 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /QA4; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xce) : mword 64) 2
                  = mword_of_int (WI + 0xd0)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HcQA5 : add_vec (QA4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 13).
    { rewrite HQA4sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0xd0)) (mword_of_int 1 : mword 6) Rs11
              QA4 (K - 14)%nat (m !!! Regidx Rs11 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hica [HfD]").
    { iEval (rewrite HcQA5). iExact "HfD". }
    iIntros (CIDQA5 HqQA5) "Hcg Hpc HfD".
    iEval (rewrite HcQA5) in "HfD".
    set (QA5 := <[Regidx Rs11 := regval_into_reg (m !!! Regidx Rs11 : mword 64)]> QA4).
    assert (HQA5sp : wi_sp m QA5) by (rewrite /wi_sp /QA5 upd_ne; [exact HQA4sp | nz]).
    assert (HQA5s5 : QA5 !!! Regidx Rs5 = ip)
      by (rewrite /QA5 upd_ne; [exact HQA4s5 | nz]).
    assert (HQA5s3 : QA5 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QA5 upd_ne; [exact HQA4s3 | nz]).
    assert (HQA5Rs1 : QA5 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QA5 upd_ne; [exact HQA4Rs1 | nz]).
    assert (HQA5Rs8 : QA5 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /QA5 upd_ne; [exact HQA4Rs8 | nz]).
    assert (HQA5Rs9 : QA5 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /QA5 upd_ne; [exact HQA4Rs9 | nz]).
    assert (HQA5Rs10 : QA5 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /QA5 upd_ne; [exact HQA4Rs10 | nz]).
    assert (HQA5Rs11 : QA5 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64))
      by (rewrite /QA5; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xd0) : mword 64) 2
                  = mword_of_int (WI + 0xd2)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
      iAssert (inode_meta ip (wi_dinode dn bm' off tot))
        with "[Hmt Hmj Hmn Hml Hmz]" as "Hmeta".
      { rewrite /inode_meta /wi_dinode.
        cbn [di_type di_major di_minor di_nlink di_size].
        rewrite -/(di_size (wi_dinode dn bm' off tot)).
        iSplitL "Hmt"; [iExact "Hmt"|]. iSplitL "Hmj"; [iExact "Hmj"|].
        iSplitL "Hmn"; [iExact "Hmn"|]. iSplitL "Hml"; [iExact "Hml"|].
        rewrite Hdsz. iExact "Hmz". }
      iAssert (wi_fr8 m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 HfA HfB HfC HfD HfE]"
        as "Hframe".
      { rewrite /wi_fr8.
        iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
        iSplitL "Hf3"; [iExists _; iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
        iSplitL "Hf5"; [iExact "Hf5"|]. iSplitL "Hf6"; [iExact "Hf6"|].
        iSplitL "Hf7"; [iExact "Hf7"|]. iSplitL "Hf8"; [iExact "Hf8"|].
        iSplitL "Hf9"; [iExact "Hf9"|].
        iSplitL "HfA"; [iExists _; iExact "HfA"|].
        iSplitL "HfB"; [iExists _; iExact "HfB"|].
        iSplitL "HfC"; [iExists _; iExact "HfC"|].
        iSplitL "HfD"; [iExists _; iExact "HfD"|]. iExact "HfE". }
      iDestruct (cpu_own_transport CID0 CIDQA5 0 eb (proc_addr j) b 
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (IntrDefs.trap_csrs_ext_transport CID0 CIDQA5 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (IntrDefs.cpu_claim_ext_transport CID0 CIDQA5 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
      assert (Hszn : bv_unsigned (di_size (wi_dinode dn bm' off tot)) < 2147483648).
      { rewrite Hdsz. rewrite moi32_small; [lia |].
        change (2 ^ 32)%Z with 4294967296%Z. lia. }
      iApply (wi_join (CID0 := CIDQA5) γs j γl γu γd γk pd pav pu γfs γi bn γ γf
                cov logstart inodestart nib dev ip inum bm bm' data data' dn
                (wi_dinode dn bm' off tot) dn0 user off n tot src_bytes wrote
                dist dstb V P' ncount u Sb SbC pidv dq dqd dqn dqs A m QA5 K eb b lks
                HK Hgeom Hist Hicov Hilog Hnib Hdtnz Hstab Hnlk eq_refl Hwf' Hhz'
                ltac:(change (2 ^ 31)%Z with 2147483648%Z; exact Hszn)
                Hcovf Hrngt Hsized'
                Hj Hgl HQA5sp HQA5s5 HQA5s3
                HQA5Rs1 HQA5Rs8 HQA5Rs9 HQA5Rs10 HQA5Rs11
                Hdb Hd0 Hdk Hrange Hker Htotn eq_refl Hlo Hhi Hhi1 Hsbsub Hwi16 Hext Hlkbelow
                with "Hcg Hcnt Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hlctx Hprocs Hdevi
                      Hdgeom Hdlock Hframe Hidev Hinum Hmeta
                      Hmap Hblocks Hsb Hba Hireg Hdn Hsrc Hsl Hop [Hcont]").
      iApply (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CIDQA5) ltac:(wp_next_chain)
                with "Hcont").
  Qed.

End WriteiSize.

(* ===================================================================== *)
(*  +0x82 (head) / +0x4c (body) : THE LOOP, by induction on FUEL.         *)
(*                                                                        *)
(*  The head runs bmap and bread, computes the chunk length, and joins    *)
(*  the body at +0x4c through an [iAssert] (the two [m = min(...)] arms   *)
(*  differ only in which register the length came from -- ProofCopyin's   *)
(*  CHUNK/BODY pattern: everything linear is BAKED IN, since a case split *)
(*  uses each branch's copy exclusively, and only the register file, the  *)
(*  chunk length and the hart travel as wands).                           *)
(*                                                                        *)
(*  THE FUEL is the number of blocks the remaining range straddles.  An   *)
(*  iteration that does NOT exit filled its block to the boundary, and    *)
(*  [wi_blocks_step] is exactly the decrease that pays for it.            *)
(* ===================================================================== *)
Section WriteiLoop.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}.

  (* the CALLER's buffer tier -- see this function's spec for why it is not
     [KT1].  A KtierLe HYPOTHESIS in the section beats [ktier_le_refl] at
     instance search, so every OTHER leaf in this file has to name its own
     datum tier out loud (the blanket [(ktd := KT1)] below). *)
  Context {ktb : ktier}.
  Context `{!KtierLe ktb KT1}.
  Local Ltac reg_neq := vm_compute; discriminate.

  (* peel a chain of [<[Regidx k := v]>]s down to the fact that names the
     register -- ProofCopyin's [lkp], which is what keeps the per-step
     bookkeeping to one line *)
  Local Ltac lkp :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | rgne
      | match goal with |- context [ ?M !!! _ ] => is_var M; progress unfold M end ];
    repeat rewrite add_vec_zero_l;
    first [ reflexivity | assumption ].

  Local Lemma wi_loop `{GEN : GenId} `{CID0 : CpuId} 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (γfs : fs_names) (γi : gname) (bn : bio_names) (γ : log_names)
      (γf γa : gname)
      (cov : gset Z) (logstart inodestart : Z) (nib : nat) (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn dn0 : dinode)
      (user : bool) (off n : nat) (src_bytes : nat -> bv 8)
      (V : pprivate) (ncount : nat) (Sb : gset Z) (usv : mword 64)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac) (A : bm_alloc)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) :
    (K_writei <= K)%nat ->
    log_geom_ok cov logstart ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    bv_unsigned (di_type dn) <> 0 ->
    (* §19.6 Part 1: iupdate's type-stability premise, travelling. *)
    di_type_stable dn dn0 ->
    di_nlink_stable dn dn0 ->
    bv_unsigned (di_size dn) < 2 ^ 31 ->
    (Z.of_nat off < 2 ^ 31) ->
    (Z.of_nat n < 2 ^ 31) ->
    (off + n <= MAXFILE * BSIZE)%nat ->
    eq_vec usv zero_reg = negb user ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    forall (W tot : nat) (bmI : blkmap) (dataI : nat -> list (bv 8))
           (wroteI : nat -> bv 8) (PI : uptd) (nI : nat) (SI : gset Z)
           (M : regfile),
    (tot < n)%nat ->
    blkmap_wf cov logstart bmI ->
    blk_holes_zero bmI dataI ->
    (* [InodeInv.inode_sized], carried as a PRESERVATION: writei touches only
       the blocks its range straddles, so the fact about the untouched ones
       is the caller's and travels through unchanged.  Re-established at each
       deposit ([wi_sized_bmap]) and each block update ([wi_splice_len]). *)
    (inode_sized data -> inode_sized dataI) ->
    (* COVERAGE, in two halves.  The first is the caller's premise carried
       across every bmap call by [bm_covers_keep]; the SECOND is the loop's
       own invariant -- every block below the byte offset reached so far has
       been allocated, because bmap runs before [tot] advances over its
       chunk.  Together they give coverage at [max(size, off + tot)], which
       is the size writei installs. *)
    bm_covers bmI (bv_unsigned (di_size dn)) ->
    bm_covers bmI (Z.of_nat (off + tot)) ->
    (forall k : nat,
       file_byte dataI k
       = if decide ((off <= k)%nat /\ (k < off + tot)%nat)
         then wroteI (k - off)%nat else file_byte data k) ->
    (user = false -> forall i : nat, (i < tot)%nat -> wroteI i = src_bytes i) ->
    uptd_ext (pv_upt V) PI ->
    (wi_blocks (off + tot) (n - tot) <= W)%nat ->
    (* THE LEDGER INVARIANT (WriteiBudget section 10).  What used to be two
       raw inequalities in 6-per-block arithmetic is now the two clauses of
       the [bm_pot] accounting: [wi_inv_bud] is what the REST of the loop
       can still afford, [wi_inv_spent] is what has been spent so far and is
       what the public spend-at-most postcondition is read off at exit.  The
       unpaid bitmap block rides inside both as one unit of potential, which
       is why neither clause needs a "has the bitmap been paid yet" case
       split -- see WriteiBudget's section-10 header. *)
    wi_inv_bud (ba_bms A) W nI SI ->
    (nI <= ncount)%nat ->
    wi_inv_spent (ba_bms A) ncount nI (wi_blocks off n) W SI ->
    (W <= wi_blocks off n)%nat ->
    (* the op's logged set only grows: the caller's entry set is still in it *)
    Sb ⊆ SI ->
    (* THE SINGLE-BLOCK SHAPE.  Not an invariant of the multi-block loop and
       deliberately not one: it is re-established at the back edge by
       REFUTING it, since [wi_blocks off n = 1] pins the fuel at one. *)
    wi16_fresh off n tot ncount nI bm bmI Sb SI ->
    wi_sp m M ->
    M !!! Regidx Rs5 = ip ->
    M !!! Regidx Rs7 = usv ->
    M !!! Regidx Rs4 = pa_add (m !!! Regidx Ra2 : mword 64) tot ->
    M !!! Regidx Rs2 = (mword_of_int (Z.of_nat (off + tot)) : mword 64) ->
    M !!! Regidx Rs6 = (mword_of_int (Z.of_nat n) : mword 64) ->
    M !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64) ->
    M !!! Regidx Rs9 = (mword_of_int 1024 : mword 64) ->
    M !!! Regidx Rs8 = (mword_of_int (-1) : mword 64) ->
    printk_gen_contract (kt := KT1) (ba_pr A) γu γd ->
    (* THE ORDER PREMISE.  Every callee this iteration reaches that carries
       one wants its own rank: bread and brelse want "bcache" (4,
       SpecBread.v / SpecBrelse.v), log_write wants "log" (3,
       SpecLogWrite.v) -- the lowest of the three, so it is the one premise
       stated here, and [locks_below_mono] widens it to "bcache" at the
       bread/brelse call sites.  [lks] is unchanged across the iteration
       (every one of those calls is push/pop-BALANCED and returns the same
       [lks] it was given), so the very same [Hbelow] is what the back-edge
       call to [IH] needs too -- nothing about it is loop-varying.  Mirrors
       SpecBfree.v's; [SpecWritei.v]'s [wp_writei_gen_body] /
       [wp_writei_sconf_body] now carry the same premise, threaded down to
       here from [wp_writei_gen]'s call to [wi_loop] (WriteiMain section). *)
    locks_below lks "log" ->
    sie_cap_gpr KT1 M (K - 14)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (WI + 0x82) : mword 64) -∗
    (* forwarded to bmap, and through it to balloc's out-of-blocks arm; both
       PERSISTENT, so neither is returned *)
    kernel_data -∗
    printk_env (ba_pr A) γu γd -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    kalloc_env γa None -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    wi_fr13 m -∗
    i_dev ip ↦₄{dqd} dev -∗
    i_inum ip ↦₄{dqn} inum -∗
    inode_meta ip dn -∗
    inode_map γfs ip bmI -∗
    inode_blocks γfs bmI dataI -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bm_alloc_res γfs cov logstart A -∗
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn0 -∗
    (if user
     then proc_priv_core (proc_addr j) pidv (upd_upt V PI)
     else ([∗ list] i ∈ seq 0 n,
             pa_add (m !!! Regidx Ra2 : mword 64) i ↦ₘ[ktb] (src_bytes i)) ∗
          p_pid (proc_addr j) ↦₄{dq} pidv) -∗
    bslots bn 3 -∗
    log_opS γ nI SI -∗
    wi_cont (ktb := ktb) (CID0 := CID0) γfs γi bn γ γf cov logstart inodestart nib dev ip inum
            bm data dn dn0 user off n src_bytes V ncount Sb
            pidv dq dqd dqn dqs A j
            m K eb b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hgeom Hist Hicov Hilog Hnib Hdtnz Hstab Hnlk Hszdn Hofflt Hnlt Hrng Husv Hj Hgl.
    pose proof HK as HK'. 
    change (2 ^ 31)%Z with 2147483648%Z in Hszdn, Hofflt, Hnlt.
    assert (Hgeom0 : log_geom_ok cov logstart) by exact Hgeom.
    destruct Hgeom as [Hcovok Hlogsub].
    pose proof Hrng as Hrng2. rewrite wi_maxfile_bsize_nat in Hrng2.
    intro W. revert CID0.
    induction W as [| W IH];
      intros CID0 tot bmI dataI wroteI PI nI SI M
             Htotlt HwfI HhzI HsizedI HcovSI HcovTI HrangeI HkerI HextI
             HW1 HW2 HW3 HW4 HW5 HWsb Hfresh
             Hsp Hs5 Hs7 Hs4 Hs2 Hs6 Hs3 Hs9 Hs8 Hprkc Hbelow;
      [ exfalso; pose proof (wi_blocks_pos (off + tot) (n - tot) ltac:(lia)); lia |].
    remember ((off + tot) `div` BSIZE)%nat as fbn eqn:Hfbne.
    remember ((off + tot) `mod` BSIZE)%nat as o eqn:Hoe.
    assert (Holt : (o < BSIZE)%nat) by (rewrite Hoe; apply wi_mod_lt).
    assert (Hdm : (fbn * BSIZE + o = off + tot)%nat).
    { rewrite Hfbne Hoe. pose proof (wi_divmod (off + tot)). lia. }
    assert (Hfbnlt : (fbn < MAXFILE)%nat) by (rewrite Hfbne; apply wi_fbn_lt; lia).
    pose proof Hfbnlt as Hfbn268. rewrite wi_maxfile_val in Hfbn268.
    assert (Hbsz : BSIZE = 1024%nat) by exact wi_bsize_val.
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hkdata #Hprkenv #Hbio #Hlctx #Hkenv
              #Hprocs
              #Hdevi #Hdgeom #Hdlock Hframe Hidev Hinum
              Hmeta Hmap Hblocks Hsb Hba #Hireg Hdn Hsrc Hsl Hop Hcont".
    iPoseProof (printk_env_panic with "Hprkenv") as "#Hpanenv".
    iDestruct (CpuOwn.cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    iPoseProof (wri_82 with "Htext") as "Hi82".
    iPoseProof (wri_86 with "Htext") as "Hi86".
    iPoseProof (wri_88 with "Htext") as "Hi88".
    iPoseProof (wri_8c with "Htext") as "Hi8c".
    iPoseProof (wri_8e with "Htext") as "Hi8e".
    (* ===== +0x82 srliw a1,s2,0xa : a1 := off / BSIZE ===== *)
    assert (Hsrlv : sign_extend' 64
                      (shift_bits_right (subrange_vec_dec (rget M Rs2) 31 0 : mword 32)
                         (mword_of_int 10 : mword 5))
                    = (mword_of_int (Z.of_nat fbn) : mword 64)).
    { rgne. rewrite Hs2.
      rewrite (wi_srliw10 (Z.of_nat (off + tot)) ltac:(lia) ltac:(lia)).
      rewrite Hfbne wi_div_z. reflexivity. }
    iApply (wp_srliw_s_sconf (mword_of_int (WI + 0x82)) Ra1 Rs2
              (mword_of_int 10 : mword 5) (mword_of_int (Z.of_nat fbn) : mword 64)
              M (K - 14)%nat b ltac:(nz) ltac:(rdok) Hsrlv with "Hcg Hpc Hi82").
    iIntros (CIDa1 Hqa1) "Hcg Hpc".
    set (A1 := <[Regidx Ra1 :=
                 regval_into_reg (mword_of_int (Z.of_nat fbn) : mword 64)]> M).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x82) : mword 64) 4
                  = mword_of_int (WI + 0x86)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x86 c.mv a0,s5 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (WI + 0x86)) Ra0 Rs5
              A1 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi86").
    iIntros (CIDa2 Hqa2) "Hcg Hpc".
    set (A2 := <[Regidx Ra0 :=
                 regval_into_reg (add_vec (zero_reg : mword 64) (rget A1 Rs5))]> A1).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x86) : mword 64) 2
                  = mword_of_int (WI + 0x88)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x88 jal ra,bmap ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (WI + 0x88)) Rra
              (mword_of_int 2095140 : mword 21) A2 (K - 14)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi88").
    iIntros (CIDa3 Hqa3) "Hcg Hpc".
    set (A3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (WI + 0x88) : mword 64) 4)]> A2).
    assert (Htgtbm : add_vec (mword_of_int (WI + 0x88) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095140 : mword 21))
                     = mword_of_int KernelSyms.bmap) by pcw.
    iEval (rewrite Htgtbm) in "Hpc".
    assert (HA3ra : A3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (WI + 0x88) : mword 64) 4)
      by (rewrite /A3; apply upd_eq).
    assert (HA3a0 : A3 !!! Regidx Ra0 = ip) by lkp.
    assert (HA3a1v : A3 !!! Regidx Ra1 = (mword_of_int (Z.of_nat fbn) : mword 64))
      by lkp.
    assert (HA3a1 : A3 !!! Regidx Ra1
                    = sign_extend' 64 (mword_of_int (Z.of_nat fbn) : mword 32)).
    { rewrite HA3a1v. symmetry. apply wi_sext32; lia. }
    assert (HA3sp : wi_sp m A3) by (rewrite /wi_sp; lkp).
    assert (HA3s5 : A3 !!! Regidx Rs5 = ip) by lkp.
    assert (HA3s7 : A3 !!! Regidx Rs7 = usv) by lkp.
    assert (HA3s4 : A3 !!! Regidx Rs4
                    = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp.
    assert (HA3s2 : A3 !!! Regidx Rs2
                    = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp.
    assert (HA3s6 : A3 !!! Regidx Rs6 = (mword_of_int (Z.of_nat n) : mword 64))
      by lkp.
    assert (HA3s3 : A3 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by lkp.
    assert (HA3s9 : A3 !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)) by lkp.
    assert (HA3s8 : A3 !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)) by lkp.
    iDestruct (cpu_own_transport CID0 CIDa3 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (IntrDefs.trap_csrs_ext_transport CID0 CIDa3 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (IntrDefs.cpu_claim_ext_transport CID0 CIDa3 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CIDa3) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbm : (K_bmap <= K - 14)%nat) by (lia).
    (* the allocation bundle opens for exactly this call and closes again
       right after: [bm_bitmap]'s index is [ba_used A] throughout, so the
       loop invariant never mentions the bitmap's current set. *)
    iDestruct "Hba" as "(%Hgok & Hszc & Hbmsc & Hbmg)".
    iDestruct "Hbmg" as (uIn) "[%HuIn Hbmres]".
    (* THE CREDIT writei PRESENTS: "this op has already logged the bitmap
       block".  It is a DECIDABLE READ of the loop's own set, not a case
       split -- [wi_bmap_need_ok] discharges bmap's reservation at either
       value of it, out of the one invariant clause. *)
    (* BORROW the pid share for bmap ([wi_src_pid], both arms at once); it
       closes again the instant bmap returns, because the failure arm below
       exits through wi_size, which wants the bracket whole. *)
    iDestruct (wi_src_pid γf j pidv dq user (upd_upt V PI)
                 (m !!! Regidx Ra2 : mword 64) n src_bytes with "Hsrc")
      as "[Hppid Hsrcback]".
    iApply (BM.wp_bmap_gen γs j γl γu γd γk pd pav pu bn γ γfs
              cov logstart (ba_bms A) (ba_size A) dev uIn (ba_pr A)
              ip bmI dataI fbn nI (bool_decide (ba_bms A ∈ SI)) SI
              pidv (wi_q user dq) dqd (ba_dqb A) (ba_dqs A)
              A3 (K - 14)%nat eb b lks
              HKbm
              (wi_bmap_need_ok (ba_bms A) (S W) nI SI (bmap_ind fbn)
                 ltac:(lia) HW2)
              Hgeom0 Hgok Hprkc
              ltac:(intros Hc; exact (proj1 (bool_decide_eq_true _) Hc))
              Hfbnlt HwfI Hj Hgl HA3a0 HA3a1
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hkdata Hprkenv Hpanenv Hbio Hlctx Hidev Hmap
                    Hblocks Hppid
                    Hszc Hbmsc Hbmres
                    Hprocs Hdevi Hdgeom Hdlock Hsl Hop").
    all: try lkbelow.
    iIntros (CIDa4 Hqa4 mB bm2 nB data2 uMid Sb2)
      "%Hcs1 %HuMid %Hwf2 %Hagr2 %Hnoun2 %Harm2 Hcg Hcnt Hextc Hextm Hpc Hppid
       Hszc Hbmsc Hbmres Hidev Hmap %Hdep2 Hblocks Hsl %Hbud2 Hop".
    (* the pid borrow closes *)
    iDestruct ("Hsrcback" with "Hppid") as "Hsrc".
    (* re-close the bundle at the SAME index -- [ba_used A ⊆ uIn ⊆ uMid] *)
    iAssert (bm_alloc_res γfs cov logstart A) with "[Hszc Hbmsc Hbmres]" as "Hba".
    { rewrite /bm_alloc_res. iSplitR; [iPureIntro; exact Hgok|].
      iFrame "Hszc Hbmsc".
      iApply (bm_bitmap_intro γfs cov logstart (ba_bms A) (ba_size A)
                (ba_used A) uMid (bm_used_trans _ _ _ HuIn HuMid) with "Hbmres"). }
    (* the loop still has a unit for its own [log_write]: the invariant
       reserved two per remaining block plus the bitmap's potential, and no
       arm of bmap costs more than two plus that potential
       ([wi_bmap_cost_le]) *)
    destruct nB as [| uX];
      [ exfalso;
        pose proof (wi_bmap_cost_le (ba_bms A) SI
                      (bmap_alloced bmI bm2 fbn) (bmap_ind fbn));
        unfold wi_inv_bud in HW2;
        destruct Hbud2 as (Hbd1 & Hbd2 & _); lia
      |].
    (* THE LEDGER, unpacked once: the spend, the two set bounds, and the two
       memberships that ARE the absorption (SpecBmap's clauses (a)-(d)). *)
    destruct Hbud2 as (Hbc1 & Hbc2 & Hbc3 & Hbc4 & Hbc5 & Hbc6 & Hbc7).
    assert (HSuXnc : (S uX <= ncount)%nat) by lia.
    assert (HsbSb2 : Sb ⊆ Sb2) by (etransitivity; [exact HWsb | exact Hbc3]).
    (* THE ITERATION'S FIRST HALF against the accounting.  Either bmap
       allocated -- and then it logged the bitmap block, so the potential is
       discharged in the same breath that spends it ([wi_step_alloc]) -- or it
       did not, and spent nothing at all ([wi_step_noalloc]).  Stated at the
       count bmap left behind, which is what the two loop EXITS below hand on;
       an iteration that CONTINUES re-derives it past its own log_write. *)
    assert (Hinv2 : wi_inv_bud (ba_bms A) W (S uX) Sb2
                    /\ wi_inv_spent (ba_bms A) ncount (S uX)
                         (wi_blocks off n) W Sb2).
    (* NOTE: [destruct ... eqn:] SUBSTITUTES the scrutinee, so [Hbc1]/[Hbc5]
       carry the literal [true]/[false] from here on -- the arm facts must be
       named at the literal, not at [bmap_alloced bmI bm2 fbn]. *)
    (* the step lemmas conclude at [S W - 1], which unification does NOT
       reduce to [W] on its own *)
    { destruct (bmap_alloced bmI bm2 fbn) eqn:Hal2.
      - assert (Hlo2 : (nI <= S uX + 2 + bm_pot (ba_bms A) SI)%nat).
        { pose proof (wi_bmap_cost_le (ba_bms A) SI true (bmap_ind fbn)). lia. }
        pose proof (wi_step_alloc (ba_bms A) ncount nI (S uX) (wi_blocks off n)
                      (S W) SI Sb2 ltac:(lia) HW5 HW2 HW4 Hbc3 (Hbc5 eq_refl)
                      Hlo2 Hbc2) as Hst2.
        replace (S W - 1)%nat with W in Hst2 by lia. exact Hst2.
      - assert (Hlo2 : (nI <= S uX + 1)%nat).
        { assert (Hz2 : bmap_cost (bool_decide (ba_bms A ∈ SI)) false
                          (bmap_ind fbn) = 0%nat) by reflexivity. lia. }
        pose proof (wi_step_noalloc (ba_bms A) ncount nI (S uX) (wi_blocks off n)
                      (S W) SI Sb2 ltac:(lia) HW5 HW2 HW4 Hbc3 Hlo2 Hbc2) as Hst2.
        replace (S W - 1)%nat with W in Hst2 by lia. exact Hst2. }
    assert (Hpc8c : ret_pc (A3 !!! Regidx Rra : mword 64)
                    = mword_of_int (WI + 0x8c)) by (rewrite HA3ra; pcw).
    iEval (rewrite Hpc8c) in "Hpc".
    pose proof Hcs1 as Hcs1c.
    assert (HmBsp : wi_sp m mB).
    { rewrite /wi_sp
        (callee_saved_lookup Hcs1c csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HA3sp. }
    assert (HmBs5 : mB !!! Regidx Rs5 = ip)
      by (rewrite (callee_saved_lookup Hcs1c Rs5 ltac:(vm_compute; reflexivity));
          exact HA3s5).
    assert (HmBs7 : mB !!! Regidx Rs7 = usv)
      by (rewrite (callee_saved_lookup Hcs1c Rs7 ltac:(vm_compute; reflexivity));
          exact HA3s7).
    assert (HmBs4 : mB !!! Regidx Rs4 = pa_add (m !!! Regidx Ra2 : mword 64) tot)
      by (rewrite (callee_saved_lookup Hcs1c Rs4 ltac:(vm_compute; reflexivity));
          exact HA3s4).
    assert (HmBs2 : mB !!! Regidx Rs2
                    = (mword_of_int (Z.of_nat (off + tot)) : mword 64))
      by (rewrite (callee_saved_lookup Hcs1c Rs2 ltac:(vm_compute; reflexivity));
          exact HA3s2).
    assert (HmBs6 : mB !!! Regidx Rs6 = (mword_of_int (Z.of_nat n) : mword 64))
      by (rewrite (callee_saved_lookup Hcs1c Rs6 ltac:(vm_compute; reflexivity));
          exact HA3s6).
    assert (HmBs3 : mB !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite (callee_saved_lookup Hcs1c Rs3 ltac:(vm_compute; reflexivity));
          exact HA3s3).
    assert (HmBs9 : mB !!! Regidx Rs9 = (mword_of_int 1024 : mword 64))
      by (rewrite (callee_saved_lookup Hcs1c Rs9 ltac:(vm_compute; reflexivity));
          exact HA3s9).
    assert (HmBs8 : mB !!! Regidx Rs8 = (mword_of_int (-1) : mword 64))
      by (rewrite (callee_saved_lookup Hcs1c Rs8 ltac:(vm_compute; reflexivity));
          exact HA3s8).
    (* the two invariants, carried across bmap's deposit *)
    assert (Hhz2 : blk_holes_zero bm2 data2)
      by exact (wi_holes_bmap bmI bm2 dataI data2 fbn Hfbnlt Hagr2 Hnoun2 Hdep2 HhzI).
    (* ...and COVERAGE, both halves, by bmap's own "never un-allocates"
       clause -- which is exactly [bm_covers_keep]'s hypothesis *)
    assert (HcovS2 : bm_covers bm2 (bv_unsigned (di_size dn)))
      by exact (bm_covers_keep bmI bm2 _ Hnoun2 HcovSI).
    assert (HcovT2 : bm_covers bm2 (Z.of_nat (off + tot)))
      by exact (bm_covers_keep bmI bm2 _ Hnoun2 HcovTI).
    assert (Hrange2 : forall k : nat,
              file_byte data2 k
              = if decide ((off <= k)%nat /\ (k < off + tot)%nat)
                then wroteI (k - off)%nat else file_byte data k).
    { intro k. rewrite (wi_bmap_data bmI dataI data2 fbn HhzI Hfbnlt Hdep2 k).
      exact (HrangeI k). }
    (* ===== +0x8c c.mv a1,a0 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (WI + 0x8c)) Ra1 Ra0
              mB (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8c").
    iIntros (CIDa5 Hqa5) "Hcg Hpc".
    set (B1 := <[Regidx Ra1 :=
                 regval_into_reg (add_vec (zero_reg : mword 64) (rget mB Ra0))]> mB).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x8c) : mword 64) 2
                  = mword_of_int (WI + 0x8e)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HB1a0 : B1 !!! Regidx Ra0 = (mB !!! Regidx Ra0 : mword 64)) by lkp.
    assert (HB1sp : wi_sp m B1) by (rewrite /wi_sp; lkp).
    assert (HB1s5 : B1 !!! Regidx Rs5 = ip) by lkp.
    assert (HB1s7 : B1 !!! Regidx Rs7 = usv) by lkp.
    assert (HB1s4 : B1 !!! Regidx Rs4
                    = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp.
    assert (HB1s2 : B1 !!! Regidx Rs2
                    = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp.
    assert (HB1s6 : B1 !!! Regidx Rs6 = (mword_of_int (Z.of_nat n) : mword 64))
      by lkp.
    assert (HB1s3 : B1 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by lkp.
    assert (HB1s9 : B1 !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)) by lkp.
    assert (HB1s8 : B1 !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)) by lkp.
    destruct Harm2 as [[Ha0z Hgetz] | [Ha0v Hgetnz]].
    - (* ============ bmap FAILED: exit the loop at +0xbc ============ *)
      assert (Hbeqz : eq_vec (B1 !!! Regidx Ra0) zero_reg = true).
      { rewrite HB1a0 Ha0z. exact bc_moi_iszero. }
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (WI + 0x8e))
                (mword_of_int 23 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                B1 (K - 14)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; exact Hbeqz) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi8e").
      iApply bi.later_intro. iIntros (CIDa6 Hqa6) "Hcg Hpc".
      iClear "Hi82 Hi86 Hi88 Hi8c Hi8e".
      assert (Htgtbc : add_vec (mword_of_int (WI + 0x8e) : mword 64)
                (sign_extend' 64 (sign_extend' 13
                   (concat_vec (mword_of_int 23 : mword 8) ('b"0"))))
              = mword_of_int (WI + 0xbc)) by pcw.
      iEval (rewrite Htgtbc) in "Hpc".
      iDestruct (cpu_own_transport CIDa4 CIDa6 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (IntrDefs.trap_csrs_ext_transport CIDa4 CIDa6 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (IntrDefs.cpu_claim_ext_transport CIDa4 CIDa6 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
      iApply (wi_size (CID0 := CIDa6) γs j γl γu γd γk pd pav pu γfs γi bn γ γf
                cov logstart inodestart nib dev ip inum bm bm2 data data2 dn dn0
                user off n tot src_bytes wroteI 0%nat wroteI V PI ncount uX
                Sb Sb2
                pidv dq dqd dqn dqs A m B1 K eb b lks
                HK Hgeom0 Hist Hicov Hilog Hnib Hdtnz Hstab Hnlk Hwf2 Hhz2 HcovS2 HcovT2
                Hszdn ltac:(lia)
                ltac:(lia)
                ltac:(intros Hs; exact (wi_sized_bmap bmI dataI data2 fbn Hdep2
                                          (HsizedI Hs)))
                Hj Hgl HB1sp HB1s5 HB1s2 HB1s3 ltac:(lia) ltac:(intros; reflexivity)
                ltac:(intros; reflexivity)
                (wi_range_dist0 data data2 off tot wroteI wroteI Hrange2)
                HkerI ltac:(lia)
                ltac:(exact (proj1 (wi_inv_exit (ba_bms A) ncount (S uX) uX
                              (wi_blocks off n) W off n Sb2
                              ltac:(lia) eq_refl (proj2 Hinv2) HSuXnc
                              ltac:(lia) ltac:(lia))))
                ltac:(exact (proj2 (wi_inv_exit (ba_bms A) ncount (S uX) uX
                              (wi_blocks off n) W off n Sb2
                              ltac:(lia) eq_refl (proj2 Hinv2) HSuXnc
                              ltac:(lia) ltac:(lia))))
                HSuXnc HsbSb2
                (* THE RECEIPT ON THE bmap-OUT-OF-BLOCKS BREAK.  bmap failed
                   on the FIRST iteration ([wi16_fresh]), so [tot] is still
                   the entry 0: the two MEMBERSHIPS are vacuous (nothing of
                   writei's own was logged -- its [log_write] is past the
                   break), and the SPEND is bmap's own arm-wise bound
                   [Hbc1] with the target block's term simply UNSPENT.
                   That the same expression still bounds it is the whole
                   point of [SpecWritei.wi16_spend_any]. *)
                ltac:(rewrite /wi16_pre; intros Hone;
                      destruct (Hfresh Hone) as (Ht0 & Hbm0 & Hn0 & HS0);
                      assert (Hfb0 : (off `div` BSIZE)%nat = fbn)
                        by (rewrite Hfbne Ht0 Nat.add_0_r; reflexivity);
                      cbv zeta; rewrite Hfb0 -Hbm0 -HS0; split_and!;
                      [ lia | left; exact Ht0 | intros Hpos; exfalso; lia ])
                HextI Hbelow
                with "Hcg Hcnt Hextc Hextm Htext Hkdata Hpc Hpanenv Hbio Hlctx Hprocs Hdevi
                      Hdgeom Hdlock Hframe Hidev Hinum Hmeta
                      Hmap Hblocks Hsb Hba Hireg Hdn Hsrc Hsl Hop [Hcont]").
      iApply (wp_next_shift (b := true) (CIDa := CIDa3) (CIDb := CIDa6) ltac:(wp_next_chain)
                with "Hcont").
    - (* ============ bmap found a block: bread it ============ *)
      assert (Hbnzz : bv_unsigned (blkmap_get bm2 fbn) <> 0) by exact Hgetnz.
      destruct (blkmap_wf_get_cov cov logstart bm2 fbn Hwf2 Hfbnlt Hbnzz)
        as [Hbcov Hblog].
      destruct (Hcovok _ Hbcov) as [Hbpos Hblt].
      change (2 ^ 31)%Z with 2147483648%Z in Hblt.
      assert (Hubno : uint (blkmap_get bm2 fbn : mword 32)
                      = bv_unsigned (blkmap_get bm2 fbn)) by apply bb_uint32.
      assert (Hbcov' : uint (blkmap_get bm2 fbn : mword 32)
                       ∈ bv_cov (fs_view γfs γd dev cov))
        by (rewrite Hubno; exact Hbcov).
      assert (Hblt' : (uint (blkmap_get bm2 fbn : mword 32) < 2147483648)%Z)
        by (rewrite Hubno; exact Hblt).
      assert (Hbcovlw : uint (blkmap_get bm2 fbn : mword 32) ∈ cov)
        by (rewrite Hubno; exact Hbcov).
      assert (Hbloglw : ~ (uint (blkmap_get bm2 fbn : mword 32)
                           ∈ log_region_set logstart))
        by (rewrite Hubno; exact Hblog).
      assert (Hbeqz : eq_vec (B1 !!! Regidx Ra0) zero_reg = false).
      { rewrite HB1a0 Ha0v. apply wi_sext_nonzero; [exact Hbnzz | exact Hblt]. }
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (WI + 0x8e))
                (mword_of_int 23 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                B1 (K - 14)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; exact Hbeqz) with "Hcg Hpc Hi8e").
      iIntros (CIDa6 Hqa6) "Hcg Hpc".
      iClear "Hi82 Hi86 Hi88 Hi8c Hi8e".
      assert (Hpp : add_vec_int (mword_of_int (WI + 0x8e) : mword 64) 2
                    = mword_of_int (WI + 0x90)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x90 lw a0,0(s5) : a0 := ip->dev ===== *)
      iPoseProof (wri_90 with "Htext") as "Hi90".
      iPoseProof (wri_94 with "Htext") as "Hi94".
      iPoseProof (wri_98 with "Htext") as "Hi98".
      iPoseProof (wri_9a with "Htext") as "Hi9a".
      iPoseProof (wri_9e with "Htext") as "Hi9e".
      iPoseProof (wri_a2 with "Htext") as "Hia2".
      iPoseProof (wri_a6 with "Htext") as "Hia6".
      iPoseProof (wri_a8 with "Htext") as "Hia8".
      iPoseProof (wri_ac with "Htext") as "Hiac".
      iPoseProof (wri_ae with "Htext") as "Hiae".
      assert (Hdadr : add_vec (rget B1 Rs5) (sign_extend' 64 (mword_of_int 0 : mword 12))
                      = i_dev ip) by (rgne; rewrite HB1s5; reflexivity).
      iEval (rewrite -Hdadr) in "Hidev".
      iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (WI + 0x90)) Ra0 Rs5
                (mword_of_int 0 : mword 12) B1 (K - 14)%nat dev b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi90 Hidev").
      iIntros (CIDa7 Hqa7) "Hcg Hpc Hidev".
      iEval (rewrite Hdadr) in "Hidev".
      set (B2 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 dev)]> B1).
      assert (Hpp : add_vec_int (mword_of_int (WI + 0x90) : mword 64) 4
                    = mword_of_int (WI + 0x94)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x94 jal ra,bread ===== *)
      iApply (wp_jal_s_sconf (mword_of_int (WI + 0x94)) Rra
                (mword_of_int 2094088 : mword 21) B2 (K - 14)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi94").
      iIntros (CIDa8 Hqa8) "Hcg Hpc".
      set (B3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (WI + 0x94) : mword 64) 4)]> B2).
      assert (Htgtbr : add_vec (mword_of_int (WI + 0x94) : mword 64)
                         (sign_extend' 64 (mword_of_int 2094088 : mword 21))
                       = mword_of_int KernelSyms.bread) by pcw.
      iEval (rewrite Htgtbr) in "Hpc".
      assert (HB3ra : B3 !!! Regidx Rra
                      = add_vec_int (mword_of_int (WI + 0x94) : mword 64) 4)
        by (rewrite /B3; apply upd_eq).
      assert (HB3a0 : B3 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64)) by lkp.
      assert (HB3a1 : B3 !!! Regidx Ra1
                      = (sign_extend' 64 (blkmap_get bm2 fbn : mword 32) : mword 64)).
      { rewrite (_ : B3 !!! Regidx Ra1 = (mB !!! Regidx Ra0 : mword 64));
          [exact Ha0v | lkp]. }
      assert (HB3sp : wi_sp m B3) by (rewrite /wi_sp; lkp).
      assert (HB3s5 : B3 !!! Regidx Rs5 = ip) by lkp.
      assert (HB3s7 : B3 !!! Regidx Rs7 = usv) by lkp.
      assert (HB3s4 : B3 !!! Regidx Rs4
                      = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp.
      assert (HB3s2 : B3 !!! Regidx Rs2
                      = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp.
      assert (HB3s6 : B3 !!! Regidx Rs6 = (mword_of_int (Z.of_nat n) : mword 64))
        by lkp.
      assert (HB3s3 : B3 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
        by lkp.
      assert (HB3s9 : B3 !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)) by lkp.
      assert (HB3s8 : B3 !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)) by lkp.
      iDestruct (cpu_own_transport CIDa4 CIDa8 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (IntrDefs.trap_csrs_ext_transport CIDa4 CIDa8 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (IntrDefs.cpu_claim_ext_transport CIDa4 CIDa8 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
      assert (HKbr : (K_bread <= K - 14)%nat) by (lia).
      iDestruct (wi_slots_split bn 2 1 with "Hsl") as "[Hsl2 Hsl1]".
      (* BORROW the pid share for bread, and close it again at once: the
         body below hands the source bracket WHOLE to either_copyin. *)
      iDestruct (wi_src_pid γf j pidv dq user (upd_upt V PI)
                   (m !!! Regidx Ra2 : mword 64) n src_bytes with "Hsrc")
        as "[Hppid Hsrcback]".
      iApply (BR.wp_bread_sconf γs j γl γu γd γk pd pav pu bn
                (fs_view γfs γd dev cov) pidv dev (blkmap_get bm2 fbn)
                (wi_q user dq)
                B3 (K - 14)%nat eb b lks
                HKbr Hblt' eq_refl Hbcov'
                eq_refl Hj Hgl HB3a0 HB3a1
                ltac:(lkbelow)
                with "Hcg Hcnt Hextc Hextm Htext Hkdata Hpc Hpanenv Hbio Hppid Hprocs Hdevi Hdgeom Hdlock Hsl1").
      all: try lkbelow.
      iIntros (CIDa9 Hqa9 mBr kkb bsB bsdB dB)
        "%Hfacts Hcg Hcnt Hextc Hextm Hpc Hppid Hheld".
      iDestruct ("Hsrcback" with "Hppid") as "Hsrc".
      destruct Hfacts as [Hcs2 HmBra0].
      assert (Hpc98 : ret_pc (B3 !!! Regidx Rra : mword 64)
                      = mword_of_int (WI + 0x98)) by (rewrite HB3ra; pcw).
      iEval (rewrite Hpc98) in "Hpc".
      pose proof Hcs2 as Hcs2c.
      assert (HmRsp : wi_sp m mBr).
      { rewrite /wi_sp
          (callee_saved_lookup Hcs2c csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HB3sp. }
      assert (HmRs5 : mBr !!! Regidx Rs5 = ip)
        by (rewrite (callee_saved_lookup Hcs2c Rs5 ltac:(vm_compute; reflexivity));
            exact HB3s5).
      assert (HmRs7 : mBr !!! Regidx Rs7 = usv)
        by (rewrite (callee_saved_lookup Hcs2c Rs7 ltac:(vm_compute; reflexivity));
            exact HB3s7).
      assert (HmRs4 : mBr !!! Regidx Rs4
                      = pa_add (m !!! Regidx Ra2 : mword 64) tot)
        by (rewrite (callee_saved_lookup Hcs2c Rs4 ltac:(vm_compute; reflexivity));
            exact HB3s4).
      assert (HmRs2 : mBr !!! Regidx Rs2
                      = (mword_of_int (Z.of_nat (off + tot)) : mword 64))
        by (rewrite (callee_saved_lookup Hcs2c Rs2 ltac:(vm_compute; reflexivity));
            exact HB3s2).
      assert (HmRs6 : mBr !!! Regidx Rs6 = (mword_of_int (Z.of_nat n) : mword 64))
        by (rewrite (callee_saved_lookup Hcs2c Rs6 ltac:(vm_compute; reflexivity));
            exact HB3s6).
      assert (HmRs3 : mBr !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
        by (rewrite (callee_saved_lookup Hcs2c Rs3 ltac:(vm_compute; reflexivity));
            exact HB3s3).
      assert (HmRs9 : mBr !!! Regidx Rs9 = (mword_of_int 1024 : mword 64))
        by (rewrite (callee_saved_lookup Hcs2c Rs9 ltac:(vm_compute; reflexivity));
            exact HB3s9).
      assert (HmRs8 : mBr !!! Regidx Rs8 = (mword_of_int (-1) : mword 64))
        by (rewrite (callee_saved_lookup Hcs2c Rs8 ltac:(vm_compute; reflexivity));
            exact HB3s8).
      (* THE COUPLING: the buffer's bytes ARE the block's logical content *)
      iDestruct (inode_blocks_acc γfs bm2 data2 fbn Hfbnlt Hbnzz with "Hblocks")
        as "[[Hfsb1 Htok1] Hblback]".
      iEval (rewrite -Hubno) in "Hfsb1".
      iEval (rewrite /bio_locked) in "Hheld".
      iDestruct (wi_held_k with "Hheld") as %Hkklt.
      iDestruct (wi_held_content with "Hfsb1 Hheld") as %Hbs0eq.
      subst bsB.
      iDestruct (wi_held_swap with "Hheld") as "[Hbuf Hheldback]".
      (* ===== +0x98 c.mv s1,a0 : s1 := bp ===== *)
      iApply (wp_cmv_s_sconf (mword_of_int (WI + 0x98)) Rs1 Ra0
                mBr (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi98").
      iIntros (CIDa10 Hqa10) "Hcg Hpc".
      set (E1 := <[Regidx Rs1 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (rget mBr Ra0))]> mBr).
      assert (HE1s1 : E1 !!! Regidx Rs1 = bnode kkb).
      { rewrite /E1 upd_eq. rgne. rewrite HmBra0. apply add_vec_zero_l. }
      assert (Hpp : add_vec_int (mword_of_int (WI + 0x98) : mword 64) 2
                    = mword_of_int (WI + 0x9a)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x9a andi a5,s2,1023 : a5 := off % BSIZE ===== *)
      assert (Handv : and_vec (rget E1 Rs2) (sign_extend' 64 (mword_of_int 1023 : mword 12))
                      = (mword_of_int (Z.of_nat o) : mword 64)).
      { rgne. rewrite (_ : E1 !!! Regidx Rs2
                           = (mword_of_int (Z.of_nat (off + tot)) : mword 64)); [| lkp].
        rewrite (wi_andi1023 (Z.of_nat (off + tot)) ltac:(lia) ltac:(lia)).
        rewrite Hoe wi_mod_z. reflexivity. }
      iApply (wp_andi_s_sconf (mword_of_int (WI + 0x9a)) Ra5 Rs2
                (mword_of_int 1023 : mword 12) (mword_of_int (Z.of_nat o) : mword 64)
                E1 (K - 14)%nat b ltac:(nz) ltac:(rdok) Handv with "Hcg Hpc Hi9a").
      iIntros (CIDa11 Hqa11) "Hcg Hpc".
      set (E2 := <[Regidx Ra5 := regval_into_reg
                    (mword_of_int (Z.of_nat o) : mword 64)]> E1).
      assert (Hpp : add_vec_int (mword_of_int (WI + 0x9a) : mword 64) 4
                    = mword_of_int (WI + 0x9e)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x9e subw a4,s9,a5 : a4 := BSIZE - off%BSIZE ===== *)
      assert (Hsubv1 : sign_extend' 64
                (sub_vec (subrange_vec_dec (rget E2 Rs9) 31 0 : mword 32)
                         (subrange_vec_dec (rget E2 Ra5) 31 0 : mword 32))
                = (mword_of_int (Z.of_nat (BSIZE - o)) : mword 64)).
      { rgne; rgne.
        rewrite (_ : E2 !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)); [| lkp].
        rewrite (_ : E2 !!! Regidx Ra5 = (mword_of_int (Z.of_nat o) : mword 64)); [| lkp].
        rewrite (wi_subw 1024 (Z.of_nat o) ltac:(lia) ltac:(lia) ltac:(lia)).
        rewrite Nat2Z.inj_sub; [| lia]. rewrite Hbsz. reflexivity. }
      iApply (wp_subw_s_sconf (mword_of_int (WI + 0x9e)) Ra4 Rs9 Ra5
                E2 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi9e").
      iIntros (CIDa12 Hqa12) "Hcg Hpc".
      set (E3 := <[Regidx Ra4 := regval_into_reg
                    (sign_extend' 64
                      (sub_vec (subrange_vec_dec (rget E2 Rs9) 31 0 : mword 32)
                               (subrange_vec_dec (rget E2 Ra5) 31 0 : mword 32)))]> E2).
      assert (HE3a4 : E3 !!! Regidx Ra4
                      = (mword_of_int (Z.of_nat (BSIZE - o)) : mword 64))
        by (rewrite /E3 upd_eq; exact Hsubv1).
      assert (Hpp : add_vec_int (mword_of_int (WI + 0x9e) : mword 64) 4
                    = mword_of_int (WI + 0xa2)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0xa2 subw a3,s6,s3 : a3 := n - tot ===== *)
      assert (Hsubv2 : sign_extend' 64
                (sub_vec (subrange_vec_dec (rget E3 Rs6) 31 0 : mword 32)
                         (subrange_vec_dec (rget E3 Rs3) 31 0 : mword 32))
                = (mword_of_int (Z.of_nat (n - tot)) : mword 64)).
      { rgne; rgne.
        rewrite (_ : E3 !!! Regidx Rs6 = (mword_of_int (Z.of_nat n) : mword 64)); [| lkp].
        rewrite (_ : E3 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64)); [| lkp].
        rewrite (wi_subw (Z.of_nat n) (Z.of_nat tot) ltac:(lia) ltac:(lia) ltac:(lia)).
        rewrite Nat2Z.inj_sub; [reflexivity | lia]. }
      iApply (wp_subw_s_sconf (mword_of_int (WI + 0xa2)) Ra3 Rs6 Rs3
                E3 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia2").
      iIntros (CIDa13 Hqa13) "Hcg Hpc".
      set (E4 := <[Regidx Ra3 := regval_into_reg
                    (sign_extend' 64
                      (sub_vec (subrange_vec_dec (rget E3 Rs6) 31 0 : mword 32)
                               (subrange_vec_dec (rget E3 Rs3) 31 0 : mword 32)))]> E3).
      assert (HE4a3 : E4 !!! Regidx Ra3
                      = (mword_of_int (Z.of_nat (n - tot)) : mword 64))
        by (rewrite /E4 upd_eq; exact Hsubv2).
      assert (HE4a4 : E4 !!! Regidx Ra4
                      = (mword_of_int (Z.of_nat (BSIZE - o)) : mword 64)) by lkp.
      assert (Hpp : add_vec_int (mword_of_int (WI + 0xa2) : mword 64) 4
                    = mword_of_int (WI + 0xa6)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0xa6 c.mv s10,a4 ===== *)
      iApply (wp_cmv_s_sconf (mword_of_int (WI + 0xa6)) Rs10 Ra4
                E4 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia6").
      iIntros (CIDa14 Hqa14) "Hcg Hpc".
      iClear "Hi90 Hi94 Hi98 Hi9a Hi9e Hia2 Hia6".
      set (E5 := <[Regidx Rs10 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (rget E4 Ra4))]> E4).
      assert (HE5s10 : E5 !!! Regidx Rs10
                       = (mword_of_int (Z.of_nat (BSIZE - o)) : mword 64)).
      { rewrite /E5 upd_eq. rgne. rewrite HE4a4. apply add_vec_zero_l. }
      assert (Hpp : add_vec_int (mword_of_int (WI + 0xa6) : mword 64) 2
                    = mword_of_int (WI + 0xa8)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      iDestruct (cpu_own_transport CIDa9 CIDa14 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (IntrDefs.trap_csrs_ext_transport CIDa9 CIDa14 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (IntrDefs.cpu_claim_ext_transport CIDa9 CIDa14 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (wp_next_shift (b := true) (CIDa := CIDa3) (CIDb := CIDa14)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".

      (* ================================================================ *)
      (*  THE +0x4c BODY.  Everything linear is BAKED IN -- the two arms   *)
      (*  of the [bgeu a3,a4] below are alternatives, so one copy serves    *)
      (*  both; only the register file, the chunk length and the hart      *)
      (*  travel as wands.                                                 *)
      (* ================================================================ *)
      iAssert (∀ (CIDb : CpuId) (Mb : regfile) (mm : nat),
          ⌜b = false \/ proc_addr j = zero_reg -> (CIDb : CPU) = (CIDa14 : CPU)⌝ -∗
          ⌜mm = Nat.min (n - tot) (BSIZE - o)⌝ -∗
          ⌜wi_sp m Mb⌝ -∗
          ⌜Mb !!! Regidx Rs10 = (mword_of_int (Z.of_nat mm) : mword 64)⌝ -∗
          ⌜Mb !!! Regidx Ra5 = (mword_of_int (Z.of_nat o) : mword 64)⌝ -∗
          ⌜Mb !!! Regidx Rs1 = bnode kkb⌝ -∗
          ⌜Mb !!! Regidx Rs4 = pa_add (m !!! Regidx Ra2 : mword 64) tot⌝ -∗
          ⌜Mb !!! Regidx Rs7 = usv⌝ -∗
          ⌜Mb !!! Regidx Rs5 = ip⌝ -∗
          ⌜Mb !!! Regidx Rs2 = (mword_of_int (Z.of_nat (off + tot)) : mword 64)⌝ -∗
          ⌜Mb !!! Regidx Rs6 = (mword_of_int (Z.of_nat n) : mword 64)⌝ -∗
          ⌜Mb !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64)⌝ -∗
          ⌜Mb !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)⌝ -∗
          ⌜Mb !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)⌝ -∗
          sie_cap_gpr KT1 Mb (K - 14)%nat b (proc_addr j) -∗
          pc_is (mword_of_int (WI + 0x4c) : mword 64) -∗
          WP (Loop : expr riscv_lang))%I
        with "[Hcnt Hextc Hextm Hcont Hframe Hidev Hinum Hmeta Hmap Hsb
               Hba Hdn Hsrc Hsl2 Hop Hbuf Hheldback Hfsb1 Htok1 Hblback]" as "BODY".
      { iIntros (CIDb Mb mm) "%Hanch %Hmmd %Hbsp %Hbs10 %Hba5 %Hbs1 %Hbs4 %Hbs7
                              %Hbs5 %Hbs2 %Hbs6 %Hbs3 %Hbs9 %Hbs8 Hcg Hpc".
        assert (Hmm1 : (1 <= mm)%nat) by (rewrite Hmmd; rewrite Hbsz in Holt |- *; lia).
        assert (Hmmn : (mm <= n - tot)%nat) by (rewrite Hmmd; lia).
        assert (Hmmo : (o + mm <= BSIZE)%nat) by (rewrite Hmmd; lia).
        iPoseProof (wri_4c with "Htext") as "Hi4c".
        iPoseProof (wri_50 with "Htext") as "Hi50".
        iPoseProof (wri_54 with "Htext") as "Hi54".
        iPoseProof (wri_58 with "Htext") as "Hi58".
        iPoseProof (wri_5a with "Htext") as "Hi5a".
        iPoseProof (wri_5c with "Htext") as "Hi5c".
        iPoseProof (wri_5e with "Htext") as "Hi5e".
        iPoseProof (wri_60 with "Htext") as "Hi60".
        iPoseProof (wri_64 with "Htext") as "Hi64".
        (* ===== +0x4c slli s11,s10,0x20 ===== *)
        iApply (wp_slli_s_sconf (mword_of_int (WI + 0x4c)) Rs11 Rs10
                  (mword_of_int 32 : mword 6)
                  (shift_bits_left (mword_of_int (Z.of_nat mm) : mword 64)
                     (subrange_vec_dec (mword_of_int 32 : mword 6)
                        (Z.sub log2_xlen 1) 0))
                  Mb (K - 14)%nat b ltac:(nz) ltac:(rdok)
                  ltac:(rgne; rewrite Hbs10; reflexivity) with "Hcg Hpc Hi4c").
        iIntros (CIDb1 Hqb1) "Hcg Hpc".
        set (D1 := <[Regidx Rs11 := regval_into_reg
                      (shift_bits_left (mword_of_int (Z.of_nat mm) : mword 64)
                         (subrange_vec_dec (mword_of_int 32 : mword 6)
                            (Z.sub log2_xlen 1) 0))]> Mb).
        assert (HD1s11 : D1 !!! Regidx Rs11
                  = shift_bits_left (mword_of_int (Z.of_nat mm) : mword 64)
                      (subrange_vec_dec (mword_of_int 32 : mword 6)
                         (Z.sub log2_xlen 1) 0))
          by (rewrite /D1; apply upd_eq).
        assert (Hpp : add_vec_int (mword_of_int (WI + 0x4c) : mword 64) 4
                      = mword_of_int (WI + 0x50)) by pcw.
        iEval (rewrite Hpp) in "Hpc". clear Hpp.
        (* ===== +0x50 srli s11,s11,0x20 : s11 := (uint64) m ===== *)
        iApply (wp_srli4_s_sconf (mword_of_int (WI + 0x50)) Rs11 Rs11
                  (mword_of_int 32 : mword 6) D1 (K - 14)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi50").
        iIntros (CIDb2 Hqb2) "Hcg Hpc".
        set (D2 := <[Regidx Rs11 := regval_into_reg
                      (shift_bits_right (rget D1 Rs11)
                         (subrange_vec_dec (mword_of_int 32 : mword 6)
                            (Z.sub log2_xlen 1) 0))]> D1).
        assert (HD2s11 : D2 !!! Regidx Rs11
                         = (mword_of_int (Z.of_nat mm) : mword 64)).
        { rewrite /D2 upd_eq. rgne. rewrite HD1s11.
          apply wi_zext32. rewrite (wi_nat_u mm ltac:(lia)).
          rewrite Hbsz in Hmmo. lia. }
        assert (Hpp : add_vec_int (mword_of_int (WI + 0x50) : mword 64) 4
                      = mword_of_int (WI + 0x54)) by pcw.
        iEval (rewrite Hpp) in "Hpc". clear Hpp.
        (* ===== +0x54 addi a0,s1,88 : a0 := bp->data ===== *)
        assert (HD2s1 : D2 !!! Regidx Rs1 = bnode kkb) by lkp.
        iApply (wp_addi4_s_sconf (mword_of_int (WI + 0x54)) Ra0 Rs1
                  (mword_of_int 88 : mword 12) D2 (K - 14)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi54").
        iIntros (CIDb3 Hqb3) "Hcg Hpc".
        set (D3 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (rget D2 Rs1)
                         (sign_extend' 64 (mword_of_int 88 : mword 12)))]> D2).
        assert (HD3a0 : D3 !!! Regidx Ra0 = b_data (bnode kkb)).
        { rewrite /D3 upd_eq. rgne. rewrite HD2s1. apply wi_data_addr. }
        assert (Hpp : add_vec_int (mword_of_int (WI + 0x54) : mword 64) 4
                      = mword_of_int (WI + 0x58)) by pcw.
        iEval (rewrite Hpp) in "Hpc". clear Hpp.
        (* ===== +0x58 c.mv a3,s11 ===== *)
        iApply (wp_cmv_s_sconf (mword_of_int (WI + 0x58)) Ra3 Rs11
                  D3 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi58").
        iIntros (CIDb4 Hqb4) "Hcg Hpc".
        set (D4 := <[Regidx Ra3 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (rget D3 Rs11))]> D3).
        assert (Hpp : add_vec_int (mword_of_int (WI + 0x58) : mword 64) 2
                      = mword_of_int (WI + 0x5a)) by pcw.
        iEval (rewrite Hpp) in "Hpc". clear Hpp.
        (* ===== +0x5a c.mv a2,s4 ===== *)
        iApply (wp_cmv_s_sconf (mword_of_int (WI + 0x5a)) Ra2 Rs4
                  D4 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5a").
        iIntros (CIDb5 Hqb5) "Hcg Hpc".
        set (D5 := <[Regidx Ra2 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (rget D4 Rs4))]> D4).
        assert (Hpp : add_vec_int (mword_of_int (WI + 0x5a) : mword 64) 2
                      = mword_of_int (WI + 0x5c)) by pcw.
        iEval (rewrite Hpp) in "Hpc". clear Hpp.
        (* ===== +0x5c c.mv a1,s7 ===== *)
        iApply (wp_cmv_s_sconf (mword_of_int (WI + 0x5c)) Ra1 Rs7
                  D5 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5c").
        iIntros (CIDb6 Hqb6) "Hcg Hpc".
        set (D6 := <[Regidx Ra1 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (rget D5 Rs7))]> D5).
        assert (Hpp : add_vec_int (mword_of_int (WI + 0x5c) : mword 64) 2
                      = mword_of_int (WI + 0x5e)) by pcw.
        iEval (rewrite Hpp) in "Hpc". clear Hpp.
        (* ===== +0x5e c.add a0,a0,a5 : a0 := bp->data + off%BSIZE ===== *)
        iApply (wp_cadd_s_sconf (mword_of_int (WI + 0x5e)) Ra0 Ra5
                  D6 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5e").
        iIntros (CIDb7 Hqb7) "Hcg Hpc".
        set (D7 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (rget D6 Ra0) (rget D6 Ra5))]> D6).
        assert (HD7a0 : D7 !!! Regidx Ra0
                        = pa_add (b_data (bnode kkb)) o).
        { rewrite /D7 upd_eq. rgne; rgne.
          rewrite (_ : D6 !!! Regidx Ra0 = b_data (bnode kkb)); [| lkp].
          rewrite (_ : D6 !!! Regidx Ra5
                       = (mword_of_int (Z.of_nat o) : mword 64)); [| lkp].
          apply wi_pa_add_moi. }
        assert (HD7a1 : D7 !!! Regidx Ra1 = usv).
        { rewrite (_ : D7 !!! Regidx Ra1
                       = add_vec (zero_reg : mword 64) (rget D5 Rs7)); [| lkp].
          rgne. rewrite (_ : D5 !!! Regidx Rs7 = usv); [| lkp].
          apply add_vec_zero_l. }
        assert (HD7a2 : D7 !!! Regidx Ra2
                        = pa_add (m !!! Regidx Ra2 : mword 64) tot).
        { rewrite (_ : D7 !!! Regidx Ra2
                       = add_vec (zero_reg : mword 64) (rget D4 Rs4)); [| lkp].
          rgne. rewrite (_ : D4 !!! Regidx Rs4
                             = pa_add (m !!! Regidx Ra2 : mword 64) tot); [| lkp].
          apply add_vec_zero_l. }
        assert (HD7a3 : D7 !!! Regidx Ra3
                        = (mword_of_int (Z.of_nat mm) : mword 64)).
        { rewrite (_ : D7 !!! Regidx Ra3
                       = add_vec (zero_reg : mword 64) (rget D3 Rs11)); [| lkp].
          rgne. rewrite (_ : D3 !!! Regidx Rs11
                             = (mword_of_int (Z.of_nat mm) : mword 64)); [| lkp].
          apply add_vec_zero_l. }
        assert (HD7sp : wi_sp m D7) by (rewrite /wi_sp; lkp).
        assert (HD7s1 : D7 !!! Regidx Rs1 = bnode kkb) by lkp.
        assert (HD7s10 : D7 !!! Regidx Rs10
                         = (mword_of_int (Z.of_nat mm) : mword 64)) by lkp.
        assert (HD7s11 : D7 !!! Regidx Rs11
                         = (mword_of_int (Z.of_nat mm) : mword 64)) by lkp.
        assert (HD7s2 : D7 !!! Regidx Rs2
                        = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp.
        assert (HD7s3 : D7 !!! Regidx Rs3
                        = (mword_of_int (Z.of_nat tot) : mword 64)) by lkp.
        assert (HD7s4 : D7 !!! Regidx Rs4
                        = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp.
        assert (HD7s5 : D7 !!! Regidx Rs5 = ip) by lkp.
        assert (HD7s6 : D7 !!! Regidx Rs6
                        = (mword_of_int (Z.of_nat n) : mword 64)) by lkp.
        assert (HD7s7 : D7 !!! Regidx Rs7 = usv) by lkp.
        assert (HD7s8 : D7 !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)) by lkp.
        assert (HD7s9 : D7 !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)) by lkp.
        assert (Hpp : add_vec_int (mword_of_int (WI + 0x5e) : mword 64) 2
                      = mword_of_int (WI + 0x60)) by pcw.
        iEval (rewrite Hpp) in "Hpc". clear Hpp.
        (* ---- the destination window inside the checked-out buffer ---- *)
        iDestruct (wi_buf_win_acc (bnode kkb) (blkmap_get bm2 fbn)
                     (mword_of_int 0 : mword 32) (data2 fbn) o mm Hmmo
                     with "Hbuf") as "(%Hlenb & Hwin & Hwinback)".
        (* ---- and the source window, on the kernel arm ---- *)
        iAssert ((if user
                  then proc_priv_core (proc_addr j) pidv (upd_upt V PI)
                  else [∗ list] jj ∈ seq 0 mm,
                         pa_add (pa_add (m !!! Regidx Ra2 : mword 64) tot) jj
                           ↦ₘ[ktb] (src_bytes (tot + jj)%nat))
                 ∗ (if user then True
                    else ([∗ list] jj ∈ seq 0 tot,
                            pa_add (m !!! Regidx Ra2 : mword 64) jj ↦ₘ[ktb] (src_bytes jj))
                         ∗ ([∗ list] jj ∈ seq 0 (n - tot - mm),
                              pa_add (pa_add (pa_add (m !!! Regidx Ra2 : mword 64) tot)
                                        mm) jj ↦ₘ[ktb] (src_bytes (tot + (mm + jj))%nat))
                         (* THE PID SHARE PARKS HERE across the copy.  On the
                            user arm it is inside [proc_priv], which travels
                            as [Hsrcw]; on the kernel arm either_copyin never
                            wants it, so it waits with the untouched tail. *)
                         ∗ p_pid (proc_addr j) ↦₄{dq} pidv))%I
          with "[Hsrc]" as "[Hsrcw Hsrcrest]".
        { destruct user.
          - iSplitL "Hsrc"; [iExact "Hsrc" | done].
          - iDestruct "Hsrc" as "[Hsrc Hppid]".
            iDestruct (ProofWriteiParts.wi_split3 (KTR := ktb) (m !!! Regidx Ra2 : mword 64)
                         tot mm (n - tot - mm)%nat n (fun i => src_bytes i)
                         ltac:(lia) with "Hsrc") as "(Hp & Hq & Hr)".
            iSplitL "Hq"; [iExact "Hq"|]. iSplitL "Hp"; [iExact "Hp"|].
            iSplitL "Hr"; [iExact "Hr"|]. iExact "Hppid". }
        (* ===== +0x60 jal ra,either_copyin ===== *)
        iApply (wp_jal_s_sconf (mword_of_int (WI + 0x60)) Rra
                  (mword_of_int 2091930 : mword 21) D7 (K - 14)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi60").
        iIntros (CIDb8 Hqb8) "Hcg Hpc".
        iClear "Hi4c Hi50 Hi54 Hi58 Hi5a Hi5c Hi5e Hi60".
        set (D8 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (WI + 0x60) : mword 64) 4)]> D7).
        assert (Htgtec : add_vec (mword_of_int (WI + 0x60) : mword 64)
                           (sign_extend' 64 (mword_of_int 2091930 : mword 21))
                         = mword_of_int KernelSyms.either_copyin) by pcw.
        iEval (rewrite Htgtec) in "Hpc".
        assert (HD8ra : D8 !!! Regidx Rra
                        = add_vec_int (mword_of_int (WI + 0x60) : mword 64) 4)
          by (rewrite /D8; apply upd_eq).
        assert (HD8a0 : D8 !!! Regidx Ra0 = pa_add (b_data (bnode kkb)) o) by lkp.
        assert (HD8a1 : D8 !!! Regidx Ra1 = usv) by lkp.
        assert (HD8a2 : D8 !!! Regidx Ra2
                        = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp.
        assert (HD8a3 : D8 !!! Regidx Ra3
                        = (mword_of_int (Z.of_nat mm) : mword 64)) by lkp.
        iDestruct (cpu_own_transport CIDa14 CIDb8 0 eb (proc_addr j) b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iEval (rewrite -HD8a0) in "Hwin".
        iEval (rewrite -HD8a2) in "Hsrcw".
        iApply (EC.wp_either_copyin_sconf KT0 ktb γa γf D8 (K - 14)%nat 0%nat eb
                  (proc_addr j) pidv (upd_upt V PI) user mm
                  (fun jj => src_bytes (tot + jj)%nat)
                  (fun i => (data2 fbn) !!! (o + i)%nat) b lks
                  ltac:(lia)
                  ltac:(rewrite HD8a1; exact Husv) HD8a3
                  ltac:(destruct user;
                        [change (2 ^ 64)%Z with 18446744073709551616%Z
                        |change (2 ^ 31)%Z with 2147483648%Z];
                        rewrite Hbsz in Hmmo; lia)
                  ltac:(change (2 ^ 31)%Z with 2147483648%Z; lia)
                  with "Hcg Hcnt Htext Hpc Hkenv Hwin Hsrcw").
        all: try lkbelow.
        iIntros (CIDb9 Hqb9 mE) "%HcsE Hcg Hcnt Hpc Hpost".
        assert (Hpc64 : ret_pc (D8 !!! Regidx Rra : mword 64)
                        = mword_of_int (WI + 0x64)) by (rewrite HD8ra; pcw).
        iEval (rewrite Hpc64) in "Hpc".
        iEval (rewrite /either_copyin_post HD8a0 HD8a2) in "Hpost".
        (* ---- the two arms of the post, in one shape ---- *)
        iAssert (∃ (g : nat -> bv 8) (P2 : uptd),
                   ⌜uptd_ext (pv_upt V) P2⌝ ∗
                   ⌜user = false -> forall i : nat, (i < mm)%nat ->
                      g i = src_bytes (tot + i)%nat⌝ ∗
                   (* THE -1 ARM CARRIES [user = true] (fs-icache.md §15.1(i)):
                      either_copyin's KERNEL post is a bare [r = 0], so a
                      failed copy is evidence of the user arm.  That is what
                      makes writei's disturbed region empty for [user =
                      false] -- the break below is simply not reachable. *)
                   ⌜(mE !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64)
                    \/ (user = true
                        /\ (mE !!! Regidx Ra0 : mword 64)
                           = (mword_of_int (-1) : mword 64))⌝ ∗
                   ([∗ list] i ∈ seq 0 mm,
                      pa_add (pa_add (b_data (bnode kkb)) o) i ↦ₘ (g i)) ∗
                   (if user then proc_priv_core (proc_addr j) pidv (upd_upt V P2)
                    else ([∗ list] i ∈ seq 0 n,
                            pa_add (m !!! Regidx Ra2 : mword 64) i ↦ₘ[ktb] (src_bytes i))
                         ∗ p_pid (proc_addr j) ↦₄{dq} pidv))%I
          with "[Hpost Hsrcrest]" as "Hnorm".
        { destruct user.
          - iDestruct "Hpost" as "(%Hr & Hpp & Hdst)".
            iDestruct "Hpp" as (P2) "[%Hx Hpriv]".
            iDestruct "Hdst" as (gg) "Hw".
            iExists gg, P2.
            iSplitR; [iPureIntro; exact (uptd_ext_trans _ _ _ HextI Hx)|].
            iSplitR; [iPureIntro; discriminate|].
            iSplitR; [iPureIntro; destruct Hr as [H0 | Hm1];
                      [left; exact H0
                      | right; split; [reflexivity | exact Hm1]]|].
            iSplitL "Hw"; [iExact "Hw"|]. iExact "Hpriv".
          - iDestruct "Hpost" as "(%Hr & Hsb2 & Hdst)".
            iDestruct "Hsrcrest" as "(Hp & Hq & Hppid)".
            iExists (fun jj => src_bytes (tot + jj)%nat), PI.
            iSplitR; [iPureIntro; exact HextI|].
            iSplitR; [iPureIntro; intros _ i _; reflexivity|].
            iSplitR; [iPureIntro; left; exact Hr|].
            iSplitL "Hdst"; [iExact "Hdst"|].
            iSplitR "Hppid"; [| iExact "Hppid"].
            iApply (ProofWriteiParts.wi_join3 (KTR := ktb) (m !!! Regidx Ra2 : mword 64)
                      tot mm (n - tot - mm)%nat n (fun i => src_bytes i)
                      ltac:(lia) with "Hp Hsb2 Hq"). }
        iDestruct "Hnorm" as (g P2) "(%Hext2 & %Hgk & %HrE & Hwin & Hsrc)".
        (* ---- the buffer, re-formed at the spliced bytes ---- *)
        iDestruct ("Hwinback" $! g with "Hwin") as "Hbuf".
        iDestruct ("Hheldback" $! (wi_splice (data2 fbn) o mm g) with "Hbuf")
          as "Hheld".
        pose proof HcsE as HcsEc.
        assert (HEsp : wi_sp m mE).
        { rewrite /wi_sp
            (callee_saved_lookup HcsEc csp_rs1 ltac:(vm_compute; reflexivity)).
          exact HD7sp. }
        assert (HEs1 : mE !!! Regidx Rs1 = bnode kkb)
          by (rewrite (callee_saved_lookup HcsEc Rs1 ltac:(vm_compute; reflexivity));
              exact HD7s1).
        assert (HEs2 : mE !!! Regidx Rs2
                       = (mword_of_int (Z.of_nat (off + tot)) : mword 64))
          by (rewrite (callee_saved_lookup HcsEc Rs2 ltac:(vm_compute; reflexivity));
              exact HD7s2).
        assert (HEs3 : mE !!! Regidx Rs3
                       = (mword_of_int (Z.of_nat tot) : mword 64))
          by (rewrite (callee_saved_lookup HcsEc Rs3 ltac:(vm_compute; reflexivity));
              exact HD7s3).
        assert (HEs4 : mE !!! Regidx Rs4
                       = pa_add (m !!! Regidx Ra2 : mword 64) tot)
          by (rewrite (callee_saved_lookup HcsEc Rs4 ltac:(vm_compute; reflexivity));
              exact HD7s4).
        assert (HEs5 : mE !!! Regidx Rs5 = ip)
          by (rewrite (callee_saved_lookup HcsEc Rs5 ltac:(vm_compute; reflexivity));
              exact HD7s5).
        assert (HEs6 : mE !!! Regidx Rs6 = (mword_of_int (Z.of_nat n) : mword 64))
          by (rewrite (callee_saved_lookup HcsEc Rs6 ltac:(vm_compute; reflexivity));
              exact HD7s6).
        assert (HEs7 : mE !!! Regidx Rs7 = usv)
          by (rewrite (callee_saved_lookup HcsEc Rs7 ltac:(vm_compute; reflexivity));
              exact HD7s7).
        assert (HEs8 : mE !!! Regidx Rs8 = (mword_of_int (-1) : mword 64))
          by (rewrite (callee_saved_lookup HcsEc Rs8 ltac:(vm_compute; reflexivity));
              exact HD7s8).
        assert (HEs9 : mE !!! Regidx Rs9 = (mword_of_int 1024 : mword 64))
          by (rewrite (callee_saved_lookup HcsEc Rs9 ltac:(vm_compute; reflexivity));
              exact HD7s9).
        assert (HEs10 : mE !!! Regidx Rs10
                        = (mword_of_int (Z.of_nat mm) : mword 64))
          by (rewrite (callee_saved_lookup HcsEc Rs10 ltac:(vm_compute; reflexivity));
              exact HD7s10).
        assert (HEs11 : mE !!! Regidx Rs11
                        = (mword_of_int (Z.of_nat mm) : mword 64))
          by (rewrite (callee_saved_lookup HcsEc Rs11 ltac:(vm_compute; reflexivity));
              exact HD7s11).
        (* the new per-block content, and the two invariants over it *)
        assert (Hhz3 : blk_holes_zero bm2
                         (<[fbn := wi_splice (data2 fbn) o mm g]> data2)).
        { intros i Hi Hz. rewrite fn_lookup_insert_ne.
          - exact (Hhz2 i Hi Hz).
          - intros ->. exact (Hbnzz Hz). }
        assert (Hlenb2 : length (data2 fbn) = BSIZE) by exact Hlenb.
        destruct HrE as [Hr0 | [Huser Hrm1]].
        + (* ============ THE COPY SUCCEEDED ============ *)
          iPoseProof (wri_68 with "Htext") as "Hi68".
          iPoseProof (wri_6a with "Htext") as "Hi6a".
          iPoseProof (wri_6e with "Htext") as "Hi6e".
          iPoseProof (wri_70 with "Htext") as "Hi70".
          iPoseProof (wri_74 with "Htext") as "Hi74".
          iPoseProof (wri_78 with "Htext") as "Hi78".
          iPoseProof (wri_7c with "Htext") as "Hi7c".
          iPoseProof (wri_7e with "Htext") as "Hi7e".
          iApply (wp_beq_fall_s_sconf (mword_of_int (WI + 0x64))
                    (mword_of_int 76 : mword 13) Rs8 Ra0 mE (K - 14)%nat b
                    ltac:(nz) ltac:(nz)
                    ltac:(rgne; rgne; rewrite Hr0 HEs8; vm_compute; reflexivity)
                    with "Hcg Hpc Hi64").
          iIntros (CIDc1 Hqc1) "Hcg Hpc".
          iClear "Hi64".
          assert (Hpp : add_vec_int (mword_of_int (WI + 0x64) : mword 64) 4
                        = mword_of_int (WI + 0x68)) by pcw.
          iEval (rewrite Hpp) in "Hpc". clear Hpp.
          (* ===== +0x68 c.mv a0,s1 ===== *)
          iApply (wp_cmv_s_sconf (mword_of_int (WI + 0x68)) Ra0 Rs1
                    mE (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi68").
          iIntros (CIDc2 Hqc2) "Hcg Hpc".
          set (F1 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64) (rget mE Rs1))]> mE).
          assert (HF1a0 : F1 !!! Regidx Ra0 = bnode kkb).
          { rewrite /F1 upd_eq. rgne. rewrite HEs1. apply add_vec_zero_l. }
          assert (Hpp : add_vec_int (mword_of_int (WI + 0x68) : mword 64) 2
                        = mword_of_int (WI + 0x6a)) by pcw.
          iEval (rewrite Hpp) in "Hpc". clear Hpp.
          (* ===== +0x6a jal ra,log_write ===== *)
          iApply (wp_jal_s_sconf (mword_of_int (WI + 0x6a)) Rra
                    (mword_of_int 1762 : mword 21) F1 (K - 14)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi6a").
          iIntros (CIDc3 Hqc3) "Hcg Hpc".
          set (F2 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (WI + 0x6a) : mword 64) 4)]> F1).
          assert (Htgtlw : add_vec (mword_of_int (WI + 0x6a) : mword 64)
                             (sign_extend' 64 (mword_of_int 1762 : mword 21))
                           = mword_of_int KernelSyms.log_write) by pcw.
          iEval (rewrite Htgtlw) in "Hpc".
          assert (HF2ra : F2 !!! Regidx Rra
                          = add_vec_int (mword_of_int (WI + 0x6a) : mword 64) 4)
            by (rewrite /F2; apply upd_eq).
          assert (HF2a0 : F2 !!! Regidx Ra0 = bnode kkb) by lkp.
          iDestruct (cpu_own_transport CIDb9 CIDc3 0 eb (proc_addr j) b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          assert (HKlw : (K_log_write <= K - 14)%nat) by (lia).
          iDestruct (wi_slots_split bn 1 1 with "Hsl2") as "[Hsla Hslb]".
          (* THE ABSORPTION, claimed as a decidable read of the op's set: if
             bmap just allocated this data block then balloc's [bzero]
             already logged it and this write is FREE.  The premise is
             discharged by the very bool_decide that names the credit. *)
          iApply (LW.wp_log_write_gen bn γ γfs γd cov logstart dev kkb pidv
                    (blkmap_get bm2 fbn) (wi_splice (data2 fbn) o mm g)
                    (data2 fbn) bsdB dB uX
                    (bool_decide (uint (blkmap_get bm2 fbn : mword 32) ∈ Sb2)) Sb2
                    F2 0%nat eb (proc_addr j) (K - 14)%nat b lks
                    HKlw ltac:(change (2 ^ 31)%Z with 2147483648%Z; lia)
                    Hkklt HF2a0 Hbcovlw Hbloglw
                    ltac:(intros Hc; exact (proj1 (bool_decide_eq_true _) Hc))
                    Hbelow
                    with "Hcg Hcnt Htext Hpc Hbio Hlctx Hsla Hop Hfsb1 Hheld").
          all: try lkbelow.
          iIntros (CIDc4 Hqc4 mL) "Hcg Hcnt Hpc %HcsL Hop Hfsb1 Hheld Hsla".
          (* the count log_write left, as a variable: [S uX] when it absorbed,
             [uX] when it spent.  Naming it keeps the rest of this iteration
             free of the case split. *)
          remember (if bool_decide (uint (blkmap_get bm2 fbn : mword 32) ∈ Sb2)
                    then S uX else uX) as nL eqn:HnLdef.
          assert (HnLhi : (nL <= S uX)%nat)
            by (rewrite HnLdef; case_bool_decide; lia).
          assert (HnLlo : (S uX <= nL + (if bool_decide (uint (blkmap_get bm2 fbn : mword 32) ∈ Sb2)
                                         then 0 else 1))%nat)
            by (rewrite HnLdef; case_bool_decide; lia).
          (* THE WHOLE ITERATION against the accounting, bmap and this
             log_write together.  The allocating arm needs the absorption to
             have fired, and [wi_ad_of_alloced] is why it did: on the
             indirect path an allocating bmap allocated the DATA block too. *)
          assert (Hinv3 : wi_inv_bud (ba_bms A) W nL (Sb2 ∪ {[uint (blkmap_get bm2 fbn : mword 32)]})
                          /\ wi_inv_spent (ba_bms A) ncount nL
                               (wi_blocks off n) W (Sb2 ∪ {[uint (blkmap_get bm2 fbn : mword 32)]})).
          { destruct (bmap_alloced bmI bm2 fbn) eqn:Hal3.
            - (* THE ABSORPTION FIRED, and [wi_ad_of_alloced] is why *)
              assert (Hcrlw : true = true -> bmap_ind fbn = true ->
                              bool_decide (uint (blkmap_get bm2 fbn : mword 32) ∈ Sb2) = true).
              { intros _ Hind3. apply bool_decide_eq_true.
                (* bmap states clause (d) on [bv_unsigned], log_write's set on
                   [uint]; [Hubno] is the bridge, already in scope *)
                rewrite Hubno. apply Hbc6.
                exact (wi_ad_of_alloced cov logstart bmI bm2 fbn HwfI Hfbnlt
                         Hbnzz Hind3 Hal3). }
              assert (Hlo3 : (nI <= nL + 2 + bm_pot (ba_bms A) SI)%nat)
                by exact (wi_iter_alloc_bound (ba_bms A) nI (S uX) nL SI _
                            true (bmap_ind fbn) Hbc1 HnLlo Hcrlw).
              pose proof (wi_step_alloc (ba_bms A) ncount nI nL (wi_blocks off n)
                            (S W) SI (Sb2 ∪ {[uint (blkmap_get bm2 fbn : mword 32)]})
                            ltac:(lia) HW5 HW2 HW4
                            (wiset_sub_add_r SI Sb2 _ Hbc3)
                            (wiset_in_add_r _ Sb2 _ (Hbc5 eq_refl))
                            Hlo3 ltac:(lia)) as Hst3.
              replace (S W - 1)%nat with W in Hst3 by lia. exact Hst3.
            - assert (Hlo3 : (nI <= nL + 1)%nat)
                by exact (wi_iter_noalloc_bound (ba_bms A) nI (S uX) nL SI _
                            (bmap_ind fbn) Hbc1 HnLlo).
              pose proof (wi_step_noalloc (ba_bms A) ncount nI nL
                            (wi_blocks off n) (S W) SI (Sb2 ∪ {[uint (blkmap_get bm2 fbn : mword 32)]})
                            ltac:(lia) HW5 HW2 HW4
                            (wiset_sub_add_r SI Sb2 _ Hbc3)
                            Hlo3 ltac:(lia)) as Hst3.
              replace (S W - 1)%nat with W in Hst3 by lia. exact Hst3. }
          assert (HsbSb3 : Sb ⊆ Sb2 ∪ {[uint (blkmap_get bm2 fbn : mword 32)]})
            by (apply wiset_sub_add_r; exact HsbSb2).
          assert (Hpc6e : ret_pc (F2 !!! Regidx Rra : mword 64)
                          = mword_of_int (WI + 0x6e)) by (rewrite HF2ra; pcw).
          iEval (rewrite Hpc6e) in "Hpc".
          iDestruct (wi_slots_join bn 1 1 with "Hsla Hslb") as "Hsl2".
          pose proof HcsL as HcsLc.
          assert (HF2s1 : F2 !!! Regidx Rs1 = bnode kkb) by lkp.
          assert (HLsp : wi_sp m mL).
          { rewrite /wi_sp
              (callee_saved_lookup HcsLc csp_rs1 ltac:(vm_compute; reflexivity)).
            assert (HH : wi_sp m F2) by (rewrite /wi_sp; lkp). exact HH. }
          assert (HLRs2 : mL !!! Regidx Rs2 = (mword_of_int (Z.of_nat (off + tot)) : mword 64)).
          { rewrite (callee_saved_lookup HcsLc Rs2 ltac:(vm_compute; reflexivity)).
            assert (HH : F2 !!! Regidx Rs2 = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp. exact HH. }
          assert (HLRs3 : mL !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64)).
          { rewrite (callee_saved_lookup HcsLc Rs3 ltac:(vm_compute; reflexivity)).
            assert (HH : F2 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64)) by lkp. exact HH. }
          assert (HLRs4 : mL !!! Regidx Rs4 = pa_add (m !!! Regidx Ra2 : mword 64) tot).
          { rewrite (callee_saved_lookup HcsLc Rs4 ltac:(vm_compute; reflexivity)).
            assert (HH : F2 !!! Regidx Rs4 = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp. exact HH. }
          assert (HLRs5 : mL !!! Regidx Rs5 = ip).
          { rewrite (callee_saved_lookup HcsLc Rs5 ltac:(vm_compute; reflexivity)).
            assert (HH : F2 !!! Regidx Rs5 = ip) by lkp. exact HH. }
          assert (HLRs6 : mL !!! Regidx Rs6 = (mword_of_int (Z.of_nat n) : mword 64)).
          { rewrite (callee_saved_lookup HcsLc Rs6 ltac:(vm_compute; reflexivity)).
            assert (HH : F2 !!! Regidx Rs6 = (mword_of_int (Z.of_nat n) : mword 64)) by lkp. exact HH. }
          assert (HLRs7 : mL !!! Regidx Rs7 = usv).
          { rewrite (callee_saved_lookup HcsLc Rs7 ltac:(vm_compute; reflexivity)).
            assert (HH : F2 !!! Regidx Rs7 = usv) by lkp. exact HH. }
          assert (HLRs8 : mL !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)).
          { rewrite (callee_saved_lookup HcsLc Rs8 ltac:(vm_compute; reflexivity)).
            assert (HH : F2 !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)) by lkp. exact HH. }
          assert (HLRs9 : mL !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)).
          { rewrite (callee_saved_lookup HcsLc Rs9 ltac:(vm_compute; reflexivity)).
            assert (HH : F2 !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)) by lkp. exact HH. }
          assert (HLRs10 : mL !!! Regidx Rs10 = (mword_of_int (Z.of_nat mm) : mword 64)).
          { rewrite (callee_saved_lookup HcsLc Rs10 ltac:(vm_compute; reflexivity)).
            assert (HH : F2 !!! Regidx Rs10 = (mword_of_int (Z.of_nat mm) : mword 64)) by lkp. exact HH. }
          assert (HLRs11 : mL !!! Regidx Rs11 = (mword_of_int (Z.of_nat mm) : mword 64)).
          { rewrite (callee_saved_lookup HcsLc Rs11 ltac:(vm_compute; reflexivity)).
            assert (HH : F2 !!! Regidx Rs11 = (mword_of_int (Z.of_nat mm) : mword 64)) by lkp. exact HH. }

          assert (HLs1 : mL !!! Regidx Rs1 = bnode kkb)
            by (rewrite (callee_saved_lookup HcsLc Rs1 ltac:(vm_compute; reflexivity));
                exact HF2s1).
          (* ===== +0x6e c.mv a0,s1 ===== *)
          iApply (wp_cmv_s_sconf (mword_of_int (WI + 0x6e)) Ra0 Rs1
                    mL (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi6e").
          iIntros (CIDc5 Hqc5) "Hcg Hpc".
          set (F3 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64) (rget mL Rs1))]> mL).
          assert (HF3a0 : F3 !!! Regidx Ra0 = bnode kkb).
          { rewrite /F3 upd_eq. rgne. rewrite HLs1. apply add_vec_zero_l. }
          assert (Hpp : add_vec_int (mword_of_int (WI + 0x6e) : mword 64) 2
                        = mword_of_int (WI + 0x70)) by pcw.
          iEval (rewrite Hpp) in "Hpc". clear Hpp.
          (* ===== +0x70 jal ra,brelse ===== *)
          iApply (wp_jal_s_sconf (mword_of_int (WI + 0x70)) Rra
                    (mword_of_int 2094388 : mword 21) F3 (K - 14)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi70").
          iIntros (CIDc6 Hqc6) "Hcg Hpc".
          set (F4 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (WI + 0x70) : mword 64) 4)]> F3).
          assert (Htgtbl : add_vec (mword_of_int (WI + 0x70) : mword 64)
                             (sign_extend' 64 (mword_of_int 2094388 : mword 21))
                           = mword_of_int KernelSyms.brelse) by pcw.
          iEval (rewrite Htgtbl) in "Hpc".
          assert (HF4ra : F4 !!! Regidx Rra
                          = add_vec_int (mword_of_int (WI + 0x70) : mword 64) 4)
            by (rewrite /F4; apply upd_eq).
          assert (HF4a0 : F4 !!! Regidx Ra0 = bnode kkb) by lkp.
          iDestruct (cpu_own_transport CIDc4 CIDc6 0 eb (proc_addr j) b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          assert (HKbl : (K_brelse <= K - 14)%nat) by (lia).
          (* BORROW the pid share for brelse.  The bracket is now at
             [upd_upt V P2] -- either_copyin extended the descriptor -- and
             the borrow closes before this iteration hands the bracket on. *)
          iDestruct (wi_src_pid γf j pidv dq user (upd_upt V P2)
                       (m !!! Regidx Ra2 : mword 64) n src_bytes with "Hsrc")
            as "[Hppid Hsrcback]".
          iApply (BL.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) kkb
                    pidv dev (blkmap_get bm2 fbn) (wi_q user dq)
                    F4 (K - 14)%nat eb
                    (proc_addr j) (wi_splice (data2 fbn) o mm g) bsdB true b lks
                    HKbl Hkklt HF4a0
                    ltac:(lkbelow)
                    with "Hcg Hcnt Htext Hpc Hbio Hppid Hprocs Hheld").
          all: try lkbelow.
          iIntros (CIDc7 Hqc7 mR) "%HcsR Hcg Hcnt Hpc Hppid Hsl1".
          iDestruct ("Hsrcback" with "Hppid") as "Hsrc".
          assert (Hpc74 : ret_pc (F4 !!! Regidx Rra : mword 64)
                          = mword_of_int (WI + 0x74)) by (rewrite HF4ra; pcw).
          iEval (rewrite Hpc74) in "Hpc".
          iDestruct (wi_slots_join bn 2 1 with "Hsl2 Hsl1") as "Hsl".
          iEval (rewrite Hubno) in "Hfsb1".
          iDestruct ("Hblback" $! (wi_splice (data2 fbn) o mm g)
                       with "Hfsb1 Htok1") as "Hblocks".
          (* ---- the accumulated effect of this chunk ---- *)
          pose proof HcsR as HcsRc.
          assert (HRsp : wi_sp m mR).
          { rewrite /wi_sp
              (callee_saved_lookup HcsRc csp_rs1 ltac:(vm_compute; reflexivity)).
            assert (HF4sp : wi_sp m F4) by (rewrite /wi_sp; lkp). exact HF4sp. }
          assert (HRs2 : mR !!! Regidx Rs2
                         = (mword_of_int (Z.of_nat (off + tot)) : mword 64)).
          { rewrite (callee_saved_lookup HcsRc Rs2 ltac:(vm_compute; reflexivity)).
            assert (HF4s2 : F4 !!! Regidx Rs2
                            = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp.
            exact HF4s2. }
          assert (HRs3 : mR !!! Regidx Rs3
                         = (mword_of_int (Z.of_nat tot) : mword 64)).
          { rewrite (callee_saved_lookup HcsRc Rs3 ltac:(vm_compute; reflexivity)).
            assert (HF4s3 : F4 !!! Regidx Rs3
                            = (mword_of_int (Z.of_nat tot) : mword 64)) by lkp.
            exact HF4s3. }
          assert (HRs4 : mR !!! Regidx Rs4
                         = pa_add (m !!! Regidx Ra2 : mword 64) tot).
          { rewrite (callee_saved_lookup HcsRc Rs4 ltac:(vm_compute; reflexivity)).
            assert (HF4s4 : F4 !!! Regidx Rs4
                            = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp.
            exact HF4s4. }
          assert (HRs5 : mR !!! Regidx Rs5 = ip).
          { rewrite (callee_saved_lookup HcsRc Rs5 ltac:(vm_compute; reflexivity)).
            assert (HF4s5 : F4 !!! Regidx Rs5 = ip) by lkp. exact HF4s5. }
          assert (HRs6 : mR !!! Regidx Rs6
                         = (mword_of_int (Z.of_nat n) : mword 64)).
          { rewrite (callee_saved_lookup HcsRc Rs6 ltac:(vm_compute; reflexivity)).
            assert (HF4s6 : F4 !!! Regidx Rs6
                            = (mword_of_int (Z.of_nat n) : mword 64)) by lkp.
            exact HF4s6. }
          assert (HRs7 : mR !!! Regidx Rs7 = usv).
          { rewrite (callee_saved_lookup HcsRc Rs7 ltac:(vm_compute; reflexivity)).
            assert (HF4s7 : F4 !!! Regidx Rs7 = usv) by lkp. exact HF4s7. }
          assert (HRs8 : mR !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)).
          { rewrite (callee_saved_lookup HcsRc Rs8 ltac:(vm_compute; reflexivity)).
            assert (HF4s8 : F4 !!! Regidx Rs8
                            = (mword_of_int (-1) : mword 64)) by lkp. exact HF4s8. }
          assert (HRs9 : mR !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)).
          { rewrite (callee_saved_lookup HcsRc Rs9 ltac:(vm_compute; reflexivity)).
            assert (HF4s9 : F4 !!! Regidx Rs9
                            = (mword_of_int 1024 : mword 64)) by lkp. exact HF4s9. }
          assert (HRs10 : mR !!! Regidx Rs10
                          = (mword_of_int (Z.of_nat mm) : mword 64)).
          { rewrite (callee_saved_lookup HcsRc Rs10 ltac:(vm_compute; reflexivity)).
            assert (HF4s10 : F4 !!! Regidx Rs10
                             = (mword_of_int (Z.of_nat mm) : mword 64)) by lkp.
            exact HF4s10. }
          assert (HRs11 : mR !!! Regidx Rs11
                          = (mword_of_int (Z.of_nat mm) : mword 64)).
          { rewrite (callee_saved_lookup HcsRc Rs11 ltac:(vm_compute; reflexivity)).
            assert (HF4s11 : F4 !!! Regidx Rs11
                             = (mword_of_int (Z.of_nat mm) : mword 64)) by lkp.
            exact HF4s11. }
          (* ===== +0x74 addw s3,s10,s3 : tot += m ===== *)
          iApply (wp_addw4_s_sconf (mword_of_int (WI + 0x74)) Rs3 Rs10 Rs3
                    mR (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi74").
          iIntros (CIDc8 Hqc8) "Hcg Hpc".
          set (G1 := <[Regidx Rs3 := regval_into_reg
                        (sign_extend' 64
                          (add_vec (subrange_vec_dec (rget mR Rs10) 31 0 : mword 32)
                                   (subrange_vec_dec (rget mR Rs3) 31 0 : mword 32)))]> mR).
          assert (HG1s3 : G1 !!! Regidx Rs3
                          = (mword_of_int (Z.of_nat (tot + mm)) : mword 64)).
          { rewrite /G1 upd_eq. rgne; rgne. rewrite HRs10 HRs3.
            rewrite (wi_addw (Z.of_nat mm) (Z.of_nat tot)
                       ltac:(lia) ltac:(lia) ltac:(lia)).
            assert (Hz : (Z.of_nat mm + Z.of_nat tot)%Z = Z.of_nat (tot + mm)) by lia.
            rewrite Hz. reflexivity. }
          assert (Hpp : add_vec_int (mword_of_int (WI + 0x74) : mword 64) 4
                        = mword_of_int (WI + 0x78)) by pcw.
          iEval (rewrite Hpp) in "Hpc". clear Hpp.
          (* ===== +0x78 addw s2,s10,s2 : off += m ===== *)
          assert (HG1s10 : G1 !!! Regidx Rs10
                           = (mword_of_int (Z.of_nat mm) : mword 64)) by lkp.
          assert (HG1s2 : G1 !!! Regidx Rs2
                          = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp.
          iApply (wp_addw4_s_sconf (mword_of_int (WI + 0x78)) Rs2 Rs10 Rs2
                    G1 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi78").
          iIntros (CIDc9 Hqc9) "Hcg Hpc".
          set (G2 := <[Regidx Rs2 := regval_into_reg
                        (sign_extend' 64
                          (add_vec (subrange_vec_dec (rget G1 Rs10) 31 0 : mword 32)
                                   (subrange_vec_dec (rget G1 Rs2) 31 0 : mword 32)))]> G1).
          assert (HG2s2 : G2 !!! Regidx Rs2
                          = (mword_of_int (Z.of_nat (off + (tot + mm))) : mword 64)).
          { rewrite /G2 upd_eq. rgne; rgne. rewrite HG1s10 HG1s2.
            rewrite (wi_addw (Z.of_nat mm) (Z.of_nat (off + tot))
                       ltac:(lia) ltac:(lia) ltac:(lia)).
            assert (Hz : (Z.of_nat mm + Z.of_nat (off + tot))%Z
                         = Z.of_nat (off + (tot + mm))) by lia.
            rewrite Hz. reflexivity. }
          assert (Hpp : add_vec_int (mword_of_int (WI + 0x78) : mword 64) 4
                        = mword_of_int (WI + 0x7c)) by pcw.
          iEval (rewrite Hpp) in "Hpc". clear Hpp.
          (* ===== +0x7c c.add s4,s4,s11 : src += m ===== *)
          assert (HG2s4 : G2 !!! Regidx Rs4
                          = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp.
          assert (HG2s11 : G2 !!! Regidx Rs11
                           = (mword_of_int (Z.of_nat mm) : mword 64)) by lkp.
          iApply (wp_cadd_s_sconf (mword_of_int (WI + 0x7c)) Rs4 Rs11
                    G2 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi7c").
          iIntros (CIDc10 Hqc10) "Hcg Hpc".
          set (G3 := <[Regidx Rs4 := regval_into_reg
                        (add_vec (rget G2 Rs4) (rget G2 Rs11))]> G2).
          assert (HG3s4 : G3 !!! Regidx Rs4
                          = pa_add (m !!! Regidx Ra2 : mword 64) (tot + mm)).
          { rewrite /G3 upd_eq. rgne; rgne. rewrite HG2s4 HG2s11. apply wi_pa_step. }
          assert (HG3s3 : G3 !!! Regidx Rs3
                          = (mword_of_int (Z.of_nat (tot + mm)) : mword 64)) by lkp.
          assert (HG3s2 : G3 !!! Regidx Rs2
                          = (mword_of_int (Z.of_nat (off + (tot + mm))) : mword 64))
            by lkp.
          assert (HG3s5 : G3 !!! Regidx Rs5 = ip) by lkp.
          assert (HG3s6 : G3 !!! Regidx Rs6
                          = (mword_of_int (Z.of_nat n) : mword 64)) by lkp.
          assert (HG3s7 : G3 !!! Regidx Rs7 = usv) by lkp.
          assert (HG3s8 : G3 !!! Regidx Rs8
                          = (mword_of_int (-1) : mword 64)) by lkp.
          assert (HG3s9 : G3 !!! Regidx Rs9
                          = (mword_of_int 1024 : mword 64)) by lkp.
          assert (HG3sp : wi_sp m G3) by (rewrite /wi_sp; lkp).
          assert (Hpp : add_vec_int (mword_of_int (WI + 0x7c) : mword 64) 2
                        = mword_of_int (WI + 0x7e)) by pcw.
          iEval (rewrite Hpp) in "Hpc". clear Hpp.
          (* ---- the invariant, one chunk further on ---- *)
          set (wrote2 := (fun i : nat =>
                 if decide (i < tot)%nat then wroteI i else g (i - tot)%nat)).
          assert (Hrange3 : forall k : nat,
                    file_byte (<[fbn := wi_splice (data2 fbn) o mm g]> data2) k
                    = if decide ((off <= k)%nat /\ (k < off + (tot + mm))%nat)
                      then wrote2 (k - off)%nat else file_byte data k)
            by exact (wi_range_step data data2 off tot mm fbn o wroteI g
                        Hmmo Hdm Hrange2).
          assert (Hker3 : user = false -> forall i : nat, (i < tot + mm)%nat ->
                            wrote2 i = src_bytes i)
            by exact (wi_ker_step user src_bytes wroteI g tot mm HkerI Hgk).
          (* COVERAGE, one chunk further on: the chunk never leaves the block
             bmap just allocated, so every block below the new byte offset is
             allocated too *)
          assert (Hcov3 : bm_covers bm2 (Z.of_nat (off + (tot + mm))))
            by exact (wi_covers_step bmI bm2 off tot fbn o mm Hdm Hmmo Hgetnz
                        Hnoun2 HcovTI).
          (* ===== +0x7e bgeu s3,s6 : is the write finished? ===== *)
          destruct (Nat.leb_spec n (tot + mm)) as [Hfin | Hmore].
          * (* ---------- finished: leave the loop at +0xbc ---------- *)
            iApply (wp_bgeu_taken_s_sconf (mword_of_int (WI + 0x7e))
                      (mword_of_int 62 : mword 13) Rs6 Rs3 G3 (K - 14)%nat b
                      ltac:(nz) ltac:(nz)
                      ltac:(rgne; rgne; rewrite HG3s3 HG3s6;
                            rewrite (bc_ge_moi (tot + mm) n ltac:(lia) ltac:(lia));
                            apply Nat.leb_le; lia)
                      ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi7e").
            iApply bi.later_intro. iIntros (CIDc11 Hqc11) "Hcg Hpc".
            iClear "Hi68 Hi6a Hi6e Hi70 Hi74 Hi78 Hi7c Hi7e".
            assert (Htgtbc : add_vec (mword_of_int (WI + 0x7e) : mword 64)
                      (sign_extend' 64 (mword_of_int 62 : mword 13))
                    = mword_of_int (WI + 0xbc)) by pcw.
            iEval (rewrite Htgtbc) in "Hpc".
            (* the trailing iupdate always has its unit: the invariant reserves
               one past the straddled blocks, on EVERY exit *)
            destruct nL as [| uY];
              [exfalso; pose proof (wi_inv_bud_pos (ba_bms A) W 0%nat _ (proj1 Hinv3));
               lia|].
            iDestruct (cpu_own_transport CIDc7 CIDc11 0 eb (proc_addr j) b
                         ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
            iDestruct (IntrDefs.trap_csrs_ext_transport CIDa14 CIDc11 eb (proc_addr j)
                         ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
            iDestruct (IntrDefs.cpu_claim_ext_transport CIDa14 CIDc11 eb (proc_addr j)
                         ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
            (* ---- THE SIXTEEN-BYTE RECEIPT (GR-3 stage 3).  This is the
                   ONLY exit that can reach it with [0 < tot], and
                   [wi16_fresh] is what makes it derivable: nothing had
                   moved when the bmap call above ran, so its arm-wise
                   ledger is stated at the ENTRY count and the ENTRY set --
                   which is exactly what [wi16_spend]'s booleans name.  The
                   log_write's absorption is [wi_ad_of_alloced_any], i.e.
                   SpecBmap's clause (d) reached through clause (e). ---- *)
            assert (Hwi16B : wi16_pre (ba_bms A) ncount (S uY) off n (tot + mm)%nat
                               bm bm2 Sb
                               (Sb2 ∪ {[uint (blkmap_get bm2 fbn : mword 32)]})).
            { rewrite /wi16_pre. intros Hone.
              destruct (Hfresh Hone) as (Ht0 & Hbm0 & Hn0 & HS0).
              assert (Hfb0 : (off `div` BSIZE)%nat = fbn)
                by (rewrite Hfbne Ht0 Nat.add_0_r; reflexivity).
              cbv zeta. unfold wi_tgt_blk. rewrite Hfb0 -Hbm0 -HS0.
              assert (Hhon : (bmap_alloced bmI bm2 fbn
                              || bool_decide
                                   (uint (blkmap_get bm2 fbn : mword 32) ∈ SI))%bool
                             = true ->
                             bool_decide
                               (uint (blkmap_get bm2 fbn : mword 32) ∈ Sb2) = true).
              { intros Hor. apply bool_decide_eq_true_2.
                destruct (bmap_alloced bmI bm2 fbn) eqn:Hal.
                - rewrite Hubno. apply Hbc6.
                  exact (wi_ad_of_alloced_any cov logstart bmI bm2 fbn HwfI Hfbnlt
                           Hbnzz Hbc7 Hal).
                - cbn in Hor.
                  exact (wiset_in_mono _ SI Sb2 Hbc3
                           (proj1 (bool_decide_eq_true _) Hor)). }
              split_and!.
              - exact (wi16_spend_step ncount (S uX) (S uY)
                         (bmap_cost (bool_decide (ba_bms A ∈ SI))
                            (bmap_alloced bmI bm2 fbn) (bmap_ind fbn))
                         (bmap_alloced bmI bm2 fbn)
                         (bool_decide (uint (blkmap_get bm2 fbn : mword 32) ∈ SI))
                         (bool_decide (uint (blkmap_get bm2 fbn : mword 32) ∈ Sb2))
                         ltac:(lia) HnLlo Hhon).
              (* the single block was filled to the END of the range, which
                 is the [n] half of the granularity fact *)
              - right. lia.
              - intros _. split.
                + exact (wiset_in_sing_r _ _).
                + intros Ha. exact (wiset_in_add_r _ _ _ (Hbc5 Ha)). }
            iApply (wi_size (CID0 := CIDc11) γs j γl γu γd γk pd pav pu γfs γi bn γ γf
                      cov logstart inodestart nib dev ip inum bm bm2 data
                      (<[fbn := wi_splice (data2 fbn) o mm g]> data2) dn dn0
                      user off n (tot + mm)%nat src_bytes wrote2 0%nat wrote2
                      V P2 ncount uY
                      Sb (Sb2 ∪ {[uint (blkmap_get bm2 fbn : mword 32)]})
                      pidv dq dqd dqn dqs A m G3 K eb b lks
                      HK Hgeom0 Hist Hicov Hilog Hnib Hdtnz Hstab Hnlk Hwf2 Hhz3 HcovS2 Hcov3
                      Hszdn ltac:(lia)
                      ltac:(lia)
                      ltac:(intros Hs;
                            exact (wi_sized_step bmI data dataI data2 fbn o mm g
                                     Hdep2 HsizedI Hs))
                      Hj Hgl HG3sp HG3s5 HG3s2 HG3s3
                      ltac:(lia) ltac:(intros; reflexivity)
                      ltac:(intros; reflexivity)
                      (wi_range_dist0 data _ off (tot + mm)%nat wrote2 wrote2 Hrange3)
                      Hker3 ltac:(lia)
                      ltac:(exact (proj1 (wi_inv_exit (ba_bms A) ncount (S uY) uY
                                    (wi_blocks off n) W off n _
                                    ltac:(lia) eq_refl (proj2 Hinv3) ltac:(lia)
                                    ltac:(lia) ltac:(lia))))
                      ltac:(exact (proj2 (wi_inv_exit (ba_bms A) ncount (S uY) uY
                                    (wi_blocks off n) W off n _
                                    ltac:(lia) eq_refl (proj2 Hinv3) ltac:(lia)
                                    ltac:(lia) ltac:(lia))))
                      ltac:(lia) HsbSb3 Hwi16B Hext2 Hbelow
                      with "Hcg Hcnt Hextc Hextm Htext Hkdata Hpc Hpanenv Hbio Hlctx Hprocs Hdevi
                            Hdgeom Hdlock Hframe Hidev Hinum Hmeta
                            Hmap Hblocks Hsb Hba Hireg Hdn Hsrc Hsl Hop [Hcont]").
            iApply (wp_next_shift (b := true) (CIDa := CIDa14) (CIDb := CIDc11)
                      ltac:(wp_next_chain) with "Hcont").
          * (* ---------- another block: back to the head at +0x82 ------- *)
            iApply (wp_bgeu_fall_s_sconf (mword_of_int (WI + 0x7e))
                      (mword_of_int 62 : mword 13) Rs6 Rs3 G3 (K - 14)%nat b
                      ltac:(nz) ltac:(nz)
                      ltac:(rgne; rgne; rewrite HG3s3 HG3s6;
                            rewrite (bc_ge_moi (tot + mm) n ltac:(lia) ltac:(lia));
                            apply Nat.leb_gt; lia)
                      with "Hcg Hpc Hi7e").
            iIntros (CIDc11 Hqc11) "Hcg Hpc".
            iClear "Hi68 Hi6a Hi6e Hi70 Hi74 Hi78 Hi7c Hi7e".
            assert (Hpp : add_vec_int (mword_of_int (WI + 0x7e) : mword 64) 4
                          = mword_of_int (WI + 0x82)) by pcw.
            iEval (rewrite Hpp) in "Hpc". clear Hpp.
            (* the iteration filled its block to the boundary, so the fuel
               decreases by exactly one ([wi_blocks_step]) *)
            assert (Hboundary : mm = (BSIZE - o)%nat) by (rewrite Hmmd; lia).
            assert (Hstep : (wi_blocks (off + (tot + mm)) (n - (tot + mm)) + 1
                             <= wi_blocks (off + tot) (n - tot))%nat).
            { assert (Ho' : ((off + tot) `mod` BSIZE)%nat = o) by (rewrite Hoe; reflexivity).
              pose proof (wi_blocks_step (off + tot) (n - tot)%nat
                            ltac:(rewrite Ho'; lia)) as Hs.
              rewrite Ho' in Hs.
              replace (off + tot + (BSIZE - o))%nat with (off + (tot + mm))%nat in Hs
                by lia.
              replace (n - tot - (BSIZE - o))%nat with (n - (tot + mm))%nat in Hs
                by lia.
              exact Hs. }
            iDestruct (cpu_own_transport CIDc7 CIDc11 0 eb (proc_addr j) b
                         ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
            iDestruct (IntrDefs.trap_csrs_ext_transport CIDa14 CIDc11 eb (proc_addr j)
                         ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
            iDestruct (IntrDefs.cpu_claim_ext_transport CIDa14 CIDc11 eb (proc_addr j)
                         ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
            iDestruct (wp_next_shift (b := true) (CIDa := CIDa14) (CIDb := CIDc11)
                         ltac:(wp_next_chain) with "Hcont") as "Hcont".
            iApply (IH CIDc11 (tot + mm)%nat bm2
                      (<[fbn := wi_splice (data2 fbn) o mm g]> data2) wrote2 P2 nL
                      (Sb2 ∪ {[uint (blkmap_get bm2 fbn : mword 32)]}) G3
                      ltac:(lia) Hwf2 Hhz3
                      ltac:(intros Hs;
                            exact (wi_sized_step bmI data dataI data2 fbn o mm g
                                     Hdep2 HsizedI Hs))
                      HcovS2 Hcov3 Hrange3 Hker3 Hext2
                      ltac:(lia) (proj1 Hinv3) ltac:(lia) (proj2 Hinv3)
                      ltac:(lia) HsbSb3
                      (* THE BACK EDGE IS UNREACHABLE FOR A ONE-BLOCK WRITE:
                         [wi_blocks off n = 1] pins the entering fuel at one
                         ([HW5]), [Hstep] spends it, and [wi_blocks_pos] says
                         the remainder still needs some.  Re-establishing the
                         clause by refuting it is what keeps the multi-block
                         ledger untouched. *)
                      ltac:(intros Hone; exfalso;
                            pose proof (wi_blocks_pos (off + (tot + mm))%nat
                                          (n - (tot + mm))%nat ltac:(lia));
                            lia)
                      HG3sp HG3s5 HG3s7 HG3s4 HG3s2 HG3s6 HG3s3 HG3s9 HG3s8 Hprkc Hbelow
                      with "Hcg Hcnt Hextc Hextm Htext Hpc Hkdata Hprkenv Hbio Hlctx
                            Hkenv Hprocs
                            Hdevi Hdgeom Hdlock Hframe Hidev Hinum
                            Hmeta Hmap Hblocks Hsb Hba Hireg Hdn Hsrc Hsl Hop Hcont").

        + (* ====== THE COPY FAILED PART-WAY (kernel defect D1's fix) ======
             copyin has already memmove'd a PREFIX of the chunk into the
             buffer, so the buffer's bytes are no longer the block's logical
             content.  writei now calls log_write BEFORE brelse, which
             re-indexes the payload at those bytes -- which is exactly what
             makes [bio_locked], and hence brelse, available.  The sequence
             is the success arm's, verbatim, at the other pair of pcs; what
             differs is only the bookkeeping: [tot] is NOT advanced, and the
             chunk becomes the postcondition's DISTURBED REGION. *)
          iPoseProof (wri_b0 with "Htext") as "Hib0".
          iPoseProof (wri_b2 with "Htext") as "Hib2".
          iPoseProof (wri_b6 with "Htext") as "Hib6".
          iPoseProof (wri_b8 with "Htext") as "Hib8".
          iApply (wp_beq_taken_s_sconf (mword_of_int (WI + 0x64))
                    (mword_of_int 76 : mword 13) Rs8 Ra0 mE (K - 14)%nat b
                    ltac:(nz) ltac:(nz)
                    ltac:(rgne; rgne; rewrite Hrm1 HEs8; vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi64").
          iApply bi.later_intro. iIntros (CIDd1 Hqd1) "Hcg Hpc".
          iClear "Hi64".
          assert (Htgtb0 : add_vec (mword_of_int (WI + 0x64) : mword 64)
                    (sign_extend' 64 (mword_of_int 76 : mword 13))
                  = mword_of_int (WI + 0xb0)) by pcw.
          iEval (rewrite Htgtb0) in "Hpc".
          (* ===== +0xb0 c.mv a0,s1 ===== *)
          iApply (wp_cmv_s_sconf (mword_of_int (WI + 0xb0)) Ra0 Rs1
                    mE (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hib0").
          iIntros (CIDd2 Hqd2) "Hcg Hpc".
          set (J1 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64) (rget mE Rs1))]> mE).
          assert (HJ1a0 : J1 !!! Regidx Ra0 = bnode kkb).
          { rewrite /J1 upd_eq. rgne. rewrite HEs1. apply add_vec_zero_l. }
          assert (Hpp : add_vec_int (mword_of_int (WI + 0xb0) : mword 64) 2
                        = mword_of_int (WI + 0xb2)) by pcw.
          iEval (rewrite Hpp) in "Hpc". clear Hpp.
          (* ===== +0xb2 jal ra,log_write  -- THE FIX ===== *)
          iApply (wp_jal_s_sconf (mword_of_int (WI + 0xb2)) Rra
                    (mword_of_int 1690 : mword 21) J1 (K - 14)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hib2").
          iIntros (CIDd3 Hqd3) "Hcg Hpc".
          set (J2 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (WI + 0xb2) : mword 64) 4)]> J1).
          assert (Htgtlw : add_vec (mword_of_int (WI + 0xb2) : mword 64)
                             (sign_extend' 64 (mword_of_int 1690 : mword 21))
                           = mword_of_int KernelSyms.log_write) by pcw.
          iEval (rewrite Htgtlw) in "Hpc".
          assert (HJ2ra : J2 !!! Regidx Rra
                          = add_vec_int (mword_of_int (WI + 0xb2) : mword 64) 4)
            by (rewrite /J2; apply upd_eq).
          assert (HJ2a0 : J2 !!! Regidx Ra0 = bnode kkb) by lkp.
          assert (HJ2s1 : J2 !!! Regidx Rs1 = bnode kkb) by lkp.
          iDestruct (cpu_own_transport CIDb9 CIDd3 0 eb (proc_addr j) b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          assert (HKlw : (K_log_write <= K - 14)%nat) by (lia).
          iDestruct (wi_slots_split bn 1 1 with "Hsl2") as "[Hsla Hslb]".
          (* THE ABSORPTION, claimed as a decidable read of the op's set: if
             bmap just allocated this data block then balloc's [bzero]
             already logged it and this write is FREE.  The premise is
             discharged by the very bool_decide that names the credit. *)
          iApply (LW.wp_log_write_gen bn γ γfs γd cov logstart dev kkb pidv
                    (blkmap_get bm2 fbn) (wi_splice (data2 fbn) o mm g)
                    (data2 fbn) bsdB dB uX
                    (bool_decide (uint (blkmap_get bm2 fbn : mword 32) ∈ Sb2)) Sb2
                    J2 0%nat eb (proc_addr j) (K - 14)%nat b lks
                    HKlw ltac:(change (2 ^ 31)%Z with 2147483648%Z; lia)
                    Hkklt HJ2a0 Hbcovlw Hbloglw
                    ltac:(intros Hc; exact (proj1 (bool_decide_eq_true _) Hc))
                    Hbelow
                    with "Hcg Hcnt Htext Hpc Hbio Hlctx Hsla Hop Hfsb1 Hheld").
          all: try lkbelow.
          iIntros (CIDd4 Hqd4 mL) "Hcg Hcnt Hpc %HcsL Hop Hfsb1 Hheld Hsla".
          (* the count log_write left, as a variable: [S uX] when it absorbed,
             [uX] when it spent.  Naming it keeps the rest of this iteration
             free of the case split. *)
          remember (if bool_decide (uint (blkmap_get bm2 fbn : mword 32) ∈ Sb2)
                    then S uX else uX) as nL eqn:HnLdef.
          assert (HnLhi : (nL <= S uX)%nat)
            by (rewrite HnLdef; case_bool_decide; lia).
          assert (HnLlo : (S uX <= nL + (if bool_decide (uint (blkmap_get bm2 fbn : mword 32) ∈ Sb2)
                                         then 0 else 1))%nat)
            by (rewrite HnLdef; case_bool_decide; lia).
          (* THE WHOLE ITERATION against the accounting, bmap and this
             log_write together.  The allocating arm needs the absorption to
             have fired, and [wi_ad_of_alloced] is why it did: on the
             indirect path an allocating bmap allocated the DATA block too. *)
          assert (Hinv3 : wi_inv_bud (ba_bms A) W nL (Sb2 ∪ {[uint (blkmap_get bm2 fbn : mword 32)]})
                          /\ wi_inv_spent (ba_bms A) ncount nL
                               (wi_blocks off n) W (Sb2 ∪ {[uint (blkmap_get bm2 fbn : mword 32)]})).
          { destruct (bmap_alloced bmI bm2 fbn) eqn:Hal3.
            - (* THE ABSORPTION FIRED, and [wi_ad_of_alloced] is why *)
              assert (Hcrlw : true = true -> bmap_ind fbn = true ->
                              bool_decide (uint (blkmap_get bm2 fbn : mword 32) ∈ Sb2) = true).
              { intros _ Hind3. apply bool_decide_eq_true.
                (* bmap states clause (d) on [bv_unsigned], log_write's set on
                   [uint]; [Hubno] is the bridge, already in scope *)
                rewrite Hubno. apply Hbc6.
                exact (wi_ad_of_alloced cov logstart bmI bm2 fbn HwfI Hfbnlt
                         Hbnzz Hind3 Hal3). }
              assert (Hlo3 : (nI <= nL + 2 + bm_pot (ba_bms A) SI)%nat)
                by exact (wi_iter_alloc_bound (ba_bms A) nI (S uX) nL SI _
                            true (bmap_ind fbn) Hbc1 HnLlo Hcrlw).
              pose proof (wi_step_alloc (ba_bms A) ncount nI nL (wi_blocks off n)
                            (S W) SI (Sb2 ∪ {[uint (blkmap_get bm2 fbn : mword 32)]})
                            ltac:(lia) HW5 HW2 HW4
                            (wiset_sub_add_r SI Sb2 _ Hbc3)
                            (wiset_in_add_r _ Sb2 _ (Hbc5 eq_refl))
                            Hlo3 ltac:(lia)) as Hst3.
              replace (S W - 1)%nat with W in Hst3 by lia. exact Hst3.
            - assert (Hlo3 : (nI <= nL + 1)%nat)
                by exact (wi_iter_noalloc_bound (ba_bms A) nI (S uX) nL SI _
                            (bmap_ind fbn) Hbc1 HnLlo).
              pose proof (wi_step_noalloc (ba_bms A) ncount nI nL
                            (wi_blocks off n) (S W) SI (Sb2 ∪ {[uint (blkmap_get bm2 fbn : mword 32)]})
                            ltac:(lia) HW5 HW2 HW4
                            (wiset_sub_add_r SI Sb2 _ Hbc3)
                            Hlo3 ltac:(lia)) as Hst3.
              replace (S W - 1)%nat with W in Hst3 by lia. exact Hst3. }
          assert (HsbSb3 : Sb ⊆ Sb2 ∪ {[uint (blkmap_get bm2 fbn : mword 32)]})
            by (apply wiset_sub_add_r; exact HsbSb2).
          assert (Hpcb6 : ret_pc (J2 !!! Regidx Rra : mword 64)
                          = mword_of_int (WI + 0xb6)) by (rewrite HJ2ra; pcw).
          iEval (rewrite Hpcb6) in "Hpc".
          iDestruct (wi_slots_join bn 1 1 with "Hsla Hslb") as "Hsl2".
          pose proof HcsL as HcsLc.
          assert (HLsp : wi_sp m mL).
          { rewrite /wi_sp
              (callee_saved_lookup HcsLc csp_rs1 ltac:(vm_compute; reflexivity)).
            assert (HH : wi_sp m J2) by (rewrite /wi_sp; lkp). exact HH. }
          assert (HLs1 : mL !!! Regidx Rs1 = bnode kkb).
          { rewrite (callee_saved_lookup HcsLc Rs1 ltac:(vm_compute; reflexivity)).
            exact HJ2s1. }
          assert (HLs2 : mL !!! Regidx Rs2
                         = (mword_of_int (Z.of_nat (off + tot)) : mword 64)).
          { rewrite (callee_saved_lookup HcsLc Rs2 ltac:(vm_compute; reflexivity)).
            assert (HH : J2 !!! Regidx Rs2
                         = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp.
            exact HH. }
          assert (HLs3 : mL !!! Regidx Rs3
                         = (mword_of_int (Z.of_nat tot) : mword 64)).
          { rewrite (callee_saved_lookup HcsLc Rs3 ltac:(vm_compute; reflexivity)).
            assert (HH : J2 !!! Regidx Rs3
                         = (mword_of_int (Z.of_nat tot) : mword 64)) by lkp. exact HH. }
          assert (HLs5 : mL !!! Regidx Rs5 = ip).
          { rewrite (callee_saved_lookup HcsLc Rs5 ltac:(vm_compute; reflexivity)).
            assert (HH : J2 !!! Regidx Rs5 = ip) by lkp. exact HH. }
          (* ===== +0xb6 c.mv a0,s1 ===== *)
          iApply (wp_cmv_s_sconf (mword_of_int (WI + 0xb6)) Ra0 Rs1
                    mL (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hib6").
          iIntros (CIDd5 Hqd5) "Hcg Hpc".
          set (J3 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64) (rget mL Rs1))]> mL).
          assert (HJ3a0 : J3 !!! Regidx Ra0 = bnode kkb).
          { rewrite /J3 upd_eq. rgne. rewrite HLs1. apply add_vec_zero_l. }
          assert (Hpp : add_vec_int (mword_of_int (WI + 0xb6) : mword 64) 2
                        = mword_of_int (WI + 0xb8)) by pcw.
          iEval (rewrite Hpp) in "Hpc". clear Hpp.
          (* ===== +0xb8 jal ra,brelse ===== *)
          iApply (wp_jal_s_sconf (mword_of_int (WI + 0xb8)) Rra
                    (mword_of_int 2094316 : mword 21) J3 (K - 14)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hib8").
          iIntros (CIDd6 Hqd6) "Hcg Hpc".
          iClear "Hib0 Hib2 Hib6 Hib8".
          set (J4 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (WI + 0xb8) : mword 64) 4)]> J3).
          assert (Htgtbl : add_vec (mword_of_int (WI + 0xb8) : mword 64)
                             (sign_extend' 64 (mword_of_int 2094316 : mword 21))
                           = mword_of_int KernelSyms.brelse) by pcw.
          iEval (rewrite Htgtbl) in "Hpc".
          assert (HJ4ra : J4 !!! Regidx Rra
                          = add_vec_int (mword_of_int (WI + 0xb8) : mword 64) 4)
            by (rewrite /J4; apply upd_eq).
          assert (HJ4a0 : J4 !!! Regidx Ra0 = bnode kkb) by lkp.
          iDestruct (cpu_own_transport CIDd4 CIDd6 0 eb (proc_addr j) b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          assert (HKbl : (K_brelse <= K - 14)%nat) by (lia).
          (* the same borrow on the break arm *)
          iDestruct (wi_src_pid γf j pidv dq user (upd_upt V P2)
                       (m !!! Regidx Ra2 : mword 64) n src_bytes with "Hsrc")
            as "[Hppid Hsrcback]".
          iApply (BL.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) kkb
                    pidv dev (blkmap_get bm2 fbn) (wi_q user dq)
                    J4 (K - 14)%nat eb
                    (proc_addr j) (wi_splice (data2 fbn) o mm g) bsdB true b lks
                    HKbl Hkklt HJ4a0
                    ltac:(lkbelow)
                    with "Hcg Hcnt Htext Hpc Hbio Hppid Hprocs Hheld").
          all: try lkbelow.
          iIntros (CIDd7 Hqd7 mR) "%HcsR Hcg Hcnt Hpc Hppid Hsl1".
          iDestruct ("Hsrcback" with "Hppid") as "Hsrc".
          assert (Hpcbc : ret_pc (J4 !!! Regidx Rra : mword 64)
                          = mword_of_int (WI + 0xbc)) by (rewrite HJ4ra; pcw).
          iEval (rewrite Hpcbc) in "Hpc".
          iDestruct (wi_slots_join bn 2 1 with "Hsl2 Hsl1") as "Hsl".
          iEval (rewrite Hubno) in "Hfsb1".
          iDestruct ("Hblback" $! (wi_splice (data2 fbn) o mm g)
                       with "Hfsb1 Htok1") as "Hblocks".
          pose proof HcsR as HcsRc.
          assert (HRsp : wi_sp m mR).
          { rewrite /wi_sp
              (callee_saved_lookup HcsRc csp_rs1 ltac:(vm_compute; reflexivity)).
            assert (HH : wi_sp m J4) by (rewrite /wi_sp; lkp). exact HH. }
          assert (HRs2 : mR !!! Regidx Rs2
                         = (mword_of_int (Z.of_nat (off + tot)) : mword 64)).
          { rewrite (callee_saved_lookup HcsRc Rs2 ltac:(vm_compute; reflexivity)).
            assert (HH : J4 !!! Regidx Rs2
                         = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp.
            exact HH. }
          assert (HRs3 : mR !!! Regidx Rs3
                         = (mword_of_int (Z.of_nat tot) : mword 64)).
          { rewrite (callee_saved_lookup HcsRc Rs3 ltac:(vm_compute; reflexivity)).
            assert (HH : J4 !!! Regidx Rs3
                         = (mword_of_int (Z.of_nat tot) : mword 64)) by lkp. exact HH. }
          assert (HRs5 : mR !!! Regidx Rs5 = ip).
          { rewrite (callee_saved_lookup HcsRc Rs5 ltac:(vm_compute; reflexivity)).
            assert (HH : J4 !!! Regidx Rs5 = ip) by lkp. exact HH. }
          destruct nL as [| uY];
            [exfalso; pose proof (wi_inv_bud_pos (ba_bms A) W 0%nat _ (proj1 Hinv3));
             lia|].
          iDestruct (cpu_own_transport CIDd7 CIDd7 0 eb (proc_addr j) b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          iDestruct (IntrDefs.trap_csrs_ext_transport CIDa14 CIDd7 eb (proc_addr j)
                       ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
          iDestruct (IntrDefs.cpu_claim_ext_transport CIDa14 CIDd7 eb (proc_addr j)
                       ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
          (* ---- THE RECEIPT ON THE COPY BREAK.  [tot] did NOT advance, so
                 the two memberships are vacuous -- but THE SPEND IS THE
                 SUCCESS ARM'S VERBATIM, because [log_write(bp)] ran BEFORE
                 the break (the fs.c fix; see this file's header), and that
                 log_write is exactly the term [wi16_spend] charges for the
                 target block.  This is the arm that makes
                 [SpecWritei.wi16_spend_any] true at [tot = 0] rather than
                 merely vacuous, and it is [wi16_fresh] again that lets the
                 booleans be read at the ENTRY count and set. ---- *)
          assert (Hwi16C : wi16_pre (ba_bms A) ncount (S uY) off n tot
                             bm bm2 Sb
                             (Sb2 ∪ {[uint (blkmap_get bm2 fbn : mword 32)]})).
          { rewrite /wi16_pre. intros Hone.
            destruct (Hfresh Hone) as (Ht0 & Hbm0 & Hn0 & HS0).
            assert (Hfb0 : (off `div` BSIZE)%nat = fbn)
              by (rewrite Hfbne Ht0 Nat.add_0_r; reflexivity).
            cbv zeta. unfold wi_tgt_blk. rewrite Hfb0 -Hbm0 -HS0.
            assert (Hhon : (bmap_alloced bmI bm2 fbn
                            || bool_decide
                                 (uint (blkmap_get bm2 fbn : mword 32) ∈ SI))%bool
                           = true ->
                           bool_decide
                             (uint (blkmap_get bm2 fbn : mword 32) ∈ Sb2) = true).
            { intros Hor. apply bool_decide_eq_true_2.
              destruct (bmap_alloced bmI bm2 fbn) eqn:Hal.
              - rewrite Hubno. apply Hbc6.
                exact (wi_ad_of_alloced_any cov logstart bmI bm2 fbn HwfI Hfbnlt
                         Hbnzz Hbc7 Hal).
              - cbn in Hor.
                exact (wiset_in_mono _ SI Sb2 Hbc3
                         (proj1 (bool_decide_eq_true _) Hor)). }
            split_and!.
            - exact (wi16_spend_step ncount (S uX) (S uY)
                       (bmap_cost (bool_decide (ba_bms A ∈ SI))
                          (bmap_alloced bmI bm2 fbn) (bmap_ind fbn))
                       (bmap_alloced bmI bm2 fbn)
                       (bool_decide (uint (blkmap_get bm2 fbn : mword 32) ∈ SI))
                       (bool_decide (uint (blkmap_get bm2 fbn : mword 32) ∈ Sb2))
                       ltac:(lia) HnLlo Hhon).
            - left. exact Ht0.
            - intros Hpos. exfalso. lia. }
          iApply (wi_size (CID0 := CIDd7) γs j γl γu γd γk pd pav pu γfs γi bn γ γf
                    cov logstart inodestart nib dev ip inum bm bm2 data
                    (<[fbn := wi_splice (data2 fbn) o mm g]> data2) dn dn0
                    user off n tot src_bytes wroteI mm g V P2 ncount uY
                    Sb (Sb2 ∪ {[uint (blkmap_get bm2 fbn : mword 32)]})
                    pidv dq dqd dqn dqs A m mR K eb b lks
                    HK Hgeom0 Hist Hicov Hilog Hnib Hdtnz Hstab Hnlk Hwf2 Hhz3 HcovS2 HcovT2
                    Hszdn ltac:(lia)
                    ltac:(lia)
                    ltac:(intros Hs;
                          exact (wi_sized_step bmI data dataI data2 fbn o mm g
                                   Hdep2 HsizedI Hs))
                    Hj Hgl HRsp HRs5 HRs2 HRs3
                    ltac:(rewrite Hbsz in Hmmo |- *; lia)
                    ltac:(intros Heq; exfalso; lia)
                    (* THE KERNEL ARM CANNOT BE HERE: either_copyin returned
                       -1, which its post allows only when [user] (§15.1(i)) *)
                    ltac:(intros Heq; exfalso; rewrite Heq in Huser; discriminate)
                    (wi_range_fail data data2 off tot mm fbn o wroteI g
                       Hmmo Hdm Hrange2)
                    HkerI ltac:(lia)
                    ltac:(exact (proj1 (wi_inv_exit (ba_bms A) ncount (S uY) uY
                                  (wi_blocks off n) W off n _
                                  ltac:(lia) eq_refl (proj2 Hinv3) ltac:(lia)
                                  ltac:(lia) ltac:(lia))))
                    ltac:(exact (proj2 (wi_inv_exit (ba_bms A) ncount (S uY) uY
                                  (wi_blocks off n) W off n _
                                  ltac:(lia) eq_refl (proj2 Hinv3) ltac:(lia)
                                  ltac:(lia) ltac:(lia))))
                    ltac:(lia) HsbSb3 Hwi16C
                    Hext2 Hbelow
                    with "Hcg Hcnt Hextc Hextm Htext Hkdata Hpc Hpanenv Hbio Hlctx Hprocs Hdevi
                          Hdgeom Hdlock Hframe Hidev Hinum Hmeta
                          Hmap Hblocks Hsb Hba Hireg Hdn Hsrc Hsl Hop [Hcont]").
          iApply (wp_next_shift (b := true) (CIDa := CIDa14) (CIDb := CIDd7)
                    ltac:(wp_next_chain) with "Hcont").
      }
      (* ===== +0xa8 bgeu a3,a4 : m = min(n - tot, BSIZE - off%BSIZE) ===== *)
      assert (HE5a5 : E5 !!! Regidx Ra5
                      = (mword_of_int (Z.of_nat o) : mword 64)) by lkp.
      assert (HE5s1 : E5 !!! Regidx Rs1 = bnode kkb) by lkp.
      assert (HE5a3 : E5 !!! Regidx Ra3
                      = (mword_of_int (Z.of_nat (n - tot)) : mword 64)) by lkp.
      assert (HE5a4 : E5 !!! Regidx Ra4
                      = (mword_of_int (Z.of_nat (BSIZE - o)) : mword 64)) by lkp.
      assert (HE5sp : wi_sp m E5) by (rewrite /wi_sp; lkp).
      assert (HE5s2 : E5 !!! Regidx Rs2
                      = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp.
      assert (HE5s3 : E5 !!! Regidx Rs3
                      = (mword_of_int (Z.of_nat tot) : mword 64)) by lkp.
      assert (HE5s4 : E5 !!! Regidx Rs4
                      = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp.
      assert (HE5s5 : E5 !!! Regidx Rs5 = ip) by lkp.
      assert (HE5s6 : E5 !!! Regidx Rs6
                      = (mword_of_int (Z.of_nat n) : mword 64)) by lkp.
      assert (HE5s7 : E5 !!! Regidx Rs7 = usv) by lkp.
      assert (HE5s8 : E5 !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)) by lkp.
      assert (HE5s9 : E5 !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)) by lkp.
      destruct (Nat.leb_spec (BSIZE - o) (n - tot)) as [Hfill | Hlast].
      + (* the chunk fills the block to the boundary: s10 already holds it *)
        iApply (wp_bgeu_taken_s_sconf (mword_of_int (WI + 0xa8))
                  (mword_of_int 8100 : mword 13) Ra4 Ra3 E5 (K - 14)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HE5a3 HE5a4;
                        rewrite (bc_ge_moi (n - tot) (BSIZE - o) ltac:(lia) ltac:(lia));
                        apply Nat.leb_le; lia)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hia8").
        iApply bi.later_intro. iIntros (CIDa15 Hqa15) "Hcg Hpc".
        iClear "Hia8 Hiac Hiae".
        assert (Htgt4c : add_vec (mword_of_int (WI + 0xa8) : mword 64)
                  (sign_extend' 64 (mword_of_int 8100 : mword 13))
                = mword_of_int (WI + 0x4c)) by pcw.
        iEval (rewrite Htgt4c) in "Hpc".
        iApply ("BODY" $! CIDa15 E5 (BSIZE - o)%nat with
                  "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hpc");
          [ wp_next_chain | lia | exact HE5sp | exact HE5s10 | exact HE5a5
          | exact HE5s1 | exact HE5s4 | exact HE5s7 | exact HE5s5 | exact HE5s2
          | exact HE5s6 | exact HE5s3 | exact HE5s9 | exact HE5s8 ].
      + (* the last chunk: s10 := a3 = n - tot *)
        iApply (wp_bgeu_fall_s_sconf (mword_of_int (WI + 0xa8))
                  (mword_of_int 8100 : mword 13) Ra4 Ra3 E5 (K - 14)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HE5a3 HE5a4;
                        rewrite (bc_ge_moi (n - tot) (BSIZE - o) ltac:(lia) ltac:(lia));
                        apply Nat.leb_gt; lia)
                  with "Hcg Hpc Hia8").
        iIntros (CIDa15 Hqa15) "Hcg Hpc".
        assert (Hpp : add_vec_int (mword_of_int (WI + 0xa8) : mword 64) 4
                      = mword_of_int (WI + 0xac)) by pcw.
        iEval (rewrite Hpp) in "Hpc". clear Hpp.
        (* ===== +0xac c.mv s10,a3 ===== *)
        iApply (wp_cmv_s_sconf (mword_of_int (WI + 0xac)) Rs10 Ra3
                  E5 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hiac").
        iIntros (CIDa16 Hqa16) "Hcg Hpc".
        set (E6 := <[Regidx Rs10 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (rget E5 Ra3))]> E5).
        assert (HE6s10 : E6 !!! Regidx Rs10
                         = (mword_of_int (Z.of_nat (n - tot)) : mword 64)).
        { rewrite /E6 upd_eq. rgne. rewrite HE5a3. apply add_vec_zero_l. }
        assert (Hpp : add_vec_int (mword_of_int (WI + 0xac) : mword 64) 2
                      = mword_of_int (WI + 0xae)) by pcw.
        iEval (rewrite Hpp) in "Hpc". clear Hpp.
        (* ===== +0xae c.j +0x4c ===== *)
        iApply (wp_cj_s_sconf (mword_of_int (WI + 0xae))
                  (sign_extend' 21 (concat_vec (mword_of_int 1999 : mword 11) ('b"0")))
                  E6 (K - 14)%nat b ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hiae").
        iIntros (CIDa17 Hqa17). iApply bi.later_intro. iIntros "Hcg Hpc".
        iClear "Hia8 Hiac Hiae".
        assert (Htgt4c : add_vec (mword_of_int (WI + 0xae) : mword 64)
                  (sign_extend' 64 (sign_extend' 21
                     (concat_vec (mword_of_int 1999 : mword 11) ('b"0"))))
                = mword_of_int (WI + 0x4c)) by pcw.
        iEval (rewrite Htgt4c) in "Hpc".
        assert (HE6a5 : E6 !!! Regidx Ra5
                        = (mword_of_int (Z.of_nat o) : mword 64)) by lkp.
        assert (HE6s1 : E6 !!! Regidx Rs1 = bnode kkb) by lkp.
        assert (HE6sp : wi_sp m E6) by (rewrite /wi_sp; lkp).
        assert (HE6s2 : E6 !!! Regidx Rs2
                        = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp.
        assert (HE6s3 : E6 !!! Regidx Rs3
                        = (mword_of_int (Z.of_nat tot) : mword 64)) by lkp.
        assert (HE6s4 : E6 !!! Regidx Rs4
                        = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp.
        assert (HE6s5 : E6 !!! Regidx Rs5 = ip) by lkp.
        assert (HE6s6 : E6 !!! Regidx Rs6
                        = (mword_of_int (Z.of_nat n) : mword 64)) by lkp.
        assert (HE6s7 : E6 !!! Regidx Rs7 = usv) by lkp.
        assert (HE6s8 : E6 !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)) by lkp.
        assert (HE6s9 : E6 !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)) by lkp.
        iApply ("BODY" $! CIDa17 E6 (n - tot)%nat with
                  "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hpc");
          [ wp_next_chain | lia | exact HE6sp | exact HE6s10 | exact HE6a5
          | exact HE6s1 | exact HE6s4 | exact HE6s7 | exact HE6s5 | exact HE6s2
          | exact HE6s6 | exact HE6s3 | exact HE6s9 | exact HE6s8 ].
  Qed.

End WriteiLoop.

(* ===================================================================== *)
(*  +0x00 .. +0x4a : the prologue, the three -1 exits and the n = 0 arm.  *)
(* ===================================================================== *)
Section WriteiMain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the CALLER's buffer tier -- see this function's spec for why it is not
     [KT1].  A KtierLe HYPOTHESIS in the section beats [ktier_le_refl] at
     instance search, so every OTHER leaf in this file has to name its own
     datum tier out loud (the blanket [(ktd := KT1)] below). *)
  Context {ktb : ktier}.
  Context `{!KtierLe ktb KT1}.
  Local Ltac reg_neq := vm_compute; discriminate.
  Local Ltac lkp :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | rgne
      | match goal with |- context [ ?M !!! _ ] => is_var M; progress unfold M end ];
    repeat rewrite add_vec_zero_l;
    first [ reflexivity | assumption ].

  (* THE CORE, in SET FORM (fs-icache.md section 18 clause 1).
     [wp_writei_sconf] below is this with the set forgotten. *)
  Lemma wp_writei_gen
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (γa : gname) (γf : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (bmapstart : Z) (size : Z) (dev : mword 32)
      (used : gset Z) (γpr : gname)
      (ip : mword 64) (inum : mword 32)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn dn0 : dinode)
      (user : bool) (off n : nat) (src_bytes : nat -> bv 8)
      (V : pprivate) (ncount : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqd dqn dqs dqb dqbs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
    : wp_writei_gen_body ktb γs j γl γu γd γk pd pav pu bn γ γfs γi γa γf
                         cov logstart inodestart nib bmapstart size dev used γpr
                         ip inum bm data dn dn0
                         user off n src_bytes V ncount Sb
                         pidv dq dqd dqn dqs dqb dqbs m K eb b lks.
  Proof.
    cbv beta delta [wp_writei_gen_body].
    intros pcE pj src ret_tgt HK Hcost Hgeom Hist Hicov Hilog Hnib Hadr Hdtnz Hstab Hnlk
           Hwf Hhz Hcovin Hsum Hszdn Hgok Hprkc Hj Hgl Ha0 Ha1 Ha3 Ha4 Hbelow.
    (* the whole allocation side travels as ONE record from here down *)
    set (A := MkBmAlloc γ bmapstart size used dqb dqbs γpr).
    pose proof HK as HK'. 
    change (2 ^ 31)%Z with 2147483648%Z in Hsum, Hszdn.
    assert (Hofflt : (Z.of_nat off < 2147483648)%Z) by lia.
    assert (Hnlt : (Z.of_nat n < 2147483648)%Z) by lia.
    assert (Hgeom0 : log_geom_ok cov logstart) by exact Hgeom.
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hkdata #Hprkenv #Hbio #Hlctx #Hkenv
              Hidev Hinum
              Hmeta Hmap Hblocks Hsb Hszc Hbmsc Hbmres #Hireg Hdn Hsrc
              #Hprocs #Hdevi #Hdgeom #Hdlock Hsl Hop Hcont".
    iPoseProof (SpecPrintk.printk_env_panic with "Hprkenv") as "#Hpanenv".
    iDestruct (CpuOwn.cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    iAssert (bm_alloc_res γfs cov logstart A) with "[Hszc Hbmsc Hbmres]" as "Hba".
    { rewrite /bm_alloc_res /A. iSplitR; [iPureIntro; exact Hgok|].
      iFrame "Hszc Hbmsc".
      iApply (bm_bitmap_intro γfs cov logstart bmapstart size used used
                (reflexivity used) with "Hbmres"). }
    (* THE ADAPTER, and the only place the two shapes meet: the public
       contract quantifies the bitmap's FINAL set with [used ⊆ used'], while
       everything below carries the bundle at the fixed entry index.  Written
       once here rather than at every interior continuation. *)
    iAssert (wi_cont (ktb := ktb) (CID0 := CID) γfs γi bn γ γf cov logstart inodestart nib dev
               ip inum bm data dn dn0 user off n src_bytes V ncount Sb
               pidv dq dqd dqn dqs A j m K eb b lks)%I with "[Hcont]" as "Hcont".
    { rewrite /wi_cont. iEval (rewrite /wp_next).
      iIntros (CIDf) "%Hchain".
      iIntros (mf tot bm2 data2 dn2 dn02 n2 wrote dist dstb P2 SbF)
        "%C1 %C2 %C3 %C4 %C5 %C6 %Ccap %Csz %C7 %C8 %C8k %C9 %C10 %C11 %C12 %Csb
         %Cwi %Cwiany %Cwiat %C13
         Hcg Hcnt Hextc Hextm Hpc Hidev Hinum Hmeta Hmap Hblocks Hsb
         Hba Hdn Hsrc Hsl Hop".
      iDestruct "Hba" as "(%Hgok2 & Hszc & Hbmsc & Hbmg)".
      iDestruct "Hbmg" as (uOut) "[%HuOut Hbmres]".
      iSpecialize ("Hcont" $! CIDf with "[%]"); [exact Hchain|].
      iApply ("Hcont" $! mf tot bm2 data2 dn2 dn02 n2 wrote dist dstb P2 uOut SbF
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                      [%] [%] [%] [%] [%] [%]
                      Hcg Hcnt Hextc Hextm Hpc Hidev Hinum Hmeta Hmap
                      Hblocks Hsb Hszc Hbmsc Hbmres Hdn Hsrc Hsl Hop").
      { exact C1. } { exact HuOut. } { exact C2. } { exact C3. }
      { exact C4. } { exact C5. } { exact C6. }
      { exact Ccap. } { exact Csz. } { exact C7. } { exact C8. }
      { exact C8k. }
      { exact C9. } { exact C10. } { exact C11. } { exact C12. }
      { exact Csb. }
      { exact Cwi. }
      { exact Cwiany. }
      { exact Cwiat. }
      { exact C13. } }
    iPoseProof (wri_00 with "Htext") as "Hi00".
    iPoseProof (wri_02 with "Htext") as "Hi02".
    iPoseProof (wri_06 with "Htext") as "Hi06".
    iPoseProof (wri_08 with "Htext") as "Hi08".
    iPoseProof (wri_0a with "Htext") as "Hi0a".
    iPoseProof (wri_0c with "Htext") as "Hi0c".
    iPoseProof (wri_0e with "Htext") as "Hi0e".
    iPoseProof (wri_10 with "Htext") as "Hi10".
    iPoseProof (wri_12 with "Htext") as "Hi12".
    iPoseProof (wri_14 with "Htext") as "Hi14".
    iPoseProof (wri_16 with "Htext") as "Hi16".
    iPoseProof (wri_18 with "Htext") as "Hi18".
    iPoseProof (wri_1a with "Htext") as "Hi1a".
    iPoseProof (wri_1c with "Htext") as "Hi1c".
    iPoseProof (wri_1e with "Htext") as "Hi1e".
    iPoseProof (wri_20 with "Htext") as "Hi20".
    iPoseProof (wri_22 with "Htext") as "Hi22".
    iPoseProof (wri_26 with "Htext") as "Hi26".
    iPoseProof (wri_2a with "Htext") as "Hi2a".
    iPoseProof (wri_2e with "Htext") as "Hi2e".
    iPoseProof (wri_32 with "Htext") as "Hi32".
    iPoseProof (wri_34 with "Htext") as "Hi34".
    iPoseProof (wri_38 with "Htext") as "Hi38".
    iPoseProof (wri_3a with "Htext") as "Hi3a".
    iPoseProof (wri_3c with "Htext") as "Hi3c".
    iPoseProof (wri_3e with "Htext") as "Hi3e".
    iPoseProof (wri_40 with "Htext") as "Hi40".
    iPoseProof (wri_42 with "Htext") as "Hi42".
    iPoseProof (wri_44 with "Htext") as "Hi44".
    iPoseProof (wri_48 with "Htext") as "Hi48".
    iPoseProof (wri_4a with "Htext") as "Hi4a".
    iPoseProof (wri_ee with "Htext") as "Hiee".
    iPoseProof (wri_f0 with "Htext") as "Hif0".
    iPoseProof (wri_fe with "Htext") as "Hife".
    iPoseProof (wri_100 with "Htext") as "Hi100".
    iPoseProof (wri_102 with "Htext") as "Hi102".
    iPoseProof (wri_104 with "Htext") as "Hi104".
    rewrite /inode_meta.
    iDestruct "Hmeta" as "(Hmt & Hmj & Hmn & Hml & Hmz)".
    (* ===== +0x00 c.lw a5,76(a0) : a5 := ip->size ===== *)
    assert (Hszadr : add_vec (rget m Ra0) (sign_extend' 64 (mword_of_int 76 : mword 12))
                     = i_size ip) by (rgne; rewrite Ha0; reflexivity).
    iEval (rewrite -Hszadr) in "Hmz".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) pcE Ra5 Ra0 (mword_of_int 76 : mword 12)
              m K (di_size dn : mword 32) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi00 Hmz").
    iIntros (CIDp0 Hqp0) "Hcg Hpc Hmz".
    iEval (rewrite Hszadr) in "Hmz".
    set (Q0 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (di_size dn : mword 32))]> m).
    assert (HQ0a5 : Q0 !!! Regidx Ra5
                    = (sign_extend' 64 (di_size dn : mword 32) : mword 64))
      by (rewrite /Q0; apply upd_eq).
    assert (HQ0a3 : Q0 !!! Regidx Ra3
                    = (mword_of_int (Z.of_nat off) : mword 64)) by lkp.
    assert (Hszu : bv_unsigned (sign_extend' 64 (di_size dn : mword 32) : mword 64)
                   = bv_unsigned (di_size dn))
      by (apply wi_sext32_unsigned; exact Hszdn).
    assert (Hoffu : bv_unsigned (mword_of_int (Z.of_nat off) : mword 64)
                    = Z.of_nat off) by (apply wi_nat_u; lia).
    assert (Hpp : add_vec_int pcE 2 = mword_of_int (WI + 0x2)) by (rewrite /pcE; pcw).
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x02 bltu a5,a3 : off > ip->size ? ===== *)
    destruct (Z_lt_le_dec (bv_unsigned (di_size dn)) (Z.of_nat off)) as [Hsml | Hbig].
    { (* ---- THE PRE-FRAME EXIT: li a0,-1; ret, with no frame at all ---- *)
      iApply (wp_bltu_taken_s_sconf (mword_of_int (WI + 0x2))
                (mword_of_int 252 : mword 13) Ra3 Ra5 Q0 K b ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HQ0a5 HQ0a3;
                      rewrite (wi_ltu_read _ _ _ _ Hszu Hoffu);
                      apply Z.ltb_lt; exact Hsml)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi02").
      iApply bi.later_intro. iIntros (CIDx1 Hqx1) "Hcg Hpc".
      assert (Htgt : add_vec (mword_of_int (WI + 0x2) : mword 64)
                (sign_extend' 64 (mword_of_int 252 : mword 13))
              = mword_of_int (WI + 0xfe)) by pcw.
      iEval (rewrite Htgt) in "Hpc".
      (* ===== +0xfe c.li a0,-1 ===== *)
      iApply (wp_cli_s_sconf (mword_of_int (WI + 0xfe)) Ra0
                (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                Q0 K b ltac:(nz) ltac:(rdok) wi_li_m1 with "Hcg Hpc Hife").
      iIntros (CIDx2 Hqx2) "Hcg Hpc".
      set (X1 := <[Regidx Ra0 := regval_into_reg
                    (mword_of_int (-1) : mword 64)]> Q0).
      assert (Hpp : add_vec_int (mword_of_int (WI + 0xfe) : mword 64) 2
                    = mword_of_int (WI + 0x100)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x100 c.ret ===== *)
      assert (HX1ra : X1 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)) by lkp.
      iApply (wp_cret_s_sconf (mword_of_int (WI + 0x100)) Rra X1 K b ltac:(nz)
                with "Hcg Hpc Hi100").
      iIntros (CIDx3 Hqx3) "Hcg Hpc".
      iEval (rgne) in "Hpc".
      assert (Hretf : ret_pc (X1 !!! Regidx Rra : mword 64)
                      = ret_pc (m !!! Regidx Rra : mword 64))
        by (rewrite HX1ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      iAssert (inode_meta ip dn) with "[Hmt Hmj Hmn Hml Hmz]" as "Hmeta".
      { rewrite /inode_meta.
        iSplitL "Hmt"; [iExact "Hmt"|]. iSplitL "Hmj"; [iExact "Hmj"|].
        iSplitL "Hmn"; [iExact "Hmn"|]. iSplitL "Hml"; [iExact "Hml"|].
        iExact "Hmz". }
      assert (HVid : upd_upt V (pv_upt V) = V) by apply wi_upd_upt_id.
      iDestruct (cpu_own_transport CID CIDx3 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (IntrDefs.trap_csrs_ext_transport CID CIDx3 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (IntrDefs.cpu_claim_ext_transport CID CIDx3 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
      rewrite /wi_cont.
      iSpecialize ("Hcont" $! CIDx3 with "[%]"); [wp_next_chain|].
      (* the -1 arm returns before anything is logged, so the op's set is
         the one it came in with *)
      iApply ("Hcont" $! X1 0%nat bm data dn dn0 ncount
                (fun _ => bv_0 8) 0%nat (fun _ => bv_0 8) (pv_upt V) Sb
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hcnt Hextc Hextm Hpc Hidev Hinum Hmeta Hmap Hblocks Hsb Hba Hdn
                      [Hsrc] Hsl Hop").
      { unfold callee_saved. split_and!; lkp. }
      { exact Hwf. }
      { exact Hhz. }
      { exact Hadr. }
      { exact Hszdn. }
      { exact Hcovin. }
      { intros Hc. exact Hc. }
      { intros Hc. exact Hc. }
      { unfold BSIZE. lia. }
      { reflexivity. }
      { reflexivity. }
      { intro k. rewrite decide_False; [| lia]. rewrite decide_False; [| lia].
        reflexivity. }
      { intros _ i Hi. exfalso. lia. }
      { left. split_and!;
          [ lkp | left; exact Hsml | reflexivity | reflexivity | reflexivity
          | reflexivity | reflexivity | reflexivity | reflexivity ]. }
      { split; lia. }
      { (* nothing was logged on the -1 arm: the set is the entry set *)
        reflexivity. }
      { (* ...and tot = 0, so the sixteen-byte clause is vacuous *)
        unfold wi16_post. intros Hpos. exfalso. lia. }
      { (* the unguarded spend: this exit is BEFORE the prologue and spends
           nothing at all, so the bound is loose by the whole figure *)
        unfold wi16_spend_any. intros _. lia. }
      { (* ...and it wrote nothing, which is the [tot = 0] half *)
        unfold wi16_atomic. intros _. left. reflexivity. }
      { apply uptd_ext_refl. }
      { rewrite HVid. iExact "Hsrc". }
    }

    (* ---- everything past this point holds the source at [upd_upt V P]
       with [P = pv_upt V], which is the shape both the loop and the two
       framed exits take ---- *)
    assert (HVid : upd_upt V (pv_upt V) = V) by apply wi_upd_upt_id.
    iAssert (if user
             then proc_priv_core (proc_addr j) pidv (upd_upt V (pv_upt V))
             else ([∗ list] i ∈ seq 0 n,
                     pa_add (m !!! Regidx Ra2 : mword 64) i ↦ₘ[ktb] (src_bytes i))
                  ∗ p_pid (proc_addr j) ↦₄{dq} pidv)%I
      with "[Hsrc]" as "Hsrc"; [rewrite HVid; iExact "Hsrc"|].
    iAssert (inode_meta ip dn) with "[Hmt Hmj Hmn Hml Hmz]" as "Hmeta".
    { rewrite /inode_meta.
      iSplitL "Hmt"; [iExact "Hmt"|]. iSplitL "Hmj"; [iExact "Hmj"|].
      iSplitL "Hmn"; [iExact "Hmn"|]. iSplitL "Hml"; [iExact "Hml"|].
      iExact "Hmz". }
    iApply (wp_bltu_fall_s_sconf (mword_of_int (WI + 0x2))
              (mword_of_int 252 : mword 13) Ra3 Ra5 Q0 K b ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HQ0a5 HQ0a3;
                    rewrite (wi_ltu_read _ _ _ _ Hszu Hoffu);
                    apply Z.ltb_ge; exact Hbig)
              with "Hcg Hpc Hi02").
    iIntros (CIDp1 Hqp1) "Hcg Hpc".
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x2) : mword 64) 4
                  = mword_of_int (WI + 0x6)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x06 c.addi16sp sp,-112 : the 14-slot frame ===== *)
    assert (HQ0sp : Q0 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64))
      by lkp.
    assert (Hpush : add_vec (Q0 !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 57 : mword 6)))
                    = pa_stk (Q0 !!! Regidx csp_rs1 : mword 64) 14).
    { unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int (WI + 0x6))
              (mword_of_int 57 : mword 6) Q0 K 14 b ltac:(lia) Hpush
              with "Hcg Hpc Hi06").
    iIntros (CIDp2 Hqp2) "Hcg Hstk Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (Q0 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 57 : mword 6))))]> Q0).
    assert (HR1sp : wi_sp m R1).
    { rewrite /wi_sp /R1 upd_eq HQ0sp. reflexivity. }
    iEval (rewrite HQ0sp) in "Hstk".
    iEval (rewrite (stack_own_slots (KTR := KT1))) in "Hstk".
    iEval (cbn [seq]) in "Hstk".
    iDestruct "Hstk" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9
                          & HfA & HfB & HfC & HfD & HfE & _)".
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x6) : mword 64) 2
                  = mword_of_int (WI + 0x8)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x08 sd Rra,104(sp) ===== *)
    iDestruct "Hf1" as (w1) "Hf1".
    assert (Hc1 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc1) in "Hf1".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0x08)) (mword_of_int 13 : mword 6) Rra
              R1 (K - 14)%nat w1 b with "Hcg Hpc Hi08 Hf1").
    iIntros (CIDs1 Hqs1) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    assert (Hv1 : rget R1 Rra = (m !!! Regidx Rra : mword 64)) by (rgne; lkp).
    assert (Hw1 : (R1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64)) by lkp.
    first [ iEval (rewrite Hw1) in "Hf1"
          | iEval (rewrite Hv1) in "Hf1"
          | iEval (rgne; rewrite Hw1) in "Hf1" ].
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x08) : mword 64) 2
                  = mword_of_int (WI + 0x0a)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x0a sd Rs0,96(sp) ===== *)
    iDestruct "Hf2" as (w2) "Hf2".
    assert (Hc2 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc2) in "Hf2".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0x0a)) (mword_of_int 12 : mword 6) Rs0
              R1 (K - 14)%nat w2 b with "Hcg Hpc Hi0a Hf2").
    iIntros (CIDs2 Hqs2) "Hcg Hpc Hf2".
    iEval (rewrite Hc2) in "Hf2".
    assert (Hv2 : rget R1 Rs0 = (m !!! Regidx Rs0 : mword 64)) by (rgne; lkp).
    assert (Hw2 : (R1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64)) by lkp.
    first [ iEval (rewrite Hw2) in "Hf2"
          | iEval (rewrite Hv2) in "Hf2"
          | iEval (rgne; rewrite Hw2) in "Hf2" ].
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x0a) : mword 64) 2
                  = mword_of_int (WI + 0x0c)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x0c sd Rs2,80(sp) ===== *)
    iDestruct "Hf4" as (w4) "Hf4".
    assert (Hc4 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc4) in "Hf4".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0x0c)) (mword_of_int 10 : mword 6) Rs2
              R1 (K - 14)%nat w4 b with "Hcg Hpc Hi0c Hf4").
    iIntros (CIDs4 Hqs4) "Hcg Hpc Hf4".
    iEval (rewrite Hc4) in "Hf4".
    assert (Hv4 : rget R1 Rs2 = (m !!! Regidx Rs2 : mword 64)) by (rgne; lkp).
    assert (Hw4 : (R1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)) by lkp.
    first [ iEval (rewrite Hw4) in "Hf4"
          | iEval (rewrite Hv4) in "Hf4"
          | iEval (rgne; rewrite Hw4) in "Hf4" ].
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x0c) : mword 64) 2
                  = mword_of_int (WI + 0x0e)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x0e sd Rs4,64(sp) ===== *)
    iDestruct "Hf6" as (w6) "Hf6".
    assert (Hc6 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc6) in "Hf6".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0x0e)) (mword_of_int 8 : mword 6) Rs4
              R1 (K - 14)%nat w6 b with "Hcg Hpc Hi0e Hf6").
    iIntros (CIDs6 Hqs6) "Hcg Hpc Hf6".
    iEval (rewrite Hc6) in "Hf6".
    assert (Hv6 : rget R1 Rs4 = (m !!! Regidx Rs4 : mword 64)) by (rgne; lkp).
    assert (Hw6 : (R1 !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64)) by lkp.
    first [ iEval (rewrite Hw6) in "Hf6"
          | iEval (rewrite Hv6) in "Hf6"
          | iEval (rgne; rewrite Hw6) in "Hf6" ].
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x0e) : mword 64) 2
                  = mword_of_int (WI + 0x10)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x10 sd Rs5,56(sp) ===== *)
    iDestruct "Hf7" as (w7) "Hf7".
    assert (Hc7 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 7).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc7) in "Hf7".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0x10)) (mword_of_int 7 : mword 6) Rs5
              R1 (K - 14)%nat w7 b with "Hcg Hpc Hi10 Hf7").
    iIntros (CIDs7 Hqs7) "Hcg Hpc Hf7".
    iEval (rewrite Hc7) in "Hf7".
    assert (Hv7 : rget R1 Rs5 = (m !!! Regidx Rs5 : mword 64)) by (rgne; lkp).
    assert (Hw7 : (R1 !!! Regidx Rs5 : mword 64) = (m !!! Regidx Rs5 : mword 64)) by lkp.
    first [ iEval (rewrite Hw7) in "Hf7"
          | iEval (rewrite Hv7) in "Hf7"
          | iEval (rgne; rewrite Hw7) in "Hf7" ].
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x10) : mword 64) 2
                  = mword_of_int (WI + 0x12)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x12 sd Rs6,48(sp) ===== *)
    iDestruct "Hf8" as (w8) "Hf8".
    assert (Hc8 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc8) in "Hf8".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0x12)) (mword_of_int 6 : mword 6) Rs6
              R1 (K - 14)%nat w8 b with "Hcg Hpc Hi12 Hf8").
    iIntros (CIDs8 Hqs8) "Hcg Hpc Hf8".
    iEval (rewrite Hc8) in "Hf8".
    assert (Hv8 : rget R1 Rs6 = (m !!! Regidx Rs6 : mword 64)) by (rgne; lkp).
    assert (Hw8 : (R1 !!! Regidx Rs6 : mword 64) = (m !!! Regidx Rs6 : mword 64)) by lkp.
    first [ iEval (rewrite Hw8) in "Hf8"
          | iEval (rewrite Hv8) in "Hf8"
          | iEval (rgne; rewrite Hw8) in "Hf8" ].
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x12) : mword 64) 2
                  = mword_of_int (WI + 0x14)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x14 sd Rs7,40(sp) ===== *)
    iDestruct "Hf9" as (w9) "Hf9".
    assert (Hc9 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 9).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc9) in "Hf9".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0x14)) (mword_of_int 5 : mword 6) Rs7
              R1 (K - 14)%nat w9 b with "Hcg Hpc Hi14 Hf9").
    iIntros (CIDs9 Hqs9) "Hcg Hpc Hf9".
    iEval (rewrite Hc9) in "Hf9".
    assert (Hv9 : rget R1 Rs7 = (m !!! Regidx Rs7 : mword 64)) by (rgne; lkp).
    assert (Hw9 : (R1 !!! Regidx Rs7 : mword 64) = (m !!! Regidx Rs7 : mword 64)) by lkp.
    first [ iEval (rewrite Hw9) in "Hf9"
          | iEval (rewrite Hv9) in "Hf9"
          | iEval (rgne; rewrite Hw9) in "Hf9" ].
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x14) : mword 64) 2
                  = mword_of_int (WI + 0x16)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.    (* ===== +0x16 addi s0,sp,112 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (WI + 0x16))
              (Cregidx (mword_of_int 0)) (mword_of_int 28 : mword 8) Rs0
              R1 (K - 14)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rdok) with "Hcg Hpc Hi16").
    iIntros (CIDp3 Hqp3) "Hcg Hpc".
    set (S1 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 28 : mword 8))))]> R1).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x16) : mword 64) 2
                  = mword_of_int (WI + 0x18)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x18 c.mv s5,a0 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (WI + 0x18)) Rs5 Ra0
              S1 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi18").
    iIntros (CIDp4 Hqp4) "Hcg Hpc".
    set (S2 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget S1 Ra0))]> S1).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x18) : mword 64) 2
                  = mword_of_int (WI + 0x1a)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x1a c.mv s7,a1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (WI + 0x1a)) Rs7 Ra1
              S2 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1a").
    iIntros (CIDp5 Hqp5) "Hcg Hpc".
    set (S3 := <[Regidx Rs7 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget S2 Ra1))]> S2).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x1a) : mword 64) 2
                  = mword_of_int (WI + 0x1c)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x1c c.mv s4,a2 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (WI + 0x1c)) Rs4 Ra2
              S3 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1c").
    iIntros (CIDp6 Hqp6) "Hcg Hpc".
    set (S4 := <[Regidx Rs4 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget S3 Ra2))]> S3).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x1c) : mword 64) 2
                  = mword_of_int (WI + 0x1e)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x1e c.mv s2,a3 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (WI + 0x1e)) Rs2 Ra3
              S4 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1e").
    iIntros (CIDp7 Hqp7) "Hcg Hpc".
    set (S5 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget S4 Ra3))]> S4).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x1e) : mword 64) 2
                  = mword_of_int (WI + 0x20)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x20 c.mv s6,a4 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (WI + 0x20)) Rs6 Ra4
              S5 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi20").
    iIntros (CIDp8 Hqp8) "Hcg Hpc".
    set (S6 := <[Regidx Rs6 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget S5 Ra4))]> S5).
    assert (HS6sp : wi_sp m S6) by (rewrite /wi_sp; lkp).
    assert (HS6a3 : S6 !!! Regidx Ra3
                    = (mword_of_int (Z.of_nat off) : mword 64)) by lkp.
    assert (HS6a4 : S6 !!! Regidx Ra4
                    = (mword_of_int (Z.of_nat n) : mword 64)) by lkp.
    assert (HS6s5 : S6 !!! Regidx Rs5 = ip).
    { rewrite (_ : S6 !!! Regidx Rs5
                   = add_vec (zero_reg : mword 64) (rget S1 Ra0)); [| lkp].
      rgne. rewrite (_ : S1 !!! Regidx Ra0 = ip); [| lkp]. apply add_vec_zero_l. }
    assert (HS6s7 : S6 !!! Regidx Rs7 = (m !!! Regidx Ra1 : mword 64)).
    { rewrite (_ : S6 !!! Regidx Rs7
                   = add_vec (zero_reg : mword 64) (rget S2 Ra1)); [| lkp].
      rgne. rewrite (_ : S2 !!! Regidx Ra1 = (m !!! Regidx Ra1 : mword 64)); [| lkp].
      apply add_vec_zero_l. }
    assert (HS6s4 : S6 !!! Regidx Rs4
                    = pa_add (m !!! Regidx Ra2 : mword 64) 0%nat).
    { rewrite (_ : S6 !!! Regidx Rs4
                   = add_vec (zero_reg : mword 64) (rget S3 Ra2)); [| lkp].
      rgne. rewrite (_ : S3 !!! Regidx Ra2 = (m !!! Regidx Ra2 : mword 64)); [| lkp].
      rewrite add_vec_zero_l. rewrite -(wi_pa_add_moi _ 0%nat).
      change (Z.of_nat 0%nat) with 0%Z. symmetry. apply kv_addv_zero. }
    assert (HS6s2 : S6 !!! Regidx Rs2
                    = (mword_of_int (Z.of_nat (off + 0)) : mword 64)).
    { rewrite (_ : S6 !!! Regidx Rs2
                   = add_vec (zero_reg : mword 64) (rget S4 Ra3)); [| lkp].
      rgne. rewrite (_ : S4 !!! Regidx Ra3
                         = (mword_of_int (Z.of_nat off) : mword 64)); [| lkp].
      rewrite add_vec_zero_l. rewrite Nat.add_0_r. reflexivity. }
    assert (HS6s6 : S6 !!! Regidx Rs6 = (mword_of_int (Z.of_nat n) : mword 64)).
    { rewrite /S6 upd_eq. rgne.
      rewrite (_ : S5 !!! Regidx Ra4 = (mword_of_int (Z.of_nat n) : mword 64)); [| lkp].
      apply add_vec_zero_l. }
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x20) : mword 64) 2
                  = mword_of_int (WI + 0x22)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x22 addw a5,a3,a4 : a5 := off + n.  THE JOINT PREMISE is
       what makes this non-wrapping; see SpecWritei.v. ===== *)
    iApply (wp_addw4_s_sconf (mword_of_int (WI + 0x22)) Ra5 Ra3 Ra4
              S6 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi22").
    iIntros (CIDp9 Hqp9) "Hcg Hpc".
    set (T1 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64
                    (add_vec (subrange_vec_dec (rget S6 Ra3) 31 0 : mword 32)
                             (subrange_vec_dec (rget S6 Ra4) 31 0 : mword 32)))]> S6).
    assert (HT1a5 : T1 !!! Regidx Ra5
                    = (mword_of_int (Z.of_nat (off + n)) : mword 64)).
    { rewrite /T1 upd_eq. rgne; rgne. rewrite HS6a3 HS6a4.
      rewrite (wi_addw (Z.of_nat off) (Z.of_nat n)
                 ltac:(lia) ltac:(lia) ltac:(lia)).
      assert (Hz : (Z.of_nat off + Z.of_nat n)%Z = Z.of_nat (off + n)) by lia.
      rewrite Hz. reflexivity. }
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x22) : mword 64) 4
                  = mword_of_int (WI + 0x26)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x26 lui a4,0x43 : a4 := MAXFILE * BSIZE ===== *)
    iApply (wp_lui_s_sconf (mword_of_int (WI + 0x26)) Ra4
              (mword_of_int 67 : mword 20) (mword_of_int 274432 : mword 64)
              T1 (K - 14)%nat b ltac:(nz) ltac:(rdok) wi_lui43 with "Hcg Hpc Hi26").
    iIntros (CIDp10 Hqp10) "Hcg Hpc".
    set (T2 := <[Regidx Ra4 := regval_into_reg
                  (mword_of_int 274432 : mword 64)]> T1).
    assert (HT2a4 : T2 !!! Regidx Ra4 = (mword_of_int 274432 : mword 64))
      by (rewrite /T2; apply upd_eq).
    assert (HT2a5 : T2 !!! Regidx Ra5
                    = (mword_of_int (Z.of_nat (off + n)) : mword 64)) by lkp.
    assert (HT2a3 : T2 !!! Regidx Ra3
                    = (mword_of_int (Z.of_nat off) : mword 64)) by lkp.
    assert (Hu274 : bv_unsigned (mword_of_int 274432 : mword 64) = 274432)
      by (apply moi64_small; lia).
    assert (Husum : bv_unsigned (mword_of_int (Z.of_nat (off + n)) : mword 64)
                    = Z.of_nat (off + n)) by (apply wi_nat_u; lia).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x26) : mword 64) 4
                  = mword_of_int (WI + 0x2a)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x2a bltu a4,a5 : off + n > MAXFILE*BSIZE ? ===== *)
    destruct (Z_lt_le_dec 274432 (Z.of_nat (off + n))) as [Htoobig | Hfits].
    { (* ---- the second -1 exit, through +0x102 and the epilogue ---- *)
      iApply (wp_bltu_taken_s_sconf (mword_of_int (WI + 0x2a))
                (mword_of_int 216 : mword 13) Ra5 Ra4 T2 (K - 14)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HT2a4 HT2a5;
                      rewrite (wi_ltu_read _ _ _ _ Hu274 Husum);
                      apply Z.ltb_lt; exact Htoobig)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi2a").
      iApply bi.later_intro. iIntros (CIDy1 Hqy1) "Hcg Hpc".
      assert (Htgt : add_vec (mword_of_int (WI + 0x2a) : mword 64)
                (sign_extend' 64 (mword_of_int 216 : mword 13))
              = mword_of_int (WI + 0x102)) by pcw.
      iEval (rewrite Htgt) in "Hpc".
      (* ===== +0x102 c.li a0,-1 ===== *)
      iApply (wp_cli_s_sconf (mword_of_int (WI + 0x102)) Ra0
                (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                T2 (K - 14)%nat b ltac:(nz) ltac:(rdok) wi_li_m1
                with "Hcg Hpc Hi102").
      iIntros (CIDy2 Hqy2) "Hcg Hpc".
      set (Y1 := <[Regidx Ra0 := regval_into_reg
                    (mword_of_int (-1) : mword 64)]> T2).
      assert (HY1a0 : Y1 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
        by (rewrite /Y1; apply upd_eq).
      assert (HY1sp : wi_sp m Y1) by (rewrite /wi_sp; lkp).
      assert (Hpp : add_vec_int (mword_of_int (WI + 0x102) : mword 64) 2
                    = mword_of_int (WI + 0x104)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x104 c.j +0xdc ===== *)
      iApply (wp_cj_s_sconf (mword_of_int (WI + 0x104))
                (sign_extend' 21 (concat_vec (mword_of_int 2028 : mword 11) ('b"0")))
                Y1 (K - 14)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi104").
      iIntros (CIDy3 Hqy3). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htgtdc : add_vec (mword_of_int (WI + 0x104) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 2028 : mword 11) ('b"0"))))
              = mword_of_int (WI + 0xdc)) by pcw.
      iEval (rewrite Htgtdc) in "Hpc".
      iAssert (wi_fr7 m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 HfA HfB HfC HfD HfE]"
        as "Hframe".
      { rewrite /wi_fr7.
        iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
        iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
        iSplitL "Hf5"; [iExact "Hf5"|]. iSplitL "Hf6"; [iExact "Hf6"|].
        iSplitL "Hf7"; [iExact "Hf7"|]. iSplitL "Hf8"; [iExact "Hf8"|].
        iSplitL "Hf9"; [iExact "Hf9"|]. iSplitL "HfA"; [iExact "HfA"|].
        iSplitL "HfB"; [iExact "HfB"|]. iSplitL "HfC"; [iExact "HfC"|].
        iSplitL "HfD"; [iExact "HfD"|]. iExact "HfE". }
      iDestruct (cpu_own_transport CID CIDy3 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (IntrDefs.trap_csrs_ext_transport CID CIDy3 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (IntrDefs.cpu_claim_ext_transport CID CIDy3 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
      iApply (wi_ret (CID0 := CIDy3) γfs γi bn γ γf cov logstart inodestart nib
                dev
                ip inum bm bm data data dn dn dn0 dn0 user off n 0%nat src_bytes
                (fun _ => bv_0 8) 0%nat (fun _ => bv_0 8) V (pv_upt V) ncount ncount
                Sb Sb
                pidv dq dqd dqn dqs A j m Y1 K eb b lks
                HK HY1sp ltac:(lkp) ltac:(lkp) ltac:(lkp) ltac:(lkp) ltac:(lkp)
                ltac:(lkp) Hwf Hhz Hadr Hszdn Hcovin
                ltac:(intros Hc; exact Hc) ltac:(intros Hc; exact Hc)
                ltac:(unfold BSIZE; lia) ltac:(intros; reflexivity)
                ltac:(intros; reflexivity)
                ltac:(intro k; rewrite decide_False; [| lia];
                      rewrite decide_False; [reflexivity | lia])
                ltac:(intros _ i Hi; exfalso; lia)
                ltac:(left; split_and!;
                      [ exact HY1a0
                      | right; rewrite wi_maxfile_val wi_bsize_val; lia
                      | reflexivity | reflexivity | reflexivity | reflexivity
                      | reflexivity | reflexivity | reflexivity ])
                ltac:(lia) ltac:(lia) ltac:(reflexivity)
                ltac:(unfold wi16_post; intros Hpos; exfalso; lia)
                (* the second -1 exit: [n' = ncount], so the unguarded spend
                   bound is loose, and [tot = 0] gives the granularity *)
                ltac:(unfold wi16_spend_any; intros _; lia)
                ltac:(unfold wi16_atomic; intros _; left; reflexivity)
                ltac:(apply uptd_ext_refl)
                with "Hcg Hcnt Hextc Hextm Htext Hpc Hframe Hidev Hinum
                      Hmeta Hmap Hblocks Hsb Hba Hdn Hsrc Hsl Hop [Hcont]").
      iApply (wp_next_shift (b := true) (CIDa := CID) (CIDb := CIDy3) ltac:(wp_next_chain)
                with "Hcont").
    }
    (* ===== +0x2a falls: off + n <= MAXFILE*BSIZE ===== *)
    iApply (wp_bltu_fall_s_sconf (mword_of_int (WI + 0x2a))
              (mword_of_int 216 : mword 13) Ra5 Ra4 T2 (K - 14)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HT2a4 HT2a5;
                    rewrite (wi_ltu_read _ _ _ _ Hu274 Husum);
                    apply Z.ltb_ge; exact Hfits)
              with "Hcg Hpc Hi2a").
    iIntros (CIDp11 Hqp11) "Hcg Hpc".
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x2a) : mword 64) 4
                  = mword_of_int (WI + 0x2e)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x2e bltu a5,a3 : xv6's overflow test -- DEAD by the joint
       premise (off + n cannot have wrapped, so it is >= off) ===== *)
    assert (Hoffu2 : bv_unsigned (mword_of_int (Z.of_nat off) : mword 64)
                     = Z.of_nat off) by (apply wi_nat_u; lia).
    iApply (wp_bltu_fall_s_sconf (mword_of_int (WI + 0x2e))
              (mword_of_int 212 : mword 13) Ra3 Ra5 T2 (K - 14)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HT2a5 HT2a3;
                    rewrite (wi_ltu_read _ _ _ _ Husum Hoffu2);
                    apply Z.ltb_ge; lia)
              with "Hcg Hpc Hi2e").
    iIntros (CIDp12 Hqp12) "Hcg Hpc".
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x2e) : mword 64) 4
                  = mword_of_int (WI + 0x32)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (Hrng : (off + n <= MAXFILE * BSIZE)%nat)
      by (rewrite wi_maxfile_val wi_bsize_val; lia).
    assert (HT2sp : wi_sp m T2) by (rewrite /wi_sp; lkp).
    (* ===== +0x32 sd Rs3,72(sp) ===== *)
    iDestruct "Hf5" as (w5) "Hf5".
    assert (Hc5 : add_vec (T2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc5) in "Hf5".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0x32)) (mword_of_int 9 : mword 6) Rs3
              T2 (K - 14)%nat w5 b with "Hcg Hpc Hi32 Hf5").
    iIntros (CIDs5 Hqs5) "Hcg Hpc Hf5".
    iEval (rewrite Hc5) in "Hf5".
    assert (Hv5 : rget T2 Rs3 = (m !!! Regidx Rs3 : mword 64)) by (rgne; lkp).
    assert (Hw5 : (T2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)) by lkp.
    first [ iEval (rewrite Hw5) in "Hf5"
          | iEval (rewrite Hv5) in "Hf5"
          | iEval (rgne; rewrite Hw5) in "Hf5" ].
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x32) : mword 64) 2
                  = mword_of_int (WI + 0x34)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.    (* ===== +0x34 beqz s6 : the n = 0 arm ===== *)
    assert (HT2s6 : T2 !!! Regidx Rs6 = (mword_of_int (Z.of_nat n) : mword 64))
      by lkp.
    assert (HT2s5 : T2 !!! Regidx Rs5 = ip) by lkp.
    assert (HT2s7 : T2 !!! Regidx Rs7 = (m !!! Regidx Ra1 : mword 64)) by lkp.
    assert (HT2s4 : T2 !!! Regidx Rs4
                    = pa_add (m !!! Regidx Ra2 : mword 64) 0%nat).
    { rewrite (_ : T2 !!! Regidx Rs4 = (S6 !!! Regidx Rs4 : mword 64));
        [exact HS6s4 | lkp]. }
    assert (HT2s2 : T2 !!! Regidx Rs2
                    = (mword_of_int (Z.of_nat (off + 0)) : mword 64)).
    { rewrite (_ : T2 !!! Regidx Rs2 = (S6 !!! Regidx Rs2 : mword 64));
        [exact HS6s2 | lkp]. }
    destruct (Nat.eqb_spec n 0) as [Hn0 | Hnne].
    { (* ---- n = 0: nothing to copy, straight to iupdate ---- *)
      subst n.
      iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (WI + 0x34))
                (mword_of_int 186 : mword 13) Rs6 T2 (K - 14)%nat b ltac:(nz)
                ltac:(rgne; rewrite HT2s6;
                      rewrite (bc_eqz_moi 0%nat ltac:(lia)); reflexivity)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi34").
      iApply bi.later_intro. iIntros (CIDz1 Hqz1) "Hcg Hpc".
      assert (Htgtee : add_vec (mword_of_int (WI + 0x34) : mword 64)
                (sign_extend' 64 (mword_of_int 186 : mword 13))
              = mword_of_int (WI + 0xee)) by pcw.
      iEval (rewrite Htgtee) in "Hpc".
      (* ===== +0xee c.mv s3,s6 : tot := n = 0 ===== *)
      iApply (wp_cmv_s_sconf (mword_of_int (WI + 0xee)) Rs3 Rs6
                T2 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hiee").
      iIntros (CIDz2 Hqz2) "Hcg Hpc".
      set (Z1 := <[Regidx Rs3 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (rget T2 Rs6))]> T2).
      assert (HZ1s3 : Z1 !!! Regidx Rs3
                      = (mword_of_int (Z.of_nat 0%nat) : mword 64)).
      { rewrite /Z1 upd_eq. rgne. rewrite HT2s6. apply add_vec_zero_l. }
      assert (HZ1s5 : Z1 !!! Regidx Rs5 = ip) by lkp.
      assert (HZ1sp : wi_sp m Z1) by (rewrite /wi_sp; lkp).
      assert (Hpp : add_vec_int (mword_of_int (WI + 0xee) : mword 64) 2
                    = mword_of_int (WI + 0xf0)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0xf0 c.j +0xd2 ===== *)
      iApply (wp_cj_s_sconf (mword_of_int (WI + 0xf0))
                (sign_extend' 21 (concat_vec (mword_of_int 2033 : mword 11) ('b"0")))
                Z1 (K - 14)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hif0").
      iIntros (CIDz3 Hqz3). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htgtd2 : add_vec (mword_of_int (WI + 0xf0) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 2033 : mword 11) ('b"0"))))
              = mword_of_int (WI + 0xd2)) by pcw.
      iEval (rewrite Htgtd2) in "Hpc".
      iAssert (wi_fr8 m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 HfA HfB HfC HfD HfE]"
        as "Hframe".
      { rewrite /wi_fr8.
        iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
        iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
        iSplitL "Hf5"; [iExact "Hf5"|]. iSplitL "Hf6"; [iExact "Hf6"|].
        iSplitL "Hf7"; [iExact "Hf7"|]. iSplitL "Hf8"; [iExact "Hf8"|].
        iSplitL "Hf9"; [iExact "Hf9"|]. iSplitL "HfA"; [iExact "HfA"|].
        iSplitL "HfB"; [iExact "HfB"|]. iSplitL "HfC"; [iExact "HfC"|].
        iSplitL "HfD"; [iExact "HfD"|]. iExact "HfE". }
      (* iupdate flushes an UNCHANGED dinode: the size test inside
         [wi_dinode] is false because [off <= ip->size] got us here *)
      assert (Hdn0 : wi_dinode dn bm off 0%nat = dn).
      { rewrite /wi_dinode. case_decide as Hd; [exfalso; lia|].
        rewrite -Hadr. destruct dn; reflexivity. }
      (* NOTE the non-monotonicity trap: [wi_cost_bmonly 0 0 = 2], where the
         old [wi_cost 0 0] was 1.  The empty range still has a positive
         budget premise, and it is the bitmap unit that the accounting holds
         back on every path.  This arm needs only that [ncount <> 0]. *)
      destruct ncount as [| unc];
        [exfalso; unfold wi_cost_bmonly in Hcost; lia|].
      iDestruct (cpu_own_transport CID CIDz3 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (IntrDefs.trap_csrs_ext_transport CID CIDz3 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (IntrDefs.cpu_claim_ext_transport CID CIDz3 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
      iApply (wi_join (CID0 := CIDz3) γs j γl γu γd γk pd pav pu γfs γi bn γ γf
                cov logstart inodestart nib dev ip inum bm bm data data dn dn dn0
                user off 0%nat 0%nat src_bytes (fun _ => bv_0 8)
                0%nat (fun _ => bv_0 8) V (pv_upt V) (S unc) unc Sb Sb
                pidv dq dqd dqn dqs A m Z1 K eb b lks
                HK Hgeom0 Hist Hicov Hilog Hnib Hdtnz Hstab Hnlk Hadr Hwf Hhz Hszdn Hcovin
                ltac:(lia) ltac:(intros Hc; exact Hc) Hj Hgl
                HZ1sp HZ1s5 HZ1s3 ltac:(lkp) ltac:(lkp) ltac:(lkp) ltac:(lkp)
                ltac:(lkp) ltac:(unfold BSIZE; lia) ltac:(intros; reflexivity)
                ltac:(intros; reflexivity)
                ltac:(intro k; rewrite decide_False; [| lia];
                      rewrite decide_False; [reflexivity | lia])
                ltac:(intros _ i Hi; exfalso; lia) ltac:(lia)
                ltac:(symmetry; exact Hdn0)
                ltac:(unfold wi_cost_bmonly; lia) ltac:(lia) ltac:(lia)
                ltac:(reflexivity)
                (* tot = 0 = n on this arm: nothing was written, so the
                   memberships cannot fire, the spend bound is loose by the
                   whole figure (only the trailing iupdate ran), and the
                   granularity fact holds at BOTH of its disjuncts *)
                ltac:(rewrite /wi16_pre; intros Hone; cbv zeta; split_and!;
                      [ lia | left; reflexivity | intros Hpos; exfalso; lia ])
                ltac:(apply uptd_ext_refl)
                ltac:(lkbelow)
                with "Hcg Hcnt Hextc Hextm Htext Hkdata Hpc Hpanenv Hbio Hlctx Hprocs Hdevi
                      Hdgeom Hdlock Hframe Hidev Hinum Hmeta
                      Hmap Hblocks Hsb Hba Hireg Hdn Hsrc Hsl Hop [Hcont]").
      iApply (wp_next_shift (b := true) (CIDa := CID) (CIDb := CIDz3) ltac:(wp_next_chain)
                with "Hcont").
    }
    (* ---- n <> 0: save the other five, initialise, enter the loop ---- *)
    iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (WI + 0x34))
              (mword_of_int 186 : mword 13) Rs6 T2 (K - 14)%nat b ltac:(nz)
              ltac:(rgne; rewrite HT2s6;
                    rewrite (bc_eqz_moi n ltac:(lia));
                    apply Nat.eqb_neq; exact Hnne)
              with "Hcg Hpc Hi34").
    iIntros (CIDp13 Hqp13) "Hcg Hpc".
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x34) : mword 64) 4
                  = mword_of_int (WI + 0x38)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x38 sd Rs1,88(sp) ===== *)
    iDestruct "Hf3" as (w3) "Hf3".
    assert (Hc3 : add_vec (T2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc3) in "Hf3".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0x38)) (mword_of_int 11 : mword 6) Rs1
              T2 (K - 14)%nat w3 b with "Hcg Hpc Hi38 Hf3").
    iIntros (CIDs3 Hqs3) "Hcg Hpc Hf3".
    iEval (rewrite Hc3) in "Hf3".
    assert (Hv3 : rget T2 Rs1 = (m !!! Regidx Rs1 : mword 64)) by (rgne; lkp).
    assert (Hw3 : (T2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64)) by lkp.
    first [ iEval (rewrite Hw3) in "Hf3"
          | iEval (rewrite Hv3) in "Hf3"
          | iEval (rgne; rewrite Hw3) in "Hf3" ].
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x38) : mword 64) 2
                  = mword_of_int (WI + 0x3a)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x3a sd Rs8,32(sp) ===== *)
    iDestruct "HfA" as (w10) "HfA".
    assert (Hc10 : add_vec (T2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc10) in "HfA".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0x3a)) (mword_of_int 4 : mword 6) Rs8
              T2 (K - 14)%nat w10 b with "Hcg Hpc Hi3a HfA").
    iIntros (CIDs10 Hqs10) "Hcg Hpc HfA".
    iEval (rewrite Hc10) in "HfA".
    assert (Hv10 : rget T2 Rs8 = (m !!! Regidx Rs8 : mword 64)) by (rgne; lkp).
    assert (Hw10 : (T2 !!! Regidx Rs8 : mword 64) = (m !!! Regidx Rs8 : mword 64)) by lkp.
    first [ iEval (rewrite Hw10) in "HfA"
          | iEval (rewrite Hv10) in "HfA"
          | iEval (rgne; rewrite Hw10) in "HfA" ].
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x3a) : mword 64) 2
                  = mword_of_int (WI + 0x3c)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x3c sd Rs9,24(sp) ===== *)
    iDestruct "HfB" as (w11) "HfB".
    assert (Hc11 : add_vec (T2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 11).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc11) in "HfB".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0x3c)) (mword_of_int 3 : mword 6) Rs9
              T2 (K - 14)%nat w11 b with "Hcg Hpc Hi3c HfB").
    iIntros (CIDs11 Hqs11) "Hcg Hpc HfB".
    iEval (rewrite Hc11) in "HfB".
    assert (Hv11 : rget T2 Rs9 = (m !!! Regidx Rs9 : mword 64)) by (rgne; lkp).
    assert (Hw11 : (T2 !!! Regidx Rs9 : mword 64) = (m !!! Regidx Rs9 : mword 64)) by lkp.
    first [ iEval (rewrite Hw11) in "HfB"
          | iEval (rewrite Hv11) in "HfB"
          | iEval (rgne; rewrite Hw11) in "HfB" ].
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x3c) : mword 64) 2
                  = mword_of_int (WI + 0x3e)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x3e sd Rs10,16(sp) ===== *)
    iDestruct "HfC" as (w12) "HfC".
    assert (Hc12 : add_vec (T2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 12).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc12) in "HfC".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0x3e)) (mword_of_int 2 : mword 6) Rs10
              T2 (K - 14)%nat w12 b with "Hcg Hpc Hi3e HfC").
    iIntros (CIDs12 Hqs12) "Hcg Hpc HfC".
    iEval (rewrite Hc12) in "HfC".
    assert (Hv12 : rget T2 Rs10 = (m !!! Regidx Rs10 : mword 64)) by (rgne; lkp).
    assert (Hw12 : (T2 !!! Regidx Rs10 : mword 64) = (m !!! Regidx Rs10 : mword 64)) by lkp.
    first [ iEval (rewrite Hw12) in "HfC"
          | iEval (rewrite Hv12) in "HfC"
          | iEval (rgne; rewrite Hw12) in "HfC" ].
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x3e) : mword 64) 2
                  = mword_of_int (WI + 0x40)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x40 sd Rs11,8(sp) ===== *)
    iDestruct "HfD" as (w13) "HfD".
    assert (Hc13 : add_vec (T2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 13).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc13) in "HfD".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (WI + 0x40)) (mword_of_int 1 : mword 6) Rs11
              T2 (K - 14)%nat w13 b with "Hcg Hpc Hi40 HfD").
    iIntros (CIDs13 Hqs13) "Hcg Hpc HfD".
    iEval (rewrite Hc13) in "HfD".
    assert (Hv13 : rget T2 Rs11 = (m !!! Regidx Rs11 : mword 64)) by (rgne; lkp).
    assert (Hw13 : (T2 !!! Regidx Rs11 : mword 64) = (m !!! Regidx Rs11 : mword 64)) by lkp.
    first [ iEval (rewrite Hw13) in "HfD"
          | iEval (rewrite Hv13) in "HfD"
          | iEval (rgne; rewrite Hw13) in "HfD" ].
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x40) : mword 64) 2
                  = mword_of_int (WI + 0x42)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.    (* ===== +0x42 c.li s3,0 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (WI + 0x42)) Rs3
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              T2 (K - 14)%nat b ltac:(nz) ltac:(rdok) wi_li_0 with "Hcg Hpc Hi42").
    iIntros (CIDp14 Hqp14) "Hcg Hpc".
    set (U1 := <[Regidx Rs3 := regval_into_reg (mword_of_int 0 : mword 64)]> T2).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x42) : mword 64) 2
                  = mword_of_int (WI + 0x44)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x44 li s9,1024 ===== *)
    iApply (wp_li4_s_sconf (mword_of_int (WI + 0x44)) Rs9
              (mword_of_int 1024 : mword 12) (mword_of_int 1024 : mword 64)
              U1 (K - 14)%nat b ltac:(nz) ltac:(rdok) wi_li_1024
              with "Hcg Hpc Hi44").
    iIntros (CIDp15 Hqp15) "Hcg Hpc".
    set (U2 := <[Regidx Rs9 := regval_into_reg (mword_of_int 1024 : mword 64)]> U1).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x44) : mword 64) 4
                  = mword_of_int (WI + 0x48)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x48 c.li s8,-1 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (WI + 0x48)) Rs8
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              U2 (K - 14)%nat b ltac:(nz) ltac:(rdok) wi_li_m1 with "Hcg Hpc Hi48").
    iIntros (CIDp16 Hqp16) "Hcg Hpc".
    set (U3 := <[Regidx Rs8 := regval_into_reg (mword_of_int (-1) : mword 64)]> U2).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0x48) : mword 64) 2
                  = mword_of_int (WI + 0x4a)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x4a c.j +0x82 : into the loop head ===== *)
    iApply (wp_cj_s_sconf (mword_of_int (WI + 0x4a))
              (sign_extend' 21 (concat_vec (mword_of_int 28 : mword 11) ('b"0")))
              U3 (K - 14)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi4a").
    iIntros (CIDp17 Hqp17). iApply bi.later_intro. iIntros "Hcg Hpc".
    iClear "Hi00 Hi02 Hi06 Hi08 Hi0a Hi0c Hi0e Hi10 Hi12 Hi14 Hi16 Hi18 Hi1a Hi1c Hi1e Hi20 Hi22 Hi26 Hi2a Hi2e Hi32 Hi34 Hi38 Hi3a Hi3c Hi3e Hi40 Hi42 Hi44 Hi48 Hi4a Hiee Hif0 Hife Hi100 Hi102 Hi104".
    assert (Htgt82 : add_vec (mword_of_int (WI + 0x4a) : mword 64)
              (sign_extend' 64 (sign_extend' 21
                 (concat_vec (mword_of_int 28 : mword 11) ('b"0"))))
            = mword_of_int (WI + 0x82)) by pcw.
    iEval (rewrite Htgt82) in "Hpc".
    iAssert (wi_fr13 m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 HfA HfB HfC HfD HfE]"
      as "Hframe".
    { rewrite /wi_fr13.
      iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
      iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
      iSplitL "Hf5"; [iExact "Hf5"|]. iSplitL "Hf6"; [iExact "Hf6"|].
      iSplitL "Hf7"; [iExact "Hf7"|]. iSplitL "Hf8"; [iExact "Hf8"|].
      iSplitL "Hf9"; [iExact "Hf9"|]. iSplitL "HfA"; [iExact "HfA"|].
      iSplitL "HfB"; [iExact "HfB"|]. iSplitL "HfC"; [iExact "HfC"|].
      iSplitL "HfD"; [iExact "HfD"|]. iExact "HfE". }
    assert (HU3sp : wi_sp m U3) by (rewrite /wi_sp; lkp).
    assert (HU3s5 : U3 !!! Regidx Rs5 = ip) by lkp.
    assert (HU3s7 : U3 !!! Regidx Rs7 = (m !!! Regidx Ra1 : mword 64)) by lkp.
    assert (HU3s4 : U3 !!! Regidx Rs4
                    = pa_add (m !!! Regidx Ra2 : mword 64) 0%nat).
    { rewrite (_ : U3 !!! Regidx Rs4 = (T2 !!! Regidx Rs4 : mword 64));
        [exact HT2s4 | lkp]. }
    assert (HU3s2 : U3 !!! Regidx Rs2
                    = (mword_of_int (Z.of_nat (off + 0)) : mword 64)).
    { rewrite (_ : U3 !!! Regidx Rs2 = (T2 !!! Regidx Rs2 : mword 64));
        [exact HT2s2 | lkp]. }
    assert (HU3s6 : U3 !!! Regidx Rs6
                    = (mword_of_int (Z.of_nat n) : mword 64)) by lkp.
    assert (HU3s3 : U3 !!! Regidx Rs3
                    = (mword_of_int (Z.of_nat 0%nat) : mword 64)) by lkp.
    assert (HU3s9 : U3 !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)) by lkp.
    assert (HU3s8 : U3 !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)) by lkp.
    iDestruct (cpu_own_transport CID CIDp17 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (IntrDefs.trap_csrs_ext_transport CID CIDp17 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (IntrDefs.cpu_claim_ext_transport CID CIDp17 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID) (CIDb := CIDp17) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iApply (wi_loop (CID0 := CIDp17) γs j γl γu γd γk pd pav pu γfs γi bn γ γf γa
              cov logstart inodestart nib dev ip inum bm data dn dn0 user off n
              src_bytes V ncount Sb (m !!! Regidx Ra1 : mword 64)
              pidv dq dqd dqn dqs A m K eb b lks
              HK Hgeom0 Hist Hicov Hilog Hnib Hdtnz Hstab Hnlk Hszdn Hofflt Hnlt Hrng Ha1 Hj Hgl
              (wi_blocks off n) 0%nat bm data (fun _ => bv_0 8) (pv_upt V) ncount Sb U3
              ltac:(lia) Hwf Hhz ltac:(intros Hc; exact Hc) Hcovin
              ltac:(apply (bm_covers_mono bm (bv_unsigned (di_size dn)) _ Hcovin);
                    rewrite Nat.add_0_r; exact Hbig)
              ltac:(intro k; rewrite decide_False; [reflexivity | lia])
              ltac:(intros _ i Hi; exfalso; lia) ltac:(apply uptd_ext_refl)
              ltac:(replace (off + 0)%nat with off by lia;
                    replace (n - 0)%nat with n by lia; lia)
              (* THE INVARIANT AT ENTRY, at the caller's OWN set: [wi_inv_enter]
                 holds at ANY entry set, which is exactly why writei needs no
                 credit parameter of its own. *)
              (proj1 (wi_inv_enter (ba_bms A) ncount off n Sb Hcost))
              ltac:(lia)
              (proj2 (wi_inv_enter (ba_bms A) ncount off n Sb Hcost))
              ltac:(lia) ltac:(reflexivity)
              (* the loop is entered at the caller's own state, so the
                 single-block clause is four reflexivities *)
              ltac:(unfold wi16_fresh; intros _; split_and!; reflexivity)
              HU3sp HU3s5 HU3s7 HU3s4 HU3s2 HU3s6 HU3s3 HU3s9 HU3s8 Hprkc Hbelow
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hkdata Hprkenv Hbio Hlctx Hkenv
                    Hprocs
                    Hdevi Hdgeom Hdlock Hframe Hidev Hinum
                    Hmeta Hmap Hblocks Hsb Hba Hireg Hdn Hsrc Hsl Hop Hcont").
  Qed.

  (* THE COUNTED SEAL, derived at the [log_op] existential's OWN WITNESS
     (fs-icache.md section 18; ProofBmap's wp_bmap_sconf, same shape).
     [log_op γ ncount] IS [∃ Sb, log_opS γ ncount Sb], so the counted form
     destructs it, runs the core at whatever set was hiding there, and
     forgets the grown set again via [log_opS_op].  Deriving at [Sb := ∅]
     instead would force every counted caller to prove its set empty, which
     is both false and unnecessary -- and here it would be pointless as well,
     since [wi_inv_enter] holds at ANY entry set. *)
  Lemma wp_writei_sconf
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (γa : gname) (γf : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (bmapstart : Z) (size : Z) (dev : mword 32)
      (used : gset Z) (γpr : gname)
      (ip : mword 64) (inum : mword 32)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn dn0 : dinode)
      (user : bool) (off n : nat) (src_bytes : nat -> bv 8)
      (V : pprivate) (ncount : nat)
      (pidv : mword 32) (dq dqd dqn dqs dqb dqbs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
    : wp_writei_sconf_body ktb γs j γl γu γd γk pd pav pu bn γ γfs γi γa γf
                           cov logstart inodestart nib bmapstart size dev used γpr
                           ip inum bm data dn dn0
                           user off n src_bytes V ncount
                           pidv dq dqd dqn dqs dqb dqbs m K eb b lks.
  Proof.
    cbv beta delta [wp_writei_sconf_body].
    intros pcE pj src ret_tgt HK Hcost Hgeom Hist Hicov Hilog Hnib Hadr Hdtnz Hstab Hnlk
           Hwf Hhz Hcovin Hsum Hszdn Hgok Hprkc Hj Hgl Ha0 Ha1 Ha3 Ha4 Hbelow.
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hkdata #Hprkenv #Hbio #Hlctx #Hkenv
              Hidev Hinum
              Hmeta Hmap Hblocks Hsb Hszc Hbmsc Hbmres #Hireg Hdn Hsrc
              #Hprocs #Hdevi #Hdgeom #Hdlock Hsl Hop Hcont".
    iDestruct "Hop" as (Sb0) "Hop".
    iApply (wp_writei_gen γs j γl γu γd γk pd pav pu bn γ γfs γi γa γf
              cov logstart inodestart nib bmapstart size dev used γpr
              ip inum bm data dn dn0 user off n src_bytes V ncount Sb0
              pidv dq dqd dqn dqs dqb dqbs m K eb b lks
              HK Hcost Hgeom Hist Hicov Hilog Hnib Hadr Hdtnz Hstab Hnlk
              Hwf Hhz Hcovin Hsum Hszdn Hgok Hprkc Hj Hgl Ha0 Ha1 Ha3 Ha4 Hbelow
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hkdata Hprkenv Hbio Hlctx Hkenv
                    Hidev Hinum
                    Hmeta Hmap Hblocks Hsb Hszc Hbmsc Hbmres Hireg Hdn Hsrc
                    Hprocs Hdevi Hdgeom Hdlock Hsl Hop [Hcont]").
    all: try lkbelow.
    iEval (rewrite /wp_next).
    iIntros (CIDf) "%Hchain".
    iIntros (mf tot bm' data' dn' dn0' n' wrote dist dstb P' used' Sb')
      "%D1 %D2 %D3 %D4 %D5 %D6 %D7 %Dcap %Dsz %D8 %D9 %D9k %D10 %D11 %D12 %D13
       %Dsb %Dwi %Dwiany %Dwiat %D14
       Hcg Hcnt Hextc Hextm Hpc Hidev Hinum Hmeta Hmap Hblocks Hsb
       Hszc Hbmsc Hbmres Hdn Hsrc Hsl Hop".
    iSpecialize ("Hcont" $! CIDf with "[%]"); [exact Hchain|].
    iApply ("Hcont" $! mf tot bm' data' dn' dn0' n' wrote dist dstb P' used'
              with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                    [%] [%]
                    Hcg Hcnt Hextc Hextm Hpc Hidev Hinum Hmeta Hmap Hblocks Hsb
                    Hszc Hbmsc Hbmres Hdn Hsrc Hsl [Hop]").
    { exact D1. } { exact D2. } { exact D3. } { exact D4. } { exact D5. }
    { exact D6. } { exact D7. } { exact Dcap. } { exact Dsz. } { exact D8. }
    { exact D9. } { exact D9k. } { exact D10. } { exact D11. } { exact D12. }
    { exact D13. } { exact D14. }
    { iApply (log_opS_op with "Hop"). }
  Qed.

End WriteiMain.

End WriteiProof.
