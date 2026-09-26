(* ===================================================================== *)
(* UkConsOut.v -- THE CONSOLE AS AN OUTPUT DEVICE of the endpoint         *)
(* interface, at the GENERIC console claim, for ANY program instance      *)
(* (program-specs cut 4(c), the console; SS3.4d's claim-free core).       *)
(*                                                                        *)
(* Design: claude-notes/design/program-specs.md SS3.4, SS3.4b.  [UkHandler. *)
(* ep_iface]'s write law, specialised to the console: a device owing one  *)
(* of [alts] funds [UkTree.wr_obl] for a chunk [bs] of a chosen           *)
(* alternative [a], answers exactly [length bs] and then owes             *)
(* [drop (length bs) a].  [UCatKernel.cat_w_of_link] is the mould, and    *)
(* this differs from it in three ways only: any program (the stub law     *)
(* [UkStub.stub_law] in place of cat's stub), any alternative (the code   *)
(* is read off [a ∈ alts]), both source halves (data and text, as         *)
(* [UEchoOut] S4 has them).                                               *)
(*                                                                        *)
(* THE ENCODING OF [cons_dev alts].  Beside [cons_short alts] (every      *)
(* alternative is below 2^31 bytes: the kernel reads the count as a C     *)
(* [int], so a longer write does not answer its length -- this is the one *)
(* fact the TAINT arm needs too), the device at a ROUND [(v, I)] -- the   *)
(* era's pins and the input typed so far, [cons_dev_at v I alts], which   *)
(* the entries pin (program-specs SS3.4e); [cons_dev alts] hides them --  *)
(* is                                                                     *)
(*                                                                        *)
(*   - the era's cursor at a block of the writer's stage                   *)
(*     ([lm_wr_blk_t], exactly [GenLinksLine.gwc_blk]'s left arm, with     *)
(*     its witnesses NAMED, because the continuation bytes are read at     *)
(*     them), and the era's pin, and EITHER                                *)
(*       UNFILED, at the block's first byte: [alts] is the BODIES          *)
(*       ([LineModelLinks.lm_body], the continuation at the round's own   *)
(*       state without the shell's prompt, which the shell writes after   *)
(*       the child exited) of a list of CODES [codes], each admissible at  *)
(*       the line typed ([cons_adm]: [lm_ok] and not coverage-ending), so  *)
(*       that [a ∈ alts] picks a code; the list need not be all of them (a *)
(*       device owing fewer alternatives is a stronger obligation on the   *)
(*       program, and no line model's code space is finite);              *)
(*     OR FILED at an admissible code [c] and position [0 < i <= |body|]:  *)
(*       [alts = [drop i (lm_body s0 cs I c)]];                            *)
(*   - or the era's taint, which funds every byte and stays.              *)
(*                                                                        *)
(* The body, not the whole alternative, so that a child CAN drain the     *)
(* device: [cons_dev_at_drained] reads the cursor at the body's end (or,   *)
(* at an empty body, still at the block's first byte) off [[[]]], and      *)
(* [cons_cur_gwc_post] turns that cursor into [gwc_post], the block        *)
(* written up to its prompt; [cons_dev_at_of_blk0] lends the device out    *)
(* of [gwc_blk … 0 0]'s named left arm.                                    *)
(*                                                                        *)
(* [gwc_blk] itself is not used because it hides its witnesses; the arm   *)
(* here is [gwc_blk]'s word for word over M2's link parameters            *)
(* ([GenLinksLine.gen_params]) and a persistent LINKS bundle that entails *)
(* the three leaves a console byte needs ([gl_w], [gl_blk], [gl_taint]),  *)
(* which every claim with a byte law supplies ([FileLinkGen.file_links_gl] *)
(* at the file application, [PipeLinksLine.pipe_links_gl] at the          *)
(* pipeline's single-writer rounds).                                       *)
(*                                                                        *)
(* THE SPLIT (program-specs SS3.4d).  [cons_write] depends on the claim   *)
(* ONLY through one byte as an [out_link], so S3 is a CLAIM-FREE CORE over *)
(* an abstract device [D] with three laws ([D_short], [D_sub], [D_step])  *)
(* holding [cons_chain] and [cons_write]; S3b is the generic claim's      *)
(* device [cons_dev] at those laws ([cons_dev_sub] narrows the device to  *)
(* [[a]]; [cons_dev_step] is one byte -- [gl_blk] at an unfiled device,   *)
(* which files the code, [gl_w] at a filed one, the taint through          *)
(* [gl_taint]); and [UkPipeConsOut] is the pipeline's two-writer device at *)
(* the same core.                                                          *)
(*                                                                        *)
(* THE PROOF OF THE CORE.  [cons_chain] is the console chain the write    *)
(* leaf's deposit asks for, at the cursor [j ↦ D [drop j a]];             *)
(* [cons_write] runs the stub law to the ecall, the leaf of the source's  *)
(* half ([cons_leaf]) between, reads the exact count off                  *)
(* [UkWriteLeaf.uwrite_no_short] and returns through the stub.  The       *)
(* source run is SPLIT in two ([usrc_at_split], at any fraction): one     *)
(* half is lent to the leaf, the other rides the deposit (the chain's     *)
(* per-byte premise is read off it) and comes home in the post.           *)
(*                                                                        *)
(* S4: the witnesses at echo and at cat.                                  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import agree.
From iris.algebra.lib Require Import gmap_view.
From iris.base_logic.lib Require Import own ghost_map ghost_var invariants.
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
Require Import UserPerm.
Require Import ProcPtOwn.
Require Import UserPtTree.
Require Import UmodeArith UmodeAbi.
Require Import ProcGeom.
Require Import VcGen.              (* [trunc32_subrange] *)
Require Import KstackArith.        (* [bvsigned_moi_small] *)
Require Import ChildTok.
Require Import UexecSlot UexecRet UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import ConsoleInv.         (* [CONSOLE] *)
Require Import WpUart.             (* [out_link] *)
Require Import UkWriteLeaf.        (* the supply and the post, at row 16 *)
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenOutPure.
Require Import EchoOut.
Require Import GenOutHist.
Require Import GenOut.
Require Import GenLinksLine.       (* [gen_params], [gl_w]/[gl_blk]/[gl_taint] *)
(* the file application's links, for S4's witnesses *)
Require Import FileDisc FileOutPure AppFile FileOut FileLinks FileLinkGen.
Require Import GenLinksGl.         (* [gcl_gl_taint_at]: the file taint's byte at the era *)
Require Import CtxIdDefs.
Require Import UCodeEcho UCodeCat.
Require User.EchoSyms User.CatSyms.
(* [UserHeap] LAST among the U-tier libraries, as [UEchoOut] has it:
   [UmodeAbi.uargs] has fields that shadow [UserHeap.uarg]'s. *)
Require Import UserHeap.
Require Import ProgTree UkTree UkStub.
Require Import UkEchoTree UkCatTree.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  S1  THE PURE HALF                                                     *)
(* ===================================================================== *)

(* a fraction, halved: two halves of any [dfrac] make it again *)
Definition dq_half (dq : dfrac) : dfrac :=
  match dq with
  | DfracOwn q => DfracOwn (q / 2)%Qp
  | DfracDiscarded => DfracDiscarded
  | DfracBoth q => DfracBoth (q / 2)%Qp
  end.

Lemma dq_half_op (dq : dfrac) : dq_half dq ⋅ dq_half dq = dq.
Proof.
  destruct dq as [q | | q]; rewrite /dq_half.
  - change (DfracOwn (q / 2)%Qp ⋅ DfracOwn (q / 2)%Qp)
      with (DfracOwn (q / 2 + q / 2)%Qp).
    by rewrite Qp.div_2.
  - exact dfrac_op_discarded.
  - change (DfracBoth (q / 2)%Qp ⋅ DfracBoth (q / 2)%Qp)
      with (DfracBoth (q / 2 + q / 2)%Qp).
    by rewrite Qp.div_2.
Qed.

(* the kernel's count is the caller's request, below the sign boundary
   ([UCatKernel.cat_count_is], generic) *)
Lemma cons_count_is (nb : nat) :
  (Z.of_nat nb < 2 ^ 31)%Z ->
  sys_rw_count (mword_of_int (Z.of_nat nb) : mword 64) = Z.of_nat nb.
Proof.
  intros Hlt. change (2 ^ 31)%Z with 2147483648%Z in Hlt.
  assert (Hu : uint (mword_of_int (Z.of_nat nb) : mword 64) = Z.of_nat nb)
    by (apply uint_moi; unfold Z64; lia).
  rewrite uint_unsigned in Hu.
  rewrite /sys_rw_count. unfold bv_signed.
  rewrite trunc32_subrange subrange_31_0_unsigned Hu.
  rewrite (Z.mod_small (Z.of_nat nb) 4294967296); [| lia].
  assert (Hhm : bv_half_modulus 32 = 2147483648) by (vm_compute; reflexivity).
  rewrite bv_swrap_small; [ reflexivity | rewrite Hhm; lia ].
Qed.

(* every alternative a console write can answer the length of *)
Definition cons_short (alts : list (list (bv 8))) : Prop :=
  Forall (fun x => (Z.of_nat (length x) < 2 ^ 31)%Z) alts.

Section cons_pure.
  Context (M : lmodel).

  (* a code the line typed admits at the round's state (from the era's
     boot state [s0] under the filed list [cs]), and after which coverage
     goes on *)
  Definition cons_adm (s0 : lm_st M) (cs : list nat) (I : list (bv 8)) (c : nat) : Prop :=
    lm_ok M (lm_upto M cs s0 (bodies_of I) (nlines I - 1)) (lm_line_at M I) (lm_dec M c)
    /\ lm_term M (lm_dec M c) = false.

  (* THE STREAM BYTE a filed block's later byte is: the continuation at the
     round's state is a prefix of what the round then owes, at ANY
     alternative (at the panic one the next prologue round follows it) *)
  Lemma cons_blk_byte (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8))
      (pos c j : nat) (b : bv 8) :
    lm_wr_blk M ps cs s0 I pos ->
    lm_abs M s0 cs I c !! j = Some b ->
    lm_proc_stream M ps (cs ++ [c]) s0 I !! (pos + j)%nat = Some b.
  Proof using.
    intros Hw Hb.
    pose proof (lm_wr_blk_nonnil M ps cs s0 I pos Hw) as Hne.
    pose proof Hw as (_ & Hr & Hn & HP).
    rewrite /lm_proc_stream (lm_wr_blk_low M ps cs s0 I pos c Hw) lookup_app_r; [| lia].
    replace (pos + j - length (lm_proc_before M ps cs s0 I))%nat with j by lia.
    rewrite /lm_pending_at decide_False; [| exact Hne].
    rewrite decide_True; [| exact Hr].
    rewrite /lm_cont_at (lm_blk_snoc_at M cs I c Hn) (lm_blk_snoc_upto M cs s0 I c Hn).
    rewrite lookup_app_l; [exact Hb |].
    exact (lookup_lt_Some _ _ _ Hb).
  Qed.
End cons_pure.

(* ===================================================================== *)
(*  S2  THE SOURCE RUN: its halves, its range, and its leaf               *)
(* ===================================================================== *)
Section cons_src.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  (* NO [ctokG] AND NO [uexecSG] VARIABLE ([UEchoOut]'s reasons): row 16's
     concrete arm is read here, so the instance is the xv6 one. *)
  Context `{PS : UexecSG.uprogSG Σ}.

  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  (* one byte at [dq1 ⋅ dq2] is one at each *)
  Lemma ubyteq_op (γ : gname) (dq1 dq2 : dfrac) (a : Z) (b : bv 8) :
    ubyteq γ (dq1 ⋅ dq2) a b ⊣⊢ ubyteq γ dq1 a b ∗ ubyteq γ dq2 a b.
  Proof using .
    rewrite /ubyteq. iSplit.
    - rewrite ghost_map.ghost_map_elem_unseal /ghost_map.ghost_map_elem_def.
      rewrite -own_op -gmap_view_frag_op agree_idemp. iIntros "$".
    - iIntros "[H1 H2]".
      iDestruct (ghost_map_elem_combine with "H1 H2") as "[$ _]".
  Qed.

  Lemma ubytesq_op (γ : gname) (dq1 dq2 : dfrac) (a : Z) (n : nat)
      (f : nat -> bv 8) :
    ubytesq γ (dq1 ⋅ dq2) a n f ⊣⊢ ubytesq γ dq1 a n f ∗ ubytesq γ dq2 a n f.
  Proof using .
    rewrite /ubytesq -big_sepL_sep.
    apply big_opL_proper. intros k j _. apply ubyteq_op.
  Qed.

  (* a source run is two runs at half the fraction (the text half is
     persistent and is simply duplicated) *)
  Lemma usrc_at_split (N : uk_names Σ) (tx : bool) (dq : dfrac) (ua : Z)
      (n : nat) (f : nat -> bv 8) :
    usrc_at N tx dq ua n f ⊣⊢
    usrc_at N tx (dq_half dq) ua n f ∗ usrc_at N tx (dq_half dq) ua n f.
  Proof using .
    rewrite /usrc_at. destruct tx.
    - iSplit; [iIntros "#H"; iFrame "H" | iIntros "[$ _]"].
    - rewrite -{1}(dq_half_op dq). apply ubytesq_op.
  Qed.

  (* the empty run is at every address *)
  Lemma usrc_at_rebase (N : uk_names Σ) (tx : bool) (dq : dfrac) (ua ua' : Z)
      (n : nat) (f : nat -> bv 8) :
    (n = 0%nat \/ ua = ua') ->
    usrc_at N tx dq ua n f ⊣⊢ usrc_at N tx dq ua' n f.
  Proof using .
    intros [-> | ->]; [| reflexivity].
    rewrite /usrc_at /ubytesq. destruct tx; cbn [seq]; rewrite !big_sepL_nil; reflexivity.
  Qed.

  (* an owned or fetchable run does not wrap *)
  Lemma urun_usrc_bnd (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (tx : bool) (dq : dfrac) (ua : Z)
      (n : nat) (f : nat -> bv 8) :
    urun N h m pc avail -∗ usrc_at N tx dq ua n f -∗
    ⌜ forall j : nat, (j < n)%nat -> 0 <= ua + Z.of_nat j < 2 ^ 38 ⌝.
  Proof using .
    iIntros "Hrun Hs".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv)
      "(_ & _ & _ & _ & Hheap & _)".
    rewrite /usrc_at. destruct tx.
    - iDestruct (uheap_text_bytes (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ua n f
                   with "Hheap Hs") as %Hb.
      iPureIntro. intros j Hj. destruct (Hb j Hj) as (_ & _ & Hc). exact Hc.
    - iDestruct (uheap_ubytes_run (ukn_t N) (ukn_d N) (ukn_s N) M pm sz dq ua n f
                   with "Hheap Hs") as %Hb.
      iPureIntro. intros j Hj. exact (proj2 (Hb j Hj)).
  Qed.

  (* the chain's per-byte premise, off either half *)
  Lemma usrc_at_wat (N : uk_names Σ) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (tx : bool) (dq : dfrac)
      (ua : mword 64) (n : nat) (f : nat -> bv 8) :
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
    usrc_at N tx dq (uint ua) n f -∗
    ⌜ forall j : nat, (j < n)%nat ->
        M !! uint (add_vec_int ua (Z.of_nat j)) = Some (f j) ⌝.
  Proof using .
    iIntros "Hheap Hs". rewrite /usrc_at. destruct tx.
    - iDestruct (usrc_ok_utext (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ua n f
                   with "Hheap Hs") as %[Hok _].
      by iPureIntro.
    - iApply (uheap_ubytes_wat (ukn_t N) (ukn_d N) (ukn_s N) M pm sz dq ua n f
                with "Hheap Hs").
  Qed.

  (* THE WRITE LEAF AT A SOURCE: the data half's or the text half's, as the
     program's reading of its run selects *)
  Lemma cons_leaf (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (fdep : sfam) (l : list fdstate) (tx : bool) (dq : dfrac)
      (nb : nat) (f : nat -> bv 8) :
    usysno m = 16 ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepwf_std N m pc 16 fdep l -∗
    UserFd.ustd (ukn_fd N) l -∗
    usrc_at N tx dq (uint (m !!! Regidx a1_idx)) nb f -∗
    (∀ (h' : CpuId) (r : mword 64) (Wv : uvis) (cw' : Z) (cs' : gset gname),
       ⌜tf_w (uvis_tf Wv) (tf_arg_idx 0) = m !!! Regidx (mword_of_int 10)⌝ -∗
       ⌜tf_w (uvis_tf Wv) (tf_arg_idx 1) = m !!! Regidx (mword_of_int 11)⌝ -∗
       ⌜tf_w (uvis_tf Wv) (tf_arg_idx 2) = m !!! Regidx (mword_of_int 12)⌝ -∗
       ⌜take NSTD (uvis_fd Wv) = l⌝ -∗
       ⌜uvis_lazy Wv = false⌝ -∗
       ⌜ forall (Pt : uptd) (j : nat),
           ProcPtOwn.proc_pt_wf Pt ->
           perm_of (ud_um Pt) (uvis_sz Wv) = uvis_perm Wv ->
           lazy_free (ud_um Pt) (uvis_sz Wv) ->
           (j < nb)%nat ->
           UserPtTree.uva_rmapped Pt
             (uint (add_vec_int (m !!! Regidx (mword_of_int 11))
                      (Z.of_nat j))) ⌝ -∗
       UserFd.ustd (ukn_fd N) l -∗
       usrc_at N tx dq (uint (m !!! Regidx a1_idx)) nb f -∗
       spost_at uslot 16 fdep Wv r (uvis_M Wv) (uvis_fd Wv) cw' cs' -∗
       urun N h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal. rewrite /usrc_at. destruct tx.
    - iApply (wp_uk_ecall_write_chain_txt N h m pc avail fdep l nb f Hn Hal).
    - iApply (wp_uk_ecall_write_chain_buf N h m pc avail fdep l dq nb f Hn Hal).
  Qed.
End cons_src.

(* ===================================================================== *)
(*  S3  THE CLAIM-FREE CORE: the chain and the write law at an ABSTRACT   *)
(*      device (program-specs SS3.4d)                                     *)
(*                                                                        *)
(*  [cons_write] depends on the console claim ONLY through one byte as an *)
(*  [out_link] ([D_step]), the narrowing to the chosen alternative        *)
(*  ([D_sub]) and the count bound ([D_short]).  So the device is a        *)
(*  section variable with those three laws, and the chain and the write   *)
(*  law are stated once for every claim that has a byte law: the generic  *)
(*  claim (S3b below, at [GenLinksLine]'s link families) and the          *)
(*  pipeline's two-writer round ([UkPipeConsOut]).                        *)
(* ===================================================================== *)
Section UkConsOutCore.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{PS : UexecSG.uprogSG Σ}.
  (* the program instance, with its write stub's law *)
  Context (N : uk_names Σ) (P : uprog Σ).
  Context `{HPc : !Persistent (up_code P)}.
  Context (Hstub : ⊢ stub_law N (up_code P) 16 (up_write P)).
  (* THE DEVICE, owing one of its alternatives, and its three laws *)
  Context (D : list (list (bv 8)) -> iProp Σ).
  Context (D_short : forall alts : list (list (bv 8)), D alts -∗ ⌜cons_short alts⌝).
  Context (D_sub : forall (alts : list (list (bv 8))) (a : list (bv 8)),
             a ∈ alts -> D alts -∗ D [a]).
  Context (D_step : forall (x : list (bv 8)) (b : bv 8),
             x !! 0%nat = Some b ->
             D [x] -∗ out_link Uart0 (S gen_id) b (D [drop 1 x])).

  (* the era the console chain of a write is at *)
  Local Notation ke := (S gen_id).

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* THE CONSOLE CHAIN at the cursor [j ↦ D [drop j a]] *)
  Lemma cons_chain (a : list (bv 8)) (Mh : gmap Z (bv 8)) (ua : mword 64)
      (fb : nat -> bv 8) :
    forall (cnt j : nat),
    (forall t : nat, (j <= t)%nat -> (t < j + cnt)%nat -> a !! t = Some (fb t)) ->
    (forall t : nat, (j <= t)%nat -> (t < j + cnt)%nat ->
       Mh !! uint (add_vec_int ua (Z.of_nat t)) = Some (fb t)) ->
    D [drop j a] -∗
    cons_out_chain ke Mh ua (fun t : nat => D [drop t a]) j cnt.
  Proof using D_step.
    intros cnt. induction cnt as [| cnt IH]; intros j Ha HM.
    - iIntros "Hd". cbn [cons_out_chain]. iExact "Hd".
    - iIntros "Hd". cbn [cons_out_chain]. iSplit; [iExact "Hd" |].
      iIntros (b) "%Hbm".
      rewrite (HM j ltac:(lia) ltac:(lia)) in Hbm. injection Hbm as <-.
      iApply (out_link_mono Uart0 ke (fb j) (D [drop 1 (drop j a)])
                with "[] [Hd]").
      { iIntros "Hd". rewrite drop_drop.
        replace (j + 1)%nat with (S j) by lia.
        iApply (IH (S j) ltac:(intros t H1 H2; apply Ha; lia)
                  ltac:(intros t H1 H2; apply HM; lia) with "Hd"). }
      iApply (D_step with "Hd").
      rewrite lookup_drop Nat.add_0_r. apply Ha; lia.
  Qed.

  (* the deposit family row 16 is read at ([UEchoOut.kec_fam]'s mould) *)
  Definition cons_fam (Q : nat -> iProp Σ) : sfam := xfam_wr Q (ukn_pay N).

  (* =================================================================== *)
  (*  THE WRITE LAW: [UkHandler.ei_write] at the console                  *)
  (* =================================================================== *)
  Lemma cons_write (l : list fdstate) (fd : nat) (rb : bool)
      (alts : list (list (bv 8))) (a bs : list (bv 8)) (K : Z -> iProp Σ) :
    (fd < NSTD)%nat -> l !! fd = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    a ∈ alts -> bs `prefix_of` a ->
    UserFd.ustd (ukn_fd N) l -∗ D alts -∗
    (UserFd.ustd (ukn_fd N) l -∗ D [drop (length bs) a]
     -∗ K (Z.of_nat (length bs))) -∗
    wr_obl N P (Z.of_nat fd) bs K.
  Proof using D_short D_step D_sub HPc Hstub.
    intros Hfd Hl Ha Hpre. iIntros "Hstd Hd HK".
    iDestruct (D_sub alts a Ha with "Hd") as "Hd".
    iDestruct (D_short with "Hd") as %Hs.
    assert (Hn31 : (Z.of_nat (length bs) < 2 ^ 31)%Z).
    { unfold cons_short in Hs. rewrite Forall_singleton in Hs.
      eapply Z.le_lt_trans; [| exact Hs].
      apply Nat2Z.inj_le. exact (prefix_length _ _ Hpre). }
    rewrite /wr_obl.
    iIntros (h m avail ua tx dq f) "%Hf %Ha0 %Ha1 %Ha2 #Hcode Hsrc Hrun Hcont".
    (* the run's address, as the leaf spells it: the register's own word,
       which is [ua] wherever a byte is held *)
    iDestruct (urun_usrc_bnd N h m _ avail tx dq ua (length bs) f
                 with "Hrun Hsrc") as %Hbnd.
    assert (Hua : length bs = 0%nat \/ ua = uint (m !!! Regidx a1_idx)).
    { destruct (decide (length bs = 0%nat)) as [Hz | Hnz]; [by left | right].
      destruct (Hbnd 0%nat ltac:(lia)) as [Hlo Hhi].
      change (2 ^ 38) with 274877906944 in Hhi.
      rewrite Ha1. symmetry. apply uint_moi. unfold Z64. lia. }
    iEval (rewrite (usrc_at_rebase N tx dq ua (uint (m !!! Regidx a1_idx))
                      (length bs) f Hua)) in "Hsrc".
    iDestruct (usrc_at_split with "Hsrc") as "[Hs1 Hs2]".
    (* the three argument rows, at the register file the leaf runs on *)
    assert (Ham0 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham1 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham2 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a2_idx = m !!! Regidx a2_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Hi0 : bv_signed (trunc32
                    ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                       !!! Regidx a0_idx)) = Z.of_nat fd)
      by (rewrite Ham0; exact Ha0).
    pose proof (cons_count_is (length bs) Hn31) as Hcz.
    assert (Hcnt : Z.to_nat (sys_rw_count
                     ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                        !!! Regidx a2_idx)) = length bs)
      by (rewrite Ham2 Ha2 Hcz; lia).
    assert (Hsys : usysno (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m) = 16).
    { unfold usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 16 : mword 64)).
      vm_compute. reflexivity. }
    (* the bytes the program hands over ARE the chosen alternative's *)
    assert (Hab : forall t : nat, (t < length bs)%nat -> a !! t = Some (f t)).
    { intros t Ht. exact (prefix_lookup_Some _ _ _ _ (Hf t Ht) Hpre). }
    (* ---- THE STUB, to the ecall ---- *)
    iPoseProof Hstub as "Hst". rewrite /stub_law.
    iDestruct "Hst" as "#Hst".
    iApply ("Hst" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Hal6 Hec Hrun Hret".
    assert (Hal : is_aligned_vaddr
                    (Virtaddr (add_vec_int (mword_of_int (up_write P + 2) : mword 64) 4)) 2
                  = true) by (rewrite E6; exact Hal6).
    unfold stub_ret.
    iApply (cons_leaf N h1 (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
              _ avail
              (cons_fam (fun t : nat =>
                 (D [drop t a]
                  ∗ usrc_at N tx (dq_half dq) (uint (m !!! Regidx a1_idx))
                      (length bs) f)%I))
              l tx (dq_half dq) (length bs) f Hsys Hal
              with "Hec Hrun [Hd Hs2] Hstd [Hs1]").
    { (* THE DEPOSIT: the console chain at the device, and the half of the
         run the chain's premise is read off, handed back beside it *)
      iApply (uwrite_chain_sup_ret N (fun t : nat => D [drop t a])
                (usrc_at N tx (dq_half dq) (uint (m !!! Regidx a1_idx))
                   (length bs) f)
                _ _ l fd rb CONSOLE Hi0 Hfd Hl).
      iIntros (Mh pm sz) "Hheap".
      iDestruct (usrc_at_wat N Mh pm sz tx (dq_half dq) (m !!! Regidx a1_idx)
                   (length bs) f with "Hheap Hs2") as %HM.
      iFrame "Hheap Hs2".
      rewrite Ham1 Hcnt.
      iApply (cons_chain a Mh (m !!! Regidx a1_idx) f (length bs) 0%nat
                ltac:(intros t _ Ht; apply Hab; lia)
                ltac:(intros t _ Ht; apply HM; lia)
                with "[Hd]").
      rewrite drop_0. iExact "Hd". }
    { rewrite Ham1. iExact "Hs1". }
    iIntros (h' ret Wv cw' cs')
      "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hs1 Hpost Hrun".
    iDestruct (uwrite_no_short
                 (fun t : nat =>
                    (D [drop t a]
                     ∗ usrc_at N tx (dq_half dq) (uint (m !!! Regidx a1_idx))
                         (length bs) f)%I)
                 (ukn_pay N) Wv ret (uvis_M Wv) (uvis_fd Wv) cw' cs'
                 l fd rb (length bs)
                 ltac:(rewrite Hka0; exact Hi0)
                 Hfd Htk Hl
                 ltac:(rewrite Hka2 Ham2 Ha2; exact Hcz)
                 Hlz
                 ltac:(rewrite Hka1; exact Hnf)
                 with "Hpost") as "[%Hret HQ]".
    iDestruct "HQ" as "[Hd Hs2]".
    rewrite Ham1 E6.
    (* ---- THE STUB, back to the caller ---- *)
    iApply ("Hret" $! h' ret with "Hrun").
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "[HK Hstd Hd] [Hs1 Hs2] Hrun").
    - rewrite Hret bvsigned_moi_small;
        [| change (2 ^ 63) with 9223372036854775808; lia].
      iApply ("HK" with "Hstd Hd").
    - rewrite (usrc_at_rebase N tx dq ua (uint (m !!! Regidx a1_idx))
                 (length bs) f Hua).
      rewrite (usrc_at_split N tx dq). iFrame "Hs1 Hs2".
  Qed.
End UkConsOutCore.

(* ===================================================================== *)
(*  S3b THE GENERIC CLAIM'S DEVICE, at [GenLinksLine]'s link families     *)
(*                                                                        *)
(*  The device of the file header, over M2's link parameters              *)
(*  ([gen_params]) and a persistent links bundle [LINKS] that entails the *)
(*  three leaves a console byte needs ([gl_w], [gl_blk], [gl_taint]) --   *)
(*  which the file application ([FileLinkGen.file_links_gl]), echo and    *)
(*  the pipeline's single-writer rounds ([PipeLinksLine.pipe_links_gl])   *)
(*  all supply.  [LINKS] rides in the device so that a byte can spend it. *)
(* ===================================================================== *)
Section UkConsOutGen.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ}.
  Context `{PS : UexecSG.uprogSG Σ}.
  (* the model, M2's link parameters, and the links bundle *)
  Context (M : lmodel) (Pm : gen_params M).
  Context (LINKS : iProp Σ) {LINKS_pers : Persistent LINKS}.
  #[local] Existing Instance LINKS_pers.
  Context (LINKS_w : LINKS -∗ gl_w M Pm).
  Context (LINKS_blk : LINKS -∗ gl_blk M Pm).
  Context (LINKS_taint : LINKS -∗ gl_taint_at M Pm (S gen_id)).

  Local Notation T := (gT Pm).
  Local Notation PIN := (gPIN Pm).
  Local Notation W := (gW Pm).
  (* the era the console chain of a write is at *)
  Local Notation ke := (S gen_id).

  (* the era's cursor at a block of the stage, [i] bytes out, the first of
     which filed [c] ([GenLinksLine.gwc_blk]'s left arm) *)
  Definition cons_cur (v : era_pins) (ps cs : list nat) (s0 : lm_st M)
      (I : list (bv 8)) (pos c i : nat) : iProp Σ :=
    (turn v (pos + i)%nat ∗ ps_lb v ps ∗ cs_lb v (lm_blkcs cs c i)
     ∗ inp_lb v I ∗ W ke s0)%I.

  (* THE DEVICE AT A ROUND [(v, I)], owing one of [alts] (the file header
     has the encoding), with the links bundle folded in *)
  Definition cons_dev_at (v : era_pins) (I : list (bv 8))
      (alts : list (list (bv 8))) : iProp Σ :=
    (LINKS ∗ ⌜cons_short alts⌝
     ∗ ((∃ (ps cs : list nat) (s0 : lm_st M) (pos : nat),
           ⌜lm_wr_blk_t M ps cs s0 I pos⌝ ∗ PIN ke v
           ∗ ((∃ codes : list nat,
                 ⌜alts = lm_body M s0 cs I <$> codes⌝
                 ∗ ⌜Forall (cons_adm M s0 cs I) codes⌝
                 ∗ cons_cur v ps cs s0 I pos 0 0)
              ∨ (∃ c i : nat,
                   ⌜(0 < i)%nat⌝ ∗ ⌜(i <= length (lm_body M s0 cs I c))%nat⌝
                   ∗ ⌜cons_adm M s0 cs I c⌝
                   ∗ ⌜alts = [drop i (lm_body M s0 cs I c)]⌝
                   ∗ cons_cur v ps cs s0 I pos c i)))
        ∨ T))%I.

  (* THE DEVICE, at some round *)
  Definition cons_dev (alts : list (list (bv 8))) : iProp Σ :=
    (∃ (v : era_pins) (I : list (bv 8)), cons_dev_at v I alts)%I.

  (* THE DEVICE REMEMBERING THE CODES IT WAS LENT (program-specs SS3.4e,
     lane D): [cons_dev_at] with the unfiled codes drawn from [C] and the
     filed one in [C].  A drained device then names a code of [C] -- which
     is what an exit payload stated at the round's two or three codes
     needs and the code-free reader cannot give.
     [cons_dev_at] is this at some [C], and its step law is proved here. *)
  Definition cons_dev_atc (C : list nat) (v : era_pins) (I : list (bv 8))
      (alts : list (list (bv 8))) : iProp Σ :=
    (LINKS ∗ ⌜cons_short alts⌝
     ∗ ((∃ (ps cs : list nat) (s0 : lm_st M) (pos : nat),
           ⌜lm_wr_blk_t M ps cs s0 I pos⌝ ∗ PIN ke v
           ∗ ((∃ codes : list nat,
                 ⌜codes ⊆ C⌝
                 ∗ ⌜alts = lm_body M s0 cs I <$> codes⌝
                 ∗ ⌜Forall (cons_adm M s0 cs I) codes⌝
                 ∗ cons_cur v ps cs s0 I pos 0 0)
              ∨ (∃ c i : nat,
                   ⌜c ∈ C⌝ ∗ ⌜(0 < i)%nat⌝ ∗ ⌜(i <= length (lm_body M s0 cs I c))%nat⌝
                   ∗ ⌜cons_adm M s0 cs I c⌝
                   ∗ ⌜alts = [drop i (lm_body M s0 cs I c)]⌝
                   ∗ cons_cur v ps cs s0 I pos c i)))
        ∨ T))%I.

  Lemma cons_dev_atc_at (C : list nat) (v : era_pins) (I : list (bv 8))
      (alts : list (list (bv 8))) :
    cons_dev_atc C v I alts -∗ cons_dev_at v I alts.
  Proof using .
    iIntros "(Hlk & %Hs & Hd)". iSplitL "Hlk"; [iExact "Hlk" |]. iSplit; [done |].
    iDestruct "Hd" as "[Hd | HT]"; [| by iRight]. iLeft.
    iDestruct "Hd" as (ps cs s0 pos) "(%Hw & Hpin & Hd)". iExists ps, cs, s0, pos.
    iSplit; [done |]. iSplitL "Hpin"; [iExact "Hpin" |].
    iDestruct "Hd" as "[(%codes & %Hsub & %Hal & %Hadm & Hc)
                      | (%c & %i & %Hc & %Hi & %Hil & %Hadm & %Hal & Hc)]".
    - iLeft. iExists codes. iSplit; [done |]. iSplit; [done |]. iExact "Hc".
    - iRight. iExists c, i. iSplit; [done |]. iSplit; [done |]. iSplit; [done |].
      iSplit; [done |]. iExact "Hc".
  Qed.

  Lemma cons_dev_at_atc (v : era_pins) (I : list (bv 8)) (alts : list (list (bv 8))) :
    cons_dev_at v I alts -∗ ∃ C : list nat, cons_dev_atc C v I alts.
  Proof using .
    iIntros "(Hlk & %Hs & Hd)".
    iDestruct "Hd" as "[Hd | HT]".
    - iDestruct "Hd" as (ps cs s0 pos) "(%Hw & Hpin & Hd)".
      iDestruct "Hd" as "[(%codes & %Hal & %Hadm & Hc)
                        | (%c & %i & %Hi & %Hil & %Hadm & %Hal & Hc)]".
      + iExists codes. iSplitL "Hlk"; [iExact "Hlk" |]. iSplit; [done |]. iLeft.
        iExists ps, cs, s0, pos. iSplit; [done |]. iSplitL "Hpin"; [iExact "Hpin" |].
        iLeft. iExists codes. iSplit; [done |]. iSplit; [done |]. iSplit; [done |].
        iExact "Hc".
      + iExists [c]. iSplitL "Hlk"; [iExact "Hlk" |]. iSplit; [done |]. iLeft.
        iExists ps, cs, s0, pos. iSplit; [done |]. iSplitL "Hpin"; [iExact "Hpin" |].
        iRight. iExists c, i. iSplit; [iPureIntro; by apply elem_of_list_singleton |].
        iSplit; [done |]. iSplit; [done |]. iSplit; [done |]. iSplit; [done |].
        iExact "Hc".
    - iExists []. iSplitL "Hlk"; [iExact "Hlk" |]. iSplit; [done |]. by iRight.
  Qed.

  Lemma cons_dev_atc_short (C : list nat) (v : era_pins) (I : list (bv 8))
      (alts : list (list (bv 8))) :
    cons_dev_atc C v I alts -∗ ⌜cons_short alts⌝.
  Proof using . iIntros "(_ & $ & _)". Qed.

  Lemma cons_dev_atc_taint (C : list nat) (v : era_pins) (I : list (bv 8))
      (alts : list (list (bv 8))) :
    cons_short alts -> LINKS -∗ T -∗ cons_dev_atc C v I alts.
  Proof using .
    iIntros (Hs) "Hlk HT". iSplitL "Hlk"; [iExact "Hlk" |].
    iSplit; [done |]. by iRight.
  Qed.

  Lemma cons_dev_atc_sub (C : list nat) (v : era_pins) (I : list (bv 8))
      (alts : list (list (bv 8))) (a : list (bv 8)) :
    a ∈ alts -> cons_dev_atc C v I alts -∗ cons_dev_atc C v I [a].
  Proof using .
    intros Ha. iIntros "(Hlk & %Hs & Hd)". iSplitL "Hlk"; [iExact "Hlk" |].
    iSplit.
    { iPureIntro. unfold cons_short in *. apply Forall_singleton.
      exact (proj1 (Forall_forall _ _) Hs a (proj1 (elem_of_list_In _ _) Ha)). }
    iDestruct "Hd" as "[Hd | HT]"; [| by iRight]. iLeft.
    iDestruct "Hd" as (ps cs s0 pos) "(%Hw & Hpin & Hd)".
    iExists ps, cs, s0, pos.
    iSplit; [iPureIntro; exact Hw |]. iSplitL "Hpin"; [iExact "Hpin" |].
    iDestruct "Hd" as "[(%codes & %Hsub & %Hal & %Hadm & Hc)
                      | (%c & %i & %Hc & %Hi & %Hil & %Hadm & %Hal & Hc)]".
    - iLeft. subst alts. apply elem_of_list_fmap in Ha as (c & -> & Hc).
      iExists [c].
      iSplit; [iPureIntro; intros x Hx; apply elem_of_list_singleton in Hx as ->; by apply Hsub |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; apply Forall_singleton;
               exact (proj1 (Forall_forall _ _) Hadm c (proj1 (elem_of_list_In _ _) Hc)) |].
      iExact "Hc".
    - iRight. subst alts. apply elem_of_list_singleton in Ha as ->.
      iExists c, i.
      iSplit; [iPureIntro; exact Hc |].
      iSplit; [iPureIntro; exact Hi |].
      iSplit; [iPureIntro; exact Hil |].
      iSplit; [iPureIntro; exact Hadm |].
      iSplit; [iPureIntro; reflexivity |].
      iExact "Hc".
  Qed.

  (* ---- the three laws, at a round ---- *)
  Lemma cons_dev_at_short (v : era_pins) (I : list (bv 8)) (alts : list (list (bv 8))) :
    cons_dev_at v I alts -∗ ⌜cons_short alts⌝.
  Proof using . iIntros "(_ & $ & _)". Qed.

  Lemma cons_dev_at_taint (v : era_pins) (I : list (bv 8)) (alts : list (list (bv 8))) :
    cons_short alts -> LINKS -∗ T -∗ cons_dev_at v I alts.
  Proof using .
    iIntros (Hs) "Hlk HT". iSplitL "Hlk"; [iExact "Hlk" |].
    iSplit; [done |]. by iRight.
  Qed.

  (* the device narrows to the alternative the program chose *)
  Lemma cons_dev_at_sub (v : era_pins) (I : list (bv 8)) (alts : list (list (bv 8)))
      (a : list (bv 8)) :
    a ∈ alts -> cons_dev_at v I alts -∗ cons_dev_at v I [a].
  Proof using .
    intros Ha. iIntros "(Hlk & %Hs & Hd)". iSplitL "Hlk"; [iExact "Hlk" |].
    iSplit.
    { iPureIntro. unfold cons_short in *. apply Forall_singleton.
      exact (proj1 (Forall_forall _ _) Hs a (proj1 (elem_of_list_In _ _) Ha)). }
    iDestruct "Hd" as "[Hd | HT]"; [| by iRight]. iLeft.
    iDestruct "Hd" as (ps cs s0 pos) "(%Hw & Hpin & Hd)".
    iExists ps, cs, s0, pos.
    iSplit; [iPureIntro; exact Hw |]. iSplitL "Hpin"; [iExact "Hpin" |].
    iDestruct "Hd" as "[(%codes & %Hal & %Hadm & Hc)
                      | (%c & %i & %Hi & %Hil & %Hadm & %Hal & Hc)]".
    - iLeft. subst alts. apply elem_of_list_fmap in Ha as (c & -> & Hc).
      iExists [c].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; apply Forall_singleton;
               exact (proj1 (Forall_forall _ _) Hadm c (proj1 (elem_of_list_In _ _) Hc)) |].
      iExact "Hc".
    - iRight. subst alts. apply elem_of_list_singleton in Ha as ->.
      iExists c, i.
      iSplit; [iPureIntro; exact Hi |].
      iSplit; [iPureIntro; exact Hil |].
      iSplit; [iPureIntro; exact Hadm |].
      iSplit; [iPureIntro; reflexivity |].
      iExact "Hc".
  Qed.

  (* ONE BYTE: the head of what the device owes, through the three leaves
     ([gl_blk] at an unfiled device -- it files the code -- and [gl_w] at a
     filed one; the taint through [gl_taint]).  A byte of the body is the
     alternative's byte ([lm_body_lookup_Some]), so the leaves apply as
     they would at the whole alternative. *)
  Lemma cons_dev_atc_step (C : list nat) (v : era_pins) (I : list (bv 8))
      (x : list (bv 8)) (b : bv 8) :
    x !! 0%nat = Some b ->
    cons_dev_atc C v I [x] -∗ out_link Uart0 ke b (cons_dev_atc C v I [drop 1 x]).
  Proof using LINKS_blk LINKS_pers LINKS_taint LINKS_w.
    intros Hb. iIntros "(#Hlk & %Hs & Hd)".
    iDestruct (LINKS_w with "Hlk") as "#Hw".
    iDestruct (LINKS_blk with "Hlk") as "#Hblk".
    iDestruct (LINKS_taint with "Hlk") as "#Htaint".
    assert (Hs' : cons_short [drop 1 x]).
    { unfold cons_short in *. apply Forall_singleton. rewrite Forall_singleton in Hs.
      eapply Z.le_lt_trans; [| exact Hs].
      apply Nat2Z.inj_le. rewrite length_drop. lia. }
    iDestruct "Hd" as "[Hd | #HT]"; last first.
    { iApply ("Htaint" $! b with "HT").
      iIntros "#HT'". iApply (cons_dev_atc_taint C v I _ Hs' with "Hlk HT'"). }
    iDestruct "Hd" as (ps cs s0 pos) "(%Hw & #Hpin & Hd)".
    pose proof Hw as [Hwb Htl].
    pose proof Hwb as (Hpin0 & Hr & Hn & HP).
    iDestruct "Hd" as "[(%codes & %Hsub & %Hal & %Hadm & Hc)
                      | (%c & %i & %HcC & %Hi & %Hil & %Hadmc & %Hal & Hc)]".
    - (* UNFILED: the block's first byte files the code *)
      destruct codes as [| c [| c' codes]]; cbn [fmap list_fmap] in Hal;
        try discriminate.
      assert (HcC : c ∈ C) by (apply Hsub; by apply elem_of_list_singleton).
      injection Hal as Hx. subst x.
      rewrite Forall_singleton in Hadm. destruct Hadm as [Hok Hterm].
      pose proof (lookup_lt_Some _ _ _ Hb) as Hlen.
      pose proof (lm_body_lookup_Some M s0 cs I c 0%nat b Hb) as Hb'.
      iDestruct "Hc" as "(Ht & #Hps & #Hcs & #Hin & #HW)".
      cbn [lm_blkcs]. iEval (rewrite Nat.add_0_r) in "Ht".
      iApply ("Hblk" $! ke v pos c b ps cs s0 I
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin HW Ht Hps Hcs Hin").
      { exact (lm_wr_blk_nonnil M ps cs s0 I pos Hwb). }
      { exact Hr. } { lia. } { exact Hpin0. } { exact HP. }
      { exact Hok. } { exact Hterm. } { exact Hb'. }
      iIntros "[(Ht & _ & #Hcs' & _) | #HT]";
        last by iApply (cons_dev_atc_taint C v I _ Hs' with "Hlk HT").
      iSplitR; [iExact "Hlk" |].
      iSplit; [iPureIntro; exact Hs' |]. iLeft. iExists ps, cs, s0, pos.
      iSplit; [iPureIntro; exact Hw |]. iSplit; [iExact "Hpin" |].
      iRight. iExists c, 1%nat.
      iSplit; [iPureIntro; exact HcC |].
      iSplit; [iPureIntro; lia |].
      iSplit; [iPureIntro; lia |].
      iSplit; [iPureIntro; split; [exact Hok | exact Hterm] |].
      iSplit; [iPureIntro; reflexivity |].
      rewrite /cons_cur. cbn [lm_blkcs].
      replace (pos + 1)%nat with (S pos) by lia.
      iFrame "Ht Hps Hcs' Hin HW".
    - (* FILED at [c], [i] bytes out: an ordinary byte of the stream *)
      injection Hal as Hx. subst x.
      rewrite lookup_drop Nat.add_0_r in Hb.
      pose proof (lookup_lt_Some _ _ _ Hb) as Hlen.
      pose proof (lm_body_lookup_Some M s0 cs I c i b Hb) as Hb'.
      destruct i as [| i']; [lia |].
      iDestruct "Hc" as "(Ht & #Hps & #Hcs & #Hin & #HW)". cbn [lm_blkcs].
      iApply ("Hw" $! ke v (pos + S i')%nat b ps (cs ++ [c]) s0 I
                with "[%] [%] [%] Hpin HW Ht Hps Hcs Hin").
      { rewrite length_app /=. lia. }
      { exact (lm_wr_blk_pin_snoc M ps cs s0 I pos c Hwb). }
      { exact (cons_blk_byte M ps cs s0 I pos c (S i') b Hwb Hb'). }
      iIntros "[(Ht & _ & _ & _) | #HT]";
        last by iApply (cons_dev_atc_taint C v I _ Hs' with "Hlk HT").
      iSplitR; [iExact "Hlk" |].
      iSplit; [iPureIntro; exact Hs' |]. iLeft. iExists ps, cs, s0, pos.
      iSplit; [iPureIntro; exact Hw |]. iSplit; [iExact "Hpin" |].
      iRight. iExists c, (S (S i')).
      iSplit; [iPureIntro; exact HcC |].
      iSplit; [iPureIntro; lia |].
      iSplit; [iPureIntro; lia |].
      iSplit; [iPureIntro; exact Hadmc |].
      iSplit.
      { iPureIntro. f_equal. rewrite drop_drop. f_equal. lia. }
      rewrite /cons_cur. cbn [lm_blkcs].
      replace (pos + S (S i'))%nat with (S (pos + S i')) by lia.
      iFrame "Ht Hps Hcs Hin HW".
  Qed.

  (* ...and the code-free device's step, off it *)
  Lemma cons_dev_at_step (v : era_pins) (I : list (bv 8)) (x : list (bv 8)) (b : bv 8) :
    x !! 0%nat = Some b ->
    cons_dev_at v I [x] -∗ out_link Uart0 ke b (cons_dev_at v I [drop 1 x]).
  Proof using LINKS_blk LINKS_pers LINKS_taint LINKS_w.
    intros Hb. iIntros "Hd".
    iDestruct (cons_dev_at_atc with "Hd") as (C) "Hd".
    iApply (out_link_mono Uart0 ke b (cons_dev_atc C v I [drop 1 x]) with "[] [Hd]").
    { iIntros "Hd". iApply (cons_dev_atc_at with "Hd"). }
    iApply (cons_dev_atc_step C v I x b Hb with "Hd").
  Qed.

  (* ---- the three laws at the round-free device ---- *)
  Lemma cons_dev_short (alts : list (list (bv 8))) :
    cons_dev alts -∗ ⌜cons_short alts⌝.
  Proof using .
    iIntros "(%v & %I & Hd)". iApply (cons_dev_at_short with "Hd").
  Qed.

  Lemma cons_dev_taint (v : era_pins) (I : list (bv 8)) (alts : list (list (bv 8))) :
    cons_short alts -> LINKS -∗ T -∗ cons_dev alts.
  Proof using .
    iIntros (Hs) "Hlk HT". iExists v, I. iApply (cons_dev_at_taint v I _ Hs with "Hlk HT").
  Qed.

  Lemma cons_dev_sub (alts : list (list (bv 8))) (a : list (bv 8)) :
    a ∈ alts -> cons_dev alts -∗ cons_dev [a].
  Proof using .
    intros Ha. iIntros "(%v & %I & Hd)". iExists v, I.
    iApply (cons_dev_at_sub v I alts a Ha with "Hd").
  Qed.

  Lemma cons_dev_step (x : list (bv 8)) (b : bv 8) :
    x !! 0%nat = Some b ->
    cons_dev [x] -∗ out_link Uart0 ke b (cons_dev [drop 1 x]).
  Proof using LINKS_blk LINKS_pers LINKS_taint LINKS_w.
    intros Hb. iIntros "(%v & %I & Hd)".
    iApply (out_link_mono Uart0 ke b (cons_dev_at v I [drop 1 x]) with "[] [Hd]").
    { iIntros "Hd". iExists v, I. iExact "Hd". }
    iApply (cons_dev_at_step v I x b Hb with "Hd").
  Qed.

  (* =================================================================== *)
  (*  THE READERS (program-specs SS3.4e): the lend at a block's first    *)
  (*  byte, the cursor at the body's end off a drained device, and that  *)
  (*  cursor as [gwc_post]                                               *)
  (* =================================================================== *)

  (* THE LEND: [gwc_blk … 0 0]'s left arm, named, at the admissible codes
     the caller chooses to owe *)
  Lemma cons_dev_at_of_blk0 (v : era_pins) (I : list (bv 8)) (ps cs : list nat)
      (s0 : lm_st M) (pos : nat) (codes : list nat) :
    lm_wr_blk_t M ps cs s0 I pos ->
    Forall (cons_adm M s0 cs I) codes ->
    cons_short (lm_body M s0 cs I <$> codes) ->
    LINKS -∗ PIN ke v -∗ cons_cur v ps cs s0 I pos 0 0 -∗
    cons_dev_at v I (lm_body M s0 cs I <$> codes).
  Proof using .
    intros Hw Hadm Hs. iIntros "Hlk Hpin Hc".
    iSplitL "Hlk"; [iExact "Hlk" |]. iSplit; [iPureIntro; exact Hs |].
    iLeft. iExists ps, cs, s0, pos. iSplit; [iPureIntro; exact Hw |].
    iSplitL "Hpin"; [iExact "Hpin" |]. iLeft. iExists codes.
    iSplit; [iPureIntro; reflexivity |]. iSplit; [iPureIntro; exact Hadm |].
    iExact "Hc".
  Qed.

  (* THE DRAINED DEVICE: nothing left to write means the cursor is at the
     body's end of the code it filed -- or, at an EMPTY body, still at the
     block's first byte, which is the same cursor (no code filed, none
     needed: [lm_blkcs cs c 0 = cs]) -- or the taint *)
  Lemma cons_dev_at_drained (v : era_pins) (I : list (bv 8)) :
    cons_dev_at v I [[]] -∗
    LINKS
    ∗ (T ∨ ∃ (ps cs : list nat) (s0 : lm_st M) (pos c : nat),
             ⌜lm_wr_blk_t M ps cs s0 I pos⌝ ∗ ⌜cons_adm M s0 cs I c⌝ ∗ PIN ke v
             ∗ cons_cur v ps cs s0 I pos c (length (lm_body M s0 cs I c))).
  Proof using .
    iIntros "(Hlk & _ & Hd)". iSplitL "Hlk"; [iExact "Hlk" |].
    iDestruct "Hd" as "[Hd | HT]"; [| by iLeft]. iRight.
    iDestruct "Hd" as (ps cs s0 pos) "(%Hw & Hpin & Hd)".
    iDestruct "Hd" as "[(%codes & %Hal & %Hadm & Hc)
                      | (%c & %i & %Hi & %Hil & %Hadm & %Hal & Hc)]".
    - destruct codes as [| c [| c' codes]]; cbn [fmap list_fmap] in Hal;
        try discriminate.
      injection Hal as Hx.
      rewrite Forall_singleton in Hadm.
      iExists ps, cs, s0, pos, c.
      iSplit; [iPureIntro; exact Hw |]. iSplit; [iPureIntro; exact Hadm |].
      iSplitL "Hpin"; [iExact "Hpin" |].
      rewrite -Hx. cbn [length]. rewrite /cons_cur. cbn [lm_blkcs]. iExact "Hc".
    - injection Hal as Hx.
      apply (f_equal length) in Hx. rewrite length_drop in Hx. cbn [length] in Hx.
      iExists ps, cs, s0, pos, c.
      iSplit; [iPureIntro; exact Hw |]. iSplit; [iPureIntro; exact Hadm |].
      iSplitL "Hpin"; [iExact "Hpin" |].
      replace (length (lm_body M s0 cs I c)) with i by lia.
      iExact "Hc".
  Qed.

  (* THE SAME TWO READERS AT THE CODES: the lend at codes drawn from [C],
     and the drained device naming the code of [C] it filed *)
  Lemma cons_dev_atc_of_blk0 (C : list nat) (v : era_pins) (I : list (bv 8))
      (ps cs : list nat) (s0 : lm_st M) (pos : nat) (codes : list nat) :
    lm_wr_blk_t M ps cs s0 I pos ->
    codes ⊆ C ->
    Forall (cons_adm M s0 cs I) codes ->
    cons_short (lm_body M s0 cs I <$> codes) ->
    LINKS -∗ PIN ke v -∗ cons_cur v ps cs s0 I pos 0 0 -∗
    cons_dev_atc C v I (lm_body M s0 cs I <$> codes).
  Proof using .
    intros Hw Hsub Hadm Hs. iIntros "Hlk Hpin Hc".
    iSplitL "Hlk"; [iExact "Hlk" |]. iSplit; [iPureIntro; exact Hs |].
    iLeft. iExists ps, cs, s0, pos. iSplit; [iPureIntro; exact Hw |].
    iSplitL "Hpin"; [iExact "Hpin" |]. iLeft. iExists codes.
    iSplit; [iPureIntro; exact Hsub |].
    iSplit; [iPureIntro; reflexivity |]. iSplit; [iPureIntro; exact Hadm |].
    iExact "Hc".
  Qed.

  Lemma cons_dev_atc_drained (C : list nat) (v : era_pins) (I : list (bv 8)) :
    cons_dev_atc C v I [[]] -∗
    LINKS
    ∗ (T ∨ ∃ (ps cs : list nat) (s0 : lm_st M) (pos c : nat),
             ⌜lm_wr_blk_t M ps cs s0 I pos⌝ ∗ ⌜c ∈ C⌝ ∗ ⌜cons_adm M s0 cs I c⌝ ∗ PIN ke v
             ∗ cons_cur v ps cs s0 I pos c (length (lm_body M s0 cs I c))).
  Proof using .
    iIntros "(Hlk & _ & Hd)". iSplitL "Hlk"; [iExact "Hlk" |].
    iDestruct "Hd" as "[Hd | HT]"; [| by iLeft]. iRight.
    iDestruct "Hd" as (ps cs s0 pos) "(%Hw & Hpin & Hd)".
    iDestruct "Hd" as "[(%codes & %Hsub & %Hal & %Hadm & Hc)
                      | (%c & %i & %HcC & %Hi & %Hil & %Hadm & %Hal & Hc)]".
    - destruct codes as [| c [| c' codes]]; cbn [fmap list_fmap] in Hal;
        try discriminate.
      injection Hal as Hx.
      rewrite Forall_singleton in Hadm.
      iExists ps, cs, s0, pos, c.
      iSplit; [iPureIntro; exact Hw |].
      iSplit; [iPureIntro; apply Hsub; by apply elem_of_list_singleton |].
      iSplit; [iPureIntro; exact Hadm |].
      iSplitL "Hpin"; [iExact "Hpin" |].
      rewrite -Hx. cbn [length]. rewrite /cons_cur. cbn [lm_blkcs]. iExact "Hc".
    - injection Hal as Hx.
      apply (f_equal length) in Hx. rewrite length_drop in Hx. cbn [length] in Hx.
      iExists ps, cs, s0, pos, c.
      iSplit; [iPureIntro; exact Hw |]. iSplit; [iPureIntro; exact HcC |].
      iSplit; [iPureIntro; exact Hadm |].
      iSplitL "Hpin"; [iExact "Hpin" |].
      replace (length (lm_body M s0 cs I c)) with i by lia.
      iExact "Hc".
  Qed.

  (* the cursor at the body's end IS [gwc_post]: the block written up to
     its prompt, at the round's own state *)
  Lemma cons_cur_gwc_post (v : era_pins) (ps cs : list nat) (s0 : lm_st M)
      (I : list (bv 8)) (pos c : nat) :
    lm_wr_blk_t M ps cs s0 I pos ->
    cons_cur v ps cs s0 I pos c (length (lm_body M s0 cs I c)) -∗
    gwc_post M Pm ke v I c.
  Proof using .
    intros Hw. rewrite /cons_cur /gwc_post (lm_body_length M s0 cs I c).
    iIntros "(Ht & Hps & Hcs & Hin & HW)". iLeft. iExists ps, cs, s0, pos.
    iSplit; [iPureIntro; exact Hw |]. iFrame "Ht Hps Hcs Hin HW".
  Qed.

  (* THE CORE AT THIS DEVICE: the write law of any program instance, at a
     round and at the round-free device *)
  Section gen_prog.
    Context (N : uk_names Σ) (P : uprog Σ).
    Context `{HPc : !Persistent (up_code P)}.
    Context (Hstub : ⊢ stub_law N (up_code P) 16 (up_write P)).

    Lemma cons_write_gl_at (v : era_pins) (I : list (bv 8))
        (l : list fdstate) (fd : nat) (rb : bool)
        (alts : list (list (bv 8))) (a bs : list (bv 8)) (K : Z -> iProp Σ) :
      (fd < NSTD)%nat -> l !! fd = Some (FdOpen rb true (FdDevice CONSOLE)) ->
      a ∈ alts -> bs `prefix_of` a ->
      UserFd.ustd (ukn_fd N) l -∗ cons_dev_at v I alts -∗
      (UserFd.ustd (ukn_fd N) l -∗ cons_dev_at v I [drop (length bs) a]
       -∗ K (Z.of_nat (length bs))) -∗
      wr_obl N P (Z.of_nat fd) bs K.
    Proof using HPc Hstub LINKS_blk LINKS_pers LINKS_taint LINKS_w.
      exact (cons_write N P Hstub (cons_dev_at v I) (cons_dev_at_short v I)
               (cons_dev_at_sub v I) (cons_dev_at_step v I) l fd rb alts a bs K).
    Qed.

    Lemma cons_write_gl_atc (C : list nat) (v : era_pins) (I : list (bv 8))
        (l : list fdstate) (fd : nat) (rb : bool)
        (alts : list (list (bv 8))) (a bs : list (bv 8)) (K : Z -> iProp Σ) :
      (fd < NSTD)%nat -> l !! fd = Some (FdOpen rb true (FdDevice CONSOLE)) ->
      a ∈ alts -> bs `prefix_of` a ->
      UserFd.ustd (ukn_fd N) l -∗ cons_dev_atc C v I alts -∗
      (UserFd.ustd (ukn_fd N) l -∗ cons_dev_atc C v I [drop (length bs) a]
       -∗ K (Z.of_nat (length bs))) -∗
      wr_obl N P (Z.of_nat fd) bs K.
    Proof using HPc Hstub LINKS_blk LINKS_pers LINKS_taint LINKS_w.
      exact (cons_write N P Hstub (cons_dev_atc C v I) (cons_dev_atc_short C v I)
               (cons_dev_atc_sub C v I) (cons_dev_atc_step C v I) l fd rb alts a bs K).
    Qed.

    Lemma cons_write_gl (l : list fdstate) (fd : nat) (rb : bool)
        (alts : list (list (bv 8))) (a bs : list (bv 8)) (K : Z -> iProp Σ) :
      (fd < NSTD)%nat -> l !! fd = Some (FdOpen rb true (FdDevice CONSOLE)) ->
      a ∈ alts -> bs `prefix_of` a ->
      UserFd.ustd (ukn_fd N) l -∗ cons_dev alts -∗
      (UserFd.ustd (ukn_fd N) l -∗ cons_dev [drop (length bs) a]
       -∗ K (Z.of_nat (length bs))) -∗
      wr_obl N P (Z.of_nat fd) bs K.
    Proof using HPc Hstub LINKS_blk LINKS_pers LINKS_taint LINKS_w.
      exact (cons_write N P Hstub cons_dev cons_dev_short cons_dev_sub
               cons_dev_step l fd rb alts a bs K).
    Qed.
  End gen_prog.
End UkConsOutGen.

(* ===================================================================== *)
(*  S4  THE WITNESSES: the law at echo and at cat, at the FILE            *)
(*      application's links ([FileLinkGen.file_links_gl] at [file_params]) *)
(* ===================================================================== *)
Section UkConsOutInst.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  (* [FileLinkGen]'s classes *)
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context (g : file_gn).
  Context (N : uk_names Σ).

  (* the three leaves, off the file application's links *)
  Lemma file_links_gl_w : file_links g -∗ gl_w file_lm (file_params g).
  Proof using .
    iIntros "Hlk". iDestruct (file_links_gl g with "Hlk") as "(H & _)". iExact "H".
  Qed.
  Lemma file_links_gl_blk : file_links g -∗ gl_blk file_lm (file_params g).
  Proof using .
    iIntros "Hlk". iDestruct (file_links_gl g with "Hlk") as "(_ & H & _)". iExact "H".
  Qed.
  Lemma file_links_gl_taint : file_links g -∗ gl_taint_at file_lm (file_params g) (S gen_id).
  Proof using .
    iIntros "%Hc".
    iApply (gcl_gl_taint_at file_lm (file_cparams g) ∅ (file_wa g) Hc
              (file_params g) eq_refl (S gen_id)).
  Qed.

  Local Notation fcons_dev := (cons_dev file_lm (file_params g) (file_links g)).

  Local Instance cat_prog_code_persistent : Persistent (up_code (cat_prog N)).
  Proof using . simpl. apply _. Qed.

  Lemma cons_write_echo (l : list fdstate) (fd : nat) (rb : bool)
      (alts : list (list (bv 8))) (a bs : list (bv 8)) (K : Z -> iProp Σ) :
    (fd < NSTD)%nat -> l !! fd = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    a ∈ alts -> bs `prefix_of` a ->
    UserFd.ustd (ukn_fd N) l -∗ fcons_dev alts -∗
    (UserFd.ustd (ukn_fd N) l -∗ fcons_dev [drop (length bs) a]
     -∗ K (Z.of_nat (length bs))) -∗
    wr_obl N (echo_prog N) (Z.of_nat fd) bs K.
  Proof using .
    exact (cons_write_gl file_lm (file_params g) (file_links g)
             (LINKS_pers := file_links_persistent g)
             file_links_gl_w file_links_gl_blk file_links_gl_taint
             N (echo_prog N) (echo_stub_write N) l fd rb alts a bs K).
  Qed.

  Lemma cons_write_cat (l : list fdstate) (fd : nat) (rb : bool)
      (alts : list (list (bv 8))) (a bs : list (bv 8)) (K : Z -> iProp Σ) :
    (fd < NSTD)%nat -> l !! fd = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    a ∈ alts -> bs `prefix_of` a ->
    UserFd.ustd (ukn_fd N) l -∗ fcons_dev alts -∗
    (UserFd.ustd (ukn_fd N) l -∗ fcons_dev [drop (length bs) a]
     -∗ K (Z.of_nat (length bs))) -∗
    wr_obl N (cat_prog N) (Z.of_nat fd) bs K.
  Proof using .
    exact (cons_write_gl file_lm (file_params g) (file_links g)
             (LINKS_pers := file_links_persistent g)
             file_links_gl_w file_links_gl_blk file_links_gl_taint
             N (cat_prog N) (cat_stub_write N) l fd rb alts a bs K).
  Qed.
End UkConsOutInst.
