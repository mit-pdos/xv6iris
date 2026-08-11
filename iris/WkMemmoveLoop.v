(** * WkMemmoveLoop.v — memmove's copy loop under WEAK memory, INTERRUPTIBLE.

    THE EXPERIMENT.  [WeakSmodeFrame] showed that an objective frame survives
    three [wp_next] crossings.  Three straight-line instructions is not a
    function: the questions that decide whether the weak port can carry
    S-mode code are about a LOOP, and this file asks them on the smallest
    piece of real kernel code that has one — memmove's forward byte-copy
    loop, [ProofMemmove.mm_loop], five instructions at [memmove+0x18..+0x24]:

      +0x18  c.addi a1,1        cursor++            (source)
      +0x1a  c.addi a4,1        cursor++            (destination)
      +0x1c  lbu   a3,-1(a1)    the byte
      +0x20  sb    a3,-1(a4)    the byte
      +0x24  bne   a5,a1        back to +0x18 unless done

    FOUR QUESTIONS, AND THIS FILE IS THE ANSWER TO ALL FOUR.

    1. **Can a loop invariant be stated objectively?**  A loop that can be
       interrupted is a loop whose invariant must survive migration, so it
       may not mention a hart or a [wstate].  Here it does not: the two
       buffers are [cobj ξ ([∗ list] …)] and the induction is
       [ProofMemmove]'s own [induction rem], unchanged.
    2. **Does the byte-buffer frame really compose?**  Both buffers are
       peeled per iteration by [WeakCtx.cobj_sep] over a [big_sepL] cons —
       the [rewrite (seq_cons …)] SC does, under the modality.
    3. **What does the 1-byte store owe?**  Nothing: [wssb1_spec] is
       objective-in / objective-out with NO released timestamp.  A store into
       a cell the context owns exclusively publishes nothing, so the release
       interface [WeakLeafO.wwp_sd8_tor_rvc_run] carries (the [T], the
       floor, the frozen payload) is simply absent.  That is the difference
       between a lock release and a private write, and it is why this leaf
       fits the [wp_next] shape unchanged.
    4. **Is a fence needed anywhere?**  NO — and that is the headline.  The
       proof below contains no fence, no view arithmetic, no timestamp and
       no [wstate].  memmove runs entirely inside one context; whatever
       synchronisation its caller needed was paid at the lock, once, and
       nothing in the loop re-pays it.

    THE LEAVES ARE HYPOTHESES, NOT AXIOMS — [WeakSmodeFrame]'s discipline,
    and for its reason: the S-mode weak funnel (privilege, trap delegation,
    and above all a FETCH THAT IS A PAGE-TABLE WALK over racy A/D
    write-backs — batch 6) does not exist yet, so these five leaves cannot be
    proved here.  Stated as [Prop]s and taken as section hypotheses they make
    the loop a real theorem — "given leaves of this shape, this proof goes
    through" — and add nothing to the trusted base.  Batch 6 discharges them
    without touching a line below.

    THEY ARE FILE-BASED, DELIBERATELY.  Each hypothesis takes the whole
    register file (inside [wsrun]) and hands it back, exactly as its SC twin
    ([WpSconfMem.wp_sb_s_sconf] & co.) does — NOT the two raw [↦ᵣ] cells the
    M-mode batch-2 leaves take.  That is the one measured difference between
    the converted M-mode chains and their SC twins (weak-memory.md's
    conversion slice), so stating these the SC way is also the experiment
    that shows the residual overhead is the cell/file interface and not weak
    memory.  Count the tactics against [mm_loop]'s and see. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RegFile WpGpr InstrBytes.
Require Import WpNext WpSconfMem ByteCursor.
Require Import WeakMem WeakInterp WeakLang WeakView WeakVProp WeakGhost.
Require Import WeakViewMono WeakWord8 WeakCtx.
Require Import WeakFunnel WeakLeafM.
Require Import WeakSmodeFrame.
From Kernel Require KernelSyms.

Import SailStdpp.Values.

Local Open Scope Z_scope.

(* [ProofMemmove]'s own list lemma, [Local] there. *)
Local Lemma seq_cons (start len : nat) : seq start (S len) = start :: seq (S start) len.
Proof. reflexivity. Qed.

(* ====================================================================== *)
(** ** 1. The five leaves, in [wp_next] form over [wsrun] / [cobj].

    Compare each with the SC leaf named in its comment: same binders, same
    premises, same postcondition — with [sie_cap_gpr m n b p] replaced by
    [WeakSmodeFrame.wsrun ξ m], [instr] by [winstr_m], every byte
    points-to by an objective [cobj ξ (… ↦w …)], and the SC file's
    [wp_next] left exactly where it was. *)

Section leaf_specs.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId}.

  (** [c.addi rd, imm] — register-only, touches no [cobj].
      SC: [WpSconfItype.wp_caddi_s_sconf]. *)
  Definition wscaddi_spec : Prop :=
    ∀ (CID0 : CpuId) (ξ : CtxId) (b : bool) (p : mword 64)
      (pc : mword 64) (rd : mword 5) (imm : mword 6) (m : regfile),
    uint rd <> 0 ->
    ⊢ ( wsrun ξ m -∗
        pc_is pc -∗
        winstr_m pc true
          (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI)) -∗
        wp_next b p (fun CID : CpuId =>
          wsrun ξ (<[Regidx rd :=
                     regval_into_reg (add_vec (m !!! Regidx rd)
                                        (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
          pc_is (add_vec_int pc 2) -∗
          WWP Loop) -∗
        WWP Loop ).

  (** [lbu rd, imm(rs1)] — ONE byte, from a cell the context owns.
      SC: [WpSconfMem.wp_lbu_s_sconf]. *)
  Definition wslbu1_spec : Prop :=
    ∀ (CID0 : CpuId) (ξ : CtxId) (b : bool) (p : mword 64)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (m : regfile)
      (v : mword 8) (dq : dfrac),
    uint rd <> 0 ->
    ⊢ ( wsrun ξ m -∗
        pc_is pc -∗
        winstr_m pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 1)) -∗
        cobj ξ (pa_z (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                  ↦w{dq} v) -∗
        wp_next b p (fun CID : CpuId =>
          wsrun ξ (<[Regidx rd := regval_into_reg (zero_extend' 64 v)]> m) -∗
          pc_is (add_vec_int pc 4) -∗
          cobj ξ (pa_z (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                    ↦w{dq} v) -∗
          WWP Loop) -∗
        WWP Loop ).

  (** [sb rs2, imm(rs1)] — ONE byte, into a cell the context owns
      EXCLUSIVELY.  NO released timestamp, NO floor, NO frozen payload: a
      private write publishes nothing.  SC: [WpSconfMem.wp_sb_s_sconf]. *)
  Definition wssb1_spec : Prop :=
    ∀ (CID0 : CpuId) (ξ : CtxId) (b : bool) (p : mword 64)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12) (m : regfile)
      (vold : mword 8),
    ⊢ ( wsrun ξ m -∗
        pc_is pc -∗
        winstr_m pc false (STORE (imm, Regidx rs2, Regidx rs1, 1)) -∗
        cobj ξ (pa_z (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                  ↦w vold) -∗
        wp_next b p (fun CID : CpuId =>
          wsrun ξ m -∗
          pc_is (add_vec_int pc 4) -∗
          cobj ξ (pa_z (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                    ↦w (trunc8 (m !!! Regidx rs2))) -∗
          WWP Loop) -∗
        WWP Loop ).

  (** [bne rs1, rs2, imm], TAKEN — a backward branch, so the continuation is
      guarded.  SC: [WpSconfBranch.wp_bne_taken_s_sconf]. *)
  Definition wsbne_taken_spec : Prop :=
    ∀ (CID0 : CpuId) (ξ : CtxId) (b : bool) (p : mword 64)
      (pc : mword 64) (imm : mword 13) (rs1 rs2 : mword 5) (m : regfile),
    neq_vec (m !!! Regidx rs2) (m !!! Regidx rs1) = true ->
    is_aligned_vaddr (Virtaddr (add_vec pc (sign_extend' 64 imm))) 2 = true ->
    ⊢ ( wsrun ξ m -∗
        pc_is pc -∗
        winstr_m pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
        ▷ wp_next b p (fun CID : CpuId =>
            wsrun ξ m -∗
            pc_is (add_vec pc (sign_extend' 64 imm)) -∗
            WWP Loop) -∗
        WWP Loop ).

  (** [bne rs1, rs2, imm], FALLING THROUGH.
      SC: [WpSconfBranch.wp_bne_fall_s_sconf]. *)
  Definition wsbne_fall_spec : Prop :=
    ∀ (CID0 : CpuId) (ξ : CtxId) (b : bool) (p : mword 64)
      (pc : mword 64) (imm : mword 13) (rs1 rs2 : mword 5) (m : regfile),
    neq_vec (m !!! Regidx rs2) (m !!! Regidx rs1) = false ->
    ⊢ ( wsrun ξ m -∗
        pc_is pc -∗
        winstr_m pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
        wp_next b p (fun CID : CpuId =>
          wsrun ξ m -∗
          pc_is (add_vec_int pc 4) -∗
          WWP Loop) -∗
        WWP Loop ).

End leaf_specs.

(* ====================================================================== *)
(** ** 2. THE LOOP.

    [ProofMemmove.mm_loop]'s statement under the swaps, and its proof
    structure line for line: [induction rem], the same two harts kept apart
    ([CIDh] anchors the caller's [wp_next] and is a LEMMA parameter, outside
    the [forall rem off m]; [CID0] is this iteration's entry hart and changes
    at every recursive step, with [Hchain] threading "still traces back to
    [CIDh]").

    WHAT IS NOT HERE is the point: no [ws], no [ws_le], no [vwp_hold], no
    [vwp_hold_mono], no timestamp, no fence.  The two buffers are named twice
    each — in and out — and the untouched TAIL of each buffer crosses five
    [wp_next] binders without being mentioned. *)

Section loop.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId}.

  (* the five leaves, as hypotheses *)
  Context (Hcaddi : wscaddi_spec) (Hlbu : wslbu1_spec) (Hsb : wssb1_spec)
          (Hbne_t : wsbne_taken_spec) (Hbne_f : wsbne_fall_spec).

  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).

  Local Definition mmpc (off : Z) : mword 64 :=
    mword_of_int (KernelSyms.memmove + off).

  (** The byte buffer, objectively: [ProofMemmove]'s
      [[∗ list] j ∈ seq off rem, (pa_add p j) ↦ₘ bs j] with [↦ₘ] swapped for
      the weak byte points-to and each byte made objective.

      IT IS IRIS'S [big_sepL], UNCHANGED.  There is no weak-memory list
      connective and none is wanted: [cobj] is applied per byte, the list
      itself is the ordinary one, and the loop's peel below is SC's own
      [seq_cons] -- a [big_opL] on a cons IS a separating conjunction, so
      nothing is rewritten under a modality and no lemma about lists and
      [cobj] is needed.  (One exists -- [WeakCtx.cobj_big_sepL], which
      commutes [cobj] with [big_sepL] -- and it is what a caller holding a
      whole region as ONE [cobj] would spend to get bytes out.  This proof
      never needs it.) *)
  Local Definition wbuf (ξ : CtxId) (p : mword 64) (off rem : nat)
      (bs : nat -> bv 8) : iProp Σ :=
    ([∗ list] j ∈ seq off rem, cobj ξ ((pa_z (pa_add p j)) ↦w bs j))%I.

  Lemma wbuf_cons (ξ : CtxId) (p : mword 64) (off rem : nat) (bs : nat -> bv 8) :
    wbuf ξ p off (S rem) bs
    ⊣⊢ cobj ξ ((pa_z (pa_add p off)) ↦w bs off) ∗ wbuf ξ p (S off) rem bs.
  Proof. rewrite /wbuf (seq_cons off rem) //. Qed.

  Lemma wmm_loop (ξ : CtxId)
      (p_src p_dst : mword 64) (len : nat) (src_bytes dst_olds : nat -> bv 8)
      (b : bool) (pcur : mword 64) (CIDh : CpuId) :
    (Z.of_nat len < 2 ^ 64)%Z ->
    forall (rem off : nat) (m : regfile) (CID0 : CpuId),
    (b = false \/ pcur = zero_reg -> (CID0 : CPU) = (CIDh : CPU)) ->
    (off + rem = len)%nat -> (1 <= rem)%nat ->
    m !!! Regidx a1_idx = pa_add p_src off ->
    m !!! Regidx a4_idx = pa_add p_dst off ->
    m !!! Regidx a5_idx = add_vec (mword_of_int (Z.of_nat len) : mword 64) p_src ->
    wsrun ξ m -∗
    pc_is (mmpc 0x18) -∗
    winstr_m (mmpc 0x18) true
      (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx a1_idx,
              Regidx a1_idx, ADDI)) -∗
    winstr_m (mmpc 0x1a) true
      (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx a4_idx,
              Regidx a4_idx, ADDI)) -∗
    winstr_m (mmpc 0x1c) false
      (LOAD (mword_of_int 0xfff, Regidx a1_idx, Regidx a3_idx, false, 1)) -∗
    winstr_m (mmpc 0x20) false
      (STORE (mword_of_int 0xfff, Regidx a3_idx, Regidx a4_idx, 1)) -∗
    winstr_m (mmpc 0x24) false
      (BTYPE (mword_of_int 0x1ff4, Regidx a5_idx, Regidx a1_idx, BNE)) -∗
    wbuf ξ p_src off rem src_bytes -∗
    wbuf ξ p_dst off rem dst_olds -∗
    wp_next (CID0 := CIDh) b pcur (fun CID : CpuId =>
      ∀ mf,
      wsrun ξ mf -∗
      pc_is (mmpc 0x28) -∗
      wbuf ξ p_src off rem src_bytes -∗
      wbuf ξ p_dst off rem src_bytes -∗
      ⌜ mf !!! Regidx (mword_of_int 10 : mword 5)
        = m !!! Regidx (mword_of_int 10 : mword 5) ⌝ -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hlen64.
    (* pure cursor arithmetic, [ProofMemmove]'s verbatim *)
    assert (Hstep : forall (p : mword 64) (j : nat),
              add_vec (pa_add p j)
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
              = pa_add p (S j)).
    { intros p j. apply pa_add_step. apply bv_eq; vm_compute; reflexivity. }
    assert (Hback : forall (p : mword 64) (j : nat),
              add_vec (pa_add p (S j))
                (sign_extend' 64 (mword_of_int 0xfff : mword 12))
              = pa_add p j).
    { intros p j. apply pa_add_back1. apply bv_eq; vm_compute; reflexivity. }
    induction rem as [| rem' IH]; intros off m CID0 Hchain Hsum Hrem Ha1 Ha4 Ha5;
      [ exfalso; lia |].
    iIntros "Hrun Hpc #Hi18 #Hi1a #Hi1c #Hi20 #Hi24 Hsrc Hdst Hcont".
    (* peel the byte at [off] off both buffers, under the modality *)
    iEval (rewrite wbuf_cons) in "Hsrc". iDestruct "Hsrc" as "[Hs0 Hsrc]".
    iEval (rewrite wbuf_cons) in "Hdst". iDestruct "Hdst" as "[Hd0 Hdst]".

    (* ---- +0x18: c.addi a1,1 ---- *)
    iApply (Hcaddi CID0 ξ b pcur (mmpc 0x18) a1_idx (mword_of_int 1) m
              ltac:(vm_compute; discriminate) with "Hrun Hpc Hi18").
    iIntros (CID1) "%Hs1 Hrun Hpc".
    assert (Hp1a : add_vec_int (mmpc 0x18) 2 = mmpc 0x1a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    set (m1 := <[Regidx a1_idx := regval_into_reg
          (add_vec (m !!! Regidx a1_idx)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> m).

    (* ---- +0x1a: c.addi a4,1 ---- *)
    iApply (Hcaddi CID1 ξ b pcur (mmpc 0x1a) a4_idx (mword_of_int 1) m1
              ltac:(vm_compute; discriminate) with "Hrun Hpc Hi1a").
    iIntros (CID2) "%Hs2 Hrun Hpc".
    assert (Hp1c : add_vec_int (mmpc 0x1a) 2 = mmpc 0x1c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c) in "Hpc".
    set (m2 := <[Regidx a4_idx := regval_into_reg
          (add_vec (m1 !!! Regidx a4_idx)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> m1).
    (* both cursors are now one past the byte about to be copied *)
    assert (Hm1a4 : m1 !!! Regidx a4_idx = pa_add p_dst off).
    { unfold m1. rewrite upd_ne; [exact Ha4 | vm_compute; discriminate]. }
    assert (Ha1_2 : m2 !!! Regidx a1_idx = pa_add p_src (S off)).
    { unfold m2. rewrite upd_ne; [| vm_compute; discriminate].
      unfold m1. rewrite upd_eq. unfold regval_into_reg. rewrite Ha1. apply Hstep. }
    assert (Ha4_2 : m2 !!! Regidx a4_idx = pa_add p_dst (S off)).
    { unfold m2. rewrite upd_eq. unfold regval_into_reg. rewrite Hm1a4. apply Hstep. }
    assert (Ha5_2 : m2 !!! Regidx a5_idx
                    = add_vec (mword_of_int (Z.of_nat len) : mword 64) p_src).
    { unfold m2, m1. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite upd_ne; [| vm_compute; discriminate]. exact Ha5. }

    (* ---- +0x1c: lbu a3,-1(a1) ---- *)
    iApply (Hlbu CID2 ξ b pcur (mmpc 0x1c) a3_idx a1_idx (mword_of_int 0xfff) m2
              (src_bytes off : mword 8) (DfracOwn 1) ltac:(vm_compute; discriminate)
              with "Hrun Hpc Hi1c [Hs0]").
    { iEval (rewrite Ha1_2 (Hback p_src off)). iExact "Hs0". }
    iIntros (CID3) "%Hs3 Hrun Hpc Hs0".
    assert (Hp20 : add_vec_int (mmpc 0x1c) 4 = mmpc 0x20)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp20) in "Hpc".
    iEval (rewrite Ha1_2 (Hback p_src off)) in "Hs0".
    set (m3 := <[Regidx a3_idx :=
                 regval_into_reg (zero_extend' 64 (src_bytes off : mword 8))]> m2).

    (* ---- +0x20: sb a3,-1(a4) ---- *)
    assert (Ha3v : m3 !!! Regidx a3_idx = zero_extend' 64 (src_bytes off : mword 8))
      by (unfold m3; apply upd_eq).
    assert (Ha4v : m3 !!! Regidx a4_idx = pa_add p_dst (S off)).
    { unfold m3. rewrite upd_ne; [| vm_compute; discriminate]. exact Ha4_2. }
    iApply (Hsb CID3 ξ b pcur (mmpc 0x20) a3_idx a4_idx (mword_of_int 0xfff) m3
              (dst_olds off : mword 8) with "Hrun Hpc Hi20 [Hd0]").
    { iEval (rewrite Ha4v (Hback p_dst off)). iExact "Hd0". }
    iIntros (CID4) "%Hs4 Hrun Hpc Hd0".
    assert (Hp24 : add_vec_int (mmpc 0x20) 4 = mmpc 0x24)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    iEval (rewrite Ha4v (Hback p_dst off) Ha3v trunc8_zext8) in "Hd0".

    (* ---- +0x24: bne a5,a1 ---- *)
    assert (Ha1_3 : m3 !!! Regidx a1_idx = pa_add p_src (S off)).
    { unfold m3. rewrite upd_ne; [| vm_compute; discriminate]. exact Ha1_2. }
    assert (Ha5_3 : m3 !!! Regidx a5_idx
                    = add_vec (mword_of_int (Z.of_nat len) : mword 64) p_src).
    { unfold m3. rewrite upd_ne; [| vm_compute; discriminate]. exact Ha5_2. }
    assert (Hcmp : neq_vec (m3 !!! Regidx a5_idx) (m3 !!! Regidx a1_idx)
                   = negb (Nat.eqb (S off) len)).
    { rewrite Ha1_3 Ha5_3 neq_vec_comm.
      apply pa_add_cmp_bound; [ exact Hlen64 | lia ]. }
    assert (Ha0eq : m3 !!! Regidx (mword_of_int 10 : mword 5)
                    = m !!! Regidx (mword_of_int 10 : mword 5)).
    { unfold m3, m2, m1. repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      reflexivity. }
    destruct rem' as [| rem''].
    - (* last byte: the cursor has reached a5, so the bne falls through *)
      assert (Hfall : neq_vec (m3 !!! Regidx a5_idx) (m3 !!! Regidx a1_idx) = false).
      { rewrite Hcmp. replace (S off) with len by lia. rewrite Nat.eqb_refl. reflexivity. }
      iApply (Hbne_f CID4 ξ b pcur (mmpc 0x24) (mword_of_int 0x1ff4) a1_idx a5_idx
                m3 Hfall with "Hrun Hpc Hi24").
      iIntros (CID5) "%Hs5 Hrun Hpc".
      assert (Hp28 : add_vec_int (mmpc 0x24) 4 = mmpc 0x28)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp28) in "Hpc".
      iSpecialize ("Hcont" $! CID5 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! m3 with "Hrun Hpc [Hs0 Hsrc] [Hd0 Hdst] [%]").
      + rewrite wbuf_cons. iSplitL "Hs0"; [iExact "Hs0"|iExact "Hsrc"].
      + rewrite wbuf_cons. iSplitL "Hd0"; [iExact "Hd0"|iExact "Hdst"].
      + exact Ha0eq.
    - (* more bytes: the bne is taken back to +0x18 *)
      assert (Htaken : neq_vec (m3 !!! Regidx a5_idx) (m3 !!! Regidx a1_idx) = true).
      { rewrite Hcmp. destruct (Nat.eqb_spec (S off) len) as [He | Hne];
          [ exfalso; lia | reflexivity ]. }
      iApply (Hbne_t CID4 ξ b pcur (mmpc 0x24) (mword_of_int 0x1ff4) a1_idx a5_idx
                m3 Htaken ltac:(vm_compute; reflexivity) with "Hrun Hpc Hi24").
      iNext. iIntros (CID5) "%Hs5 Hrun Hpc".
      assert (Hback18 : add_vec (mmpc 0x24) (sign_extend' 64 (mword_of_int 0x1ff4 : mword 13))
                        = mmpc 0x18) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hback18) in "Hpc".
      assert (Hchain' : b = false \/ pcur = zero_reg -> (CID5 : CPU) = (CIDh : CPU))
        by wp_next_chain.
      iApply (IH (S off) m3 CID5 Hchain' ltac:(lia) ltac:(lia) Ha1_3 Ha4v Ha5_3
                with "Hrun Hpc Hi18 Hi1a Hi1c Hi20 Hi24 Hsrc Hdst").
      iIntros (CIDr) "%Hsr %mf Hrun Hpc Hsrc Hdst %Ha0f".
      iSpecialize ("Hcont" $! CIDr with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "Hrun Hpc [Hs0 Hsrc] [Hd0 Hdst] [%]").
      + rewrite wbuf_cons. iSplitL "Hs0"; [iExact "Hs0"|iExact "Hsrc"].
      + rewrite wbuf_cons. iSplitL "Hd0"; [iExact "Hd0"|iExact "Hdst"].
      + rewrite Ha0f. exact Ha0eq.
  Qed.

End loop.
