(* ===================================================================== *)
(* UkRun.v -- THE RUNNING PREDICATE, and the leaf interface above it.     *)
(*                                                                        *)
(* [UserHeap.uheap] is the memory half: two ghost_map authorities against  *)
(* the image, the segment facts, the break and the slack.  THIS file      *)
(* packages that together with the machine bundle into the one thing a    *)
(* user-program proof ever holds:                                          *)
(*                                                                        *)
(*   urun γt γd γs m pc                                                    *)
(*                                                                        *)
(* -- "the process is running, with general registers [m] at pc [pc]".     *)
(* Everything else is INSIDE, existentially: the hart, the loop-constant   *)
(* config, the page table, the residue the trap loop threads, [p->sz], the *)
(* memory image and the permission map.  None of them matter to a user     *)
(* program, and none of them appear in a leaf statement.                   *)
(*                                                                        *)
(* WHY THE EXISTENTIAL AMBIENT IS THE WHOLE TRICK.  Today every leaf       *)
(* consumes a bundle at ONE ambient but demands a continuation good at     *)
(* EVERY ambient ([UexecRet.ukc]'s ∀), because an interrupt may hand the   *)
(* process back on a different hart under a different table.  The program  *)
(* pays for that mismatch by re-introducing five binders after every       *)
(* instruction -- [rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb"],  *)
(* seventy-six times in UkEcho.v alone.  Packing the ambient inside [urun] *)
(* makes the caller's continuation [urun ... m' pc' -* WP] good at any       *)
(* ambient BY CONSTRUCTION, so the leaf absorbs the quantifier and the     *)
(* program never sees it.  [ukc] then has nothing left to name.            *)
(*                                                                        *)
(* THE SPLIT BETWEEN REGISTERS AND MEMORY IS DELIBERATE.  Registers are a  *)
(* whole file inside [urun]: there is no framing to be had -- the slot's   *)
(* key is the trapframe, so every instruction's obligation mentions all of *)
(* them anyway.  Memory is the opposite: fragments live OUTSIDE [urun] and *)
(* a leaf names exactly the bytes it touches, so everything else frames.   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile InstrBytes.
Require Import UserPtTree UserExec ProcPtOwn.
Require Import UmodeMem UmodeArith UmodeAbi.
Require Import UserPerm UsysMemOk UexecWp UexecSlot UexecRet.
Require Import WpMmodeLeafBase.
Require Import UmodeFetch.
Require Import WpUmodeStore.
Require Import UkStep UkLeaf UkStore.
Require Import UserHeap.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.


(* ===================================================================== *)
(* WpUmodeStore's store-run and UserPtTree's are the same map.  The two   *)
(* build it from opposite ends -- [uM_store] folds index 0 outermost,     *)
(* [umem_write] recurses with index n-1 outermost -- so they are equal    *)
(* but not convertible.  The heap speaks [umem_write]; the store leaves   *)
(* speak [uM_store8]; this is the one lemma that lets a leaf wrapper hand *)
(* one to the other.                                                     *)
(* ===================================================================== *)
Lemma uM_store_umem_write (M : gmap Z (bv 8)) (a : Z) (n : nat) (v : mword 64) :
  uM_store M a (Z.of_nat n) v = umem_write M a n (nth_byte v).
Proof.
  apply map_eq. intro k.
  destruct (decide (a <= k < a + Z.of_nat n)) as [Hin | Hout].
  - assert (Hj : (Z.to_nat (k - a) < n)%nat) by lia.
    replace k with (a + Z.of_nat (Z.to_nat (k - a))) by lia.
    rewrite (uM_store_lookup M a (Z.of_nat n) v _
               ltac:(rewrite Nat2Z.id; exact Hj)).
    rewrite (umem_write_lookup_in M a n (nth_byte v) _ Hj). reflexivity.
  - rewrite (uM_store_lookup_ne M a (Z.of_nat n) v k
               ltac:(intros j Hj; rewrite Nat2Z.id in Hj; lia)).
    rewrite (umem_write_lookup_out M a n (nth_byte v) k
               ltac:(intros j Hj; lia)).
    reflexivity.
Qed.

Lemma uM_store8_umem_write (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  uM_store8 M a v = umem_write M a 8 (nth_byte v).
Proof. exact (uM_store_umem_write M a 8%nat v). Qed.

Section UkRun.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  (* NO ambient [CpuId]: the hart is an explicit argument of [urun], and the
     [WP] under that binder resolves to the one bound there -- the trick
     [UexecRet.ukc] uses. *)
  Context `{!ghost_varG Σ Z}.

  (* ===================================================================== *)
  (* §1 THE RUNNING PREDICATE.                                             *)
  (* ===================================================================== *)
  Definition urun (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64) : iProp Σ :=
    (∃ (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z)
       (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm),
       ⌜ loop_ok C pt ⌝ ∗ ⌜ perm_of (ud_um pt) sz = pm ⌝ ∗
       uheap γt γd γs M pm ∗
       uvb (CID := h) C pt Rut sz pm M m pc)%I.

  (* THE CLOSE.  This is the lemma that makes the whole interface work: a
     continuation phrased on [urun] discharges the ∀-quantified [ukc] that
     every existing leaf demands, because [urun] supplies its own ambient. *)
  Lemma urun_close (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (m : regfile) (pc : mword 64) :
    uheap γt γd γs M pm -∗
    (∀ h : CpuId, urun γt γd γs h m pc -∗ WP (Loop : expr riscv_lang)) -∗
    ukc pm M m pc.
  Proof.
    iIntros "Hheap Hcont".
    rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    iApply ("Hcont" $! h). iExists C, pt, Rut, sz, M, pm.
    iFrame "Hheap Hb". iPureIntro. split; [ exact Hlo | exact Hpm ].
  Qed.

  (* ===================================================================== *)
  (* §2 THE FETCH BRIDGE.                                                  *)
  (*                                                                       *)
  (* [uinstr_is] plus the heap gives the Prop-level decode fact the         *)
  (* existing engine consumes.  Every clause of [UmodeMem.uinstr] comes off *)
  (* a text fragment except [ui_inpage], which is TEMPORARY: it is here     *)
  (* only until WpUmodeStep's [uv_fetch_base_2] takes the second halfword's *)
  (* leaf as a premise instead of deriving it from the window being on one  *)
  (* page.  The source for that premise is the fragment at [uint pc + 2],   *)
  (* which this lemma already has in hand.                                  *)
  (* ===================================================================== *)
  Lemma uheap_text_byte (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (a : Z) (b : bv 8) :
    uheap γt γd γs M pm -∗ utext γt a b -∗
    ⌜ M !! a = Some b /\ forall pt sz, proc_pt_wf pt ->
        perm_of (ud_um pt) sz = pm -> uva_fetch_leaf pt (mword_of_int a) ⌝.
  Proof.
    iIntros "Hheap Hb".
    iDestruct (uheap_text with "Hheap Hb") as %(HM & (q & Hq & Hx) & Hbnd).
    iPureIntro. split; [ exact HM | ].
    intros pt sz Hwf Hpmeq.
    unfold uperm_at in Hq. rewrite <- Hpmeq in Hq.
    destruct (perm_of_X pt sz _ q Hwf Hq Hx) as (w & Hw & Hok).
    exists w. exact (conj Hw Hok).
  Qed.


  (* the byte AT THE PC gives the two things every branch of the bridge needs:
     the pc is canonical, and its page is fetch-ok at any table realizing the
     key.  Factored out so the three decode shapes below do not triplicate it. *)
  Lemma uheap_text_pc (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (pc : mword 64) (b : bv 8) :
    uheap γt γd γs M pm -∗ utext γt (uint pc + Z.of_nat 0) b -∗
    ⌜ uva_canon pc /\
      forall pt sz, proc_pt_wf pt -> perm_of (ud_um pt) sz = pm ->
                    uva_fetch_leaf pt pc ⌝.
  Proof.
    iIntros "Hheap Hb".
    iDestruct (uheap_text_byte with "Hheap Hb") as %(_ & Hlf).
    iDestruct (uheap_text with "Hheap Hb") as %(_ & _ & Hbnd).
    iPureIntro.
    change (Z.of_nat 0) with 0 in Hbnd, Hlf. rewrite Z.add_0_r in Hbnd, Hlf.
    destruct (ucanon_of_bound (uint pc) Hbnd) as [_ Hcan].
    rewrite moi_of_uint in Hcan, Hlf.
    exact (conj Hcan Hlf).
  Qed.

  (* THE BRIDGE: [uinstr_is] plus the heap gives the Prop-level decode fact
     the existing engine consumes.  Every clause of [UmodeMem.uinstr] comes
     off a text fragment -- the leaf and canonicity from the byte at the pc,
     the code bytes from the run -- except [ui_inpage], which [uinstr_is]
     still carries for its one remaining consumer. *)
  Lemma uinstr_is_uk_instr (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (pc : mword 64) (is_rvc : bool) (i : instruction) :
    uheap γt γd γs M pm -∗ uinstr_is γt pc is_rvc i -∗
    ⌜ uk_instr pm M pc is_rvc i ⌝.
  Proof.
    iIntros "Hheap #Hi". rewrite /uinstr_is.
    iDestruct "Hi" as "(%Hal2 & %Hpg & Hcode)".
    destruct is_rvc.
    - iDestruct "Hcode" as (h) "(%HisRVC & %Hdec & Hbs)".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + (* compressed at a 4-ALIGNED pc: the window IS a 4-byte word whose
           low half is the halfword *)
        iDestruct "Hbs" as (w) "(%Hlow & #Hbs)".
        iDestruct (uheap_text_run with "Hheap Hbs") as %Hb4.
        iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbs") as "#H0";
          [ reflexivity | ].
        iDestruct (uheap_text_pc with "Hheap H0") as %[Hcanon Hlf].
        iPureIntro. intros pt sz Hwf Hpmeq.
        refine (UInstr pt M pc true i Hal2 Hcanon (Hlf pt sz Hwf Hpmeq) Hpg _).
        exists h. split_and!; [ exact HisRVC | | exact Hdec | ].
        * intros j Hj. rewrite <- Hlow.
          rewrite (nth_byte_subrange_lo w j ltac:(lia)).
          exact (Hb4 j ltac:(lia)).
        * intros _. exists (nth_byte w 2), (nth_byte w 3).
          pose proof (Hb4 2%nat ltac:(lia)) as H2.
          pose proof (Hb4 3%nat ltac:(lia)) as H3.
          change (Z.of_nat 2) with 2 in H2. change (Z.of_nat 3) with 3 in H3.
          exact (conj H2 H3).
      + (* compressed at a 2-mod-4 pc: two bytes, no trailing obligation *)
        iDestruct "Hbs" as "#Hbs".
        iDestruct (uheap_text_run with "Hheap Hbs") as %Hb2.
        iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbs") as "#H0";
          [ reflexivity | ].
        iDestruct (uheap_text_pc with "Hheap H0") as %[Hcanon Hlf].
        iPureIntro. intros pt sz Hwf Hpmeq.
        refine (UInstr pt M pc true i Hal2 Hcanon (Hlf pt sz Hwf Hpmeq) Hpg _).
        exists h. split_and!; [ exact HisRVC | exact Hb2 | exact Hdec | ].
        intros Hc. rewrite Hc in Hal4. discriminate Hal4.
    - iDestruct "Hcode" as (w) "(%HnRVC & %Hdec & #Hbs)".
      iDestruct (uheap_text_run with "Hheap Hbs") as %Hb4.
      iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbs") as "#H0";
        [ reflexivity | ].
      iDestruct (uheap_text_pc with "Hheap H0") as %[Hcanon Hlf].
      iPureIntro. intros pt sz Hwf Hpmeq.
      refine (UInstr pt M pc false i Hal2 Hcanon (Hlf pt sz Hwf Hpmeq) Hpg _).
      exists w. split_and!; [ exact HnRVC | exact Hb4 | exact Hdec ].
  Qed.


  (* ===================================================================== *)
  (* §3 THE LEAVES.                                                        *)
  (*                                                                       *)
  (* Two representatives, one register-only and one memory, cut in the     *)
  (* shape every remaining leaf will take:                                 *)
  (*                                                                       *)
  (*   the instruction resource, the memory the instruction TOUCHES, the   *)
  (*   run, and a continuation at the updated run.                         *)
  (*                                                                       *)
  (* No ambient, no [ukc], no postcondition, and the immediate in NORMAL   *)
  (* FORM.  Everything the instruction does not touch frames, because it   *)
  (* is either inside [urun] (registers, image, table, permissions) or     *)
  (* outside and unmentioned (every other byte).                           *)
  (* ===================================================================== *)

  (* the data byte AT a virtual address: canonical, and WRITABLE.  This is
     where the permission table stops being visible -- the caller holds an
     exclusive [ubyte], and the heap turns that into the leaf's [uk_store_ok]
     without the caller ever naming a page or a PTE bit. *)
  Lemma uheap_udata_va (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (va : mword 64) (b : bv 8) :
    uheap γt γd γs M pm -∗ ubyte γd (uint va + Z.of_nat 0) b -∗
    ⌜ uva_canon va /\
      exists q : uperm, uperm_at pm va = Some q /\ up_W q = true ⌝.
  Proof.
    iIntros "Hheap Hb".
    iDestruct (uheap_ubyte with "Hheap Hb") as %(_ & (q & Hq & Hw) & Hbnd).
    iPureIntro.
    change (Z.of_nat 0) with 0 in Hbnd, Hq. rewrite Z.add_0_r in Hbnd, Hq.
    destruct (ucanon_of_bound (uint va) Hbnd) as [_ Hcan].
    rewrite moi_of_uint in Hcan, Hq.
    split; [ exact Hcan | exists q; exact (conj Hq Hw) ].
  Qed.

  (* the same, off a whole owned word.  Consuming the run INSIDE this proof
     is free: the conclusion is pure, so the caller's [iDestruct … as %…]
     keeps both the heap and the word. *)
  Lemma uheap_uword_va (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (va : mword 64) (w : mword 64) :
    uheap γt γd γs M pm -∗ uword γd (uint va) w -∗
    ⌜ uva_canon va /\
      exists q : uperm, uperm_at pm va = Some q /\ up_W q = true ⌝.
  Proof.
    iIntros "Hheap Hw". rewrite /uword /ubytes.
    iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hw") as "H0";
      [ reflexivity | ].
    iApply (uheap_udata_va with "Hheap H0").
  Qed.

  (* a run of owned data bytes is present in the image, at its own values *)
  Lemma uheap_ubytes_mapped (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (a : Z) (n : nat) (f : nat -> bv 8) :
    uheap γt γd γs M pm -∗ ubytes γd a n f -∗
    ⌜ forall j : nat, (j < n)%nat -> M !! (a + Z.of_nat j)%Z = Some (f j) ⌝.
  Proof.
    iIntros "Hheap Hbs". rewrite /ubytes.
    iInduction n as [| n IH] "IH" forall (f).
    - iPureIntro. intros j Hj. exfalso. lia.
    - iEval (rewrite seq_S big_sepL_app /=) in "Hbs".
      iDestruct "Hbs" as "(Hlo & Hhi & _)".
      iDestruct (uheap_ubyte with "Hheap Hhi") as %(HM & _ & _).
      (* the IH is generalised over [f], so instantiate that before feeding it *)
      iDestruct ("IH" $! f with "Hheap Hlo") as %Hlo.
      iPureIntro. intros j Hj.
      destruct (decide (j = n)) as [-> | Hne]; [ exact HM | apply Hlo; lia ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.li rd, imm -- rd := sext(imm).  THE register-only shape.           *)
  (*                                                                     *)
  (* The immediate is [sign_extend' 64 imm], not the decoder's            *)
  (* [add_vec x0 (sign_extend' 64 (sign_extend' 12 imm))]: the expansion  *)
  (* chain is the model's business and [uimm6_norm] discharges it here,   *)
  (* once, rather than at every call site.                                *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_cli (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 6) (rd : mword 5) :
    uint rd <> 0 ->
    uinstr_is γt pc true (C_LI (imm, Regidx rd)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h'
         (<[Regidx rd := regval_into_reg (sign_extend' 64 imm : mword 64)]> m)
         (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hrd. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cli C pt Rut pm sz Hlo Hpm M m pc imm rd
              (sign_extend' 64 imm) Hui Hrd (eq_sym (uimm6_norm imm))
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.sdsp rs2, uimm(sp) -- THE memory shape, and the point of the whole  *)
  (* exercise: the caller hands over the eight bytes it is about to        *)
  (* clobber and gets them back holding the stored value.  Every other     *)
  (* byte of the process frames, untouched and unmentioned.                *)
  (*                                                                      *)
  (* Note what is NOT a premise: writability.  The old leaf demanded       *)
  (* [uk_store_ok tgt] -- an explicit claim about the permission map --    *)
  (* and every caller had to produce one.  Here it comes out of the        *)
  (* EXCLUSIVE ownership of the bytes, which is the invariant [uheap]      *)
  (* maintains.  Nor is presence in the image, nor canonicity, nor the     *)
  (* in-page condition: an 8-aligned address has [rem 4096] a multiple of  *)
  (* 8 below 4096, hence at most 4088, so alignment alone gives it.        *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_csdsp (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (uimm : mword 6) (rs2 : mword 5) (tgt v0 : mword 64) :
    tgt = add_vec (m !!! Regidx csp_rs1)
            (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000")))) ->
    is_aligned_vaddr (Virtaddr tgt) 8 = true ->
    uinstr_is γt pc true (C_SDSP (uimm, Regidx rs2)) -∗
    uword γd (uint tgt) v0 -∗
    urun γt γd γs h m pc -∗
    (uword γd (uint tgt) (m !!! Regidx rs2) -∗
       ∀ h' : CpuId,
         urun γt γd γs h' m (add_vec_int pc 2) -∗ WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Htgt Hal8. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    (* the target is canonical, and writable -- from OWNERSHIP, not a PTE *)
    iDestruct (uheap_uword_va with "Hheap Hw") as %[Hcanon Hok].
    (* all eight are present in the image *)
    iDestruct (uheap_ubytes_mapped γt γd γs M pm (uint tgt) 8 (nth_byte v0)
                 with "Hheap Hw") as %Hmap.
    (* the in-page condition, from alignment alone *)
    assert (Hrem : Z.rem (uint tgt) 4096 <= 4088).
    { pose proof (ualign_page_off tgt 8 ltac:(lia)
                    ltac:(exists 512; reflexivity) Hal8) as Hm8.
      rewrite uint_unsigned.
      rewrite Z.rem_mod_nonneg;
        [ | exact (proj1 (bv_unsigned_in_range _ tgt)) | lia ].
      pose proof (Z.mod_pos_bound (bv_unsigned tgt) 4096 ltac:(lia)) as Hb.
      pose proof (Z.div_mod (bv_unsigned tgt mod 4096) 8 ltac:(lia)) as Hdm.
      lia. }
    (* do the write in the ghost heap, then hand the image to the leaf *)
    iMod (uheap_store_run γt γd γs M pm (uint tgt) 8 (nth_byte v0)
            (nth_byte (m !!! Regidx rs2)) with "Hheap Hw") as "(Hheap & Hw)".
    iApply (UkStore.wp_uk_csdsp C pt Rut pm sz Hlo Hpm M m pc uimm rs2
              tgt (m !!! Regidx rs2) Hui Htgt eq_refl Hok Hcanon Hrem Hal8
              ltac:(intros j Hj; exists (nth_byte v0 j); exact (Hmap j Hj))
              with "Hb [Hheap Hw Hcont]").
    rewrite uM_store8_umem_write.
    iApply (urun_close with "Hheap"). iApply ("Hcont" with "Hw").
  Qed.

End UkRun.
