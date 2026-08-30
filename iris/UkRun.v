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
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RegFile InstrBytes.
Require Import UserPtTree UserExec ProcPtOwn.
Require Import UmodeMem UmodeArith.
Require Import UserPerm UexecWp UexecSlot UexecRet.
Require Import WpMmodeLeafBase.
Require Import UptTree.
Require Import WpUmodeStore.
Require Import WpUmodeStep.
Require Import UkStep.
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
  (* [avail] is the FREE STACK, in words, below the current sp -- the
     user-mode twin of [sie_cap_gpr]'s counting argument.  The process owns
     it; an sp-adjust hands a frame out of it or takes one back; every other
     instruction threads it unchanged, which is why every leaf that writes a
     register takes [unot_sp] as a premise (a write to sp would move the
     index this ownership is keyed by). *)
  Definition urun (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) : iProp Σ :=
    (∃ (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z)
       (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm),
       ⌜ loop_ok C pt ⌝ ∗ ⌜ perm_of (ud_um pt) sz = pm ⌝ ∗
       uheap γt γd γs M pm ∗
       ustack γd (m !!! Regidx csp_rs1) avail ∗
       uvb (CID := h) C pt Rut sz pm M m pc)%I.

  (* "this instruction does not write sp".  Every leaf that writes a general
     register carries it; a concrete [rd] decides it by [vm_compute]. *)
  Definition unot_sp (rd : mword 5) : Prop := Regidx csp_rs1 <> Regidx rd.

  Lemma unot_sp_upd (rd : mword 5) (v : mword 64) (m : regfile) :
    unot_sp rd -> (<[Regidx rd := v]> m) !!! Regidx csp_rs1 = m !!! Regidx csp_rs1.
  Proof. intro H. exact (upd_ne m (Regidx rd) (Regidx csp_rs1) v H). Qed.

  (* THE CLOSE.  This is the lemma that makes the whole interface work: a
     continuation phrased on [urun] discharges the ∀-quantified [ukc] that
     every existing leaf demands, because [urun] supplies its own ambient. *)
  Lemma urun_close (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (m : regfile) (pc : mword 64) (avail : nat) :
    uheap γt γd γs M pm -∗
    ustack γd (m !!! Regidx csp_rs1) avail -∗
    (∀ h : CpuId, urun γt γd γs h m pc avail -∗ WP (Loop : expr riscv_lang)) -∗
    ukc pm M m pc.
  Proof.
    iIntros "Hheap Hstk Hcont".
    rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    iApply ("Hcont" $! h). iExists C, pt, Rut, sz, M, pm.
    iFrame "Hheap Hstk Hb". iPureIntro. split; [ exact Hlo | exact Hpm ].
  Qed.

  (* [uv_upd] is the OTHER way a leaf writes a register (jalr's, where the
     write is optional).  It hid a real bug: the generated wrapper did not
     recognise the shape, so it claimed [avail] was preserved across an
     instruction that can write sp -- and that showed up not as a proof
     failure but as unification diverging inside the transparent [rf_upd].
     Hence this lemma, and the [unot_sp] premise that goes with it. *)
  Lemma uv_upd_not_sp (m : regfile) (rd : mword 5)
      (wr : option (mword 5 * mword 64)) (d : mword 64) :
    unot_sp rd ->
    (uint rd = 0 /\ wr = None) \/ (uint rd <> 0 /\ wr = Some (rd, d)) ->
    (uv_upd m wr) !!! Regidx csp_rs1 = m !!! Regidx csp_rs1.
  Proof.
    intros Hns [[_ ->] | [_ ->]]; [ reflexivity | ].
    cbn [uv_upd]. exact (unot_sp_upd rd (regval_into_reg d) m Hns).
  Qed.

  (* ...and the same when the instruction WROTE a register: the free stack
     is keyed by sp, and [unot_sp] says this write was not to sp. *)
  Lemma urun_close_upd (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (m : regfile) (rd : mword 5) (v : mword 64)
      (pc' : mword 64) (avail : nat) :
    unot_sp rd ->
    uheap γt γd γs M pm -∗
    ustack γd (m !!! Regidx csp_rs1) avail -∗
    (∀ h : CpuId, urun γt γd γs h (<[Regidx rd := v]> m) pc' avail -∗
                  WP (Loop : expr riscv_lang)) -∗
    ukc pm M (<[Regidx rd := v]> m) pc'.
  Proof.
    intros Hns. iIntros "Hheap Hstk Hcont".
    iApply (urun_close with "Hheap [Hstk] Hcont").
    rewrite (unot_sp_upd rd v m Hns). iExact "Hstk".
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
  (* §3 WHAT A MEMORY LEAF READS OFF THE HEAP.                                                        *)
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

  (* THE DATA WORD AT AN ADDRESS: in range, and WRITABLE.  This is where
     the permission table stops being visible -- the caller holds an
     exclusive [uword], and the heap turns that into the leaf's
     [uk_store_ok] without the caller ever naming a page or a PTE bit.
     Consuming the run inside this proof is free: the conclusion is pure, so
     the caller's [iDestruct … as %…] keeps both the heap and the word. *)
  Lemma uheap_uword_at (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (a : Z) (w : mword 64) :
    uheap γt γd γs M pm -∗ uword γd a w -∗
    ⌜ 0 <= a < 2 ^ 38 /\ uw_addr pm a ⌝.
  Proof.
    iIntros "Hheap Hw". rewrite /uword /ubytes.
    iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hw") as "H0";
      [ reflexivity | ].
    iDestruct (uheap_ubyte with "Hheap H0") as %(_ & Hw & Hb).
    iPureIntro. change (Z.of_nat 0) with 0 in Hw, Hb.
    rewrite Z.add_0_r in Hw, Hb. exact (conj Hb Hw).
  Qed.

  (* A RUN OF OWNED DATA BYTES: present in the image at its own values, on
     writable pages, in range.  This is the single lemma every memory leaf
     goes through -- it is what replaces the caller-supplied permission,
     canonicity and presence premises of the UkStore/UkLoad leaves. *)
  Lemma uheap_ubytes_at (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (a : Z) (n : nat) (f : nat -> bv 8) :
    uheap γt γd γs M pm -∗ ubytes γd a n f -∗
    ⌜ forall j : nat, (j < n)%nat ->
        M !! (a + Z.of_nat j)%Z = Some (f j) /\
        uw_addr pm (a + Z.of_nat j)%Z /\
        0 <= a + Z.of_nat j < 2 ^ 38 ⌝.
  Proof.
    iIntros "Hheap Hbs". rewrite /ubytes.
    iInduction n as [| n IH] "IH" forall (f).
    - iPureIntro. intros j Hj. exfalso. lia.
    - iEval (rewrite seq_S big_sepL_app /=) in "Hbs".
      iDestruct "Hbs" as "(Hlo & Hhi & _)".
      iDestruct (uheap_ubyte with "Hheap Hhi") as %Hn.
      (* the IH is generalised over [f], so instantiate that before feeding it *)
      iDestruct ("IH" $! f with "Hheap Hlo") as %Hlo.
      iPureIntro. intros j Hj.
      destruct (decide (j = n)) as [-> | Hne]; [ exact Hn | apply Hlo; lia ].
  Qed.

  (* ===================================================================== *)
  (* §4 THE ENTRY: the process's FIRST WP.                                 *)
  (*                                                                       *)
  (* This is the other end of the interface.  A program never constructs a  *)
  (* [urun]; it is handed one here, together with the points-to facts for   *)
  (* its whole initial image, in exchange for a proof that it is safe from  *)
  (* the key's resume state.  The gnames are FRESH -- allocated at this     *)
  (* WP, under the ambient the slot quantifies over -- which is why they    *)
  (* are arguments of [urun] rather than section variables.                 *)
  (* ===================================================================== *)

  (* [uheap_alloc]'s one premise, discharged.  Two sources: a MAPPED address
     sits in a page the table maps, and [upt_map_wf] puts every such page
     below the trapframe; a LIVE address is below the break, and [usz_ok]
     puts the break below the trapframe too. *)
  Lemma umem_lazy_bound (pt : uptd) (sz : Z) (M : gmap Z (bv 8)) :
    proc_pt_wf pt -> usz_ok sz ->
    umem_lazy pt sz M -∗ ⌜ forall a : Z, is_Some (M !! a) -> 0 <= a < 2 ^ 38 ⌝.
  Proof.
    iIntros (Hwf Hsz) "H". iDestruct "H" as (Mp) "(_ & %Hiff & _ & _)".
    iPureIntro. intros a Ha.
    change (2 ^ 38) with 274877906944.
    destruct (proj1 (Hiff a) Ha) as [Hm | Hl].
    - destruct Hm as (vpn & w & j & Hvl & Hj & ->).
      destruct Hwf as (Hmw & _).
      destruct (Hmw vpn w Hvl) as [Hlt _].
      rewrite tf_vpn_unsigned in Hlt.
      pose proof (proj1 (bv_unsigned_in_range _ vpn)) as Hv0.
      lia.
    - pose proof (usz_ok_live sz a Hsz Hl). lia.
  Qed.

  Lemma uslot_of_urun (W : uvis) :
    (∀ (γt γd γs : gname) (h : CpuId) (sz : Z),
       ⌜ usz_ok sz ⌝ -∗
       usz γs sz -∗
       utext_all γt (uvis_M W) (uvis_perm W) -∗
       ([∗ map] a ↦ b ∈ udata_lo (uvis_M W) (uvis_perm W) sz, ubyte γd a b) -∗
       (* AVAIL = 0.  Carving the process's initial stack out of the data
          the entry hands over is a separate step, and belongs with the
          program's slot constructor rather than here -- it is the fact the
          old [uk_stack] gate decided. *)
       urun γt γd γs h (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W)) 0 -∗
       WP (Loop : expr riscv_lang))
    -∗ uslot W.
  Proof.
    iIntros "Hprog". rewrite uslot_ukc /ukc.
    iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    assert (Hwf : proc_pt_wf pt)
      by (destruct Hlo as (_ & _ & _ & _ & _ & H); exact H).
    rewrite /uvb /uvb_F /user_ptm_inv.
    iDestruct "Hb" as
      "(Hamb & Hregs & %Hsz & (Htlb & Hlazy & %Hinj & %Hacc) &
        Hcfg & Hgpr & Hpc & Hrut & Hkont)".
    iDestruct (umem_lazy_bound pt sz (uvis_M W) Hwf Hsz with "Hlazy") as %Hcan.
    iMod (uheap_alloc (uvis_M W) (uvis_perm W) sz Hcan)
      as (γt γd γs) "(Hheap & Hszf & #Ht & Hd)".
    rewrite -/(utext_all γt (uvis_M W) (uvis_perm W)).
    iSpecialize ("Hprog" $! γt γd γs h sz with "[%] Hszf Ht Hd"); [ exact Hsz | ].
    iApply "Hprog".
    iExists C, pt, Rut, sz, (uvis_M W), (uvis_perm W).
    iSplitR; [ iPureIntro; exact Hlo | ].
    iSplitR; [ iPureIntro; exact Hpm | ].
    iFrame "Hheap". rewrite ustack_0. iSplitR; [ done | ].
    rewrite /uvb /uvb_F /user_ptm_inv.
    iFrame "Hamb Hregs Hcfg Hgpr Hpc Hrut Hkont Htlb Hlazy".
    iPureIntro. split_and!; [ exact Hsz | exact Hinj | exact Hacc ].
  Qed.

End UkRun.
