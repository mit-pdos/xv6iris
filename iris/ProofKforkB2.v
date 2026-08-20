(* ProofKforkB2.v -- kfork's TRAPFRAME COPY LOOP, +0x4a .. +0x62 (landing at
   +0x66).  Nine turns of four words each, copying the parent's trapframe
   page verbatim into the child's:

     +0x04a  c.ld  a0,0(a5)      +0x050  c.sd a0,0(a4)
     +0x04c  c.ld  a1,8(a5)      +0x052  c.sd a1,8(a4)
     +0x04e  c.ld  a2,16(a5)     +0x054  c.sd a2,16(a4)
     +0x056  c.ld  a2,24(a5)     +0x058  c.sd a2,24(a4)
     +0x05a  addi  a5,a5,32
     +0x05e  addi  a4,a4,32
     +0x062  bne   a5,a3,-24 -> +0x04a

   Runs with interrupts OFF throughout (the child's lock is held, so [b] is
   the literal [false]): every leaf closes with [wp_next_off_intro] and the
   hart never moves, so there is no [cpu_own]/[wp_next_shift] bookkeeping
   here at all -- unlike ProofFdalloc/ProofReparent's loops.

   No calls, no locks; the only ghost state touched is the two
   [ProcInv.tf_page]s (source unchanged throughout, destination rebuilt word
   by word).  Proved as ONE lemma over a symbolic loop index [k], by a
   bounded FUEL induction (ProofFdalloc.v's "Hloop" shape): the numeric side
   conditions live in top-level, mword-free [nat] lemmas up front (the
   bitvector zify hook makes an inline [lia] fail once a [bv_unsigned] is
   merely in context -- durable-notes.md), and the loop's own continuation
   is a PREMISE of the generalized statement, not a resource in its
   context, so [iInduction]'s IH comes out usable at every [k]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import WpNext.
Require Import CalleeSaved.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfBtype.
Require Import IntrDefs.
Require Import PageGeom.
Require Import ProcGeom.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import KptTree TrampPt.
Require Import ProofKforkParts.
Require Import CodeKfork.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* durable-notes: a syscall-altitude goal over [ProcInv.tf_page] carries a
   4096-conjunct big-op; printing one takes tens of minutes, so a one-line
   mistake reads as a hang. *)
Set Printing Depth 40.

Notation KF := KernelSyms.kfork (only parsing).

(* ===================================================================== *)
(*  PURE, mword-FREE NUMERIC SIDE CONDITIONS.                            *)
(*  Kept OUT of the Iris proof: under the bitvector zify hook, an inline  *)
(*  [lia] answers "Cannot find witness" whenever a [bv_unsigned] is       *)
(*  merely in the ambient context, even if the goal itself does not       *)
(*  mention one.                                                          *)
(* ===================================================================== *)
Lemma kfk_fuel0_start : (9 - 0 <= 9)%nat.
Proof. lia. Qed.

Lemma kfk_k0_lt9 : (0 < 9)%nat.
Proof. lia. Qed.

Lemma kfk_fuel_absurd (k : nat) : (k < 9)%nat -> (9 - k <= 0)%nat -> False.
Proof. lia. Qed.

Lemma kfk_fuel_dec (k fuel : nat) :
  (9 - k <= S fuel)%nat -> (k < 9)%nat -> (S k <> 9)%nat -> (9 - S k <= fuel)%nat.
Proof. lia. Qed.

Lemma kfk_k_dec (k : nat) : (k < 9)%nat -> (S k <> 9)%nat -> (S k < 9)%nat.
Proof. lia. Qed.

Lemma kfk_idx_lt36_0 (k : nat) : (k < 9)%nat -> ((4*k+0)%nat < 36)%nat. Proof. lia. Qed.
Lemma kfk_idx_lt36_1 (k : nat) : (k < 9)%nat -> ((4*k+1)%nat < 36)%nat. Proof. lia. Qed.
Lemma kfk_idx_lt36_2 (k : nat) : (k < 9)%nat -> ((4*k+2)%nat < 36)%nat. Proof. lia. Qed.
Lemma kfk_idx_lt36_3 (k : nat) : (k < 9)%nat -> ((4*k+3)%nat < 36)%nat. Proof. lia. Qed.

Lemma kfk_mul4_eq36 (x : nat) : (4 * x = 36)%nat -> x = 9%nat.
Proof. lia. Qed.

Lemma kfk_send9_mul (k : nat) : (S k = 9)%nat -> (4 * S k = 36)%nat.
Proof. intro H. rewrite H. reflexivity. Qed.

Lemma kfk_tf_inj_bound_sk (k : nat) : (k < 9)%nat -> (8 * (4 * S k) < 4096)%nat.
Proof. lia. Qed.

Lemma kfk_tf_inj_bound36 : (8 * 36 < 4096)%nat.
Proof. lia. Qed.

(* the agreement invariant's extension across one iteration's four stores *)
Lemma kfk_cur_agree_step (ws cur : list (mword 64)) (k : nat) (w0 w1 w2 w3 : mword 64) :
  (k < 9)%nat ->
  length cur = 36%nat ->
  (forall i, (i < 4*k)%nat -> cur !! i = ws !! i) ->
  ws !! (4*k+0)%nat = Some w0 -> ws !! (4*k+1)%nat = Some w1 ->
  ws !! (4*k+2)%nat = Some w2 -> ws !! (4*k+3)%nat = Some w3 ->
  forall i, (i < 4 * S k)%nat ->
    (<[(4*k+3)%nat := w3]> (<[(4*k+2)%nat := w2]> (<[(4*k+1)%nat := w1]> (<[(4*k+0)%nat := w0]> cur)))) !! i = ws !! i.
Proof.
  intros Hk9 Hlen Hagree H0 H1 H2 H3 i Hi.
  assert (Hb0 : ((4*k+0)%nat < length cur)%nat) by (rewrite Hlen; exact (kfk_idx_lt36_0 k Hk9)).
  assert (Hb1 : ((4*k+1)%nat < length (<[(4*k+0)%nat:=w0]> cur))%nat)
    by (rewrite length_insert Hlen; exact (kfk_idx_lt36_1 k Hk9)).
  assert (Hb2 : ((4*k+2)%nat < length (<[(4*k+1)%nat:=w1]> (<[(4*k+0)%nat:=w0]> cur)))%nat)
    by (rewrite length_insert length_insert Hlen; exact (kfk_idx_lt36_2 k Hk9)).
  assert (Hb3 : ((4*k+3)%nat < length (<[(4*k+2)%nat:=w2]> (<[(4*k+1)%nat:=w1]> (<[(4*k+0)%nat:=w0]> cur))))%nat)
    by (rewrite length_insert length_insert length_insert Hlen; exact (kfk_idx_lt36_3 k Hk9)).
  destruct (decide (i = (4*k+3)%nat)%nat) as [-> | Ne3].
  { rewrite (list_lookup_insert _ _ _ Hb3). congruence. }
  rewrite (list_lookup_insert_ne _ _ _ _ (not_eq_sym Ne3)).
  destruct (decide (i = (4*k+2)%nat)%nat) as [-> | Ne2].
  { rewrite (list_lookup_insert _ _ _ Hb2). congruence. }
  rewrite (list_lookup_insert_ne _ _ _ _ (not_eq_sym Ne2)).
  destruct (decide (i = (4*k+1)%nat)%nat) as [-> | Ne1].
  { rewrite (list_lookup_insert _ _ _ Hb1). congruence. }
  rewrite (list_lookup_insert_ne _ _ _ _ (not_eq_sym Ne1)).
  destruct (decide (i = (4*k+0)%nat)%nat) as [-> | Ne0].
  { rewrite (list_lookup_insert _ _ _ Hb0). congruence. }
  rewrite (list_lookup_insert_ne _ _ _ _ (not_eq_sym Ne0)).
  apply Hagree. lia.
Qed.

(* the exit: full-length agreement forces list equality *)
Lemma kfk_full_agree (ws cur : list (mword 64)) :
  length cur = length ws ->
  (forall i, (i < length ws)%nat -> cur !! i = ws !! i) ->
  cur = ws.
Proof.
  intros Hlen Hagree. apply list_eq. intro i.
  destruct (decide (i < length ws)%nat) as [Hi | Hi].
  - exact (Hagree i Hi).
  - assert (Hge1 : (length ws <= i)%nat) by lia.
    assert (Hge2 : (length cur <= i)%nat) by lia.
    rewrite (lookup_ge_None_2 ws i Hge1) (lookup_ge_None_2 cur i Hge2).
    reflexivity.
Qed.

(* ===================================================================== *)
Section KforkTfLoop.
  Context `{!riscvGS Σ, !xv6G Σ, !fileG Σ, !fdslotG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* THE BLOCK.  Entry: pc = +0x4a, a5/a4 at the SOURCE/DEST word-0
     cursors, a3 at the source's end pointer, [tf_page tfsrc ws] and
     [tf_page tfdst cur0] for an arbitrary initial [cur0].  Exit: pc =
     +0x66, a5 = a3 = the source's end pointer, a4 at the dest's end
     pointer, every callee-saved register untouched, and [tf_page tfdst
     ws] -- the child's trapframe is now a verbatim copy of the parent's. *)
  Lemma kfk_tf_copy_loop (M : regfile) (tfsrc tfdst : mword 44)
      (ws cur0 : list (mword 64)) (n : nat) (p : mword 64) :
    page_valid (page_base tfsrc) ->
    page_valid (page_base tfdst) ->
    length ws = TFWORDS ->
    length cur0 = TFWORDS ->
    M !!! Regidx Ra5 = tf_pa tfsrc (8 * Z.of_nat 0) ->
    M !!! Regidx Ra4 = tf_pa tfdst (8 * Z.of_nat 0) ->
    M !!! Regidx Ra3 = tf_pa tfsrc (8 * Z.of_nat 36) ->
    (* NO premise tying [M] to kfork's ENTRY map: at +0x4a the frame is
       pushed, s0 is the frame pointer, s4 is the child and s5 is the parent,
       so "every callee-saved register still agrees with the entry map" is
       FALSE here.  The loop writes only a0..a5, so what it can honestly say
       -- and what the capstone actually wants -- is preservation relative to
       ITS OWN entry map [M].  (durable-notes / S11: getting this wrong
       compiles, and only fails when the capstone tries to apply the block.) *)
    sie_cap_gpr KT1 M n false p -∗
    kernel_text -∗
    pc_is (mword_of_int (KF + 0x4a) : mword 64) -∗
    tf_page tfsrc ws -∗
    tf_page tfdst cur0 -∗
    wp_next false p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved M mf /\
         mf !!! Regidx Ra5 = tf_pa tfsrc (8 * Z.of_nat 36) /\
         mf !!! Regidx Ra4 = tf_pa tfdst (8 * Z.of_nat 36)⌝ -∗
        sie_cap_gpr KT1 mf n false p -∗
        pc_is (mword_of_int (KF + 0x66) : mword 64) -∗
        tf_page tfsrc ws -∗
        tf_page tfdst ws -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hpvsrc Hpvdst Hwslen Hcur0len HM5 HM4 HM3.
    iIntros "Hcg #Htext Hpc Hsrcp Hdstp Hcont".
    (* [pt_node_claim] for both pages, ONCE: [hw_config] peels off [Hcg]
       persistently (no loss), and [page_valid] is [Hpvsrc]/[Hpvdst].  These
       stay in the intuitionistic context for the whole fuel induction below
       (like [Htext]/[Hi04a] etc.), so the loop body needs no extra threading. *)
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhw Hcg]".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb & _)".
    iPoseProof (pt_node_claim_from_static tfsrc Hpvsrc with "Hkmapb") as "#Hptcsrc".
    iPoseProof (pt_node_claim_from_static tfdst Hpvdst with "Hkmapb") as "#Hptcdst".
    assert (Hwslen36 : length ws = 36%nat) by (unfold TFWORDS in Hwslen; exact Hwslen).
    iPoseProof (kfk_04a with "Htext") as "Hi04a".
    iPoseProof (kfk_04c with "Htext") as "Hi04c".
    iPoseProof (kfk_04e with "Htext") as "Hi04e".
    iPoseProof (kfk_050 with "Htext") as "Hi050".
    iPoseProof (kfk_052 with "Htext") as "Hi052".
    iPoseProof (kfk_054 with "Htext") as "Hi054".
    iPoseProof (kfk_056 with "Htext") as "Hi056".
    iPoseProof (kfk_058 with "Htext") as "Hi058".
    iPoseProof (kfk_05a with "Htext") as "Hi05a".
    iPoseProof (kfk_05e with "Htext") as "Hi05e".
    iPoseProof (kfk_062 with "Htext") as "Hi062".
    (* ------------------------------------------------------------- *)
    (*  THE GENERALISED LOOP, by fuel induction.  The continuation is  *)
    (*  a PREMISE of the loop statement (durable-notes / the brief's   *)
    (*  lesson from ProofFdalloc): otherwise the IH comes out with a   *)
    (*  wand in front of the [∀] and [IHf] cannot be applied below.    *)
    (* ------------------------------------------------------------- *)
    iAssert (∀ (fuel k : nat) (Mk : regfile) (cur : list (mword 64)),
      ⌜(9 - k <= fuel)%nat⌝ -∗
      ⌜(k < 9)%nat⌝ -∗
      ⌜length cur = TFWORDS⌝ -∗
      ⌜forall i, (i < 4*k)%nat -> cur !! i = ws !! i⌝ -∗
      ⌜Mk !!! Regidx Ra5 = tf_pa tfsrc (8 * Z.of_nat (4*k)) /\
       Mk !!! Regidx Ra4 = tf_pa tfdst (8 * Z.of_nat (4*k)) /\
       Mk !!! Regidx Ra3 = tf_pa tfsrc (8 * Z.of_nat 36) /\
       (forall r : mword 5, is_cs_idx r = true -> Mk !!! Regidx r = M !!! Regidx r)⌝ -∗
      sie_cap_gpr KT1 Mk n false p -∗
      pc_is (mword_of_int (KF + 0x4a) : mword 64) -∗
      tf_page tfsrc ws -∗
      tf_page tfdst cur -∗
      wp_next false p (fun (CID : CpuId) =>
        ∀ mf : regfile,
          ⌜callee_saved M mf /\
           mf !!! Regidx Ra5 = tf_pa tfsrc (8 * Z.of_nat 36) /\
           mf !!! Regidx Ra4 = tf_pa tfdst (8 * Z.of_nat 36)⌝ -∗
          sie_cap_gpr KT1 mf n false p -∗
          pc_is (mword_of_int (KF + 0x66) : mword 64) -∗
          tf_page tfsrc ws -∗
          tf_page tfdst ws -∗
          WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang))%I
      with "[]" as "Hloop".
    { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
      { iIntros (k Mk cur) "%Hfuel %Hk9 %Hcurlen %Hagree %HMkregs Hcg Hpc Hsrcp Hdstp Hcont".
        exfalso. exact (kfk_fuel_absurd k Hk9 Hfuel). }
      iIntros (k Mk cur) "%Hfuel %Hk9 %Hcurlen %Hagree %HMkregs Hcg Hpc Hsrcp Hdstp Hcont".
      destruct HMkregs as (HMka5 & HMka4 & HMka3 & HMkcs).
      assert (Hcurlen36 : length cur = 36%nat) by (unfold TFWORDS in Hcurlen; exact Hcurlen).
      (* ---- the four source words this iteration copies ---- *)
      assert (Hb0 : ((4*k+0)%nat < length ws)%nat) by (rewrite Hwslen36; exact (kfk_idx_lt36_0 k Hk9)).
      assert (Hb1 : ((4*k+1)%nat < length ws)%nat) by (rewrite Hwslen36; exact (kfk_idx_lt36_1 k Hk9)).
      assert (Hb2 : ((4*k+2)%nat < length ws)%nat) by (rewrite Hwslen36; exact (kfk_idx_lt36_2 k Hk9)).
      assert (Hb3 : ((4*k+3)%nat < length ws)%nat) by (rewrite Hwslen36; exact (kfk_idx_lt36_3 k Hk9)).
      destruct (lookup_lt_is_Some_2 ws ((4*k+0)%nat) Hb0) as [w0 Hw0].
      destruct (lookup_lt_is_Some_2 ws ((4*k+1)%nat) Hb1) as [w1 Hw1].
      destruct (lookup_lt_is_Some_2 ws ((4*k+2)%nat) Hb2) as [w2 Hw2].
      destruct (lookup_lt_is_Some_2 ws ((4*k+3)%nat) Hb3) as [w3 Hw3].
      (* ---- the address arithmetic, all off Mk's a5/a4 (unchanged   ----
         ---- across the whole body until the two trailing addi's)     *)
      assert (Ha0 : add_vec (Mk !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = tf_pa tfsrc (8 * Z.of_nat ((4*k+0)%nat))).
      { rewrite HMka5. exact (kfk_tf_disp tfsrc k 0 0 ltac:(lia) ltac:(lia) ltac:(reflexivity)
          ltac:(apply bv_eq; vm_compute; reflexivity)). }
      assert (Ha1 : add_vec (Mk !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 8 : mword 12))
                    = tf_pa tfsrc (8 * Z.of_nat ((4*k+1)%nat))).
      { rewrite HMka5. exact (kfk_tf_disp tfsrc k 1 8 ltac:(lia) ltac:(lia) ltac:(reflexivity)
          ltac:(apply bv_eq; vm_compute; reflexivity)). }
      assert (Ha2 : add_vec (Mk !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 16 : mword 12))
                    = tf_pa tfsrc (8 * Z.of_nat ((4*k+2)%nat))).
      { rewrite HMka5. exact (kfk_tf_disp tfsrc k 2 16 ltac:(lia) ltac:(lia) ltac:(reflexivity)
          ltac:(apply bv_eq; vm_compute; reflexivity)). }
      assert (Ha3 : add_vec (Mk !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 24 : mword 12))
                    = tf_pa tfsrc (8 * Z.of_nat ((4*k+3)%nat))).
      { rewrite HMka5. exact (kfk_tf_disp tfsrc k 3 24 ltac:(lia) ltac:(lia) ltac:(reflexivity)
          ltac:(apply bv_eq; vm_compute; reflexivity)). }
      assert (Hd0 : add_vec (Mk !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = tf_pa tfdst (8 * Z.of_nat ((4*k+0)%nat))).
      { rewrite HMka4. exact (kfk_tf_disp tfdst k 0 0 ltac:(lia) ltac:(lia) ltac:(reflexivity)
          ltac:(apply bv_eq; vm_compute; reflexivity)). }
      assert (Hd1 : add_vec (Mk !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 8 : mword 12))
                    = tf_pa tfdst (8 * Z.of_nat ((4*k+1)%nat))).
      { rewrite HMka4. exact (kfk_tf_disp tfdst k 1 8 ltac:(lia) ltac:(lia) ltac:(reflexivity)
          ltac:(apply bv_eq; vm_compute; reflexivity)). }
      assert (Hd2 : add_vec (Mk !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 16 : mword 12))
                    = tf_pa tfdst (8 * Z.of_nat ((4*k+2)%nat))).
      { rewrite HMka4. exact (kfk_tf_disp tfdst k 2 16 ltac:(lia) ltac:(lia) ltac:(reflexivity)
          ltac:(apply bv_eq; vm_compute; reflexivity)). }
      assert (Hd3 : add_vec (Mk !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 24 : mword 12))
                    = tf_pa tfdst (8 * Z.of_nat ((4*k+3)%nat))).
      { rewrite HMka4. exact (kfk_tf_disp tfdst k 3 24 ltac:(lia) ltac:(lia) ltac:(reflexivity)
          ltac:(apply bv_eq; vm_compute; reflexivity)). }
      (* ================================================================ *)
      (*  +0x4a: c.ld a0,0(a5)                                             *)
      (* ================================================================ *)
      iDestruct (tf_page_word_mem tfsrc ws ((4*k+0)%nat) w0 ltac:(lia) Hw0 with "Hptcsrc Hsrcp") as "[Hr0 Hsrcback0]".
      iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KF + 0x4a) : mword 64) Ra0 Ra5 (mword_of_int 0 : mword 12)
                Mk n w0 false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi04a [Hr0]").
      { iEval (rgne; rewrite Ha0). iExact "Hr0". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hr0". iEval (rgne; rewrite Ha0) in "Hr0".
      iDestruct ("Hsrcback0" with "Hr0") as "Hsrcp".
      set (M1 := <[Regidx Ra0 := regval_into_reg w0]> Mk).
      change (<[Regidx Ra0 := regval_into_reg w0]> Mk) with M1.
      assert (Hp4c : add_vec_int (mword_of_int (KF + 0x4a) : mword 64) 2 = mword_of_int (KF + 0x4c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp4c) in "Hpc".
      assert (HM1a0 : M1 !!! Regidx Ra0 = w0) by (rewrite /M1 upd_eq; reflexivity).
      assert (HM1a3 : M1 !!! Regidx Ra3 = Mk !!! Regidx Ra3)
        by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
      assert (HM1a4 : M1 !!! Regidx Ra4 = Mk !!! Regidx Ra4)
        by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
      assert (HM1a5 : M1 !!! Regidx Ra5 = Mk !!! Regidx Ra5)
        by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
      (* ================================================================ *)
      (*  +0x4c: c.ld a1,8(a5)                                             *)
      (* ================================================================ *)
      iDestruct (tf_page_word_mem tfsrc ws ((4*k+1)%nat) w1 ltac:(lia) Hw1 with "Hptcsrc Hsrcp") as "[Hr1 Hsrcback1]".
      iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KF + 0x4c) : mword 64) Ra1 Ra5 (mword_of_int 8 : mword 12)
                M1 n w1 false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi04c [Hr1]").
      { iEval (rgne; rewrite HM1a5 Ha1). iExact "Hr1". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hr1". iEval (rgne; rewrite HM1a5 Ha1) in "Hr1".
      iDestruct ("Hsrcback1" with "Hr1") as "Hsrcp".
      set (M2 := <[Regidx Ra1 := regval_into_reg w1]> M1).
      change (<[Regidx Ra1 := regval_into_reg w1]> M1) with M2.
      assert (Hp4e : add_vec_int (mword_of_int (KF + 0x4c) : mword 64) 2 = mword_of_int (KF + 0x4e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp4e) in "Hpc".
      assert (HM2a1 : M2 !!! Regidx Ra1 = w1) by (rewrite /M2 upd_eq; reflexivity).
      assert (HM2a0 : M2 !!! Regidx Ra0 = w0)
        by (rewrite /M2 upd_ne; [exact HM1a0 | vm_compute; discriminate]).
      assert (HM2a3 : M2 !!! Regidx Ra3 = Mk !!! Regidx Ra3)
        by (rewrite /M2 upd_ne; [exact HM1a3 | vm_compute; discriminate]).
      assert (HM2a4 : M2 !!! Regidx Ra4 = Mk !!! Regidx Ra4)
        by (rewrite /M2 upd_ne; [exact HM1a4 | vm_compute; discriminate]).
      assert (HM2a5 : M2 !!! Regidx Ra5 = Mk !!! Regidx Ra5)
        by (rewrite /M2 upd_ne; [exact HM1a5 | vm_compute; discriminate]).
      (* ================================================================ *)
      (*  +0x4e: c.ld a2,16(a5)                                            *)
      (* ================================================================ *)
      iDestruct (tf_page_word_mem tfsrc ws ((4*k+2)%nat) w2 ltac:(lia) Hw2 with "Hptcsrc Hsrcp") as "[Hr2 Hsrcback2]".
      iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KF + 0x4e) : mword 64) Ra2 Ra5 (mword_of_int 16 : mword 12)
                M2 n w2 false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi04e [Hr2]").
      { iEval (rgne; rewrite HM2a5 Ha2). iExact "Hr2". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hr2". iEval (rgne; rewrite HM2a5 Ha2) in "Hr2".
      iDestruct ("Hsrcback2" with "Hr2") as "Hsrcp".
      set (M3 := <[Regidx Ra2 := regval_into_reg w2]> M2).
      change (<[Regidx Ra2 := regval_into_reg w2]> M2) with M3.
      assert (Hp50 : add_vec_int (mword_of_int (KF + 0x4e) : mword 64) 2 = mword_of_int (KF + 0x50))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp50) in "Hpc".
      assert (HM3a2 : M3 !!! Regidx Ra2 = w2) by (rewrite /M3 upd_eq; reflexivity).
      assert (HM3a0 : M3 !!! Regidx Ra0 = w0)
        by (rewrite /M3 upd_ne; [exact HM2a0 | vm_compute; discriminate]).
      assert (HM3a1 : M3 !!! Regidx Ra1 = w1)
        by (rewrite /M3 upd_ne; [exact HM2a1 | vm_compute; discriminate]).
      assert (HM3a3 : M3 !!! Regidx Ra3 = Mk !!! Regidx Ra3)
        by (rewrite /M3 upd_ne; [exact HM2a3 | vm_compute; discriminate]).
      assert (HM3a4 : M3 !!! Regidx Ra4 = Mk !!! Regidx Ra4)
        by (rewrite /M3 upd_ne; [exact HM2a4 | vm_compute; discriminate]).
      assert (HM3a5 : M3 !!! Regidx Ra5 = Mk !!! Regidx Ra5)
        by (rewrite /M3 upd_ne; [exact HM2a5 | vm_compute; discriminate]).
      (* ================================================================ *)
      (*  +0x50 .. +0x54: c.sd a0,0(a4) ; c.sd a1,8(a4) ; c.sd a2,16(a4)    *)
      (*  -- all off the SAME map M3, matching the disassembly.            *)
      (* ================================================================ *)
      assert (Hcb0 : ((4*k+0)%nat < length cur)%nat) by (rewrite Hcurlen36; exact (kfk_idx_lt36_0 k Hk9)).
      destruct (lookup_lt_is_Some_2 cur ((4*k+0)%nat) Hcb0) as [c0 Hc0].
      iDestruct (tf_page_word_upd_mem tfdst cur ((4*k+0)%nat) c0 ltac:(lia) Hc0 with "Hptcdst Hdstp") as "[Hw0 Hback0]".
      iApply (wp_csd_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KF + 0x50) : mword 64) Ra0 Ra4 (mword_of_int 0 : mword 12)
                M3 n c0 false
                with "Hcg Hpc Hi050 [Hw0]").
      { iEval (rgne; rewrite HM3a4 Hd0). iExact "Hw0". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hw0".
      iEval (rgne; rgne; rewrite HM3a4 Hd0 HM3a0) in "Hw0".
      iDestruct ("Hback0" with "Hw0") as "Hdstp".
      set (cur1 := <[(4*k+0)%nat := w0]> cur).
      change (<[(4*k+0)%nat := w0]> cur) with cur1.
      assert (Hp52 : add_vec_int (mword_of_int (KF + 0x50) : mword 64) 2 = mword_of_int (KF + 0x52))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp52) in "Hpc".
      assert (Hcb1 : ((4*k+1)%nat < length cur1)%nat)
        by (rewrite /cur1 length_insert Hcurlen36; exact (kfk_idx_lt36_1 k Hk9)).
      destruct (lookup_lt_is_Some_2 cur1 ((4*k+1)%nat) Hcb1) as [c1 Hc1].
      iDestruct (tf_page_word_upd_mem tfdst cur1 ((4*k+1)%nat) c1 ltac:(lia) Hc1 with "Hptcdst Hdstp") as "[Hw1 Hback1]".
      iApply (wp_csd_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KF + 0x52) : mword 64) Ra1 Ra4 (mword_of_int 8 : mword 12)
                M3 n c1 false
                with "Hcg Hpc Hi052 [Hw1]").
      { iEval (rgne; rewrite HM3a4 Hd1). iExact "Hw1". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hw1".
      iEval (rgne; rgne; rewrite HM3a4 Hd1 HM3a1) in "Hw1".
      iDestruct ("Hback1" with "Hw1") as "Hdstp".
      set (cur2 := <[(4*k+1)%nat := w1]> cur1).
      change (<[(4*k+1)%nat := w1]> cur1) with cur2.
      assert (Hp54 : add_vec_int (mword_of_int (KF + 0x52) : mword 64) 2 = mword_of_int (KF + 0x54))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp54) in "Hpc".
      assert (Hcb2 : ((4*k+2)%nat < length cur2)%nat)
        by (rewrite /cur2 length_insert /cur1 length_insert Hcurlen36; exact (kfk_idx_lt36_2 k Hk9)).
      destruct (lookup_lt_is_Some_2 cur2 ((4*k+2)%nat) Hcb2) as [c2 Hc2].
      iDestruct (tf_page_word_upd_mem tfdst cur2 ((4*k+2)%nat) c2 ltac:(lia) Hc2 with "Hptcdst Hdstp") as "[Hw2 Hback2]".
      iApply (wp_csd_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KF + 0x54) : mword 64) Ra2 Ra4 (mword_of_int 16 : mword 12)
                M3 n c2 false
                with "Hcg Hpc Hi054 [Hw2]").
      { iEval (rgne; rewrite HM3a4 Hd2). iExact "Hw2". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hw2".
      iEval (rgne; rgne; rewrite HM3a4 Hd2 HM3a2) in "Hw2".
      iDestruct ("Hback2" with "Hw2") as "Hdstp".
      set (cur3 := <[(4*k+2)%nat := w2]> cur2).
      change (<[(4*k+2)%nat := w2]> cur2) with cur3.
      assert (Hp56 : add_vec_int (mword_of_int (KF + 0x54) : mword 64) 2 = mword_of_int (KF + 0x56))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp56) in "Hpc".
      (* ================================================================ *)
      (*  +0x56: c.ld a2,24(a5) -- reloads a2, off the SAME map M3          *)
      (* ================================================================ *)
      iDestruct (tf_page_word_mem tfsrc ws ((4*k+3)%nat) w3 ltac:(lia) Hw3 with "Hptcsrc Hsrcp") as "[Hr3 Hsrcback3]".
      iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KF + 0x56) : mword 64) Ra2 Ra5 (mword_of_int 24 : mword 12)
                M3 n w3 false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi056 [Hr3]").
      { iEval (rgne; rewrite HM3a5 Ha3). iExact "Hr3". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hr3". iEval (rgne; rewrite HM3a5 Ha3) in "Hr3".
      iDestruct ("Hsrcback3" with "Hr3") as "Hsrcp".
      set (M4 := <[Regidx Ra2 := regval_into_reg w3]> M3).
      change (<[Regidx Ra2 := regval_into_reg w3]> M3) with M4.
      assert (Hp58 : add_vec_int (mword_of_int (KF + 0x56) : mword 64) 2 = mword_of_int (KF + 0x58))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp58) in "Hpc".
      assert (HM4a2 : M4 !!! Regidx Ra2 = w3) by (rewrite /M4 upd_eq; reflexivity).
      assert (HM4a3 : M4 !!! Regidx Ra3 = Mk !!! Regidx Ra3)
        by (rewrite /M4 upd_ne; [exact HM3a3 | vm_compute; discriminate]).
      assert (HM4a4 : M4 !!! Regidx Ra4 = Mk !!! Regidx Ra4)
        by (rewrite /M4 upd_ne; [exact HM3a4 | vm_compute; discriminate]).
      assert (HM4a5 : M4 !!! Regidx Ra5 = Mk !!! Regidx Ra5)
        by (rewrite /M4 upd_ne; [exact HM3a5 | vm_compute; discriminate]).
      (* ================================================================ *)
      (*  +0x58: c.sd a2,24(a4) -- off the freshly-updated map M4          *)
      (* ================================================================ *)
      assert (Hcb3 : ((4*k+3)%nat < length cur3)%nat)
        by (rewrite /cur3 length_insert /cur2 length_insert /cur1 length_insert Hcurlen36;
            exact (kfk_idx_lt36_3 k Hk9)).
      destruct (lookup_lt_is_Some_2 cur3 ((4*k+3)%nat) Hcb3) as [c3 Hc3].
      iDestruct (tf_page_word_upd_mem tfdst cur3 ((4*k+3)%nat) c3 ltac:(lia) Hc3 with "Hptcdst Hdstp") as "[Hw3 Hback3]".
      iApply (wp_csd_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KF + 0x58) : mword 64) Ra2 Ra4 (mword_of_int 24 : mword 12)
                M4 n c3 false
                with "Hcg Hpc Hi058 [Hw3]").
      { iEval (rgne; rewrite HM4a4 Hd3). iExact "Hw3". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hw3".
      iEval (rgne; rgne; rewrite HM4a4 Hd3 HM4a2) in "Hw3".
      iDestruct ("Hback3" with "Hw3") as "Hdstp".
      set (cur4 := <[(4*k+3)%nat := w3]> cur3).
      change (<[(4*k+3)%nat := w3]> cur3) with cur4.
      assert (Hp5a : add_vec_int (mword_of_int (KF + 0x58) : mword 64) 2 = mword_of_int (KF + 0x5a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp5a) in "Hpc".
      (* ---- [cur4] is exactly [kfk_cur_agree_step]'s composite insert ---- *)
      assert (Hagree4 : forall i, (i < 4 * S k)%nat -> cur4 !! i = ws !! i)
        by (rewrite /cur4 /cur3 /cur2 /cur1;
            exact (kfk_cur_agree_step ws cur k w0 w1 w2 w3 Hk9 Hcurlen36 Hagree Hw0 Hw1 Hw2 Hw3)).
      assert (Hcur4len : length cur4 = 36%nat).
      { rewrite /cur4 length_insert /cur3 length_insert /cur2 length_insert /cur1 length_insert.
        exact Hcurlen36. }
      (* ================================================================ *)
      (*  +0x5a: addi a5,a5,32                                             *)
      (* ================================================================ *)
      iApply (wp_addi4_s_sconf (mword_of_int (KF + 0x5a) : mword 64) Ra5 Ra5 (mword_of_int 32 : mword 12)
                M4 n false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi05a").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
      set (M5 := <[Regidx Ra5 := regval_into_reg
                    (add_vec (M4 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 32 : mword 12)))]> M4).
      change (<[Regidx Ra5 := regval_into_reg
                (add_vec (M4 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 32 : mword 12)))]> M4)
        with M5.
      assert (Hp5e : add_vec_int (mword_of_int (KF + 0x5a) : mword 64) 4 = mword_of_int (KF + 0x5e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp5e) in "Hpc".
      assert (HM5a5 : M5 !!! Regidx Ra5 = tf_pa tfsrc (8 * Z.of_nat (4 * S k))).
      { rewrite /M5 upd_eq HM4a5 HMka5.
        exact (kfk_tf_step tfsrc k ltac:(lia) ltac:(lia)
                 ltac:(apply bv_eq; vm_compute; reflexivity)). }
      assert (HM5a3 : M5 !!! Regidx Ra3 = Mk !!! Regidx Ra3)
        by (rewrite /M5 upd_ne; [exact HM4a3 | vm_compute; discriminate]).
      assert (HM5a4 : M5 !!! Regidx Ra4 = Mk !!! Regidx Ra4)
        by (rewrite /M5 upd_ne; [exact HM4a4 | vm_compute; discriminate]).
      (* ================================================================ *)
      (*  +0x5e: addi a4,a4,32                                             *)
      (* ================================================================ *)
      iApply (wp_addi4_s_sconf (mword_of_int (KF + 0x5e) : mword 64) Ra4 Ra4 (mword_of_int 32 : mword 12)
                M5 n false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi05e").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
      set (M6 := <[Regidx Ra4 := regval_into_reg
                    (add_vec (M5 !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 32 : mword 12)))]> M5).
      change (<[Regidx Ra4 := regval_into_reg
                (add_vec (M5 !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 32 : mword 12)))]> M5)
        with M6.
      assert (Hp62 : add_vec_int (mword_of_int (KF + 0x5e) : mword 64) 4 = mword_of_int (KF + 0x62))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp62) in "Hpc".
      assert (HM6a4 : M6 !!! Regidx Ra4 = tf_pa tfdst (8 * Z.of_nat (4 * S k))).
      { rewrite /M6 upd_eq HM5a4 HMka4.
        exact (kfk_tf_step tfdst k ltac:(lia) ltac:(lia)
                 ltac:(apply bv_eq; vm_compute; reflexivity)). }
      assert (HM6a3 : M6 !!! Regidx Ra3 = Mk !!! Regidx Ra3)
        by (rewrite /M6 upd_ne; [exact HM5a3 | vm_compute; discriminate]).
      assert (HM6a5 : M6 !!! Regidx Ra5 = tf_pa tfsrc (8 * Z.of_nat (4 * S k)))
        by (rewrite /M6 upd_ne; [exact HM5a5 | vm_compute; discriminate]).
      assert (HM6cs : forall r : mword 5, is_cs_idx r = true -> M6 !!! Regidx r = M !!! Regidx r).
      { intros r Hr.
        rewrite /M6 upd_ne; [| regne].
        rewrite /M5 upd_ne; [| regne].
        rewrite /M4 upd_ne; [| regne].
        rewrite /M3 upd_ne; [| regne].
        rewrite /M2 upd_ne; [| regne].
        rewrite /M1 upd_ne; [| regne].
        exact (HMkcs r Hr). }
      (* ================================================================ *)
      (*  +0x62: bne a5,a3,-24 -> +0x4a                                    *)
      (* ================================================================ *)
      destruct (decide (S k = 9)%nat) as [Hend | Hne].
      - (* ---- the array is done: the bne FALLS THROUGH to +0x66 ---- *)
        assert (Haddreq : tf_pa tfsrc (8 * Z.of_nat (4 * S k)) = tf_pa tfsrc (8 * Z.of_nat 36))
          by (rewrite (kfk_send9_mul k Hend); reflexivity).
        assert (Heqt : eq_vec (M6 !!! Regidx Ra5) (M6 !!! Regidx Ra3) = true).
        { rewrite HM6a5 HM6a3 HMka3.
          exact (proj2 (eq_vec_true_iff _ _) Haddreq). }
        assert (Hfall : neq_vec (M6 !!! Regidx Ra5) (M6 !!! Regidx Ra3) = false)
          by (unfold neq_vec; rewrite Heqt; reflexivity).
        iApply (wp_bne_fall_s_sconf (mword_of_int (KF + 0x62) : mword 64) (mword_of_int 8168 : mword 13)
                  Ra3 Ra5 M6 n false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rgne; exact Hfall)
                  with "Hcg Hpc Hi062").
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc".
        assert (Hp66 : add_vec_int (mword_of_int (KF + 0x62) : mword 64) 4 = mword_of_int (KF + 0x66))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp66) in "Hpc".
        assert (Hcur4_ws : cur4 = ws).
        { apply kfk_full_agree.
          - rewrite Hcur4len Hwslen36. reflexivity.
          - rewrite Hwslen36. rewrite (kfk_send9_mul k Hend) in Hagree4. exact Hagree4. }
        iAssert (tf_page tfdst ws) with "[Hdstp]" as "Hdstp".
        { rewrite -Hcur4_ws. iExact "Hdstp". }
        iSpecialize ("Hcont" $! CID0 with "[%]"); [intros _; reflexivity |].
        iApply ("Hcont" $! M6 with "[%] Hcg Hpc Hsrcp Hdstp").
        + split; [| split].
          * rewrite /callee_saved. split_and!;
              first
                [ exact (HM6cs (mword_of_int 2 : mword 5) ltac:(vm_compute; reflexivity))
                | exact (HM6cs (mword_of_int 8 : mword 5) ltac:(vm_compute; reflexivity))
                | exact (HM6cs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity))
                | exact (HM6cs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity))
                | exact (HM6cs (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity))
                | exact (HM6cs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity))
                | exact (HM6cs (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity))
                | exact (HM6cs (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity))
                | exact (HM6cs (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity))
                | exact (HM6cs (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity))
                | exact (HM6cs (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity))
                | exact (HM6cs (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity))
                | exact (HM6cs (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity)) ].
          * rewrite HM6a5 (kfk_send9_mul k Hend). reflexivity.
          * rewrite HM6a4 (kfk_send9_mul k Hend). reflexivity.
      - (* ---- more words left: the bne is TAKEN, back to +0x4a ---- *)
        assert (Hneq_addr : tf_pa tfsrc (8 * Z.of_nat (4 * S k)) <> tf_pa tfsrc (8 * Z.of_nat 36)).
        { intro Heq.
          apply Hne, (kfk_mul4_eq36 (S k)).
          exact (kfk_tf_inj tfsrc (4 * S k) 36 Hpvsrc
                   (kfk_tf_inj_bound_sk k Hk9) kfk_tf_inj_bound36 Heq). }
        assert (Heqf : eq_vec (M6 !!! Regidx Ra5) (M6 !!! Regidx Ra3) = false).
        { rewrite HM6a5 HM6a3 HMka3.
          exact (proj2 (eq_vec_false_iff _ _) Hneq_addr). }
        assert (Htaken : neq_vec (M6 !!! Regidx Ra5) (M6 !!! Regidx Ra3) = true)
          by (unfold neq_vec; rewrite Heqf; reflexivity).
        assert (Htgt : add_vec (mword_of_int (KF + 0x62) : mword 64)
                         (sign_extend' 64 (mword_of_int 8168 : mword 13))
                       = mword_of_int (KF + 0x4a))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_bne_taken_s_sconf (mword_of_int (KF + 0x62) : mword 64) (mword_of_int 8168 : mword 13)
                  Ra3 Ra5 M6 n false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rgne; exact Htaken)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi062").
        iNext. iApply wp_next_off_intro.
        iIntros "Hcg Hpc". iEval (rewrite Htgt) in "Hpc".
        iApply ("IHf" $! (S k) M6 cur4
                  with "[%] [%] [%] [%] [%] Hcg Hpc Hsrcp Hdstp Hcont").
        + exact (kfk_fuel_dec k fuel Hfuel Hk9 Hne).
        + exact (kfk_k_dec k Hk9 Hne).
        + exact Hcur4len.
        + exact Hagree4.
        + split; [exact HM6a5 |]. split; [exact HM6a4 |].
          split; [rewrite HM6a3; exact HMka3 |]. exact HM6cs. }
    (* ------------------------------------------------------------- *)
    (*  Enter the loop at k = 0 with fuel 9.                          *)
    (* ------------------------------------------------------------- *)
    iApply ("Hloop" $! 9%nat 0%nat M cur0
              with "[%] [%] [%] [%] [%] Hcg Hpc Hsrcp Hdstp Hcont").
    - exact kfk_fuel0_start.
    - exact kfk_k0_lt9.
    - exact Hcur0len.
    - intros i Hi. exfalso. exact (Nat.nlt_0_r i Hi).
    - split; [exact HM5 |]. split; [exact HM4 |]. split; [exact HM3 |].
      (* the loop is entered at its own entry map, so the agreement is refl *)
      intros r _. reflexivity.
  Qed.

End KforkTfLoop.
