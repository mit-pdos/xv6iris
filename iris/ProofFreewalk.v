(* ProofFreewalk.v -- freewalk() over the SIE-agnostic sconf world.

     void freewalk(pagetable_t pagetable)
     {
       for (int i = 0; i < 512; i++) {
         pte_t pte = pagetable[i];
         if ((pte & PTE_V) && (pte & (PTE_R|PTE_W|PTE_X)) == 0) {
           uint64 child = PTE2PA(pte);
           freewalk((pagetable_t)child);          // RECURSIVE
           pagetable[i] = 0;
         } else if (pte & PTE_V) {
           panic("freewalk: leaf");
         }
       }
       kfree((void * )pagetable);
     }

   Spec of record: SpecFreewalk.v -- the raw [ptree_own] altitude, indexed by
   the node's level.

   THE RECURSION IS AN INDUCTION ON [lvl], NOT AN iLob.  [ptree_own] is
   indexed by the same level the contract is, so the call at +0x3e is served
   by the induction hypothesis at [lvl - 1].  The induction is STRONG
   (a level-[l] child of a level-[lvl] node only satisfies [l < lvl]), staged
   through [fw_go_aux] so no well-founded machinery is needed; [fw_rec l] is
   the whole contract at level [l], and [fw_body] / [fw_loop] take it as the
   parameter [REC].  The stack budget works out with nothing to spare and
   nothing to prove: the contract asks [6 * S lvl + 14 <= K], the frame is 6
   slots, so the callee gets [K - 6] and needs [6 * S l + 14 <= K - 6] --
   the same inequality once [l < lvl].

   THE LOOP COMPARES POINTERS, NOT AN INDEX.  [s1] walks the node page eight
   bytes at a time from [page_base b] and [s2] is the fixed sentinel
   [page_base b + 4096]; [fw_cur b d] is that cursor at slot [d], and it is
   defined for [d = 512] too (where it IS the sentinel -- [fw_cur_end]),
   which is exactly why the invariant can be carried past the last slot.
   [fw_cur_slot] identifies it with the slot address [u_pte_addr b] the
   OWNERSHIP is indexed by, for [d < 512] only.  Everything rests on the node
   page not wrapping the address space, which is arithmetic on
   [bv_unsigned b < 2^44] alone.

   THE LOOP INVARIANT splits the node's 512 slot doublewords at [d]:
   [fw_done b d] holds slots [0, d) at ARBITRARY contents (the code has
   zeroed some of them and freed their subtrees), [fw_todo lvl t d] holds
   slots [d, 512) at the description's words TOGETHER WITH their subtrees
   ([fw_slot]).  Pairing the word and its child in ONE [big_sepL] is what
   makes the peel a single [fw_todo_cons]; the entry split is [fw_open],
   which is [PtTree.ptree_own_S] + [big_sepL_sep] at [S l] and
   [big_sepL_emp] at [0].  At the end all 512 slots are arbitrary and
   [PtFree.pt_slots_kfree_pre] turns them into kfree's precondition.

   THE PANIC BLOCK +0x18..+0x23 IS DEAD.  [pt_free_ok lvl t] says every slot
   is either the literal zero word (V clear, +0x30 taken) or a valid POINTER
   (V set and R|W|X clear, so +0x30 and +0x36 both fall through).
   [fw_ok] is that dichotomy per slot, phrased over [fw_kid] so the two arms
   never have to case on [lvl] itself.  A panic credential is not needed
   anywhere in this file. *)
Set Printing Depth 40.
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import HartTp WpNext.
Require Import CalleeSaved StackOwn.
Require Import IntrDefs.
Require Import WpLock.
Require Import KallocInv.
Require Import PageGeom.
Require Import CommonWalk Pt4kWalk.
Require Import PtTree PtBuild PtFree.
Require Import KptTree.
Require Import CpuOwn.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import CodeFreewalk.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecKfree.
Require Import SpecFreewalk.
Require Import KernelRvcDecode.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* §0  Pure vocabulary and arithmetic (mword-free where [lia] must run).  *)
(* ===================================================================== *)

(* the callee-saved registers freewalk never touches: it writes sp, s0, s1,
   s2 and s3 (and the caller-saved ra/a0/a4/a5, which are not in the set). *)
Definition fw_thr (mm m : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 ->
    c <> (mword_of_int 8 : mword 5) -> c <> (mword_of_int 9 : mword 5) ->
    c <> (mword_of_int 18 : mword 5) -> c <> (mword_of_int 19 : mword 5) ->
    m !!! Regidx c = mm !!! Regidx c.

(* ---- the loop cursor: [s1] after [d] iterations --------------------- *)
Definition fw_cur (b : mword 44) (d : Z) : mword 64 :=
  add_vec (page_base b) (mword_of_int (8 * d)).


Local Lemma fw_wrap64 (x : Z) : 0 <= x < 18446744073709551616 -> bv_wrap 64 x = x.
Proof. intros H. apply bv_wrap_small. rewrite bv_modulus64. exact H. Qed.

(* the node-page arithmetic, over plain [Z] (any goal mentioning
   [bv_unsigned] defeats [lia] under this file's transitive
   [bitvector.tactics] import) *)
Local Lemma fw_z_cur (B d : Z) :
  0 <= B < 17592186044416 -> 0 <= d <= 512 ->
  0 <= 8 * d < 18446744073709551616 /\ 0 <= B * 4096 + 8 * d < 18446744073709551616.
Proof. lia. Qed.

Local Lemma fw_z_step (B d : Z) :
  0 <= B < 17592186044416 -> 0 <= d < 512 ->
  0 <= 8 < 18446744073709551616
  /\ 0 <= B * 4096 + 8 * d + 8 < 18446744073709551616
  /\ B * 4096 + 8 * d + 8 = B * 4096 + 8 * (d + 1).
Proof. lia. Qed.

Local Lemma fw_z_end (B : Z) :
  0 <= B < 17592186044416 ->
  0 <= 4096 < 18446744073709551616
  /\ 0 <= 4096 + B * 4096 < 18446744073709551616
  /\ B * 4096 + 8 * 512 = 4096 + B * 4096.
Proof. lia. Qed.

Local Lemma fw_b_range (b : mword 44) : 0 <= bv_unsigned b < 17592186044416.
Proof.
  pose proof (bv_unsigned_in_range _ b) as Hr.
  assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 44) = 17592186044416)
    by (vm_compute; reflexivity).
  rewrite Hm in Hr. exact Hr.
Qed.

Lemma fw_cur_unsigned (b : mword 44) (d : Z) :
  0 <= d <= 512 -> bv_unsigned (fw_cur b d) = bv_unsigned b * 4096 + 8 * d.
Proof.
  intros Hd.
  destruct (fw_z_cur (bv_unsigned b) d (fw_b_range b) Hd) as [H1 H2].
  unfold fw_cur.
  rewrite add_vec64_unsigned moi64_unsigned page_base_unsigned.
  rewrite (fw_wrap64 _ H1). rewrite (fw_wrap64 _ H2). reflexivity.
Qed.

Lemma fw_cur_slot (b : mword 44) (d : Z) :
  0 <= d < 512 -> fw_cur b d = u_pte_addr b (mword_of_int d).
Proof.
  intros Hd. apply bv_eq.
  rewrite (fw_cur_unsigned b d ltac:(lia)).
  rewrite (pte_addr_at_unsigned b (mword_of_int d)).
  rewrite (pt_mword9_unsigned d ltac:(lia)).
  f_equal. lia.
Qed.

Lemma fw_cur_zero (b : mword 44) : fw_cur b 0 = page_base b.
Proof.
  unfold fw_cur. replace (8 * 0) with 0 by lia. apply kv_addv_zero.
Qed.

Lemma fw_cur_step (b : mword 44) (d : Z) :
  0 <= d < 512 ->
  add_vec (fw_cur b d) (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6)))
  = fw_cur b (d + 1).
Proof.
  intros Hd.
  assert (H8 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6)) : mword 64)
               = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
  rewrite H8.
  destruct (fw_z_step (bv_unsigned b) d (fw_b_range b) Hd) as (Ha & Hb & Hc).
  apply bv_eq.
  rewrite add_vec64_unsigned moi64_unsigned.
  rewrite (fw_cur_unsigned b d ltac:(lia)).
  rewrite (fw_cur_unsigned b (d + 1) ltac:(lia)).
  rewrite (fw_wrap64 _ Ha). rewrite Hc. apply fw_wrap64. rewrite <- Hc. exact Hb.
Qed.

Lemma fw_cur_end (b : mword 44) :
  fw_cur b 512 = add_vec (mword_of_int 4096) (page_base b).
Proof.
  destruct (fw_z_end (bv_unsigned b) (fw_b_range b)) as (Ha & Hb & Hc).
  apply bv_eq.
  rewrite (fw_cur_unsigned b 512 ltac:(lia)).
  rewrite add_vec64_unsigned moi64_unsigned page_base_unsigned.
  rewrite (fw_wrap64 _ Ha). rewrite Hc. symmetry. apply fw_wrap64. exact Hb.
Qed.

Lemma fw_cur_ne (b : mword 44) (d : Z) : 0 <= d < 512 -> fw_cur b d <> fw_cur b 512.
Proof.
  intros Hd He. apply (f_equal bv_unsigned) in He.
  rewrite (fw_cur_unsigned b d ltac:(lia)) in He.
  rewrite (fw_cur_unsigned b 512 ltac:(lia)) in He.
  revert He. generalize (bv_unsigned b). intros B HB. lia.
Qed.

(* the [andi a4,a5,14] leaf test -- "a POINTER masks to zero" -- is
   [PtBuild.fw_ptr_and14], next to the V-bit ([pte_valid_bit0]) and V|U-pair
   ([pte_vu_bits]) bridges of the same family. *)

(* [CommonWalk.u_next_base] and [ProcPtOwn.pte_ppn] are the same ppn, one
   [autocast] apart. *)
Lemma fw_next_ppn (w : mword 64) : pte_ppn w = u_next_base w.
Proof. unfold pte_ppn, u_next_base. rewrite autocast_id. reflexivity. Qed.

(* ---- freewalk's per-slot precondition, phrased so neither arm has to
        case on [lvl] ------------------------------------------------- *)

Definition fw_kid (lvl : nat) (t : ptree) (i : mword 9) : option (nat * ptree) :=
  match lvl with
  | O => None
  | S l => match pt_kids t i with Some c => Some (l, c) | None => None end
  end.

Definition fw_ok (lvl : nat) (t : ptree) (i : mword 9) : Prop :=
  (fw_kid lvl t i = None /\ pt_ents t i = mword_of_int 0)
  \/ (exists (l : nat) (c : ptree),
        fw_kid lvl t i = Some (l, c) /\
        pte_valid (pt_ents t i) /\ pte_ptr (pt_ents t i) /\
        u_next_base (pt_ents t i) = pt_base c /\ pt_free_ok l c).

Lemma fw_ok_of (lvl : nat) (t : ptree) :
  pt_free_ok lvl t -> forall i : mword 9, fw_ok lvl t i.
Proof.
  destruct lvl as [| l]; intros H i.
  - left. split; [reflexivity | exact (H i)].
  - destruct (H i) as [(Hk & He) | (c & Hk & Hv & Hp & Hb & Hf)].
    + left. split; [| exact He]. unfold fw_kid. rewrite Hk. reflexivity.
    + right. exists l, c. unfold fw_kid. rewrite Hk.
      split; [reflexivity |]. split; [exact Hv |]. split; [exact Hp |].
      split; [exact Hb | exact Hf].
Qed.

Lemma fw_kid_lt (lvl : nat) (t : ptree) (i : mword 9) (l : nat) (c : ptree) :
  fw_kid lvl t i = Some (l, c) -> (l < lvl)%nat.
Proof.
  unfold fw_kid. destruct lvl as [| l0]; [discriminate |].
  destruct (pt_kids t i) as [c0 |]; [| discriminate].
  intros H. inversion H. lia.
Qed.

(* ===================================================================== *)
(*  THE WHOLE FUNCTION.                                                   *)
(* ===================================================================== *)

Module FreewalkProof (Kfree : KFREE) : FREEWALK.

Section ProofFreewalk.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{GEN : GenId}.
  Context {kt : ktier}.
  (* NOTE: no shared [Context `{CID : CpuId}] here -- fw_epilogue / fw_loop /
     fw_body apply each other at a hart a [wp_next] crossing may have
     migrated to, so each needs its OWN implicit per-lemma [CID] binder
     (shadowing what a section Context would give); see the porting guide's
     "Two things a DECOMPOSED proof needs" and ProofWalk.v's identical note. *)

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Ltac slot_addr :=
    unfold pa_stk, add_vec_int; rewrite pa_stk_off2;
    apply f_equal; apply bv_eq; vm_compute; reflexivity.

  Ltac lkp :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | match goal with |- context [ ?M !!! _ ] => is_var M; progress unfold M end ];
    repeat rewrite add_vec_zero_l;
    first [ reflexivity | assumption ].

  Ltac lkp0 :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | match goal with |- context [ ?M !!! _ ] => is_var M; progress unfold M end ];
    repeat rewrite add_vec_zero_l.

  (* the [upd_ne] side goal is [Regidx c <> Regidx k] (LOOKUP key first): either
     [k] is not callee-saved at all, or it is one of the five freewalk writes
     and the excluded-register hypothesis is in context.  Never [congruence]
     here -- see optimization.md's peel rule. *)
  Ltac thr_side :=
    first
      [ apply not_eq_sym; apply is_cs_idx_true_neq;
        [ vm_compute; reflexivity | assumption ]
      | let He := fresh "Hxx" in
        intro He; injection He as He; subst;
        lazymatch goal with H : ?a <> ?a |- _ => exact (H eq_refl) end ].

  Ltac thr_peel :=
    repeat first
      [ rewrite upd_ne; [| thr_side]
      | match goal with |- context [ ?M !!! _ ] => is_var M; progress unfold M end ].

  (* ================================================================== *)
  (*  §1  The loop's resource split.                                     *)
  (* ================================================================== *)

  (* the subtree hanging off slot [i] of a level-[lvl] node (nothing at
     level 0, and nothing where the description claims no child) *)
  Definition fw_slot (lvl : nat) (t : ptree) (i : mword 9) : iProp Σ :=
    match fw_kid lvl t i with
    | Some lc => ptree_own (fst lc) (DfracOwn 1) (snd lc)
    | None => emp
    end%I.

  (* slots [0, d): whatever the loop left in them *)
  Definition fw_done (b : mword 44) (d : Z) : iProp Σ :=
    ([∗ list] i ∈ seqZ 0 d, ∃ w : mword 64, u_pte_addr b (mword_of_int i) ↦ₚ₈ w)%I.

  (* slots [d, 512): still the description's words, and still their subtrees *)
  Definition fw_todo (lvl : nat) (t : ptree) (d : Z) : iProp Σ :=
    ([∗ list] i ∈ seqZ d (512 - d),
       u_pte_addr (pt_base t) (mword_of_int i) ↦ₚ₈ pt_ents t (mword_of_int i)
       ∗ fw_slot lvl t (mword_of_int i))%I.

  Lemma fw_open (lvl : nat) (t : ptree) :
    ptree_own lvl (DfracOwn 1) t ⊢ pt_node_claim (pt_base t) ∗ fw_todo lvl t 0.
  Proof.
    rewrite /fw_todo. replace (512 - 0) with 512 by lia.
    rewrite big_sepL_sep.
    destruct lvl as [| l].
    - rewrite /ptree_own /pt_page_own /fw_slot /fw_kid.
      iIntros "[[#Hcl Hpg] _]". iFrame "Hcl Hpg".
      rewrite big_sepL_emp. done.
    - rewrite ptree_own_S /pt_page_own /pt_kids_own /fw_slot /fw_kid.
      iIntros "[[#Hcl Hpg] Hks]". iFrame "Hcl Hpg".
      iApply (big_sepL_mono with "Hks"). intros k j _. cbn beta.
      destruct (pt_kids t (mword_of_int j)); reflexivity.
  Qed.

  Lemma fw_todo_cons (lvl : nat) (t : ptree) (d : Z) :
    0 <= d < 512 ->
    fw_todo lvl t d ⊢
      (u_pte_addr (pt_base t) (mword_of_int d) ↦ₚ₈ pt_ents t (mword_of_int d)
       ∗ fw_slot lvl t (mword_of_int d))
      ∗ fw_todo lvl t (d + 1).
  Proof.
    intros Hd. rewrite /fw_todo.
    rewrite (seqZ_cons d (512 - d) ltac:(lia)).
    assert (E1 : Z.succ d = d + 1) by lia.
    assert (E2 : Z.pred (512 - d) = 512 - (d + 1)) by lia.
    rewrite E1 E2.
    iIntros "[Hh Ht]". iFrame "Hh Ht".
  Qed.

  Lemma fw_done_snoc (b : mword 44) (d : Z) :
    0 <= d ->
    fw_done b d ∗ (∃ w : mword 64, u_pte_addr b (mword_of_int d) ↦ₚ₈ w)
    ⊢ fw_done b (d + 1).
  Proof.
    intros Hd. rewrite /fw_done.
    rewrite (seqZ_app 0 d 1 ltac:(lia) ltac:(lia)).
    rewrite big_sepL_app.
    assert (E0 : 0 + d = d) by lia. rewrite E0.
    rewrite (seqZ_cons d 1 ltac:(lia)).
    rewrite (seqZ_nil (Z.succ d) (Z.pred 1) ltac:(lia)).
    iIntros "[Ha Hb]". iSplitL "Ha"; [iExact "Ha" |].
    iSplitL "Hb"; [iExact "Hb" |]. done.
  Qed.

  (* ================================================================== *)
  (*  §2  The contract, as a Prop, so the induction can name it.         *)
  (* ================================================================== *)

  Definition fw_rec (l : nat) : Prop :=
    forall (CID0 : CpuId) (γa : gname) (mm : regfile) (t : ptree)
           (K : nat) (eb : bool) (p : mword 64) (ilvl : nat) (b : bool) (lks : gset string),
      wp_freewalk_sconf_body kt (CID:=CID0) γa mm t l K eb p ilvl b lks.

  (* ================================================================== *)
  (*  §3  THE EXIT (+0x48 .. +0x5a): kfree(pagetable), then the epilogue. *)
  (* ================================================================== *)
  Local Lemma fw_epilogue `{CID0 : CpuId} (ilvl : nat) (γa : gname)
      (mm mj : regfile) (K : nat) (sp0 : mword 64) (bpt : mword 44)
      (eb : bool) (p : mword 64) (b : bool) (lks : gset string) :
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) in
    (20 <= K)%nat ->
    (Z.of_nat ilvl + 1 < 2 ^ 31)%Z ->
    mm !!! Regidx csp_rs1 = sp0 ->
    mj !!! Regidx csp_rs1 = spr ->
    mj !!! Regidx Rs3 = page_base bpt ->
    fw_thr mm mj ->
    (* THE FRESHNESS PREMISE: this epilogue acquires and releases
       [kmem.lock] internally (balanced -- [lks] is unchanged), so the
       caller must already hold only locks BELOW "kmem"'s rank. *)
    locks_below lks "kmem" ->
    sie_cap_gpr kt mj (K - 6) b p -∗
    cpu_own ilvl eb p b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.freewalk + 0x48) : mword 64) -∗
    kfree_pre (page_base bpt) -∗
    kalloc_env γa None -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx Rra) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx Rs0) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx Rs1) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx Rs2) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx Rs3) -∗
    (∃ w : mword 64, pa_stk sp0 6 ↦₈ w) -∗
    wp_next b p (fun (CID : CpuId) =>
    ∀ mf : regfile,
      sie_cap_gpr kt mf K b p -∗
      cpu_own ilvl eb p b lks -∗
      pc_is (ret_pc (mm !!! Regidx Rra)) -∗
      ⌜callee_saved mm mf⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros spr HK Hilvl Hmmsp Hjsp Hjs3 Hjthr Hfresh.
    iIntros "Hcg Hcnt #Htext Hpc Hpre #Henv Hk1 Hk2 Hk3 Hk4 Hk5 Hk6 Hcont".
    iDestruct "Hk6" as (u6) "Hk6".
    iDestruct "Henv" as (γk) "(#Hlock & #Havail)".
    iPoseProof (fwi_48 with "Htext") as "Hi48".
    iPoseProof (fwi_4a with "Htext") as "Hi4a".
    iPoseProof (fwi_4e with "Htext") as "Hi4e".
    iPoseProof (fwi_50 with "Htext") as "Hi50".
    iPoseProof (fwi_52 with "Htext") as "Hi52".
    iPoseProof (fwi_54 with "Htext") as "Hi54".
    iPoseProof (fwi_56 with "Htext") as "Hi56".
    iPoseProof (fwi_58 with "Htext") as "Hi58".
    iPoseProof (fwi_5a with "Htext") as "Hi5a".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (unfold spr; slot_addr).
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (unfold spr; slot_addr).
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (unfold spr; slot_addr).
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (unfold spr; slot_addr).
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (unfold spr; slot_addr).
    assert (Hsprstk : pa_stk sp0 6 = spr).
    { unfold spr, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    (* --- +0x48 c.mv a0,s3 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.freewalk + 0x48)) Ra0 Rs3 mj (K - 6) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi48").
    iIntros (CIDe1 Hse1) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (E0 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mj !!! Regidx Rs3))]> mj).
    assert (HE0a0 : E0 !!! Regidx Ra0 = page_base bpt).
    { rewrite /E0 upd_eq. rewrite add_vec_zero_l. exact Hjs3. }
    assert (Hp4a : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x48) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp4a) in "Hpc".
    (* --- +0x4a jal ra,kfree --- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.freewalk + 0x4a)) Rra
              (mword_of_int 2094724 : mword 21) E0 (K - 6) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi4a").
    iIntros (CIDe2 Hse2) "Hcg Hpc".
    set (E1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.freewalk + 0x4a) : mword 64) 4)]> E0).
    assert (Htgtkf : add_vec (mword_of_int (KernelSyms.freewalk + 0x4a) : mword 64)
              (sign_extend' 64 (mword_of_int 2094724 : mword 21))
            = mword_of_int KernelSyms.kfree) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtkf) in "Hpc".
    assert (HE1a0 : E1 !!! Regidx Ra0 = page_base bpt).
    { rewrite /E1. rewrite upd_ne; [exact HE0a0 | reg_neq]. }
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by lkp.
    assert (HE1thr : fw_thr mm E1).
    { intros c Hc H2 H8 H9 H18 H19. thr_peel. apply Hjthr; assumption. }
    assert (Hret4e : ret_pc (E1 !!! Regidx Rra) = mword_of_int (KernelSyms.freewalk + 0x4e)).
    { rewrite /E1 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iDestruct (cpu_own_transport CID0 CIDe2 ilvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Kfree.wp_kfree_sconf kt γa γk (mword_of_int KernelSyms.kmem)
              (mword_of_int (KernelSyms.kmem + 24)) E1 None ilvl eb p (K - 6)%nat b lks
              ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) Hilvl
              Hfresh
              with "Hcg Hcnt Htext Hpc Hlock [Hpre] Havail").
    all: try lkbelow.
    { rewrite HE1a0. iExact "Hpre". }
    iIntros (CIDkf Hskf mk) "Hcg Hcnt Hpc %Hkcs _".
    iEval (rewrite Hret4e) in "Hpc".
    assert (Hmksp : mk !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hkcs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HE1sp. }
    assert (Hmkthr : fw_thr mm mk).
    { intros c Hc H2 H8 H9 H18 H19.
      rewrite (callee_saved_lookup Hkcs c Hc). apply HE1thr; assumption. }
    (* --- +0x4e c.ldsp ra,40(sp) --- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.freewalk + 0x4e)) (mword_of_int 5 : mword 6) Rra
              mk (K - 6) (mm !!! Regidx Rra) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4e [Hk1]").
    { iEval (rewrite Hmksp Hb1). iExact "Hk1". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hk1". iEval (rewrite Hmksp Hb1) in "Hk1".
    set (E2 := <[Regidx Rra := regval_into_reg (mm !!! Regidx Rra)]> mk).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp50 : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x4e) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp50) in "Hpc".
    (* --- +0x50 c.ldsp s0,32(sp) --- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.freewalk + 0x50)) (mword_of_int 4 : mword 6) Rs0
              E2 (K - 6) (mm !!! Regidx Rs0) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi50 [Hk2]").
    { iEval (rewrite HE2sp Hb2). iExact "Hk2". }
    iIntros (CIDe4 Hse4) "Hcg Hpc Hk2". iEval (rewrite HE2sp Hb2) in "Hk2".
    set (E3 := <[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0)]> E2).
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp52 : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x50) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp52) in "Hpc".
    (* --- +0x52 c.ldsp s1,24(sp) --- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.freewalk + 0x52)) (mword_of_int 3 : mword 6) Rs1
              E3 (K - 6) (mm !!! Regidx Rs1) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi52 [Hk3]").
    { iEval (rewrite HE3sp Hb3). iExact "Hk3". }
    iIntros (CIDe5 Hse5) "Hcg Hpc Hk3". iEval (rewrite HE3sp Hb3) in "Hk3".
    set (E4 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> E3).
    assert (HE4sp : E4 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp54 : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x52) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp54) in "Hpc".
    (* --- +0x54 c.ldsp s2,16(sp) --- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.freewalk + 0x54)) (mword_of_int 2 : mword 6) Rs2
              E4 (K - 6) (mm !!! Regidx Rs2) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi54 [Hk4]").
    { iEval (rewrite HE4sp Hb4). iExact "Hk4". }
    iIntros (CIDe6 Hse6) "Hcg Hpc Hk4". iEval (rewrite HE4sp Hb4) in "Hk4".
    set (E5 := <[Regidx Rs2 := regval_into_reg (mm !!! Regidx Rs2)]> E4).
    assert (HE5sp : E5 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp56 : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x54) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp56) in "Hpc".
    (* --- +0x56 c.ldsp s3,8(sp) --- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.freewalk + 0x56)) (mword_of_int 1 : mword 6) Rs3
              E5 (K - 6) (mm !!! Regidx Rs3) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi56 [Hk5]").
    { iEval (rewrite HE5sp Hb5). iExact "Hk5". }
    iIntros (CIDe7 Hse7) "Hcg Hpc Hk5". iEval (rewrite HE5sp Hb5) in "Hk5".
    set (E6 := <[Regidx Rs3 := regval_into_reg (mm !!! Regidx Rs3)]> E5).
    assert (HE6sp : E6 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp58 : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x56) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp58) in "Hpc".
    (* --- +0x58 c.addi16sp sp,48 : trade the frame back --- *)
    set (E7 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (E6 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E6).
    assert (Hwv : add_vec (E6 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0).
    { rewrite HE6sp. unfold spr. apply frame_cancel_48. }
    assert (Hpop : E6 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E6 !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
    { rewrite Hwv HE6sp. symmetry. exact Hsprstk. }
    iAssert (stack_own (KTR := kt) sp0 6) with "[Hk1 Hk2 Hk3 Hk4 Hk5 Hk6]" as "Hframe".
    { rewrite (stack_own_slots (KTR := kt)). cbn [seq].
      iSplitL "Hk1"; [iExists _; iExact "Hk1" |].
      iSplitL "Hk2"; [iExists _; iExact "Hk2" |].
      iSplitL "Hk3"; [iExists _; iExact "Hk3" |].
      iSplitL "Hk4"; [iExists _; iExact "Hk4" |].
      iSplitL "Hk5"; [iExists _; iExact "Hk5" |].
      iSplitL "Hk6"; [iExists _; iExact "Hk6" |].
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.freewalk + 0x58))
              (mword_of_int 3 : mword 6) E6 (K - 6) 6 b Hpop
              with "Hcg Hpc Hi58 Hframe").
    iIntros (CIDe8 Hse8) "Hcg Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
      (add_vec (E6 !!! Regidx csp_rs1)
         (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E6) with E7.
    assert (Hnk : ((K - 6) + 6)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hp5a : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x58) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5a) in "Hpc".
    (* --- +0x5a c.ret --- *)
    assert (HE7ra : E7 !!! Regidx Rra = mm !!! Regidx Rra) by lkp.
    assert (HE7thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              E7 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H18 H19. thr_peel. apply Hmkthr; assumption. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.freewalk + 0x5a)) Rra E7 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi5a").
    iIntros (CIDe9 Hse9) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    iEval (rewrite HE7ra) in "Hpc".
    iDestruct (cpu_own_transport CIDkf CIDe9 ilvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CIDe9 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! E7 with "Hcg Hcnt Hpc [%]").
    unfold callee_saved. split_and!.
    - rewrite /E7 upd_eq. rewrite Hwv. symmetry. exact Hmmsp.
    - rewrite /E7. rewrite upd_ne; [| reg_neq]. rewrite /E6. rewrite upd_ne; [| reg_neq].
      rewrite /E5. rewrite upd_ne; [| reg_neq]. rewrite /E4. rewrite upd_ne; [| reg_neq].
      rewrite /E3 upd_eq. reflexivity.
    - rewrite /E7. rewrite upd_ne; [| reg_neq]. rewrite /E6. rewrite upd_ne; [| reg_neq].
      rewrite /E5. rewrite upd_ne; [| reg_neq]. rewrite /E4 upd_eq. reflexivity.
    - rewrite /E7. rewrite upd_ne; [| reg_neq]. rewrite /E6. rewrite upd_ne; [| reg_neq].
      rewrite /E5 upd_eq. reflexivity.
    - rewrite /E7. rewrite upd_ne; [| reg_neq]. rewrite /E6 upd_eq. reflexivity.
    - apply HE7thr; [vm_compute; reflexivity | vm_compute; discriminate ..].
    - apply HE7thr; [vm_compute; reflexivity | vm_compute; discriminate ..].
    - apply HE7thr; [vm_compute; reflexivity | vm_compute; discriminate ..].
    - apply HE7thr; [vm_compute; reflexivity | vm_compute; discriminate ..].
    - apply HE7thr; [vm_compute; reflexivity | vm_compute; discriminate ..].
    - apply HE7thr; [vm_compute; reflexivity | vm_compute; discriminate ..].
    - apply HE7thr; [vm_compute; reflexivity | vm_compute; discriminate ..].
    - apply HE7thr; [vm_compute; reflexivity | vm_compute; discriminate ..].
  Qed.

  (* ================================================================== *)
  (*  §4  THE LOOP (+0x2a head, +0x24 tail), by induction on the number   *)
  (*      of slots still to visit.  [REC] is the contract one level down. *)
  (* ================================================================== *)
  (* [fw_loop] is a FUEL INDUCTION on the number of remaining slots [rem],
     carrying its own hart [CID] as PART OF THE SAME induction: [revert CID]
     BEFORE [induction rem] (ProofProcMapstacks.v's validated "two hart
     binders" recipe -- the lemma-level [CID] doubles as the per-recursion-
     instance anchor once reverted) so [IH] re-quantifies it fresh at each
     back-edge.  The +0x24/+0x26 tail is factored into "TAIL", itself
     CpuId-generic (its own [CIDx] binder plus a [b = false -> CIDx = CID]
     premise): both body arms transport ["Hcnt"] to their current hart
     before calling it, and TAIL re-anchors ["Hcont"] with [wp_next_shift]
     only at its OWN recurse-via-[IH] exit (the one place a wp_next-shaped
     resource is forwarded, rather than terminally applied). *)
  Local Lemma fw_loop `{CID : CpuId} (lvl : nat) (REC : forall l, (l < lvl)%nat -> fw_rec l)
      (γa : gname)
      (mm : regfile) (t : ptree) (K : nat) (eb : bool) (p : mword 64)
      (spr : mword 64) (ilvl : nat) (b : bool) (lks : gset string) :
    (6 * S lvl + 14 <= K)%nat ->
    (Z.of_nat ilvl + 1 < 2 ^ 31)%Z ->
    (forall i : mword 9, fw_ok lvl t i) ->
    forall (rem : nat) (d : Z) (m : regfile),
    (1 <= rem)%nat -> (0 <= d)%Z -> (d + Z.of_nat rem = 512)%Z ->
    m !!! Regidx csp_rs1 = spr ->
    m !!! Regidx Rs1 = fw_cur (pt_base t) d ->
    m !!! Regidx Rs2 = add_vec (mword_of_int 4096) (page_base (pt_base t)) ->
    m !!! Regidx Rs3 = page_base (pt_base t) ->
    fw_thr mm m ->
    (* threaded on this recursion's own binder list too: it is what its
       [REC] call one level down, and its own [IH] back-edge, both need. *)
    locks_below lks "kmem" ->
    sie_cap_gpr kt m (K - 6) b p -∗
    cpu_own ilvl eb p b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.freewalk + 0x2a) : mword 64) -∗
    pt_node_claim (pt_base t) -∗
    fw_done (pt_base t) d -∗
    fw_todo lvl t d -∗
    kalloc_env γa None -∗
    wp_next b p (fun (CID : CpuId) =>
    ∀ mj : regfile,
      ⌜ mj !!! Regidx csp_rs1 = spr
        /\ mj !!! Regidx Rs3 = page_base (pt_base t)
        /\ fw_thr mm mj ⌝ -∗
      sie_cap_gpr kt mj (K - 6) b p -∗
      cpu_own ilvl eb p b lks -∗
      pc_is (mword_of_int (KernelSyms.freewalk + 0x48) : mword 64) -∗
      fw_done (pt_base t) 512 -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hilvl Hok.
    intro rem.
    revert CID.
    induction rem as [| rem' IH];
      intros CID d m Hrem Hd0 Hsum Hsp Hs1 Hs2 Hs3 Hthr Hbelow;
      [ destruct (Nat.nle_succ_0 0 Hrem) |].
    iIntros "Hcg Hcnt #Htext Hpc #Hcl Hdone Htodo #Henv Hcont".
    assert (Hdlt : (0 <= d < 512)%Z) by lia.
    iPoseProof (fwi_2a with "Htext") as "Hi2a".
    iPoseProof (fwi_2c with "Htext") as "Hi2c".
    iPoseProof (fwi_30 with "Htext") as "Hi30".
    iPoseProof (fwi_32 with "Htext") as "Hi32".
    iPoseProof (fwi_36 with "Htext") as "Hi36".
    iPoseProof (fwi_38 with "Htext") as "Hi38".
    iPoseProof (fwi_3a with "Htext") as "Hi3a".
    iPoseProof (fwi_3e with "Htext") as "Hi3e".
    iPoseProof (fwi_42 with "Htext") as "Hi42".
    iPoseProof (fwi_46 with "Htext") as "Hi46".
    (* ================================================================ *)
    (*  THE +0x24 JOIN: the loop tail (bump, exit test), over the         *)
    (*  post-body slot accounting.  Both arms of the body reach it.       *)
    (* ================================================================ *)
    iAssert (∀ (CIDx : CpuId) (mt : regfile),
        ⌜ mt !!! Regidx csp_rs1 = spr
          /\ mt !!! Regidx Rs1 = fw_cur (pt_base t) d
          /\ mt !!! Regidx Rs2 = add_vec (mword_of_int 4096) (page_base (pt_base t))
          /\ mt !!! Regidx Rs3 = page_base (pt_base t)
          /\ fw_thr mm mt
          /\ (b = false \/ p = zero_reg -> (CIDx : CPU) = (CID : CPU)) ⌝ -∗
        sie_cap_gpr kt (CID:=CIDx) mt (K - 6) b p -∗
        cpu_own (CID:=CIDx) ilvl eb p b lks -∗
        pc_is (CID:=CIDx) (mword_of_int (KernelSyms.freewalk + 0x24) : mword 64) -∗
        fw_done (pt_base t) (d + 1) -∗
        fw_todo lvl t (d + 1) -∗
        WP (Loop : expr riscv_lang))%I with "[Hcont]" as "TAIL".
    { iIntros (CIDx mt).
      iIntros "(%Htsp & %Hts1 & %Hts2 & %Hts3 & %Htthr & %Hshiftx) Hcg Hcnt Hpc Hdone Htodo".
      iPoseProof (fwi_24 with "Htext") as "Hi24".
      iPoseProof (fwi_26 with "Htext") as "Hi26".
      (* --- +0x24 c.addi s1,s1,8 --- *)
      iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.freewalk + 0x24)) Rs1
                (mword_of_int 8 : mword 6) mt (K - 6) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi24").
      iIntros (CIDt1 Hst1) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (T1 := <[Regidx Rs1 := regval_into_reg
                    (add_vec (mt !!! Regidx Rs1)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))))]> mt).
      assert (HT1s1 : T1 !!! Regidx Rs1 = fw_cur (pt_base t) (d + 1)).
      { rewrite /T1 upd_eq. rewrite Hts1. apply fw_cur_step. lia. }
      assert (HT1sp : T1 !!! Regidx csp_rs1 = spr) by lkp.
      assert (HT1s2 : T1 !!! Regidx Rs2
                      = add_vec (mword_of_int 4096) (page_base (pt_base t))) by lkp.
      assert (HT1s3 : T1 !!! Regidx Rs3 = page_base (pt_base t)) by lkp.
      assert (HT1thr : fw_thr mm T1).
      { intros c Hc H2 H8 H9 H18 H19. thr_peel. apply Htthr; assumption. }
      assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x24) : mword 64) 2
                     = mword_of_int (KernelSyms.freewalk + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp26) in "Hpc".
      (* --- +0x26 beq s1,s2 : the cursor reached &pagetable[512] ? --- *)
      destruct (Nat.eq_dec rem' 0) as [Hr0 | Hrne].
      { (* all 512 slots done: leave for the kfree at +0x48 *)
        assert (Hd512 : (d + 1 = 512)%Z) by lia.
        assert (Hcmp : eq_vec (rget T1 Rs1) (rget T1 Rs2) = true).
        { rgne; rgne. rewrite HT1s1 HT1s2. rewrite Hd512. rewrite fw_cur_end.
          apply eq_vec_true_iff. reflexivity. }
        iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.freewalk + 0x26))
                  (mword_of_int 34 : mword 13) Rs2 Rs1 T1 (K - 6) b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi26").
        iNext. iIntros (CIDt2 Hst2) "Hcg Hpc".
        assert (Htgt48 : add_vec (mword_of_int (KernelSyms.freewalk + 0x26) : mword 64)
                  (sign_extend' 64 (mword_of_int 34 : mword 13))
                = mword_of_int (KernelSyms.freewalk + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt48) in "Hpc".
        iEval (rewrite Hd512) in "Hdone".
        iDestruct (cpu_own_transport CIDx CIDt2 ilvl eb p b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iSpecialize ("Hcont" $! CIDt2 with "[]"); [iPureIntro; wp_next_chain|].
        iApply ("Hcont" $! T1 with "[%] Hcg Hcnt Hpc Hdone").
        split_and!; assumption. }
      (* more slots: back to the loop head *)
      assert (Hcmp : eq_vec (rget T1 Rs1) (rget T1 Rs2) = false).
      { rgne; rgne. rewrite HT1s1 HT1s2. rewrite <- fw_cur_end.
        apply eq_vec_false_iff. apply fw_cur_ne. lia. }
      iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.freewalk + 0x26))
                (mword_of_int 34 : mword 13) Rs2 Rs1 T1 (K - 6) b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp with "Hcg Hpc Hi26").
      iIntros (CIDt3 Hst3) "Hcg Hpc".
      assert (Hp2a : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x26) : mword 64) 4
                     = mword_of_int (KernelSyms.freewalk + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp2a) in "Hpc".
      assert (Hshiftrec : b = false \/ p = zero_reg -> (CIDt3 : CPU) = (CID : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift Hshiftrec with "Hcont") as "Hcont".
      iDestruct (cpu_own_transport CIDx CIDt3 ilvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply (IH CIDt3 (d + 1) T1 ltac:(lia) ltac:(lia) ltac:(lia)
                HT1sp HT1s1 HT1s2 HT1s3 HT1thr Hbelow
                with "Hcg Hcnt Htext Hpc Hcl Hdone Htodo Henv Hcont"). }
    (* ================================================================ *)
    (*  THE BODY: read the slot, classify it, maybe recurse.             *)
    (* ================================================================ *)
    iDestruct (fw_todo_cons lvl t d Hdlt with "Htodo") as "[[Hslot Hch] Htodo]".
    iDestruct (pt_slot_phys_to_mem (pt_base t) (mword_of_int d) (DfracOwn 1)
                 (pt_ents t (mword_of_int d)) with "Hcl Hslot") as "Hcell".
    assert (Hcuraddr : fw_cur (pt_base t) d = u_pte_addr (pt_base t) (mword_of_int d))
      by (apply fw_cur_slot; lia).
    assert (Hea0 : forall X : mword 64,
        add_vec X (sign_extend' 64 (zero_extend' 12
          (concat_vec (mword_of_int 0 : mword 5) ('b"000")))) = X).
    { intro X.
      replace (sign_extend' 64 (zero_extend' 12
        (concat_vec (mword_of_int 0 : mword 5) ('b"000"))) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    (* --- +0x2a c.ld a5,0(s1) --- *)
    iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.freewalk + 0x2a)) Ra5 Rs1
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))
              m (K - 6) (pt_ents t (mword_of_int d)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2a [Hcell]").
    { iEval (rgne; rewrite Hea0 Hs1 Hcuraddr). iExact "Hcell". }
    iIntros (CIDb1 Hsb1) "Hcg Hpc Hcell". iEval (rgne; rewrite Hea0 Hs1 Hcuraddr) in "Hcell".
    set (B1 := <[Regidx Ra5 := regval_into_reg (pt_ents t (mword_of_int d))]> m).
    assert (HB1a5 : B1 !!! Regidx Ra5 = pt_ents t (mword_of_int d))
      by (rewrite /B1 upd_eq; reflexivity).
    assert (Hp2c : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x2a) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2c) in "Hpc".
    (* --- +0x2c andi a4,a5,1 : PTE_V --- *)
    assert (Hand1 : and_vec (rget B1 Ra5)
                      (sign_extend' 64 (mword_of_int 1 : mword 12))
                    = and_vec (pt_ents t (mword_of_int d))
                        (sign_extend' 64 (mword_of_int 1 : mword 12))).
    { rgne. rewrite HB1a5; reflexivity. }
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.freewalk + 0x2c)) Ra4 Ra5
              (mword_of_int 1 : mword 12)
              (and_vec (pt_ents t (mword_of_int d))
                 (sign_extend' 64 (mword_of_int 1 : mword 12)))
              B1 (K - 6) b
              ltac:(vm_compute; discriminate) ltac:(rdok) Hand1
              with "Hcg Hpc Hi2c").
    iIntros (CIDb2 Hsb2) "Hcg Hpc".
    set (B2 := <[Regidx Ra4 := regval_into_reg
                  (and_vec (pt_ents t (mword_of_int d))
                     (sign_extend' 64 (mword_of_int 1 : mword 12)))]> B1).
    assert (HB2a4 : B2 !!! Regidx Ra4
                    = and_vec (pt_ents t (mword_of_int d))
                        (sign_extend' 64 (mword_of_int 1 : mword 12)))
      by (rewrite /B2 upd_eq; reflexivity).
    assert (HB2a5 : B2 !!! Regidx Ra5 = pt_ents t (mword_of_int d)).
    { rewrite /B2. rewrite upd_ne; [exact HB1a5 | reg_neq]. }
    assert (HB2sp : B2 !!! Regidx csp_rs1 = spr) by lkp.
    assert (HB2s1 : B2 !!! Regidx Rs1 = fw_cur (pt_base t) d) by lkp.
    assert (HB2s2 : B2 !!! Regidx Rs2
                    = add_vec (mword_of_int 4096) (page_base (pt_base t))) by lkp.
    assert (HB2s3 : B2 !!! Regidx Rs3 = page_base (pt_base t)) by lkp.
    assert (HB2thr : fw_thr mm B2).
    { intros c Hc H2 H8 H9 H18 H19. thr_peel. apply Hthr; assumption. }
    assert (Hp30 : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x2c) : mword 64) 4
                   = mword_of_int (KernelSyms.freewalk + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp30) in "Hpc".
    assert (Htgt24 : add_vec (mword_of_int (KernelSyms.freewalk + 0x30) : mword 64)
              (sign_extend' 64 (sign_extend' 13
                 (concat_vec (mword_of_int 250 : mword 8) ('b"0"))))
            = mword_of_int (KernelSyms.freewalk + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    destruct (Hok (mword_of_int d : mword 9))
      as [(Hkid & Hzero) | (l & c & Hkid & Hv & Hptr & Hnb & Hfok)].
    { (* ---- the slot claims no child: V is clear, next slot ---- *)
      assert (Hbz : eq_vec (rget B2 Ra4) zero_reg = true).
      { rgne. rewrite HB2a4 Hzero. vm_compute; reflexivity. }
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.freewalk + 0x30))
                (mword_of_int 250 : mword 8) (Cregidx (mword_of_int 6)) Ra4 B2 (K - 6) b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                Hbz ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi30").
      iNext. iIntros (CIDb3 Hsb3) "Hcg Hpc".
      iEval (rewrite Htgt24) in "Hpc".
      iDestruct (pt_slot_mem_to_phys (pt_base t) (mword_of_int d) (DfracOwn 1)
                   (pt_ents t (mword_of_int d)) with "Hcl Hcell") as "Hslot".
      iDestruct (cpu_own_transport CID CIDb3 ilvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply ("TAIL" $! CIDb3 B2 with "[%] Hcg Hcnt Hpc [Hdone Hslot] Htodo").
      { split_and!; [assumption|assumption|assumption|assumption|assumption|wp_next_chain]. }
      { iApply (fw_done_snoc (pt_base t) d ltac:(lia)).
        iSplitL "Hdone"; [iExact "Hdone" | iExists _; iExact "Hslot"]. } }
    (* ---- the slot points at a child node: recurse into it ---- *)
    assert (Hbnz : eq_vec (rget B2 Ra4) zero_reg = false).
    { rgne. rewrite HB2a4. rewrite (pte_valid_bit0 _ Hv). vm_compute; reflexivity. }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.freewalk + 0x30))
              (mword_of_int 250 : mword 8) (Cregidx (mword_of_int 6)) Ra4 B2 (K - 6) b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              Hbnz with "Hcg Hpc Hi30").
    iIntros (CIDb4 Hsb4) "Hcg Hpc".
    assert (Hp32 : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x30) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp32) in "Hpc".
    (* --- +0x32 andi a4,a5,14 : PTE_R|PTE_W|PTE_X.  A POINTER masks to 0,
           so the panic block at +0x18 is unreachable. --- *)
    assert (Hand14 : and_vec (rget B2 Ra5)
                       (sign_extend' 64 (mword_of_int 14 : mword 12))
                     = (mword_of_int 0 : mword 64)).
    { rgne. rewrite HB2a5. exact (fw_ptr_and14 _ Hptr). }
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.freewalk + 0x32)) Ra4 Ra5
              (mword_of_int 14 : mword 12) (mword_of_int 0 : mword 64) B2 (K - 6) b
              ltac:(vm_compute; discriminate) ltac:(rdok) Hand14
              with "Hcg Hpc Hi32").
    iIntros (CIDb5 Hsb5) "Hcg Hpc".
    set (B3 := <[Regidx Ra4 := regval_into_reg (mword_of_int 0 : mword 64)]> B2).
    assert (HB3a4 : B3 !!! Regidx Ra4 = (mword_of_int 0 : mword 64))
      by (rewrite /B3 upd_eq; reflexivity).
    assert (HB3a5 : B3 !!! Regidx Ra5 = pt_ents t (mword_of_int d)).
    { rewrite /B3. rewrite upd_ne; [exact HB2a5 | reg_neq]. }
    assert (Hp36 : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x32) : mword 64) 4
                   = mword_of_int (KernelSyms.freewalk + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp36) in "Hpc".
    (* --- +0x36 c.bnez a4 : NOT taken (the panic block is dead) --- *)
    assert (Hnz : neq_vec (rget B3 Ra4) zero_reg = false).
    { rgne. rewrite HB3a4. vm_compute; reflexivity. }
    iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.freewalk + 0x36))
              (mword_of_int 241 : mword 8) (Cregidx (mword_of_int 6)) Ra4 B3 (K - 6) b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hnz
              with "Hcg Hpc Hi36").
    iIntros (CIDb6 Hsb6) "Hcg Hpc".
    assert (Hp38 : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x36) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp38) in "Hpc".
    (* --- +0x38 c.srli a5,a5,0xa  /  +0x3a slli a0,a5,0xc : PTE2PA --- *)
    iApply (wp_csrli_s_sconf (mword_of_int (KernelSyms.freewalk + 0x38)) (Cregidx (mword_of_int 7))
              Ra5 (mword_of_int 10 : mword 6) B3 (K - 6) b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi38").
    iIntros (CIDb7 Hsb7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B4 := <[Regidx Ra5 := regval_into_reg
        (shift_bits_right (B3 !!! Regidx Ra5)
           (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> B3).
    assert (HB4a5 : B4 !!! Regidx Ra5
                    = shift_bits_right (pt_ents t (mword_of_int d))
                        (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0)).
    { rewrite /B4 upd_eq. rewrite HB3a5. reflexivity. }
    assert (Hp3a : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x38) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3a) in "Hpc".
    assert (Hs10 : int_of_mword false
              (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0) = 10)
      by (vm_compute; reflexivity).
    assert (Hs12 : int_of_mword false
              (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0) = 12)
      by (vm_compute; reflexivity).
    assert (Hlt54 : bv_unsigned (pt_ents t (mword_of_int d)) < 18014398509481984)
      by (exact (pte_ptr_hi_zero _ Hv Hptr)).
    assert (Hbc : page_base (pte_ppn (pt_ents t (mword_of_int d))) = page_base (pt_base c)).
    { rewrite fw_next_ppn. rewrite Hnb. reflexivity. }
    assert (Hpte2pa : shift_bits_left (rget B4 Ra5)
              (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
            = page_base (pt_base c)).
    { rgne. rewrite HB4a5. rewrite <- Hbc.
      apply pte2pa; [ exact Hs10 | exact Hs12 | exact Hlt54 ]. }
    iApply (wp_slli_s_sconf (mword_of_int (KernelSyms.freewalk + 0x3a)) Ra0 Ra5
              (mword_of_int 12 : mword 6) (page_base (pt_base c)) B4 (K - 6) b
              ltac:(vm_compute; discriminate) ltac:(rdok) Hpte2pa
              with "Hcg Hpc Hi3a").
    iIntros (CIDb8 Hsb8) "Hcg Hpc".
    set (B5 := <[Regidx Ra0 := regval_into_reg (page_base (pt_base c))]> B4).
    assert (Hp3e : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x3a) : mword 64) 4
                   = mword_of_int (KernelSyms.freewalk + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3e) in "Hpc".
    (* --- +0x3e jal ra,freewalk : THE RECURSIVE CALL --- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.freewalk + 0x3e)) Rra
              (mword_of_int 2097090 : mword 21) B5 (K - 6) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi3e").
    iIntros (CIDb9 Hsb9) "Hcg Hpc".
    set (B6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.freewalk + 0x3e) : mword 64) 4)]> B5).
    assert (Htgtfw : add_vec (mword_of_int (KernelSyms.freewalk + 0x3e) : mword 64)
              (sign_extend' 64 (mword_of_int 2097090 : mword 21))
            = mword_of_int KernelSyms.freewalk) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtfw) in "Hpc".
    assert (HB6a0 : B6 !!! Regidx Ra0 = page_base (pt_base c)).
    { rewrite /B6. rewrite upd_ne; [| reg_neq]. rewrite /B5 upd_eq. reflexivity. }
    assert (HB6sp : B6 !!! Regidx csp_rs1 = spr) by lkp.
    assert (HB6s1 : B6 !!! Regidx Rs1 = fw_cur (pt_base t) d) by lkp.
    assert (HB6s2 : B6 !!! Regidx Rs2
                    = add_vec (mword_of_int 4096) (page_base (pt_base t))) by lkp.
    assert (HB6s3 : B6 !!! Regidx Rs3 = page_base (pt_base t)) by lkp.
    assert (HB6thr : fw_thr mm B6).
    { intros cc Hc H2 H8 H9 H18 H19. thr_peel. apply Hthr; assumption. }
    assert (Hret42 : ret_pc (B6 !!! Regidx Rra) = mword_of_int (KernelSyms.freewalk + 0x42)).
    { rewrite /B6 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    assert (Hlt : (l < lvl)%nat) by (exact (fw_kid_lt lvl t (mword_of_int d) l c Hkid)).
    assert (HKrec : (6 * S l + 14 <= K - 6)%nat) by lia.
    iEval (rewrite /fw_slot Hkid) in "Hch".
    (* [REC] is [fw_rec l], wrapping [wp_freewalk_sconf_body] from
       SpecFreewalk.v at the SAME rank ("kmem"), so [Hbelow] passes
       straight through with no [locks_below_mono] needed. *)
    iDestruct (cpu_own_transport CID CIDb9 ilvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (REC l Hlt CIDb9 γa B6 c (K - 6)%nat eb p ilvl b _ HKrec Hilvl HB6a0 Hfok
              Hbelow
              with "Hcg Hcnt Htext Hpc Hch Henv").
    iIntros (CIDrec Hsrec mr) "Hcg Hcnt Hpc %Hrcs".
    iEval (rewrite Hret42) in "Hpc".
    assert (Hmrsp : mr !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hrcs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HB6sp. }
    assert (Hmrs1 : mr !!! Regidx Rs1 = fw_cur (pt_base t) d).
    { rewrite (callee_saved_lookup Hrcs Rs1 ltac:(vm_compute; reflexivity)).
      exact HB6s1. }
    assert (Hmrs2 : mr !!! Regidx Rs2
                    = add_vec (mword_of_int 4096) (page_base (pt_base t))).
    { rewrite (callee_saved_lookup Hrcs Rs2 ltac:(vm_compute; reflexivity)).
      exact HB6s2. }
    assert (Hmrs3 : mr !!! Regidx Rs3 = page_base (pt_base t)).
    { rewrite (callee_saved_lookup Hrcs Rs3 ltac:(vm_compute; reflexivity)).
      exact HB6s3. }
    assert (Hmrthr : fw_thr mm mr).
    { intros cc Hc H2 H8 H9 H18 H19.
      rewrite (callee_saved_lookup Hrcs cc Hc). apply HB6thr; assumption. }
    (* --- +0x42 sd zero,0(s1) : pagetable[i] = 0 --- *)
    assert (Hzoff : forall X : mword 64,
        add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X).
    { intro X.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    iApply (wp_sd_zero_s_sconf (mword_of_int (KernelSyms.freewalk + 0x42)) Rs1
              (mword_of_int 0 : mword 12) mr (K - 6) (pt_ents t (mword_of_int d)) b
              with "Hcg Hpc Hi42 [Hcell]").
    { iEval (rgne; rewrite Hzoff Hmrs1 Hcuraddr). iExact "Hcell". }
    iIntros (CIDb10 Hsb10) "Hcg Hpc Hcell". iEval (rgne; rewrite Hzoff Hmrs1 Hcuraddr) in "Hcell".
    assert (Hzr : (zero_reg : mword 64) = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hzr) in "Hcell".
    iDestruct (pt_slot_mem_to_phys (pt_base t) (mword_of_int d) (DfracOwn 1)
                 (mword_of_int 0) with "Hcl Hcell") as "Hslot".
    assert (Hp46 : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x42) : mword 64) 4
                   = mword_of_int (KernelSyms.freewalk + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp46) in "Hpc".
    (* --- +0x46 c.j -0x22 : back to the loop tail --- *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.freewalk + 0x46))
              (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")))
              mr (K - 6) b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi46").
    iIntros (CIDb11 Hsb11). iNext. iIntros "Hcg Hpc".
    assert (Htgt24' : add_vec (mword_of_int (KernelSyms.freewalk + 0x46) : mword 64)
              (sign_extend' 64 (sign_extend' 21
                 (concat_vec (mword_of_int 2031 : mword 11) ('b"0"))))
            = mword_of_int (KernelSyms.freewalk + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt24') in "Hpc".
    iDestruct (cpu_own_transport CIDrec CIDb11 ilvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply ("TAIL" $! CIDb11 mr with "[%] Hcg Hcnt Hpc [Hdone Hslot] Htodo").
    { split_and!; [assumption|assumption|assumption|assumption|assumption|wp_next_chain]. }
    { iApply (fw_done_snoc (pt_base t) d ltac:(lia)).
      iSplitL "Hdone"; [iExact "Hdone" | iExists _; iExact "Hslot"]. }
  Qed.

  (* ================================================================== *)
  (*  §5  THE WHOLE FUNCTION at one level, over [REC] one level down.     *)
  (* ================================================================== *)
  Local Lemma fw_body (lvl : nat) (REC : forall l, (l < lvl)%nat -> fw_rec l) : fw_rec lvl.
  Proof.
    unfold fw_rec. intros CID0 γa mm t K eb p ilvl b lks.
    cbv beta delta [wp_freewalk_sconf_body].
    intros pcE ret_tgt HK Hilvl Ha0 Hfree Hbelow.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    iIntros "Hcg Hcnt #Htext Hpc Hptree #Henv Hcont".
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhwc Hcg]".
    iDestruct "Hhwc" as (hwmisa0 hwmseccfg0 hwpmar0 hwelp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hkmapb)".
    iDestruct (fw_open lvl t with "Hptree") as "[#Hcl Htodo]".
    iDestruct "Hcl" as "#(%Hkd & %Hpv & Hkat)".
    iAssert (pt_node_claim (pt_base t)) as "#Hclaim".
    { rewrite /pt_node_claim. iSplitR; [iPureIntro; exact Hkd |].
      iSplitR; [iPureIntro; exact Hpv | iExact "Hkat"]. }
    iPoseProof (fwi_00 with "Htext") as "Hi00".
    iPoseProof (fwi_02 with "Htext") as "Hi02".
    iPoseProof (fwi_04 with "Htext") as "Hi04".
    iPoseProof (fwi_06 with "Htext") as "Hi06".
    iPoseProof (fwi_08 with "Htext") as "Hi08".
    iPoseProof (fwi_0a with "Htext") as "Hi0a".
    iPoseProof (fwi_0c with "Htext") as "Hi0c".
    iPoseProof (fwi_0e with "Htext") as "Hi0e".
    iPoseProof (fwi_10 with "Htext") as "Hi10".
    iPoseProof (fwi_12 with "Htext") as "Hi12".
    iPoseProof (fwi_14 with "Htext") as "Hi14".
    iPoseProof (fwi_16 with "Htext") as "Hi16".
    (* --- +0x00 c.addi16sp sp,-48 : the 6-slot frame push --- *)
    assert (Hspm : mm !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                    = pa_stk (mm !!! Regidx csp_rs1) 6).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) mm K 6 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (mm !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> mm).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> mm) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := kt)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & _)".
    iDestruct "S1" as (u1) "Hk1".   iDestruct "S2" as (u2) "Hk2".
    iDestruct "S3" as (u3) "Hk3".   iDestruct "S4" as (u4) "Hk4".
    iDestruct "S5" as (u5) "Hk5".   iDestruct "S6" as (u6) "Hk6".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (unfold spr, sp0; slot_addr).
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (unfold spr, sp0; slot_addr).
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (unfold spr, sp0; slot_addr).
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (unfold spr, sp0; slot_addr).
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (unfold spr, sp0; slot_addr).
    assert (Hq02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.freewalk + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq02) in "Hpc".
    (* --- +0x02 c.sdsp ra,40(sp) --- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.freewalk + 0x02)) (mword_of_int 5 : mword 6) Rra
              R1 (K - 6) u1 b with "Hcg Hpc Hi02 [Hk1]").
    { iEval (rewrite HspR1 Hb1). iExact "Hk1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hk1". iEval (rewrite HspR1 Hb1) in "Hk1".
    iEval (rgne) in "Hk1".
    assert (HR1ra : R1 !!! Regidx Rra = mm !!! Regidx Rra) by lkp.
    iEval (rewrite HR1ra) in "Hk1".
    assert (Hq04 : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x02) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq04) in "Hpc".
    (* --- +0x04 c.sdsp s0,32(sp) --- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.freewalk + 0x04)) (mword_of_int 4 : mword 6) Rs0
              R1 (K - 6) u2 b with "Hcg Hpc Hi04 [Hk2]").
    { iEval (rewrite HspR1 Hb2). iExact "Hk2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hk2". iEval (rewrite HspR1 Hb2) in "Hk2".
    iEval (rgne) in "Hk2".
    assert (HR1s0 : R1 !!! Regidx Rs0 = mm !!! Regidx Rs0) by lkp.
    iEval (rewrite HR1s0) in "Hk2".
    assert (Hq06 : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x04) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq06) in "Hpc".
    (* --- +0x06 c.sdsp s1,24(sp) --- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.freewalk + 0x06)) (mword_of_int 3 : mword 6) Rs1
              R1 (K - 6) u3 b with "Hcg Hpc Hi06 [Hk3]").
    { iEval (rewrite HspR1 Hb3). iExact "Hk3". }
    iIntros (CID4 Hs4) "Hcg Hpc Hk3". iEval (rewrite HspR1 Hb3) in "Hk3".
    iEval (rgne) in "Hk3".
    assert (HR1s1 : R1 !!! Regidx Rs1 = mm !!! Regidx Rs1) by lkp.
    iEval (rewrite HR1s1) in "Hk3".
    assert (Hq08 : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x06) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq08) in "Hpc".
    (* --- +0x08 c.sdsp s2,16(sp) --- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.freewalk + 0x08)) (mword_of_int 2 : mword 6) Rs2
              R1 (K - 6) u4 b with "Hcg Hpc Hi08 [Hk4]").
    { iEval (rewrite HspR1 Hb4). iExact "Hk4". }
    iIntros (CID5 Hs5) "Hcg Hpc Hk4". iEval (rewrite HspR1 Hb4) in "Hk4".
    iEval (rgne) in "Hk4".
    assert (HR1s2 : R1 !!! Regidx Rs2 = mm !!! Regidx Rs2) by lkp.
    iEval (rewrite HR1s2) in "Hk4".
    assert (Hq0a : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x08) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq0a) in "Hpc".
    (* --- +0x0a c.sdsp s3,8(sp) --- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.freewalk + 0x0a)) (mword_of_int 1 : mword 6) Rs3
              R1 (K - 6) u5 b with "Hcg Hpc Hi0a [Hk5]").
    { iEval (rewrite HspR1 Hb5). iExact "Hk5". }
    iIntros (CID6 Hs6) "Hcg Hpc Hk5". iEval (rewrite HspR1 Hb5) in "Hk5".
    iEval (rgne) in "Hk5".
    assert (HR1s3 : R1 !!! Regidx Rs3 = mm !!! Regidx Rs3) by lkp.
    iEval (rewrite HR1s3) in "Hk5".
    assert (Hq0c : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x0a) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq0c) in "Hpc".
    (* --- +0x0c c.addi4spn s0,sp,48 --- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.freewalk + 0x0c)) (Cregidx (mword_of_int 0))
              (mword_of_int 12 : mword 8) Rs0 R1 (K - 6) b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    assert (Hq0e : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x0c) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq0e) in "Hpc".
    (* --- +0x0e c.mv s3,a0 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.freewalk + 0x0e)) Rs3 Ra0 R2 (K - 6) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R3 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    assert (Hq10 : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x0e) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq10) in "Hpc".
    (* --- +0x10 c.mv s1,a0 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.freewalk + 0x10)) Rs1 Ra0 R3 (K - 6) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10").
    iIntros (CID9 Hs9) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R4 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (R3 !!! Regidx Ra0))]> R3).
    assert (Hq12 : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x10) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq12) in "Hpc".
    (* --- +0x12 c.lui s2,0x1 : PGSIZE --- *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.freewalk + 0x12)) Rs2
              (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
              R4 (K - 6) b ltac:(vm_compute; discriminate) ltac:(rdok)
              lui_4096 with "Hcg Hpc Hi12").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (R5 := <[Regidx Rs2 := regval_into_reg (mword_of_int 4096 : mword 64)]> R4).
    assert (Hq14 : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x12) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq14) in "Hpc".
    (* --- +0x14 c.add s2,s2,a0 : the end sentinel --- *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.freewalk + 0x14)) Rs2 Ra0 R5 (K - 6) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14").
    iIntros (CID11 Hs11) "Hcg Hpc".
    iEval (rgne; rgne) in "Hcg".
    set (R6 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (R5 !!! Regidx Rs2) (R5 !!! Regidx Ra0))]> R5).
    assert (Hq16 : add_vec_int (mword_of_int (KernelSyms.freewalk + 0x14) : mword 64) 2
                   = mword_of_int (KernelSyms.freewalk + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq16) in "Hpc".
    (* ---- the register facts at the loop entry ---- *)
    assert (HR6sp : R6 !!! Regidx csp_rs1 = spr) by lkp.
    assert (HR6s1 : R6 !!! Regidx Rs1 = fw_cur (pt_base t) 0).
    { rewrite fw_cur_zero. rewrite /R6. rewrite upd_ne; [| reg_neq].
      rewrite /R5. rewrite upd_ne; [| reg_neq]. rewrite /R4 upd_eq.
      rewrite add_vec_zero_l. lkp0. exact Ha0. }
    assert (HR6s2 : R6 !!! Regidx Rs2
                    = add_vec (mword_of_int 4096) (page_base (pt_base t))).
    { rewrite /R6 upd_eq.
      assert (Hx : R5 !!! Regidx Rs2 = (mword_of_int 4096 : mword 64))
        by (rewrite /R5 upd_eq; reflexivity).
      assert (Hy : R5 !!! Regidx Ra0 = page_base (pt_base t)) by (lkp0; exact Ha0).
      rewrite Hx Hy. reflexivity. }
    assert (HR6s3 : R6 !!! Regidx Rs3 = page_base (pt_base t)).
    { rewrite /R6. rewrite upd_ne; [| reg_neq]. rewrite /R5. rewrite upd_ne; [| reg_neq].
      rewrite /R4. rewrite upd_ne; [| reg_neq]. rewrite /R3 upd_eq.
      rewrite add_vec_zero_l. lkp0. exact Ha0. }
    assert (HR6thr : fw_thr mm R6).
    { intros cc Hc H2 H8 H9 H18 H19. thr_peel. reflexivity. }
    (* --- +0x16 c.j +0x14 : into the loop at its head --- *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.freewalk + 0x16))
              (sign_extend' 21 (concat_vec (mword_of_int 10 : mword 11) ('b"0")))
              R6 (K - 6) b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi16").
    iIntros (CID12 Hs12). iNext. iIntros "Hcg Hpc".
    assert (Htgt2a : add_vec (mword_of_int (KernelSyms.freewalk + 0x16) : mword 64)
              (sign_extend' 64 (sign_extend' 21
                 (concat_vec (mword_of_int 10 : mword 11) ('b"0"))))
            = mword_of_int (KernelSyms.freewalk + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt2a) in "Hpc".
    (* [Hcont] entered at [CID0]; the twelve plain prologue instructions
       have each moved it, so the loop's own entry hart [CID12] wants it
       re-anchored -- the sole [wp_next_shift] this lemma needs, since
       both callees below take a FRESH inline continuation ([-]). *)
    assert (Hshift12 : b = false \/ p = zero_reg -> (CID12 : CPU) = (CID0 : CPU)) by wp_next_chain.
    iDestruct (wp_next_shift Hshift12 with "Hcont") as "Hcont".
    (* [wp_freewalk_sconf_body] (SpecFreewalk.v) now carries the caller's
       real held-lock set [lks] and the "kmem" bound [Hbelow] on it; both
       [fw_loop] and [fw_epilogue] take the SAME [lks] and premise (freewalk
       itself acquires no lock, so [lks] is unchanged end to end). *)
    iDestruct (cpu_own_transport CID0 CID12 ilvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (fw_loop (CID:=CID12) lvl REC γa mm t K eb p spr ilvl b lks HK Hilvl (fw_ok_of lvl t Hfree)
              512%nat 0%Z R6 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              HR6sp HR6s1 HR6s2 HR6s3 HR6thr Hbelow
              with "Hcg Hcnt Htext Hpc Hclaim [] Htodo Henv").
    { rewrite /fw_done. rewrite (seqZ_nil 0 0 ltac:(lia)). done. }
    iIntros (CIDj Hsj mj) "(%Hjsp & %Hjs3 & %Hjthr) Hcg Hcnt Hpc Hdone".
    iApply (fw_epilogue (CID0:=CIDj) ilvl γa mm mj K sp0 (pt_base t) eb p b lks
              ltac:(lia) Hilvl Hspm Hjsp Hjs3 Hjthr
              Hbelow
              with "Hcg Hcnt Htext Hpc [Hdone] Henv Hk1 Hk2 Hk3 Hk4 Hk5 [Hk6]").
    { iApply (pt_slots_kfree_pre (pt_base t) Hpv with "Hkmapb Hdone"). }
    { iExists u6. iExact "Hk6". }
    iIntros (CIDy Hsy mf) "Hcg Hcnt Hpc %Hcs".
    iSpecialize ("Hcont" $! CIDy with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! mf with "Hcg Hcnt Hpc [%]").
    exact Hcs.
  Qed.

  (* ================================================================== *)
  (*  §6  The induction on the level.                                     *)
  (* ================================================================== *)
  Local Lemma fw_go_aux (n : nat) : forall lvl : nat, (lvl <= n)%nat -> fw_rec lvl.
  Proof.
    induction n as [| n IHn]; intros lvl Hle.
    - apply fw_body. intros l Hl. exfalso. lia.
    - apply fw_body. intros l Hl. apply IHn. lia.
  Qed.

  Lemma wp_freewalk_sconf `{CID : CpuId} (γa : gname) (mm : regfile)
      (t : ptree) (lvl : nat) (K : nat) (eb : bool) (p : mword 64)
      (ilvl : nat) (b : bool) (lks : gset string)
    : wp_freewalk_sconf_body kt γa mm t lvl K eb p ilvl b lks.
  Proof. exact (fw_go_aux lvl lvl (Nat.le_refl lvl) CID γa mm t K eb p ilvl b lks). Qed.

End ProofFreewalk.

End FreewalkProof.
