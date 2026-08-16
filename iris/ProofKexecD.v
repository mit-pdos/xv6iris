(* ProofKexecD.v -- PHASE D of kexec: THE COMMIT (+0x2a6 .. +0x31a).

   Entry is [ProofKexecSeam.kxc_at_2a6], phase C's exit: both copyouts are
   done, every [bad:] entry is behind us, and the state already ASSERTS the
   two conditions [SpecKexec.kexec_ok]'s success arm quotes.  What is left is
   the commit itself --

     p->trapframe->a1  = sp                    +0x2a6 .. +0x2aa
     last = the byte after the final '/' in path
                                               +0x2ae .. +0x2d0
     safestrcpy(p->name, last, PNAMELEN)       +0x2d2 .. +0x2dc
     p->pagetable = the new table ; p->sz = sz1
                                               +0x2e0 .. +0x2e8
     p->trapframe->epc = elf.entry ; p->trapframe->sp = sp
                                               +0x2ec .. +0x2fa
     proc_freepagetable(the OLD table, oldsz)  +0x2fe .. +0x300
     return argc                               +0x304 .. +0x31a -> +0x72

   -- and it has no failure arm at all: past +0x2a2 the function cannot fail.

   THE NAME SCAN IS THE ONLY LOOP, AND ITS INVARIANT IS DELIBERATELY WEAK.
   [kexec_ok] asks only for an EXISTENTIAL name of the right length, so the
   loop never has to model "the byte after the final '/'": all it must carry
   is that the pointer it leaves in the frame is INSIDE the path buffer.
   That is what makes [kxd_name_loop] a dozen lines of invariant rather than
   a string-search specification.

   A MINIMAL FUNCTOR: phase D calls exactly two functions, so it takes two
   modules.  Its [bad:]-free-ness is why it needs neither the FS fabric nor
   [ProofKexecTail]'s [-1] tail. *)
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
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import KptTree.
Require Import CpuOwn.
Require Import WpLock.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import FsCrash.
Require Import InodeRegion.
Require Import ByteBuf.
Require Import ElfEnc.
Require Import PageGeom.
Require Import ProcGeom.
Require Import TrampPt.
Require Import ProcInv.
Require Import DiskPtsto.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import InodeInv.
Require Import IrefSlots.
Require Import KallocInv.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import IrefSlots.
Require Import DiskInv.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import UmCovered.
Require Import FileInvDefs.
Require Import SpecKexec.
Require Import SpecProcFreepagetable.
Require Import SpecSafestrcpy.
Require Import ProofKexecParts.
(* the frame vocabulary the epilogue reloads through ([kxc_slot5_sp] ..
   [kxc_slot13_sp], [kxc_stack_of_top5], [kxc_mid_join]) -- the file the
   notes designate as the home for anything two phases share.  No new
   critical path: ProofKexecSeam.v already requires it. *)
Require Import ProofKexecTail.
Require Import ProofKexecSeam.
Require Import ProofKforkParts.
Require Import CodeKexec.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* durable-notes' rule: a goal over [proc_priv] carries [tf_page]'s
   4096-conjunct big-op, and printing one turns a one-line mistake into a
   forty-minute non-answer. *)
Set Printing Depth 40.

Notation KXD := KernelSyms.kexec (only parsing).


(* ===================================================================== *)
(*  THE NAME SCAN, +0x2c0 .. +0x2d0.                                      *)
(*                                                                        *)
(*    for (last = s = path; *s; s++)  if *s is '/' then last = s + 1        *)
(*                                                                        *)
(*  gcc emits it ROTATED: the head is the [bne] against '/' at +0x2c8,     *)
(*  the byte fetch is at the BOTTOM (+0x2c0 .. +0x2c6), and the entry      *)
(*  (+0x2ae .. +0x2be) jumps into the middle.  Three lemmas rather than    *)
(*  one, which is what keeps the '/'-arm's store from being duplicated:    *)
(*                                                                        *)
(*    kxd_scan_tail  +0x2c0 .. +0x2c6 -- step, fetch, NUL test            *)
(*    kxd_name_step  +0x2c8 (.. +0x2d0) -- the '/' test, then the tail     *)
(*    kxd_name_loop  the fuel induction, measure [plen - i]                *)
(*                                                                        *)
(*  ITS OWN SECTION, and NOT inside the functor: the scan calls nothing,   *)
(*  touches no process resource, and its [CID0] must be a LEMMA binder so  *)
(*  the induction can generalise over it (the back edge re-enters at the   *)
(*  hart the previous iteration ended on).                                 *)
(* ===================================================================== *)
Section KexecDName.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId}.

  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs10 := (mword_of_int 26 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  (* ---- the four small facts the scan is built out of ---- *)

  (* [pa_add_S]'s inverse: the [lbu a4,-1(a5)] at +0x2c2 reads the byte the
     [c.addi a5,a5,1] just before it stepped OVER. *)
  Lemma pa_add_pred (p : mword 64) (i : nat) :
    add_vec (pa_add p (S i)) (sign_extend' 64 (mword_of_int 4095 : mword 12))
    = pa_add p i.
  Proof.
    assert (Hm1 : (sign_extend' 64 (mword_of_int 4095 : mword 12) : mword 64)
                  = mword_of_int (-1)) by (apply bv_eq; vm_compute; reflexivity).
    (* [StackBytes.pa_add_S]'s own order -- idemp_r BEFORE idemp_l.  The
       other way round the first rewrite does not fire at all. *)
    rewrite Hm1. unfold pa_add, add_vec_int. apply bv_eq.
    rewrite !add_vec64_unsigned !moi64_unsigned.
    rewrite !bv_wrap_add_idemp_r. rewrite !bv_wrap_add_idemp_l.
    f_equal. lia.
  Qed.

  (* the frame slot [last] lives in, as [sd a5,-528(s0)] addresses it *)
  Lemma kxd_last_slot (sp0 : mword 64) :
    add_vec sp0 (sign_extend' 64 (mword_of_int 3568 : mword 12)) = pa_stk sp0 66.
  Proof.
    assert (Hm : (sign_extend' 64 (mword_of_int 3568 : mword 12) : mword 64)
                 = mword_of_int (-528)) by (apply bv_eq; vm_compute; reflexivity).
    (* [f_equal] closes this outright -- [reflexivity]'s kernel conversion
       computes both literal offsets.  A trailing [vm_compute] would fail
       with "No such goal". *)
    rewrite Hm. unfold pa_stk, add_vec_int. f_equal.
  Qed.

  (* the [lbu] result as a plain unsigned byte (ProofBallocParts' copy) *)
  Lemma kxd_zext8_unsigned (v : mword 8) :
    bv_unsigned (zero_extend' 64 v : mword 64) = bv_unsigned v.
  Proof.
    cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec
         Values.to_word get_word MachineWord.MachineWord.zero_extend].
    rewrite bv_zero_extend_unsigned. reflexivity.
    first [ lia | vm_compute; discriminate | done ].
  Qed.

  (* ...so the NUL test at the word tier IS the byte-level one.  Only ZERO
     needs this: the '/' test never leaves width 64 (the scan compares the
     zero-extended word against 47 and never looks at the byte), which is
     why there is no general width-8 literal bridge here. *)
  Lemma kxd_zext8_zero (v : mword 8) :
    ((zero_extend' 64 v : mword 64) = mword_of_int 0) <-> v = mword_of_int 0.
  Proof.
    split; intro Heq.
    - apply bv_eq.
      apply (f_equal (@bv_unsigned 64)) in Heq.
      rewrite kxd_zext8_unsigned moi64_unsigned in Heq.
      rewrite Heq. vm_compute. reflexivity.
    - rewrite Heq. apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma kxd_neq_vec64 (x y : mword 64) : x <> y -> neq_vec x y = true.
  Proof.
    intro Hxy. unfold neq_vec.
    destruct (eq_vec x y) eqn:E; [| reflexivity].
    apply eq_vec_true_iff in E. contradiction.
  Qed.

  Lemma kxd_eq_vec64_false (x y : mword 64) : x <> y -> eq_vec x y = false.
  Proof.
    intro Hxy. destruct (eq_vec x y) eqn:E; [| reflexivity].
    apply eq_vec_true_iff in E. contradiction.
  Qed.

  (* THE SCAN'S ONE OUTPUT, shared by all three lemmas so the tail's result
     can be handed straight through the '/' test and the induction: another
     turn round the head at [S i], or the scan's end at +0x2d2.  [q'] is
     where [last] ends up, and the ONLY thing promised about it is that it
     is inside the buffer -- which is all [safestrcpy] needs and all
     [kexec_ok] asks for. *)
  Definition kxd_scan_out `{CID0 : CpuId}
      (pj : mword 64) (b : bool) (n : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (sp0 pv : mword 64) (vsp v1 v2 v4 v5 v6 v10 : mword 64)
      (i : nat) : iProp Σ :=
    wp_next b pj (fun (CID : CpuId) =>
      ∀ (M' : regfile) (q' : nat),
        ⌜(q' <= plen)%nat /\
          M' !!! Regidx csp_rs1 = vsp /\ M' !!! Regidx Rs0 = sp0 /\
          M' !!! Regidx Rs1 = v1 /\ M' !!! Regidx Rs2 = v2 /\
          M' !!! Regidx Rs4 = v4 /\ M' !!! Regidx Rs5 = v5 /\
          M' !!! Regidx Rs6 = v6 /\ M' !!! Regidx Rs10 = v10⌝ -∗
        ( ⌜(S i < plen)%nat /\
           M' !!! Regidx Ra3 = (mword_of_int 47 : mword 64) /\
           M' !!! Regidx Ra4 = (zero_extend' 64 (pfun (S i) : mword 8) : mword 64) /\
           M' !!! Regidx Ra5 = pa_add pv (S (S i))⌝
          ∗ pc_is (mword_of_int (KXD + 0x2c8) : mword 64)
        ∨ pc_is (mword_of_int (KXD + 0x2d2) : mword 64) ) -∗
        sie_cap_gpr M' n b pj -∗
        ([∗ list] k ∈ seq 0 (S plen), pa_add pv k ↦ₘ pfun k) -∗
        word_pointsto (pa_stk sp0 66) (DfracOwn 1) (pa_add pv q') -∗
        WP (Loop : expr riscv_lang))%I.

  (* ------------------------------------------------------------------- *)
  (*  +0x2c0 .. +0x2c6 -- STEP, FETCH, NUL TEST.                          *)
  (*  On entry [a5 = path + (S i)] and the byte to read is [pfun (S i)];   *)
  (*  the [c.addi] steps [a5] past it and the [lbu -1(a5)] reads it back.  *)
  (* ------------------------------------------------------------------- *)
  Lemma kxd_scan_tail `{CID0 : CpuId}
      (pj : mword 64) (b : bool) (n : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (sp0 pv : mword 64) (vsp v1 v2 v4 v5 v6 v10 : mword 64)
      (M : regfile) (i q : nat) :
    bb_cstr pfun plen ->
    (i < plen)%nat -> (q <= plen)%nat ->
    M !!! Regidx csp_rs1 = vsp -> M !!! Regidx Rs0 = sp0 ->
    M !!! Regidx Rs1 = v1 -> M !!! Regidx Rs2 = v2 -> M !!! Regidx Rs4 = v4 ->
    M !!! Regidx Rs5 = v5 -> M !!! Regidx Rs6 = v6 -> M !!! Regidx Rs10 = v10 ->
    M !!! Regidx Ra3 = (mword_of_int 47 : mword 64) ->
    M !!! Regidx Ra5 = pa_add pv (S i) ->
    kernel_text -∗
    pc_is (mword_of_int (KXD + 0x2c0) : mword 64) -∗
    sie_cap_gpr M n b pj -∗
    ([∗ list] k ∈ seq 0 (S plen), pa_add pv k ↦ₘ pfun k) -∗
    word_pointsto (pa_stk sp0 66) (DfracOwn 1) (pa_add pv q) -∗
    kxd_scan_out pj b n plen pfun sp0 pv vsp v1 v2 v4 v5 v6 v10 i -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros [Hnonul Hnul] Hiplen Hq Hsp Hs0 Hv1 Hv2 Hv4 Hv5 Hv6 Hv10 Ha3 Ha5.
    iIntros "#Htext Hpc Hcg Hpath Hlast Hout".
    iPoseProof (kxc_2c0 with "Htext") as "Hi2c0".
    iPoseProof (kxc_2c2 with "Htext") as "Hi2c2".
    iPoseProof (kxc_2c6 with "Htext") as "Hi2c6".
    (* ---- +0x2c0: c.addi a5,a5,1 ---- *)
    iApply (wp_caddi_s_sconf (mword_of_int (KXD + 0x2c0)) Ra5
              (mword_of_int 1 : mword 6) M n b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi2c0").
    iIntros (CID1 Hs1) "Hcg Hpc".
    pose (N1 := <[Regidx Ra5 := regval_into_reg
                   (add_vec (rget M Ra5)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> M).
    assert (Hse1 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)) : mword 64)
                   = mword_of_int 1) by (apply bv_eq; vm_compute; reflexivity).
    assert (HN1a5 : N1 !!! Regidx Ra5 = pa_add pv (S (S i))).
    { rewrite /N1 upd_eq (rget_ne M Ra5 ltac:(nz)) Ha5 Hse1. apply pa_add_S. }
    assert (HN1sp : N1 !!! Regidx csp_rs1 = vsp)
      by (rewrite /N1 upd_ne; [exact Hsp | nz]).
    assert (HN1s0 : N1 !!! Regidx Rs0 = sp0)
      by (rewrite /N1 upd_ne; [exact Hs0 | nz]).
    assert (HN1s1 : N1 !!! Regidx Rs1 = v1)
      by (rewrite /N1 upd_ne; [exact Hv1 | nz]).
    assert (HN1s2 : N1 !!! Regidx Rs2 = v2)
      by (rewrite /N1 upd_ne; [exact Hv2 | nz]).
    assert (HN1s4 : N1 !!! Regidx Rs4 = v4)
      by (rewrite /N1 upd_ne; [exact Hv4 | nz]).
    assert (HN1s5 : N1 !!! Regidx Rs5 = v5)
      by (rewrite /N1 upd_ne; [exact Hv5 | nz]).
    assert (HN1s6 : N1 !!! Regidx Rs6 = v6)
      by (rewrite /N1 upd_ne; [exact Hv6 | nz]).
    assert (HN1s10 : N1 !!! Regidx Rs10 = v10)
      by (rewrite /N1 upd_ne; [exact Hv10 | nz]).
    assert (HN1a3 : N1 !!! Regidx Ra3 = (mword_of_int 47 : mword 64))
      by (rewrite /N1 upd_ne; [exact Ha3 | nz]).
    assert (Hpp2c2 : add_vec_int (mword_of_int (KXD + 0x2c0) : mword 64) 2
                     = mword_of_int (KXD + 0x2c2)) by pcw.
    iEval (rewrite Hpp2c2) in "Hpc".
    (* ---- +0x2c2: lbu a4,-1(a5) -- the byte at index [S i] ---- *)
    assert (Hlk : seq 0 (S plen) !! (S i) = Some (S i))
      by (rewrite (lookup_seq_lt 0 (S plen) (S i) ltac:(lia)); f_equal; lia).
    iDestruct (big_sepL_lookup_acc _ _ (S i) (S i) Hlk with "Hpath")
      as "[Hbyte Hpathback]".
    assert (Hloadaddr : add_vec (N1 !!! Regidx Ra5)
                          (sign_extend' 64 (mword_of_int 4095 : mword 12))
                        = pa_add pv (S i))
      by (rewrite HN1a5; apply pa_add_pred).
    iEval (rewrite -Hloadaddr) in "Hbyte".
    iApply (wp_lbu_s_sconf (mword_of_int (KXD + 0x2c2)) Ra4 Ra5
              (mword_of_int 4095 : mword 12) N1 n (pfun (S i)) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2c2 Hbyte").
    iIntros (CID2 Hs2) "Hcg Hpc Hbyte".
    iEval (rewrite Hloadaddr) in "Hbyte".
    iDestruct ("Hpathback" with "Hbyte") as "Hpath".
    pose (N2 := <[Regidx Ra4 := regval_into_reg
                   (zero_extend' 64 (pfun (S i) : mword 8) : mword 64)]> N1).
    assert (HN2a4 : N2 !!! Regidx Ra4 = (zero_extend' 64 (pfun (S i) : mword 8) : mword 64))
      by (rewrite /N2; apply upd_eq).
    assert (HN2a5 : N2 !!! Regidx Ra5 = pa_add pv (S (S i)))
      by (rewrite /N2 upd_ne; [exact HN1a5 | nz]).
    assert (HN2a3 : N2 !!! Regidx Ra3 = (mword_of_int 47 : mword 64))
      by (rewrite /N2 upd_ne; [exact HN1a3 | nz]).
    assert (HN2sp : N2 !!! Regidx csp_rs1 = vsp)
      by (rewrite /N2 upd_ne; [exact HN1sp | nz]).
    assert (HN2s0 : N2 !!! Regidx Rs0 = sp0)
      by (rewrite /N2 upd_ne; [exact HN1s0 | nz]).
    assert (HN2s1 : N2 !!! Regidx Rs1 = v1)
      by (rewrite /N2 upd_ne; [exact HN1s1 | nz]).
    assert (HN2s2 : N2 !!! Regidx Rs2 = v2)
      by (rewrite /N2 upd_ne; [exact HN1s2 | nz]).
    assert (HN2s4 : N2 !!! Regidx Rs4 = v4)
      by (rewrite /N2 upd_ne; [exact HN1s4 | nz]).
    assert (HN2s5 : N2 !!! Regidx Rs5 = v5)
      by (rewrite /N2 upd_ne; [exact HN1s5 | nz]).
    assert (HN2s6 : N2 !!! Regidx Rs6 = v6)
      by (rewrite /N2 upd_ne; [exact HN1s6 | nz]).
    assert (HN2s10 : N2 !!! Regidx Rs10 = v10)
      by (rewrite /N2 upd_ne; [exact HN1s10 | nz]).
    assert (Hpp2c6 : add_vec_int (mword_of_int (KXD + 0x2c2) : mword 64) 4
                     = mword_of_int (KXD + 0x2c6)) by pcw.
    iEval (rewrite Hpp2c6) in "Hpc".
    (* ---- +0x2c6: c.beqz a4,+0x2d2 -- the string's own end ---- *)
    assert (Hcreg : creg2reg_idx (Cregidx (mword_of_int 6)) = Regidx Ra4)
      by (vm_compute; reflexivity).
    assert (Htgt2d2 : add_vec (mword_of_int (KXD + 0x2c6) : mword 64)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 6 : mword 8) ('b"0"))))
                      = mword_of_int (KXD + 0x2d2)) by pcw.
    destruct (decide (pfun (S i) = (mword_of_int 0 : mword 8))) as [Hz | Hnz].
    - (* ==== NUL: the scan is over ==== *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KXD + 0x2c6))
                (mword_of_int 6 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                N2 n b Hcreg ltac:(nz)
                ltac:(rewrite (rget_ne N2 Ra4 ltac:(nz)) HN2a4 Hz;
                      vm_compute; reflexivity)
                ltac:(rewrite Htgt2d2; vm_compute; reflexivity)
                with "Hcg Hpc Hi2c6").
      iIntros (CID3 Hs3). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt2d2) in "Hpc".
      iEval (rewrite /kxd_scan_out) in "Hout".
      iSpecialize ("Hout" $! CID3 with "[%]"); [wp_next_chain |].
      iApply ("Hout" $! N2 q with "[%] [Hpc] Hcg Hpath Hlast").
      { split_and!; [exact Hq | exact HN2sp | exact HN2s0 | exact HN2s1
                    | exact HN2s2 | exact HN2s4 | exact HN2s5 | exact HN2s6
                    | exact HN2s10]. }
      { iRight. iExact "Hpc". }
    - (* ==== not a NUL: on to the '/' test at +0x2c8 ==== *)
      assert (HSiplen : (S i < plen)%nat).
      { destruct (Nat.lt_ge_cases (S i) plen) as [Hlt | Hge]; [exact Hlt |].
        exfalso. apply Hnz.
        assert (HSieq : S i = plen) by lia. rewrite HSieq. exact Hnul. }
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KXD + 0x2c6))
                (mword_of_int 6 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                N2 n b Hcreg ltac:(nz)
                ltac:(rewrite (rget_ne N2 Ra4 ltac:(nz)) HN2a4;
                      apply kxd_eq_vec64_false;
                      intro Heq; apply Hnz;
                      apply (proj1 (kxd_zext8_zero (pfun (S i))));
                      rewrite Heq; apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi2c6").
      iIntros (CID3 Hs3) "Hcg Hpc".
      assert (Hpp2c8 : add_vec_int (mword_of_int (KXD + 0x2c6) : mword 64) 2
                       = mword_of_int (KXD + 0x2c8)) by pcw.
      iEval (rewrite Hpp2c8) in "Hpc".
      iEval (rewrite /kxd_scan_out) in "Hout".
      iSpecialize ("Hout" $! CID3 with "[%]"); [wp_next_chain |].
      iApply ("Hout" $! N2 q with "[%] [Hpc] Hcg Hpath Hlast").
      { split_and!; [exact Hq | exact HN2sp | exact HN2s0 | exact HN2s1
                    | exact HN2s2 | exact HN2s4 | exact HN2s5 | exact HN2s6
                    | exact HN2s10]. }
      { iLeft. iSplitR; [| iExact "Hpc"].
        iPureIntro. split_and!;
          [exact HSiplen | exact HN2a3 | exact HN2a4 | exact HN2a5]. }
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  +0x2c8 (.. +0x2d0) -- THE '/' TEST, then the tail.                  *)
  (*  The only thing the two arms differ in is [q], so the fetch block is  *)
  (*  called rather than written twice.                                   *)
  (* ------------------------------------------------------------------- *)
  Lemma kxd_name_step `{CID0 : CpuId}
      (pj : mword 64) (b : bool) (n : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (sp0 pv : mword 64) (vsp v1 v2 v4 v5 v6 v10 : mword 64)
      (M : regfile) (i q : nat) :
    bb_cstr pfun plen ->
    (i < plen)%nat -> (q <= plen)%nat ->
    M !!! Regidx csp_rs1 = vsp -> M !!! Regidx Rs0 = sp0 ->
    M !!! Regidx Rs1 = v1 -> M !!! Regidx Rs2 = v2 -> M !!! Regidx Rs4 = v4 ->
    M !!! Regidx Rs5 = v5 -> M !!! Regidx Rs6 = v6 -> M !!! Regidx Rs10 = v10 ->
    M !!! Regidx Ra3 = (mword_of_int 47 : mword 64) ->
    M !!! Regidx Ra4 = (zero_extend' 64 (pfun i : mword 8) : mword 64) ->
    M !!! Regidx Ra5 = pa_add pv (S i) ->
    kernel_text -∗
    pc_is (mword_of_int (KXD + 0x2c8) : mword 64) -∗
    sie_cap_gpr M n b pj -∗
    ([∗ list] k ∈ seq 0 (S plen), pa_add pv k ↦ₘ pfun k) -∗
    word_pointsto (pa_stk sp0 66) (DfracOwn 1) (pa_add pv q) -∗
    kxd_scan_out pj b n plen pfun sp0 pv vsp v1 v2 v4 v5 v6 v10 i -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hcstr Hiplen Hq Hsp Hs0 Hv1 Hv2 Hv4 Hv5 Hv6 Hv10 Ha3 Ha4 Ha5.
    iIntros "#Htext Hpc Hcg Hpath Hlast Hout".
    iPoseProof (kxc_2c8 with "Htext") as "Hi2c8".
    iPoseProof (kxc_2cc with "Htext") as "Hi2cc".
    iPoseProof (kxc_2d0 with "Htext") as "Hi2d0".
    assert (Htgt2c0 : add_vec (mword_of_int (KXD + 0x2c8) : mword 64)
                        (sign_extend' 64 (mword_of_int 8184 : mword 13))
                      = mword_of_int (KXD + 0x2c0)) by pcw.
    destruct (decide ((zero_extend' 64 (pfun i : mword 8) : mword 64) = mword_of_int 47))
      as [Hslash | Hnoslash].
    - (* ==== a '/': record [last = s + 1], then the fetch block ==== *)
      iApply (wp_bne_fall_s_sconf (mword_of_int (KXD + 0x2c8))
                (mword_of_int 8184 : mword 13) Ra3 Ra4 M n b
                ltac:(nz) ltac:(nz)
                ltac:(rewrite (rget_ne M Ra4 ltac:(nz)) (rget_ne M Ra3 ltac:(nz))
                              Ha4 Ha3 Hslash;
                      vm_compute; reflexivity)
                with "Hcg Hpc Hi2c8").
      iIntros (CID1 Hs1) "Hcg Hpc".
      assert (Hpp2cc : add_vec_int (mword_of_int (KXD + 0x2c8) : mword 64) 4
                       = mword_of_int (KXD + 0x2cc)) by pcw.
      iEval (rewrite Hpp2cc) in "Hpc".
      (* ---- +0x2cc: sd a5,-528(s0) ---- *)
      assert (Hslotaddr : add_vec (M !!! Regidx Rs0)
                            (sign_extend' 64 (mword_of_int 3568 : mword 12))
                          = pa_stk sp0 66)
        by (rewrite Hs0; apply kxd_last_slot).
      iEval (rewrite -Hslotaddr) in "Hlast".
      iApply (wp_sd_s_sconf (mword_of_int (KXD + 0x2cc)) Ra5 Rs0
                (mword_of_int 3568 : mword 12) M n (pa_add pv q) b
                with "Hcg Hpc Hi2cc Hlast").
      iIntros (CID2 Hs2) "Hcg Hpc Hlast".
      iEval (rewrite Hslotaddr) in "Hlast".
      (* the store's [storeval] is [rget m rs2] at the ENTRY hart -- the one
         active when [wp_sd_s_sconf] was applied ([CID1], bound by the [bne]
         just above), not the continuation's [CID2].  kexec.md's fourth
         hart-mismatch class. *)
      iEval (rewrite (rget_ne (CID := CID1) M Ra5 ltac:(nz)) Ha5) in "Hlast".
      assert (Hpp2d0 : add_vec_int (mword_of_int (KXD + 0x2cc) : mword 64) 4
                       = mword_of_int (KXD + 0x2d0)) by pcw.
      iEval (rewrite Hpp2d0) in "Hpc".
      (* ---- +0x2d0: c.j +0x2c0 ---- *)
      assert (Htgt2d0 : add_vec (mword_of_int (KXD + 0x2d0) : mword 64)
                          (sign_extend' 64 (sign_extend' 21
                             (concat_vec (mword_of_int 2040 : mword 11) ('b"0"))))
                        = mword_of_int (KXD + 0x2c0)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (KXD + 0x2d0))
                (sign_extend' 21 (concat_vec (mword_of_int 2040 : mword 11) ('b"0")))
                M n b ltac:(rewrite Htgt2d0; vm_compute; reflexivity)
                with "Hcg Hpc Hi2d0").
      iIntros (CID3 Hs3). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt2d0) in "Hpc".
      iApply (kxd_scan_tail (CID0 := CID3) pj b n plen pfun sp0 pv
                vsp v1 v2 v4 v5 v6 v10 M i (S i)
                Hcstr Hiplen ltac:(lia) Hsp Hs0 Hv1 Hv2 Hv4 Hv5 Hv6 Hv10 Ha3 Ha5
                with "Htext Hpc Hcg Hpath Hlast [Hout]").
      rewrite /kxd_scan_out.
      assert (Hcr3 : b = false \/ pj = zero_reg -> (CID3 : CPU) = (CID0 : CPU))
        by wp_next_chain.
      iApply (wp_next_retarget CID0 CID3 b pj _ Hcr3 with "Hout").
    - (* ==== not a '/': straight to the fetch block, [last] unmoved ==== *)
      iApply (wp_bne_taken_s_sconf (mword_of_int (KXD + 0x2c8))
                (mword_of_int 8184 : mword 13) Ra3 Ra4 M n b
                ltac:(nz) ltac:(nz)
                ltac:(rewrite (rget_ne M Ra4 ltac:(nz)) (rget_ne M Ra3 ltac:(nz))
                              Ha4 Ha3; apply kxd_neq_vec64; exact Hnoslash)
                ltac:(rewrite Htgt2c0; vm_compute; reflexivity)
                with "Hcg Hpc Hi2c8").
      iIntros (CID1 Hs1). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt2c0) in "Hpc".
      iApply (kxd_scan_tail (CID0 := CID1) pj b n plen pfun sp0 pv
                vsp v1 v2 v4 v5 v6 v10 M i q
                Hcstr Hiplen Hq Hsp Hs0 Hv1 Hv2 Hv4 Hv5 Hv6 Hv10 Ha3 Ha5
                with "Htext Hpc Hcg Hpath Hlast [Hout]").
      rewrite /kxd_scan_out.
      assert (Hcr1 : b = false \/ pj = zero_reg -> (CID1 : CPU) = (CID0 : CPU))
        by wp_next_chain.
      iApply (wp_next_retarget CID0 CID1 b pj _ Hcr1 with "Hout").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE SCAN, ITERATED.  Measure [plen - i]; the [W = 0] case is refuted *)
  (*  by the head's own [i < plen], carried as a PREMISE for exactly the   *)
  (*  reason ProofKexecC.kxc_argv_loop carries its own.                    *)
  (* ------------------------------------------------------------------- *)
  Lemma kxd_name_loop `{CID0 : CpuId}
      (pj : mword 64) (b : bool) (n : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (sp0 pv : mword 64) (vsp v1 v2 v4 v5 v6 v10 : mword 64) :
    bb_cstr pfun plen ->
    forall (W : nat) (M : regfile) (i q : nat),
    (plen - i <= W)%nat ->
    (i < plen)%nat -> (q <= plen)%nat ->
    M !!! Regidx csp_rs1 = vsp -> M !!! Regidx Rs0 = sp0 ->
    M !!! Regidx Rs1 = v1 -> M !!! Regidx Rs2 = v2 -> M !!! Regidx Rs4 = v4 ->
    M !!! Regidx Rs5 = v5 -> M !!! Regidx Rs6 = v6 -> M !!! Regidx Rs10 = v10 ->
    M !!! Regidx Ra3 = (mword_of_int 47 : mword 64) ->
    M !!! Regidx Ra4 = (zero_extend' 64 (pfun i : mword 8) : mword 64) ->
    M !!! Regidx Ra5 = pa_add pv (S i) ->
    kernel_text -∗
    pc_is (mword_of_int (KXD + 0x2c8) : mword 64) -∗
    sie_cap_gpr M n b pj -∗
    ([∗ list] k ∈ seq 0 (S plen), pa_add pv k ↦ₘ pfun k) -∗
    word_pointsto (pa_stk sp0 66) (DfracOwn 1) (pa_add pv q) -∗
    wp_next b pj (fun (CID : CpuId) =>
      ∀ (M' : regfile) (q' : nat),
        ⌜(q' <= plen)%nat /\
          M' !!! Regidx csp_rs1 = vsp /\ M' !!! Regidx Rs0 = sp0 /\
          M' !!! Regidx Rs1 = v1 /\ M' !!! Regidx Rs2 = v2 /\
          M' !!! Regidx Rs4 = v4 /\ M' !!! Regidx Rs5 = v5 /\
          M' !!! Regidx Rs6 = v6 /\ M' !!! Regidx Rs10 = v10⌝ -∗
        pc_is (mword_of_int (KXD + 0x2d2) : mword 64) -∗
        sie_cap_gpr M' n b pj -∗
        ([∗ list] k ∈ seq 0 (S plen), pa_add pv k ↦ₘ pfun k) -∗
        word_pointsto (pa_stk sp0 66) (DfracOwn 1) (pa_add pv q') -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hcstr W. revert CID0.
    induction W as [| W IH]; intros CID0 M i q Hfuel Hiplen Hq
      Hsp Hs0 Hv1 Hv2 Hv4 Hv5 Hv6 Hv10 Ha3 Ha4 Ha5.
    { exfalso. lia. }
    iIntros "#Htext Hpc Hcg Hpath Hlast Hout".
    iApply (kxd_name_step (CID0 := CID0) pj b n plen pfun sp0 pv
              vsp v1 v2 v4 v5 v6 v10 M i q
              Hcstr Hiplen Hq Hsp Hs0 Hv1 Hv2 Hv4 Hv5 Hv6 Hv10 Ha3 Ha4 Ha5
              with "Htext Hpc Hcg Hpath Hlast [Hout]").
    rewrite /kxd_scan_out.
    iIntros (CIDn Hsn M' q') "%Hpres [[%Hnext Hpc] | Hpc] Hcg Hpath Hlast".
    - (* the back edge, at [S i] *)
      destruct Hnext as (HSi & Ha3' & Ha4' & Ha5').
      destruct Hpres as (Hq' & Hsp' & Hs0' & Hv1' & Hv2' & Hv4' & Hv5' & Hv6' & Hv10').
      assert (Hcr : b = false \/ pj = zero_reg -> (CIDn : CPU) = (CID0 : CPU))
        by wp_next_chain.
      iDestruct (wp_next_retarget CID0 CIDn b pj _ Hcr with "Hout") as "Hout".
      iApply (IH CIDn M' (S i) q' ltac:(lia) HSi Hq'
                Hsp' Hs0' Hv1' Hv2' Hv4' Hv5' Hv6' Hv10' Ha3' Ha4' Ha5'
                with "Htext Hpc Hcg Hpath Hlast Hout").
    - (* the scan is over *)
      iSpecialize ("Hout" $! CIDn with "[%]"); [wp_next_chain |].
      iApply ("Hout" $! M' q' with "[%] Hpc Hcg Hpath Hlast").
      exact Hpres.
  Qed.

End KexecDName.

(* ===================================================================== *)
(*  PHASE D PROPER.                                                       *)
(* ===================================================================== *)
Module KexecDProof (PFP : PROC_FREEPAGETABLE) (SS : SAFESTRCPY).

Section KexecDCommit.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

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
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  (* ---- the small address/shape facts the commit block needs ---- *)

  (* every trapframe word this block writes, at one lemma: the [sd]'s own
     12-bit displacement against [tf_pa]'s [8*i] indexing.  Concludes in
     [tf_pa], not [a_tf_word]: every downstream consumer (tf_page_word_mem
     and friends) is physical-native now, so stating it that way makes every
     call site below line up with no further bridging. *)
  Lemma kxd_tf_addr (tfp : mword 44) (z : Z) (i : nat) :
    (i < 512)%nat ->
    (sign_extend' 64 (mword_of_int z : mword 12) : mword 64)
      = mword_of_int (8 * Z.of_nat i) ->
    add_vec (page_base tfp) (sign_extend' 64 (mword_of_int z : mword 12))
    = tf_pa tfp (8 * Z.of_nat i).
  Proof.
    intros Hi Hz. rewrite (tf_pa_eq_pa_add8 tfp i Hi).
    rewrite Hz /pa_add /add_vec_int.
    f_equal. f_equal. lia.
  Qed.

  (* the trapframe page's own length, read WITHOUT consuming it -- the
     [ws !! i = Some w] side conditions of [tf_page_word_upd] all come from
     it, and the block writes three different words. *)
  Lemma kxd_tf_len (tfp : mword 44) (ws : list (mword 64)) :
    tf_page tfp ws ⊢ ⌜length ws = TFWORDS⌝ ∗ tf_page tfp ws.
  Proof.
    rewrite /tf_page. iIntros "(%Hl & A & B)".
    iSplitR; [done |]. iSplitR; [done |].
    iSplitL "A"; [iExact "A" | iExact "B"].
  Qed.

  (* an EIGHT-byte window into a named byte run -- [ProofKexecSeam.kxc_win4]'s
     width-8 sibling, which +0x2f0's [ld a4,-408(s0)] (elf.entry, byte 24 of
     the header) needs and nothing before phase D did. *)
  Lemma kxd_win8 (a : mword 64) (f : nat -> bv 8) (o r n : nat) :
    (o + 8 + r)%nat = n ->
    is_aligned_paddr (Physaddr (pa_add a o)) 8 = true ->
    ([∗ list] j ∈ seq 0 n, pa_add a j ↦ₘ f j) ⊢
    (pa_add a o ↦₈ (Z_to_bv 64 (le_at f o 8) : mword 64)) ∗
    ((pa_add a o ↦₈ (Z_to_bv 64 (le_at f o 8) : mword 64)) -∗
       [∗ list] j ∈ seq 0 n, pa_add a j ↦ₘ f j).
  Proof.
    intros Hn Hal.
    rewrite (bb_split3 a o 8 r n f Hn).
    iIntros "(Hpre & Hmid & Hsuf)".
    iSplitL "Hmid".
    { iApply (word_pointsto_intro _ _ _ Hal).
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

  (* the three successive [upd_*]s the block's three accessor closes produce,
     composed into the contract's own one-shot [upd_exec]. *)
  Lemma kxd_upd_compose (V : pprivate) (ws1 ws3 : list (mword 64))
      (ns : list (bv 8)) (P' : uptd) (szv : mword 64) :
    upd_sz (upd_pt (upd_name (upd_tf V ws1) ns) P' ws3) szv
    = upd_exec V szv P' ws3 ns.
  Proof. by destruct V. Qed.

  Lemma kxd_priv_exec (gf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) (ws1 ws3 : list (mword 64)) (ns : list (bv 8))
      (P' : uptd) (szv : mword 64) :
    proc_priv gf pa pid
      (upd_sz (upd_pt (upd_name (upd_tf V ws1) ns) P' ws3) szv) -∗
    proc_priv gf pa pid (upd_exec V szv P' ws3 ns).
  Proof. rewrite kxd_upd_compose. iIntros "H". iExact "H". Qed.

  (* the two trapframe words the commit writes SECOND and THIRD are at
     distinct indices, so the order the block happens to write them in is
     not the order [SpecKexec.kxc_tf] quotes. *)
  Lemma kxd_tf_swap (ws : list (mword 64)) (a b : mword 64) :
    <[kxc_tf_sp_idx := b]> (<[tf_epc_idx := a]> ws)
    = <[tf_epc_idx := a]> (<[kxc_tf_sp_idx := b]> ws).
  Proof. apply list_insert_commute. unfold kxc_tf_sp_idx, tf_epc_idx. lia. Qed.

  (* the two accessor closes that touch only the trapframe words, folded to
     the one-field update [upd_tf] the commit block reasons over. *)
  Lemma kxd_close_tf (V : pprivate) (ws : list (mword 64)) :
    upd_sz (upd_pt V (pv_upt V) ws) (pv_sz V) = upd_tf V ws.
  Proof. by destruct V. Qed.

  (* ...at the RESOURCE, because [iEval (rewrite ...)] on a [pprivate]
     equation inside [proc_priv] finds no relation to rewrite. *)
  Lemma kxd_priv_close_tf (gf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) (ws : list (mword 64)) :
    proc_priv gf pa pid (upd_sz (upd_pt V (pv_upt V) ws) (pv_sz V)) -∗
    proc_priv gf pa pid (upd_tf V ws).
  Proof. rewrite kxd_close_tf. iIntros "H". iExact "H". Qed.

  (* THE EXIT'S OWN [kexec_ok], assembled.  Stated separately because the
     commit block reaches it from a register file it has just reloaded nine
     registers into, and mixing the arithmetic in there is what makes such a
     block unreadable. *)
  Lemma kxd_kexec_ok (V : pprivate) (na : nat) (alen : nat -> nat)
      (P : uptd) (entry sz1 : mword 64) (ns : list (bv 8)) (r : mword 64) :
    r = (mword_of_int (Z.of_nat na) : mword 64) ->
    (na < MAXARG)%nat ->
    kxc_stack_ok (uint sz1) (uint sz1 - 4096) alen na ->
    ud_tfp P = ud_tfp (pv_upt V) ->
    length ns = PNAMELEN ->
    (uint sz1 - 4096
       <= uint (mword_of_int (kxc_sp_final (uint sz1) alen na) : mword 64))%Z ->
    (uint (mword_of_int (kxc_sp_final (uint sz1) alen na) : mword 64)
       <= uint sz1)%Z ->
    kexec_ok V
      (upd_exec V sz1 P
         (<[kxc_tf_sp_idx
            := (mword_of_int (kxc_sp_final (uint sz1) alen na) : mword 64)]>
            (<[tf_epc_idx := entry]>
               (<[tf_arg_idx 1
                  := (mword_of_int (kxc_sp_final (uint sz1) alen na) : mword 64)]>
                  (pv_tf V))))
         ns)
      r entry (mword_of_int (kxc_sp_final (uint sz1) alen na)) sz1 na alen.
  Proof.
    intros Hr Hna Hstk Htfp Hns Hlo Hhi. right.
    rewrite kxd_tf_swap.
    split_and!; try reflexivity; try assumption; try (unfold MAXARG in *; lia).
  Qed.


  (* ------------------------------------------------------------------- *)
  (*  PHASE D'S RESOURCES.  [ProofKexecSeam.kxc_d_res] with the frame's    *)
  (*  slot 66 SPLIT OUT of the path base: the name scan writes [last] into  *)
  (*  that slot while the path buffer it points into stays where it is, so  *)
  (*  the two cannot share one parameter the way [kxc_d_res] has them do.   *)
  (*  [kxd_res ... pv] IS [kxc_d_res ...]; the scan's exit is at some       *)
  (*  [pa_add pv q'] instead.                                              *)
  (* ------------------------------------------------------------------- *)
  Definition kxd_res
      (jp : nat) (bn : bio_names) (gfs : fs_names) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (size : Z) (used2 : gset Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (Vc : pprivate) (dqb dqs dqa : dfrac)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (c : nat) (last : mword 64) : iProp Σ :=
    (iref_slots 2 ∗
     sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) ∗
     sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) ∗
     bitmap_res gfs bmapstart cov logstart size used2 ∗
     bslots bn 3 ∗
     proc_pt P ∗
     proc_priv gf (proc_addr jp) pidv Vc ∗
     ([∗ list] k ∈ seq 0 (S plen), pa_add pv k ↦ₘ pfun k) ∗
     ([∗ list] k ∈ seq 0 (S na), pa_add av (8 * k) ↦₈{dqa} avf k) ∗
     ([∗ list] k ∈ seq 0 na,
        [∗ list] j ∈ seq 0 (aslen k), pa_add (avf k) j ↦ₘ afun k j) ∗
     ([∗ list] j ∈ seq 0 64, pa_add (pa_stk sp0 54) j ↦ₘ ef j) ∗
     kxc_frameB sp0 ra0 s00 s10 s20 last (pa_add av (8 * c))
                w5 w6 w7 w8 w9 w10 w11 w12 w13 w67)%I.

  (* ---- the four address/shape facts the commit block adds ---- *)

  (* [ld a4,-408(s0)] at +0x2f0 is [elf.entry]: byte 24 of the ELF header,
     which lives at [pa_stk sp0 54]. *)
  Lemma kxd_elf_entry_addr (sp0 : mword 64) :
    add_vec sp0 (sign_extend' 64 (mword_of_int 3688 : mword 12))
    = pa_add (pa_stk sp0 54) 24.
  Proof.
    assert (Hm : (sign_extend' 64 (mword_of_int 3688 : mword 12) : mword 64)
                 = mword_of_int (-408)) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hm. unfold pa_add, pa_stk. rewrite avi_assoc. f_equal.
  Qed.

  (* [addiw a0,s1,0] at +0x304: argc, sign-extended from 32 bits, is argc *)
  Lemma kxd_addiw_id (n : nat) : (Z.of_nat n < 4096)%Z ->
    sign_extend' 64 (subrange_vec_dec
       (add_vec (mword_of_int (Z.of_nat n) : mword 64)
                (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0)
    = (mword_of_int (Z.of_nat n) : mword 64).
  Proof.
    intro Hn.
    assert (E : (subrange_vec_dec
                   (add_vec (mword_of_int (Z.of_nat n) : mword 64)
                      (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0 : mword 32)
                = (mword_of_int (Z.of_nat n) : mword 32)).
    { apply bv_eq. rewrite subrange_31_0_unsigned add_vec64_unsigned moi64_unsigned.
      assert (H0c : bv_unsigned (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                    = 0%Z) by (vm_compute; reflexivity).
      rewrite H0c moi32_unsigned. unfold bv_wrap.
      rewrite (Z.mod_small (Z.of_nat n) 18446744073709551616); [| lia].
      rewrite Z.add_0_r.
      rewrite (Z.mod_small (Z.of_nat n) 18446744073709551616); [| lia].
      reflexivity. }
    rewrite E. apply bv_eq.
    assert (Hrange : (0 <= Z.of_nat n < 2 ^ 31)%Z)
      by (change (2 ^ 31)%Z with 2147483648%Z; lia).
    rewrite (sext64_moi32_unsigned (Z.of_nat n) Hrange) moi64_unsigned.
    unfold bv_wrap. symmetry. apply Z.mod_small.
    change (bv_modulus 64) with 18446744073709551616%Z. lia.
  Qed.

  (* [ProofKforkB4]'s naming function, copied rather than required: that file
     is a 900-line proof and this is two lines of it. *)
  Definition kxd_name_fn (bs : list (bv 8)) : nat -> bv 8 :=
    fun i => default (bv_0 8) (bs !! i).

  Lemma kxd_name_fn_spec (bs : list (bv 8)) (i : nat) :
    (i < length bs)%nat -> bs !! i = Some (kxd_name_fn bs i).
  Proof.
    intro Hi. unfold kxd_name_fn.
    destruct (bs !! i) as [x |] eqn:E; [reflexivity |].
    exfalso. apply lookup_ge_None in E. lia.
  Qed.

  Lemma kxd_name_fn_len (n : nat) (h : nat -> bv 8) :
    length (h <$> seq 0 n) = n.
  Proof. by rewrite length_fmap length_seq. Qed.

  (* [ProofKexecC]'s two [kxc_sp] facts, local there and needed here to put
     the final [sp] back in range: it is at most the stack top (the
     recurrence only ever subtracts and rounds DOWN) and at least stackbase
     (the [bltu] at +0x290, carried in [kxc_stack_ok]). *)
  Lemma kxd_sp_S (top : Z) (len : nat -> nat) (i : nat) :
    kxc_sp top len (S i) = kxc_round16 (kxc_sp top len i - (Z.of_nat (len i) + 1)).
  Proof. reflexivity. Qed.

  Lemma kxd_sp_le_top (top : Z) (len : nat -> nat) (i : nat) :
    kxc_sp top len i <= top.
  Proof.
    induction i as [| i IH].
    - change (kxc_sp top len 0) with top. lia.
    - rewrite kxd_sp_S. unfold kxc_round16.
      pose proof (Z.mod_pos_bound
                    (kxc_sp top len i - (Z.of_nat (len i) + 1)) 16 ltac:(lia)) as Hb.
      lia.
  Qed.

  Lemma kxd_sp_final_le_top (top : Z) (len : nat -> nat) (i : nat) :
    kxc_sp_final top len i <= top.
  Proof.
    unfold kxc_sp_final, kxc_round16.
    pose proof (kxd_sp_le_top top len i) as Hle.
    pose proof (Z.mod_pos_bound
                  (kxc_sp top len i - 8 * (Z.of_nat i + 1)) 16 ltac:(lia)) as Hb.
    lia.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  +0x2d2 .. +0x31a -- THE COMMIT PROPER.                              *)
  (*                                                                      *)
  (*  Its own lemma because +0x2d2 has TWO predecessors -- the scan's exit *)
  (*  and the [argv[0] is NUL] skip at +0x2b6 -- and the caller's exit     *)
  (*  continuation is linear, so publishing it twice is not an option.     *)
  (*  [Vc] is the process block with the FIRST trapframe word already      *)
  (*  written; the commit's own two writes and the name copy take it the   *)
  (*  rest of the way to the contract's [upd_exec].                        *)
  (* ------------------------------------------------------------------- *)
  Lemma kxd_commit
      (jp : nat) (bn : bio_names) (gfs : fs_names) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (size : Z) (used2 : gset Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
      (m M : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (sz1 : mword 64) (c q : nat) :
    (K_kexec <= K)%nat ->
    bb_cstr pfun plen ->
    (q <= plen)%nat ->
    (na < MAXARG)%nat ->
    (8192 <= uint sz1)%Z ->
    c = na ->
    kxc_stack_ok (uint sz1) (uint sz1 - 4096) alen na ->
    ud_tfp P = ud_tfp (pv_upt V) ->
    um_below sz1 P.(ud_um) -> um_covered sz1 P.(ud_um) ->
    (forall i, (i < 8)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (54 - i))) 8 = true) ->
    m !!! Regidx csp_rs1 = sp0 -> m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 -> m !!! Regidx Rs1 = s10 -> m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Rs3 = w5 -> m !!! Regidx Rs4 = w6 -> m !!! Regidx Rs5 = w7 ->
    m !!! Regidx Rs6 = w8 -> m !!! Regidx Rs7 = w9 -> m !!! Regidx Rs8 = w10 ->
    m !!! Regidx Rs9 = w11 -> m !!! Regidx Rs10 = w12 -> m !!! Regidx Rs11 = w13 ->
    M !!! Regidx csp_rs1 = pa_stk sp0 68 ->
    M !!! Regidx Rs0 = sp0 ->
    M !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64) ->
    M !!! Regidx Rs2
      = (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64) ->
    M !!! Regidx Rs4 = sz1 ->
    M !!! Regidx Rs5 = proc_addr jp ->
    M !!! Regidx Rs6 = page_base P.(ud_root) ->
    M !!! Regidx Rs10 = pv_sz V ->
    kernel_text -∗
    pc_is (mword_of_int (KXD + 0x2d2) : mword 64) -∗
    sie_cap_gpr M (K - 68)%nat true (proc_addr jp) -∗
    cpu_own 0 true (proc_addr jp) true ∅ -∗
    kalloc_env ga None -∗
    kxd_res jp bn gfs ga gf cov logstart bmapstart inodestart size used2
            plen pfun na avf aslen afun pidv
            (upd_tf V (<[tf_arg_idx 1
                         := (mword_of_int (kxc_sp_final (uint sz1) alen c)
                             : mword 64)]> (pv_tf V)))
            dqb dqs dqa sp0 ra0 s00 s10 s20 pv av
            w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P c (pa_add pv q) -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
    ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
       (entry spv szv' : mword 64),
        ⌜callee_saved m mf⌝ -∗
        ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
        sie_cap_gpr mf K true (proc_addr jp) -∗
        cpu_own 0 true (proc_addr jp) true ∅ -∗
        pc_is (ret_pc ra0) -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        ⌜used' ⊆ used2⌝ -∗
        bitmap_res gfs bmapstart cov logstart size used' -∗
        kalloc_env ga None -∗
        proc_priv gf (proc_addr jp) pidv V' -∗
        ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
        ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
        ([∗ list] i ∈ seq 0 na,
           [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
        bslots bn 3 -∗
        iref_slots 2 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hcstr Hq Hnamax Hsz1ge Hceq Hstk HPtfp Hbelow Hcov Hal
           Hmsp Hmra Hms0 Hms1 Hms2
           Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13
           HMsp HMs0 HMs1 HMs2 HMs4 HMs5 HMs6 HMs10.
    (* the loop's final counter IS the argument count; say so once, so the
       exit's [alen na] and the state's [alen c] are the same term.  [subst
       na], not [subst c]: the block's own text is written in [c]. *)
    subst na.
    
    iIntros "#Htext Hpc Hcg Hcnt #Hka Hres Hcont".
    rewrite /kxd_res.
    iDestruct "Hres" as "(Hirs & Hbm & Hins & Hbits & Hbs & Hpt & Hpriv &
                          Hpath & Hargv & Hargs & Helf & Hframe)".
    rewrite /kxc_frameB.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9 &
                            Hf10 & Hf11 & Hf12 & Hf13 & Hust & Hph &
                            Hf64 & Hf65e & Hf66 & Hf67 & Hf68e)".
    iDestruct "Hf65e" as (w65) "Hf65". iDestruct "Hf68e" as (w68) "Hf68".
    iPoseProof (kxc_2d2 with "Htext") as "Hi2d2".
    iPoseProof (kxc_2d4 with "Htext") as "Hi2d4".
    iPoseProof (kxc_2d8 with "Htext") as "Hi2d8".
    iPoseProof (kxc_2dc with "Htext") as "Hi2dc".
    (* ---- +0x2d2: c.li a2,16 (PNAMELEN) ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KXD + 0x2d2)) Ra2
              (mword_of_int 16 : mword 6) (mword_of_int 16 : mword 64)
              M (K - 68)%nat true ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi2d2").
    iIntros (CID1 Hs1) "Hcg Hpc".
    pose (E1 := <[Regidx Ra2 := regval_into_reg (mword_of_int 16 : mword 64)]> M).
    assert (HE1a2 : E1 !!! Regidx Ra2 = (mword_of_int 16 : mword 64))
      by (rewrite /E1; apply upd_eq).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /E1 upd_ne; [exact HMsp | nz]).
    assert (HE1s0 : E1 !!! Regidx Rs0 = sp0)
      by (rewrite /E1 upd_ne; [exact HMs0 | nz]).
    assert (HE1s1 : E1 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
      by (rewrite /E1 upd_ne; [exact HMs1 | nz]).
    assert (HE1s2 : E1 !!! Regidx Rs2
                    = (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64))
      by (rewrite /E1 upd_ne; [exact HMs2 | nz]).
    assert (HE1s4 : E1 !!! Regidx Rs4 = sz1)
      by (rewrite /E1 upd_ne; [exact HMs4 | nz]).
    assert (HE1s5 : E1 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /E1 upd_ne; [exact HMs5 | nz]).
    assert (HE1s6 : E1 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /E1 upd_ne; [exact HMs6 | nz]).
    assert (HE1s10 : E1 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /E1 upd_ne; [exact HMs10 | nz]).
    assert (Hpp2d4 : add_vec_int (mword_of_int (KXD + 0x2d2) : mword 64) 2
                     = mword_of_int (KXD + 0x2d4)) by pcw.
    iEval (rewrite Hpp2d4) in "Hpc".
    (* ---- +0x2d4: ld a1,-528(s0) -- a1 = last ---- *)
    assert (Hslot66 : add_vec (E1 !!! Regidx Rs0)
                        (sign_extend' 64 (mword_of_int 3568 : mword 12))
                      = pa_stk sp0 66)
      by (rewrite HE1s0; apply kxd_last_slot).
    iEval (rewrite -Hslot66) in "Hf66".
    iApply (wp_ld_s_sconf (mword_of_int (KXD + 0x2d4)) Ra1 Rs0
              (mword_of_int 3568 : mword 12) E1 (K - 68)%nat (pa_add pv q) true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2d4 Hf66").
    iIntros (CID2 Hs2) "Hcg Hpc Hf66". iEval (rewrite Hslot66) in "Hf66".
    pose (E2 := <[Regidx Ra1 := regval_into_reg (pa_add pv q)]> E1).
    assert (HE2a1 : E2 !!! Regidx Ra1 = pa_add pv q)
      by (rewrite /E2; apply upd_eq).
    assert (HE2a2 : E2 !!! Regidx Ra2 = (mword_of_int 16 : mword 64))
      by (rewrite /E2 upd_ne; [exact HE1a2 | nz]).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /E2 upd_ne; [exact HE1sp | nz]).
    assert (HE2s0 : E2 !!! Regidx Rs0 = sp0)
      by (rewrite /E2 upd_ne; [exact HE1s0 | nz]).
    assert (HE2s1 : E2 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
      by (rewrite /E2 upd_ne; [exact HE1s1 | nz]).
    assert (HE2s2 : E2 !!! Regidx Rs2
                    = (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64))
      by (rewrite /E2 upd_ne; [exact HE1s2 | nz]).
    assert (HE2s4 : E2 !!! Regidx Rs4 = sz1)
      by (rewrite /E2 upd_ne; [exact HE1s4 | nz]).
    assert (HE2s5 : E2 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /E2 upd_ne; [exact HE1s5 | nz]).
    assert (HE2s6 : E2 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /E2 upd_ne; [exact HE1s6 | nz]).
    assert (HE2s10 : E2 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /E2 upd_ne; [exact HE1s10 | nz]).
    assert (Hpp2d8 : add_vec_int (mword_of_int (KXD + 0x2d4) : mword 64) 4
                     = mword_of_int (KXD + 0x2d8)) by pcw.
    iEval (rewrite Hpp2d8) in "Hpc".
    (* ---- +0x2d8: addi a0,s5,344 -- a0 = &p->name ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KXD + 0x2d8)) Ra0 Rs5
              (mword_of_int 344 : mword 12) E2 (K - 68)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2d8").
    iIntros (CID3 Hs3) "Hcg Hpc".
    pose (E3 := <[Regidx Ra0 := regval_into_reg
                   (add_vec (rget E2 Rs5)
                      (sign_extend' 64 (mword_of_int 344 : mword 12)))]> E2).
    assert (HE3a0 : E3 !!! Regidx Ra0 = kfk_name_base (proc_addr jp)).
    { rewrite /E3 upd_eq (rget_ne E2 Rs5 ltac:(nz)) HE2s5 /kfk_name_base.
      f_equal. }
    assert (HE3a1 : E3 !!! Regidx Ra1 = pa_add pv q)
      by (rewrite /E3 upd_ne; [exact HE2a1 | nz]).
    assert (HE3a2 : E3 !!! Regidx Ra2 = (mword_of_int 16 : mword 64))
      by (rewrite /E3 upd_ne; [exact HE2a2 | nz]).
    assert (HE3sp : E3 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /E3 upd_ne; [exact HE2sp | nz]).
    assert (HE3s0 : E3 !!! Regidx Rs0 = sp0)
      by (rewrite /E3 upd_ne; [exact HE2s0 | nz]).
    assert (HE3s1 : E3 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
      by (rewrite /E3 upd_ne; [exact HE2s1 | nz]).
    assert (HE3s2 : E3 !!! Regidx Rs2
                    = (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64))
      by (rewrite /E3 upd_ne; [exact HE2s2 | nz]).
    assert (HE3s4 : E3 !!! Regidx Rs4 = sz1)
      by (rewrite /E3 upd_ne; [exact HE2s4 | nz]).
    assert (HE3s5 : E3 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /E3 upd_ne; [exact HE2s5 | nz]).
    assert (HE3s6 : E3 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /E3 upd_ne; [exact HE2s6 | nz]).
    assert (HE3s10 : E3 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /E3 upd_ne; [exact HE2s10 | nz]).
    assert (Hpp2dc : add_vec_int (mword_of_int (KXD + 0x2d8) : mword 64) 4
                     = mword_of_int (KXD + 0x2dc)) by pcw.
    iEval (rewrite Hpp2dc) in "Hpc".
    (* ---- +0x2dc: jal ra,safestrcpy ---- *)
    assert (Htss : add_vec (mword_of_int (KXD + 0x2dc) : mword 64)
                     (sign_extend' 64 (mword_of_int 2081690 : mword 21))
                   = mword_of_int KernelSyms.safestrcpy) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXD + 0x2dc)) Rra
              (mword_of_int 2081690 : mword 21) E3 (K - 68)%nat true
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htss; vm_compute; reflexivity)
              with "Hcg Hpc Hi2dc").
    iIntros (CID4 Hs4) "Hcg Hpc". iEval (rewrite Htss) in "Hpc".
    pose (E4 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (KXD + 0x2dc) : mword 64) 4)]> E3).
    assert (HE4ra : E4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXD + 0x2dc) : mword 64) 4)
      by (rewrite /E4; apply upd_eq).
    assert (HE4a0 : E4 !!! Regidx Ra0 = kfk_name_base (proc_addr jp))
      by (rewrite /E4 upd_ne; [exact HE3a0 | nz]).
    assert (HE4a1 : E4 !!! Regidx Ra1 = pa_add pv q)
      by (rewrite /E4 upd_ne; [exact HE3a1 | nz]).
    assert (HE4a2 : E4 !!! Regidx Ra2 = (mword_of_int 16 : mword 64))
      by (rewrite /E4 upd_ne; [exact HE3a2 | nz]).
    assert (HE4sp : E4 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /E4 upd_ne; [exact HE3sp | nz]).
    assert (HE4s0 : E4 !!! Regidx Rs0 = sp0)
      by (rewrite /E4 upd_ne; [exact HE3s0 | nz]).
    assert (HE4s1 : E4 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
      by (rewrite /E4 upd_ne; [exact HE3s1 | nz]).
    assert (HE4s2 : E4 !!! Regidx Rs2
                    = (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64))
      by (rewrite /E4 upd_ne; [exact HE3s2 | nz]).
    assert (HE4s4 : E4 !!! Regidx Rs4 = sz1)
      by (rewrite /E4 upd_ne; [exact HE3s4 | nz]).
    assert (HE4s5 : E4 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /E4 upd_ne; [exact HE3s5 | nz]).
    assert (HE4s6 : E4 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /E4 upd_ne; [exact HE3s6 | nz]).
    assert (HE4s10 : E4 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /E4 upd_ne; [exact HE3s10 | nz]).
    (* ---- the two buffers safestrcpy wants: [p->name]'s sixteen cells out
       of the process block, and the path RE-BASED at [last]. ---- *)
    iDestruct (proc_priv_name with "Hpriv") as "(%Hnl & Hnm & Hnmback)".
    iDestruct (kfk_pname_bytes (proc_addr jp) (DfracOwn 1)
                 (pv_name (upd_tf V
                    (<[tf_arg_idx 1
                       := (mword_of_int (kxc_sp_final (uint sz1) alen c)
                           : mword 64)]> (pv_tf V))))
                 (kxd_name_fn (pv_name V))
                 ltac:(intros i Hi; apply kxd_name_fn_spec; exact Hi)
                 with "Hnm") as "Hnmseq".
    iEval (rewrite Hnl) in "Hnmseq".
    iEval (rewrite -HE4a0) in "Hnmseq".
    assert (Hsplit3 : (q + (S plen - q) + 0 = S plen)%nat) by lia.
    iEval (rewrite (bb_split3 pv q (S plen - q) 0 (S plen) pfun Hsplit3))
      in "Hpath".
    iDestruct "Hpath" as "(Hpre & Hsrc & Hsuf)".
    iEval (rewrite -HE4a1) in "Hsrc".
    assert (Hsrcok : ssc_src_ok (fun j => pfun (q + j)%nat) PNAMELEN
                       (S plen - q)%nat).
    { right. exists (plen - q)%nat. split; [lia |].
      destruct Hcstr as [_ Hnul].
      assert (Hqp : (q + (plen - q))%nat = plen) by lia.
      rewrite Hqp. exact Hnul. }
    iApply (SS.wp_safestrcpy_sconf E4 PNAMELEN (S plen - q)%nat
              (fun j => pfun (q + j)%nat) (kxd_name_fn (pv_name V))
              (K - 68)%nat (DfracOwn 1) true (proc_addr jp)
              ltac:(unfold PNAMELEN; lia)
              ltac:(rewrite HE4a2; apply bv_eq; vm_compute; reflexivity)
              ltac:(unfold PNAMELEN; change (2 ^ 31)%Z with 2147483648%Z; lia)
              Hsrcok
              with "Hcg Htext Hpc Hsrc Hnmseq").
    iIntros (CID5 Hs5 mr h) "Hcg Hpc Hsrc Hnmseq %Hcsn %Hnra0 %Hnpost".
    assert (Hpc2e0 : ret_pc (E4 !!! Regidx Rra) = mword_of_int (KXD + 0x2e0))
      by (rewrite HE4ra; pcw).
    iEval (rewrite Hpc2e0) in "Hpc".
    (* ---- put both buffers back ---- *)
    iEval (rewrite HE4a1) in "Hsrc".
    iAssert ([∗ list] k ∈ seq 0 (S plen), pa_add pv k ↦ₘ pfun k)%I
      with "[Hpre Hsrc Hsuf]" as "Hpath".
    { iEval (rewrite (bb_split3 pv q (S plen - q) 0 (S plen) pfun Hsplit3)).
      iSplitL "Hpre"; [iExact "Hpre" |].
      iSplitL "Hsrc"; [iExact "Hsrc" | iExact "Hsuf"]. }
    iEval (rewrite HE4a0) in "Hnmseq".
    iDestruct (kfk_bytes_pname (proc_addr jp) (DfracOwn 1) PNAMELEN h
                 with "Hnmseq") as "Hnmfold".
    iSpecialize ("Hnmback" $! (h <$> seq 0 PNAMELEN)).
    iSpecialize ("Hnmback" with "[%]"); [apply kxd_name_fn_len |].
    iDestruct ("Hnmback" with "Hnmfold") as "Hpriv".
    (* the registers safestrcpy preserved *)
    assert (HF0sp : mr !!! Regidx csp_rs1 = pa_stk sp0 68).
    { rewrite (callee_saved_lookup Hcsn csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HE4sp. }
    assert (HF0s0 : mr !!! Regidx Rs0 = sp0).
    { rewrite (callee_saved_lookup Hcsn Rs0 ltac:(vm_compute; reflexivity)).
      exact HE4s0. }
    assert (HF0s1 : mr !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64)).
    { rewrite (callee_saved_lookup Hcsn Rs1 ltac:(vm_compute; reflexivity)).
      exact HE4s1. }
    assert (HF0s2 : mr !!! Regidx Rs2
                    = (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64)).
    { rewrite (callee_saved_lookup Hcsn Rs2 ltac:(vm_compute; reflexivity)).
      exact HE4s2. }
    assert (HF0s4 : mr !!! Regidx Rs4 = sz1).
    { rewrite (callee_saved_lookup Hcsn Rs4 ltac:(vm_compute; reflexivity)).
      exact HE4s4. }
    assert (HF0s5 : mr !!! Regidx Rs5 = proc_addr jp).
    { rewrite (callee_saved_lookup Hcsn Rs5 ltac:(vm_compute; reflexivity)).
      exact HE4s5. }
    assert (HF0s6 : mr !!! Regidx Rs6 = page_base P.(ud_root)).
    { rewrite (callee_saved_lookup Hcsn Rs6 ltac:(vm_compute; reflexivity)).
      exact HE4s6. }
    assert (HF0s10 : mr !!! Regidx Rs10 = pv_sz V).
    { rewrite (callee_saved_lookup Hcsn Rs10 ltac:(vm_compute; reflexivity)).
      exact HE4s10. }
    (* [pt_node_claim], off [hw_config] (peeled from [Hcg] persistently) and
       [page_valid] (the trapframe page's own well-formedness) -- what the
       SD instructions below need to cross [tf_page_word_upd]'s physical-
       native result to the mem tier they actually run at (kernel code
       reaching the trapframe through its own mapping, not the trampoline's
       physical entry/exit path). *)
    iDestruct (proc_priv_tfp_valid with "Hpriv") as %Hpv_valid.
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhw Hcg]".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iPoseProof (pt_node_claim_from_static (ud_tfp (pv_upt V)) Hpv_valid with "Hkmapb") as "#Hptc".
    (* ---- the process block, opened for the COMMIT's own three writes ---- *)
    iDestruct (proc_priv_newspace with "Hpriv")
      as "(%Hszmax & %Hbelold & Hpsz & Hppt & Hptf & Hptold & Htfp & Hprivback)".
    iDestruct (kxd_tf_len with "Htfp") as "[%Htflen Htfp]".
    iPoseProof (kxc_2e0 with "Htext") as "Hi2e0".
    iPoseProof (kxc_2e4 with "Htext") as "Hi2e4".
    iPoseProof (kxc_2e8 with "Htext") as "Hi2e8".
    iPoseProof (kxc_2ec with "Htext") as "Hi2ec".
    iPoseProof (kxc_2f0 with "Htext") as "Hi2f0".
    iPoseProof (kxc_2f4 with "Htext") as "Hi2f4".
    iPoseProof (kxc_2f6 with "Htext") as "Hi2f6".
    iPoseProof (kxc_2fa with "Htext") as "Hi2fa".
    iPoseProof (kxc_2fe with "Htext") as "Hi2fe".
    iPoseProof (kxc_300 with "Htext") as "Hi300".
    (* ---- +0x2e0: ld a0,80(s5) -- the OLD table, for proc_freepagetable ---- *)
    assert (Hppaddr : add_vec (mr !!! Regidx Rs5)
                        (sign_extend' 64 (mword_of_int 80 : mword 12))
                      = p_pagetable (proc_addr jp))
      by (rewrite HF0s5; reflexivity).
    iEval (rewrite -Hppaddr) in "Hppt".
    iApply (wp_ld_s_sconf (mword_of_int (KXD + 0x2e0)) Ra0 Rs5
              (mword_of_int 80 : mword 12) mr (K - 68)%nat
              (page_base (ud_root (pv_upt V))) true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2e0 Hppt").
    iIntros (CID6 Hs6) "Hcg Hpc Hppt". iEval (rewrite Hppaddr) in "Hppt".
    pose (F1 := <[Regidx Ra0 := regval_into_reg
                   (page_base (ud_root (pv_upt V)))]> mr).
    assert (HF1a0 : F1 !!! Regidx Ra0 = page_base (ud_root (pv_upt V)))
      by (rewrite /F1; apply upd_eq).
    assert (HF1sp : F1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /F1 upd_ne; [exact HF0sp | nz]).
    assert (HF1s0 : F1 !!! Regidx Rs0 = sp0)
      by (rewrite /F1 upd_ne; [exact HF0s0 | nz]).
    assert (HF1s1 : F1 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
      by (rewrite /F1 upd_ne; [exact HF0s1 | nz]).
    assert (HF1s2 : F1 !!! Regidx Rs2
                    = (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64))
      by (rewrite /F1 upd_ne; [exact HF0s2 | nz]).
    assert (HF1s4 : F1 !!! Regidx Rs4 = sz1)
      by (rewrite /F1 upd_ne; [exact HF0s4 | nz]).
    assert (HF1s5 : F1 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /F1 upd_ne; [exact HF0s5 | nz]).
    assert (HF1s6 : F1 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /F1 upd_ne; [exact HF0s6 | nz]).
    assert (HF1s10 : F1 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /F1 upd_ne; [exact HF0s10 | nz]).
    assert (Hpp2e4 : add_vec_int (mword_of_int (KXD + 0x2e0) : mword 64) 4
                     = mword_of_int (KXD + 0x2e4)) by pcw.
    iEval (rewrite Hpp2e4) in "Hpc".
    (* ---- +0x2e4: sd s6,80(s5) -- p->pagetable = the NEW table ---- *)
    assert (Hppaddr1 : add_vec (F1 !!! Regidx Rs5)
                         (sign_extend' 64 (mword_of_int 80 : mword 12))
                       = p_pagetable (proc_addr jp))
      by (rewrite HF1s5; reflexivity).
    iEval (rewrite -Hppaddr1) in "Hppt".
    iApply (wp_sd_s_sconf (mword_of_int (KXD + 0x2e4)) Rs6 Rs5
              (mword_of_int 80 : mword 12) F1 (K - 68)%nat
              (page_base (ud_root (pv_upt V))) true
              with "Hcg Hpc Hi2e4 Hppt").
    iIntros (CID7 Hs7) "Hcg Hpc Hppt". iEval (rewrite Hppaddr1) in "Hppt".
    iEval (rewrite (rget_ne (CID := CID6) F1 Rs6 ltac:(nz)) HF1s6) in "Hppt".
    assert (Hpp2e8 : add_vec_int (mword_of_int (KXD + 0x2e4) : mword 64) 4
                     = mword_of_int (KXD + 0x2e8)) by pcw.
    iEval (rewrite Hpp2e8) in "Hpc".
    (* ---- +0x2e8: sd s4,72(s5) -- p->sz = sz1 ---- *)
    assert (Hszaddr : add_vec (F1 !!! Regidx Rs5)
                        (sign_extend' 64 (mword_of_int 72 : mword 12))
                      = p_sz (proc_addr jp))
      by (rewrite HF1s5; reflexivity).
    iEval (rewrite -Hszaddr) in "Hpsz".
    iApply (wp_sd_s_sconf (mword_of_int (KXD + 0x2e8)) Rs4 Rs5
              (mword_of_int 72 : mword 12) F1 (K - 68)%nat (pv_sz V) true
              with "Hcg Hpc Hi2e8 Hpsz").
    iIntros (CID8 Hs8) "Hcg Hpc Hpsz". iEval (rewrite Hszaddr) in "Hpsz".
    iEval (rewrite (rget_ne (CID := CID7) F1 Rs4 ltac:(nz)) HF1s4) in "Hpsz".
    assert (Hpp2ec : add_vec_int (mword_of_int (KXD + 0x2e8) : mword 64) 4
                     = mword_of_int (KXD + 0x2ec)) by pcw.
    iEval (rewrite Hpp2ec) in "Hpc".
    (* ---- +0x2ec: ld a5,88(s5) -- the trapframe page ---- *)
    assert (Htfaddr : add_vec (F1 !!! Regidx Rs5)
                        (sign_extend' 64 (mword_of_int 88 : mword 12))
                      = p_trapframe (proc_addr jp))
      by (rewrite HF1s5; reflexivity).
    iEval (rewrite -Htfaddr) in "Hptf".
    iApply (wp_ld_s_sconf (mword_of_int (KXD + 0x2ec)) Ra5 Rs5
              (mword_of_int 88 : mword 12) F1 (K - 68)%nat
              (page_base (ud_tfp (pv_upt V))) true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2ec Hptf").
    iIntros (CID9 Hs9) "Hcg Hpc Hptf". iEval (rewrite Htfaddr) in "Hptf".
    pose (F2 := <[Regidx Ra5 := regval_into_reg
                   (page_base (ud_tfp (pv_upt V)))]> F1).
    assert (HF2a5 : F2 !!! Regidx Ra5 = page_base (ud_tfp (pv_upt V)))
      by (rewrite /F2; apply upd_eq).
    assert (HF2a0 : F2 !!! Regidx Ra0 = page_base (ud_root (pv_upt V)))
      by (rewrite /F2 upd_ne; [exact HF1a0 | nz]).
    assert (HF2sp : F2 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /F2 upd_ne; [exact HF1sp | nz]).
    assert (HF2s0 : F2 !!! Regidx Rs0 = sp0)
      by (rewrite /F2 upd_ne; [exact HF1s0 | nz]).
    assert (HF2s1 : F2 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
      by (rewrite /F2 upd_ne; [exact HF1s1 | nz]).
    assert (HF2s2 : F2 !!! Regidx Rs2
                    = (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64))
      by (rewrite /F2 upd_ne; [exact HF1s2 | nz]).
    assert (HF2s4 : F2 !!! Regidx Rs4 = sz1)
      by (rewrite /F2 upd_ne; [exact HF1s4 | nz]).
    assert (HF2s5 : F2 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /F2 upd_ne; [exact HF1s5 | nz]).
    assert (HF2s6 : F2 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /F2 upd_ne; [exact HF1s6 | nz]).
    assert (HF2s10 : F2 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /F2 upd_ne; [exact HF1s10 | nz]).
    assert (Hpp2f0 : add_vec_int (mword_of_int (KXD + 0x2ec) : mword 64) 4
                     = mword_of_int (KXD + 0x2f0)) by pcw.
    iEval (rewrite Hpp2f0) in "Hpc".
    (* ---- +0x2f0: ld a4,-408(s0) -- elf.entry, byte 24 of the header ---- *)
    assert (Helfaddr : add_vec (F2 !!! Regidx Rs0)
                         (sign_extend' 64 (mword_of_int 3688 : mword 12))
                       = pa_add (pa_stk sp0 54) 24)
      by (rewrite HF2s0; apply kxd_elf_entry_addr).
    assert (Halelf : is_aligned_paddr (Physaddr (pa_add (pa_stk sp0 54) 24)) 8
                     = true).
    { assert (He : pa_add (pa_stk sp0 54) 24 = pa_stk sp0 51).
      { change 24%nat with (8 * 3)%nat.
        rewrite (pa_stk_addn sp0 54 3 ltac:(lia)). f_equal. }
      rewrite He. exact (Hal 3%nat ltac:(lia)). }
    iDestruct (kxd_win8 (pa_stk sp0 54) ef 24 32 64 ltac:(lia) Halelf
                 with "Helf") as "[Hentry Helfback]".
    iEval (rewrite -Helfaddr) in "Hentry".
    iApply (wp_ld_s_sconf (mword_of_int (KXD + 0x2f0)) Ra4 Rs0
              (mword_of_int 3688 : mword 12) F2 (K - 68)%nat
              (Z_to_bv 64 (le_at ef 24 8) : mword 64) true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2f0 Hentry").
    iIntros (CID10 Hs10) "Hcg Hpc Hentry". iEval (rewrite Helfaddr) in "Hentry".
    iDestruct ("Helfback" with "Hentry") as "Helf".
    pose (F3 := <[Regidx Ra4 := regval_into_reg
                   (Z_to_bv 64 (le_at ef 24 8) : mword 64)]> F2).
    assert (HF3a4 : F3 !!! Regidx Ra4 = (Z_to_bv 64 (le_at ef 24 8) : mword 64))
      by (rewrite /F3; apply upd_eq).
    assert (HF3a5 : F3 !!! Regidx Ra5 = page_base (ud_tfp (pv_upt V)))
      by (rewrite /F3 upd_ne; [exact HF2a5 | nz]).
    assert (HF3a0 : F3 !!! Regidx Ra0 = page_base (ud_root (pv_upt V)))
      by (rewrite /F3 upd_ne; [exact HF2a0 | nz]).
    assert (HF3sp : F3 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /F3 upd_ne; [exact HF2sp | nz]).
    assert (HF3s0 : F3 !!! Regidx Rs0 = sp0)
      by (rewrite /F3 upd_ne; [exact HF2s0 | nz]).
    assert (HF3s1 : F3 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
      by (rewrite /F3 upd_ne; [exact HF2s1 | nz]).
    assert (HF3s2 : F3 !!! Regidx Rs2
                    = (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64))
      by (rewrite /F3 upd_ne; [exact HF2s2 | nz]).
    assert (HF3s4 : F3 !!! Regidx Rs4 = sz1)
      by (rewrite /F3 upd_ne; [exact HF2s4 | nz]).
    assert (HF3s5 : F3 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /F3 upd_ne; [exact HF2s5 | nz]).
    assert (HF3s6 : F3 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /F3 upd_ne; [exact HF2s6 | nz]).
    assert (HF3s10 : F3 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /F3 upd_ne; [exact HF2s10 | nz]).
    assert (Hpp2f4 : add_vec_int (mword_of_int (KXD + 0x2f0) : mword 64) 4
                     = mword_of_int (KXD + 0x2f4)) by pcw.
    iEval (rewrite Hpp2f4) in "Hpc".
    (* ---- +0x2f4: c.sd a4,24(a5) -- trapframe->epc = elf.entry ---- *)
    assert (Hw3 : exists u3,
              (<[tf_arg_idx 1
                 := (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64)]>
                 (pv_tf V)) !! tf_epc_idx = Some u3).
    { apply lookup_lt_is_Some_2. rewrite Htflen.
      unfold TFWORDS, tf_epc_idx. lia. }
    destruct Hw3 as [u3 Hu3].
    iDestruct (tf_page_word_upd_mem _ _ tf_epc_idx u3
                 ltac:(unfold tf_epc_idx; lia) Hu3 with "Hptc Htfp")
      as "(Hword3 & Htfback3)".
    assert (Haddr24 : add_vec (F3 !!! Regidx Ra5)
                        (sign_extend' 64 (mword_of_int 24 : mword 12))
                      = tf_pa (ud_tfp (pv_upt V)) (8 * Z.of_nat tf_epc_idx)).
    { rewrite HF3a5. apply kxd_tf_addr.
      { unfold tf_epc_idx. lia. }
      unfold tf_epc_idx. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Haddr24) in "Hword3".
    iApply (wp_csd_s_sconf (mword_of_int (KXD + 0x2f4)) Ra4 Ra5
              (mword_of_int 24 : mword 12) F3 (K - 68)%nat u3 true
              with "Hcg Hpc Hi2f4 Hword3").
    iIntros (CID11 Hs11) "Hcg Hpc Hword3". iEval (rewrite Haddr24) in "Hword3".
    iEval (rewrite (rget_ne (CID := CID10) F3 Ra4 ltac:(nz)) HF3a4) in "Hword3".
    iDestruct ("Htfback3" with "Hword3") as "Htfp".
    assert (Hpp2f6 : add_vec_int (mword_of_int (KXD + 0x2f4) : mword 64) 2
                     = mword_of_int (KXD + 0x2f6)) by pcw.
    iEval (rewrite Hpp2f6) in "Hpc".
    (* ---- +0x2f6: ld a5,88(s5) -- the trapframe page, again ---- *)
    assert (Htfaddr2 : add_vec (F3 !!! Regidx Rs5)
                         (sign_extend' 64 (mword_of_int 88 : mword 12))
                       = p_trapframe (proc_addr jp))
      by (rewrite HF3s5; reflexivity).
    iEval (rewrite -Htfaddr2) in "Hptf".
    iApply (wp_ld_s_sconf (mword_of_int (KXD + 0x2f6)) Ra5 Rs5
              (mword_of_int 88 : mword 12) F3 (K - 68)%nat
              (page_base (ud_tfp (pv_upt V))) true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2f6 Hptf").
    iIntros (CID12 Hs12) "Hcg Hpc Hptf". iEval (rewrite Htfaddr2) in "Hptf".
    pose (F4 := <[Regidx Ra5 := regval_into_reg
                   (page_base (ud_tfp (pv_upt V)))]> F3).
    assert (HF4a5 : F4 !!! Regidx Ra5 = page_base (ud_tfp (pv_upt V)))
      by (rewrite /F4; apply upd_eq).
    assert (HF4a0 : F4 !!! Regidx Ra0 = page_base (ud_root (pv_upt V)))
      by (rewrite /F4 upd_ne; [exact HF3a0 | nz]).
    assert (HF4sp : F4 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /F4 upd_ne; [exact HF3sp | nz]).
    assert (HF4s0 : F4 !!! Regidx Rs0 = sp0)
      by (rewrite /F4 upd_ne; [exact HF3s0 | nz]).
    assert (HF4s1 : F4 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
      by (rewrite /F4 upd_ne; [exact HF3s1 | nz]).
    assert (HF4s2 : F4 !!! Regidx Rs2
                    = (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64))
      by (rewrite /F4 upd_ne; [exact HF3s2 | nz]).
    assert (HF4s4 : F4 !!! Regidx Rs4 = sz1)
      by (rewrite /F4 upd_ne; [exact HF3s4 | nz]).
    assert (HF4s5 : F4 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /F4 upd_ne; [exact HF3s5 | nz]).
    assert (HF4s6 : F4 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /F4 upd_ne; [exact HF3s6 | nz]).
    assert (HF4s10 : F4 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /F4 upd_ne; [exact HF3s10 | nz]).
    assert (Hpp2fa : add_vec_int (mword_of_int (KXD + 0x2f6) : mword 64) 4
                     = mword_of_int (KXD + 0x2fa)) by pcw.
    iEval (rewrite Hpp2fa) in "Hpc".
    (* ---- +0x2fa: sd s2,48(a5) -- trapframe->sp = the new user sp ---- *)
    assert (Hw6 : exists u6,
              (<[tf_epc_idx := (Z_to_bv 64 (le_at ef 24 8) : mword 64)]>
                 (<[tf_arg_idx 1
                    := (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64)]>
                    (pv_tf V))) !! kxc_tf_sp_idx = Some u6).
    { apply lookup_lt_is_Some_2. rewrite length_insert Htflen.
      unfold TFWORDS, kxc_tf_sp_idx. lia. }
    destruct Hw6 as [u6 Hu6].
    iDestruct (tf_page_word_upd_mem _ _ kxc_tf_sp_idx u6
                 ltac:(unfold kxc_tf_sp_idx; lia) Hu6 with "Hptc Htfp")
      as "(Hword6 & Htfback6)".
    assert (Haddr48 : add_vec (F4 !!! Regidx Ra5)
                        (sign_extend' 64 (mword_of_int 48 : mword 12))
                      = tf_pa (ud_tfp (pv_upt V)) (8 * Z.of_nat kxc_tf_sp_idx)).
    { rewrite HF4a5. apply kxd_tf_addr.
      { unfold kxc_tf_sp_idx. lia. }
      unfold kxc_tf_sp_idx. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Haddr48) in "Hword6".
    iApply (wp_sd_s_sconf (mword_of_int (KXD + 0x2fa)) Rs2 Ra5
              (mword_of_int 48 : mword 12) F4 (K - 68)%nat u6 true
              with "Hcg Hpc Hi2fa Hword6").
    iIntros (CID13 Hs13) "Hcg Hpc Hword6". iEval (rewrite Haddr48) in "Hword6".
    iEval (rewrite (rget_ne (CID := CID12) F4 Rs2 ltac:(nz)) HF4s2) in "Hword6".
    iDestruct ("Htfback6" with "Hword6") as "Htfp".
    (* ---- the process block CLOSES here, at the new table and size: this is
       the commit.  [upd_exec_compose] is what turns the three successive
       accessor closes into the contract's own one-shot move. ---- *)
    iDestruct (proc_pt_wf_get with "Hpt") as %Hwf.
    pose proof (proc_pt_covered_maxsz P sz1 Hwf Hcov) as Hmaxsz1.
    iSpecialize ("Hprivback" $! P sz1
                   (<[kxc_tf_sp_idx
                      := (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64)]>
                      (<[tf_epc_idx := (Z_to_bv 64 (le_at ef 24 8) : mword 64)]>
                         (<[tf_arg_idx 1
                            := (mword_of_int (kxc_sp_final (uint sz1) alen c)
                                : mword 64)]> (pv_tf V))))).
    iSpecialize ("Hprivback" with "[%]"); [exact HPtfp |].
    iSpecialize ("Hprivback" with "[%]");
      [rewrite uint_unsigned; exact Hmaxsz1 |].
    iSpecialize ("Hprivback" with "[%]"); [exact Hbelow |].
    (* the close wants the trapframe page named through the NEW descriptor;
       [HPtfp] is the equation, and it is the one thing [proc_priv_newspace]
       pins because the trapframe page genuinely does not move. *)
    iEval (rewrite -HPtfp) in "Hptf".
    iEval (rewrite -HPtfp) in "Htfp".
    iDestruct ("Hprivback" with "Hpsz Hppt Hptf Hpt Htfp") as "Hpriv".
    assert (Hpp2fe : add_vec_int (mword_of_int (KXD + 0x2fa) : mword 64) 4
                     = mword_of_int (KXD + 0x2fe)) by pcw.
    iEval (rewrite Hpp2fe) in "Hpc".
    (* ---- +0x2fe: c.mv a1,s10 -- oldsz, for proc_freepagetable ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXD + 0x2fe)) Ra1 Rs10
              F4 (K - 68)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2fe").
    iIntros (CID14 Hs14) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (F5 := <[Regidx Ra1 := regval_into_reg
                   (add_vec zero_reg (F4 !!! Regidx Rs10))]> F4).
    assert (HF5a1 : F5 !!! Regidx Ra1 = pv_sz V).
    { rewrite /F5 upd_eq HF4s10. apply add_vec_zero_l. }
    assert (HF5a0 : F5 !!! Regidx Ra0 = page_base (ud_root (pv_upt V)))
      by (rewrite /F5 upd_ne; [exact HF4a0 | nz]).
    assert (HF5sp : F5 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /F5 upd_ne; [exact HF4sp | nz]).
    assert (HF5s0 : F5 !!! Regidx Rs0 = sp0)
      by (rewrite /F5 upd_ne; [exact HF4s0 | nz]).
    assert (HF5s1 : F5 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
      by (rewrite /F5 upd_ne; [exact HF4s1 | nz]).
    assert (Hpp300 : add_vec_int (mword_of_int (KXD + 0x2fe) : mword 64) 2
                     = mword_of_int (KXD + 0x300)) by pcw.
    iEval (rewrite Hpp300) in "Hpc".
    (* ---- +0x300: jal ra,proc_freepagetable(old table, oldsz) ---- *)
    assert (Htpfp : add_vec (mword_of_int (KXD + 0x300) : mword 64)
                      (sign_extend' 64 (mword_of_int 2084892 : mword 21))
                    = mword_of_int KernelSyms.proc_freepagetable) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXD + 0x300)) Rra
              (mword_of_int 2084892 : mword 21) F5 (K - 68)%nat true
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htpfp; vm_compute; reflexivity)
              with "Hcg Hpc Hi300").
    iIntros (CID15 Hs15) "Hcg Hpc". iEval (rewrite Htpfp) in "Hpc".
    pose (F6 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (KXD + 0x300) : mword 64) 4)]> F5).
    assert (HF6ra : F6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXD + 0x300) : mword 64) 4)
      by (rewrite /F6; apply upd_eq).
    assert (HF6a0 : F6 !!! Regidx Ra0 = page_base (ud_root (pv_upt V)))
      by (rewrite /F6 upd_ne; [exact HF5a0 | nz]).
    assert (HF6a1 : F6 !!! Regidx Ra1 = pv_sz V)
      by (rewrite /F6 upd_ne; [exact HF5a1 | nz]).
    assert (HF6sp : F6 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /F6 upd_ne; [exact HF5sp | nz]).
    assert (HF6s0 : F6 !!! Regidx Rs0 = sp0)
      by (rewrite /F6 upd_ne; [exact HF5s0 | nz]).
    assert (HF6s1 : F6 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
      by (rewrite /F6 upd_ne; [exact HF5s1 | nz]).
    iApply (PFP.wp_proc_freepagetable_sconf ga F6 (pv_upt V) (K - 68)%nat true
              (proc_addr jp) 0%nat true ∅
              ltac:(lia) ltac:(change (2 ^ 31)%Z with 2147483648%Z; lia)
              HF6a0 ltac:(rewrite HF6a1; exact Hszmax)
              ltac:(rewrite HF6a1; exact Hbelold) (locks_below_empty _)
              with "Hcg Hcnt Htext Hpc Hptold Hka").
    iIntros (CID16 Hs16 mr2) "Hcg Hcnt Hpc %Hcsf".
    assert (Hpc304 : ret_pc (F6 !!! Regidx Rra) = mword_of_int (KXD + 0x304))
      by (rewrite HF6ra; pcw).
    iEval (rewrite Hpc304) in "Hpc".
    iPoseProof (kxc_304 with "Htext") as "Hi304".
    iPoseProof (kxc_308 with "Htext") as "Hi308".
    iPoseProof (kxc_30a with "Htext") as "Hi30a".
    iPoseProof (kxc_30c with "Htext") as "Hi30c".
    iPoseProof (kxc_30e with "Htext") as "Hi30e".
    iPoseProof (kxc_310 with "Htext") as "Hi310".
    iPoseProof (kxc_312 with "Htext") as "Hi312".
    iPoseProof (kxc_314 with "Htext") as "Hi314".
    iPoseProof (kxc_316 with "Htext") as "Hi316".
    iPoseProof (kxc_318 with "Htext") as "Hi318".
    iPoseProof (kxc_31a with "Htext") as "Hi31a".
    assert (HG0sp : mr2 !!! Regidx csp_rs1 = pa_stk sp0 68).
    { rewrite (callee_saved_lookup Hcsf csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HF6sp. }
    assert (HG0s1 : mr2 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64)).
    { rewrite (callee_saved_lookup Hcsf Rs1 ltac:(vm_compute; reflexivity)).
      exact HF6s1. }
    (* ---- +0x304: addiw a0,s1,0 -- the return value is argc ---- *)
    iApply (wp_addiw_s_sconf (mword_of_int (KXD + 0x304)) Ra0 Rs1
              (mword_of_int 0 : mword 12) mr2 (K - 68)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi304").
    iIntros (CID17 Hs17) "Hcg Hpc".
    pose (G1 := <[Regidx Ra0 := regval_into_reg
                   (sign_extend' 64 (subrange_vec_dec
                      (add_vec (mr2 !!! Regidx Rs1)
                         (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> mr2).
    assert (HG1a0 : G1 !!! Regidx Ra0 = (mword_of_int (Z.of_nat c) : mword 64)).
    { rewrite /G1 upd_eq HG0s1. apply kxd_addiw_id.
      unfold MAXARG in Hnamax. lia. }
    assert (HG1sp : G1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /G1 upd_ne; [exact HG0sp | nz]).
    assert (Hpp308 : add_vec_int (mword_of_int (KXD + 0x304) : mword 64) 4
                     = mword_of_int (KXD + 0x308)) by pcw.
    iEval (rewrite Hpp308) in "Hpc".
    (* ---- +0x308 .. +0x318: reload s3..s11 from their spill slots ---- *)
    assert (Hpa5 : add_vec (G1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 63 : mword 6) ('b"000")))
                   = pa_stk sp0 5) by (rewrite HG1sp; apply kxc_slot5_sp).
    iEval (rewrite -Hpa5) in "Hf5". iEval (rewrite -Hmw5) in "Hf5".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXD + 0x308)) (mword_of_int 63 : mword 6)
              Rs3 G1 (K - 68)%nat (m !!! Regidx Rs3) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi308 Hf5").
    iIntros (CID18 Hs18) "Hcg Hpc Hf5". iEval (rewrite Hpa5) in "Hf5".
    pose (G2 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> G1).
    assert (HG2sp : G2 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /G2 upd_ne; [exact HG1sp | nz]).
    assert (Hpp30a : add_vec_int (mword_of_int (KXD + 0x308) : mword 64) 2
                     = mword_of_int (KXD + 0x30a)) by pcw.
    iEval (rewrite Hpp30a) in "Hpc".
    assert (Hpa6 : add_vec (G2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 62 : mword 6) ('b"000")))
                   = pa_stk sp0 6) by (rewrite HG2sp; apply kxc_slot6_sp).
    iEval (rewrite -Hpa6) in "Hf6". iEval (rewrite -Hmw6) in "Hf6".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXD + 0x30a)) (mword_of_int 62 : mword 6)
              Rs4 G2 (K - 68)%nat (m !!! Regidx Rs4) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi30a Hf6").
    iIntros (CID19 Hs19) "Hcg Hpc Hf6". iEval (rewrite Hpa6) in "Hf6".
    pose (G3 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4)]> G2).
    assert (HG3sp : G3 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /G3 upd_ne; [exact HG2sp | nz]).
    assert (Hpp30c : add_vec_int (mword_of_int (KXD + 0x30a) : mword 64) 2
                     = mword_of_int (KXD + 0x30c)) by pcw.
    iEval (rewrite Hpp30c) in "Hpc".
    assert (Hpa7 : add_vec (G3 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 61 : mword 6) ('b"000")))
                   = pa_stk sp0 7) by (rewrite HG3sp; apply kxc_slot7_sp).
    iEval (rewrite -Hpa7) in "Hf7". iEval (rewrite -Hmw7) in "Hf7".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXD + 0x30c)) (mword_of_int 61 : mword 6)
              Rs5 G3 (K - 68)%nat (m !!! Regidx Rs5) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi30c Hf7").
    iIntros (CID20 Hs20) "Hcg Hpc Hf7". iEval (rewrite Hpa7) in "Hf7".
    pose (G4 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5)]> G3).
    assert (HG4sp : G4 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /G4 upd_ne; [exact HG3sp | nz]).
    assert (Hpp30e : add_vec_int (mword_of_int (KXD + 0x30c) : mword 64) 2
                     = mword_of_int (KXD + 0x30e)) by pcw.
    iEval (rewrite Hpp30e) in "Hpc".
    assert (Hpa8 : add_vec (G4 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 60 : mword 6) ('b"000")))
                   = pa_stk sp0 8) by (rewrite HG4sp; apply kxc_slot8_sp).
    iEval (rewrite -Hpa8) in "Hf8". iEval (rewrite -Hmw8) in "Hf8".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXD + 0x30e)) (mword_of_int 60 : mword 6)
              Rs6 G4 (K - 68)%nat (m !!! Regidx Rs6) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi30e Hf8").
    iIntros (CID21 Hs21) "Hcg Hpc Hf8". iEval (rewrite Hpa8) in "Hf8".
    pose (G5 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6)]> G4).
    assert (HG5sp : G5 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /G5 upd_ne; [exact HG4sp | nz]).
    assert (Hpp310 : add_vec_int (mword_of_int (KXD + 0x30e) : mword 64) 2
                     = mword_of_int (KXD + 0x310)) by pcw.
    iEval (rewrite Hpp310) in "Hpc".
    assert (Hpa9 : add_vec (G5 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 59 : mword 6) ('b"000")))
                   = pa_stk sp0 9) by (rewrite HG5sp; apply kxc_slot9_sp).
    iEval (rewrite -Hpa9) in "Hf9". iEval (rewrite -Hmw9) in "Hf9".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXD + 0x310)) (mword_of_int 59 : mword 6)
              Rs7 G5 (K - 68)%nat (m !!! Regidx Rs7) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi310 Hf9").
    iIntros (CID22 Hs22) "Hcg Hpc Hf9". iEval (rewrite Hpa9) in "Hf9".
    pose (G6 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7)]> G5).
    assert (HG6sp : G6 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /G6 upd_ne; [exact HG5sp | nz]).
    assert (Hpp312 : add_vec_int (mword_of_int (KXD + 0x310) : mword 64) 2
                     = mword_of_int (KXD + 0x312)) by pcw.
    iEval (rewrite Hpp312) in "Hpc".
    assert (Hpa10 : add_vec (G6 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 58 : mword 6) ('b"000")))
                    = pa_stk sp0 10) by (rewrite HG6sp; apply kxc_slot10_sp).
    iEval (rewrite -Hpa10) in "Hf10". iEval (rewrite -Hmw10) in "Hf10".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXD + 0x312)) (mword_of_int 58 : mword 6)
              Rs8 G6 (K - 68)%nat (m !!! Regidx Rs8) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi312 Hf10").
    iIntros (CID23 Hs23) "Hcg Hpc Hf10". iEval (rewrite Hpa10) in "Hf10".
    pose (G7 := <[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8)]> G6).
    assert (HG7sp : G7 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /G7 upd_ne; [exact HG6sp | nz]).
    assert (Hpp314 : add_vec_int (mword_of_int (KXD + 0x312) : mword 64) 2
                     = mword_of_int (KXD + 0x314)) by pcw.
    iEval (rewrite Hpp314) in "Hpc".
    assert (Hpa11 : add_vec (G7 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 57 : mword 6) ('b"000")))
                    = pa_stk sp0 11) by (rewrite HG7sp; apply kxc_slot11_sp).
    iEval (rewrite -Hpa11) in "Hf11". iEval (rewrite -Hmw11) in "Hf11".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXD + 0x314)) (mword_of_int 57 : mword 6)
              Rs9 G7 (K - 68)%nat (m !!! Regidx Rs9) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi314 Hf11").
    iIntros (CID24 Hs24) "Hcg Hpc Hf11". iEval (rewrite Hpa11) in "Hf11".
    pose (G8 := <[Regidx Rs9 := regval_into_reg (m !!! Regidx Rs9)]> G7).
    assert (HG8sp : G8 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /G8 upd_ne; [exact HG7sp | nz]).
    assert (Hpp316 : add_vec_int (mword_of_int (KXD + 0x314) : mword 64) 2
                     = mword_of_int (KXD + 0x316)) by pcw.
    iEval (rewrite Hpp316) in "Hpc".
    assert (Hpa12 : add_vec (G8 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 56 : mword 6) ('b"000")))
                    = pa_stk sp0 12) by (rewrite HG8sp; apply kxc_slot12_sp).
    iEval (rewrite -Hpa12) in "Hf12". iEval (rewrite -Hmw12) in "Hf12".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXD + 0x316)) (mword_of_int 56 : mword 6)
              Rs10 G8 (K - 68)%nat (m !!! Regidx Rs10) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi316 Hf12").
    iIntros (CID25 Hs25) "Hcg Hpc Hf12". iEval (rewrite Hpa12) in "Hf12".
    pose (G9 := <[Regidx Rs10 := regval_into_reg (m !!! Regidx Rs10)]> G8).
    assert (HG9sp : G9 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /G9 upd_ne; [exact HG8sp | nz]).
    assert (Hpp318 : add_vec_int (mword_of_int (KXD + 0x316) : mword 64) 2
                     = mword_of_int (KXD + 0x318)) by pcw.
    iEval (rewrite Hpp318) in "Hpc".
    assert (Hpa13 : add_vec (G9 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 55 : mword 6) ('b"000")))
                    = pa_stk sp0 13) by (rewrite HG9sp; apply kxc_slot13_sp).
    iEval (rewrite -Hpa13) in "Hf13". iEval (rewrite -Hmw13) in "Hf13".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXD + 0x318)) (mword_of_int 55 : mword 6)
              Rs11 G9 (K - 68)%nat (m !!! Regidx Rs11) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi318 Hf13").
    iIntros (CID26 Hs26) "Hcg Hpc Hf13". iEval (rewrite Hpa13) in "Hf13".
    pose (G10 := <[Regidx Rs11 := regval_into_reg (m !!! Regidx Rs11)]> G9).
    assert (HG10sp : G10 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /G10 upd_ne; [exact HG9sp | nz]).
    assert (HG10a0 : G10 !!! Regidx Ra0 = (mword_of_int (Z.of_nat c) : mword 64)).
    { rewrite /G10 upd_ne; [| nz]. rewrite /G9 upd_ne; [| nz].
      rewrite /G8 upd_ne; [| nz]. rewrite /G7 upd_ne; [| nz].
      rewrite /G6 upd_ne; [| nz]. rewrite /G5 upd_ne; [| nz].
      rewrite /G4 upd_ne; [| nz]. rewrite /G3 upd_ne; [| nz].
      rewrite /G2 upd_ne; [| nz]. exact HG1a0. }
    assert (Hpp31a : add_vec_int (mword_of_int (KXD + 0x318) : mword 64) 2
                     = mword_of_int (KXD + 0x31a)) by pcw.
    iEval (rewrite Hpp31a) in "Hpc".
    (* ---- +0x31a: c.j +0x72 -- into the shared epilogue ---- *)
    assert (Htgt72 : add_vec (mword_of_int (KXD + 0x31a) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 1708 : mword 11) ('b"0"))))
                     = mword_of_int (KXD + 0x72)) by pcw.
    iApply (wp_cj_s_sconf (mword_of_int (KXD + 0x31a))
              (sign_extend' 21 (concat_vec (mword_of_int 1708 : mword 11) ('b"0")))
              G10 (K - 68)%nat true
              ltac:(rewrite Htgt72; vm_compute; reflexivity)
              with "Hcg Hpc Hi31a").
    iIntros (CID27 Hs27). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htgt72) in "Hpc".
    (* ---- the threading clause: all NINE came back from THIS block's own
       reload, so [kxc_cs_cases] lands the symbolic [r] on the register each
       case is really about. ---- *)
    assert (HG10thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> G10 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns2.
      destruct (kxc_cs_cases r Hr)
        as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> |
           [-> | [-> | ->]]]]]]]]]]]];
        try (exfalso; congruence).
      - rewrite /G10 upd_ne; [| nz]. rewrite /G9 upd_ne; [| nz]. rewrite /G8 upd_ne; [| nz]. rewrite /G7 upd_ne; [| nz]. rewrite /G6 upd_ne; [| nz]. rewrite /G5 upd_ne; [| nz]. rewrite /G4 upd_ne; [| nz]. rewrite /G3 upd_ne; [| nz]. rewrite /G2; apply upd_eq.
      - rewrite /G10 upd_ne; [| nz]. rewrite /G9 upd_ne; [| nz]. rewrite /G8 upd_ne; [| nz]. rewrite /G7 upd_ne; [| nz]. rewrite /G6 upd_ne; [| nz]. rewrite /G5 upd_ne; [| nz]. rewrite /G4 upd_ne; [| nz]. rewrite /G3; apply upd_eq.
      - rewrite /G10 upd_ne; [| nz]. rewrite /G9 upd_ne; [| nz]. rewrite /G8 upd_ne; [| nz]. rewrite /G7 upd_ne; [| nz]. rewrite /G6 upd_ne; [| nz]. rewrite /G5 upd_ne; [| nz]. rewrite /G4; apply upd_eq.
      - rewrite /G10 upd_ne; [| nz]. rewrite /G9 upd_ne; [| nz]. rewrite /G8 upd_ne; [| nz]. rewrite /G7 upd_ne; [| nz]. rewrite /G6 upd_ne; [| nz]. rewrite /G5; apply upd_eq.
      - rewrite /G10 upd_ne; [| nz]. rewrite /G9 upd_ne; [| nz]. rewrite /G8 upd_ne; [| nz]. rewrite /G7 upd_ne; [| nz]. rewrite /G6; apply upd_eq.
      - rewrite /G10 upd_ne; [| nz]. rewrite /G9 upd_ne; [| nz]. rewrite /G8 upd_ne; [| nz]. rewrite /G7; apply upd_eq.
      - rewrite /G10 upd_ne; [| nz]. rewrite /G9 upd_ne; [| nz]. rewrite /G8; apply upd_eq.
      - rewrite /G10 upd_ne; [| nz]. rewrite /G9; apply upd_eq.
      - rewrite /G10; apply upd_eq. }
    (* ---- the frame, back to [kxc_frame]'s shape ---- *)
    iDestruct (kxc_stack_of_top5 sp0 (pa_add av (8 * c)) w65 (pa_add pv q) w67 w68
                 with "Hf64 Hf65 Hf66 Hf67 Hf68") as "Htop5".
    iDestruct (kxc_elf_give sp0 ef Hal with "Helf") as "Aelf".
    iDestruct (kxc_mid_join sp0 with "Hust Aelf Hph") as "Amid50".
    iAssert (kxc_frame sp0 ra0 s00 s10 s20)
      with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10 Hf11 Hf12 Hf13
             Amid50 Htop5]" as "Hfr".
    { rewrite /kxc_frame.
      iSplitL "Hf1"; [iExact "Hf1" |]. iSplitL "Hf2"; [iExact "Hf2" |].
      iSplitL "Hf3"; [iExact "Hf3" |]. iSplitL "Hf4"; [iExact "Hf4" |].
      iSplitL "Hf5"; [by iExists (m !!! Regidx Rs3) |].
      iSplitL "Hf6"; [by iExists (m !!! Regidx Rs4) |].
      iSplitL "Hf7"; [by iExists (m !!! Regidx Rs5) |].
      iSplitL "Hf8"; [by iExists (m !!! Regidx Rs6) |].
      iSplitL "Hf9"; [by iExists (m !!! Regidx Rs7) |].
      iSplitL "Hf10"; [by iExists (m !!! Regidx Rs8) |].
      iSplitL "Hf11"; [by iExists (m !!! Regidx Rs9) |].
      iSplitL "Hf12"; [by iExists (m !!! Regidx Rs10) |].
      iSplitL "Hf13"; [by iExists (m !!! Regidx Rs11) |].
      change 55%nat with (50 + 5)%nat.
      rewrite stack_own_app (pa_stk_assoc sp0 13 50).
      iSplitL "Amid50"; [iExact "Amid50" | iExact "Htop5"]. }
    iApply (kxc_epi_frame m G10 K sp0 ra0 s00 s10 s20 (proc_addr jp) true
              ltac:(lia) Hmsp Hmra Hms0 Hms1 Hms2 HG10sp HG10thr
              with "Hcg Htext Hpc Hfr").
    iIntros (CIDe Hse mf) "%Hcs %Hpres Hcg Hpc".
    iDestruct (cpu_own_transport CID16 CIDe 0%nat true (proc_addr jp) true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (kxd_priv_exec with "Hpriv") as "Hpriv".
    (* the final [sp] is inside the image's top page, which is [kxc_stack_ok]'s
       lower half and [kxd_sp_final_le_top]'s upper one. *)
    assert (Hspfin_range : (0 <= kxc_sp_final (uint sz1) alen c
                            < 18446744073709551616)%Z).
    { pose proof (kxd_sp_final_le_top (uint sz1) alen c) as Hup.
      pose proof (bv_unsigned_in_range 64 sz1) as Hr.
      rewrite -uint_unsigned in Hr.
      change (bv_modulus 64) with 18446744073709551616%Z in Hr.
      destruct Hstk as [_ Hlo]. lia. }
    assert (Hspu : uint (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64)
                   = kxc_sp_final (uint sz1) alen c).
    { rewrite uint_unsigned moi64_unsigned. unfold bv_wrap. apply Z.mod_small.
      change (bv_modulus 64) with 18446744073709551616%Z. exact Hspfin_range. }
    iSpecialize ("Hcont" $! CIDe with "[%]"); [wp_next_chain |].
    iSpecialize ("Hcont" $! mf used2
              (upd_exec V sz1 P
                 (<[kxc_tf_sp_idx
                    := (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64)]>
                    (<[tf_epc_idx := (Z_to_bv 64 (le_at ef 24 8) : mword 64)]>
                       (<[tf_arg_idx 1
                          := (mword_of_int (kxc_sp_final (uint sz1) alen c)
                              : mword 64)]> (pv_tf V))))
                 (h <$> seq 0 PNAMELEN))
              (Z_to_bv 64 (le_at ef 24 8) : mword 64)
              (mword_of_int (kxc_sp_final (uint sz1) alen c)) sz1).
    iApply ("Hcont" with "[%] [%] Hcg Hcnt Hpc Hbm Hins [%] Hbits Hka Hpriv Hpath
                    Hargv Hargs Hbs Hirs").
    - exact Hcs.
    - apply kxd_kexec_ok; try assumption.
      + rewrite (Hpres Ra0 ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
        exact HG10a0.
      + apply kxd_name_fn_len.
      + rewrite Hspu. destruct Hstk as [_ Hlo]. lia.
      + rewrite Hspu. apply kxd_sp_final_le_top.
    - reflexivity.
  Qed.

(* [kxd_commit] closes its own section: [kxd_phaseD] applies it at the hart
   the scan ended on, and a lemma proved inside a section that fixes [CID0]
   as a Context variable cannot take a [(CID0 := ...)] annotation at all
   ("Wrong argument name CID0"). *)
End KexecDCommit.

Section KexecDMain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

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
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.


  (* [last] starts AT [path], i.e. at offset 0 -- as its OWN lemma, because
     [iEval (rewrite -(pa_add_0 pv)) in "H"] hits durable-notes' inline-split
     trap: the rewrite abstracts over [pv] before the points-to's own evar is
     solved, and fails with "cannot instantiate ?b because pv is not in its
     scope". *)
  Lemma kxd_last_at0 (sp0 pv : mword 64) :
    word_pointsto (pa_stk sp0 66) (DfracOwn 1) pv -∗
    word_pointsto (pa_stk sp0 66) (DfracOwn 1) (pa_add pv 0).
  Proof. rewrite pa_add_0. iIntros "H". iExact "H". Qed.

  (* [c.addi a5,a5,1] at +0x2b8 steps [path] to [path + 1] *)
  Lemma kxd_add_one (p : mword 64) :
    add_vec p (mword_of_int 1 : mword 64) = pa_add p 1.
  Proof. unfold pa_add, add_vec_int. f_equal. Qed.

  (* the [lbu a4,0(a5)] at +0x2b2 reads the path's own byte 0 *)
  Lemma kxd_add_zero (p : mword 64) :
    add_vec p (sign_extend' 64 (mword_of_int 0 : mword 12)) = pa_add p 0.
  Proof.
    unfold pa_add, add_vec_int. f_equal.
  Qed.

  (* =================================================================== *)
  (*  +0x2a6 .. +0x31a -- PHASE D.                                        *)
  (*                                                                      *)
  (*  [c = na] rather than merely [c <= na]: the state carries [avf c = 0] *)
  (*  and the contract carries "every index below [na] is non-null", so    *)
  (*  the two pin the loop's final counter to the argument count -- which  *)
  (*  is what lets the exit quote [alen na] where the state says [alen c]. *)
  (* =================================================================== *)
  Lemma kxd_phaseD
      (jp : nat) (bn : bio_names) (gfs : fs_names) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (size : Z) (used2 : gset Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
      (m M : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (sz1 : mword 64) (c : nat) :
    (K_kexec <= K)%nat ->
    bb_cstr pfun plen ->
    (na < MAXARG)%nat ->
    (8192 <= uint sz1)%Z ->
    (forall i, (i < na)%nat -> avf i <> (mword_of_int 0 : mword 64)) ->
    (forall i, (i < 8)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (54 - i))) 8 = true) ->
    m !!! Regidx csp_rs1 = sp0 -> m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 -> m !!! Regidx Rs1 = s10 -> m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Rs3 = w5 -> m !!! Regidx Rs4 = w6 -> m !!! Regidx Rs5 = w7 ->
    m !!! Regidx Rs6 = w8 -> m !!! Regidx Rs7 = w9 -> m !!! Regidx Rs8 = w10 ->
    m !!! Regidx Rs9 = w11 -> m !!! Regidx Rs10 = w12 -> m !!! Regidx Rs11 = w13 ->
    kernel_text -∗
    kxc_at_2a6 jp bn gfs ga gf cov logstart bmapstart inodestart size used2
               plen pfun na avf alen aslen afun pidv V dqb dqs dqa
               M K sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P (pv_sz V) sz1 c -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
    ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
       (entry spv szv' : mword 64),
        ⌜callee_saved m mf⌝ -∗
        ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
        sie_cap_gpr mf K true (proc_addr jp) -∗
        cpu_own 0 true (proc_addr jp) true ∅ -∗
        pc_is (ret_pc ra0) -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        ⌜used' ⊆ used2⌝ -∗
        bitmap_res gfs bmapstart cov logstart size used' -∗
        kalloc_env ga None -∗
        proc_priv gf (proc_addr jp) pidv V' -∗
        ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
        ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
        ([∗ list] i ∈ seq 0 na,
           [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
        bslots bn 3 -∗
        iref_slots 2 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hcstr Hnamax Hsz1ge Havf_nz Hal Hmsp Hmra Hms0 Hms1 Hms2
           Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13.
    
    iIntros "#Htext Hst Hcont".
    rewrite /kxc_at_2a6.
    iDestruct "Hst" as "((%HMsp & %HMs0 & %HMs1 & %HMs2 & %HMs4 & %HMs5 & %HMs6 &
                          %HMs10) &
                         (%Hcna & %Hcmax & %Havfc & %Hstackok) &
                         (%HPtfp & %Hbelow & %Hcov) &
                         Hpc & Hcg & Hcnt & Hres)".
    assert (Hceq : c = na).
    { destruct (Nat.lt_ge_cases c na) as [Hlt | Hge];
        [exfalso; exact (Havf_nz c Hlt Havfc) | lia]. }
    rewrite /kxc_d_res.
    iDestruct "Hres" as "(Hirs & Hbm & Hins & Hbits & Hbs & #Hka & Hpt & Hpriv &
                          Hpath & Hargv & Hargs & Helf & Hframe)".
    rewrite /kxc_frameB.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9 &
                            Hf10 & Hf11 & Hf12 & Hf13 & Hust & Hph &
                            Hf64 & Hf65e & Hf66 & Hf67 & Hf68e)".
    iDestruct "Hf65e" as (w65) "Hf65". iDestruct "Hf68e" as (w68) "Hf68".
    iPoseProof (kxc_2a6 with "Htext") as "Hi2a6".
    iPoseProof (kxc_2aa with "Htext") as "Hi2aa".
    iPoseProof (kxc_2ae with "Htext") as "Hi2ae".
    iPoseProof (kxc_2b2 with "Htext") as "Hi2b2".
    iPoseProof (kxc_2b6 with "Htext") as "Hi2b6".
    iPoseProof (kxc_2b8 with "Htext") as "Hi2b8".
    iPoseProof (kxc_2ba with "Htext") as "Hi2ba".
    iPoseProof (kxc_2be with "Htext") as "Hi2be".
    (* [pt_node_claim], for the same reason as [kxd_phaseC]'s own commit
       block above: [tf_page_word_upd]'s result is physical-native, and the
       SD instruction here runs through the kernel's own mapping. *)
    iDestruct (proc_priv_tfp_valid with "Hpriv") as %Hpv_valid.
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhw Hcg]".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iPoseProof (pt_node_claim_from_static (ud_tfp (pv_upt V)) Hpv_valid with "Hkmapb") as "#Hptc".
    (* ---- the process block, opened for the FIRST trapframe write ---- *)
    iDestruct (proc_priv_newspace with "Hpriv")
      as "(%Hszmax & %Hbelold & Hpsz & Hppt & Hptf & Hptold & Htfp & Hprivback)".
    iDestruct (kxd_tf_len with "Htfp") as "[%Htflen Htfp]".
    (* ---- +0x2a6: ld a5,88(s5) -- a5 = p->trapframe ---- *)
    assert (Htfaddr : add_vec (M !!! Regidx Rs5)
                        (sign_extend' 64 (mword_of_int 88 : mword 12))
                      = p_trapframe (proc_addr jp))
      by (rewrite HMs5; reflexivity).
    iEval (rewrite -Htfaddr) in "Hptf".
    iApply (wp_ld_s_sconf (mword_of_int (KXD + 0x2a6)) Ra5 Rs5
              (mword_of_int 88 : mword 12) M (K - 68)%nat
              (page_base (ud_tfp (pv_upt V))) true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2a6 Hptf").
    iIntros (CID1 Hs1) "Hcg Hpc Hptf". iEval (rewrite Htfaddr) in "Hptf".
    pose (D1 := <[Regidx Ra5 := regval_into_reg
                   (page_base (ud_tfp (pv_upt V)))]> M).
    assert (HD1a5 : D1 !!! Regidx Ra5 = page_base (ud_tfp (pv_upt V)))
      by (rewrite /D1; apply upd_eq).
    assert (HD1sp : D1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /D1 upd_ne; [exact HMsp | nz]).
    assert (HD1s0 : D1 !!! Regidx Rs0 = sp0)
      by (rewrite /D1 upd_ne; [exact HMs0 | nz]).
    assert (HD1s1 : D1 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
      by (rewrite /D1 upd_ne; [exact HMs1 | nz]).
    assert (HD1s2 : D1 !!! Regidx Rs2
                    = (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64))
      by (rewrite /D1 upd_ne; [exact HMs2 | nz]).
    assert (HD1s4 : D1 !!! Regidx Rs4 = sz1)
      by (rewrite /D1 upd_ne; [exact HMs4 | nz]).
    assert (HD1s5 : D1 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /D1 upd_ne; [exact HMs5 | nz]).
    assert (HD1s6 : D1 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /D1 upd_ne; [exact HMs6 | nz]).
    assert (HD1s10 : D1 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /D1 upd_ne; [exact HMs10 | nz]).
    assert (Hpp2aa : add_vec_int (mword_of_int (KXD + 0x2a6) : mword 64) 4
                     = mword_of_int (KXD + 0x2aa)) by pcw.
    iEval (rewrite Hpp2aa) in "Hpc".
    (* ---- +0x2aa: sd s2,120(a5) -- trapframe->a1 = sp ---- *)
    assert (Hw15 : exists u15, pv_tf V !! tf_arg_idx 1 = Some u15).
    { apply lookup_lt_is_Some_2. rewrite Htflen. unfold TFWORDS, tf_arg_idx. lia. }
    destruct Hw15 as [u15 Hu15].
    iDestruct (tf_page_word_upd_mem _ _ (tf_arg_idx 1) u15
                 ltac:(unfold tf_arg_idx; lia) Hu15 with "Hptc Htfp")
      as "(Hword & Htfback)".
    assert (Haddr120 : add_vec (D1 !!! Regidx Ra5)
                         (sign_extend' 64 (mword_of_int 120 : mword 12))
                       = tf_pa (ud_tfp (pv_upt V)) (8 * Z.of_nat (tf_arg_idx 1))).
    { rewrite HD1a5. apply kxd_tf_addr.
      { unfold tf_arg_idx. lia. }
      unfold tf_arg_idx. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Haddr120) in "Hword".
    iApply (wp_sd_s_sconf (mword_of_int (KXD + 0x2aa)) Rs2 Ra5
              (mword_of_int 120 : mword 12) D1 (K - 68)%nat u15 true
              with "Hcg Hpc Hi2aa Hword").
    iIntros (CID2 Hs2) "Hcg Hpc Hword".
    iEval (rewrite Haddr120) in "Hword".
    iEval (rewrite (rget_ne (CID := CID1) D1 Rs2 ltac:(nz)) HD1s2) in "Hword".
    iDestruct ("Htfback" with "Hword") as "Htfp".
    (* close at the SAME table and size: only the trapframe words moved *)
    (* the accessor's three side conditions are IRIS wands over pure props,
       not Coq arrows, so they go in one [iSpecialize] each. *)
    iSpecialize ("Hprivback" $! (pv_upt V) (pv_sz V)
                   (<[tf_arg_idx 1
                      := (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64)]>
                      (pv_tf V))).
    iSpecialize ("Hprivback" with "[%]"); [reflexivity |].
    iSpecialize ("Hprivback" with "[%]"); [exact Hszmax |].
    iSpecialize ("Hprivback" with "[%]"); [exact Hbelold |].
    iDestruct ("Hprivback" with "Hpsz Hppt Hptf Hptold Htfp") as "Hpriv".
    iDestruct (kxd_priv_close_tf with "Hpriv") as "Hpriv".
    assert (Hpp2ae : add_vec_int (mword_of_int (KXD + 0x2aa) : mword 64) 4
                     = mword_of_int (KXD + 0x2ae)) by pcw.
    iEval (rewrite Hpp2ae) in "Hpc".
    (* ---- +0x2ae: ld a5,-528(s0) -- a5 = last (= path, still) ---- *)
    assert (Hslot66 : add_vec (D1 !!! Regidx Rs0)
                        (sign_extend' 64 (mword_of_int 3568 : mword 12))
                      = pa_stk sp0 66)
      by (rewrite HD1s0; apply kxd_last_slot).
    iEval (rewrite -Hslot66) in "Hf66".
    iApply (wp_ld_s_sconf (mword_of_int (KXD + 0x2ae)) Ra5 Rs0
              (mword_of_int 3568 : mword 12) D1 (K - 68)%nat pv true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2ae Hf66").
    iIntros (CID3 Hs3) "Hcg Hpc Hf66". iEval (rewrite Hslot66) in "Hf66".
    pose (D2 := <[Regidx Ra5 := regval_into_reg pv]> D1).
    assert (HD2a5 : D2 !!! Regidx Ra5 = pv) by (rewrite /D2; apply upd_eq).
    assert (HD2sp : D2 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /D2 upd_ne; [exact HD1sp | nz]).
    assert (HD2s0 : D2 !!! Regidx Rs0 = sp0)
      by (rewrite /D2 upd_ne; [exact HD1s0 | nz]).
    assert (HD2s1 : D2 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
      by (rewrite /D2 upd_ne; [exact HD1s1 | nz]).
    assert (HD2s2 : D2 !!! Regidx Rs2
                    = (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64))
      by (rewrite /D2 upd_ne; [exact HD1s2 | nz]).
    assert (HD2s4 : D2 !!! Regidx Rs4 = sz1)
      by (rewrite /D2 upd_ne; [exact HD1s4 | nz]).
    assert (HD2s5 : D2 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /D2 upd_ne; [exact HD1s5 | nz]).
    assert (HD2s6 : D2 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /D2 upd_ne; [exact HD1s6 | nz]).
    assert (HD2s10 : D2 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /D2 upd_ne; [exact HD1s10 | nz]).
    assert (Hpp2b2 : add_vec_int (mword_of_int (KXD + 0x2ae) : mword 64) 4
                     = mword_of_int (KXD + 0x2b2)) by pcw.
    iEval (rewrite Hpp2b2) in "Hpc".
    (* ---- +0x2b2: lbu a4,0(a5) -- path[0] ---- *)
    assert (Hlk0 : seq 0 (S plen) !! 0%nat = Some 0%nat)
      by (rewrite (lookup_seq_lt 0 (S plen) 0 ltac:(lia)); reflexivity).
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat Hlk0 with "Hpath")
      as "[Hbyte0 Hpathback]".
    assert (Haddr0 : add_vec (D2 !!! Regidx Ra5)
                       (sign_extend' 64 (mword_of_int 0 : mword 12))
                     = pa_add pv 0)
      by (rewrite HD2a5; apply kxd_add_zero).
    iEval (rewrite -Haddr0) in "Hbyte0".
    iApply (wp_lbu_s_sconf (mword_of_int (KXD + 0x2b2)) Ra4 Ra5
              (mword_of_int 0 : mword 12) D2 (K - 68)%nat (pfun 0%nat) true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2b2 Hbyte0").
    iIntros (CID4 Hs4) "Hcg Hpc Hbyte0". iEval (rewrite Haddr0) in "Hbyte0".
    iDestruct ("Hpathback" with "Hbyte0") as "Hpath".
    pose (D3 := <[Regidx Ra4 := regval_into_reg
                   (zero_extend' 64 (pfun 0%nat : mword 8) : mword 64)]> D2).
    assert (HD3a4 : D3 !!! Regidx Ra4 = (zero_extend' 64 (pfun 0%nat : mword 8) : mword 64))
      by (rewrite /D3; apply upd_eq).
    assert (HD3a5 : D3 !!! Regidx Ra5 = pv)
      by (rewrite /D3 upd_ne; [exact HD2a5 | nz]).
    assert (HD3sp : D3 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /D3 upd_ne; [exact HD2sp | nz]).
    assert (HD3s0 : D3 !!! Regidx Rs0 = sp0)
      by (rewrite /D3 upd_ne; [exact HD2s0 | nz]).
    assert (HD3s1 : D3 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
      by (rewrite /D3 upd_ne; [exact HD2s1 | nz]).
    assert (HD3s2 : D3 !!! Regidx Rs2
                    = (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64))
      by (rewrite /D3 upd_ne; [exact HD2s2 | nz]).
    assert (HD3s4 : D3 !!! Regidx Rs4 = sz1)
      by (rewrite /D3 upd_ne; [exact HD2s4 | nz]).
    assert (HD3s5 : D3 !!! Regidx Rs5 = proc_addr jp)
      by (rewrite /D3 upd_ne; [exact HD2s5 | nz]).
    assert (HD3s6 : D3 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /D3 upd_ne; [exact HD2s6 | nz]).
    assert (HD3s10 : D3 !!! Regidx Rs10 = pv_sz V)
      by (rewrite /D3 upd_ne; [exact HD2s10 | nz]).
    (* the resource bundle the commit takes, assembled once and used by both
       arms of the [beqz] below *)
    iAssert (∀ (last : mword 64),
               word_pointsto (pa_stk sp0 66) (DfracOwn 1) last -∗
               ([∗ list] k ∈ seq 0 (S plen), pa_add pv k ↦ₘ pfun k) -∗
               kxd_res jp bn gfs ga gf cov logstart bmapstart inodestart size
                       used2 plen pfun na avf aslen afun pidv
                       (upd_tf V (<[tf_arg_idx 1
                                    := (mword_of_int
                                          (kxc_sp_final (uint sz1) alen c)
                                        : mword 64)]> (pv_tf V)))
                       dqb dqs dqa sp0 ra0 s00 s10 s20 pv av
                       w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P c last)%I
      with "[Hirs Hbm Hins Hbits Hbs Hpt Hpriv Hargv Hargs Helf
             Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10 Hf11 Hf12 Hf13
             Hust Hph Hf64 Hf65 Hf67 Hf68]" as "Hmk".
    { iIntros (last) "Hf66 Hpath". rewrite /kxd_res /kxc_frameB.
      iSplitL "Hirs"; [iExact "Hirs" |]. iSplitL "Hbm"; [iExact "Hbm" |].
      iSplitL "Hins"; [iExact "Hins" |]. iSplitL "Hbits"; [iExact "Hbits" |].
      iSplitL "Hbs"; [iExact "Hbs" |]. iSplitL "Hpt"; [iExact "Hpt" |].
      iSplitL "Hpriv"; [iExact "Hpriv" |]. iSplitL "Hpath"; [iExact "Hpath" |].
      iSplitL "Hargv"; [iExact "Hargv" |]. iSplitL "Hargs"; [iExact "Hargs" |].
      iSplitL "Helf"; [iExact "Helf" |].
      iSplitL "Hf1"; [iExact "Hf1" |]. iSplitL "Hf2"; [iExact "Hf2" |].
      iSplitL "Hf3"; [iExact "Hf3" |]. iSplitL "Hf4"; [iExact "Hf4" |].
      iSplitL "Hf5"; [iExact "Hf5" |]. iSplitL "Hf6"; [iExact "Hf6" |].
      iSplitL "Hf7"; [iExact "Hf7" |]. iSplitL "Hf8"; [iExact "Hf8" |].
      iSplitL "Hf9"; [iExact "Hf9" |]. iSplitL "Hf10"; [iExact "Hf10" |].
      iSplitL "Hf11"; [iExact "Hf11" |]. iSplitL "Hf12"; [iExact "Hf12" |].
      iSplitL "Hf13"; [iExact "Hf13" |]. iSplitL "Hust"; [iExact "Hust" |].
      iSplitL "Hph"; [iExact "Hph" |]. iSplitL "Hf64"; [iExact "Hf64" |].
      iSplitL "Hf65"; [iExists w65; iExact "Hf65" |].
      iSplitL "Hf66"; [iExact "Hf66" |]. iSplitL "Hf67"; [iExact "Hf67" |].
      iExists w68. iExact "Hf68". }
    assert (Hcreg2b6 : creg2reg_idx (Cregidx (mword_of_int 6)) = Regidx Ra4)
      by (vm_compute; reflexivity).
    assert (Htgt2d2a : add_vec (mword_of_int (KXD + 0x2b6) : mword 64)
                         (sign_extend' 64 (sign_extend' 13
                            (concat_vec (mword_of_int 14 : mword 8) ('b"0"))))
                       = mword_of_int (KXD + 0x2d2)) by pcw.
    destruct (decide (pfun 0%nat = (mword_of_int 0 : mword 8))) as [Hz0 | Hnz0].
    - (* ==== the path is EMPTY: [last] stays at [path] ==== *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KXD + 0x2b6))
                (mword_of_int 14 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                D3 (K - 68)%nat true Hcreg2b6 ltac:(nz)
                ltac:(rewrite (rget_ne D3 Ra4 ltac:(nz)) HD3a4 Hz0;
                      vm_compute; reflexivity)
                ltac:(rewrite Htgt2d2a; vm_compute; reflexivity)
                with "Hcg Hpc Hi2b6").
      iIntros (CID5 Hs5). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt2d2a) in "Hpc".
      iDestruct (kxd_last_at0 with "Hf66") as "Hf66".
      iDestruct ("Hmk" $! (pa_add pv 0) with "Hf66 Hpath") as "Hres".
      iDestruct (cpu_own_transport CID0 CID5 0%nat true (proc_addr jp) true
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      assert (Hcr5 : true = false \/ proc_addr jp = zero_reg ->
                      (CID5 : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_retarget CID0 CID5 true (proc_addr jp) _ Hcr5
                   with "Hcont") as "Hcont".
      iApply (kxd_commit (CID0 := CID5) jp bn gfs ga gf cov logstart bmapstart
                inodestart size used2 plen pfun na avf alen aslen afun pidv V
                dqb dqs dqa m D3 K sp0 ra0 s00 s10 s20 pv av
                w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P sz1 c 0%nat
                ltac:(lia) Hcstr ltac:(lia) Hnamax Hsz1ge Hceq
                ltac:(rewrite -Hceq; exact Hstackok) HPtfp Hbelow Hcov Hal
                Hmsp Hmra Hms0 Hms1 Hms2
                Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13
                HD3sp HD3s0 HD3s1 HD3s2 HD3s4 HD3s5 HD3s6 HD3s10
                with "Htext Hpc Hcg Hcnt Hka Hres Hcont").
    - (* ==== the path is non-empty: run the scan from index 0 ==== *)
      assert (H0plen : (0 < plen)%nat).
      { destruct Hcstr as [_ Hnul].
        destruct (Nat.eq_dec plen 0) as [Hp0 | Hp0]; [| lia].
        exfalso. apply Hnz0. rewrite Hp0 in Hnul. exact Hnul. }
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KXD + 0x2b6))
                (mword_of_int 14 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                D3 (K - 68)%nat true Hcreg2b6 ltac:(nz)
                ltac:(rewrite (rget_ne D3 Ra4 ltac:(nz)) HD3a4;
                      apply kxd_eq_vec64_false;
                      intro Heq; apply Hnz0;
                      apply (proj1 (kxd_zext8_zero (pfun 0%nat)));
                      rewrite Heq; apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi2b6").
      iIntros (CID5 Hs5) "Hcg Hpc".
      assert (Hpp2b8 : add_vec_int (mword_of_int (KXD + 0x2b6) : mword 64) 2
                       = mword_of_int (KXD + 0x2b8)) by pcw.
      iEval (rewrite Hpp2b8) in "Hpc".
      (* ---- +0x2b8: c.addi a5,a5,1 ---- *)
      iApply (wp_caddi_s_sconf (mword_of_int (KXD + 0x2b8)) Ra5
                (mword_of_int 1 : mword 6) D3 (K - 68)%nat true
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2b8").
      iIntros (CID6 Hs6) "Hcg Hpc".
      pose (D4 := <[Regidx Ra5 := regval_into_reg
                     (add_vec (rget D3 Ra5)
                        (sign_extend' 64 (sign_extend' 12
                           (mword_of_int 1 : mword 6))))]> D3).
      assert (Hse1 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
                      : mword 64) = mword_of_int 1)
        by (apply bv_eq; vm_compute; reflexivity).
      assert (HD4a5 : D4 !!! Regidx Ra5 = pa_add pv 1).
      { rewrite /D4 upd_eq (rget_ne D3 Ra5 ltac:(nz)) HD3a5 Hse1.
        apply kxd_add_one. }
      assert (HD4a4 : D4 !!! Regidx Ra4
                      = (zero_extend' 64 (pfun 0%nat : mword 8) : mword 64))
        by (rewrite /D4 upd_ne; [exact HD3a4 | nz]).
      assert (HD4sp : D4 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /D4 upd_ne; [exact HD3sp | nz]).
      assert (HD4s0 : D4 !!! Regidx Rs0 = sp0)
        by (rewrite /D4 upd_ne; [exact HD3s0 | nz]).
      assert (HD4s1 : D4 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
        by (rewrite /D4 upd_ne; [exact HD3s1 | nz]).
      assert (HD4s2 : D4 !!! Regidx Rs2
                      = (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64))
        by (rewrite /D4 upd_ne; [exact HD3s2 | nz]).
      assert (HD4s4 : D4 !!! Regidx Rs4 = sz1)
        by (rewrite /D4 upd_ne; [exact HD3s4 | nz]).
      assert (HD4s5 : D4 !!! Regidx Rs5 = proc_addr jp)
        by (rewrite /D4 upd_ne; [exact HD3s5 | nz]).
      assert (HD4s6 : D4 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /D4 upd_ne; [exact HD3s6 | nz]).
      assert (HD4s10 : D4 !!! Regidx Rs10 = pv_sz V)
        by (rewrite /D4 upd_ne; [exact HD3s10 | nz]).
      assert (Hpp2ba : add_vec_int (mword_of_int (KXD + 0x2b8) : mword 64) 2
                       = mword_of_int (KXD + 0x2ba)) by pcw.
      iEval (rewrite Hpp2ba) in "Hpc".
      (* ---- +0x2ba: addi a3,zero,47 -- the '/' the scan compares against ---- *)
      iApply (wp_li4_s_sconf (mword_of_int (KXD + 0x2ba)) Ra3
                (mword_of_int 47 : mword 12) (mword_of_int 47 : mword 64)
                D4 (K - 68)%nat true ltac:(nz) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi2ba").
      iIntros (CID7 Hs7) "Hcg Hpc".
      pose (D5 := <[Regidx Ra3 := regval_into_reg
                     (mword_of_int 47 : mword 64)]> D4).
      assert (HD5a3 : D5 !!! Regidx Ra3 = (mword_of_int 47 : mword 64))
        by (rewrite /D5; apply upd_eq).
      assert (HD5a4 : D5 !!! Regidx Ra4
                      = (zero_extend' 64 (pfun 0%nat : mword 8) : mword 64))
        by (rewrite /D5 upd_ne; [exact HD4a4 | nz]).
      assert (HD5a5 : D5 !!! Regidx Ra5 = pa_add pv 1)
        by (rewrite /D5 upd_ne; [exact HD4a5 | nz]).
      assert (HD5sp : D5 !!! Regidx csp_rs1 = pa_stk sp0 68)
        by (rewrite /D5 upd_ne; [exact HD4sp | nz]).
      assert (HD5s0 : D5 !!! Regidx Rs0 = sp0)
        by (rewrite /D5 upd_ne; [exact HD4s0 | nz]).
      assert (HD5s1 : D5 !!! Regidx Rs1 = (mword_of_int (Z.of_nat c) : mword 64))
        by (rewrite /D5 upd_ne; [exact HD4s1 | nz]).
      assert (HD5s2 : D5 !!! Regidx Rs2
                      = (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64))
        by (rewrite /D5 upd_ne; [exact HD4s2 | nz]).
      assert (HD5s4 : D5 !!! Regidx Rs4 = sz1)
        by (rewrite /D5 upd_ne; [exact HD4s4 | nz]).
      assert (HD5s5 : D5 !!! Regidx Rs5 = proc_addr jp)
        by (rewrite /D5 upd_ne; [exact HD4s5 | nz]).
      assert (HD5s6 : D5 !!! Regidx Rs6 = page_base P.(ud_root))
        by (rewrite /D5 upd_ne; [exact HD4s6 | nz]).
      assert (HD5s10 : D5 !!! Regidx Rs10 = pv_sz V)
        by (rewrite /D5 upd_ne; [exact HD4s10 | nz]).
      assert (Hpp2be : add_vec_int (mword_of_int (KXD + 0x2ba) : mword 64) 4
                       = mword_of_int (KXD + 0x2be)) by pcw.
      iEval (rewrite Hpp2be) in "Hpc".
      (* ---- +0x2be: c.j +0x2c8 -- into the scan's head ---- *)
      assert (Htgt2c8 : add_vec (mword_of_int (KXD + 0x2be) : mword 64)
                          (sign_extend' 64 (sign_extend' 21
                             (concat_vec (mword_of_int 5 : mword 11) ('b"0"))))
                        = mword_of_int (KXD + 0x2c8)) by pcw.
      iPoseProof (kxc_2be with "Htext") as "Hi2be'".
      iApply (wp_cj_s_sconf (mword_of_int (KXD + 0x2be))
                (sign_extend' 21 (concat_vec (mword_of_int 5 : mword 11) ('b"0")))
                D5 (K - 68)%nat true
                ltac:(rewrite Htgt2c8; vm_compute; reflexivity)
                with "Hcg Hpc Hi2be'").
      iIntros (CID8 Hs8). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt2c8) in "Hpc".
      iDestruct (kxd_last_at0 with "Hf66") as "Hf66".
      iApply (kxd_name_loop (CID0 := CID8) (proc_addr jp) true (K - 68)%nat
                plen pfun sp0 pv (pa_stk sp0 68)
                (mword_of_int (Z.of_nat c) : mword 64)
                (mword_of_int (kxc_sp_final (uint sz1) alen c) : mword 64)
                sz1 (proc_addr jp) (page_base P.(ud_root)) (pv_sz V)
                Hcstr plen D5 0%nat 0%nat ltac:(lia) H0plen ltac:(lia)
                HD5sp HD5s0 HD5s1 HD5s2 HD5s4 HD5s5 HD5s6 HD5s10 HD5a3 HD5a4 HD5a5
                with "Htext Hpc Hcg Hpath Hf66").
      iIntros (CID9 Hs9 Mf q') "%Hpres Hpc Hcg Hpath Hf66".
      destruct Hpres as (Hq' & Hfsp & Hfs0 & Hfs1 & Hfs2 & Hfs4 & Hfs5 & Hfs6 & Hfs10).
      iDestruct ("Hmk" $! (pa_add pv q') with "Hf66 Hpath") as "Hres".
      iDestruct (cpu_own_transport CID0 CID9 0%nat true (proc_addr jp) true
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      assert (Hcr9 : true = false \/ proc_addr jp = zero_reg ->
                      (CID9 : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_retarget CID0 CID9 true (proc_addr jp) _ Hcr9
                   with "Hcont") as "Hcont".
      iApply (kxd_commit (CID0 := CID9) jp bn gfs ga gf cov logstart bmapstart
                inodestart size used2 plen pfun na avf alen aslen afun pidv V
                dqb dqs dqa m Mf K sp0 ra0 s00 s10 s20 pv av
                w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P sz1 c q'
                ltac:(lia) Hcstr Hq' Hnamax Hsz1ge Hceq
                ltac:(rewrite -Hceq; exact Hstackok) HPtfp Hbelow Hcov Hal
                Hmsp Hmra Hms0 Hms1 Hms2
                Hmw5 Hmw6 Hmw7 Hmw8 Hmw9 Hmw10 Hmw11 Hmw12 Hmw13
                Hfsp Hfs0 Hfs1 Hfs2 Hfs4 Hfs5 Hfs6 Hfs10
                with "Htext Hpc Hcg Hcnt Hka Hres Hcont").
  Qed.

End KexecDMain.

End KexecDProof.
