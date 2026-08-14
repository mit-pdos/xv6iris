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
Require Import KernelRvcDecode.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeHalf.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import SleepLock.
Require Import WpLock.
Require Import PanicStub.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import FsCrash.
Require Import InodeRegion.
Require Import IcacheEscrow.
Require Import ByteBuf.
Require Import VcGen.
Require Import W32Arith.
Require Import ElfEnc.
Require Import PageGeom.
Require Import ProcGeom.
Require Import ProcInv.
Require Import DiskPtsto.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import DirentEnc.
Require Import PathElems.
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
Require Import SchedCtx.
Require Import DiskInv.
Require Import PtTree.
Require Import PtBuild.
Require Import ProcPt.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import UmCovered.
Require Import FileInv.
Require Import SpecKexec.
Require Import SpecProcFreepagetable.
Require Import SpecSafestrcpy.
Require Import ProofKexecParts.
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
     12-bit displacement against [a_tf_word]'s [8*i] indexing. *)
  Lemma kxd_tf_addr (tfp : mword 44) (z : Z) (i : nat) :
    (sign_extend' 64 (mword_of_int z : mword 12) : mword 64)
      = mword_of_int (8 * Z.of_nat i) ->
    add_vec (page_base tfp) (sign_extend' 64 (mword_of_int z : mword 12))
    = a_tf_word tfp i.
  Proof.
    intro Hz. rewrite Hz /a_tf_word /pa_add /add_vec_int.
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
    upd_sz (upd_pt (upd_name (upd_sz (upd_pt V (pv_upt V) ws1) (pv_sz V)) ns)
                   P' ws3) szv
    = upd_exec V szv P' ws3 ns.
  Proof. by destruct V. Qed.

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
         (<[tf_epc_idx := entry]>
            (<[kxc_tf_sp_idx
               := (mword_of_int (kxc_sp_final (uint sz1) alen na) : mword 64)]>
               (<[tf_arg_idx 1
                  := (mword_of_int (kxc_sp_final (uint sz1) alen na) : mword 64)]>
                  (pv_tf V))))
         ns)
      r entry (mword_of_int (kxc_sp_final (uint sz1) alen na)) sz1 na alen.
  Proof.
    intros Hr Hna Hstk Htfp Hns Hlo Hhi. right.
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
      (m M : regfile) (K : nat) (C : iProp Σ)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (sz1 : mword 64) (c q : nat) :
    (K_kexec <= K)%nat ->
    bb_cstr pfun plen ->
    (q <= plen)%nat ->
    (na < MAXARG)%nat ->
    c = na ->
    kxc_stack_ok (uint sz1) (uint sz1 - 4096) alen na ->
    ud_tfp P = ud_tfp (pv_upt V) ->
    um_below sz1 P.(ud_um) -> um_covered sz1 P.(ud_um) ->
    (forall i, (i < 8)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (54 - i))) 8 = true) ->
    m !!! Regidx csp_rs1 = sp0 -> m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 -> m !!! Regidx Rs1 = s10 -> m !!! Regidx Rs2 = s20 ->
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
    cpu_own 0 true (proc_addr jp) C true ∅ -∗
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
        cpu_own 0 true (proc_addr jp) C true ∅ -∗
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
  Admitted.

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
      (m M : regfile) (K : nat) (C : iProp Σ)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (sz1 : mword 64) (c : nat) :
    (K_kexec <= K)%nat ->
    bb_cstr pfun plen ->
    (na < MAXARG)%nat ->
    (forall i, (i < na)%nat -> avf i <> (mword_of_int 0 : mword 64)) ->
    (forall i, (i < 8)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (54 - i))) 8 = true) ->
    m !!! Regidx csp_rs1 = sp0 -> m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 -> m !!! Regidx Rs1 = s10 -> m !!! Regidx Rs2 = s20 ->
    kernel_text -∗
    kxc_at_2a6 jp bn gfs ga gf cov logstart bmapstart inodestart size used2
               plen pfun na avf alen aslen afun pidv V dqb dqs dqa
               M K C sp0 ra0 s00 s10 s20 pv av
               w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P (pv_sz V) sz1 c -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
    ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
       (entry spv szv' : mword 64),
        ⌜callee_saved m mf⌝ -∗
        ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
        sie_cap_gpr mf K true (proc_addr jp) -∗
        cpu_own 0 true (proc_addr jp) C true ∅ -∗
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
    intros HK Hcstr Hnamax Havf_nz Hal Hmsp Hmra Hms0 Hms1 Hms2.
    unfold K_kexec in HK.
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
    iDestruct (tf_page_word_upd _ _ (tf_arg_idx 1) u15 Hu15 with "Htfp")
      as "(Hword & Htfback)".
    assert (Haddr120 : add_vec (D1 !!! Regidx Ra5)
                         (sign_extend' 64 (mword_of_int 120 : mword 12))
                       = a_tf_word (ud_tfp (pv_upt V)) (tf_arg_idx 1)).
    { rewrite HD1a5. apply kxd_tf_addr.
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
      iDestruct (cpu_own_transport CID0 CID5 0%nat true (proc_addr jp) C true
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      assert (Hcr5 : true = false \/ proc_addr jp = zero_reg ->
                      (CID5 : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_retarget CID0 CID5 true (proc_addr jp) _ Hcr5
                   with "Hcont") as "Hcont".
      iApply (kxd_commit (CID0 := CID5) jp bn gfs ga gf cov logstart bmapstart
                inodestart size used2 plen pfun na avf alen aslen afun pidv V
                dqb dqs dqa m D3 K C sp0 ra0 s00 s10 s20 pv av
                w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P sz1 c 0%nat
                ltac:(unfold K_kexec; lia) Hcstr ltac:(lia) Hnamax Hceq
                ltac:(rewrite -Hceq; exact Hstackok) HPtfp Hbelow Hcov Hal
                Hmsp Hmra Hms0 Hms1 Hms2
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
      iDestruct (cpu_own_transport CID0 CID9 0%nat true (proc_addr jp) C true
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      assert (Hcr9 : true = false \/ proc_addr jp = zero_reg ->
                      (CID9 : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_retarget CID0 CID9 true (proc_addr jp) _ Hcr9
                   with "Hcont") as "Hcont".
      iApply (kxd_commit (CID0 := CID9) jp bn gfs ga gf cov logstart bmapstart
                inodestart size used2 plen pfun na avf alen aslen afun pidv V
                dqb dqs dqa m Mf K C sp0 ra0 s00 s10 s20 pv av
                w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ef P sz1 c q'
                ltac:(unfold K_kexec; lia) Hcstr Hq' Hnamax Hceq
                ltac:(rewrite -Hceq; exact Hstackok) HPtfp Hbelow Hcov Hal
                Hmsp Hmra Hms0 Hms1 Hms2
                Hfsp Hfs0 Hfs1 Hfs2 Hfs4 Hfs5 Hfs6 Hfs10
                with "Htext Hpc Hcg Hcnt Hka Hres Hcont").
  Qed.

End KexecDMain.

End KexecDProof.
