(* ProofCopyinstr.v -- copyinstr() over the SIE-agnostic sconf world.

     int copyinstr(pagetable_t pagetable, char *dst, uint64 srcva, uint64 max) {
       int got_null = 0;
       while (got_null == 0 && max > 0) {
         va0 = PGROUNDDOWN(srcva);
         pa0 = walkaddr(pagetable, va0);
         if (pa0 == 0) return -1;
         n = PGSIZE - (srcva - va0);  if (n > max) n = max;
         char *p = (char * )(pa0 + (srcva - va0));
         while (n > 0) {
           if ( *p == '\0') { *dst = '\0'; got_null = 1; break; }
           else *dst = *p;
           --n; --max; p++; dst++;
         }
         srcva = va0 + PGSIZE;
       }
       return got_null ? 0 : -1;
     }

   Contract: SpecCopyinstr.v.  The THIRD member of the copyin family and the
   only one with two nested loops; walkaddr is its only callee, so unlike
   copyin there is no vmfault tier, no [kalloc_env], no [cpu_own] and no
   [uptd_ext] -- the descriptor that goes in is the descriptor that comes out,
   and [ProcPtOwn.proc_pt_acc_rep0] / [proc_pt_rebuild] / [proc_pt_page_acc]
   are the only table lemmas in the file.

   THE MACHINE (offsets into CodeCopyinstr.v's byte-verified listing):

     +0x00 beqz a3,+0xb0          max == 0: return -1 with NO frame
     +0x02..+0x16                 the 80-byte (10-slot) prologue
     +0x18..+0x22                 s5=pagetable s1=dst s7=srcva s3=max
                                  s6=-4096 s4=4096
     +0x24 j +0x5e                enter the OUTER loop at its head

     +0x5e and s2,s7,s6           va0 = PGROUNDDOWN(srcva)   <-- outer head
     +0x66 jal walkaddr(s5,s2)
     +0x6a beqz a0 -> +0xa4       unmapped: return -1
     +0x6c..+0x76                 n = min(4096 - off, rem)
     +0x78 beqz a3 -> +0xa8       DEAD: n >= 1 always
     +0x7a..+0x86                 a2 = p - dst, a5 = dst, a3 = dst + n

     +0x88 mv a1,a5               <-- INNER head, one byte per iteration
     +0x8e lbu a4,0(a4)
     +0x92 beqz a4 -> +0x26       the NUL: plant it and return 0
     +0x94..+0x98                 *dst = *p ; dst++
     +0x9a bne a5,a3 -> +0x88     more of this chunk
     +0x9e j +0x4a                the chunk is done

     +0x4a..+0x58                 max -= n, srcva = va0 + 4096, and
                                  beq a1,a4 -> +0xa0 when max hit 0
     +0x5c mv s1,a5               dst += n, fall through to the outer head

     +0x26..+0x30                 *dst = 0 ; got_null = 1 ; a0 = 0
     +0xa0..+0x30                 got_null = 0 ; a0 = -1
     +0x34..+0x48                 the 10-slot epilogue, all three
                                  frame-holding exits
     +0xb0..+0xba                 the frameless max == 0 return

   FIVE THINGS WORTH KEEPING.

   1. THE BUFFER IS NEVER SPLIT.  copyin carves its destination into
      prefix/chunk/suffix each iteration and rejoins with [bb_join3], which
      returns an EXISTENTIAL naming function -- fine there, because copyin's
      postcondition says nothing about the bytes.  copyinstr's does
      ([bb_cstr]), so an existential would throw away exactly what has to be
      proved.  Instead the destination is carried WHOLE and touched one index
      at a time through [ByteBuf.bb_byte_acc], with the naming function
      updated by [bb_upd]; [bb_nonul f (done + i)] is then a plain invariant
      on that function.  The SOURCE page is still split (it is read-only and
      unnamed in the postcondition), so [bb_split3]/[bb_join3] stay.

   2. THE INNER LOOP INDEXES OFF THE CHUNK BASE, the outer off the buffer
      base.  gcc keeps [a2 = p - dst_base] and forms each source address as
      [a2 + cursor], so the base cancels ([ByteCursor.pa_add_delta]); the
      cursor itself is [pa_add dstb i], and [pa_add_assoc] is what carries it
      back to the caller's [pa_add dst (done + i)] indexing whenever the
      destination resource is touched.

   3. THE OUTER LOOP'S COUNTER IS RECOVERED FROM TWO POINTERS.  There is no
      [max] register left at +0x4a: gcc rebuilds [max - n] as
      [(dst_base + (max-1)) - (dst_base + (n-1))] and tests exhaustion with
      [beq] on those same two pointers.  [pa_add_diff] and [pa_add_eqb] are
      those two readings, and both are wrap-free for any indices below 2^64.

   4. FUEL INDUCTION on the outer loop (the measure drops by [n], not by 1)
      and a plain [nat] induction on the inner one (it drops by exactly 1).
      The inner loop's back edge is a TAKEN [bne], so its IH is used under an
      [iNext].

   5. +0x78 IS DEAD and is discharged, not decoded away: [n = min(4096-off,
      rem)] with [off < 4096] and [rem >= 1] is never 0, so the [c.beqz] falls
      through and the four instructions at +0xa8 are never reached. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import CalleeSaved StackOwn.
Require Import IntrDefs WpSmodeIntr.
Require Import HartTp WpNext WpSconfVc.
Require Import ByteCursor ByteBuf.
Require Import PtreeType.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import CodeCopyinstr.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecWalkaddr.
Require Import SpecCopyinstr.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Import Defs.
Local Open Scope Z_scope.
Set Printing Depth 40.

(* ===================================================================== *)
(* Pure arithmetic.                                                       *)
(* ===================================================================== *)

(* the 80-byte frame: BOTH ends are [c.addi16sp]. *)
Lemma cs_push (X : mword 64) :
  add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) = pa_stk X 10.
Proof.
  unfold pa_stk, add_vec_int. apply f_equal.
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma cs_pop (X : mword 64) :
  add_vec (pa_stk X 10) (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))) = X.
Proof.
  rewrite <- cs_push. apply frame_cancel.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* the page offset as a [nat] (copyin's [ci_off_id] / [ci_off_lt]) -- kept
   here too so this file needs no dependency on ProofCopyin. *)
Lemma cs_off_id (z : Z) : Z.of_nat (Z.to_nat (z mod 4096)) = (z mod 4096)%Z.
Proof. rewrite Z2Nat.id; [reflexivity | apply Z.mod_pos_bound; lia]. Qed.

Lemma cs_off_lt (z : Z) : (Z.to_nat (z mod 4096) < 4096)%nat.
Proof. pose proof (Z.mod_pos_bound z 4096 ltac:(lia)) as [H1 H2]. lia. Qed.

(* the two [negw a0,a5] outcomes, as closed literals *)
Lemma cs_negw_0 :
  sign_extend' 64 (sub_vec (subrange_vec_dec (zero_reg : mword 64) 31 0 : mword 32)
                     (subrange_vec_dec (mword_of_int 0 : mword 64) 31 0 : mword 32))
  = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma cs_negw_1 :
  sign_extend' 64 (sub_vec (subrange_vec_dec (zero_reg : mword 64) 31 0 : mword 32)
                     (subrange_vec_dec (mword_of_int 1 : mword 64) 31 0 : mword 32))
  = (mword_of_int (-1) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* [xori a5,a5,1] on the two values got_null ever holds *)
Lemma cs_xor_0 :
  xor_vec (mword_of_int 0 : mword 64) (sign_extend' 64 (mword_of_int 1 : mword 12))
  = (mword_of_int 1 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma cs_xor_1 :
  xor_vec (mword_of_int 1 : mword 64) (sign_extend' 64 (mword_of_int 1 : mword 12))
  = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.


(* ===================================================================== *)
(* THE WHOLE FUNCTION.                                                    *)
(* ===================================================================== *)

Module CopyinstrProof (Walkaddr : WALKADDR) : COPYINSTR.

Section ProofCopyinstr.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation Rx0 := (mword_of_int 0 : mword 5).
  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
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

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  (* peel a register lookup through the insert tower, one layer at a time,
     then close against the base map's own fact (copyin's [lkp]).  [rgne]
     (IntrDefs.v) bridges a leaf's [rget m k] spelling (every leaf whose
     register index is a lemma PARAMETER reads via [rget], even when the
     call site happens to instantiate it at a concrete non-tp register) back
     to the plain [m !!! Regidx k] this file's facts are stated at. *)
  Ltac lkp :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | rgne
      | match goal with |- context [ ?M !!! _ ] => is_var M; progress unfold M end ];
    repeat rewrite add_vec_zero_l;
    first [ reflexivity | assumption ].

  Ltac slot_addr :=
    unfold pa_stk, add_vec_int; rewrite pa_stk_off2;
    apply f_equal; apply bv_eq; vm_compute; reflexivity.

  (* a symbolic index that is none of the three the inner loop writes *)
  Ltac peel_sym :=
    rewrite upd_ne;
    [| let H := fresh "Hpe" in
       let H' := fresh "Hpe" in
       intro H; injection H as H'; congruence ].

  (* ================================================================== *)
  (*  THE EPILOGUE (+0x34 .. +0x48).  All three frame-holding exits.     *)
  (* ================================================================== *)
  Local Lemma cs_epilogue `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (m Mt : regfile) (av : nat) (res : mword 64)
      (sp0 ra0 s00 s10 s20 s30 s40 s50 s60 s70 gap : mword 64)
      (b : bool) (pcur : mword 64) :
    (10 <= av)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Rs3 = s30 ->
    m !!! Regidx Rs4 = s40 ->
    m !!! Regidx Rs5 = s50 ->
    m !!! Regidx Rs6 = s60 ->
    m !!! Regidx Rs7 = s70 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 10 ->
    Mt !!! Regidx Ra0 = res ->
    Mt !!! Regidx Rs8 = m !!! Regidx Rs8 ->
    Mt !!! Regidx Rs9 = m !!! Regidx Rs9 ->
    Mt !!! Regidx Rs10 = m !!! Regidx Rs10 ->
    Mt !!! Regidx Rs11 = m !!! Regidx Rs11 ->
    sie_cap_gpr Mt (av - 10)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (CIS + 0x34) : mword 64) -∗
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    word_pointsto (pa_stk sp0 4) (DfracOwn 1) s20 -∗
    word_pointsto (pa_stk sp0 5) (DfracOwn 1) s30 -∗
    word_pointsto (pa_stk sp0 6) (DfracOwn 1) s40 -∗
    word_pointsto (pa_stk sp0 7) (DfracOwn 1) s50 -∗
    word_pointsto (pa_stk sp0 8) (DfracOwn 1) s60 -∗
    word_pointsto (pa_stk sp0 9) (DfracOwn 1) s70 -∗
    word_pointsto (pa_stk sp0 10) (DfracOwn 1) gap -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = res⌝ -∗
        sie_cap_gpr mf av b pcur -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hav Hsp0 Hra0 Hs00 Hs10 Hs20 Hs30 Hs40 Hs50 Hs60 Hs70
           Hmtsp Hmta0 Hmt8 Hmt9 Hmt10 Hmt11.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hcont".
    iPoseProof (csi_34 with "Htext") as "Hi34".
    iPoseProof (csi_36 with "Htext") as "Hi36".
    iPoseProof (csi_38 with "Htext") as "Hi38".
    iPoseProof (csi_3a with "Htext") as "Hi3a".
    iPoseProof (csi_3c with "Htext") as "Hi3c".
    iPoseProof (csi_3e with "Htext") as "Hi3e".
    iPoseProof (csi_40 with "Htext") as "Hi40".
    iPoseProof (csi_42 with "Htext") as "Hi42".
    iPoseProof (csi_44 with "Htext") as "Hi44".
    iPoseProof (csi_46 with "Htext") as "Hi46".
    iPoseProof (csi_48 with "Htext") as "Hi48".
    (* ---- +0x34: c.ldsp ra,72(sp) ---- *)
    assert (Hpa1 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = pa_stk sp0 1)
      by (rewrite Hmtsp; slot_addr).
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (CIS + 0x34))
              (mword_of_int 9 : mword 6) Rra Mt (av - 10)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi34 Hb1 [-]").
    iIntros (CIDe1 Hse1) "Hcg Hpc Hb1". iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> Mt).
    assert (Hq36 : add_vec_int (mword_of_int (CIS + 0x34) : mword 64) 2
                   = mword_of_int (CIS + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq36) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 10) by lkp.
    (* ---- +0x36: c.ldsp s0,64(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000"))) = pa_stk sp0 2)
      by (rewrite HT1sp; slot_addr).
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (CIS + 0x36))
              (mword_of_int 8 : mword 6) Rs0 T1 (av - 10)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi36 Hb2 [-]").
    iIntros (CIDe2 Hse2) "Hcg Hpc Hb2". iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    assert (Hq38 : add_vec_int (mword_of_int (CIS + 0x36) : mword 64) 2
                   = mword_of_int (CIS + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq38) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 10) by lkp.
    (* ---- +0x38: c.ldsp s1,56(sp) ---- *)
    assert (Hpa3 : add_vec (T2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 3)
      by (rewrite HT2sp; slot_addr).
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (CIS + 0x38))
              (mword_of_int 7 : mword 6) Rs1 T2 (av - 10)%nat s10 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi38 Hb3 [-]").
    iIntros (CIDe3 Hse3) "Hcg Hpc Hb3". iEval (rewrite Hpa3) in "Hb3".
    set (T3 := <[Regidx Rs1 := regval_into_reg s10]> T2).
    assert (Hq3a : add_vec_int (mword_of_int (CIS + 0x38) : mword 64) 2
                   = mword_of_int (CIS + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq3a) in "Hpc".
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 10) by lkp.
    (* ---- +0x3a: c.ldsp s2,48(sp) ---- *)
    assert (Hpa4 : add_vec (T3 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 4)
      by (rewrite HT3sp; slot_addr).
    iEval (rewrite -Hpa4) in "Hb4".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (CIS + 0x3a))
              (mword_of_int 6 : mword 6) Rs2 T3 (av - 10)%nat s20 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3a Hb4 [-]").
    iIntros (CIDe4 Hse4) "Hcg Hpc Hb4". iEval (rewrite Hpa4) in "Hb4".
    set (T4 := <[Regidx Rs2 := regval_into_reg s20]> T3).
    assert (Hq3c : add_vec_int (mword_of_int (CIS + 0x3a) : mword 64) 2
                   = mword_of_int (CIS + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq3c) in "Hpc".
    assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk sp0 10) by lkp.
    (* ---- +0x3c: c.ldsp s3,40(sp) ---- *)
    assert (Hpa5 : add_vec (T4 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 5)
      by (rewrite HT4sp; slot_addr).
    iEval (rewrite -Hpa5) in "Hb5".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (CIS + 0x3c))
              (mword_of_int 5 : mword 6) Rs3 T4 (av - 10)%nat s30 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3c Hb5 [-]").
    iIntros (CIDe5 Hse5) "Hcg Hpc Hb5". iEval (rewrite Hpa5) in "Hb5".
    set (T5 := <[Regidx Rs3 := regval_into_reg s30]> T4).
    assert (Hq3e : add_vec_int (mword_of_int (CIS + 0x3c) : mword 64) 2
                   = mword_of_int (CIS + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq3e) in "Hpc".
    assert (HT5sp : T5 !!! Regidx csp_rs1 = pa_stk sp0 10) by lkp.
    (* ---- +0x3e: c.ldsp s4,32(sp) ---- *)
    assert (Hpa6 : add_vec (T5 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 6)
      by (rewrite HT5sp; slot_addr).
    iEval (rewrite -Hpa6) in "Hb6".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (CIS + 0x3e))
              (mword_of_int 4 : mword 6) Rs4 T5 (av - 10)%nat s40 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3e Hb6 [-]").
    iIntros (CIDe6 Hse6) "Hcg Hpc Hb6". iEval (rewrite Hpa6) in "Hb6".
    set (T6 := <[Regidx Rs4 := regval_into_reg s40]> T5).
    assert (Hq40 : add_vec_int (mword_of_int (CIS + 0x3e) : mword 64) 2
                   = mword_of_int (CIS + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq40) in "Hpc".
    assert (HT6sp : T6 !!! Regidx csp_rs1 = pa_stk sp0 10) by lkp.
    (* ---- +0x40: c.ldsp s5,24(sp) ---- *)
    assert (Hpa7 : add_vec (T6 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 7)
      by (rewrite HT6sp; slot_addr).
    iEval (rewrite -Hpa7) in "Hb7".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (CIS + 0x40))
              (mword_of_int 3 : mword 6) Rs5 T6 (av - 10)%nat s50 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40 Hb7 [-]").
    iIntros (CIDe7 Hse7) "Hcg Hpc Hb7". iEval (rewrite Hpa7) in "Hb7".
    set (T7 := <[Regidx Rs5 := regval_into_reg s50]> T6).
    assert (Hq42 : add_vec_int (mword_of_int (CIS + 0x40) : mword 64) 2
                   = mword_of_int (CIS + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq42) in "Hpc".
    assert (HT7sp : T7 !!! Regidx csp_rs1 = pa_stk sp0 10) by lkp.
    (* ---- +0x42: c.ldsp s6,16(sp) ---- *)
    assert (Hpa8 : add_vec (T7 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 8)
      by (rewrite HT7sp; slot_addr).
    iEval (rewrite -Hpa8) in "Hb8".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (CIS + 0x42))
              (mword_of_int 2 : mword 6) Rs6 T7 (av - 10)%nat s60 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi42 Hb8 [-]").
    iIntros (CIDe8 Hse8) "Hcg Hpc Hb8". iEval (rewrite Hpa8) in "Hb8".
    set (T8 := <[Regidx Rs6 := regval_into_reg s60]> T7).
    assert (Hq44 : add_vec_int (mword_of_int (CIS + 0x42) : mword 64) 2
                   = mword_of_int (CIS + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq44) in "Hpc".
    assert (HT8sp : T8 !!! Regidx csp_rs1 = pa_stk sp0 10) by lkp.
    (* ---- +0x44: c.ldsp s7,8(sp) ---- *)
    assert (Hpa9 : add_vec (T8 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 9)
      by (rewrite HT8sp; slot_addr).
    iEval (rewrite -Hpa9) in "Hb9".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (CIS + 0x44))
              (mword_of_int 1 : mword 6) Rs7 T8 (av - 10)%nat s70 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi44 Hb9 [-]").
    iIntros (CIDe9 Hse9) "Hcg Hpc Hb9". iEval (rewrite Hpa9) in "Hb9".
    set (T9 := <[Regidx Rs7 := regval_into_reg s70]> T8).
    assert (Hq46 : add_vec_int (mword_of_int (CIS + 0x44) : mword 64) 2
                   = mword_of_int (CIS + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq46) in "Hpc".
    assert (HT9sp : T9 !!! Regidx csp_rs1 = pa_stk sp0 10) by lkp.
    (* ---- +0x46: c.addi16sp sp,80 (the frame pop) ---- *)
    assert (Hwv : add_vec (T9 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))) = sp0)
      by (rewrite HT9sp; apply cs_pop).
    assert (Hpop : T9 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T9 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))) 10)
      by (rewrite Hwv; exact HT9sp).
    iAssert (stack_own sp0 10) with "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hb1"; [iExists _; iExact "Hb1"|].
      iSplitL "Hb2"; [iExists _; iExact "Hb2"|].
      iSplitL "Hb3"; [iExists _; iExact "Hb3"|].
      iSplitL "Hb4"; [iExists _; iExact "Hb4"|].
      iSplitL "Hb5"; [iExists _; iExact "Hb5"|].
      iSplitL "Hb6"; [iExists _; iExact "Hb6"|].
      iSplitL "Hb7"; [iExists _; iExact "Hb7"|].
      iSplitL "Hb8"; [iExists _; iExact "Hb8"|].
      iSplitL "Hb9"; [iExists _; iExact "Hb9"|].
      iSplitL "Hb10"; [iExists _; iExact "Hb10"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (CIS + 0x46))
              (mword_of_int 5 : mword 6) T9 (av - 10)%nat 10 b Hpop
              with "Hcg Hpc Hi46 Hframe [-]").
    iIntros (CIDe10 Hse10) "Hcg Hpc".
    assert (Hnk : ((av - 10) + 10)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hq48 : add_vec_int (mword_of_int (CIS + 0x46) : mword 64) 2
                   = mword_of_int (CIS + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq48) in "Hpc".
    set (TA := <[Regidx csp_rs1 := regval_into_reg (add_vec (T9 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> T9).
    (* ---- +0x48: c.ret ---- *)
    assert (HTAra : TA !!! Regidx Rra = ra0) by lkp.
    iApply (wp_cret_s_sconf Φ (mword_of_int (CIS + 0x48)) Rra TA av b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi48 [-]").
    iIntros (CIDe11 Hse11) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    iEval (rewrite HTAra) in "Hpc".
    (* ---- the postcondition ---- *)
    assert (HTAsp : TA !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /TA upd_eq Hwv; symmetry; exact Hsp0).
    assert (HTAs0 : TA !!! Regidx Rs0 = m !!! Regidx Rs0)
      by (rewrite Hs00; lkp).
    assert (HTAs1 : TA !!! Regidx Rs1 = m !!! Regidx Rs1)
      by (rewrite Hs10; lkp).
    assert (HTAs2 : TA !!! Regidx Rs2 = m !!! Regidx Rs2)
      by (rewrite Hs20; lkp).
    assert (HTAs3 : TA !!! Regidx Rs3 = m !!! Regidx Rs3)
      by (rewrite Hs30; lkp).
    assert (HTAs4 : TA !!! Regidx Rs4 = m !!! Regidx Rs4)
      by (rewrite Hs40; lkp).
    assert (HTAs5 : TA !!! Regidx Rs5 = m !!! Regidx Rs5)
      by (rewrite Hs50; lkp).
    assert (HTAs6 : TA !!! Regidx Rs6 = m !!! Regidx Rs6)
      by (rewrite Hs60; lkp).
    assert (HTAs7 : TA !!! Regidx Rs7 = m !!! Regidx Rs7)
      by (rewrite Hs70; lkp).
    assert (HTA8 : TA !!! Regidx Rs8 = m !!! Regidx Rs8) by lkp.
    assert (HTA9 : TA !!! Regidx Rs9 = m !!! Regidx Rs9) by lkp.
    assert (HTA10 : TA !!! Regidx Rs10 = m !!! Regidx Rs10) by lkp.
    assert (HTA11 : TA !!! Regidx Rs11 = m !!! Regidx Rs11) by lkp.
    assert (HTAa0 : TA !!! Regidx Ra0 = res) by lkp.
    iSpecialize ("Hcont" $! CIDe11 with "[]"); [ iPureIntro; wp_next_chain | ].
    iApply ("Hcont" $! TA with "[%] Hcg Hpc").
    split; [| exact HTAa0].
    unfold callee_saved. split_and!;
      first [ exact HTAsp | exact HTAs0 | exact HTAs1 | exact HTAs2
            | exact HTAs3 | exact HTAs4 | exact HTAs5 | exact HTAs6 | exact HTAs7
            | exact HTA8 | exact HTA9 | exact HTA10 | exact HTA11 ].
  Qed.

  (* ================================================================== *)
  (*  THE RETURN-VALUE TAIL (+0x2c .. +0x30), shared by the NUL exit     *)
  (*  (which reaches it through +0x26) and the max-exhausted one.        *)
  (* ================================================================== *)
  Local Lemma cs_ret2c `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (M : regfile) (Kv : nat) (a5v resv : mword 64) (b : bool) (pcur : mword 64) :
    M !!! Regidx Ra5 = a5v ->
    xor_vec a5v (sign_extend' 64 (mword_of_int 1 : mword 12)) = (mword_of_int 0 : mword 64)
      /\ resv = (mword_of_int 0 : mword 64)
    \/ xor_vec a5v (sign_extend' 64 (mword_of_int 1 : mword 12)) = (mword_of_int 1 : mword 64)
      /\ resv = (mword_of_int (-1) : mword 64) ->
    sie_cap_gpr M Kv b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (CIS + 0x2c) : mword 64) -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ Mo : regfile,
        ⌜Mo !!! Regidx Ra0 = resv⌝ -∗
        ⌜forall r : mword 5, r <> Ra0 -> r <> Ra5 -> Mo !!! Regidx r = M !!! Regidx r⌝ -∗
        sie_cap_gpr Mo Kv b pcur -∗
        pc_is (mword_of_int (CIS + 0x34) : mword 64) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Ha5 Hcase.
    iIntros "Hcg #Htext Hpc Hcont".
    iPoseProof (csi_2c with "Htext") as "Hi2c".
    iPoseProof (csi_30 with "Htext") as "Hi30".
    (* the flipped flag, and the negation of it, as CLOSED literals *)
    set (fl := xor_vec a5v (sign_extend' 64 (mword_of_int 1 : mword 12))).
    (* ---- +0x2c: xori a5,a5,1 ---- *)
    iApply (wp_xori_s_sconf Φ (mword_of_int (CIS + 0x2c)) Ra5 Ra5
              (mword_of_int 1 : mword 12) fl M Kv b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite /fl Ha5; reflexivity)
              with "Hcg Hpc Hi2c [-]").
    iIntros (CIDr1 Hsr1) "Hcg Hpc".
    set (N1 := <[Regidx Ra5 := regval_into_reg fl]> M).
    assert (Hq30 : add_vec_int (mword_of_int (CIS + 0x2c) : mword 64) 4
                   = mword_of_int (CIS + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq30) in "Hpc".
    (* ---- +0x30: negw a0,a5  (= subw a0,x0,a5) ---- *)
    iDestruct (sie_cap_gpr_x0 N1 Kv b pcur Rx0 ltac:(vm_compute; reflexivity) with "Hcg")
      as "[%Hz0 Hcg]".
    iApply (wp_subw_s_sconf Φ (mword_of_int (CIS + 0x30)) Ra0 Rx0 Ra5 N1 Kv b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi30 [-]").
    iIntros (CIDr2 Hsr2) "Hcg Hpc".
    set (N2 := <[Regidx Ra0 := regval_into_reg
                  (sign_extend' 64 (sub_vec (subrange_vec_dec (rget N1 Rx0) 31 0 : mword 32)
                                            (subrange_vec_dec (rget N1 Ra5) 31 0 : mword 32)))]> N1).
    assert (Hq34 : add_vec_int (mword_of_int (CIS + 0x30) : mword 64) 4
                   = mword_of_int (CIS + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq34) in "Hpc".
    assert (HN1x0 : N1 !!! Regidx Rx0 = zero_reg)
      by (rewrite /N1 upd_ne; [exact Hz0 | reg_neq]).
    assert (HN1a5 : N1 !!! Regidx Ra5 = fl) by (rewrite /N1 upd_eq; reflexivity).
    assert (HN2a0 : N2 !!! Regidx Ra0 = resv).
    { rewrite /N2 upd_eq. rgne. rgne. rewrite HN1x0 HN1a5 /fl.
      destruct Hcase as [[Hfl ->] | [Hfl ->]]; rewrite Hfl;
        [exact cs_negw_0 | exact cs_negw_1]. }
    iSpecialize ("Hcont" $! CIDr2 with "[]"); [ iPureIntro; wp_next_chain | ].
    iApply ("Hcont" $! N2 with "[%] [%] Hcg Hpc").
    - exact HN2a0.
    - intros r N10 N15.
      rewrite /N2 upd_ne; [| intro He; injection He as He'; congruence].
      rewrite /N1 upd_ne; [| intro He; injection He as He'; congruence].
      reflexivity.
  Qed.


  (* ================================================================== *)
  (*  THE INNER LOOP (+0x88 head): one byte per iteration.               *)
  (* ================================================================== *)
  (* The chunk's destination base is [pa_add dst done]; the cursor is that
     base plus [i] and the end pointer that base plus [n].  Nothing about
     [srcva] or the page table appears -- the loop walks two byte buffers and
     nothing else.  The two exits are the NUL (at +0x26, cursor still on the
     terminator, buffer UNCHANGED -- the store is the +0x26 block's job) and
     the chunk running out (at +0x4a).  Both hand back a threading fact
     against the map [M0] the loop was ENTERED with, which is what lets the
     induction below carry it. *)
  Local Lemma cs_inner (Φ : mval -> iProp Σ)
      (dst srcp : mword 64) (maxn done n : nat) (fsrc : nat -> bv 8)
      (Kv : nat) (M0 : regfile) (b : bool) (pcur : mword 64) :
    (done + n <= maxn)%nat ->
    (Z.of_nat maxn < 18446744073709551616)%Z ->
    forall (rest i : nat) `(CID0 : CpuId) (M : regfile) (f : nat -> bv 8),
    (i + rest = n)%nat -> (i < n)%nat ->
    bb_nonul f (done + i) ->
    M !!! Regidx Ra5 = pa_add (pa_add dst done) i ->
    M !!! Regidx Ra3 = pa_add (pa_add dst done) n ->
    M !!! Regidx Ra2 = sub_vec srcp (pa_add dst done) ->
    (forall r : mword 5, r <> Ra1 -> r <> Ra4 -> r <> Ra5 ->
        M !!! Regidx r = M0 !!! Regidx r) ->
    sie_cap_gpr M Kv b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (CIS + 0x88) : mword 64) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add srcp j) ↦ₘ fsrc j) -∗
    ([∗ list] j ∈ seq 0 maxn, (pa_add dst j) ↦ₘ f j) -∗
    (* THE TWO EXITS, as an Iris [∧] and not two separate wands: they are
       ALTERNATIVES, and both need the same resources (the rest of the
       borrowed page, its returning wand, and the function's own exit
       continuation).  [∧] is exactly "prove either from what you hold".
       Both live under ONE [wp_next], anchored at [CID0] -- this loop's own
       per-iteration hart -- since either exit's resources (Hcg/Hpc) are
       whatever hart the inner loop's OWN leaf steps land on. *)
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ( ( ∀ (Mn : regfile) (i' : nat) (g : nat -> bv 8),
          ⌜(i' < n)%nat⌝ -∗
          ⌜bb_nonul g (done + i')⌝ -∗
          ⌜Mn !!! Regidx Ra5 = pa_add (pa_add dst done) i'⌝ -∗
          ⌜forall r : mword 5, r <> Ra1 -> r <> Ra4 -> r <> Ra5 ->
              Mn !!! Regidx r = M0 !!! Regidx r⌝ -∗
          sie_cap_gpr Mn Kv b pcur -∗
          pc_is (mword_of_int (CIS + 0x26) : mword 64) -∗
          ([∗ list] j ∈ seq 0 n, (pa_add srcp j) ↦ₘ fsrc j) -∗
          ([∗ list] j ∈ seq 0 maxn, (pa_add dst j) ↦ₘ g j) -∗
          WP (Loop : expr riscv_lang) {{ Φ }})
        ∧
        ( ∀ (Mc : regfile) (g : nat -> bv 8),
          ⌜bb_nonul g (done + n)⌝ -∗
          ⌜Mc !!! Regidx Ra1 = pa_add (pa_add dst done) (n - 1)⌝ -∗
          ⌜Mc !!! Regidx Ra5 = pa_add (pa_add dst done) n⌝ -∗
          ⌜forall r : mword 5, r <> Ra1 -> r <> Ra4 -> r <> Ra5 ->
              Mc !!! Regidx r = M0 !!! Regidx r⌝ -∗
          sie_cap_gpr Mc Kv b pcur -∗
          pc_is (mword_of_int (CIS + 0x4a) : mword 64) -∗
          ([∗ list] j ∈ seq 0 n, (pa_add srcp j) ↦ₘ fsrc j) -∗
          ([∗ list] j ∈ seq 0 maxn, (pa_add dst j) ↦ₘ g j) -∗
          WP (Loop : expr riscv_lang) {{ Φ }}) )) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hdn Hmax64.
    assert (Hn64 : (Z.of_nat n < 18446744073709551616)%Z).
    { apply (Z.le_lt_trans _ (Z.of_nat maxn)); [apply Nat2Z.inj_le; lia | exact Hmax64]. }
    intro rest.
    induction rest as [| rest IH];
      intros i CID0 M f Hsum Hin Hnul Ha5 Ha3 Ha2 Hthr; [ exfalso; lia |].
    iIntros "Hcg #Htext Hpc Hsrc Hdst HK".
    iPoseProof (csi_88 with "Htext") as "Hi88".
    iPoseProof (csi_8a with "Htext") as "Hi8a".
    iPoseProof (csi_8e with "Htext") as "Hi8e".
    iPoseProof (csi_92 with "Htext") as "Hi92".
    iPoseProof (csi_94 with "Htext") as "Hi94".
    iPoseProof (csi_98 with "Htext") as "Hi98".
    iPoseProof (csi_9a with "Htext") as "Hi9a".
    iPoseProof (csi_9e with "Htext") as "Hi9e".
    (* ---- +0x88: c.mv a1,a5 ---- *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (CIS + 0x88)) Ra1 Ra5 M Kv b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi88 [-]").
    iIntros (CIDn1 Hsn1) "Hcg Hpc".
    set (I1 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (rget M Ra5))]> M).
    assert (Hq8a : add_vec_int (mword_of_int (CIS + 0x88) : mword 64) 2
                   = mword_of_int (CIS + 0x8a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq8a) in "Hpc".
    assert (HI1a1 : I1 !!! Regidx Ra1 = pa_add (pa_add dst done) i) by lkp.
    assert (HI1a5 : I1 !!! Regidx Ra5 = pa_add (pa_add dst done) i) by lkp.
    assert (HI1a3 : I1 !!! Regidx Ra3 = pa_add (pa_add dst done) n) by lkp.
    assert (HI1a2 : I1 !!! Regidx Ra2 = sub_vec srcp (pa_add dst done)) by lkp.
    (* ---- +0x8a: add a4,a2,a5 -- the source address ---- *)
    iApply (wp_add_s_sconf Φ (mword_of_int (CIS + 0x8a)) Ra4 Ra2 Ra5
              (pa_add srcp i) I1 Kv b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HI1a2 HI1a5; apply pa_add_delta)
              with "Hcg Hpc Hi8a [-]").
    iIntros (CIDn2 Hsn2) "Hcg Hpc".
    set (I2 := <[Regidx Ra4 := regval_into_reg (pa_add srcp i)]> I1).
    assert (Hq8e : add_vec_int (mword_of_int (CIS + 0x8a) : mword 64) 4
                   = mword_of_int (CIS + 0x8e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq8e) in "Hpc".
    assert (HI2a4 : I2 !!! Regidx Ra4 = pa_add srcp i) by lkp.
    (* ---- +0x8e: lbu a4,0(a4) ---- *)
    iDestruct (bb_byte_acc srcp n i fsrc (DfracOwn 1) Hin with "Hsrc") as "[Hsb Hsback]".
    iApply (wp_lbu_s_sconf Φ (mword_of_int (CIS + 0x8e)) Ra4 Ra4
              (mword_of_int 0 : mword 12) I2 Kv (fsrc i : mword 8) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8e [Hsb] [-]").
    { iEval (rgne; rewrite HI2a4 addv_sext0). iExact "Hsb". }
    iIntros (CIDn3 Hsn3) "Hcg Hpc Hsb".
    iEval (rgne; rewrite HI2a4 addv_sext0) in "Hsb".
    iDestruct ("Hsback" $! fsrc with "[%] Hsb") as "Hsrc"; [done |].
    set (I3 := <[Regidx Ra4 := regval_into_reg (zero_extend' 64 (fsrc i : mword 8))]> I2).
    assert (Hq92 : add_vec_int (mword_of_int (CIS + 0x8e) : mword 64) 4
                   = mword_of_int (CIS + 0x92)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq92) in "Hpc".
    assert (HI3a4 : I3 !!! Regidx Ra4 = zero_extend' 64 (fsrc i : mword 8)) by lkp.
    assert (HI3a5 : I3 !!! Regidx Ra5 = pa_add (pa_add dst done) i) by lkp.
    assert (HI3a3 : I3 !!! Regidx Ra3 = pa_add (pa_add dst done) n) by lkp.
    assert (HI3a1 : I3 !!! Regidx Ra1 = pa_add (pa_add dst done) i) by lkp.
    assert (HI3a2 : I3 !!! Regidx Ra2 = sub_vec srcp (pa_add dst done)) by lkp.
    assert (HthrI3 : forall r : mword 5, r <> Ra1 -> r <> Ra4 -> r <> Ra5 ->
              I3 !!! Regidx r = M0 !!! Regidx r).
    { intros r N1 N4 N5. rewrite /I3. peel_sym.
      rewrite /I2. peel_sym. rewrite /I1. peel_sym. apply Hthr; assumption. }
    (* ---- +0x92: c.beqz a4 -- is this byte the terminator? ---- *)
    destruct (decide (fsrc i = (mword_of_int 0 : mword 8))) as [Hz | Hnz].
    - (* ============ the NUL: branch to +0x26 ============ *)
      iApply (wp_cbeqz_taken_s_sconf Φ (mword_of_int (CIS + 0x92))
                (mword_of_int 202 : mword 8) (Cregidx (mword_of_int 6)) Ra4 I3 Kv b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HI3a4 Hz; exact bc_zext8_iszero)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi92 [-]").
      iNext. iIntros (CIDn4 Hsn4) "Hcg Hpc".
      assert (Htgt26 : add_vec (mword_of_int (CIS + 0x92) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 202 : mword 8) ('b"0"))))
                = mword_of_int (CIS + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt26) in "Hpc".
      iSpecialize ("HK" $! CIDn4 with "[]"); [ iPureIntro; wp_next_chain | ].
      iDestruct "HK" as "[HNUL _]".
      iApply ("HNUL" $! I3 i f with "[%] [%] [%] [%] Hcg Hpc Hsrc Hdst");
        [exact Hin | exact Hnul | exact HI3a5 | exact HthrI3].
    - (* ============ a real byte: copy it and go on ============ *)
      iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (CIS + 0x92))
                (mword_of_int 202 : mword 8) (Cregidx (mword_of_int 6)) Ra4 I3 Kv b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HI3a4; exact (bc_zext8_nonzero _ Hnz))
                with "Hcg Hpc Hi92 [-]").
      iIntros (CIDn4 Hsn4) "Hcg Hpc".
      assert (Hq94 : add_vec_int (mword_of_int (CIS + 0x92) : mword 64) 2
                     = mword_of_int (CIS + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq94) in "Hpc".
      (* ---- +0x94: sb a4,0(a5) ---- *)
      assert (Hdi : (done + i < maxn)%nat) by lia.
      assert (Hcur : pa_add (pa_add dst done) i = pa_add dst (done + i))
        by apply pa_add_assoc.
      iDestruct (bb_byte_acc dst maxn (done + i) f (DfracOwn 1) Hdi with "Hdst")
        as "[Hdb Hdback]".
      iApply (wp_sb_s_sconf Φ (mword_of_int (CIS + 0x94)) Ra4 Ra5
                (mword_of_int 0 : mword 12) I3 Kv (f (done + i)%nat) b
                with "Hcg Hpc Hi94 [Hdb] [-]").
      { iEval (rgne; rewrite HI3a5 addv_sext0 Hcur). iExact "Hdb". }
      iIntros (CIDn5 Hsn5) "Hcg Hpc Hdb".
      iEval (rgne; rgne; rewrite HI3a5 addv_sext0 Hcur HI3a4 trunc8_zext8) in "Hdb".
      iDestruct ("Hdback" $! (bb_upd f (done + i)%nat (fsrc i)) with "[%] [Hdb]") as "Hdst".
      { intros j Hj Hne. apply bb_upd_ne. exact Hne. }
      { iEval (rewrite bb_upd_eq). iExact "Hdb". }
      assert (Hq98 : add_vec_int (mword_of_int (CIS + 0x94) : mword 64) 4
                     = mword_of_int (CIS + 0x98)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq98) in "Hpc".
      assert (Hnul' : bb_nonul (bb_upd f (done + i)%nat (fsrc i)) (done + S i)).
      { replace (done + S i)%nat with (S (done + i))%nat by lia.
        apply bb_nonul_upd; [exact Hnul | exact Hnz]. }
      (* ---- +0x98: c.addi a5,a5,1 ---- *)
      iApply (wp_caddi_s_sconf Φ (mword_of_int (CIS + 0x98)) Ra5
                (mword_of_int 1 : mword 6) I3 Kv b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi98 [-]").
      iIntros (CIDn6 Hsn6) "Hcg Hpc".
      set (I4 := <[Regidx Ra5 := regval_into_reg
                    (add_vec (rget I3 Ra5)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> I3).
      assert (Hq9a : add_vec_int (mword_of_int (CIS + 0x98) : mword 64) 2
                     = mword_of_int (CIS + 0x9a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq9a) in "Hpc".
      assert (HI4a5 : I4 !!! Regidx Ra5 = pa_add (pa_add dst done) (S i)).
      { rewrite /I4 upd_eq. rgne. rewrite HI3a5.
        apply pa_add_step. apply bv_eq; vm_compute; reflexivity. }
      assert (HI4a3 : I4 !!! Regidx Ra3 = pa_add (pa_add dst done) n) by lkp.
      assert (HI4a1 : I4 !!! Regidx Ra1 = pa_add (pa_add dst done) i) by lkp.
      assert (HI4a2 : I4 !!! Regidx Ra2 = sub_vec srcp (pa_add dst done)) by lkp.
      assert (HthrI4 : forall r : mword 5, r <> Ra1 -> r <> Ra4 -> r <> Ra5 ->
                I4 !!! Regidx r = M0 !!! Regidx r).
      { intros r N1 N4 N5. rewrite /I4. peel_sym. apply HthrI3; assumption. }
      assert (HSi64 : (Z.of_nat (S i) < 18446744073709551616)%Z).
      { apply (Z.le_lt_trans _ (Z.of_nat n)); [apply Nat2Z.inj_le; lia | exact Hn64]. }
      (* ---- +0x9a: bne a5,a3 -- is the chunk exhausted? ---- *)
      destruct (Nat.eqb_spec (S i) n) as [Hend | Hmore].
      + (* ------- the chunk is done: fall through to +0x9e ------- *)
        iApply (wp_bne_fall_s_sconf Φ (mword_of_int (CIS + 0x9a))
                  (mword_of_int 8174 : mword 13) Ra3 Ra5 I4 Kv b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rgne; rewrite HI4a5 HI4a3; unfold neq_vec;
                        rewrite (pa_add_eqb _ (S i) n HSi64 Hn64);
                        rewrite Hend Nat.eqb_refl; reflexivity)
                  with "Hcg Hpc Hi9a [-]").
        iIntros (CIDn7 Hsn7) "Hcg Hpc".
        assert (Hq9e : add_vec_int (mword_of_int (CIS + 0x9a) : mword 64) 4
                       = mword_of_int (CIS + 0x9e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq9e) in "Hpc".
        (* ---- +0x9e: c.j -0x54 -> +0x4a ---- *)
        iApply (wp_cj_s_sconf Φ (mword_of_int (CIS + 0x9e))
                  (sign_extend' 21 (concat_vec (mword_of_int 2006 : mword 11) ('b"0")))
                  I4 Kv b ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi9e [-]").
        iIntros (CIDn8 Hsn8). iNext. iIntros "Hcg Hpc".
        assert (Htgt4a : add_vec (mword_of_int (CIS + 0x9e) : mword 64)
                  (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2006 : mword 11) ('b"0"))))
                  = mword_of_int (CIS + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt4a) in "Hpc".
        assert (Hi1 : i = (n - 1)%nat) by lia.
        iSpecialize ("HK" $! CIDn8 with "[]"); [ iPureIntro; wp_next_chain | ].
        iDestruct "HK" as "[_ HDONE]".
        iApply ("HDONE" $! I4 (bb_upd f (done + i)%nat (fsrc i))
                  with "[%] [%] [%] [%] Hcg Hpc Hsrc Hdst").
        { rewrite <- Hend. exact Hnul'. }
        { rewrite <- Hi1. exact HI4a1. }
        { rewrite <- Hend. exact HI4a5. }
        { exact HthrI4. }
      + (* ------- more bytes in this chunk: take the back edge ------- *)
        iApply (wp_bne_taken_s_sconf Φ (mword_of_int (CIS + 0x9a))
                  (mword_of_int 8174 : mword 13) Ra3 Ra5 I4 Kv b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rgne; rewrite HI4a5 HI4a3; unfold neq_vec;
                        rewrite (pa_add_eqb _ (S i) n HSi64 Hn64);
                        rewrite (proj2 (Nat.eqb_neq (S i) n) Hmore); reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi9a [-]").
        iNext. iIntros (CIDn9 Hsn9) "Hcg Hpc".
        assert (Htgt88 : add_vec (mword_of_int (CIS + 0x9a) : mword 64)
                  (sign_extend' 64 (mword_of_int 8174 : mword 13))
                  = mword_of_int (CIS + 0x88)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt88) in "Hpc".
        assert (Hshift : b = false \/ pcur = zero_reg -> (CIDn9 : CPU) = (CID0 : CPU)) by wp_next_chain.
        iDestruct (wp_next_shift Hshift with "HK") as "HK".
        iApply (IH (S i) CIDn9 I4 (bb_upd f (done + i)%nat (fsrc i))
                  ltac:(lia) ltac:(lia) Hnul' HI4a5 HI4a3 HI4a2 HthrI4
                  with "Hcg Htext Hpc Hsrc Hdst HK").
  Qed.

  (* ================================================================== *)
  (*  THE OUTER LOOP (+0x5e head), by induction on FUEL.                 *)
  (* ================================================================== *)
  (* The measure is [rem], which drops by [n = min(4096 - off, rem)] and not
     by 1, so the induction is on a fuel bound above it.  The user-side
     cursor [s7] has NO invariant -- everything the iteration needs about it
     (the in-page offset, and hence [1 <= n]) is re-derived from
     [ProcPtOwn.pgd_unsigned] on the spot, exactly as in copyin. *)
  Local Lemma cs_loop (Φ : mval -> iProp Σ)
      (P : uptd) (K : nat) (dst spr : mword 64) (maxn : nat)
      (v8 v9 v10 v11 : mword 64) (b : bool) (pcur : mword 64) :
    (20 <= K)%nat ->
    (Z.of_nat maxn < 18446744073709551616)%Z ->
    forall (fuel done rem : nat) `(CID0 : CpuId) (m : regfile) (f : nat -> bv 8),
    (rem <= fuel)%nat -> (1 <= rem)%nat -> (done + rem = maxn)%nat ->
    bb_nonul f done ->
    m !!! Regidx csp_rs1 = spr ->
    m !!! Regidx Rs1 = pa_add dst done ->
    m !!! Regidx Rs3 = (mword_of_int (Z.of_nat rem) : mword 64) ->
    m !!! Regidx Rs4 = (mword_of_int 4096 : mword 64) ->
    m !!! Regidx Rs5 = page_base P.(ud_root) ->
    m !!! Regidx Rs6 = (mword_of_int (-4096) : mword 64) ->
    m !!! Regidx Rs8 = v8 ->
    m !!! Regidx Rs9 = v9 ->
    m !!! Regidx Rs10 = v10 ->
    m !!! Regidx Rs11 = v11 ->
    sie_cap_gpr m (K - 10)%nat b pcur -∗
    kernel_text -∗
    pc_is (mword_of_int (CIS + 0x5e) : mword 64) -∗
    proc_pt P -∗
    ([∗ list] j ∈ seq 0 maxn, (pa_add dst j) ↦ₘ f j) -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ (mj : regfile) (res : mword 64) (g : nat -> bv 8),
      ⌜mj !!! Regidx csp_rs1 = spr⌝ -∗
      ⌜mj !!! Regidx Rs8 = v8⌝ -∗
      ⌜mj !!! Regidx Rs9 = v9⌝ -∗
      ⌜mj !!! Regidx Rs10 = v10⌝ -∗
      ⌜mj !!! Regidx Rs11 = v11⌝ -∗
      ⌜mj !!! Regidx Ra0 = res⌝ -∗
      ⌜copyinstr_ret maxn g res⌝ -∗
      sie_cap_gpr mj (K - 10)%nat b pcur -∗
      pc_is (mword_of_int (CIS + 0x34) : mword 64) -∗
      proc_pt P -∗
      ([∗ list] j ∈ seq 0 maxn, (pa_add dst j) ↦ₘ g j) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HK Hmax64.
    intro fuel.
    induction fuel as [| fuel IH];
      intros done rem CID0 m f Hfuel Hrem Hsum Hnul Hsp Hs1 Hs3 Hs4 Hs5 Hs6 Hs8 Hs9 Hs10 Hs11;
      [ exfalso; lia |].
    iIntros "Hcg #Htext Hpc Hpt Hdst Hcont".
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhwc Hcg]".
    iDestruct "Hhwc" as (hwmisa0 hwmseccfg0 hwpmar0 hwelp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hkmapb)".
    iPoseProof (csi_5e with "Htext") as "Hi5e".
    iPoseProof (csi_62 with "Htext") as "Hi62".
    iPoseProof (csi_64 with "Htext") as "Hi64".
    iPoseProof (csi_66 with "Htext") as "Hi66".
    iPoseProof (csi_6a with "Htext") as "Hi6a".
    (* the cursor, its page and its offset inside that page *)
    pose (cur := (m !!! Regidx Rs7 : mword 64)).
    pose (va0 := (and_vec cur (mword_of_int (-4096)) : mword 64)).
    pose (off := Z.to_nat (bv_unsigned cur mod 4096)).
    assert (Hoffz : Z.of_nat off = (bv_unsigned cur mod 4096)%Z)
      by (unfold off; apply cs_off_id).
    assert (Hoff4 : (off < 4096)%nat) by (unfold off; apply cs_off_lt).
    assert (Hnav : add_vec (sub_vec va0 cur) (mword_of_int 4096)
                   = (mword_of_int (Z.of_nat (4096 - off)) : mword 64)).
    { unfold va0. rewrite pgd_room.
      assert (Heq : (4096 - bv_unsigned cur mod 4096)%Z = Z.of_nat (4096 - off)).
      { rewrite Nat2Z.inj_sub; [| lia]. rewrite Hoffz. reflexivity. }
      rewrite Heq. reflexivity. }
    assert (Hoffv : sub_vec cur va0 = (mword_of_int (Z.of_nat off) : mword 64)).
    { unfold va0. rewrite pgd_off. rewrite <- Hoffz. reflexivity. }
    assert (Hrem64 : (Z.of_nat rem < 18446744073709551616)%Z).
    { apply (Z.le_lt_trans _ (Z.of_nat maxn)); [apply Nat2Z.inj_le; lia | exact Hmax64]. }
    (* ---- +0x5e: and s2,s7,s6 -- va0 = PGROUNDDOWN(srcva) ---- *)
    iApply (wp_and_s_sconf Φ (mword_of_int (CIS + 0x5e)) Rs2 Rs7 Rs6 va0 m (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite Hs6; reflexivity)
              with "Hcg Hpc Hi5e [-]").
    iIntros (CIDl1 Hsl1) "Hcg Hpc".
    set (W1 := <[Regidx Rs2 := regval_into_reg va0]> m).
    assert (Hq62 : add_vec_int (mword_of_int (CIS + 0x5e) : mword 64) 4
                   = mword_of_int (CIS + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq62) in "Hpc".
    (* ---- +0x62: c.mv a1,s2 ---- *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (CIS + 0x62)) Ra1 Rs2 W1 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi62 [-]").
    iIntros (CIDl2 Hsl2) "Hcg Hpc".
    set (W2 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (rget W1 Rs2))]> W1).
    assert (Hq64 : add_vec_int (mword_of_int (CIS + 0x62) : mword 64) 2
                   = mword_of_int (CIS + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq64) in "Hpc".
    (* ---- +0x64: c.mv a0,s5 ---- *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (CIS + 0x64)) Ra0 Rs5 W2 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi64 [-]").
    iIntros (CIDl3 Hsl3) "Hcg Hpc".
    set (W3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget W2 Rs5))]> W2).
    assert (Hq66 : add_vec_int (mword_of_int (CIS + 0x64) : mword 64) 2
                   = mword_of_int (CIS + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq66) in "Hpc".
    (* ---- +0x66: jal ra,walkaddr ---- *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (CIS + 0x66)) Rra
              (mword_of_int 2095816 : mword 21) W3 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi66 [-]").
    iIntros (CIDl4 Hsl4) "Hcg Hpc".
    set (W4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CIS + 0x66) : mword 64) 4)]> W3).
    assert (Htgtwa : add_vec (mword_of_int (CIS + 0x66) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095816 : mword 21))
                     = mword_of_int KernelSyms.walkaddr)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtwa) in "Hpc".
    assert (HW4a0 : W4 !!! Regidx Ra0 = page_base P.(ud_root)) by lkp.
    assert (HW4a1 : W4 !!! Regidx Ra1 = va0) by lkp.
    assert (HW4ra : W4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CIS + 0x66) : mword 64) 4)
      by (rewrite /W4 upd_eq; reflexivity).
    (* ---- open the table into the exact represented view ---- *)
    iDestruct (proc_pt_acc_rep0 P with "Hpt") as
      (t m_ad) "(%Hrep & %Hview & %Hbase & %Hwf & Hptree & Hown)".
    assert (HW4root : W4 !!! Regidx Ra0
                      = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { rewrite HW4a0 Hbase. reflexivity. }
    iApply (Walkaddr.wp_walkaddr_sconf Φ W4 t m_ad (K - 10)%nat (DfracOwn 1) b pcur
              ltac:(lia) HW4root Hrep with "Hcg Htext Hpc Hptree [-]").
    iIntros (CIDl5 Hsl5 mw) "Hcg Hpc Hptree %Hwcs %Hwv".
    rewrite HW4a1 in Hwv.
    iDestruct (proc_pt_rebuild P t m_ad Hwf Hview Hrep Hbase with "Hptree Hown") as "Hpt".
    assert (Hret6a : ret_pc (W4 !!! Regidx Rra) = mword_of_int (CIS + 0x6a)).
    { rewrite HW4ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret6a) in "Hpc".
    (* everything copyinstr parked across the call *)
    assert (Hmwsp : mw !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hwcs csp_rs1 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws1 : mw !!! Regidx Rs1 = pa_add dst done).
    { rewrite (callee_saved_lookup Hwcs Rs1 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws2 : mw !!! Regidx Rs2 = va0).
    { rewrite (callee_saved_lookup Hwcs Rs2 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws3 : mw !!! Regidx Rs3 = (mword_of_int (Z.of_nat rem) : mword 64)).
    { rewrite (callee_saved_lookup Hwcs Rs3 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws4 : mw !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)).
    { rewrite (callee_saved_lookup Hwcs Rs4 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws5 : mw !!! Regidx Rs5 = page_base P.(ud_root)).
    { rewrite (callee_saved_lookup Hwcs Rs5 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws6 : mw !!! Regidx Rs6 = (mword_of_int (-4096) : mword 64)).
    { rewrite (callee_saved_lookup Hwcs Rs6 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws7 : mw !!! Regidx Rs7 = cur).
    { rewrite (callee_saved_lookup Hwcs Rs7 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws8 : mw !!! Regidx Rs8 = v8).
    { rewrite (callee_saved_lookup Hwcs Rs8 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws9 : mw !!! Regidx Rs9 = v9).
    { rewrite (callee_saved_lookup Hwcs Rs9 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws10 : mw !!! Regidx Rs10 = v10).
    { rewrite (callee_saved_lookup Hwcs Rs10 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws11 : mw !!! Regidx Rs11 = v11).
    { rewrite (callee_saved_lookup Hwcs Rs11 ltac:(vm_compute; reflexivity)). lkp. }
    (* ---- +0x6a: c.beqz a0 -- the walkaddr verdict ---- *)
    destruct Hwv as [Ha0z | (w & Hsome & Hvu & Hvab & Ha0v)].
    - (* =============== UNMAPPED: return -1 =============== *)
      iPoseProof (csi_a4 with "Htext") as "Hia4".
      iPoseProof (csi_a6 with "Htext") as "Hia6".
      iApply (wp_cbeqz_taken_s_sconf Φ (mword_of_int (CIS + 0x6a))
                (mword_of_int 29 : mword 8) (Cregidx (mword_of_int 2)) Ra0 mw (K - 10)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Ha0z; exact bc_moi_iszero)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi6a [-]").
      iNext. iIntros (CIDu1 Hsu1) "Hcg Hpc".
      assert (Htgta4 : add_vec (mword_of_int (CIS + 0x6a) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 29 : mword 8) ('b"0"))))
                = mword_of_int (CIS + 0xa4)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgta4) in "Hpc".
      (* ---- +0xa4: c.li a0,-1 ---- *)
      iApply (wp_cli_s_sconf Φ (mword_of_int (CIS + 0xa4)) Ra0
                (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64) mw (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hia4 [-]").
      iIntros (CIDu2 Hsu2) "Hcg Hpc".
      set (U1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> mw).
      assert (Hqa6 : add_vec_int (mword_of_int (CIS + 0xa4) : mword 64) 2
                     = mword_of_int (CIS + 0xa6)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hqa6) in "Hpc".
      (* ---- +0xa6: c.j -0x72 -> +0x34 ---- *)
      iApply (wp_cj_s_sconf Φ (mword_of_int (CIS + 0xa6))
                (sign_extend' 21 (concat_vec (mword_of_int 1991 : mword 11) ('b"0")))
                U1 (K - 10)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hia6 [-]").
      iIntros (CIDu3 Hsu3). iNext. iIntros "Hcg Hpc".
      assert (Htgt34 : add_vec (mword_of_int (CIS + 0xa6) : mword 64)
                (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1991 : mword 11) ('b"0"))))
                = mword_of_int (CIS + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt34) in "Hpc".
      iSpecialize ("Hcont" $! CIDu3 with "[]"); [ iPureIntro; wp_next_chain | ].
      iApply ("Hcont" $! U1 (mword_of_int (-1) : mword 64) f
                with "[%] [%] [%] [%] [%] [%] [%] Hcg Hpc Hpt Hdst").
      { lkp. } { lkp. } { lkp. } { lkp. } { lkp. } { lkp. }
      { right. reflexivity. }
    - (* =============== MAPPED: borrow the page =============== *)
      destruct (upt_ad_view_vu P.(ud_tfp) P.(ud_um) m_ad (svpn_of va0) w Hview Hsome Hvu)
        as (w0 & Hl0 & Hppn).
      assert (Hin0 : pte_ppn w0 ∈ um_ppns P.(ud_um))
        by (apply elem_of_um_ppns; exists (svpn_of va0), w0; split; [exact Hl0 | reflexivity]).
      assert (Hpv : page_valid (page_base (pte_ppn w))).
      { rewrite -Hppn. exact (proj1 (proj2 (proj2 Hwf)) _ Hin0). }
      pose proof (proc_pt_page_acc P (svpn_of va0) w0 Hl0) as Hacc.
      rewrite Hppn in Hacc.
      iDestruct (Hacc with "Hkmapb Hpt") as "[Hpg Hback]".
      assert (Hnz0 : eq_vec (mw !!! Regidx Ra0) zero_reg = false).
      { rewrite Ha0v. pose proof (page_valid_neq_zero _ Hpv) as Hne.
        unfold neq_vec in Hne.
        destruct (eq_vec (page_base (pte_ppn w)) (zero_reg : mword 64));
          [discriminate | reflexivity]. }
      (* ============================================================== *)
      (*  THE +0x78 JOIN: the chunk, over its length [n].                *)
      (* ============================================================== *)
      iAssert (∀ (CIDb : CpuId) (mb : regfile) (n : nat),
          ⌜(1 <= n)%nat⌝ -∗ ⌜(n <= rem)%nat⌝ -∗ ⌜(off + n <= 4096)%nat⌝ -∗
          ⌜mb !!! Regidx Ra3 = (mword_of_int (Z.of_nat n) : mword 64)⌝ -∗
          ⌜mb !!! Regidx Ra0 = page_base (pte_ppn w)⌝ -∗
          ⌜mb !!! Regidx csp_rs1 = spr⌝ -∗
          ⌜mb !!! Regidx Rs1 = pa_add dst done⌝ -∗
          ⌜mb !!! Regidx Rs2 = va0⌝ -∗
          ⌜mb !!! Regidx Rs3 = (mword_of_int (Z.of_nat rem) : mword 64)⌝ -∗
          ⌜mb !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)⌝ -∗
          ⌜mb !!! Regidx Rs5 = page_base P.(ud_root)⌝ -∗
          ⌜mb !!! Regidx Rs6 = (mword_of_int (-4096) : mword 64)⌝ -∗
          ⌜mb !!! Regidx Rs7 = cur⌝ -∗
          ⌜mb !!! Regidx Rs8 = v8⌝ -∗
          ⌜mb !!! Regidx Rs9 = v9⌝ -∗
          ⌜mb !!! Regidx Rs10 = v10⌝ -∗
          ⌜mb !!! Regidx Rs11 = v11⌝ -∗
          sie_cap_gpr (CID:=CIDb) mb (K - 10)%nat b pcur -∗
          pc_is (CID:=CIDb) (mword_of_int (CIS + 0x78) : mword 64) -∗
          (* [Hcont] re-anchored to THIS invocation's entry hart [CIDb] --
             [BODY] is proven ONCE, generically over [CIDb], so nothing
             inside its own proof can relate [CIDb] back to the outer
             [CID0]; each call site below re-anchors cs_loop's own [Hcont]
             via [wp_next_shift] before handing it in. *)
          wp_next (CID0 := CIDb) b pcur (fun (CID : CpuId) =>
            ∀ (mj : regfile) (res : mword 64) (g : nat -> bv 8),
            ⌜mj !!! Regidx csp_rs1 = spr⌝ -∗
            ⌜mj !!! Regidx Rs8 = v8⌝ -∗
            ⌜mj !!! Regidx Rs9 = v9⌝ -∗
            ⌜mj !!! Regidx Rs10 = v10⌝ -∗
            ⌜mj !!! Regidx Rs11 = v11⌝ -∗
            ⌜mj !!! Regidx Ra0 = res⌝ -∗
            ⌜copyinstr_ret maxn g res⌝ -∗
            sie_cap_gpr mj (K - 10)%nat b pcur -∗
            pc_is (mword_of_int (CIS + 0x34) : mword 64) -∗
            proc_pt P -∗
            ([∗ list] j ∈ seq 0 maxn, (pa_add dst j) ↦ₘ g j) -∗
            WP (Loop : expr riscv_lang) {{ Φ }}) -∗
          WP (Loop : expr riscv_lang) {{ Φ }})%I
        with "[Hdst Hpg Hback]" as "BODY".
      { iIntros (CIDb mb n) "%Hn1 %Hnrem %Hnoff %Hba3 %Hba0 %Hbsp %Hbs1 %Hbs2 %Hbs3
                        %Hbs4 %Hbs5 %Hbs6 %Hbs7 %Hbs8 %Hbs9 %Hbs10 %Hbs11 Hcg Hpc Hcont".
        iPoseProof (csi_78 with "Htext") as "Hi78".
        iPoseProof (csi_7a with "Htext") as "Hi7a".
        iPoseProof (csi_7e with "Htext") as "Hi7e".
        iPoseProof (csi_82 with "Htext") as "Hi82".
        iPoseProof (csi_84 with "Htext") as "Hi84".
        iPoseProof (csi_86 with "Htext") as "Hi86".
        assert (Hn64 : (Z.of_nat n < 18446744073709551616)%Z).
        { apply (Z.le_lt_trans _ (Z.of_nat rem)); [apply Nat2Z.inj_le; lia | exact Hrem64]. }
        (* ---- +0x78: c.beqz a3 -- DEAD, since n >= 1 ---- *)
        iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (CIS + 0x78))
                  (mword_of_int 24 : mword 8) (Cregidx (mword_of_int 5)) Ra3 mb (K - 10)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite Hba3; exact (bc_moi_nonzero n Hn64 ltac:(lia)))
                  with "Hcg Hpc Hi78 [-]").
        iIntros (CIDm1 Hsm1) "Hcg Hpc".
        assert (Hq7a : add_vec_int (mword_of_int (CIS + 0x78) : mword 64) 2
                       = mword_of_int (CIS + 0x7a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq7a) in "Hpc".
        (* ---- +0x7a: add a2,a0,s7 ---- *)
        iApply (wp_add_s_sconf Φ (mword_of_int (CIS + 0x7a)) Ra2 Ra0 Rs7
                  (add_vec (page_base (pte_ppn w)) cur) mb (K - 10)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(rgne; rgne; rewrite Hba0 Hbs7; reflexivity)
                  with "Hcg Hpc Hi7a [-]").
        iIntros (CIDm2 Hsm2) "Hcg Hpc".
        set (C1 := <[Regidx Ra2 := regval_into_reg
                      (add_vec (page_base (pte_ppn w)) cur)]> mb).
        assert (Hq7e : add_vec_int (mword_of_int (CIS + 0x7a) : mword 64) 4
                       = mword_of_int (CIS + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq7e) in "Hpc".
        (* ---- +0x7e: sub a2,a2,s2 -- p = pa0 + (srcva - va0) ---- *)
        iApply (wp_sub_s_sconf Φ (mword_of_int (CIS + 0x7e)) Ra2 Ra2 Rs2
                  (pa_add (page_base (pte_ppn w)) off) C1 (K - 10)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(rgne; rgne;
                        assert (HC1a2 : C1 !!! Regidx Ra2
                                = add_vec (page_base (pte_ppn w)) cur) by lkp;
                        assert (HC1s2 : C1 !!! Regidx Rs2 = va0) by lkp;
                        rewrite HC1a2 HC1s2; apply pa_add_of_diff; exact Hoffv)
                  with "Hcg Hpc Hi7e [-]").
        iIntros (CIDm3 Hsm3) "Hcg Hpc".
        set (C2 := <[Regidx Ra2 := regval_into_reg
                      (pa_add (page_base (pte_ppn w)) off)]> C1).
        assert (Hq82 : add_vec_int (mword_of_int (CIS + 0x7e) : mword 64) 4
                       = mword_of_int (CIS + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq82) in "Hpc".
        (* ---- +0x82: c.mv a5,s1 ---- *)
        iApply (wp_cmv_s_sconf Φ (mword_of_int (CIS + 0x82)) Ra5 Rs1 C2 (K - 10)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi82 [-]").
        iIntros (CIDm4 Hsm4) "Hcg Hpc".
        set (C3 := <[Regidx Ra5 := regval_into_reg (add_vec zero_reg (rget C2 Rs1))]> C2).
        assert (Hq84 : add_vec_int (mword_of_int (CIS + 0x82) : mword 64) 2
                       = mword_of_int (CIS + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq84) in "Hpc".
        (* ---- +0x84: c.sub a2,a2,s1 -- the source/dest delta ---- *)
        iApply (wp_csub_s_sconf Φ (mword_of_int (CIS + 0x84)) Ra2 Rs1 C3 (K - 10)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi84 [-]").
        iIntros (CIDm5 Hsm5) "Hcg Hpc".
        set (C4 := <[Regidx Ra2 := regval_into_reg
                      (sub_vec (rget C3 Ra2) (rget C3 Rs1))]> C3).
        assert (Hq86 : add_vec_int (mword_of_int (CIS + 0x84) : mword 64) 2
                       = mword_of_int (CIS + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq86) in "Hpc".
        (* ---- +0x86: c.add a3,a3,s1 -- the end pointer ---- *)
        iApply (wp_cadd_s_sconf Φ (mword_of_int (CIS + 0x86)) Ra3 Rs1 C4 (K - 10)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi86 [-]").
        iIntros (CIDm6 Hsm6) "Hcg Hpc".
        set (C5 := <[Regidx Ra3 := regval_into_reg
                      (add_vec (rget C4 Ra3) (rget C4 Rs1))]> C4).
        assert (Hq88 : add_vec_int (mword_of_int (CIS + 0x86) : mword 64) 2
                       = mword_of_int (CIS + 0x88)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq88) in "Hpc".
        (* the three registers the inner loop runs on *)
        assert (HC5a5 : C5 !!! Regidx Ra5 = pa_add (pa_add dst done) 0).
        { rewrite pa_add_0. lkp. }
        assert (HC5a3 : C5 !!! Regidx Ra3 = pa_add (pa_add dst done) n).
        { rewrite /C5 upd_eq. rgne. rgne.
          assert (E1 : C4 !!! Regidx Ra3 = (mword_of_int (Z.of_nat n) : mword 64)) by lkp.
          assert (E2 : C4 !!! Regidx Rs1 = pa_add dst done) by lkp.
          rewrite E1 E2. apply pa_add_comm. }
        assert (HC5a2 : C5 !!! Regidx Ra2
                        = sub_vec (pa_add (page_base (pte_ppn w)) off) (pa_add dst done)).
        { rewrite /C5 upd_ne; [| reg_neq]. rewrite /C4 upd_eq. rgne. rgne.
          assert (E1 : C3 !!! Regidx Ra2 = pa_add (page_base (pte_ppn w)) off) by lkp.
          assert (E2 : C3 !!! Regidx Rs1 = pa_add dst done) by lkp.
          rewrite E1 E2. reflexivity. }
        assert (HthrC5 : forall r : mword 5, r <> Ra1 -> r <> Ra4 -> r <> Ra5 ->
                  C5 !!! Regidx r = C5 !!! Regidx r)
          by (intros; reflexivity).
        (* carve the source window out of the borrowed page *)
        iDestruct (bb_page_named (page_base (pte_ppn w)) with "Hpg") as (fpg) "Hpg".
        assert (Hsplitp : (off + n + (4096 - off - n) = 4096)%nat) by lia.
        iEval (rewrite (bb_split3 (page_base (pte_ppn w)) off n (4096 - off - n) 4096
                          fpg Hsplitp)) in "Hpg".
        iDestruct "Hpg" as "(Hpg0 & Hsrc & Hpg2)".
        assert (Hdn : (done + n <= maxn)%nat) by lia.
        (* ---- the inner loop ---- *)
        iApply (cs_inner Φ dst (pa_add (page_base (pte_ppn w)) off) maxn done n
                  (fun j => fpg (off + j)%nat) (K - 10)%nat C5 b pcur
                  Hdn Hmax64 n 0%nat CIDm6 C5 f
                  ltac:(lia) ltac:(lia) ltac:(rewrite Nat.add_0_r; exact Hnul)
                  HC5a5 HC5a3 HC5a2 HthrC5
                  with "Hcg Htext Hpc Hsrc Hdst [-]").
        iIntros (CIDci Hsci). iSplit.
        { (* ---------- the NUL exit, at +0x26 ---------- *)
          iIntros (Mn i' g) "%Hi'n %Hnulg %Hna5 %Hnthr Hcg Hpc Hsrc Hdst".
          iPoseProof (csi_26 with "Htext") as "Hi26".
          iPoseProof (csi_2a with "Htext") as "Hi2a".
          (* give the page back *)
          iDestruct (bb_join3 (page_base (pte_ppn w)) off n (4096 - off - n) 4096 fpg
                       (fun j => fpg (off + j)%nat) (fun j => fpg (off + (n + j))%nat)
                       Hsplitp with "Hpg0 Hsrc Hpg2") as (fpg') "Hpg".
          iDestruct (bb_page_of_named (page_base (pte_ppn w)) fpg' with "Hpg") as "Hpg".
          iDestruct ("Hback" with "Hpg") as "Hpt".
          (* ---- +0x26: sb zero,0(a5) -- plant the terminator ---- *)
          assert (Hdi : (done + i' < maxn)%nat) by lia.
          assert (Hcur : pa_add (pa_add dst done) i' = pa_add dst (done + i'))
            by apply pa_add_assoc.
          iDestruct (sie_cap_gpr_x0 Mn (K - 10)%nat b pcur Rx0 ltac:(vm_compute; reflexivity)
                       with "Hcg") as "[%Hz0 Hcg]".
          iDestruct (bb_byte_acc dst maxn (done + i') g (DfracOwn 1) Hdi with "Hdst")
            as "[Hdb Hdback]".
          iApply (wp_sb_s_sconf Φ (mword_of_int (CIS + 0x26)) Rx0 Ra5
                    (mword_of_int 0 : mword 12) Mn (K - 10)%nat (g (done + i')%nat) b
                    with "Hcg Hpc Hi26 [Hdb] [-]").
          { iEval (rgne; rewrite Hna5 addv_sext0 Hcur). iExact "Hdb". }
          iIntros (CIDn1 Hsn1) "Hcg Hpc Hdb".
          iEval (rgne; rgne; rewrite Hna5 addv_sext0 Hcur Hz0 trunc8_zero) in "Hdb".
          iDestruct ("Hdback" $! (bb_upd g (done + i')%nat (mword_of_int 0 : mword 8))
                       with "[%] [Hdb]") as "Hdst".
          { intros j Hj Hne. apply bb_upd_ne. exact Hne. }
          { iEval (rewrite bb_upd_eq). iExact "Hdb". }
          assert (Hq2a : add_vec_int (mword_of_int (CIS + 0x26) : mword 64) 4
                         = mword_of_int (CIS + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hq2a) in "Hpc".
          (* ---- +0x2a: c.li a5,1 ---- *)
          iApply (wp_cli_s_sconf Φ (mword_of_int (CIS + 0x2a)) Ra5
                    (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64) Mn (K - 10)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    with "Hcg Hpc Hi2a [-]").
          iIntros (CIDn2 Hsn2) "Hcg Hpc".
          set (G1 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> Mn).
          assert (Hq2c : add_vec_int (mword_of_int (CIS + 0x2a) : mword 64) 2
                         = mword_of_int (CIS + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hq2c) in "Hpc".
          (* ---- +0x2c .. +0x30 ---- *)
          iApply (cs_ret2c Φ G1 (K - 10)%nat (mword_of_int 1 : mword 64)
                    (mword_of_int 0 : mword 64) b pcur
                    ltac:(rewrite /G1 upd_eq; reflexivity)
                    ltac:(left; split; [exact cs_xor_1 | reflexivity])
                    with "Hcg Htext Hpc [-]").
          iIntros (CIDn3 Hsn3 Mo) "%Hoa0 %Hothr Hcg Hpc".
          (* the answer: the buffer now holds a NUL-terminated string *)
          assert (Hcstr : bb_cstr (bb_upd g (done + i')%nat (mword_of_int 0 : mword 8))
                            (done + i')%nat) by (apply bb_cstr_upd; exact Hnulg).
          iSpecialize ("Hcont" $! CIDn3 with "[]"); [ iPureIntro; wp_next_chain | ].
          iApply ("Hcont" $! Mo (mword_of_int 0 : mword 64)
                    (bb_upd g (done + i')%nat (mword_of_int 0 : mword 8))
                    with "[%] [%] [%] [%] [%] [%] [%] Hcg Hpc Hpt Hdst").
          { rewrite (Hothr csp_rs1 ltac:(reg_neq) ltac:(reg_neq)).
            rewrite /G1 upd_ne; [| reg_neq].
            rewrite (Hnthr csp_rs1 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). lkp. }
          { rewrite (Hothr Rs8 ltac:(reg_neq) ltac:(reg_neq)).
            rewrite /G1 upd_ne; [| reg_neq].
            rewrite (Hnthr Rs8 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). lkp. }
          { rewrite (Hothr Rs9 ltac:(reg_neq) ltac:(reg_neq)).
            rewrite /G1 upd_ne; [| reg_neq].
            rewrite (Hnthr Rs9 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). lkp. }
          { rewrite (Hothr Rs10 ltac:(reg_neq) ltac:(reg_neq)).
            rewrite /G1 upd_ne; [| reg_neq].
            rewrite (Hnthr Rs10 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). lkp. }
          { rewrite (Hothr Rs11 ltac:(reg_neq) ltac:(reg_neq)).
            rewrite /G1 upd_ne; [| reg_neq].
            rewrite (Hnthr Rs11 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). lkp. }
          { exact Hoa0. }
          { left. split; [reflexivity |]. exists (done + i')%nat.
            split; [lia | exact Hcstr]. } }
        { (* ---------- the chunk-done exit, at +0x4a ---------- *)
          iIntros (Mc g) "%Hnulg %Hca1 %Hca5 %Hcthr Hcg Hpc Hsrc Hdst".
          iPoseProof (csi_4a with "Htext") as "Hi4a".
          iPoseProof (csi_4e with "Htext") as "Hi4e".
          iPoseProof (csi_50 with "Htext") as "Hi50".
          iPoseProof (csi_54 with "Htext") as "Hi54".
          iPoseProof (csi_58 with "Htext") as "Hi58".
          iPoseProof (csi_5c with "Htext") as "Hi5c".
          (* give the page back *)
          iDestruct (bb_join3 (page_base (pte_ppn w)) off n (4096 - off - n) 4096 fpg
                       (fun j => fpg (off + j)%nat) (fun j => fpg (off + (n + j))%nat)
                       Hsplitp with "Hpg0 Hsrc Hpg2") as (fpg') "Hpg".
          iDestruct (bb_page_of_named (page_base (pte_ppn w)) fpg' with "Hpg") as "Hpg".
          iDestruct ("Hback" with "Hpg") as "Hpt".
          (* the register facts the chunk left standing *)
          assert (Hcs1 : Mc !!! Regidx Rs1 = pa_add dst done)
            by (rewrite (Hcthr Rs1 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); lkp).
          assert (Hcs3 : Mc !!! Regidx Rs3 = (mword_of_int (Z.of_nat rem) : mword 64))
            by (rewrite (Hcthr Rs3 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); lkp).
          assert (Hcs2 : Mc !!! Regidx Rs2 = va0)
            by (rewrite (Hcthr Rs2 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); lkp).
          assert (Hcs4 : Mc !!! Regidx Rs4 = (mword_of_int 4096 : mword 64))
            by (rewrite (Hcthr Rs4 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); lkp).
          assert (Hcs5 : Mc !!! Regidx Rs5 = page_base P.(ud_root))
            by (rewrite (Hcthr Rs5 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); lkp).
          assert (Hcs6 : Mc !!! Regidx Rs6 = (mword_of_int (-4096) : mword 64))
            by (rewrite (Hcthr Rs6 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); lkp).
          assert (Hcsp : Mc !!! Regidx csp_rs1 = spr)
            by (rewrite (Hcthr csp_rs1 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); lkp).
          assert (Hc8 : Mc !!! Regidx Rs8 = v8)
            by (rewrite (Hcthr Rs8 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); lkp).
          assert (Hc9 : Mc !!! Regidx Rs9 = v9)
            by (rewrite (Hcthr Rs9 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); lkp).
          assert (Hc10 : Mc !!! Regidx Rs10 = v10)
            by (rewrite (Hcthr Rs10 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); lkp).
          assert (Hc11 : Mc !!! Regidx Rs11 = v11)
            by (rewrite (Hcthr Rs11 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); lkp).
          (* ---- +0x4a: addi a4,s3,-1 ---- *)
          iApply (wp_addi4_s_sconf Φ (mword_of_int (CIS + 0x4a)) Ra4 Rs3
                    (mword_of_int 4095 : mword 12) Mc (K - 10)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi4a [-]").
          iIntros (CIDd1 Hsd1) "Hcg Hpc".
          set (D1 := <[Regidx Ra4 := regval_into_reg
                        (add_vec (rget Mc Rs3)
                           (sign_extend' 64 (mword_of_int 4095 : mword 12)))]> Mc).
          assert (Hq4e : add_vec_int (mword_of_int (CIS + 0x4a) : mword 64) 4
                         = mword_of_int (CIS + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hq4e) in "Hpc".
          assert (Hm1 : (sign_extend' 64 (mword_of_int 4095 : mword 12) : mword 64)
                        = mword_of_int (-1))
            by (apply bv_eq; vm_compute; reflexivity).
          assert (HD1a4 : D1 !!! Regidx Ra4
                          = (mword_of_int (Z.of_nat (rem - 1)) : mword 64)).
          { rewrite /D1 upd_eq. rgne. rewrite Hcs3.
            exact (bc_add_m1_nat rem _ Hm1 ltac:(lia) Hrem64). }
          assert (HD1s1 : D1 !!! Regidx Rs1 = pa_add dst done) by lkp.
          (* ---- +0x4e: c.add a4,a4,s1 ---- *)
          iApply (wp_cadd_s_sconf Φ (mword_of_int (CIS + 0x4e)) Ra4 Rs1 D1 (K - 10)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi4e [-]").
          iIntros (CIDd2 Hsd2) "Hcg Hpc".
          set (D2 := <[Regidx Ra4 := regval_into_reg
                        (add_vec (rget D1 Ra4) (rget D1 Rs1))]> D1).
          assert (Hq50 : add_vec_int (mword_of_int (CIS + 0x4e) : mword 64) 2
                         = mword_of_int (CIS + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hq50) in "Hpc".
          assert (HD2a4 : D2 !!! Regidx Ra4 = pa_add (pa_add dst done) (rem - 1)).
          { rewrite /D2 upd_eq. rgne. rgne. rewrite HD1a4 HD1s1. apply pa_add_comm. }
          assert (HD2a1 : D2 !!! Regidx Ra1 = pa_add (pa_add dst done) (n - 1)) by lkp.
          (* ---- +0x50: sub s3,a4,a1 -- max -= n ---- *)
          assert (Hrm164 : (Z.of_nat (rem - 1) < 18446744073709551616)%Z).
          { apply (Z.le_lt_trans _ (Z.of_nat rem)); [apply Nat2Z.inj_le; lia | exact Hrem64]. }
          iApply (wp_sub_s_sconf Φ (mword_of_int (CIS + 0x50)) Rs3 Ra4 Ra1
                    (mword_of_int (Z.of_nat (rem - n)) : mword 64) D2 (K - 10)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    ltac:(rgne; rgne; rewrite HD2a4 HD2a1;
                          rewrite (pa_add_diff _ (rem - 1) (n - 1) ltac:(lia) Hrm164);
                          replace (rem - 1 - (n - 1))%nat with (rem - n)%nat by lia;
                          reflexivity)
                    with "Hcg Hpc Hi50 [-]").
          iIntros (CIDd3 Hsd3) "Hcg Hpc".
          set (D3 := <[Regidx Rs3 := regval_into_reg
                        (mword_of_int (Z.of_nat (rem - n)) : mword 64)]> D2).
          assert (Hq54 : add_vec_int (mword_of_int (CIS + 0x50) : mword 64) 4
                         = mword_of_int (CIS + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hq54) in "Hpc".
          (* ---- +0x54: add s7,s2,s4 -- srcva = va0 + PGSIZE ---- *)
          iApply (wp_add_s_sconf Φ (mword_of_int (CIS + 0x54)) Rs7 Rs2 Rs4
                    (add_vec va0 (mword_of_int 4096)) D3 (K - 10)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    ltac:(rgne; rgne;
                          assert (E1 : D3 !!! Regidx Rs2 = va0) by lkp;
                          assert (E2 : D3 !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)) by lkp;
                          rewrite E1 E2; reflexivity)
                    with "Hcg Hpc Hi54 [-]").
          iIntros (CIDd4 Hsd4) "Hcg Hpc".
          set (D4 := <[Regidx Rs7 := regval_into_reg (add_vec va0 (mword_of_int 4096))]> D3).
          assert (Hq58 : add_vec_int (mword_of_int (CIS + 0x54) : mword 64) 4
                         = mword_of_int (CIS + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hq58) in "Hpc".
          assert (HD4a1 : D4 !!! Regidx Ra1 = pa_add (pa_add dst done) (n - 1)) by lkp.
          assert (HD4a4 : D4 !!! Regidx Ra4 = pa_add (pa_add dst done) (rem - 1)) by lkp.
          assert (Hn164 : (Z.of_nat (n - 1) < 18446744073709551616)%Z).
          { apply (Z.le_lt_trans _ (Z.of_nat rem)); [apply Nat2Z.inj_le; lia | exact Hrem64]. }
          (* ---- +0x58: beq a1,a4 -- did [max] run out? ---- *)
          destruct (Nat.eqb_spec (n - 1) (rem - 1)) as [Heq | Hne].
          - (* ------- max exhausted with no NUL: return -1 ------- *)
            assert (Hnr : n = rem) by lia.
            iPoseProof (csi_a0 with "Htext") as "Hia0".
            iPoseProof (csi_a2 with "Htext") as "Hia2".
            iApply (wp_beq_taken_s_sconf Φ (mword_of_int (CIS + 0x58))
                      (mword_of_int 72 : mword 13) Ra4 Ra1 D4 (K - 10)%nat b
                      ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                      ltac:(rgne; rgne; rewrite HD4a1 HD4a4;
                            rewrite (pa_add_eqb _ (n - 1) (rem - 1) Hn164 Hrm164);
                            rewrite Heq Nat.eqb_refl; reflexivity)
                      ltac:(vm_compute; reflexivity)
                      with "Hcg Hpc Hi58 [-]").
            iNext. iIntros (CIDd5 Hsd5) "Hcg Hpc".
            assert (Htgta0 : add_vec (mword_of_int (CIS + 0x58) : mword 64)
                      (sign_extend' 64 (mword_of_int 72 : mword 13))
                      = mword_of_int (CIS + 0xa0)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Htgta0) in "Hpc".
            (* ---- +0xa0: c.li a5,0 ---- *)
            iApply (wp_cli_s_sconf Φ (mword_of_int (CIS + 0xa0)) Ra5
                      (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) D4 (K - 10)%nat b
                      ltac:(vm_compute; discriminate) ltac:(rdok)
                      ltac:(apply bv_eq; vm_compute; reflexivity)
                      with "Hcg Hpc Hia0 [-]").
            iIntros (CIDd6 Hsd6) "Hcg Hpc".
            set (E1 := <[Regidx Ra5 := regval_into_reg (mword_of_int 0 : mword 64)]> D4).
            assert (Hqa2 : add_vec_int (mword_of_int (CIS + 0xa0) : mword 64) 2
                           = mword_of_int (CIS + 0xa2)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hqa2) in "Hpc".
            (* ---- +0xa2: c.j -0x76 -> +0x2c ---- *)
            iApply (wp_cj_s_sconf Φ (mword_of_int (CIS + 0xa2))
                      (sign_extend' 21 (concat_vec (mword_of_int 1989 : mword 11) ('b"0")))
                      E1 (K - 10)%nat b ltac:(vm_compute; reflexivity)
                      with "Hcg Hpc Hia2 [-]").
            iIntros (CIDd7 Hsd7). iNext. iIntros "Hcg Hpc".
            assert (Htgt2c : add_vec (mword_of_int (CIS + 0xa2) : mword 64)
                      (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1989 : mword 11) ('b"0"))))
                      = mword_of_int (CIS + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Htgt2c) in "Hpc".
            iApply (cs_ret2c Φ E1 (K - 10)%nat (mword_of_int 0 : mword 64)
                      (mword_of_int (-1) : mword 64) b pcur
                      ltac:(rewrite /E1 upd_eq; reflexivity)
                      ltac:(right; split; [exact cs_xor_0 | reflexivity])
                      with "Hcg Htext Hpc [-]").
            iIntros (CIDd8 Hsd8 Mo) "%Hoa0 %Hothr Hcg Hpc".
            iSpecialize ("Hcont" $! CIDd8 with "[]"); [ iPureIntro; wp_next_chain | ].
            iApply ("Hcont" $! Mo (mword_of_int (-1) : mword 64) g
                      with "[%] [%] [%] [%] [%] [%] [%] Hcg Hpc Hpt Hdst").
            { rewrite (Hothr csp_rs1 ltac:(reg_neq) ltac:(reg_neq)). lkp. }
            { rewrite (Hothr Rs8 ltac:(reg_neq) ltac:(reg_neq)). lkp. }
            { rewrite (Hothr Rs9 ltac:(reg_neq) ltac:(reg_neq)). lkp. }
            { rewrite (Hothr Rs10 ltac:(reg_neq) ltac:(reg_neq)). lkp. }
            { rewrite (Hothr Rs11 ltac:(reg_neq) ltac:(reg_neq)). lkp. }
            { exact Hoa0. }
            { right. reflexivity. }
          - (* ------- more room: bump [dst] and go round again ------- *)
            iApply (wp_beq_fall_s_sconf Φ (mword_of_int (CIS + 0x58))
                      (mword_of_int 72 : mword 13) Ra4 Ra1 D4 (K - 10)%nat b
                      ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                      ltac:(rgne; rgne; rewrite HD4a1 HD4a4;
                            rewrite (pa_add_eqb _ (n - 1) (rem - 1) Hn164 Hrm164);
                            exact (proj2 (Nat.eqb_neq (n - 1) (rem - 1)) Hne))
                      with "Hcg Hpc Hi58 [-]").
            iIntros (CIDd5 Hsd5) "Hcg Hpc".
            assert (Hq5c : add_vec_int (mword_of_int (CIS + 0x58) : mword 64) 4
                           = mword_of_int (CIS + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hq5c) in "Hpc".
            (* ---- +0x5c: c.mv s1,a5 -- dst += n ---- *)
            iApply (wp_cmv_s_sconf Φ (mword_of_int (CIS + 0x5c)) Rs1 Ra5 D4 (K - 10)%nat b
                      ltac:(vm_compute; discriminate) ltac:(rdok)
                      with "Hcg Hpc Hi5c [-]").
            iIntros (CIDd6 Hsd6) "Hcg Hpc".
            set (D5 := <[Regidx Rs1 := regval_into_reg
                          (add_vec zero_reg (rget D4 Ra5))]> D4).
            assert (Hq5e : add_vec_int (mword_of_int (CIS + 0x5c) : mword 64) 2
                           = mword_of_int (CIS + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hq5e) in "Hpc".
            assert (HD4a5 : D4 !!! Regidx Ra5 = pa_add (pa_add dst done) n) by lkp.
            assert (HD5s1 : D5 !!! Regidx Rs1 = pa_add dst (done + n)).
            { rewrite /D5 upd_eq add_vec_zero_l. rgne. rewrite HD4a5. apply pa_add_assoc. }
            assert (HD5s3 : D5 !!! Regidx Rs3
                            = (mword_of_int (Z.of_nat (rem - n)) : mword 64)) by lkp.
            assert (HD5sp : D5 !!! Regidx csp_rs1 = spr) by lkp.
            assert (HD5s4 : D5 !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)) by lkp.
            assert (HD5s5 : D5 !!! Regidx Rs5 = page_base P.(ud_root)) by lkp.
            assert (HD5s6 : D5 !!! Regidx Rs6 = (mword_of_int (-4096) : mword 64)) by lkp.
            assert (HD5s8 : D5 !!! Regidx Rs8 = v8) by lkp.
            assert (HD5s9 : D5 !!! Regidx Rs9 = v9) by lkp.
            assert (HD5s10 : D5 !!! Regidx Rs10 = v10) by lkp.
            assert (HD5s11 : D5 !!! Regidx Rs11 = v11) by lkp.
            assert (Hf1 : (rem - n <= fuel)%nat) by lia.
            assert (Hf2 : (1 <= rem - n)%nat) by lia.
            assert (Hf3 : (done + n + (rem - n) = maxn)%nat) by lia.
            assert (Hshift : b = false \/ pcur = zero_reg -> (CIDd6 : CPU) = (CIDb : CPU)) by wp_next_chain.
            iDestruct (wp_next_shift Hshift with "Hcont") as "Hcont".
            iApply (IH (done + n)%nat (rem - n)%nat CIDd6 D5 g
                      Hf1 Hf2 Hf3 Hnulg
                      HD5sp HD5s1 HD5s3 HD5s4 HD5s5 HD5s6
                      HD5s8 HD5s9 HD5s10 HD5s11
                      with "Hcg Htext Hpc Hpt Hdst Hcont"). } }
      (* ---- +0x6a falls through: the page is mapped ---- *)
      iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (CIS + 0x6a))
                (mword_of_int 29 : mword 8) (Cregidx (mword_of_int 2)) Ra0 mw (K - 10)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hnz0
                with "Hcg Hpc Hi6a [-]").
      iIntros (CIDv1 Hsv1) "Hcg Hpc".
      assert (Hq6c : add_vec_int (mword_of_int (CIS + 0x6a) : mword 64) 2
                     = mword_of_int (CIS + 0x6c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq6c) in "Hpc".
      iPoseProof (csi_6c with "Htext") as "Hi6c".
      iPoseProof (csi_70 with "Htext") as "Hi70".
      iPoseProof (csi_72 with "Htext") as "Hi72".
      iPoseProof (csi_76 with "Htext") as "Hi76".
      (* ---- +0x6c: sub a3,s2,s7 ---- *)
      iApply (wp_sub_s_sconf Φ (mword_of_int (CIS + 0x6c)) Ra3 Rs2 Rs7
                (sub_vec va0 cur) mw (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(rgne; rgne; rewrite Hmws2 Hmws7; reflexivity)
                with "Hcg Hpc Hi6c [-]").
      iIntros (CIDv2 Hsv2) "Hcg Hpc".
      set (V1 := <[Regidx Ra3 := regval_into_reg (sub_vec va0 cur)]> mw).
      assert (Hq70 : add_vec_int (mword_of_int (CIS + 0x6c) : mword 64) 4
                     = mword_of_int (CIS + 0x70)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq70) in "Hpc".
      (* ---- +0x70: c.add a3,a3,s4 -- n0 = PGSIZE - off ---- *)
      iApply (wp_cadd_s_sconf Φ (mword_of_int (CIS + 0x70)) Ra3 Rs4 V1 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi70 [-]").
      iIntros (CIDv3 Hsv3) "Hcg Hpc".
      set (V2 := <[Regidx Ra3 := regval_into_reg
                    (add_vec (rget V1 Ra3) (rget V1 Rs4))]> V1).
      assert (Hq72 : add_vec_int (mword_of_int (CIS + 0x70) : mword 64) 2
                     = mword_of_int (CIS + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq72) in "Hpc".
      assert (HV2a3 : V2 !!! Regidx Ra3
                      = (mword_of_int (Z.of_nat (4096 - off)) : mword 64)).
      { rewrite /V2 upd_eq. rgne. rgne.
        assert (E1 : V1 !!! Regidx Ra3 = sub_vec va0 cur) by lkp.
        assert (E2 : V1 !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)) by lkp.
        rewrite E1 E2. exact Hnav. }
      assert (HV2s3 : V2 !!! Regidx Rs3 = (mword_of_int (Z.of_nat rem) : mword 64)) by lkp.
      assert (Hpg64 : (Z.of_nat (4096 - off) < 18446744073709551616)%Z).
      { apply (Z.le_lt_trans _ (Z.of_nat 4096%nat));
          [apply Nat2Z.inj_le; lia | vm_compute; reflexivity]. }
      (* ---- +0x72: bgeu s3,a3 -- n = min(n0, rem) ---- *)
      destruct (Nat.leb_spec (4096 - off) rem) as [Hle | Hgt].
      + (* n = 4096 - off *)
        iApply (wp_bgeu_taken_s_sconf Φ (mword_of_int (CIS + 0x72))
                  (mword_of_int 6 : mword 13) Ra3 Rs3 V2 (K - 10)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rgne; rewrite HV2s3 HV2a3;
                        rewrite (bc_ge_moi rem (4096 - off) Hrem64 Hpg64);
                        exact (proj2 (Nat.leb_le (4096 - off) rem) Hle))
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi72 [-]").
        iNext. iIntros (CIDv4 Hsv4) "Hcg Hpc".
        assert (Htgt78 : add_vec (mword_of_int (CIS + 0x72) : mword 64)
                  (sign_extend' 64 (mword_of_int 6 : mword 13))
                  = mword_of_int (CIS + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt78) in "Hpc".
        assert (Hshiftv4 : b = false \/ pcur = zero_reg -> (CIDv4 : CPU) = (CID0 : CPU)) by wp_next_chain.
        iDestruct (wp_next_shift Hshiftv4 with "Hcont") as "Hcontv4".
        iApply ("BODY" $! CIDv4 V2 (4096 - off)%nat
                  with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hpc Hcontv4").
        { lia. } { lia. } { lia. } { exact HV2a3. }
        { lkp. } { lkp. } { lkp. } { lkp. } { lkp. } { lkp. } { lkp. }
        { lkp. } { lkp. } { lkp. } { lkp. } { lkp. } { lkp. }
      + (* n = rem *)
        iApply (wp_bgeu_fall_s_sconf Φ (mword_of_int (CIS + 0x72))
                  (mword_of_int 6 : mword 13) Ra3 Rs3 V2 (K - 10)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rgne; rewrite HV2s3 HV2a3;
                        rewrite (bc_ge_moi rem (4096 - off) Hrem64 Hpg64);
                        exact (proj2 (Nat.leb_gt (4096 - off) rem) Hgt))
                  with "Hcg Hpc Hi72 [-]").
        iIntros (CIDv4 Hsv4) "Hcg Hpc".
        assert (Hq76 : add_vec_int (mword_of_int (CIS + 0x72) : mword 64) 4
                       = mword_of_int (CIS + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq76) in "Hpc".
        (* ---- +0x76: c.mv a3,s3 ---- *)
        iApply (wp_cmv_s_sconf Φ (mword_of_int (CIS + 0x76)) Ra3 Rs3 V2 (K - 10)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi76 [-]").
        iIntros (CIDv5 Hsv5) "Hcg Hpc".
        set (V3 := <[Regidx Ra3 := regval_into_reg (add_vec zero_reg (rget V2 Rs3))]> V2).
        assert (Hq78 : add_vec_int (mword_of_int (CIS + 0x76) : mword 64) 2
                       = mword_of_int (CIS + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq78) in "Hpc".
        assert (HV3a3 : V3 !!! Regidx Ra3 = (mword_of_int (Z.of_nat rem) : mword 64)).
        { rewrite /V3 upd_eq add_vec_zero_l. rgne. exact HV2s3. }
        assert (Hshiftv5 : b = false \/ pcur = zero_reg -> (CIDv5 : CPU) = (CID0 : CPU)) by wp_next_chain.
        iDestruct (wp_next_shift Hshiftv5 with "Hcont") as "Hcontv5".
        iApply ("BODY" $! CIDv5 V3 rem
                  with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hpc Hcontv5").
        { lia. } { lia. } { lia. } { exact HV3a3. }
        { lkp. } { lkp. } { lkp. } { lkp. } { lkp. } { lkp. } { lkp. }
        { lkp. } { lkp. } { lkp. } { lkp. } { lkp. } { lkp. }
  Qed.

  (* ================================================================== *)
  (*  THE CAPSTONE.                                                      *)
  (* ================================================================== *)
  Lemma wp_copyinstr_sconf (Φ : mval -> iProp Σ) (mm : regfile)
      (P : uptd) (maxn : nat) (dst_olds : nat -> bv 8) (K : nat) (b : bool) (p : mword 64)
    : wp_copyinstr_sconf_body Φ mm P maxn dst_olds K b p.
  Proof.
    cbv beta delta [wp_copyinstr_sconf_body].
    intros pcE dst ret_tgt HK Hroot Hmaxr Hmax64.
    assert (E64 : (2 ^ 64)%Z = 18446744073709551616%Z) by (vm_compute; reflexivity).
    rewrite E64 in Hmax64.
    set (sp0 := mm !!! Regidx csp_rs1).
    set (ra0 := mm !!! Regidx Rra).
    set (s00 := mm !!! Regidx Rs0).
    set (s10 := mm !!! Regidx Rs1).
    set (s20 := mm !!! Regidx Rs2).
    set (s30 := mm !!! Regidx Rs3).
    set (s40 := mm !!! Regidx Rs4).
    set (s50 := mm !!! Regidx Rs5).
    set (s60 := mm !!! Regidx Rs6).
    set (s70 := mm !!! Regidx Rs7).
    iIntros "Hcg #Htext Hpc Hpt Hdst Hcont".
    iPoseProof (csi_00 with "Htext") as "Hi00".
    (* ---- +0x00: c.beqz a3 -- the [max == 0] shortcut ---- *)
    destruct (Nat.eqb_spec maxn 0) as [Hz | Hnz].
    - (* ============ max == 0: return -1 with no frame ============ *)
      iPoseProof (csi_b0 with "Htext") as "Hib0".
      iPoseProof (csi_b2 with "Htext") as "Hib2".
      iPoseProof (csi_b6 with "Htext") as "Hib6".
      iPoseProof (csi_ba with "Htext") as "Hiba".
      iApply (wp_cbeqz_taken_s_sconf Φ pcE
                (mword_of_int 88 : mword 8) (Cregidx (mword_of_int 5)) Ra3 mm K b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Hmaxr; rewrite (bc_eqz_moi maxn Hmax64);
                      rewrite Hz; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi00 [-]").
      iNext. iIntros (CIDz1 Hsz1) "Hcg Hpc".
      assert (Htgtb0 : add_vec (pcE : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 88 : mword 8) ('b"0"))))
                = mword_of_int (CIS + 0xb0)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtb0) in "Hpc".
      (* ---- +0xb0: c.li a5,0 ---- *)
      iApply (wp_cli_s_sconf Φ (mword_of_int (CIS + 0xb0)) Ra5
                (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) mm K b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hib0 [-]").
      iIntros (CIDz2 Hsz2) "Hcg Hpc".
      set (Z1 := <[Regidx Ra5 := regval_into_reg (mword_of_int 0 : mword 64)]> mm).
      assert (Hqb2 : add_vec_int (mword_of_int (CIS + 0xb0) : mword 64) 2
                     = mword_of_int (CIS + 0xb2)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hqb2) in "Hpc".
      (* ---- +0xb2: xori a5,a5,1 ---- *)
      iApply (wp_xori_s_sconf Φ (mword_of_int (CIS + 0xb2)) Ra5 Ra5
                (mword_of_int 1 : mword 12) (mword_of_int 1 : mword 64) Z1 K b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(rgne; assert (E : Z1 !!! Regidx Ra5 = (mword_of_int 0 : mword 64)) by lkp;
                      rewrite E; exact cs_xor_0)
                with "Hcg Hpc Hib2 [-]").
      iIntros (CIDz3 Hsz3) "Hcg Hpc".
      set (Z2 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> Z1).
      assert (Hqb6 : add_vec_int (mword_of_int (CIS + 0xb2) : mword 64) 4
                     = mword_of_int (CIS + 0xb6)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hqb6) in "Hpc".
      (* ---- +0xb6: negw a0,a5 ---- *)
      iDestruct (sie_cap_gpr_x0 Z2 K b p Rx0 ltac:(vm_compute; reflexivity) with "Hcg")
        as "[%Hz0 Hcg]".
      iApply (wp_subw_s_sconf Φ (mword_of_int (CIS + 0xb6)) Ra0 Rx0 Ra5 Z2 K b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hib6 [-]").
      iIntros (CIDz4 Hsz4) "Hcg Hpc".
      set (Z3 := <[Regidx Ra0 := regval_into_reg
                    (sign_extend' 64 (sub_vec (subrange_vec_dec (rget Z2 Rx0) 31 0 : mword 32)
                                              (subrange_vec_dec (rget Z2 Ra5) 31 0 : mword 32)))]> Z2).
      assert (Hqba : add_vec_int (mword_of_int (CIS + 0xb6) : mword 64) 4
                     = mword_of_int (CIS + 0xba)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hqba) in "Hpc".
      assert (HZ3a0 : Z3 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64)).
      { rewrite /Z3 upd_eq. rgne. rgne.
        assert (E1 : Z2 !!! Regidx Rx0 = zero_reg) by (rewrite /Z2 upd_ne; [exact Hz0 | reg_neq]).
        assert (E2 : Z2 !!! Regidx Ra5 = (mword_of_int 1 : mword 64)) by lkp.
        rewrite E1 E2. exact cs_negw_1. }
      (* ---- +0xba: c.ret ---- *)
      assert (HZ3ra : Z3 !!! Regidx Rra = mm !!! Regidx Rra) by lkp.
      iApply (wp_cret_s_sconf Φ (mword_of_int (CIS + 0xba)) Rra Z3 K b
                ltac:(vm_compute; discriminate) with "Hcg Hpc Hiba [-]").
      iIntros (CIDz5 Hsz5) "Hcg Hpc".
      iEval (rgne) in "Hpc".
      assert (Hretfin : ret_pc (Z3 !!! Regidx Rra) = ret_tgt) by (rewrite HZ3ra; reflexivity).
      iEval (rewrite Hretfin) in "Hpc".
      iSpecialize ("Hcont" $! CIDz5 with "[]"); [ iPureIntro; wp_next_chain | ].
      iApply ("Hcont" $! Z3 dst_olds with "Hcg Hpc Hpt Hdst [%] [%]").
      { unfold callee_saved. split_and!; lkp. }
      { right. exact HZ3a0. }
    - (* ============ max >= 1: push the frame and loop ============ *)
      assert (Hmax1 : (1 <= maxn)%nat) by lia.
      iPoseProof (csi_02 with "Htext") as "Hi02".
      iPoseProof (csi_04 with "Htext") as "Hi04".
      iPoseProof (csi_06 with "Htext") as "Hi06".
      iPoseProof (csi_08 with "Htext") as "Hi08".
      iPoseProof (csi_0a with "Htext") as "Hi0a".
      iPoseProof (csi_0c with "Htext") as "Hi0c".
      iPoseProof (csi_0e with "Htext") as "Hi0e".
      iPoseProof (csi_10 with "Htext") as "Hi10".
      iPoseProof (csi_12 with "Htext") as "Hi12".
      iPoseProof (csi_14 with "Htext") as "Hi14".
      iPoseProof (csi_16 with "Htext") as "Hi16".
      iPoseProof (csi_18 with "Htext") as "Hi18".
      iPoseProof (csi_1a with "Htext") as "Hi1a".
      iPoseProof (csi_1c with "Htext") as "Hi1c".
      iPoseProof (csi_1e with "Htext") as "Hi1e".
      iPoseProof (csi_20 with "Htext") as "Hi20".
      iPoseProof (csi_22 with "Htext") as "Hi22".
      iPoseProof (csi_24 with "Htext") as "Hi24".
      iApply (wp_cbeqz_fall_s_sconf Φ pcE
                (mword_of_int 88 : mword 8) (Cregidx (mword_of_int 5)) Ra3 mm K b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Hmaxr; rewrite (bc_eqz_moi maxn Hmax64);
                      exact (proj2 (Nat.eqb_neq maxn 0) Hnz))
                with "Hcg Hpc Hi00 [-]").
      iIntros (CIDp0 Hsp0') "Hcg Hpc".
      assert (Hq02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (CIS + 0x02))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq02) in "Hpc".
      (* ---- +0x02: c.addi16sp sp,-80 (frame push) ---- *)
      iApply (wp_caddi16sp_push_s_sconf Φ (mword_of_int (CIS + 0x02))
                (mword_of_int 59 : mword 6) mm K 10 b
                ltac:(lia) (cs_push (mm !!! Regidx csp_rs1))
                with "Hcg Hpc Hi02 [-]").
      iIntros (CIDp1 Hsp1) "Hcg Hframe Hpc".
      set (M1 := <[Regidx csp_rs1 := regval_into_reg
                    (add_vec (mm !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> mm).
      assert (Hq04 : add_vec_int (mword_of_int (CIS + 0x02) : mword 64) 2
                     = mword_of_int (CIS + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq04) in "Hpc".
      assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 10)
        by (rewrite /M1 upd_eq; apply cs_push).
      iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
      iDestruct "Hframe" as "(K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & _)".
      iDestruct "K1" as (u1) "Hb1".   iDestruct "K2" as (u2) "Hb2".
      iDestruct "K3" as (u3) "Hb3".   iDestruct "K4" as (u4) "Hb4".
      iDestruct "K5" as (u5) "Hb5".   iDestruct "K6" as (u6) "Hb6".
      iDestruct "K7" as (u7) "Hb7".   iDestruct "K8" as (u8) "Hb8".
      iDestruct "K9" as (u9) "Hb9".   iDestruct "K10" as (u10) "Hb10".
      assert (Hpa1 : add_vec (M1 !!! Regidx csp_rs1)
                (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = pa_stk sp0 1)
        by (rewrite HM1sp; slot_addr).
      assert (Hpa2 : add_vec (M1 !!! Regidx csp_rs1)
                (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000"))) = pa_stk sp0 2)
        by (rewrite HM1sp; slot_addr).
      assert (Hpa3 : add_vec (M1 !!! Regidx csp_rs1)
                (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 3)
        by (rewrite HM1sp; slot_addr).
      assert (Hpa4 : add_vec (M1 !!! Regidx csp_rs1)
                (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 4)
        by (rewrite HM1sp; slot_addr).
      assert (Hpa5 : add_vec (M1 !!! Regidx csp_rs1)
                (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 5)
        by (rewrite HM1sp; slot_addr).
      assert (Hpa6 : add_vec (M1 !!! Regidx csp_rs1)
                (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 6)
        by (rewrite HM1sp; slot_addr).
      assert (Hpa7 : add_vec (M1 !!! Regidx csp_rs1)
                (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 7)
        by (rewrite HM1sp; slot_addr).
      assert (Hpa8 : add_vec (M1 !!! Regidx csp_rs1)
                (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 8)
        by (rewrite HM1sp; slot_addr).
      assert (Hpa9 : add_vec (M1 !!! Regidx csp_rs1)
                (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 9)
        by (rewrite HM1sp; slot_addr).
      (* ---- +0x04 .. +0x14: save ra / s0 .. s7 ---- *)
      iEval (rewrite -Hpa1) in "Hb1".
      iApply (wp_csdsp_s_sconf Φ (mword_of_int (CIS + 0x04))
                (mword_of_int 9 : mword 6) Rra M1 (K - 10)%nat u1 b
                with "Hcg Hpc Hi04 Hb1 [-]").
      iIntros (CIDp2 Hsp2) "Hcg Hpc Hb1".
      assert (Hq06 : add_vec_int (mword_of_int (CIS + 0x04) : mword 64) 2
                     = mword_of_int (CIS + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq06) in "Hpc".
      iEval (rewrite -Hpa2) in "Hb2".
      iApply (wp_csdsp_s_sconf Φ (mword_of_int (CIS + 0x06))
                (mword_of_int 8 : mword 6) Rs0 M1 (K - 10)%nat u2 b
                with "Hcg Hpc Hi06 Hb2 [-]").
      iIntros (CIDp3 Hsp3) "Hcg Hpc Hb2".
      assert (Hq08 : add_vec_int (mword_of_int (CIS + 0x06) : mword 64) 2
                     = mword_of_int (CIS + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq08) in "Hpc".
      iEval (rewrite -Hpa3) in "Hb3".
      iApply (wp_csdsp_s_sconf Φ (mword_of_int (CIS + 0x08))
                (mword_of_int 7 : mword 6) Rs1 M1 (K - 10)%nat u3 b
                with "Hcg Hpc Hi08 Hb3 [-]").
      iIntros (CIDp4 Hsp4) "Hcg Hpc Hb3".
      assert (Hq0a : add_vec_int (mword_of_int (CIS + 0x08) : mword 64) 2
                     = mword_of_int (CIS + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq0a) in "Hpc".
      iEval (rewrite -Hpa4) in "Hb4".
      iApply (wp_csdsp_s_sconf Φ (mword_of_int (CIS + 0x0a))
                (mword_of_int 6 : mword 6) Rs2 M1 (K - 10)%nat u4 b
                with "Hcg Hpc Hi0a Hb4 [-]").
      iIntros (CIDp5 Hsp5) "Hcg Hpc Hb4".
      assert (Hq0c : add_vec_int (mword_of_int (CIS + 0x0a) : mword 64) 2
                     = mword_of_int (CIS + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq0c) in "Hpc".
      iEval (rewrite -Hpa5) in "Hb5".
      iApply (wp_csdsp_s_sconf Φ (mword_of_int (CIS + 0x0c))
                (mword_of_int 5 : mword 6) Rs3 M1 (K - 10)%nat u5 b
                with "Hcg Hpc Hi0c Hb5 [-]").
      iIntros (CIDp6 Hsp6) "Hcg Hpc Hb5".
      assert (Hq0e : add_vec_int (mword_of_int (CIS + 0x0c) : mword 64) 2
                     = mword_of_int (CIS + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq0e) in "Hpc".
      iEval (rewrite -Hpa6) in "Hb6".
      iApply (wp_csdsp_s_sconf Φ (mword_of_int (CIS + 0x0e))
                (mword_of_int 4 : mword 6) Rs4 M1 (K - 10)%nat u6 b
                with "Hcg Hpc Hi0e Hb6 [-]").
      iIntros (CIDp7 Hsp7) "Hcg Hpc Hb6".
      assert (Hq10 : add_vec_int (mword_of_int (CIS + 0x0e) : mword 64) 2
                     = mword_of_int (CIS + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq10) in "Hpc".
      iEval (rewrite -Hpa7) in "Hb7".
      iApply (wp_csdsp_s_sconf Φ (mword_of_int (CIS + 0x10))
                (mword_of_int 3 : mword 6) Rs5 M1 (K - 10)%nat u7 b
                with "Hcg Hpc Hi10 Hb7 [-]").
      iIntros (CIDp8 Hsp8) "Hcg Hpc Hb7".
      assert (Hq12 : add_vec_int (mword_of_int (CIS + 0x10) : mword 64) 2
                     = mword_of_int (CIS + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq12) in "Hpc".
      iEval (rewrite -Hpa8) in "Hb8".
      iApply (wp_csdsp_s_sconf Φ (mword_of_int (CIS + 0x12))
                (mword_of_int 2 : mword 6) Rs6 M1 (K - 10)%nat u8 b
                with "Hcg Hpc Hi12 Hb8 [-]").
      iIntros (CIDp9 Hsp9) "Hcg Hpc Hb8".
      assert (Hq14 : add_vec_int (mword_of_int (CIS + 0x12) : mword 64) 2
                     = mword_of_int (CIS + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq14) in "Hpc".
      iEval (rewrite -Hpa9) in "Hb9".
      iApply (wp_csdsp_s_sconf Φ (mword_of_int (CIS + 0x14))
                (mword_of_int 1 : mword 6) Rs7 M1 (K - 10)%nat u9 b
                with "Hcg Hpc Hi14 Hb9 [-]").
      iIntros (CIDp10 Hsp10) "Hcg Hpc Hb9".
      assert (Hq16 : add_vec_int (mword_of_int (CIS + 0x14) : mword 64) 2
                     = mword_of_int (CIS + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq16) in "Hpc".
      (* normalize the nine saved cells *)
      assert (HM1ra : M1 !!! Regidx Rra = ra0) by lkp.
      assert (HM1s0 : M1 !!! Regidx Rs0 = s00) by lkp.
      assert (HM1s1 : M1 !!! Regidx Rs1 = s10) by lkp.
      assert (HM1s2 : M1 !!! Regidx Rs2 = s20) by lkp.
      assert (HM1s3 : M1 !!! Regidx Rs3 = s30) by lkp.
      assert (HM1s4 : M1 !!! Regidx Rs4 = s40) by lkp.
      assert (HM1s5 : M1 !!! Regidx Rs5 = s50) by lkp.
      assert (HM1s6 : M1 !!! Regidx Rs6 = s60) by lkp.
      assert (HM1s7 : M1 !!! Regidx Rs7 = s70) by lkp.
      iEval (rgne; rewrite Hpa1 HM1ra) in "Hb1".
      iEval (rgne; rewrite Hpa2 HM1s0) in "Hb2".
      iEval (rgne; rewrite Hpa3 HM1s1) in "Hb3".
      iEval (rgne; rewrite Hpa4 HM1s2) in "Hb4".
      iEval (rgne; rewrite Hpa5 HM1s3) in "Hb5".
      iEval (rgne; rewrite Hpa6 HM1s4) in "Hb6".
      iEval (rgne; rewrite Hpa7 HM1s5) in "Hb7".
      iEval (rgne; rewrite Hpa8 HM1s6) in "Hb8".
      iEval (rgne; rewrite Hpa9 HM1s7) in "Hb9".
      (* ---- +0x16: c.addi4spn s0,sp,80 (s0's VALUE is never read) ---- *)
      iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (CIS + 0x16))
                (Cregidx (mword_of_int 0)) (mword_of_int 20 : mword 8) Rs0 M1 (K - 10)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rdok)
                with "Hcg Hpc Hi16 [-]").
      iIntros (CIDp11 Hsp11) "Hcg Hpc".
      set (M2 := <[Regidx Rs0 := regval_into_reg
                    (add_vec (M1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> M1).
      assert (Hq18 : add_vec_int (mword_of_int (CIS + 0x16) : mword 64) 2
                     = mword_of_int (CIS + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq18) in "Hpc".
      (* ---- +0x18: c.mv s5,a0 -- the page table ---- *)
      iApply (wp_cmv_s_sconf Φ (mword_of_int (CIS + 0x18)) Rs5 Ra0 M2 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi18 [-]").
      iIntros (CIDp12 Hsp12) "Hcg Hpc".
      set (M3 := <[Regidx Rs5 := regval_into_reg (add_vec zero_reg (rget M2 Ra0))]> M2).
      assert (Hq1a : add_vec_int (mword_of_int (CIS + 0x18) : mword 64) 2
                     = mword_of_int (CIS + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq1a) in "Hpc".
      (* ---- +0x1a: c.mv s1,a1 -- dst ---- *)
      iApply (wp_cmv_s_sconf Φ (mword_of_int (CIS + 0x1a)) Rs1 Ra1 M3 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi1a [-]").
      iIntros (CIDp13 Hsp13) "Hcg Hpc".
      set (M4 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (rget M3 Ra1))]> M3).
      assert (Hq1c : add_vec_int (mword_of_int (CIS + 0x1a) : mword 64) 2
                     = mword_of_int (CIS + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq1c) in "Hpc".
      (* ---- +0x1c: c.mv s7,a2 -- srcva ---- *)
      iApply (wp_cmv_s_sconf Φ (mword_of_int (CIS + 0x1c)) Rs7 Ra2 M4 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi1c [-]").
      iIntros (CIDp14 Hsp14) "Hcg Hpc".
      set (M5 := <[Regidx Rs7 := regval_into_reg (add_vec zero_reg (rget M4 Ra2))]> M4).
      assert (Hq1e : add_vec_int (mword_of_int (CIS + 0x1c) : mword 64) 2
                     = mword_of_int (CIS + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq1e) in "Hpc".
      (* ---- +0x1e: c.mv s3,a3 -- max ---- *)
      iApply (wp_cmv_s_sconf Φ (mword_of_int (CIS + 0x1e)) Rs3 Ra3 M5 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi1e [-]").
      iIntros (CIDp15 Hsp15) "Hcg Hpc".
      set (M6 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (rget M5 Ra3))]> M5).
      assert (Hq20 : add_vec_int (mword_of_int (CIS + 0x1e) : mword 64) 2
                     = mword_of_int (CIS + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq20) in "Hpc".
      (* ---- +0x20: c.lui s6,0xfffff -- the PGROUNDDOWN mask ---- *)
      iApply (wp_clui_s_sconf Φ (mword_of_int (CIS + 0x20)) Rs6
                (sign_extend' 20 (mword_of_int 63 : mword 6))
                (mword_of_int (-4096) : mword 64) M6 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                lui_m4096 with "Hcg Hpc Hi20 [-]").
      iIntros (CIDp16 Hsp16) "Hcg Hpc".
      set (M7 := <[Regidx Rs6 := regval_into_reg (mword_of_int (-4096) : mword 64)]> M6).
      assert (Hq22 : add_vec_int (mword_of_int (CIS + 0x20) : mword 64) 2
                     = mword_of_int (CIS + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq22) in "Hpc".
      (* ---- +0x22: c.lui s4,0x1 -- PGSIZE ---- *)
      iApply (wp_clui_s_sconf Φ (mword_of_int (CIS + 0x22)) Rs4
                (sign_extend' 20 (mword_of_int 1 : mword 6))
                (mword_of_int 4096 : mword 64) M7 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                lui_4096 with "Hcg Hpc Hi22 [-]").
      iIntros (CIDp17 Hsp17) "Hcg Hpc".
      set (M8 := <[Regidx Rs4 := regval_into_reg (mword_of_int 4096 : mword 64)]> M7).
      assert (Hq24 : add_vec_int (mword_of_int (CIS + 0x22) : mword 64) 2
                     = mword_of_int (CIS + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq24) in "Hpc".
      (* ---- +0x24: c.j +0x5e -- enter the outer loop ---- *)
      iApply (wp_cj_s_sconf Φ (mword_of_int (CIS + 0x24))
                (sign_extend' 21 (concat_vec (mword_of_int 29 : mword 11) ('b"0")))
                M8 (K - 10)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi24 [-]").
      iIntros (CIDp18 Hsp18). iNext. iIntros "Hcg Hpc".
      assert (Htgt5e : add_vec (mword_of_int (CIS + 0x24) : mword 64)
                (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 29 : mword 11) ('b"0"))))
                = mword_of_int (CIS + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt5e) in "Hpc".
      (* the loop's entry facts *)
      assert (HM8s1 : M8 !!! Regidx Rs1 = pa_add dst 0).
      { rewrite pa_add_0. lkp. }
      assert (HM8s3 : M8 !!! Regidx Rs3 = (mword_of_int (Z.of_nat maxn) : mword 64)).
      { assert (E : M5 !!! Regidx Ra3 = (mword_of_int (Z.of_nat maxn) : mword 64)) by lkp.
        rewrite /M8 upd_ne; [| reg_neq]. rewrite /M7 upd_ne; [| reg_neq].
        rewrite /M6 upd_eq add_vec_zero_l. rgne. exact E. }
      assert (HM8s5 : M8 !!! Regidx Rs5 = page_base P.(ud_root)).
      { assert (E : M2 !!! Regidx Ra0 = page_base P.(ud_root)) by lkp.
        rewrite /M8 upd_ne; [| reg_neq]. rewrite /M7 upd_ne; [| reg_neq].
        rewrite /M6 upd_ne; [| reg_neq]. rewrite /M5 upd_ne; [| reg_neq].
        rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_eq add_vec_zero_l. rgne. exact E. }
      assert (HM8sp : M8 !!! Regidx csp_rs1 = pa_stk sp0 10) by lkp.
      (* ---- the loop ---- *)
      assert (HM8s4 : M8 !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)) by lkp.
      assert (HM8s6 : M8 !!! Regidx Rs6 = (mword_of_int (-4096) : mword 64)) by lkp.
      assert (HM8s8 : M8 !!! Regidx Rs8 = mm !!! Regidx Rs8) by lkp.
      assert (HM8s9 : M8 !!! Regidx Rs9 = mm !!! Regidx Rs9) by lkp.
      assert (HM8s10 : M8 !!! Regidx Rs10 = mm !!! Regidx Rs10) by lkp.
      assert (HM8s11 : M8 !!! Regidx Rs11 = mm !!! Regidx Rs11) by lkp.
      assert (Hg1 : (maxn <= maxn)%nat) by lia.
      assert (Hg3 : (0 + maxn = maxn)%nat) by lia.
      iApply (cs_loop Φ P K dst (pa_stk sp0 10) maxn
                (mm !!! Regidx Rs8) (mm !!! Regidx Rs9)
                (mm !!! Regidx Rs10) (mm !!! Regidx Rs11) b p
                HK Hmax64 maxn 0%nat maxn CIDp18 M8 dst_olds
                Hg1 Hmax1 Hg3 (bb_nonul_0 dst_olds)
                HM8sp HM8s1 HM8s3 HM8s4 HM8s5 HM8s6
                HM8s8 HM8s9 HM8s10 HM8s11
                with "Hcg Htext Hpc Hpt Hdst [-]").
      iIntros (CIDj Hsj mj res g) "%Hjsp %Hj8 %Hj9 %Hj10 %Hj11 %Hja0 %Hjret Hcg Hpc Hpt Hdst".
      (* ---- the epilogue ---- *)
      iApply (cs_epilogue Φ mm mj K res sp0 ra0 s00 s10 s20 s30 s40 s50 s60 s70 u10 b p
                ltac:(lia) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                eq_refl eq_refl eq_refl
                Hjsp Hja0 Hj8 Hj9 Hj10 Hj11
                with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 [-]").
      iIntros (CIDf Hsf mf) "[%Hcsf %Hfa0] Hcg Hpc".
      iSpecialize ("Hcont" $! CIDf with "[]"); [ iPureIntro; wp_next_chain | ].
      iApply ("Hcont" $! mf g with "Hcg Hpc Hpt Hdst [%] [%]").
      { exact Hcsf. }
      { rewrite Hfa0. exact Hjret. }
  Qed.

End ProofCopyinstr.

End CopyinstrProof.
