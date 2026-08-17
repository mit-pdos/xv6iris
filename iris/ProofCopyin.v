(* ProofCopyin.v -- copyin() over the SIE-agnostic sconf world.

     int copyin(pagetable_t pagetable, uint64 psz, char *dst, uint64 srcva,
                uint64 len) {
       while (len > 0) {
         va0 = PGROUNDDOWN(srcva);
         pa0 = walkaddr(pagetable, va0);
         if (pa0 == 0 && (pa0 = vmfault(pagetable, psz, va0, 1)) == 0) return -1;
         n = PGSIZE - (srcva - va0);  if (n > len) n = len;
         memmove(dst, (void * )(pa0 + (srcva - va0)), n);
         len -= n; dst += n; srcva = va0 + PGSIZE;
       }
       return 0;
     }

   Spec of record: SpecCopyin.v -- stated at the [proc_pt] altitude, so the
   whole loop is bracketed by ProcPtOwn's dovetail lemmas: [proc_pt_acc_rep0]
   opens the table into the exact [pt_rep0] view walkaddr consumes,
   [proc_pt_rebuild] closes it again before vmfault (which wants it CLOSED),
   and the two PAGE ACCESSORS [proc_pt_page_acc] / [proc_pt_page_acc_vmfault]
   borrow the one page the chunk is copied out of.

   THE MACHINE (offsets into CodeCopyin.v's byte-verified listing):

     +0x00 beqz a4,+0x98          len == 0: return 0 with NO frame pushed
     +0x02..+0x1c                 the 96-byte (12-slot) prologue -- TWELVE
                                  saves now (ra,s0..s10), so slot 12 is live
     +0x1e..+0x2c                 s7=pagetable s9=psz s5=dst s2=srcva s4=len
                                  s8=-4096 s10=1 s6=4096
     +0x2e j +0x5a                enter the loop at its HEAD

     +0x5a and s3,s2,s8           va0 = PGROUNDDOWN(srcva)      <-- loop head
     +0x62 jal walkaddr(s7,s3)
     +0x66 bnez a0 -> +0x30       mapped
     +0x70 jal vmfault(s7,s9,s3,1)
     +0x74 bnez a0 -> +0x30       faulted in
     +0x76 li a0,-1; j +0x7c      unmapped and unfaultable

     +0x30 s1 = (va0 - srcva) + 4096          <-- the chunk, both arms join
     +0x36 bgeu s4,s1 -> +0x3c else s1 = s4   n = min(4096-off, rem)
     +0x3c a1 = (srcva - va0) + a0 ; a2 = sext.w s1 ; a0 = s5
     +0x48 jal memmove
     +0x4c s4 -= s1 ; s5 += s1 ; s2 = va0 + 4096
     +0x56 beqz s4 -> +0x7a       done: return 0; else fall through to +0x5a

     +0x7c..+0x96                 the 12-slot epilogue, reached by BOTH the
                                  -1 exit (through +0x78) and the 0 exit
     +0x98 li a0,0; ret           the frameless len == 0 return

   THE psz BUMP (xv6 `4f2fc8b`).  The size arrives in a1, shifting dst/srcva/
   len down to a2/a3/a4, and gcc parks it in s9 for the whole loop -- which
   pushed the constant 1 (vmfault's `read` argument) out to s10 and made the
   frame's twelfth slot live.  The two proc cells [p_sz] / [p_pagetable] are
   gone from every contract in the family, so nothing is threaded for them.

   THREE STRUCTURAL POINTS.

   1. THE USER-SIDE CURSOR HAS NO INVARIANT.  The postcondition says nothing
      about where the bytes came from, so at the loop head [s2] is an
      arbitrary [mword 64]; everything the iteration needs about it -- the
      page offset [off = uint srcva mod 4096], and hence [1 <= n] -- is
      re-derived from [ProcPtOwn.pgd_unsigned] on the spot.  Likewise the
      DESTINATION BUFFER is carried WHOLE at existential contents: there is no
      copied-prefix / untouched-suffix split, because [ByteBuf.bb_split3] re-derives
      the chunk each iteration and [bb_join3] puts it back.

   2. FUEL INDUCTION.  The measure decreases by [n = min(4096-off, rem)], not
      by 1, so [induction rem] does not fit; the loop lemma takes a [fuel]
      with [rem <= fuel] and inducts on that.  Unlike [ProofMemmove.mm_loop]
      the back edge is the FALL-THROUGH of the [beqz] at +0x52, not a taken
      branch, so no [iNext] is needed against the IH.

   3. TWO JOINS, BOTH BY [iAssert]ed CONTINUATIONS (vmfault.md item F).
      [CHUNK] joins the walkaddr-hit and vmfault-hit arms at +0x2c -- it takes
      the borrowed page, its returning wand, the descriptor, the destination
      buffer and the exit continuation as WAND ARGUMENTS, because the two arms
      supply different pages/descriptors and the give-up arm still needs the
      buffer and the continuation.  Only the persistent context is captured.
      [BODY] joins the two [bgeu] arms at +0x38 over the chunk length [n]; it
      captures everything, since nothing between +0x32 and +0x38 touches it.
      The function's own exits need no join at all: the loop lemma's single
      continuation IS the +0x76 join, so the epilogue is written once, in
      [ci_epilogue].

   The two base-encoding ALU leaves this proof needs -- [wp_and_s_sconf] (the
   PGROUNDDOWN mask into a different register) and [wp_addiw_s_sconf] (the
   [sext.w] at +0x3c) -- are in WpSconfAlu.v.

   TWO CONVENTIONS WORTH COPYING.

   * NEVER [rewrite] a computed value INSIDE the register map.  Every write
     whose value is not already closed ([c.add], [sext.w], [c.mv rd,rs]) is
     [set] at the leaf's RAW output and the interesting fact is proved as a
     LOOKUP -- [rewrite /Mk upd_eq <the operand facts>; exact <the bv lemma>].
     [exact] closes up to conversion, so it is immune to the type-ascription
     and [regval_into_reg] noise that makes an [iEval (rewrite ...)] on the
     map fail to find its pattern; everything downstream only ever reads the
     map through [lkp], which does not care what the value looks like.

   * [destruct (Nat.eqb_spec x y)] / [(Nat.leb_spec x y)] SUBSTITUTES the
     boolean into the recorded comparison fact as well, so in each arm that
     fact is ALREADY the literal -- discharge the branch premise with
     [first [ exact Hcmp | <the rewrite> ]]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import CalleeSaved StackOwn.
Require Import IntrDefs WpSmodeIntr.
Require Import HartTp WpNext.
Require Import WpLock.
Require Import KallocInv.
Require Import ByteCursor ByteBuf.
Require Import PtreeType.
Require Import UserPtTree.
Require Import CpuOwn.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import CodeCopyin.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecWalkaddr SpecVmfault SpecMemmove.
Require Import SpecCopyin.
Require Import KernelRvcDecode.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.


(* ===================================================================== *)
(* Pure bridges.                                                          *)
(*                                                                        *)
(*   Everything this proof needs about the loop counter, the byte cursor   *)
(*   and PGROUNDDOWN now lives at its own altitude and is shared with      *)
(*   copyout: ByteCursor.v ([bc_eqz_moi] / [bc_ge_moi] / [bc_sub_nat] /    *)
(*   [pa_add_bump] / [pa_add_comm]), ProcPtOwn.v ([pgd_idem] / [pgd_off] / *)
(*   [pgd_room]), RiscvExtras.v ([sextw_moi]), KernelRvcDecode.v           *)
(*   ([frame_cancel_96] / [lui_m4096] / [lui_4096]), KallocInv.v           *)
(*   ([page_valid_neq_zero]) and ByteBuf.v ([bb_split3] / [bb_join3]).     *)
(*   All that is left here is the [nat]-vs-[Z] glue for this loop's own    *)
(*   page offset.                                                          *)
(* ===================================================================== *)

(* the page offset, as a [nat] -- and the two facts about it that keep
   [bv_unsigned] out of every later [lia] goal (the zify-hook rule) *)
Lemma ci_off_id (z : Z) : Z.of_nat (Z.to_nat (z mod 4096)) = (z mod 4096)%Z.
Proof. rewrite Z2Nat.id; [reflexivity | apply Z.mod_pos_bound; lia]. Qed.

Lemma ci_off_lt (z : Z) : (Z.to_nat (z mod 4096) < 4096)%nat.
Proof. pose proof (Z.mod_pos_bound z 4096 ltac:(lia)) as [H1 H2]. lia. Qed.


(* ===================================================================== *)
(* THE WHOLE FUNCTION.                                                    *)
(* ===================================================================== *)

Module CopyinProof (Walkaddr : WALKADDR) (Vmfault : VMFAULT) (Memmove : MEMMOVE)
  : COPYIN.

Section ProofCopyin.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {kt : ktier}.
  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
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

  (* [Regidx a <> Regidx b] for two CONCRETE literals -- [rd_ok]'s Rtp half
     needs to peel [Regidx]'s injectivity before the [mword] disequality is
     [vm_compute]-decidable (durable-notes' [rdok] does the same, folded into
     a pair with the sp half; here only the Rtp half is ever needed). *)
  Ltac ridx_neq :=
    let H1 := fresh in let H2 := fresh in
    intro H1; injection H1 as H2; vm_compute in H2; congruence.

  (* one frame slot's address, in the [c.sdsp]/[c.ldsp] displacement spelling.
     Stated at a CONCRETE slot index at every call site: a symbolic one would
     put a [vm_compute] on a goal mentioning it. *)
  Ltac slot_addr :=
    unfold pa_stk, add_vec_int; rewrite pa_stk_off2;
    apply f_equal; apply bv_eq; vm_compute; reflexivity.

  (* peel a register lookup through the insert tower via the [upd_eq]/[upd_ne]
     LEMMAS, one layer at a time (values stay opaque -- optimization.md's
     [peel_reg]), then close against the base map's own fact. *)
  Ltac lkp :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | match goal with |- context [ ?M !!! _ ] => is_var M; progress unfold M end ];
    repeat rewrite add_vec_zero_l;
    first [ reflexivity | assumption ].

  (* [rget]'s equation restated with [tp_pin] already unfolded, so it
     [rewrite]s a goal that already shows [tp_pin m !!! Regidx k] (e.g. after
     [callee_saved_lookup] against a callee invoked at a [tp_pin]ned map)
     without an intervening [rgne]. *)
  Local Lemma tp_pin_ne `{CIDx : CpuId} (m : regfile) (k : mword 5) :
    Regidx k <> Regidx Rtp -> tp_pin m !!! Regidx k = m !!! Regidx k.
  Proof. exact (rget_ne m k). Qed.

  (* copyin's own map is threaded GENERICALLY (SpecCopyin states no raw-tp
     premise on it: "delete a meaningless tp statement", durable-notes), but
     vmfault's contract still needs one (its kalloc/acquire chain reads tp
     mid-body, the push_off cid convention).  [sie_cap_gpr] is insensitive to
     WHICH representative of the resource's map we use -- [tp_pin] only
     touches index 4, which neither [sie_cap] (keyed on sp) nor a second
     [tp_pin] (idempotent, [tp_pin_id] off [rget_tp]) can tell apart -- so a
     caller with no raw-tp fact in hand may simply RE-POINT its map at its own
     [tp_pin] image, for which the raw fact is now true BY CONSTRUCTION. *)
  Local Lemma sie_cap_gpr_tp_pin `{CIDx : CpuId} (m : regfile) (n : nat) (b : bool) (pcur : mword 64) :
    sie_cap_gpr kt m n b pcur -∗ sie_cap_gpr kt (tp_pin m) n b pcur.
  Proof.
    rewrite /sie_cap_gpr /sie_cap (tp_pin_sp m).
    assert (Htp2 : tp_pin (tp_pin m) = tp_pin m) by (apply tp_pin_id; exact (rget_tp m)).
    rewrite Htp2. iIntros "$".
  Qed.

  (* ================================================================== *)
  (*  THE EPILOGUE (+0x7c .. +0x96).  Both exits reach it, so it is       *)
  (*  written once; nothing is shrink-wrapped, so it needs no existential *)
  (*  slot arguments.  All TWELVE slots are live now: the psz bump pushed *)
  (*  vmfault's [read] constant out to s10, which the prologue saves.     *)
  (* ================================================================== *)
  Local Lemma ci_epilogue `{CID0 : CpuId}
      (mm mj : regfile) (K ncnt : nat) (eb b : bool) (res sp0 pcur : mword 64) (lks : gset string) :
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))) in
    (12 <= K)%nat ->
    mm !!! Regidx csp_rs1 = sp0 ->
    mj !!! Regidx csp_rs1 = spr ->
    mj !!! Regidx Ra0 = res ->
    mj !!! Regidx Rs11 = mm !!! Regidx Rs11 ->
    sie_cap_gpr kt mj (K - 12) b pcur -∗
    cpu_own ncnt eb pcur b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.copyin + 0x7c) : mword 64) -∗
    pa_stk sp0 1 ↦₈[kt] (mm !!! Regidx Rra) -∗
    pa_stk sp0 2 ↦₈[kt] (mm !!! Regidx Rs0) -∗
    pa_stk sp0 3 ↦₈[kt] (mm !!! Regidx Rs1) -∗
    pa_stk sp0 4 ↦₈[kt] (mm !!! Regidx Rs2) -∗
    pa_stk sp0 5 ↦₈[kt] (mm !!! Regidx Rs3) -∗
    pa_stk sp0 6 ↦₈[kt] (mm !!! Regidx Rs4) -∗
    pa_stk sp0 7 ↦₈[kt] (mm !!! Regidx Rs5) -∗
    pa_stk sp0 8 ↦₈[kt] (mm !!! Regidx Rs6) -∗
    pa_stk sp0 9 ↦₈[kt] (mm !!! Regidx Rs7) -∗
    pa_stk sp0 10 ↦₈[kt] (mm !!! Regidx Rs8) -∗
    pa_stk sp0 11 ↦₈[kt] (mm !!! Regidx Rs9) -∗
    pa_stk sp0 12 ↦₈[kt] (mm !!! Regidx Rs10) -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mf : regfile,
      sie_cap_gpr kt mf K b pcur -∗
      cpu_own ncnt eb pcur b lks -∗
      pc_is (ret_pc (mm !!! Regidx Rra)) -∗
      ⌜callee_saved mm mf⌝ -∗
      ⌜mf !!! Regidx Ra0 = res⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros spr HK Hmmsp Hjsp Hja0 Hjs11.
    iIntros "Hcg Hcnt #Htext Hpc Hk1 Hk2 Hk3 Hk4 Hk5 Hk6 Hk7 Hk8 Hk9 Hk10 Hk11 Hk12 Hcont".
    iPoseProof (cii_7c with "Htext") as "Hi7c".
    iPoseProof (cii_7e with "Htext") as "Hi7e".
    iPoseProof (cii_80 with "Htext") as "Hi80".
    iPoseProof (cii_82 with "Htext") as "Hi82".
    iPoseProof (cii_84 with "Htext") as "Hi84".
    iPoseProof (cii_86 with "Htext") as "Hi86".
    iPoseProof (cii_88 with "Htext") as "Hi88".
    iPoseProof (cii_8a with "Htext") as "Hi8a".
    iPoseProof (cii_8c with "Htext") as "Hi8c".
    iPoseProof (cii_8e with "Htext") as "Hi8e".
    iPoseProof (cii_90 with "Htext") as "Hi90".
    iPoseProof (cii_92 with "Htext") as "Hi92".
    iPoseProof (cii_94 with "Htext") as "Hi94".
    iPoseProof (cii_96 with "Htext") as "Hi96".
    (* the twelve slot addresses, in the [c.ldsp] displacement spelling *)
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (unfold spr; slot_addr).
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (unfold spr; slot_addr).
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (unfold spr; slot_addr).
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (unfold spr; slot_addr).
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (unfold spr; slot_addr).
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 6) by (unfold spr; slot_addr).
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (unfold spr; slot_addr).
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (unfold spr; slot_addr).
    assert (Hb9 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 9) by (unfold spr; slot_addr).
    assert (Hb10 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 10) by (unfold spr; slot_addr).
    assert (Hb11 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 11) by (unfold spr; slot_addr).
    assert (Hb12 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk sp0 12) by (unfold spr; slot_addr).
    assert (Hsprstk : pa_stk sp0 12 = spr).
    { unfold spr, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    (* --- +0x7c .. +0x92 : twelve c.ldsp ------------------------------ *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x7c)) (mword_of_int 11 : mword 6) Rra
              mj (K - 12) (mm !!! Regidx Rra) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7c [Hk1]").
    { iEval (rewrite Hjsp Hb1). iExact "Hk1". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hk1". iEval (rewrite Hjsp Hb1) in "Hk1".
    set (E1 := <[Regidx Rra := regval_into_reg (mm !!! Regidx Rra)]> mj).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp7e : add_vec_int (mword_of_int (KernelSyms.copyin + 0x7c) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7e) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x7e)) (mword_of_int 10 : mword 6) Rs0
              E1 (K - 12) (mm !!! Regidx Rs0) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7e [Hk2]").
    { iEval (rewrite HE1sp Hb2). iExact "Hk2". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hk2". iEval (rewrite HE1sp Hb2) in "Hk2".
    set (E2 := <[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0)]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp80 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x7e) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x80)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp80) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x80)) (mword_of_int 9 : mword 6) Rs1
              E2 (K - 12) (mm !!! Regidx Rs1) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi80 [Hk3]").
    { iEval (rewrite HE2sp Hb3). iExact "Hk3". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hk3". iEval (rewrite HE2sp Hb3) in "Hk3".
    set (E3 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> E2).
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp82 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x80) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp82) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x82)) (mword_of_int 8 : mword 6) Rs2
              E3 (K - 12) (mm !!! Regidx Rs2) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi82 [Hk4]").
    { iEval (rewrite HE3sp Hb4). iExact "Hk4". }
    iIntros (CIDe4 Hse4) "Hcg Hpc Hk4". iEval (rewrite HE3sp Hb4) in "Hk4".
    set (E4 := <[Regidx Rs2 := regval_into_reg (mm !!! Regidx Rs2)]> E3).
    assert (HE4sp : E4 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp84 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x82) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp84) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x84)) (mword_of_int 7 : mword 6) Rs3
              E4 (K - 12) (mm !!! Regidx Rs3) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi84 [Hk5]").
    { iEval (rewrite HE4sp Hb5). iExact "Hk5". }
    iIntros (CIDe5 Hse5) "Hcg Hpc Hk5". iEval (rewrite HE4sp Hb5) in "Hk5".
    set (E5 := <[Regidx Rs3 := regval_into_reg (mm !!! Regidx Rs3)]> E4).
    assert (HE5sp : E5 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp86 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x84) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp86) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x86)) (mword_of_int 6 : mword 6) Rs4
              E5 (K - 12) (mm !!! Regidx Rs4) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi86 [Hk6]").
    { iEval (rewrite HE5sp Hb6). iExact "Hk6". }
    iIntros (CIDe6 Hse6) "Hcg Hpc Hk6". iEval (rewrite HE5sp Hb6) in "Hk6".
    set (E6 := <[Regidx Rs4 := regval_into_reg (mm !!! Regidx Rs4)]> E5).
    assert (HE6sp : E6 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp88 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x86) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x88)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp88) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x88)) (mword_of_int 5 : mword 6) Rs5
              E6 (K - 12) (mm !!! Regidx Rs5) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi88 [Hk7]").
    { iEval (rewrite HE6sp Hb7). iExact "Hk7". }
    iIntros (CIDe7 Hse7) "Hcg Hpc Hk7". iEval (rewrite HE6sp Hb7) in "Hk7".
    set (E7 := <[Regidx Rs5 := regval_into_reg (mm !!! Regidx Rs5)]> E6).
    assert (HE7sp : E7 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp8a : add_vec_int (mword_of_int (KernelSyms.copyin + 0x88) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x8a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp8a) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x8a)) (mword_of_int 4 : mword 6) Rs6
              E7 (K - 12) (mm !!! Regidx Rs6) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8a [Hk8]").
    { iEval (rewrite HE7sp Hb8). iExact "Hk8". }
    iIntros (CIDe8 Hse8) "Hcg Hpc Hk8". iEval (rewrite HE7sp Hb8) in "Hk8".
    set (E8 := <[Regidx Rs6 := regval_into_reg (mm !!! Regidx Rs6)]> E7).
    assert (HE8sp : E8 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp8c : add_vec_int (mword_of_int (KernelSyms.copyin + 0x8a) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x8c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp8c) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x8c)) (mword_of_int 3 : mword 6) Rs7
              E8 (K - 12) (mm !!! Regidx Rs7) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8c [Hk9]").
    { iEval (rewrite HE8sp Hb9). iExact "Hk9". }
    iIntros (CIDe9 Hse9) "Hcg Hpc Hk9". iEval (rewrite HE8sp Hb9) in "Hk9".
    set (E9 := <[Regidx Rs7 := regval_into_reg (mm !!! Regidx Rs7)]> E8).
    assert (HE9sp : E9 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp8e : add_vec_int (mword_of_int (KernelSyms.copyin + 0x8c) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x8e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp8e) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x8e)) (mword_of_int 2 : mword 6) Rs8
              E9 (K - 12) (mm !!! Regidx Rs8) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8e [Hk10]").
    { iEval (rewrite HE9sp Hb10). iExact "Hk10". }
    iIntros (CIDe10 Hse10) "Hcg Hpc Hk10". iEval (rewrite HE9sp Hb10) in "Hk10".
    set (E10 := <[Regidx Rs8 := regval_into_reg (mm !!! Regidx Rs8)]> E9).
    assert (HE10sp : E10 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp90 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x8e) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x90)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp90) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x90)) (mword_of_int 1 : mword 6) Rs9
              E10 (K - 12) (mm !!! Regidx Rs9) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi90 [Hk11]").
    { iEval (rewrite HE10sp Hb11). iExact "Hk11". }
    iIntros (CIDe11 Hse11) "Hcg Hpc Hk11". iEval (rewrite HE10sp Hb11) in "Hk11".
    set (E11 := <[Regidx Rs9 := regval_into_reg (mm !!! Regidx Rs9)]> E10).
    assert (HE11sp : E11 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp92 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x90) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x92)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp92) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x92)) (mword_of_int 0 : mword 6) Rs10
              E11 (K - 12) (mm !!! Regidx Rs10) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi92 [Hk12]").
    { iEval (rewrite HE11sp Hb12). iExact "Hk12". }
    iIntros (CIDe12 Hse12) "Hcg Hpc Hk12". iEval (rewrite HE11sp Hb12) in "Hk12".
    set (E12 := <[Regidx Rs10 := regval_into_reg (mm !!! Regidx Rs10)]> E11).
    assert (HE12sp : E12 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp94 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x92) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp94) in "Hpc".
    (* --- +0x94 c.addi16sp sp,96 : trade the frame back --------------- *)
    set (E13 := <[Regidx csp_rs1 := regval_into_reg
                   (add_vec (E12 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))))]> E12).
    assert (Hwv : add_vec (E12 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))) = sp0).
    { rewrite HE12sp. unfold spr. apply frame_cancel_96. }
    assert (Hpop : E12 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E12 !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))) 12).
    { rewrite Hwv HE12sp. symmetry. exact Hsprstk. }
    iAssert (stack_own (KTR := kt) sp0 12) with
      "[Hk1 Hk2 Hk3 Hk4 Hk5 Hk6 Hk7 Hk8 Hk9 Hk10 Hk11 Hk12]" as "Hframe".
    { rewrite (stack_own_slots (KTR := kt)). cbn [seq].
      iSplitL "Hk1";  [iExists _; iExact "Hk1"  |].
      iSplitL "Hk2";  [iExists _; iExact "Hk2"  |].
      iSplitL "Hk3";  [iExists _; iExact "Hk3"  |].
      iSplitL "Hk4";  [iExists _; iExact "Hk4"  |].
      iSplitL "Hk5";  [iExists _; iExact "Hk5"  |].
      iSplitL "Hk6";  [iExists _; iExact "Hk6"  |].
      iSplitL "Hk7";  [iExists _; iExact "Hk7"  |].
      iSplitL "Hk8";  [iExists _; iExact "Hk8"  |].
      iSplitL "Hk9";  [iExists _; iExact "Hk9"  |].
      iSplitL "Hk10"; [iExists _; iExact "Hk10" |].
      iSplitL "Hk11"; [iExists _; iExact "Hk11" |].
      iSplitL "Hk12"; [iExists _; iExact "Hk12" |].
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.copyin + 0x94))
              (mword_of_int 6 : mword 6) E12 (K - 12) 12 b Hpop
              with "Hcg Hpc Hi94 Hframe").
    iIntros (CIDe12b Hse12b) "Hcg Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
      (add_vec (E12 !!! Regidx csp_rs1)
         (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))))]> E12) with E13.
    assert (Hnk : ((K - 12) + 12)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hp96 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x94) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x96)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp96) in "Hpc".
    (* --- +0x96 c.ret ------------------------------------------------- *)
    assert (HE13ra : E13 !!! Regidx Rra = mm !!! Regidx Rra) by lkp.
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.copyin + 0x96)) Rra E13 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi96").
    iIntros (CIDe13 Hse13) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (E13 !!! Regidx Rra) = ret_pc (mm !!! Regidx Rra))
      by (rewrite HE13ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iDestruct (cpu_own_transport CID0 CIDe13 ncnt eb pcur b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CIDe13 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! E13 with "Hcg Hcnt Hpc [%] [%]").
    { unfold callee_saved.
      split_and!; first [ rewrite /E13 upd_eq Hmmsp; exact Hwv | lkp ]. }
    { lkp. }
  Qed.

  (* RULE ONE (claude-notes/optimization.md): [ci_loop]'s two block
     continuations, named so the walk's proofmode steps stop re-embedding
     ~20 lines of ∀/wands per step.  Transparent on purpose; the ∀ binders
     stay visible at each [iAssert]. *)
  Definition ci_copy_body
      (b : bool) (p : mword 64) (CID0 : CpuId) (off rem : nat) (dst : mword 64)
      (done : nat) (P : uptd) (szv v11 : mword 64) (K : nat)
      (spr cur va0 pa0 : mword 64)
      (CIDc : CpuId) (mc : regfile) (n : nat) : iProp Σ :=
    (⌜b = false \/ p = zero_reg -> (CIDc : CPU) = (CID0 : CPU)⌝ -∗
     ⌜(1 <= n)%nat⌝ -∗ ⌜(n <= rem)%nat⌝ -∗ ⌜(off + n <= 4096)%nat⌝ -∗
     ⌜mc !!! Regidx Rs1 = (mword_of_int (Z.of_nat n) : mword 64)⌝ -∗
     ⌜mc !!! Regidx Ra0 = pa0⌝ -∗
     ⌜mc !!! Regidx csp_rs1 = spr⌝ -∗
     ⌜mc !!! Regidx Rs2 = cur⌝ -∗
     ⌜mc !!! Regidx Rs3 = va0⌝ -∗
     ⌜mc !!! Regidx Rs4 = (mword_of_int (Z.of_nat rem) : mword 64)⌝ -∗
     ⌜mc !!! Regidx Rs5 = pa_add dst done⌝ -∗
     ⌜mc !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)⌝ -∗
     ⌜mc !!! Regidx Rs7 = page_base P.(ud_root)⌝ -∗
     ⌜mc !!! Regidx Rs8 = (mword_of_int (-4096) : mword 64)⌝ -∗
     ⌜mc !!! Regidx Rs9 = szv⌝ -∗
     ⌜mc !!! Regidx Rs10 = (mword_of_int 1 : mword 64)⌝ -∗
     ⌜mc !!! Regidx Rs11 = v11⌝ -∗
     sie_cap_gpr kt mc (K - 12) b p -∗
     pc_is (mword_of_int (KernelSyms.copyin + 0x3c) : mword 64) -∗
     WP (Loop : expr riscv_lang))%I.

  Definition ci_chunk_body {kt : ktier}
      (b : bool) (p : mword 64) (CID0 : CpuId) (szv : mword 64) (Pc : uptd)
      (spr cur va0 dst : mword 64) (rem done : nat) (P : uptd) (v11 : mword 64)
      (K lvl : nat) (eb : bool) (len : nat) (fd : nat -> bv 8)
      (EXIT : iProp Σ)
      (CIDb : CpuId) (mb : regfile) (pa0 : mword 64) (Pd : uptd) (lks : gset string) : iProp Σ :=
    (⌜b = false \/ p = zero_reg -> (CIDb : CPU) = (CID0 : CPU)⌝ -∗
     ⌜uptd_ext_sz szv Pc Pd⌝ -∗
     ⌜mb !!! Regidx Ra0 = pa0⌝ -∗
     ⌜mb !!! Regidx csp_rs1 = spr⌝ -∗
     ⌜mb !!! Regidx Rs2 = cur⌝ -∗
     ⌜mb !!! Regidx Rs3 = va0⌝ -∗
     ⌜mb !!! Regidx Rs4 = (mword_of_int (Z.of_nat rem) : mword 64)⌝ -∗
     ⌜mb !!! Regidx Rs5 = pa_add dst done⌝ -∗
     ⌜mb !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)⌝ -∗
     ⌜mb !!! Regidx Rs7 = page_base P.(ud_root)⌝ -∗
     ⌜mb !!! Regidx Rs8 = (mword_of_int (-4096) : mword 64)⌝ -∗
     ⌜mb !!! Regidx Rs9 = szv⌝ -∗
     ⌜mb !!! Regidx Rs10 = (mword_of_int 1 : mword 64)⌝ -∗
     ⌜mb !!! Regidx Rs11 = v11⌝ -∗
     sie_cap_gpr kt mb (K - 12) b p -∗
     cpu_own lvl eb p b lks -∗
     pc_is (mword_of_int (KernelSyms.copyin + 0x30) : mword 64) -∗
     page_own pa0 -∗
     (page_own pa0 -∗ proc_pt Pd) -∗
     ([∗ list] j ∈ seq 0 len, (pa_add dst j) ↦ₘ fd j) -∗
     EXIT -∗
     WP (Loop : expr riscv_lang))%I.

  (* ================================================================== *)
  (*  THE LOOP (+0x56 head, +0x2c body), by induction on FUEL.           *)
  (* ================================================================== *)
  Local Lemma ci_loop `{CID0 : CpuId} (γa : gname)
      (P : uptd) (szv : mword 64) (K lvl : nat) (eb : bool) (p : mword 64)
      (dst spr : mword 64) (len : nat) (b : bool)
      (v11 : mword 64) (lks : gset string) :
    (50 <= K)%nat ->
    (Z.of_nat len < 2 ^ 64)%Z ->
    (uint szv <= 2 ^ 38)%Z ->
    (* vmfault's kalloc: the transient noff increment stays in int range *)
    (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
    forall (fuel done rem : nat) (Pc : uptd) (m : regfile) (fd : nat -> bv 8),
    (rem <= fuel)%nat -> (1 <= rem)%nat -> (done + rem = len)%nat ->
    uptd_ext_sz szv P Pc ->
    m !!! Regidx csp_rs1 = spr ->
    m !!! Regidx Rs4 = (mword_of_int (Z.of_nat rem) : mword 64) ->
    m !!! Regidx Rs5 = pa_add dst done ->
    m !!! Regidx Rs6 = (mword_of_int 4096 : mword 64) ->
    m !!! Regidx Rs7 = page_base P.(ud_root) ->
    m !!! Regidx Rs8 = (mword_of_int (-4096) : mword 64) ->
    m !!! Regidx Rs9 = szv ->
    m !!! Regidx Rs10 = (mword_of_int 1 : mword 64) ->
    m !!! Regidx Rs11 = v11 ->
    locks_below lks "kmem" ->
    sie_cap_gpr kt m (K - 12) b p -∗
    cpu_own lvl eb p b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.copyin + 0x5a) : mword 64) -∗
    proc_pt Pc -∗
    kalloc_env γa None -∗
    ([∗ list] j ∈ seq 0 len, (pa_add dst j) ↦ₘ fd j) -∗
    wp_next (CID0 := CID0) b p (fun (CID : CpuId) =>
      ∀ (mj : regfile) (res : mword 64) (P' : uptd) (g : nat -> bv 8),
      ⌜mj !!! Regidx csp_rs1 = spr⌝ -∗
      ⌜mj !!! Regidx Rs11 = v11⌝ -∗
      ⌜mj !!! Regidx Ra0 = res⌝ -∗
      ⌜res = (mword_of_int 0 : mword 64) \/ res = (mword_of_int (-1) : mword 64)⌝ -∗
      ⌜uptd_ext_sz szv P P'⌝ -∗
      sie_cap_gpr kt mj (K - 12) b p -∗
      cpu_own lvl eb p b lks -∗
      pc_is (mword_of_int (KernelSyms.copyin + 0x7c) : mword 64) -∗
      proc_pt P' -∗
      ([∗ list] j ∈ seq 0 len, (pa_add dst j) ↦ₘ g j) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlen64 Hszb Hlvl.
    change (2 ^ 64)%Z with 18446744073709551616%Z in Hlen64.
    intro fuel.
    revert CID0.
    induction fuel as [| fuel IH];
      intros CID0 done rem Pc m fd Hfuel Hrem Hsum Hext Hsp Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11
        Hlkbelow;
      [ exfalso; lia |].
    iIntros "Hcg Hcnt #Htext Hpc Hpt Henv Hdst Hcont".
    iDestruct "Henv" as (γk) "(#Hlock & #Havail)".
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhwc Hcg]".
    iDestruct "Hhwc" as (hwmisa0 hwmseccfg0 hwpmar0 hwelp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hkmapb)".
    (* the exit continuation, named so the two joins below can take it -- kept
       [wp_next]-shaped (matching ["Hcont"]'s own type verbatim), since it is
       specialised at whichever hart each exit finally reaches. *)
    set (EXIT := (wp_next (CID0 := CID0) b p (fun (CID : CpuId) =>
      ∀ (mj : regfile) (res : mword 64) (P' : uptd) (g : nat -> bv 8),
      ⌜mj !!! Regidx csp_rs1 = spr⌝ -∗
      ⌜mj !!! Regidx Rs11 = v11⌝ -∗
      ⌜mj !!! Regidx Ra0 = res⌝ -∗
      ⌜res = (mword_of_int 0 : mword 64) \/ res = (mword_of_int (-1) : mword 64)⌝ -∗
      ⌜uptd_ext_sz szv P P'⌝ -∗
      sie_cap_gpr kt mj (K - 12) b p -∗
      cpu_own lvl eb p b lks -∗
      pc_is (mword_of_int (KernelSyms.copyin + 0x7c) : mword 64) -∗
      proc_pt P' -∗
      ([∗ list] j ∈ seq 0 len, (pa_add dst j) ↦ₘ g j) -∗
      WP (Loop : expr riscv_lang)))%I).
    (* the cursor, its page and its offset inside that page *)
    pose (cur := (m !!! Regidx Rs2 : mword 64)).
    pose (va0 := (and_vec cur (mword_of_int (-4096)) : mword 64)).
    pose (off := Z.to_nat (bv_unsigned cur mod 4096)).
    assert (Hoffz : Z.of_nat off = (bv_unsigned cur mod 4096)%Z)
      by (unfold off; apply ci_off_id).
    assert (Hoff4 : (off < 4096)%nat) by (unfold off; apply ci_off_lt).
    assert (Hrootc : Pc.(ud_root) = P.(ud_root))
      by (destruct Hext as ((H & _) & _); exact H).
    (* PGROUNDDOWN is idempotent (vmfault re-masks), and [va0 - cur + 4096] is
       the page tail.  Both stated at the LOCAL [va0] so [rewrite] matches. *)
    assert (Hidem : and_vec va0 (mword_of_int (-4096)) = va0)
      by (unfold va0; apply pgd_idem).
    assert (Hnav : add_vec (sub_vec va0 cur) (mword_of_int 4096)
                   = (mword_of_int (Z.of_nat (4096 - off)) : mword 64)).
    { unfold va0. rewrite pgd_room.
      assert (Heq : (4096 - bv_unsigned cur mod 4096)%Z = Z.of_nat (4096 - off)).
      { rewrite Nat2Z.inj_sub; [| lia]. rewrite Hoffz. reflexivity. }
      rewrite Heq. reflexivity. }
    (* ...and the offset itself, as the [sub a1,s2,s3] at +0x38 computes it *)
    assert (Hoffv : sub_vec cur va0 = (mword_of_int (Z.of_nat off) : mword 64)).
    { unfold va0. rewrite pgd_off. rewrite <- Hoffz. reflexivity. }
    (* ================================================================ *)
    (*  THE +0x2c JOIN: the chunk copy, over an arbitrary borrowed page.  *)
    (* ================================================================ *)
    iAssert (∀ (CIDb : CpuId) (mb : regfile) (pa0 : mword 64) (Pd : uptd),
        ci_chunk_body (kt := kt) b p CID0 szv Pc spr cur va0 dst rem done P v11 K lvl eb
          len fd EXIT CIDb mb pa0 Pd lks)%I with "[]" as "CHUNK".
    { iIntros (CIDb mb pa0 Pd) "%Hanchorb %Hextd %Hba0 %Hbsp %Hbs2 %Hbs3 %Hbs4 %Hbs5 %Hbs6
                            %Hbs7 %Hbs8 %Hbs9 %Hbs10 %Hbs11
                            Hcg Hcnt Hpc Hpg Hback Hdst HEXIT".
      iPoseProof (cii_30 with "Htext") as "Hi30".
      iPoseProof (cii_34 with "Htext") as "Hi34".
      iPoseProof (cii_36 with "Htext") as "Hi36".
      iPoseProof (cii_3a with "Htext") as "Hi3a".
      (* ---- +0x2c sub s1,s3,s2 ---- *)
      iApply (wp_sub_s_sconf (mword_of_int (KernelSyms.copyin + 0x30)) Rs1 Rs3 Rs2
                (sub_vec va0 cur) mb (K - 12) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(rgne; rgne; rewrite Hbs3 Hbs2; reflexivity)
                with "Hcg Hpc Hi30").
      iIntros (CIDb1 Hsb1) "Hcg Hpc".
      set (B1 := <[Regidx Rs1 := regval_into_reg (sub_vec va0 cur)]> mb).
      assert (Hp34 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x30) : mword 64) 4
                     = mword_of_int (KernelSyms.copyin + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp34) in "Hpc".
      (* ---- +0x30 c.add s1,s1,s6 ---- *)
      assert (HB1s1 : B1 !!! Regidx Rs1 = sub_vec va0 cur) by lkp.
      assert (HB1s6 : B1 !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)) by lkp.
      iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.copyin + 0x34)) Rs1 Rs6 B1 (K - 12) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi34").
      iIntros (CIDb2 Hsb2) "Hcg Hpc".
      set (B2 := <[Regidx Rs1 := regval_into_reg
                    (add_vec (rget B1 Rs1) (rget B1 Rs6))]> B1).
      assert (HB2s1 : B2 !!! Regidx Rs1
                      = (mword_of_int (Z.of_nat (4096 - off)) : mword 64)).
      { rewrite /B2 upd_eq. rgne; rgne. rewrite HB1s1 HB1s6. exact Hnav. }
      assert (Hp36 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x34) : mword 64) 2
                     = mword_of_int (KernelSyms.copyin + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp36) in "Hpc".
      (* ============================================================== *)
      (*  THE +0x38 JOIN: the copy proper, over the chunk length [n].     *)
      (* ============================================================== *)
      iAssert (∀ (CIDc : CpuId) (mc : regfile) (n : nat),
          ci_copy_body (kt := kt) b p CID0 off rem dst done P szv v11 K spr cur va0 pa0
            CIDc mc n)%I
        with "[Hdst Hcnt Hpg Hback HEXIT]" as "BODY".
      { iIntros (CIDc mc n) "%Hanchorc %Hn1 %Hnrem %Hnoff %Hcs1 %Hca0 %Hcsp %Hcs2 %Hcs3
                        %Hcs4 %Hcs5 %Hcs6 %Hcs7 %Hcs8 %Hcs9 %Hcs10 %Hcs11 Hcg Hpc".
        iPoseProof (cii_3c with "Htext") as "Hi3c".
        iPoseProof (cii_40 with "Htext") as "Hi40".
        iPoseProof (cii_44 with "Htext") as "Hi44".
        iPoseProof (cii_46 with "Htext") as "Hi46".
        iPoseProof (cii_48 with "Htext") as "Hi48".
        iPoseProof (cii_4c with "Htext") as "Hi4c".
        iPoseProof (cii_50 with "Htext") as "Hi50".
        iPoseProof (cii_52 with "Htext") as "Hi52".
        iPoseProof (cii_56 with "Htext") as "Hi56".
        (* ---- +0x38 sub a1,s2,s3 ---- *)
        iApply (wp_sub_s_sconf (mword_of_int (KernelSyms.copyin + 0x3c)) Ra1 Rs2 Rs3
                  (mword_of_int (Z.of_nat off) : mword 64) mc (K - 12) b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(rgne; rgne; rewrite Hcs2 Hcs3; exact Hoffv)
                  with "Hcg Hpc Hi3c").
        iIntros (CIDd1 Hsd1) "Hcg Hpc".
        set (D1 := <[Regidx Ra1 := regval_into_reg
                      (mword_of_int (Z.of_nat off) : mword 64)]> mc).
        assert (Hp40 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x3c) : mword 64) 4
                       = mword_of_int (KernelSyms.copyin + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp40) in "Hpc".
        (* ---- +0x3c sext.w a2,s1 ---- *)
        assert (HD1s1 : D1 !!! Regidx Rs1 = (mword_of_int (Z.of_nat n) : mword 64)) by lkp.
        iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.copyin + 0x40)) Ra2 Rs1
                  (mword_of_int 0 : mword 12) D1 (K - 12) b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi40").
        iIntros (CIDd2 Hsd2) "Hcg Hpc".
        set (D2 := <[Regidx Ra2 := regval_into_reg
              (sign_extend' 64 (subrange_vec_dec
                 (add_vec (rget D1 Rs1)
                          (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> D1).
        assert (Hn31 : (Z.of_nat n < 2147483648)%Z) by lia.
        assert (HD2a2 : D2 !!! Regidx Ra2 = (mword_of_int (Z.of_nat n) : mword 64)).
        { rewrite /D2 upd_eq. rgne. rewrite HD1s1.
          exact (sextw_moi (Z.of_nat n) (Nat2Z.is_nonneg n) Hn31). }
        assert (Hp44 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x40) : mword 64) 4
                       = mword_of_int (KernelSyms.copyin + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp44) in "Hpc".
        (* ---- +0x40 c.add a1,a1,a0 ---- *)
        assert (HD2a1 : D2 !!! Regidx Ra1 = (mword_of_int (Z.of_nat off) : mword 64)) by lkp.
        assert (HD2a0 : D2 !!! Regidx Ra0 = pa0) by lkp.
        iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.copyin + 0x44)) Ra1 Ra0 D2 (K - 12) b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi44").
        iIntros (CIDd3 Hsd3) "Hcg Hpc".
        set (D3 := <[Regidx Ra1 := regval_into_reg
                      (add_vec (rget D2 Ra1) (rget D2 Ra0))]> D2).
        assert (HD3a1 : D3 !!! Regidx Ra1 = pa_add pa0 off).
        { rewrite /D3 upd_eq. rgne; rgne. rewrite HD2a1 HD2a0. exact (pa_add_comm pa0 off). }
        assert (Hp46 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x44) : mword 64) 2
                       = mword_of_int (KernelSyms.copyin + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp46) in "Hpc".
        (* ---- +0x42 c.mv a0,s5 ---- *)
        iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.copyin + 0x46)) Ra0 Rs5 D3 (K - 12) b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi46").
        iIntros (CIDd4 Hsd4) "Hcg Hpc".
        set (D4 := <[Regidx Ra0 := regval_into_reg
                      (add_vec zero_reg (rget D3 Rs5))]> D3).
        assert (Hp48 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x46) : mword 64) 2
                       = mword_of_int (KernelSyms.copyin + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp48) in "Hpc".
        (* ---- +0x44 jal ra,memmove ---- *)
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.copyin + 0x48)) Rra
                  (mword_of_int 2094776 : mword 21) D4 (K - 12) b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi48").
        iIntros (CIDd5 Hsd5) "Hcg Hpc".
        set (D5 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KernelSyms.copyin + 0x48) : mword 64) 4)]> D4).
        assert (Htgtmm : add_vec (mword_of_int (KernelSyms.copyin + 0x48) : mword 64)
                           (sign_extend' 64 (mword_of_int 2094776 : mword 21))
                         = mword_of_int KernelSyms.memmove)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgtmm) in "Hpc".
        assert (HD5a0 : D5 !!! Regidx Ra0 = pa_add dst done) by lkp.
        assert (HD5a1 : D5 !!! Regidx Ra1 = pa_add pa0 off).
        { rewrite /D5. rewrite upd_ne; [| reg_neq].
          rewrite /D4. rewrite upd_ne; [| reg_neq]. exact HD3a1. }
        assert (HD5a2 : D5 !!! Regidx Ra2 = (mword_of_int (Z.of_nat n) : mword 64)).
        { rewrite /D5. rewrite upd_ne; [| reg_neq].
          rewrite /D4. rewrite upd_ne; [| reg_neq].
          rewrite /D3. rewrite upd_ne; [| reg_neq]. exact HD2a2. }
        assert (HD5ra : D5 !!! Regidx Rra
                        = add_vec_int (mword_of_int (KernelSyms.copyin + 0x48) : mword 64) 4)
          by (rewrite /D5 upd_eq; reflexivity).
        (* carve the page window and the destination chunk *)
        iDestruct (bb_page_named pa0 with "Hpg") as (fpg) "Hpg".
        assert (Hsplitp : (off + n + (4096 - off - n) = 4096)%nat) by lia.
        iEval (rewrite (bb_split3 pa0 off n (4096 - off - n) 4096 fpg Hsplitp)) in "Hpg".
        iDestruct "Hpg" as "(Hpg0 & Hsrc & Hpg2)".
        assert (Hsplitd : (done + n + (rem - n) = len)%nat) by lia.
        iEval (rewrite (bb_split3 dst done n (rem - n) len fd Hsplitd)) in "Hdst".
        iDestruct "Hdst" as "(Hd0 & Hdc & Hd2)".
        iApply (Memmove.wp_memmove_sconf kt D5 (K - 12) n
                  (fun j => fpg (off + j)%nat) (fun j => fd (done + j)%nat) b p
                  ltac:(lia) ltac:(change (2 ^ 32)%Z with 4294967296%Z; lia) HD5a2
                  with "Hcg Htext Hpc [Hsrc] [Hdc]").
        { iEval (rewrite HD5a1). iExact "Hsrc". }
        { iEval (rewrite HD5a0). iExact "Hdc". }
        iIntros (CIDmm Hsmm mfm) "Hcg Hpc Hsrc Hdc %Hmma0 %Hmmcs".
        iEval (rewrite HD5a1) in "Hsrc".
        iEval (rewrite HD5a0) in "Hdc".
        assert (Hret4c : ret_pc (D5 !!! Regidx Rra) = mword_of_int (KernelSyms.copyin + 0x4c)).
        { rewrite HD5ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Hret4c) in "Hpc".
        (* give the page back, and rebuild the whole destination buffer *)
        iDestruct (bb_join3 pa0 off n (4096 - off - n) 4096 fpg
                     (fun j => fpg (off + j)%nat) (fun j => fpg (off + (n + j))%nat)
                     Hsplitp with "Hpg0 Hsrc Hpg2") as (fpg') "Hpg".
        iDestruct (bb_page_of_named pa0 fpg' with "Hpg") as "Hpg".
        iDestruct ("Hback" with "Hpg") as "Hpt".
        iDestruct (bb_join3 dst done n (rem - n) len fd
                     (fun j => fpg (off + j)%nat) (fun j => fd (done + (n + j))%nat)
                     Hsplitd with "Hd0 Hdc Hd2") as (fd') "Hdst".
        (* the register facts memmove hands through *)
        assert (Hmmsp : mfm !!! Regidx csp_rs1 = spr).
        { rewrite (callee_saved_lookup Hmmcs csp_rs1 ltac:(vm_compute; reflexivity)). lkp. }
        assert (Hmms1 : mfm !!! Regidx Rs1 = (mword_of_int (Z.of_nat n) : mword 64)).
        { rewrite (callee_saved_lookup Hmmcs Rs1 ltac:(vm_compute; reflexivity)). lkp. }
        assert (Hmms3 : mfm !!! Regidx Rs3 = va0).
        { rewrite (callee_saved_lookup Hmmcs Rs3 ltac:(vm_compute; reflexivity)). lkp. }
        assert (Hmms4 : mfm !!! Regidx Rs4 = (mword_of_int (Z.of_nat rem) : mword 64)).
        { rewrite (callee_saved_lookup Hmmcs Rs4 ltac:(vm_compute; reflexivity)). lkp. }
        assert (Hmms5 : mfm !!! Regidx Rs5 = pa_add dst done).
        { rewrite (callee_saved_lookup Hmmcs Rs5 ltac:(vm_compute; reflexivity)). lkp. }
        assert (Hmms6 : mfm !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)).
        { rewrite (callee_saved_lookup Hmmcs Rs6 ltac:(vm_compute; reflexivity)). lkp. }
        assert (Hmms7 : mfm !!! Regidx Rs7 = page_base P.(ud_root)).
        { rewrite (callee_saved_lookup Hmmcs Rs7 ltac:(vm_compute; reflexivity)). lkp. }
        assert (Hmms8 : mfm !!! Regidx Rs8 = (mword_of_int (-4096) : mword 64)).
        { rewrite (callee_saved_lookup Hmmcs Rs8 ltac:(vm_compute; reflexivity)). lkp. }
        assert (Hmms9 : mfm !!! Regidx Rs9 = szv).
        { rewrite (callee_saved_lookup Hmmcs Rs9 ltac:(vm_compute; reflexivity)). lkp. }
        assert (Hmms10 : mfm !!! Regidx Rs10 = (mword_of_int 1 : mword 64)).
        { rewrite (callee_saved_lookup Hmmcs Rs10 ltac:(vm_compute; reflexivity)). lkp. }
        assert (Hmms11 : mfm !!! Regidx Rs11 = v11).
        { rewrite (callee_saved_lookup Hmmcs Rs11 ltac:(vm_compute; reflexivity)). lkp. }
        (* ---- +0x48 sub s4,s4,s1 ---- *)
        iApply (wp_sub_s_sconf (mword_of_int (KernelSyms.copyin + 0x4c)) Rs4 Rs4 Rs1
                  (mword_of_int (Z.of_nat (rem - n)) : mword 64) mfm (K - 12) b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(rgne; rgne; rewrite Hmms4 Hmms1; exact (bc_sub_nat rem n ltac:(lia) ltac:(lia)))
                  with "Hcg Hpc Hi4c").
        iIntros (CIDg1 Hsg1) "Hcg Hpc".
        set (G1 := <[Regidx Rs4 := regval_into_reg
                      (mword_of_int (Z.of_nat (rem - n)) : mword 64)]> mfm).
        assert (Hp50 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x4c) : mword 64) 4
                       = mword_of_int (KernelSyms.copyin + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp50) in "Hpc".
        (* ---- +0x4c c.add s5,s5,s1 ---- *)
        assert (HG1s5 : G1 !!! Regidx Rs5 = pa_add dst done) by lkp.
        assert (HG1s1 : G1 !!! Regidx Rs1 = (mword_of_int (Z.of_nat n) : mword 64)) by lkp.
        iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.copyin + 0x50)) Rs5 Rs1 G1 (K - 12) b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi50").
        iIntros (CIDg2 Hsg2) "Hcg Hpc".
        set (G2 := <[Regidx Rs5 := regval_into_reg
                      (add_vec (rget G1 Rs5) (rget G1 Rs1))]> G1).
        assert (HG2s5 : G2 !!! Regidx Rs5 = pa_add dst (done + n)).
        { rewrite /G2 upd_eq. rgne; rgne. rewrite HG1s5 HG1s1. exact (pa_add_bump dst done n). }
        assert (Hp52 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x50) : mword 64) 2
                       = mword_of_int (KernelSyms.copyin + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp52) in "Hpc".
        (* ---- +0x4e add s2,s3,s6 ---- *)
        iApply (wp_add_s_sconf (mword_of_int (KernelSyms.copyin + 0x52)) Rs2 Rs3 Rs6
                  (add_vec va0 (mword_of_int 4096)) G2 (K - 12) b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(rgne; rgne;
                        assert (HA : G2 !!! Regidx Rs3 = va0) by lkp;
                        assert (HB : G2 !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)) by lkp;
                        rewrite HA HB; reflexivity)
                  with "Hcg Hpc Hi52").
        iIntros (CIDg3 Hsg3) "Hcg Hpc".
        set (G3 := <[Regidx Rs2 := regval_into_reg
                      (add_vec va0 (mword_of_int 4096))]> G2).
        assert (Hp56 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x52) : mword 64) 4
                       = mword_of_int (KernelSyms.copyin + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp56) in "Hpc".
        (* ---- +0x52 beqz s4 ---- *)
        assert (HG3s4 : G3 !!! Regidx Rs4
                        = (mword_of_int (Z.of_nat (rem - n)) : mword 64)) by lkp.
        assert (Hcmp : eq_vec (G3 !!! Regidx Rs4) zero_reg = Nat.eqb (rem - n) 0).
        { rewrite HG3s4. apply bc_eqz_moi. lia. }
        destruct (Nat.eqb_spec (rem - n) 0) as [Hdone | Hmore].
        - (* ---- the copy is finished: +0x74 c.li a0,0, then the epilogue ---- *)
          iPoseProof (cii_7a with "Htext") as "Hi7a".
          iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (KernelSyms.copyin + 0x56))
                    (mword_of_int 36 : mword 13) Rs4 G3 (K - 12) b
                    ltac:(vm_compute; discriminate)
                    ltac:(rgne; first [ exact Hcmp | (rewrite Hcmp Hdone; reflexivity) ])
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi56").
          iApply bi.later_intro. iIntros (CIDg4 Hsg4) "Hcg Hpc".
          assert (Htgt7a : add_vec (mword_of_int (KernelSyms.copyin + 0x56) : mword 64)
                             (sign_extend' 64 (mword_of_int 36 : mword 13))
                           = mword_of_int (KernelSyms.copyin + 0x7a))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgt7a) in "Hpc".
          iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.copyin + 0x7a)) Ra0
                    (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) G3 (K - 12) b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    with "Hcg Hpc Hi7a").
          iIntros (CIDg5 Hsg5) "Hcg Hpc".
          set (G4 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> G3).
          assert (Hp7c : add_vec_int (mword_of_int (KernelSyms.copyin + 0x7a) : mword 64) 2
                         = mword_of_int (KernelSyms.copyin + 0x7c)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp7c) in "Hpc".
          iDestruct (cpu_own_transport CIDb CIDg5 lvl eb p b ltac:(wp_next_chain)
                       with "Hcnt") as "Hcnt".
          iSpecialize ("HEXIT" $! CIDg5 with "[]"); [iPureIntro; wp_next_chain|].
          iApply ("HEXIT" $! G4 (mword_of_int 0) Pd fd'
                    with "[%] [%] [%] [%] [%] Hcg Hcnt Hpc Hpt Hdst").
          + lkp.
          + lkp.
          + rewrite /G4 upd_eq. reflexivity.
          + left; reflexivity.
          + exact (uptd_ext_sz_trans szv P Pc Pd Hext Hextd).
        - (* ---- more to copy: fall through to the loop head at +0x56 ---- *)
          iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KernelSyms.copyin + 0x56))
                    (mword_of_int 36 : mword 13) Rs4 G3 (K - 12) b
                    ltac:(vm_compute; discriminate)
                    ltac:(rgne; first [ exact Hcmp
                                | (rewrite Hcmp; apply Nat.eqb_neq; exact Hmore) ])
                    with "Hcg Hpc Hi56").
          iIntros (CIDg4' Hsg4') "Hcg Hpc".
          assert (Hp5a : add_vec_int (mword_of_int (KernelSyms.copyin + 0x56) : mword 64) 4
                         = mword_of_int (KernelSyms.copyin + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp5a) in "Hpc".
          iAssert (kalloc_env γa None) as "Henv".
          { iExists γk. iFrame "Hlock Havail". }
          (* every premise pre-asserted and passed BY NAME (optimization.md's
             inline-[ltac:] rule) *)
          assert (HG3sp : G3 !!! Regidx csp_rs1 = spr) by lkp.
          assert (HG3s5 : G3 !!! Regidx Rs5 = pa_add dst (done + n)).
          { rewrite /G3. rewrite upd_ne; [| reg_neq]. exact HG2s5. }
          assert (HG3s6 : G3 !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)) by lkp.
          assert (HG3s7 : G3 !!! Regidx Rs7 = page_base P.(ud_root)) by lkp.
          assert (HG3s8 : G3 !!! Regidx Rs8 = (mword_of_int (-4096) : mword 64)) by lkp.
          assert (HG3s9 : G3 !!! Regidx Rs9 = szv) by lkp.
          assert (HG3s10 : G3 !!! Regidx Rs10 = (mword_of_int 1 : mword 64)) by lkp.
          assert (HG3s11 : G3 !!! Regidx Rs11 = v11) by lkp.
          assert (HF1 : (rem - n <= fuel)%nat) by lia.
          assert (HF2 : (1 <= rem - n)%nat) by lia.
          assert (HF3 : (done + n + (rem - n) = len)%nat) by lia.
          assert (HshiftIH : b = false \/ p = zero_reg -> (CIDg4' : CPU) = (CID0 : CPU)) by wp_next_chain.
          iDestruct (wp_next_shift HshiftIH with "HEXIT") as "HEXIT".
          iDestruct (cpu_own_transport CIDb CIDg4' lvl eb p b ltac:(wp_next_chain)
                       with "Hcnt") as "Hcnt".
          iApply (IH CIDg4' (done + n)%nat (rem - n)%nat Pd G3 fd'
                    HF1 HF2 HF3 (uptd_ext_sz_trans szv P Pc Pd Hext Hextd)
                    HG3sp HG3s4 HG3s5 HG3s6 HG3s7 HG3s8 HG3s9 HG3s10 HG3s11
                    Hlkbelow
                    with "Hcg Hcnt Htext Hpc Hpt Henv Hdst HEXIT").
      }
      (* ---- +0x32 bgeu s4,s1 : n = min(4096 - off, rem) ---- *)
      assert (HB2s4 : B2 !!! Regidx Rs4 = (mword_of_int (Z.of_nat rem) : mword 64)) by lkp.
      assert (Hbge : zopz0zKzJ_u (B2 !!! Regidx Rs4) (B2 !!! Regidx Rs1)
                     = Nat.leb (4096 - off) rem).
      { rewrite HB2s4 HB2s1. apply bc_ge_moi; lia. }
      destruct (Nat.leb_spec (4096 - off) rem) as [Hle | Hlt].
      + (* the whole page tail fits: taken, n = 4096 - off *)
        iApply (wp_bgeu_taken_s_sconf (mword_of_int (KernelSyms.copyin + 0x36))
                  (mword_of_int 6 : mword 13) Rs1 Rs4 B2 (K - 12) b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rgne; first [ exact Hbge | (rewrite Hbge; apply Nat.leb_le; exact Hle) ])
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi36").
        iApply bi.later_intro. iIntros (CIDb3 Hsb3) "Hcg Hpc".
        assert (Htgt3c : add_vec (mword_of_int (KernelSyms.copyin + 0x36) : mword 64)
                           (sign_extend' 64 (mword_of_int 6 : mword 13))
                         = mword_of_int (KernelSyms.copyin + 0x3c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt3c) in "Hpc".
        iApply ("BODY" $! CIDb3 B2 (4096 - off)%nat with
                  "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hpc");
          [ wp_next_chain | lia | lia | lia | exact HB2s1
          | lkp | lkp | lkp | lkp | lkp | lkp | lkp | lkp | lkp | lkp | lkp | lkp ].
      + (* only [rem] bytes are left: fall through, +0x36 c.mv s1,s4 *)
        iApply (wp_bgeu_fall_s_sconf (mword_of_int (KernelSyms.copyin + 0x36))
                  (mword_of_int 6 : mword 13) Rs1 Rs4 B2 (K - 12) b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rgne; first [ exact Hbge | (rewrite Hbge; apply Nat.leb_gt; exact Hlt) ])
                  with "Hcg Hpc Hi36").
        iIntros (CIDb3f Hsb3f) "Hcg Hpc".
        assert (Hp3a : add_vec_int (mword_of_int (KernelSyms.copyin + 0x36) : mword 64) 4
                       = mword_of_int (KernelSyms.copyin + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp3a) in "Hpc".
        iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.copyin + 0x3a)) Rs1 Rs4 B2 (K - 12) b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi3a").
        iIntros (CIDb4 Hsb4) "Hcg Hpc".
        set (B3 := <[Regidx Rs1 := regval_into_reg
                      (add_vec zero_reg (rget B2 Rs4))]> B2).
        assert (Hp3c : add_vec_int (mword_of_int (KernelSyms.copyin + 0x3a) : mword 64) 2
                       = mword_of_int (KernelSyms.copyin + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp3c) in "Hpc".
        iApply ("BODY" $! CIDb4 B3 rem with
                  "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hpc");
          [ wp_next_chain | lia | lia | lia
          | rewrite /B3 upd_eq add_vec_zero_l; rgne; exact HB2s4
          | lkp | lkp | lkp | lkp | lkp | lkp | lkp | lkp | lkp | lkp | lkp | lkp ]. }
    (* ================================================================ *)
    (*  THE LOOP HEAD (+0x56 .. +0x72).                                  *)
    (* ================================================================ *)
    iPoseProof (cii_5a with "Htext") as "Hi5a".
    iPoseProof (cii_5e with "Htext") as "Hi5e".
    iPoseProof (cii_60 with "Htext") as "Hi60".
    iPoseProof (cii_62 with "Htext") as "Hi62".
    iPoseProof (cii_66 with "Htext") as "Hi66".
    (* ---- +0x56 and s3,s2,s8 ---- *)
    iApply (wp_and_s_sconf (mword_of_int (KernelSyms.copyin + 0x5a)) Rs3 Rs2 Rs8 va0 m (K - 12) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite Hs8; reflexivity)
              with "Hcg Hpc Hi5a").
    iIntros (CIDw1 Hsw1) "Hcg Hpc".
    set (W1 := <[Regidx Rs3 := regval_into_reg va0]> m).
    assert (Hp5e : add_vec_int (mword_of_int (KernelSyms.copyin + 0x5a) : mword 64) 4
                   = mword_of_int (KernelSyms.copyin + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5e) in "Hpc".
    (* ---- +0x5a c.mv a1,s3 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.copyin + 0x5e)) Ra1 Rs3 W1 (K - 12) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5e").
    iIntros (CIDw2 Hsw2) "Hcg Hpc".
    set (W2 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (rget W1 Rs3))]> W1).
    assert (Hp60 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x5e) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp60) in "Hpc".
    (* ---- +0x5c c.mv a0,s7 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.copyin + 0x60)) Ra0 Rs7 W2 (K - 12) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi60").
    iIntros (CIDw3 Hsw3) "Hcg Hpc".
    set (W3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget W2 Rs7))]> W2).
    assert (Hp62 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x60) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp62) in "Hpc".
    (* ---- +0x5e jal ra,walkaddr ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.copyin + 0x62)) Rra
              (mword_of_int 2095470 : mword 21) W3 (K - 12) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi62").
    iIntros (CIDw4 Hsw4) "Hcg Hpc".
    set (W4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.copyin + 0x62) : mword 64) 4)]> W3).
    assert (Htgtwa : add_vec (mword_of_int (KernelSyms.copyin + 0x62) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095470 : mword 21))
                     = mword_of_int KernelSyms.walkaddr)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtwa) in "Hpc".
    assert (HW4a0 : W4 !!! Regidx Ra0 = page_base P.(ud_root)) by lkp.
    assert (HW4a1 : W4 !!! Regidx Ra1 = va0) by lkp.
    assert (HW4ra : W4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.copyin + 0x62) : mword 64) 4)
      by (rewrite /W4 upd_eq; reflexivity).
    (* ---- open the table into the exact represented view ---- *)
    iDestruct (proc_pt_acc_rep0 Pc with "Hpt") as
      (t m_ad) "(%Hrep & %Hview & %Hbase & %Hwf & Hptree & Hown)".
    assert (HW4root : W4 !!! Regidx Ra0
                      = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { rewrite HW4a0 Hbase Hrootc. reflexivity. }
    iApply (Walkaddr.wp_walkaddr_sconf kt W4 t m_ad (K - 12) (DfracOwn 1) b p
              ltac:(lia) HW4root Hrep with "Hcg Htext Hpc Hptree").
    iIntros (CIDw5 Hsw5 mw) "Hcg Hpc Hptree %Hwcs %Hwv".
    rewrite HW4a1 in Hwv.
    iDestruct (proc_pt_rebuild Pc t m_ad Hwf Hview Hrep Hbase with "Hptree Hown") as "Hpt".
    assert (Hret66 : ret_pc (W4 !!! Regidx Rra) = mword_of_int (KernelSyms.copyin + 0x66)).
    { rewrite HW4ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret66) in "Hpc".
    assert (Hmwsp : mw !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hwcs csp_rs1 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws2 : mw !!! Regidx Rs2 = cur).
    { rewrite (callee_saved_lookup Hwcs Rs2 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws3 : mw !!! Regidx Rs3 = va0).
    { rewrite (callee_saved_lookup Hwcs Rs3 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws4 : mw !!! Regidx Rs4 = (mword_of_int (Z.of_nat rem) : mword 64)).
    { rewrite (callee_saved_lookup Hwcs Rs4 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws5 : mw !!! Regidx Rs5 = pa_add dst done).
    { rewrite (callee_saved_lookup Hwcs Rs5 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws6 : mw !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)).
    { rewrite (callee_saved_lookup Hwcs Rs6 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws7 : mw !!! Regidx Rs7 = page_base P.(ud_root)).
    { rewrite (callee_saved_lookup Hwcs Rs7 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws8 : mw !!! Regidx Rs8 = (mword_of_int (-4096) : mword 64)).
    { rewrite (callee_saved_lookup Hwcs Rs8 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws9 : mw !!! Regidx Rs9 = szv).
    { rewrite (callee_saved_lookup Hwcs Rs9 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws10 : mw !!! Regidx Rs10 = (mword_of_int 1 : mword 64)).
    { rewrite (callee_saved_lookup Hwcs Rs10 ltac:(vm_compute; reflexivity)). lkp. }
    assert (Hmws11 : mw !!! Regidx Rs11 = v11).
    { rewrite (callee_saved_lookup Hwcs Rs11 ltac:(vm_compute; reflexivity)). lkp. }
    (* ---- +0x62 c.bnez a0 : the walkaddr verdict ---- *)
    destruct Hwv as [(Ha0z & _) | (w & Hsome & Hvu & Hvab & Ha0v)].
    2:{ (* ================= MAPPED: borrow the page ==================== *)
      destruct (upt_ad_view_vu Pc.(ud_tfp) Pc.(ud_um) m_ad (svpn_of va0) w Hview Hsome Hvu)
        as (w0 & Hl0 & Hppn).
      assert (Hin0 : pte_ppn w0 ∈ um_ppns Pc.(ud_um))
        by (apply elem_of_um_ppns; exists (svpn_of va0), w0; split; [exact Hl0 | reflexivity]).
      assert (Hpv : page_valid (page_base (pte_ppn w))).
      { rewrite -Hppn. exact (proj1 (proj2 (proj2 Hwf)) _ Hin0). }
      pose proof (proc_pt_page_acc Pc (svpn_of va0) w0 Hl0) as Hacc.
      rewrite Hppn in Hacc.
      iDestruct (Hacc with "Hkmapb Hpt") as "[Hpg Hback]".
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.copyin + 0x66))
                (mword_of_int 229 : mword 8) (Cregidx (mword_of_int 2)) Ra0 mw (K - 12) b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Ha0v; exact (page_valid_neq_zero _ Hpv))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi66").
      iApply bi.later_intro. iIntros (CIDw6 Hsw6) "Hcg Hpc".
      assert (Htgt30 : add_vec (mword_of_int (KernelSyms.copyin + 0x66) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 229 : mword 8) ('b"0"))))
              = mword_of_int (KernelSyms.copyin + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt30) in "Hpc".
      iDestruct (cpu_own_transport CID0 CIDw6 lvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply ("CHUNK" $! CIDw6 mw (page_base (pte_ppn w)) Pc
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                      Hcg Hcnt Hpc Hpg Hback Hdst Hcont").
      - wp_next_chain.
      - apply uptd_ext_sz_refl.
      - exact Ha0v.
      - exact Hmwsp.
      - exact Hmws2.
      - exact Hmws3.
      - exact Hmws4.
      - exact Hmws5.
      - exact Hmws6.
      - exact Hmws7.
      - exact Hmws8.
      - exact Hmws9.
      - exact Hmws10.
      - exact Hmws11. }
    (* ================= UNMAPPED: let vmfault map it ================== *)
    iPoseProof (cii_68 with "Htext") as "Hi68".
    iPoseProof (cii_6a with "Htext") as "Hi6a".
    iPoseProof (cii_6c with "Htext") as "Hi6c".
    iPoseProof (cii_6e with "Htext") as "Hi6e".
    iPoseProof (cii_70 with "Htext") as "Hi70".
    iPoseProof (cii_74 with "Htext") as "Hi74".
    iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.copyin + 0x66))
              (mword_of_int 229 : mword 8) (Cregidx (mword_of_int 2)) Ra0 mw (K - 12) b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite Ha0z; vm_compute; reflexivity)
              with "Hcg Hpc Hi66").
    iIntros (CIDv0 Hsv0) "Hcg Hpc".
    assert (Hp68 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x66) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp68) in "Hpc".
    (* ---- +0x68 c.mv a3,s10 : vmfault's [read] argument ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.copyin + 0x68)) Ra3 Rs10 mw (K - 12) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi68").
    iIntros (CIDv1 Hsv1) "Hcg Hpc".
    set (V1 := <[Regidx Ra3 := regval_into_reg (add_vec zero_reg (rget mw Rs10))]> mw).
    assert (Hp6a : add_vec_int (mword_of_int (KernelSyms.copyin + 0x68) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x6a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6a) in "Hpc".
    (* ---- +0x6a c.mv a2,s3 : the faulting va ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.copyin + 0x6a)) Ra2 Rs3 V1 (K - 12) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6a").
    iIntros (CIDv2 Hsv2) "Hcg Hpc".
    set (V2 := <[Regidx Ra2 := regval_into_reg (add_vec zero_reg (rget V1 Rs3))]> V1).
    assert (Hp6c : add_vec_int (mword_of_int (KernelSyms.copyin + 0x6a) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x6c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6c) in "Hpc".
    (* ---- +0x6c c.mv a1,s9 : the SIZE, an argument now ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.copyin + 0x6c)) Ra1 Rs9 V2 (K - 12) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6c").
    iIntros (CIDv3 Hsv3) "Hcg Hpc".
    set (V3 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (rget V2 Rs9))]> V2).
    assert (Hp6e : add_vec_int (mword_of_int (KernelSyms.copyin + 0x6c) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x6e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6e) in "Hpc".
    (* ---- +0x6e c.mv a0,s7 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.copyin + 0x6e)) Ra0 Rs7 V3 (K - 12) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6e").
    iIntros (CIDv3' Hsv3') "Hcg Hpc".
    set (V4 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget V3 Rs7))]> V3).
    assert (Hp70 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x6e) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x70)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp70) in "Hpc".
    (* ---- +0x70 jal ra,vmfault ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.copyin + 0x70)) Rra
              (mword_of_int 2096718 : mword 21) V4 (K - 12) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi70").
    iIntros (CIDv4 Hsv4) "Hcg Hpc".
    set (V5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.copyin + 0x70) : mword 64) 4)]> V4).
    assert (Htgtvf : add_vec (mword_of_int (KernelSyms.copyin + 0x70) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096718 : mword 21))
                     = mword_of_int KernelSyms.vmfault)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtvf) in "Hpc".
    assert (HV5a0 : V5 !!! Regidx Ra0 = page_base Pc.(ud_root))
      by (rewrite Hrootc; lkp).
    assert (HV5a1 : V5 !!! Regidx Ra1 = szv) by lkp.
    assert (HV5a2 : V5 !!! Regidx Ra2 = va0) by lkp.
    assert (HV5ra : V5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.copyin + 0x70) : mword 64) 4)
      by (rewrite /V5 upd_eq; reflexivity).
    iAssert (kalloc_env γa None) as "Henv".
    { iExists γk. iFrame "Hlock Havail". }
    iDestruct (cpu_own_transport CID0 CIDv4 lvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    (* vmfault's contract still wants the RAW tp premise (its kalloc/acquire
       chain reads tp mid-body); copyin's own map carries no such invariant
       any more, so re-point at [tp_pin V5], for which it holds by
       construction ([sie_cap_gpr_tp_pin] above). *)
    iDestruct (sie_cap_gpr_tp_pin (CIDx := CIDv4) V5 (K - 12) b p with "Hcg") as "Hcg".
    assert (HV5tp : tp_pin V5 !!! Regidx Rtp = cid_word) by (rewrite upd_eq; reflexivity).
    assert (HV5a0' : tp_pin V5 !!! Regidx Ra0 = page_base Pc.(ud_root))
      by (rewrite (tp_pin_ne (CIDx := CIDv4) V5 Ra0 ltac:(ridx_neq)); exact HV5a0).
    assert (HV5a1' : tp_pin V5 !!! Regidx Ra1 = szv)
      by (rewrite (tp_pin_ne (CIDx := CIDv4) V5 Ra1 ltac:(ridx_neq)); exact HV5a1).
    assert (HV5a2' : tp_pin V5 !!! Regidx Ra2 = va0)
      by (rewrite (tp_pin_ne (CIDx := CIDv4) V5 Ra2 ltac:(ridx_neq)); exact HV5a2).
    iApply (Vmfault.wp_vmfault_sconf kt γa (tp_pin V5) Pc szv (K - 12) lvl eb p b
              _ ltac:(lia) HV5tp HV5a0' HV5a1' Hszb Hlvl
              with "Hcg Hcnt Htext Hpc Hpt Henv").
    all: try lkbelow.
    iIntros (CIDvf Hsvf mv) "Hcg Hcnt Hpc %Hvcs Hvpost".
    iEval (rewrite HV5a2' Hidem) in "Hvpost".
    assert (Hret74 : ret_pc (tp_pin (CID:=CIDv4) V5 !!! Regidx Rra) = mword_of_int (KernelSyms.copyin + 0x74)).
    { rewrite (tp_pin_ne (CIDx := CIDv4) V5 Rra ltac:(ridx_neq)) HV5ra.
      unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret74) in "Hpc".
    assert (Hmvsp : mv !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hvcs csp_rs1 ltac:(vm_compute; reflexivity))
        (tp_pin_ne (CIDx := CIDv4) V5 csp_rs1 ltac:(ridx_neq)). lkp. }
    assert (Hmvs2 : mv !!! Regidx Rs2 = cur).
    { rewrite (callee_saved_lookup Hvcs Rs2 ltac:(vm_compute; reflexivity))
        (tp_pin_ne (CIDx := CIDv4) V5 Rs2 ltac:(ridx_neq)). lkp. }
    assert (Hmvs3 : mv !!! Regidx Rs3 = va0).
    { rewrite (callee_saved_lookup Hvcs Rs3 ltac:(vm_compute; reflexivity))
        (tp_pin_ne (CIDx := CIDv4) V5 Rs3 ltac:(ridx_neq)). lkp. }
    assert (Hmvs4 : mv !!! Regidx Rs4 = (mword_of_int (Z.of_nat rem) : mword 64)).
    { rewrite (callee_saved_lookup Hvcs Rs4 ltac:(vm_compute; reflexivity))
        (tp_pin_ne (CIDx := CIDv4) V5 Rs4 ltac:(ridx_neq)). lkp. }
    assert (Hmvs5 : mv !!! Regidx Rs5 = pa_add dst done).
    { rewrite (callee_saved_lookup Hvcs Rs5 ltac:(vm_compute; reflexivity))
        (tp_pin_ne (CIDx := CIDv4) V5 Rs5 ltac:(ridx_neq)). lkp. }
    assert (Hmvs6 : mv !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)).
    { rewrite (callee_saved_lookup Hvcs Rs6 ltac:(vm_compute; reflexivity))
        (tp_pin_ne (CIDx := CIDv4) V5 Rs6 ltac:(ridx_neq)). lkp. }
    assert (Hmvs7 : mv !!! Regidx Rs7 = page_base P.(ud_root)).
    { rewrite (callee_saved_lookup Hvcs Rs7 ltac:(vm_compute; reflexivity))
        (tp_pin_ne (CIDx := CIDv4) V5 Rs7 ltac:(ridx_neq)). lkp. }
    assert (Hmvs8 : mv !!! Regidx Rs8 = (mword_of_int (-4096) : mword 64)).
    { rewrite (callee_saved_lookup Hvcs Rs8 ltac:(vm_compute; reflexivity))
        (tp_pin_ne (CIDx := CIDv4) V5 Rs8 ltac:(ridx_neq)). lkp. }
    assert (Hmvs9 : mv !!! Regidx Rs9 = szv).
    { rewrite (callee_saved_lookup Hvcs Rs9 ltac:(vm_compute; reflexivity))
        (tp_pin_ne (CIDx := CIDv4) V5 Rs9 ltac:(ridx_neq)). lkp. }
    assert (Hmvs10 : mv !!! Regidx Rs10 = (mword_of_int 1 : mword 64)).
    { rewrite (callee_saved_lookup Hvcs Rs10 ltac:(vm_compute; reflexivity))
        (tp_pin_ne (CIDx := CIDv4) V5 Rs10 ltac:(ridx_neq)). lkp. }
    assert (Hmvs11 : mv !!! Regidx Rs11 = v11).
    { rewrite (callee_saved_lookup Hvcs Rs11 ltac:(vm_compute; reflexivity))
        (tp_pin_ne (CIDx := CIDv4) V5 Rs11 ltac:(ridx_neq)). lkp. }
    (* ---- +0x6e c.bnez a0 : the vmfault verdict ---- *)
    iDestruct "Hvpost" as "[(%Hvz & Hpt) | Hvs]".
    2:{ (* --- faulted in: borrow the brand-new page --- *)
      iDestruct "Hvs" as (r) "(%Hva0r & %Hpvr & %Hvlt & %Hnone & Hpt)".
      iDestruct (proc_pt_page_acc_vmfault Pc (svpn_of va0) r Hpvr with "Hkmapb Hpt")
        as "[Hpg Hback]".
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.copyin + 0x74))
                (mword_of_int 222 : mword 8) (Cregidx (mword_of_int 2)) Ra0 mv (K - 12) b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Hva0r; exact (page_valid_neq_zero _ Hpvr))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi74").
      iApply bi.later_intro. iIntros (CIDvf2 Hsvf2) "Hcg Hpc".
      assert (Htgt30' : add_vec (mword_of_int (KernelSyms.copyin + 0x74) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 222 : mword 8) ('b"0"))))
              = mword_of_int (KernelSyms.copyin + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt30') in "Hpc".
      iDestruct (cpu_own_transport CIDvf CIDvf2 lvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply ("CHUNK" $! CIDvf2 mv r (uptd_insert Pc (svpn_of va0) r)
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                      Hcg Hcnt Hpc Hpg Hback Hdst Hcont").
      - wp_next_chain.
      - apply uptd_ext_sz_insert; [exact Hnone |].
        apply svpn_of_below.
        + rewrite -uint_unsigned. exact Hszb.
        + rewrite -!uint_unsigned. exact Hvlt.
      - exact Hva0r.
      - exact Hmvsp.
      - exact Hmvs2.
      - exact Hmvs3.
      - exact Hmvs4.
      - exact Hmvs5.
      - exact Hmvs6.
      - exact Hmvs7.
      - exact Hmvs8.
      - exact Hmvs9.
      - exact Hmvs10.
      - exact Hmvs11. }
    (* --- unmapped and unfaultable: +0x70 li a0,-1, +0x72 j +0x76 --- *)
    iPoseProof (cii_76 with "Htext") as "Hi76".
    iPoseProof (cii_78 with "Htext") as "Hi78".
    iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.copyin + 0x74))
              (mword_of_int 222 : mword 8) (Cregidx (mword_of_int 2)) Ra0 mv (K - 12) b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite Hvz; vm_compute; reflexivity)
              with "Hcg Hpc Hi74").
    iIntros (CIDu0 Hsu0) "Hcg Hpc".
    assert (Hp76 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x74) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp76) in "Hpc".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.copyin + 0x76)) Ra0
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64) mv (K - 12) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi76").
    iIntros (CIDu1 Hsu1) "Hcg Hpc".
    set (V6 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> mv).
    assert (Hp78 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x76) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp78) in "Hpc".
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.copyin + 0x78))
              (sign_extend' 21 (concat_vec (mword_of_int 2 : mword 11) ('b"0")))
              V6 (K - 12) b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi78").
    iIntros (CIDu2 Hsu2). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Hjt78 : add_vec (mword_of_int (KernelSyms.copyin + 0x78) : mword 64)
              (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2 : mword 11) ('b"0"))))
            = mword_of_int (KernelSyms.copyin + 0x7c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjt78) in "Hpc".
    iDestruct (cpu_own_transport CIDvf CIDu2 lvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CIDu2 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! V6 (mword_of_int (-1)) Pc fd
              with "[%] [%] [%] [%] [%] Hcg Hcnt Hpc Hpt Hdst").
    - lkp.
    - lkp.
    - rewrite /V6 upd_eq. reflexivity.
    - right; reflexivity.
    - exact Hext.
  Qed.

  (* ================================================================== *)
  (*  THE WHOLE FUNCTION.                                                *)
  (* ================================================================== *)
  Lemma wp_copyin_sconf
      (γa : gname) (mm : regfile)
      (P : uptd) (szv : mword 64) (len : nat) (dst_olds : nat -> bv 8)
      (K lvl : nat) (eb : bool) (p : mword 64) (b : bool) (lks : gset string)
    : wp_copyin_sconf_body kt γa mm P szv len dst_olds K lvl eb p b lks.
  Proof.
    cbv beta delta [wp_copyin_sconf_body].
    intros pcE dst ret_tgt HK Hroot Hsza1 Hlenr Hlen64 Hszb Hlvl Hlkbelow.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc Hpt Henv Hdst Hcont".
    iPoseProof (cii_00 with "Htext") as "Hi00".
    (* ---- +0x00 beqz a4 : the len == 0 short circuit ---- *)
    assert (Hz : eq_vec (mm !!! Regidx Ra4) zero_reg = Nat.eqb len 0).
    { rewrite Hlenr. apply bc_eqz_moi. change (2 ^ 64)%Z with 18446744073709551616%Z in Hlen64.
      exact Hlen64. }
    destruct (Nat.eqb_spec len 0) as [Hlen0 | Hlenpos].
    { (* --- nothing to copy: +0x98 c.li a0,0 ; +0x9a c.ret, NO frame --- *)
      iPoseProof (cii_98 with "Htext") as "Hi98".
      iPoseProof (cii_9a with "Htext") as "Hi9a".
      iApply (wp_cbeqz_taken_s_sconf pcE (mword_of_int 76 : mword 8)
                (Cregidx (mword_of_int 6)) Ra4 mm K b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; first [ exact Hz | (rewrite Hz Hlen0; reflexivity) ])
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi00").
      iApply bi.later_intro. iIntros (CIDz0 Hsz0) "Hcg Hpc".
      assert (Htgt98 : add_vec (pcE : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 76 : mword 8) ('b"0"))))
              = mword_of_int (KernelSyms.copyin + 0x98)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt98) in "Hpc".
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.copyin + 0x98)) Ra0
                (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) mm K b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi98").
      iIntros (CIDz1 Hsz1) "Hcg Hpc".
      set (Z1 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> mm).
      assert (Hp9a : add_vec_int (mword_of_int (KernelSyms.copyin + 0x98) : mword 64) 2
                     = mword_of_int (KernelSyms.copyin + 0x9a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp9a) in "Hpc".
      assert (HZ1ra : Z1 !!! Regidx Rra = mm !!! Regidx Rra) by lkp.
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.copyin + 0x9a)) Rra Z1 K b
                ltac:(vm_compute; discriminate) with "Hcg Hpc Hi9a").
      iIntros (CIDz2 Hsz2) "Hcg Hpc".
      iEval (rgne; rewrite HZ1ra) in "Hpc".
      iDestruct (cpu_own_transport CID CIDz2 lvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CIDz2 with "[]"); [iPureIntro; wp_next_chain|].
      iApply ("Hcont" $! Z1 P dst_olds with "Hcg Hcnt Hpc Hpt Hdst [%] [%] [%]").
      - unfold callee_saved.
        rewrite /Z1. split_and!;
          (rewrite upd_ne; [reflexivity | reg_neq]).
      - apply uptd_ext_sz_refl.
      - left. rewrite /Z1 upd_eq. reflexivity.
    }
    (* ---- the real path: fall through into the 12-slot prologue ---- *)
    iApply (wp_cbeqz_fall_s_sconf pcE (mword_of_int 76 : mword 8)
              (Cregidx (mword_of_int 6)) Ra4 mm K b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; first [ exact Hz | (rewrite Hz; apply Nat.eqb_neq; exact Hlenpos) ])
              with "Hcg Hpc Hi00").
    iIntros (CIDp0 Hsp0) "Hcg Hpc".
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.copyin + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    iPoseProof (cii_02 with "Htext") as "Hi02".
    iPoseProof (cii_04 with "Htext") as "Hi04".
    iPoseProof (cii_06 with "Htext") as "Hi06".
    iPoseProof (cii_08 with "Htext") as "Hi08".
    iPoseProof (cii_0a with "Htext") as "Hi0a".
    iPoseProof (cii_0c with "Htext") as "Hi0c".
    iPoseProof (cii_0e with "Htext") as "Hi0e".
    iPoseProof (cii_10 with "Htext") as "Hi10".
    iPoseProof (cii_12 with "Htext") as "Hi12".
    iPoseProof (cii_14 with "Htext") as "Hi14".
    iPoseProof (cii_16 with "Htext") as "Hi16".
    iPoseProof (cii_18 with "Htext") as "Hi18".
    iPoseProof (cii_1a with "Htext") as "Hi1a".
    iPoseProof (cii_1c with "Htext") as "Hi1c".
    (* --- +0x02 c.addi16sp sp,-96 --- *)
    set (spr := add_vec (mm !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))).
    assert (Hspm : mm !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))
                    = pa_stk (mm !!! Regidx csp_rs1) 12).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int (KernelSyms.copyin + 0x02))
              (mword_of_int 58 : mword 6) mm K 12 b ltac:(lia) Hpush
              with "Hcg Hpc Hi02").
    iIntros (CIDp1 Hsp1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (mm !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))))]> mm).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))))]> mm) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := kt)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as
      "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & _)".
    iDestruct "S1" as (u1) "Hk1".   iDestruct "S2" as (u2) "Hk2".
    iDestruct "S3" as (u3) "Hk3".   iDestruct "S4" as (u4) "Hk4".
    iDestruct "S5" as (u5) "Hk5".   iDestruct "S6" as (u6) "Hk6".
    iDestruct "S7" as (u7) "Hk7".   iDestruct "S8" as (u8) "Hk8".
    iDestruct "S9" as (u9) "Hk9".   iDestruct "S10" as (u10) "Hk10".
    iDestruct "S11" as (u11) "Hk11". iDestruct "S12" as (u12) "Hk12".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (unfold spr, sp0; slot_addr).
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (unfold spr, sp0; slot_addr).
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (unfold spr, sp0; slot_addr).
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (unfold spr, sp0; slot_addr).
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (unfold spr, sp0; slot_addr).
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 6) by (unfold spr, sp0; slot_addr).
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (unfold spr, sp0; slot_addr).
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (unfold spr, sp0; slot_addr).
    assert (Hb9 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 9) by (unfold spr, sp0; slot_addr).
    assert (Hb10 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 10) by (unfold spr, sp0; slot_addr).
    assert (Hb11 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 11) by (unfold spr, sp0; slot_addr).
    assert (Hb12 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk sp0 12) by (unfold spr, sp0; slot_addr).
    (* --- +0x04 .. +0x1a : the twelve c.sdsp --- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x04)) (mword_of_int 11 : mword 6) Rra
              R1 (K - 12) u1 b with "Hcg Hpc Hi04 [Hk1]").
    { iEval (rewrite HspR1 Hb1). iExact "Hk1". }
    iIntros (CIDp2 Hsp2) "Hcg Hpc Hk1". iEval (rewrite HspR1 Hb1) in "Hk1".
    assert (HR1ra : R1 !!! Regidx Rra = mm !!! Regidx Rra) by lkp.
    iEval (rgne; rewrite HR1ra) in "Hk1".
    assert (Hq06 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x04) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x06)) (mword_of_int 10 : mword 6) Rs0
              R1 (K - 12) u2 b with "Hcg Hpc Hi06 [Hk2]").
    { iEval (rewrite HspR1 Hb2). iExact "Hk2". }
    iIntros (CIDp3 Hsp3) "Hcg Hpc Hk2". iEval (rewrite HspR1 Hb2) in "Hk2".
    assert (HR1s0 : R1 !!! Regidx Rs0 = mm !!! Regidx Rs0) by lkp.
    iEval (rgne; rewrite HR1s0) in "Hk2".
    assert (Hq08 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x06) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x08)) (mword_of_int 9 : mword 6) Rs1
              R1 (K - 12) u3 b with "Hcg Hpc Hi08 [Hk3]").
    { iEval (rewrite HspR1 Hb3). iExact "Hk3". }
    iIntros (CIDp4 Hsp4) "Hcg Hpc Hk3". iEval (rewrite HspR1 Hb3) in "Hk3".
    assert (HR1s1 : R1 !!! Regidx Rs1 = mm !!! Regidx Rs1) by lkp.
    iEval (rgne; rewrite HR1s1) in "Hk3".
    assert (Hq0a : add_vec_int (mword_of_int (KernelSyms.copyin + 0x08) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq0a) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x0a)) (mword_of_int 8 : mword 6) Rs2
              R1 (K - 12) u4 b with "Hcg Hpc Hi0a [Hk4]").
    { iEval (rewrite HspR1 Hb4). iExact "Hk4". }
    iIntros (CIDp5 Hsp5) "Hcg Hpc Hk4". iEval (rewrite HspR1 Hb4) in "Hk4".
    assert (HR1s2 : R1 !!! Regidx Rs2 = mm !!! Regidx Rs2) by lkp.
    iEval (rgne; rewrite HR1s2) in "Hk4".
    assert (Hq0c : add_vec_int (mword_of_int (KernelSyms.copyin + 0x0a) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq0c) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x0c)) (mword_of_int 7 : mword 6) Rs3
              R1 (K - 12) u5 b with "Hcg Hpc Hi0c [Hk5]").
    { iEval (rewrite HspR1 Hb5). iExact "Hk5". }
    iIntros (CIDp6 Hsp6) "Hcg Hpc Hk5". iEval (rewrite HspR1 Hb5) in "Hk5".
    assert (HR1s3 : R1 !!! Regidx Rs3 = mm !!! Regidx Rs3) by lkp.
    iEval (rgne; rewrite HR1s3) in "Hk5".
    assert (Hq0e : add_vec_int (mword_of_int (KernelSyms.copyin + 0x0c) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq0e) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x0e)) (mword_of_int 6 : mword 6) Rs4
              R1 (K - 12) u6 b with "Hcg Hpc Hi0e [Hk6]").
    { iEval (rewrite HspR1 Hb6). iExact "Hk6". }
    iIntros (CIDp7 Hsp7) "Hcg Hpc Hk6". iEval (rewrite HspR1 Hb6) in "Hk6".
    assert (HR1s4 : R1 !!! Regidx Rs4 = mm !!! Regidx Rs4) by lkp.
    iEval (rgne; rewrite HR1s4) in "Hk6".
    assert (Hq10 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x0e) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq10) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x10)) (mword_of_int 5 : mword 6) Rs5
              R1 (K - 12) u7 b with "Hcg Hpc Hi10 [Hk7]").
    { iEval (rewrite HspR1 Hb7). iExact "Hk7". }
    iIntros (CIDp8 Hsp8) "Hcg Hpc Hk7". iEval (rewrite HspR1 Hb7) in "Hk7".
    assert (HR1s5 : R1 !!! Regidx Rs5 = mm !!! Regidx Rs5) by lkp.
    iEval (rgne; rewrite HR1s5) in "Hk7".
    assert (Hq12 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x10) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq12) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x12)) (mword_of_int 4 : mword 6) Rs6
              R1 (K - 12) u8 b with "Hcg Hpc Hi12 [Hk8]").
    { iEval (rewrite HspR1 Hb8). iExact "Hk8". }
    iIntros (CIDp9 Hsp9) "Hcg Hpc Hk8". iEval (rewrite HspR1 Hb8) in "Hk8".
    assert (HR1s6 : R1 !!! Regidx Rs6 = mm !!! Regidx Rs6) by lkp.
    iEval (rgne; rewrite HR1s6) in "Hk8".
    assert (Hq14 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x12) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq14) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x14)) (mword_of_int 3 : mword 6) Rs7
              R1 (K - 12) u9 b with "Hcg Hpc Hi14 [Hk9]").
    { iEval (rewrite HspR1 Hb9). iExact "Hk9". }
    iIntros (CIDp10 Hsp10) "Hcg Hpc Hk9". iEval (rewrite HspR1 Hb9) in "Hk9".
    assert (HR1s7 : R1 !!! Regidx Rs7 = mm !!! Regidx Rs7) by lkp.
    iEval (rgne; rewrite HR1s7) in "Hk9".
    assert (Hq16 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x14) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq16) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x16)) (mword_of_int 2 : mword 6) Rs8
              R1 (K - 12) u10 b with "Hcg Hpc Hi16 [Hk10]").
    { iEval (rewrite HspR1 Hb10). iExact "Hk10". }
    iIntros (CIDp11 Hsp11) "Hcg Hpc Hk10". iEval (rewrite HspR1 Hb10) in "Hk10".
    assert (HR1s8 : R1 !!! Regidx Rs8 = mm !!! Regidx Rs8) by lkp.
    iEval (rgne; rewrite HR1s8) in "Hk10".
    assert (Hq18 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x16) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq18) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x18)) (mword_of_int 1 : mword 6) Rs9
              R1 (K - 12) u11 b with "Hcg Hpc Hi18 [Hk11]").
    { iEval (rewrite HspR1 Hb11). iExact "Hk11". }
    iIntros (CIDp12 Hsp12) "Hcg Hpc Hk11". iEval (rewrite HspR1 Hb11) in "Hk11".
    assert (HR1s9 : R1 !!! Regidx Rs9 = mm !!! Regidx Rs9) by lkp.
    iEval (rgne; rewrite HR1s9) in "Hk11".
    assert (Hq1a : add_vec_int (mword_of_int (KernelSyms.copyin + 0x18) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq1a) in "Hpc".
    (* --- +0x1a c.sdsp s10,0(sp) : the twelfth slot, live since the bump --- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.copyin + 0x1a)) (mword_of_int 0 : mword 6) Rs10
              R1 (K - 12) u12 b with "Hcg Hpc Hi1a [Hk12]").
    { iEval (rewrite HspR1 Hb12). iExact "Hk12". }
    iIntros (CIDp12b Hsp12b) "Hcg Hpc Hk12". iEval (rewrite HspR1 Hb12) in "Hk12".
    assert (HR1s10 : R1 !!! Regidx Rs10 = mm !!! Regidx Rs10) by lkp.
    iEval (rgne; rewrite HR1s10) in "Hk12".
    assert (Hq1c : add_vec_int (mword_of_int (KernelSyms.copyin + 0x1a) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq1c) in "Hpc".
    (* --- +0x1c c.addi4spn s0,sp,96 --- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.copyin + 0x1c)) (Cregidx (mword_of_int 0))
              (mword_of_int 24 : mword 8) Rs0 R1 (K - 12) b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi1c").
    iIntros (CIDp13 Hsp13) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))))]> R1).
    assert (Hq1e : add_vec_int (mword_of_int (KernelSyms.copyin + 0x1c) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq1e) in "Hpc".
    (* --- +0x1c .. +0x28 : the loop-invariant registers --- *)
    iPoseProof (cii_1e with "Htext") as "Hi1e".
    iPoseProof (cii_20 with "Htext") as "Hi20".
    iPoseProof (cii_22 with "Htext") as "Hi22".
    iPoseProof (cii_24 with "Htext") as "Hi24".
    iPoseProof (cii_26 with "Htext") as "Hi26".
    iPoseProof (cii_28 with "Htext") as "Hi28".
    iPoseProof (cii_2a with "Htext") as "Hi2a".
    iPoseProof (cii_2c with "Htext") as "Hi2c".
    iPoseProof (cii_2e with "Htext") as "Hi2e".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.copyin + 0x1e)) Rs7 Ra0 R2 (K - 12) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e").
    iIntros (CIDp14 Hsp14) "Hcg Hpc".
    set (R3 := <[Regidx Rs7 := regval_into_reg (add_vec zero_reg (rget R2 Ra0))]> R2).
    assert (Hq20 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x1e) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq20) in "Hpc".
    (* --- +0x20 c.mv s9,a1 : psz is parked for the whole loop --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.copyin + 0x20)) Rs9 Ra1 R3 (K - 12) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20").
    iIntros (CIDp14b Hsp14b) "Hcg Hpc".
    set (R4 := <[Regidx Rs9 := regval_into_reg (add_vec zero_reg (rget R3 Ra1))]> R3).
    assert (Hq22 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x20) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq22) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.copyin + 0x22)) Rs5 Ra2 R4 (K - 12) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22").
    iIntros (CIDp15 Hsp15) "Hcg Hpc".
    set (R5 := <[Regidx Rs5 := regval_into_reg (add_vec zero_reg (rget R4 Ra2))]> R4).
    assert (Hq24 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x22) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq24) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.copyin + 0x24)) Rs2 Ra3 R5 (K - 12) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24").
    iIntros (CIDp16 Hsp16) "Hcg Hpc".
    set (R6 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (rget R5 Ra3))]> R5).
    assert (Hq26 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x24) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq26) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.copyin + 0x26)) Rs4 Ra4 R6 (K - 12) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26").
    iIntros (CIDp17 Hsp17) "Hcg Hpc".
    set (R7 := <[Regidx Rs4 := regval_into_reg (add_vec zero_reg (rget R6 Ra4))]> R6).
    assert (Hq28 : add_vec_int (mword_of_int (KernelSyms.copyin + 0x26) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq28) in "Hpc".
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.copyin + 0x28)) Rs8
              (sign_extend' 20 (mword_of_int 63 : mword 6)) (mword_of_int (-4096) : mword 64)
              R7 (K - 12) b ltac:(vm_compute; discriminate) ltac:(rdok)
              lui_m4096 with "Hcg Hpc Hi28").
    iIntros (CIDp18 Hsp18) "Hcg Hpc".
    set (R8 := <[Regidx Rs8 := regval_into_reg (mword_of_int (-4096) : mword 64)]> R7).
    assert (Hq2a : add_vec_int (mword_of_int (KernelSyms.copyin + 0x28) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq2a) in "Hpc".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.copyin + 0x2a)) Rs10
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64) R8 (K - 12) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi2a").
    iIntros (CIDp19 Hsp19) "Hcg Hpc".
    set (R9 := <[Regidx Rs10 := regval_into_reg (mword_of_int 1 : mword 64)]> R8).
    assert (Hq2c : add_vec_int (mword_of_int (KernelSyms.copyin + 0x2a) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq2c) in "Hpc".
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.copyin + 0x2c)) Rs6
              (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
              R9 (K - 12) b ltac:(vm_compute; discriminate) ltac:(rdok)
              lui_4096 with "Hcg Hpc Hi2c").
    iIntros (CIDp20 Hsp20) "Hcg Hpc".
    set (R10 := <[Regidx Rs6 := regval_into_reg (mword_of_int 4096 : mword 64)]> R9).
    assert (Hq2e : add_vec_int (mword_of_int (KernelSyms.copyin + 0x2c) : mword 64) 2
                   = mword_of_int (KernelSyms.copyin + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq2e) in "Hpc".
    (* --- +0x2a c.j +0x56 : enter the loop --- *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.copyin + 0x2e))
              (sign_extend' 21 (concat_vec (mword_of_int 22 : mword 11) ('b"0")))
              R10 (K - 12) b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2e").
    iIntros (CIDp21 Hsp21). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Hjt2e : add_vec (mword_of_int (KernelSyms.copyin + 0x2e) : mword 64)
              (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 22 : mword 11) ('b"0"))))
            = mword_of_int (KernelSyms.copyin + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjt2e) in "Hpc".
    (* --- the loop --- *)
    assert (HR10s5 : R10 !!! Regidx Rs5 = pa_add dst 0%nat).
    { rewrite pa_add_0. lkp. }
    assert (HR10s4 : R10 !!! Regidx Rs4 = (mword_of_int (Z.of_nat len) : mword 64)) by lkp.
    assert (HR10sp : R10 !!! Regidx csp_rs1 = spr) by lkp.
    assert (HR10s6 : R10 !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)) by lkp.
    assert (HR10s7 : R10 !!! Regidx Rs7 = page_base P.(ud_root)) by lkp.
    assert (HR10s8 : R10 !!! Regidx Rs8 = (mword_of_int (-4096) : mword 64)) by lkp.
    assert (HR10s9 : R10 !!! Regidx Rs9 = szv) by (rewrite -Hsza1; lkp).
    assert (HR10s10 : R10 !!! Regidx Rs10 = (mword_of_int 1 : mword 64)) by lkp.
    assert (HR10s11 : R10 !!! Regidx Rs11 = mm !!! Regidx Rs11) by lkp.
    assert (HL1 : (len <= len)%nat) by lia.
    assert (HL2 : (1 <= len)%nat) by lia.
    assert (HL3 : (0 + len = len)%nat) by lia.
    iDestruct (cpu_own_transport CID CIDp21 lvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (ci_loop (CID0 := CIDp21) γa P szv K lvl eb p dst spr len b
              (mm !!! Regidx Rs11) lks
              HK Hlen64 Hszb Hlvl len 0%nat len P R10 dst_olds
              HL1 HL2 HL3 (uptd_ext_sz_refl szv P)
              HR10sp HR10s4 HR10s5 HR10s6 HR10s7 HR10s8 HR10s9 HR10s10 HR10s11
              Hlkbelow
              with "Hcg Hcnt Htext Hpc Hpt Henv Hdst").
    iIntros (CIDl Hsl mj res P' g) "%Hjsp %Hjs11 %Hja0 %Hres %Hjext
                            Hcg Hcnt Hpc Hpt Hdst".
    iApply (ci_epilogue (CID0 := CIDl) mm mj K lvl eb b res sp0 p lks
              ltac:(lia) ltac:(reflexivity)
              Hjsp Hja0 Hjs11
              with "Hcg Hcnt Htext Hpc Hk1 Hk2 Hk3 Hk4 Hk5 Hk6 Hk7 Hk8 Hk9 Hk10 Hk11 Hk12").
    iIntros (CIDe Hse mf) "Hcg Hcnt Hpc %Hcs %Hfa0".
    iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! mf P' g with "Hcg Hcnt Hpc Hpt Hdst [%] [%] [%]").
    - exact Hcs.
    - exact Hjext.
    - rewrite Hfa0. exact Hres.
  Qed.

End ProofCopyin.

End CopyinProof.
