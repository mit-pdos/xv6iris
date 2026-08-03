(* ProofArgfd.v -- whole-function WP for argfd(), the syscall layer's fd
   lookup.

     static int argfd(int n, int *pfd, struct file **pf) {
       int fd; struct file *f;
       argint(n, &fd);
       if (fd < 0 || fd >= NOFILE || (f = myproc()->ofile[fd]) == 0)
         return -1;
       if (pfd) *pfd = fd;
       if (pf)  *pf  = f;
       return 0;
     }

   Thirty-three instructions (KernelInstrs @ 0x80004a04; the listing is in
   CodeArgfd.v).  What is new here relative to sys_close:

   * THREE arms joining at the epilogue (+0x46) -- each [return -1] tail being
     a [c.li a0,-1] plus a [c.j] back -- so [af_tail] is applied three times
     rather than twice.

   * THE FUSED RANGE TEST.  gcc turns [fd < 0 || fd >= NOFILE] into the single
     UNSIGNED compare [bltu a5,a4] against 15: a negative [fd] sign-extends to
     a huge unsigned and fails the same test.  [af_bltu_in]/[af_bltu_out] are
     that argument, over [bv_signed] of the loaded [int].

   * THE [int] ROUND TRIP.  The local is reloaded with an [lw] (sign-extending)
     and written to [*pfd] with an [sw] (truncating), and
     [RiscvExtras.trunc32_sext64] says that is the identity -- which is why the
     caller's cell ends up holding exactly argint's [trunc32 v].

   * THE TWO NULL TESTS ARE DEAD in this contract: the spec's two disequality
     premises discharge both [c.beqz]es' fall-through, so the skip targets are
     never entered.  A caller passing stack locals proves those premises from
     the frame's own geometry, not by assumption (SpecArgfd.v, and StackOwn's
     [stack_own_sp_bounds]). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import KernelRvcDecode.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import IntrDefs WpLock.
Require Import HartTp WpNext.
Require Import ProcGeom CpuOwn.
Require Import UserPtTree.
Require Import FdSlots FileInv ProcInv.
Require Import SpecMyproc SpecArgint.
Require Import SpecArgfd.
Require Import CodeArgfd.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  Pure arithmetic: the 48-byte frame and the [int fd] local.            *)
(* ===================================================================== *)

Lemma af_push (X : mword 64) :
  add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) = pa_stk X 6.
Proof.
  unfold pa_stk, add_vec_int. apply f_equal.
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma af_s0_entry (X : mword 64) :
  add_vec (pa_stk X 6) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))) = X.
Proof.
  rewrite <- af_push. apply frame_cancel.
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma af_pop (X : mword 64) :
  add_vec (pa_stk X 6) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = X.
Proof.
  rewrite <- af_push. apply frame_cancel.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* [addi a1,s0,-36] : &fd, the UPPER WORD of frame slot 5 *)
Lemma af_addr_fd (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 0xfdc : mword 12)) = pa_add (pa_stk X 5) 4.
Proof.
  unfold pa_add, pa_stk. rewrite avi_assoc.
  unfold add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma af_addr_fd_base (X : mword 64) :
  pa_add (pa_stk X 5) 4 = add_vec_int (pa_stk X 6) 12.
Proof. unfold pa_add, pa_stk. rewrite !avi_assoc. f_equal; lia. Qed.

(* ===================================================================== *)
(*  The fused range test.                                                 *)
(* ===================================================================== *)
(* [bltu a5,a4] with a5 = 15 and a4 = the sign-extended [int fd] is taken
   exactly when [fd] is outside [0, NOFILE).  A negative fd sign-extends to
   ~2^64, which is why ONE unsigned compare implements C's two tests. *)
Lemma af_sext_uint (w : mword 32) :
  uint (sign_extend' 64 w : mword 64) = bv_wrap 64 (bv_signed w).
Proof. rewrite uint_unsigned sext32_64_moi. apply moi64_unsigned. Qed.

(* The arithmetic, in mword-FREE form: under the bitvector zify hook [lia]
   fails whenever an [mword] is merely in CONTEXT, so the Z reasoning is
   packaged as closed facts and applied (durable-notes). *)
Local Lemma af_wrap_neg (z : Z) : (z < 0)%Z -> (-2147483648 <= z)%Z ->
  (z mod 18446744073709551616)%Z = (z + 18446744073709551616)%Z.
Proof.
  intros H1 H2. rewrite <- (Z.mod_add z 1 18446744073709551616); [| lia].
  apply Z.mod_small. lia.
Qed.

Local Lemma af_in_arith (z : Z) : (0 <= z < 16)%Z ->
  (z mod 18446744073709551616 <= 15)%Z.
Proof. intro H. rewrite (Z.mod_small z 18446744073709551616); lia. Qed.

Local Lemma af_out_arith (z : Z) :
  ~ (0 <= z < 16)%Z -> (-2147483648 <= z < 2147483648)%Z ->
  (15 < z mod 18446744073709551616)%Z.
Proof.
  intros Hr Hrange.
  destruct (Z_lt_le_dec z 0) as [Hneg | Hpos].
  - rewrite (af_wrap_neg z Hneg ltac:(lia)). lia.
  - rewrite (Z.mod_small z 18446744073709551616); lia.
Qed.

Lemma af_bltu_in (w : mword 32) :
  (0 <= bv_signed w < Z.of_nat NOFILE)%Z ->
  zopz0zI_u (mword_of_int 15 : mword 64) (sign_extend' 64 w) = false.
Proof.
  intro Hr. unfold NOFILE in Hr. change (Z.of_nat 16) with 16%Z in Hr.
  unfold zopz0zI_u. apply Z.ltb_ge.
  rewrite af_sext_uint.
  assert (H15 : uint (mword_of_int 15 : mword 64) = 15) by (vm_compute; reflexivity).
  rewrite H15.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  apply (af_in_arith _ Hr).
Qed.

Lemma af_bltu_out (w : mword 32) :
  ~ (0 <= bv_signed w < Z.of_nat NOFILE)%Z ->
  zopz0zI_u (mword_of_int 15 : mword 64) (sign_extend' 64 w) = true.
Proof.
  intro Hr. unfold NOFILE in Hr. change (Z.of_nat 16) with 16%Z in Hr.
  pose proof (bv_signed_in_range 32 w ltac:(discriminate)) as Hrange.
  assert (Hhm : bv_half_modulus 32 = 2147483648%Z) by (vm_compute; reflexivity).
  rewrite Hhm in Hrange.
  unfold zopz0zI_u. apply Z.ltb_lt.
  rewrite af_sext_uint.
  assert (H15 : uint (mword_of_int 15 : mword 64) = 15) by (vm_compute; reflexivity).
  rewrite H15.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  apply (af_out_arith _ Hr Hrange).
Qed.

Module ArgfdProof (Argint : ARGINT) (Myproc : MYPROC) : ARGFD.

Section ProofArgfd.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ}.
  Context `{CID : CpuId}.

  (* =================================================================== *)
  (*  The shared tail at +0x46: the epilogue, entered by all three arms.  *)
  (* =================================================================== *)
  Lemma af_tail `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (m Mt : regfile) (av : nat) (rv : mword 64)
      (sp0 ra0 s00 s10 s20 : mword 64) (w5 w6 : bv 64)
      (p : mword 64) (b : bool) :
    (6 <= av)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx (mword_of_int 1 : mword 5) = ra0 ->
    m !!! Regidx (mword_of_int 8 : mword 5) = s00 ->
    m !!! Regidx (mword_of_int 9 : mword 5) = s10 ->
    m !!! Regidx (mword_of_int 18 : mword 5) = s20 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 6 ->
    Mt !!! Regidx (mword_of_int 10 : mword 5) = rv ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> (mword_of_int 8 : mword 5) -> r <> (mword_of_int 9 : mword 5) ->
        r <> (mword_of_int 18 : mword 5) -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr Mt (av - 6)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.argfd + 0x46) : mword 64) -∗
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    word_pointsto (pa_stk sp0 4) (DfracOwn 1) s20 -∗
    word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5 -∗
    word_pointsto (pa_stk sp0 6) (DfracOwn 1) w6 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx (mword_of_int 10 : mword 5) = rv⌝ -∗
        sie_cap_gpr mf av b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hav Hsp0 Hra0 Hs00 Hs10 Hs20 Hmtsp Hmta0 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hcont".
    iPoseProof (afi_46 with "Htext") as "Hi46".
    iPoseProof (afi_48 with "Htext") as "Hi48".
    iPoseProof (afi_4a with "Htext") as "Hi4a".
    iPoseProof (afi_4c with "Htext") as "Hi4c".
    iPoseProof (afi_4e with "Htext") as "Hi4e".
    iPoseProof (afi_50 with "Htext") as "Hi50".
    (* ---- +0x46: c.ldsp ra,40(sp) ---- *)
    assert (Hpa1 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hmtsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x46))
              (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5) Mt (av - 6)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi46 Hb1 [-]").
    iIntros (CIDt1 Hkt1) "Hcg Hpc Hb1".
    iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0]> Mt).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0]> Mt) with T1.
    assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.argfd + 0x46) : mword 64) 2
                    = mword_of_int (KernelSyms.argfd + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp48) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T1 upd_ne; [exact Hmtsp | vm_compute; discriminate]).
    (* ---- +0x48: c.ldsp s0,32(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x48))
              (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5) T1 (av - 6)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi48 Hb2 [-]").
    iIntros (CIDt2 Hkt2) "Hcg Hpc Hb2".
    iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00]> T1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00]> T1) with T2.
    assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.argfd + 0x48) : mword 64) 2
                    = mword_of_int (KernelSyms.argfd + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T2 upd_ne; [exact HT1sp | vm_compute; discriminate]).
    (* ---- +0x4a: c.ldsp s1,24(sp) ---- *)
    assert (Hpa3 : add_vec (T2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x4a))
              (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5) T2 (av - 6)%nat s10 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4a Hb3 [-]").
    iIntros (CIDt3 Hkt3) "Hcg Hpc Hb3".
    iEval (rewrite Hpa3) in "Hb3".
    set (T3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg s10]> T2).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg s10]> T2) with T3.
    assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.argfd + 0x4a) : mword 64) 2
                    = mword_of_int (KernelSyms.argfd + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4c) in "Hpc".
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T3 upd_ne; [exact HT2sp | vm_compute; discriminate]).
    (* ---- +0x4c: c.ldsp s2,16(sp) ---- *)
    assert (Hpa4 : add_vec (T3 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HT3sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa4) in "Hb4".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x4c))
              (mword_of_int 2 : mword 6) (mword_of_int 18 : mword 5) T3 (av - 6)%nat s20 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4c Hb4 [-]").
    iIntros (CIDt4 Hkt4) "Hcg Hpc Hb4".
    iEval (rewrite Hpa4) in "Hb4".
    set (T4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg s20]> T3).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg s20]> T3) with T4.
    assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.argfd + 0x4c) : mword 64) 2
                    = mword_of_int (KernelSyms.argfd + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4e) in "Hpc".
    assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T4 upd_ne; [exact HT3sp | vm_compute; discriminate]).
    (* ---- +0x4e: c.addi16sp sp,48 (frame pop) ---- *)
    assert (Hwv : add_vec (T4 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0)
      by (rewrite HT4sp; apply af_pop).
    assert (Hpop : T4 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T4 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6)
      by (rewrite Hwv; exact HT4sp).
    (* rebundle the six slots *)
    assert (E5 : pa_stk (pa_stk sp0 4) 1 = pa_stk sp0 5) by (rewrite pa_stk_assoc; reflexivity).
    assert (E6 : pa_stk (pa_stk sp0 4) 2 = pa_stk sp0 6) by (rewrite pa_stk_assoc; reflexivity).
    iEval (rewrite -E5) in "Hb5".
    iEval (rewrite -E6) in "Hb6".
    iDestruct (stack_own_4_intro sp0 ra0 s00 s10 s20 with "Hb1 Hb2 Hb3 Hb4") as "Hf14".
    iDestruct (stack_own_2_intro (pa_stk sp0 4) w5 w6 with "Hb5 Hb6") as "Hf56".
    iAssert (stack_own sp0 6) with "[Hf14 Hf56]" as "Hframe".
    { rewrite (stack_own_split sp0 4 6 ltac:(lia)). change (6 - 4)%nat with 2%nat. iFrame. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x4e))
              (mword_of_int 3 : mword 6) T4 (av - 6)%nat 6 b Hpop
              with "Hcg Hpc Hi4e Hframe [-]").
    iIntros (CIDt5 Hkt5) "Hcg Hpc".
    assert (Hnk : ((av - 6) + 6)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.argfd + 0x4e) : mword 64) 2
                    = mword_of_int (KernelSyms.argfd + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    set (T5 := <[Regidx csp_rs1 := regval_into_reg (add_vec (T4 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> T4).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (T4 !!! Regidx csp_rs1)
              (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> T4) with T5.
    (* ---- +0x50: c.ret ---- *)
    assert (HT5ra : T5 !!! Regidx (mword_of_int 1 : mword 5) = ra0).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x50))
              (mword_of_int 1 : mword 5) T5 av b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi50 [-]").
    iIntros (CIDt6 Hkt6) "Hcg Hpc".
    iEval (rewrite (rget_ne (CID := CIDt5) T5 (mword_of_int 1 : mword 5)
                      ltac:(vm_compute; discriminate))) in "Hpc".
    iEval (rewrite HT5ra) in "Hpc".
    (* ---- the postcondition ---- *)
    assert (HT5sp : T5 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /T5 upd_eq Hwv; symmetry; exact Hsp0).
    assert (HT5s0 : T5 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_eq. symmetry; exact Hs00. }
    assert (HT5s1 : T5 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_eq. symmetry; exact Hs10. }
    assert (HT5s2 : T5 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_eq. symmetry; exact Hs20. }
    assert (HT5a0 : T5 !!! Regidx (mword_of_int 10 : mword 5) = rv).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_ne; [| vm_compute; discriminate]. exact Hmta0. }
    assert (Hthr5 : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> (mword_of_int 8 : mword 5) ->
              r <> (mword_of_int 9 : mword 5) -> r <> (mword_of_int 18 : mword 5) ->
              T5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /T5 upd_ne; [| congruence].
      rewrite /T4 upd_ne; [| congruence].
      rewrite /T3 upd_ne; [| congruence].
      rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [| congruence].
      apply Hthr; assumption. }
    iSpecialize ("Hcont" $! CIDt6 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! T5 with "[%] Hcg Hpc").
    split; [| exact HT5a0].
    unfold callee_saved.
    split; [exact HT5sp|].
    split; [exact HT5s0|].
    split; [exact HT5s1|].
    split; [exact HT5s2|].
    split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
    apply Hthr5; vm_compute; first [reflexivity | discriminate].
  Qed.

  (* =================================================================== *)
  (*  THE CAPSTONE.                                                       *)
  (* =================================================================== *)
  Lemma wp_argfd_sconf (Φ : mval -> iProp Σ) (γf : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (i : nat) (v : mword 64)
      (pid : mword 32) (V : pprivate) (oldfd : mword 32) (oldf : mword 64) (b : bool)
    : wp_argfd_sconf_body Φ γf m av n eb p C i v pid V oldfd oldf b.
  Proof.
    cbv beta delta [wp_argfd_sconf_body].
    intros pcE pfd pf ret_tgt Hi Ha0 Harg Hnzfd Hnzf Hn Hav.
    unfold argfd_stack in Hav.
    set (sp0 := m !!! Regidx csp_rs1).
    set (ra0 := m !!! Regidx (mword_of_int 1 : mword 5)).
    set (s00 := m !!! Regidx (mword_of_int 8 : mword 5)).
    set (s10 := m !!! Regidx (mword_of_int 9 : mword 5)).
    set (s20 := m !!! Regidx (mword_of_int 18 : mword 5)).
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    iIntros "Hcg Hcpu #Htext #Hdata Hpc Hpriv Hfdcell Hfcell Hcont".
    iPoseProof (afi_00 with "Htext") as "Hi00".
    iPoseProof (afi_02 with "Htext") as "Hi02".
    iPoseProof (afi_04 with "Htext") as "Hi04".
    iPoseProof (afi_06 with "Htext") as "Hi06".
    iPoseProof (afi_08 with "Htext") as "Hi08".
    iPoseProof (afi_0a with "Htext") as "Hi0a".
    iPoseProof (afi_0c with "Htext") as "Hi0c".
    iPoseProof (afi_0e with "Htext") as "Hi0e".
    iPoseProof (afi_10 with "Htext") as "Hi10".
    iPoseProof (afi_14 with "Htext") as "Hi14".
    iPoseProof (afi_18 with "Htext") as "Hi18".
    iPoseProof (afi_1c with "Htext") as "Hi1c".
    iPoseProof (afi_1e with "Htext") as "Hi1e".
    iPoseProof (afi_22 with "Htext") as "Hi22".
    iPoseProof (afi_26 with "Htext") as "Hi26".
    iPoseProof (afi_2a with "Htext") as "Hi2a".
    iPoseProof (afi_2e with "Htext") as "Hi2e".
    iPoseProof (afi_32 with "Htext") as "Hi32".
    iPoseProof (afi_34 with "Htext") as "Hi34".
    iPoseProof (afi_36 with "Htext") as "Hi36".
    iPoseProof (afi_38 with "Htext") as "Hi38".
    iPoseProof (afi_3c with "Htext") as "Hi3c".
    iPoseProof (afi_40 with "Htext") as "Hi40".
    iPoseProof (afi_42 with "Htext") as "Hi42".
    iPoseProof (afi_44 with "Htext") as "Hi44".
    iPoseProof (afi_52 with "Htext") as "Hi52".
    iPoseProof (afi_54 with "Htext") as "Hi54".
    iPoseProof (afi_56 with "Htext") as "Hi56".
    iPoseProof (afi_58 with "Htext") as "Hi58".
    (* ---- +0x00: c.addi16sp sp,-48 (frame push) ---- *)
    iApply (wp_caddi16sp_push_s_sconf Φ pcE (mword_of_int 61 : mword 6) m av 6 b
              ltac:(lia) (af_push (m !!! Regidx csp_rs1))
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hk1) "Hcg Hframe Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.argfd + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /M1 upd_eq; apply af_push).
    (* the six frame slots *)
    assert (E5 : pa_stk (pa_stk sp0 4) 1 = pa_stk sp0 5) by (rewrite pa_stk_assoc; reflexivity).
    assert (E6 : pa_stk (pa_stk sp0 4) 2 = pa_stk sp0 6) by (rewrite pa_stk_assoc; reflexivity).
    rewrite (stack_own_split sp0 4 6 ltac:(lia)). change (6 - 4)%nat with 2%nat.
    iDestruct "Hframe" as "[Hf14 Hf56]".
    iDestruct (stack_own_4_elim with "Hf14") as (u1 u2 u3 u4) "(Hs1 & Hs2 & Hs3 & Hs4)".
    iDestruct (stack_own_2_elim with "Hf56") as (w5 w6) "[Hs5 Hs6]".
    iEval (rewrite E5) in "Hs5". iEval (rewrite E6) in "Hs6".
    (* ---- +0x02 .. +0x08: save ra / s0 / s1 / s2 ---- *)
    assert (Hpa1 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa2 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa3 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa4 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hs1".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x02))
              (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5) M1 (av - 6)%nat u1 b
              with "Hcg Hpc Hi02 Hs1 [-]").
    iIntros (CID2 Hk2) "Hcg Hpc Hs1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.argfd + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.argfd + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iEval (rewrite -Hpa2) in "Hs2".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x04))
              (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5) M1 (av - 6)%nat u2 b
              with "Hcg Hpc Hi04 Hs2 [-]").
    iIntros (CID3 Hk3) "Hcg Hpc Hs2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.argfd + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.argfd + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iEval (rewrite -Hpa3) in "Hs3".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x06))
              (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5) M1 (av - 6)%nat u3 b
              with "Hcg Hpc Hi06 Hs3 [-]").
    iIntros (CID4 Hk4) "Hcg Hpc Hs3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.argfd + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.argfd + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iEval (rewrite -Hpa4) in "Hs4".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x08))
              (mword_of_int 2 : mword 6) (mword_of_int 18 : mword 5) M1 (av - 6)%nat u4 b
              with "Hcg Hpc Hi08 Hs4 [-]").
    iIntros (CID5 Hk5) "Hcg Hpc Hs4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.argfd + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.argfd + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* name the four saved values *)
    assert (HM1ra : M1 !!! Regidx (mword_of_int 1 : mword 5) = ra0)
      by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HM1s0 : M1 !!! Regidx (mword_of_int 8 : mword 5) = s00)
      by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HM1s1 : M1 !!! Regidx (mword_of_int 9 : mword 5) = s10)
      by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HM1s2 : M1 !!! Regidx (mword_of_int 18 : mword 5) = s20)
      by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite (rget_ne (CID := CID1) M1 (mword_of_int 1 : mword 5)
                      ltac:(vm_compute; discriminate)) Hpa1 HM1ra) in "Hs1".
    iEval (rewrite (rget_ne (CID := CID2) M1 (mword_of_int 8 : mword 5)
                      ltac:(vm_compute; discriminate)) Hpa2 HM1s0) in "Hs2".
    iEval (rewrite (rget_ne (CID := CID3) M1 (mword_of_int 9 : mword 5)
                      ltac:(vm_compute; discriminate)) Hpa3 HM1s1) in "Hs3".
    iEval (rewrite (rget_ne (CID := CID4) M1 (mword_of_int 18 : mword 5)
                      ltac:(vm_compute; discriminate)) Hpa4 HM1s2) in "Hs4".
    (* ---- +0x0a: c.addi4spn s0,sp,48 -- s0 := the entry sp ---- *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x0a))
              (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) (mword_of_int 8 : mword 5)
              M1 (av - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hk6) "Hcg Hpc".
    set (M2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> M1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
              (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> M1) with M2.
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.argfd + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.argfd + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    assert (HM2s0 : M2 !!! Regidx (mword_of_int 8 : mword 5) = sp0).
    { rewrite /M2 upd_eq HM1sp. apply af_s0_entry. }
    (* ---- +0x0c: c.mv s2,a1 -- s2 := pfd ---- *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x0c))
              (mword_of_int 18 : mword 5) (mword_of_int 11 : mword 5) M2 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID7 Hk7) "Hcg Hpc".
    set (M3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
                  (add_vec zero_reg (M2 !!! Regidx (mword_of_int 11 : mword 5)))]> M2).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
              (add_vec zero_reg (M2 !!! Regidx (mword_of_int 11 : mword 5)))]> M2) with M3.
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.argfd + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.argfd + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    assert (HM2a1 : M2 !!! Regidx (mword_of_int 11 : mword 5) = pfd).
    { rewrite /M2 upd_ne; [| vm_compute; discriminate].
      rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HM3s2 : M3 !!! Regidx (mword_of_int 18 : mword 5) = pfd).
    { rewrite /M3 upd_eq HM2a1. apply add_vec_zero_l. }
    assert (HM3s0 : M3 !!! Regidx (mword_of_int 8 : mword 5) = sp0)
      by (rewrite /M3 upd_ne; [exact HM2s0 | vm_compute; discriminate]).
    (* ---- +0x0e: c.mv s1,a2 -- s1 := pf ---- *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x0e))
              (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 5) M3 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID8 Hk8) "Hcg Hpc".
    set (M4 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
                  (add_vec zero_reg (M3 !!! Regidx (mword_of_int 12 : mword 5)))]> M3).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
              (add_vec zero_reg (M3 !!! Regidx (mword_of_int 12 : mword 5)))]> M3) with M4.
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.argfd + 0x0e) : mword 64) 2
                    = mword_of_int (KernelSyms.argfd + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    assert (HM3a2 : M3 !!! Regidx (mword_of_int 12 : mword 5) = pf).
    { rewrite /M3 upd_ne; [| vm_compute; discriminate].
      rewrite /M2 upd_ne; [| vm_compute; discriminate].
      rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HM4s1 : M4 !!! Regidx (mword_of_int 9 : mword 5) = pf).
    { rewrite /M4 upd_eq HM3a2. apply add_vec_zero_l. }
    assert (HM4s2 : M4 !!! Regidx (mword_of_int 18 : mword 5) = pfd)
      by (rewrite /M4 upd_ne; [exact HM3s2 | vm_compute; discriminate]).
    assert (HM4s0 : M4 !!! Regidx (mword_of_int 8 : mword 5) = sp0)
      by (rewrite /M4 upd_ne; [exact HM3s0 | vm_compute; discriminate]).
    (* ---- +0x10: addi a1,s0,-36 -- a1 := &fd ---- *)
    iApply (wp_addi4_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x10))
              (mword_of_int 11 : mword 5) (mword_of_int 8 : mword 5) (mword_of_int 0xfdc : mword 12)
              M4 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 [-]").
    iIntros (CID9 Hk9) "Hcg Hpc".
    set (M5 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg
                  (add_vec (M4 !!! Regidx (mword_of_int 8 : mword 5)) (sign_extend' 64 (mword_of_int 0xfdc : mword 12)))]> M4).
    change (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg
              (add_vec (M4 !!! Regidx (mword_of_int 8 : mword 5)) (sign_extend' 64 (mword_of_int 0xfdc : mword 12)))]> M4) with M5.
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.argfd + 0x10) : mword 64) 4
                    = mword_of_int (KernelSyms.argfd + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    assert (HM5a1 : M5 !!! Regidx (mword_of_int 11 : mword 5) = pa_add (pa_stk sp0 5) 4).
    { rewrite /M5 upd_eq HM4s0. apply af_addr_fd. }
    (* ---- +0x14: jal ra,argint ---- *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x14))
              (mword_of_int 1 : mword 5) (mword_of_int 2088428 : mword 21) M5 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi14 [-]").
    iIntros (CID10 Hk10) "Hcg Hpc".
    set (M6 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.argfd + 0x14) : mword 64) 4)]> M5).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.argfd + 0x14) : mword 64) 4)]> M5) with M6.
    assert (Hjai : add_vec (mword_of_int (KernelSyms.argfd + 0x14) : mword 64)
                     (sign_extend' 64 (mword_of_int 2088428 : mword 21)) = mword_of_int KernelSyms.argint)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjai) in "Hpc".
    assert (HM6ra : M6 !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KernelSyms.argfd + 0x14) : mword 64) 4)
      by (rewrite /M6 upd_eq; reflexivity).
    assert (HM6a1 : M6 !!! Regidx (mword_of_int 11 : mword 5) = pa_add (pa_stk sp0 5) 4)
      by (rewrite /M6 upd_ne; [exact HM5a1 | vm_compute; discriminate]).
    assert (HM6a0 : M6 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (Z.of_nat i)).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate].
      rewrite /M5 upd_ne; [| vm_compute; discriminate].
      rewrite /M4 upd_ne; [| vm_compute; discriminate].
      rewrite /M3 upd_ne; [| vm_compute; discriminate].
      rewrite /M2 upd_ne; [| vm_compute; discriminate].
      rewrite /M1 upd_ne; [| vm_compute; discriminate]. exact Ha0. }
    assert (HM6sp : M6 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate].
      rewrite /M5 upd_ne; [| vm_compute; discriminate].
      rewrite /M4 upd_ne; [| vm_compute; discriminate].
      rewrite /M3 upd_ne; [| vm_compute; discriminate].
      rewrite /M2 upd_ne; [| vm_compute; discriminate]. exact HM1sp. }
    assert (HM6s0 : M6 !!! Regidx (mword_of_int 8 : mword 5) = sp0).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate].
      rewrite /M5 upd_ne; [| vm_compute; discriminate]. exact HM4s0. }
    assert (HM6s1 : M6 !!! Regidx (mword_of_int 9 : mword 5) = pf).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate].
      rewrite /M5 upd_ne; [| vm_compute; discriminate]. exact HM4s1. }
    assert (HM6s2 : M6 !!! Regidx (mword_of_int 18 : mword 5) = pfd).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate].
      rewrite /M5 upd_ne; [| vm_compute; discriminate]. exact HM4s2. }
    (* the [int fd] local: the UPPER word of frame slot 5 *)
    iDestruct (word_pointsto_aligned_p with "Hs5") as %Hal5.
    iDestruct (word_pointsto_split4 with "Hs5") as "[Hs5lo Hs5hi]".
    iEval (rewrite -HM6a1) in "Hs5hi".
    (* argint reads the trapframe pointer AND page out of [proc_priv] *)
    iDestruct (proc_priv_ofile_len with "Hpriv") as %Hoflen.
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfp & Hpage & Hpback)".
    (* ---- argint(n, &fd) ---- *)
    (* [Hcpu] came in at the entry hart; nine leaf steps may have moved us, so
       re-anchor it before argint's own [cpu_own] premise can take it. *)
    iDestruct (cpu_own_transport CID CID10 n eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Argint.wp_argint_sconf Φ M6 (av - 6)%nat n eb p C i
              (ud_tfp (pv_upt V)) (pv_tf V) v (word_hi w5) (DfracOwn (1/4)) b
              Hi HM6a0 Harg Hn ltac:(lia)
              with "Hcg Hcpu Htext Hdata Hpc Htfp Hpage Hs5hi [-]").
    iIntros (CID11 Hk11 A) "%HcsA Hcg Hcpu Hpc Htfp Hpage Hs5hi".
    iDestruct ("Hpback" with "Htfp Hpage") as "Hpriv".
    assert (Hpc18 : ret_pc (M6 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.argfd + 0x18))
      by (rewrite HM6ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    (* the callee-saved registers argfd parked before the call *)
    assert (HAsp : A !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)); exact HM6sp).
    assert (HAs0 : A !!! Regidx (mword_of_int 8 : mword 5) = sp0)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 8) ltac:(vm_compute; reflexivity)); exact HM6s0).
    assert (HAs1 : A !!! Regidx (mword_of_int 9 : mword 5) = pf)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HM6s1).
    assert (HAs2 : A !!! Regidx (mword_of_int 18 : mword 5) = pfd)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 18) ltac:(vm_compute; reflexivity)); exact HM6s2).
    (* the residual threading fact every arm hands to [af_tail] *)
    assert (HthrA : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> (mword_of_int 8 : mword 5) -> r <> (mword_of_int 9 : mword 5) ->
              r <> (mword_of_int 18 : mword 5) -> A !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N11 : r <> mword_of_int 11)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite (callee_saved_lookup HcsA r Hr).
      rewrite /M6 upd_ne; [| congruence].
      rewrite /M5 upd_ne; [| congruence].
      rewrite /M4 upd_ne; [| congruence].
      rewrite /M3 upd_ne; [| congruence].
      rewrite /M2 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence]. reflexivity. }
    (* ---- +0x18: lw a4,-36(s0) -- a4 := fd ---- *)
    assert (Haddrfd : add_vec (A !!! Regidx (mword_of_int 8 : mword 5))
                        (sign_extend' 64 (mword_of_int 0xfdc : mword 12)) = pa_add (pa_stk sp0 5) 4)
      by (rewrite HAs0; apply af_addr_fd).
    iEval (rewrite HM6a1 -Haddrfd) in "Hs5hi".
    iApply (wp_lw_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x18))
              (mword_of_int 14 : mword 5) (mword_of_int 8 : mword 5) (mword_of_int 0xfdc : mword 12)
              A (av - 6)%nat (trunc32 v) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18 Hs5hi [-]").
    iIntros (CID12 Hk12) "Hcg Hpc Hs5hi".
    set (A1 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 (trunc32 v))]> A).
    change (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 (trunc32 v))]> A) with A1.
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.argfd + 0x18) : mword 64) 4
                    = mword_of_int (KernelSyms.argfd + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* ---- +0x1c: c.li a5,15 -- NOFILE - 1 ---- *)
    iApply (wp_cli_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x1c))
              (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 6)
              (mword_of_int 15 : mword 64) A1 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi1c [-]").
    iIntros (CID13 Hk13) "Hcg Hpc".
    set (A2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 15 : mword 64)]> A1).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 15 : mword 64)]> A1) with A2.
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.argfd + 0x1c) : mword 64) 2
                    = mword_of_int (KernelSyms.argfd + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    assert (HA2a5 : A2 !!! Regidx (mword_of_int 15 : mword 5) = (mword_of_int 15 : mword 64))
      by (rewrite /A2 upd_eq; reflexivity).
    assert (HA2a4 : A2 !!! Regidx (mword_of_int 14 : mword 5) = sign_extend' 64 (trunc32 v)).
    { rewrite /A2 upd_ne; [| vm_compute; discriminate]. rewrite /A1 upd_eq. reflexivity. }
    assert (HA2sp : A2 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate]. exact HAsp. }
    assert (HA2s0 : A2 !!! Regidx (mword_of_int 8 : mword 5) = sp0).
    { rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate]. exact HAs0. }
    assert (HA2s1 : A2 !!! Regidx (mword_of_int 9 : mword 5) = pf).
    { rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate]. exact HAs1. }
    assert (HA2s2 : A2 !!! Regidx (mword_of_int 18 : mword 5) = pfd).
    { rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate]. exact HAs2. }
    assert (HA2a5' : forall CID' : CpuId,
              rget (CID := CID') A2 (mword_of_int 15 : mword 5) = (mword_of_int 15 : mword 64))
      by (intros CID'; rgne; exact HA2a5).
    assert (HA2a4' : forall CID' : CpuId,
              rget (CID := CID') A2 (mword_of_int 14 : mword 5) = sign_extend' 64 (trunc32 v))
      by (intros CID'; rgne; exact HA2a4).
    assert (HthrA2 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> (mword_of_int 8 : mword 5) -> r <> (mword_of_int 9 : mword 5) ->
              r <> (mword_of_int 18 : mword 5) -> A2 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      assert (N14 : r <> mword_of_int 14)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> mword_of_int 15)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence].
      apply HthrA; assumption. }
    (* ---- +0x1e: bltu a5,a4 -- the fused range test ---- *)
    destruct (decide (0 <= bv_signed (trunc32 v) < Z.of_nat NOFILE)%Z) as [Hrng | Hrng].
    - (* ============ IN RANGE ============ *)
      iApply (wp_bltu_fall_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x1e))
                (mword_of_int 52 : mword 13) (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5)
                A2 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HA2a5' HA2a4'; apply af_bltu_in; exact Hrng)
                with "Hcg Hpc Hi1e [-]").
      iIntros (CID14 Hk14) "Hcg Hpc".
      assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.argfd + 0x1e) : mword 64) 4
                      = mword_of_int (KernelSyms.argfd + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      (* the descriptor index, and the pointer it holds *)
      set (fd := Z.to_nat (bv_signed (trunc32 v))).
      assert (Hfdlt : (fd < NOFILE)%nat).
      { subst fd. apply Nat2Z.inj_lt.
        rewrite Z2Nat.id; [exact (proj2 Hrng) | exact (proj1 Hrng)]. }
      assert (Hfdz : Z.of_nat fd = bv_signed (trunc32 v))
        by (subst fd; apply Z2Nat.id; exact (proj1 Hrng)).
      assert (Hsext : sign_extend' 64 (trunc32 v) = mword_of_int (Z.of_nat fd))
        by (rewrite Hfdz; apply sext32_64_moi).
      destruct (pv_ofile V !! fd) as [fv|] eqn:Hlk; last first.
      { exfalso. apply lookup_ge_None_1 in Hlk. rewrite Hoflen in Hlk. lia. }
      (* ---- +0x22: jal ra,myproc ---- *)
      iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x22))
                (mword_of_int 1 : mword 5) (mword_of_int 2084574 : mword 21) A2 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi22 [-]").
      iIntros (CID15 Hk15) "Hcg Hpc".
      set (B := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
                   (add_vec_int (mword_of_int (KernelSyms.argfd + 0x22) : mword 64) 4)]> A2).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
                (add_vec_int (mword_of_int (KernelSyms.argfd + 0x22) : mword 64) 4)]> A2) with B.
      assert (Hjmp : add_vec (mword_of_int (KernelSyms.argfd + 0x22) : mword 64)
                       (sign_extend' 64 (mword_of_int 2084574 : mword 21)) = mword_of_int KernelSyms.myproc)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjmp) in "Hpc".
      assert (HBra : B !!! Regidx (mword_of_int 1 : mword 5)
                     = add_vec_int (mword_of_int (KernelSyms.argfd + 0x22) : mword 64) 4)
        by (rewrite /B upd_eq; reflexivity).
      iDestruct (cpu_own_transport CID11 CID15 n eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iApply (Myproc.wp_myproc_sconf Φ B (av - 6)%nat n eb p C b
                Hn ltac:(lia)
                with "Hcg Hcpu Htext Hpc [-]").
      iIntros (CID16 Hk16 ms P) "%Hms Hcg Hcpu Hpc %HcsP".
      destruct HcsP as [HcsP HPa0].
      assert (Hpc26 : ret_pc (B !!! Regidx (mword_of_int 1 : mword 5))
                      = mword_of_int (KernelSyms.argfd + 0x26))
        by (rewrite HBra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc26) in "Hpc".
      assert (HPsp : P !!! Regidx csp_rs1 = pa_stk sp0 6).
      { rewrite (callee_saved_lookup HcsP csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite /B upd_ne; [| vm_compute; discriminate]. exact HA2sp. }
      assert (HPs0 : P !!! Regidx (mword_of_int 8 : mword 5) = sp0).
      { rewrite (callee_saved_lookup HcsP (mword_of_int 8) ltac:(vm_compute; reflexivity)).
        rewrite /B upd_ne; [| vm_compute; discriminate]. exact HA2s0. }
      assert (HPs1 : P !!! Regidx (mword_of_int 9 : mword 5) = pf).
      { rewrite (callee_saved_lookup HcsP (mword_of_int 9) ltac:(vm_compute; reflexivity)).
        rewrite /B upd_ne; [| vm_compute; discriminate]. exact HA2s1. }
      assert (HPs2 : P !!! Regidx (mword_of_int 18 : mword 5) = pfd).
      { rewrite (callee_saved_lookup HcsP (mword_of_int 18) ltac:(vm_compute; reflexivity)).
        rewrite /B upd_ne; [| vm_compute; discriminate]. exact HA2s2. }
      assert (HthrP : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> (mword_of_int 8 : mword 5) -> r <> (mword_of_int 9 : mword 5) ->
                r <> (mword_of_int 18 : mword 5) -> P !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18.
        assert (N1 : r <> mword_of_int 1)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite (callee_saved_lookup HcsP r Hr).
        rewrite /B upd_ne; [| congruence].
        apply HthrA2; assumption. }
      (* ---- +0x26: lw a4,-36(s0) -- reload fd ---- *)
      assert (Haddrfd' : add_vec (P !!! Regidx (mword_of_int 8 : mword 5))
                           (sign_extend' 64 (mword_of_int 0xfdc : mword 12)) = pa_add (pa_stk sp0 5) 4)
        by (rewrite HPs0; apply af_addr_fd).
      iEval (rewrite Haddrfd -Haddrfd') in "Hs5hi".
      iApply (wp_lw_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x26))
                (mword_of_int 14 : mword 5) (mword_of_int 8 : mword 5) (mword_of_int 0xfdc : mword 12)
                P (av - 6)%nat (trunc32 v) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi26 Hs5hi [-]").
      iIntros (CID17 Hk17) "Hcg Hpc Hs5hi".
      iEval (rewrite Haddrfd') in "Hs5hi".
      set (C1 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 (trunc32 v))]> P).
      change (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 (trunc32 v))]> P) with C1.
      assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.argfd + 0x26) : mword 64) 4
                      = mword_of_int (KernelSyms.argfd + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      assert (HC1a4 : C1 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int (Z.of_nat fd))
        by (rewrite /C1 upd_eq; exact Hsext).
      (* ---- +0x2a: slli a5,a4,3 ---- *)
      assert (Hfdb : (Z.of_nat fd < 16)%Z) by (unfold NOFILE in Hfdlt; lia).
      assert (HC1a4' : forall CID' : CpuId,
                rget (CID := CID') C1 (mword_of_int 14 : mword 5) = mword_of_int (Z.of_nat fd))
        by (intros CID'; rgne; exact HC1a4).
      iApply (wp_slli_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x2a))
                (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 3 : mword 6)
                (mword_of_int (Z.of_nat fd * 8) : mword 64) C1 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(rewrite HC1a4'; apply ofile_slli3; lia)
                with "Hcg Hpc Hi2a [-]").
      iIntros (CID18 Hk18) "Hcg Hpc".
      set (C2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int (Z.of_nat fd * 8) : mword 64)]> C1).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int (Z.of_nat fd * 8) : mword 64)]> C1) with C2.
      assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.argfd + 0x2a) : mword 64) 4
                      = mword_of_int (KernelSyms.argfd + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2e) in "Hpc".
      (* ---- +0x2e: addi a5,a5,208 ---- *)
      iApply (wp_addi4_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x2e))
                (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 208 : mword 12)
                C2 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2e [-]").
      iIntros (CID19 Hk19) "Hcg Hpc".
      set (C3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
                    (add_vec (C2 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 208 : mword 12)))]> C2).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
                (add_vec (C2 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 208 : mword 12)))]> C2) with C3.
      assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.argfd + 0x2e) : mword 64) 4
                      = mword_of_int (KernelSyms.argfd + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp32) in "Hpc".
      assert (HC3a5 : C3 !!! Regidx (mword_of_int 15 : mword 5)
                      = mword_of_int (208 + 8 * Z.of_nat fd)).
      { rewrite /C3 upd_eq /C2 upd_eq.
        rewrite (ofile_addi208 (Z.of_nat fd * 8) ltac:(lia) ltac:(lia)).
        assert (Harith : (208 + Z.of_nat fd * 8)%Z = (208 + 8 * Z.of_nat fd)%Z) by lia.
        rewrite Harith. reflexivity. }
      assert (HC3a0 : C3 !!! Regidx (mword_of_int 10 : mword 5) = p).
      { rewrite /C3 upd_ne; [| vm_compute; discriminate].
        rewrite /C2 upd_ne; [| vm_compute; discriminate].
        rewrite /C1 upd_ne; [| vm_compute; discriminate]. exact HPa0. }
      (* ---- +0x32: c.add a0,a0,a5 -- a0 := &p->ofile[fd] ---- *)
      iApply (wp_cadd_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x32))
                (mword_of_int 10 : mword 5) (mword_of_int 15 : mword 5) C3 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi32 [-]").
      iIntros (CID20 Hk20) "Hcg Hpc".
      set (C4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
                    (add_vec (C3 !!! Regidx (mword_of_int 10 : mword 5)) (C3 !!! Regidx (mword_of_int 15 : mword 5)))]> C3).
      change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
                (add_vec (C3 !!! Regidx (mword_of_int 10 : mword 5)) (C3 !!! Regidx (mword_of_int 15 : mword 5)))]> C3) with C4.
      assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.argfd + 0x32) : mword 64) 2
                      = mword_of_int (KernelSyms.argfd + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp34) in "Hpc".
      assert (HC4a0 : C4 !!! Regidx (mword_of_int 10 : mword 5) = p_ofile p fd)
        by (rewrite /C4 upd_eq HC3a0 HC3a5; reflexivity).
      (* ---- +0x34: c.ld a5,0(a0) -- f = p->ofile[fd] ---- *)
      iDestruct (proc_priv_ofile γf p pid V fd fv Hlk with "Hpriv") as "[Hslot Hback]".
      iDestruct "Hslot" as "[Hcell Hrest]".
      assert (Haddrof : add_vec (C4 !!! Regidx (mword_of_int 10 : mword 5))
                          (sign_extend' 64 (mword_of_int 0 : mword 12)) = p_ofile p fd)
        by (rewrite HC4a0; apply addv_sext0).
      iEval (rewrite -Haddrof) in "Hcell".
      iApply (wp_cld_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x34))
                (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 0 : mword 12)
                C4 (av - 6)%nat fv b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi34 Hcell [-]").
      iIntros (CID21 Hk21) "Hcg Hpc Hcell".
      iEval (rewrite Haddrof) in "Hcell".
      iDestruct ("Hback" $! fv with "[Hcell Hrest]") as "Hpriv"; [by iFrame|].
      rewrite (upd_ofile_id V fd fv Hlk).
      set (C5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg fv]> C4).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg fv]> C4) with C5.
      assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.argfd + 0x34) : mword 64) 2
                      = mword_of_int (KernelSyms.argfd + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      assert (HC5a5 : C5 !!! Regidx (mword_of_int 15 : mword 5) = fv)
        by (rewrite /C5 upd_eq; reflexivity).
      assert (HC5sp : C5 !!! Regidx csp_rs1 = pa_stk sp0 6).
      { rewrite /C5 upd_ne; [| vm_compute; discriminate].
        rewrite /C4 upd_ne; [| vm_compute; discriminate].
        rewrite /C3 upd_ne; [| vm_compute; discriminate].
        rewrite /C2 upd_ne; [| vm_compute; discriminate].
        rewrite /C1 upd_ne; [| vm_compute; discriminate]. exact HPsp. }
      assert (HC5s1 : C5 !!! Regidx (mword_of_int 9 : mword 5) = pf).
      { rewrite /C5 upd_ne; [| vm_compute; discriminate].
        rewrite /C4 upd_ne; [| vm_compute; discriminate].
        rewrite /C3 upd_ne; [| vm_compute; discriminate].
        rewrite /C2 upd_ne; [| vm_compute; discriminate].
        rewrite /C1 upd_ne; [| vm_compute; discriminate]. exact HPs1. }
      assert (HC5s2 : C5 !!! Regidx (mword_of_int 18 : mword 5) = pfd).
      { rewrite /C5 upd_ne; [| vm_compute; discriminate].
        rewrite /C4 upd_ne; [| vm_compute; discriminate].
        rewrite /C3 upd_ne; [| vm_compute; discriminate].
        rewrite /C2 upd_ne; [| vm_compute; discriminate].
        rewrite /C1 upd_ne; [| vm_compute; discriminate]. exact HPs2. }
      assert (HC5a4 : C5 !!! Regidx (mword_of_int 14 : mword 5) = sign_extend' 64 (trunc32 v)).
      { rewrite /C5 upd_ne; [| vm_compute; discriminate].
        rewrite /C4 upd_ne; [| vm_compute; discriminate].
        rewrite /C3 upd_ne; [| vm_compute; discriminate].
        rewrite /C2 upd_ne; [| vm_compute; discriminate].
        rewrite /C1 upd_eq. reflexivity. }
      assert (HC5a5' : forall CID' : CpuId,
                rget (CID := CID') C5 (mword_of_int 15 : mword 5) = fv)
        by (intros CID'; rgne; exact HC5a5).
      assert (HC5s2' : forall CID' : CpuId,
                rget (CID := CID') C5 (mword_of_int 18 : mword 5) = pfd)
        by (intros CID'; rgne; exact HC5s2).
      assert (HC5a4' : forall CID' : CpuId,
                rget (CID := CID') C5 (mword_of_int 14 : mword 5) = sign_extend' 64 (trunc32 v))
        by (intros CID'; rgne; exact HC5a4).
      assert (HthrC5 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> (mword_of_int 8 : mword 5) -> r <> (mword_of_int 9 : mword 5) ->
                r <> (mword_of_int 18 : mword 5) -> C5 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18.
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N14 : r <> mword_of_int 14)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N15 : r <> mword_of_int 15)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /C5 upd_ne; [| congruence].
        rewrite /C4 upd_ne; [| congruence].
        rewrite /C3 upd_ne; [| congruence].
        rewrite /C2 upd_ne; [| congruence].
        rewrite /C1 upd_ne; [| congruence].
        apply HthrP; assumption. }
      (* ---- +0x36: c.beqz a5 -- is the descriptor free? ---- *)
      destruct (decide (fv = (zero_reg : mword 64))) as [Hfv0 | Hfvnz].
      + (* ------- free: return -1 ------- *)
        iApply (wp_cbeqz_taken_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x36))
                  (mword_of_int 16 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                  C5 (av - 6)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite HC5a5' Hfv0; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi36 [-]").
        iNext. iIntros (CID22 Hk22) "Hcg Hpc".
        assert (Hbt1 : add_vec (mword_of_int (KernelSyms.argfd + 0x36) : mword 64)
                         (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 16 : mword 8) ('b"0"))))
                       = mword_of_int (KernelSyms.argfd + 0x56))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hbt1) in "Hpc".
        (* +0x56 c.li a0,-1 *)
        iApply (wp_cli_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x56))
                  (mword_of_int 10 : mword 5) (mword_of_int 63 : mword 6)
                  (mword_of_int (-1) : mword 64) C5 (av - 6)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hi56 [-]").
        iIntros (CID23 Hk23) "Hcg Hpc".
        set (D := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (mword_of_int (-1) : mword 64)]> C5).
        change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (mword_of_int (-1) : mword 64)]> C5) with D.
        assert (Hpp58 : add_vec_int (mword_of_int (KernelSyms.argfd + 0x56) : mword 64) 2
                        = mword_of_int (KernelSyms.argfd + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp58) in "Hpc".
        (* +0x58 c.j -0x12 *)
        iApply (wp_cj_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x58))
                  (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0"))) D (av - 6)%nat b
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi58 [-]").
        iIntros (CID24 Hk24). iNext. iIntros "Hcg Hpc".
        assert (Hjt : add_vec (mword_of_int (KernelSyms.argfd + 0x58) : mword 64)
                        (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0"))))
                      = mword_of_int (KernelSyms.argfd + 0x46))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjt) in "Hpc".
        iDestruct (word_pointsto_join4 _ _ _ _ Hal5 with "Hs5lo Hs5hi") as "Hs5".
        assert (HDsp : D !!! Regidx csp_rs1 = pa_stk sp0 6)
          by (rewrite /D upd_ne; [exact HC5sp | vm_compute; discriminate]).
        assert (HDa0 : D !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int (-1) : mword 64))
          by (rewrite /D upd_eq; reflexivity).
        assert (HthrD : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                  r <> (mword_of_int 8 : mword 5) -> r <> (mword_of_int 9 : mword 5) ->
                  r <> (mword_of_int 18 : mword 5) -> D !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          assert (N10 : r <> mword_of_int 10)
            by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /D upd_ne; [| congruence]. apply HthrC5; assumption. }
        iApply (af_tail Φ m D av (mword_of_int (-1) : mword 64) sp0 ra0 s00 s10 s20 _ w6 p b
                  ltac:(lia) eq_refl eq_refl eq_refl eq_refl eq_refl HDsp HDa0 HthrD
                  with "Hcg Htext Hpc Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 [-]").
        iIntros (CID25 Hk25 mf) "[%Hcsf %Hmfa0] Hcg Hpc".
        iDestruct (cpu_own_transport CID16 CID25 n eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
        iSpecialize ("Hcont" $! CID25 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! mf with "[%] Hcg Hcpu Hpc Hpriv [Hfdcell Hfcell]"); [exact Hcsf|].
        rewrite /argfd_post. iLeft. iFrame "Hfdcell Hfcell". iPureIntro.
        split; [exact Hmfa0|].
        unfold arg_fd. rewrite (decide_True _ _ Hrng).
        change (Z.to_nat (bv_signed (trunc32 v))) with fd.
        rewrite Hlk. rewrite (decide_True _ _ Hfv0). reflexivity.
      + (* ------- a live file: the success path ------- *)
        iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x36))
                  (mword_of_int 16 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                  C5 (av - 6)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite HC5a5'; apply eq_vec_false_iff; exact Hfvnz)
                  with "Hcg Hpc Hi36 [-]").
        iIntros (CID22 Hk22) "Hcg Hpc".
        assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.argfd + 0x36) : mword 64) 2
                        = mword_of_int (KernelSyms.argfd + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp38) in "Hpc".
        (* ---- +0x38: beq s2,x0 -- pfd is not null, so fall through ---- *)
        iApply (wp_beqz_x0_fall_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x38))
                  (mword_of_int 8 : mword 13) (mword_of_int 18 : mword 5) C5 (av - 6)%nat b
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite HC5s2'; apply eq_vec_false_iff; exact Hnzfd)
                  with "Hcg Hpc Hi38 [-]").
        iIntros (CID23 Hk23) "Hcg Hpc".
        assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.argfd + 0x38) : mword 64) 4
                        = mword_of_int (KernelSyms.argfd + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp3c) in "Hpc".
        (* ---- +0x3c: sw a4,0(s2) -- *pfd = fd ---- *)
        assert (Haddrp : add_vec (C5 !!! Regidx (mword_of_int 18 : mword 5))
                           (sign_extend' 64 (mword_of_int 0 : mword 12)) = pfd)
          by (rewrite HC5s2; apply addv_sext0).
        iEval (rewrite -Haddrp) in "Hfdcell".
        iApply (wp_sw_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x3c))
                  (mword_of_int 14 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
                  C5 (av - 6)%nat oldfd b
                  with "Hcg Hpc Hi3c Hfdcell [-]").
        iIntros (CID24 Hk24) "Hcg Hpc Hfdcell".
        iEval (rewrite Haddrp HC5a4' trunc32_sext64) in "Hfdcell".
        assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.argfd + 0x3c) : mword 64) 4
                        = mword_of_int (KernelSyms.argfd + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp40) in "Hpc".
        (* ---- +0x40: c.li a0,0 ---- *)
        iApply (wp_cli_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x40))
                  (mword_of_int 10 : mword 5) (mword_of_int 0 : mword 6)
                  (zero_reg : mword 64) C5 (av - 6)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hi40 [-]").
        iIntros (CID25 Hk25) "Hcg Hpc".
        set (E1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (zero_reg : mword 64)]> C5).
        change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (zero_reg : mword 64)]> C5) with E1.
        assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.argfd + 0x40) : mword 64) 2
                        = mword_of_int (KernelSyms.argfd + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp42) in "Hpc".
        assert (HE1s1 : E1 !!! Regidx (mword_of_int 9 : mword 5) = pf)
          by (rewrite /E1 upd_ne; [exact HC5s1 | vm_compute; discriminate]).
        assert (HE1a5 : E1 !!! Regidx (mword_of_int 15 : mword 5) = fv)
          by (rewrite /E1 upd_ne; [exact HC5a5 | vm_compute; discriminate]).
        assert (HE1s1' : forall CID' : CpuId,
                  rget (CID := CID') E1 (mword_of_int 9 : mword 5) = pf)
          by (intros CID'; rgne; exact HE1s1).
        assert (HE1a5' : forall CID' : CpuId,
                  rget (CID := CID') E1 (mword_of_int 15 : mword 5) = fv)
          by (intros CID'; rgne; exact HE1a5).
        (* ---- +0x42: c.beqz s1 -- pf is not null, so fall through ---- *)
        iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x42))
                  (mword_of_int 2 : mword 8) (Cregidx (mword_of_int 1)) (mword_of_int 9 : mword 5)
                  E1 (av - 6)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite HE1s1'; apply eq_vec_false_iff; exact Hnzf)
                  with "Hcg Hpc Hi42 [-]").
        iIntros (CID26 Hk26) "Hcg Hpc".
        assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.argfd + 0x42) : mword 64) 2
                        = mword_of_int (KernelSyms.argfd + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp44) in "Hpc".
        (* ---- +0x44: c.sd a5,0(s1) -- *pf = f ---- *)
        assert (Haddrf : add_vec (E1 !!! Regidx (mword_of_int 9 : mword 5))
                           (sign_extend' 64 (mword_of_int 0 : mword 12)) = pf)
          by (rewrite HE1s1; apply addv_sext0).
        iEval (rewrite -Haddrf) in "Hfcell".
        iApply (wp_csd_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x44))
                  (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 0 : mword 12)
                  E1 (av - 6)%nat oldf b
                  with "Hcg Hpc Hi44 Hfcell [-]").
        iIntros (CID27 Hk27) "Hcg Hpc Hfcell".
        iEval (rewrite Haddrf HE1a5') in "Hfcell".
        assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.argfd + 0x44) : mword 64) 2
                        = mword_of_int (KernelSyms.argfd + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp46) in "Hpc".
        iDestruct (word_pointsto_join4 _ _ _ _ Hal5 with "Hs5lo Hs5hi") as "Hs5".
        assert (HE1sp : E1 !!! Regidx csp_rs1 = pa_stk sp0 6)
          by (rewrite /E1 upd_ne; [exact HC5sp | vm_compute; discriminate]).
        assert (HE1a0 : E1 !!! Regidx (mword_of_int 10 : mword 5) = (zero_reg : mword 64))
          by (rewrite /E1 upd_eq; reflexivity).
        assert (HthrE1 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                  r <> (mword_of_int 8 : mword 5) -> r <> (mword_of_int 9 : mword 5) ->
                  r <> (mword_of_int 18 : mword 5) -> E1 !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          assert (N10 : r <> mword_of_int 10)
            by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /E1 upd_ne; [| congruence]. apply HthrC5; assumption. }
        iApply (af_tail Φ m E1 av (zero_reg : mword 64) sp0 ra0 s00 s10 s20 _ w6 p b
                  ltac:(lia) eq_refl eq_refl eq_refl eq_refl eq_refl HE1sp HE1a0 HthrE1
                  with "Hcg Htext Hpc Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 [-]").
        iIntros (CID28 Hk28 mf) "[%Hcsf %Hmfa0] Hcg Hpc".
        iDestruct (cpu_own_transport CID16 CID28 n eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
        iSpecialize ("Hcont" $! CID28 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! mf with "[%] Hcg Hcpu Hpc Hpriv [Hfdcell Hfcell]"); [exact Hcsf|].
        rewrite /argfd_post. iRight. iExists fd, fv. iFrame "Hfdcell Hfcell". iPureIntro.
        split; [exact Hmfa0|].
        unfold arg_fd. rewrite (decide_True _ _ Hrng).
        change (Z.to_nat (bv_signed (trunc32 v))) with fd.
        rewrite Hlk. rewrite (decide_False _ _ Hfvnz). reflexivity.
    - (* ============ OUT OF RANGE: return -1 without calling myproc ============ *)
      iApply (wp_bltu_taken_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x1e))
                (mword_of_int 52 : mword 13) (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5)
                A2 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HA2a5' HA2a4'; apply af_bltu_out; exact Hrng)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi1e [-]").
      iNext. iIntros (CID14 Hk14) "Hcg Hpc".
      assert (Hbt2 : add_vec (mword_of_int (KernelSyms.argfd + 0x1e) : mword 64)
                       (sign_extend' 64 (mword_of_int 52 : mword 13))
                     = mword_of_int (KernelSyms.argfd + 0x52))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbt2) in "Hpc".
      (* +0x52 c.li a0,-1 *)
      iApply (wp_cli_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x52))
                (mword_of_int 10 : mword 5) (mword_of_int 63 : mword 6)
                (mword_of_int (-1) : mword 64) A2 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi52 [-]").
      iIntros (CID15 Hk15) "Hcg Hpc".
      set (F := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (mword_of_int (-1) : mword 64)]> A2).
      change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (mword_of_int (-1) : mword 64)]> A2) with F.
      assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.argfd + 0x52) : mword 64) 2
                      = mword_of_int (KernelSyms.argfd + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp54) in "Hpc".
      (* +0x54 c.j -0x0e *)
      iApply (wp_cj_s_sconf Φ (mword_of_int (KernelSyms.argfd + 0x54))
                (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0"))) F (av - 6)%nat b
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi54 [-]").
      iIntros (CID16 Hk16). iNext. iIntros "Hcg Hpc".
      assert (Hjt2 : add_vec (mword_of_int (KernelSyms.argfd + 0x54) : mword 64)
                       (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.argfd + 0x46))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjt2) in "Hpc".
      iEval (rewrite Haddrfd) in "Hs5hi".
      iDestruct (word_pointsto_join4 _ _ _ _ Hal5 with "Hs5lo Hs5hi") as "Hs5".
      assert (HFsp : F !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite /F upd_ne; [exact HA2sp | vm_compute; discriminate]).
      assert (HFa0 : F !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int (-1) : mword 64))
        by (rewrite /F upd_eq; reflexivity).
      assert (HthrF : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> (mword_of_int 8 : mword 5) -> r <> (mword_of_int 9 : mword 5) ->
                r <> (mword_of_int 18 : mword 5) -> F !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18.
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /F upd_ne; [| congruence]. apply HthrA2; assumption. }
      iApply (af_tail Φ m F av (mword_of_int (-1) : mword 64) sp0 ra0 s00 s10 s20 _ w6 p b
                ltac:(lia) eq_refl eq_refl eq_refl eq_refl eq_refl HFsp HFa0 HthrF
                with "Hcg Htext Hpc Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 [-]").
      iIntros (CID17 Hk17 mf) "[%Hcsf %Hmfa0] Hcg Hpc".
      iDestruct (cpu_own_transport CID11 CID17 n eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iSpecialize ("Hcont" $! CID17 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "[%] Hcg Hcpu Hpc Hpriv [Hfdcell Hfcell]"); [exact Hcsf|].
      rewrite /argfd_post. iLeft. iFrame "Hfdcell Hfcell". iPureIntro.
      split; [exact Hmfa0|].
      unfold arg_fd. rewrite (decide_False _ _ Hrng). reflexivity.
  Qed.

End ProofArgfd.

End ArgfdProof.
