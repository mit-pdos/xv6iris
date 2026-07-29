(* ProofPiperead.v -- the whole-function WP for xv6's piperead().

     int piperead(struct pipe *pi, uint64 addr, int n)
     {
       int i;  char ch;
       struct proc *pr = myproc();
       acquire(&pi->lock);
       while(pi->nread == pi->nwrite && pi->writeopen){
         if(killed(pr)){ release(&pi->lock); return -1; }
         sleep(&pi->nread, &pi->lock);
       }
       for(i = 0; i < n; i++){
         if(pi->nread == pi->nwrite) break;
         ch = pi->data[pi->nread++ % PIPESIZE];
         if(copyout(pr->pagetable, addr + i, &ch, 1) == -1) break;
       }
       wakeup(&pi->nwrite);
       release(&pi->lock);
       return i;
     }

   Ninety instructions; the contract is SpecPiperead.v, the decode layer
   WpPipereadDecode.v.  TWO loops of DIFFERENT kinds:

   - the WAIT loop (+0x34) is unbounded (it sleeps), so it is an iLöb over a
     loop lemma whose back edge is the [beq]-TAKEN leaf at +0x52 (which hands
     its step's later out).  Its state is just "locked + pipe_res + the
     register pins": nothing accumulates, so the IH needs no extra ∀.
   - the COPY loop (+0x84) is BOUNDED by [n], so it is FUEL induction on the
     remaining count -- no Löb (packaged leaves strip the step's later, so a
     ▷-guarded IH could never be applied).

   FOUR iAssert'ed continuations, in the order they are built: [EPI] (+0xd6,
   the epilogue, parameterised over the returned value and the arriving map),
   [M1ARM] (+0x66, the killed/-1 arm) and [CPHASE] (+0x76, the copy phase --
   offered to the wait loop as ONE conjunction [M1ARM ∧ CPHASE] since exactly
   one is taken and both need the whole frame), and inside CPHASE the
   five-entry [WEXIT] join at +0xc2 (wakeup; release; restore s6..s8).

   The pipe stays REASSEMBLED at every loop head and is destructed inside a
   body -- one destruct per wait-loop half, one per copy-loop iteration.  The
   copy loop keeps its cells destructed ACROSS copyout (copyout does not touch
   the pipe, so they simply frame), which is what lets the [nread++] store
   re-use the very disequality the [beq] at +0x8c refuted.               *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.algebra Require Import frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvExec RiscvFetchExec.
Require Import RegFile.
Require Import InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn StackBytes CalleeSaved.
Require Import RiscvTryStep.
Require Import ExecCommon WpGpr.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import IntrDefs WpSmodeIntr.
Require Import WpLock WpMycpu ProcGeom CpuOwn KernelRvcDecode.
Require Import KallocInv.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FdSlots FileInv ProcInv.
Require Import PipeInv.
Require Import SchedCtx.
Require Import SpecMyproc SpecAcquire SpecKilled SpecWakeup SpecSleep SpecCopyout SpecRelease.
Require Import WpPipereadDecode.
Require Import SpecPiperead.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  Pure bitvector / arithmetic facts.                                    *)
(* ===================================================================== *)

Lemma pr_addv_comm (a b : mword 64) : add_vec a b = add_vec b a.
Proof. apply bv_eq. rewrite !add_vec64_unsigned. f_equal. ring. Qed.

Lemma pr_pa_add0 (a : mword 64) : pa_add a 0%nat = a.
Proof. unfold pa_add. change (Z.of_nat 0%nat) with 0%Z. apply avi0. Qed.

Lemma pr_sext24 : sign_extend' 64 (mword_of_int 24 : mword 12) = (mword_of_int 24 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* the byte address the [andi]/[c.add]/[lbu 24] triple lands on: element [k]
   of [pi->data].  Composed through [pa_add_add] so no symbolic base ever
   reaches [vm_compute]. *)
Lemma pr_dataddr (p : mword 64) (k : nat) :
  add_vec (add_vec (mword_of_int (Z.of_nat k) : mword 64) p)
          (sign_extend' 64 (mword_of_int 24 : mword 12))
  = pa_add p (pipe_data_off + k)%nat.
Proof.
  rewrite pr_sext24.
  rewrite (pr_addv_comm (mword_of_int (Z.of_nat k) : mword 64) p).
  change (add_vec p (mword_of_int (Z.of_nat k))) with (pa_add p k).
  change (add_vec (pa_add p k) (mword_of_int 24)) with (pa_add (pa_add p k) 24%nat).
  rewrite pa_add_add. unfold pipe_data_off. rewrite (Nat.add_comm 24%nat k). reflexivity.
Qed.

(* a 64-bit word is the literal of its own unsigned reading *)
Lemma pr_moi_unsigned (x : mword 64) : (mword_of_int (bv_unsigned x) : mword 64) = x.
Proof.
  apply bv_eq. rewrite moi64_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* %PIPESIZE: the [andi rd,rs,511] result is BELOW 512 -- which is all the
   proof needs (the contents are existential, so WHICH byte is irrelevant).
   No sign analysis of the counter is required. *)
Lemma pr_and511_bound (x : mword 64) :
  (0 <= bv_unsigned (and_vec x (sign_extend' 64 (mword_of_int 511 : mword 12))) < 512)%Z.
Proof.
  rewrite and_vec64_unsigned.
  assert (H511 : bv_unsigned (sign_extend' 64 (mword_of_int 511 : mword 12) : mword 64) = 511%Z)
    by (vm_compute; reflexivity).
  rewrite H511.
  replace 511%Z with (Z.ones 9) by (vm_compute; reflexivity).
  rewrite Z.land_ones; [| lia].
  change (2 ^ 9)%Z with 512%Z.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma pr_to_nat_lt (z : Z) : (0 <= z < 512)%Z -> (Z.to_nat z < 512)%nat.
Proof. intro H. lia. Qed.

(* ---- literal / comparison bridges ---- *)

Lemma pr_moi_nz (z : Z) : (0 < z < 18446744073709551616)%Z ->
  neq_vec (mword_of_int z : mword 64) zero_reg = true.
Proof.
  intro Hz. unfold neq_vec. rewrite negb_true_iff. apply eq_vec_false_iff.
  intro Hc. apply (f_equal bv_unsigned) in Hc.
  rewrite moi64_unsigned in Hc.
  assert (Hzz : bv_unsigned (zero_reg : mword 64) = 0%Z) by (vm_compute; reflexivity).
  rewrite Hzz in Hc.
  assert (Hb : bv_wrap 64 z = z) by (apply bvw64_small; change (2^64)%Z with 18446744073709551616%Z; lia).
  rewrite Hb in Hc. lia.
Qed.

Lemma pr_moi0_z : neq_vec (mword_of_int 0 : mword 64) zero_reg = false.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_moi_neq (a b : Z) :
  (0 <= a < 18446744073709551616)%Z -> (0 <= b < 18446744073709551616)%Z -> a <> b ->
  neq_vec (mword_of_int a : mword 64) (mword_of_int b : mword 64) = true.
Proof.
  intros Ha Hb Hne. unfold neq_vec. rewrite negb_true_iff. apply eq_vec_false_iff.
  intro Hc. apply (f_equal bv_unsigned) in Hc.
  rewrite !moi64_unsigned in Hc.
  assert (Ha' : bv_wrap 64 a = a) by (apply bvw64_small; change (2^64)%Z with 18446744073709551616%Z; lia).
  assert (Hb' : bv_wrap 64 b = b) by (apply bvw64_small; change (2^64)%Z with 18446744073709551616%Z; lia).
  rewrite Ha' Hb' in Hc. contradiction.
Qed.

Lemma pr_moi_eqself (a : Z) :
  neq_vec (mword_of_int a : mword 64) (mword_of_int a : mword 64) = false.
Proof. unfold neq_vec. rewrite negb_false_iff. apply eq_vec_true_iff. reflexivity. Qed.

(* the [beq] on two sign-extended [lw]s refutes equality of the CELLS *)
Lemma pr_sext_neq (x y : mword 32) :
  eq_vec (sign_extend' 64 x) (sign_extend' 64 y) = false -> y <> x.
Proof.
  intros H Hc. subst.
  assert (Ht : eq_vec (sign_extend' 64 x : mword 64) (sign_extend' 64 x) = true)
    by (apply eq_vec_true_iff; reflexivity).
  rewrite Ht in H. discriminate.
Qed.

(* [sint] of a 64-bit literal, at BOTH signs (KstackArith's version is
   non-negative only, and [n] may be negative here). *)
Lemma pr_swrap_wrap (z : Z) : bv_swrap 64 (bv_wrap 64 z) = bv_swrap 64 z.
Proof. apply bv_swrap_wrap. Qed.

Lemma pr_sint_moi (z : Z) : (-9223372036854775808 <= z < 9223372036854775808)%Z ->
  sint (mword_of_int z : mword 64) = z.
Proof.
  intro Hz.
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  rewrite moi64_unsigned pr_swrap_wrap.
  apply bv_swrap_small.
  assert (Hhm : bv_half_modulus 64 = 9223372036854775808%Z) by (vm_compute; reflexivity).
  rewrite Hhm. lia.
Qed.

(* ---- the [c.addiw rd,rd,1] increments ---- *)

(* the loop counter [i]: [s3] stays the literal [i] *)
Lemma pr_addiw1_moi (z : Z) : (0 <= z)%Z -> (z + 1 < 2147483648)%Z ->
  sign_extend' 64 (subrange_vec_dec
     (add_vec (mword_of_int z : mword 64)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)
  = (mword_of_int (z + 1) : mword 64).
Proof.
  intros Hz0 Hb.
  rewrite <- trunc32_subrange.
  rewrite trunc32_add trunc32_mword_of_int.
  assert (HK : trunc32 (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
               = (mword_of_int 1 : mword 32))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite HK.
  assert (Hsum : add_vec (mword_of_int z : mword 32) (mword_of_int 1 : mword 32)
                 = (mword_of_int (z + 1) : mword 32)).
  { apply bv_eq.
    unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned.
    rewrite (moi32_small z ltac:(change (2^32)%Z with 4294967296%Z; lia)).
    rewrite (moi32_small 1 ltac:(change (2^32)%Z with 4294967296%Z; lia)).
    rewrite moi32_unsigned.
    rewrite (bvw32_small (z+1) ltac:(change (2^32)%Z with 4294967296%Z; lia)).
    reflexivity. }
  rewrite Hsum.
  apply bv_eq. rewrite (sext64_moi32_unsigned (z+1) ltac:(change (2^31)%Z with 2147483648%Z; lia)).
  rewrite moi64_unsigned. symmetry.
  apply bvw64_small. change (2^64)%Z with 18446744073709551616%Z. lia.
Qed.

(* [pi->nread++]: the [addiw]/[sw] round trip commits [nr + 1] at width 32 *)
Lemma pr_sw_nread (nr : mword 32) :
  trunc32 (sign_extend' 64 (subrange_vec_dec
     (add_vec (sign_extend' 64 nr)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
  = add_vec nr (mword_of_int 1 : mword 32).
Proof.
  rewrite <- trunc32_subrange.
  rewrite trunc32_sext.
  rewrite trunc32_add trunc32_sext.
  assert (HK : trunc32 (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
               = (mword_of_int 1 : mword 32))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite HK. reflexivity.
Qed.

(* ---- the return-value range ---- *)
Lemma pr_ret_neg1 (z : Z) : pipe_rw_ret z (mword_of_int (-1) : mword 64).
Proof. left. reflexivity. Qed.

Lemma pr_ret_cnt (z i : Z) : (0 <= i <= Z.max 0 z)%Z ->
  pipe_rw_ret z (mword_of_int i : mword 64).
Proof. intro H. right. exists i. split; [reflexivity | exact H]. Qed.

(* the two level bounds every callee wants *)
Lemma pr_lvl0 : (Z.of_nat 0%nat + 1 < 2 ^ 31)%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma pr_lvl1 : (Z.of_nat 1%nat + 1 < 2 ^ 31)%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma pr_len1_64 : (Z.of_nat 1%nat < 2 ^ 64)%Z.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  The one leaf WpSconfBtype does not have: a 4-byte [bnez rs1] (BNE      *)
(*  against x0).  x0 is not in the register file, so this is the           *)
(*  x0-specialised twin of [wp_bne_{fall,taken}_s_sconf], exactly as       *)
(*  [wp_beqz_x0_*] is of [wp_beq_*].  Kept here (rather than added to      *)
(*  WpSconfBtype.v) because piperead's +0xea is its only consumer so far.  *)
(* ===================================================================== *)

Local Definition prvv (r : mword 5) (s : mstate) : mword 64 :=
  if Z.eqb (uint r) 0 then zero_reg
  else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s.(sregs).

Local Lemma pr_exec_cmp_BNE (rs2 rs1 : mword 5) s :
  exec (Defs.bind (rX_bits (Regidx rs1))
          (fun w2 => Defs.bind (rX_bits (Regidx rs2))
             (fun w3 => returnM (neq_vec w2 w3)))) s
    = Some (neq_vec (prvv rs1 s) (prvv rs2 s), s).
Proof.
  unfold prvv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  apply exec_returnM.
Qed.

Local Lemma pr_exec_BNE_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
  neq_vec (prvv rs1 s) (prvv rs2 s) = false ->
  exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))) s = Some (RETIRE_SUCCESS, s).
Proof.
  intro Hfall. unfold execute. cbn match. unfold execute_BTYPE.
  rewrite (exec_bind_Some _ _ _ _ _ (pr_exec_cmp_BNE rs2 rs1 s)).
  rewrite Hfall. apply exec_returnM.
Qed.

Local Lemma pr_exec_BNE_taken (imm : mword 13) (rs2 rs1 : mword 5) s :
  neq_vec (prvv rs1 s) (prvv rs2 s) = true ->
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))) s
    = Some (RETIRE_SUCCESS,
            set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
Proof.
  intros Ht Hal Hz. unfold execute. cbn match. unfold execute_BTYPE.
  rewrite (exec_bind_Some _ _ _ _ _ (pr_exec_cmp_BNE rs2 rs1 s)).
  rewrite Ht.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  exact (exec_jump_to_zca _ s Hal Hz).
Qed.

Section PrLeaves.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_pr_bnez_x0_fall (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5) (m : regfile) (n : nat) :
    uint rs1 <> 0 ->
    neq_vec (m !!! Regidx rs1) zero_reg = false ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc false (BTYPE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, BNE)) -∗
    ( sie_cap_gpr γ m n -∗ pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hcmp) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf γ m n Φ pc false
              (BTYPE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, BNE))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfile") as "[Hrac Hfb]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb" with "Hrac") as "Hfile".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply pr_exec_BNE_fall. unfold prvv. rewrite Lva.
      replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" with "Hcg [$Hpc' $Hnpc]").
  Qed.

  Lemma wp_pr_bnez_x0_taken (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5) (m : regfile) (n : nat) :
    uint rs1 <> 0 ->
    neq_vec (m !!! Regidx rs1) zero_reg = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc false (BTYPE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, BNE)) -∗
    ( ▷ ( sie_cap_gpr γ m n -∗ pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hcmp Hal0) "Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf γ m n Φ pc false
              (BTYPE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, BNE))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "[#Hhw Hsc2]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfile") as "[Hrac Hfb]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfb" with "Hrac") as "Hfile".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : neq_vec (prvv rs1 s_pc) (prvv (mword_of_int 0 : mword 5) s_pc) = true).
      { unfold prvv. rewrite Lva.
        replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact Hcmp. }
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (pr_exec_BNE_taken imm (mword_of_int 0 : mword 5) rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
                     (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
                   = add_vec pc (sign_extend' 64 imm))
      by (rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hsc2] Hcap Hfile") as "Hcg".
    iApply ("Hcont" with "Hcg [$Hpc' $Hnpc]").
  Qed.

  (* copyin/copyout's one-byte buffer, in and out of the [seq 0 1] big-sep *)
  Lemma pr_buf1_intro (a : mword 64) (b : bv 8) :
    a ↦ₘ b ⊢ [∗ list] j ∈ seq 0 1, (pa_add a j) ↦ₘ b.
  Proof.
    iIntros "H". cbn [seq]. rewrite big_sepL_singleton pr_pa_add0. iExact "H".
  Qed.

  Lemma pr_buf1_elim (a : mword 64) (b : bv 8) :
    ([∗ list] j ∈ seq 0 1, (pa_add a j) ↦ₘ b) ⊢ a ↦ₘ b.
  Proof.
    iIntros "H". cbn [seq] in *. rewrite big_sepL_singleton pr_pa_add0. iExact "H".
  Qed.

  (* borrow one byte of [pi->data] and give it back *)
  Lemma pr_data_acc (p : mword 64) (bs : list (bv 8)) (k : nat) (b : bv 8) :
    bs !! k = Some b ->
    pipe_data p bs ⊢ (pa_add p (pipe_data_off + k)%nat ↦ₘ b) ∗
                     ((pa_add p (pipe_data_off + k)%nat ↦ₘ b) -∗ pipe_data p bs).
  Proof.
    intro Hk. rewrite /pipe_data. iIntros "H".
    iDestruct (big_sepL_lookup_acc
                 (fun j c => ((pa_add p (pipe_data_off + j)%nat) ↦ₘ c)%I) bs k b Hk
                 with "H") as "[Hb Hcl]".
    iFrame "Hb". iIntros "Hb". iApply "Hcl". iExact "Hb".
  Qed.

End PrLeaves.

(* ===================================================================== *)
Module PipereadProof (Myproc : MYPROC) (AcquireGen : ACQUIRE_GEN)
                     (Killed : KILLED) (Wakeup : WAKEUP) (SleepGen : SLEEP_GEN)
                     (Copyout : COPYOUT) (ReleaseGen : RELEASE_GEN) : PIPEREAD.

Section ProofPiperead.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !pipeG Σ, !kallocG Σ}.
  Context `{CID : CpuId}.

  (* register disequality guard (perf rule): [unify] settles convertibility
     cheaply, so [discriminate] only ever runs on a genuine miss. *)
  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.
  Local Ltac nz := vm_compute; discriminate.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).
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

  Lemma wp_piperead_sconf (γ : gname) (γa : gname) (γf : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γlp : gname)
      (γl : gname) (γp : pipe_names) (w : bool) (q : Qp)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (n : Z)
    : wp_piperead_sconf_body γ γa γf Φ γs j γlp γl γp w q m av eb C pid V n.
  Proof.
    cbv beta delta [wp_piperead_sconf_body].
    intros pcE pj pi ret_tgt Htp Hj Hjl Hlen Ha2 Hnrng Hav.
    unfold piperead_stack in Hav.
    assert (Hn31 : (-2147483648 <= n < 2147483648)%Z)
      by (change (2 ^ 31)%Z with 2147483648%Z in Hnrng; lia).
    assert (Hsn : sint (mword_of_int n : mword 64) = n)
      by (apply pr_sint_moi; lia).
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    pose (vra := (m !!! Regidx Rra : mword 64)).
    pose (vs0 := (m !!! Regidx Rs0 : mword 64)).
    pose (vs1 := (m !!! Regidx Rs1 : mword 64)).
    pose (vs2 := (m !!! Regidx Rs2 : mword 64)).
    pose (vs3 := (m !!! Regidx Rs3 : mword 64)).
    pose (vs4 := (m !!! Regidx Rs4 : mword 64)).
    pose (vs5 := (m !!! Regidx Rs5 : mword 64)).
    pose (vs6 := (m !!! Regidx Rs6 : mword 64)).
    pose (vs7 := (m !!! Regidx Rs7 : mword 64)).
    pose (vs8 := (m !!! Regidx Rs8 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))).
    set (s0v := add_vec spr (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8)))).
    set (chaddr := add_vec s0v (sign_extend' 64 (mword_of_int 4015 : mword 12))).
    assert (Hcpune : eq_vec (zero_reg : mword 64) (mycpu_ret cid_word) = false)
      by (apply mycpu_ret_nonzero; apply tp_ok_cid).
    iIntros "Hcg Hown #Htext Hpc #Hpipe Href Hpriv #Henv #Hpinv #Hpanic Hctx Hsched Hcont".
    iDestruct (is_pipe_valid with "Hpipe") as %Hpv.
    iPoseProof (is_pipe_openable with "Hpipe") as "#Hopen".
    (* =================== PROLOGUE: the 12-slot frame =================== *)
    iPoseProof (pri_00 with "Htext") as "Hi00".
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 12).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf γ Φ pcE (mword_of_int 58 : mword 6) m av 12
              ltac:(lia) Hpush with "Hcg Hpc Hi00 [-]").
    iIntros "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (P0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))))]> m) with P0.
    assert (HcspP0 : P0 !!! Regidx csp_rs1 = spr) by (rewrite /P0 upd_eq; reflexivity).
    assert (Hspr12 : pa_stk sp0 12 = spr).
    { rewrite /spr. unfold pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (PR + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    (* the twelve frame-slot address bridges *)
    assert (Hb1 : pa_stk sp0 1 = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))).
    { rewrite /spr. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2 = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))).
    { rewrite /spr. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3 = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))).
    { rewrite /spr. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : pa_stk sp0 4 = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))).
    { rewrite /spr. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : pa_stk sp0 5 = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))).
    { rewrite /spr. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : pa_stk sp0 6 = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))).
    { rewrite /spr. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : pa_stk sp0 7 = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))).
    { rewrite /spr. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : pa_stk sp0 8 = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))).
    { rewrite /spr. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb9 : pa_stk sp0 9 = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spr. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb10 : pa_stk sp0 10 = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spr. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* the [ch] byte: s0-81 is byte 7 of the frame slot at sp+8 = [pa_stk sp0 11] *)
    assert (Hchaddr : chaddr = pa_add (pa_stk sp0 11) 7%nat).
    { rewrite /chaddr /s0v /spr. unfold pa_add, pa_stk, add_vec_int.
      rewrite !add_vec_off2. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & _)".
    iDestruct "Q1" as (u1) "Hf1". iDestruct "Q2" as (u2) "Hf2".
    iDestruct "Q3" as (u3) "Hf3". iDestruct "Q4" as (u4) "Hf4".
    iDestruct "Q5" as (u5) "Hf5". iDestruct "Q6" as (u6) "Hf6".
    iDestruct "Q7" as (u7) "Hf7".
    (* ---- 0x02..0x0e: save ra,s0..s5 ---- *)
    iPoseProof (pri_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PR + 0x02)) (mword_of_int 11 : mword 6) Rra
              P0 (av - 12)%nat u1 with "Hcg Hpc Hi02 [Hf1] [-]").
    { iEval (rewrite HcspP0 -Hb1). iExact "Hf1". }
    iIntros "Hcg Hpc Hf1".
    assert (HraP0 : P0 !!! Regidx Rra = vra) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HcspP0 -Hb1 HraP0) in "Hf1".
    assert (Hpc04 : add_vec_int (mword_of_int (PR + 0x02) : mword 64) 2 = mword_of_int (PR + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    iPoseProof (pri_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PR + 0x04)) (mword_of_int 10 : mword 6) Rs0
              P0 (av - 12)%nat u2 with "Hcg Hpc Hi04 [Hf2] [-]").
    { iEval (rewrite HcspP0 -Hb2). iExact "Hf2". }
    iIntros "Hcg Hpc Hf2".
    assert (Hs0P0 : P0 !!! Regidx Rs0 = vs0) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HcspP0 -Hb2 Hs0P0) in "Hf2".
    assert (Hpc06 : add_vec_int (mword_of_int (PR + 0x04) : mword 64) 2 = mword_of_int (PR + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    iPoseProof (pri_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PR + 0x06)) (mword_of_int 9 : mword 6) Rs1
              P0 (av - 12)%nat u3 with "Hcg Hpc Hi06 [Hf3] [-]").
    { iEval (rewrite HcspP0 -Hb3). iExact "Hf3". }
    iIntros "Hcg Hpc Hf3".
    assert (Hs1P0 : P0 !!! Regidx Rs1 = vs1) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HcspP0 -Hb3 Hs1P0) in "Hf3".
    assert (Hpc08 : add_vec_int (mword_of_int (PR + 0x06) : mword 64) 2 = mword_of_int (PR + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    iPoseProof (pri_08 with "Htext") as "Hi08".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PR + 0x08)) (mword_of_int 8 : mword 6) Rs2
              P0 (av - 12)%nat u4 with "Hcg Hpc Hi08 [Hf4] [-]").
    { iEval (rewrite HcspP0 -Hb4). iExact "Hf4". }
    iIntros "Hcg Hpc Hf4".
    assert (Hs2P0 : P0 !!! Regidx Rs2 = vs2) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HcspP0 -Hb4 Hs2P0) in "Hf4".
    assert (Hpc0a : add_vec_int (mword_of_int (PR + 0x08) : mword 64) 2 = mword_of_int (PR + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    iPoseProof (pri_0a with "Htext") as "Hi0a".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PR + 0x0a)) (mword_of_int 7 : mword 6) Rs3
              P0 (av - 12)%nat u5 with "Hcg Hpc Hi0a [Hf5] [-]").
    { iEval (rewrite HcspP0 -Hb5). iExact "Hf5". }
    iIntros "Hcg Hpc Hf5".
    assert (Hs3P0 : P0 !!! Regidx Rs3 = vs3) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HcspP0 -Hb5 Hs3P0) in "Hf5".
    assert (Hpc0c : add_vec_int (mword_of_int (PR + 0x0a) : mword 64) 2 = mword_of_int (PR + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    iPoseProof (pri_0c with "Htext") as "Hi0c".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PR + 0x0c)) (mword_of_int 6 : mword 6) Rs4
              P0 (av - 12)%nat u6 with "Hcg Hpc Hi0c [Hf6] [-]").
    { iEval (rewrite HcspP0 -Hb6). iExact "Hf6". }
    iIntros "Hcg Hpc Hf6".
    assert (Hs4P0 : P0 !!! Regidx Rs4 = vs4) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HcspP0 -Hb6 Hs4P0) in "Hf6".
    assert (Hpc0e : add_vec_int (mword_of_int (PR + 0x0c) : mword 64) 2 = mword_of_int (PR + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    iPoseProof (pri_0e with "Htext") as "Hi0e".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PR + 0x0e)) (mword_of_int 5 : mword 6) Rs5
              P0 (av - 12)%nat u7 with "Hcg Hpc Hi0e [Hf7] [-]").
    { iEval (rewrite HcspP0 -Hb7). iExact "Hf7". }
    iIntros "Hcg Hpc Hf7".
    assert (Hs5P0 : P0 !!! Regidx Rs5 = vs5) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HcspP0 -Hb7 Hs5P0) in "Hf7".
    assert (Hpc10 : add_vec_int (mword_of_int (PR + 0x0e) : mword 64) 2 = mword_of_int (PR + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* ================= EPI: the epilogue at +0xd6 ================= *)
    pose (EPIP := ((∀ (M : regfile) (P' : uptd) (rv : mword 64),
               ⌜ M !!! Regidx csp_rs1 = spr
                 /\ M !!! Regidx Rs3 = rv
                 /\ M !!! Regidx Rtp = cid_word
                 /\ M !!! Regidx Rs6 = vs6
                 /\ M !!! Regidx Rs7 = vs7
                 /\ M !!! Regidx Rs8 = vs8
                 /\ M !!! Regidx Rs9 = m !!! Regidx Rs9
                 /\ M !!! Regidx Rs10 = m !!! Regidx Rs10
                 /\ M !!! Regidx Rs11 = m !!! Regidx Rs11 ⌝ -∗
               ⌜ uptd_ext (pv_upt V) P' ⌝ -∗
               ⌜ pipe_rw_ret n rv ⌝ -∗
               sie_cap_gpr γ M (av - 12)%nat -∗
               pc_is (mword_of_int (PR + 0xd6) : mword 64) -∗
               cpu_own γ 0%nat eb pj C -∗
               pipe_ref γp w q -∗
               proc_priv γf pj pid (upd_upt V P') -∗
               own_ctx (p_context pj) -∗
               ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj -∗
               pa_stk sp0 1 ↦₈ vra -∗ pa_stk sp0 2 ↦₈ vs0 -∗ pa_stk sp0 3 ↦₈ vs1 -∗
               pa_stk sp0 4 ↦₈ vs2 -∗ pa_stk sp0 5 ↦₈ vs3 -∗ pa_stk sp0 6 ↦₈ vs4 -∗
               pa_stk sp0 7 ↦₈ vs5 -∗
               (∃ z : mword 64, pa_stk sp0 8 ↦₈ z) -∗
               (∃ z : mword 64, pa_stk sp0 9 ↦₈ z) -∗
               (∃ z : mword 64, pa_stk sp0 10 ↦₈ z) -∗
               (∃ z : mword 64, pa_stk sp0 11 ↦₈ z) -∗
               (∃ z : mword 64, pa_stk sp0 12 ↦₈ z) -∗
               WP (Loop : expr riscv_lang) {{ Φ }})%I : iProp Σ)).
    iAssert EPIP with "[Hcont]" as "EPI".
    { rewrite /EPIP.
      iIntros (M P' rv) "%Hrg %Hext %Hret Hcg Hpc Hown Href Hpriv Hctx Hsched Hg1 Hg2 Hg3 Hg4 Hg5 Hg6 Hg7 Hg8 Hg9 Hg10 Hg11 Hg12".
      destruct Hrg as (Hcsp & Hrv & HMtp & HMs6 & HMs7 & HMs8 & HMs9 & HMs10 & HMs11).
      (* 0xd6 c.mv a0,s3 *)
      iPoseProof (pri_d6 with "Htext") as "Hid6".
      iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PR + 0xd6)) Ra0 Rs3
                M (av - 12)%nat ltac:(nz) ltac:(nz) with "Hcg Hpc Hid6 [-]").
      iIntros "Hcg Hpc".
      set (F0 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs3))]> M).
      change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs3))]> M) with F0.
      assert (Hppd8 : add_vec_int (mword_of_int (PR + 0xd6) : mword 64) 2 = mword_of_int (PR + 0xd8))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppd8) in "Hpc".
      assert (HF0csp : F0 !!! Regidx csp_rs1 = spr) by (rewrite /F0 upd_ne; [exact Hcsp | reg_neq]).
      (* 0xd8 c.ldsp ra,88(sp) *)
      iPoseProof (pri_d8 with "Htext") as "Hid8".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PR + 0xd8)) (mword_of_int 11 : mword 6) Rra
                F0 (av - 12)%nat vra ltac:(nz) ltac:(nz) with "Hcg Hpc Hid8 [Hg1] [-]").
      { iEval (rewrite HF0csp -Hb1). iExact "Hg1". }
      iIntros "Hcg Hpc Hg1". iEval (rewrite HF0csp -Hb1) in "Hg1".
      set (F1 := <[Regidx Rra := regval_into_reg vra]> F0).
      change (<[Regidx Rra := regval_into_reg vra]> F0) with F1.
      assert (Hppda : add_vec_int (mword_of_int (PR + 0xd8) : mword 64) 2 = mword_of_int (PR + 0xda))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppda) in "Hpc".
      assert (HF1csp : F1 !!! Regidx csp_rs1 = spr) by (rewrite /F1 upd_ne; [exact HF0csp | reg_neq]).
      (* 0xda c.ldsp s0,80(sp) *)
      iPoseProof (pri_da with "Htext") as "Hida".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PR + 0xda)) (mword_of_int 10 : mword 6) Rs0
                F1 (av - 12)%nat vs0 ltac:(nz) ltac:(nz) with "Hcg Hpc Hida [Hg2] [-]").
      { iEval (rewrite HF1csp -Hb2). iExact "Hg2". }
      iIntros "Hcg Hpc Hg2". iEval (rewrite HF1csp -Hb2) in "Hg2".
      set (F2 := <[Regidx Rs0 := regval_into_reg vs0]> F1).
      change (<[Regidx Rs0 := regval_into_reg vs0]> F1) with F2.
      assert (Hppdc : add_vec_int (mword_of_int (PR + 0xda) : mword 64) 2 = mword_of_int (PR + 0xdc))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppdc) in "Hpc".
      assert (HF2csp : F2 !!! Regidx csp_rs1 = spr) by (rewrite /F2 upd_ne; [exact HF1csp | reg_neq]).
      (* 0xdc c.ldsp s1,72(sp) *)
      iPoseProof (pri_dc with "Htext") as "Hidc".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PR + 0xdc)) (mword_of_int 9 : mword 6) Rs1
                F2 (av - 12)%nat vs1 ltac:(nz) ltac:(nz) with "Hcg Hpc Hidc [Hg3] [-]").
      { iEval (rewrite HF2csp -Hb3). iExact "Hg3". }
      iIntros "Hcg Hpc Hg3". iEval (rewrite HF2csp -Hb3) in "Hg3".
      set (F3 := <[Regidx Rs1 := regval_into_reg vs1]> F2).
      change (<[Regidx Rs1 := regval_into_reg vs1]> F2) with F3.
      assert (Hppde : add_vec_int (mword_of_int (PR + 0xdc) : mword 64) 2 = mword_of_int (PR + 0xde))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppde) in "Hpc".
      assert (HF3csp : F3 !!! Regidx csp_rs1 = spr) by (rewrite /F3 upd_ne; [exact HF2csp | reg_neq]).
      (* 0xde c.ldsp s2,64(sp) *)
      iPoseProof (pri_de with "Htext") as "Hide".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PR + 0xde)) (mword_of_int 8 : mword 6) Rs2
                F3 (av - 12)%nat vs2 ltac:(nz) ltac:(nz) with "Hcg Hpc Hide [Hg4] [-]").
      { iEval (rewrite HF3csp -Hb4). iExact "Hg4". }
      iIntros "Hcg Hpc Hg4". iEval (rewrite HF3csp -Hb4) in "Hg4".
      set (F4 := <[Regidx Rs2 := regval_into_reg vs2]> F3).
      change (<[Regidx Rs2 := regval_into_reg vs2]> F3) with F4.
      assert (Hppe0 : add_vec_int (mword_of_int (PR + 0xde) : mword 64) 2 = mword_of_int (PR + 0xe0))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppe0) in "Hpc".
      assert (HF4csp : F4 !!! Regidx csp_rs1 = spr) by (rewrite /F4 upd_ne; [exact HF3csp | reg_neq]).
      (* 0xe0 c.ldsp s3,56(sp) *)
      iPoseProof (pri_e0 with "Htext") as "Hie0".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PR + 0xe0)) (mword_of_int 7 : mword 6) Rs3
                F4 (av - 12)%nat vs3 ltac:(nz) ltac:(nz) with "Hcg Hpc Hie0 [Hg5] [-]").
      { iEval (rewrite HF4csp -Hb5). iExact "Hg5". }
      iIntros "Hcg Hpc Hg5". iEval (rewrite HF4csp -Hb5) in "Hg5".
      set (F5 := <[Regidx Rs3 := regval_into_reg vs3]> F4).
      change (<[Regidx Rs3 := regval_into_reg vs3]> F4) with F5.
      assert (Hppe2 : add_vec_int (mword_of_int (PR + 0xe0) : mword 64) 2 = mword_of_int (PR + 0xe2))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppe2) in "Hpc".
      assert (HF5csp : F5 !!! Regidx csp_rs1 = spr) by (rewrite /F5 upd_ne; [exact HF4csp | reg_neq]).
      (* 0xe2 c.ldsp s4,48(sp) *)
      iPoseProof (pri_e2 with "Htext") as "Hie2".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PR + 0xe2)) (mword_of_int 6 : mword 6) Rs4
                F5 (av - 12)%nat vs4 ltac:(nz) ltac:(nz) with "Hcg Hpc Hie2 [Hg6] [-]").
      { iEval (rewrite HF5csp -Hb6). iExact "Hg6". }
      iIntros "Hcg Hpc Hg6". iEval (rewrite HF5csp -Hb6) in "Hg6".
      set (F6 := <[Regidx Rs4 := regval_into_reg vs4]> F5).
      change (<[Regidx Rs4 := regval_into_reg vs4]> F5) with F6.
      assert (Hppe4 : add_vec_int (mword_of_int (PR + 0xe2) : mword 64) 2 = mword_of_int (PR + 0xe4))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppe4) in "Hpc".
      assert (HF6csp : F6 !!! Regidx csp_rs1 = spr) by (rewrite /F6 upd_ne; [exact HF5csp | reg_neq]).
      (* 0xe4 c.ldsp s5,40(sp) *)
      iPoseProof (pri_e4 with "Htext") as "Hie4".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PR + 0xe4)) (mword_of_int 5 : mword 6) Rs5
                F6 (av - 12)%nat vs5 ltac:(nz) ltac:(nz) with "Hcg Hpc Hie4 [Hg7] [-]").
      { iEval (rewrite HF6csp -Hb7). iExact "Hg7". }
      iIntros "Hcg Hpc Hg7". iEval (rewrite HF6csp -Hb7) in "Hg7".
      set (F7 := <[Regidx Rs5 := regval_into_reg vs5]> F6).
      change (<[Regidx Rs5 := regval_into_reg vs5]> F6) with F7.
      assert (Hppe6 : add_vec_int (mword_of_int (PR + 0xe4) : mword 64) 2 = mword_of_int (PR + 0xe6))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppe6) in "Hpc".
      assert (HF7csp : F7 !!! Regidx csp_rs1 = spr) by (rewrite /F7 upd_ne; [exact HF6csp | reg_neq]).
      (* 0xe6 c.addi16sp sp,96 -- the frame pop *)
      assert (Hsp0up : add_vec spr (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))) = sp0)
        by (rewrite /spr; apply frame_cancel_96).
      assert (Hwv : add_vec (F7 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))) = sp0)
        by (rewrite HF7csp; exact Hsp0up).
      assert (Hpop : F7 !!! Regidx csp_rs1
                     = pa_stk (add_vec (F7 !!! Regidx csp_rs1)
                                 (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))) 12).
      { rewrite Hwv HF7csp. symmetry. exact Hspr12. }
      iAssert (stack_own sp0 12) with "[Hg1 Hg2 Hg3 Hg4 Hg5 Hg6 Hg7 Hg8 Hg9 Hg10 Hg11 Hg12]" as "Hfr12".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hg1"; [by iExists vra|].
        iSplitL "Hg2"; [by iExists vs0|].
        iSplitL "Hg3"; [by iExists vs1|].
        iSplitL "Hg4"; [by iExists vs2|].
        iSplitL "Hg5"; [by iExists vs3|].
        iSplitL "Hg6"; [by iExists vs4|].
        iSplitL "Hg7"; [by iExists vs5|].
        iSplitL "Hg8"; [iExact "Hg8"|].
        iSplitL "Hg9"; [iExact "Hg9"|].
        iSplitL "Hg10"; [iExact "Hg10"|].
        iSplitL "Hg11"; [iExact "Hg11"|].
        iSplitL "Hg12"; [iExact "Hg12"|]. done. }
      iEval (rewrite -Hwv) in "Hfr12".
      iPoseProof (pri_e6 with "Htext") as "Hie6".
      iApply (wp_caddi16sp_pop_s_sconf γ Φ (mword_of_int (PR + 0xe6)) (mword_of_int 6 : mword 6)
                F7 (av - 12)%nat 12 Hpop with "Hcg Hpc Hie6 Hfr12 [-]").
      iIntros "Hcg Hpc".
      assert (Hnk : ((av - 12) + 12)%nat = av) by lia.
      iEval (rewrite Hnk) in "Hcg".
      set (F8 := <[Regidx csp_rs1 := regval_into_reg
          (add_vec (F7 !!! Regidx csp_rs1)
             (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))))]> F7).
      change (<[Regidx csp_rs1 := regval_into_reg
          (add_vec (F7 !!! Regidx csp_rs1)
             (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))))]> F7) with F8.
      assert (Hppe8 : add_vec_int (mword_of_int (PR + 0xe6) : mword 64) 2 = mword_of_int (PR + 0xe8))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppe8) in "Hpc".
      (* the final register facts *)
      assert (HF8ra : F8 !!! Regidx Rra = vra).
      { rewrite /F8 upd_ne; [| reg_neq]. rewrite /F7 upd_ne; [| reg_neq].
        rewrite /F6 upd_ne; [| reg_neq]. rewrite /F5 upd_ne; [| reg_neq].
        rewrite /F4 upd_ne; [| reg_neq]. rewrite /F3 upd_ne; [| reg_neq].
        rewrite /F2 upd_ne; [| reg_neq]. rewrite /F1 upd_eq. reflexivity. }
      assert (HF8a0 : F8 !!! Regidx Ra0 = rv).
      { rewrite /F8 upd_ne; [| reg_neq]. rewrite /F7 upd_ne; [| reg_neq].
        rewrite /F6 upd_ne; [| reg_neq]. rewrite /F5 upd_ne; [| reg_neq].
        rewrite /F4 upd_ne; [| reg_neq]. rewrite /F3 upd_ne; [| reg_neq].
        rewrite /F2 upd_ne; [| reg_neq]. rewrite /F1 upd_ne; [| reg_neq].
        rewrite /F0 upd_eq. unfold regval_into_reg. rewrite Hrv. apply add_vec_zero_l. }
      assert (HF8sp : F8 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
        by (rewrite /F8 upd_eq; unfold regval_into_reg; rewrite Hwv; reflexivity).
      assert (Hthru : forall r : mword 5,
                r <> csp_rs1 -> r <> Rra -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
                r <> Rs3 -> r <> Rs4 -> r <> Rs5 -> r <> Ra0 ->
                F8 !!! Regidx r = M !!! Regidx r).
      { intros r N2 N1 N8 N9 N18 N19 N20 N21 N10.
        rewrite /F8 upd_ne; [| congruence]. rewrite /F7 upd_ne; [| congruence].
        rewrite /F6 upd_ne; [| congruence]. rewrite /F5 upd_ne; [| congruence].
        rewrite /F4 upd_ne; [| congruence]. rewrite /F3 upd_ne; [| congruence].
        rewrite /F2 upd_ne; [| congruence]. rewrite /F1 upd_ne; [| congruence].
        rewrite /F0 upd_ne; [| congruence]. reflexivity. }
      iPoseProof (pri_e8 with "Htext") as "Hie8".
      iApply (wp_cret_s_sconf γ Φ (mword_of_int (PR + 0xe8)) Rra F8 av ltac:(nz)
                with "Hcg Hpc Hie8 [-]").
      iIntros "Hcg Hpc".
      assert (Hrafin : ret_pc (F8 !!! Regidx Rra) = ret_tgt) by (rewrite HF8ra; reflexivity).
      iEval (rewrite Hrafin) in "Hpc".
      iApply ("Hcont" $! F8 P' with "[%] [%] [%] Hcg Hown Hpc Href Hpriv Hctx Hsched").
      { unfold callee_saved. split_and!.
        - exact HF8sp.
        - rewrite (Hthru Rtp ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
          rewrite HMtp. symmetry. exact Htp.
        - rewrite /F8 upd_ne; [| reg_neq]. rewrite /F7 upd_ne; [| reg_neq].
          rewrite /F6 upd_ne; [| reg_neq]. rewrite /F5 upd_ne; [| reg_neq].
          rewrite /F4 upd_ne; [| reg_neq]. rewrite /F3 upd_ne; [| reg_neq].
          rewrite /F2 upd_eq. reflexivity.
        - rewrite /F8 upd_ne; [| reg_neq]. rewrite /F7 upd_ne; [| reg_neq].
          rewrite /F6 upd_ne; [| reg_neq]. rewrite /F5 upd_ne; [| reg_neq].
          rewrite /F4 upd_ne; [| reg_neq]. rewrite /F3 upd_eq. reflexivity.
        - rewrite /F8 upd_ne; [| reg_neq]. rewrite /F7 upd_ne; [| reg_neq].
          rewrite /F6 upd_ne; [| reg_neq]. rewrite /F5 upd_ne; [| reg_neq].
          rewrite /F4 upd_eq. reflexivity.
        - rewrite /F8 upd_ne; [| reg_neq]. rewrite /F7 upd_ne; [| reg_neq].
          rewrite /F6 upd_ne; [| reg_neq]. rewrite /F5 upd_eq. reflexivity.
        - rewrite /F8 upd_ne; [| reg_neq]. rewrite /F7 upd_ne; [| reg_neq].
          rewrite /F6 upd_eq. reflexivity.
        - rewrite /F8 upd_ne; [| reg_neq]. rewrite /F7 upd_eq. reflexivity.
        - rewrite (Hthru Rs6 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
          exact HMs6.
        - rewrite (Hthru Rs7 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
          exact HMs7.
        - rewrite (Hthru Rs8 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
          exact HMs8.
        - rewrite (Hthru Rs9 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
          exact HMs9.
        - rewrite (Hthru Rs10 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
          exact HMs10.
        - rewrite (Hthru Rs11 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
          exact HMs11. }
      { exact Hext. }
      { rewrite HF8a0. exact Hret. } }
    (* ============ 0x10: c.addi4spn s0,sp,96 ============ *)
    iPoseProof (pri_10 with "Htext") as "Hi10".
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (PR + 0x10)) (Cregidx (mword_of_int 0))
              (mword_of_int 24 : mword 8) Rs0 P0 (av - 12)%nat
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
              with "Hcg Hpc Hi10 [-]").
    iIntros "Hcg Hpc".
    set (P1 := <[Regidx Rs0 := regval_into_reg
        (add_vec (P0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))))]> P0).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (P0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))))]> P0) with P1.
    assert (Hpc12 : add_vec_int (mword_of_int (PR + 0x10) : mword 64) 2 = mword_of_int (PR + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    (* ============ 0x12/0x14/0x16: s1:=a0, s2:=a1, s5:=a2 ============ *)
    iPoseProof (pri_12 with "Htext") as "Hi12".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PR + 0x12)) Rs1 Ra0 P1 (av - 12)%nat
              ltac:(nz) ltac:(nz) with "Hcg Hpc Hi12 [-]").
    iIntros "Hcg Hpc".
    set (P2 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (P1 !!! Regidx Ra0))]> P1).
    change (<[Regidx Rs1 := regval_into_reg (add_vec zero_reg (P1 !!! Regidx Ra0))]> P1) with P2.
    assert (Hpc14 : add_vec_int (mword_of_int (PR + 0x12) : mword 64) 2 = mword_of_int (PR + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    iPoseProof (pri_14 with "Htext") as "Hi14".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PR + 0x14)) Rs2 Ra1 P2 (av - 12)%nat
              ltac:(nz) ltac:(nz) with "Hcg Hpc Hi14 [-]").
    iIntros "Hcg Hpc".
    set (P3 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (P2 !!! Regidx Ra1))]> P2).
    change (<[Regidx Rs2 := regval_into_reg (add_vec zero_reg (P2 !!! Regidx Ra1))]> P2) with P3.
    assert (Hpc16 : add_vec_int (mword_of_int (PR + 0x14) : mword 64) 2 = mword_of_int (PR + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    iPoseProof (pri_16 with "Htext") as "Hi16".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PR + 0x16)) Rs5 Ra2 P3 (av - 12)%nat
              ltac:(nz) ltac:(nz) with "Hcg Hpc Hi16 [-]").
    iIntros "Hcg Hpc".
    set (P4 := <[Regidx Rs5 := regval_into_reg (add_vec zero_reg (P3 !!! Regidx Ra2))]> P3).
    change (<[Regidx Rs5 := regval_into_reg (add_vec zero_reg (P3 !!! Regidx Ra2))]> P3) with P4.
    assert (Hpc18 : add_vec_int (mword_of_int (PR + 0x16) : mword 64) 2 = mword_of_int (PR + 0x18))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    (* ============ 0x18: jal ra,myproc ============ *)
    iPoseProof (pri_18 with "Htext") as "Hi18".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (PR + 0x18)) Rra (mword_of_int 2085718 : mword 21)
              P4 (av - 12)%nat ltac:(nz) ltac:(nz) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi18 [-]").
    iIntros "Hcg Hpc".
    set (P5 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (PR + 0x18) : mword 64) 4)]> P4).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (PR + 0x18) : mword 64) 4)]> P4) with P5.
    assert (Hjmp : add_vec (mword_of_int (PR + 0x18) : mword 64)
                     (sign_extend' 64 (mword_of_int 2085718 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    pose (addrv := (m !!! Regidx Ra1 : mword 64)).
    assert (HP5tp : P5 !!! Regidx Rtp = cid_word).
    { rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4 upd_ne; [| reg_neq].
      rewrite /P3 upd_ne; [| reg_neq]. rewrite /P2 upd_ne; [| reg_neq].
      rewrite /P1 upd_ne; [| reg_neq]. rewrite /P0 upd_ne; [| reg_neq]. exact Htp. }
    assert (HP5csp : P5 !!! Regidx csp_rs1 = spr).
    { rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4 upd_ne; [| reg_neq].
      rewrite /P3 upd_ne; [| reg_neq]. rewrite /P2 upd_ne; [| reg_neq].
      rewrite /P1 upd_ne; [| reg_neq]. exact HcspP0. }
    assert (HP5s0 : P5 !!! Regidx Rs0 = s0v).
    { rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4 upd_ne; [| reg_neq].
      rewrite /P3 upd_ne; [| reg_neq]. rewrite /P2 upd_ne; [| reg_neq].
      rewrite /P1 upd_eq. unfold regval_into_reg. rewrite HcspP0. reflexivity. }
    assert (HP5s1 : P5 !!! Regidx Rs1 = pi).
    { rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4 upd_ne; [| reg_neq].
      rewrite /P3 upd_ne; [| reg_neq]. rewrite /P2 upd_eq. unfold regval_into_reg.
      rewrite /P1 upd_ne; [| reg_neq]. rewrite /P0 upd_ne; [| reg_neq].
      apply add_vec_zero_l. }
    assert (HP5s2 : P5 !!! Regidx Rs2 = addrv).
    { rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4 upd_ne; [| reg_neq].
      rewrite /P3 upd_eq. unfold regval_into_reg.
      rewrite /P2 upd_ne; [| reg_neq]. rewrite /P1 upd_ne; [| reg_neq].
      rewrite /P0 upd_ne; [| reg_neq]. apply add_vec_zero_l. }
    assert (HP5s5 : P5 !!! Regidx Rs5 = (mword_of_int n : mword 64)).
    { rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4 upd_eq. unfold regval_into_reg.
      rewrite /P3 upd_ne; [| reg_neq]. rewrite /P2 upd_ne; [| reg_neq].
      rewrite /P1 upd_ne; [| reg_neq]. rewrite /P0 upd_ne; [| reg_neq].
      rewrite add_vec_zero_l. exact Ha2. }
    assert (HP5ra : P5 !!! Regidx Rra = add_vec_int (mword_of_int (PR + 0x18) : mword 64) 4)
      by (rewrite /P5; apply upd_eq).
    assert (HthrP : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs5 ->
              P5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9 N18 N21.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /P5 upd_ne; [| congruence]. rewrite /P4 upd_ne; [| congruence].
      rewrite /P3 upd_ne; [| congruence]. rewrite /P2 upd_ne; [| congruence].
      rewrite /P1 upd_ne; [| congruence]. rewrite /P0 upd_ne; [| congruence]. reflexivity. }
    iApply (Myproc.wp_myproc_sconf γ Φ P5 (av - 12)%nat 0%nat eb pj C
              HP5tp pr_lvl0 ltac:(lia) with "Hcg Hown Htext Hpc [-]").
    iIntros (ms1 A0) "%Hms1 Hcg Hown Hpc %HcsA0d".
    destruct HcsA0d as [HcsA0 HA0a0].
    assert (Hpc1c : ret_pc (P5 !!! Regidx Rra) = (mword_of_int (PR + 0x1c) : mword 64))
      by (rewrite HP5ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    (* ============ 0x1c: s4 := a0 (= pj);  0x1e: a0 := s1 ============ *)
    iPoseProof (pri_1c with "Htext") as "Hi1c".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PR + 0x1c)) Rs4 Ra0 A0 (av - 12)%nat
              ltac:(nz) ltac:(nz) with "Hcg Hpc Hi1c [-]").
    iIntros "Hcg Hpc".
    set (A1 := <[Regidx Rs4 := regval_into_reg (add_vec zero_reg (A0 !!! Regidx Ra0))]> A0).
    change (<[Regidx Rs4 := regval_into_reg (add_vec zero_reg (A0 !!! Regidx Ra0))]> A0) with A1.
    assert (Hpc1e : add_vec_int (mword_of_int (PR + 0x1c) : mword 64) 2 = mword_of_int (PR + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    iPoseProof (pri_1e with "Htext") as "Hi1e".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PR + 0x1e)) Ra0 Rs1 A1 (av - 12)%nat
              ltac:(nz) ltac:(nz) with "Hcg Hpc Hi1e [-]").
    iIntros "Hcg Hpc".
    set (A2 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Rs1))]> A1).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Rs1))]> A1) with A2.
    assert (Hpc20 : add_vec_int (mword_of_int (PR + 0x1e) : mword 64) 2 = mword_of_int (PR + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc20) in "Hpc".
    (* ============ 0x20: jal ra,acquire ============ *)
    iPoseProof (pri_20 with "Htext") as "Hi20".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (PR + 0x20)) Rra (mword_of_int 2082386 : mword 21)
              A2 (av - 12)%nat ltac:(nz) ltac:(nz) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi20 [-]").
    iIntros "Hcg Hpc".
    set (A3 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (PR + 0x20) : mword 64) 4)]> A2).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (PR + 0x20) : mword 64) 4)]> A2) with A3.
    assert (Hjaq : add_vec (mword_of_int (PR + 0x20) : mword 64)
                     (sign_extend' 64 (mword_of_int 2082386 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjaq) in "Hpc".
    assert (HA0s1 : A0 !!! Regidx Rs1 = pi)
      by (rewrite (callee_saved_lookup HcsA0 Rs1 ltac:(vm_compute; reflexivity)); exact HP5s1).
    assert (HA3a0 : A3 !!! Regidx Ra0 = pi).
    { rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_eq. unfold regval_into_reg.
      rewrite /A1 upd_ne; [| reg_neq]. rewrite HA0s1. apply add_vec_zero_l. }
    assert (HA3tp : A3 !!! Regidx Rtp = cid_word).
    { rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_ne; [| reg_neq].
      rewrite (callee_saved_lookup HcsA0 Rtp ltac:(vm_compute; reflexivity)). exact HP5tp. }
    assert (HA3ra : A3 !!! Regidx Rra = add_vec_int (mword_of_int (PR + 0x20) : mword 64) 4)
      by (rewrite /A3; apply upd_eq).
    assert (HA3s4 : A3 !!! Regidx Rs4 = pj).
    { rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_eq. unfold regval_into_reg. rewrite HA0a0. apply add_vec_zero_l. }
    assert (HthrA : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 -> r <> Rs5 ->
              A3 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9 N18 N20 N21.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /A3 upd_ne; [| congruence]. rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsA0 r Hr). apply HthrP; assumption. }
    assert (HA3csp : A3 !!! Regidx csp_rs1 = spr).
    { rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_ne; [| reg_neq].
      rewrite (callee_saved_lookup HcsA0 csp_rs1 ltac:(vm_compute; reflexivity)). exact HP5csp. }
    assert (HA3s0 : A3 !!! Regidx Rs0 = s0v).
    { rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_ne; [| reg_neq].
      rewrite (callee_saved_lookup HcsA0 Rs0 ltac:(vm_compute; reflexivity)). exact HP5s0. }
    assert (HA3s1 : A3 !!! Regidx Rs1 = pi).
    { rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_ne; [| reg_neq]. exact HA0s1. }
    assert (HA3s2 : A3 !!! Regidx Rs2 = addrv).
    { rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_ne; [| reg_neq].
      rewrite (callee_saved_lookup HcsA0 Rs2 ltac:(vm_compute; reflexivity)). exact HP5s2. }
    assert (HA3s5 : A3 !!! Regidx Rs5 = (mword_of_int n : mword 64)).
    { rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_ne; [| reg_neq].
      rewrite (callee_saved_lookup HcsA0 Rs5 ltac:(vm_compute; reflexivity)). exact HP5s5. }
    iApply (AcquireGen.wp_acquire_gen_sconf γ Φ γl (pipe_res γp pi)
              (pipe_ref γp w q) (pipe_dead γl γp) A3 0%nat eb pj C (av - 12)%nat
              HA3tp pr_lvl0 ltac:(lia)
              ltac:(iApply pipe_ref_dead) ltac:(iApply locked_pre_dead)
              with "Hcg Hown Htext Hpc [] Href Hpanic [-]").
    { iEval (rewrite HA3a0). iExact "Hopen". }
    iIntros (ms2 M0) "%Hms2 Href Hcg Hpc %HcsM0 Hlocked Hres Hown Hpay".
    iEval (rewrite HA3ra) in "Hpc".
    assert (Hpc24 : ret_pc (add_vec_int (mword_of_int (PR + 0x20) : mword 64) 4)
                    = (mword_of_int (PR + 0x24) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    (* ============ 0x24/0x28/0x2c ============ *)
    assert (HM0s1 : M0 !!! Regidx Rs1 = pi)
      by (rewrite (callee_saved_lookup HcsM0 Rs1 ltac:(vm_compute; reflexivity)); exact HA3s1).
    iDestruct "Hres" as (nr0 nw0 ro0 wo0 vnm0 bs0)
      "(Hnm & Hnr & Hnw & Hro & Hwo & Hst0 & Hst1 & %Hcnt0 & %Hlen0 & Hdat & Hslack)".
    assert (Hnra0 : add_vec (M0 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 536 : mword 12)) = a_pnread pi)
      by (rewrite HM0s1; reflexivity).
    iPoseProof (pri_24 with "Htext") as "Hi24".
    iApply (wp_lw_s_sconf γ Φ (mword_of_int (PR + 0x24)) Ra4 Rs1 (mword_of_int 536 : mword 12)
              M0 (av - 12)%nat nr0 ltac:(nz) ltac:(nz) with "Hcg Hpc Hi24 [Hnr] [-]").
    { iEval (rewrite Hnra0). iExact "Hnr". }
    iIntros "Hcg Hpc Hnr". iEval (rewrite Hnra0) in "Hnr".
    set (W1 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 nr0)]> M0).
    change (<[Regidx Ra4 := regval_into_reg (sign_extend' 64 nr0)]> M0) with W1.
    assert (Hpc28 : add_vec_int (mword_of_int (PR + 0x24) : mword 64) 4 = mword_of_int (PR + 0x28))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    assert (HW1s1 : W1 !!! Regidx Rs1 = pi) by (rewrite /W1 upd_ne; [exact HM0s1 | reg_neq]).
    assert (Hnwa1 : add_vec (W1 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 540 : mword 12)) = a_pnwrite pi)
      by (rewrite HW1s1; reflexivity).
    iPoseProof (pri_28 with "Htext") as "Hi28".
    iApply (wp_lw_s_sconf γ Φ (mword_of_int (PR + 0x28)) Ra5 Rs1 (mword_of_int 540 : mword 12)
              W1 (av - 12)%nat nw0 ltac:(nz) ltac:(nz) with "Hcg Hpc Hi28 [Hnw] [-]").
    { iEval (rewrite Hnwa1). iExact "Hnw". }
    iIntros "Hcg Hpc Hnw". iEval (rewrite Hnwa1) in "Hnw".
    set (W2 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 nw0)]> W1).
    change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 nw0)]> W1) with W2.
    assert (Hpc2c : add_vec_int (mword_of_int (PR + 0x28) : mword 64) 4 = mword_of_int (PR + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2c) in "Hpc".
    iPoseProof (pri_2c with "Htext") as "Hi2c".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (PR + 0x2c)) Rs3 Rs1 (mword_of_int 536 : mword 12)
              W2 (av - 12)%nat ltac:(nz) ltac:(nz) with "Hcg Hpc Hi2c [-]").
    iIntros "Hcg Hpc".
    set (W0 := <[Regidx Rs3 := regval_into_reg
        (add_vec (W2 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 536 : mword 12)))]> W2).
    change (<[Regidx Rs3 := regval_into_reg
        (add_vec (W2 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 536 : mword 12)))]> W2) with W0.
    assert (Hpc30 : add_vec_int (mword_of_int (PR + 0x2c) : mword 64) 4 = mword_of_int (PR + 0x30))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc30) in "Hpc".
    (* the register pins at the wait-loop base map [W0] *)
    assert (HW2s1 : W2 !!! Regidx Rs1 = pi) by (rewrite /W2 upd_ne; [exact HW1s1 | reg_neq]).
    assert (HW0s3 : W0 !!! Regidx Rs3 = a_pnread pi).
    { rewrite /W0 upd_eq. unfold regval_into_reg. rewrite HW2s1. reflexivity. }
    assert (HW0s1 : W0 !!! Regidx Rs1 = pi) by (rewrite /W0 upd_ne; [exact HW2s1 | reg_neq]).
    assert (HW0a4 : W0 !!! Regidx Ra4 = sign_extend' 64 nr0).
    { rewrite /W0 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_eq. reflexivity. }
    assert (HW0a5 : W0 !!! Regidx Ra5 = sign_extend' 64 nw0).
    { rewrite /W0 upd_ne; [| reg_neq]. rewrite /W2 upd_eq. reflexivity. }
    assert (HthrW : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 -> r <> Rs5 ->
              W0 !!! Regidx r = m !!! Regidx r).
    { intros r Hr N2 N8 N9 N18 N19 N20 N21.
      assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /W0 upd_ne; [| congruence]. rewrite /W2 upd_ne; [| congruence].
      rewrite /W1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsM0 r Hr). apply HthrA; assumption. }
    assert (HW0csp : W0 !!! Regidx csp_rs1 = spr).
    { rewrite /W0 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [| reg_neq].
      rewrite (callee_saved_lookup HcsM0 csp_rs1 ltac:(vm_compute; reflexivity)). exact HA3csp. }
    assert (HW0s0 : W0 !!! Regidx Rs0 = s0v).
    { rewrite /W0 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [| reg_neq].
      rewrite (callee_saved_lookup HcsM0 Rs0 ltac:(vm_compute; reflexivity)). exact HA3s0. }
    assert (HW0s2 : W0 !!! Regidx Rs2 = addrv).
    { rewrite /W0 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [| reg_neq].
      rewrite (callee_saved_lookup HcsM0 Rs2 ltac:(vm_compute; reflexivity)). exact HA3s2. }
    assert (HW0s4 : W0 !!! Regidx Rs4 = pj).
    { rewrite /W0 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [| reg_neq].
      rewrite (callee_saved_lookup HcsM0 Rs4 ltac:(vm_compute; reflexivity)). exact HA3s4. }
    assert (HW0s5 : W0 !!! Regidx Rs5 = (mword_of_int n : mword 64)).
    { rewrite /W0 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [| reg_neq].
      rewrite (callee_saved_lookup HcsM0 Rs5 ltac:(vm_compute; reflexivity)). exact HA3s5. }
    assert (HW0tp : W0 !!! Regidx Rtp = cid_word).
    { rewrite (HthrW Rtp ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)
                 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
      exact Htp. }
    assert (HW0s6 : W0 !!! Regidx Rs6 = vs6)
      by (rewrite (HthrW Rs6 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); reflexivity).
    assert (HW0s7 : W0 !!! Regidx Rs7 = vs7)
      by (rewrite (HthrW Rs7 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); reflexivity).
    assert (HW0s8 : W0 !!! Regidx Rs8 = vs8)
      by (rewrite (HthrW Rs8 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); reflexivity).
    assert (HW0s9 : W0 !!! Regidx Rs9 = m !!! Regidx Rs9)
      by (apply HthrW; first [vm_compute; reflexivity | reg_neq]).
    assert (HW0s10 : W0 !!! Regidx Rs10 = m !!! Regidx Rs10)
      by (apply HthrW; first [vm_compute; reflexivity | reg_neq]).
    assert (HW0s11 : W0 !!! Regidx Rs11 = m !!! Regidx Rs11)
      by (apply HthrW; first [vm_compute; reflexivity | reg_neq]).
    (* ================================================================= *)
    (* CPHASE (+0x76): the copy phase, offered to the wait loop together  *)
    (* with EPI as a CONJUNCTION -- exactly one is taken, so they share    *)
    (* the frame slots and the caller's continuation.                     *)
    (* ================================================================= *)
    pose (CPP := ((∀ M : regfile,
        ⌜ M !!! Regidx csp_rs1 = spr
          /\ M !!! Regidx Rs0 = s0v
          /\ M !!! Regidx Rs1 = pi
          /\ M !!! Regidx Rs2 = addrv
          /\ M !!! Regidx Rs4 = pj
          /\ M !!! Regidx Rs5 = (mword_of_int n : mword 64)
          /\ M !!! Regidx Rtp = cid_word
          /\ M !!! Regidx Rs9 = m !!! Regidx Rs9
          /\ M !!! Regidx Rs10 = m !!! Regidx Rs10
          /\ M !!! Regidx Rs11 = m !!! Regidx Rs11 ⌝ -∗
        sie_cap_gpr γ M (av - 12)%nat -∗
        pc_is (mword_of_int (PR + 0x76) : mword 64) -∗
        cpu_own γ 1%nat eb pj C -∗
        trap_csrs_pay 0 eb -∗
        locked γl cpu_id -∗
        pipe_res γp pi -∗
        pipe_ref γp w q -∗
        proc_priv γf pj pid V -∗
        own_ctx (p_context pj) -∗
        ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj -∗
        pa_stk sp0 8 ↦₈ vs6 -∗
        pa_stk sp0 9 ↦₈ vs7 -∗
        pa_stk sp0 10 ↦₈ vs8 -∗
        (∃ z : mword 64, pa_stk sp0 11 ↦₈ z) -∗
        (∃ z : mword 64, pa_stk sp0 12 ↦₈ z) -∗
        WP (Loop : expr riscv_lang) {{ Φ }})%I : iProp Σ)).
    pose (EPIC := ((∀ (M : regfile) (P' : uptd) (rv : mword 64),
               ⌜ M !!! Regidx csp_rs1 = spr
                 /\ M !!! Regidx Rs3 = rv
                 /\ M !!! Regidx Rtp = cid_word
                 /\ M !!! Regidx Rs6 = vs6
                 /\ M !!! Regidx Rs7 = vs7
                 /\ M !!! Regidx Rs8 = vs8
                 /\ M !!! Regidx Rs9 = m !!! Regidx Rs9
                 /\ M !!! Regidx Rs10 = m !!! Regidx Rs10
                 /\ M !!! Regidx Rs11 = m !!! Regidx Rs11 ⌝ -∗
               ⌜ uptd_ext (pv_upt V) P' ⌝ -∗
               ⌜ pipe_rw_ret n rv ⌝ -∗
               sie_cap_gpr γ M (av - 12)%nat -∗
               pc_is (mword_of_int (PR + 0xd6) : mword 64) -∗
               cpu_own γ 0%nat eb pj C -∗
               pipe_ref γp w q -∗
               proc_priv γf pj pid (upd_upt V P') -∗
               own_ctx (p_context pj) -∗
               ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj -∗
               (∃ z : mword 64, pa_stk sp0 8 ↦₈ z) -∗
               (∃ z : mword 64, pa_stk sp0 9 ↦₈ z) -∗
               (∃ z : mword 64, pa_stk sp0 10 ↦₈ z) -∗
               (∃ z : mword 64, pa_stk sp0 11 ↦₈ z) -∗
               (∃ z : mword 64, pa_stk sp0 12 ↦₈ z) -∗
               WP (Loop : expr riscv_lang) {{ Φ }})%I : iProp Σ)).
    iAssert ((EPIC ∧ CPP)%I) with "[EPI Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7]" as "EXITS".
    { iSplit.
      { rewrite /EPIC. iEval (rewrite /EPIP) in "EPI".
        iIntros (M P' rv) "%Hrg %Hext %Hret Hcg Hpc Hown Href Hpriv Hctx Hsched Hz8 Hz9 Hz10 Hz11 Hz12".
        iApply ("EPI" $! M P' rv with "[%] [%] [%] Hcg Hpc Hown Href Hpriv Hctx Hsched
                  Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hz8 Hz9 Hz10 Hz11 Hz12").
        { exact Hrg. }
        { exact Hext. }
        { exact Hret. } }
      rewrite /CPP.
      iIntros (M) "%Hrg Hcg Hpc Hown Hpay Hlocked Hres Href Hpriv Hctx Hsched Hc8 Hc9 Hc10 Hq11 Hq12".
      destruct Hrg as (HMcsp & HMs0 & HMs1 & HMs2 & HMs4 & HMs5 & HMtp & HMs9 & HMs10 & HMs11).
      (* ---- 0x76 c.li s3,0 ---- *)
      iPoseProof (pri_76 with "Htext") as "Hi76".
      iApply (wp_cli_s_sconf γ Φ (mword_of_int (PR + 0x76)) Rs3 (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) M (av - 12)%nat ltac:(nz) ltac:(nz)
                ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi76 [-]").
      iIntros "Hcg Hpc".
      set (G0 := <[Regidx Rs3 := regval_into_reg (mword_of_int 0 : mword 64)]> M).
      change (<[Regidx Rs3 := regval_into_reg (mword_of_int 0 : mword 64)]> M) with G0.
      assert (Hp78 : add_vec_int (mword_of_int (PR + 0x76) : mword 64) 2 = mword_of_int (PR + 0x78))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp78) in "Hpc".
      assert (HG0s0 : G0 !!! Regidx Rs0 = s0v) by (rewrite /G0 upd_ne; [exact HMs0 | reg_neq]).
      (* ---- 0x78 addi s8,s0,-81 : s8 := &ch ---- *)
      iPoseProof (pri_78 with "Htext") as "Hi78".
      iApply (wp_addi4_s_sconf γ Φ (mword_of_int (PR + 0x78)) Rs8 Rs0 (mword_of_int 4015 : mword 12)
                G0 (av - 12)%nat ltac:(nz) ltac:(nz) with "Hcg Hpc Hi78 [-]").
      iIntros "Hcg Hpc".
      iEval (rewrite HG0s0) in "Hcg".
      set (G1 := <[Regidx Rs8 := regval_into_reg chaddr]> G0).
      change (<[Regidx Rs8 := regval_into_reg
          (add_vec s0v (sign_extend' 64 (mword_of_int 4015 : mword 12)))]> G0) with G1.
      assert (Hp7c : add_vec_int (mword_of_int (PR + 0x78) : mword 64) 4 = mword_of_int (PR + 0x7c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp7c) in "Hpc".
      (* ---- 0x7c c.li s7,1 ; 0x7e c.li s6,-1 ---- *)
      iPoseProof (pri_7c with "Htext") as "Hi7c".
      iApply (wp_cli_s_sconf γ Φ (mword_of_int (PR + 0x7c)) Rs7 (mword_of_int 1 : mword 6)
                (mword_of_int 1 : mword 64) G1 (av - 12)%nat ltac:(nz) ltac:(nz)
                ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi7c [-]").
      iIntros "Hcg Hpc".
      set (G2 := <[Regidx Rs7 := regval_into_reg (mword_of_int 1 : mword 64)]> G1).
      change (<[Regidx Rs7 := regval_into_reg (mword_of_int 1 : mword 64)]> G1) with G2.
      assert (Hp7e : add_vec_int (mword_of_int (PR + 0x7c) : mword 64) 2 = mword_of_int (PR + 0x7e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp7e) in "Hpc".
      iPoseProof (pri_7e with "Htext") as "Hi7e".
      iApply (wp_cli_s_sconf γ Φ (mword_of_int (PR + 0x7e)) Rs6 (mword_of_int 63 : mword 6)
                (mword_of_int (-1) : mword 64) G2 (av - 12)%nat ltac:(nz) ltac:(nz)
                ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi7e [-]").
      iIntros "Hcg Hpc".
      set (G3 := <[Regidx Rs6 := regval_into_reg (mword_of_int (-1) : mword 64)]> G2).
      change (<[Regidx Rs6 := regval_into_reg (mword_of_int (-1) : mword 64)]> G2) with G3.
      assert (Hp80 : add_vec_int (mword_of_int (PR + 0x7e) : mword 64) 2 = mword_of_int (PR + 0x80))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp80) in "Hpc".
      (* the register pins at [G3] *)
      assert (HG3s6 : G3 !!! Regidx Rs6 = (mword_of_int (-1) : mword 64))
        by (rewrite /G3; apply upd_eq).
      assert (HG3s7 : G3 !!! Regidx Rs7 = (mword_of_int 1 : mword 64)).
      { rewrite /G3 upd_ne; [| reg_neq]. rewrite /G2 upd_eq. reflexivity. }
      assert (HG3s8 : G3 !!! Regidx Rs8 = chaddr).
      { rewrite /G3 upd_ne; [| reg_neq]. rewrite /G2 upd_ne; [| reg_neq].
        rewrite /G1 upd_eq. reflexivity. }
      assert (HG3s3 : G3 !!! Regidx Rs3 = (mword_of_int 0 : mword 64)).
      { rewrite /G3 upd_ne; [| reg_neq]. rewrite /G2 upd_ne; [| reg_neq].
        rewrite /G1 upd_ne; [| reg_neq]. rewrite /G0 upd_eq. reflexivity. }
      assert (HthrG : forall r : mword 5, r <> Rs3 -> r <> Rs6 -> r <> Rs7 -> r <> Rs8 ->
                G3 !!! Regidx r = M !!! Regidx r).
      { intros r N19 N22 N23 N24.
        rewrite /G3 upd_ne; [| congruence]. rewrite /G2 upd_ne; [| congruence].
        rewrite /G1 upd_ne; [| congruence]. rewrite /G0 upd_ne; [| congruence]. reflexivity. }
      assert (HG3csp : G3 !!! Regidx csp_rs1 = spr)
        by (rewrite (HthrG csp_rs1 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HMcsp).
      assert (HG3s0 : G3 !!! Regidx Rs0 = s0v)
        by (rewrite (HthrG Rs0 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HMs0).
      assert (HG3s1 : G3 !!! Regidx Rs1 = pi)
        by (rewrite (HthrG Rs1 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HMs1).
      assert (HG3s2 : G3 !!! Regidx Rs2 = addrv)
        by (rewrite (HthrG Rs2 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HMs2).
      assert (HG3s4 : G3 !!! Regidx Rs4 = pj)
        by (rewrite (HthrG Rs4 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HMs4).
      assert (HG3s5 : G3 !!! Regidx Rs5 = (mword_of_int n : mword 64))
        by (rewrite (HthrG Rs5 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HMs5).
      assert (HG3tp : G3 !!! Regidx Rtp = cid_word)
        by (rewrite (HthrG Rtp ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HMtp).
      assert (HG3s9 : G3 !!! Regidx Rs9 = m !!! Regidx Rs9)
        by (rewrite (HthrG Rs9 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HMs9).
      assert (HG3s10 : G3 !!! Regidx Rs10 = m !!! Regidx Rs10)
        by (rewrite (HthrG Rs10 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HMs10).
      assert (HG3s11 : G3 !!! Regidx Rs11 = m !!! Regidx Rs11)
        by (rewrite (HthrG Rs11 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HMs11).
      (* ---- carve the [ch] byte out of the frame slot at sp+8 ---- *)
      iDestruct "Hq11" as (w11) "Hc11".
      iDestruct (slot_bytes_own with "Hc11") as "[%Hal11 Hby11]".
      iDestruct (bytes_own_acc (DfracOwn 1) (pa_stk sp0 11) 8 7 ltac:(lia) with "Hby11")
        as "[Hchb Hchback]".
      iDestruct "Hchb" as (chb0) "Hch".
      iEval (rewrite -Hchaddr) in "Hch".
      (* ---- the process block, borrowed once for the whole copy phase ---- *)
      iDestruct (proc_priv_sz_bound with "Hpriv") as %Hszb.
      iDestruct (proc_priv_copy with "Hpriv") as "(Hszc & Hptc & Hpt & Hpback)".
      (* ================= WEXIT: the five-entry join at +0xc2 ============= *)
      pose (WXP := ((∀ (M2 : regfile) (P' : uptd) (rv : mword 64),
          ⌜ M2 !!! Regidx csp_rs1 = spr
            /\ M2 !!! Regidx Rs1 = pi
            /\ M2 !!! Regidx Rs3 = rv
            /\ M2 !!! Regidx Rtp = cid_word
            /\ M2 !!! Regidx Rs9 = m !!! Regidx Rs9
            /\ M2 !!! Regidx Rs10 = m !!! Regidx Rs10
            /\ M2 !!! Regidx Rs11 = m !!! Regidx Rs11 ⌝ -∗
          ⌜ uptd_ext (pv_upt V) P' ⌝ -∗
          ⌜ pipe_rw_ret n rv ⌝ -∗
          sie_cap_gpr γ M2 (av - 12)%nat -∗
          pc_is (mword_of_int (PR + 0xc2) : mword 64) -∗
          cpu_own γ 1%nat eb pj C -∗
          trap_csrs_pay 0 eb -∗
          locked γl cpu_id -∗
          pipe_res γp pi -∗
          pipe_ref γp w q -∗
          proc_priv γf pj pid (upd_upt V P') -∗
          own_ctx (p_context pj) -∗
          ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj -∗
          (∃ b : bv 8, chaddr ↦ₘ b) -∗
          WP (Loop : expr riscv_lang) {{ Φ }})%I : iProp Σ)).
      iAssert WXP with "[EPI Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hc8 Hc9 Hc10 Hq12 Hchback]" as "HWX".
      { rewrite /WXP. iEval (rewrite /EPIP) in "EPI".
        iIntros (M2 P' rv) "%Hxg %Hxext %Hxret Hcg Hpc Hown Hpay Hlocked Hres Href Hpriv Hctx Hsched Hchx".
        destruct Hxg as (HXcsp & HXs1 & HXs3 & HXtp & HXs9 & HXs10 & HXs11).
        (* 0xc2 addi a0,s1,540 *)
        iPoseProof (pri_c2 with "Htext") as "Hic2".
        iApply (wp_addi4_s_sconf γ Φ (mword_of_int (PR + 0xc2)) Ra0 Rs1 (mword_of_int 540 : mword 12)
                  M2 (av - 12)%nat ltac:(nz) ltac:(nz) with "Hcg Hpc Hic2 [-]").
        iIntros "Hcg Hpc".
        set (X1 := <[Regidx Ra0 := regval_into_reg
            (add_vec (M2 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 540 : mword 12)))]> M2).
        change (<[Regidx Ra0 := regval_into_reg
            (add_vec (M2 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 540 : mword 12)))]> M2) with X1.
        assert (Hpc6 : add_vec_int (mword_of_int (PR + 0xc2) : mword 64) 4 = mword_of_int (PR + 0xc6))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc6) in "Hpc".
        (* 0xc6 jal wakeup *)
        iPoseProof (pri_c6 with "Htext") as "Hic6".
        iApply (wp_jal_s_sconf γ Φ (mword_of_int (PR + 0xc6)) Rra (mword_of_int 2087158 : mword 21)
                  X1 (av - 12)%nat ltac:(nz) ltac:(nz) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hic6 [-]").
        iIntros "Hcg Hpc".
        set (X2 := <[Regidx Rra := regval_into_reg
            (add_vec_int (mword_of_int (PR + 0xc6) : mword 64) 4)]> X1).
        change (<[Regidx Rra := regval_into_reg
            (add_vec_int (mword_of_int (PR + 0xc6) : mword 64) 4)]> X1) with X2.
        assert (Hjwk : add_vec (mword_of_int (PR + 0xc6) : mword 64)
                         (sign_extend' 64 (mword_of_int 2087158 : mword 21)) = mword_of_int KernelSyms.wakeup)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjwk) in "Hpc".
        assert (HX2tp : X2 !!! Regidx Rtp = cid_word).
        { rewrite /X2 upd_ne; [| reg_neq]. rewrite /X1 upd_ne; [| reg_neq]. exact HXtp. }
        assert (HX2ra : X2 !!! Regidx Rra = add_vec_int (mword_of_int (PR + 0xc6) : mword 64) 4)
          by (rewrite /X2; apply upd_eq).
        assert (HwK : (18 <= av - 12)%nat) by lia.
        assert (HwdomX : forall r : regidx, r ∈ dom (rf_to_gmap X2)) by (intro r; apply rf_to_gmap_dom).
        assert (Hwa0f : mycpu_ret (X2 !!! Regidx Rtp) = mycpu_ret cid_word)
          by (rewrite HX2tp; reflexivity).
        assert (Hwnz : eq_vec (zero_reg : mword 64) (mycpu_ret (X2 !!! Regidx Rtp)) = false)
          by (rewrite HX2tp; exact Hcpune).
        iApply (Wakeup.wp_wakeup_sconf γ Φ X2 γs (mycpu_ret cid_word) pj 1%nat (av - 12)%nat eb C
                  HwK HwdomX Hlen HX2tp Hwa0f Hwnz pr_lvl1
                  with "Hcg Hown Htext Hpc Hpanic Hpinv [-]").
        iIntros (Mw) "[%Hwcs %Hwdom] Hcg Hown Htext2 Hpc".
        iEval (rewrite HX2ra) in "Hpc".
        assert (Hpca : ret_pc (add_vec_int (mword_of_int (PR + 0xc6) : mword 64) 4)
                       = (mword_of_int (PR + 0xca) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpca) in "Hpc".
        assert (HthrW2 : forall r : mword 5, is_cs_idx r = true -> Mw !!! Regidx r = M2 !!! Regidx r).
        { intros r Hr.
          assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite (callee_saved_lookup Hwcs r Hr).
          rewrite /X2 upd_ne; [| congruence]. rewrite /X1 upd_ne; [| congruence]. reflexivity. }
        assert (HMws1 : Mw !!! Regidx Rs1 = pi)
          by (rewrite (HthrW2 Rs1 ltac:(vm_compute; reflexivity)); exact HXs1).
        (* 0xca c.mv a0,s1 *)
        iPoseProof (pri_ca with "Htext") as "Hica".
        iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PR + 0xca)) Ra0 Rs1 Mw (av - 12)%nat
                  ltac:(nz) ltac:(nz) with "Hcg Hpc Hica [-]").
        iIntros "Hcg Hpc".
        set (X3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mw !!! Regidx Rs1))]> Mw).
        change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mw !!! Regidx Rs1))]> Mw) with X3.
        assert (Hpcc : add_vec_int (mword_of_int (PR + 0xca) : mword 64) 2 = mword_of_int (PR + 0xcc))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpcc) in "Hpc".
        (* 0xcc jal release *)
        iPoseProof (pri_cc with "Htext") as "Hicc".
        iApply (wp_jal_s_sconf γ Φ (mword_of_int (PR + 0xcc)) Rra (mword_of_int 2082350 : mword 21)
                  X3 (av - 12)%nat ltac:(nz) ltac:(nz) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hicc [-]").
        iIntros "Hcg Hpc".
        set (X4 := <[Regidx Rra := regval_into_reg
            (add_vec_int (mword_of_int (PR + 0xcc) : mword 64) 4)]> X3).
        change (<[Regidx Rra := regval_into_reg
            (add_vec_int (mword_of_int (PR + 0xcc) : mword 64) 4)]> X3) with X4.
        assert (Hjrl : add_vec (mword_of_int (PR + 0xcc) : mword 64)
                         (sign_extend' 64 (mword_of_int 2082350 : mword 21)) = mword_of_int KernelSyms.release)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjrl) in "Hpc".
        assert (HX4a0 : X4 !!! Regidx Ra0 = pi).
        { rewrite /X4 upd_ne; [| reg_neq]. rewrite /X3 upd_eq. unfold regval_into_reg.
          rewrite HMws1. apply add_vec_zero_l. }
        assert (HX4tp : X4 !!! Regidx Rtp = cid_word).
        { rewrite /X4 upd_ne; [| reg_neq]. rewrite /X3 upd_ne; [| reg_neq].
          rewrite (HthrW2 Rtp ltac:(vm_compute; reflexivity)). exact HXtp. }
        assert (HX4ra : X4 !!! Regidx Rra = add_vec_int (mword_of_int (PR + 0xcc) : mword 64) 4)
          by (rewrite /X4; apply upd_eq).
        assert (HX4lka : add_vec (X4 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pi).
        { rewrite HX4a0.
          replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
            by (apply bv_eq; vm_compute; reflexivity).
          apply kv_addv_zero. }
        iApply (ReleaseGen.wp_release_gen_sconf γ Φ γl pi (pipe_res γp pi) (pipe_dead γl γp) emp%I
                  X4 0%nat eb pj C (av - 12)%nat HX4lka HX4tp ltac:(lia)
                  ltac:(iApply locked_dead) ltac:(iApply locked_pre_dead)
                  with "Hcg Htext Hpc Hopen Hlocked Hres [] Hown Hpay [-]").
        { iApply lock_finisher_close. }
        iIntros (mrx) "_ Hcg Hpc %Hcsrx Hown".
        iEval (rewrite HX4ra) in "Hpc".
        assert (Hpd0 : ret_pc (add_vec_int (mword_of_int (PR + 0xcc) : mword 64) 4)
                       = (mword_of_int (PR + 0xd0) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpd0) in "Hpc".
        assert (HthrX : forall r : mword 5, is_cs_idx r = true -> mrx !!! Regidx r = M2 !!! Regidx r).
        { intros r Hr.
          assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite (callee_saved_lookup Hcsrx r Hr).
          rewrite /X4 upd_ne; [| congruence]. rewrite /X3 upd_ne; [| congruence].
          apply HthrW2; exact Hr. }
        assert (Hmrxcsp : mrx !!! Regidx csp_rs1 = spr)
          by (rewrite (HthrX csp_rs1 ltac:(vm_compute; reflexivity)); exact HXcsp).
        (* 0xd0/0xd2/0xd4: reload s6, s7, s8 *)
        iPoseProof (pri_d0 with "Htext") as "Hid0".
        iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PR + 0xd0)) (mword_of_int 4 : mword 6) Rs6
                  mrx (av - 12)%nat vs6 ltac:(nz) ltac:(nz) with "Hcg Hpc Hid0 [Hc8] [-]").
        { iEval (rewrite Hmrxcsp -Hb8). iExact "Hc8". }
        iIntros "Hcg Hpc Hc8". iEval (rewrite Hmrxcsp -Hb8) in "Hc8".
        set (X5 := <[Regidx Rs6 := regval_into_reg vs6]> mrx).
        change (<[Regidx Rs6 := regval_into_reg vs6]> mrx) with X5.
        assert (Hpd2 : add_vec_int (mword_of_int (PR + 0xd0) : mword 64) 2 = mword_of_int (PR + 0xd2))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpd2) in "Hpc".
        assert (HX5csp : X5 !!! Regidx csp_rs1 = spr)
          by (rewrite /X5 upd_ne; [exact Hmrxcsp | reg_neq]).
        iPoseProof (pri_d2 with "Htext") as "Hid2".
        iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PR + 0xd2)) (mword_of_int 3 : mword 6) Rs7
                  X5 (av - 12)%nat vs7 ltac:(nz) ltac:(nz) with "Hcg Hpc Hid2 [Hc9] [-]").
        { iEval (rewrite HX5csp -Hb9). iExact "Hc9". }
        iIntros "Hcg Hpc Hc9". iEval (rewrite HX5csp -Hb9) in "Hc9".
        set (X6 := <[Regidx Rs7 := regval_into_reg vs7]> X5).
        change (<[Regidx Rs7 := regval_into_reg vs7]> X5) with X6.
        assert (Hpd4 : add_vec_int (mword_of_int (PR + 0xd2) : mword 64) 2 = mword_of_int (PR + 0xd4))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpd4) in "Hpc".
        assert (HX6csp : X6 !!! Regidx csp_rs1 = spr)
          by (rewrite /X6 upd_ne; [exact HX5csp | reg_neq]).
        iPoseProof (pri_d4 with "Htext") as "Hid4".
        iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PR + 0xd4)) (mword_of_int 2 : mword 6) Rs8
                  X6 (av - 12)%nat vs8 ltac:(nz) ltac:(nz) with "Hcg Hpc Hid4 [Hc10] [-]").
        { iEval (rewrite HX6csp -Hb10). iExact "Hc10". }
        iIntros "Hcg Hpc Hc10". iEval (rewrite HX6csp -Hb10) in "Hc10".
        set (X7 := <[Regidx Rs8 := regval_into_reg vs8]> X6).
        change (<[Regidx Rs8 := regval_into_reg vs8]> X6) with X7.
        assert (Hpd6 : add_vec_int (mword_of_int (PR + 0xd4) : mword 64) 2 = mword_of_int (PR + 0xd6))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpd6) in "Hpc".
        (* rebuild the frame slot the [ch] byte was carved out of *)
        iDestruct "Hchx" as (chbf) "Hchf".
        iEval (rewrite Hchaddr) in "Hchf".
        iDestruct ("Hchback" $! chbf with "Hchf") as "Hby11".
        iDestruct (bytes_own_slot (pa_stk sp0 11) Hal11 with "Hby11") as (w11f) "Hc11".
        assert (HthrX7 : forall r : mword 5, is_cs_idx r = true ->
                  r <> Rs6 -> r <> Rs7 -> r <> Rs8 -> X7 !!! Regidx r = M2 !!! Regidx r).
        { intros r Hr N22 N23 N24.
          rewrite /X7 upd_ne; [| congruence]. rewrite /X6 upd_ne; [| congruence].
          rewrite /X5 upd_ne; [| congruence]. apply HthrX; exact Hr. }
        iApply ("EPI" $! X7 P' rv with "[%] [%] [%] Hcg Hpc Hown Href Hpriv Hctx Hsched
                  Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 [Hc8] [Hc9] [Hc10] [Hc11] Hq12").
        { split_and!.
          - rewrite (HthrX7 csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
            exact HXcsp.
          - rewrite (HthrX7 Rs3 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
            exact HXs3.
          - rewrite (HthrX7 Rtp ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
            exact HXtp.
          - rewrite /X7 upd_ne; [| reg_neq]. rewrite /X6 upd_ne; [| reg_neq].
            rewrite /X5 upd_eq. reflexivity.
          - rewrite /X7 upd_ne; [| reg_neq]. rewrite /X6 upd_eq. reflexivity.
          - rewrite /X7 upd_eq. reflexivity.
          - rewrite (HthrX7 Rs9 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
            exact HXs9.
          - rewrite (HthrX7 Rs10 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
            exact HXs10.
          - rewrite (HthrX7 Rs11 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
            exact HXs11. }
        { exact Hxext. }
        { exact Hxret. }
        { by iExists vs6. }
        { by iExists vs7. }
        { by iExists vs8. }
        { by iExists w11f. } }
      (* ---- 0x80 blez s5 ---- *)
      assert (Hsz : sint (zero_reg : mword 64) = 0%Z) by (vm_compute; reflexivity).
      assert (Hblez : zopz0zKzJ_s (zero_reg : mword 64) (G3 !!! Regidx Rs5) = Z.geb 0 n).
      { rewrite HG3s5. unfold zopz0zKzJ_s. rewrite Hsn Hsz. reflexivity. }
      iPoseProof (pri_80 with "Htext") as "Hi80".
      destruct (Z.geb 0 n) eqn:Hbz.
      { (* n <= 0: nothing to copy, return 0 *)
        iApply (wp_bge_x0_taken_s_sconf γ Φ (mword_of_int (PR + 0x80)) (mword_of_int 66 : mword 13)
                  Rs5 G3 (av - 12)%nat ltac:(nz) ltac:(exact Hblez)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi80 [-]").
        iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Hjbz : add_vec (mword_of_int (PR + 0x80) : mword 64)
                         (sign_extend' 64 (mword_of_int 66 : mword 13)) = mword_of_int (PR + 0xc2))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjbz) in "Hpc".
        iAssert (⌜uptd_ext_sz (pv_sz V) (pv_upt V) (pv_upt V)⌝)%I as "#Hxr"; [iPureIntro; apply uptd_ext_sz_refl|].
        iDestruct ("Hpback" $! (pv_upt V) with "Hxr Hszc Hptc Hpt") as "Hpriv".
        iAssert (∃ b : bv 8, chaddr ↦ₘ b)%I with "[Hch]" as "Hchx"; [by iExists chb0|].
        iEval (rewrite /WXP) in "HWX".
        iApply ("HWX" $! G3 (pv_upt V) (mword_of_int 0 : mword 64)
                  with "[%] [%] [%] Hcg Hpc Hown Hpay Hlocked Hres Href Hpriv Hctx Hsched Hchx").
        { split_and!; try assumption. }
        { apply uptd_ext_refl. }
        { apply pr_ret_cnt. split; [lia | apply Z.le_max_l]. } }
      (* ---- n > 0: run the bounded copy loop ---- *)
      assert (Hnpos : (0 < n)%Z).
      { rewrite Z.geb_leb in Hbz. apply Z.leb_gt in Hbz. lia. }
      pose (Nn := Z.to_nat n).
      assert (HNn : Z.of_nat Nn = n) by (rewrite /Nn; apply Z2Nat.id; lia).
      iApply (wp_bge_x0_fall_s_sconf γ Φ (mword_of_int (PR + 0x80)) (mword_of_int 66 : mword 13)
                Rs5 G3 (av - 12)%nat ltac:(nz) ltac:(exact Hblez)
                with "Hcg Hpc Hi80 [-]").
      iIntros "Hcg Hpc".
      assert (Hp84 : add_vec_int (mword_of_int (PR + 0x80) : mword 64) 4 = mword_of_int (PR + 0x84))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp84) in "Hpc".
      (* ============ the BOUNDED copy loop at +0x84 (fuel induction) ====== *)
      iAssert (∀ (fuel i : nat) (cur : mword 64) (M3 : regfile) (P' : uptd) (chb : bv 8),
          ⌜(Nn - i <= fuel)%nat⌝ -∗ ⌜(i < Nn)%nat⌝ -∗
          ⌜ M3 !!! Regidx csp_rs1 = spr
            /\ M3 !!! Regidx Rs0 = s0v
            /\ M3 !!! Regidx Rs1 = pi
            /\ M3 !!! Regidx Rs2 = cur
            /\ M3 !!! Regidx Rs3 = (mword_of_int (Z.of_nat i) : mword 64)
            /\ M3 !!! Regidx Rs4 = pj
            /\ M3 !!! Regidx Rs5 = (mword_of_int n : mword 64)
            /\ M3 !!! Regidx Rs6 = (mword_of_int (-1) : mword 64)
            /\ M3 !!! Regidx Rs7 = (mword_of_int 1 : mword 64)
            /\ M3 !!! Regidx Rs8 = chaddr
            /\ M3 !!! Regidx Rtp = cid_word
            /\ M3 !!! Regidx Rs9 = m !!! Regidx Rs9
            /\ M3 !!! Regidx Rs10 = m !!! Regidx Rs10
            /\ M3 !!! Regidx Rs11 = m !!! Regidx Rs11 ⌝ -∗
          ⌜ uptd_ext_sz (pv_sz V) (pv_upt V) P' ⌝ -∗
          WXP -∗
          sie_cap_gpr γ M3 (av - 12)%nat -∗
          pc_is (mword_of_int (PR + 0x84) : mword 64) -∗
          cpu_own γ 1%nat eb pj C -∗
          trap_csrs_pay 0 eb -∗
          locked γl cpu_id -∗
          pipe_res γp pi -∗
          pipe_ref γp w q -∗
          p_sz pj ↦₈ pv_sz V -∗
          p_pagetable pj ↦₈ page_base (ud_root (pv_upt V)) -∗
          proc_pt P' -∗
          (∀ P'' : uptd, ⌜uptd_ext_sz (pv_sz V) (pv_upt V) P''⌝ -∗ p_sz pj ↦₈ pv_sz V -∗
             p_pagetable pj ↦₈ page_base (ud_root (pv_upt V)) -∗ proc_pt P'' -∗
             proc_priv γf pj pid (upd_upt V P'')) -∗
          chaddr ↦ₘ chb -∗
          own_ctx (p_context pj) -∗
          ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj -∗
          WP (Loop : expr riscv_lang) {{ Φ }})%I with "[]" as "CLOOP".
      { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
        { iIntros (i cur M3 P' chb) "%Hfu %Hi %Hrg3 %Hex3 HWX Hcg Hpc Hown Hpay Hlocked Hres Href Hszc Hptc Hpt Hpback Hch Hctx Hsched".
          exfalso. lia. }
        iIntros (i cur M3 P' chb) "%Hfu %Hi %Hrg3 %Hex3 HWX Hcg Hpc Hown Hpay Hlocked Hres Href Hszc Hptc Hpt Hpback Hch Hctx Hsched".
        destruct Hrg3 as (H3csp & H3s0 & H3s1 & H3s2 & H3s3 & H3s4 & H3s5 & H3s6 & H3s7 & H3s8 & H3tp & H3s9 & H3s10 & H3s11).
        assert (HZi : (0 <= Z.of_nat i < n)%Z) by lia.
        assert (Hroot : ud_root P' = ud_root (pv_upt V))
          by (destruct Hex3 as ((H1 & _) & _); exact H1).
        iDestruct "Hres" as (nr nw ro wo vnm bs)
          "(Hnm & Hnr & Hnw & Hro & Hwo & Hst0 & Hst1 & %Hcnt & %Hbslen & Hdat & Hslack)".
        assert (Hnra : add_vec (M3 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 536 : mword 12)) = a_pnread pi)
          by (rewrite H3s1; reflexivity).
        (* 0x84 lw a5,536(s1) *)
        iPoseProof (pri_84 with "Htext") as "Hi84".
        iApply (wp_lw_s_sconf γ Φ (mword_of_int (PR + 0x84)) Ra5 Rs1 (mword_of_int 536 : mword 12)
                  M3 (av - 12)%nat nr ltac:(nz) ltac:(nz) with "Hcg Hpc Hi84 [Hnr] [-]").
        { iEval (rewrite Hnra). iExact "Hnr". }
        iIntros "Hcg Hpc Hnr". iEval (rewrite Hnra) in "Hnr".
        set (K1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 nr)]> M3).
        change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 nr)]> M3) with K1.
        assert (Hq88 : add_vec_int (mword_of_int (PR + 0x84) : mword 64) 4 = mword_of_int (PR + 0x88))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq88) in "Hpc".
        assert (HK1s1 : K1 !!! Regidx Rs1 = pi) by (rewrite /K1 upd_ne; [exact H3s1 | reg_neq]).
        assert (Hnwa : add_vec (K1 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 540 : mword 12)) = a_pnwrite pi)
          by (rewrite HK1s1; reflexivity).
        (* 0x88 lw a4,540(s1) *)
        iPoseProof (pri_88 with "Htext") as "Hi88".
        iApply (wp_lw_s_sconf γ Φ (mword_of_int (PR + 0x88)) Ra4 Rs1 (mword_of_int 540 : mword 12)
                  K1 (av - 12)%nat nw ltac:(nz) ltac:(nz) with "Hcg Hpc Hi88 [Hnw] [-]").
        { iEval (rewrite Hnwa). iExact "Hnw". }
        iIntros "Hcg Hpc Hnw". iEval (rewrite Hnwa) in "Hnw".
        set (K2 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 nw)]> K1).
        change (<[Regidx Ra4 := regval_into_reg (sign_extend' 64 nw)]> K1) with K2.
        assert (Hq8c : add_vec_int (mword_of_int (PR + 0x88) : mword 64) 4 = mword_of_int (PR + 0x8c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq8c) in "Hpc".
        assert (HK2a4 : K2 !!! Regidx Ra4 = sign_extend' 64 nw) by (rewrite /K2; apply upd_eq).
        assert (HK2a5 : K2 !!! Regidx Ra5 = sign_extend' 64 nr).
        { rewrite /K2 upd_ne; [| reg_neq]. rewrite /K1 upd_eq. reflexivity. }
        assert (HthrK2 : forall r : mword 5, is_cs_idx r = true -> K2 !!! Regidx r = M3 !!! Regidx r).
        { intros r Hr.
          assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /K2 upd_ne; [| congruence]. rewrite /K1 upd_ne; [| congruence]. reflexivity. }
        iPoseProof (pri_8c with "Htext") as "Hi8c".
        destruct (eq_vec (sign_extend' 64 nw : mword 64) (sign_extend' 64 nr)) eqn:Hemp.
        { (* the pipe is EMPTY: break with the current count *)
          iApply (wp_beq_taken_s_sconf γ Φ (mword_of_int (PR + 0x8c)) (mword_of_int 54 : mword 13)
                    Ra5 Ra4 K2 (av - 12)%nat ltac:(nz) ltac:(nz)
                    ltac:(rewrite HK2a4 HK2a5; exact Hemp) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi8c [-]").
          iApply bi.later_intro. iIntros "Hcg Hpc".
          assert (Hjc2 : add_vec (mword_of_int (PR + 0x8c) : mword 64)
                           (sign_extend' 64 (mword_of_int 54 : mword 13)) = mword_of_int (PR + 0xc2))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hjc2) in "Hpc".
          iAssert (⌜uptd_ext_sz (pv_sz V) (pv_upt V) P'⌝)%I as "#Hxe"; [iPureIntro; exact Hex3|].
          iDestruct ("Hpback" $! P' with "Hxe Hszc Hptc Hpt") as "Hpriv".
          iAssert (pipe_res γp pi) with "[Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack]" as "Hres".
          { iExists nr, nw, ro, wo, vnm, bs.
            iFrame "Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack". iPureIntro. split; assumption. }
          iAssert (∃ b : bv 8, chaddr ↦ₘ b)%I with "[Hch]" as "Hchx"; [by iExists chb|].
          iEval (rewrite /WXP) in "HWX".
          iApply ("HWX" $! K2 P' (mword_of_int (Z.of_nat i))
                    with "[%] [%] [%] Hcg Hpc Hown Hpay Hlocked Hres Href Hpriv Hctx Hsched Hchx").
          { split_and!.
            - rewrite (HthrK2 csp_rs1 ltac:(vm_compute; reflexivity)). exact H3csp.
            - rewrite (HthrK2 Rs1 ltac:(vm_compute; reflexivity)). exact H3s1.
            - rewrite (HthrK2 Rs3 ltac:(vm_compute; reflexivity)). exact H3s3.
            - rewrite (HthrK2 Rtp ltac:(vm_compute; reflexivity)). exact H3tp.
            - rewrite (HthrK2 Rs9 ltac:(vm_compute; reflexivity)). exact H3s9.
            - rewrite (HthrK2 Rs10 ltac:(vm_compute; reflexivity)). exact H3s10.
            - rewrite (HthrK2 Rs11 ltac:(vm_compute; reflexivity)). exact H3s11. }
          { exact (uptd_ext_sz_ext _ _ _ Hex3). }
          { apply pr_ret_cnt. rewrite Z.max_r; [| lia]. lia. } }
        (* the pipe is NOT empty: nr <> nw *)
        assert (Hne : nr <> nw) by (apply (pr_sext_neq nw nr); exact Hemp).
        iApply (wp_beq_fall_s_sconf γ Φ (mword_of_int (PR + 0x8c)) (mword_of_int 54 : mword 13)
                  Ra5 Ra4 K2 (av - 12)%nat ltac:(nz) ltac:(nz)
                  ltac:(rewrite HK2a4 HK2a5; exact Hemp) with "Hcg Hpc Hi8c [-]").
        iIntros "Hcg Hpc".
        assert (Hq90 : add_vec_int (mword_of_int (PR + 0x8c) : mword 64) 4 = mword_of_int (PR + 0x90))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq90) in "Hpc".
        (* 0x90 andi a5,a5,511 : the %PIPESIZE index *)
        pose (idxw := and_vec (sign_extend' 64 nr : mword 64)
                        (sign_extend' 64 (mword_of_int 511 : mword 12))).
        pose (idx := Z.to_nat (bv_unsigned idxw)).
        assert (Hidxb : (0 <= bv_unsigned idxw < 512)%Z) by (rewrite /idxw; apply pr_and511_bound).
        assert (Hidxlt : (idx < 512)%nat) by (rewrite /idx; apply pr_to_nat_lt; exact Hidxb).
        assert (Hidxw : idxw = (mword_of_int (Z.of_nat idx) : mword 64)).
        { rewrite /idx Z2Nat.id; [| exact (proj1 Hidxb)]. symmetry. apply pr_moi_unsigned. }
        assert (Hwv : and_vec (K2 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 511 : mword 12))
                      = (mword_of_int (Z.of_nat idx) : mword 64))
          by (rewrite HK2a5; exact Hidxw).
        iPoseProof (pri_90 with "Htext") as "Hi90".
        iApply (wp_andi_s_sconf γ Φ (mword_of_int (PR + 0x90)) Ra5 Ra5 (mword_of_int 511 : mword 12)
                  (mword_of_int (Z.of_nat idx) : mword 64) K2 (av - 12)%nat
                  ltac:(nz) ltac:(nz) Hwv with "Hcg Hpc Hi90 [-]").
        iIntros "Hcg Hpc".
        set (K3 := <[Regidx Ra5 := regval_into_reg (mword_of_int (Z.of_nat idx) : mword 64)]> K2).
        change (<[Regidx Ra5 := regval_into_reg (mword_of_int (Z.of_nat idx) : mword 64)]> K2) with K3.
        assert (Hq94 : add_vec_int (mword_of_int (PR + 0x90) : mword 64) 4 = mword_of_int (PR + 0x94))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq94) in "Hpc".
        assert (HK3a5 : K3 !!! Regidx Ra5 = (mword_of_int (Z.of_nat idx) : mword 64))
          by (rewrite /K3; apply upd_eq).
        assert (HK2s1 : K2 !!! Regidx Rs1 = pi) by (rewrite /K2 upd_ne; [exact HK1s1 | reg_neq]).
        assert (HK3s1 : K3 !!! Regidx Rs1 = pi) by (rewrite /K3 upd_ne; [exact HK2s1 | reg_neq]).
        (* 0x94 c.add a5,a5,s1 *)
        iPoseProof (pri_94 with "Htext") as "Hi94".
        iApply (wp_cadd_s_sconf γ Φ (mword_of_int (PR + 0x94)) Ra5 Rs1 K3 (av - 12)%nat
                  ltac:(nz) ltac:(nz) with "Hcg Hpc Hi94 [-]").
        iIntros "Hcg Hpc".
        iEval (rewrite HK3a5 HK3s1) in "Hcg".
        set (K4 := <[Regidx Ra5 := regval_into_reg
            (add_vec (mword_of_int (Z.of_nat idx) : mword 64) pi)]> K3).
        change (<[Regidx Ra5 := regval_into_reg
            (add_vec (mword_of_int (Z.of_nat idx) : mword 64) pi)]> K3) with K4.
        assert (Hq96 : add_vec_int (mword_of_int (PR + 0x94) : mword 64) 2 = mword_of_int (PR + 0x96))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq96) in "Hpc".
        assert (HK4a5 : K4 !!! Regidx Ra5 = add_vec (mword_of_int (Z.of_nat idx) : mword 64) pi)
          by (rewrite /K4; apply upd_eq).
        (* 0x96 lbu a5,24(a5) : read the data byte *)
        destruct (lookup_lt_is_Some_2 bs idx ltac:(rewrite Hbslen; unfold PIPESIZE; exact Hidxlt))
          as [db Hlk].
        iDestruct (pr_data_acc pi bs idx db Hlk with "Hdat") as "[Hbyte Hdback]".
        iPoseProof (pri_96 with "Htext") as "Hi96".
        iApply (wp_lbu_s_sconf γ Φ (mword_of_int (PR + 0x96)) Ra5 Ra5 (mword_of_int 24 : mword 12)
                  K4 (av - 12)%nat (db : mword 8) ltac:(nz) ltac:(nz) with "Hcg Hpc Hi96 [Hbyte] [-]").
        { iEval (rewrite HK4a5 pr_dataddr). iExact "Hbyte". }
        iIntros "Hcg Hpc Hbyte". iEval (rewrite HK4a5 pr_dataddr) in "Hbyte".
        iDestruct ("Hdback" with "Hbyte") as "Hdat".
        set (K5 := <[Regidx Ra5 := regval_into_reg (zero_extend' 64 (db : mword 8))]> K4).
        change (<[Regidx Ra5 := regval_into_reg (zero_extend' 64 (db : mword 8))]> K4) with K5.
        assert (Hq9a : add_vec_int (mword_of_int (PR + 0x96) : mword 64) 4 = mword_of_int (PR + 0x9a))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq9a) in "Hpc".
        assert (HthrK5 : forall r : mword 5, is_cs_idx r = true -> K5 !!! Regidx r = M3 !!! Regidx r).
        { intros r Hr.
          assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /K5 upd_ne; [| congruence]. rewrite /K4 upd_ne; [| congruence].
          rewrite /K3 upd_ne; [| congruence]. apply HthrK2; exact Hr. }
        assert (HK5a5 : K5 !!! Regidx Ra5 = zero_extend' 64 (db : mword 8)) by (rewrite /K5; apply upd_eq).
        assert (HK5s0 : K5 !!! Regidx Rs0 = s0v)
          by (rewrite (HthrK5 Rs0 ltac:(vm_compute; reflexivity)); exact H3s0).
        assert (Hchd : add_vec s0v (sign_extend' 64 (mword_of_int 4015 : mword 12)) = chaddr)
          by reflexivity.
        (* 0x9a sb a5,-81(s0) : store the byte into [ch] *)
        iPoseProof (pri_9a with "Htext") as "Hi9a".
        iApply (wp_sb_s_sconf γ Φ (mword_of_int (PR + 0x9a)) Ra5 Rs0 (mword_of_int 4015 : mword 12)
                  K5 (av - 12)%nat chb with "Hcg Hpc Hi9a [Hch] [-]").
        { iEval (rewrite HK5s0 Hchd). iExact "Hch". }
        iIntros "Hcg Hpc Hch". iEval (rewrite HK5s0 Hchd) in "Hch".
        assert (Hq9e : add_vec_int (mword_of_int (PR + 0x9a) : mword 64) 4 = mword_of_int (PR + 0x9e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq9e) in "Hpc".
        (* 0x9e/0xa0/0xa2: a3 := 1, a2 := &ch, a1 := cursor *)
        iPoseProof (pri_9e with "Htext") as "Hi9e".
        iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PR + 0x9e)) Ra3 Rs7 K5 (av - 12)%nat
                  ltac:(nz) ltac:(nz) with "Hcg Hpc Hi9e [-]").
        iIntros "Hcg Hpc".
        set (K6 := <[Regidx Ra3 := regval_into_reg (add_vec zero_reg (K5 !!! Regidx Rs7))]> K5).
        change (<[Regidx Ra3 := regval_into_reg (add_vec zero_reg (K5 !!! Regidx Rs7))]> K5) with K6.
        assert (Hqa0 : add_vec_int (mword_of_int (PR + 0x9e) : mword 64) 2 = mword_of_int (PR + 0xa0))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hqa0) in "Hpc".
        iPoseProof (pri_a0 with "Htext") as "Hia0".
        iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PR + 0xa0)) Ra2 Rs8 K6 (av - 12)%nat
                  ltac:(nz) ltac:(nz) with "Hcg Hpc Hia0 [-]").
        iIntros "Hcg Hpc".
        set (K7 := <[Regidx Ra2 := regval_into_reg (add_vec zero_reg (K6 !!! Regidx Rs8))]> K6).
        change (<[Regidx Ra2 := regval_into_reg (add_vec zero_reg (K6 !!! Regidx Rs8))]> K6) with K7.
        assert (Hqa2 : add_vec_int (mword_of_int (PR + 0xa0) : mword 64) 2 = mword_of_int (PR + 0xa2))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hqa2) in "Hpc".
        iPoseProof (pri_a2 with "Htext") as "Hia2".
        iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PR + 0xa2)) Ra1 Rs2 K7 (av - 12)%nat
                  ltac:(nz) ltac:(nz) with "Hcg Hpc Hia2 [-]").
        iIntros "Hcg Hpc".
        set (K8 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (K7 !!! Regidx Rs2))]> K7).
        change (<[Regidx Ra1 := regval_into_reg (add_vec zero_reg (K7 !!! Regidx Rs2))]> K7) with K8.
        assert (Hqa4 : add_vec_int (mword_of_int (PR + 0xa2) : mword 64) 2 = mword_of_int (PR + 0xa4))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hqa4) in "Hpc".
        assert (HK8s4 : K8 !!! Regidx Rs4 = pj).
        { rewrite /K8 upd_ne; [| reg_neq]. rewrite /K7 upd_ne; [| reg_neq].
          rewrite /K6 upd_ne; [| reg_neq].
          rewrite (HthrK5 Rs4 ltac:(vm_compute; reflexivity)). exact H3s4. }
        assert (Hpta : add_vec (K8 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 80 : mword 12))
                       = p_pagetable pj) by (rewrite HK8s4; reflexivity).
        (* 0xa4 ld a0,80(s4) : a0 := p->pagetable *)
        iEval (rewrite -Hroot) in "Hptc".
        iPoseProof (pri_a4 with "Htext") as "Hia4".
        iApply (wp_ld_s_sconf γ Φ (mword_of_int (PR + 0xa4)) Ra0 Rs4 (mword_of_int 80 : mword 12)
                  K8 (av - 12)%nat (page_base (ud_root P')) ltac:(nz) ltac:(nz)
                  with "Hcg Hpc Hia4 [Hptc] [-]").
        { iEval (rewrite Hpta). iExact "Hptc". }
        iIntros "Hcg Hpc Hptc". iEval (rewrite Hpta) in "Hptc".
        set (K9 := <[Regidx Ra0 := regval_into_reg (page_base (ud_root P'))]> K8).
        change (<[Regidx Ra0 := regval_into_reg (page_base (ud_root P'))]> K8) with K9.
        assert (Hqa8 : add_vec_int (mword_of_int (PR + 0xa4) : mword 64) 4 = mword_of_int (PR + 0xa8))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hqa8) in "Hpc".
        (* 0xa8 jal copyout *)
        iPoseProof (pri_a8 with "Htext") as "Hia8".
        iApply (wp_jal_s_sconf γ Φ (mword_of_int (PR + 0xa8)) Rra (mword_of_int 2084838 : mword 21)
                  K9 (av - 12)%nat ltac:(nz) ltac:(nz) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hia8 [-]").
        iIntros "Hcg Hpc".
        set (K10 := <[Regidx Rra := regval_into_reg
            (add_vec_int (mword_of_int (PR + 0xa8) : mword 64) 4)]> K9).
        change (<[Regidx Rra := regval_into_reg
            (add_vec_int (mword_of_int (PR + 0xa8) : mword 64) 4)]> K9) with K10.
        assert (Hjco : add_vec (mword_of_int (PR + 0xa8) : mword 64)
                         (sign_extend' 64 (mword_of_int 2084838 : mword 21)) = mword_of_int KernelSyms.copyout)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjco) in "Hpc".
        assert (HthrK : forall r : mword 5, is_cs_idx r = true -> K10 !!! Regidx r = M3 !!! Regidx r).
        { intros r Hr.
          assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N11 : r <> Ra1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N12 : r <> Ra2) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N13 : r <> Ra3) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /K10 upd_ne; [| congruence]. rewrite /K9 upd_ne; [| congruence].
          rewrite /K8 upd_ne; [| congruence]. rewrite /K7 upd_ne; [| congruence].
          rewrite /K6 upd_ne; [| congruence]. apply HthrK5; exact Hr. }
        assert (HK10a0 : K10 !!! Regidx Ra0 = page_base (ud_root P')).
        { rewrite /K10 upd_ne; [| reg_neq]. rewrite /K9 upd_eq. reflexivity. }
        assert (HK10a2 : K10 !!! Regidx Ra2 = chaddr).
        { rewrite /K10 upd_ne; [| reg_neq]. rewrite /K9 upd_ne; [| reg_neq].
          rewrite /K8 upd_ne; [| reg_neq]. rewrite /K7 upd_eq. unfold regval_into_reg.
          rewrite /K6 upd_ne; [| reg_neq]. rewrite (HthrK5 Rs8 ltac:(vm_compute; reflexivity)) H3s8.
          apply add_vec_zero_l. }
        assert (HK10a3 : K10 !!! Regidx Ra3 = (mword_of_int (Z.of_nat 1%nat) : mword 64)).
        { rewrite /K10 upd_ne; [| reg_neq]. rewrite /K9 upd_ne; [| reg_neq].
          rewrite /K8 upd_ne; [| reg_neq]. rewrite /K7 upd_ne; [| reg_neq].
          rewrite /K6 upd_eq. unfold regval_into_reg.
          rewrite (HthrK5 Rs7 ltac:(vm_compute; reflexivity)) H3s7.
          rewrite add_vec_zero_l. reflexivity. }
        assert (HK10tp : K10 !!! Regidx Rtp = cid_word)
          by (rewrite (HthrK Rtp ltac:(vm_compute; reflexivity)); exact H3tp).
        assert (HK50 : (50 <= av - 12)%nat) by lia.
        iApply (Copyout.wp_copyout_sconf γ γa Φ K10 P' (pv_sz V) 1%nat
                  (fun _ => trunc8 (K5 !!! Regidx Ra5)) (av - 12)%nat 1%nat eb pj C
                  (DfracOwn 1) (DfracOwn 1)
                  HK50 HK10tp HK10a0 HK10a3 pr_len1_64 Hszb pr_lvl1
                  with "Hcg Hown Htext Hpc Hszc Hptc Hpt Henv [Hch] [-]").
        { iEval (rewrite HK10a2). iApply pr_buf1_intro. iExact "Hch". }
        iIntros (mrc P'') "Hcg Hown Hpc Hszc Hptc Hpt Hbuf %Hcsr %Hext2 %Hret".
        iEval (rewrite HK10a2) in "Hbuf".
        iDestruct (pr_buf1_elim with "Hbuf") as "Hch".
        iEval (rewrite Hroot) in "Hptc".
        assert (HK10ra : K10 !!! Regidx Rra = add_vec_int (mword_of_int (PR + 0xa8) : mword 64) 4)
          by (rewrite /K10; apply upd_eq).
        iEval (rewrite HK10ra) in "Hpc".
        assert (Hqac : ret_pc (add_vec_int (mword_of_int (PR + 0xa8) : mword 64) 4)
                       = (mword_of_int (PR + 0xac) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hqac) in "Hpc".
        assert (Hext' : uptd_ext_sz (pv_sz V) (pv_upt V) P'')
          by (apply (uptd_ext_sz_trans _ _ P' _); assumption).
        assert (HthrMr : forall r : mword 5, is_cs_idx r = true -> mrc !!! Regidx r = M3 !!! Regidx r).
        { intros r Hr. rewrite (callee_saved_lookup Hcsr r Hr). apply HthrK; exact Hr. }
        assert (Hmrcs6 : mrc !!! Regidx Rs6 = (mword_of_int (-1) : mword 64))
          by (rewrite (HthrMr Rs6 ltac:(vm_compute; reflexivity)); exact H3s6).
        assert (Hmrcs3 : mrc !!! Regidx Rs3 = (mword_of_int (Z.of_nat i) : mword 64))
          by (rewrite (HthrMr Rs3 ltac:(vm_compute; reflexivity)); exact H3s3).
        iPoseProof (pri_ac with "Htext") as "Hiac".
        destruct Hret as [Hr0 | Hrm1].
        { (* copyout SUCCEEDED: fall through and bump nread / i / the cursor *)
          iApply (wp_beq_fall_s_sconf γ Φ (mword_of_int (PR + 0xac)) (mword_of_int 62 : mword 13)
                    Rs6 Ra0 mrc (av - 12)%nat ltac:(nz) ltac:(nz)
                    ltac:(rewrite Hr0 Hmrcs6; vm_compute; reflexivity)
                    with "Hcg Hpc Hiac [-]").
          iIntros "Hcg Hpc".
          assert (Hqb0 : add_vec_int (mword_of_int (PR + 0xac) : mword 64) 4 = mword_of_int (PR + 0xb0))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hqb0) in "Hpc".
          assert (Hmrcs1 : mrc !!! Regidx Rs1 = pi)
            by (rewrite (HthrMr Rs1 ltac:(vm_compute; reflexivity)); exact H3s1).
          assert (Hnra2 : add_vec (mrc !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 536 : mword 12))
                          = a_pnread pi) by (rewrite Hmrcs1; reflexivity).
          (* 0xb0 lw a5,536(s1) *)
          iPoseProof (pri_b0 with "Htext") as "Hib0".
          iApply (wp_lw_s_sconf γ Φ (mword_of_int (PR + 0xb0)) Ra5 Rs1 (mword_of_int 536 : mword 12)
                    mrc (av - 12)%nat nr ltac:(nz) ltac:(nz) with "Hcg Hpc Hib0 [Hnr] [-]").
          { iEval (rewrite Hnra2). iExact "Hnr". }
          iIntros "Hcg Hpc Hnr". iEval (rewrite Hnra2) in "Hnr".
          set (D1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 nr)]> mrc).
          change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 nr)]> mrc) with D1.
          assert (Hqb4 : add_vec_int (mword_of_int (PR + 0xb0) : mword 64) 4 = mword_of_int (PR + 0xb4))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hqb4) in "Hpc".
          assert (HD1a5 : D1 !!! Regidx Ra5 = sign_extend' 64 nr) by (rewrite /D1; apply upd_eq).
          (* 0xb4 c.addiw a5,a5,1 *)
          iPoseProof (pri_b4 with "Htext") as "Hib4".
          iApply (wp_caddiw_s_sconf γ Φ (mword_of_int (PR + 0xb4)) Ra5 (mword_of_int 1 : mword 6)
                    D1 (av - 12)%nat ltac:(nz) ltac:(nz) with "Hcg Hpc Hib4 [-]").
          iIntros "Hcg Hpc".
          iEval (rewrite HD1a5) in "Hcg".
          set (D2 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (subrange_vec_dec
              (add_vec (sign_extend' 64 nr)
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> D1).
          change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 (subrange_vec_dec
              (add_vec (sign_extend' 64 nr)
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> D1) with D2.
          assert (Hqb6 : add_vec_int (mword_of_int (PR + 0xb4) : mword 64) 2 = mword_of_int (PR + 0xb6))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hqb6) in "Hpc".
          assert (HD2s1 : D2 !!! Regidx Rs1 = pi).
          { rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [| reg_neq]. exact Hmrcs1. }
          assert (Hnra3 : add_vec (D2 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 536 : mword 12))
                          = a_pnread pi) by (rewrite HD2s1; reflexivity).
          (* 0xb6 sw a5,536(s1) : nread++ *)
          iPoseProof (pri_b6 with "Htext") as "Hib6".
          iApply (wp_sw_s_sconf γ Φ (mword_of_int (PR + 0xb6)) Ra5 Rs1 (mword_of_int 536 : mword 12)
                    D2 (av - 12)%nat nr with "Hcg Hpc Hib6 [Hnr] [-]").
          { iEval (rewrite Hnra3). iExact "Hnr". }
          iIntros "Hcg Hpc Hnr".
          assert (HD2a5 : D2 !!! Regidx Ra5 = sign_extend' 64 (subrange_vec_dec
              (add_vec (sign_extend' 64 nr)
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
            by (rewrite /D2; apply upd_eq).
          iEval (rewrite Hnra3 HD2a5 pr_sw_nread) in "Hnr".
          assert (Hqba : add_vec_int (mword_of_int (PR + 0xb6) : mword 64) 4 = mword_of_int (PR + 0xba))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hqba) in "Hpc".
          assert (HD2s3 : D2 !!! Regidx Rs3 = (mword_of_int (Z.of_nat i) : mword 64)).
          { rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1 upd_ne; [| reg_neq]. exact Hmrcs3. }
          (* 0xba c.addiw s3,s3,1 : i++ *)
          iPoseProof (pri_ba with "Htext") as "Hiba".
          iApply (wp_caddiw_s_sconf γ Φ (mword_of_int (PR + 0xba)) Rs3 (mword_of_int 1 : mword 6)
                    D2 (av - 12)%nat ltac:(nz) ltac:(nz) with "Hcg Hpc Hiba [-]").
          iIntros "Hcg Hpc".
          iEval (rewrite HD2s3) in "Hcg".
          assert (HSi : sign_extend' 64 (subrange_vec_dec
                    (add_vec (mword_of_int (Z.of_nat i) : mword 64)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)
                  = (mword_of_int (Z.of_nat (S i)) : mword 64)).
          { rewrite (pr_addiw1_moi (Z.of_nat i) ltac:(lia) ltac:(lia)).
            f_equal. lia. }
          iEval (rewrite HSi) in "Hcg".
          set (D3 := <[Regidx Rs3 := regval_into_reg (mword_of_int (Z.of_nat (S i)) : mword 64)]> D2).
          change (<[Regidx Rs3 := regval_into_reg (mword_of_int (Z.of_nat (S i)) : mword 64)]> D2) with D3.
          assert (Hqbc : add_vec_int (mword_of_int (PR + 0xba) : mword 64) 2 = mword_of_int (PR + 0xbc))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hqbc) in "Hpc".
          assert (HD3s2 : D3 !!! Regidx Rs2 = cur).
          { rewrite /D3 upd_ne; [| reg_neq]. rewrite /D2 upd_ne; [| reg_neq].
            rewrite /D1 upd_ne; [| reg_neq].
            rewrite (HthrMr Rs2 ltac:(vm_compute; reflexivity)). exact H3s2. }
          (* 0xbc c.addi s2,s2,1 : the user cursor *)
          iPoseProof (pri_bc with "Htext") as "Hibc".
          iApply (wp_caddi_s_sconf γ Φ (mword_of_int (PR + 0xbc)) Rs2 (mword_of_int 1 : mword 6)
                    D3 (av - 12)%nat ltac:(nz) ltac:(nz) with "Hcg Hpc Hibc [-]").
          iIntros "Hcg Hpc".
          iEval (rewrite HD3s2) in "Hcg".
          set (D4 := <[Regidx Rs2 := regval_into_reg
              (add_vec cur (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> D3).
          change (<[Regidx Rs2 := regval_into_reg
              (add_vec cur (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> D3) with D4.
          assert (Hqbe : add_vec_int (mword_of_int (PR + 0xbc) : mword 64) 2 = mword_of_int (PR + 0xbe))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hqbe) in "Hpc".
          assert (HthrD : forall r : mword 5, is_cs_idx r = true -> r <> Rs2 -> r <> Rs3 ->
                    D4 !!! Regidx r = M3 !!! Regidx r).
          { intros r Hr N18 N19.
            assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
            rewrite /D4 upd_ne; [| congruence]. rewrite /D3 upd_ne; [| congruence].
            rewrite /D2 upd_ne; [| congruence]. rewrite /D1 upd_ne; [| congruence].
            apply HthrMr; exact Hr. }
          assert (HD4s2 : D4 !!! Regidx Rs2
                          = add_vec cur (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
            by (rewrite /D4; apply upd_eq).
          assert (HD4s3 : D4 !!! Regidx Rs3 = (mword_of_int (Z.of_nat (S i)) : mword 64)).
          { rewrite /D4 upd_ne; [| reg_neq]. rewrite /D3 upd_eq. reflexivity. }
          assert (HD4s5 : D4 !!! Regidx Rs5 = (mword_of_int n : mword 64))
            by (rewrite (HthrD Rs5 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)); exact H3s5).
          (* re-establish the count invariant for the incremented nread *)
          assert (Hcnt' : pipe_count_ok (add_vec nr (mword_of_int 1 : mword 32)) nw)
            by (apply pipe_count_decr_r; assumption).
          iAssert (pipe_res γp pi) with "[Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack]" as "Hres".
          { iExists (add_vec nr (mword_of_int 1 : mword 32)), nw, ro, wo, vnm, bs.
            iFrame "Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack". iPureIntro. split; assumption. }
          (* 0xbe bne s5,s3 *)
          iPoseProof (pri_be with "Htext") as "Hibe".
          destruct (decide (S i = Nn)) as [Hlast | Hmore].
          - (* i+1 = n: the loop is done *)
            assert (HZs : Z.of_nat (S i) = n) by (rewrite Hlast; exact HNn).
            iApply (wp_bne_fall_s_sconf γ Φ (mword_of_int (PR + 0xbe)) (mword_of_int 8134 : mword 13)
                      Rs3 Rs5 D4 (av - 12)%nat ltac:(nz) ltac:(nz)
                      ltac:(rewrite HD4s5 HD4s3 HZs; apply pr_moi_eqself)
                      with "Hcg Hpc Hibe [-]").
            iIntros "Hcg Hpc".
            assert (Hqc2 : add_vec_int (mword_of_int (PR + 0xbe) : mword 64) 4 = mword_of_int (PR + 0xc2))
              by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hqc2) in "Hpc".
            iAssert (⌜uptd_ext_sz (pv_sz V) (pv_upt V) P''⌝)%I as "#Hxe"; [iPureIntro; exact Hext'|].
            iDestruct ("Hpback" $! P'' with "Hxe Hszc Hptc Hpt") as "Hpriv".
            iAssert (∃ b : bv 8, chaddr ↦ₘ b)%I with "[Hch]" as "Hchx";
              [by iExists (trunc8 (K5 !!! Regidx Ra5))|].
            iEval (rewrite /WXP) in "HWX".
            iApply ("HWX" $! D4 P'' (mword_of_int (Z.of_nat (S i)))
                      with "[%] [%] [%] Hcg Hpc Hown Hpay Hlocked Hres Href Hpriv Hctx Hsched Hchx").
            { split_and!.
              - rewrite (HthrD csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)). exact H3csp.
              - rewrite (HthrD Rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)). exact H3s1.
              - exact HD4s3.
              - rewrite (HthrD Rtp ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)). exact H3tp.
              - rewrite (HthrD Rs9 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)). exact H3s9.
              - rewrite (HthrD Rs10 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)). exact H3s10.
              - rewrite (HthrD Rs11 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)). exact H3s11. }
            { exact (uptd_ext_sz_ext _ _ _ Hext'). }
            { apply pr_ret_cnt. rewrite Z.max_r; [| lia]. lia. }
          - (* i+1 < n: the back edge *)
            assert (HSilt : (S i < Nn)%nat) by lia.
            assert (HZs : (Z.of_nat (S i) < n)%Z) by lia.
            iApply (wp_bne_taken_s_sconf γ Φ (mword_of_int (PR + 0xbe)) (mword_of_int 8134 : mword 13)
                      Rs3 Rs5 D4 (av - 12)%nat ltac:(nz) ltac:(nz)
                      ltac:(rewrite HD4s5 HD4s3; apply pr_moi_neq; lia)
                      ltac:(vm_compute; reflexivity)
                      with "Hcg Hpc Hibe [-]").
            iApply bi.later_intro. iIntros "Hcg Hpc".
            assert (Hbk : add_vec (mword_of_int (PR + 0xbe) : mword 64)
                            (sign_extend' 64 (mword_of_int 8134 : mword 13)) = mword_of_int (PR + 0x84))
              by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hbk) in "Hpc".
            iApply ("IHf" $! (S i) (add_vec cur (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
                      D4 P'' (trunc8 (K5 !!! Regidx Ra5))
                      with "[%] [%] [%] [%] HWX Hcg Hpc Hown Hpay Hlocked Hres Href Hszc Hptc Hpt Hpback Hch Hctx Hsched").
            { lia. }
            { exact HSilt. }
            { split_and!.
              - rewrite (HthrD csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)). exact H3csp.
              - rewrite (HthrD Rs0 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)). exact H3s0.
              - rewrite (HthrD Rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)). exact H3s1.
              - exact HD4s2.
              - exact HD4s3.
              - rewrite (HthrD Rs4 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)). exact H3s4.
              - exact HD4s5.
              - rewrite (HthrD Rs6 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)). exact H3s6.
              - rewrite (HthrD Rs7 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)). exact H3s7.
              - rewrite (HthrD Rs8 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)). exact H3s8.
              - rewrite (HthrD Rtp ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)). exact H3tp.
              - rewrite (HthrD Rs9 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)). exact H3s9.
              - rewrite (HthrD Rs10 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)). exact H3s10.
              - rewrite (HthrD Rs11 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)). exact H3s11. }
            { exact Hext'. } }
        (* copyout FAILED: break, returning -1 only if nothing was copied *)
        iApply (wp_beq_taken_s_sconf γ Φ (mword_of_int (PR + 0xac)) (mword_of_int 62 : mword 13)
                  Rs6 Ra0 mrc (av - 12)%nat ltac:(nz) ltac:(nz)
                  ltac:(rewrite Hrm1 Hmrcs6; apply eq_vec_true_iff; reflexivity)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hiac [-]").
        iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Hjea : add_vec (mword_of_int (PR + 0xac) : mword 64)
                         (sign_extend' 64 (mword_of_int 62 : mword 13)) = mword_of_int (PR + 0xea))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjea) in "Hpc".
        iAssert (⌜uptd_ext_sz (pv_sz V) (pv_upt V) P''⌝)%I as "#Hxe"; [iPureIntro; exact Hext'|].
        iDestruct ("Hpback" $! P'' with "Hxe Hszc Hptc Hpt") as "Hpriv".
        iAssert (pipe_res γp pi) with "[Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack]" as "Hres".
        { iExists nr, nw, ro, wo, vnm, bs.
          iFrame "Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack". iPureIntro. split; assumption. }
        iAssert (∃ b : bv 8, chaddr ↦ₘ b)%I with "[Hch]" as "Hchx";
          [by iExists (trunc8 (K5 !!! Regidx Ra5))|].
        iEval (rewrite /WXP) in "HWX".
        iPoseProof (pri_ea with "Htext") as "Hiea".
        destruct (decide (i = 0%nat)) as [Hi0 | Hinz].
        { (* nothing copied yet: s3 := -1 *)
          iApply (wp_pr_bnez_x0_fall γ Φ (mword_of_int (PR + 0xea)) (mword_of_int 8152 : mword 13)
                    Rs3 mrc (av - 12)%nat ltac:(nz)
                    ltac:(rewrite Hmrcs3 Hi0; exact pr_moi0_z) with "Hcg Hpc Hiea [-]").
          iIntros "Hcg Hpc".
          assert (Hqee : add_vec_int (mword_of_int (PR + 0xea) : mword 64) 4 = mword_of_int (PR + 0xee))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hqee) in "Hpc".
          (* 0xee c.mv s3,a0 *)
          iPoseProof (pri_ee with "Htext") as "Hiee".
          iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PR + 0xee)) Rs3 Ra0 mrc (av - 12)%nat
                    ltac:(nz) ltac:(nz) with "Hcg Hpc Hiee [-]").
          iIntros "Hcg Hpc".
          set (E1 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (mrc !!! Regidx Ra0))]> mrc).
          change (<[Regidx Rs3 := regval_into_reg (add_vec zero_reg (mrc !!! Regidx Ra0))]> mrc) with E1.
          assert (Hqf0 : add_vec_int (mword_of_int (PR + 0xee) : mword 64) 2 = mword_of_int (PR + 0xf0))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hqf0) in "Hpc".
          assert (HE1s3 : E1 !!! Regidx Rs3 = (mword_of_int (-1) : mword 64)).
          { rewrite /E1 upd_eq. unfold regval_into_reg. rewrite Hrm1. apply add_vec_zero_l. }
          (* 0xf0 c.j -> +0xc2 *)
          iPoseProof (pri_f0 with "Htext") as "Hif0".
          iApply (wp_cj_s_sconf γ Φ (mword_of_int (PR + 0xf0))
                    (sign_extend' 21 (concat_vec (mword_of_int 2025 : mword 11) ('b"0")))
                    E1 (av - 12)%nat ltac:(vm_compute; reflexivity) with "Hcg Hpc Hif0 [-]").
          iApply bi.later_intro. iIntros "Hcg Hpc".
          assert (Hjf0 : add_vec (mword_of_int (PR + 0xf0) : mword 64)
                           (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2025 : mword 11) ('b"0"))))
                         = mword_of_int (PR + 0xc2)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hjf0) in "Hpc".
          iApply ("HWX" $! E1 P'' (mword_of_int (-1))
                    with "[%] [%] [%] Hcg Hpc Hown Hpay Hlocked Hres Href Hpriv Hctx Hsched Hchx").
          { split_and!.
            - rewrite /E1 upd_ne; [| reg_neq].
              rewrite (HthrMr csp_rs1 ltac:(vm_compute; reflexivity)). exact H3csp.
            - rewrite /E1 upd_ne; [| reg_neq].
              rewrite (HthrMr Rs1 ltac:(vm_compute; reflexivity)). exact H3s1.
            - exact HE1s3.
            - rewrite /E1 upd_ne; [| reg_neq].
              rewrite (HthrMr Rtp ltac:(vm_compute; reflexivity)). exact H3tp.
            - rewrite /E1 upd_ne; [| reg_neq].
              rewrite (HthrMr Rs9 ltac:(vm_compute; reflexivity)). exact H3s9.
            - rewrite /E1 upd_ne; [| reg_neq].
              rewrite (HthrMr Rs10 ltac:(vm_compute; reflexivity)). exact H3s10.
            - rewrite /E1 upd_ne; [| reg_neq].
              rewrite (HthrMr Rs11 ltac:(vm_compute; reflexivity)). exact H3s11. }
          { exact (uptd_ext_sz_ext _ _ _ Hext'). }
          { apply pr_ret_neg1. } }
        (* something WAS copied: keep the partial count *)
        iApply (wp_pr_bnez_x0_taken γ Φ (mword_of_int (PR + 0xea)) (mword_of_int 8152 : mword 13)
                  Rs3 mrc (av - 12)%nat ltac:(nz)
                  ltac:(rewrite Hmrcs3; apply pr_moi_nz; lia)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hiea [-]").
        iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Hjeac : add_vec (mword_of_int (PR + 0xea) : mword 64)
                          (sign_extend' 64 (mword_of_int 8152 : mword 13)) = mword_of_int (PR + 0xc2))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjeac) in "Hpc".
        iApply ("HWX" $! mrc P'' (mword_of_int (Z.of_nat i))
                  with "[%] [%] [%] Hcg Hpc Hown Hpay Hlocked Hres Href Hpriv Hctx Hsched Hchx").
        { split_and!.
          - rewrite (HthrMr csp_rs1 ltac:(vm_compute; reflexivity)). exact H3csp.
          - rewrite (HthrMr Rs1 ltac:(vm_compute; reflexivity)). exact H3s1.
          - exact Hmrcs3.
          - rewrite (HthrMr Rtp ltac:(vm_compute; reflexivity)). exact H3tp.
          - rewrite (HthrMr Rs9 ltac:(vm_compute; reflexivity)). exact H3s9.
          - rewrite (HthrMr Rs10 ltac:(vm_compute; reflexivity)). exact H3s10.
          - rewrite (HthrMr Rs11 ltac:(vm_compute; reflexivity)). exact H3s11. }
        { exact (uptd_ext_sz_ext _ _ _ Hext'). }
        { apply pr_ret_cnt. rewrite Z.max_r; [| lia]. lia. } }
      (* enter the copy loop at i = 0 *)
      iApply ("CLOOP" $! Nn 0%nat addrv G3 (pv_upt V) chb0
                with "[%] [%] [%] [%] HWX Hcg Hpc Hown Hpay Hlocked Hres Href Hszc Hptc Hpt Hpback Hch Hctx Hsched").
      { lia. }
      { lia. }
      { split_and!; try assumption. }
      { apply uptd_ext_sz_refl. } }
    (* ================= the WAIT LOOP (iLöb) from +0x34 ================= *)
    iAssert (∀ M : regfile,
        ⌜ callee_saved W0 M ⌝ -∗
        (EPIC ∧ CPP) -∗
        sie_cap_gpr γ M (av - 12)%nat -∗
        pc_is (mword_of_int (PR + 0x34) : mword 64) -∗
        cpu_own γ 1%nat eb pj C -∗
        trap_csrs_pay 0 eb -∗
        locked γl cpu_id -∗
        pipe_res γp pi -∗
        pipe_ref γp w q -∗
        proc_priv γf pj pid V -∗
        own_ctx (p_context pj) -∗
        ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj -∗
        (∃ z : mword 64, pa_stk sp0 8 ↦₈ z) -∗
        (∃ z : mword 64, pa_stk sp0 9 ↦₈ z) -∗
        (∃ z : mword 64, pa_stk sp0 10 ↦₈ z) -∗
        (∃ z : mword 64, pa_stk sp0 11 ↦₈ z) -∗
        (∃ z : mword 64, pa_stk sp0 12 ↦₈ z) -∗
        WP (Loop : expr riscv_lang) {{ Φ }})%I with "[]" as "WLOOP".
    { iLöb as "IH".
      iIntros (M) "%HcsM HEX Hcg Hpc Hown Hpay Hlocked Hres Href Hpriv Hctx Hsched Hq8 Hq9 Hq10 Hq11 Hq12".
      assert (HMcsp : M !!! Regidx csp_rs1 = spr)
        by (rewrite (callee_saved_lookup HcsM csp_rs1 ltac:(vm_compute; reflexivity)); exact HW0csp).
      assert (HMs0 : M !!! Regidx Rs0 = s0v)
        by (rewrite (callee_saved_lookup HcsM Rs0 ltac:(vm_compute; reflexivity)); exact HW0s0).
      assert (HMs1 : M !!! Regidx Rs1 = pi)
        by (rewrite (callee_saved_lookup HcsM Rs1 ltac:(vm_compute; reflexivity)); exact HW0s1).
      assert (HMs2 : M !!! Regidx Rs2 = addrv)
        by (rewrite (callee_saved_lookup HcsM Rs2 ltac:(vm_compute; reflexivity)); exact HW0s2).
      assert (HMs3 : M !!! Regidx Rs3 = a_pnread pi)
        by (rewrite (callee_saved_lookup HcsM Rs3 ltac:(vm_compute; reflexivity)); exact HW0s3).
      assert (HMs4 : M !!! Regidx Rs4 = pj)
        by (rewrite (callee_saved_lookup HcsM Rs4 ltac:(vm_compute; reflexivity)); exact HW0s4).
      assert (HMs5 : M !!! Regidx Rs5 = (mword_of_int n : mword 64))
        by (rewrite (callee_saved_lookup HcsM Rs5 ltac:(vm_compute; reflexivity)); exact HW0s5).
      assert (HMtp : M !!! Regidx Rtp = cid_word)
        by (rewrite (callee_saved_lookup HcsM Rtp ltac:(vm_compute; reflexivity)); exact HW0tp).
      assert (HMs6 : M !!! Regidx Rs6 = vs6)
        by (rewrite (callee_saved_lookup HcsM Rs6 ltac:(vm_compute; reflexivity)); exact HW0s6).
      assert (HMs7 : M !!! Regidx Rs7 = vs7)
        by (rewrite (callee_saved_lookup HcsM Rs7 ltac:(vm_compute; reflexivity)); exact HW0s7).
      assert (HMs8 : M !!! Regidx Rs8 = vs8)
        by (rewrite (callee_saved_lookup HcsM Rs8 ltac:(vm_compute; reflexivity)); exact HW0s8).
      assert (HMs9 : M !!! Regidx Rs9 = m !!! Regidx Rs9)
        by (rewrite (callee_saved_lookup HcsM Rs9 ltac:(vm_compute; reflexivity)); exact HW0s9).
      assert (HMs10 : M !!! Regidx Rs10 = m !!! Regidx Rs10)
        by (rewrite (callee_saved_lookup HcsM Rs10 ltac:(vm_compute; reflexivity)); exact HW0s10).
      assert (HMs11 : M !!! Regidx Rs11 = m !!! Regidx Rs11)
        by (rewrite (callee_saved_lookup HcsM Rs11 ltac:(vm_compute; reflexivity)); exact HW0s11).
      (* ---- 0x34 lw a5,548(s1) : the writeopen flag ---- *)
      iDestruct "Hres" as (nr1 nw1 ro1 wo1 vnm1 bs1)
        "(Hnm & Hnr & Hnw & Hro & Hwo & Hst0 & Hst1 & %Hcnt1 & %Hlen1 & Hdat & Hslack)".
      assert (Hwoa : add_vec (M !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 548 : mword 12))
                     = a_popen pi true) by (rewrite HMs1; reflexivity).
      iPoseProof (pri_34 with "Htext") as "Hi34".
      iApply (wp_lw_s_sconf γ Φ (mword_of_int (PR + 0x34)) Ra5 Rs1 (mword_of_int 548 : mword 12)
                M (av - 12)%nat wo1 ltac:(nz) ltac:(nz) with "Hcg Hpc Hi34 [Hwo] [-]").
      { iEval (rewrite Hwoa). iExact "Hwo". }
      iIntros "Hcg Hpc Hwo". iEval (rewrite Hwoa) in "Hwo".
      set (L1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 wo1)]> M).
      change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 wo1)]> M) with L1.
      assert (Hw38 : add_vec_int (mword_of_int (PR + 0x34) : mword 64) 4 = mword_of_int (PR + 0x38))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hw38) in "Hpc".
      assert (HL1a5 : L1 !!! Regidx Ra5 = sign_extend' 64 wo1) by (rewrite /L1; apply upd_eq).
      assert (HcsL1 : callee_saved W0 L1)
        by (rewrite /L1; apply callee_saved_insert_r; [vm_compute; reflexivity | exact HcsM]).
      assert (HthrL1 : forall r : mword 5, is_cs_idx r = true -> L1 !!! Regidx r = M !!! Regidx r).
      { intros r Hr.
        assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /L1 upd_ne; [| congruence]. reflexivity. }
      iAssert (pipe_res γp pi) with "[Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack]" as "Hres".
      { iExists nr1, nw1, ro1, wo1, vnm1, bs1.
        iFrame "Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack". iPureIntro. split; assumption. }
      iPoseProof (pri_38 with "Htext") as "Hi38".
      destruct (eq_vec (sign_extend' 64 wo1 : mword 64) (zero_reg : mword 64)) eqn:Hwoz.
      { (* ==== the write end is CLOSED: c.beqz taken -> +0x70 ==== *)
        iApply (wp_cbeqz_taken_s_sconf γ Φ (mword_of_int (PR + 0x38)) (mword_of_int 28 : mword 8)
                  (Cregidx (mword_of_int 7)) Ra5 L1 (av - 12)%nat
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rewrite HL1a5; exact Hwoz) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi38 [-]").
        iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Hj70 : add_vec (mword_of_int (PR + 0x38) : mword 64)
                         (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0"))))
                       = mword_of_int (PR + 0x70)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hj70) in "Hpc".
        assert (HL1csp : L1 !!! Regidx csp_rs1 = spr)
          by (rewrite (HthrL1 csp_rs1 ltac:(vm_compute; reflexivity)); exact HMcsp).
        assert (HL1s6 : L1 !!! Regidx Rs6 = vs6)
          by (rewrite (HthrL1 Rs6 ltac:(vm_compute; reflexivity)); exact HMs6).
        assert (HL1s7 : L1 !!! Regidx Rs7 = vs7)
          by (rewrite (HthrL1 Rs7 ltac:(vm_compute; reflexivity)); exact HMs7).
        assert (HL1s8 : L1 !!! Regidx Rs8 = vs8)
          by (rewrite (HthrL1 Rs8 ltac:(vm_compute; reflexivity)); exact HMs8).
        iDestruct "Hq8" as (y8) "Hc8". iDestruct "Hq9" as (y9) "Hc9".
        iDestruct "Hq10" as (y10) "Hc10".
        iPoseProof (pri_70 with "Htext") as "Hi70".
        iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PR + 0x70)) (mword_of_int 4 : mword 6) Rs6
                  L1 (av - 12)%nat y8 with "Hcg Hpc Hi70 [Hc8] [-]").
        { iEval (rewrite HL1csp -Hb8). iExact "Hc8". }
        iIntros "Hcg Hpc Hc8". iEval (rewrite HL1csp -Hb8 HL1s6) in "Hc8".
        assert (Hw72 : add_vec_int (mword_of_int (PR + 0x70) : mword 64) 2 = mword_of_int (PR + 0x72))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hw72) in "Hpc".
        iPoseProof (pri_72 with "Htext") as "Hi72".
        iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PR + 0x72)) (mword_of_int 3 : mword 6) Rs7
                  L1 (av - 12)%nat y9 with "Hcg Hpc Hi72 [Hc9] [-]").
        { iEval (rewrite HL1csp -Hb9). iExact "Hc9". }
        iIntros "Hcg Hpc Hc9". iEval (rewrite HL1csp -Hb9 HL1s7) in "Hc9".
        assert (Hw74 : add_vec_int (mword_of_int (PR + 0x72) : mword 64) 2 = mword_of_int (PR + 0x74))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hw74) in "Hpc".
        iPoseProof (pri_74 with "Htext") as "Hi74".
        iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PR + 0x74)) (mword_of_int 2 : mword 6) Rs8
                  L1 (av - 12)%nat y10 with "Hcg Hpc Hi74 [Hc10] [-]").
        { iEval (rewrite HL1csp -Hb10). iExact "Hc10". }
        iIntros "Hcg Hpc Hc10". iEval (rewrite HL1csp -Hb10 HL1s8) in "Hc10".
        assert (Hw76 : add_vec_int (mword_of_int (PR + 0x74) : mword 64) 2 = mword_of_int (PR + 0x76))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hw76) in "Hpc".
        iDestruct "HEX" as "[_ HCP]". iEval (rewrite /CPP) in "HCP".
        iApply ("HCP" $! L1 with "[%] Hcg Hpc Hown Hpay Hlocked Hres Href Hpriv Hctx Hsched Hc8 Hc9 Hc10 Hq11 Hq12").
        split_and!.
        - exact HL1csp.
        - rewrite (HthrL1 Rs0 ltac:(vm_compute; reflexivity)). exact HMs0.
        - rewrite (HthrL1 Rs1 ltac:(vm_compute; reflexivity)). exact HMs1.
        - rewrite (HthrL1 Rs2 ltac:(vm_compute; reflexivity)). exact HMs2.
        - rewrite (HthrL1 Rs4 ltac:(vm_compute; reflexivity)). exact HMs4.
        - rewrite (HthrL1 Rs5 ltac:(vm_compute; reflexivity)). exact HMs5.
        - rewrite (HthrL1 Rtp ltac:(vm_compute; reflexivity)). exact HMtp.
        - rewrite (HthrL1 Rs9 ltac:(vm_compute; reflexivity)). exact HMs9.
        - rewrite (HthrL1 Rs10 ltac:(vm_compute; reflexivity)). exact HMs10.
        - rewrite (HthrL1 Rs11 ltac:(vm_compute; reflexivity)). exact HMs11. }
      (* ==== the write end is still OPEN: fall to +0x3a, test killed ==== *)
      iApply (wp_cbeqz_fall_s_sconf γ Φ (mword_of_int (PR + 0x38)) (mword_of_int 28 : mword 8)
                (Cregidx (mword_of_int 7)) Ra5 L1 (av - 12)%nat
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rewrite HL1a5; exact Hwoz) with "Hcg Hpc Hi38 [-]").
      iIntros "Hcg Hpc".
      assert (Hw3a : add_vec_int (mword_of_int (PR + 0x38) : mword 64) 2 = mword_of_int (PR + 0x3a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hw3a) in "Hpc".
      (* 0x3a c.mv a0,s4 *)
      iPoseProof (pri_3a with "Htext") as "Hi3a".
      iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PR + 0x3a)) Ra0 Rs4 L1 (av - 12)%nat
                ltac:(nz) ltac:(nz) with "Hcg Hpc Hi3a [-]").
      iIntros "Hcg Hpc".
      set (L2 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (L1 !!! Regidx Rs4))]> L1).
      change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (L1 !!! Regidx Rs4))]> L1) with L2.
      assert (Hw3c : add_vec_int (mword_of_int (PR + 0x3a) : mword 64) 2 = mword_of_int (PR + 0x3c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hw3c) in "Hpc".
      (* 0x3c jal killed *)
      iPoseProof (pri_3c with "Htext") as "Hi3c".
      iApply (wp_jal_s_sconf γ Φ (mword_of_int (PR + 0x3c)) Rra (mword_of_int 2087792 : mword 21)
                L2 (av - 12)%nat ltac:(nz) ltac:(nz) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi3c [-]").
      iIntros "Hcg Hpc".
      set (L3 := <[Regidx Rra := regval_into_reg
          (add_vec_int (mword_of_int (PR + 0x3c) : mword 64) 4)]> L2).
      change (<[Regidx Rra := regval_into_reg
          (add_vec_int (mword_of_int (PR + 0x3c) : mword 64) 4)]> L2) with L3.
      assert (Hjkl : add_vec (mword_of_int (PR + 0x3c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2087792 : mword 21)) = mword_of_int KernelSyms.killed)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjkl) in "Hpc".
      assert (HL3a0 : L3 !!! Regidx Ra0 = proc_addr j).
      { rewrite /L3 upd_ne; [| reg_neq]. rewrite /L2 upd_eq. unfold regval_into_reg.
        rewrite (HthrL1 Rs4 ltac:(vm_compute; reflexivity)) HMs4. apply add_vec_zero_l. }
      assert (HL3tp : L3 !!! Regidx Rtp = cid_word).
      { rewrite /L3 upd_ne; [| reg_neq]. rewrite /L2 upd_ne; [| reg_neq].
        rewrite (HthrL1 Rtp ltac:(vm_compute; reflexivity)). exact HMtp. }
      assert (HL3ra : L3 !!! Regidx Rra = add_vec_int (mword_of_int (PR + 0x3c) : mword 64) 4)
        by (rewrite /L3; apply upd_eq).
      assert (HcsML3 : callee_saved M L3).
      { rewrite /L3 /L2 /L1.
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_refl. }
      iApply (Killed.wp_killed_sconf γ Φ γs j γlp L3 (av - 12)%nat 1%nat eb pj C
                HL3a0 HL3tp Hj Hjl pr_lvl1 ltac:(lia)
                with "Hcg Hown Htext Hpc Hpinv Hpanic [-]").
      iIntros (mk kl) "[%Hkcs %Hka0] Hcg Hown Hpc".
      iEval (rewrite HL3ra) in "Hpc".
      assert (Hw40 : ret_pc (add_vec_int (mword_of_int (PR + 0x3c) : mword 64) 4)
                     = (mword_of_int (PR + 0x40) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hw40) in "Hpc".
      assert (HcsMmk : callee_saved M mk) by (apply (callee_saved_trans M L3 mk HcsML3 Hkcs)).
      assert (Hmks1 : mk !!! Regidx Rs1 = pi)
        by (rewrite (callee_saved_lookup HcsMmk Rs1 ltac:(vm_compute; reflexivity)); exact HMs1).
      assert (Hmks3 : mk !!! Regidx Rs3 = a_pnread pi)
        by (rewrite (callee_saved_lookup HcsMmk Rs3 ltac:(vm_compute; reflexivity)); exact HMs3).
      assert (Hmktp : mk !!! Regidx Rtp = cid_word)
        by (rewrite (callee_saved_lookup HcsMmk Rtp ltac:(vm_compute; reflexivity)); exact HMtp).
      iPoseProof (pri_40 with "Htext") as "Hi40".
      destruct (neq_vec (sign_extend' 64 kl : mword 64) (zero_reg : mword 64)) eqn:Hkz.
      { (* ==== KILLED: c.bnez taken -> +0x66, release and return -1 ==== *)
        iApply (wp_cbnez_taken_s_sconf γ Φ (mword_of_int (PR + 0x40)) (mword_of_int 19 : mword 8)
                  (Cregidx (mword_of_int 2)) Ra0 mk (av - 12)%nat
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rewrite Hka0; exact Hkz) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi40 [-]").
        iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Hj66 : add_vec (mword_of_int (PR + 0x40) : mword 64)
                         (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 19 : mword 8) ('b"0"))))
                       = mword_of_int (PR + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hj66) in "Hpc".
        (* 0x66 c.mv a0,s1 *)
        iPoseProof (pri_66 with "Htext") as "Hi66".
        iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PR + 0x66)) Ra0 Rs1 mk (av - 12)%nat
                  ltac:(nz) ltac:(nz) with "Hcg Hpc Hi66 [-]").
        iIntros "Hcg Hpc".
        set (N1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mk !!! Regidx Rs1))]> mk).
        change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mk !!! Regidx Rs1))]> mk) with N1.
        assert (Hw68 : add_vec_int (mword_of_int (PR + 0x66) : mword 64) 2 = mword_of_int (PR + 0x68))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hw68) in "Hpc".
        (* 0x68 jal release *)
        iPoseProof (pri_68 with "Htext") as "Hi68".
        iApply (wp_jal_s_sconf γ Φ (mword_of_int (PR + 0x68)) Rra (mword_of_int 2082450 : mword 21)
                  N1 (av - 12)%nat ltac:(nz) ltac:(nz) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi68 [-]").
        iIntros "Hcg Hpc".
        set (N2 := <[Regidx Rra := regval_into_reg
            (add_vec_int (mword_of_int (PR + 0x68) : mword 64) 4)]> N1).
        change (<[Regidx Rra := regval_into_reg
            (add_vec_int (mword_of_int (PR + 0x68) : mword 64) 4)]> N1) with N2.
        assert (Hjrl1 : add_vec (mword_of_int (PR + 0x68) : mword 64)
                          (sign_extend' 64 (mword_of_int 2082450 : mword 21)) = mword_of_int KernelSyms.release)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjrl1) in "Hpc".
        assert (HN2a0 : N2 !!! Regidx Ra0 = pi).
        { rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_eq. unfold regval_into_reg.
          rewrite Hmks1. apply add_vec_zero_l. }
        assert (HN2tp : N2 !!! Regidx Rtp = cid_word).
        { rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_ne; [| reg_neq]. exact Hmktp. }
        assert (HN2ra : N2 !!! Regidx Rra = add_vec_int (mword_of_int (PR + 0x68) : mword 64) 4)
          by (rewrite /N2; apply upd_eq).
        assert (HN2lka : add_vec (N2 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pi).
        { rewrite HN2a0.
          replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
            by (apply bv_eq; vm_compute; reflexivity).
          apply kv_addv_zero. }
        assert (HcsMN2 : callee_saved M N2).
        { rewrite /N2 /N1.
          apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_insert_r; [vm_compute; reflexivity|]. exact HcsMmk. }
        iApply (ReleaseGen.wp_release_gen_sconf γ Φ γl pi (pipe_res γp pi) (pipe_dead γl γp) emp%I
                  N2 0%nat eb pj C (av - 12)%nat HN2lka HN2tp ltac:(lia)
                  ltac:(iApply locked_dead) ltac:(iApply locked_pre_dead)
                  with "Hcg Htext Hpc Hopen Hlocked Hres [] Hown Hpay [-]").
        { iApply lock_finisher_close. }
        iIntros (mrl) "_ Hcg Hpc %Hcsrl Hown".
        iEval (rewrite HN2ra) in "Hpc".
        assert (Hw6c : ret_pc (add_vec_int (mword_of_int (PR + 0x68) : mword 64) 4)
                       = (mword_of_int (PR + 0x6c) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hw6c) in "Hpc".
        assert (HcsMmrl : callee_saved M mrl) by (apply (callee_saved_trans M N2 mrl HcsMN2 Hcsrl)).
        (* 0x6c c.li s3,-1 *)
        iPoseProof (pri_6c with "Htext") as "Hi6c".
        iApply (wp_cli_s_sconf γ Φ (mword_of_int (PR + 0x6c)) Rs3 (mword_of_int 63 : mword 6)
                  (mword_of_int (-1) : mword 64) mrl (av - 12)%nat ltac:(nz) ltac:(nz)
                  ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi6c [-]").
        iIntros "Hcg Hpc".
        set (N3 := <[Regidx Rs3 := regval_into_reg (mword_of_int (-1) : mword 64)]> mrl).
        change (<[Regidx Rs3 := regval_into_reg (mword_of_int (-1) : mword 64)]> mrl) with N3.
        assert (Hw6e : add_vec_int (mword_of_int (PR + 0x6c) : mword 64) 2 = mword_of_int (PR + 0x6e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hw6e) in "Hpc".
        (* 0x6e c.j -> the epilogue at +0xd6 *)
        iPoseProof (pri_6e with "Htext") as "Hi6e".
        iApply (wp_cj_s_sconf γ Φ (mword_of_int (PR + 0x6e))
                  (sign_extend' 21 (concat_vec (mword_of_int 52 : mword 11) ('b"0")))
                  N3 (av - 12)%nat ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi6e [-]").
        iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Hjd6 : add_vec (mword_of_int (PR + 0x6e) : mword 64)
                         (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 52 : mword 11) ('b"0"))))
                       = mword_of_int (PR + 0xd6)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjd6) in "Hpc".
        iDestruct (proc_priv_copy with "Hpriv") as "(Hszc & Hptc & Hpt & Hpback)".
        iAssert (⌜uptd_ext_sz (pv_sz V) (pv_upt V) (pv_upt V)⌝)%I as "#Hxr"; [iPureIntro; apply uptd_ext_sz_refl|].
        iDestruct ("Hpback" $! (pv_upt V) with "Hxr Hszc Hptc Hpt") as "Hpriv".
        iDestruct "HEX" as "[HEPI _]". iEval (rewrite /EPIC) in "HEPI".
        iApply ("HEPI" $! N3 (pv_upt V) (mword_of_int (-1))
                  with "[%] [%] [%] Hcg Hpc Hown Href Hpriv Hctx Hsched
                       Hq8 Hq9 Hq10 Hq11 Hq12").
        { split_and!.
          - rewrite /N3 upd_ne; [| reg_neq].
            rewrite (callee_saved_lookup HcsMmrl csp_rs1 ltac:(vm_compute; reflexivity)). exact HMcsp.
          - rewrite /N3 upd_eq. reflexivity.
          - rewrite /N3 upd_ne; [| reg_neq].
            rewrite (callee_saved_lookup HcsMmrl Rtp ltac:(vm_compute; reflexivity)). exact HMtp.
          - rewrite /N3 upd_ne; [| reg_neq].
            rewrite (callee_saved_lookup HcsMmrl Rs6 ltac:(vm_compute; reflexivity)). exact HMs6.
          - rewrite /N3 upd_ne; [| reg_neq].
            rewrite (callee_saved_lookup HcsMmrl Rs7 ltac:(vm_compute; reflexivity)). exact HMs7.
          - rewrite /N3 upd_ne; [| reg_neq].
            rewrite (callee_saved_lookup HcsMmrl Rs8 ltac:(vm_compute; reflexivity)). exact HMs8.
          - rewrite /N3 upd_ne; [| reg_neq].
            rewrite (callee_saved_lookup HcsMmrl Rs9 ltac:(vm_compute; reflexivity)). exact HMs9.
          - rewrite /N3 upd_ne; [| reg_neq].
            rewrite (callee_saved_lookup HcsMmrl Rs10 ltac:(vm_compute; reflexivity)). exact HMs10.
          - rewrite /N3 upd_ne; [| reg_neq].
            rewrite (callee_saved_lookup HcsMmrl Rs11 ltac:(vm_compute; reflexivity)). exact HMs11. }
        { apply uptd_ext_refl. }
        { apply pr_ret_neg1. } }
      (* ==== NOT killed: sleep on &pi->nread ==== *)
      iApply (wp_cbnez_fall_s_sconf γ Φ (mword_of_int (PR + 0x40)) (mword_of_int 19 : mword 8)
                (Cregidx (mword_of_int 2)) Ra0 mk (av - 12)%nat
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rewrite Hka0; exact Hkz) with "Hcg Hpc Hi40 [-]").
      iIntros "Hcg Hpc".
      assert (Hw42 : add_vec_int (mword_of_int (PR + 0x40) : mword 64) 2 = mword_of_int (PR + 0x42))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hw42) in "Hpc".
      (* 0x42 c.mv a1,s1 ; 0x44 c.mv a0,s3 *)
      iPoseProof (pri_42 with "Htext") as "Hi42".
      iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PR + 0x42)) Ra1 Rs1 mk (av - 12)%nat
                ltac:(nz) ltac:(nz) with "Hcg Hpc Hi42 [-]").
      iIntros "Hcg Hpc".
      set (L4 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (mk !!! Regidx Rs1))]> mk).
      change (<[Regidx Ra1 := regval_into_reg (add_vec zero_reg (mk !!! Regidx Rs1))]> mk) with L4.
      assert (Hw44 : add_vec_int (mword_of_int (PR + 0x42) : mword 64) 2 = mword_of_int (PR + 0x44))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hw44) in "Hpc".
      iPoseProof (pri_44 with "Htext") as "Hi44".
      iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PR + 0x44)) Ra0 Rs3 L4 (av - 12)%nat
                ltac:(nz) ltac:(nz) with "Hcg Hpc Hi44 [-]").
      iIntros "Hcg Hpc".
      set (L5 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (L4 !!! Regidx Rs3))]> L4).
      change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (L4 !!! Regidx Rs3))]> L4) with L5.
      assert (Hw46 : add_vec_int (mword_of_int (PR + 0x44) : mword 64) 2 = mword_of_int (PR + 0x46))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hw46) in "Hpc".
      (* 0x46 jal sleep *)
      iPoseProof (pri_46 with "Htext") as "Hi46".
      iApply (wp_jal_s_sconf γ Φ (mword_of_int (PR + 0x46)) Rra (mword_of_int 2087210 : mword 21)
                L5 (av - 12)%nat ltac:(nz) ltac:(nz) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi46 [-]").
      iIntros "Hcg Hpc".
      set (L6 := <[Regidx Rra := regval_into_reg
          (add_vec_int (mword_of_int (PR + 0x46) : mword 64) 4)]> L5).
      change (<[Regidx Rra := regval_into_reg
          (add_vec_int (mword_of_int (PR + 0x46) : mword 64) 4)]> L5) with L6.
      assert (Hjsl : add_vec (mword_of_int (PR + 0x46) : mword 64)
                       (sign_extend' 64 (mword_of_int 2087210 : mword 21)) = mword_of_int KernelSyms.sleep)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjsl) in "Hpc".
      assert (HL6a1 : L6 !!! Regidx Ra1 = pi).
      { rewrite /L6 upd_ne; [| reg_neq]. rewrite /L5 upd_ne; [| reg_neq].
        rewrite /L4 upd_eq. unfold regval_into_reg. rewrite Hmks1. apply add_vec_zero_l. }
      assert (HL6tp : L6 !!! Regidx Rtp = cid_word).
      { rewrite /L6 upd_ne; [| reg_neq]. rewrite /L5 upd_ne; [| reg_neq].
        rewrite /L4 upd_ne; [| reg_neq]. exact Hmktp. }
      assert (HL6ra : L6 !!! Regidx Rra = add_vec_int (mword_of_int (PR + 0x46) : mword 64) 4)
        by (rewrite /L6; apply upd_eq).
      assert (HL6lka : add_vec (L6 !!! Regidx Ra1) (sign_extend' 64 (mword_of_int 0 : mword 12)) = pi).
      { rewrite HL6a1.
        replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
          by (apply bv_eq; vm_compute; reflexivity).
        apply kv_addv_zero. }
      assert (HcsMkL6 : callee_saved mk L6).
      { rewrite /L6 /L5 /L4.
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_refl. }
      iApply (SleepGen.wp_sleep_gen_sconf γ Φ γs j γlp γl pi (pipe_res γp pi)
                (pipe_ref γp w q) (pipe_dead γl γp) L6 (av - 12)%nat eb C
                HL6tp Hj Hjl HL6lka ltac:(lia)
                ltac:(iApply pipe_ref_dead) ltac:(iApply locked_dead) ltac:(iApply locked_pre_dead)
                with "Hcg Hown Hpay Htext Hpc Hpinv Hopen Href Hlocked Hres Hpanic Hctx Hsched [-]").
      iIntros (mfs) "%Hscs Hcg Hown Hpay Hpc Href Hlocked Hres Hctx Hsched".
      iEval (rewrite HL6ra) in "Hpc".
      assert (Hw4a : ret_pc (add_vec_int (mword_of_int (PR + 0x46) : mword 64) 4)
                     = (mword_of_int (PR + 0x4a) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hw4a) in "Hpc".
      assert (HcsMmfs : callee_saved M mfs).
      { apply (callee_saved_trans M mk mfs HcsMmk).
        apply (callee_saved_trans mk L6 mfs HcsMkL6 Hscs). }
      assert (Hmfss1 : mfs !!! Regidx Rs1 = pi)
        by (rewrite (callee_saved_lookup HcsMmfs Rs1 ltac:(vm_compute; reflexivity)); exact HMs1).
      (* 0x4a lw a4,536(s1) ; 0x4e lw a5,540(s1) *)
      iDestruct "Hres" as (nr2 nw2 ro2 wo2 vnm2 bs2)
        "(Hnm & Hnr & Hnw & Hro & Hwo & Hst0 & Hst1 & %Hcnt2 & %Hlen2 & Hdat & Hslack)".
      assert (Hnra4 : add_vec (mfs !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 536 : mword 12))
                      = a_pnread pi) by (rewrite Hmfss1; reflexivity).
      iPoseProof (pri_4a with "Htext") as "Hi4a".
      iApply (wp_lw_s_sconf γ Φ (mword_of_int (PR + 0x4a)) Ra4 Rs1 (mword_of_int 536 : mword 12)
                mfs (av - 12)%nat nr2 ltac:(nz) ltac:(nz) with "Hcg Hpc Hi4a [Hnr] [-]").
      { iEval (rewrite Hnra4). iExact "Hnr". }
      iIntros "Hcg Hpc Hnr". iEval (rewrite Hnra4) in "Hnr".
      set (L7 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 nr2)]> mfs).
      change (<[Regidx Ra4 := regval_into_reg (sign_extend' 64 nr2)]> mfs) with L7.
      assert (Hw4e : add_vec_int (mword_of_int (PR + 0x4a) : mword 64) 4 = mword_of_int (PR + 0x4e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hw4e) in "Hpc".
      assert (HL7s1 : L7 !!! Regidx Rs1 = pi) by (rewrite /L7 upd_ne; [exact Hmfss1 | reg_neq]).
      assert (Hnwa4 : add_vec (L7 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 540 : mword 12))
                      = a_pnwrite pi) by (rewrite HL7s1; reflexivity).
      iPoseProof (pri_4e with "Htext") as "Hi4e".
      iApply (wp_lw_s_sconf γ Φ (mword_of_int (PR + 0x4e)) Ra5 Rs1 (mword_of_int 540 : mword 12)
                L7 (av - 12)%nat nw2 ltac:(nz) ltac:(nz) with "Hcg Hpc Hi4e [Hnw] [-]").
      { iEval (rewrite Hnwa4). iExact "Hnw". }
      iIntros "Hcg Hpc Hnw". iEval (rewrite Hnwa4) in "Hnw".
      set (L8 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 nw2)]> L7).
      change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 nw2)]> L7) with L8.
      assert (Hw52 : add_vec_int (mword_of_int (PR + 0x4e) : mword 64) 4 = mword_of_int (PR + 0x52))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hw52) in "Hpc".
      assert (HL8a4 : L8 !!! Regidx Ra4 = sign_extend' 64 nr2).
      { rewrite /L8 upd_ne; [| reg_neq]. rewrite /L7 upd_eq. reflexivity. }
      assert (HL8a5 : L8 !!! Regidx Ra5 = sign_extend' 64 nw2) by (rewrite /L8; apply upd_eq).
      assert (HcsWL8 : callee_saved W0 L8).
      { apply (callee_saved_trans W0 M L8 HcsM).
        apply (callee_saved_trans M mfs L8 HcsMmfs).
        rewrite /L8 /L7.
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_refl. }
      assert (HthrL8 : forall r : mword 5, is_cs_idx r = true -> L8 !!! Regidx r = M !!! Regidx r).
      { intros r Hr.
        assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /L8 upd_ne; [| congruence]. rewrite /L7 upd_ne; [| congruence].
        exact (callee_saved_lookup HcsMmfs r Hr). }
      iAssert (pipe_res γp pi) with "[Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack]" as "Hres".
      { iExists nr2, nw2, ro2, wo2, vnm2, bs2.
        iFrame "Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack". iPureIntro. split; assumption. }
      iPoseProof (pri_52 with "Htext") as "Hi52".
      destruct (eq_vec (sign_extend' 64 nr2 : mword 64) (sign_extend' 64 nw2)) eqn:Hstill.
      { (* still empty: the BACK EDGE to +0x34 *)
        iApply (wp_beq_taken_s_sconf γ Φ (mword_of_int (PR + 0x52)) (mword_of_int 8162 : mword 13)
                  Ra5 Ra4 L8 (av - 12)%nat ltac:(nz) ltac:(nz)
                  ltac:(rewrite HL8a4 HL8a5; exact Hstill) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi52 [-]").
        (* THE ONE SITE IN THIS FILE THAT STILL NEEDS A REAL [iNext]: the Löb
           back edge below applies "IH" and "HEX", so the [▷] has to come off
           THOSE, not just off the goal.  Stripping [▷ sched_vc] with them is
           the price, hence the re-introduction on the next two lines.  Every
           other instruction step here wants only the goal's later gone and
           uses [iApply bi.later_intro], which never walks the context (~0.06 s
           against [iNext]'s ~1.1 s — see optimization.md). *)
        iNext. iIntros "Hcg Hpc".
        iAssert (▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj)%I with "[Hsched]" as "Hsched".
        { iApply bi.later_intro. iExact "Hsched". }
        assert (Hbk34 : add_vec (mword_of_int (PR + 0x52) : mword 64)
                          (sign_extend' 64 (mword_of_int 8162 : mword 13)) = mword_of_int (PR + 0x34))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hbk34) in "Hpc".
        iApply ("IH" $! L8 with "[%] HEX Hcg Hpc Hown Hpay Hlocked Hres Href Hpriv Hctx Hsched Hq8 Hq9 Hq10 Hq11 Hq12").
        exact HcsWL8. }
      (* data arrived: fall to +0x56, save s6..s8 and jump to the copy phase *)
      iApply (wp_beq_fall_s_sconf γ Φ (mword_of_int (PR + 0x52)) (mword_of_int 8162 : mword 13)
                Ra5 Ra4 L8 (av - 12)%nat ltac:(nz) ltac:(nz)
                ltac:(rewrite HL8a4 HL8a5; exact Hstill) with "Hcg Hpc Hi52 [-]").
      iIntros "Hcg Hpc".
      assert (Hw56 : add_vec_int (mword_of_int (PR + 0x52) : mword 64) 4 = mword_of_int (PR + 0x56))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hw56) in "Hpc".
      assert (HL8csp : L8 !!! Regidx csp_rs1 = spr)
        by (rewrite (HthrL8 csp_rs1 ltac:(vm_compute; reflexivity)); exact HMcsp).
      assert (HL8s6 : L8 !!! Regidx Rs6 = vs6)
        by (rewrite (HthrL8 Rs6 ltac:(vm_compute; reflexivity)); exact HMs6).
      assert (HL8s7 : L8 !!! Regidx Rs7 = vs7)
        by (rewrite (HthrL8 Rs7 ltac:(vm_compute; reflexivity)); exact HMs7).
      assert (HL8s8 : L8 !!! Regidx Rs8 = vs8)
        by (rewrite (HthrL8 Rs8 ltac:(vm_compute; reflexivity)); exact HMs8).
      iDestruct "Hq8" as (z8) "Hc8". iDestruct "Hq9" as (z9) "Hc9".
      iDestruct "Hq10" as (z10) "Hc10".
      iPoseProof (pri_56 with "Htext") as "Hi56".
      iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PR + 0x56)) (mword_of_int 4 : mword 6) Rs6
                L8 (av - 12)%nat z8 with "Hcg Hpc Hi56 [Hc8] [-]").
      { iEval (rewrite HL8csp -Hb8). iExact "Hc8". }
      iIntros "Hcg Hpc Hc8". iEval (rewrite HL8csp -Hb8 HL8s6) in "Hc8".
      assert (Hw58 : add_vec_int (mword_of_int (PR + 0x56) : mword 64) 2 = mword_of_int (PR + 0x58))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hw58) in "Hpc".
      iPoseProof (pri_58 with "Htext") as "Hi58".
      iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PR + 0x58)) (mword_of_int 3 : mword 6) Rs7
                L8 (av - 12)%nat z9 with "Hcg Hpc Hi58 [Hc9] [-]").
      { iEval (rewrite HL8csp -Hb9). iExact "Hc9". }
      iIntros "Hcg Hpc Hc9". iEval (rewrite HL8csp -Hb9 HL8s7) in "Hc9".
      assert (Hw5a : add_vec_int (mword_of_int (PR + 0x58) : mword 64) 2 = mword_of_int (PR + 0x5a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hw5a) in "Hpc".
      iPoseProof (pri_5a with "Htext") as "Hi5a".
      iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PR + 0x5a)) (mword_of_int 2 : mword 6) Rs8
                L8 (av - 12)%nat z10 with "Hcg Hpc Hi5a [Hc10] [-]").
      { iEval (rewrite HL8csp -Hb10). iExact "Hc10". }
      iIntros "Hcg Hpc Hc10". iEval (rewrite HL8csp -Hb10 HL8s8) in "Hc10".
      assert (Hw5c : add_vec_int (mword_of_int (PR + 0x5a) : mword 64) 2 = mword_of_int (PR + 0x5c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hw5c) in "Hpc".
      iPoseProof (pri_5c with "Htext") as "Hi5c".
      iApply (wp_cj_s_sconf γ Φ (mword_of_int (PR + 0x5c))
                (sign_extend' 21 (concat_vec (mword_of_int 13 : mword 11) ('b"0")))
                L8 (av - 12)%nat ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi5c [-]").
      iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Hj76 : add_vec (mword_of_int (PR + 0x5c) : mword 64)
                       (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 13 : mword 11) ('b"0"))))
                     = mword_of_int (PR + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hj76) in "Hpc".
      iDestruct "HEX" as "[_ HCP]". iEval (rewrite /CPP) in "HCP".
      iApply ("HCP" $! L8 with "[%] Hcg Hpc Hown Hpay Hlocked Hres Href Hpriv Hctx Hsched Hc8 Hc9 Hc10 Hq11 Hq12").
      split_and!.
      - exact HL8csp.
      - rewrite (HthrL8 Rs0 ltac:(vm_compute; reflexivity)). exact HMs0.
      - rewrite (HthrL8 Rs1 ltac:(vm_compute; reflexivity)). exact HMs1.
      - rewrite (HthrL8 Rs2 ltac:(vm_compute; reflexivity)). exact HMs2.
      - rewrite (HthrL8 Rs4 ltac:(vm_compute; reflexivity)). exact HMs4.
      - rewrite (HthrL8 Rs5 ltac:(vm_compute; reflexivity)). exact HMs5.
      - rewrite (HthrL8 Rtp ltac:(vm_compute; reflexivity)). exact HMtp.
      - rewrite (HthrL8 Rs9 ltac:(vm_compute; reflexivity)). exact HMs9.
      - rewrite (HthrL8 Rs10 ltac:(vm_compute; reflexivity)). exact HMs10.
      - rewrite (HthrL8 Rs11 ltac:(vm_compute; reflexivity)). exact HMs11. }
    (* ============ 0x30 bne a4,a5: the entry dispatch ============ *)
    iAssert (pipe_res γp pi) with "[Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack]" as "Hres".
    { iExists nr0, nw0, ro0, wo0, vnm0, bs0.
      iFrame "Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack". iPureIntro. split; assumption. }
    iPoseProof (pri_30 with "Htext") as "Hi30".
    destruct (neq_vec (sign_extend' 64 nr0 : mword 64) (sign_extend' 64 nw0)) eqn:Hdisp.
    { (* data already available: taken -> +0x5e *)
      iApply (wp_bne_taken_s_sconf γ Φ (mword_of_int (PR + 0x30)) (mword_of_int 46 : mword 13)
                Ra5 Ra4 W0 (av - 12)%nat ltac:(nz) ltac:(nz)
                ltac:(rewrite HW0a4 HW0a5; exact Hdisp) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi30 [-]").
      iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Hj5e : add_vec (mword_of_int (PR + 0x30) : mword 64)
                       (sign_extend' 64 (mword_of_int 46 : mword 13)) = mword_of_int (PR + 0x5e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hj5e) in "Hpc".
      iDestruct "Q8" as (z8) "Hc8". iDestruct "Q9" as (z9) "Hc9".
      iDestruct "Q10" as (z10) "Hc10".
      iPoseProof (pri_5e with "Htext") as "Hi5e".
      iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PR + 0x5e)) (mword_of_int 4 : mword 6) Rs6
                W0 (av - 12)%nat z8 with "Hcg Hpc Hi5e [Hc8] [-]").
      { iEval (rewrite HW0csp -Hb8). iExact "Hc8". }
      iIntros "Hcg Hpc Hc8". iEval (rewrite HW0csp -Hb8 HW0s6) in "Hc8".
      assert (Hd60 : add_vec_int (mword_of_int (PR + 0x5e) : mword 64) 2 = mword_of_int (PR + 0x60))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hd60) in "Hpc".
      iPoseProof (pri_60 with "Htext") as "Hi60".
      iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PR + 0x60)) (mword_of_int 3 : mword 6) Rs7
                W0 (av - 12)%nat z9 with "Hcg Hpc Hi60 [Hc9] [-]").
      { iEval (rewrite HW0csp -Hb9). iExact "Hc9". }
      iIntros "Hcg Hpc Hc9". iEval (rewrite HW0csp -Hb9 HW0s7) in "Hc9".
      assert (Hd62 : add_vec_int (mword_of_int (PR + 0x60) : mword 64) 2 = mword_of_int (PR + 0x62))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hd62) in "Hpc".
      iPoseProof (pri_62 with "Htext") as "Hi62".
      iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PR + 0x62)) (mword_of_int 2 : mword 6) Rs8
                W0 (av - 12)%nat z10 with "Hcg Hpc Hi62 [Hc10] [-]").
      { iEval (rewrite HW0csp -Hb10). iExact "Hc10". }
      iIntros "Hcg Hpc Hc10". iEval (rewrite HW0csp -Hb10 HW0s8) in "Hc10".
      assert (Hd64 : add_vec_int (mword_of_int (PR + 0x62) : mword 64) 2 = mword_of_int (PR + 0x64))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hd64) in "Hpc".
      iPoseProof (pri_64 with "Htext") as "Hi64".
      iApply (wp_cj_s_sconf γ Φ (mword_of_int (PR + 0x64))
                (sign_extend' 21 (concat_vec (mword_of_int 9 : mword 11) ('b"0")))
                W0 (av - 12)%nat ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi64 [-]").
      iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Hj76b : add_vec (mword_of_int (PR + 0x64) : mword 64)
                        (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 9 : mword 11) ('b"0"))))
                      = mword_of_int (PR + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hj76b) in "Hpc".
      iDestruct "EXITS" as "[_ HCP]". iEval (rewrite /CPP) in "HCP".
      iApply ("HCP" $! W0 with "[%] Hcg Hpc Hown Hpay Hlocked Hres Href Hpriv Hctx Hsched Hc8 Hc9 Hc10 Q11 Q12").
      split_and!; try assumption. }
    (* the pipe is empty: fall into the wait loop *)
    iApply (wp_bne_fall_s_sconf γ Φ (mword_of_int (PR + 0x30)) (mword_of_int 46 : mword 13)
              Ra5 Ra4 W0 (av - 12)%nat ltac:(nz) ltac:(nz)
              ltac:(rewrite HW0a4 HW0a5; exact Hdisp) with "Hcg Hpc Hi30 [-]").
    iIntros "Hcg Hpc".
    assert (Hd34 : add_vec_int (mword_of_int (PR + 0x30) : mword 64) 4 = mword_of_int (PR + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hd34) in "Hpc".
    iApply ("WLOOP" $! W0 with "[%] EXITS Hcg Hpc Hown Hpay Hlocked Hres Href Hpriv Hctx Hsched Q8 Q9 Q10 Q11 Q12").
    apply callee_saved_refl.
  Qed.


End ProofPiperead.

End PipereadProof.
