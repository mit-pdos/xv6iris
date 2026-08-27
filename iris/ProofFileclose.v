(* ProofFileclose.v -- fileclose over the SIE-agnostic sconf world.

     acquire(&ftable.lock);
     if (f->ref < 1) panic("fileclose");
     if (--f->ref > 0) { release(&ftable.lock); return; }
     ff = *f; f->ref = 0; f->type = FD_NONE;
     release(&ftable.lock);
     if (ff.type == FD_PIPE) pipeclose(ff.pipe, ff.writable);
     else if (ff.type == FD_INODE || ff.type == FD_DEVICE) {
       begin_op(); iput(ff.ip); end_op();
     }

   The two blocks the five exits share -- the epilogue at +0x8e and the
   [ld s2..s5; j] gcc emitted three times -- are [ProofFilecloseParts.v], so
   what is left here is the function's own control flow and its ghost steps.

   THE THREE THINGS THE GHOST STATE HAS TO SUPPLY:

   * the [f->ref < 1] arm is DEAD, exactly as in filedup: the caller's
     [file_ref] is a fragment of the authority, so [fref_tok_lookup] puts slot
     k in the domain with a [positive] count and [fref_word_spos] turns that
     into "the sign-extended load is signed-positive", which is what [blez]
     tests.  The panic tail gets no [instr] fact at all.

   * [--f->ref > 0] is the count being at least 2, and [file_close_step]
     absorbs the departing share -- of the cells, of the payload-names field
     and of the payload -- back into [file_rest] ([file_rest_absorb]).

   * [--f->ref == 0] is the count being exactly 1, which by [fref_tok_lookup]
     means this closer holds every share ever handed out.  Joining with what
     the invariant kept ([file_rest_join]) makes it fraction ONE of the whole
     slot: enough to write [f->type = FD_NONE], and a WHOLE pipe end (or
     inode reference) to give pipeclose (or iput).

   THE ORDER MATTERS, and the C code has it right: [f->type = FD_NONE] is
   stored, and the lock released, BEFORE the payload is spent.  At FD_NONE
   the payload is [emp], so what goes back into the table is the slot with no
   payload while the closer walks away with it.

   LAZY SPILLS.  [s2..s5] are saved at +0x26, on the slow path only, so the
   fast path never touches frame slots 4..7 and hands them back untouched --
   which is why one epilogue serves both. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots FileInv.
Require Import ProcGeom.
Require Import WpUart LogInv.
Require Import WpLock.
Require Import SpecAcquire SpecRelease.
Require Import SpecPipeclose SpecBeginOp SpecIput SpecEndOp.
Require Import IrefSlots.
Require Import IcacheEscrow.  (* [ic_sleeplocks], hoisted out of the two function specs *)
Require Import IcacheRef.     (* [icfg_log] / [icfg_ist] / [icfg_nib] / [icfg_dev] *)
Require Import FsCfg.         (* the ambient fs names the FS arm now runs at *)
Require Import FsReady.       (* [fs_ready] and its projection family *)
Require Import SpecFileclose.
Require Import CodeFileclose ProofFilecloseParts.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import ProcDefs.  (* [pprivate], [proc_priv_bare] *)
Local Open Scope Z_scope.
Set Printing Depth 40.

Module FilecloseProof (Acquire : ACQUIRE) (Release : RELEASE)
                      (Pipeclose : PIPECLOSE) (BeginOp : BEGIN_OP)
                      (Iput : IPUT) (EndOp : END_OP) : FILECLOSE.

Section ProofFileclose.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* MOVING THE TRAP-CSR COMPLEMENT ACROSS A STRETCH.  [trap_csrs_ext] /
     [cpu_claim_ext] transport under an [eb]-indexed guard, while a
     straight-line stretch's chain facts are [b]-indexed -- so [wp_next_chain]
     cannot close such a goal directly.  It does not have to: [eb = false]
     forces [b = false] at EVERY nesting depth ([Hebf], read off
     [sie_b_agree]), so the [eb] guard reduces to the [b] one and the ordinary
     chain closes that.  [Hf] is [Hebf] and [Bv] is the proof's [b]; both are
     passed rather than named here so the tactic is usable inside the arms
     that have substituted their other indices. *)
  Local Ltac ext_chain Hf Bv :=
    let Hd := fresh "Hdx" in
    let Hd2 := fresh "Hdx2" in
    lazymatch goal with
    | |- (_ = false \/ ?P = zero_reg -> _) =>
        intros Hd;
        assert (Hd2 : Bv = false \/ P = zero_reg)
          by (destruct Hd as [Hee | Hpp];
              [ left; exact (Hf Hee) | right; exact Hpp ]);
        clear Hd; revert Hd2; wp_next_chain
    end.

  (* [b] and [n],[eb] are two presentations of the same SIE state; read once
     at entry, this is what makes release's derived exit index fileclose's
     own.  (Copied from ProofFiledup; a shared home for it would drag the
     lock layer into every function proof that has one.) *)
  Local Lemma sie_b_agree (m : regfile) (n K0 : nat) (eb b : bool)
      (p : mword 64) (lks : gset string) :
    sie_cap_gpr KT1 m K0 b p -∗ cpu_own n eb p b lks -∗
    ⌜ b = match n with O => eb | S _ => false end ⌝.
  Proof.
    iIntros "Hcg Hcnt". destruct b.
    - iDestruct "Hcnt" as "%Hb". destruct Hb as (-> & -> & _). done.
    - destruct n as [|n']; [ | done ].
      iDestruct "Hcnt" as "[_ Hint]".
      iDestruct "Hcg" as "(_ & _ & (_ & _ & Harm & _) & _)".
      iDestruct (ghost_var_agree with "Harm Hint") as %Heq.
      destruct eb; [ exfalso | done ].
      apply (f_equal (@bv_unsigned _)) in Heq. vm_compute in Heq. discriminate.
  Qed.

  Lemma wp_fileclose_sconf  (γfl γf : gname)
      (k : nat) (q : Qp) (Cf : fcontent)
      (fn : fclose_names) (on : option nat)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64)
      (K : nat) (b : bool) (lks : gset string) (pidv : mword 32) (Vpr : pprivate)
    : wp_fileclose_sconf_body γfl γf k q Cf fn on m n eb p K b lks pidv Vpr.
  Proof.
    cbv beta delta [wp_fileclose_sconf_body].
    intros pcE ret_tgt HK HnZ Ha0 Hbelow.
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt Hextc Hextm #Htext #Hkd Hpc #Hlock #Hpenv Href Hpbare Hiru Henv Hcont".
    iDestruct (sie_b_agree m n K eb b p lks with "Hcg Hcnt") as %Houtb.
    (* THE ONE FACT THE COMPLEMENT'S TRANSPORTS NEED (see [ext_chain]): the
       disabled base forces the disabled arm, at any nesting depth. *)
    assert (Hebf : eb = false -> b = false)
      by (intro Hx; rewrite Houtb Hx; by destruct n).
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))).
    (* ===================================================================
       PROLOGUE (generic [b]): push 8 slots, spill ra/s0/s1, s0 := old sp,
       s1 := f, a0 := &ftable, call acquire.
       =================================================================== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 8).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 60 : mword 6) m K 8 b
              ltac:(lia) Hpush with "Hcg Hpc []").
    { iApply (fci_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    assert (HsprS : spr = pa_stk sp0 8) by exact Hpush.
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _)".
    iDestruct "S1" as (u1) "Hb1". iDestruct "S2" as (u2) "Hb2".
    iDestruct "S3" as (u3) "Hb3". iDestruct "S4" as (u4) "Hb4".
    iDestruct "S5" as (u5) "Hb5". iDestruct "S6" as (u6) "Hb6".
    iDestruct "S7" as (u7) "Hb7". iDestruct "S8" as (u8) "Hb8".
    (* the three spills, at 56/48/40(sp) *)
    assert (Hf1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HspR1 HsprS; apply fc_frm1).
    assert (Hf2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HspR1 HsprS; apply fc_frm2).
    assert (Hf3 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HspR1 HsprS; apply fc_frm3).
    iEval (rewrite -Hf1) in "Hb1". iEval (rewrite -Hf2) in "Hb2".
    iEval (rewrite -Hf3) in "Hb3".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (FC + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (FC + 0x02)) (mword_of_int 7 : mword 6) Rra
              R1 (K - 8)%nat u1 b with "Hcg Hpc [] Hb1").
    { iApply (fci_02 with "Htext"). }
    iIntros (CID2 Hs2) "Hcg Hpc Hb1". iEval (rgne) in "Hb1".
    iEval (rewrite Hf1) in "Hb1".
    assert (Hpp04 : add_vec_int (mword_of_int (FC + 0x02) : mword 64) 2
                    = mword_of_int (FC + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (FC + 0x04)) (mword_of_int 6 : mword 6) Rs0
              R1 (K - 8)%nat u2 b with "Hcg Hpc [] Hb2").
    { iApply (fci_04 with "Htext"). }
    iIntros (CID3 Hs3) "Hcg Hpc Hb2". iEval (rgne) in "Hb2".
    iEval (rewrite Hf2) in "Hb2".
    assert (Hpp06 : add_vec_int (mword_of_int (FC + 0x04) : mword 64) 2
                    = mword_of_int (FC + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (FC + 0x06)) (mword_of_int 5 : mword 6) Rs1
              R1 (K - 8)%nat u3 b with "Hcg Hpc [] Hb3").
    { iApply (fci_06 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc Hb3". iEval (rgne) in "Hb3".
    iEval (rewrite Hf3) in "Hb3".
    assert (Hpp08 : add_vec_int (mword_of_int (FC + 0x06) : mword 64) 2
                    = mword_of_int (FC + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.addi4spn s0,sp,64 : the frame pointer *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (FC + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 16 : mword 8) Rs0 R1 (K - 8)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fci_08 with "Htext"). }
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> R1).
    assert (Hpp0a : add_vec_int (mword_of_int (FC + 0x08) : mword 64) 2
                    = mword_of_int (FC + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.mv s1,a0 : the cursor takes the argument *)
    iApply (wp_cmv_s_sconf (mword_of_int (FC + 0x0a)) Rs1 Ra0
              R2 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fci_0a with "Htext"). }
    iIntros (CID6 Hs6) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R3 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    assert (HR3s1 : R3 !!! Regidx Rs1 = fnode k).
    { rewrite /R3 upd_eq. rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite Ha0. apply add_vec_zero_l. }
    assert (Hpp0c : add_vec_int (mword_of_int (FC + 0x0a) : mword 64) 2
                    = mword_of_int (FC + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c/+0x10 a0 := &ftable *)
    iApply (wp_auipc_s_sconf (mword_of_int (FC + 0x0c)) Ra0 (mword_of_int 0x1e : mword 20)
              R3 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fci_0c with "Htext"). }
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (R4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (FC + 0x0c) : mword 64)
                     (auipc_off (mword_of_int 0x1e : mword 20)))]> R3).
    assert (Hpp10 : add_vec_int (mword_of_int (FC + 0x0c) : mword 64) 4
                    = mword_of_int (FC + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (FC + 0x10)) Ra0 Ra0 (mword_of_int 922 : mword 12)
              R4 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fci_10 with "Htext"). }
    iIntros (CID8 Hs8) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (R4 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 922 : mword 12)))]> R4).
    assert (HR5a0 : R5 !!! Regidx Ra0 = ftable_addr).
    { rewrite /R5 upd_eq /R4 upd_eq. rewrite /ftable_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp14 : add_vec_int (mword_of_int (FC + 0x10) : mword 64) 4
                    = mword_of_int (FC + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 jal ra,acquire ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (FC + 0x14)) Rra (mword_of_int 2083452 : mword 21)
              R5 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (fci_14 with "Htext"). }
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (mA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (FC + 0x14) : mword 64) 4)]> R5).
    assert (Htgtacq : add_vec (mword_of_int (FC + 0x14) : mword 64)
                        (sign_extend' 64 (mword_of_int 2083452 : mword 21))
                      = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtacq) in "Hpc".
    assert (HmAsp : mA !!! Regidx csp_rs1 = spr).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      exact HspR1. }
    assert (HmAa0 : mA !!! Regidx Ra0 = ftable_addr).
    { rewrite /mA upd_ne; [| vm_compute; discriminate]. exact HR5a0. }
    assert (HmAs1 : mA !!! Regidx Rs1 = fnode k).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate]. exact HR3s1. }
    assert (HmAra : mA !!! Regidx Rra
                    = add_vec_int (mword_of_int (FC + 0x14) : mword 64) 4)
      by (rewrite /mA; apply upd_eq).
    assert (HmAthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              mA !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9.
      rewrite /mA upd_ne; [| regne].
      rewrite /R5 upd_ne; [| regne].
      rewrite /R4 upd_ne; [| regne].
      rewrite /R3 upd_ne; [| regne].
      rewrite /R2 upd_ne; [| regne].
      rewrite /R1 upd_ne; [reflexivity | regne]. }
    iDestruct (cpu_own_transport CID CID9 n eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf KT1 γfl "ftable"%string (ftable_res γf) mA
              n eb p (K - 8)%nat b lks
              HnZ ltac:(lia) ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc [Hlock]").
    all: try lkbelow.
    { iEval (rewrite HmAa0). iExact "Hlock". }
    iIntros (CIDacq Hsacq ms macq) "%Hmsfacts Hcg Hpc %Hacqpins Htok HRres Hcnt Hpay".
    assert (Hpc18 : ret_pc (mA !!! Regidx Rra) = mword_of_int (FC + 0x18)).
    { rewrite HmAra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc18) in "Hpc".
    pose proof Hacqpins as Hacqpins_cs.
    assert (Hmsp : macq !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hacqpins_cs csp_rs1 ltac:(vm_compute; reflexivity));
          exact HmAsp).
    assert (Hms1 : macq !!! Regidx Rs1 = fnode k)
      by (rewrite (callee_saved_lookup Hacqpins_cs (mword_of_int 9)
                     ltac:(vm_compute; reflexivity)); exact HmAs1).
    assert (Hmthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              macq !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9.
      rewrite (callee_saved_lookup Hacqpins_cs c Hcs). exact (HmAthr c Hcs N2 N8 N9). }
    (* ===================================================================
       THE CRITICAL SECTION (literal [false]: no hart threading).
       =================================================================== *)
    iDestruct "HRres" as (Mg) "(Hauth & Hfdauth & %Hdom & Hslots)".
    iDestruct "Href" as "(Hrtok & Hrfields & Hrpay & Hrlv)".
    iDestruct (fref_tok_lookup with "Hauth Hrtok")
      as %(qt & cnt & HMk & Hqt1 & Hn1 & _ & Hqlt).
    assert (Hk : (k < NFILE)%nat) by (apply Hdom; rewrite HMk; eauto).
    iDestruct (ftable_slots_acc γf Mg k Hk with "Hslots") as "[Hslot Hback]".
    iEval (rewrite /fslot HMk) in "Hslot".
    iDestruct "Hslot" as "(%Hcnt & Hcell & Hrest & Hfd)".
    (* +0x18 c.lw a5,4(s1) : a5 := f->ref *)
    assert (Hpa : add_vec (rget macq Rs1) (sign_extend' 64 (mword_of_int 4 : mword 12))
                  = a_fref k).
    { rewrite (rget_ne macq Rs1 ltac:(vm_compute; discriminate)) Hms1. reflexivity. }
    iEval (rewrite -Hpa) in "Hcell".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FC + 0x18)) Ra5 Rs1 (mword_of_int 4 : mword 12)
              macq (trap_res b + (K - 8))%nat (mword_of_int (Z.pos cnt) : mword 32) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hcell").
    { iApply (fci_18 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell".
    iEval (rewrite Hpa) in "Hcell".
    set (D1 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.pos cnt) : mword 32))]> macq).
    assert (HD1a5 : D1 !!! Regidx Ra5
                    = sign_extend' 64 (mword_of_int (Z.pos cnt) : mword 32))
      by (rewrite /D1; apply upd_eq).
    assert (HD1s1 : D1 !!! Regidx Rs1 = fnode k)
      by (rewrite /D1 upd_ne; [exact Hms1 | vm_compute; discriminate]).
    assert (HD1sp : D1 !!! Regidx csp_rs1 = spr)
      by (rewrite /D1 upd_ne; [exact Hmsp | vm_compute; discriminate]).
    assert (Hpp1a : add_vec_int (mword_of_int (FC + 0x18) : mword 64) 2
                    = mword_of_int (FC + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a blez a5 -- the panic arm, DEAD *)
    iApply (wp_bge_x0_fall_s_sconf (mword_of_int (FC + 0x1a)) (mword_of_int 84 : mword 13)
              Ra5 D1 (trap_res b + (K - 8))%nat false ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite HD1a5; apply fref_word_spos; exact Hcnt)
              with "Hcg Hpc []").
    { iApply (fci_1a with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hpp1e : add_vec_int (mword_of_int (FC + 0x1a) : mword 64) 4
                    = mword_of_int (FC + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e c.addiw a5,a5,-1 *)
    iApply (wp_caddiw_s_sconf (mword_of_int (FC + 0x1e)) Ra5 (mword_of_int 63 : mword 6)
              D1 (trap_res b + (K - 8))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fci_1e with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
    set (D2 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (D1 !!! Regidx Ra5)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> D1).
    assert (HD2s1 : D2 !!! Regidx Rs1 = fnode k)
      by (rewrite /D2 upd_ne; [exact HD1s1 | vm_compute; discriminate]).
    assert (HD2sp : D2 !!! Regidx csp_rs1 = spr)
      by (rewrite /D2 upd_ne; [exact HD1sp | vm_compute; discriminate]).
    assert (Hpp20 : add_vec_int (mword_of_int (FC + 0x1e) : mword 64) 2
                    = mword_of_int (FC + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 c.sw a5,4(s1) : f->ref = ref - 1 *)
    assert (Hpa2 : add_vec (rget D2 Rs1) (sign_extend' 64 (mword_of_int 4 : mword 12))
                   = a_fref k).
    { rewrite (rget_ne D2 Rs1 ltac:(vm_compute; discriminate)) HD2s1. reflexivity. }
    iEval (rewrite -Hpa2) in "Hcell".
    iApply (wp_csw_s_sconf (mword_of_int (FC + 0x20)) Ra5 Rs1 (mword_of_int 4 : mword 12)
              D2 (trap_res b + (K - 8))%nat (mword_of_int (Z.pos cnt) : mword 32) false
              with "Hcg Hpc [] Hcell").
    { iApply (fci_20 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell".
    iEval (rewrite Hpa2) in "Hcell".
    assert (Hpp22 : add_vec_int (mword_of_int (FC + 0x20) : mword 64) 2
                    = mword_of_int (FC + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* the value that was stored, and the one the [bgtz] tests, are both
       [cnt - 1]; which arm runs is exactly whether the count was 1. *)
    assert (Hcnt31 : (Z.pos cnt < 2 ^ 31)%Z) by exact Hcnt.
    assert (Hstv : trunc32 (rget D2 Ra5) = (mword_of_int (Z.pos cnt - 1) : mword 32)).
    { rewrite (rget_ne D2 Ra5 ltac:(vm_compute; discriminate)).
      rewrite /D2 upd_eq. unfold regval_into_reg. rewrite HD1a5.
      apply fc_storeval_pred; lia. }
    iEval (rewrite Hstv) in "Hcell".
    assert (Hregv : rget D2 Ra5 = sign_extend' 64 (mword_of_int (Z.pos cnt - 1) : mword 32)).
    { rewrite (rget_ne D2 Ra5 ltac:(vm_compute; discriminate)).
      rewrite /D2 upd_eq. unfold regval_into_reg. rewrite HD1a5.
      apply fc_pred_reg; lia. }
    destruct (decide (cnt = 1%positive)) as [Hone | Hmany]; last first.
    - (* ===============================================================
         [--f->ref > 0]: the count was at least 2, so this is NOT the last
         reference.  The departing share goes back into [file_rest] and the
         function releases and returns having touched no payload.
         =============================================================== *)
      set (n' := Pos.pred cnt).
      assert (Hsucc : cnt = Pos.succ n') by (rewrite /n' Pos.succ_pred; done).
      assert (Hge2 : (2 <= Z.pos cnt)%Z).
      { destruct (Pos.lt_total 1 cnt) as [Hlt|[He|Hgt]];
          [lia | exfalso; apply Hmany; by symmetry | lia]. }
      assert (Hn'lt : (Z.pos n' < 2 ^ 31)%Z).
      { assert (Hx : (Z.pos cnt = Z.pos n' + 1)%Z)
          by (rewrite {1}Hsucc Pos2Z.inj_succ; lia).
        lia. }
      assert (Hcv : (Z.pos cnt - 1)%Z = Z.pos n')
        by (rewrite {1}Hsucc Pos2Z.inj_succ; lia).
      (* +0x22 bgtz a5 -- TAKEN *)
      assert (Htgt82 : add_vec (mword_of_int (FC + 0x22) : mword 64)
                         (sign_extend' 64 (mword_of_int 96 : mword 13))
                       = mword_of_int (FC + 0x82))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_bgtz_taken_s_sconf (mword_of_int (FC + 0x22))
                (mword_of_int 96 : mword 13) Ra5 D2 (trap_res b + (K - 8))%nat false
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hregv; apply fc_pred_gtz; lia)
                ltac:(rewrite Htgt82; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (fci_22 with "Htext"). }
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt82) in "Hpc".
      (* ---- the ghost step: the departing share goes home ---- *)
      destruct (proj1 (Qp.lt_sum q qt) (Hqlt Hmany)) as [qr Hqr].
      assert (Hsub : (qt - q)%Qp = Some qr) by (apply Qp.sub_Some; exact Hqr).
      iMod (file_close_step γf Mg k q Cf qt n' qr
              ltac:(rewrite -Hsucc; exact HMk) Hsub
              with "Hauth [Hrtok Hrfields Hrpay Hrlv]") as "(Hauth & Hfl & Hpy)".
      { rewrite /file_ref /fref_tok. iFrame "Hrtok Hrfields Hrpay Hrlv". }
      iDestruct (file_rest_absorb γf k qt q qr Cf Hsub Hqt1 with "Hrest Hfl Hpy")
        as "Hrest".
      (* the fd slot the destroyed reference was holding comes back *)
      assert (Hton : Pos.to_nat cnt = (Pos.to_nat n' + 1)%nat)
        by (rewrite {1}Hsucc Pos2Nat.inj_succ; lia).
      iEval (rewrite Hton) in "Hfd".
      iDestruct (fd_slots_split with "Hfd") as "[Hfd Hunit]".
      iEval (rewrite Hcv) in "Hcell".
      iDestruct ("Hback" $! (<[k := (qr, n')]> Mg) with "[%] [Hcell Hrest Hfd]")
        as "Hslots".
      { intros j Hj. rewrite lookup_insert_ne; [reflexivity | congruence]. }
      { rewrite /fslot lookup_insert. iFrame "Hcell Hrest Hfd". iPureIntro. exact Hn'lt. }
      iAssert (ftable_res γf) with "[Hauth Hfdauth Hslots]" as "HRres".
      { iExists (<[k := (qr, n')]> Mg). iFrame "Hauth Hfdauth Hslots".
        iPureIntro. intros j Hj.
        destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
        apply Hdom. by rewrite lookup_insert_ne in Hj. }
      (* ---- +0x82/+0x86 a0 := &ftable ; +0x8a jal release ---- *)
      iApply (wp_auipc_s_sconf (mword_of_int (FC + 0x82)) Ra0
                (mword_of_int 0x1e : mword 20) D2 (trap_res b + (K - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (fci_82 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (E1 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (mword_of_int (FC + 0x82) : mword 64)
                       (auipc_off (mword_of_int 0x1e : mword 20)))]> D2).
      assert (Hpp86 : add_vec_int (mword_of_int (FC + 0x82) : mword 64) 4
                      = mword_of_int (FC + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp86) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (FC + 0x86)) Ra0 Ra0
                (mword_of_int 804 : mword 12) E1 (trap_res b + (K - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (fci_86 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
      set (E2 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (E1 !!! Regidx Ra0)
                       (sign_extend' 64 (mword_of_int 804 : mword 12)))]> E1).
      assert (HE2a0 : E2 !!! Regidx Ra0 = ftable_addr).
      { rewrite /E2 upd_eq /E1 upd_eq. rewrite /ftable_addr.
        apply bv_eq; vm_compute; reflexivity. }
      assert (Hpp8a : add_vec_int (mword_of_int (FC + 0x86) : mword 64) 4
                      = mword_of_int (FC + 0x8a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp8a) in "Hpc".
      iApply (wp_jal_s_sconf (mword_of_int (FC + 0x8a)) Rra
                (mword_of_int 2083470 : mword 21) E2 (trap_res b + (K - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (fci_8a with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (E3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (FC + 0x8a) : mword 64) 4)]> E2).
      assert (Htgtrel : add_vec (mword_of_int (FC + 0x8a) : mword 64)
                          (sign_extend' 64 (mword_of_int 2083470 : mword 21))
                        = mword_of_int KernelSyms.release)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtrel) in "Hpc".
      assert (HE3a0 : E3 !!! Regidx Ra0 = ftable_addr)
        by (rewrite /E3 upd_ne; [exact HE2a0 | vm_compute; discriminate]).
      assert (HE3ra : E3 !!! Regidx Rra
                      = add_vec_int (mword_of_int (FC + 0x8a) : mword 64) 4)
        by (rewrite /E3; apply upd_eq).
      assert (HE3thr : forall c : mword 5, is_cs_idx c = true ->
                E3 !!! Regidx c = macq !!! Regidx c).
      { intros c Hcs.
        rewrite /E3 upd_ne; [| regne].
        rewrite /E2 upd_ne; [| regne].
        rewrite /E1 upd_ne; [| regne].
        rewrite /D2 upd_ne; [| regne].
        rewrite /D1 upd_ne; [reflexivity | regne]. }
      assert (HE3sp : E3 !!! Regidx csp_rs1 = spr)
        by (rewrite (HE3thr csp_rs1 ltac:(vm_compute; reflexivity)); exact Hmsp).
      (* the acquire handed the window index out as [trap_res b + N]; release
         wants it as [trap_res outb + N] with [outb = match n with O => eb
         | S _ => false end].  Those are the same bool -- [cpu_own] forces
         it -- so this is a pure re-spelling, and it is what makes the
         acquire/release pair compose back to [N]. *)
      iEval (rewrite Houtb) in "Hcg".
      iApply (Release.wp_release_sconf KT1 γfl ftable_addr "ftable"%string
                (ftable_res γf) E3 n eb p (K - 8)%nat
                ({["ftable"]} ∪ lks)
                ltac:(rewrite HE3a0; apply bv_eq; vm_compute; reflexivity)
                ltac:(lia)
                with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay").
      { iExact "Hlock". }
      iIntros (CIDr Hsr mr) "Hcg Hpc %Hrelpins Hcnt".
      (* fileclose is BALANCED on this arm: the set release hands back
         collapses to the entry [lks] -- [Hfresh] makes the singleton
         insert/delete cancel. *)
      assert (Hsetback : ({["ftable"]} ∪ lks) ∖ {["ftable"]} = lks)
      by (apply locks_add_del_below; lkbelow).
      iEval (rewrite Hsetback) in "Hcnt".
      iEval (rewrite <- Houtb) in "Hcg". iEval (rewrite <- Houtb) in "Hcnt".
      rewrite <- Houtb in Hsr.
      pose proof Hrelpins as Hrelpins_cs.
      assert (Hpc8e : ret_pc (E3 !!! Regidx Rra) = mword_of_int (FC + 0x8e)).
      { rewrite HE3ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc8e) in "Hpc".
      (* ---- the epilogue.  Frame slots 4..7 were NEVER written on this
             path: [s2..s5] are spilled only by the last-reference arm. ---- *)
      assert (Hmrsp : mr !!! Regidx csp_rs1 = pa_stk sp0 8).
      { rewrite (callee_saved_lookup Hrelpins_cs csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite HE3sp. exact HsprS. }
      assert (Hmrthr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> mr !!! Regidx r = m !!! Regidx r).
      { intros r Hr N2 N8 N9.
        rewrite (callee_saved_lookup Hrelpins_cs r Hr).
        rewrite (HE3thr r Hr). exact (Hmthr r Hr N2 N8 N9). }
      assert (HR1ra : R1 !!! Regidx Rra = m !!! Regidx Rra)
        by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
      assert (HR1s0 : R1 !!! Regidx Rs0 = m !!! Regidx Rs0)
        by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
      assert (HR1s1 : R1 !!! Regidx Rs1 = m !!! Regidx Rs1)
        by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
      iEval (rewrite HR1ra) in "Hb1". iEval (rewrite HR1s0) in "Hb2".
      iEval (rewrite HR1s1) in "Hb3".
      iApply (fc_epi (CID0 := CIDr) m mr K sp0 (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) u4 u5 u6 u7 u8 p b
                ltac:(lia) eq_refl eq_refl eq_refl eq_refl Hmrsp Hmrthr
                with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8").
      iIntros (CIDe Hse mf) "%Hcsf Hcg Hpc".
      iDestruct (cpu_own_transport CIDr CIDe n eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      (* ONE WIDE HOP for the complement: nothing on this path threads it
         (acquire and release do not mention it), so it is still at the entry
         hart and moves straight to the exit's. *)
      iDestruct (trap_csrs_ext_transport CID CIDe eb p ltac:(ext_chain Hebf b)
                   with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID CIDe eb p ltac:(ext_chain Hebf b)
                   with "Hextm") as "Hextm".
      iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
      iApply ("Hcont" $! mf with "Hcg Hcnt Hextc Hextm [Hpc] [%] Hunit Hiru [Henv] Hpbare").
      { iEval (rewrite /ret_tgt). iExact "Hpc". }
      { exact Hcsf. }
      { by iApply fileclose_env_out_of_env. }
    - (* ===============================================================
         [--f->ref == 0]: the LAST reference.
         =============================================================== *)
      subst cnt.
      specialize (Hn1 eq_refl). subst qt.
      (* +0x22 bgtz a5 -- FALLS: the count reached zero *)
      iApply (wp_bgtz_fall_s_sconf (mword_of_int (FC + 0x22))
                (mword_of_int 96 : mword 13) Ra5 D2 (trap_res b + (K - 8))%nat false
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hregv; exact fc_pred_ngtz)
                with "Hcg Hpc []").
      { iApply (fci_22 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpp26 : add_vec_int (mword_of_int (FC + 0x22) : mword 64) 4
                      = mword_of_int (FC + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      (* ---- THE GHOST STEP.  [fref_tok_lookup] made this closer's share the
             whole OUTSTANDING total; the invariant's leftover makes it the
             whole slot ([file_rest_join]).  Doing it here, before the reads,
             is what puts every content cell at fraction 1. ---- *)
      iDestruct (file_rest_join γf k q Cf Hqt1 with "Hrfields Hrpay Hrest")
        as "[Hfl Hpy]".
      iDestruct "Hpy" as (pn) "[Hpn Hpl]".
      iDestruct "Hpl" as "[Hcore Hoh]".
      (* ---- R-open-1b: RETIRE THE OFF-BORROW CINV, and it has to happen
             HERE.  The refutation of a stale checked-out state is the
             liveness COUNT, which reads the authority entry the ghost step
             below deletes; and the join above is what makes the cancel token
             whole.  The type is not tested for another two hundred lines, so
             the cancel is uniform in [file_armed] -- an unarmed body has no
             disjunction to refute.  What comes back are the two cells, which
             go straight into a FRESH unarmed cinv for the free slot. ---- *)
      iApply fupd_wp.
      iMod (off_hold_cancel ⊤ γf (fp_ocv pn) (file_armed Cf) Mg k q
              ltac:(solve_ndisj) HMk with "Hoh Hauth Hrlv")
        as "(Hauth & Hrlv & Hraw)".
      iMod (off_hold_alloc ⊤ γf k false with "Hraw") as (γo0) "Hoh0".
      set (pn0 := MkFPNames (fp_lock pn) (fp_pipe pn) (fp_icv pn) (fp_iq pn)
                    (fp_ig pn) γo0).
      iMod (fpay_tok_update γf k pn pn0 with "Hpn") as "Hpn".
      iMod (file_close_last_ghost γf Mg k q HMk with "Hauth Hrtok Hrlv")
        as "Hauth".
      iModIntro.
      assert (Hzz : (Z.pos 1 - 1)%Z = 0%Z) by lia.
      iEval (rewrite Hzz) in "Hcell".
      rewrite /file_fields.
      iDestruct "Hfl" as "(Hcty & Hcrd & Hcwr & Hcpp & Hcip & Hcmaj)".
      (* ---- +0x26 .. +0x2c: the LAZY spills of s2..s5 ---- *)
      assert (Hg4 : add_vec (D2 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                    = pa_stk sp0 4) by (rewrite HD2sp HsprS; apply fc_frm4).
      assert (Hg5 : add_vec (D2 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                    = pa_stk sp0 5) by (rewrite HD2sp HsprS; apply fc_frm5).
      assert (Hg6 : add_vec (D2 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                    = pa_stk sp0 6) by (rewrite HD2sp HsprS; apply fc_frm6).
      assert (Hg7 : add_vec (D2 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                    = pa_stk sp0 7) by (rewrite HD2sp HsprS; apply fc_frm7).
      iEval (rewrite -Hg4) in "Hb4".
      iApply (wp_csdsp_s_sconf (mword_of_int (FC + 0x26)) (mword_of_int 4 : mword 6) Rs2
                D2 (trap_res b + (K - 8))%nat u4 false with "Hcg Hpc [] Hb4").
      { iApply (fci_26 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hb4".
      iEval (rgne) in "Hb4". iEval (rewrite Hg4) in "Hb4".
      assert (Hpp28 : add_vec_int (mword_of_int (FC + 0x26) : mword 64) 2
                      = mword_of_int (FC + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp28) in "Hpc".
      iEval (rewrite -Hg5) in "Hb5".
      iApply (wp_csdsp_s_sconf (mword_of_int (FC + 0x28)) (mword_of_int 3 : mword 6) Rs3
                D2 (trap_res b + (K - 8))%nat u5 false with "Hcg Hpc [] Hb5").
      { iApply (fci_28 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hb5".
      iEval (rgne) in "Hb5". iEval (rewrite Hg5) in "Hb5".
      assert (Hpp2a : add_vec_int (mword_of_int (FC + 0x28) : mword 64) 2
                      = mword_of_int (FC + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      iEval (rewrite -Hg6) in "Hb6".
      iApply (wp_csdsp_s_sconf (mword_of_int (FC + 0x2a)) (mword_of_int 2 : mword 6) Rs4
                D2 (trap_res b + (K - 8))%nat u6 false with "Hcg Hpc [] Hb6").
      { iApply (fci_2a with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hb6".
      iEval (rgne) in "Hb6". iEval (rewrite Hg6) in "Hb6".
      assert (Hpp2c : add_vec_int (mword_of_int (FC + 0x2a) : mword 64) 2
                      = mword_of_int (FC + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2c) in "Hpc".
      iEval (rewrite -Hg7) in "Hb7".
      iApply (wp_csdsp_s_sconf (mword_of_int (FC + 0x2c)) (mword_of_int 1 : mword 6) Rs5
                D2 (trap_res b + (K - 8))%nat u7 false with "Hcg Hpc [] Hb7").
      { iApply (fci_2c with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hb7".
      iEval (rgne) in "Hb7". iEval (rewrite Hg7) in "Hb7".
      assert (Hpp2e : add_vec_int (mword_of_int (FC + 0x2c) : mword 64) 2
                      = mword_of_int (FC + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2e) in "Hpc".
      (* ---- +0x2e .. +0x3e: [ff = *f], the four fields the arms use ---- *)
      assert (Hat : add_vec (rget D2 Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = a_ftype k).
      { rewrite (rget_ne D2 Rs1 ltac:(vm_compute; discriminate)) HD2s1.
        rewrite /a_ftype. apply addv_sext0. }
      iEval (rewrite -Hat) in "Hcty".
      iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FC + 0x2e)) Rs2 Rs1
                (mword_of_int 0 : mword 12) D2 (trap_res b + (K - 8))%nat (fc_type Cf) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hcty").
      { iApply (fci_2e with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hcty".
      iEval (rewrite Hat) in "Hcty".
      set (F1 := <[Regidx Rs2 := regval_into_reg (sign_extend' 64 (fc_type Cf))]> D2).
      assert (HF1s1 : F1 !!! Regidx Rs1 = fnode k)
        by (rewrite /F1 upd_ne; [exact HD2s1 | vm_compute; discriminate]).
      assert (HF1s2 : F1 !!! Regidx Rs2 = sign_extend' 64 (fc_type Cf))
        by (rewrite /F1; apply upd_eq).
      assert (Hpp32 : add_vec_int (mword_of_int (FC + 0x2e) : mword 64) 4
                      = mword_of_int (FC + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp32) in "Hpc".
      assert (Haw : add_vec (rget F1 Rs1) (sign_extend' 64 (mword_of_int 9 : mword 12))
                    = a_fwritable k).
      { rewrite (rget_ne F1 Rs1 ltac:(vm_compute; discriminate)) HF1s1. reflexivity. }
      iEval (rewrite -Haw) in "Hcwr".
      iApply (wp_lbu_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FC + 0x32)) Ra5 Rs1
                (mword_of_int 9 : mword 12) F1 (trap_res b + (K - 8))%nat (fc_writable Cf : mword 8) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hcwr").
      { iApply (fci_32 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hcwr".
      iEval (rewrite Haw) in "Hcwr".
      set (F2 := <[Regidx Ra5 := regval_into_reg
                    (zero_extend' 64 (fc_writable Cf : mword 8))]> F1).
      assert (HF2s1 : F2 !!! Regidx Rs1 = fnode k)
        by (rewrite /F2 upd_ne; [exact HF1s1 | vm_compute; discriminate]).
      assert (HF2a5 : F2 !!! Regidx Ra5 = zero_extend' 64 (fc_writable Cf : mword 8))
        by (rewrite /F2; apply upd_eq).
      assert (Hpp36 : add_vec_int (mword_of_int (FC + 0x32) : mword 64) 4
                      = mword_of_int (FC + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      iApply (wp_cmv_s_sconf (mword_of_int (FC + 0x36)) Rs3 Ra5 F2 (trap_res b + (K - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (fci_36 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
      set (F3 := <[Regidx Rs3 := regval_into_reg
                    (add_vec zero_reg (F2 !!! Regidx Ra5))]> F2).
      assert (HF3s1 : F3 !!! Regidx Rs1 = fnode k)
        by (rewrite /F3 upd_ne; [exact HF2s1 | vm_compute; discriminate]).
      assert (Hpp38 : add_vec_int (mword_of_int (FC + 0x36) : mword 64) 2
                      = mword_of_int (FC + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp38) in "Hpc".
      assert (Hap : add_vec (rget F3 Rs1) (sign_extend' 64 (mword_of_int 16 : mword 12))
                    = a_fpipe k).
      { rewrite (rget_ne F3 Rs1 ltac:(vm_compute; discriminate)) HF3s1. reflexivity. }
      iEval (rewrite -Hap) in "Hcpp".
      iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FC + 0x38)) Ra5 Rs1
                (mword_of_int 16 : mword 12) F3 (trap_res b + (K - 8))%nat (fc_pipe Cf) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hcpp").
      { iApply (fci_38 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hcpp".
      iEval (rewrite Hap) in "Hcpp".
      set (F4 := <[Regidx Ra5 := regval_into_reg (fc_pipe Cf)]> F3).
      assert (HF4s1 : F4 !!! Regidx Rs1 = fnode k)
        by (rewrite /F4 upd_ne; [exact HF3s1 | vm_compute; discriminate]).
      assert (Hpp3a : add_vec_int (mword_of_int (FC + 0x38) : mword 64) 2
                      = mword_of_int (FC + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      iApply (wp_cmv_s_sconf (mword_of_int (FC + 0x3a)) Rs4 Ra5 F4 (trap_res b + (K - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (fci_3a with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
      set (F5 := <[Regidx Rs4 := regval_into_reg
                    (add_vec zero_reg (F4 !!! Regidx Ra5))]> F4).
      assert (HF5s1 : F5 !!! Regidx Rs1 = fnode k)
        by (rewrite /F5 upd_ne; [exact HF4s1 | vm_compute; discriminate]).
      assert (Hpp3c : add_vec_int (mword_of_int (FC + 0x3a) : mword 64) 2
                      = mword_of_int (FC + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3c) in "Hpc".
      assert (Hai : add_vec (rget F5 Rs1) (sign_extend' 64 (mword_of_int 24 : mword 12))
                    = a_fip k).
      { rewrite (rget_ne F5 Rs1 ltac:(vm_compute; discriminate)) HF5s1. reflexivity. }
      iEval (rewrite -Hai) in "Hcip".
      iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FC + 0x3c)) Ra5 Rs1
                (mword_of_int 24 : mword 12) F5 (trap_res b + (K - 8))%nat (fc_ip Cf) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hcip").
      { iApply (fci_3c with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hcip".
      iEval (rewrite Hai) in "Hcip".
      set (F6 := <[Regidx Ra5 := regval_into_reg (fc_ip Cf)]> F5).
      assert (HF6s1 : F6 !!! Regidx Rs1 = fnode k)
        by (rewrite /F6 upd_ne; [exact HF5s1 | vm_compute; discriminate]).
      assert (Hpp3e : add_vec_int (mword_of_int (FC + 0x3c) : mword 64) 2
                      = mword_of_int (FC + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3e) in "Hpc".
      iApply (wp_cmv_s_sconf (mword_of_int (FC + 0x3e)) Rs5 Ra5 F6 (trap_res b + (K - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (fci_3e with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
      set (F7 := <[Regidx Rs5 := regval_into_reg
                    (add_vec zero_reg (F6 !!! Regidx Ra5))]> F6).
      assert (HF7s1 : F7 !!! Regidx Rs1 = fnode k)
        by (rewrite /F7 upd_ne; [exact HF6s1 | vm_compute; discriminate]).
      assert (Hpp40 : add_vec_int (mword_of_int (FC + 0x3e) : mword 64) 2
                      = mword_of_int (FC + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      (* ---- +0x40 / +0x44: empty the slot.  [f->type = FD_NONE] is what
             makes the payload [emp], so the table gets the slot back with
             nothing in it while this closer keeps the pipe end. ---- *)
      assert (Har : add_vec (rget F7 Rs1) (sign_extend' 64 (mword_of_int 4 : mword 12))
                    = a_fref k).
      { rewrite (rget_ne F7 Rs1 ltac:(vm_compute; discriminate)) HF7s1. reflexivity. }
      iEval (rewrite -Har) in "Hcell".
      iApply (wp_sw_zero_s_sconf (mword_of_int (FC + 0x40)) Rs1
                (mword_of_int 4 : mword 12) F7 (trap_res b + (K - 8))%nat
                (mword_of_int 0 : mword 32) false
                with "Hcg Hpc [] Hcell").
      { iApply (fci_40 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell".
      iEval (rewrite Har) in "Hcell".
      assert (Hpp44 : add_vec_int (mword_of_int (FC + 0x40) : mword 64) 4
                      = mword_of_int (FC + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp44) in "Hpc".
      assert (Hat2 : add_vec (rget F7 Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))
                     = a_ftype k).
      { rewrite (rget_ne F7 Rs1 ltac:(vm_compute; discriminate)) HF7s1.
        rewrite /a_ftype. apply addv_sext0. }
      iEval (rewrite -Hat2) in "Hcty".
      iApply (wp_sw_zero_s_sconf (mword_of_int (FC + 0x44)) Rs1
                (mword_of_int 0 : mword 12) F7 (trap_res b + (K - 8))%nat (fc_type Cf) false
                with "Hcg Hpc [] Hcty").
      { iApply (fci_44 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hcty".
      iEval (rewrite Hat2) in "Hcty".
      assert (Hpp48 : add_vec_int (mword_of_int (FC + 0x44) : mword 64) 4
                      = mword_of_int (FC + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp48) in "Hpc".
      (* ---- the slot goes back FREE, and the payload leaves with us ---- *)
      set (C0 := MkFContent (mword_of_int 0 : mword 32) (fc_readable Cf)
                   (fc_writable Cf) (fc_pipe Cf) (fc_ip Cf) (fc_major Cf)).
      (* THE FREED SLOT GETS ITS IREF UNIT, out of the one the caller lent us.
         [file_core]'s untyped arm holds the entry's provisioned unit, so a
         free slot's payload carries one -- and this is the moment it has to
         be there, because [f->type = FD_NONE] is written and ftable.lock
         released BEFORE the type is tested, so on the FD_INODE arm the unit
         [iput] will make does not exist yet.  Each arm repays the loan below
         from what it does have. *)
      iAssert (file_pay γf k 1 C0) with "[Hpn Hoh0 Hiru]" as "Hpy0".
      { iExists pn0. iFrame "Hpn".
        rewrite /file_payload /file_core /C0 /pn0; cbn [fc_type fp_ocv].
        rewrite bool_decide_eq_false_2; [|by vm_compute].
        rewrite bool_decide_eq_false_2; [|by vm_compute].
        rewrite bool_decide_eq_false_2; [|by vm_compute].
        rewrite (file_armed_none C0 ltac:(rewrite /C0 /FD_NONE; reflexivity)).
        iSplitL "Hiru"; [iApply iref_slot_frac; iExact "Hiru" | iExact "Hoh0"]. }
      (* NB: [Hfd] is NOT handed over.  The free arm of [fslot] holds no fd
         slots, and the unit the destroyed reference was accounted by is
         exactly what the postcondition returns -- framing it here would
         drain the supply one unit per close. *)
      iDestruct ("Hback" $! (delete k Mg) with "[%] [Hcell Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hpy0]")
        as "Hslots".
      { intros j Hj. rewrite lookup_delete_ne; [reflexivity | congruence]. }
      { rewrite /fslot lookup_delete. iFrame "Hcell". iExists C0.
        iSplitR; [iPureIntro; rewrite /C0 /FD_NONE; reflexivity|].
        rewrite /file_fields /C0;
          cbn [fc_type fc_readable fc_writable fc_pipe fc_ip fc_major].
        iFrame "Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hpy0". }
      iAssert (ftable_res γf) with "[Hauth Hfdauth Hslots]" as "HRres".
      { iExists (delete k Mg). iFrame "Hauth Hfdauth Hslots".
        iPureIntro. intros j Hj.
        destruct (decide (j = k)) as [->|Hne];
          [rewrite lookup_delete in Hj; by destruct Hj as [? Hx]|].
        apply Hdom. by rewrite lookup_delete_ne in Hj. }
      (* ---- +0x48/+0x4c a0 := &ftable ; +0x50 jal release ---- *)
      iApply (wp_auipc_s_sconf (mword_of_int (FC + 0x48)) Ra0
                (mword_of_int 0x1e : mword 20) F7 (trap_res b + (K - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (fci_48 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (G1 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (mword_of_int (FC + 0x48) : mword 64)
                       (auipc_off (mword_of_int 0x1e : mword 20)))]> F7).
      assert (Hpp4c : add_vec_int (mword_of_int (FC + 0x48) : mword 64) 4
                      = mword_of_int (FC + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4c) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (FC + 0x4c)) Ra0 Ra0
                (mword_of_int 862 : mword 12) G1 (trap_res b + (K - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (fci_4c with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
      set (G2 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (G1 !!! Regidx Ra0)
                       (sign_extend' 64 (mword_of_int 862 : mword 12)))]> G1).
      assert (HG2a0 : G2 !!! Regidx Ra0 = ftable_addr).
      { rewrite /G2 upd_eq /G1 upd_eq. rewrite /ftable_addr.
        apply bv_eq; vm_compute; reflexivity. }
      assert (Hpp50 : add_vec_int (mword_of_int (FC + 0x4c) : mword 64) 4
                      = mword_of_int (FC + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp50) in "Hpc".
      iApply (wp_jal_s_sconf (mword_of_int (FC + 0x50)) Rra
                (mword_of_int 2083528 : mword 21) G2 (trap_res b + (K - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (fci_50 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (G3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (FC + 0x50) : mword 64) 4)]> G2).
      assert (Htgtrel2 : add_vec (mword_of_int (FC + 0x50) : mword 64)
                           (sign_extend' 64 (mword_of_int 2083528 : mword 21))
                         = mword_of_int KernelSyms.release)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtrel2) in "Hpc".
      assert (HG3a0 : G3 !!! Regidx Ra0 = ftable_addr)
        by (rewrite /G3 upd_ne; [exact HG2a0 | vm_compute; discriminate]).
      assert (HG3ra : G3 !!! Regidx Rra
                      = add_vec_int (mword_of_int (FC + 0x50) : mword 64) 4)
        by (rewrite /G3; apply upd_eq).
      (* the four fields ff parked in callee-saved registers survive it *)
      assert (HG3cs : forall c : mword 5, is_cs_idx c = true ->
                G3 !!! Regidx c = F7 !!! Regidx c).
      { intros c Hcs.
        rewrite /G3 upd_ne; [| regne].
        rewrite /G2 upd_ne; [| regne].
        rewrite /G1 upd_ne; [reflexivity | regne]. }
      assert (HF7s2 : F7 !!! Regidx Rs2 = sign_extend' 64 (fc_type Cf)).
      { rewrite /F7 upd_ne; [| vm_compute; discriminate].
        rewrite /F6 upd_ne; [| vm_compute; discriminate].
        rewrite /F5 upd_ne; [| vm_compute; discriminate].
        rewrite /F4 upd_ne; [| vm_compute; discriminate].
        rewrite /F3 upd_ne; [| vm_compute; discriminate].
        rewrite /F2 upd_ne; [| vm_compute; discriminate].
        exact HF1s2. }
      assert (HF7s3 : F7 !!! Regidx Rs3
                      = add_vec zero_reg (zero_extend' 64 (fc_writable Cf : mword 8))).
      { rewrite /F7 upd_ne; [| vm_compute; discriminate].
        rewrite /F6 upd_ne; [| vm_compute; discriminate].
        rewrite /F5 upd_ne; [| vm_compute; discriminate].
        rewrite /F4 upd_ne; [| vm_compute; discriminate].
        rewrite /F3 upd_eq. by rewrite HF2a5. }
      assert (HF7s4 : F7 !!! Regidx Rs4 = add_vec zero_reg (fc_pipe Cf)).
      { rewrite /F7 upd_ne; [| vm_compute; discriminate].
        rewrite /F6 upd_ne; [| vm_compute; discriminate].
        rewrite /F5 upd_eq. rewrite /F4 upd_eq. reflexivity. }
      assert (HF7s5 : F7 !!! Regidx Rs5 = add_vec zero_reg (fc_ip Cf)).
      { rewrite /F7 upd_eq. rewrite /F6 upd_eq. reflexivity. }
      assert (HG3sp : G3 !!! Regidx csp_rs1 = spr).
      { rewrite (HG3cs csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite /F7 upd_ne; [| vm_compute; discriminate].
        rewrite /F6 upd_ne; [| vm_compute; discriminate].
        rewrite /F5 upd_ne; [| vm_compute; discriminate].
        rewrite /F4 upd_ne; [| vm_compute; discriminate].
        rewrite /F3 upd_ne; [| vm_compute; discriminate].
        rewrite /F2 upd_ne; [| vm_compute; discriminate].
        rewrite /F1 upd_ne; [exact HD2sp | vm_compute; discriminate]. }
      (* the acquire handed the window index out as [trap_res b + N]; release
         wants it as [trap_res outb + N] with [outb = match n with O => eb
         | S _ => false end].  Those are the same bool -- [cpu_own] forces
         it -- so this is a pure re-spelling, and it is what makes the
         acquire/release pair compose back to [N]. *)
      iEval (rewrite Houtb) in "Hcg".
      iApply (Release.wp_release_sconf KT1 γfl ftable_addr "ftable"%string
                (ftable_res γf) G3 n eb p (K - 8)%nat
                ({["ftable"]} ∪ lks)
                ltac:(rewrite HG3a0; apply bv_eq; vm_compute; reflexivity)
                ltac:(lia)
                with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay").
      { iExact "Hlock". }
      iIntros (CIDr2 Hsr2 mr2) "Hcg Hpc %Hrel2 Hcnt".
      (* fileclose is BALANCED on this arm too. *)
      assert (Hsetback : ({["ftable"]} ∪ lks) ∖ {["ftable"]} = lks)
      by (apply locks_add_del_below; lkbelow).
      iEval (rewrite Hsetback) in "Hcnt".
      iEval (rewrite <- Houtb) in "Hcg". iEval (rewrite <- Houtb) in "Hcnt".
      rewrite <- Houtb in Hsr2.
      pose proof Hrel2 as Hrel2_cs.
      assert (Hpc54 : ret_pc (G3 !!! Regidx Rra) = mword_of_int (FC + 0x54)).
      { rewrite HG3ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc54) in "Hpc".
      assert (Hmr2s2 : mr2 !!! Regidx Rs2 = sign_extend' 64 (fc_type Cf)).
      { rewrite (callee_saved_lookup Hrel2_cs Rs2 ltac:(vm_compute; reflexivity)).
        rewrite (HG3cs Rs2 ltac:(vm_compute; reflexivity)). exact HF7s2. }
      assert (Hmr2s3 : mr2 !!! Regidx Rs3
                       = add_vec zero_reg (zero_extend' 64 (fc_writable Cf : mword 8))).
      { rewrite (callee_saved_lookup Hrel2_cs Rs3 ltac:(vm_compute; reflexivity)).
        rewrite (HG3cs Rs3 ltac:(vm_compute; reflexivity)). exact HF7s3. }
      assert (Hmr2s4 : mr2 !!! Regidx Rs4 = add_vec zero_reg (fc_pipe Cf)).
      { rewrite (callee_saved_lookup Hrel2_cs Rs4 ltac:(vm_compute; reflexivity)).
        rewrite (HG3cs Rs4 ltac:(vm_compute; reflexivity)). exact HF7s4. }
      assert (Hmr2s5 : mr2 !!! Regidx Rs5 = add_vec zero_reg (fc_ip Cf)).
      { rewrite (callee_saved_lookup Hrel2_cs Rs5 ltac:(vm_compute; reflexivity)).
        rewrite (HG3cs Rs5 ltac:(vm_compute; reflexivity)). exact HF7s5. }
      assert (Hmr2sp : mr2 !!! Regidx csp_rs1 = pa_stk sp0 8).
      { rewrite (callee_saved_lookup Hrel2_cs csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite HG3sp. exact HsprS. }
      (* ---- +0x54 c.li a5,1 ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (FC + 0x54)) Ra5
                (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                mr2 (K - 8)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) fc_li1_val
                with "Hcg Hpc []").
      { iApply (fci_54 with "Htext"). }
      iIntros (CIDt1 Hst1) "Hcg Hpc".
      set (H1 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> mr2).
      assert (HH1a5 : H1 !!! Regidx Ra5 = (mword_of_int 1 : mword 64))
        by (rewrite /H1; apply upd_eq).
      assert (HH1s2 : H1 !!! Regidx Rs2 = sign_extend' 64 (fc_type Cf))
        by (rewrite /H1 upd_ne; [exact Hmr2s2 | vm_compute; discriminate]).
      assert (Hpp56 : add_vec_int (mword_of_int (FC + 0x54) : mword 64) 2
                      = mword_of_int (FC + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp56) in "Hpc".
      (* ---- +0x56 beq s2,a5 : the FD_PIPE test ---- *)
      assert (Hcmp56 : eq_vec (rget H1 Rs2) (rget H1 Ra5)
                       = eq_vec (fc_type Cf) (mword_of_int 1 : mword 32)).
      { rewrite (rget_ne H1 Rs2 ltac:(vm_compute; discriminate)).
        rewrite (rget_ne H1 Ra5 ltac:(vm_compute; discriminate)).
        rewrite HH1a5 HH1s2. apply fc_ty_eq1. }
      assert (Htgt98 : add_vec (mword_of_int (FC + 0x56) : mword 64)
                         (sign_extend' 64 (mword_of_int 66 : mword 13))
                       = mword_of_int (FC + 0x98))
        by (apply bv_eq; vm_compute; reflexivity).
      (* the frame slots the restore block will read back *)
      assert (HD2s2 : D2 !!! Regidx Rs2 = m !!! Regidx Rs2).
      { rewrite /D2 upd_ne; [| vm_compute; discriminate].
        rewrite /D1 upd_ne; [| vm_compute; discriminate].
        apply Hmthr; vm_compute; first [reflexivity | discriminate]. }
      assert (HD2s3 : D2 !!! Regidx Rs3 = m !!! Regidx Rs3).
      { rewrite /D2 upd_ne; [| vm_compute; discriminate].
        rewrite /D1 upd_ne; [| vm_compute; discriminate].
        apply Hmthr; vm_compute; first [reflexivity | discriminate]. }
      assert (HD2s4 : D2 !!! Regidx Rs4 = m !!! Regidx Rs4).
      { rewrite /D2 upd_ne; [| vm_compute; discriminate].
        rewrite /D1 upd_ne; [| vm_compute; discriminate].
        apply Hmthr; vm_compute; first [reflexivity | discriminate]. }
      assert (HD2s5 : D2 !!! Regidx Rs5 = m !!! Regidx Rs5).
      { rewrite /D2 upd_ne; [| vm_compute; discriminate].
        rewrite /D1 upd_ne; [| vm_compute; discriminate].
        apply Hmthr; vm_compute; first [reflexivity | discriminate]. }
      iEval (rewrite HD2s2) in "Hb4". iEval (rewrite HD2s3) in "Hb5".
      iEval (rewrite HD2s4) in "Hb6". iEval (rewrite HD2s5) in "Hb7".
      assert (HR1ra : R1 !!! Regidx Rra = m !!! Regidx Rra)
        by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
      assert (HR1s0 : R1 !!! Regidx Rs0 = m !!! Regidx Rs0)
        by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
      assert (HR1s1 : R1 !!! Regidx Rs1 = m !!! Regidx Rs1)
        by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
      iEval (rewrite HR1ra) in "Hb1". iEval (rewrite HR1s0) in "Hb2".
      iEval (rewrite HR1s1) in "Hb3".
      destruct (decide (fc_type Cf = FD_PIPE)) as [Hpipe | Hnpipe].
      + (* ============ FD_PIPE: pipeclose(ff.pipe, ff.writable) ======= *)
        iApply (wp_beq_taken_s_sconf (mword_of_int (FC + 0x56))
                  (mword_of_int 66 : mword 13) Ra5 Rs2 H1 (K - 8)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rewrite Hcmp56 Hpipe; by vm_compute)
                  ltac:(rewrite Htgt98; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (fci_56 with "Htext"). }
        iApply bi.later_intro. iIntros (CIDp1 Hsp1) "Hcg Hpc".
        iEval (rewrite Htgt98) in "Hpc".
        assert (HH1s3 : H1 !!! Regidx Rs3
                        = add_vec zero_reg (zero_extend' 64 (fc_writable Cf : mword 8)))
          by (rewrite /H1 upd_ne; [exact Hmr2s3 | vm_compute; discriminate]).
        assert (HH1s4 : H1 !!! Regidx Rs4 = add_vec zero_reg (fc_pipe Cf))
          by (rewrite /H1 upd_ne; [exact Hmr2s4 | vm_compute; discriminate]).
        assert (HH1sp : H1 !!! Regidx csp_rs1 = pa_stk sp0 8)
          by (rewrite /H1 upd_ne; [exact Hmr2sp | vm_compute; discriminate]).
        (* +0x98 c.mv a1,s3 *)
        iApply (wp_cmv_s_sconf (mword_of_int (FC + 0x98)) Ra1 Rs3 H1 (K - 8)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (fci_98 with "Htext"). }
        iIntros (CIDp2 Hsp2) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (P1 := <[Regidx Ra1 := regval_into_reg
                      (add_vec zero_reg (H1 !!! Regidx Rs3))]> H1).
        assert (Hpp9a : add_vec_int (mword_of_int (FC + 0x98) : mword 64) 2
                        = mword_of_int (FC + 0x9a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp9a) in "Hpc".
        (* +0x9a c.mv a0,s4 *)
        iApply (wp_cmv_s_sconf (mword_of_int (FC + 0x9a)) Ra0 Rs4 P1 (K - 8)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (fci_9a with "Htext"). }
        iIntros (CIDp3 Hsp3) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (P2 := <[Regidx Ra0 := regval_into_reg
                      (add_vec zero_reg (P1 !!! Regidx Rs4))]> P1).
        assert (Hpp9c : add_vec_int (mword_of_int (FC + 0x9a) : mword 64) 2
                        = mword_of_int (FC + 0x9c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp9c) in "Hpc".
        (* +0x9c jal pipeclose *)
        iApply (wp_jal_s_sconf (mword_of_int (FC + 0x9c)) Rra
                  (mword_of_int 864 : mword 21) P2 (K - 8)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
        { iApply (fci_9c with "Htext"). }
        iIntros (CIDp4 Hsp4) "Hcg Hpc".
        set (P3 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (FC + 0x9c) : mword 64) 4)]> P2).
        assert (Htgtpc : add_vec (mword_of_int (FC + 0x9c) : mword 64)
                           (sign_extend' 64 (mword_of_int 864 : mword 21))
                         = mword_of_int KernelSyms.pipeclose)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgtpc) in "Hpc".
        assert (HP3a0 : P3 !!! Regidx Ra0 = fc_pipe Cf).
        { rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /P2 upd_eq.
          rewrite /P1 upd_ne; [| vm_compute; discriminate].
          rewrite HH1s4. rewrite add_vec_zero_l. apply add_vec_zero_l. }
        assert (HP3a1 : P3 !!! Regidx Ra1
                        = add_vec zero_reg (zero_extend' 64 (fc_writable Cf : mword 8))).
        { rewrite /P3 upd_ne; [| vm_compute; discriminate].
          rewrite /P2 upd_ne; [| vm_compute; discriminate].
          rewrite /P1 upd_eq. rewrite HH1s3. apply add_vec_zero_l. }
        assert (HP3ra : P3 !!! Regidx Rra
                        = add_vec_int (mword_of_int (FC + 0x9c) : mword 64) 4)
          by (rewrite /P3; apply upd_eq).
        assert (HP3cs : forall c : mword 5, is_cs_idx c = true ->
                  P3 !!! Regidx c = H1 !!! Regidx c).
        { intros c Hcs.
          rewrite /P3 upd_ne; [| regne].
          rewrite /P2 upd_ne; [| regne].
          rewrite /P1 upd_ne; [reflexivity | regne]. }
        assert (HP3sp : P3 !!! Regidx csp_rs1 = pa_stk sp0 8)
          by (rewrite (HP3cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HH1sp).
        (* the payload IS the pipe end this call closes *)
        iEval (rewrite /file_core Hpipe bool_decide_eq_true_2; [|reflexivity])
          in "Hcore".
        (* the pipe arm's own iref unit REPAYS the loan deposited above: a pipe
           never spent it, so [file_core] still has it and pipeclose has no
           use for it. *)
        iDestruct "Hcore" as "(#Hispipe & Hpref & Hiru)".
        iEval (rewrite /fileclose_env Hpipe bool_decide_eq_true_2; [|reflexivity])
          in "Henv".
        rewrite /fileclose_pipe_env.
        iDestruct "Henv" as "(%Hn2 & #Hprocs & #Hkmem & Hav)".
        iEval (rewrite -HP3a0) in "Hispipe".
        (* the pure premises as NAMED facts: a tactic in an argument position
           whose expected type is still an evar is the divergence trap. *)
        assert (Hw1 : eq_vec (P3 !!! Regidx Ra1) (zero_reg : mword 64)
                      = negb (fc_wbool Cf)).
        { rewrite HP3a1 /fc_wbool. apply fc_wbool_arg. }
        assert (Hav22 : (22 <= K - 8)%nat) by lia.
        (* [cpu_own] was delivered at the hart release returned on; five
           plain instructions have moved us. *)
        iDestruct (cpu_own_transport CIDr2 CIDp4 n eb p b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iApply (Pipeclose.wp_pipeclose_sconf (CID := CIDp4)  (fcn_procs fn) (fp_lock pn)
                  (fp_pipe pn) (fc_wbool Cf) (fcn_kmem fn) (fcn_kalloc fn)
                  (mword_of_int KernelSyms.kmem)
                  (mword_of_int (KernelSyms.kmem + 24)) on
                  P3 n eb p (K - 8)%nat b
                  lks Hw1 Hav22 Hn2 eq_refl eq_refl
                  ltac:(lkbelow)
                  with "Hcg Hcnt Htext Hpc Hispipe Hpref Hkmem Hav Hprocs").
        all: try lkbelow.
        iIntros (CIDp5 Hsp5 mp) "Hcg Hcnt Hpc %Hpcs Hav".
        pose proof Hpcs as Hpcs_cs.
        assert (Hpca0 : ret_pc (P3 !!! Regidx Rra) = mword_of_int (FC + 0xa0)).
        { rewrite HP3ra. apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Hpca0) in "Hpc".
        assert (Hmpsp : mp !!! Regidx csp_rs1 = pa_stk sp0 8)
          by (rewrite (callee_saved_lookup Hpcs_cs csp_rs1 ltac:(vm_compute; reflexivity));
              exact HP3sp).
        assert (Htgt8e : add_vec (mword_of_int (FC + 0xa8) : mword 64)
                           (sign_extend' 64 (sign_extend' 21
                              (concat_vec (mword_of_int 2035 : mword 11) ('b"0"))))
                         = mword_of_int (FC + 0x8e))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (fc_restore4 (CID0 := CIDp5) mp (K - 8)%nat sp0
                  (m !!! Regidx Rs2) (m !!! Regidx Rs3) (m !!! Regidx Rs4)
                  (m !!! Regidx Rs5)
                  (FC + 0xa0) (FC + 0xa2) (FC + 0xa4) (FC + 0xa6) (FC + 0xa8)
                  (sign_extend' 21 (concat_vec (mword_of_int 2035 : mword 11) ('b"0")))
                  p b Hmpsp
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  Htgt8e
                  with "Hcg Hpc [] [] [] [] [] Hb4 Hb5 Hb6 Hb7").
        { iApply (fci_a0 with "Htext"). }
        { iApply (fci_a2 with "Htext"). }
        { iApply (fci_a4 with "Htext"). }
        { iApply (fci_a6 with "Htext"). }
        { iApply (fci_a8 with "Htext"). }
        iIntros (CIDp6 Hsp6 Mr) "(%HMrsp & %HMr2 & %HMr3 & %HMr4 & %HMr5 & %HMrthr)
                                 Hcg Hpc Hb4 Hb5 Hb6 Hb7".
        assert (HMrall : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                  r <> Rs0 -> r <> Rs1 -> Mr !!! Regidx r = m !!! Regidx r).
        { intros r Hr N2 N8 N9.
          destruct (decide (r = Rs2)) as [->|Nr2]; [exact HMr2|].
          destruct (decide (r = Rs3)) as [->|Nr3]; [exact HMr3|].
          destruct (decide (r = Rs4)) as [->|Nr4]; [exact HMr4|].
          destruct (decide (r = Rs5)) as [->|Nr5]; [exact HMr5|].
          rewrite (HMrthr r Hr Nr2 Nr3 Nr4 Nr5).
          rewrite (callee_saved_lookup Hpcs_cs r Hr).
          rewrite (HP3cs r Hr).
          rewrite /H1 upd_ne; [| regne].
          rewrite (callee_saved_lookup Hrel2_cs r Hr).
          rewrite (HG3cs r Hr).
          rewrite /F7 upd_ne; [| regne].
          rewrite /F6 upd_ne; [| regne].
          rewrite /F5 upd_ne; [| regne].
          rewrite /F4 upd_ne; [| regne].
          rewrite /F3 upd_ne; [| regne].
          rewrite /F2 upd_ne; [| regne].
          rewrite /F1 upd_ne; [| regne].
          rewrite /D2 upd_ne; [| regne].
          rewrite /D1 upd_ne; [| regne].
          exact (Hmthr r Hr N2 N8 N9). }
        iApply (fc_epi (CID0 := CIDp6) m Mr K sp0 (m !!! Regidx Rra)
                  (m !!! Regidx Rs0) (m !!! Regidx Rs1)
                  (m !!! Regidx Rs2) (m !!! Regidx Rs3) (m !!! Regidx Rs4)
                  (m !!! Regidx Rs5) u8 p b
                  ltac:(lia) eq_refl eq_refl eq_refl eq_refl HMrsp HMrall
                  with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8").
        iIntros (CIDp7 Hsp7 mf) "%Hcsf Hcg Hpc".
        iDestruct (cpu_own_transport CIDp5 CIDp7 n eb p b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        (* ONE WIDE HOP again: pipeclose does not thread the complement
           either, so it never left the entry hart. *)
        iDestruct (trap_csrs_ext_transport CID CIDp7 eb p ltac:(ext_chain Hebf b)
                     with "Hextc") as "Hextc".
        iDestruct (cpu_claim_ext_transport CID CIDp7 eb p ltac:(ext_chain Hebf b)
                     with "Hextm") as "Hextm".
        iSpecialize ("Hcont" $! CIDp7 with "[]"); [iPureIntro; wp_next_chain|].
        iApply ("Hcont" $! mf with "Hcg Hcnt Hextc Hextm [Hpc] [%] Hfd Hiru [Hav] Hpbare").
        { iEval (rewrite /ret_tgt). iExact "Hpc". }
        { exact Hcsf. }
        { rewrite /fileclose_env_out Hpipe bool_decide_eq_true_2; [|reflexivity].
          rewrite /fileclose_pipe_out. iExact "Hav". }
      + (* ============ not a pipe: the inode test at +0x5a ============ *)
        iApply (wp_beq_fall_s_sconf (mword_of_int (FC + 0x56))
                  (mword_of_int 66 : mword 13) Ra5 Rs2 H1 (K - 8)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rewrite Hcmp56; apply eq_vec_false_iff; exact Hnpipe)
                  with "Hcg Hpc []").
        { iApply (fci_56 with "Htext"). }
        iIntros (CIDn1 Hsn1) "Hcg Hpc".
        assert (Hpp5a : add_vec_int (mword_of_int (FC + 0x56) : mword 64) 4
                        = mword_of_int (FC + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp5a) in "Hpc".
        (* +0x5a addiw a5,s2,-2 *)
        iApply (wp_addiw_s_sconf (mword_of_int (FC + 0x5a)) Ra5 Rs2
                  (mword_of_int 4094 : mword 12) H1 (K - 8)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (fci_5a with "Htext"). }
        iIntros (CIDn2 Hsn2) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (Q1 := <[Regidx Ra5 := regval_into_reg
                      (sign_extend' 64 (subrange_vec_dec
                         (add_vec (rget H1 Rs2)
                            (sign_extend' 64 (mword_of_int 4094 : mword 12))) 31 0))]> H1).
        assert (HQ1a5 : Q1 !!! Regidx Ra5
                        = sign_extend' 64 (subrange_vec_dec
                            (add_vec (sign_extend' 64 (fc_type Cf))
                               (sign_extend' 64 (mword_of_int 4094 : mword 12))) 31 0)).
        { rewrite /Q1 upd_eq.
          by rewrite (rget_ne H1 Rs2 ltac:(vm_compute; discriminate)) HH1s2. }
        assert (Hpp5e : add_vec_int (mword_of_int (FC + 0x5a) : mword 64) 4
                        = mword_of_int (FC + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp5e) in "Hpc".
        (* +0x5e c.li a4,1 *)
        iApply (wp_cli_s_sconf (mword_of_int (FC + 0x5e)) Ra4
                  (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                  Q1 (K - 8)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok) fc_li1_val
                  with "Hcg Hpc []").
        { iApply (fci_5e with "Htext"). }
        iIntros (CIDn3 Hsn3) "Hcg Hpc".
        set (Q2 := <[Regidx Ra4 := regval_into_reg (mword_of_int 1 : mword 64)]> Q1).
        assert (HQ2a4 : Q2 !!! Regidx Ra4 = (mword_of_int 1 : mword 64))
          by (rewrite /Q2; apply upd_eq).
        assert (HQ2a5 : Q2 !!! Regidx Ra5 = Q1 !!! Regidx Ra5)
          by (rewrite /Q2 upd_ne; [reflexivity | vm_compute; discriminate]).
        assert (HQ2cs : forall c : mword 5, is_cs_idx c = true ->
                  Q2 !!! Regidx c = H1 !!! Regidx c).
        { intros c Hcs.
          rewrite /Q2 upd_ne; [| regne].
          rewrite /Q1 upd_ne; [reflexivity | regne]. }
        assert (HQ2sp : Q2 !!! Regidx csp_rs1 = pa_stk sp0 8).
        { rewrite (HQ2cs csp_rs1 ltac:(vm_compute; reflexivity)).
          rewrite /H1 upd_ne; [exact Hmr2sp | vm_compute; discriminate]. }
        assert (Hcmp60 : zopz0zKzJ_u (rget Q2 Ra4) (rget Q2 Ra5)
                         = zopz0zKzJ_u (mword_of_int 1 : mword 64)
                             (sign_extend' 64 (subrange_vec_dec
                                (add_vec (sign_extend' 64 (fc_type Cf))
                                   (sign_extend' 64 (mword_of_int 4094 : mword 12))) 31 0))).
        { rewrite (rget_ne Q2 Ra4 ltac:(vm_compute; discriminate)).
          rewrite (rget_ne Q2 Ra5 ltac:(vm_compute; discriminate)).
          by rewrite HQ2a4 HQ2a5 HQ1a5. }
        assert (Hpp60 : add_vec_int (mword_of_int (FC + 0x5e) : mword 64) 2
                        = mword_of_int (FC + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp60) in "Hpc".
        assert (Htgtaa : add_vec (mword_of_int (FC + 0x60) : mword 64)
                           (sign_extend' 64 (mword_of_int 74 : mword 13))
                         = mword_of_int (FC + 0xaa))
          by (apply bv_eq; vm_compute; reflexivity).
        destruct (decide (fc_type Cf = FD_INODE \/ fc_type Cf = FD_DEVICE))
          as [Hinode | Hnone].
        * (* ======== FD_INODE / FD_DEVICE: begin_op(); iput(); end_op() === *)
          assert (Hib : (bool_decide (fc_type Cf = FD_INODE)
                         || bool_decide (fc_type Cf = FD_DEVICE)) = true).
          { apply orb_true_intro. destruct Hinode as [H|H]; [left|right];
              by apply bool_decide_eq_true_2. }
          iAssert (fileclose_fs_env fn n eb p) with "[Henv]" as "Henv".
          { rewrite /fileclose_env bool_decide_eq_false_2; [|exact Hnpipe].
            rewrite Hib. iExact "Henv". }
          (* THE PAYLOAD IS THE REFERENCE, and this closer holds ALL of it:
             [file_rest_join] gave fraction one, so the cancel token is
             whole and [FileInv.inode_pay_cancel] turns it into the inode
             reference iput consumes.  This is the one fupd fileclose
             performs, and the whole point of the payload being a
             cancellable invariant rather than a fraction of the reference
             (which does not exist -- see [FileInv.inode_pay]). *)
          iAssert (inode_pay (fp_icv pn) (fp_iq pn) (fp_ig pn) (fc_ip Cf)
                     (fc_wbool Cf) 1) with "[Hcore]" as "Hpl".
          { rewrite /file_core bool_decide_eq_false_2; [|exact Hnpipe].
            rewrite Hib. iExact "Hcore". }
          iApply fupd_wp.
          (* THE GATHER IS INSIDE THE CANCEL (B3).  The cinv parks the
             reference SHORT by [fp_iq pn] and the payload's own arm at
             [1 * fp_iq pn] is the exact complement, so what comes out is
             canonical and iput can spend it. *)
          iMod (inode_pay_cancel ⊤ (fp_icv pn) (fp_iq pn) (fp_ig pn) (fc_ip Cf)
                  (fc_wbool Cf) ltac:(solve_ndisj) with "Hpl") as "Hheld".
          iDestruct "Hheld" as (kk qq inum) "(%Hipe & %Hkk & %Hinumb & Href & Hru)".
          iModIntro.
          rewrite /fileclose_fs_env /fileclose_fs_env_nopid.
          (* FIVE pure conjuncts, not six: the bundle no longer pins
             [eb = true], and this arm runs at a generic index.  [n] and [p]
             still are pinned, and both substitutions stay. *)
          iDestruct "Henv" as "(%Hn0 & %Hpj & %Hjlt & %Hgl & %Hties &
                                #Hprocs & #Hrdy & Hbsl)".
          subst n. subst p.
          (* ---- THE TIES, DESTRUCTED ONCE ----
             [fclose_ties] says [fn]'s own names ARE the ambient ones, so the
             whole FS arm below is spelled AMBIENTLY and the eighteen
             equations are used only where a resource ARRIVES at [fn]'s
             spelling ([Hbsl]) or has to LEAVE at it (the postcondition's
             [fileclose_fs_out]).  That is [FsSyscalls.fs_world_all]'s idiom
             with the substitution going the other way: there the ties are
             [->]d into the ambient predicate, here the callees are
             instantiated at the ambient names directly. *)
          destruct Hties as [Ht_uart Ht_disk Ht_dlock Ht_kmem Ht_kalloc Ht_bio Ht_log Ht_dev Ht_ireg Ht_tlock Ht_bms Ht_ist Ht_nib Ht_size].
          (* the [fcn_bio] tie has nothing to rewrite in a [bslots] any
             more: the slot supply is at the CANONICAL ghost name, so the
             count no longer mentions the bio record at all. *)
          (* ---- AND THE FILE SYSTEM, OUT OF [fs_ready] ----
             Each row is one projection.  What used to be [fileclose_ic_env]
             (nine pure facts and six invariants) and [fileclose_bm] (the two
             superblock cells and the threaded [bitmap_res]) is now this
             block: the cells come back at [□], and the bitmap is the
             persistent invariant, so nothing here is consumable. *)
          iDestruct (FsReady.fs_ready_geom with "Hrdy") as "%Hgok".
          iDestruct (FsReady.fs_ready_bio with "Hrdy") as "#Hbio".
          iDestruct (FsReady.fs_ready_log with "Hrdy") as "#Hlog".
          iDestruct (FsReady.fs_ready_seam with "Hrdy") as "#Hseam".
          iDestruct (FsReady.fs_ready_gen with "Hrdy") as "#Hgen".
          iDestruct (FsReady.fs_ready_disk with "Hrdy") as "[#Hdev Hdd]".
          (* the three ring pages are QUANTIFIED in [fs_ready] (fs-cfg-boot
             R1); the callees take them as parameters, so this arm simply
             runs at the predicate's own witness -- the bundle no longer
             carries disk-fabric rows at all. *)
          iDestruct "Hdd" as (pdd pavd pud) "[#Hgeod #Hdlkd]".
          iDestruct (FsReady.fs_ready_icache with "Hrdy")
            as "(#Hitab & #Hitinv & #Hescrows & #Hslks)".
          iDestruct (FsReady.fs_ready_region with "Hrdy") as "[#Hireg #Hropen]".
          iDestruct (FsReady.fs_ready_sb_four with "Hrdy")
            as "(_ & #Hsbi & _ & #Hsbb)".
          iDestruct (FsReady.fs_ready_bitmap with "Hrdy") as "#Hbmres".
          pose proof (FsReady.fgo_loggeom Hgok) as Hgeom.
          pose proof (FsReady.fgo_size Hgok) as Hsz.
          pose proof (FsReady.fgo_bm_nn Hgok) as Hbm0.
          pose proof (FsReady.fgo_bm_cov Hgok) as Hbmcov.
          pose proof (FsReady.fgo_bm_out Hgok) as Hbmlog.
          pose proof (FsReady.fgo_ist_nn Hgok) as Hist0.
          pose proof (FsReady.fgo_covbelow Hgok) as Hcovb.
          pose proof (FsReady.fgo_iblocks Hgok) as Hinumgeo.
          (* the entry's own escrow and sleeplock, out of the two families:
             a closer cannot name the slot in its contract, so it takes
             every slot's and picks the one the reference names *)
          iDestruct (ic_escrows_acc _ kk Hkk with "Hescrows") as "#Hescrow".
          iDestruct (ic_sleeplocks_lookup _ kk Hkk with "Hslks") as (gil gisl) "#Hslk".
          destruct (Hinumgeo inum Hinumb) as [Hiblk Hiblog].
          (* NO [subst b] HERE.  [Houtb] does read [b = eb] at [noff = 0], but
             the arm is proved at the generic index: [cpu_own]'s slot stays
             [eb], a leaf instruction's index stays [b], and the three
             sleeping callees take the complement rather than an [eb] pin. *)
          iApply (wp_bgeu_taken_s_sconf (mword_of_int (FC + 0x60))
                    (mword_of_int 74 : mword 13) Ra5 Ra4 Q2 (K - 8)%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    ltac:(rewrite Hcmp60; by apply fc_ty_inode_iff)
                    ltac:(rewrite Htgtaa; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (fci_60 with "Htext"). }
          iApply bi.later_intro. iIntros (CIDf1 Hsf1) "Hcg Hpc".
          iEval (rewrite Htgtaa) in "Hpc".
          (* ---- +0xaa jal begin_op ---- *)
          iApply (wp_jal_s_sconf (mword_of_int (FC + 0xaa)) Rra
                    (mword_of_int 2095772 : mword 21) Q2 (K - 8)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
          { iApply (fci_aa with "Htext"). }
          iIntros (CIDf2 Hsf2) "Hcg Hpc".
          set (B1 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (FC + 0xaa) : mword 64) 4)]> Q2).
          assert (Htgtbo : add_vec (mword_of_int (FC + 0xaa) : mword 64)
                             (sign_extend' 64 (mword_of_int 2095772 : mword 21))
                           = mword_of_int KernelSyms.begin_op)
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgtbo) in "Hpc".
          assert (HB1ra : B1 !!! Regidx Rra
                          = add_vec_int (mword_of_int (FC + 0xaa) : mword 64) 4)
            by (rewrite /B1; apply upd_eq).
          assert (HB1cs : forall c : mword 5, is_cs_idx c = true ->
                    B1 !!! Regidx c = Q2 !!! Regidx c)
            by (intros c Hcs; rewrite /B1 upd_ne; [reflexivity | regne]).
          iDestruct (cpu_own_transport CIDr2 CIDf2 0 eb (proc_addr (fcn_j fn)) b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          (* the complement is still at the ENTRY hart -- neither acquire nor
             release nor the leaves between them thread it -- so it makes one
             wide hop to the hart begin_op is called on. *)
          iDestruct (trap_csrs_ext_transport CID CIDf2 eb (proc_addr (fcn_j fn))
                       ltac:(ext_chain Hebf b) with "Hextc") as "Hextc".
          iDestruct (cpu_claim_ext_transport CID CIDf2 eb (proc_addr (fcn_j fn))
                       ltac:(ext_chain Hebf b) with "Hextm") as "Hextm".
          iApply (BeginOp.wp_begin_op_sconf (CID := CIDf2)  (fcn_procs fn)
                    (fcn_j fn) (fcn_plock fn) fsc_bio icfg_log fsc_fs
                    fsc_cov fsc_logst icfg_dev
                    pidv (fcn_dq fn) B1 (K - 8)%nat eb b lks Vpr
                    ltac:(lia) Hjlt Hgl
                    ltac:(lkbelow)
                    with "Hcg Hcnt Hextc Hextm Htext Hpc Hlog Hpbare Hprocs").
          all: try lkbelow.
          iIntros (CIDf3 Hsf3 mb) "%Hbcs Hcg Hcnt Hextc Hextm Hpc Hpbare Hop".
          pose proof Hbcs as Hbcs_cs.
          assert (Hpcae : ret_pc (B1 !!! Regidx Rra) = mword_of_int (FC + 0xae)).
          { rewrite HB1ra. apply bv_eq; vm_compute; reflexivity. }
          iEval (rewrite Hpcae) in "Hpc".
          assert (Hmbs5 : mb !!! Regidx Rs5 = add_vec zero_reg (fc_ip Cf)).
          { rewrite (callee_saved_lookup Hbcs_cs Rs5 ltac:(vm_compute; reflexivity)).
            rewrite (HB1cs Rs5 ltac:(vm_compute; reflexivity)).
            rewrite (HQ2cs Rs5 ltac:(vm_compute; reflexivity)).
            rewrite /H1 upd_ne; [exact Hmr2s5 | vm_compute; discriminate]. }
          (* ---- +0xae c.mv a0,s5 ---- *)
          iApply (wp_cmv_s_sconf (mword_of_int (FC + 0xae)) Ra0 Rs5 mb (K - 8)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc []").
          { iApply (fci_ae with "Htext"). }
          iIntros (CIDf4 Hsf4) "Hcg Hpc". iEval (rgne) in "Hcg".
          set (B2 := <[Regidx Ra0 := regval_into_reg
                        (add_vec zero_reg (mb !!! Regidx Rs5))]> mb).
          assert (HB2a0 : B2 !!! Regidx Ra0 = fc_ip Cf).
          { rewrite /B2 upd_eq. rewrite Hmbs5. rewrite add_vec_zero_l.
            apply add_vec_zero_l. }
          assert (Hppb0 : add_vec_int (mword_of_int (FC + 0xae) : mword 64) 2
                          = mword_of_int (FC + 0xb0)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hppb0) in "Hpc".
          (* ---- +0xb0 jal iput ---- *)
          iApply (wp_jal_s_sconf (mword_of_int (FC + 0xb0)) Rra
                    (mword_of_int 2093486 : mword 21) B2 (K - 8)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
          { iApply (fci_b0 with "Htext"). }
          iIntros (CIDf5 Hsf5) "Hcg Hpc".
          set (B3 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (FC + 0xb0) : mword 64) 4)]> B2).
          assert (Htgtip : add_vec (mword_of_int (FC + 0xb0) : mword 64)
                             (sign_extend' 64 (mword_of_int 2093486 : mword 21))
                           = mword_of_int KernelSyms.iput)
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgtip) in "Hpc".
          assert (HB3a0 : B3 !!! Regidx Ra0 = fc_ip Cf)
            by (rewrite /B3 upd_ne; [exact HB2a0 | vm_compute; discriminate]).
          assert (HB3ra : B3 !!! Regidx Rra
                          = add_vec_int (mword_of_int (FC + 0xb0) : mword 64) 4)
            by (rewrite /B3; apply upd_eq).
          assert (HB3cs : forall c : mword 5, is_cs_idx c = true ->
                    B3 !!! Regidx c = mb !!! Regidx c).
          { intros c Hcs.
            rewrite /B3 upd_ne; [| regne].
            rewrite /B2 upd_ne; [reflexivity | regne]. }
          iDestruct (cpu_own_transport CIDf3 CIDf5 0 eb (proc_addr (fcn_j fn)) b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          (* begin_op HANDED the complement back, so this hop matches
             [cpu_own]'s own span: two plain instructions. *)
          iDestruct (trap_csrs_ext_transport CIDf3 CIDf5 eb (proc_addr (fcn_j fn))
                       ltac:(ext_chain Hebf b) with "Hextc") as "Hextc".
          iDestruct (cpu_claim_ext_transport CIDf3 CIDf5 eb (proc_addr (fcn_j fn))
                       ltac:(ext_chain Hebf b) with "Hextm") as "Hextm".
          iApply (Iput.wp_iput_sconf (CID := CIDf5) (fcn_procs fn) (fcn_j fn)
                    (fcn_plock fn) fsc_uart fsc_disk fsc_dlock
                    pdd pavd pud fsc_bio
                    icfg_log fsc_ireg
                    fsc_itlock gil gisl
                    fsc_bmapstart
                    icfg_ist icfg_nib fsc_size
                    icfg_dev kk qq inum MAXOPBLOCKS
                    pidv (fcn_dq fn) DfracDiscarded DfracDiscarded
                    B3 (K - 8)%nat eb b lks Vpr
                    ltac:(lia) eq_refl Hkk Hgeom Hsz Hbm0 Hbmcov Hbmlog
                    Hist0 Hiblk Hiblog Hinumb Hcovb
                    ltac:(unfold iput_units, MAXOPBLOCKS; lia) Hjlt Hgl
                    ltac:(rewrite HB3a0; exact Hipe)
                    ltac:(lkbelow)
                    with "Hcg Hcnt Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hlog Hitab Hitinv
                          Hescrow Hireg Hropen Hslk [$Href $Hru] Hsbb Hsbi Hbmres Hpbare Hprocs
                          Hdev Hgeod Hdlkd Hbsl Hop").
          all: try lkbelow.
          (* the two superblock cells come back at [□] and are dropped: they
             are persistent conjuncts of [fs_ready], which this proof still
             holds. *)
          iIntros (CIDf6 Hsf6 mi ni) "%Hics Hcg Hcnt Hextc Hextm Hpc Hpbare _ _
                                      Hbsl %Hni Hop Hislot".
          pose proof Hics as Hics_cs.
          assert (Hpcb4 : ret_pc (B3 !!! Regidx Rra) = mword_of_int (FC + 0xb4)).
          { rewrite HB3ra. apply bv_eq; vm_compute; reflexivity. }
          iEval (rewrite Hpcb4) in "Hpc".
          (* ---- +0xb4 jal end_op ---- *)
          iApply (wp_jal_s_sconf (mword_of_int (FC + 0xb4)) Rra
                    (mword_of_int 2095902 : mword 21) mi (K - 8)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
          { iApply (fci_b4 with "Htext"). }
          iIntros (CIDf7 Hsf7) "Hcg Hpc".
          set (B4 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (FC + 0xb4) : mword 64) 4)]> mi).
          assert (Htgteo : add_vec (mword_of_int (FC + 0xb4) : mword 64)
                             (sign_extend' 64 (mword_of_int 2095902 : mword 21))
                           = mword_of_int KernelSyms.end_op)
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgteo) in "Hpc".
          assert (HB4ra : B4 !!! Regidx Rra
                          = add_vec_int (mword_of_int (FC + 0xb4) : mword 64) 4)
            by (rewrite /B4; apply upd_eq).
          assert (HB4cs : forall c : mword 5, is_cs_idx c = true ->
                    B4 !!! Regidx c = mi !!! Regidx c)
            by (intros c Hcs; rewrite /B4 upd_ne; [reflexivity | regne]).
          iDestruct (cpu_own_transport CIDf6 CIDf7 0 eb (proc_addr (fcn_j fn)) b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          iDestruct (trap_csrs_ext_transport CIDf6 CIDf7 eb (proc_addr (fcn_j fn))
                       ltac:(ext_chain Hebf b) with "Hextc") as "Hextc".
          iDestruct (cpu_claim_ext_transport CIDf6 CIDf7 eb (proc_addr (fcn_j fn))
                       ltac:(ext_chain Hebf b) with "Hextm") as "Hextm".
          iApply (EndOp.wp_end_op_sconf (CID := CIDf7)  (fcn_procs fn) (fcn_j fn)
                    (fcn_plock fn) fsc_uart fsc_disk fsc_dlock
                    pdd pavd pud fsc_bio
                    icfg_log fsc_fs fsc_cov fsc_logst
                    icfg_dev ni pidv (fcn_dq fn)
                    B4 (K - 8)%nat eb b lks Vpr
                    ltac:(lia) Hgeom Hjlt Hgl
                    ltac:(lkbelow)
                    with "Hcg Hcnt Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen Hpbare
                          Hprocs Hdev Hgeod Hdlkd Hop").
          all: try lkbelow.
          iIntros (CIDf8 Hsf8 me) "%Hecs Hcg Hcnt Hextc Hextm Hpc Hpbare".
          pose proof Hecs as Hecs_cs.
          assert (Hpcb8 : ret_pc (B4 !!! Regidx Rra) = mword_of_int (FC + 0xb8)).
          { rewrite HB4ra. apply bv_eq; vm_compute; reflexivity. }
          iEval (rewrite Hpcb8) in "Hpc".
          (* ---- the restore block and the epilogue ---- *)
          assert (Hmesp : me !!! Regidx csp_rs1 = pa_stk sp0 8).
          { rewrite (callee_saved_lookup Hecs_cs csp_rs1 ltac:(vm_compute; reflexivity)).
            rewrite (HB4cs csp_rs1 ltac:(vm_compute; reflexivity)).
            rewrite (callee_saved_lookup Hics_cs csp_rs1 ltac:(vm_compute; reflexivity)).
            rewrite (HB3cs csp_rs1 ltac:(vm_compute; reflexivity)).
            rewrite (callee_saved_lookup Hbcs_cs csp_rs1 ltac:(vm_compute; reflexivity)).
            rewrite (HB1cs csp_rs1 ltac:(vm_compute; reflexivity)). exact HQ2sp. }
          assert (Htgt8eF : add_vec (mword_of_int (FC + 0xc0) : mword 64)
                             (sign_extend' 64 (sign_extend' 21
                                (concat_vec (mword_of_int 2023 : mword 11) ('b"0"))))
                           = mword_of_int (FC + 0x8e))
            by (apply bv_eq; vm_compute; reflexivity).
          iApply (fc_restore4 (CID0 := CIDf8) me (K - 8)%nat sp0
                    (m !!! Regidx Rs2) (m !!! Regidx Rs3) (m !!! Regidx Rs4)
                    (m !!! Regidx Rs5)
                    (FC + 0xb8) (FC + 0xba) (FC + 0xbc) (FC + 0xbe) (FC + 0xc0)
                    (sign_extend' 21 (concat_vec (mword_of_int 2023 : mword 11) ('b"0")))
                    (proc_addr (fcn_j fn)) b Hmesp
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    Htgt8eF
                    with "Hcg Hpc [] [] [] [] [] Hb4 Hb5 Hb6 Hb7").
          { iApply (fci_b8 with "Htext"). }
          { iApply (fci_ba with "Htext"). }
          { iApply (fci_bc with "Htext"). }
          { iApply (fci_be with "Htext"). }
          { iApply (fci_c0 with "Htext"). }
          iIntros (CIDf9 Hsf9 Mr) "(%HMrsp & %HMr2 & %HMr3 & %HMr4 & %HMr5 & %HMrthr)
                                   Hcg Hpc Hb4 Hb5 Hb6 Hb7".
          assert (HMrall : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                    r <> Rs0 -> r <> Rs1 -> Mr !!! Regidx r = m !!! Regidx r).
          { intros r Hr N2 N8 N9.
            destruct (decide (r = Rs2)) as [->|Nr2]; [exact HMr2|].
            destruct (decide (r = Rs3)) as [->|Nr3]; [exact HMr3|].
            destruct (decide (r = Rs4)) as [->|Nr4]; [exact HMr4|].
            destruct (decide (r = Rs5)) as [->|Nr5]; [exact HMr5|].
            rewrite (HMrthr r Hr Nr2 Nr3 Nr4 Nr5).
            rewrite (callee_saved_lookup Hecs_cs r Hr).
            rewrite (HB4cs r Hr).
            rewrite (callee_saved_lookup Hics_cs r Hr).
            rewrite (HB3cs r Hr).
            rewrite (callee_saved_lookup Hbcs_cs r Hr).
            rewrite (HB1cs r Hr).
            rewrite (HQ2cs r Hr).
            rewrite /H1 upd_ne; [| regne].
            rewrite (callee_saved_lookup Hrel2_cs r Hr).
            rewrite (HG3cs r Hr).
            rewrite /F7 upd_ne; [| regne].
            rewrite /F6 upd_ne; [| regne].
            rewrite /F5 upd_ne; [| regne].
            rewrite /F4 upd_ne; [| regne].
            rewrite /F3 upd_ne; [| regne].
            rewrite /F2 upd_ne; [| regne].
            rewrite /F1 upd_ne; [| regne].
            rewrite /D2 upd_ne; [| regne].
            rewrite /D1 upd_ne; [| regne].
            exact (Hmthr r Hr N2 N8 N9). }
          iApply (fc_epi (CID0 := CIDf9) m Mr K sp0 (m !!! Regidx Rra)
                    (m !!! Regidx Rs0) (m !!! Regidx Rs1)
                    (m !!! Regidx Rs2) (m !!! Regidx Rs3) (m !!! Regidx Rs4)
                    (m !!! Regidx Rs5) u8 (proc_addr (fcn_j fn)) b
                    ltac:(lia) eq_refl eq_refl eq_refl eq_refl HMrsp HMrall
                    with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8").
          iIntros (CIDf10 Hsf10 mf) "%Hcsf Hcg Hpc".
          iDestruct (cpu_own_transport CIDf8 CIDf10 0 eb (proc_addr (fcn_j fn)) b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          iDestruct (trap_csrs_ext_transport CIDf8 CIDf10 eb (proc_addr (fcn_j fn))
                       ltac:(ext_chain Hebf b) with "Hextc") as "Hextc".
          iDestruct (cpu_claim_ext_transport CIDf8 CIDf10 eb (proc_addr (fcn_j fn))
                       ltac:(ext_chain Hebf b) with "Hextm") as "Hextm".
          iSpecialize ("Hcont" $! CIDf10 with "[]"); [iPureIntro; wp_next_chain|].
          (* [Hislot] is [iput]'s give-back, and it is what REPAYS the loan the
             free-slot construction above spent.  It used to be dropped here
             -- SpecFileclose.v recorded that as a leak of one unit of the
             IrefSlots supply per inode file closed; it has a home now. *)
          iApply ("Hcont" $! mf with
                    "Hcg Hcnt Hextc Hextm [Hpc] [%] Hfd Hislot [Hbsl] Hpbare").
          { iEval (rewrite /ret_tgt). iExact "Hpc". }
          { exact Hcsf. }
          (* THE WHOLE FS POSTCONDITION IS THE THREE SLOTS.  The bitmap said
             [used' ⊆ used] here; it is an invariant now and says nothing,
             and the two superblock cells are persistent.  (iput's
             [iref_slot] is spent above rather than dropped -- see the note
             on [Hislot].) *)
          { rewrite /fileclose_env_out bool_decide_eq_false_2; [|exact Hnpipe].
            rewrite Hib /fileclose_fs_out. iExact "Hbsl". }
        * (* ======== FD_NONE (or anything else): nothing to do ========== *)
          iApply (wp_bgeu_fall_s_sconf (mword_of_int (FC + 0x60))
                    (mword_of_int 74 : mword 13) Ra5 Ra4 Q2 (K - 8)%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    ltac:(rewrite Hcmp60;
                          destruct (zopz0zKzJ_u (mword_of_int 1 : mword 64) _) eqn:Hb60;
                          [exfalso; apply Hnone; by apply fc_ty_inode_iff | reflexivity])
                    with "Hcg Hpc []").
          { iApply (fci_60 with "Htext"). }
          iIntros (CIDz1 Hsz1) "Hcg Hpc".
          assert (Hpp64 : add_vec_int (mword_of_int (FC + 0x60) : mword 64) 4
                          = mword_of_int (FC + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp64) in "Hpc".
          assert (Htgt8eN : add_vec (mword_of_int (FC + 0x6c) : mword 64)
                             (sign_extend' 64 (sign_extend' 21
                                (concat_vec (mword_of_int 17 : mword 11) ('b"0"))))
                           = mword_of_int (FC + 0x8e))
            by (apply bv_eq; vm_compute; reflexivity).
          iApply (fc_restore4 (CID0 := CIDz1) Q2 (K - 8)%nat sp0
                    (m !!! Regidx Rs2) (m !!! Regidx Rs3) (m !!! Regidx Rs4)
                    (m !!! Regidx Rs5)
                    (FC + 0x64) (FC + 0x66) (FC + 0x68) (FC + 0x6a) (FC + 0x6c)
                    (sign_extend' 21 (concat_vec (mword_of_int 17 : mword 11) ('b"0")))
                    p b HQ2sp
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    Htgt8eN
                    with "Hcg Hpc [] [] [] [] [] Hb4 Hb5 Hb6 Hb7").
          { iApply (fci_64 with "Htext"). }
          { iApply (fci_66 with "Htext"). }
          { iApply (fci_68 with "Htext"). }
          { iApply (fci_6a with "Htext"). }
          { iApply (fci_6c with "Htext"). }
          iIntros (CIDz2 Hsz2 Mr) "(%HMrsp & %HMr2 & %HMr3 & %HMr4 & %HMr5 & %HMrthr)
                                   Hcg Hpc Hb4 Hb5 Hb6 Hb7".
          assert (HMrall : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                    r <> Rs0 -> r <> Rs1 -> Mr !!! Regidx r = m !!! Regidx r).
          { intros r Hr N2 N8 N9.
            destruct (decide (r = Rs2)) as [->|Nr2]; [exact HMr2|].
            destruct (decide (r = Rs3)) as [->|Nr3]; [exact HMr3|].
            destruct (decide (r = Rs4)) as [->|Nr4]; [exact HMr4|].
            destruct (decide (r = Rs5)) as [->|Nr5]; [exact HMr5|].
            rewrite (HMrthr r Hr Nr2 Nr3 Nr4 Nr5).
            rewrite (HQ2cs r Hr).
            rewrite /H1 upd_ne; [| regne].
            rewrite (callee_saved_lookup Hrel2_cs r Hr).
            rewrite (HG3cs r Hr).
            rewrite /F7 upd_ne; [| regne].
            rewrite /F6 upd_ne; [| regne].
            rewrite /F5 upd_ne; [| regne].
            rewrite /F4 upd_ne; [| regne].
            rewrite /F3 upd_ne; [| regne].
            rewrite /F2 upd_ne; [| regne].
            rewrite /F1 upd_ne; [| regne].
            rewrite /D2 upd_ne; [| regne].
            rewrite /D1 upd_ne; [| regne].
            exact (Hmthr r Hr N2 N8 N9). }
          iApply (fc_epi (CID0 := CIDz2) m Mr K sp0 (m !!! Regidx Rra)
                    (m !!! Regidx Rs0) (m !!! Regidx Rs1)
                    (m !!! Regidx Rs2) (m !!! Regidx Rs3) (m !!! Regidx Rs4)
                    (m !!! Regidx Rs5) u8 p b
                    ltac:(lia) eq_refl eq_refl eq_refl eq_refl HMrsp HMrall
                    with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8").
          iIntros (CIDz3 Hsz3 mf) "%Hcsf Hcg Hpc".
          iDestruct (cpu_own_transport CIDr2 CIDz3 n eb p b ltac:(wp_next_chain)
                       with "Hcnt") as "Hcnt".
          iDestruct (trap_csrs_ext_transport CID CIDz3 eb p ltac:(ext_chain Hebf b)
                       with "Hextc") as "Hextc".
          iDestruct (cpu_claim_ext_transport CID CIDz3 eb p ltac:(ext_chain Hebf b)
                       with "Hextm") as "Hextm".
          iSpecialize ("Hcont" $! CIDz3 with "[]"); [iPureIntro; wp_next_chain|].
          iApply ("Hcont" $! mf with
                    "Hcg Hcnt Hextc Hextm [Hpc] [%] Hfd [Hcore] [Henv] Hpbare").
          { iEval (rewrite /ret_tgt). iExact "Hpc". }
          { exact Hcsf. }
          (* AN UNTYPED FILE'S PAYLOAD IS ITS IREF UNIT.  [file_core]'s else
             arm is where a slot that holds no inode reference keeps the one
             the entry is provisioned for, so closing an untyped file repays
             the loan out of the payload itself -- no [iput] and no pipe. *)
          { iApply iref_slot_frac.
            rewrite /file_core bool_decide_eq_false_2; [|exact Hnpipe].
            rewrite bool_decide_eq_false_2;
              [| intro Hc; apply Hnone; by left].
            rewrite bool_decide_eq_false_2;
              [| intro Hc; apply Hnone; by right].
            iExact "Hcore". }
          { by iApply fileclose_env_out_of_env. }
  Qed.

End ProofFileclose.

End FilecloseProof.
