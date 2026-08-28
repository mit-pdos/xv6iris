(* ProofRelease.v: release over the SIE-agnostic v2 bundle (stage 8).

   release = holding-check (the lock token forces a0=1), lk->cpu := 0,
   fence, the lock-word clear (the token ∗ R re-enter the invariant), then
   pop_off -- the FIRST composition that threads push_off's payload
   disjunct end-to-end: release's caller hands the intenav-keyed input
   (built from push_off's post via WpIntenaBits), pop_off's restore may
   genuinely re-enable interrupts, and the conditional payload flows
   back out through release's post.

   Deep custody: 10 slots below the entry carve -- 4 traded for
   release's own frame, 6 riding for holding (which trades 4 + rides 2
   for mycpu), of which 4 are re-lent to pop_off.                       *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import HartTp WpNext IntrDefs CpuOwn.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfLock.
Require Import WpLock.
Require Import SpecHolding.
Require Import SpecPushOff.
Require Import CodeRelease.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecRelease.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
(* A6.86: [TsoCtxShim] is RETIRED -- its last live use died with the M4
   contract flip.  See its tombstone. *)
Require Import SieCapCtx.
Import Defs.



Module ReleaseGenProof (Holding : HOLDING) (PushOff : PUSHOFF) : RELEASE_GEN.

Section ProofRelease.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Context {kt : ktier}.
  (* [rget m k] at a NON-tp index is the plain map lookup ([rget_ne]) -- the
     one-line bridge from a leaf's [rget] to the register-map facts a
     whole-function proof already has.  Written name-free (durable-notes: an
     Ltac body cannot mention a hypothesis by literal name). *)
  Local Ltac rgne :=
    rewrite rget_ne;
    [ | let H1 := fresh in let H2 := fresh in
        intro H1; injection H1 as H2; vm_compute in H2; congruence ].

  Lemma wp_release_gen_sconf
      (γl : gname) (lka : mword 64) (s : string) (R : CtxId → iProp Σ) `{!CtxMorph R} (Dc Out : iProp Σ)
      (m : regfile)
      (n : nat) (eb : bool) (p : mword 64) (av : nat) (lks : gset string)
    : wp_release_gen_sconf_body kt γl lka s R Dc Out m n eb p av lks.
  Proof.
    cbv beta delta [wp_release_gen_sconf_body].
    intros pcE lk0 ret_tgt. cbv zeta. intros Hlka Hav Href Hrefpre.
    (* [cbv zeta] just inlined the body's [outb]; give it a name again, because
       the ENTRY stack index now mentions it.  release's entry count is
       [trap_res outb + av] and its exit count is [av]: the pop_off it ends with
       re-enables interrupts when the level fully unwinds with an enabled base,
       and re-enabling must PUT THE TRAP RESERVE BACK -- out of release's own
       usable slots, which are exactly the ones the matching acquire's push_off
       freed.  See SpecRelease.v's header.  At [outb = false] (a nested critical
       section) [trap_res false + n] IS [n], so nothing below changes there. *)
    pose (outb := match n with O => eb | S _ => false end).
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg #Htext Hpc #Hlock Htoken HR Hfin Hown Hpay Hcont".
    (* the deposit arrives at the caller's own context; the invariant parks
       it ∃-closed (tso-port M3 -- at cutover this introduction becomes the
       transport into the lock's internal context,
       [TsoCtxTwin2.ctx_dom_to_parked]) *)
    iAssert (∃ ξ : CtxId, R ξ)%I with "[HR]" as "HR"; first by iExists cur_ctx.
    (* ---- 0x00: c.addi sp,-32 -- the frame trade (k := 4) ---- *)
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (R0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspR0 : R0 !!! Regidx csp_rs1 = spr)
      by (rewrite /R0 upd_eq; reflexivity).
    assert (Hspr4 : pa_stk sp0 4 = spr).
    { rewrite /spr. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m (trap_res outb + av)%nat 4 false ltac:(lia) Hpush
              with "Hcg Hpc []").
    { iApply (rli_00 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hframe Hpc".
    (* re-spell [(trap_res outb + av) - 4] as [trap_res outb + (av - 4)]:
       [trap_res outb] is an opaque nat atom [lia] carries across, and this is
       the form pop_off's own entry index wants below. *)
    assert (Hreidx : ((trap_res outb + av) - 4)%nat = (trap_res outb + (av - 4))%nat) by lia.
    iEval (rewrite Hreidx) in "Hcg".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with R0.
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.release + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    iEval (rewrite (stack_own_slots (KTR := kt)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1
                   = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spr. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                   = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spr. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                   = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spr. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ---- 0x02/0x04/0x06: c.sdsp ra/s0/s1 ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.release + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              R0 (trap_res outb + (av - 4))%nat vr24 false
              with "Hcg Hpc [] [Hr24]").
    { iApply (rli_02 with "Htext"). }
    { iEval (rewrite HcspR0 -Hb1). iExact "Hr24". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.release + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.release + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.release + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R0 (trap_res outb + (av - 4))%nat vr16 false
              with "Hcg Hpc [] [Hr16]").
    { iApply (rli_04 with "Htext"). }
    { iEval (rewrite HcspR0 -Hb2). iExact "Hr16". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.release + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.release + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.release + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R0 (trap_res outb + (av - 4))%nat vr8 false
              with "Hcg Hpc [] [Hr8]").
    { iApply (rli_06 with "Htext"). }
    { iEval (rewrite HcspR0 -Hb3). iExact "Hr8". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.release + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.release + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* ---- 0x08: c.addi4spn s0,sp,32 ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.release + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              R0 (trap_res outb + (av - 4))%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (rli_08 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (R0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (R0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R0) with R1.
    assert (Hpc0a : add_vec_int (mword_of_int (KernelSyms.release + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.release + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* ---- 0x0a: c.mv s1,a0 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.release + 0x0a)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              R1 (trap_res outb + (av - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (rli_0a with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (R1 !!! Regidx (mword_of_int 10 : mword 5)))]> R1).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (R1 !!! Regidx (mword_of_int 10 : mword 5)))]> R1) with R2.
    assert (Hpc0c : add_vec_int (mword_of_int (KernelSyms.release + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.release + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    (* ---- 0x0c: jal ra,holding ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.release + 0x0c)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fff06 : mword 21)
              R2 (trap_res outb + (av - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (rli_0c with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.release + 0x0c) : mword 64) 4)]> R2).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.release + 0x0c) : mword 64) 4)]> R2) with R3.
    assert (Hpchd : add_vec (mword_of_int (KernelSyms.release + 0x0c) : mword 64) (sign_extend' 64 (mword_of_int 0x1fff06 : mword 21))
                    = mword_of_int KernelSyms.holding) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpchd) in "Hpc".
    (* ---- holding(): the token forces the slow path, a0 := 1 ---- *)
    assert (Ha0R3 : R3 !!! Regidx (mword_of_int 10 : mword 5) = lk0).
    { rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HcspR3 : R3 !!! Regidx csp_rs1 = spr).
    { rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      exact HcspR0. }
    assert (HlkaR3 : add_vec (R3 !!! Regidx (mword_of_int 10 : mword 5))
                       (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka)
      by (rewrite Ha0R3; exact Hlka).
    iApply (Holding.wp_holding_lockinv_locked_s_sconf kt γl lka s R Dc R3 (trap_res outb + (av - 4))%nat p
              HlkaR3 ltac:(lia) Href
              with "Hcg Htext Hpc Hlock Htoken").
    iIntros (mh) "Hcg Hpc %Hmh Htoken".
    destruct Hmh as [Hcsh Ha0h].
    destruct Hcsh as (Hcsph & Hs0h & Hs1h & Hs2h & Hs3h & Hs4h & Hs5h & Hs6h & Hs7h & Hs8h & Hs9h & Hs10h & Hs11h).
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc10 : ret_pc (add_vec_int (mword_of_int (KernelSyms.release + 0x0c) : mword 64) 4)
                    = (mword_of_int (KernelSyms.release + 0x10) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* ---- 0x10: c.beqz a0 falls (a0 = 1) ---- *)
    assert (Ha0mh : eq_vec (mh !!! Regidx (mword_of_int 10 : mword 5)) zero_reg = false)
      by (rewrite Ha0h; vm_compute; reflexivity).
    iApply (wp_cbeqz_fall_s_sconf (CID:=CID) (mword_of_int (KernelSyms.release + 0x10)) (mword_of_int 14 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              mh (trap_res outb + (av - 4))%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rgne; exact Ha0mh)
              with "Hcg Hpc []").
    { iApply (rli_10 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpc12 : add_vec_int (mword_of_int (KernelSyms.release + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.release + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    (* ---- 0x12: sd zero,16(s1) : lk->cpu := 0 ---- *)
    assert (Hs1mh : mh !!! Regidx (mword_of_int 9 : mword 5) = lk0).
    { rewrite Hs1h /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_eq /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate].
      apply add_vec_zero_l. }
    assert (Hacpu : add_vec (mh !!! Regidx (mword_of_int 9 : mword 5))
                      (sign_extend' 64 (mword_of_int 16 : mword 12)) = lock_cpu lka).
    { rewrite Hs1mh. rewrite -Hlka.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. reflexivity. }
    (* THE SET-REMOVING INSTRUCTION, and the one that CANNOT run without the
       set: while the lock is held the invariant owns only half of [lk->cpu],
       so this store is licensed by redeeming the membership fragment out of
       the hart's own held-lock set (LockSet.cpu_locks_delete).  The set is an
       INDEX now, so it is NAMED here: [cpu_own_locks_swap] takes the
       authority out at [lks] and puts back [lks ∖ {[s]}], which is
       exactly release's postcondition.  No premise is needed -- membership is
       DERIVED from the fragment the lock invariant was holding. *)
    iDestruct (cpu_own_locks_swap with "Hown") as "[Hlks [%Hsz Hownback]]".
    iApply (wp_sd_zero_lkcpu_lockopen_s_sconf (CID:=CID) γl lka s R Dc (mword_of_int (KernelSyms.release + 0x12))
              (mword_of_int 9 : mword 5) (mword_of_int 16 : mword 12) mh (trap_res outb + (av - 4))%nat false lks
              ltac:(rgne; exact Hacpu) Href
              with "Hcg Hpc [] Hlock Htoken Hlks").
    { iApply (rli_12 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Htoken Hlks %Hin".
    (* The rank WAS held ([Hin], out of the leaf's own [cpu_locks_delete]), so
       the set STRICTLY shrank: [size lks <= S n] becomes
       [size (lks ∖ {[rank s]}) <= n], which is exactly pop_off's unwind
       premise below.  That is the whole compositional argument. *)
    iDestruct ("Hownback" $! (lks ∖ {[s]})
                 ltac:(exact (size_del_le s lks (S n) Hsz)) with "Hlks") as "Hown".
    assert (Hpc16 : add_vec_int (mword_of_int (KernelSyms.release + 0x12) : mword 64) 4 = mword_of_int (KernelSyms.release + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* ---- 0x16: fence rw,w ---- *)
    iApply (wp_fence_s_sconf (mword_of_int (KernelSyms.release + 0x16)) mh (trap_res outb + (av - 4))%nat false
              with "Hcg Hpc []").
    { iApply (rli_16 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpc1a : add_vec_int (mword_of_int (KernelSyms.release + 0x16) : mword 64) 4 = mword_of_int (KernelSyms.release + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* ---- 0x1a: sw zero,0(s1) : the lock word clears ---- *)
    iApply (wp_sw_zero_lockfin_s_sconf (CID:=CID) γl lka s R Dc Out (mword_of_int (KernelSyms.release + 0x1a)) (mword_of_int 9 : mword 5)
              (mword_of_int 0 : mword 12) mh (trap_res outb + (av - 4))%nat false
              ltac:(rgne; rewrite Hs1mh; exact Hlka) Hrefpre
              with "Hcg Hpc [] Hlock Htoken HR Hfin").
    { iApply (rli_1a with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "HOut Hcg Hpc".
    assert (Hpc1e : add_vec_int (mword_of_int (KernelSyms.release + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.release + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* ---- 0x1e: jal ra,pop_off ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.release + 0x1e)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fff9a : mword 21)
              mh (trap_res outb + (av - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (rli_1e with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (M1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.release + 0x1e) : mword 64) 4)]> mh).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.release + 0x1e) : mword 64) 4)]> mh) with M1.
    assert (Hpcpp : add_vec (mword_of_int (KernelSyms.release + 0x1e) : mword 64) (sign_extend' 64 (mword_of_int 0x1fff9a : mword 21))
                    = mword_of_int KernelSyms.pop_off) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcpp) in "Hpc".
    (* ---- pop_off(): the payload threads through ---- *)
    assert (HcspM1 : M1 !!! Regidx csp_rs1 = spr).
    { rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hcsph. exact HcspR3. }
    (* pop_off's UNWIND PREMISE, discharged exactly as the discipline says:
       the coupling gave [size lks <= S n] on the way in, the cpu-field clear
       above deleted this lock's rank, so the set now fits under [n]. *)
    iApply (PushOff.wp_pop_off_sconf kt M1 (av - 4)%nat n eb p _
              ltac:(lia)
              ltac:(exact (size_del_lt s lks n Hin Hsz))
              with "Hcg Hown Hpay Htext Hpc").
    iIntros (CIDpo Hspo mf) "Hcg Hown Hpc %Hmf".
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc22 : ret_pc (add_vec_int (mword_of_int (KernelSyms.release + 0x1e) : mword 64) 4)
                    = (mword_of_int (KernelSyms.release + 0x22) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    destruct Hmf as (Hcspf & Hs0f & Hs1f & Hs2f & Hs3f & Hs4f & Hs5f & Hs6f & Hs7f & Hs8f & Hs9f & Hs10f & Hs11f).
    assert (Hcspmf : mf !!! Regidx csp_rs1 = spr) by (rewrite Hcspf; exact HcspM1).
    (* the frame cells hold the entry values *)
    assert (HraR0 : R0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /R0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0R0 : R0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /R0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1R0 : R0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /R0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rgne) in "Hr24". iEval (rewrite HcspR0 HraR0) in "Hr24".
    iEval (rgne) in "Hr16". iEval (rewrite HcspR0 Hs0R0) in "Hr16".
    iEval (rgne) in "Hr8". iEval (rewrite HcspR0 Hs1R0) in "Hr8".
    (* ---- 0x22/0x24/0x26: c.ldsp ra/s0/s1 ---- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.release + 0x22)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              mf (av - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) (match n with O => eb | S _ => false end)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr24]").
    { iApply (rli_22 with "Htext"). }
    { iEval (rewrite Hcspmf). iExact "Hr24". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hr24".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mf).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mf) with E1.
    assert (Hpc24 : add_vec_int (mword_of_int (KernelSyms.release + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.release + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    assert (HcspE1 : E1 !!! Regidx csp_rs1 = spr)
      by (rewrite /E1 upd_ne; [exact Hcspmf | vm_compute; discriminate]).
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.release + 0x24)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              E1 (av - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) (match n with O => eb | S _ => false end)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr16]").
    { iApply (rli_24 with "Htext"). }
    { iEval (rewrite HcspE1). iExact "Hr16". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hr16".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1) with E2.
    assert (Hpc26 : add_vec_int (mword_of_int (KernelSyms.release + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.release + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc26) in "Hpc".
    assert (HcspE2 : E2 !!! Regidx csp_rs1 = spr)
      by (rewrite /E2 upd_ne; [exact HcspE1 | vm_compute; discriminate]).
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.release + 0x26)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              E2 (av - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) (match n with O => eb | S _ => false end)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr8]").
    { iApply (rli_26 with "Htext"). }
    { iEval (rewrite HcspE2). iExact "Hr8". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hr8".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2) with E3.
    assert (Hpc28 : add_vec_int (mword_of_int (KernelSyms.release + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.release + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    (* ---- 0x28: c.addi16sp sp,32 -- the frame trade back ---- *)
    assert (HcspE3 : E3 !!! Regidx csp_rs1 = spr)
      by (rewrite /E3 upd_ne; [exact HcspE2 | vm_compute; discriminate]).
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
    assert (Hsp0up : add_vec spr (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite /spr /sp0 add_vec_assoc.
      assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                            (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply avi0. }
    assert (HE4sp : E4 !!! Regidx csp_rs1 = sp0).
    { rewrite /E4 upd_eq HcspE3. exact Hsp0up. }
    assert (Hwv : add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HcspE3. exact Hsp0up. }
    assert (Hpop : E3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HcspE3. symmetry. exact Hspr4. }
    iAssert (stack_own (KTR := kt) sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
    { rewrite (stack_own_slots (KTR := kt)). cbn [seq].
      iSplitL "Hr24". { iExists _. iEval (rewrite Hb1 -Hcspmf). iExact "Hr24". }
      iSplitL "Hr16". { iExists _. iEval (rewrite Hb2 -HcspE1). iExact "Hr16". }
      iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3 -HcspE2). iExact "Hr8". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.release + 0x28)) (mword_of_int 2 : mword 6) E3 (av - 4)%nat 4 (match n with O => eb | S _ => false end) Hpop
              with "Hcg Hpc [] Hframe4").
    { iApply (rli_28 with "Htext"). }
    iIntros (CIDe4 Hse4) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    assert (Hpc2a : add_vec_int (mword_of_int (KernelSyms.release + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.release + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* ---- 0x2a: c.ret ---- *)
    assert (HE4ra : E4 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1. apply upd_eq. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.release + 0x2a)) (mword_of_int 1 : mword 5) E4 av (match n with O => eb | S _ => false end)
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc []").
    { iApply (rli_2a with "Htext"). }
    iIntros (CIDe5 Hse5) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hra_final : ret_pc (E4 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HE4ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    assert (Hchainf : (match n with O => eb | S _ => false end) = false \/ p = zero_reg -> (CIDe5 : CPU) = (CIDpo : CPU)) by wp_next_chain.
    iDestruct (cpu_own_transport CIDpo CIDe5 n eb p (match n with O => eb | S _ => false end) Hchainf with "Hown") as "Hown".
    iSpecialize ("Hcont" $! CIDe5 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E4 with "HOut Hcg Hpc [%] Hown").
    unfold callee_saved. repeat split.
    + rewrite HE4sp. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs2f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs2h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs3f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs3h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs4f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs4h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs5f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs5h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs6f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs6h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs7f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs7h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs8f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs8h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs9f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs9h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs10f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs10h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs11f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs11h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
  Qed.

End ProofRelease.

End ReleaseGenProof.

(* The static-kernel-lock instance: the finisher closes the invariant, so
   nothing comes back out.  Verbatim the statement the thirteen ordinary
   consumers were written against. *)
Module ReleaseOfGen (G : RELEASE_GEN) : RELEASE.

Section OfGen.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Context {kt : ktier}.
  Lemma wp_release_sconf
      (γl : gname) (lka : mword 64) (s : string) (R : CtxId → iProp Σ) `{!CtxMorph R}
      (m : regfile)
      (n : nat) (eb : bool) (p : mword 64) (av : nat)
      (lks : gset string)
    : wp_release_sconf_body kt γl lka s R m n eb p av lks.
  Proof.
    cbv beta delta [wp_release_sconf_body].
    intros pcE lk0 ret_tgt. cbv zeta. intros Hlka Hav.
    iIntros "Hcg #Htext Hpc #Hlock Htoken HR Hown Hpay Hcont".
    iApply (G.wp_release_gen_sconf kt γl lka s R False%I emp%I m n eb p av lks
              Hlka Hav (lock_refute_False _) (lock_refute_False _)
              with "Hcg Htext Hpc [] Htoken HR [] Hown Hpay").
    { iApply (is_lock_openable with "Hlock"). }
    { iApply lock_finisher_close. }
    iIntros (CIDg Hsg mr) "_ Hcg Hpc %Hcs Hown".
    iSpecialize ("Hcont" $! CIDg with "[%]"); [exact Hsg|].
    iApply ("Hcont" $! mr with "Hcg Hpc [//] Hown").
  Qed.

End OfGen.

End ReleaseOfGen.

(* The cancelling instance: the finisher DESTROYS the invariant at the store,
   so release walks off with the lock's own two words and whatever the caller
   makes of R -- the storage, reclaimable.  The caller's completion wand is
   what turns its opening share into the disposal certificate; see
   SpecRelease.v for why that cannot be done before the call. *)
Module ReleaseCancelOfGen (G : RELEASE_GEN) : RELEASE_CANCEL.

Section CancelOfGen.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Context {kt : ktier}.
  Lemma wp_release_cancel_sconf
      (γl : gname) (lka : mword 64) (s : string) (R : CtxId → iProp Σ) `{!CtxMorph R} (D Out : iProp Σ)
      (m : regfile)
      (n : nat) (eb : bool) (p : mword 64) (av : nat)
      (lks : gset string)
    : wp_release_cancel_sconf_body kt γl lka s R D Out m n eb p av lks.
  Proof.
    cbv beta delta [wp_release_cancel_sconf_body].
    intros pcE lk0 ret_tgt. cbv zeta. intros Hlka Hav Href Hrefpre.
    iIntros "Hcg #Htext Hpc #Hlock Htoken HR Hbuild Hown Hpay Hcont".
    iApply (G.wp_release_gen_sconf kt γl lka s R D
              (lka ↦₄ (mword_of_int 0 : mword 32) ∗ WpLock.lk_cpu_fresh lka ∗ Out)%I
              m n eb p av lks
              Hlka Hav Href Hrefpre
              with "Hcg Htext Hpc Hlock Htoken HR [Hbuild] Hown Hpay").
    { (* the destroyer's completion wand speaks at ITS context; the
         invariant's parked payload is ∃-closed -- bridge with the shim's
         SC-only transport (the cutover kit's finisher morphs against real
         AMO evidence instead) *)
      iApply lock_finisher_destroy.
      iIntros "Hfrag HRx". iDestruct "HRx" as (ξ0) "HRx".
      iPoseProof (ctx_dom_sc ξ0 cur_ctx) as "Hdom".
      iMod (ctx_morph ξ0 cur_ctx with "Hdom HRx") as "[_ HRx]".
      iApply ("Hbuild" with "Hfrag HRx"). }
    iIntros (CIDg Hsg mr) "(Hword & Hcpu & HOut) Hcg Hpc %Hcs Hown".
    iSpecialize ("Hcont" $! CIDg with "[%]"); [exact Hsg|].
    iApply ("Hcont" $! mr with "Hword Hcpu HOut Hcg Hpc [//] Hown").
  Qed.

End CancelOfGen.

End ReleaseCancelOfGen.
