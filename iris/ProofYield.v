(* ProofYield.v -- the whole-function sconf-tier proof of yield()
   (SpecYield.v), as a sealed functor over its callees' interfaces
   (myproc, acquire, sched, release).  See claude-notes/projects/yield-sched.md.

   yield() @ 0x80001eda: the 32-byte frame prologue (byte-identical to
   myproc's) / p = myproc() / acquire(&p->lock) / p->state = RUNNABLE (the
   c.sw) / sched() / release(&p->lock) / epilogue.  The proof threads the
   scheduler-swtch protocol resources (SchedCtx.v): it acquires proc j's lock,
   flips the state to RUNNABLE, hands sched the parking-proc payload
   (proc_held + cpu_cells), and -- once dispatched again -- releases with the
   process RUNNING (needs_ctx RUNNING = false, so the lock slot is emp).

   THE EXPLICIT-CPUID SHAPE.  yield's contract is [wp_next b pj ...], and [b]
   is DERIVABLY [true] here: the entry bundle is [cpu_own 0 eb pj C b] with
   [eb = true], and [CpuOwn.cpu_own_forces_on] turns that into [b = true].  So
   the whole function is the hart-GENERIC case -- except for the stretch
   between acquire's return and release's call, where the held lock pins the
   hart at the literal [false] and every leaf collapses via [wp_next_off].
   yield's own [wp_next] obligation is discharged at whatever hart the
   epilogue ends on: at [b = true] the pinning condition is
   [pj = zero_reg], which [SchedCtx.proc_addr_nonzero] refutes.

   THE PARKED SCHEDULER RECORD IS GLOBAL NOW.  yield no longer carries
   [▷ sched_vc] (fourteen exclusive words of ONE hart's struct cpu, for which
   no [wp_next] transport exists); it carries the persistent, HART-FREE
   [scheds_inv Φ γs] plus the per-PROC receipt [park_hlf j true].  The record
   is checked OUT of the global invariant just before the [jal sched]
   ([SchedCtx.scheds_take], which also flips the receipt to [false] -- the
   fifth conjunct of the [proc_held] sched demands) and deposited back at the
   RESUMED hart, the dispatched thread's first move ([SchedCtx.scheds_put]). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import InstrBytes KernelText IntrDefs.
Require Import HartTp WpNext.
Require Import WpSmodeIntr.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import KernelRvcDecode.
Require Import CodeYield.
Require Import SpecMyproc SpecAcquire SpecSched SpecRelease SpecYield.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* Pure helpers: address arithmetic + the two noff-cell value forms.      *)
(* ===================================================================== *)

Lemma yd_addv_unsigned (x y : mword 64) :
  bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned. reflexivity.
Qed.

Lemma yd_addv_zero_l (x : mword 64) : add_vec zero_reg x = x.
Proof.
  apply bv_eq. rewrite yd_addv_unsigned.
  assert (Hz : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite Hz Z.add_0_l. apply bv_wrap_bv_unsigned.
Qed.

(* acquire's noff output (push_off's +1 store over the entry value 0) is
   exactly [mword_of_int 1] (closed; needed for sched's cpu_cells). *)
Lemma yd_acq_noff_one :
  (autocast (T := mword) (subrange_vec_dec
     (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 (mword_of_int 0 : mword 32))
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
     (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = (mword_of_int 1 : mword 32).
Proof. vm_compute. reflexivity. Qed.

(* release's noff output (pop_off's -1 store over the entry value 1) is
   exactly [mword_of_int 0] (closed; needed for yield's postcondition). *)
Lemma yd_rel_noff_zero :
  (autocast (T := mword) (subrange_vec_dec
     (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 (mword_of_int 1 : mword 32))
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
     (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = (mword_of_int 0 : mword 32).
Proof. vm_compute. reflexivity. Qed.

(* the c.li a5,3 value truncated to 32 bits is RUNNABLE = mword_of_int 3. *)
Lemma yd_runnable :
  trunc32 (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6))) : mword 64)
  = (mword_of_int 3 : mword 32).
Proof. vm_compute. reflexivity. Qed.

Module YieldProof (Myproc : MYPROC) (Acquire : ACQUIRE) (Sched : SCHED) (Release : RELEASE) : YIELD.

(* ===================================================================== *)
(* THE POST-RESUME HALF, AS ITS OWN LEMMA.                                *)
(*                                                                        *)
(* sched() does not return on the hart it parked from (SpecSched.v): proc  *)
(* contexts are migratable, so its continuation is a [wp_next true] whose  *)
(* rebound [CID] is the DISPATCHING hart.  Everything yield does after the *)
(* park -- the release, the epilogue, the postcondition -- therefore has   *)
(* to hold at an ARBITRARY hart, which a Section-fixed [CID] cannot        *)
(* express.  So the whole half is ONE lemma with its OWN [CID0] binder     *)
(* (the porting guide's rule for a decomposed proof), and its own          *)
(* continuation is a [wp_next] as well: release re-enables interrupts at   *)
(* its last instruction, so even the epilogue is hart-generic.             *)
(* ===================================================================== *)
Section YieldPostSched.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}.

  (* generic register-map peel over the proof's [set]-chain (hit-first). *)
  Local Ltac yd_peel :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| vm_compute; discriminate]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].

  (* extract the opaque context-slot payload, leaving the bundle at slot
     [emp] (what the sched call-site hands across the swtch).  It carries its
     OWN hart binder: the call site is PAST an interrupts-enabled stretch, so
     a lemma sharing an enclosing section's [Context CID] would silently pin
     to the entry hart (porting guide, "a helper lemma sharing the enclosing
     Section's Context"). *)
  Lemma cpu_own_ctx_take `{CID0 : CpuId}
      (n : nat) (eb : bool) (p : mword 64) (D : iProp Σ) :
    cpu_own n eb p D false -∗ D ∗ cpu_own n eb p emp false.
  Proof.
    iIntros "[Hh HD]". iFrame "HD". rewrite cpu_own_off. iFrame "Hh".
  Qed.

  Lemma yield_post_sched `{CID0 : CpuId}
      (Φ : mval -> iProp Σ) (γs : list gname)
      (j : nat) (γl : gname) (ch' : mword 64)
      (m msch : regfile) (av : nat) (C : iProp Σ)
      (sp0 spd vgap : mword 64) :
    let pj := proc_addr j in
    (20 <= av)%nat ->
    (j < NPROC)%nat ->
    add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = spd ->
    sp0 = m !!! Regidx csp_rs1 ->
    (* NOTE: the old [⌜msch !!! x4 = cid_word⌝] premise is GONE -- [tp_pin]
       makes the tp slot unobservable, so nothing can read it. *)
    msch !!! Regidx csp_rs1 = spd ->
    msch !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j) ->
    (* s2..s11: untouched by yield and by everything it calls *)
    msch !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5) ->
    msch !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5) ->
    msch !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5) ->
    msch !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) ->
    msch !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) ->
    msch !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) ->
    msch !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) ->
    msch !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) ->
    msch !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) ->
    msch !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5) ->
    kernel_text -∗
    is_lock γl (proc_addr j) "proc"%string (proc_lock_res Φ γs γl (proc_addr j)) -∗
    scheds_inv Φ γs -∗
    sie_cap_gpr msch (av - 4)%nat false pj -∗
    pc_is (mword_of_int (YD + 0x1c)) -∗
    proc_held cpu_id j γl RUNNING ch' -∗
    trap_csrs -∗
    cpu_own 1 true pj emp false -∗
    C -∗
    own_ctx (p_context pj) -∗
    ▷ sched_vc Φ γs (a_cpu_ctx cid_word) pj -∗
    (* the three saved frame words + the frame's bottom slot *)
    pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈ vgap -∗
    wp_next true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr mf av true pj -∗
        cpu_own 0 true pj C true -∗
        pc_is (ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))) -∗
        own_ctx (p_context pj) -∗
        park_hlf j true -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pj Hav Hj Hspd Hsp0 Hsp_msch Hs1_msch
           Hmsch18 Hmsch19 Hmsch20 Hmsch21 Hmsch22 Hmsch23 Hmsch24 Hmsch25 Hmsch26 Hmsch27.
    iIntros "#Htext #Hislock #Hscheds Hcg Hpc Hheld' Htc Hcpuemp HC Hown' Hvc' Hr24 Hr16 Hr8 Hgap Hcont".
    (* frame-slot address bridges: slot k sits at [spd + 8*(4-k)]. *)
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : pa_stk sp0 1
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iDestruct "Hheld'" as "(Hlocked & Hstate & Hchan & Hpub & Hpark)".
    (* ------------------------------------------------------------------ *)
    (* THE DEPOSIT: the dispatched thread's first move.  The record sched   *)
    (* handed back goes into [scheds_inv]'s slot for the hart we woke up    *)
    (* on, and the per-PROC receipt flips back to [true] -- which is        *)
    (* exactly what yield's postcondition owes.                             *)
    (* ------------------------------------------------------------------ *)
    iDestruct (cpu_own_set_proc 1 true pj pj emp with "Hcpuemp") as "[Hph Hback]".
    iApply fupd_wp.
    iMod (SchedCtx.scheds_put Φ γs ⊤ CID0 j with "Hscheds Hph Hpark Hvc'")
      as "[Hph Hpark]"; [solve_ndisj|exact Hj|].
    iModIntro.
    iDestruct ("Hback" with "Hph") as "Hcpuemp".
    (* re-inject the opaque context-slot payload into the returned bundle. *)
    iAssert (cpu_own 1 true (proc_addr j) C false) with "[Hcpuemp HC]" as "Hcpu".
    { iApply (cpu_own_ctx_swap with "Hcpuemp"). iIntros "_". iExact "HC". }
    (* +0x1c: c.mv a0,s1 : a0 := s1 = proc_addr j -- lock still held, so the
       hart is PINNED and [wp_next_off] collapses the binder. *)
    iPoseProof (ydi_1c with "Htext") as "Hi1c".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (YD + 0x1c)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              msch (av - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c [-]").
    rewrite wp_next_off.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (D0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (msch !!! Regidx (mword_of_int 9 : mword 5)))]> msch).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (msch !!! Regidx (mword_of_int 9 : mword 5)))]> msch) with D0.
    assert (Hpc1e : add_vec_int (mword_of_int (YD + 0x1c) : mword 64) 2 = mword_of_int (YD + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* +0x1e: jal release *)
    iPoseProof (ydi_1e with "Htext") as "Hi1e".
    iApply (wp_jal_s_sconf Φ (mword_of_int (YD + 0x1e)) (mword_of_int 1 : mword 5) (mword_of_int 2092440 : mword 21)
              D0 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1e [-]").
    rewrite wp_next_off.
    iIntros "Hcg Hpc".
    set (D1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (YD + 0x1e) : mword 64) 4)]> D0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (YD + 0x1e) : mword 64) 4)]> D0) with D1.
    assert (Hpcrl : add_vec (mword_of_int (YD + 0x1e) : mword 64) (sign_extend' 64 (mword_of_int 2092440 : mword 21))
                    = mword_of_int KernelSyms.release) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcrl) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x1e: release(&p->lock) -- with the process RUNNING (slot emp).    *)
    (* ------------------------------------------------------------------ *)
    assert (Ha0_D1 : D1 !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j).
    { rewrite /D1 upd_ne; [| vm_compute; discriminate].
      rewrite /D0 upd_eq Hs1_msch !yd_addv_zero_l. reflexivity. }
    assert (HD1ra : D1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (YD + 0x1e) : mword 64) 4)
      by (rewrite /D1 upd_eq; reflexivity).
    assert (Hlka : add_vec (D1 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr j).
    { rewrite Ha0_D1.
      assert (H0 : sign_extend' 64 (mword_of_int 0 : mword 12) = (mword_of_int 0 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H0. apply kv_addv_zero. }
    (* rebuild the lock resource: RUNNING needs no context, no dormant block
       and -- since it IS running -- no park receipt either. *)
    iAssert (proc_lock_res Φ γs γl (proc_addr j)) with "[Hstate Hchan Hpub]" as "HR2".
    { rewrite /proc_lock_res. iExists RUNNING, ch'. iFrame "Hstate Hchan Hpub".
      rewrite /proc_slots needs_ctx_RUNNING inv_dormant_RUNNING not_running_RUNNING. done. }
    iApply (Release.wp_release_sconf Φ γl (proc_addr j) "proc"%string
              (proc_lock_res Φ γs γl (proc_addr j)) D1 0 true pj C (av - 4)%nat
              Hlka
              ltac:(lia)
              with "Hcg Htext Hpc Hislock Hlocked HR2 Hcpu Htc [-]").
    (* release's exit index is [outb = eb = true]: it re-enables at its LAST
       instruction, so the hart can move there and the whole epilogue below
       is hart-GENERIC. *)
    iIntros (CIDr Hsr mrel) "Hcg Hpc %Hcs_rel Hcpu".
    assert (Hpc22 : ret_pc (D1 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (YD + 0x22)) by (rewrite HD1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* Epilogue: restore ra/s0/s1, pop the frame, return (mirror myproc).  *)
    (* ------------------------------------------------------------------ *)
    (* sp threads (callee-saved) through all four callees back to the push. *)
    assert (Hcsp_mrel : mrel !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcs_rel csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /D1 upd_ne; [| vm_compute; discriminate]. rewrite /D0 upd_ne; [| vm_compute; discriminate].
      exact Hsp_msch. }
    (* the three saved frame cells arrive at [pa_stk sp0 k]; bridge each to
       the [spd + imm] form the c.ldsp leaves compute. *)
    iEval (rewrite Hb1) in "Hr24".
    iEval (rewrite Hb2) in "Hr16".
    iEval (rewrite Hb3) in "Hr8".
    (* +0x22: c.ldsp ra,24 *)
    iPoseProof (ydi_22 with "Htext") as "Hi22".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (YD + 0x22)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              mrel (av - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [Hr24] [-]").
    { iEval (rewrite Hcsp_mrel). iExact "Hr24". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hr24".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel) with E1.
    assert (Hpc24 : add_vec_int (mword_of_int (YD + 0x22) : mword 64) 2 = mword_of_int (YD + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    assert (HcspE1 : E1 !!! Regidx csp_rs1 = spd)
      by (rewrite /E1 upd_ne; [exact Hcsp_mrel | vm_compute; discriminate]).
    (* +0x24: c.ldsp s0,16 *)
    iPoseProof (ydi_24 with "Htext") as "Hi24".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (YD + 0x24)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              E1 (av - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [Hr16] [-]").
    { iEval (rewrite HcspE1). iExact "Hr16". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hr16".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1) with E2.
    assert (Hpc26 : add_vec_int (mword_of_int (YD + 0x24) : mword 64) 2 = mword_of_int (YD + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc26) in "Hpc".
    assert (HcspE2 : E2 !!! Regidx csp_rs1 = spd)
      by (rewrite /E2 upd_ne; [exact HcspE1 | vm_compute; discriminate]).
    (* +0x26: c.ldsp s1,8 *)
    iPoseProof (ydi_26 with "Htext") as "Hi26".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (YD + 0x26)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              E2 (av - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26 [Hr8] [-]").
    { iEval (rewrite HcspE2). iExact "Hr8". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hr8".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2) with E3.
    assert (Hpc28 : add_vec_int (mword_of_int (YD + 0x26) : mword 64) 2 = mword_of_int (YD + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    assert (HcspE3 : E3 !!! Regidx csp_rs1 = spd)
      by (rewrite /E3 upd_ne; [exact HcspE2 | vm_compute; discriminate]).
    (* +0x28: c.addi16sp sp,32 -- pop the frame *)
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
    assert (Hsp0up : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite -Hspd po_addv_assoc.
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
    { rewrite Hwv HcspE3. symmetry. exact Hspd4. }
    iPoseProof (ydi_28 with "Htext") as "Hi28".
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24". { iExists _. iEval (rewrite Hb1 -Hcsp_mrel). iExact "Hr24". }
      iSplitL "Hr16". { iExists _. iEval (rewrite Hb2 -HcspE1). iExact "Hr16". }
      iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3 -HcspE2). iExact "Hr8". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (YD + 0x28)) (mword_of_int 2 : mword 6) E3 (av - 4)%nat 4 true Hpop
              with "Hcg Hpc Hi28 Hframe4 [-]").
    iIntros (CIDe4 Hse4) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    assert (Hpc2a : add_vec_int (mword_of_int (YD + 0x28) : mword 64) 2 = mword_of_int (YD + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* +0x2a: c.ret *)
    assert (HE4ra : E4 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1. apply upd_eq. }
    iPoseProof (ydi_2a with "Htext") as "Hi2a".
    iApply (wp_cret_s_sconf Φ (mword_of_int (YD + 0x2a)) (mword_of_int 1 : mword 5) E4 av true
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2a [-]").
    iIntros (CIDe5 Hse5) "Hcg Hpc".
    assert (Hra_final : ret_pc (rget E4 (mword_of_int 1 : mword 5))
                        = ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)))
      by (rgne; rewrite HE4ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* Post: hand every resource straight back; callee_saved via threading.*)
    (* The tp conjunct is GONE -- [tp_pin] makes it true by construction,  *)
    (* so [callee_saved] has thirteen components, not fourteen.            *)
    (* ------------------------------------------------------------------ *)
    (* the registers yield itself never writes thread E4 -> mrel -> msch,
       and the ten [Hmsch_*] premises carry them the rest of the way. *)
    assert (Cthr : forall c : mword 5, is_cs_idx c = true ->
      Regidx c ≠ Regidx (mword_of_int 1) -> Regidx c ≠ Regidx (mword_of_int 8) ->
      Regidx c ≠ Regidx (mword_of_int 9) -> Regidx c ≠ Regidx (mword_of_int 10) ->
      Regidx c ≠ Regidx csp_rs1 ->
      E4 !!! Regidx c = msch !!! Regidx c).
    { intros c Hcs H1 H8 H9 H10 Hsp.
      rewrite /E4 upd_ne; [| exact Hsp].
      rewrite /E3 upd_ne; [| exact H9]. rewrite /E2 upd_ne; [| exact H8].
      rewrite /E1 upd_ne; [| exact H1].
      rewrite (callee_saved_lookup Hcs_rel c Hcs).
      rewrite /D1 upd_ne; [| exact H1]. rewrite /D0 upd_ne; [| exact H10].
      reflexivity. }
    assert (Csp : E4 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite HE4sp Hsp0; reflexivity).
    assert (Cs0 : E4 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (yd_peel; reflexivity).
    assert (Cs1 : E4 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (yd_peel; reflexivity).
    assert (Cs2 : E4 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5))
      by (rewrite (Cthr (mword_of_int 18) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch18).
    assert (Cs3 : E4 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5))
      by (rewrite (Cthr (mword_of_int 19) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch19).
    assert (Cs4 : E4 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5))
      by (rewrite (Cthr (mword_of_int 20) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch20).
    assert (Cs5 : E4 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5))
      by (rewrite (Cthr (mword_of_int 21) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch21).
    assert (Cs6 : E4 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5))
      by (rewrite (Cthr (mword_of_int 22) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch22).
    assert (Cs7 : E4 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5))
      by (rewrite (Cthr (mword_of_int 23) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch23).
    assert (Cs8 : E4 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5))
      by (rewrite (Cthr (mword_of_int 24) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch24).
    assert (Cs9 : E4 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5))
      by (rewrite (Cthr (mword_of_int 25) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch25).
    assert (Cs10 : E4 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5))
      by (rewrite (Cthr (mword_of_int 26) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch26).
    assert (Cs11 : E4 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5))
      by (rewrite (Cthr (mword_of_int 27) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch27).
    iDestruct (cpu_own_transport CIDr CIDe5 0 true pj C true ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CIDe5 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E4 with "[%] Hcg Hcpu Hpc Hown' Hpark").
    unfold callee_saved. repeat split; assumption.
  Qed.

End YieldPostSched.

Section ProofYield.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_yield_sconf (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool)
    : wp_yield_sconf_body Φ γs j γl m av eb C b.
  Proof.
    cbv beta delta [wp_yield_sconf_body].
    intros pcE pj ret_tgt Hj Hgl Heb Hav. subst eb.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext Hpc #Hprocs #Hscheds #Hpanic Hown Hpark Hcont".
    (* THE INDEX IS DERIVABLE.  [cpu_own 0 true pj C b] at the enabled base
       forces [b = true] ([CpuOwn.cpu_own_forces_on]), so yield is entirely in
       the hart-GENERIC case -- and its own [wp_next true] obligation is
       dischargeable at any hart, since [pj = proc_addr j] is never
       [zero_reg]. *)
    iDestruct (cpu_own_forces_on with "Hcg Hcpu") as %Hbtrue. subst b.
    (* ------------------------------------------------------------------ *)
    (* Prologue: 32-byte frame (push 4), save ra/s0/s1 (mirror myproc).   *)
    (* ------------------------------------------------------------------ *)
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (ydi_00 with "Htext") as "Hi00".
    iApply (wp_caddi_sp_push_s_sconf Φ pcE (mword_of_int 32 : mword 6) m av 4 true ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (YD + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x02/0x04/0x06: c.sdsp ra/s0/s1 *)
    iPoseProof (ydi_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (YD + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              A0 (av - 4)%nat vr24 true with "Hcg Hpc Hi02 [Hr24] [-]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (YD + 0x02) : mword 64) 2 = mword_of_int (YD + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    iPoseProof (ydi_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (YD + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat vr16 true with "Hcg Hpc Hi04 [Hr16] [-]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (YD + 0x04) : mword 64) 2 = mword_of_int (YD + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    iPoseProof (ydi_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (YD + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              A0 (av - 4)%nat vr8 true with "Hcg Hpc Hi06 [Hr8] [-]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (YD + 0x06) : mword 64) 2 = mword_of_int (YD + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* +0x08: c.addi4spn s0,sp,32 *)
    iPoseProof (ydi_08 with "Htext") as "Hi08".
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (YD + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat true
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (A1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpc0a : add_vec_int (mword_of_int (YD + 0x08) : mword 64) 2 = mword_of_int (YD + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x0a: jal myproc -> a0 = proc_addr j; noff/intena/cur_proc round.  *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (ydi_0a with "Htext") as "Hi0a".
    iApply (wp_jal_s_sconf Φ (mword_of_int (YD + 0x0a)) (mword_of_int 1 : mword 5) (mword_of_int 2095648 : mword 21)
              A1 (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (A2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (YD + 0x0a) : mword 64) 4)]> A1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (YD + 0x0a) : mword 64) 4)]> A1) with A2.
    assert (Hpcmp : add_vec (mword_of_int (YD + 0x0a) : mword 64) (sign_extend' 64 (mword_of_int 2095648 : mword 21))
                    = mword_of_int KernelSyms.myproc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcmp) in "Hpc".
    assert (HA2ra : A2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (YD + 0x0a) : mword 64) 4)
      by (rewrite /A2 upd_eq; reflexivity).
    iDestruct (cpu_own_transport CID CID6 0 true pj C true ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Myproc.wp_myproc_sconf Φ A2 (av - 4)%nat 0 true pj C true
              ltac:(lia)
              ltac:(lia)
              with "Hcg Hcpu Htext Hpc [-]").
    iIntros (CID7 Hs7 ms mp) "%Hmsf Hcg Hcpu Hpc %Hmp".
    destruct Hmp as [Hcs_mp Ha0_mp].
    assert (Hpc0e : ret_pc (A2 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (YD + 0x0e)) by (rewrite HA2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    (* +0x0e: c.mv s1,a0 : s1 := a0 = proc_addr j *)
    iPoseProof (ydi_0e with "Htext") as "Hi0e".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (YD + 0x0e)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              mp (av - 4)%nat true ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (B0 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (mp !!! Regidx (mword_of_int 10 : mword 5)))]> mp).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (mp !!! Regidx (mword_of_int 10 : mword 5)))]> mp) with B0.
    assert (Hpc10 : add_vec_int (mword_of_int (YD + 0x0e) : mword 64) 2 = mword_of_int (YD + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* +0x10: jal acquire *)
    iPoseProof (ydi_10 with "Htext") as "Hi10".
    iApply (wp_jal_s_sconf Φ (mword_of_int (YD + 0x10)) (mword_of_int 1 : mword 5) (mword_of_int 2092318 : mword 21)
              B0 (av - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi10 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (B1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (YD + 0x10) : mword 64) 4)]> B0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (YD + 0x10) : mword 64) 4)]> B0) with B1.
    assert (Hpcaq : add_vec (mword_of_int (YD + 0x10) : mword 64) (sign_extend' 64 (mword_of_int 2092318 : mword 21))
                    = mword_of_int KernelSyms.acquire) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcaq) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x10: acquire(&p->lock) -- take proc j's lock.                     *)
    (* ------------------------------------------------------------------ *)
    assert (Ha0_B1 : B1 !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j).
    { rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite /B0 upd_ne; [| vm_compute; discriminate]. exact Ha0_mp. }
    assert (HB1ra : B1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (YD + 0x10) : mword 64) 4)
      by (rewrite /B1 upd_eq; reflexivity).
    iPoseProof (procs_inv_lookup Φ γs j γl Hgl with "Hprocs") as "#Hislock".
    iDestruct (cpu_own_transport CID7 CID9 0 true pj C true ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Acquire.wp_acquire_sconf Φ γl "proc"%string
              (proc_lock_res Φ γs γl (proc_addr j)) B1 0 true pj C (av - 4)%nat true
              ltac:(lia)
              ltac:(lia)
              with "Hcg Hcpu Htext Hpc [Hislock] Hpanic [-]").
    { iEval (rewrite Ha0_B1). iExact "Hislock". }
    (* FROM HERE TO THE RELEASE THE LOCK IS HELD, so the index is the literal
       [false] and every leaf collapses with [wp_next_off]. *)
    iIntros (CIDa Hsa ms2 macq) "%Hmsf2 Hcg Hpc %Hcs_acq Hlocked HR Hcpu Hpay".
    assert (Hpc14 : ret_pc (B1 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (YD + 0x14)) by (rewrite HB1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* unpack the lock resource; drop the detachable slots (the proc is
       RUNNING, so all three are [emp], but nothing here needs to know). *)
    iDestruct (proc_lock_res_elim Φ γs γl (proc_addr j) with "HR") as (st0 ch0) "(Hstate & Hchan & Hpub & Hslot)".
    iClear "Hslot".
    (* +0x14: c.li a5,3 *)
    iPoseProof (ydi_14 with "Htext") as "Hi14".
    iApply (wp_cli_s_sconf Φ (mword_of_int (YD + 0x14)) (mword_of_int 15 : mword 5) (mword_of_int 3 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6)))) macq (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi14 [-]").
    rewrite wp_next_off.
    iIntros "Hcg Hpc".
    set (C0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6))))]> macq).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6))))]> macq) with C0.
    assert (Hpc16 : add_vec_int (mword_of_int (YD + 0x14) : mword 64) 2 = mword_of_int (YD + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* the s1 value threads (callee-saved) through acquire, so p->state's
       address reconciles to p_state (proc_addr j). *)
    assert (HC0s1 : C0 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
    { rewrite /C0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_acq (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. rewrite /B0 upd_eq Ha0_mp. reflexivity. }
    assert (Hrec_state : add_vec (C0 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 24 : mword 12))
                         = p_state (proc_addr j)).
    { rewrite HC0s1 yd_addv_zero_l. unfold p_state, state_off.
      assert (H24 : sign_extend' 64 (mword_of_int 24 : mword 12) = (mword_of_int 24 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H24. reflexivity. }
    assert (Hsv : trunc32 (C0 !!! Regidx (mword_of_int 15 : mword 5)) = RUNNABLE).
    { rewrite /C0 upd_eq. unfold RUNNABLE. exact yd_runnable. }
    (* the [rget]-spelled twins the store leaf's [pa] / [storeval] want. *)
    assert (Hrec_state_g : add_vec (rget C0 (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 24 : mword 12))
                           = p_state (proc_addr j)) by (rgne; exact Hrec_state).
    assert (Hsv_g : trunc32 (rget C0 (mword_of_int 15 : mword 5)) = RUNNABLE)
      by (rgne; exact Hsv).
    (* +0x16: c.sw a5,24(s1) : p->state := RUNNABLE *)
    iPoseProof (ydi_16 with "Htext") as "Hi16".
    iApply (wp_csw_s_sconf Φ (mword_of_int (YD + 0x16)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
              (mword_of_int 24 : mword 12) C0 (av - 4)%nat st0 false
              with "Hcg Hpc Hi16 [Hstate] [-]").
    { iEval (rewrite Hrec_state_g). iExact "Hstate". }
    rewrite wp_next_off.
    iIntros "Hcg Hpc Hstate".
    iEval (rewrite Hrec_state_g Hsv_g) in "Hstate".
    assert (Hpc18 : add_vec_int (mword_of_int (YD + 0x16) : mword 64) 2 = mword_of_int (YD + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    (* +0x18: jal sched *)
    iPoseProof (ydi_18 with "Htext") as "Hi18".
    iApply (wp_jal_s_sconf Φ (mword_of_int (YD + 0x18)) (mword_of_int 1 : mword 5) (mword_of_int 2096940 : mword 21)
              C0 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi18 [-]").
    rewrite wp_next_off.
    iIntros "Hcg Hpc".
    set (C1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (YD + 0x18) : mword 64) 4)]> C0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (YD + 0x18) : mword 64) 4)]> C0) with C1.
    assert (Hpcsd : add_vec (mword_of_int (YD + 0x18) : mword 64) (sign_extend' 64 (mword_of_int 2096940 : mword 21))
                    = mword_of_int KernelSyms.sched) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcsd) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x18: sched() -- park; resumes with the process dispatched again.  *)
    (* ------------------------------------------------------------------ *)
    assert (HC1ra : C1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (YD + 0x18) : mword 64) 4)
      by (rewrite /C1 upd_eq; reflexivity).
    iDestruct (cpu_own_ctx_take with "Hcpu") as "[HC Hcpuemp]".
    (* acquire's [trap_csrs_pay 0 true] IS the trap-CSR set; it crosses inside
       the chain payload and comes back at the dispatching hart, where this
       function's own release spends it. *)
    iAssert trap_csrs with "[Hpay]" as "Htc". { iExact "Hpay". }
    (* ------------------------------------------------------------------ *)
    (* THE TAKE-OUT: check THIS hart's parked scheduler record out of the   *)
    (* global invariant.  It is what sched's [▷ sched_vc] premise wants,    *)
    (* and it flips the per-PROC receipt to [false] -- the fifth conjunct   *)
    (* of [proc_held].                                                      *)
    (* ------------------------------------------------------------------ *)
    iDestruct (cpu_own_set_proc 1 true pj pj emp with "Hcpuemp") as "[Hph Hback]".
    iApply fupd_wp.
    iMod (SchedCtx.scheds_take Φ γs ⊤ CIDa j with "Hscheds Hph Hpark")
      as "(Hvc & Hph & Hpark)"; [solve_ndisj|exact Hj|].
    iModIntro.
    iDestruct ("Hback" with "Hph") as "Hcpuemp".
    iApply (Sched.wp_sched_sconf Φ γs j γl RUNNABLE ch0 C1 (av - 4)%nat true
              Hj Hgl (needs_ctx_RUNNABLE) eq_refl ltac:(lia)
              with "Hcg Htext Hpc Hprocs [Hlocked Hstate Hchan Hpub Hpark] Htc Hcpuemp Hown Hvc [-]").
    { rewrite /proc_held. iFrame "Hlocked Hstate Hchan Hpub Hpark". }
    (* SCHED RETURNS ON HART [CIDs].  Everything below runs there, inside
       [yield_post_sched] at [(CID0 := CIDs)]. *)
    iIntros (CIDs Hss msch ch') "%Hcs_sch Hcg Hpc Hheld' Htc' #Havail Hcpuemp Hown' Hvc'".
    (* what the post-resume half needs about [msch], read off this tower. *)
    assert (Hsp_msch : msch !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcs_sch csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /C1 upd_ne; [| vm_compute; discriminate]. rewrite /C0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_acq csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. rewrite /B0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_mp csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /A2 upd_ne; [| vm_compute; discriminate]. rewrite /A1 upd_ne; [| vm_compute; discriminate].
      exact HcspA0. }
    assert (Hs1_msch : msch !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
    { rewrite (callee_saved_lookup Hcs_sch (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /C1 upd_ne; [| vm_compute; discriminate]. exact HC0s1. }
    assert (Hthr : forall c : mword 5, is_cs_idx c = true ->
      Regidx c ≠ Regidx (mword_of_int 1) -> Regidx c ≠ Regidx (mword_of_int 8) ->
      Regidx c ≠ Regidx (mword_of_int 9) -> Regidx c ≠ Regidx (mword_of_int 10) ->
      Regidx c ≠ Regidx (mword_of_int 15) -> Regidx c ≠ Regidx csp_rs1 ->
      msch !!! Regidx c = m !!! Regidx c).
    { intros c Hcs H1 H8 H9 H10 H15 Hsp.
      rewrite (callee_saved_lookup Hcs_sch c Hcs).
      rewrite /C1 upd_ne; [| exact H1]. rewrite /C0 upd_ne; [| exact H15].
      rewrite (callee_saved_lookup Hcs_acq c Hcs).
      rewrite /B1 upd_ne; [| exact H1]. rewrite /B0 upd_ne; [| exact H9].
      rewrite (callee_saved_lookup Hcs_mp c Hcs).
      rewrite /A2 upd_ne; [| exact H1]. rewrite /A1 upd_ne; [| exact H8].
      rewrite /A0 upd_ne; [| exact Hsp]. reflexivity. }
    assert (Hmsch18 : msch !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5))
      by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hmsch19 : msch !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5))
      by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hmsch20 : msch !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5))
      by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hmsch21 : msch !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5))
      by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hmsch22 : msch !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5))
      by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hmsch23 : msch !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5))
      by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hmsch24 : msch !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5))
      by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hmsch25 : msch !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5))
      by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hmsch26 : msch !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5))
      by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hmsch27 : msch !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5))
      by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    (* the pc: sched hands back [ret_pc (C1 !!! ra)] = YD + 0x1c *)
    assert (Hpc1c : ret_pc (C1 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (YD + 0x1c)) by (rewrite HC1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    (* the three saved frame cells, re-addressed at [pa_stk sp0 k]. *)
    assert (HraA0 : A0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0A0 : A0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1A0 : A0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HcspA0 HraA0 -Hb1) in "Hr24".
    iEval (rewrite HcspA0 Hs0A0 -Hb2) in "Hr16".
    iEval (rewrite HcspA0 Hs1A0 -Hb3) in "Hr8".
    (* ONE application of the post-resume half, at the resuming hart. *)
    iApply (yield_post_sched (CID0 := CIDs) Φ γs j γl ch' m msch av C sp0 spd vgap
              ltac:(lia) Hj ltac:(reflexivity) ltac:(reflexivity)
              Hsp_msch Hs1_msch
              Hmsch18 Hmsch19 Hmsch20 Hmsch21 Hmsch22 Hmsch23 Hmsch24 Hmsch25 Hmsch26 Hmsch27
              with "Htext Hislock Hscheds Hcg Hpc Hheld' Htc' Hcpuemp HC Hown' Hvc' Hr24 Hr16 Hr8 Hgap [Hcont]").
    (* yield's own [wp_next true pj] obligation, re-anchored at the resuming
       hart: at [b = true] the only pinning condition left is
       [pj = zero_reg], which [proc_addr_nonzero] refutes -- so the
       obligation transports to ANY hart. *)
    iIntros (CIDx Hsx).
    iSpecialize ("Hcont" $! CIDx with "[%]").
    { intros [Hf | Hz]; [discriminate | exfalso; exact (proc_addr_nonzero j Hj Hz)]. }
    iExact "Hcont".
  Qed.

End ProofYield.

End YieldProof.
