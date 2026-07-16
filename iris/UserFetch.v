(* UserFetch.v -- the U-mode instruction-fetch layer: exec-level reductions
   of the model's [fetch] over the user page table.

   FAULT side (this file's first installment): a fetch whose pc is odd
   raises E_Fetch_Addr_Align before touching memory; a 4-aligned fetch
   whose translation errs surfaces the exception as [F_Error (e, pc)],
   which [run_hart_active] turns into [Step_Fetch_Failure] -- delivered by
   UserTrap.v's tower.  The 2-aligned (split) fetch variants land together
   with the 2-aligned success machinery.

   All lemmas are state-threading generic where translation can fill the
   TLB; the pure fault paths leave the state untouched.                   *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpIntrCore.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 fetch_bytes on a FAILED translation: the exception surfaces.         *)
(* Generic over the chunk width and the translate's output state (a walk   *)
(* that faults leaves the state untouched, but a straddling second chunk   *)
(* runs after the first chunk's TLB fill).                                 *)
(* ===================================================================== *)
Lemma exec_fetch_bytes_fault (width : Z) (fs gs : mword 64) (ex : ExceptionType)
    (s s' : mstate) :
  exec (translateAddr (Virtaddr gs) (InstructionFetch tt)) s
    = Some (Err (ex, tt), s') ->
  exec (fetch_bytes fs gs width) s = Some (FetchBytes_Exception ex, s').
Proof.
  intros Htr.
  unfold fetch_bytes.
  rewrite exec_catch_early_return.
  change (ext_fetch_check_pc fs gs) with (@None unit). cbv iota beta.
  rewrite (execR_bind_Some _ _ _ _ _
    (_ : execR (Defs.bind0 (Defs.returnR _ tt)
            (Defs.liftR (translateAddr (Virtaddr gs) (InstructionFetch tt)))) s
         = Some (inr (Err (ex, tt)), s'))).
  2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite Htr.
      cbn match. reflexivity. }
  cbv iota beta.
  rewrite execR_bind. rewrite execR_early_return. cbn match.
  reflexivity.
Qed.

(* ===================================================================== *)
(* §2 The whole [fetch] on the fault paths.                                *)
(* ===================================================================== *)
Section UserFetchFault.
  Context (s : mstate) (pc : mword 64).
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.

  Let HrdPC : exec (Defs.read_reg PC) s = Some (pc, s).
  Proof. rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. Qed.

  (* an ODD pc: E_Fetch_Addr_Align before any translation or memory read
     (with Zca enabled, bit 1 never matters -- only bit 0) *)
  Lemma exec_fetch_align_fault :
    neq_vec (access_vec_dec pc 0) ('b"0") = true ->
    exec (fetch tt) s = Some (F_Error (E_Fetch_Addr_Align tt, pc), s).
  Proof using HpcPC.
    intros Hbit0.
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ true s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0.
            apply execR_returnR_fwd. }
        cbv iota beta. apply execR_returnR_fwd. }
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

  (* a 4-ALIGNED pc whose translation faults *)
  Lemma exec_fetch_fault_4 (ex : ExceptionType) :
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    exec (translateAddr (Virtaddr pc) (InstructionFetch tt)) s
      = Some (Err (ex, tt), s) ->
    exec (fetch tt) s = Some (F_Error (ex, pc), s).
  Proof using HpcPC.
    intros Hvalign Htr.
    destruct (align4_low_bits pc Hvalign) as [Hbit0 Hbit1].
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0.
            apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1.
            apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ true s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign.
            apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif.
        cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _
              (exec_fetch_bytes_fault 4 pc pc ex s s Htr)).
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

End UserFetchFault.

(* ===================================================================== *)
(* §3 run_hart_active on a failed fetch (privilege-generic): no decode,    *)
(* no execute; the step result is Step_Fetch_Failure, delivered by the     *)
(* trap tower via try_step's arm ([exec_riscv_step_fetch_failure]).        *)
(* ===================================================================== *)
Lemma exec_run_hart_active_fetch_failure
    (priv : Privilege) (s s_f : mstate) (vaddr : mword 64) (ex : ExceptionType) :
  register_lookup cur_privilege s.(sregs) = priv ->
  exec (dispatchInterrupt priv) s = Some (None, s) ->
  exec (fetch tt) s = Some (F_Error (ex, vaddr), s_f) ->
  exec (run_hart_active 0) s = Some (Step_Fetch_Failure (Virtaddr vaddr, ex), s_f).
Proof.
  intros Hpriv Hdisp Hfetch.
  unfold run_hart_active.
  rewrite exec_catch_early_return.
  rewrite execR_bind execR_liftR exec_read_reg Hpriv. cbn match.
  rewrite execR_bind execR_liftR Hdisp. cbn match.
  rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
  rewrite execR_liftR Hfetch. cbn match. cbn match.
  unfold ext_fetch_hook. cbn match. cbn beta iota.
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.
