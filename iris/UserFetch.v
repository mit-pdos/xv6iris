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
From iris.program_logic Require Import language lifting.
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

(* ===================================================================== *)
(* §4 The Iris FETCH-FAULT arm: a fetch that faults (odd, non-canonical,   *)
(* unmapped, or fetch-denied pc) traps the ACTIVE user hart to stvec,      *)
(* producing [user_trap_frame].  ONE arm, generic over a per-flavor        *)
(* fault-derivation callback (the §2 / UserTranslate §3 facts plug in).    *)
(* ===================================================================== *)
(* ===================================================================== *)
(* §5 The fetch-SUCCESS reductions (4-aligned pc): translation Ok +        *)
(* readable bytes => F_Base / F_RVC.  Generic over the translate's output  *)
(* state (hit: s' = s; walk: s' = the TLB-filled state) -- the mem_read    *)
(* facts live at s'.                                                       *)
(* ===================================================================== *)

Lemma exec_fetch_bytes_ok (width : Z) (fs gs pa : mword 64)
    (w : mword (8 * width)) (s s' : mstate) :
  exec (translateAddr (Virtaddr gs) (InstructionFetch tt)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  exec (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) width false false false) s'
    = Some (Ok w, s') ->
  exec (fetch_bytes fs gs width) s
    = Some (FetchBytes_Success (autocast (T := mword) w), s').
Proof.
  intros Htr Hmr.
  unfold fetch_bytes.
  rewrite exec_catch_early_return.
  change (ext_fetch_check_pc fs gs) with (@None unit). cbv iota beta.
  rewrite (execR_bind_Some _ _ _ _ _
    (_ : execR (Defs.bind0 (Defs.returnR _ tt)
            (Defs.liftR (translateAddr (Virtaddr gs) (InstructionFetch tt)))) s
         = Some (inr (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), s'))).
  2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite Htr.
      cbn match. reflexivity. }
  cbv iota beta.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s')).
  cbv iota beta.
  rewrite (execR_bind_Some _ _ _ _ _
    (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa)
                              width false false false)) s'
         = Some (inr (Ok w), s'))).
  2:{ rewrite execR_liftR. rewrite Hmr. cbn match. reflexivity. }
  cbv iota beta.
  rewrite execR_returnR_fwd. cbn match. reflexivity.
Qed.

Section UserFetchOk4.
  Context (s s' : mstate) (pc pa : mword 64) (w : mword 32).
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = true.
  Hypothesis Htr :
    exec (translateAddr (Virtaddr pc) (InstructionFetch tt)) s
      = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hmr :
    exec (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4 false false false) s'
      = Some (Ok w, s').

  Let HrdPC : exec (Defs.read_reg PC) s = Some (pc, s).
  Proof. rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. Qed.

  Lemma exec_fetch_ok_4 :
    exec (fetch tt) s
      = Some ((if isRVC (subrange_vec_dec (autocast (T := mword) w : mword 32) 15 0)
               then F_RVC (subrange_vec_dec (autocast (T := mword) w : mword 32) 15 0)
               else F_Base (autocast (T := mword) w)), s').
  Proof using HpcPC Hvalign Htr Hmr.
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
              (exec_fetch_bytes_ok 4 pc pc pa w s s' Htr Hmr)).
    cbv iota beta.
    destruct (isRVC (subrange_vec_dec (autocast (T := mword) w : mword 32) 15 0)) eqn:Hrvc;
      rewrite Hrvc; rewrite execR_returnR_fwd; cbn match; reflexivity.
  Qed.

End UserFetchOk4.

(* The upt-record fetch-success composer that used to follow (§6,
   [upt_fetch_instr]) was superseded by the ptree layer: the bundle-level
   composer is [user_pt_fetch_instr] (UserFetchPt.v).                    *)

(* ===================================================================== *)
(* §6 The 2-ALIGNED (split) fetch reductions, premise-shaped (the         *)
(* translate and mem_read outcomes come in as facts, so the lemmas are    *)
(* privilege-blind).  A pc with bit0 = 0 and bit1 = 1 takes the split     *)
(* path: a halfword at pc (RVC if its low bits say so), else a SECOND     *)
(* independently-translated halfword at pc+2 (possibly another page).     *)
(* ===================================================================== *)

Section UserFetchSplit.
  Context (s s1 : mstate) (va pa : mword 64).
  Hypothesis HpcPC : register_lookup PC s.(sregs) = va.
  Hypothesis HmisaC : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Hbit0 : neq_vec (access_vec_dec va 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec va 1) ('b"0") = true.
  Hypothesis Hvalign4 : is_aligned_vaddr (Virtaddr va) 4 = false.

  Let HrdPC : exec (Defs.read_reg PC) s = Some (va, s).
  Proof. rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. Qed.

  (* the shared head: dispatch into the split path *)
  Local Ltac split_head :=
    unfold fetch;
    rewrite exec_catch_early_return;
    change (get_config_rvfi tt) with false; cbv iota beta;
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC);
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC);
    change (ext_fetch_check_pc va va) with (@None unit); cbv iota beta;
    rewrite (execR_bind_Some _ _ _ false s);
    [ | rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s));
        unfold or_boolM;
        rewrite (execR_bind_Some _ _ _ false s);
        [ | rewrite (execR_liftR_seq _ _ _ _ _ HrdPC); rewrite Hbit0; apply execR_returnR_fwd ];
        cbv iota beta;
        unfold and_boolM;
        rewrite (execR_bind_Some _ _ _ true s);
        [ | rewrite (execR_liftR_seq _ _ _ _ _ HrdPC); rewrite Hbit1; apply execR_returnR_fwd ];
        cbv iota beta;
        rewrite (execR_bind_Some _ _ _ true s);
        [ | rewrite execR_liftR; rewrite (exec_currentlyEnabled_Zca s HmisaC); cbn match;
            apply execR_returnR_fwd ];
        cbv iota beta; reflexivity ];
    cbv iota beta;
    rewrite (execR_bind_Some _ _ _ false s);
    [ | unfold and_boolM;
        rewrite (execR_bind_Some _ _ _ false s);
        [ | rewrite (execR_liftR_seq _ _ _ _ _ HrdPC); rewrite Hvalign4; apply execR_returnR_fwd ];
        cbv iota beta; reflexivity ];
    cbv iota beta;
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC);
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).

  (* the first halfword's fetch_bytes, from its translate + read facts *)
  Section FirstHalfOk.
    Context (ilo : mword 16).
    Hypothesis Htrl :
      exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s1).
    Hypothesis Hmrl :
      exec (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 2 false false false) s1
        = Some (Ok ilo, s1).

    Let Hfb2l : exec (fetch_bytes va va 2) s = Some (@FetchBytes_Success 2 ilo, s1).
    Proof.
      unfold fetch_bytes.
      rewrite exec_catch_early_return.
      change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _
        (_ : execR (Defs.bind0 (Defs.returnR _ tt)
                (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
             = Some (inr (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), s1))).
      2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
          rewrite execR_liftR. rewrite Htrl. cbn match. reflexivity. }
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s1)).
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _
        (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa)
                                  2 false false false)) s1
             = Some (inr (Ok ilo), s1))).
      2:{ rewrite execR_liftR. rewrite Hmrl. cbn match. reflexivity. }
      cbv iota beta. rewrite autocast_mword_id_16.
      rewrite execR_returnR_fwd. cbn match. reflexivity.
    Qed.

    (* RVC: the low halfword is a compressed instruction *)
    Lemma exec_fetch_rvc_2 :
      isRVC ilo = true ->
      exec (fetch tt) s = Some (F_RVC ilo, s1).
    Proof using HpcPC HmisaC Hbit0 Hbit1 Hvalign4 Htrl Hmrl.
      intros HisRVC.
      split_head.
      rewrite (execR_liftR_seq _ _ _ _ _ Hfb2l).
      cbv iota beta.
      match goal with
      | |- context [isRVC ?x] =>
          replace (isRVC x) with true by (symmetry; exact HisRVC)
      end.
      cbv iota beta.
      rewrite execR_returnR_fwd. cbn match. reflexivity.
    Qed.

    Section SecondHalf.
      Context (s2 : mstate) (pah : mword 64).
      Hypothesis HpcPC1 : register_lookup PC s1.(sregs) = va.
      Hypothesis HnotRVC : isRVC ilo = false.

      Let HrdPC1 : exec (Defs.read_reg PC) s1 = Some (va, s1).
      Proof. rewrite (exec_read_reg PC s1). rewrite HpcPC1. reflexivity. Qed.

      (* BASE: the second halfword translates (possibly onto ANOTHER page)
         and reads at the moved state *)
      Lemma exec_fetch_base_2 (ihi : mword 16) :
        exec (translateAddr (Virtaddr (add_vec_int va 2)) (InstructionFetch tt)) s1
          = Some (Ok (Physaddr pah, PBMT_PMA, init_ext_ptw), s2) ->
        exec (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pah) 2 false false false) s2
          = Some (Ok ihi, s2) ->
        exec (fetch tt) s = Some (F_Base (concat_vec ihi ilo), s2).
      Proof using HpcPC HpcPC1 HmisaC Hbit0 Hbit1 Hvalign4 Htrl Hmrl HnotRVC.
        intros Htrh Hmrh.
        assert (Hfb2h : exec (fetch_bytes va (add_vec_int va 2) 2) s1
                        = Some (@FetchBytes_Success 2 ihi, s2)).
        { unfold fetch_bytes.
          rewrite exec_catch_early_return.
          change (ext_fetch_check_pc va (add_vec_int va 2)) with (@None unit). cbv iota beta.
          rewrite (execR_bind_Some _ _ _ _ _
            (_ : execR (Defs.bind0 (Defs.returnR _ tt)
                    (Defs.liftR (translateAddr (Virtaddr (add_vec_int va 2))
                                   (InstructionFetch tt)))) s1
                 = Some (inr (Ok (Physaddr pah, PBMT_PMA, init_ext_ptw)), s2))).
          2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s1)).
              rewrite execR_liftR. rewrite Htrh. cbn match. reflexivity. }
          cbv iota beta.
          rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pah, PBMT_PMA) s2)).
          cbv iota beta.
          rewrite (execR_bind_Some _ _ _ _ _
            (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pah)
                                      2 false false false)) s2
                 = Some (inr (Ok ihi), s2))).
          2:{ rewrite execR_liftR. rewrite Hmrh. cbn match. reflexivity. }
          cbv iota beta. rewrite autocast_mword_id_16.
          rewrite execR_returnR_fwd. cbn match. reflexivity. }
        split_head.
        rewrite (execR_liftR_seq _ _ _ _ _ Hfb2l).
        cbv iota beta.
        match goal with
        | |- context [isRVC ?x] =>
            replace (isRVC x) with false by (symmetry; exact HnotRVC)
        end.
        cbv iota beta.
        rewrite (execR_liftR_seq _ _ _ _ _ HrdPC1).
        rewrite (execR_liftR_seq _ _ _ _ _ HrdPC1).
        rewrite (execR_liftR_seq _ _ _ _ _ Hfb2h).
        cbv iota beta. rewrite execR_returnR_fwd. cbn match. reflexivity.
      Qed.

      (* the SECOND halfword's translation faults: the reported va is pc+2 *)
      Lemma exec_fetch_fault_2_second (ex : ExceptionType) :
        exec (translateAddr (Virtaddr (add_vec_int va 2)) (InstructionFetch tt)) s1
          = Some (Err (ex, tt), s1) ->
        exec (fetch tt) s = Some (F_Error (ex, add_vec_int va 2), s1).
      Proof using HpcPC HpcPC1 HmisaC Hbit0 Hbit1 Hvalign4 Htrl Hmrl HnotRVC.
        intros Htrh.
        split_head.
        rewrite (execR_liftR_seq _ _ _ _ _ Hfb2l).
        cbv iota beta.
        match goal with
        | |- context [isRVC ?x] =>
            replace (isRVC x) with false by (symmetry; exact HnotRVC)
        end.
        cbv iota beta.
        rewrite (execR_liftR_seq _ _ _ _ _ HrdPC1).
        rewrite (execR_liftR_seq _ _ _ _ _ HrdPC1).
        rewrite (execR_liftR_seq _ _ _ _ _
                  (exec_fetch_bytes_fault 2 va (add_vec_int va 2) ex s1 s1 Htrh)).
        cbv iota beta.
        rewrite (execR_liftR_seq _ _ _ _ _ HrdPC1).
        rewrite execR_returnR_fwd. cbn match. reflexivity.
      Qed.

    End SecondHalf.
  End FirstHalfOk.

  (* the FIRST halfword's translation faults: the reported va is pc *)
  Lemma exec_fetch_fault_2_first (ex : ExceptionType) :
    exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
      = Some (Err (ex, tt), s) ->
    exec (fetch tt) s = Some (F_Error (ex, va), s).
  Proof using HpcPC HmisaC Hbit0 Hbit1 Hvalign4.
    intros Htr.
    split_head.
    rewrite (execR_liftR_seq _ _ _ _ _
              (exec_fetch_bytes_fault 2 va va ex s s Htr)).
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

End UserFetchSplit.
