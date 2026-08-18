(* HartRunFull.v -- [run_hart_active] WITH THE OUTCOME LEFT TO THE MACHINE,
   and the User-mode interrupt dispatch that feeds it.

   [HartRunGen]'s two rules already drop the privilege and make the dispatch
   and the fetch obligations.  They still bake in THREE things that the user
   tier cannot accept, and each one is forced by a user outcome the M/S rules
   cannot express:

     - THE FETCH SHAPE.  [swp_run_hart_active_gen] hardcodes [r = F_Base w]
       (its twin [F_RVC h]), so a caller whose fetch may FAULT has no rule at
       all: the model early-returns an [F_Error] as [Step_Fetch_Failure], and
       a user fetch walks a page table that may refuse it.  Here the fetch
       obligation is MATCH-SHAPED over [FetchResult]: the caller says, per
       constructor, what it is prepared to have happen -- and gives [False]
       for the shapes it has ruled out.  The base and RVC arms carry their
       own tail (the decode certificate, the landing-pad refusal, the
       compressed gate, and the execute obligation) INSIDE the fetch's
       postcondition, because the file the fetch lands on is existential:
       a TLB-filling or A/D-updating walk does not land where it started.

     - THE EXECUTE RESULT.  [⌜e = RETIRE_SUCCESS⌝] becomes an arbitrary
       [r : ExecutionResult] with the postcondition MATCHING on it, since a
       user instruction may Trap, be Illegal, or Enter_Wait
       ([UserClassify.u_result_ok]).  Nothing downstream of [execute] looks
       at the result other than to hand it to [Step_Execute], so the rule
       does not have to know which one it is.

     - THE [ExecuteAs] REDIRECT.  The model re-executes exactly once and
       feeds the SECOND result to [Step_Execute] unfiltered.  So the redirect
       is not a side condition but a second obligation, and it lives in the
       first execute's own postcondition ([run_exec_post]) -- which is what
       lets ONE rule serve both the direct and the redirecting composers
       ([SmodeCore.exec_hart_active_progress_base_gen] / [_RVC_gen],
       [UserStep.exec_hart_active_progress_base_redirect_gen] /
       [_RVC_direct_gen]) with no case split at the call site.

   Contents:
   §1  [dispatch_of_pending] and [swp_dispatchInterrupt_U] -- the dispatch at
       User.  It is STRICTLY SIMPLER than [WpIntrCore.swp_dispatchInterrupt_S]:
       at User both effective enables short-circuit on the privilege
       comparison alone ([and_boolM (returnM false) _]), so mstatus is never
       read and the rule takes no mstatus premise.  The PLIC wires are
       ∀-peeled exactly as in the S rule -- [swp_read_mip_S] and
       [swp_external_interrupts_pending_S] are privilege-free and are reused
       verbatim -- so the answer is EXISTENTIAL in [sig_meip] / [sig_seip].
   §2  [swp_run_hart_active_full] -- the core rule.
   §3  the five instances: the four that mirror the tier's exec composers,
       and the fetch-failure one.
   §4  [swp_run_hart_active_U] -- §2 with §1's dispatch discharged.

   The whole file is PRIVILEGE-GENERIC except §1 and §4.                    *)
From Stdlib Require Import ZArith Bool Zquot Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins
        SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import ExecCommon.
Require Import HartSwp HartLift HartRegNode HartSpan HartSpanChar HartGoodb
        WpDecodeBridge WpMmodeCsrSwp HartRunGen.
Require Import RiscvExtras.
Require Import SmodeCore WpIntrCore.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 THE DISPATCH AT USER.                                               *)
(* ===================================================================== *)

(* The dispatch decision once the S-destined pending set is known.  Both
   [WpIntrCore.s_dispatch] (Supervisor, gated on mstatus.SIE) and
   [UserStep.u_dispatch] (User, ungated) are readings of this one function;
   [u_dispatch mip meip seip mie mdv] IS
   [dispatch_of_pending (s_pending mip meip seip mie mdv)], by [reflexivity]. *)
Definition dispatch_of_pending (ip : mword 64)
    : option (InterruptType * Privilege) :=
  if neq_vec ip (zeros' 64)
  then match findPendingInterrupt ip with
       | Some i => Some (i, Supervisor)
       | None => None
       end
  else None.

Section rundisp.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [getPendingSet User].  Mirrors [WpIntrCore.swp_getPendingSet_S] node for
     node; the two boolean blocks are bridged as their exec facts, and at
     User each is data-free (the privilege comparison decides it), so this
     rule -- unlike the S one -- needs neither [Db mstatus = true] nor a
     value for mstatus. *)
  Lemma swp_getPendingSet_U (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (dst : mstate) (Db : register -> bool)
      (mip_v mie_v mdv_v : mword 64) :
    Drw ## Dro ->
    (mip : register) ∈ Drw ∪ Dro ->
    (mie : register) ∈ Drw ∪ Dro ->
    (mideleg : register) ∈ Drw ∪ Dro ->
    register_lookup mip rs = mip_v ->
    register_lookup mie rs = mie_v ->
    register_lookup mideleg rs = mdv_v ->
    and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
    (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, Db r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    exec (currentlyEnabled Ext_S) dst = Some (true, dst) ->
    goodb Db (currentlyEnabled Ext_S) dst = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (getPendingSet User)
      (fun v => ∃ meip seip : mword 1,
                ⌜v = (if neq_vec (s_pending mip_v meip seip mie_v mdv_v)
                                 (zeros' 64)
                      then Some (s_pending mip_v meip seip mie_v mdv_v,
                                 Supervisor)
                      else None)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof. Admitted.

  Lemma swp_dispatchInterrupt_U (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (dst : mstate)
      (Db : register -> bool) (mip_v mie_v mdv_v : mword 64) :
    Drw ## Dro ->
    (mip : register) ∈ Drw ∪ Dro ->
    (mie : register) ∈ Drw ∪ Dro ->
    (mideleg : register) ∈ Drw ∪ Dro ->
    register_lookup mip rs = mip_v ->
    register_lookup mie rs = mie_v ->
    register_lookup mideleg rs = mdv_v ->
    and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
    (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, Db r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    exec (currentlyEnabled Ext_S) dst = Some (true, dst) ->
    goodb Db (currentlyEnabled Ext_S) dst = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (dispatchInterrupt User)
      (fun r => ∃ meip seip : mword 1,
                ⌜r = dispatch_of_pending
                       (s_pending mip_v meip seip mie_v mdv_v)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof. Admitted.

End rundisp.

(* ===================================================================== *)
(* §2 [run_hart_active], RESULT-GENERIC.                                  *)
(* ===================================================================== *)

Section runfull.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac r_glue :=
    cbn beta iota zeta delta
      [Defs.returnm returnM returnR Defs.returnR andb orb negb not
       Instances.generic_eq Instances.generic_neq get_config_rvfi
       get_config_print_instr].

  (* THE EXECUTE OBLIGATION'S POSTCONDITION.  The model re-executes an
     [ExecuteAs] ONCE and feeds the second result to [Step_Execute]
     unfiltered, so the redirect is a second [swp] sitting in the first
     execute's post -- not a side condition, and not a separate rule. *)
  Definition run_exec_post (Pe : ExecutionResult -> mword 32 -> iProp Σ)
      (ib : mword 32) (e : ExecutionResult) : iProp Σ :=
    match e with
    | ExecuteAs other => swp (execute other) (fun e' => Pe e' ib)
    | _ => Pe e ib
    end.

  (* THE BASE FETCH'S TAIL.  [rsf] is existential because a fetch that fills
     the TLB or updates A/D does not land on the file it started from; the
     decode certificate, the landing-pad refusal and the PC value are
     therefore stated ABOUT [rsf] here rather than as premises of the rule. *)
  Definition run_fetch_base (Drw Dro : gset register) (Df : register -> dfrac)
      (Pe : ExecutionResult -> mword 32 -> iProp Σ) (w : mword 32) : iProp Σ :=
    (∃ (rsf : regstate) (i : instruction) (pc : mword 64) (nl : nat),
       ⌜register_lookup (R_bitvector_64 PC) rsf = pc⌝ ∗
       ⌜hval (Drw ∪ Dro) Drw rsf (ext_decode w) i rsf⌝ ∗
       ⌜hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
          = Some (false, rsf)⌝ ∗
       hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
       (hreg_frame (register_set (R_bitvector_64 nextPC)
                      (add_vec_int pc 4) rsf) Drw -∗
        hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                      (add_vec_int pc 4) rsf) Dro -∗
        swp (execute i) (run_exec_post Pe (zero_extend' 32 w))))%I.

  (* THE COMPRESSED FETCH'S TAIL.  Same, plus the [Ext_Zca] gate: the model
     answers a compressed word with [Illegal_Instruction] when the extension
     is off, and this rule covers only the enabled path. *)
  Definition run_fetch_rvc (Drw Dro : gset register) (Df : register -> dfrac)
      (Pe : ExecutionResult -> mword 32 -> iProp Σ) (h : mword 16) : iProp Σ :=
    (∃ (rsf : regstate) (i : instruction) (pc : mword 64) (nl nz : nat),
       ⌜register_lookup (R_bitvector_64 PC) rsf = pc⌝ ∗
       ⌜hval (Drw ∪ Dro) Drw rsf (ext_decode_compressed h) i rsf⌝ ∗
       ⌜hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
          = Some (false, rsf)⌝ ∗
       ⌜hfrun nz (Drw ∪ Dro) Drw rsf (currentlyEnabled Ext_Zca)
          = Some (true, rsf)⌝ ∗
       hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
       (hreg_frame (register_set (R_bitvector_64 nextPC)
                      (add_vec_int pc 2) rsf) Drw -∗
        hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                      (add_vec_int pc 2) rsf) Dro -∗
        swp (execute i) (run_exec_post Pe (zero_extend' 32 h))))%I.

  (* THE FETCH OBLIGATION'S POSTCONDITION: one arm per [FetchResult]
     constructor.  A caller that has ruled a shape out gives [False] for it. *)
  Definition run_fetch_post (Drw Dro : gset register) (Df : register -> dfrac)
      (Pe : ExecutionResult -> mword 32 -> iProp Σ)
      (Pf : mword 64 -> ExceptionType -> iProp Σ)
      (Px : ext_fetch_addr_error -> iProp Σ) (fr : FetchResult) : iProp Σ :=
    match fr with
    | F_Base w        => run_fetch_base Drw Dro Df Pe w
    | F_RVC h         => run_fetch_rvc Drw Dro Df Pe h
    | F_Error (e, xv) => Pf xv e
    | F_Ext_Error x   => Px x
    end.

  (* ==================================================================== *)
  (* THE CORE RULE.                                                        *)
  (* ==================================================================== *)
  Lemma swp_run_hart_active_full (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (p : Privilege)
      (Qi : InterruptType -> Privilege -> iProp Σ)
      (Pe : ExecutionResult -> mword 32 -> iProp Σ)
      (Pf : mword 64 -> ExceptionType -> iProp Σ)
      (Px : ext_fetch_addr_error -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (* THE DISPATCH: the machine picks the arm *)
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (* THE FETCH: the machine picks the SHAPE, and each shape carries its
       own tail *)
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt) (run_fetch_post Drw Dro Df Pe Pf Px)) -∗
    swp (run_hart_active 0)
      (fun st => match st with
                 | Step_Pending_Interrupt (ii, pr) => Qi ii pr
                 | Step_Execute (r, ib)            => Pe r ib
                 | Step_Fetch_Failure (Virtaddr xv, e) => Pf xv e
                 | Step_Ext_Fetch_Failure x        => Px x
                 | Step_Waiting _                  => False
                 end).
  Proof. Admitted.

  (* ==================================================================== *)
  (* §3 THE INSTANCES.  Each pins the fetch's shape and reads off exactly   *)
  (* one of the tier's exec composers; the conclusion is [HartRunGen]'s     *)
  (* disjunctive one, generalised from [RETIRE_SUCCESS] to any [resf].      *)
  (* ==================================================================== *)

  (* the swp twin of [SmodeCore.exec_hart_active_progress_base_gen] *)
  Lemma swp_run_hart_active_base (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rsf : regstate) (p : Privilege)
      (pc : mword 64) (w : mword 32) (i : instruction) (nl : nat)
      (resf : ExecutionResult) (R : iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    register_lookup (R_bitvector_64 PC) rsf = pc ->
    hval (Drw ∪ Dro) Drw rsf (ext_decode w) i rsf ->
    hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
      = Some (false, rsf) ->
    (match resf with ExecuteAs _ => False | _ => True end) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt)
         (fun r => ⌜r = F_Base w⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 4) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 4) rsf) Dro -∗
     swp (execute i) (fun e => ⌜e = resf⌝ ∗ R)) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (⌜st = Step_Execute (resf, zero_extend' 32 w)⌝ ∗ R)).
  Proof. Admitted.

  (* the swp twin of [UserStep.exec_hart_active_progress_base_redirect_gen] *)
  Lemma swp_run_hart_active_base_redirect (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rsf : regstate) (p : Privilege)
      (pc : mword 64) (w : mword 32) (i other : instruction) (nl : nat)
      (resf : ExecutionResult) (R : iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    register_lookup (R_bitvector_64 PC) rsf = pc ->
    hval (Drw ∪ Dro) Drw rsf (ext_decode w) i rsf ->
    hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
      = Some (false, rsf) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt)
         (fun r => ⌜r = F_Base w⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 4) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 4) rsf) Dro -∗
     swp (execute i)
       (fun e => ⌜e = ExecuteAs other⌝ ∗
                 swp (execute other) (fun e' => ⌜e' = resf⌝ ∗ R))) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (⌜st = Step_Execute (resf, zero_extend' 32 w)⌝ ∗ R)).
  Proof. Admitted.

  (* the swp twin of [SmodeCore.exec_hart_active_progress_RVC_gen] *)
  Lemma swp_run_hart_active_rvc (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rsf : regstate) (p : Privilege)
      (pc : mword 64) (h : mword 16) (i other : instruction) (nl : nat)
      (resf : ExecutionResult) (R : iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    register_lookup (R_bitvector_64 PC) rsf = pc ->
    eq_vec (_get_Misa_C (register_lookup misa rsf))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    hval (Drw ∪ Dro) Drw rsf (ext_decode_compressed h) i rsf ->
    hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
      = Some (false, rsf) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt)
         (fun r => ⌜r = F_RVC h⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Dro -∗
     swp (execute i)
       (fun e => ⌜e = ExecuteAs other⌝ ∗
                 swp (execute other) (fun e' => ⌜e' = resf⌝ ∗ R))) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (⌜st = Step_Execute (resf, zero_extend' 32 h)⌝ ∗ R)).
  Proof. Admitted.

  (* the swp twin of [UserStep.exec_hart_active_progress_RVC_direct_gen] *)
  Lemma swp_run_hart_active_rvc_direct (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rsf : regstate) (p : Privilege)
      (pc : mword 64) (h : mword 16) (i : instruction) (nl : nat)
      (resf : ExecutionResult) (R : iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    register_lookup (R_bitvector_64 PC) rsf = pc ->
    eq_vec (_get_Misa_C (register_lookup misa rsf))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    hval (Drw ∪ Dro) Drw rsf (ext_decode_compressed h) i rsf ->
    hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
      = Some (false, rsf) ->
    (match resf with ExecuteAs _ => False | _ => True end) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt)
         (fun r => ⌜r = F_RVC h⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Dro -∗
     swp (execute i) (fun e => ⌜e = resf⌝ ∗ R)) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (⌜st = Step_Execute (resf, zero_extend' 32 h)⌝ ∗ R)).
  Proof. Admitted.

  (* THE FETCH-FAILURE INSTANCE.  Nothing after the fetch runs: the model
     early-returns, so the caller owes no decode, no landing-pad fact and no
     execute -- only the fetch itself, landing on [F_Error]. *)
  Lemma swp_run_hart_active_fetch_fail (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (p : Privilege)
      (xv : mword 64) (e : ExceptionType) (R : iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt) (fun r => ⌜r = F_Error (e, xv)⌝ ∗ R)) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (⌜st = Step_Fetch_Failure (Virtaddr xv, e)⌝ ∗ R)).
  Proof. Admitted.

  (* ==================================================================== *)
  (* §4 THE CORE RULE AT USER, dispatch discharged.  [Qi] is BAKED (as in    *)
  (* [WpIntrCore.swp_run_hart_active_S]): the wire values are not known      *)
  (* until the dispatch has run, so the existential lives in the payload.    *)
  (* ==================================================================== *)
  Lemma swp_run_hart_active_U (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (dst : mstate)
      (Db : register -> bool) (mip_v mie_v mdv_v : mword 64)
      (Pe : ExecutionResult -> mword 32 -> iProp Σ)
      (Pf : mword 64 -> ExceptionType -> iProp Σ)
      (Px : ext_fetch_addr_error -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (mip : register) ∈ Drw ∪ Dro ->
    (mie : register) ∈ Drw ∪ Dro ->
    (mideleg : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = User ->
    register_lookup mip rs = mip_v ->
    register_lookup mie rs = mie_v ->
    register_lookup mideleg rs = mdv_v ->
    and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
    (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, Db r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    exec (currentlyEnabled Ext_S) dst = Some (true, dst) ->
    goodb Db (currentlyEnabled Ext_S) dst = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt) (run_fetch_post Drw Dro Df Pe Pf Px)) -∗
    swp (run_hart_active 0)
      (fun st => match st with
                 | Step_Pending_Interrupt (ii, pr) =>
                     ∃ meip seip : mword 1,
                       ⌜dispatch_of_pending
                          (s_pending mip_v meip seip mie_v mdv_v)
                        = Some (ii, pr)⌝ ∗
                       hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                 | Step_Execute (r, ib)            => Pe r ib
                 | Step_Fetch_Failure (Virtaddr xv, e) => Pf xv e
                 | Step_Ext_Fetch_Failure x        => Px x
                 | Step_Waiting _                  => False
                 end).
  Proof. Admitted.

End runfull.
