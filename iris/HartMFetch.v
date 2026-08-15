(* HartMFetch.v -- SEGMENT 2 of the M-mode cycle: from the post-chop monad
   [mseg2_start] to the instruction-fetch MemRead, assembled from the two
   sub-characterizations (HartMDispatch, HartMPmp) and the peel kit.

   THE LEAF-ATTACHMENT CONCLUSION (worklist 0d, the resolution): the
   landing is pinned to an UNEVALUATED WALKER APPLICATION,
       l.1 = (hrun_any_f 200 (register_set pmpcfg_n pmpcfg_boot rs)
                mseg2_start).2
   -- the unfootprinted walk at the caller's own pin file [rs], with ONE
   register forced concrete: pmpcfg is replaced by the all-OFF boot table,
   because at a merely-unlocked symbolic [pcfg] the walk's per-entry
   branches are stuck terms (the CHAIN's landing is still characterized at
   the caller's real pcfg -- the equality holds because the post-fetch
   continuation retains nothing the PMP loop read, which is exactly what
   the equality's proof verifies).  A leaf's functional cursors then start
   at [hread_resume w <that application>]: parametric in [pc] (and the
   other pins) through [rs], spelled, F8-safe, and reducible by the
   incantation + the same premise rewrites. *)
From Stdlib Require Import ZArith Zquot Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvExtras
        RiscvFetchExec HartLift HartRegNode HartSpan HartSpanChar HartMCycle
        HartMDispatch HartMPmp.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* the unfootprinted functional walker (the collector's stepper, promoted;  *)
(* HartPilot carries a probe-local copy -- consolidation there is owed)     *)
(* ---------------------------------------------------------------------- *)

Definition hsil_node_f (rs : regstate) (m : M unit)
    : option (regstate * M unit) :=
  match m with
  | Interface.Ret _ => None
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M unit) -> option (regstate * M unit) with
       | Interface.RegRead r _ => fun k => Some (rs, k (register_lookup r rs))
       | Interface.RegWrite r _ v => fun k => Some (register_set r v rs, k tt)
       | Interface.InstrAnnounce _   => fun k => Some (rs, k tt)
       | Interface.BranchAnnounce _ _=> fun k => Some (rs, k tt)
       | Interface.Barrier _         => fun k => Some (rs, k tt)
       | Interface.CacheOp _         => fun k => Some (rs, k tt)
       | Interface.TlbOp _           => fun k => Some (rs, k tt)
       | Interface.TakeException _   => fun k => Some (rs, k tt)
       | Interface.ReturnException _ => fun k => Some (rs, k tt)
       | Interface.TranslationStart _=> fun k => Some (rs, k tt)
       | Interface.TranslationEnd _  => fun k => Some (rs, k tt)
       | Interface.CycleCount        => fun k => Some (rs, k tt)
       | Interface.Message _         => fun k => Some (rs, k tt)
       | Interface.GetCycleCount     => fun k => Some (rs, k 0%Z)
       | _ => fun _ => None
       end) k
  end.

Fixpoint hrun_any_f (n : nat) (rs : regstate) (m : M unit)
    : regstate * M unit :=
  match n with
  | 0%nat => (rs, m)
  | S n' => match hsil_node_f rs m with
            | Some (rs', m') => hrun_any_f n' rs' m'
            | None => (rs, m)
            end
  end.

(* ---------------------------------------------------------------------- *)
(* the fetch request, as the model builds it (adjust the BODY if the       *)
(* model spells a field differently -- the pilot's concrete request is     *)
(* the reference)                                                          *)
(* ---------------------------------------------------------------------- *)
Definition mfetch_req (pc : SailStdpp.Values.mword 64)
    : Interface.ReadReq.t 4 :=
  {| Interface.ReadReq.pa := pc;
     Interface.ReadReq.access_kind :=
       SailStdpp.ConcurrencyInterfaceTypes.AK_explicit
         {| SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_variety
              := SailStdpp.ConcurrencyInterfaceTypes.AV_plain;
            SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_strength
              := SailStdpp.ConcurrencyInterfaceTypes.AS_normal |};
     Interface.ReadReq.va := None;
     Interface.ReadReq.translation := tt;
     Interface.ReadReq.tag := false |}.

(* ---------------------------------------------------------------------- *)
(* local helpers                                                           *)
(* ---------------------------------------------------------------------- *)

(* a RegRead head never stops a span (the classifier bridge, local copies
   exist in HartMCycle/HartMDispatch -- both Local there) *)
Local Lemma hregread_at_stops_false_local (Drw : gset register)
    (r : register) (m : M unit) :
  hregread_at r m = true -> hspan_stops Drw m = false.
Proof.
  destruct m as [y|T oc k]; simpl; [discriminate|].
  destruct oc; try discriminate; reflexivity.
Qed.

(* THE INCANTATION, fetch edition: HartMCycle's recipe with this segment's
   model functions whitelisted.  Everything value-carrying (dispatchInterrupt,
   pmpCheck, execute, currentlyEnabled, pmpMatchAddr, ...) stays FOLDED. *)
Local Ltac mf_red_in H :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR Defs.returnR
     Defs.read_reg Defs.write_reg Defs.early_return Defs.throw
     Defs.assert_exp ext_pre_step_hook should_inc_minstret Defs.and_boolM
     Defs.or_boolM andb orb negb not
     fetch get_config_rvfi ext_fetch_check_pc] in H.

(* peel ONE exposed read node whose value is unowned or value-dead
   (HartMPmp's tactic, copied) *)
Local Ltac mf_peel_any reg H Hstop v rsN HagN :=
  apply hspan_peel in H; [ | reflexivity | exact Hstop ];
  let c := fresh "c" in
  let Hstep := fresh "Hstep" in
  destruct H as (c & Hstep & H);
  let Hat := fresh "Hat" in
  match type of Hstep with
  | hspani _ _ (?m, _) _ =>
      assert (Hat : hregread_at reg m = true)
        by (cbn [hregread_at]; apply bool_decide_eq_true_2; reflexivity)
  end;
  destruct (hspani_read_any_inv _ _ reg _ _ _ Hat Hstep) as (v & rsN & HagN & ->);
  clear Hat Hstep;
  rewrite hregread_resume_red in H.

(* [currentlyEnabled Ext_S] as a read equation (HartMDispatch's
   mdisp_cE_S_eq_local, re-derived -- it is Local there) *)
Local Lemma mf_cE_S_eq_local :
  currentlyEnabled Ext_S
  = Defs.bind (Defs.read_reg misa)
      (fun w : SailStdpp.Values.mword 64 =>
         if eq_vec (_get_Misa_S w) (MachineWord.MachineWord.N_to_word 1 1%N)
         then returnM true else returnM false).
Proof. reflexivity. Qed.

(* [currentlyEnabled Ext_Ziccif] is a CONSTANT true (no read: hartSupports
   answers from the config) -- a pure conversion *)
Local Lemma mf_cE_Ziccif_eq_local : currentlyEnabled Ext_Ziccif = returnM true.
Proof. reflexivity. Qed.

(* the identity translation's address, at the spelling [translateAddr]'s
   Bare arm produces ([RiscvExtras.fetch_pa_id], restated unfolded so the
   rewrite matches the term) *)
Local Lemma mf_zext_pc_local (x : SailStdpp.Values.mword 64) :
  zero_extend' 64 (bits_of_virtaddr (Virtaddr x)) = x.
Proof. exact (fetch_pa_id x). Qed.

(* the 4-byte-fetch RAM class access, from [addr_is_ram] + 4-alignment
   (the arithmetic in a clean Z context -- lia is unusable next to a bv) *)
Local Lemma mf_fit4_local (x k : Z) :
  x = 4 * k -> x < 2147483648 + 134217728 -> x + 4 <= 2147483648 + 134217728.
Proof. intros -> H. lia. Qed.

Local Lemma mf_pma_access_local (a : SailStdpp.Values.mword 64) :
  addr_is_ram a -> is_aligned_paddr (Physaddr a) 4 = true ->
  pma_ram_access a 4.
Proof.
  intros [Hlo Hhi] Hal.
  unfold is_aligned_paddr in Hal. apply Z.eqb_eq in Hal.
  apply Zrem_divides in Hal. destruct Hal as [k Hk].
  unfold ram_base, ram_size in Hhi.
  unfold pma_ram_access, ram_base, ram_size.
  exact (conj (pma_width_ok 4 eq_refl eq_refl)
              (conj Hlo (mf_fit4_local (uint a) k Hk Hhi))).
Qed.

(* THE INCANTATION, pmp edition (HartMPmp's mpmp_red plus the wrapper
   names of this file's context) *)
Local Ltac mp_red_in H :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR Defs.returnR
     Defs.read_reg pmpReadAddrReg Defs.early_return Defs.throw
     sys_pmp_grain Z.geb Z.compare andb not negb pmpCheckRWX
     Defs.or_boolM] in H.

(* the per-entry PMP decision (HartMPmp's mpmp_matchaddr_pure_local,
   re-derived -- it is Local there): a one-grain-fit access answers
   NoMatch or full Match, whatever the entry and the address registers *)
Local Lemma mf_matchaddr_pure_local (pa : physaddr)
    (wbv : SailStdpp.Values.mword 64) (ent : SailStdpp.Values.mword 8)
    (paddr prev : SailStdpp.Values.mword 64) :
  uint (bits_of_physaddr pa) mod 4 + uint wbv <= 4 ->
  pmpMatchAddr pa wbv ent paddr prev = returnM PMP_NoMatch
  \/ pmpMatchAddr pa wbv ent paddr prev = returnM PMP_Match.
Proof.
  intros Hfit. destruct pa as [a]. cbn in Hfit.
  unfold pmpMatchAddr. cbn zeta.
  destruct (pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent)).
  - (* OFF *) left. reflexivity.
  - (* TOR *)
    destruct (zopz0zKzJ_u prev paddr).
    + left. reflexivity.
    + destruct (pmpRangeMatch_cell (Z.mul (uint prev) 4)
                  (Z.mul (uint paddr) 4) (uint a) (uint wbv)
                  (divide4_factor _) (divide4_factor _) Hfit)
        as [Hr|Hr]; [left|right]; rewrite Hr; reflexivity.
  - (* NA4 *)
    destruct (pmpRangeMatch_cell (Z.mul (uint paddr) 4)
                (Z.add (Z.mul (uint paddr) 4) 4) (uint a) (uint wbv)
                (divide4_factor _) (divide4_factor_plus _) Hfit)
      as [Hr|Hr]; [left|right]; rewrite Hr; reflexivity.
  - (* NAPOT *)
    destruct (pmpRangeMatch_cell
                (Z.mul (uint
                   (and_vec paddr (not_vec (xor_vec paddr (add_vec_int paddr 1))))) 4)
                (Z.mul (Z.add (Z.add (uint
                   (and_vec paddr (not_vec (xor_vec paddr (add_vec_int paddr 1)))))
                   (uint (xor_vec paddr (add_vec_int paddr 1)))) 1) 4)
                (uint a) (uint wbv)
                (divide4_factor _) (divide4_factor _) Hfit)
      as [Hr|Hr]; [left|right]; rewrite Hr; reflexivity.
Qed.

(* the CLINT window is strictly below RAM, at the spelling the reduced
   [within_clint] test carries (the arithmetic in a clean Z context) *)
Local Lemma mf_clint_gt_local (x : Z) : 2147483648 <= x -> 34340864 < x + 4.
Proof. lia. Qed.

Local Lemma mf_clint_false_local (a : SailStdpp.Values.mword 64) :
  addr_is_ram a ->
  andb (Z.leb (uint plat_clint_base) (uint a))
       (Z.leb (Z.add (uint a) (__id 4))
              (Z.add (uint plat_clint_base) (uint plat_clint_size)))
  = false.
Proof.
  intros [Hlo _]. unfold ram_base in Hlo.
  assert (Hsum : Z.add (uint plat_clint_base) (uint plat_clint_size)
                 = 34340864) by (vm_compute; reflexivity).
  rewrite Hsum. unfold __id.
  apply andb_false_intro2. apply Z.leb_gt.
  exact (mf_clint_gt_local (uint a) Hlo).
Qed.

(* a zero (boot) PMP entry never matches: its A-field decodes OFF -- the
   walk side's 16 entries all die through this single equation *)
Local Lemma mf_matchaddr_off_local (pa : physaddr)
    (wbv : SailStdpp.Values.mword 64)
    (paddr prev : SailStdpp.Values.mword 64) :
  pmpMatchAddr pa wbv (SailStdpp.Values.mword_of_int 0) paddr prev
  = returnM PMP_NoMatch.
Proof.
  destruct pa as [a].
  unfold pmpMatchAddr. cbn beta zeta.
  replace (pmpAddrMatchType_encdec_backwards
             (_get_Pmpcfg_ent_A (SailStdpp.Values.mword_of_int 0)))
    with OFF by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* the MemRead projection at an exposed node (the missing sibling of
   [hregwrite_val_at_red_local]; the [decide] does not cbn-reduce) *)
Local Lemma mf_hread_req_at_red_local (n : N) (req : Interface.ReadReq.t n)
    (K : (bv (8 * n) * option bool + Arch.abort)%type -> M unit) :
  hread_req_at n (Interface.Next (Interface.MemRead n req) K) = Some req.
Proof.
  simpl. destruct (decide (n = n)) as [Heq|Hne]; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel.
  reflexivity.
Qed.

(* stdpp flags the Z/Pos arithmetic [simpl never], which blocks cbn even
   through an explicit delta whitelist; the walk side's CLOSED index
   arithmetic (loop bounds, entry indices, offsets) needs them to compute,
   so lift the flag FILE-LOCALLY (Local: nothing leaks) *)
Local Arguments Z.sub _ _ : simpl nomatch.
Local Arguments Z.add _ _ : simpl nomatch.
Local Arguments Z.opp _ : simpl nomatch.
Local Arguments Z.mul _ _ : simpl nomatch.
Local Arguments Z.leb _ _ : simpl nomatch.
Local Arguments Z.gtb _ _ : simpl nomatch.
Local Arguments Z.eqb _ _ : simpl nomatch.
Local Arguments Z.compare _ _ : simpl nomatch.
Local Arguments Z.abs_nat _ : simpl nomatch.
Local Arguments Z.pos_sub _ _ : simpl nomatch.
Local Arguments Pos.to_nat _ : simpl nomatch.
Local Arguments Pos.add _ _ : simpl nomatch.
Local Arguments Pos.succ _ : simpl nomatch.
Local Arguments Pos.mul _ _ : simpl nomatch.
Local Arguments Pos.compare _ _ : simpl nomatch.
Local Arguments Pos.compare_cont _ _ _ : simpl nomatch.
Local Arguments Pos.pred_double _ : simpl nomatch.
Local Arguments Pos.iter_op {_} _ _ _ : simpl nomatch.
Local Arguments Nat.add _ _ : simpl nomatch.

(* THE INCANTATION, walk edition: everything the chain side unfolded, plus
   the walker's own stepper and the closed index arithmetic.  It runs on
   the GOAL, hence symmetrically on both sides of the equality. *)
Local Ltac mf_red_g :=
  cbn beta iota zeta delta
    [hrun_any_f hsil_node_f
     Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR Defs.returnR
     Defs.read_reg Defs.write_reg Defs.early_return Defs.throw
     Defs.assert_exp Defs.assert_exp' ext_pre_step_hook should_inc_minstret
     Defs.and_boolM Defs.or_boolM andb orb negb not
     fetch get_config_rvfi ext_fetch_check_pc
     run_hart_active fetch_bytes
     dispatchInterrupt getPendingSet read_mip external_interrupts_pending
     translateAddr effectivePrivilege translationMode is_shadow_stack_access
     mem_read mem_read_priv mem_read_priv_meta checked_mem_read
     check_pma_with_pmp_priority pmaCheck mag_pma_check
     is_mag_applicable_access split_misaligned misaligned_order
     read_kind_of_flags sys_misaligned_order_decreasing
     within_mmio_readable within_clint within_sig within_htif_readable
     within_htif_writable plat_have_clint plat_have_sig __id
     read_ram Defs.sail_mem_read
     Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
     Defs.foreach_ZM_up Defs.foreach_ZM_up'
     pmpCheck pmpReadAddrReg sys_pmp_grain sys_pmp_count pmpCheckRWX
     bits_of_physaddr Z.to_N
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_pa
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_access_kind
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_va
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_translation
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_tag
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_size
     Phys_Mem_Access_Info_splittable Phys_Mem_Access_Info_granule_size_exp
     Z.mul Z.leb Z.gtb Z.geb Z.eqb Z.compare Z.add Z.sub Z.opp Z.abs_nat
     Z.pos_sub Z.double Z.succ_double Z.pred_double
     Pos.compare Pos.compare_cont Pos.add Pos.succ Pos.mul Pos.pred_double
     Z.of_nat Pos.of_succ_nat Pos.to_nat Pos.iter_op Nat.add].


(* peel ONE exposed read node of a D-pinned register *)
Local Ltac mf_peel_D reg H Hstop HD rsN HagN :=
  apply hspan_peel in H; [ | reflexivity | exact Hstop ];
  let c := fresh "c" in
  let Hstep := fresh "Hstep" in
  destruct H as (c & Hstep & H);
  let Hat := fresh "Hat" in
  match type of Hstep with
  | hspani _ _ (?m, _) _ =>
      assert (Hat : hregread_at reg m = true)
        by (cbn [hregread_at]; apply bool_decide_eq_true_2; reflexivity)
  end;
  destruct (hspani_read_D_inv _ _ reg _ _ _ Hat HD Hstep) as (rsN & HagN & ->);
  clear Hat Hstep;
  rewrite hregread_resume_red in H.

(* the RUNNING-AGREEMENT variants: [Hag] is the single accumulated
   agreement of the current chain file against the PIN file [rs]; each
   step re-establishes it at the successor file under the SAME name, so
   no rewrite chain ever grows.  [mf_step_D] additionally injects the
   pinned value ([Hpin] : register_lookup reg rs = v). *)
Local Ltac mf_step_D reg HD Hpin Hag H Hstop :=
  let rsN := fresh "rsc" in
  let HagN := fresh "Hagc" in
  mf_peel_D reg H Hstop HD rsN HagN;
  rewrite (Hag _ HD) Hpin in H;
  let Hag' := fresh "Hagt" in
  match type of Hag with
  | reg_agree_on ?D0 _ ?rsP =>
      assert (Hag' : reg_agree_on D0 rsN rsP)
        by (let r := fresh "r" in let Hr := fresh "Hr" in
            intros r Hr; rewrite (HagN r Hr); exact (Hag r Hr))
  end;
  clear Hag HagN; rename Hag' into Hag.

Local Ltac mf_step_any reg v Hag H Hstop :=
  let rsN := fresh "rsc" in
  let HagN := fresh "Hagc" in
  mf_peel_any reg H Hstop v rsN HagN;
  let Hag' := fresh "Hagt" in
  match type of Hag with
  | reg_agree_on ?D0 _ ?rsP =>
      assert (Hag' : reg_agree_on D0 rsN rsP)
        by (let r := fresh "r" in let Hr := fresh "Hr" in
            intros r Hr; rewrite (HagN r Hr); exact (Hag r Hr))
  end;
  clear Hag HagN; rename Hag' into Hag.

(* ---------------------------------------------------------------------- *)
(* the segment characterization, K-GENERALIZED (worklist 0e): the whole    *)
(* tail continuation [KT] is abstract -- the tick's if-node sits beyond    *)
(* the fetch, so ONE proof serves both ticks; [mfetch_char] below is the   *)
(* tick=false instance                                                     *)
(* ---------------------------------------------------------------------- *)
Lemma mfetch_charK (KT : bool -> M unit)
    (D Drw : gset register) (rs rs0 : regstate)
    (l : M unit * regstate)
    (pc misa0 mstatus0 : SailStdpp.Values.mword 64)
    (pcfg : type_of_register pmpcfg_n) (pmar0 : list PMA_Region) :
  (hart_state : register) ∈ D ->
  (cur_privilege : register) ∈ D ->
  (misa : register) ∈ D ->
  (mstatus : register) ∈ D ->
  (pma_regions : register) ∈ D ->
  (pmpcfg_n : register) ∈ D ->
  (htif_tohost_base : register) ∈ D ->
  (R_bitvector_64 PC : register) ∈ D ->
  eq_vec (_get_Misa_S misa0)
    (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  eq_vec (_get_Mstatus_MIE mstatus0)
    (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
  eq_vec (_get_Mstatus_MPRV mstatus0)
    (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
  register_lookup hart_state rs = HART_ACTIVE tt ->
  register_lookup cur_privilege rs = Machine ->
  register_lookup misa rs = misa0 ->
  register_lookup mstatus rs = mstatus0 ->
  register_lookup pma_regions rs = pmar0 ->
  register_lookup pmpcfg_n rs = pcfg ->
  register_lookup htif_tohost_base rs = None ->
  register_lookup (R_bitvector_64 PC) rs = pc ->
  (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
  is_aligned_vaddr (Virtaddr pc) 4 = true ->
  is_aligned_paddr (Physaddr pc) 4 = true ->
  pma_allows_ram pmar0 ->
  addr_is_ram pc ->
  reg_agree_on D rs0 rs ->
  hspan D Drw (mseg2_startK KT, rs0) l ->
  hspan_stops Drw l.1 = true ->
  l.1 = (hrun_any_f 200 (register_set pmpcfg_n pmpcfg_boot rs)
           (mseg2_startK KT)).2
  /\ hread_req_at 4 l.1 = Some (mfetch_req pc)
  /\ reg_agree_on D l.2 rs.
Proof.
  intros HD1 HD2 HD3 HD4 HD5 HD6 HD7 HD8 HmisaS HmIE Hmprv
    Hhart Hpriv Hmisa Hmst Hpma Hpcfg Hhtif Hpc Hunlock Hva Hpa
    Hpallow Hram Hag0 Hchain Hstop.
  (* reduce mseg2_startK's spine in the chain hypothesis (the
     mseg1_resume_set_local script, replayed in H; KT stays opaque) *)
  unfold mseg2_startK, mwrap, try_step in Hchain.
  mf_red_in Hchain.
  rewrite !hregread_resume_red in Hchain.
  mf_red_in Hchain.
  rewrite mseg1_mc1_ir in Hchain.
  cbn beta iota zeta delta
    [hregwrite_resume Defs.bind Defs.bind0 Interface.iMon_bind
     returnM Defs.returnm] in Hchain.
  rename Hag0 into Hag.
  (* peel 1: hart_state (D-pinned, HART_ACTIVE) *)
  mf_step_D hart_state HD1 Hhart Hag Hchain Hstop.
  cbn beta iota zeta delta
    [run_hart_active Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR
     Defs.try_catch Defs.catch_early_return Defs.returnm returnM returnR
     Defs.read_reg] in Hchain.
  (* peel 2: cur_privilege (D-pinned, Machine) *)
  mf_step_D cur_privilege HD2 Hpriv Hag Hchain Hstop.
  mf_red_in Hchain.
  (* -------------------------------------------------------------------- *)
  (* the dispatch stretch, replayed inline on the WRAPPED term (the
     [liftR]/[catch_early_return] wrappers around [dispatchInterrupt] are
     stuck fixpoint applications, so no syntactic [iMon_bind _ K] seam
     exists and [mdispatch_span_char] cannot be applied; its nine peels
     replay verbatim here)                                                 *)
  (* -------------------------------------------------------------------- *)
  unfold dispatchInterrupt, getPendingSet, read_mip,
    external_interrupts_pending in Hchain.
  rewrite !mf_cE_S_eq_local in Hchain.
  mf_red_in Hchain.
  change (Instances.generic_eq Machine Machine) with true in Hchain;
  change (Instances.generic_eq Machine Supervisor) with false in Hchain;
  change (Instances.generic_eq Machine User) with false in Hchain.
  mf_red_in Hchain.
  (* peel 3: misa (D-pinned); the S bit resolves the mideleg branch *)
  mf_step_D misa HD3 Hmisa Hag Hchain Hstop.
  rewrite HmisaS in Hchain. mf_red_in Hchain.
  (* peel 4-6: mideleg, mip, sig_meip (all unownable, ∀) *)
  mf_step_any mideleg dm Hag Hchain Hstop. mf_red_in Hchain.
  mf_step_any mip pm Hag Hchain Hstop. mf_red_in Hchain.
  mf_step_any sig_meip me Hag Hchain Hstop. mf_red_in Hchain.
  (* peel 7: the second misa read (D-pinned) *)
  mf_step_D misa HD3 Hmisa Hag Hchain Hstop.
  rewrite HmisaS in Hchain. mf_red_in Hchain.
  (* peel 8-10: sig_seip, mie, mie (∀) *)
  mf_step_any sig_seip se Hag Hchain Hstop. mf_red_in Hchain.
  mf_step_any mie e1 Hag Hchain Hstop. mf_red_in Hchain.
  mf_step_any mie e2 Hag Hchain Hstop. mf_red_in Hchain.
  (* peel 11: mstatus (D-pinned); MIE clear collapses the dispatch *)
  mf_step_D mstatus HD4 Hmst Hag Hchain Hstop.
  rewrite HmIE in Hchain. mf_red_in Hchain.
  (* -------------------------------------------------------------------- *)
  (* the fetch prelude: PC reads (all D-pinned to [pc]), the alignment
     branches, Ziccif                                                      *)
  (* -------------------------------------------------------------------- *)
  destruct (align4_low_bits pc Hva) as [Hbit0 Hbit1].
  (* peel 12-13: the two PC reads feeding ext_fetch_check_pc *)
  mf_step_any (R_bitvector_64 PC) pcv1 Hag Hchain Hstop. mf_red_in Hchain.
  mf_step_any (R_bitvector_64 PC) pcv2 Hag Hchain Hstop. mf_red_in Hchain.
  (* peel 14: the bit-0 alignment PC read (D-pinned, resolved by Hbit0) *)
  mf_step_D (R_bitvector_64 PC) HD8 Hpc Hag Hchain Hstop.
  rewrite Hbit0 in Hchain. mf_red_in Hchain.
  (* peel 15: the bit-1 alignment PC read (D-pinned, resolved by Hbit1) *)
  mf_step_D (R_bitvector_64 PC) HD8 Hpc Hag Hchain Hstop.
  rewrite Hbit1 in Hchain. mf_red_in Hchain.
  (* peel 16: the is_aligned_vaddr PC read; then Ziccif is a constant true *)
  mf_step_D (R_bitvector_64 PC) HD8 Hpc Hag Hchain Hstop.
  rewrite Hva in Hchain. mf_red_in Hchain.
  rewrite mf_cE_Ziccif_eq_local in Hchain. mf_red_in Hchain.
  (* peel 17-18: fetch_start (dead) and granule_start (pc) for fetch_bytes *)
  mf_step_any (R_bitvector_64 PC) pcv3 Hag Hchain Hstop. mf_red_in Hchain.
  mf_step_D (R_bitvector_64 PC) HD8 Hpc Hag Hchain Hstop.
  cbn beta iota zeta delta
    [fetch_bytes Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR
     Defs.try_catch Defs.catch_early_return Defs.returnm returnM returnR
     Defs.returnR Defs.read_reg Defs.early_return Defs.throw
     ext_fetch_check_pc] in Hchain.
  (* -------------------------------------------------------------------- *)
  (* translateAddr at Machine: identity translation                        *)
  (* -------------------------------------------------------------------- *)
  unfold translateAddr in Hchain. mf_red_in Hchain.
  (* peel 19: the mstatus read (value dead for a fetch: MPRV is not
     consulted) *)
  mf_step_any mstatus mst1 Hag Hchain Hstop. mf_red_in Hchain.
  (* peel 20: cur_privilege (D-pinned, Machine) *)
  mf_step_D cur_privilege HD2 Hpriv Hag Hchain Hstop.
  (* the effective privilege of a fetch is the current privilege *)
  unfold effectivePrivilege in Hchain.
  change (Instances.generic_neq (InstructionFetch tt) (InstructionFetch tt))
    with false in Hchain.
  mf_red_in Hchain.
  unfold translationMode in Hchain.
  change (Instances.generic_eq Machine Machine) with true in Hchain.
  mf_red_in Hchain.
  unfold is_shadow_stack_access in Hchain.
  mf_red_in Hchain.
  change (Instances.generic_eq Bare Bare) with true in Hchain.
  mf_red_in Hchain.
  rewrite mf_zext_pc_local in Hchain.
  mf_red_in Hchain.
  (* -------------------------------------------------------------------- *)
  (* mem_read -> checked_mem_read -> pmaCheck (the pma stretch)            *)
  (* -------------------------------------------------------------------- *)
  unfold mem_read in Hchain. mf_red_in Hchain.
  (* peel 21: mstatus (dead), peel 22: cur_privilege (Machine) *)
  mf_step_any mstatus mst2 Hag Hchain Hstop. mf_red_in Hchain.
  mf_step_D cur_privilege HD2 Hpriv Hag Hchain Hstop.
  unfold effectivePrivilege in Hchain.
  change (Instances.generic_neq (InstructionFetch tt) (InstructionFetch tt))
    with false in Hchain.
  mf_red_in Hchain.
  unfold mem_read_priv, mem_read_priv_meta, checked_mem_read,
    check_pma_with_pmp_priority, pmaCheck in Hchain.
  mf_red_in Hchain.
  (* peel 23: pma_regions (D-pinned to pmar0) *)
  mf_step_D pma_regions HD5 Hpma Hag Hchain Hstop.
  (* the PURE region match: the RAM class premise supplies the ∃-region *)
  destruct (Hpallow pc 4 (mf_pma_access_local pc Hram Hpa))
    as (region & Hmatch & Hgrant).
  destruct region as [rbase rsize rattr rdtree].
  destruct Hgrant as (Hx & _).
  cbn [PMA_Region_attributes] in Hx.
  rewrite Hmatch in Hchain. mf_red_in Hchain.
  (* the executable grant resolves the canAccess branch *)
  rewrite Hx in Hchain. mf_red_in Hchain.
  (* mag_pma_check: an aligned fetch answers CannotSplit *)
  unfold mag_pma_check, is_mag_applicable_access in Hchain.
  mf_red_in Hchain.
  rewrite Hpa in Hchain. mf_red_in Hchain.
  cbn [Phys_Mem_Access_Info_splittable
       Phys_Mem_Access_Info_granule_size_exp] in Hchain.
  (* split_misaligned: CannotSplit does not split *)
  unfold split_misaligned in Hchain.
  change (Instances.generic_eq CannotSplit CannotSplit) with true in Hchain.
  mf_red_in Hchain.
  unfold misaligned_order, read_kind_of_flags in Hchain.
  cbn beta iota zeta delta
    [sys_misaligned_order_decreasing Defs.bind Defs.bind0
     Interface.iMon_bind Defs.liftR Defs.try_catch Defs.catch_early_return
     Defs.returnm returnM returnR Defs.returnR] in Hchain.
  (* the one-iteration split loop: fuel 1, offset 0 *)
  unfold Defs.untilMT in Hchain.
  cbn beta iota zeta delta
    [Defs.untilMT' Defs.Zwf_guarded Defs.bind Defs.bind0
     Interface.iMon_bind Defs.liftR Defs.try_catch Defs.catch_early_return
     Defs.returnm returnM returnR Defs.returnR Defs.assert_exp'
     bits_of_physaddr Z.mul] in Hchain.
  (* resolve the termination guard by COMPUTATION (a canonical closed
     proof, identical on the chain and walk sides -- a [destruct] would
     bake an un-replayable context variable into the landing term) *)
  let v := eval vm_compute in (Z_ge_dec 1 0) in
    change (Z_ge_dec 1 0) with v in Hchain.
  mf_red_in Hchain.
  cbn beta iota zeta delta
    [Defs.assert_exp' bits_of_physaddr Z.mul Defs.bind Defs.bind0
     Interface.iMon_bind Defs.liftR Defs.try_catch Defs.catch_early_return
     Defs.returnm returnM returnR Defs.returnR] in Hchain.
  rewrite !avi0 in Hchain.
  (* -------------------------------------------------------------------- *)
  (* the PMP stretch, replayed on the wrapped term (HartMPmp's loop
     induction; [mpmp_span_char_ifetch4] itself is out of reach for the
     same wrapper reason as the dispatch)                                  *)
  (* -------------------------------------------------------------------- *)
  (* the one-grain fit, exactly as the exec ifetch4 corollary derived it *)
  assert (Hfit : uint pc mod 4 + uint (to_bits 64 4) <= 4).
  { pose proof Hpa as HH. unfold is_aligned_paddr in HH.
    apply Z.eqb_eq in HH. apply Zrem_divides in HH.
    destruct HH as [k Hk].
    replace (uint (to_bits 64 4)) with 4 by (vm_compute; reflexivity).
    rewrite Hk. replace (4 * k) with (k * 4) by lia.
    rewrite Z_mod_mult. lia. }
  (* normalize the checker to the fueled loop under its handler *)
  unfold pmpCheck in Hchain.
  replace (Z.eqb sys_pmp_count 0) with false in Hchain
    by (vm_compute; reflexivity).
  replace (Z.sub sys_pmp_count 1) with 15 in Hchain
    by (vm_compute; reflexivity).
  unfold Defs.foreach_ZM_up in Hchain.
  replace (S (Z.abs_nat (Z.sub 0 15))) with 16%nat in Hchain
    by (vm_compute; reflexivity).
  mp_red_in Hchain.
  (* the after-loop default is the M-mode allow *)
  change (Instances.generic_eq Machine Machine) with true in Hchain.
  mp_red_in Hchain.
  (* the loop invariant, generic in the fuel and start index; the body [B],
     the after-loop default [AF] and the WRAPPED CONTEXT [F] are captured
     from the hypothesis *)
  match type of Hchain with
  | hspan _ _ (?S, _) _ =>
    match S with
    | context [ Defs.bind0 (Defs.foreach_ZM_up' 0 15 1 16%nat tt ?B) ?AF ] =>
      let tgt := constr:(Defs.catch_early_return
                    (Defs.bind0 (Defs.foreach_ZM_up' 0 15 1 16%nat tt B) AF)) in
      let pat := eval pattern tgt in S in
      match pat with
      | ?F _ =>
        assert (HLOOP : forall (n : nat) (from : Z) (rs0' : regstate)
                               (l' : M unit * regstate),
          reg_agree_on D rs0' rs ->
          hspan D Drw
            (F (Defs.catch_early_return
                  (Defs.bind0 (Defs.foreach_ZM_up' from 15 1 n tt B) AF)),
             rs0') l' ->
          hspan_stops Drw l'.1 = true ->
          exists rs1, reg_agree_on D rs1 rs /\
            hspan D Drw
              (F (Defs.returnm (None : option ExceptionType)), rs1) l')
      end
    end
  end.
  { intro n; induction n as [|n IH]; intros from rs0' l' Hagl Hch Hstop'.
    - (* fuel exhausted: the residual is the default allow *)
      cbn [Defs.foreach_ZM_up'] in Hch.
      destruct (Z.leb from 15) eqn:Hle; mp_red_in Hch;
        match type of Hch with
        | hspan _ _ (_, ?c) _ =>
            exists c; split; [exact Hagl|exact Hch]
        end.
    - cbn [Defs.foreach_ZM_up'] in Hch.
      destruct (Z.leb from 15) eqn:Hle.
      2: { (* index past the last entry: default allow *)
        mp_red_in Hch.
        match type of Hch with
        | hspan _ _ (_, ?c) _ =>
            exists c; split; [exact Hagl|exact Hch]
        end. }
      destruct (Z.gtb from 0) eqn:Hgt; mp_red_in Hch.
      + (* i > 0: prev-entry pmpcfg + pmpaddr, then cfg, entry cfg + addr *)
        mf_step_any pmpcfg_n w1 Hagl Hch Hstop'. mp_red_in Hch.
        mf_step_any pmpaddr_n v1 Hagl Hch Hstop'. mp_red_in Hch.
        mf_step_D pmpcfg_n HD6 Hpcfg Hagl Hch Hstop'. mp_red_in Hch.
        mf_step_any pmpcfg_n w4 Hagl Hch Hstop'. mp_red_in Hch.
        mf_step_any pmpaddr_n v2 Hagl Hch Hstop'. mp_red_in Hch.
        match type of Hch with
        | context [ pmpMatchAddr ?PA ?W ?ENT ?PD ?PV ] =>
            destruct (mf_matchaddr_pure_local PA W ENT PD PV Hfit) as [Hm|Hm]
        end; rewrite Hm in Hch; mp_red_in Hch.
        * (* NoMatch: the next entry *)
          exact (IH (Z.add from 1) _ l' Hagl Hch Hstop').
        * (* Match: Machine + unlocked allows, early return *)
          rewrite (Hunlock from) in Hch.
          change (Instances.generic_eq Machine Machine) with true in Hch.
          match type of Hch with
          | context [ eq_vec (_get_Pmpcfg_ent_X ?E) ?ONE ] =>
              destruct (eq_vec (_get_Pmpcfg_ent_X E) ONE) eqn:HX
          end; mp_red_in Hch;
            match type of Hch with
            | hspan _ _ (_, ?c) _ =>
                exists c; split; [exact Hagl|exact Hch]
            end.
      + (* i = 0: no previous entry; cfg, then entry pmpcfg + pmpaddr *)
        mf_step_D pmpcfg_n HD6 Hpcfg Hagl Hch Hstop'. mp_red_in Hch.
        mf_step_any pmpcfg_n w4 Hagl Hch Hstop'. mp_red_in Hch.
        mf_step_any pmpaddr_n v2 Hagl Hch Hstop'. mp_red_in Hch.
        match type of Hch with
        | context [ pmpMatchAddr ?PA ?W ?ENT ?PD ?PV ] =>
            destruct (mf_matchaddr_pure_local PA W ENT PD PV Hfit) as [Hm|Hm]
        end; rewrite Hm in Hch; mp_red_in Hch.
        * exact (IH (Z.add from 1) _ l' Hagl Hch Hstop').
        * rewrite (Hunlock from) in Hch.
          change (Instances.generic_eq Machine Machine) with true in Hch.
          match type of Hch with
          | context [ eq_vec (_get_Pmpcfg_ent_X ?E) ?ONE ] =>
              destruct (eq_vec (_get_Pmpcfg_ent_X E) ONE) eqn:HX
          end; mp_red_in Hch;
            match type of Hch with
            | hspan _ _ (_, ?c) _ =>
                exists c; split; [exact Hagl|exact Hch]
            end.
  }
  destruct (HLOOP 16%nat 0 _ l Hag Hchain Hstop) as (rsP & HagP & HchainP).
  clear Hchain Hag HLOOP.
  rename HchainP into Hchain. rename HagP into Hag.
  mp_red_in Hchain.
  (* -------------------------------------------------------------------- *)
  (* the MMIO gate: clint/sig windows are below RAM, htif is D-pinned None *)
  (* -------------------------------------------------------------------- *)
  unfold within_mmio_readable, within_clint, within_sig,
    within_htif_readable, within_htif_writable in Hchain.
  cbn beta iota zeta delta
    [get_config_rvfi plat_have_clint plat_have_sig __id not negb
     Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.returnm returnM returnR Defs.returnR Defs.read_reg
     Defs.or_boolM Defs.and_boolM] in Hchain.
  rewrite (mf_clint_false_local pc Hram) in Hchain.
  mf_red_in Hchain.
  (* peel: htif_tohost_base (D-pinned None); the tohost branch dies *)
  mf_step_D htif_tohost_base HD7 Hhtif Hag Hchain Hstop.
  mf_red_in Hchain.
  (* -------------------------------------------------------------------- *)
  (* the RAM read: land on the MemRead node                                *)
  (* -------------------------------------------------------------------- *)
  unfold read_ram, Defs.sail_mem_read in Hchain.
  mf_red_in Hchain.
  cbn beta iota zeta delta
    [Z.to_N SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_pa
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_access_kind
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_va
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_translation
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_tag
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_size
     Defs.bind Defs.bind0 Interface.iMon_bind
     Defs.liftR Defs.try_catch Defs.returnm returnM returnR
     Defs.returnR] in Hchain.
  (* -------------------------------------------------------------------- *)
  (* the landing: a MemRead head stops the span                            *)
  (* -------------------------------------------------------------------- *)
  apply hspan_stop_refl in Hchain; [ | reflexivity ].
  rewrite Hchain. cbn [fst snd].
  (* the walk-side value pins, restated at the walk file's spelling (each
     is the corresponding premise up to CONVERSION: pmpcfg_n lives in a
     different register group than every pinned register) *)
  assert (Whart : register_lookup hart_state
            (register_set pmpcfg_n pmpcfg_boot rs) = HART_ACTIVE tt)
    by (rewrite (irrelevant_register_set hart_state pmpcfg_n rs pmpcfg_boot
                   eq_refl); exact Hhart).
  assert (Wpriv : register_lookup cur_privilege
            (register_set pmpcfg_n pmpcfg_boot rs) = Machine)
    by (rewrite (irrelevant_register_set cur_privilege pmpcfg_n rs
                   pmpcfg_boot eq_refl); exact Hpriv).
  assert (Wmisa : register_lookup misa
            (register_set pmpcfg_n pmpcfg_boot rs) = misa0)
    by (rewrite (irrelevant_register_set misa pmpcfg_n rs pmpcfg_boot
                   eq_refl); exact Hmisa).
  assert (Wmst : register_lookup mstatus
            (register_set pmpcfg_n pmpcfg_boot rs) = mstatus0)
    by (rewrite (irrelevant_register_set mstatus pmpcfg_n rs pmpcfg_boot
                   eq_refl); exact Hmst).
  assert (Wpma : register_lookup pma_regions
            (register_set pmpcfg_n pmpcfg_boot rs) = pmar0)
    by (rewrite (irrelevant_register_set pma_regions pmpcfg_n rs pmpcfg_boot
                   eq_refl); exact Hpma).
  assert (Whtif : register_lookup htif_tohost_base
            (register_set pmpcfg_n pmpcfg_boot rs) = None)
    by (rewrite (irrelevant_register_set htif_tohost_base pmpcfg_n rs
                   pmpcfg_boot eq_refl); exact Hhtif).
  assert (Wpc : register_lookup (R_bitvector_64 PC)
            (register_set pmpcfg_n pmpcfg_boot rs) = pc)
    by (rewrite (irrelevant_register_set (R_bitvector_64 PC) pmpcfg_n rs
                   pmpcfg_boot eq_refl); exact Hpc).
  split; [ | split; [ exact (mf_hread_req_at_red_local 4 _ _) | exact Hag ] ].
  (* -------------------------------------------------------------------- *)
  (* conclusion 1: THE WALK.  Reduce the walker application by the same
     staged rewrites; the landing is already normal for every constant the
     incantation opens, so the passes are symmetric and reflexivity closes
     the equality.  QED-COST SHAPE: the reduction runs under
     [etransitivity] against an evar, so none of its ~60 rewrite motives
     spells the giant landing (each eq_ind motive would otherwise carry
     both sides of the equality, and the kernel's Qed walks are linear in
     tree OCCURRENCES); the landing enters exactly one term -- the final
     reflexivity between the two reduced forms.                            *)
  (* -------------------------------------------------------------------- *)
  symmetry. etransitivity.
  { unfold mseg2_startK, mwrap, try_step.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind ext_pre_step_hook
     should_inc_minstret Defs.and_boolM Defs.read_reg Defs.write_reg
     returnM Defs.returnm].
  rewrite !hregread_resume_red.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind returnM Defs.returnm].
  rewrite mseg1_mc1_ir.
  cbn beta iota zeta delta
    [hregwrite_resume Defs.bind Defs.bind0 Interface.iMon_bind
     returnM Defs.returnm].
  (* the walker: hart_state, then the dispatch stretch *)
  mf_red_g. rewrite Whart.
  mf_red_g. rewrite Wpriv.
  unfold dispatchInterrupt, getPendingSet, read_mip,
    external_interrupts_pending.
  rewrite !mf_cE_S_eq_local.
  mf_red_g.
  change (Instances.generic_eq Machine Machine) with true.
  change (Instances.generic_eq Machine Supervisor) with false.
  change (Instances.generic_eq Machine User) with false.
  mf_red_g. rewrite Wmisa. rewrite HmisaS.
  mf_red_g. rewrite Wmisa. rewrite HmisaS.
  mf_red_g. rewrite Wmst. rewrite HmIE.
  (* the fetch prelude *)
  mf_red_g. rewrite Wpc. rewrite Hbit0.
  mf_red_g. rewrite Wpc. rewrite Hbit1.
  mf_red_g. rewrite Wpc. rewrite Hva.
  rewrite mf_cE_Ziccif_eq_local.
  mf_red_g. rewrite Wpc.
  (* translateAddr: effective privilege, Bare mode, identity address *)
  unfold effectivePrivilege, translationMode.
  change (Instances.generic_neq (InstructionFetch tt) (InstructionFetch tt))
    with false.
  mf_red_g.
  rewrite Wpriv.
  change (Instances.generic_eq Machine Machine) with true.
  mf_red_g.
  change (Instances.generic_eq Bare Bare) with true.
  mf_red_g. rewrite mf_zext_pc_local.
  (* mem_read: the second effective privilege *)
  mf_red_g. rewrite Wpriv.
  mf_red_g.
  (* the pma stretch *)
  rewrite Wpma. rewrite Hmatch.
  mf_red_g. rewrite Hx.
  mf_red_g. rewrite Hpa.
  mf_red_g.
  change (Instances.generic_eq CannotSplit CannotSplit) with true.
  mf_red_g.
  (* the split loop's termination guard, by the same canonical value *)
  let v := eval vm_compute in (Z_ge_dec 1 0) in
    change (Z_ge_dec 1 0) with v.
  mf_red_g.
  rewrite !avi0.
  (* the PMP walk: all 16 boot entries are OFF, each dies by computation *)
  do 16 (try rewrite !register_lookup_set;
         try rewrite !pmpcfg_boot_entry;
         try rewrite !mf_matchaddr_off_local;
         mf_red_g).
  change (Instances.generic_eq Machine Machine) with true.
  mf_red_g.
  (* the MMIO gate and the htif window *)
  rewrite (mf_clint_false_local pc Hram).
  mf_red_g.
  rewrite Whtif.
  mf_red_g.
  reflexivity. }
  reflexivity.
Qed.

(* the ORIGINAL statement, re-proven as the tick=false instance:
   transport the hspan premise and the walker conclusion with
   [mseg2_start_as_K] *)
Lemma mfetch_char (D Drw : gset register) (rs rs0 : regstate)
    (l : M unit * regstate)
    (pc misa0 mstatus0 : SailStdpp.Values.mword 64)
    (pcfg : type_of_register pmpcfg_n) (pmar0 : list PMA_Region) :
  (hart_state : register) ∈ D ->
  (cur_privilege : register) ∈ D ->
  (misa : register) ∈ D ->
  (mstatus : register) ∈ D ->
  (pma_regions : register) ∈ D ->
  (pmpcfg_n : register) ∈ D ->
  (htif_tohost_base : register) ∈ D ->
  (R_bitvector_64 PC : register) ∈ D ->
  eq_vec (_get_Misa_S misa0)
    (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  eq_vec (_get_Mstatus_MIE mstatus0)
    (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
  eq_vec (_get_Mstatus_MPRV mstatus0)
    (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
  register_lookup hart_state rs = HART_ACTIVE tt ->
  register_lookup cur_privilege rs = Machine ->
  register_lookup misa rs = misa0 ->
  register_lookup mstatus rs = mstatus0 ->
  register_lookup pma_regions rs = pmar0 ->
  register_lookup pmpcfg_n rs = pcfg ->
  register_lookup htif_tohost_base rs = None ->
  register_lookup (R_bitvector_64 PC) rs = pc ->
  (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
  is_aligned_vaddr (Virtaddr pc) 4 = true ->
  is_aligned_paddr (Physaddr pc) 4 = true ->
  pma_allows_ram pmar0 ->
  addr_is_ram pc ->
  reg_agree_on D rs0 rs ->
  hspan D Drw (mseg2_start, rs0) l ->
  hspan_stops Drw l.1 = true ->
  l.1 = (hrun_any_f 200 (register_set pmpcfg_n pmpcfg_boot rs)
           mseg2_start).2
  /\ hread_req_at 4 l.1 = Some (mfetch_req pc)
  /\ reg_agree_on D l.2 rs.
Proof.
  intros HD1 HD2 HD3 HD4 HD5 HD6 HD7 HD8 HmisaS HmIE Hmprv
    Hhart Hpriv Hmisa Hmst Hpma Hpcfg Hhtif Hpc Hunlock Hva Hpa
    Hpallow Hram Hag0 Hchain Hstop.
  rewrite mseg2_start_as_K in Hchain.
  destruct (mfetch_charK _ D Drw rs rs0 l pc misa0 mstatus0 pcfg pmar0
              HD1 HD2 HD3 HD4 HD5 HD6 HD7 HD8 HmisaS HmIE Hmprv
              Hhart Hpriv Hmisa Hmst Hpma Hpcfg Hhtif Hpc Hunlock Hva Hpa
              Hpallow Hram Hag0 Hchain Hstop) as (H1 & H2 & H3).
  rewrite <- mseg2_start_as_K in H1.
  exact (conj H1 (conj H2 H3)).
Qed.
