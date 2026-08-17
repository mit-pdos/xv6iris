(* HartMFetch.v -- the fetch path, one [swp] fact per model function.

   [fetch] is decomposed along its OWN structure: a [catch_early_return]
   region whose body binds [liftR sub] for each call it makes.  The walk is
   uniform and mechanical:

     - peel a call with [swp_use_cer{,2,3}] (the depth is how many
       MR-level binds sit between the [liftR] and the handler; matching is
       first-order, so the former is never guessed);
     - clear the glue with the REWRITE equations [mbind_ret], [mbind0_ret],
       [mliftR_ret], [mcer_ret] -- never with a cbn wide enough to unfold
       [Defs.bind], which re-spells the goal as [Interface.iMon_bind] and
       breaks every match downstream;
     - unfold [Defs.and_boolM] / [Defs.or_boolM] with [unfold], not [cbn]
       (cbn declines: unfolding them exposes no iota redex);
     - resolve each test from a premise by [rewrite].

   WHAT THE 4-ALIGNED M-MODE PATH ACTUALLY TOUCHES: five PC reads (the two
   feeding [ext_fetch_check_pc], the two misalignment bit tests, the
   4-alignment test) plus two more feeding [fetch_bytes].  [Ext_Zca] is
   never read -- with bit 1 clear the [and_boolM] short-circuits before it
   -- and [Ext_Ziccif] is a constant true from the config, no read at all.

   THE OTHER TOOL, and the judgement the walk turns on: [hfrun] DOES NOT
   CARE about [catch_early_return].  It walks nodes, and the term structure
   reduces out of the way -- so any maximal stretch whose reads are all
   pinned and which contains NO memory event gets a two-line proof no
   matter how it is wrapped.  [translateAddr] at Bare is the case in point:
   the whole page-translation function, ten lines, 2 s.  The same goes for
   [check_pma_with_pmp_priority] and [within_mmio_readable].

   THE LOOP.  [checked_mem_read]'s [untilMT] recurses on an [Acc (Zwf 0)]
   built by [Zwf_guarded], so a step is a CONVERSION, not an iota -- but it
   is one cbn away all the same, with [Defs.untilMT'] and
   [Defs.Zwf_guarded] whitelisted and stdpp's [simpl never] flags on the Z
   arithmetic lifted file-locally.  No induction is needed: for an aligned
   4-byte fetch [split_misaligned] answers N = 1, so the loop runs once and
   the residual sits in a dead branch.

   [swp_fetch_ram] is the whole thing, with NO obligation but the memory
   one -- which is the leaf's job and nobody else's, since the leaf is what
   owns the text bytes. *)
From Stdlib Require Import ZArith Zquot Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar HartEvents HartMPmp.
Require Import RiscvTryStep RiscvExtras RiscvFetchExec.
Local Open Scope Z_scope.

Local Notation zerobit :=
  (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 1)
     (BinaryString.Raw.to_N "0" 0%N)).

(* [currentlyEnabled Ext_Ziccif] is a CONSTANT true (no read: hartSupports
   answers from the config) -- a pure conversion *)
Local Lemma mf_cE_Ziccif_eq_local : currentlyEnabled Ext_Ziccif = returnM true.
Proof. reflexivity. Qed.

(* THE 2-mod-4 PATH'S EXTRA READ.  The 4-aligned fetch never evaluates
   [Ext_Zca] -- with PC bit 1 clear the misalignment [and_boolM]
   short-circuits before it -- but with bit 1 SET the model does reach the
   probe, so that path needs the read equation and a pinned misa.C. *)
Lemma mf_cE_Zca_eq_local :
  currentlyEnabled Ext_Zca
  = Defs.bind (Defs.read_reg misa)
      (fun v : SailStdpp.Values.mword 64 =>
         if eq_vec (_get_Misa_C v) (MachineWord.MachineWord.N_to_word 1 1%N)
         then returnM true else returnM false).
Proof. reflexivity. Qed.



Local Ltac mf_glue :=
  cbn beta iota zeta delta [get_config_rvfi ext_fetch_check_pc].

Local Ltac tr_cbn :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR Defs.returnR
     Defs.read_reg Defs.early_return Defs.throw Defs.and_boolM Defs.or_boolM
     andb orb negb not].

Local Ltac tr_read :=
  rewrite hfrun_read;
  match goal with
  | |- context [ bool_decide ?P ] =>
      rewrite (bool_decide_eq_true_2 P ltac:(assumption))
  end.

(* the identity translation's address, at the spelling [translateAddr]'s
   Bare arm produces *)
Local Lemma zext_pc_id (x : SailStdpp.Values.mword 64) :
  zero_extend' 64 (bits_of_virtaddr (Virtaddr x)) = x.
Proof. exact (fetch_pa_id x). Qed.

(* GENERIC IN THE ACCESS.  The Bare-mode translation is access-agnostic;
   the access enters in exactly two places, and each is a one-line premise
   the caller discharges -- so the fetch and the store share this walk
   rather than owning a copy each. *)
Lemma hfrun_translateAddr_M (D Drw : gset register) (rs : regstate)
    (pc : SailStdpp.Values.mword 64)
    (acc : MemoryAccessType mem_payload) :
  (mstatus : register) ∈ D ->
  (cur_privilege : register) ∈ D ->
  register_lookup cur_privilege rs = Machine ->
  effectivePrivilege acc (register_lookup mstatus rs) Machine
    = returnM Machine ->
  is_shadow_stack_access acc = returnM false ->
  hfrun 8 D Drw rs (translateAddr (Virtaddr pc) acc)
  = Some (Values.Ok (Physaddr pc, PBMT_PMA, init_ext_ptw), rs).
Proof.
  intros HD1 HD2 Hpriv Hep Hss.
  unfold translateAddr. tr_cbn.
  tr_read. tr_cbn.
  tr_read. rewrite Hpriv. tr_cbn.
  rewrite Hep. tr_cbn.
  unfold translationMode.
  change (Instances.generic_eq Machine Machine) with true. tr_cbn.
  rewrite Hss. tr_cbn.
  change (Instances.generic_eq Bare Bare) with true. tr_cbn.
  rewrite zext_pc_id. apply hfrun_ret.
Qed.

Lemma hfrun_translateAddr_M_ifetch (D Drw : gset register) (rs : regstate)
    (pc : SailStdpp.Values.mword 64) :
  (mstatus : register) ∈ D ->
  (cur_privilege : register) ∈ D ->
  register_lookup cur_privilege rs = Machine ->
  hfrun 8 D Drw rs (translateAddr (Virtaddr pc) (InstructionFetch tt))
  = Some (Values.Ok (Physaddr pc, PBMT_PMA, init_ext_ptw), rs).
Proof.
  intros HD1 HD2 Hpriv.
  apply (hfrun_translateAddr_M D Drw rs pc _ HD1 HD2 Hpriv);
    reflexivity.
Qed.

(* stdpp flags the Z/Pos arithmetic [simpl never], which blocks cbn even
   through an explicit delta whitelist; the loop's CLOSED index arithmetic
   needs them to compute, so lift the flag FILE-LOCALLY *)
Local Arguments Z.sub _ _ : simpl nomatch.
Local Arguments Z.add _ _ : simpl nomatch.
Local Arguments Z.mul _ _ : simpl nomatch.
Local Arguments Z.eqb _ _ : simpl nomatch.
Local Arguments Z.compare _ _ : simpl nomatch.
Local Arguments Z.pos_sub _ _ : simpl nomatch.
Local Arguments Pos.compare _ _ : simpl nomatch.
Local Arguments Pos.compare_cont _ _ _ : simpl nomatch.

Local Ltac cmr_cbn :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR
     Defs.returnR Defs.read_reg Defs.early_return Defs.throw
     Defs.assert_exp Defs.assert_exp'
     Defs.and_boolM Defs.or_boolM andb orb negb not
     check_pma_with_pmp_priority pmaCheck mag_pma_check
     is_mag_applicable_access __id
     get_config_rvfi plat_have_clint plat_have_sig].

Local Ltac cmr_read :=
  rewrite hfrun_read;
  match goal with
  | |- context [ bool_decide ?P ] =>
      rewrite (bool_decide_eq_true_2 P ltac:(assumption))
  end.

Local Lemma fit4_local (x k : Z) :
  x = 4 * k -> x < 2147483648 + 134217728 -> x + 4 <= 2147483648 + 134217728.
Proof. intros -> H. lia. Qed.

Local Lemma pma_access_local (a : SailStdpp.Values.mword 64) :
  addr_is_ram a -> is_aligned_paddr (Physaddr a) 4 = true ->
  pma_ram_access a 4.
Proof.
  intros [Hlo Hhi] Hal.
  unfold is_aligned_paddr in Hal. apply Z.eqb_eq in Hal.
  apply Zrem_divides in Hal. destruct Hal as [k Hk].
  unfold ram_base, ram_size in Hhi.
  unfold pma_ram_access, ram_base, ram_size.
  exact (conj (pma_width_ok 4 eq_refl eq_refl)
              (conj Hlo (fit4_local (uint a) k Hk Hhi))).
Qed.

Local Lemma fit2_local (x k : Z) :
  x = 2 * k -> x < 2147483648 + 134217728 -> x + 2 <= 2147483648 + 134217728.
Proof. intros -> H. lia. Qed.

Local Lemma pma_access2_local (a : SailStdpp.Values.mword 64) :
  addr_is_ram a -> is_aligned_paddr (Physaddr a) 2 = true ->
  pma_ram_access a 2.
Proof.
  intros [Hlo Hhi] Hal.
  unfold is_aligned_paddr in Hal. apply Z.eqb_eq in Hal.
  apply Zrem_divides in Hal. destruct Hal as [k Hk].
  unfold ram_base, ram_size in Hhi.
  unfold pma_ram_access, ram_base, ram_size.
  exact (conj (pma_width_ok 2 eq_refl eq_refl)
              (conj Hlo (fit2_local (uint a) k Hk Hhi))).
Qed.

Local Lemma clint_gt_local (x n : Z) : 0 <= n -> 2147483648 <= x -> 34340864 < x + n.
Proof. lia. Qed.

Local Lemma clint_false_local (a : SailStdpp.Values.mword 64) (n : Z) :
  0 <= n ->
  addr_is_ram a ->
  andb (Z.leb (uint plat_clint_base) (uint a))
       (Z.leb (Z.add (uint a) (__id n))
              (Z.add (uint plat_clint_base) (uint plat_clint_size)))
  = false.
Proof.
  intros Hn [Hlo _]. unfold ram_base in Hlo.
  assert (Hsum : Z.add (uint plat_clint_base) (uint plat_clint_size)
                 = 34340864) by (vm_compute; reflexivity).
  rewrite Hsum. unfold __id.
  apply andb_false_intro2. apply Z.leb_gt.
  exact (clint_gt_local (uint a) n Hn Hlo).
Qed.

(* WIDTH-GENERIC.  The fetch reads FOUR bytes at a 4-aligned pc but only
   TWO at a 2-mod-4 one (the model branches on PC bit 1), so everything from
   here up carries the width. *)
Lemma hfrun_within_mmio_ram (D Drw : gset register) (rs : regstate)
    (pa : SailStdpp.Values.mword 64) (n : Z) :
  0 <= n ->
  (htif_tohost_base : register) ∈ D ->
  register_lookup htif_tohost_base rs = None ->
  addr_is_ram pa ->
  hfrun 12 D Drw rs (within_mmio_readable (Physaddr pa) n) = Some (false, rs).
Proof.
  intros Hn HD Hhtif Hram.
  unfold within_mmio_readable, within_clint, within_sig,
    within_htif_readable, within_htif_writable.
  cmr_cbn.
  rewrite (clint_false_local pa n Hn Hram). cmr_cbn.
  cmr_read. rewrite Hhtif. cmr_cbn.
  apply hfrun_ret.
Qed.

(* the fetch request, as the model builds it *)
Definition mread_req (pa : SailStdpp.Values.mword 64)
    : Interface.ReadReq.t 4 :=
  {| Interface.ReadReq.pa := pa;
     Interface.ReadReq.access_kind :=
       SailStdpp.ConcurrencyInterfaceTypes.AK_explicit
         {| SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_variety
              := SailStdpp.ConcurrencyInterfaceTypes.AV_plain;
            SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_strength
              := SailStdpp.ConcurrencyInterfaceTypes.AS_normal |};
     Interface.ReadReq.va := None;
     Interface.ReadReq.translation := tt;
     Interface.ReadReq.tag := false |}.

Local Lemma hread_req_at_red_local (n : N) (req : Interface.ReadReq.t n)
    (K : (bv (8 * n) * option bool + Arch.abort)%type -> M unit) :
  hread_req_at n (Interface.Next (Interface.MemRead n req) K) = Some req.
Proof.
  simpl. destruct (decide (n = n)) as [Heq|Hne]; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel.
  reflexivity.
Qed.

Lemma hread_req_at_read_ram (pa : SailStdpp.Values.mword 64) :
  hread_req_at 4 (read_ram Read_plain (Physaddr pa) 4 false)
  = Some (mread_req pa).
Proof.
  unfold read_ram, Defs.sail_mem_read.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.returnm returnM
     Z.to_N bits_of_physaddr
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_pa
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_access_kind
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_va
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_translation
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_tag
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_size].
  cbn [hread_req_at].
  destruct (decide (4%N = 4%N)) as [Heq|Hne]; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel.
  reflexivity.
Qed.

Lemma hread_resume_read_ram (pa : SailStdpp.Values.mword 64) (w : bv 32) :
  hread_resume (bv_unsigned w) (read_ram Read_plain (Physaddr pa) 4 false)
  = Interface.Ret (w, default_meta).
Proof.
  unfold read_ram, Defs.sail_mem_read.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.returnm returnM
     Z.to_N bits_of_physaddr
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_pa
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_access_kind
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_va
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_translation
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_tag
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_size].
  cbn [hread_resume].
  rewrite Z_to_bv_bv_unsigned TypeCasts.cast_N_refl.
  reflexivity.
Qed.

(* THE 2-BYTE TWINS.  Not a width PARAMETER: RISC-V fetch is 2 or 4
   bytes and nothing else, so a parameter buys no generality while forcing
   [ReadReq.t n] / [bv (8*n)] type INDICES that do not reduce -- the trap
   recorded in the worklist.  Two concrete instances are the honest shape
   here; the PURE walkers below/above are parameterised because their width
   is a plain [Z] argument with no type dependency. *)
Definition mread_req2 (pa : SailStdpp.Values.mword 64)
    : Interface.ReadReq.t 2 :=
  {| Interface.ReadReq.pa := pa;
     Interface.ReadReq.access_kind :=
       SailStdpp.ConcurrencyInterfaceTypes.AK_explicit
         {| SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_variety
              := SailStdpp.ConcurrencyInterfaceTypes.AV_plain;
            SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_strength
              := SailStdpp.ConcurrencyInterfaceTypes.AS_normal |};
     Interface.ReadReq.va := None;
     Interface.ReadReq.translation := tt;
     Interface.ReadReq.tag := false |}.

Local Lemma hread_req_at_red_local2 (n : N) (req : Interface.ReadReq.t n)
    (K : (bv (8 * n) * option bool + Arch.abort)%type -> M unit) :
  hread_req_at n (Interface.Next (Interface.MemRead n req) K) = Some req.
Proof.
  simpl. destruct (decide (n = n)) as [Heq|Hne]; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel.
  reflexivity.
Qed.

Lemma hread_req_at_read_ram2 (pa : SailStdpp.Values.mword 64) :
  hread_req_at 2 (read_ram Read_plain (Physaddr pa) 2 false)
  = Some (mread_req2 pa).
Proof.
  unfold read_ram, Defs.sail_mem_read.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.returnm returnM
     Z.to_N bits_of_physaddr
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_pa
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_access_kind
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_va
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_translation
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_tag
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_size].
  cbn [hread_req_at].
  destruct (decide (2%N = 2%N)) as [Heq|Hne]; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel.
  reflexivity.
Qed.

Lemma hread_resume_read_ram2 (pa : SailStdpp.Values.mword 64) (w : bv 16) :
  hread_resume (bv_unsigned w) (read_ram Read_plain (Physaddr pa) 2 false)
  = Interface.Ret (w, default_meta).
Proof.
  unfold read_ram, Defs.sail_mem_read.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.returnm returnM
     Z.to_N bits_of_physaddr
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_pa
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_access_kind
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_va
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_translation
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_tag
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_size].
  cbn [hread_resume].
  rewrite Z_to_bv_bv_unsigned TypeCasts.cast_N_refl.
  reflexivity.
Qed.

(* WIDTH-GENERIC, and the RAM-access fact arrives as a PREMISE rather than
   being derived here from [addr_is_ram] + 4-alignment.  That is what keeps
   the chain width-agnostic: the alignment arithmetic is width-specific, so
   it belongs at the top where the width is known, not buried in the walk.
   [pma_access_local] is the width-4 discharge. *)
Lemma hfrun_check_pma_ifetch (D Drw : gset register) (rs : regstate)
    (pa : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region) (n : Z) :
  (pma_regions : register) ∈ D ->
  register_lookup pma_regions rs = pmar0 ->
  pma_allows_ram pmar0 ->
  pma_ram_access pa n ->
  is_aligned_paddr (Physaddr pa) n = true ->
  hfrun 6 D Drw rs
    (check_pma_with_pmp_priority (InstructionFetch tt) PBMT_PMA Machine
       (Physaddr pa) n false)
  = Some (Values.Ok
            {| Phys_Mem_Access_Info_splittable := CannotSplit;
               Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).
Proof.
  intros HD Hpma Hpallow Hacc Hpa.
  unfold check_pma_with_pmp_priority. cmr_cbn.
  cmr_read. rewrite Hpma. cmr_cbn.
  destruct (Hpallow pa n Hacc) as (region & Hmatch & Hgrant).
  destruct region as [rbase rsize rattr rdtree].
  destruct Hgrant as (Hx & _).
  cbn [PMA_Region_attributes] in Hx.
  rewrite Hmatch. cmr_cbn.
  rewrite Hx. cmr_cbn.
  rewrite Hpa. cmr_cbn.
  apply hfrun_ret.
Qed.

(* the width-4 instance the 4-aligned fetch path uses *)
Lemma hfrun_check_pma_ifetch4 (D Drw : gset register) (rs : regstate)
    (pa : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region) :
  (pma_regions : register) ∈ D ->
  register_lookup pma_regions rs = pmar0 ->
  pma_allows_ram pmar0 ->
  addr_is_ram pa ->
  is_aligned_paddr (Physaddr pa) 4 = true ->
  hfrun 6 D Drw rs
    (check_pma_with_pmp_priority (InstructionFetch tt) PBMT_PMA Machine
       (Physaddr pa) 4 false)
  = Some (Values.Ok
            {| Phys_Mem_Access_Info_splittable := CannotSplit;
               Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).
Proof.
  intros HD Hpma Hpallow Hram Hpa.
  exact (hfrun_check_pma_ifetch D Drw rs pa pmar0 4 HD Hpma Hpallow
           (pma_access_local pa Hram Hpa) Hpa).
Qed.

Section fetch.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma swp_checked_mem_read_ifetch4 (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (bytes : bv 32) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) pa 4 = Some bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Machine
           (Physaddr pa) 4 false false false false)
      (fun r => ⌜r = Values.Ok (bytes, tt)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HD HDcfg HDhtif Hhtif Hpma Hpcfg Hunlock Hpallow Hram Hpa.
    iIntros "#Hcert Hrw Hro Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold checked_mem_read.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority (InstructionFetch tt) PBMT_PMA
                 Machine (Physaddr pa) 4 false) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_check_pma_ifetch4 (Drw ∪ Dro) Drw rs pa pmar0
                   HD Hpma Hpallow Hram Hpa) with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind_ret. cbn beta iota zeta.
    cbn [Phys_Mem_Access_Info_granule_size_exp Phys_Mem_Access_Info_splittable].
    cbn beta iota zeta delta [split_misaligned misaligned_order
      sys_misaligned_order_decreasing read_kind_of_flags].
    change (Instances.generic_eq CannotSplit CannotSplit) with true.
    cbn beta iota.
    rewrite /returnM mliftR_ret mbind_ret. cbn beta iota zeta.
    rewrite mliftR_ret mbind_ret. cbn beta iota zeta.
    cbn beta iota zeta delta [Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
      Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare].
    cbn beta iota zeta delta [Defs.assert_exp' bits_of_physaddr].
    rewrite mliftR_ret mbind_ret. cbn beta iota.
    change (0 * 4) with 0. rewrite avi0.
    iApply (swp_use_cer3
              (pmpCheck (Physaddr pa) 4 (InstructionFetch tt) Machine)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_ifetch4 Drw Dro Df rs pcfg pa Hdisj HDcfg
                Hunlock Hpa Hpcfg with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind0_ret.
    iApply (swp_use_cer3 (within_mmio_readable (Physaddr pa) 4)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 12 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_within_mmio_ram (Drw ∪ Dro) Drw rs pa 4
                   ltac:(lia) HDhtif Hhtif Hram)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer4 (read_ram Read_plain (Physaddr pa) 4 false)
              _ _ _ _ _ C HC with "[Hrw Hro Hmem] [-]").
    { iApply (swp_hart_ram_read 4 (mread_req pa) _
                (fun r => (⌜r = (bytes, default_meta)⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I)
                (hread_req_at_read_ram pa)
                (addr_is_ram_not_dev pa Hram) ltac:(reflexivity)
                with "Hcert [Hrw Hro Hmem]").
      iIntros (σ) "Hσ". iMod ("Hmem" $! σ with "Hσ") as "[%Hrb Hclose]".
      iModIntro. iExists bytes. iSplitR; [done|]. iNext.
      iMod "Hclose" as "Hσ". iModIntro. iFrame "Hσ".
      rewrite hread_resume_read_ram. iApply swp_ret. by iFrame. }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota zeta.
    rewrite mbind_ret. cbn beta.
    change (0 =? 1 - 1) with true. cbn beta iota zeta.
    rewrite !autocast_id usvd_zeros_full_32 mcer_ret.
    iApply ("Hcont" $! (Values.Ok (bytes, tt))). by iFrame.
  Qed.

  (* the 2-byte instance: the halfword fetch at a 2-mod-4 pc *)
  Lemma swp_checked_mem_read_ifetch2 (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (bytes : bv 16) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_paddr (Physaddr pa) 2 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) pa 2 = Some bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Machine
           (Physaddr pa) 2 false false false false)
      (fun r => ⌜r = Values.Ok (bytes, tt)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HD HDcfg HDhtif Hhtif Hpma Hpcfg Hunlock Hpallow Hram Hpa.
    iIntros "#Hcert Hrw Hro Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold checked_mem_read.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority (InstructionFetch tt) PBMT_PMA
                 Machine (Physaddr pa) 2 false) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_check_pma_ifetch (Drw ∪ Dro) Drw rs pa pmar0 2
                   HD Hpma Hpallow (pma_access2_local pa Hram Hpa) Hpa)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind_ret. cbn beta iota zeta.
    cbn [Phys_Mem_Access_Info_granule_size_exp Phys_Mem_Access_Info_splittable].
    cbn beta iota zeta delta [split_misaligned misaligned_order
      sys_misaligned_order_decreasing read_kind_of_flags].
    change (Instances.generic_eq CannotSplit CannotSplit) with true.
    cbn beta iota.
    rewrite /returnM mliftR_ret mbind_ret. cbn beta iota zeta.
    rewrite mliftR_ret mbind_ret. cbn beta iota zeta.
    cbn beta iota zeta delta [Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
      Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare].
    cbn beta iota zeta delta [Defs.assert_exp' bits_of_physaddr].
    rewrite mliftR_ret mbind_ret. cbn beta iota.
    change (0 * 2) with 0. rewrite avi0.
    iApply (swp_use_cer3
              (pmpCheck (Physaddr pa) 2 (InstructionFetch tt) Machine)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_ifetch2 Drw Dro Df rs pcfg pa Hdisj HDcfg
                Hunlock Hpa Hpcfg with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind0_ret.
    iApply (swp_use_cer3 (within_mmio_readable (Physaddr pa) 2)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 12 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_within_mmio_ram (Drw ∪ Dro) Drw rs pa 2
                   ltac:(lia) HDhtif Hhtif Hram)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer4 (read_ram Read_plain (Physaddr pa) 2 false)
              _ _ _ _ _ C HC with "[Hrw Hro Hmem] [-]").
    { iApply (swp_hart_ram_read 2 (mread_req2 pa) _
                (fun r => (⌜r = (bytes, default_meta)⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I)
                (hread_req_at_read_ram2 pa)
                (addr_is_ram_not_dev pa Hram) ltac:(reflexivity)
                with "Hcert [Hrw Hro Hmem]").
      iIntros (σ) "Hσ". iMod ("Hmem" $! σ with "Hσ") as "[%Hrb Hclose]".
      iModIntro. iExists bytes. iSplitR; [done|]. iNext.
      iMod "Hclose" as "Hσ". iModIntro. iFrame "Hσ".
      rewrite hread_resume_read_ram2. iApply swp_ret. by iFrame. }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota zeta.
    rewrite mbind_ret. cbn beta.
    change (0 =? 1 - 1) with true. cbn beta iota zeta.
    rewrite !autocast_id usvd_zeros_full_16 mcer_ret.
    iApply ("Hcont" $! (Values.Ok (bytes, tt))). by iFrame.
  Qed.

  Lemma swp_translateAddr_M (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pc : SailStdpp.Values.mword 64) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (translateAddr (Virtaddr pc) (InstructionFetch tt))
      (fun r => ⌜r = Values.Ok (Physaddr pc, PBMT_PMA, init_ext_ptw)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv.
    apply (swp_hfrun 8 Drw Dro Df rs rs _ _ Hdisj).
    exact (hfrun_translateAddr_M_ifetch (Drw ∪ Dro) Drw rs pc
             HDmst HDpriv Hpriv).
  Qed.

  Lemma swp_mem_read_M (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pa : physaddr) (w : SailStdpp.Values.mword 32)
      (pv : Privilege) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = pv ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA pv pa 4
              false false false false)
         (fun r => ⌜r = Values.Ok (w, tt)⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    swp (mem_read (InstructionFetch tt) PBMT_PMA pa 4 false false false)
      (fun r => ⌜r = Values.Ok w⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv.
    iIntros "#Hcert Hrw Hro Hcmr".
    unfold mem_read.
    iApply (swp_bind_use (Defs.read_reg mstatus) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    unfold effectivePrivilege.
    change (Instances.generic_neq (InstructionFetch tt) (InstructionFetch tt))
      with false.
    cbn beta iota zeta delta [Defs.returnm returnM].
    rewrite mbind_ret.
    unfold mem_read_priv, mem_read_priv_meta.
    cbn beta iota.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I) _
              with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_bind_use _ _
                (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I) _
                with "[Hrw Hro Hcmr] [-]").
      - iApply ("Hcmr" with "Hrw Hro").
      - iIntros (v) "(-> & Hrw & Hro)". iApply swp_ret. by iFrame. }
    iIntros (v) "(-> & Hrw & Hro)". iApply swp_ret.
    cbn [MemoryOpResult_drop_meta]. by iFrame.
  Qed.

  (* the 2-byte instance *)
  Lemma swp_mem_read_M2 (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pa : physaddr) (w : SailStdpp.Values.mword 16)
      (pv : Privilege) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = pv ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA pv pa 2
              false false false false)
         (fun r => ⌜r = Values.Ok (w, tt)⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    swp (mem_read (InstructionFetch tt) PBMT_PMA pa 2 false false false)
      (fun r => ⌜r = Values.Ok w⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv.
    iIntros "#Hcert Hrw Hro Hcmr".
    unfold mem_read.
    iApply (swp_bind_use (Defs.read_reg mstatus) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    unfold effectivePrivilege.
    change (Instances.generic_neq (InstructionFetch tt) (InstructionFetch tt))
      with false.
    cbn beta iota zeta delta [Defs.returnm returnM].
    rewrite mbind_ret.
    unfold mem_read_priv, mem_read_priv_meta.
    cbn beta iota.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I) _
              with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_bind_use _ _
                (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I) _
                with "[Hrw Hro Hcmr] [-]").
      - iApply ("Hcmr" with "Hrw Hro").
      - iIntros (v) "(-> & Hrw & Hro)". iApply swp_ret. by iFrame. }
    iIntros (v) "(-> & Hrw & Hro)". iApply swp_ret.
    cbn [MemoryOpResult_drop_meta]. by iFrame.
  Qed.

  Lemma swp_fetch_bytes_M (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pc : SailStdpp.Values.mword 64)
      (w : SailStdpp.Values.mword 32) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Machine
              (Physaddr pc) 4 false false false false)
         (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                    hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I)) -∗
    swp (fetch_bytes pc pc 4)
      (fun r => ⌜r = @FetchBytes_Success 4 w⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv.
    iIntros "#Hcert Hrw Hro Hcmr".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold fetch_bytes.
    cbn beta iota zeta delta [ext_fetch_check_pc].
    rewrite mbind0_ret.
    iApply (swp_use_cer (translateAddr (Virtaddr pc) (InstructionFetch tt))
              _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_translateAddr_M Drw Dro Df rs pc Hdisj HDmst HDpriv Hpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer
              (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pc) 4
                 false false false) _ _ C HC with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_mem_read_M Drw Dro Df rs (Physaddr pc) w Machine Hdisj HDmst
                HDpriv Hpriv with "Hcert Hrw Hro Hcmr"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite autocast_id mcer_ret.
    iApply ("Hcont" $! (@FetchBytes_Success 4 w)). by iFrame.
  Qed.

  (* the 2-byte instance *)
  (* the 2-byte instance, with the two addresses SEPARATE: the model
     translates and reads at [granule_start], and the second halfword of a
     base instruction at a 2-mod-4 pc is fetched at [pc+2] while
     [fetch_start] stays [pc]. *)
  Lemma swp_fetch_bytes_M2 (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (fs gs : SailStdpp.Values.mword 64)
      (w : SailStdpp.Values.mword 16) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Machine
              (Physaddr gs) 2 false false false false)
         (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                    hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I)) -∗
    swp (fetch_bytes fs gs 2)
      (fun r => ⌜r = @FetchBytes_Success 2 w⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv.
    iIntros "#Hcert Hrw Hro Hcmr".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold fetch_bytes.
    cbn beta iota zeta delta [ext_fetch_check_pc].
    rewrite mbind0_ret.
    iApply (swp_use_cer (translateAddr (Virtaddr gs) (InstructionFetch tt))
              _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_translateAddr_M Drw Dro Df rs gs Hdisj HDmst HDpriv Hpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer
              (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr gs) 2
                 false false false) _ _ C HC with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_mem_read_M2 Drw Dro Df rs (Physaddr gs) w Machine Hdisj HDmst
                HDpriv Hpriv with "Hcert Hrw Hro Hcmr"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite autocast_id mcer_ret.
    iApply ("Hcont" $! (@FetchBytes_Success 2 w)). by iFrame.
  Qed.

  (* THE LANDING FILE IS A PARAMETER.  Everything this rule does itself --
     the PC reads and the alignment tests -- happens at [rs], and then it
     hands off to [fetch_bytes]; where THAT lands is the fetch's business,
     not this rule's.  M-mode's fetch lands back on [rs] (a physical read
     writes nothing) and instantiates [rsf := rs]; S-mode's may fill the TLB
     and lands elsewhere. *)
  Lemma swp_fetch (Drw Dro : gset register) (Df : register -> dfrac)
      (rs rsf : regstate) (pc : SailStdpp.Values.mword 64)
      (w : SailStdpp.Values.mword 32) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch_bytes pc pc 4)
         (fun r => ⌜r = @FetchBytes_Success 4 w⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    swp (fetch tt)
      (fun r => ⌜r = (if isRVC (subrange_vec_dec w 15 0)
                      then F_RVC (subrange_vec_dec w 15 0)
                      else F_Base w)⌝ ∗
                hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro).
  Proof.
    intros Hdisj HDpc Hpc Hb0 Hb1 Hal.
    iIntros "#Hcert Hrw Hro Hfb".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold fetch. mf_glue.
    (* the two PC reads feeding ext_fetch_check_pc *)
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". mf_glue.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". mf_glue.
    rewrite mbind0_ret. unfold Defs.or_boolM.
    (* the misalignment test's bit-0 read *)
    iApply (swp_use_cer3 (Defs.read_reg (R_bitvector_64 PC)) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hpc mbind_ret. cbn beta. rewrite Hb0.
    unfold Defs.and_boolM.
    (* the bit-1 read; with a 4-aligned PC it short-circuits before Zca *)
    iApply (swp_use_cer3 (Defs.read_reg (R_bitvector_64 PC)) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hpc mbind_ret. cbn beta. rewrite Hb1.
    rewrite mbind_ret. cbn beta.
    (* the 4-alignment test; Ziccif is a constant true, no read *)
    unfold Defs.and_boolM.
    iApply (swp_use_cer3 (Defs.read_reg (R_bitvector_64 PC)) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hpc mbind_ret. cbn beta. rewrite Hal.
    rewrite mf_cE_Ziccif_eq_local /returnM mliftR_ret mbind_ret. cbn beta.
    (* the two PC reads feeding fetch_bytes *)
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpc.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpc.
    (* THE CALL *)
    iApply (swp_use_cer (fetch_bytes pc pc 4) _ _ C HC
              with "[Hrw Hro Hfb] [-]").
    { iApply ("Hfb" with "Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mcer_ret.
    iApply ("Hcont" $! (if isRVC (subrange_vec_dec w 15 0)
                        then F_RVC (subrange_vec_dec w 15 0)
                        else F_Base w)). by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE 2-mod-4 COMPRESSED FETCH.  With PC bit 1 SET the model takes the *)
  (* halfword path: [fetch_bytes pc pc 2], and if that halfword is        *)
  (* compressed the fetch is done in ONE access.                          *)
  (*                                                                     *)
  (* WHAT DIFFERS FROM THE 4-ALIGNED RULE, and it is not just the width:  *)
  (* with bit 1 set the misalignment test does NOT short-circuit, so the  *)
  (* model reads [misa] to evaluate [Ext_Zca].  Hence the two extra       *)
  (* premises.  (This file's header says "Ext_Zca is never read" -- true  *)
  (* of the 4-aligned path, and exactly why this one needs its own rule.) *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_fetch_rvc2 (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pc : SailStdpp.Values.mword 64)
      (h : SailStdpp.Values.mword 16) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = true ->
    (* NOT derived here: [InstrBytes.align2_not4_facts] already gives the
       caller this together with the two bit tests, off [instr_bytes]'s own
       2-alignment. *)
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    isRVC h = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch_bytes pc pc 2)
         (fun r => ⌜r = @FetchBytes_Success 2 h⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    swp (fetch tt)
      (fun r => ⌜r = F_RVC h⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpc HDmisa Hpc Hb0 Hb1 Hal4 HmisaC Hrvc.
    iIntros "#Hcert Hrw Hro Hfb".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold fetch. mf_glue.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". mf_glue.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". mf_glue.
    rewrite mbind0_ret. unfold Defs.or_boolM.
    iApply (swp_use_cer3 (Defs.read_reg (R_bitvector_64 PC)) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hpc mbind_ret. cbn beta. rewrite Hb0.
    unfold Defs.and_boolM.
    iApply (swp_use_cer3 (Defs.read_reg (R_bitvector_64 PC)) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hpc mbind_ret. cbn beta. rewrite Hb1.
    (* bit 1 SET: the Zca probe IS reached *)
    rewrite mf_cE_Zca_eq_local.
    iApply (swp_use_cer3 (Defs.read_reg misa) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmisa
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite HmisaC. cbn beta iota.
    rewrite mbind_ret. cbn beta.
    (* the 4-alignment test is FALSE, so the and_boolM short-circuits *)
    unfold Defs.and_boolM.
    iApply (swp_use_cer3 (Defs.read_reg (R_bitvector_64 PC)) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hpc mbind_ret. cbn beta.
    rewrite Hal4. cbn beta iota.
    rewrite mbind_ret. cbn beta.
    (* the two PC reads feeding the halfword fetch_bytes *)
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpc.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpc.
    iApply (swp_use_cer (fetch_bytes pc pc 2) _ _ C HC
              with "[Hrw Hro Hfb] [-]").
    { iApply ("Hfb" with "Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite Hrvc. cbn beta iota.
    rewrite mcer_ret.
    iApply ("Hcont" $! (F_RVC h)). by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* A BASE INSTRUCTION AT A 2-mod-4 pc: TWO halfword fetches, then     *)
  (* [F_Base (concat_vec ihi ilo)].  This case is real -- strncpy+0xe   *)
  (* is a BGE sitting after seven compressed instructions -- so it is   *)
  (* not an exotic corner the kernel avoids.                             *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_fetch_base2 (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pc : SailStdpp.Values.mword 64)
      (ilo ihi : SailStdpp.Values.mword 16) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = true ->
    (* NOT derived here: [InstrBytes.align2_not4_facts] already gives the
       caller this together with the two bit tests, off [instr_bytes]'s own
       2-alignment. *)
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    isRVC ilo = false ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch_bytes pc pc 2)
         (fun r => ⌜r = @FetchBytes_Success 2 ilo⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch_bytes pc (add_vec_int pc 2) 2)
         (fun r => ⌜r = @FetchBytes_Success 2 ihi⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    swp (fetch tt)
      (fun r => ⌜r = F_Base (concat_vec ihi ilo)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpc HDmisa Hpc Hb0 Hb1 Hal4 HmisaC Hnrvc.
    iIntros "#Hcert Hrw Hro Hlo Hhi".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold fetch. mf_glue.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". mf_glue.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". mf_glue.
    rewrite mbind0_ret. unfold Defs.or_boolM.
    iApply (swp_use_cer3 (Defs.read_reg (R_bitvector_64 PC)) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hpc mbind_ret. cbn beta. rewrite Hb0.
    unfold Defs.and_boolM.
    iApply (swp_use_cer3 (Defs.read_reg (R_bitvector_64 PC)) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hpc mbind_ret. cbn beta. rewrite Hb1.
    (* bit 1 SET: the Zca probe IS reached *)
    rewrite mf_cE_Zca_eq_local.
    iApply (swp_use_cer3 (Defs.read_reg misa) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmisa
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite HmisaC. cbn beta iota.
    rewrite mbind_ret. cbn beta.
    (* the 4-alignment test is FALSE, so the and_boolM short-circuits *)
    unfold Defs.and_boolM.
    iApply (swp_use_cer3 (Defs.read_reg (R_bitvector_64 PC)) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hpc mbind_ret. cbn beta.
    rewrite Hal4. cbn beta iota.
    rewrite mbind_ret. cbn beta.
    (* the two PC reads feeding the FIRST halfword fetch *)
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpc.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpc.
    iApply (swp_use_cer (fetch_bytes pc pc 2) _ _ C HC
              with "[Hrw Hro Hlo] [-]").
    { iApply ("Hlo" with "Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    (* NOT compressed, so the model goes back for the high halfword *)
    rewrite Hnrvc. cbn beta iota.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpc.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpc.
    iApply (swp_use_cer (fetch_bytes pc (add_vec_int pc 2) 2) _ _ C HC
              with "[Hrw Hro Hhi] [-]").
    { iApply ("Hhi" with "Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mcer_ret.
    iApply ("Hcont" $! (F_Base (concat_vec ihi ilo))). by iFrame.
  Qed.

  (* THE COMPOSITION: [fetch] with [fetch_bytes] filled in, leaving only
     [checked_mem_read] -- where [pmpCheck] and the memory event live -- as
     the obligation. *)
  Lemma swp_fetch_M (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pc : SailStdpp.Values.mword 64)
      (w : SailStdpp.Values.mword 32) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    register_lookup cur_privilege rs = Machine ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Machine
              (Physaddr pc) 4 false false false false)
         (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                    hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I)) -∗
    swp (fetch tt)
      (fun r => ⌜r = (if isRVC (subrange_vec_dec w 15 0)
                      then F_RVC (subrange_vec_dec w 15 0)
                      else F_Base w)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpc HDmst HDpriv Hpc Hpriv Hb0 Hb1 Hal.
    iIntros "#Hcert Hrw Hro Hcmr".
    iApply (swp_fetch Drw Dro Df rs rs pc w Hdisj HDpc Hpc Hb0 Hb1 Hal
              with "Hcert Hrw Hro [Hcmr]").
    iIntros "Hrw Hro".
    iApply (swp_fetch_bytes_M Drw Dro Df rs pc w Hdisj HDmst HDpriv Hpriv
              with "Hcert Hrw Hro Hcmr").
  Qed.

  (* THE WHOLE FETCH, no obligation but the memory one -- which is the
     caller's job and nobody else's: the leaf owns the text bytes. *)
  Lemma swp_fetch_ram (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pc : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (w : SailStdpp.Values.mword 32) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup htif_tohost_base rs = None ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram pc ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    is_aligned_paddr (Physaddr pc) 4 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) pc 4 = Some w⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    swp (fetch tt)
      (fun r => ⌜r = (if isRVC (subrange_vec_dec w 15 0)
                      then F_RVC (subrange_vec_dec w 15 0)
                      else F_Base w)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpc HDmst HDpriv HDpma HDcfg HDhtif
      Hpc Hpriv Hpma Hpcfg Hhtif Hunlock Hpallow Hram Hb0 Hb1 Hva Hpa.
    iIntros "#Hcert Hrw Hro Hmem".
    iApply (swp_fetch_M Drw Dro Df rs pc w Hdisj HDpc HDmst HDpriv
              Hpc Hpriv Hb0 Hb1 Hva with "Hcert Hrw Hro [Hmem]").
    iIntros "Hrw Hro".
    iApply (swp_checked_mem_read_ifetch4 Drw Dro Df rs pc pmar0 pcfg w
              Hdisj HDpma HDcfg HDhtif Hhtif Hpma Hpcfg Hunlock Hpallow
              Hram Hpa with "Hcert Hrw Hro Hmem").
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE 2-mod-4 COMPRESSED FETCH, from owned bytes.  Same composition as *)
  (* [swp_fetch_ram] one width down, ending at [swp_fetch_rvc2] rather    *)
  (* than [swp_fetch]: TWO bytes read, and the caller owes only those.    *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_fetch_ram_rvc2 (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pc : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (h : SailStdpp.Values.mword 16) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram pc ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    is_aligned_paddr (Physaddr pc) 2 = true ->
    isRVC h = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) pc 2 = Some h⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    swp (fetch tt)
      (fun r => ⌜r = F_RVC h⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpc HDmst HDpriv HDmisa HDpma HDcfg HDhtif
      Hpc Hpriv Hpma Hpcfg Hhtif HmisaC Hunlock Hpallow Hram Hb0 Hb1 Hal4
      Hpa Hrvc.
    iIntros "#Hcert Hrw Hro Hmem".
    iApply (swp_fetch_rvc2 Drw Dro Df rs pc h Hdisj HDpc HDmisa Hpc Hb0 Hb1
              Hal4 HmisaC Hrvc with "Hcert Hrw Hro [Hmem]").
    iIntros "Hrw Hro".
    iApply (swp_fetch_bytes_M2 Drw Dro Df rs pc pc h Hdisj HDmst HDpriv Hpriv
              with "Hcert Hrw Hro [Hmem]").
    iIntros "Hrw Hro".
    iApply (swp_checked_mem_read_ifetch2 Drw Dro Df rs pc pmar0 pcfg h
              Hdisj HDpma HDcfg HDhtif Hhtif Hpma Hpcfg Hunlock Hpallow
              Hram Hpa with "Hcert Hrw Hro Hmem").
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE BASE-AT-2-mod-4 FETCH, from owned bytes.  The first place TWO    *)
  (* memory obligations appear: one per halfword, at [pc] and [pc+2].     *)
  (* [pc] is 2-mod-4, so [pc+2] is 4-aligned and a fortiori 2-aligned --  *)
  (* but it is a DIFFERENT address, so it carries its own RAM and         *)
  (* alignment premises rather than inheriting [pc]'s.                    *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_fetch_ram_base2 (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pc : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (ilo ihi : SailStdpp.Values.mword 16) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram pc ->
    addr_is_ram (add_vec_int pc 2) ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    is_aligned_paddr (Physaddr pc) 2 = true ->
    is_aligned_paddr (Physaddr (add_vec_int pc 2)) 2 = true ->
    isRVC ilo = false ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) pc 2 = Some ilo⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) (add_vec_int pc 2) 2 = Some ihi⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    swp (fetch tt)
      (fun r => ⌜r = F_Base (concat_vec ihi ilo)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpc HDmst HDpriv HDmisa HDpma HDcfg HDhtif
      Hpc Hpriv Hpma Hpcfg Hhtif HmisaC Hunlock Hpallow Hram Hram2
      Hb0 Hb1 Hal4 Hpa Hpa2 Hnrvc.
    iIntros "#Hcert Hrw Hro Hlo Hhi".
    iApply (swp_fetch_base2 Drw Dro Df rs pc ilo ihi Hdisj HDpc HDmisa Hpc
              Hb0 Hb1 Hal4 HmisaC Hnrvc with "Hcert Hrw Hro [Hlo] [Hhi]").
    - iIntros "Hrw Hro".
      iApply (swp_fetch_bytes_M2 Drw Dro Df rs pc pc ilo Hdisj HDmst HDpriv
                Hpriv with "Hcert Hrw Hro [Hlo]").
      iIntros "Hrw Hro".
      iApply (swp_checked_mem_read_ifetch2 Drw Dro Df rs pc pmar0 pcfg ilo
                Hdisj HDpma HDcfg HDhtif Hhtif Hpma Hpcfg Hunlock Hpallow
                Hram Hpa with "Hcert Hrw Hro Hlo").
    - iIntros "Hrw Hro".
      iApply (swp_fetch_bytes_M2 Drw Dro Df rs pc (add_vec_int pc 2) ihi
                Hdisj HDmst HDpriv Hpriv with "Hcert Hrw Hro [Hhi]").
      iIntros "Hrw Hro".
      iApply (swp_checked_mem_read_ifetch2 Drw Dro Df rs (add_vec_int pc 2)
                pmar0 pcfg ihi Hdisj HDpma HDcfg HDhtif Hhtif Hpma Hpcfg
                Hunlock Hpallow Hram2 Hpa2 with "Hcert Hrw Hro Hhi").
  Qed.

End fetch.
