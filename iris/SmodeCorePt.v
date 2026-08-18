(* SmodeCorePt.v -- the S-mode instruction-step ENGINE, at the PER-NODE
   (swp) layer, over the generalized page-table-tree invariant.

   THE SHAPE.  A cycle is no longer one language step against one sigma:
   it is a walk over the Sail monad's nodes, so the wrappers here do NOT
   hand a caller [mstate_interp σ] and ask for a successor.  They hand it
   CELLS and ask for one [swp (execute i) ..] -- exactly what
   [WpInstr.wp_instr] and [WpInstrConfig.wp_instr_config] do for M-mode,
   one privilege over.  What is genuinely S-mode is the FETCH: it
   TRANSLATES, which means a page walk that may read three PTEs and FILL
   THE TLB while other harts run.

   WHAT THE WRAPPERS TAKE, and the one interface decision this conversion
   had to make:

     - the config cells (cur_privilege / mstatus / mie / mideleg /
       menvcfg) at a caller-chosen fraction, as before, plus [hw_config],
       [minstret_inv], [hart_state], [pc_is pc] and [instr pc is_rvc i];
     - the four cells the regime used to hide inside [SRegime.sr_inv R]
       (satp, tlb, pmpcfg_n, pmpaddr_n) RAW -- they must be in the frame,
       because the walk reads and writes them;
     - the regime's non-cell RESIDUE as a family
       [Res : type_of_register tlb -> iProp Σ] ([SRegime.sr_swp_res] at
       the tlb value the cell carries -- [tlb_snap_ok tv ∗ kpt_inv] at
       [kpt_share_regime], [True] at [bare_regime]);
     - the regime's FETCH TRANSLATION as a persistent obligation
       ([spt_fetch_tr], which is [SRegime.sr_swp_translate] at
       [InstructionFetch tt] instantiated at the wrapper's tower).

   THE RAW-CELL WRAPPER IS NOT PARAMETERISED BY [R : s_regime] at all,
   and the reason is structural: [sr_swp_res] is a
   function of the FILE and [sr_swp_side] mentions the file and a
   reference [mstate], while the wrapper's file is a tower whose
   components come out of [pc_is] and [hw_config] EXISTENTIALLY.  No
   premise of the wrapper can name that tower, so "the residue at the
   tower" is not statable.  Taking the residue family and the translate
   obligation instead costs a caller nothing -- [sr_swp_translate] is
   itself ∀-over-files -- and puts [sr_swp_side] where it was designed to
   be discharged: at the caller, which knows which arm it is on.

   THE LAYERS, bottom up (each names the file it belongs in; they are
   here so that this conversion costs no rebuild of the M-mode cone):

     - [s_fetch_chunk] / [s_mem_chunk] / [s_win_write] and the two
       claim-keyed word writes: the WINDOW COLLAPSE lemmas, unchanged --
       a non-straddling chunk of a claim-carrying va window reads and
       writes at the TRANSLATED pa [pa_of ppn b];
     - [s_regime_fetch] and [tlb_inv_pt_fetch]: the exec-shaped unified
       S-mode fetch, kept for the callers that still consume it;
     - PART A [hfrun_check_pma_ifetch_S], [swp_checked_mem_read_ifetch4_S]
       / [_2_S]: the instruction-fetch RAM read at SUPERVISOR, where the
       PMP fall-through is DENY so entry 0 must actually match;
     - PART B [s_text_obl] and [s_chunk_ram]: the persistent text window
       as a per-node memory obligation at the translated pa, and its two
       RAM endpoints off the bytes' own claims;
     - PART C [swp_run_hart_active_gen_exf] / [_rvc_exf]: [HartRunGen]'s
       rules with the FETCH-LANDING FILE a predicate and a landing-file-
       indexed rider.  A walking fetch cannot NAME the landing file --
       [sr_swp_translate]'s post is existential precisely because no
       caller knows whether the TLB hits -- and an existential inside a
       [swp] postcondition cannot be hoisted out;
     - PARTS D-F [spt_fetch_P] / [_rvc2_P] / [_base2_P] and the S-mode
       chain over them: [HartMFetch]'s fetch shapes with the
       [fetch_bytes] post ABSTRACT (the landing file never occurs in
       their proofs, only in that post);
     - PART G [spt_run_hart_active_instr_S]: the four-arm dispatch on the
       [instr] resource (F_Base / F_RVC x pc's 4-alignment), which is
       [WpInstrRun.swp_run_hart_active_instr_ex]'s twin;
     - PARTS H-K [spt_cycle], [spt_frames_intro] / [_elim], [s_npc_agree]
       and the three wrappers.

   WHAT IS NOT PROVED, and it is one thing.  [spt_cycle] is
   [WpSFrames.s_cycle_any] with the body's rider INDEXED BY THE POST
   FILE, and that indexing is what the S-mode cycle needs and does not
   have.  The walk lands the frames on the tower at a tlb value it
   CHOOSES; the regime's residue comes back at that value; the
   continuation needs it paired with the tlb CELL, which arrives inside
   the post-cycle frames.  With [HartStepAny.swp_exec_step_any]'s rider a
   plain [iProp Σ] the pairing cannot be expressed -- the rider cannot
   mention the post file and the pure [Q] cannot mention a resource.
   [WpSFrames.s_cycle]'s [tlb_snap_ok tlbv'] premise is the same gap one
   level up: it asks the caller to NAME the landing tlb value before the
   body runs.  Indexing the rider ([swp_exec_step_any], and
   [wp_loop_cycle] under it) closes both.  The three wrappers are stated
   and admitted on top of it; each carries the list of assembly steps it
   still owes.

   ONE INTERFACE NARROWING, recorded because a call site depends on it:
   [wp_instr_s_config_regime] returns cur_privilege at Supervisor.  A leaf
   that WRITES cur_privilege (SRET) needs the privilege-parametric S tower
   -- [WpInstrConfig.mc_rs]'s S twin -- which is not built here.          *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import SmodeCore.
Require Import KptPt UserBits.
Require Import KptGhost.   (* kptN: named in the mask premise *)
Require Import KptShare.   (* tlb_res_pt: the shared-table residue *)
Require Import KptGoodb.  (* the fetch probes' footprint certificates *)
Require Import SRegime.
Require Import HartSwp HartLift HartSpan HartSpanChar HartSFrame.
Require Import HartEvents HartRegNode HartMCycle HartStepAny HartRunGen.
Require Import HartMFetch HartSTrans PtTreeAdue.
Require Import WpDecodeBridge WpIntrCore CommonWalk HartGoodb.
Require Import WpInstrRun WpSFrames.
Require Import SmodePte RiscvExtras.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* every non-tlb register survives a translation step (the absorption
   theorem's sregs shape: unchanged, or exactly one tlb register_set) *)
Lemma pt_regs_preserved (rs rs' : regstate) :
  (rs' = rs \/ exists tv, rs' = register_set tlb tv rs)%type ->
  forall rr, register_beq rr tlb = false ->
    register_lookup rr rs' = register_lookup rr rs.
Proof.
  intros [-> | (tv & ->)] rr Hrr; [reflexivity |].
  apply (irrelevant_register_set rr tlb rs tv Hrr).
Qed.

(* Sv39 canonicality from the positive-half bound alone -- the
   [addr_is_ram]-free analogue of [ram_canonical] (a va with [uint va < 2^38]
   sign-extends its low 39 bits back to itself).  The S-mode FETCH engine needs
   this at the virtual pc, which the HARD GUARD forbids assuming is a RAM
   (identity) address: the bound comes from the code window's OWN [uint pc <
   2^38] conjunct ([text_canonical]), never from a static/identity premise. *)
Lemma lo_canonical (a : mword 64) :
  uint a < 274877906944 ->
  neq_vec (bits_of_virtaddr (Virtaddr a))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0)) = false.
Proof.
  intros Hlt. pose proof Hlt as Hlt'. rewrite uint_unsigned in Hlt'.
  cbn [bits_of_virtaddr].
  unfold neq_vec. rewrite negb_false_iff. unfold eq_vec.
  rewrite MachineWord.MachineWord.eqb_true_iff. apply bv_eq. symmetry.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec to_word get_word
       MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned. unfold bv_signed.
  rewrite (lo_subrange_unsigned a Hlt).
  pose proof (bv_unsigned_in_range 64 a) as Hr.
  assert (Emod : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite Emod in Hr.
  assert (Hsw : bv_swrap (39 - 0) (uint a) = uint a).
  { apply bv_swrap_small. rewrite uint_unsigned.
    assert (bv_half_modulus (39 - 0) = 274877906944) as -> by (vm_compute; reflexivity).
    split; [ transitivity 0%Z; [ vm_compute; discriminate | exact (proj1 Hr) ] | exact Hlt' ]. }
  rewrite Hsw. rewrite uint_unsigned.
  apply bv_wrap_small. rewrite Emod. exact Hr.
Qed.

(* [N.of_nat]-guarded window bound to a plain [nat] bound (the model's
   mem-read premises are [(N.of_nat j < N)%N]; [lia] is unavailable under the
   bitvector zify hook this file loads). *)
Lemma nat_lt_of_N (j len : nat) : (N.of_nat j < N.of_nat len)%N -> (j < len)%nat.
Proof.
  unfold N.lt. rewrite <- Nat2N.inj_compare. apply Nat.compare_lt_iff.
Qed.

(* the whitelisted reduction the checked-read chain is stepped with
   ([PtTreeAdue]'s [scmr_cbn]/[scmr_read], which are Local there). *)
Local Ltac spt_cbn :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR
     Defs.returnR Defs.read_reg Defs.early_return Defs.throw
     Defs.assert_exp Defs.assert_exp'
     Defs.and_boolM Defs.or_boolM andb orb negb not
     check_pma_with_pmp_priority pmaCheck mag_pma_check
     is_mag_applicable_access __id
     get_config_rvfi plat_have_clint plat_have_sig].

Local Ltac spt_read :=
  rewrite hfrun_read;
  match goal with
  | |- context [ bool_decide ?P ] =>
      rewrite (bool_decide_eq_true_2 P ltac:(assumption))
  end.

Local Ltac spt_srs :=
  by rewrite ?s_rs_PC ?s_rs_nPC ?s_rs_ms ?s_rs_mi ?s_rs_cy ?s_rs_ti
     ?s_rs_ip ?s_rs_tlb ?s_rs_priv ?s_rs_mst ?s_rs_hart ?s_rs_pcfg
     ?s_rs_paddr ?s_rs_mc ?s_rs_micfg ?s_rs_misa ?s_rs_sec ?s_rs_pma
     ?s_rs_htif ?s_rs_elp ?s_rs_senv ?s_rs_satp ?s_rs_mie ?s_rs_mdl
     ?s_rs_menv.

Local Ltac rg_glue :=
  cbn beta iota zeta delta
    [Defs.returnm returnM returnR Defs.returnR andb orb negb not
     Instances.generic_eq Instances.generic_neq get_config_rvfi
     get_config_print_instr].

(* the misalignment tests' spelling, as [HartMFetch] / [HartSTrans] use it *)
Local Notation zerobit :=
  (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 1)
     (BinaryString.Raw.to_N "0" 0%N)).

Local Ltac spt_mf :=
  cbn beta iota zeta delta [get_config_rvfi ext_fetch_check_pc].

Local Lemma spt_cE_Ziccif : currentlyEnabled Ext_Ziccif = returnM true.
Proof. reflexivity. Qed.

Section SmodeCorePt.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* =================================================================== *)
  (* WINDOW COLLAPSE (uniform-claims): a non-straddling [len]-byte chunk   *)
  (* of a persistent [↦ₓ□] instruction window, based at [b] (the window    *)
  (* itself is based at [pc], the chunk occupying window offsets           *)
  (* [lo..lo+len)).  Every byte carries its OWN mapping claim at its own    *)
  (* [svpn]; since the chunk does not cross a page ([off + len <= 4096]),   *)
  (* those svpns all coincide with [svpn_of b] ([svpn_of_pa_add]) so a      *)
  (* single [kmap_at_agree] pins EVERY byte's claim ppn to the base ppn.    *)
  (* The physical read then lands at [pa_add (pa_of ppn b) j] throughout    *)
  (* ([pa_of_pa_add]) -- an ARBITRARY translated pa, no identity premise.   *)
  (* =================================================================== *)
  (* TIER-GENERIC (sp-migration K5), exactly as [s_mem_chunk] below: the
     collapse is about the CLAIM each byte carries, never about its tier
     pin, so one lemma serves a KT0 (identity image) and a KT1
     (TRAMPOLINE-va) window with the statement unchanged. *)
  Lemma s_fetch_chunk `{KTR : !CurKtier} (σ' : mstate) (pc b : mword 64)
      (lo len N : nat) (g : nat -> bv 8) (ppn : mword 44) :
    (lo + len <= N)%nat ->
    (0 < len)%nat ->
    (forall k : nat, pa_add pc (lo + k)%nat = pa_add b k) ->
    (bv_unsigned (subrange_vec_dec b 11 0) + Z.of_nat len <= 4096)%Z ->
    (uint b < 274877906944)%Z ->
    gen_heap_interp σ'.(mem) -∗
    kmap_at (svpn_of b) ppn KP_rx -∗
    ([∗ list] j ∈ seq 0 N, (pa_add pc j) ↦ₓ□ g j) -∗
    ⌜(forall j : nat, (N.of_nat j < N.of_nat len)%N ->
         σ'.(mem) !! pa_add (pa_of ppn b) j = Some (g (lo + j)%nat))
     /\ addr_is_ram (pa_of ppn b)
     /\ addr_is_ram (pa_add (pa_of ppn b) (len - 1))⌝.
  Proof.
    intros Hlon Hlen Hbase Hoff Hcan.
    iIntros "Hmem #Hk #Hbytes".
    iAssert (⌜forall j : nat, (N.of_nat j < N.of_nat len)%N ->
               σ'.(mem) !! pa_add (pa_of ppn b) j = Some (g (lo + j)%nat)⌝)%I as %Hbf.
    { iIntros (j HjN). assert (Hj : (j < len)%nat) by (apply nat_lt_of_N; exact HjN).
      assert (Hoffj : (bv_unsigned (subrange_vec_dec b 11 0) + Z.of_nat j < 4096)%Z).
      { eapply Z.lt_le_trans; [| exact Hoff].
        apply Z.add_lt_mono_l. apply Nat2Z.inj_lt. exact Hj. }
      iDestruct (big_sepL_lookup _ _ (lo + j)%nat (lo + j)%nat with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iEval (rewrite (Hbase j)) in "Hbj".
      iDestruct (text_valid with "Hmem Hbj") as (ppnj) "(#Hkj & _ & %Hlk)".
      iEval (rewrite (svpn_of_pa_add b j Hcan Hoffj)) in "Hkj".
      iDestruct (kmap_at_agree with "Hkj Hk") as %[Heqp _].
      rewrite Heqp in Hlk.
      rewrite (pa_of_pa_add ppn b j Hcan Hoffj) in Hlk.
      iPureIntro. exact Hlk. }
    iAssert (⌜addr_is_ram (pa_of ppn b)⌝)%I as %Hram0.
    { iDestruct (big_sepL_lookup _ _ (lo + 0)%nat (lo + 0)%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iEval (rewrite (Hbase 0%nat) pa_add_0) in "Hb0".
      iDestruct (code_ram with "Hb0") as (ppn0) "[#Hk0 %Hr]".
      iDestruct (kmap_at_agree with "Hk0 Hk") as %[Heqp _].
      rewrite Heqp in Hr. iPureIntro. exact Hr. }
    iAssert (⌜addr_is_ram (pa_add (pa_of ppn b) (len - 1))⌝)%I as %Hramh.
    { assert (Hoffh : (bv_unsigned (subrange_vec_dec b 11 0) + Z.of_nat (len - 1) < 4096)%Z).
      { eapply Z.lt_le_trans; [| exact Hoff].
        apply Z.add_lt_mono_l. apply Nat2Z.inj_lt. lia. }
      iDestruct (big_sepL_lookup _ _ (lo + (len - 1))%nat (lo + (len - 1))%nat with "Hbytes") as "Hbh".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iEval (rewrite (Hbase (len - 1)%nat)) in "Hbh".
      iDestruct (code_ram with "Hbh") as (ppnh) "[#Hkh %Hr]".
      iEval (rewrite (svpn_of_pa_add b (len - 1)%nat Hcan Hoffh)) in "Hkh".
      iDestruct (kmap_at_agree with "Hkh Hk") as %[Heqp _].
      rewrite Heqp in Hr.
      rewrite (pa_of_pa_add ppn b (len - 1)%nat Hcan Hoffh) in Hr.
      iPureIntro. exact Hr. }
    iPureIntro. split; [exact Hbf | split; [exact Hram0 | exact Hramh]].
  Qed.

  (* =================================================================== *)
  (* WINDOW COLLAPSE, the KP_rw (DATA) analogue of [s_fetch_chunk]: a      *)
  (* non-straddling [len]-byte chunk of a [↦ₘ{dq}] window (window based    *)
  (* at [pc], chunk at window offsets [lo..lo+len), each byte carrying its  *)
  (* OWN KP_rw claim).  Since the chunk does not cross a page every byte's  *)
  (* svpn coincides with [svpn_of b] ([svpn_of_pa_add]) so a single         *)
  (* [kmap_at_agree] pins every byte's ppn to the base ppn, and the read    *)
  (* lands at [pa_add (pa_of ppn b) j] ([pa_of_pa_add]) -- an ARBITRARY     *)
  (* translated pa, no identity premise.  The window is NON-persistent      *)
  (* ([dq]), so the per-index heap+kdata facts are gathered in ONE pass     *)
  (* (each byte used once) into a [∀]-fact, then read off at 0 and [len-1]  *)
  (* for the region endpoints.                                             *)
  (* =================================================================== *)
  (* TIER-GENERIC (sp-migration phase D): the collapse is about the CLAIM
     each byte carries, never about its tier pin, so the [CurKtier] binder
     makes one lemma serve a KT0 and a KT1 window with the statement
     unchanged.  Ambient callers keep resolving it at the KT0 default. *)
  Lemma s_mem_chunk `{KTR : !CurKtier} (σ' : mstate) (pc b : mword 64)
      (lo len N : nat) (g : nat -> bv 8) (ppn : mword 44) (dq : dfrac) :
    (lo + len <= N)%nat ->
    (0 < len)%nat ->
    (forall k : nat, pa_add pc (lo + k)%nat = pa_add b k) ->
    (bv_unsigned (subrange_vec_dec b 11 0) + Z.of_nat len <= 4096)%Z ->
    (uint b < 274877906944)%Z ->
    gen_heap_interp σ'.(mem) -∗
    kmap_at (svpn_of b) ppn KP_rw -∗
    ([∗ list] j ∈ seq 0 N, mem_pointsto (pa_add pc j) dq (g j)) -∗
    ⌜(forall j : nat, (N.of_nat j < N.of_nat len)%N ->
         σ'.(mem) !! pa_add (pa_of ppn b) j = Some (g (lo + j)%nat))
     /\ addr_is_ram (pa_of ppn b)
     /\ addr_is_ram (pa_add (pa_of ppn b) (len - 1))
     /\ addr_is_ram (pa_of ppn b)⌝.
  Proof.
    intros Hlon Hlen Hbase Hoff Hcan.
    iIntros "Hmem #Hk Hbytes".
    iAssert (⌜forall j : nat, (j < len)%nat ->
               σ'.(mem) !! pa_add (pa_of ppn b) j = Some (g (lo + j)%nat)
               /\ addr_is_ram (pa_add (pa_of ppn b) j)⌝)%I as %Hall.
    { iIntros (j Hj).
      assert (Hoffj : (bv_unsigned (subrange_vec_dec b 11 0) + Z.of_nat j < 4096)%Z).
      { eapply Z.lt_le_trans; [| exact Hoff].
        apply Z.add_lt_mono_l. apply Nat2Z.inj_lt. exact Hj. }
      iDestruct (big_sepL_lookup _ _ (lo + j)%nat (lo + j)%nat with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iEval (rewrite (Hbase j)) in "Hbj".
      iDestruct (mem_valid with "Hmem Hbj") as (ppnj) "(#Hkj & %Hkd & %Hlk)".
      iEval (rewrite (svpn_of_pa_add b j Hcan Hoffj)) in "Hkj".
      iDestruct (kmap_at_agree with "Hkj Hk") as %[Heqp _].
      rewrite Heqp in Hlk. rewrite Heqp in Hkd.
      rewrite (pa_of_pa_add ppn b j Hcan Hoffj) in Hlk.
      rewrite (pa_of_pa_add ppn b j Hcan Hoffj) in Hkd.
      iPureIntro. split; [exact Hlk | exact Hkd]. }
    iPureIntro.
    assert (Hram0 : addr_is_ram (pa_of ppn b)).
    { pose proof (proj2 (Hall 0%nat Hlen)) as H0. rewrite pa_add_0 in H0. exact H0. }
    split; [| split; [| split]].
    - intros j HjN. exact (proj1 (Hall j (nat_lt_of_N j len HjN))).
    - exact Hram0.
    - exact (proj2 (Hall (len - 1)%nat ltac:(lia))).
    - exact Hram0.
  Qed.

  (* =================================================================== *)
  (* CLAIM-KEYED VA WINDOW WRITE (uniform-claims).  The write analogue of  *)
  (* [s_mem_chunk]: given the base KP_rw claim of a non-straddling VA byte  *)
  (* window (each byte owning its OWN mapped physical byte), overwrite the  *)
  (* physical bytes at [pa_add (pa_of ppn va) j] -- the actual translated   *)
  (* pas -- in step with the heap update, refolding the window at the new   *)
  (* values.  Width-agnostic (over the index list + old/new byte fns).     *)
  (* =================================================================== *)
  (* TIER-PRESERVING and TIER-GENERIC (sp-migration phase D): the window
     goes back in at the tier it came in at -- the re-mint below re-uses
     the pin it destructured ([Hid]) rather than re-establishing one -- so
     the [CurKtier] binder costs the statement nothing. *)
  Lemma s_win_write `{KTR : !CurKtier} (va : mword 64) (ppn : mword 44) (gold gnew : nat -> bv 8) :
    (uint va < 274877906944)%Z ->
    forall (l : list nat),
    Forall (fun j => (bv_unsigned (subrange_vec_dec va 11 0) + Z.of_nat j < 4096)%Z) l ->
    forall (mm : _),
    kmap_at (svpn_of va) ppn KP_rw -∗
    gen_heap_interp (hG:=riscv_memGS) mm -∗
    ([∗ list] j ∈ l, (pa_add va j) ↦ₘ (gold j)) ==∗
    gen_heap_interp (hG:=riscv_memGS) (foldr (fun j acc => <[pa_add (pa_of ppn va) j := gnew j]> acc) mm l)
      ∗ ([∗ list] j ∈ l, (pa_add va j) ↦ₘ (gnew j)).
  Proof.
    intros Hcan l. induction l as [|x xs IH]; intros Hall mm.
    - iIntros "_ Hm _". iModIntro. simpl. iFrame.
    - apply Forall_cons_1 in Hall as [Hx Hxs].
      iIntros "#Hk Hm [Ha Hrest]".
      iMod (IH Hxs mm with "Hk Hm Hrest") as "[Hm Hrest]".
      iAssert (kmap_at (svpn_of (pa_add va x)) ppn KP_rw)%I as "#Hkx".
      { rewrite (svpn_of_pa_add va x Hcan Hx). iExact "Hk". }
      iDestruct (mem_pointsto_pin (pa_add va x) (DfracOwn 1) (gold x) ppn with "Hkx Ha")
        as "(%Hc & %Hd & %Hid & Hp & _)".
      simpl foldr.
      rewrite -(pa_of_pa_add ppn va x Hcan Hx).
      iMod (gen_heap_update _ (pa_of ppn (pa_add va x)) (gold x) (gnew x) with "Hm Hp") as "[Hm Hp]".
      iModIntro. iFrame "Hm". simpl. iFrame "Hrest".
      iExists ppn. iFrame "Hkx Hp". iPureIntro.
      split; [exact Hc | split; [exact Hd | exact Hid]].
  Qed.

  (* 8-byte claim-keyed write: the VA replacement for the (now physical)
     [word_pointsto_write], writing at [pa_of ppn va]. *)
  Lemma word_pointsto_write_c `{KTR : !CurKtier} (mm : _) (va : mword 64)
      (ppn : mword 44) (vold vnew : bv 64) :
    (uint va < 274877906944)%Z ->
    (bv_unsigned (subrange_vec_dec va 11 0) + 8 <= 4096)%Z ->
    kmap_at (svpn_of va) ppn KP_rw -∗
    gen_heap_interp (hG:=riscv_memGS) mm -∗ va ↦₈ vold ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mm (pa_of ppn va) 8 vnew) ∗ va ↦₈ vnew.
  Proof.
    intros Hcan Hoff. iIntros "#Hk Hm Hw".
    iDestruct (word_pointsto_aligned_p with "Hw") as %Hal.
    iDestruct (word_pointsto_bytes with "Hw") as "Hb".
    iMod (s_win_write va ppn (nth_byte vold) (nth_byte vnew) Hcan (seq 0 8)
            ltac:(apply Forall_forall; intros j Hj; apply elem_of_list_In, elem_of_seq in Hj;
                  destruct Hj as [_ Hj8]; pose proof (Nat2Z.inj_lt j 8) as Hnz;
                  change (Z.of_nat 8) with 8%Z in Hnz; lia)
            mm with "Hk Hm Hb") as "[Hm Hb]".
    iModIntro. unfold write_bytes. change (N.to_nat 8) with 8%nat. iFrame "Hm".
    iApply word_pointsto_intro; [exact Hal | iExact "Hb"].
  Qed.

  (* 4-byte claim-keyed write (the width-4 analogue). *)
  Lemma word4_pointsto_write_c `{KTR : !CurKtier} (mm : _) (va : mword 64)
      (ppn : mword 44) (vold vnew : bv 32) :
    (uint va < 274877906944)%Z ->
    (bv_unsigned (subrange_vec_dec va 11 0) + 4 <= 4096)%Z ->
    kmap_at (svpn_of va) ppn KP_rw -∗
    gen_heap_interp (hG:=riscv_memGS) mm -∗ va ↦₄ vold ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mm (pa_of ppn va) 4 vnew) ∗ va ↦₄ vnew.
  Proof.
    intros Hcan Hoff. iIntros "#Hk Hm Hw".
    iDestruct (word4_pointsto_aligned_p with "Hw") as %Hal.
    iDestruct (word4_pointsto_bytes with "Hw") as "Hb".
    iMod (s_win_write va ppn (nth_byte vold) (nth_byte vnew) Hcan (seq 0 4)
            ltac:(apply Forall_forall; intros j Hj; apply elem_of_list_In, elem_of_seq in Hj;
                  destruct Hj as [_ Hj4]; pose proof (Nat2Z.inj_lt j 4) as Hnz;
                  change (Z.of_nat 4) with 4%Z in Hnz; lia)
            mm with "Hk Hm Hb") as "[Hm Hb]".
    iModIntro. unfold write_bytes. change (N.to_nat 4) with 4%nat. iFrame "Hm".
    iApply word4_pointsto_intro; [exact Hal | iExact "Hb"].
  Qed.

  (* =================================================================== *)
  (* The unified S-mode fetch over [tlb_inv_pt], as a bupd.  Pure         *)
  (* premises are the σ-level config lookups (the engine extracts them    *)
  (* from [smode_config]/[hw_config]'s cells); everything the walk needs  *)
  (* rides inside [tlb_inv_pt].                                           *)
  (* =================================================================== *)
  (* TIER-INDEXED (sp-migration K5).  The window's tier is the ambient
     [CurKtier]; the reconciliation with the hardware goes through the ONE
     generic dispatcher [SRegime.sr_absorb_ktier] instead of the KT0-only
     [sr_absorb]+[sr_adm_id] pair, so BOTH arms are this one proof:

       KT0 -- the window byte's pin IS the identity, fed to [sr_adm];
       KT1 -- there is no pin, and admissibility comes from the regime's
              all-claims witness, which the caller supplies as
              [sr_ktier_wit R cur_ktier].

     The witness is PERSISTENT and free at KT0 ([sr_ktier_wit_KT0]) and at
     the shared-kernel-table regime at every tier
     ([sr_ktier_wit_kpt_share]), so every caller in the tree discharges it
     in one line and no function contract grows anything. *)
  Lemma s_regime_fetch `{KTR : !CurKtier} (R : s_regime) (σ : mstate)
      (pc : mword 64) (r : FetchResult) (E : coPset) :
    ↑kptN ⊆ E ->
    register_lookup PC σ.(sregs) = pc ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    sr_ktier_wit R cur_ktier -∗
    mstate_interp σ -∗
    sr_inv R -∗
    instr_bytes pc r ={E}=∗
    ∃ σf : mstate,
      ⌜ exec (fetch tt) σ = Some (r, σf) ⌝ ∗
      ⌜ σf.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ forall rr, register_beq rr tlb = false ->
          register_lookup rr σf.(sregs) = register_lookup rr σ.(sregs) ⌝ ∗
      mstate_interp σf ∗
      sr_inv R.
  Proof.
    intros HE Lpc Lpriv Lmisa Lmenv Lhtif LSXL Lpma.
    iIntros "#Hwit [Hreg [Hmem Hdev]] Hinv Hbytes".
    assert (HmisaC : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    iEval (rewrite /instr_bytes) in "Hbytes".
    iDestruct "Hbytes" as "[%H2al Hbytes]".
    destruct r as [e | w | h | erx].
    - (* F_Ext_Error *) done.
    - (* F_Base w *)
      iDestruct "Hbytes" as "[%HnotRVC #Hbytes]".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* 4-aligned: ONE chunk, one 4-byte read at [pa_of ppn pc] *)
        (* claim + canonicality from byte 0's own [↦ₓ□] *)
        iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "#Hb0".
        { rewrite lookup_seq_lt; [reflexivity | lia]. }
        iEval (rewrite pa_add_0) in "Hb0".
        iDestruct (code_text with "Hb0") as (ppn) "(#Hk & %Htext0 & %Hid)".
        iDestruct (text_canonical with "Hb0") as %Hcan.
        pose proof (off4_bound pc Hal) as Hoff. rewrite (uint_unsigned_n _) in Hoff.
        (* present the claim to the claim-keyed absorb: translate pc = pa_of ppn pc *)
        unshelve iMod (sr_absorb_ktier R cur_ktier cur_ktier (InstructionFetch tt) pc (pa_of ppn pc) ppn KP_rx σ _
                (or_introl eq_refl) eq_refl (lo_canonical pc Hcan) ltac:(reflexivity)
                Lmisa Lmenv Lhtif Lpriv LSXL
                (exec_effectivePrivilege_fetch _ _ σ) (exec_is_shadow_stack_fetch σ)
                Lpma Hid _ with "Hwit Hk Hreg Hmem Hinv")
          as (s1) "(%Htr1 & %Hmdev1 & %Hsh1 & %Hgr1 & Hreg & Hmem & Hinv)"; [solve_ndisj |].
        pose proof (pt_regs_preserved _ _ Hsh1) as Hpres1.
        iDestruct (s_fetch_chunk s1 pc pc 0 4 4 (nth_byte w) ppn
                     ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                     with "Hmem Hk Hbytes") as %(Hbf & Hram0 & Hram3).
        pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
        destruct (pma_all_ram Lpma (pa_of ppn pc) 4
                   (pma_access_ram _ _ _ Hram0 Hram3 (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl))
          as (region & Hmatch0 & Hexec0 & _ & _).
        destruct Hgr1 as (HA & Hord & HX & HW & HR & Hcov).
        assert (Hfetch : exec (fetch tt) σ = Some (F_Base w, s1)).
        { apply (exec_fetch_F_Base_4_S_gen pc (pa_of ppn pc) w σ s1 region Lpc Hal Htr1).
          - exact HA.
          - exact Hord.
          - exact (ram_fetch_pmp (pa_of ppn pc) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) 4 3
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hram0 Hram3 Hcov).
          - exact HX.
          - rewrite (Hpres1 pma_regions ltac:(vm_compute; reflexivity)). exact Hmatch0.
          - exact (pa4_aligned ppn pc Hal).
          - exact Hexec0.
          - apply within_clint_false; [exact Hnc | lia].
          - apply within_sig_false; [exact Hns | lia].
          - apply within_htif_false.
            rewrite (Hpres1 htif_tohost_base ltac:(vm_compute; reflexivity)). exact Lhtif.
          - apply addr_is_ram_not_dev. exact Hram0.
          - exact Hbf.
          - rewrite (Hpres1 cur_privilege ltac:(vm_compute; reflexivity)). exact Lpriv.
          - exact HnotRVC. }
        iModIntro. iExists s1.
        iSplit; [iPureIntro; exact Hfetch |].
        iSplit; [iPureIntro; exact Hmdev1 |].
        iSplit; [iPureIntro; exact Hpres1 |].
        rewrite /mstate_interp. rewrite Hmdev1.
        iFrame "Hreg Hmem Hdev Hinv".
      + (* 2-aligned but NOT 4-aligned: TWO chunks across TWO pages *)
        destruct (align2_not4_facts pc H2al Hal) as (_ & Hbit0 & Hbit1).
        assert (Hvah2 : is_aligned_vaddr (Virtaddr (add_vec_int pc 2)) 2 = true).
        { pose proof (align2_plus2 pc H2al) as Hh. rewrite fetch_pa_id in Hh. exact Hh. }
        assert (HbaseH : forall k : nat, pa_add pc (2 + k)%nat = pa_add (add_vec_int pc 2) k).
        { intros k. unfold pa_add. rewrite avi_assoc. f_equal. lia. }
        (* low claim from byte 0, high claim from byte 2 (its own [svpn]) *)
        iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "#Hb0".
        { rewrite lookup_seq_lt; [reflexivity | lia]. }
        iEval (rewrite pa_add_0) in "Hb0".
        iDestruct (code_text with "Hb0") as (ppnl) "(#Hkl & %Htextl & %Hidl)".
        iDestruct (text_canonical with "Hb0") as %Hcanl.
        pose proof (off_bound_div pc 2 ltac:(lia) ltac:(exists 2048; lia) H2al) as Hoffl. rewrite (uint_unsigned_n _) in Hoffl.
        iDestruct (big_sepL_lookup _ _ 2%nat 2%nat with "Hbytes") as "#Hb2".
        { rewrite lookup_seq_lt; [reflexivity | lia]. }
        iDestruct (code_text with "Hb2") as (ppnh) "(#Hkh & %Htexth & %Hidh)".
        iDestruct (text_canonical with "Hb2") as %Hcanh.
        pose proof (off_bound_div (add_vec_int pc 2) 2 ltac:(lia) ltac:(exists 2048; lia) Hvah2) as Hoffh. rewrite (uint_unsigned_n _) in Hoffh.
        (* absorb the LOW translation: pc -> pa_of ppnl pc, at [σ -> s1] *)
        unshelve iMod (sr_absorb_ktier R cur_ktier cur_ktier (InstructionFetch tt) pc (pa_of ppnl pc) ppnl KP_rx σ _
                (or_introl eq_refl) eq_refl (lo_canonical pc Hcanl) ltac:(reflexivity)
                Lmisa Lmenv Lhtif Lpriv LSXL
                (exec_effectivePrivilege_fetch _ _ σ) (exec_is_shadow_stack_fetch σ)
                Lpma Hidl _ with "Hwit Hkl Hreg Hmem Hinv")
          as (s1) "(%Htr1 & %Hmdev1 & %Hsh1 & %Hgr1 & Hreg & Hmem & Hinv)"; [solve_ndisj |].
        pose proof (pt_regs_preserved _ _ Hsh1) as Hpres1.
        assert (L1pc : register_lookup PC s1.(sregs) = pc)
          by (rewrite (Hpres1 PC ltac:(vm_compute; reflexivity)); exact Lpc).
        assert (L1priv : register_lookup cur_privilege s1.(sregs) = Supervisor)
          by (rewrite (Hpres1 cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv).
        assert (L1misa : register_lookup misa s1.(sregs) = MISA_C)
          by (rewrite (Hpres1 misa ltac:(vm_compute; reflexivity)); exact Lmisa).
        assert (L1menv : register_lookup menvcfg s1.(sregs) = MENVCFG_S)
          by (rewrite (Hpres1 menvcfg ltac:(vm_compute; reflexivity)); exact Lmenv).
        assert (L1htif : register_lookup htif_tohost_base s1.(sregs) = None)
          by (rewrite (Hpres1 htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif).
        assert (L1SXL : _get_Mstatus_SXL (register_lookup mstatus s1.(sregs)) = 'b"10")
          by (rewrite (Hpres1 mstatus ltac:(vm_compute; reflexivity)); exact LSXL).
        assert (L1pma : pma_allows_all (register_lookup pma_regions s1.(sregs)))
          by (rewrite (Hpres1 pma_regions ltac:(vm_compute; reflexivity)); exact Lpma).
        (* low byte + ram facts, read at [s1] (before the high step may move memory) *)
        iDestruct (s_fetch_chunk s1 pc pc 0 2 4 (nth_byte w) ppnl
                     ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoffl Hcanl
                     with "Hmem Hkl Hbytes") as %(HbfL & Hraml0 & Hraml1).
        (* absorb the HIGH translation: pc+2 -> pa_of ppnh (pc+2), at [s1 -> s2] *)
        unshelve iMod (sr_absorb_ktier R cur_ktier cur_ktier (InstructionFetch tt) (add_vec_int pc 2) (pa_of ppnh (add_vec_int pc 2)) ppnh KP_rx s1 _
                (or_introl eq_refl) eq_refl (lo_canonical (add_vec_int pc 2) Hcanh) ltac:(reflexivity)
                L1misa L1menv L1htif L1priv L1SXL
                (exec_effectivePrivilege_fetch _ _ s1) (exec_is_shadow_stack_fetch s1)
                L1pma Hidh _ with "Hwit Hkh Hreg Hmem Hinv")
          as (s2) "(%Htr2 & %Hmdev2 & %Hsh2 & %Hgr2 & Hreg & Hmem & Hinv)"; [solve_ndisj |].
        pose proof (pt_regs_preserved _ _ Hsh2) as Hpres2.
        assert (Hpres12 : forall rr, register_beq rr tlb = false ->
                  register_lookup rr s2.(sregs) = register_lookup rr σ.(sregs)).
        { intros rr Hrr. rewrite (Hpres2 rr Hrr). exact (Hpres1 rr Hrr). }
        iDestruct (s_fetch_chunk s2 pc (add_vec_int pc 2) 2 2 4 (nth_byte w) ppnh
                     ltac:(lia) ltac:(lia) HbaseH Hoffh Hcanh
                     with "Hmem Hkh Hbytes") as %(HbfH & Hramh0 & Hramh1).
        (* re-slice the raw window bytes into the low/high 16-bit halves *)
        assert (HblS1 : forall j : nat, (N.of_nat j < 2)%N ->
                  s1.(mem) !! (pa_add (pa_of ppnl pc) j)
                  = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)).
        { intros j Hj. rewrite nth_byte_subrange_lo; [| exact Hj]. apply HbfL; exact Hj. }
        assert (HbhS2 : forall j : nat, (N.of_nat j < 2)%N ->
                  s2.(mem) !! (pa_add (pa_of ppnh (add_vec_int pc 2)) j)
                  = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j)).
        { intros j Hj. rewrite nth_byte_subrange_hi; [| exact Hj]. apply HbfH; exact Hj. }
        pose proof (addr_is_ram_not_in_clint _ Hraml0) as Hncl.
        pose proof (addr_is_ram_not_in_sig _ Hraml0) as Hnsl.
        pose proof (addr_is_ram_not_in_clint _ Hramh0) as Hnch.
        pose proof (addr_is_ram_not_in_sig _ Hramh0) as Hnsh.
        destruct (pma_all_ram Lpma (pa_of ppnl pc) 2
                   (pma_access_ram _ _ _ Hraml0 Hraml1 (pma_width_ok 2 eq_refl eq_refl) eq_refl eq_refl))
          as (regl & Hml0 & Hxl & _ & _).
        destruct (pma_all_ram Lpma (pa_of ppnh (add_vec_int pc 2)) 2
                   (pma_access_ram _ _ _ Hramh0 Hramh1 (pma_width_ok 2 eq_refl eq_refl) eq_refl eq_refl))
          as (regh & Hmh0 & Hxh & _ & _).
        destruct Hgr1 as (HA1 & Hord1 & HX1 & HW1 & HR1 & Hcov1).
        destruct Hgr2 as (HA2 & Hord2 & HX2 & HW2 & HR2 & Hcov2).
        assert (Hfetch : exec (fetch tt) σ = Some (F_Base w, s2)).
        { apply (exec_fetch_F_Base_2_S_gen pc (pa_of ppnl pc) (pa_of ppnh (add_vec_int pc 2))
                   w σ s1 s2 regl regh
                   Lpc L1pc HmisaC Hbit0 Hbit1 Hal Htr1 Htr2).
          - exact HA1.
          - exact Hord1.
          - exact (ram_fetch_pmp (pa_of ppnl pc) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) 2 1
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hraml0 Hraml1 Hcov1).
          - exact HX1.
          - rewrite (Hpres1 pma_regions ltac:(vm_compute; reflexivity)). exact Hml0.
          - exact (pa_aligned_div ppnl pc 2 ltac:(lia) ltac:(exists 2048; lia) H2al).
          - exact Hxl.
          - apply within_clint_false; [exact Hncl | lia].
          - apply within_sig_false; [exact Hnsl | lia].
          - apply within_htif_false. exact L1htif.
          - apply addr_is_ram_not_dev. exact Hraml0.
          - exact HblS1.
          - exact L1priv.
          - exact HA2.
          - exact Hord2.
          - exact (ram_fetch_pmp (pa_of ppnh (add_vec_int pc 2)) (vec_access_dec (register_lookup pmpaddr_n s2.(sregs)) 0) 2 1
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hramh0 Hramh1 Hcov2).
          - exact HX2.
          - rewrite (Hpres12 pma_regions ltac:(vm_compute; reflexivity)). exact Hmh0.
          - exact (pa_aligned_div ppnh (add_vec_int pc 2) 2 ltac:(lia) ltac:(exists 2048; lia) Hvah2).
          - exact Hxh.
          - apply within_clint_false; [exact Hnch | lia].
          - apply within_sig_false; [exact Hnsh | lia].
          - apply within_htif_false.
            rewrite (Hpres12 htif_tohost_base ltac:(vm_compute; reflexivity)). exact Lhtif.
          - apply addr_is_ram_not_dev. exact Hramh0.
          - exact HbhS2.
          - rewrite (Hpres12 cur_privilege ltac:(vm_compute; reflexivity)). exact Lpriv.
          - exact HnotRVC.
          - exact (concat_subranges_id w). }
        iModIntro. iExists s2.
        iSplit; [iPureIntro; exact Hfetch |].
        iSplit; [iPureIntro; rewrite Hmdev2; exact Hmdev1 |].
        iSplit; [iPureIntro; exact Hpres12 |].
        rewrite /mstate_interp. rewrite Hmdev2 Hmdev1.
        iFrame "Hreg Hmem Hdev Hinv".
    - (* F_RVC h *)
      iDestruct "Hbytes" as "[%HisRVC Hbytes]".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* 4-aligned window: one chunk, one 4-byte read *)
        iDestruct "Hbytes" as (w) "[%Hsub #Hbytes]".
        iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "#Hb0".
        { rewrite lookup_seq_lt; [reflexivity | lia]. }
        iEval (rewrite pa_add_0) in "Hb0".
        iDestruct (code_text with "Hb0") as (ppn) "(#Hk & %Htext0 & %Hid)".
        iDestruct (text_canonical with "Hb0") as %Hcan.
        pose proof (off4_bound pc Hal) as Hoff. rewrite (uint_unsigned_n _) in Hoff.
        unshelve iMod (sr_absorb_ktier R cur_ktier cur_ktier (InstructionFetch tt) pc (pa_of ppn pc) ppn KP_rx σ _
                (or_introl eq_refl) eq_refl (lo_canonical pc Hcan) ltac:(reflexivity)
                Lmisa Lmenv Lhtif Lpriv LSXL
                (exec_effectivePrivilege_fetch _ _ σ) (exec_is_shadow_stack_fetch σ)
                Lpma Hid _ with "Hwit Hk Hreg Hmem Hinv")
          as (s1) "(%Htr1 & %Hmdev1 & %Hsh1 & %Hgr1 & Hreg & Hmem & Hinv)"; [solve_ndisj |].
        pose proof (pt_regs_preserved _ _ Hsh1) as Hpres1.
        iDestruct (s_fetch_chunk s1 pc pc 0 4 4 (nth_byte w) ppn
                     ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                     with "Hmem Hk Hbytes") as %(Hbf & Hram0 & Hram3).
        pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
        destruct (pma_all_ram Lpma (pa_of ppn pc) 4
                   (pma_access_ram _ _ _ Hram0 Hram3 (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl))
          as (region & Hmatch0 & Hexec0 & _ & _).
        destruct Hgr1 as (HA & Hord & HX & HW & HR & Hcov).
        assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, s1)).
        { rewrite <- Hsub.
          apply (exec_fetch_RVC_4_S_gen pc (pa_of ppn pc) w σ s1 region Lpc Hal Htr1).
          - exact HA.
          - exact Hord.
          - exact (ram_fetch_pmp (pa_of ppn pc) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) 4 3
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hram0 Hram3 Hcov).
          - exact HX.
          - rewrite (Hpres1 pma_regions ltac:(vm_compute; reflexivity)). exact Hmatch0.
          - exact (pa4_aligned ppn pc Hal).
          - exact Hexec0.
          - apply within_clint_false; [exact Hnc | lia].
          - apply within_sig_false; [exact Hns | lia].
          - apply within_htif_false.
            rewrite (Hpres1 htif_tohost_base ltac:(vm_compute; reflexivity)). exact Lhtif.
          - apply addr_is_ram_not_dev. exact Hram0.
          - exact Hbf.
          - rewrite (Hpres1 cur_privilege ltac:(vm_compute; reflexivity)). exact Lpriv.
          - rewrite Hsub. exact HisRVC. }
        iModIntro. iExists s1.
        iSplit; [iPureIntro; exact Hfetch |].
        iSplit; [iPureIntro; exact Hmdev1 |].
        iSplit; [iPureIntro; exact Hpres1 |].
        rewrite /mstate_interp. rewrite Hmdev1.
        iFrame "Hreg Hmem Hdev Hinv".
      + (* 2-aligned: one chunk, one 2-byte read *)
        iDestruct "Hbytes" as "#Hbytes".
        destruct (align2_not4_facts pc H2al Hal) as (_ & Hbit0 & Hbit1).
        iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "#Hb0".
        { rewrite lookup_seq_lt; [reflexivity | lia]. }
        iEval (rewrite pa_add_0) in "Hb0".
        iDestruct (code_text with "Hb0") as (ppn) "(#Hk & %Htext0 & %Hid)".
        iDestruct (text_canonical with "Hb0") as %Hcan.
        pose proof (off_bound_div pc 2 ltac:(lia) ltac:(exists 2048; lia) H2al) as Hoff. rewrite (uint_unsigned_n _) in Hoff.
        unshelve iMod (sr_absorb_ktier R cur_ktier cur_ktier (InstructionFetch tt) pc (pa_of ppn pc) ppn KP_rx σ _
                (or_introl eq_refl) eq_refl (lo_canonical pc Hcan) ltac:(reflexivity)
                Lmisa Lmenv Lhtif Lpriv LSXL
                (exec_effectivePrivilege_fetch _ _ σ) (exec_is_shadow_stack_fetch σ)
                Lpma Hid _ with "Hwit Hk Hreg Hmem Hinv")
          as (s1) "(%Htr1 & %Hmdev1 & %Hsh1 & %Hgr1 & Hreg & Hmem & Hinv)"; [solve_ndisj |].
        pose proof (pt_regs_preserved _ _ Hsh1) as Hpres1.
        iDestruct (s_fetch_chunk s1 pc pc 0 2 2 (nth_byte h) ppn
                     ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                     with "Hmem Hk Hbytes") as %(Hbf & Hram0 & Hram1).
        pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
        destruct (pma_all_ram Lpma (pa_of ppn pc) 2
                   (pma_access_ram _ _ _ Hram0 Hram1 (pma_width_ok 2 eq_refl eq_refl) eq_refl eq_refl))
          as (region & Hmatch0 & Hexec0 & _ & _).
        destruct Hgr1 as (HA & Hord & HX & HW & HR & Hcov).
        assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, s1)).
        { apply (exec_fetch_RVC_2_S_gen pc (pa_of ppn pc) h σ s1 region Lpc HmisaC
                   Hbit0 Hbit1 Hal Htr1).
          - exact HA.
          - exact Hord.
          - exact (ram_fetch_pmp (pa_of ppn pc) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) 2 1
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hram0 Hram1 Hcov).
          - exact HX.
          - rewrite (Hpres1 pma_regions ltac:(vm_compute; reflexivity)). exact Hmatch0.
          - exact (pa_aligned_div ppn pc 2 ltac:(lia) ltac:(exists 2048; lia) H2al).
          - exact Hexec0.
          - apply within_clint_false; [exact Hnc | lia].
          - apply within_sig_false; [exact Hns | lia].
          - apply within_htif_false.
            rewrite (Hpres1 htif_tohost_base ltac:(vm_compute; reflexivity)). exact Lhtif.
          - apply addr_is_ram_not_dev. exact Hram0.
          - exact Hbf.
          - rewrite (Hpres1 cur_privilege ltac:(vm_compute; reflexivity)). exact Lpriv.
          - exact HisRVC. }
        iModIntro. iExists s1.
        iSplit; [iPureIntro; exact Hfetch |].
        iSplit; [iPureIntro; exact Hmdev1 |].
        iSplit; [iPureIntro; exact Hpres1 |].
        rewrite /mstate_interp. rewrite Hmdev1.
        iFrame "Hreg Hmem Hdev Hinv".
    - (* F_Ext_Error *) done.
  Qed.


  (* =================================================================== *)
  (* PART A -- THE S-MODE INSTRUCTION-FETCH MEMORY READ.                  *)
  (*                                                                     *)
  (* [HartMFetch.swp_checked_mem_read_ifetch4] / [_ifetch2] one privilege *)
  (* over, assembled exactly like [PtTreeAdue.swp_checked_mem_read_pte8]  *)
  (* (which is the same node at [Load PageTableEntry]): the PMA check,    *)
  (* the SUPERVISOR pmp walk ([PtTreeAdue.swp_pmpCheck_S], where the      *)
  (* fall-through is DENY so entry 0 must actually match), the MMIO test  *)
  (* and the RAM read node.  The bytes arrive as the atomic-step fupd, so *)
  (* the text window is re-read per chunk and nothing is owned across a   *)
  (* node.                                                               *)
  (*                                                                     *)
  (* (Generic in the frame -- it belongs in [HartSTrans] beside           *)
  (* [swp_fetch_S]; it is here so that this conversion costs no rebuild   *)
  (* of the M-mode cone.)                                                *)
  (* =================================================================== *)

  (* the PMA check at Supervisor: [check_pma_with_pmp_priority] never reads
     the privilege, so this is [HartMFetch.hfrun_check_pma_ifetch] with the
     argument changed. *)
  Lemma hfrun_check_pma_ifetch_S (D Drw : gset register) (rs : regstate)
      (pa : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region) (n : Z) :
    (pma_regions : register) ∈ D ->
    register_lookup pma_regions rs = pmar0 ->
    pma_allows_ram pmar0 ->
    pma_ram_access pa n ->
    is_aligned_paddr (Physaddr pa) n = true ->
    hfrun 6 D Drw rs
      (check_pma_with_pmp_priority (InstructionFetch tt) PBMT_PMA Supervisor
         (Physaddr pa) n false)
    = Some (Values.Ok
              {| Phys_Mem_Access_Info_splittable := CannotSplit;
                 Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).
  Proof.
    intros HD Hpma Hpallow Hacc Hpa.
    unfold check_pma_with_pmp_priority. spt_cbn.
    spt_read. rewrite Hpma. spt_cbn.
    destruct (Hpallow pa n Hacc) as (region & Hmatch & Hgrant).
    destruct region as [rbase rsize rattr rdtree].
    destruct Hgrant as (Hx & _).
    cbn [PMA_Region_attributes] in Hx.
    rewrite Hmatch. spt_cbn.
    rewrite Hx. spt_cbn.
    rewrite Hpa. spt_cbn.
    apply hfrun_ret.
  Qed.


  (* the 4-byte fetch read at Supervisor *)
  Lemma swp_checked_mem_read_ifetch4_S (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (bytes : bv 32) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    addr_is_ram (pa_add pa 3) ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) pa 4 = Some bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
           (Physaddr pa) 4 false false false false)
      (fun r => ⌜r = Values.Ok (bytes, tt)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HD HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr
      HA Hord HX Hcov Hpallow Hram Hram3 Hpa.
    pose proof (ram_fetch_pmp pa (vec_access_dec paddr 0) 4 3
                  ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                  ltac:(reflexivity) Hram Hram3 Hcov) as Hrange.
    iIntros "#Hcert Hrw Hro Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold checked_mem_read.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority (InstructionFetch tt) PBMT_PMA
                 Supervisor (Physaddr pa) 4 false) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_check_pma_ifetch_S (Drw ∪ Dro) Drw rs pa pmar0 4
                   HD Hpma Hpallow (pma_access_ram pa 4 3 Hram Hram3
                      (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl) Hpa)
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
    change (0 * 4) with 0. rewrite avi0.
    iApply (swp_use_cer3
              (pmpCheck (Physaddr pa) 4 (InstructionFetch tt) Supervisor)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_S (InstructionFetch tt) Drw Dro Df rs pcfg paddr
                pa 4 Hdisj HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange
                ltac:(unfold pmpCheckRWX; cbn match; rewrite HX; reflexivity)
                with "Hcert Hrw Hro"). }
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

  (* the 2-byte fetch read at Supervisor *)
  Lemma swp_checked_mem_read_ifetch2_S (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (bytes : bv 16) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    addr_is_ram (pa_add pa 1) ->
    is_aligned_paddr (Physaddr pa) 2 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) pa 2 = Some bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
           (Physaddr pa) 2 false false false false)
      (fun r => ⌜r = Values.Ok (bytes, tt)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HD HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr
      HA Hord HX Hcov Hpallow Hram Hram1 Hpa.
    pose proof (ram_fetch_pmp pa (vec_access_dec paddr 0) 2 1
                  ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                  ltac:(reflexivity) Hram Hram1 Hcov) as Hrange.
    iIntros "#Hcert Hrw Hro Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold checked_mem_read.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority (InstructionFetch tt) PBMT_PMA
                 Supervisor (Physaddr pa) 2 false) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_check_pma_ifetch_S (Drw ∪ Dro) Drw rs pa pmar0 2
                   HD Hpma Hpallow (pma_access_ram pa 2 1 Hram Hram1
                      (pma_width_ok 2 eq_refl eq_refl) eq_refl eq_refl) Hpa)
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
              (pmpCheck (Physaddr pa) 2 (InstructionFetch tt) Supervisor)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_S (InstructionFetch tt) Drw Dro Df rs pcfg paddr
                pa 2 Hdisj HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange
                ltac:(unfold pmpCheckRWX; cbn match; rewrite HX; reflexivity)
                with "Hcert Hrw Hro"). }
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


  (* =================================================================== *)
  (* PART B -- THE TEXT BYTES AT THE TRANSLATED PHYSICAL ADDRESS.         *)
  (*                                                                     *)
  (* [InstrBytes.text_fetch_obl]'s S-mode twin.  There the window's va IS *)
  (* its pa; here the chunk is read at [pa_of ppn b], the address the      *)
  (* walk translated to, and the per-byte agreement is [s_fetch_chunk]'s  *)
  (* claim collapse.  The obligation is re-provable at EVERY node because *)
  (* the window is persistent, which is what lets it be discharged once   *)
  (* per fetch node without owning anything across the walk.              *)
  (* =================================================================== *)
  Lemma s_text_obl `{KTR : !CurKtier} (pc b : mword 64) (lo Nw : nat) (n : N)
      (g : nat -> bv 8) (ppn : mword 44) (w : bv (8 * n)) :
    (lo + N.to_nat n <= Nw)%nat ->
    (0 < N.to_nat n)%nat ->
    (forall k : nat, pa_add pc (lo + k)%nat = pa_add b k) ->
    (bv_unsigned (subrange_vec_dec b 11 0) + Z.of_nat (N.to_nat n) <= 4096)%Z ->
    (uint b < 274877906944)%Z ->
    (forall j : nat, (N.of_nat j < n)%N -> g (lo + j)%nat = nth_byte w j) ->
    kmap_at (svpn_of b) ppn KP_rx -∗
    ([∗ list] j ∈ seq 0 Nw, (pa_add pc j) ↦ₓ□ g j) -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ⌜read_bytes σ.(mem) (pa_of ppn b) n = Some w⌝ ∗
       ▷ (|={∅,⊤}=> mstate_interp σ)).
  Proof.
    intros Hlon Hlen Hbase Hoff Hcan Hg.
    iIntros "#Hk #Hbytes" (σ) "Hσ".
    rewrite /mstate_interp. iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    iDestruct (s_fetch_chunk σ pc b lo (N.to_nat n) Nw g ppn
                 Hlon Hlen Hbase Hoff Hcan with "Hmem Hk Hbytes")
      as %(Hbf & _ & _).
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hmask".
    iSplitR.
    { iPureIntro. apply read_bytes_of_bytes. intros j Hj.
      rewrite <- (Hg j Hj). apply Hbf.
      rewrite N2Nat.id. exact Hj. }
    iNext. iMod "Hmask" as "_". iModIntro. by iFrame.
  Qed.


  (* =================================================================== *)
  (* PART C -- run_hart_active WITH AN EXISTENTIAL FETCH-LANDING FILE.    *)
  (*                                                                     *)
  (* [HartRunGen.swp_run_hart_active_gen_ex] leaves the landing file      *)
  (* [rsf] of the FETCH a lemma binder.  A WALKING fetch cannot name it:  *)
  (* [SRegime.sr_swp_translate]'s post is [∃ rsf, ⌜rsf = rs ∨ ∃ tv,       *)
  (* rsf = register_set tlb tv rs⌝ ∗ …] precisely because no caller knows *)
  (* whether the TLB hits, and an existential inside a [swp]              *)
  (* postcondition cannot be hoisted out.  So the rule is restated with   *)
  (* the landing file a PREDICATE [Qf]: the fetch delivers SOME file      *)
  (* satisfying it, the decode/landing-pad facts are demanded of every    *)
  (* such file, and the execute obligation is quantified over it.         *)
  (*                                                                     *)
  (* This is the same generalization [_ex] made on the POST file, one     *)
  (* file earlier in the chain, and it belongs beside its twin in         *)
  (* [HartRunGen]; it is here so that this conversion costs no rebuild of *)
  (* the M-mode cone.                                                    *)
  (* =================================================================== *)
  Lemma swp_run_hart_active_gen_exf_res (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (Qf Q : regstate -> Prop) (Rf : regstate -> iProp Σ) (Wd : iProp Σ)
      (p : Privilege)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (i : instruction) (nl : nat) (Rr : regstate -> iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ)
      (resf : ExecutionResult) :
    (* THE MODEL RE-DISPATCHES ON THE EXECUTE RESULT ([ExecuteAs] re-enters
       [execute]), so a SYMBOLIC result leaves that match stuck.  The
       premise is the one δ-step equation that unsticks it, and it is
       [reflexivity] at every result the kernel actually produces. *)
    (match resf with
     | ExecuteAs other_inst =>
         (liftR (execute other_inst) : MR Step ExecutionResult)
     | result' => returnR Step result'
     end) = returnR Step resf ->
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    (forall rsf, Qf rsf -> register_lookup (R_bitvector_64 PC) rsf = pc) ->
    (forall rsf, Qf rsf -> hval (Drw ∪ Dro) Drw rsf (ext_decode w) i rsf) ->
    (forall rsf, Qf rsf ->
       hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
       = Some (false, rsf)) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    Wd -∗
    (Wd -∗ hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => Wd ∗ hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (Wd -∗ hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt)
         (fun r => ⌜r = F_Base w⌝ ∗
                   ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (∀ rsf : regstate, ⌜Qf rsf⌝ -∗ Rf rsf -∗
     hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 4) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 4) rsf) Dro -∗
     swp (execute i)
       (fun e => ⌜e = resf⌝ ∗
                 ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                 hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ Rr rs2)) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (⌜st = Step_Execute (resf, zero_extend' 32 w)⌝ ∗
                    ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                    hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ Rr rs2)).
  Proof.
    intros Hplain Hdisj HDpriv HDpc HDnpc Hpriv Hpcf Hdec Hlpad.
    iIntros "#Hcert Hrw Hro HWd Hdisp Hfet Hex".
    unfold run_hart_active.
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    iApply (swp_use_cer (dispatchInterrupt p) _ _ C HC
              with "[Hrw Hro Hdisp HWd] [-]").
    { iApply ("Hdisp" with "HWd Hrw Hro"). }
    iIntros (o) "Ho".
    destruct o as [[ii pr] |].
    - cbn beta iota. rewrite mcer_early_return.
      iApply ("Hcont" $! (Step_Pending_Interrupt (ii, pr))).
      iLeft. iExists ii, pr. by iFrame.
    - iDestruct "Ho" as "(HWd & Hrw & Hro)".
      cbn beta iota. rewrite mbind0_ret.
      iApply (swp_use_cer (fetch tt) _ _ C HC with "[Hrw Hro Hfet HWd] [-]").
      { iApply ("Hfet" with "HWd Hrw Hro"). }
      iIntros (v) "(-> & Hf)".
      iDestruct "Hf" as (rsf) "(%HQf & HRf & Hrw & Hro)".
      cbn beta iota zeta delta [ext_fetch_hook sail_instr_announce
        fetch_callback get_config_print_instr].
      iApply (swp_use_cer (ext_decode w) _ _ C HC with "[Hrw Hro] [-]").
      { iApply (swp_span Drw Dro Df rsf rsf _ _ Hdisj (Hdec rsf HQf)
                  with "Hcert Hrw Hro"). }
      iIntros (v) "(-> & Hrw & Hro)". rg_glue.
      rewrite mbind0_ret.
      iApply (swp_use_cer2 (is_landing_pad_expected tt) _ _ _ C HC
                with "[Hrw Hro] [-]").
      { iApply (swp_hfrun nl Drw Dro Df rsf rsf _ _ Hdisj (Hlpad rsf HQf)
                  with "Hcert Hrw Hro"). }
      iIntros (v) "(-> & Hrw & Hro)". rg_glue.
      rewrite mbind_ret. rg_glue.
      iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
                with "[Hrw Hro] [-]").
      { iApply (swp_read_reg_pinned Drw Dro Df rsf _ Hdisj HDpc
                  with "Hcert Hrw Hro"). }
      iIntros (v) "(-> & Hrw & Hro)". rewrite (Hpcf rsf HQf).
      iApply (swp_use_cer2
                (Defs.write_reg (R_bitvector_64 nextPC)
                   (add_vec_int pc 4)) _ _ _ C HC with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned Drw Dro Df rsf _ _ Hdisj HDnpc
                  with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_use_cer (execute i) _ _ C HC with "[Hrw Hro Hex HRf] [-]").
      { iApply ("Hex" $! rsf with "[%] HRf Hrw Hro"). exact HQf. }
      iIntros (v) "(-> & HEx)".
      iDestruct "HEx" as (rs2) "(%HQ & Hrw & Hro & HR)".
      rewrite Hplain. rg_glue.
      rewrite mcer_ret.
      iApply ("Hcont" $! (Step_Execute (resf, zero_extend' 32 w))).
      iRight. iSplitR "Hrw Hro HR"; [ by iPureIntro | ].
      iExists rs2. by iFrame.
  Qed.

  (* the retiring instance -- the statement every existing caller uses *)
  Lemma swp_run_hart_active_gen_exf (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (Qf Q : regstate -> Prop) (Rf : regstate -> iProp Σ) (Wd : iProp Σ)
      (p : Privilege)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (i : instruction) (nl : nat) (Rr : regstate -> iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    (forall rsf, Qf rsf -> register_lookup (R_bitvector_64 PC) rsf = pc) ->
    (forall rsf, Qf rsf -> hval (Drw ∪ Dro) Drw rsf (ext_decode w) i rsf) ->
    (forall rsf, Qf rsf ->
       hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
       = Some (false, rsf)) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    Wd -∗
    (Wd -∗ hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => Wd ∗ hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (Wd -∗ hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt)
         (fun r => ⌜r = F_Base w⌝ ∗
                   ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (∀ rsf : regstate, ⌜Qf rsf⌝ -∗ Rf rsf -∗
     hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 4) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 4) rsf) Dro -∗
     swp (execute i)
       (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                 ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                 hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ Rr rs2)) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (⌜st = Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w)⌝ ∗
                    ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                    hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ Rr rs2)).
  Proof.
    exact (swp_run_hart_active_gen_exf_res Drw Dro Df rs Qf Q Rf Wd p pc w i nl Rr Qi
             RETIRE_SUCCESS eq_refl).
  Qed.


  (* the compressed twin of [swp_run_hart_active_gen_exf] *)
  Lemma swp_run_hart_active_gen_rvc_exf_res (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (Qf Q : regstate -> Prop) (Rf : regstate -> iProp Σ) (Wd : iProp Σ)
      (p : Privilege)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (i other : instruction) (nl : nat) (Rr : regstate -> iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ)
      (resf : ExecutionResult) :
    (* NO re-dispatch premise here: the model's [match] on the execute
       result has already fired -- this is the [ExecuteAs other] shape, and
       [Hexp] is what pins it. *)
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    (forall rsf, Qf rsf -> register_lookup (R_bitvector_64 PC) rsf = pc) ->
    (forall rsf, Qf rsf ->
       eq_vec (_get_Misa_C (register_lookup misa rsf))
         (MachineWord.MachineWord.N_to_word 1 1%N) = true) ->
    (forall rsf, Qf rsf ->
       hval (Drw ∪ Dro) Drw rsf (ext_decode_compressed h) i rsf) ->
    (forall rsf, Qf rsf ->
       hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
       = Some (false, rsf)) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    Wd -∗
    (Wd -∗ hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => Wd ∗ hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (Wd -∗ hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt)
         (fun r => ⌜r = F_RVC h⌝ ∗
                   ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (∀ rsf : regstate, ⌜Qf rsf⌝ -∗
     hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Dro -∗
     swp (execute i)
       (fun e => ⌜e = ExecuteAs other⌝ ∗
                 hreg_frame (register_set (R_bitvector_64 nextPC)
                               (add_vec_int pc 2) rsf) Drw ∗
                 hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                                     (add_vec_int pc 2) rsf) Dro)) -∗
    (∀ rsf : regstate, ⌜Qf rsf⌝ -∗ Rf rsf -∗
     hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Dro -∗
     swp (execute other)
       (fun e => ⌜e = resf⌝ ∗
                 ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                 hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ Rr rs2)) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (⌜st = Step_Execute (resf, zero_extend' 32 h)⌝ ∗
                    ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                    hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ Rr rs2)).
  Proof.
    intros Hdisj HDpriv HDmisa HDpc HDnpc Hpriv Hpcf HmisaCf Hdec Hlpad.
    iIntros "#Hcert Hrw Hro HWd Hdisp Hfet Hexp Hex".
    unfold run_hart_active.
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    iApply (swp_use_cer (dispatchInterrupt p) _ _ C HC
              with "[Hrw Hro Hdisp HWd] [-]").
    { iApply ("Hdisp" with "HWd Hrw Hro"). }
    iIntros (o) "Ho".
    destruct o as [[ii pr] |].
    - cbn beta iota. rewrite mcer_early_return.
      iApply ("Hcont" $! (Step_Pending_Interrupt (ii, pr))).
      iLeft. iExists ii, pr. by iFrame.
    - iDestruct "Ho" as "(HWd & Hrw & Hro)".
      cbn beta iota. rewrite mbind0_ret.
      iApply (swp_use_cer (fetch tt) _ _ C HC with "[Hrw Hro Hfet HWd] [-]").
      { iApply ("Hfet" with "HWd Hrw Hro"). }
      iIntros (v) "(-> & Hf)".
      iDestruct "Hf" as (rsf) "(%HQf & HRf & Hrw & Hro)".
      cbn beta iota zeta delta [ext_fetch_hook sail_instr_announce
        fetch_callback get_config_print_instr].
      iApply (swp_use_cer (ext_decode_compressed h) _ _ C HC
                with "[Hrw Hro] [-]").
      { iApply (swp_span Drw Dro Df rsf rsf _ _ Hdisj (Hdec rsf HQf)
                  with "Hcert Hrw Hro"). }
      iIntros (v) "(-> & Hrw & Hro)". rg_glue.
      rewrite mbind0_ret.
      iApply (swp_use_cer2 (is_landing_pad_expected tt) _ _ _ C HC
                with "[Hrw Hro] [-]").
      { iApply (swp_hfrun nl Drw Dro Df rsf rsf _ _ Hdisj (Hlpad rsf HQf)
                  with "Hcert Hrw Hro"). }
      iIntros (v) "(-> & Hrw & Hro)". rg_glue.
      rewrite mbind_ret. rg_glue.
      iApply (swp_use_cer (currentlyEnabled Ext_Zca) _ _ C HC
                with "[Hrw Hro] [-]").
      { iApply (swp_hfrun 4 Drw Dro Df rsf rsf _ _ Hdisj
                  (hfrun_cE_Zca (Drw ∪ Dro) Drw rsf HDmisa (HmisaCf rsf HQf))
                  with "Hcert Hrw Hro"). }
      iIntros (v) "(-> & Hrw & Hro)". rg_glue.
      iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
                with "[Hrw Hro] [-]").
      { iApply (swp_read_reg_pinned Drw Dro Df rsf _ Hdisj HDpc
                  with "Hcert Hrw Hro"). }
      iIntros (v) "(-> & Hrw & Hro)". rewrite (Hpcf rsf HQf).
      iApply (swp_use_cer2
                (Defs.write_reg (R_bitvector_64 nextPC)
                   (add_vec_int pc 2)) _ _ _ C HC with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned Drw Dro Df rsf _ _ Hdisj HDnpc
                  with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_use_cer (execute i) _ _ C HC with "[Hrw Hro Hexp] [-]").
      { iApply ("Hexp" $! rsf with "[%] Hrw Hro"). exact HQf. }
      iIntros (v) "(-> & Hrw & Hro)". rg_glue.
      iApply (swp_use_cer (execute other) _ _ C HC with "[Hrw Hro Hex HRf] [-]").
      { iApply ("Hex" $! rsf with "[%] HRf Hrw Hro"). exact HQf. }
      iIntros (v) "(-> & HEx)".
      iDestruct "HEx" as (rs2) "(%HQ & Hrw & Hro & HR)".
      rg_glue.
      rewrite mcer_ret.
      iApply ("Hcont" $! (Step_Execute (resf, zero_extend' 32 h))).
      iRight. iSplitR "Hrw Hro HR"; [ by iPureIntro | ].
      iExists rs2. by iFrame.
  Qed.

  (* the retiring instance -- the statement every existing caller uses *)
  Lemma swp_run_hart_active_gen_rvc_exf (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (Qf Q : regstate -> Prop) (Rf : regstate -> iProp Σ) (Wd : iProp Σ)
      (p : Privilege)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (i other : instruction) (nl : nat) (Rr : regstate -> iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    (forall rsf, Qf rsf -> register_lookup (R_bitvector_64 PC) rsf = pc) ->
    (forall rsf, Qf rsf ->
       eq_vec (_get_Misa_C (register_lookup misa rsf))
         (MachineWord.MachineWord.N_to_word 1 1%N) = true) ->
    (forall rsf, Qf rsf ->
       hval (Drw ∪ Dro) Drw rsf (ext_decode_compressed h) i rsf) ->
    (forall rsf, Qf rsf ->
       hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
       = Some (false, rsf)) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    Wd -∗
    (Wd -∗ hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => Wd ∗ hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (Wd -∗ hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt)
         (fun r => ⌜r = F_RVC h⌝ ∗
                   ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (∀ rsf : regstate, ⌜Qf rsf⌝ -∗
     hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Dro -∗
     swp (execute i)
       (fun e => ⌜e = ExecuteAs other⌝ ∗
                 hreg_frame (register_set (R_bitvector_64 nextPC)
                               (add_vec_int pc 2) rsf) Drw ∗
                 hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                                     (add_vec_int pc 2) rsf) Dro)) -∗
    (∀ rsf : regstate, ⌜Qf rsf⌝ -∗ Rf rsf -∗
     hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Dro -∗
     swp (execute other)
       (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                 ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                 hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ Rr rs2)) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (⌜st = Step_Execute (RETIRE_SUCCESS, zero_extend' 32 h)⌝ ∗
                    ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                    hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ Rr rs2)).
  Proof.
    exact (swp_run_hart_active_gen_rvc_exf_res Drw Dro Df rs Qf Q Rf Wd p pc h
             i other nl Rr Qi RETIRE_SUCCESS).
  Qed.


  (* =================================================================== *)
  (* PART D -- THE FETCH SHAPES WITH AN ABSTRACT LANDING POSTCONDITION.   *)
  (*                                                                     *)
  (* [HartMFetch.swp_fetch] / [_rvc2] / [_base2] name the file            *)
  (* [fetch_bytes] lands on.  A walking fetch does not know it (PART C),  *)
  (* and the landing file never occurs in these rules' PROOFS -- only in  *)
  (* the shape of the sub-obligation's post.  So each is restated with    *)
  (* that post an abstract [P], which is strictly more general and whose  *)
  (* proof is the SAME walk; the [_base2] rule keeps a predicate for its  *)
  (* INTERMEDIATE file, because the model re-reads PC between the two     *)
  (* halfword fetches.                                                   *)
  (*                                                                     *)
  (* These belong in [HartMFetch] beside the rules they generalize (M-mode *)
  (* recovers each by [P := frames rsf]); they are here so that this      *)
  (* conversion costs no rebuild of the M-mode cone.                      *)
  (* =================================================================== *)
  Lemma spt_fetch_P (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pc : SailStdpp.Values.mword 64)
      (w : SailStdpp.Values.mword 32) (P : iProp Σ) :
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
         (fun r => ⌜r = @FetchBytes_Success 4 w⌝ ∗ P)) -∗
    swp (fetch tt)
      (fun r => ⌜r = (if isRVC (subrange_vec_dec w 15 0)
                      then F_RVC (subrange_vec_dec w 15 0)
                      else F_Base w)⌝ ∗ P).
  Proof.
    intros Hdisj HDpc Hpc Hb0 Hb1 Hal.
    iIntros "#Hcert Hrw Hro Hfb".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold fetch. spt_mf.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". spt_mf.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". spt_mf.
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
    rewrite mbind_ret. cbn beta.
    unfold Defs.and_boolM.
    iApply (swp_use_cer3 (Defs.read_reg (R_bitvector_64 PC)) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hpc mbind_ret. cbn beta. rewrite Hal.
    rewrite spt_cE_Ziccif /returnM mliftR_ret mbind_ret. cbn beta.
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
    iApply (swp_use_cer (fetch_bytes pc pc 4) _ _ C HC
              with "[Hrw Hro Hfb] [-]").
    { iApply ("Hfb" with "Hrw Hro"). }
    iIntros (v) "(-> & HP)". cbn beta iota.
    rewrite mcer_ret.
    iApply ("Hcont" $! (if isRVC (subrange_vec_dec w 15 0)
                        then F_RVC (subrange_vec_dec w 15 0)
                        else F_Base w)). by iFrame.
  Qed.

  Lemma spt_fetch_rvc2_P (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pc : SailStdpp.Values.mword 64)
      (h : SailStdpp.Values.mword 16) (P : iProp Σ) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    isRVC h = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch_bytes pc pc 2)
         (fun r => ⌜r = @FetchBytes_Success 2 h⌝ ∗ P)) -∗
    swp (fetch tt) (fun r => ⌜r = F_RVC h⌝ ∗ P).
  Proof.
    intros Hdisj HDpc HDmisa Hpc Hb0 Hb1 Hal4 HmisaC Hrvc.
    iIntros "#Hcert Hrw Hro Hfb".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold fetch. spt_mf.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". spt_mf.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". spt_mf.
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
    rewrite mf_cE_Zca_eq_local.
    iApply (swp_use_cer3 (Defs.read_reg misa) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmisa
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite HmisaC. cbn beta iota.
    rewrite mbind_ret. cbn beta.
    unfold Defs.and_boolM.
    iApply (swp_use_cer3 (Defs.read_reg (R_bitvector_64 PC)) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hpc mbind_ret. cbn beta.
    rewrite Hal4. cbn beta iota.
    rewrite mbind_ret. cbn beta.
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
    iIntros (v) "(-> & HP)". cbn beta iota.
    rewrite Hrvc. cbn beta iota.
    rewrite mcer_ret.
    iApply ("Hcont" $! (F_RVC h)). by iFrame.
  Qed.

  Lemma spt_fetch_base2_P (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (Qf1 : regstate -> Prop) (Rf1 : regstate -> iProp Σ)
      (pc : SailStdpp.Values.mword 64)
      (ilo ihi : SailStdpp.Values.mword 16) (P : iProp Σ) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    isRVC ilo = false ->
    (forall rs1, Qf1 rs1 -> register_lookup (R_bitvector_64 PC) rs1 = pc) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch_bytes pc pc 2)
         (fun r => ⌜r = @FetchBytes_Success 2 ilo⌝ ∗
                   ∃ rs1 : regstate, ⌜Qf1 rs1⌝ ∗ Rf1 rs1 ∗
                   hreg_frame rs1 Drw ∗ hreg_frame_ro Df rs1 Dro)) -∗
    (∀ rs1 : regstate, ⌜Qf1 rs1⌝ -∗ Rf1 rs1 -∗
     hreg_frame rs1 Drw -∗ hreg_frame_ro Df rs1 Dro -∗
       swp (fetch_bytes pc (add_vec_int pc 2) 2)
         (fun r => ⌜r = @FetchBytes_Success 2 ihi⌝ ∗ P)) -∗
    swp (fetch tt)
      (fun r => ⌜r = F_Base (concat_vec ihi ilo)⌝ ∗ P).
  Proof.
    intros Hdisj HDpc HDmisa Hpc Hb0 Hb1 Hal4 HmisaC Hnrvc Hpc1.
    iIntros "#Hcert Hrw Hro Hlo Hhi".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold fetch. spt_mf.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". spt_mf.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". spt_mf.
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
    rewrite mf_cE_Zca_eq_local.
    iApply (swp_use_cer3 (Defs.read_reg misa) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmisa
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite HmisaC. cbn beta iota.
    rewrite mbind_ret. cbn beta.
    unfold Defs.and_boolM.
    iApply (swp_use_cer3 (Defs.read_reg (R_bitvector_64 PC)) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hpc mbind_ret. cbn beta.
    rewrite Hal4. cbn beta iota.
    rewrite mbind_ret. cbn beta.
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
    iIntros (v) "(-> & Hf)". cbn beta iota.
    iDestruct "Hf" as (rs1) "(%HQ1 & HRf1 & Hrw & Hro)".
    rewrite Hnrvc. cbn beta iota.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs1 _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite (Hpc1 rs1 HQ1).
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs1 _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite (Hpc1 rs1 HQ1).
    iApply (swp_use_cer (fetch_bytes pc (add_vec_int pc 2) 2) _ _ C HC
              with "[Hrw Hro Hhi HRf1] [-]").
    { iApply ("Hhi" $! rs1 with "[%] HRf1 Hrw Hro"). exact HQ1. }
    iIntros (v) "(-> & HP)". cbn beta iota.
    rewrite mcer_ret.
    iApply ("Hcont" $! (F_Base (concat_vec ihi ilo))). by iFrame.
  Qed.


  (* =================================================================== *)
  (* PART E -- fetch_bytes AT SUPERVISOR, WITH THE LANDING FILE A         *)
  (* PREDICATE.  [HartSTrans.swp_fetch_bytes_S] / [_S2] with [rsf]        *)
  (* replaced by [Qf]: the translation delivers SOME landing file (it may *)
  (* or may not have filled the TLB) and the text read runs at whichever  *)
  (* it delivered.                                                        *)
  (* =================================================================== *)
  Lemma spt_fetch_bytes_S_P (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (Qf : regstate -> Prop) (Rf : regstate -> iProp Σ)
      (pc pa : mword 64) (w : mword 32) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (forall rsf, Qf rsf -> register_lookup cur_privilege rsf = Supervisor) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr pc) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (∀ rsf : regstate, ⌜Qf rsf⌝ -∗
     hreg_frame rsf Drw -∗ hreg_frame_ro Df rsf Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
              (Physaddr pa) 4 false false false false)
         (fun r => ⌜r = Values.Ok (w, tt)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    swp (fetch_bytes pc pc 4)
      (fun r => ⌜r = @FetchBytes_Success 4 w⌝ ∗
                ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv.
    iIntros "#Hcert Hrw Hro Htr Hcmr".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold fetch_bytes.
    cbn beta iota zeta delta [ext_fetch_check_pc].
    rewrite mbind0_ret.
    iApply (swp_use_cer (translateAddr (Virtaddr pc) (InstructionFetch tt))
              _ _ C HC with "[Hrw Hro Htr] [-]").
    { iApply ("Htr" with "Hrw Hro"). }
    iIntros (v) "(-> & Hf)". cbn beta iota.
    iDestruct "Hf" as (rsf) "(%HQ & HRf & Hrw & Hro)".
    iApply (swp_use_cer
              (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4
                 false false false) _ _ C HC with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_mem_read_M Drw Dro Df rsf (Physaddr pa) w Supervisor Hdisj
                HDmst HDpriv (Hpriv rsf HQ) with "Hcert Hrw Hro [Hcmr]").
      iApply ("Hcmr" $! rsf with "[%]"). exact HQ. }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite autocast_id mcer_ret.
    iApply ("Hcont" $! (@FetchBytes_Success 4 w)).
    iSplitR; [done|]. iExists rsf. by iFrame.
  Qed.

  Lemma spt_fetch_bytes_S2_P (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (Qf : regstate -> Prop) (Rf : regstate -> iProp Σ)
      (fs gs pa : mword 64) (h : mword 16) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (forall rsf, Qf rsf -> register_lookup cur_privilege rsf = Supervisor) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr gs) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (∀ rsf : regstate, ⌜Qf rsf⌝ -∗
     hreg_frame rsf Drw -∗ hreg_frame_ro Df rsf Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
              (Physaddr pa) 2 false false false false)
         (fun r => ⌜r = Values.Ok (h, tt)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    swp (fetch_bytes fs gs 2)
      (fun r => ⌜r = @FetchBytes_Success 2 h⌝ ∗
                ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv.
    iIntros "#Hcert Hrw Hro Htr Hcmr".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold fetch_bytes.
    cbn beta iota zeta delta [ext_fetch_check_pc].
    rewrite mbind0_ret.
    iApply (swp_use_cer (translateAddr (Virtaddr gs) (InstructionFetch tt))
              _ _ C HC with "[Hrw Hro Htr] [-]").
    { iApply ("Htr" with "Hrw Hro"). }
    iIntros (v) "(-> & Hf)". cbn beta iota.
    iDestruct "Hf" as (rsf) "(%HQ & HRf & Hrw & Hro)".
    iApply (swp_use_cer
              (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 2
                 false false false) _ _ C HC with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_mem_read_M2 Drw Dro Df rsf (Physaddr pa) h Supervisor Hdisj
                HDmst HDpriv (Hpriv rsf HQ) with "Hcert Hrw Hro [Hcmr]").
      iApply ("Hcmr" $! rsf with "[%]"). exact HQ. }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite autocast_id mcer_ret.
    iApply ("Hcont" $! (@FetchBytes_Success 2 h)).
    iSplitR; [done|]. iExists rsf. by iFrame.
  Qed.


  (* =================================================================== *)
  (* PART F -- THE THREE S-MODE FETCH SHAPES, LANDING FILE EXISTENTIAL.   *)
  (* [HartSTrans.swp_fetch_S] / [_S_rvc2] / [_S_base2] over PART D/E.     *)
  (* =================================================================== *)
  Lemma spt_fetch_S_P (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (Qf : regstate -> Prop) (Rf : regstate -> iProp Σ)
      (pc pa : mword 64) (w : mword 32) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    (forall rsf, Qf rsf -> register_lookup cur_privilege rsf = Supervisor) ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr pc) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (∀ rsf : regstate, ⌜Qf rsf⌝ -∗
     hreg_frame rsf Drw -∗ hreg_frame_ro Df rsf Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
              (Physaddr pa) 4 false false false false)
         (fun r => ⌜r = Values.Ok (w, tt)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    swp (fetch tt)
      (fun r => ⌜r = (if isRVC (subrange_vec_dec w 15 0)
                      then F_RVC (subrange_vec_dec w 15 0)
                      else F_Base w)⌝ ∗
                ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro).
  Proof.
    intros Hdisj HDpc HDmst HDpriv Hpc Hpriv Hb0 Hb1 Hal.
    iIntros "#Hcert Hrw Hro Htr Hcmr".
    iApply (spt_fetch_P Drw Dro Df rs pc w _ Hdisj HDpc Hpc Hb0 Hb1 Hal
              with "Hcert Hrw Hro [Htr Hcmr]").
    iIntros "Hrw Hro".
    iApply (spt_fetch_bytes_S_P Drw Dro Df rs Qf Rf pc pa w Hdisj HDmst
              HDpriv Hpriv with "Hcert Hrw Hro Htr Hcmr").
  Qed.

  Lemma spt_fetch_S_rvc2_P (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (Qf : regstate -> Prop) (Rf : regstate -> iProp Σ)
      (pc pa : mword 64) (h : mword 16) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    (forall rsf, Qf rsf -> register_lookup cur_privilege rsf = Supervisor) ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC h = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr pc) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (∀ rsf : regstate, ⌜Qf rsf⌝ -∗
     hreg_frame rsf Drw -∗ hreg_frame_ro Df rsf Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
              (Physaddr pa) 2 false false false false)
         (fun r => ⌜r = Values.Ok (h, tt)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    swp (fetch tt)
      (fun r => ⌜r = F_RVC h⌝ ∗
                ∃ rsf : regstate, ⌜Qf rsf⌝ ∗ Rf rsf ∗
                hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro).
  Proof.
    intros Hdisj HDpc HDmisa HDmst HDpriv Hpc Hpriv HmisaC Hb0 Hb1 Hal4 Hrvc.
    iIntros "#Hcert Hrw Hro Htr Hcmr".
    iApply (spt_fetch_rvc2_P Drw Dro Df rs pc h _ Hdisj HDpc HDmisa Hpc Hb0
              Hb1 Hal4 HmisaC Hrvc with "Hcert Hrw Hro [Htr Hcmr]").
    iIntros "Hrw Hro".
    iApply (spt_fetch_bytes_S2_P Drw Dro Df rs Qf Rf pc pc pa h Hdisj HDmst
              HDpriv Hpriv with "Hcert Hrw Hro Htr Hcmr").
  Qed.

  Lemma spt_fetch_S_base2_P (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (Qf1 Qf2 : regstate -> Prop)
      (Rf1 Rf2 : regstate -> iProp Σ) (pc pa1 pa2 : mword 64)
      (ilo ihi : mword 16) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    (forall rs1, Qf1 rs1 -> register_lookup (R_bitvector_64 PC) rs1 = pc) ->
    (forall rs1, Qf1 rs1 -> register_lookup cur_privilege rs1 = Supervisor) ->
    (forall rs2, Qf2 rs2 -> register_lookup cur_privilege rs2 = Supervisor) ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC ilo = false ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr pc) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa1, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rs1 : regstate, ⌜Qf1 rs1⌝ ∗ Rf1 rs1 ∗
                   hreg_frame rs1 Drw ∗ hreg_frame_ro Df rs1 Dro)) -∗
    (∀ rs1 : regstate, ⌜Qf1 rs1⌝ -∗
     hreg_frame rs1 Drw -∗ hreg_frame_ro Df rs1 Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
              (Physaddr pa1) 2 false false false false)
         (fun r => ⌜r = Values.Ok (ilo, tt)⌝ ∗
                   hreg_frame rs1 Drw ∗ hreg_frame_ro Df rs1 Dro)) -∗
    (∀ rs1 : regstate, ⌜Qf1 rs1⌝ -∗ Rf1 rs1 -∗
     hreg_frame rs1 Drw -∗ hreg_frame_ro Df rs1 Dro -∗
       swp (translateAddr (Virtaddr (add_vec_int pc 2)) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa2, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rs2 : regstate, ⌜Qf2 rs2⌝ ∗ Rf2 rs2 ∗
                   hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro)) -∗
    (∀ rs2 : regstate, ⌜Qf2 rs2⌝ -∗
     hreg_frame rs2 Drw -∗ hreg_frame_ro Df rs2 Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
              (Physaddr pa2) 2 false false false false)
         (fun r => ⌜r = Values.Ok (ihi, tt)⌝ ∗
                   hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro)) -∗
    swp (fetch tt)
      (fun r => ⌜r = F_Base (concat_vec ihi ilo)⌝ ∗
                ∃ rs2 : regstate, ⌜Qf2 rs2⌝ ∗ Rf2 rs2 ∗
                hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro).
  Proof.
    intros Hdisj HDpc HDmisa HDmst HDpriv Hpc Hpc1 Hpriv1 Hpriv2 HmisaC
      Hb0 Hb1 Hal4 Hnrvc.
    iIntros "#Hcert Hrw Hro Htr1 Hcmr1 Htr2 Hcmr2".
    iApply (spt_fetch_base2_P Drw Dro Df rs Qf1 Rf1 pc ilo ihi _ Hdisj HDpc
              HDmisa Hpc Hb0 Hb1 Hal4 HmisaC Hnrvc Hpc1
              with "Hcert Hrw Hro [Htr1 Hcmr1] [Htr2 Hcmr2]").
    - iIntros "Hrw Hro".
      iApply (spt_fetch_bytes_S2_P Drw Dro Df rs Qf1 Rf1 pc pc pa1 ilo Hdisj
                HDmst HDpriv Hpriv1 with "Hcert Hrw Hro Htr1 Hcmr1").
    - iIntros (rs1) "%HQ1 HRf1 Hrw Hro".
      iApply (spt_fetch_bytes_S2_P Drw Dro Df rs1 Qf2 Rf2 pc (add_vec_int pc 2)
                pa2 ihi Hdisj HDmst HDpriv Hpriv2
                with "Hcert Hrw Hro [Htr2 HRf1] Hcmr2").
      iApply ("Htr2" $! rs1 with "[%] HRf1"). exact HQ1.
  Qed.


  (* the two RAM endpoints of a text chunk, with NO heap interpretation:
     they come off the bytes' own claims ([code_ram]), which is what lets
     the fetch's PMA/PMP premises be discharged before any node runs.
     [s_fetch_chunk]'s last two blocks, split out. *)
  Lemma s_chunk_ram `{KTR : !CurKtier} (pc b : mword 64)
      (lo len N : nat) (g : nat -> bv 8) (ppn : mword 44) :
    (lo + len <= N)%nat ->
    (0 < len)%nat ->
    (forall k : nat, pa_add pc (lo + k)%nat = pa_add b k) ->
    (bv_unsigned (subrange_vec_dec b 11 0) + Z.of_nat len <= 4096)%Z ->
    (uint b < 274877906944)%Z ->
    kmap_at (svpn_of b) ppn KP_rx -∗
    ([∗ list] j ∈ seq 0 N, (pa_add pc j) ↦ₓ□ g j) -∗
    ⌜ addr_is_ram (pa_of ppn b)
      /\ addr_is_ram (pa_add (pa_of ppn b) (len - 1)) ⌝.
  Proof.
    intros Hlon Hlen Hbase Hoff Hcan.
    iIntros "#Hk #Hbytes".
    iAssert (⌜addr_is_ram (pa_of ppn b)⌝)%I as %Hram0.
    { iDestruct (big_sepL_lookup _ _ (lo + 0)%nat (lo + 0)%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iEval (rewrite (Hbase 0%nat) pa_add_0) in "Hb0".
      iDestruct (code_ram with "Hb0") as (ppn0) "[#Hk0 %Hr]".
      iDestruct (kmap_at_agree with "Hk0 Hk") as %[Heqp _].
      rewrite Heqp in Hr. iPureIntro. exact Hr. }
    iAssert (⌜addr_is_ram (pa_add (pa_of ppn b) (len - 1))⌝)%I as %Hramh.
    { assert (Hoffh : (bv_unsigned (subrange_vec_dec b 11 0) + Z.of_nat (len - 1) < 4096)%Z).
      { eapply Z.lt_le_trans; [| exact Hoff].
        apply Z.add_lt_mono_l. apply Nat2Z.inj_lt. lia. }
      iDestruct (big_sepL_lookup _ _ (lo + (len - 1))%nat (lo + (len - 1))%nat with "Hbytes") as "Hbh".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iEval (rewrite (Hbase (len - 1)%nat)) in "Hbh".
      iDestruct (code_ram with "Hbh") as (ppnh) "[#Hkh %Hr]".
      iEval (rewrite (svpn_of_pa_add b (len - 1)%nat Hcan Hoffh)) in "Hkh".
      iDestruct (kmap_at_agree with "Hkh Hk") as %[Heqp _].
      rewrite Heqp in Hr.
      rewrite (pa_of_pa_add ppn b (len - 1)%nat Hcan Hoffh) in Hr.
      iPureIntro. exact Hr. }
    iPureIntro. exact (conj Hram0 Hramh).
  Qed.



  (* ------------------------------------------------------------------ *)
  (* THE DISPATCH, PINNED TO [None].  [smode_config] (and this wrapper's  *)
  (* SIE premise) says interrupts are OFF, so the S-mode dispatch -- which *)
  (* does read the PLIC wires -- cannot fire whatever they hold:           *)
  (* [WpIntrCore.s_dispatch]'s guard is exactly [_get_Mstatus_SIE ms].     *)
  (* The reference state is THIS HART'S OWN FILE, so the agreement premise *)
  (* is [reflexivity] and the only real fact is misa.S.                    *)
  (* ------------------------------------------------------------------ *)
  Definition spt_Db (r : register) : bool :=
    orb (register_beq r (R_bitvector_64 misa))
        (register_beq r (R_bitvector_64 mstatus)).

  Lemma spt_Db_in (r : register) : spt_Db r = true -> r ∈ s_Drw ∪ s_Dro.
  Proof.
    unfold spt_Db. intros Hr.
    apply orb_true_elim in Hr as [Hr|Hr]; apply register_beq_eq in Hr; subst r;
      [exact s_in_misa | exact s_in_mst].
  Qed.

  Lemma spt_exec_cE_S (s : mstate) :
    register_lookup misa s.(sregs) = MISA_C ->
    exec (currentlyEnabled Ext_S) s = Some (true, s).
  Proof.
    intro Hmisa.
    apply (decode_state_bridge D_misa _ dstateM).
    - intros r Hr. unfold D_misa in Hr. apply register_beq_eq in Hr. subst r.
      rewrite Hmisa. vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
  Qed.

  Lemma spt_goodb_cE_S (s : mstate) :
    register_lookup misa s.(sregs) = MISA_C ->
    goodb spt_Db (currentlyEnabled Ext_S) s = true.
  Proof.
    intro Hmisa.
    apply (goodb_mono D_misa spt_Db).
    - intros r Hr. unfold D_misa in Hr. unfold spt_Db. by rewrite Hr.
    - apply (goodb_congr D_misa (currentlyEnabled Ext_S) dstateM s).
      + intros r Hr. unfold D_misa in Hr. apply register_beq_eq in Hr. subst r.
        rewrite Hmisa. vm_compute; reflexivity.
      + vm_compute; reflexivity.
  Qed.

  (* =================================================================== *)
  (* PART G -- THE S-MODE FETCH-SHAPE DISPATCH.                          *)
  (*                                                                     *)
  (* [WpInstrRun.swp_run_hart_active_instr_ex] one privilege over: it     *)
  (* takes the [instr] resource and dispatches on the fetch result hidden *)
  (* inside it and on pc's 4-alignment, four cases in all.  The three     *)
  (* differences from the M-mode dispatch are the whole of the S-mode     *)
  (* fetch story:                                                        *)
  (*                                                                     *)
  (*   - the text is read AT THE TRANSLATED pa ([pa_of ppn b], the        *)
  (*     window byte's own claim), not at its va;                        *)
  (*   - the PMP walk runs at Supervisor, where the fall-through is DENY; *)
  (*   - the translation is the REGIME's, handed in as a PERSISTENT       *)
  (*     obligation ([SRegime.sr_swp_translate] at [InstructionFetch tt]  *)
  (*     is emp-valid and therefore boxable, which is what lets the       *)
  (*     2-mod-4 base shape translate TWICE), and it may FILL THE TLB, so *)
  (*     the file it lands on is the tower at SOME tlb value.             *)
  (* =================================================================== *)
  Section SPtDispatch.
    (* NO [CurKtier] binder: [InstrBytes.instr] resolves the tier from the
       ambient instance, and a section binder here would shadow it and make
       the window's [↦ₓ□] a different proposition from the one the chunk
       lemmas ask for. *)
    Context (Df : register -> dfrac).
    Context (pc ms : SailStdpp.Values.mword 64) (bmi : bool)
            (cy ti ip mst0 : SailStdpp.Values.mword 64)
            (pcfg : type_of_register pmpcfg_n)
            (paddr : type_of_register pmpaddr_n)
            (mc : SailStdpp.Values.mword 32)
            (micfg misa0 mseccfg0 senv0 : SailStdpp.Values.mword 64)
            (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
            (satp0 mie0 mdv0 menv0 : SailStdpp.Values.mword 64).
    Context (Res : type_of_register tlb -> iProp Σ).

    Local Notation srs tv :=
      (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
         senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv).

    (* the landing family: the tower at SOME tlb value *)
    Local Notation Qtow :=
      (fun rsx : regstate => exists tv : type_of_register tlb, rsx = srs tv).
    (* the landing rider: the caller's [W], the regime residue at the file's
       own tlb value, and the reservation.  [W] rides here so the RETIRE arm
       sees it -- the trap arm gets it through [Qi]. *)
    Local Notation RtowW W :=
      (fun rsx : regstate =>
         (W ∗ Res (register_lookup tlb rsx) ∗ resv_any cpu_id)%I).

    Local Ltac srs_lk :=
      by rewrite ?s_rs_PC ?s_rs_nPC ?s_rs_ms ?s_rs_mi ?s_rs_cy ?s_rs_ti
         ?s_rs_ip ?s_rs_tlb ?s_rs_priv ?s_rs_mst ?s_rs_hart ?s_rs_pcfg
         ?s_rs_paddr ?s_rs_mc ?s_rs_micfg ?s_rs_misa ?s_rs_sec ?s_rs_pma
         ?s_rs_htif ?s_rs_elp ?s_rs_senv ?s_rs_satp ?s_rs_mie ?s_rs_mdl
         ?s_rs_menv.

    (* the decode's regime pins, at every tower in the landing family *)
    Local Lemma spt_decode_ok (tv : type_of_register tlb) :
      misa0 = MISA_C -> menv0 = MENVCFG_S ->
      decode_ok (s_Drw ∪ s_Dro) (srs tv).
    Proof.
      intros Hmisa Hmenv. rewrite /decode_ok. split_and!.
      - exact s_in_priv.
      - exact s_in_misa.
      - rewrite s_rs_priv. vm_compute. reflexivity.
      - rewrite s_rs_misa Hmisa. vm_compute. reflexivity.
      - rewrite s_rs_misa Hmisa. vm_compute. reflexivity.
      - rewrite s_rs_misa. exact Hmisa.
      - right. split_and!.
        + exact s_in_menv.
        + srs_lk.
        + rewrite s_rs_menv. exact Hmenv.
    Qed.

    (* THE DISPATCH OBLIGATION.  [W] is a caller-chosen rider, and the
       [None] arm hands the regime residue and the reservation frag back
       along with the frames: a caller whose SIE is SYMBOLIC reaches the
       TRAP arm through [Qi], and there it needs exactly those three to
       re-form its own bundle ([WpIntrInv] re-forms [sie_cap] from the tlb
       residue and carries its [wp_next] into the Löb re-entry).  A caller
       that cannot trap instantiates [W := emp] and drops the extras. *)
    Definition spt_disp_obl (tlbv : type_of_register tlb) (W : iProp Σ)
        (Qi : InterruptType -> Privilege -> iProp Σ) : iProp Σ :=
      (W -∗ Res tlbv -∗ resv_frag cpu_id None -∗
       hreg_frame (srs tlbv) s_Drw -∗ hreg_frame_ro Df (srs tlbv) s_Dro -∗
         swp (dispatchInterrupt Supervisor)
           (fun o => match o with
                     | Some (ii, pr) => Qi ii pr
                     | None => W ∗ Res tlbv ∗ resv_frag cpu_id None ∗
                               hreg_frame (srs tlbv) s_Drw ∗
                               hreg_frame_ro Df (srs tlbv) s_Dro
                     end))%I.

    (* the regime's fetch translation, at any claimed byte and any file in
       the landing family -- PERSISTENT, because the 2-mod-4 base shape
       translates twice *)
    Definition spt_tr_obl : iProp Σ :=
      (□ (∀ (va : SailStdpp.Values.mword 64) (ppn : mword 44)
            (tv : type_of_register tlb) (rr : option resv),
            ⌜(uint va < 274877906944)%Z⌝ -∗
            ⌜ktier_pin cur_ktier ppn va⌝ -∗
            kmap_at (svpn_of va) ppn KP_rx -∗
            resv_frag cpu_id rr -∗ Res tv -∗
            hreg_frame (srs tv) s_Drw -∗ hreg_frame_ro Df (srs tv) s_Dro -∗
            swp (translateAddr (Virtaddr va) (InstructionFetch tt))
              (fun r => ⌜r = Values.Ok (Physaddr (pa_of ppn va), PBMT_PMA,
                                        init_ext_ptw)⌝ ∗
                        ∃ tv' : type_of_register tlb,
                          Res tv' ∗ resv_any cpu_id ∗
                          hreg_frame (srs tv') s_Drw ∗
                          hreg_frame_ro Df (srs tv') s_Dro)))%I.

    Definition spt_ex_obl (is_rvc : bool) (i : instruction)
        (Q : regstate -> Prop) (Rr : regstate -> iProp Σ) (W : iProp Σ)
      : iProp Σ :=
      (∀ tv' : type_of_register tlb,
         W -∗ Res tv' -∗ resv_any cpu_id -∗
         hreg_frame (register_set (R_bitvector_64 nextPC)
             (add_vec_int pc (if is_rvc then 2 else 4)) (srs tv')) s_Drw -∗
         hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
             (add_vec_int pc (if is_rvc then 2 else 4)) (srs tv')) s_Dro -∗
         swp (execute i)
           (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                     ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                     hreg_frame rs2 s_Drw ∗ hreg_frame_ro Df rs2 s_Dro ∗ Rr rs2))%I.

    Definition spt_run_post (Q : regstate -> Prop) (Rr : regstate -> iProp Σ)
        (Qi : InterruptType -> Privilege -> iProp Σ) : Step -> iProp Σ :=
      (fun st => ((∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                  ∨ (∃ w : SailStdpp.Values.mword 32,
                       ⌜st = Step_Execute (RETIRE_SUCCESS, w)⌝ ∗
                       ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                       hreg_frame rs2 s_Drw ∗ hreg_frame_ro Df rs2 s_Dro ∗ Rr rs2))%I).

    (* the [_exf] rules land at a NAMED word; the dispatch's four arms each
       know their own and no caller does *)
    Local Lemma spt_ex_w (Q : regstate -> Prop) (Rr : regstate -> iProp Σ)
        (Qi : InterruptType -> Privilege -> iProp Σ)
        (w : SailStdpp.Values.mword 32) :
      swp (run_hart_active 0)
        (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                   ∨ (⌜st = Step_Execute (RETIRE_SUCCESS, w)⌝ ∗
                      ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                      hreg_frame rs2 s_Drw ∗ hreg_frame_ro Df rs2 s_Dro ∗ Rr rs2))
      -∗ swp (run_hart_active 0) (spt_run_post Q Rr Qi).
    Proof.
      iIntros "H". iApply (swp_mono with "[] H").
      iIntros (st) "[Hi | (-> & Hr)]".
      - by iLeft.
      - iRight. iExists w. by iFrame.
    Qed.

    (* the execute obligation, adapted to the [_exf] rules' shape *)
    Local Lemma spt_ex_adapt (is_rvc : bool) (i : instruction)
        (Q : regstate -> Prop) (Rr : regstate -> iProp Σ) (W : iProp Σ) :
      spt_ex_obl is_rvc i Q Rr W -∗
      (∀ rsf : regstate, ⌜Qtow rsf⌝ -∗ RtowW W rsf -∗
       hreg_frame (register_set (R_bitvector_64 nextPC)
           (add_vec_int pc (if is_rvc then 2 else 4)) rsf) s_Drw -∗
       hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
           (add_vec_int pc (if is_rvc then 2 else 4)) rsf) s_Dro -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                   hreg_frame rs2 s_Drw ∗ hreg_frame_ro Df rs2 s_Dro ∗ Rr rs2)).
    Proof.
      iIntros "Hex" (rsf) "%HQ (HW & HRes & Hany) Hrw Hro".
      destruct HQ as (tv & ->). rewrite s_rs_tlb.
      iApply ("Hex" $! tv with "HW HRes Hany Hrw Hro").
    Qed.


    (* the dispatch obligation, discharged: SIE clear makes [s_dispatch]
       [None] whatever the PLIC wires hold. *)
    Lemma spt_dispatch_none (tv : type_of_register tlb) (W : iProp Σ)
        (Qi : InterruptType -> Privilege -> iProp Σ) :
      misa0 = MISA_C ->
      eq_vec (_get_Mstatus_SIE mst0) ('b"1") = false ->
      and_vec mie0 (not_vec mdv0) = zeros' 64 ->
      gen_cert -∗ spt_disp_obl tv W Qi.
    Proof.
      intros Hmisa HSIE Hmm.
      assert (Lmisa : register_lookup misa
                        (MState (srs tv) ∅ dev0_state).(sregs) = MISA_C).
      { change ((MState (srs tv) ∅ dev0_state).(sregs)) with (srs tv).
        rewrite s_rs_misa. exact Hmisa. }
      assert (Lmst : register_lookup mstatus
                       (MState (srs tv) ∅ dev0_state).(sregs) = mst0).
      { change ((MState (srs tv) ∅ dev0_state).(sregs)) with (srs tv).
        apply s_rs_mst. }
      iIntros "#Hcert HW HRes Hfrag Hrw Hro".
      iApply (swp_mono with "[HW HRes Hfrag] [-]");
        [| iApply (swp_dispatchInterrupt_S s_Drw s_Dro Df (srs tv)
                     (MState (srs tv) ∅ dev0_state) spt_Db ip mie0 mdv0 mst0
                     s_disj s_in_ip s_in_mie s_in_mdl eq_refl
                     ltac:(spt_srs) ltac:(spt_srs) ltac:(spt_srs) Lmst Hmm
                     spt_Db_in (fun r _ => eq_refl)
                     (spt_exec_cE_S (MState (srs tv) ∅ dev0_state) Lmisa)
                     (spt_goodb_cE_S (MState (srs tv) ∅ dev0_state) Lmisa)
                     with "Hcert Hrw Hro") ].
      iIntros (o). iDestruct 1 as (meip seip) "(-> & Hrw & Hro)".
      unfold s_dispatch. rewrite HSIE. cbn [andb]. iFrame.
    Qed.

    (* THE DISPATCH.  Four arms: F_Base / F_RVC crossed with pc's
       4-alignment, exactly the four the physical fetch has. *)
    Lemma spt_run_hart_active_instr_S (tlbv : type_of_register tlb)
        (is_rvc : bool) (i : instruction) (Q : regstate -> Prop)
        (Rr : regstate -> iProp Σ) (W : iProp Σ)
        (Qi : InterruptType -> Privilege -> iProp Σ) :
      misa0 = MISA_C ->
      menv0 = MENVCFG_S ->
      eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
      pma_allows_ram pmar0 ->
      pmpAddrMatchType_encdec_backwards
        (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
      zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
      eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pcfg 0)) ('b"1") = true ->
      (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
      gen_cert -∗
      instr pc is_rvc i -∗
      W -∗
      resv_frag cpu_id None -∗
      Res tlbv -∗
      hreg_frame (srs tlbv) s_Drw -∗
      hreg_frame_ro Df (srs tlbv) s_Dro -∗
      spt_disp_obl tlbv W Qi -∗
      spt_tr_obl -∗
      spt_ex_obl is_rvc i Q Rr W -∗
      swp (run_hart_active 0) (spt_run_post Q Rr Qi).
    Proof.
      intros Hmisa Hmenv Help Hpallow HA Hord HX Hcov.
      iIntros "#Hcert Hinstr HW Hfrag0 HRes Hrw Hro Hdisp #Htr Hex".
      (* [spt_disp_obl]'s three extras, re-associated into the ONE rider
         [swp_run_hart_active_gen_exf] threads from the dispatch to the
         fetch.  Done once, before the shape split, since all four arms
         run the dispatch at the same tower. *)
      iAssert ((W ∗ Res tlbv ∗ resv_frag cpu_id None) -∗
               hreg_frame (srs tlbv) s_Drw -∗
               hreg_frame_ro Df (srs tlbv) s_Dro -∗
               swp (dispatchInterrupt Supervisor)
                 (fun o => match o with
                           | Some (ii, pr) => Qi ii pr
                           | None => (W ∗ Res tlbv ∗ resv_frag cpu_id None) ∗
                                     hreg_frame (srs tlbv) s_Drw ∗
                                     hreg_frame_ro Df (srs tlbv) s_Dro
                           end))%I with "[Hdisp]" as "Hdisp'".
      { iIntros "(HW & HRes & Hfrag) Hrw Hro".
        iApply (swp_mono with "[] [-]");
          [| iApply ("Hdisp" with "HW HRes Hfrag Hrw Hro") ].
        iIntros (o). destruct o as [[ii pr] |].
        - iIntros "H". iExact "H".
        - iIntros "(HW & HRes & Hfrag & Hrw & Hro)". iFrame. }
      iDestruct "Hinstr" as "(%Hlpi & Hib)".
      iDestruct "Hib" as (r) "(%Hrvc & Hbytes & %Hdec)".
      iEval (rewrite /instr_bytes) in "Hbytes".
      iDestruct "Hbytes" as "[%H2al Hbytes]".
      pose proof (fun tv : type_of_register tlb =>
                    hfrun_lpad (s_Drw ∪ s_Dro) s_Drw (srs tv) s_in_elp
                      ltac:(rewrite s_rs_elp; exact Help)) as Hlp.
      destruct r as [e | w | h | erx]; [ done | | | done ];
        cbn [fetch_is_rvc decode_fetch] in Hrvc, Hdec; subst is_rvc.

      - (* ======================= F_Base w ========================== *)
        iDestruct "Hbytes" as "[%HnotRVC #Hb]".
        destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
        + (* ---- 4-aligned: one 4-byte read ---- *)
          destruct (align4_low_bits pc Hal) as [Hbit0 Hbit1].
          iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "#Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iEval (rewrite pa_add_0) in "Hb0".
          iDestruct (code_text with "Hb0") as (ppn) "(#Hk & _ & %Hid)".
          iDestruct (text_canonical with "Hb0") as %Hcan.
          pose proof (off4_bound pc Hal) as Hoff.
          rewrite (uint_unsigned_n _) in Hoff.
          iDestruct (s_chunk_ram pc pc 0 4 4 (nth_byte w) ppn
                       ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                       with "Hk Hb") as %[Hram0 Hram3].
          iApply (spt_ex_w Q Rr Qi _).
          iApply (swp_run_hart_active_gen_exf s_Drw s_Dro Df (srs tlbv)
                    Qtow Q (RtowW W) (W ∗ Res tlbv ∗ resv_frag cpu_id None)%I Supervisor pc w i 8 Rr Qi
                    s_disj s_in_priv s_in_PC s_w_nPC ltac:(srs_lk)
                    ltac:(intros rsf (tv & ->); srs_lk)
                    ltac:(intros rsf (tv & ->);
                          exact (Hdec _ _ _ (spt_decode_ok tv Hmisa Hmenv)))
                    ltac:(intros rsf (tv & ->); exact (Hlp tv))
                    with "Hcert Hrw Hro [$HW $HRes $Hfrag0] Hdisp' [] [Hex]").
          2:{ iApply (spt_ex_adapt false i Q Rr W with "Hex"). }
          iIntros "(HW & HRes & Hany) Hrw Hro".
          iApply (swp_mono with "[] [-]");
            [| iApply (spt_fetch_S_P s_Drw s_Dro Df (srs tlbv) Qtow (RtowW W) pc
                         (pa_of ppn pc) w s_disj s_in_PC s_in_mst s_in_priv
                         ltac:(srs_lk) ltac:(intros rsf (tv & ->); srs_lk)
                         Hbit0 Hbit1 Hal
                         with "Hcert Hrw Hro [Hany HRes HW] []") ].
          * iIntros (rr) "(%Hr & Hf)". rewrite HnotRVC in Hr. subst rr.
            by iFrame.
          * iIntros "Hrw Hro". iRename "Hany" into "Hfrag".
            iApply (swp_mono with "[HW] [-]");
              [| iApply ("Htr" $! pc ppn tlbv None with
                           "[%] [%] Hk Hfrag HRes Hrw Hro") ].
            2:{ exact Hcan. }
            2:{ exact Hid. }
            iIntros (v) "(-> & Hf)". iSplitR; [done|].
            iDestruct "Hf" as (tv') "(HRes & Hany & Hrw & Hro)".
            iExists (srs tv'). iSplitR; [iPureIntro; by exists tv' |].
            rewrite s_rs_tlb. iFrame.
          * iIntros (rsf) "%HQ Hrw Hro". destruct HQ as (tv & ->).
            iApply (swp_checked_mem_read_ifetch4_S s_Drw s_Dro Df (srs tv)
                      (pa_of ppn pc) pmar0 pcfg paddr w s_disj s_in_pma
                      s_in_pcfg s_in_paddr s_in_htif ltac:(srs_lk)
                      ltac:(srs_lk) ltac:(srs_lk) ltac:(srs_lk)
                      HA Hord HX Hcov Hpallow Hram0 Hram3
                      (pa4_aligned ppn pc Hal) with "Hcert Hrw Hro []").
            iApply (s_text_obl pc pc 0%nat 4%nat 4%N (nth_byte w) ppn w
                      ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                      (fun j _ => eq_refl) with "Hk Hb").

        + (* ---- 2 mod 4: two halfword reads, two translations ---- *)
          destruct (align2_not4_facts pc H2al Hal) as (_ & Hbit0 & Hbit1).
          assert (Hvah2 : is_aligned_vaddr (Virtaddr (add_vec_int pc 2)) 2 = true).
          { pose proof (align2_plus2 pc H2al) as Hh. rewrite fetch_pa_id in Hh.
            exact Hh. }
          assert (HbaseH : forall k : nat,
                    pa_add pc (2 + k)%nat = pa_add (add_vec_int pc 2) k).
          { intros k. unfold pa_add. rewrite avi_assoc. f_equal. lia. }
          iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "#Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iEval (rewrite pa_add_0) in "Hb0".
          iDestruct (code_text with "Hb0") as (ppnl) "(#Hkl & _ & %Hidl)".
          iDestruct (text_canonical with "Hb0") as %Hcanl.
          pose proof (off_bound_div pc 2 ltac:(lia) ltac:(exists 2048; lia) H2al)
            as Hoffl. rewrite (uint_unsigned_n _) in Hoffl.
          iDestruct (big_sepL_lookup _ _ 2%nat 2%nat with "Hb") as "#Hb2".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (code_text with "Hb2") as (ppnh) "(#Hkh & _ & %Hidh)".
          iDestruct (text_canonical with "Hb2") as %Hcanh.
          pose proof (off_bound_div (add_vec_int pc 2) 2 ltac:(lia)
                        ltac:(exists 2048; lia) Hvah2) as Hoffh.
          rewrite (uint_unsigned_n _) in Hoffh.
          iDestruct (s_chunk_ram pc pc 0 2 4 (nth_byte w) ppnl
                       ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoffl Hcanl
                       with "Hkl Hb") as %[Hraml0 Hraml1].
          iDestruct (s_chunk_ram pc (add_vec_int pc 2) 2 2 4 (nth_byte w) ppnh
                       ltac:(lia) ltac:(lia) HbaseH Hoffh Hcanh
                       with "Hkh Hb") as %[Hramh0 Hramh1].
          iApply (spt_ex_w Q Rr Qi _).
          iApply (swp_run_hart_active_gen_exf s_Drw s_Dro Df (srs tlbv)
                    Qtow Q (RtowW W) (W ∗ Res tlbv ∗ resv_frag cpu_id None)%I Supervisor pc
                    (concat_vec (subrange_vec_dec w 31 16)
                       (subrange_vec_dec w 15 0)) i 8 Rr Qi
                    s_disj s_in_priv s_in_PC s_w_nPC ltac:(srs_lk)
                    ltac:(intros rsf (tv & ->); srs_lk)
                    ltac:(intros rsf (tv & ->);
                          rewrite concat_subranges_id;
                          exact (Hdec _ _ _ (spt_decode_ok tv Hmisa Hmenv)))
                    ltac:(intros rsf (tv & ->); exact (Hlp tv))
                    with "Hcert Hrw Hro [$HW $HRes $Hfrag0] Hdisp' [] [Hex]").
          2:{ iApply (spt_ex_adapt false i Q Rr W with "Hex"). }
          iIntros "(HW & HRes & Hany) Hrw Hro".
          iApply (spt_fetch_S_base2_P s_Drw s_Dro Df (srs tlbv) Qtow Qtow
                    (RtowW W) (RtowW W) pc (pa_of ppnl pc)
                    (pa_of ppnh (add_vec_int pc 2))
                    (subrange_vec_dec w 15 0) (subrange_vec_dec w 31 16)
                    s_disj s_in_PC s_in_misa s_in_mst s_in_priv
                    ltac:(srs_lk) ltac:(intros rs1 (tv & ->); srs_lk)
                    ltac:(intros rs1 (tv & ->); srs_lk)
                    ltac:(intros rs2 (tv & ->); srs_lk)
                    ltac:(rewrite s_rs_misa Hmisa; vm_compute; reflexivity)
                    Hbit0 Hbit1 Hal
                    HnotRVC
                    with "Hcert Hrw Hro [Hany HRes HW] [] [] []").
          * iIntros "Hrw Hro". iRename "Hany" into "Hfrag".
            iApply (swp_mono with "[HW] [-]");
              [| iApply ("Htr" $! pc ppnl tlbv None with
                           "[%] [%] Hkl Hfrag HRes Hrw Hro") ].
            2:{ exact Hcanl. }
            2:{ exact Hidl. }
            iIntros (v) "(-> & Hf)". iSplitR; [done|].
            iDestruct "Hf" as (tv') "(HRes & Hany & Hrw & Hro)".
            iExists (srs tv'). iSplitR; [iPureIntro; by exists tv' |].
            rewrite s_rs_tlb. iFrame.
          * iIntros (rs1) "%HQ Hrw Hro". destruct HQ as (tv & ->).
            iApply (swp_checked_mem_read_ifetch2_S s_Drw s_Dro Df (srs tv)
                      (pa_of ppnl pc) pmar0 pcfg paddr
                      (subrange_vec_dec w 15 0) s_disj s_in_pma
                      s_in_pcfg s_in_paddr s_in_htif ltac:(srs_lk)
                      ltac:(srs_lk) ltac:(srs_lk) ltac:(srs_lk)
                      HA Hord HX Hcov Hpallow Hraml0 Hraml1
                      (pa_aligned_div ppnl pc 2 ltac:(lia)
                         ltac:(exists 2048; lia) H2al)
                      with "Hcert Hrw Hro []").
            iApply (s_text_obl pc pc 0%nat 4%nat 2%N (nth_byte w) ppnl
                      (subrange_vec_dec w 15 0)
                      ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoffl Hcanl
                      ltac:(intros j Hj;
                            exact (eq_sym (nth_byte_subrange_lo w j Hj)))
                      with "Hkl Hb").
          * iIntros (rs1) "%HQ (HW & HRes & Hany) Hrw Hro".
            destruct HQ as (tv & ->). rewrite s_rs_tlb.
            iDestruct "Hany" as (rr) "Hfrag".
            iApply (swp_mono with "[HW] [-]");
              [| iApply ("Htr" $! (add_vec_int pc 2) ppnh tv rr with
                           "[%] [%] Hkh Hfrag HRes Hrw Hro") ].
            2:{ exact Hcanh. }
            2:{ exact Hidh. }
            iIntros (v) "(-> & Hf)". iSplitR; [done|].
            iDestruct "Hf" as (tv') "(HRes & Hany & Hrw & Hro)".
            iExists (srs tv'). iSplitR; [iPureIntro; by exists tv' |].
            rewrite s_rs_tlb. iFrame.
          * iIntros (rs2) "%HQ Hrw Hro". destruct HQ as (tv & ->).
            iApply (swp_checked_mem_read_ifetch2_S s_Drw s_Dro Df (srs tv)
                      (pa_of ppnh (add_vec_int pc 2)) pmar0 pcfg paddr
                      (subrange_vec_dec w 31 16) s_disj s_in_pma
                      s_in_pcfg s_in_paddr s_in_htif ltac:(srs_lk)
                      ltac:(srs_lk) ltac:(srs_lk) ltac:(srs_lk)
                      HA Hord HX Hcov Hpallow Hramh0 Hramh1
                      (pa_aligned_div ppnh (add_vec_int pc 2) 2 ltac:(lia)
                         ltac:(exists 2048; lia) Hvah2)
                      with "Hcert Hrw Hro []").
            iApply (s_text_obl pc (add_vec_int pc 2) 2%nat 4%nat 2%N
                      (nth_byte w) ppnh (subrange_vec_dec w 31 16)
                      ltac:(lia) ltac:(lia) HbaseH Hoffh Hcanh
                      ltac:(intros j Hj;
                            exact (eq_sym (nth_byte_subrange_hi w j Hj)))
                      with "Hkh Hb").

      - (* ======================= F_RVC h =========================== *)
        iDestruct "Hbytes" as "[%HisRVC Hbytes]".
        destruct Hdec as (i0 & Hlp0 & Hdec2).
        destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
        + (* ---- 4-aligned: the halfword sits in a 4-byte word ---- *)
          iDestruct "Hbytes" as (w) "[%Hsub #Hb]".
          destruct (align4_low_bits pc Hal) as [Hbit0 Hbit1].
          iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "#Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iEval (rewrite pa_add_0) in "Hb0".
          iDestruct (code_text with "Hb0") as (ppn) "(#Hk & _ & %Hid)".
          iDestruct (text_canonical with "Hb0") as %Hcan.
          pose proof (off4_bound pc Hal) as Hoff.
          rewrite (uint_unsigned_n _) in Hoff.
          iDestruct (s_chunk_ram pc pc 0 4 4 (nth_byte w) ppn
                       ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                       with "Hk Hb") as %[Hram0 Hram3].
          iApply (spt_ex_w Q Rr Qi _).
          iApply (swp_run_hart_active_gen_rvc_exf s_Drw s_Dro Df (srs tlbv)
                    Qtow Q (RtowW W) (W ∗ Res tlbv ∗ resv_frag cpu_id None)%I Supervisor pc h i0 i 8 Rr Qi
                    s_disj s_in_priv s_in_misa s_in_PC s_w_nPC ltac:(srs_lk)
                    ltac:(intros rsf (tv & ->); srs_lk)
                    ltac:(intros rsf (tv & ->); rewrite s_rs_misa Hmisa;
                          vm_compute; reflexivity)
                    ltac:(intros rsf (tv & ->);
                          exact (proj1 (Hdec2 _ _ _
                                   (spt_decode_ok tv Hmisa Hmenv))))
                    ltac:(intros rsf (tv & ->); exact (Hlp tv))
                    with "Hcert Hrw Hro [$HW $HRes $Hfrag0] Hdisp' [] [] [Hex]").
          2:{ iIntros (rsf) "%HQ Hrw Hro". destruct HQ as (tv & ->).
              iApply (swp_span s_Drw s_Dro Df _ _ _ _ s_disj
                        (proj2 (Hdec2 _ _ _ (decode_ok_set_nPC _ _ _
                                  (spt_decode_ok tv Hmisa Hmenv))))
                        with "Hcert Hrw Hro"). }
          2:{ iApply (spt_ex_adapt true i Q Rr W with "Hex"). }
          iIntros "(HW & HRes & Hany) Hrw Hro".
          iApply (swp_mono with "[] [-]");
            [| iApply (spt_fetch_S_P s_Drw s_Dro Df (srs tlbv) Qtow (RtowW W) pc
                         (pa_of ppn pc) w s_disj s_in_PC s_in_mst s_in_priv
                         ltac:(srs_lk) ltac:(intros rsf (tv & ->); srs_lk)
                         Hbit0 Hbit1 Hal
                         with "Hcert Hrw Hro [Hany HRes HW] []") ].
          * iIntros (rr) "(%Hr & Hf)". rewrite Hsub HisRVC in Hr. subst rr.
            by iFrame.
          * iIntros "Hrw Hro". iRename "Hany" into "Hfrag".
            iApply (swp_mono with "[HW] [-]");
              [| iApply ("Htr" $! pc ppn tlbv None with
                           "[%] [%] Hk Hfrag HRes Hrw Hro") ].
            2:{ exact Hcan. }
            2:{ exact Hid. }
            iIntros (v) "(-> & Hf)". iSplitR; [done|].
            iDestruct "Hf" as (tv') "(HRes & Hany & Hrw & Hro)".
            iExists (srs tv'). iSplitR; [iPureIntro; by exists tv' |].
            rewrite s_rs_tlb. iFrame.
          * iIntros (rsf) "%HQ Hrw Hro". destruct HQ as (tv & ->).
            iApply (swp_checked_mem_read_ifetch4_S s_Drw s_Dro Df (srs tv)
                      (pa_of ppn pc) pmar0 pcfg paddr w s_disj s_in_pma
                      s_in_pcfg s_in_paddr s_in_htif ltac:(srs_lk)
                      ltac:(srs_lk) ltac:(srs_lk) ltac:(srs_lk)
                      HA Hord HX Hcov Hpallow Hram0 Hram3
                      (pa4_aligned ppn pc Hal) with "Hcert Hrw Hro []").
            iApply (s_text_obl pc pc 0%nat 4%nat 4%N (nth_byte w) ppn w
                      ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                      (fun j _ => eq_refl) with "Hk Hb").

        + (* ---- 2 mod 4: a bare halfword read ---- *)
          iDestruct "Hbytes" as "#Hb".
          destruct (align2_not4_facts pc H2al Hal) as (_ & Hbit0 & Hbit1).
          iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "#Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iEval (rewrite pa_add_0) in "Hb0".
          iDestruct (code_text with "Hb0") as (ppn) "(#Hk & _ & %Hid)".
          iDestruct (text_canonical with "Hb0") as %Hcan.
          pose proof (off_bound_div pc 2 ltac:(lia) ltac:(exists 2048; lia) H2al)
            as Hoff. rewrite (uint_unsigned_n _) in Hoff.
          iDestruct (s_chunk_ram pc pc 0 2 2 (nth_byte h) ppn
                       ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                       with "Hk Hb") as %[Hram0 Hram1].
          iApply (spt_ex_w Q Rr Qi _).
          iApply (swp_run_hart_active_gen_rvc_exf s_Drw s_Dro Df (srs tlbv)
                    Qtow Q (RtowW W) (W ∗ Res tlbv ∗ resv_frag cpu_id None)%I Supervisor pc h i0 i 8 Rr Qi
                    s_disj s_in_priv s_in_misa s_in_PC s_w_nPC ltac:(srs_lk)
                    ltac:(intros rsf (tv & ->); srs_lk)
                    ltac:(intros rsf (tv & ->); rewrite s_rs_misa Hmisa;
                          vm_compute; reflexivity)
                    ltac:(intros rsf (tv & ->);
                          exact (proj1 (Hdec2 _ _ _
                                   (spt_decode_ok tv Hmisa Hmenv))))
                    ltac:(intros rsf (tv & ->); exact (Hlp tv))
                    with "Hcert Hrw Hro [$HW $HRes $Hfrag0] Hdisp' [] [] [Hex]").
          2:{ iIntros (rsf) "%HQ Hrw Hro". destruct HQ as (tv & ->).
              iApply (swp_span s_Drw s_Dro Df _ _ _ _ s_disj
                        (proj2 (Hdec2 _ _ _ (decode_ok_set_nPC _ _ _
                                  (spt_decode_ok tv Hmisa Hmenv))))
                        with "Hcert Hrw Hro"). }
          2:{ iApply (spt_ex_adapt true i Q Rr W with "Hex"). }
          iIntros "(HW & HRes & Hany) Hrw Hro".
          iApply (spt_fetch_S_rvc2_P s_Drw s_Dro Df (srs tlbv) Qtow (RtowW W) pc
                    (pa_of ppn pc) h s_disj s_in_PC s_in_misa s_in_mst
                    s_in_priv ltac:(srs_lk)
                    ltac:(intros rsf (tv & ->); srs_lk)
                    ltac:(rewrite s_rs_misa Hmisa; vm_compute; reflexivity)
                    Hbit0 Hbit1 Hal HisRVC
                    with "Hcert Hrw Hro [Hany HRes HW] []").
          * iIntros "Hrw Hro". iRename "Hany" into "Hfrag".
            iApply (swp_mono with "[HW] [-]");
              [| iApply ("Htr" $! pc ppn tlbv None with
                           "[%] [%] Hk Hfrag HRes Hrw Hro") ].
            2:{ exact Hcan. }
            2:{ exact Hid. }
            iIntros (v) "(-> & Hf)". iSplitR; [done|].
            iDestruct "Hf" as (tv') "(HRes & Hany & Hrw & Hro)".
            iExists (srs tv'). iSplitR; [iPureIntro; by exists tv' |].
            rewrite s_rs_tlb. iFrame.
          * iIntros (rsf) "%HQ Hrw Hro". destruct HQ as (tv & ->).
            iApply (swp_checked_mem_read_ifetch2_S s_Drw s_Dro Df (srs tv)
                      (pa_of ppn pc) pmar0 pcfg paddr h s_disj s_in_pma
                      s_in_pcfg s_in_paddr s_in_htif ltac:(srs_lk)
                      ltac:(srs_lk) ltac:(srs_lk) ltac:(srs_lk)
                      HA Hord HX Hcov Hpallow Hram0 Hram1
                      (pa_aligned_div ppn pc 2 ltac:(lia)
                         ltac:(exists 2048; lia) H2al)
                      with "Hcert Hrw Hro []").
            iApply (s_text_obl pc pc 0%nat 2%nat 2%N (nth_byte h) ppn h
                      ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                      (fun j _ => eq_refl) with "Hk Hb").
    Qed.

  End SPtDispatch.


  (* =================================================================== *)
  (* PART H -- THE THREE WRAPPERS.                                        *)
  (*                                                                     *)
  (* WHAT THEY ARE PARAMETERISED BY, and why the RAW-CELL one is not      *)
  (* parameterised by [R : s_regime] (the choice this conversion had to    *)
  (* make, and the reason, recorded so it is not re-litigated):            *)
  (*                                                                     *)
  (*   [SRegime.sr_swp_res] is a function of the FILE, and                *)
  (*   [sr_swp_side] mentions the file and a reference [mstate] as well.  *)
  (*   The wrapper's file is a TOWER whose components ([ms], [bmi], the   *)
  (*   clock cells, the [hw_config] pins) come out of [pc_is] and         *)
  (*   [hw_config] EXISTENTIALLY, so no premise of the wrapper can name   *)
  (*   it -- a bundle "the residue at the tower" is not statable.  So the *)
  (*   wrapper takes                                                     *)
  (*     - [Res : type_of_register tlb -> iProp Σ], the residue as a      *)
  (*       function of the one component of the file it actually depends  *)
  (*       on (it is [KptShare.tlb_snap_ok tv ∗ kpt_inv] at               *)
  (*       [kpt_share_regime], [True] at [bare_regime]), and          *)
  (*     - the regime's FETCH TRANSLATION as a persistent obligation      *)
  (*       ([spt_tr_obl], which is [sr_swp_translate] at                  *)
  (*       [InstructionFetch tt] instantiated at the tower).              *)
  (*   A caller discharges the obligation from [RS.(sr_swp_translate)] --  *)
  (*   that field is ∀-over-files, so instantiating it at a tower is      *)
  (*   free, and its side condition is discharged by the caller, which is *)
  (*   where [sr_swp_side] was designed to be discharged.                 *)
  (* =================================================================== *)

  (* the cycle rule the wrappers sit on: [WpSFrames.s_cycle_any] with the
     body's rider INDEXED BY THE POST FILE.

     THIS IS THE ONE PIECE THIS CONVERSION COULD NOT BUILD, and the reason
     is exact.  A walking fetch lands the frames on the tower at a tlb
     value the walk CHOOSES ([spt_run_hart_active_instr_S]'s conclusion is
     existential in it, because no caller knows whether the TLB hits).  The
     regime's residue comes back at THAT value, and the continuation needs
     it paired with the tlb CELL, which arrives inside the post-cycle
     frames.  With [HartStepAny.swp_exec_step_any]'s rider a plain
     [iProp Σ] the pairing cannot be expressed: the rider cannot mention
     the post file, and the pure [Q] cannot mention a resource.  Indexing
     the rider by the post file -- which is what this statement does, and
     what [swp_exec_step_any] (and [wp_loop_cycle] under it) must be
     generalized to -- makes it immediate: the continuation receives
     [Psi rs2] for the SAME [rs2] the agreement names, and [tlb ∉
     tk_clock3], so [register_lookup tlb rs3 = register_lookup tlb rs2].

     [WpSFrames.s_cycle]'s [tlb_snap_ok tlbv'] premise has the same
     problem one level up: it asks the CALLER to name the landing tlb
     value before the body runs.  Both are the same gap. *)
  Lemma spt_cycle (Df : register -> dfrac) (pc : mword 64)
      (Psi : regstate -> iProp Σ) (Q : regstate -> Prop)
      (ms : mword 64) (bmi : bool) (cy ti ip mst0 : mword 64)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
      (satp0 mie0 mdv0 menv0 : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (tlbv : type_of_register tlb) :
    (forall rs2, Q rs2 -> register_lookup hart_state rs2 = HART_ACTIVE tt) ->
    (forall rs2, Q rs2 ->
       register_lookup (R_bool minstret_increment) rs2
       = minstret_inc_flag mc micfg Supervisor) ->
    gen_cert -∗
    resv_any cpu_id -∗
    hreg_frame (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                  mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv)
      s_Drw -∗
    hreg_frame_ro Df
      (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
         mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv) s_Dro -∗
    (resv_frag cpu_id None -∗
     hreg_frame (s_rs pc pc ms (minstret_inc_flag mc micfg Supervisor)
                   cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0
                   pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv) s_Drw -∗
     hreg_frame_ro Df
       (s_rs pc pc ms (minstret_inc_flag mc micfg Supervisor)
          cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0
          pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv) s_Dro -∗
       swp (run_hart_active 0)
         (fun st => ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
            match st with
            | Step_Execute (Retire_Success tt, _) =>
                hreg_frame rs2 s_Drw ∗
                hreg_frame_ro Df rs2 s_Dro ∗ Psi rs2
            | Step_Pending_Interrupt (i, p) =>
                swp (handle_interrupt i p)
                  (fun _ => hreg_frame rs2 s_Drw ∗
                            hreg_frame_ro Df rs2 s_Dro ∗ Psi rs2)
            | _ => False
            end)) -∗
    ▷ (∀ (rs3 rs2 : regstate) (mi : mword 64),
         ⌜Q rs2 /\
           reg_agree_on ((s_Drw ∪ s_Dro) ∖ tk_clock3) rs3
             (wrap_post rs2 mi)⌝ -∗
         hreg_frame rs3 s_Drw -∗
         hreg_frame_ro Df rs3 s_Dro -∗ Psi rs2 -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HQhart HQmi.
    iIntros "#Hcert Hfrag Hrw Hro Hbody Hcont".
    iApply (swp_exec_step_any_ex s_Drw s_Dro Df
              (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv)
              (s_rs pc pc ms (minstret_inc_flag mc micfg Supervisor)
                 cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0
                 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv) Q Psi
              s_disj s_w_cy s_w_ti s_w_ip s_in_priv s_in_hart s_in_mc
              s_in_micfg s_w_mi s_in_mi s_w_ms s_in_ms s_w_PC s_in_PC
              s_in_nPC ltac:(spt_srs) HQhart
              ltac:(intros rs2 HQ; rewrite (HQmi rs2 HQ);
                    by rewrite s_rs_mc s_rs_micfg s_rs_priv)
              (s_pre_agree pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv)
              with "Hcert Hfrag Hrw Hro [Hbody] Hcont").
    (* [swp_exec_step_any_ex]'s body premise is UNDER A LATER (the body runs
       at the next language step, so a caller may build it from a resource a
       step produces).  Absorbed here rather than threaded: no consumer of
       [spt_cycle] or of the wrappers needs it, and threading it would put an
       [iNext] in every leaf's obligation for nothing. *)
    iNext. iExact "Hbody".
  Qed.



  (* [HartSFrame.s_ro_ext] is stated at [s_Df dq]; this wrapper's frame is at
     [s_Df_mix dq] (satp and the two PMP cells at full ownership), so the
     transport is restated at an arbitrary [Df].  Belongs beside its twin. *)
  Lemma s_ro_ext_gen (Df : register -> dfrac) (rs rs' : regstate) :
    reg_agree_on (s_Drw ∪ s_Dro) rs rs' ->
    hreg_frame_ro Df rs s_Dro -∗ (hreg_frame_ro Df rs' s_Dro : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ro_ext _ _ _ s_Dro (s_agree_ro _ _ Hag)).
    iIntros "H". iExact "H".
  Qed.

  (* the raw-cell <-> frame bridge, [WpSFrames.sm_frames_intro]'s twin with
     the config arriving as CELLS (so no [smode_config] is built) and the
     regime's four cells likewise raw.  [s_Df_mix dq] is exactly this
     split: the config cells at the caller's fraction, satp and the two PMP
     cells at full ownership. *)
  Lemma spt_frames_intro (dq : dfrac) (pc : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 satp0 : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (tlbv : type_of_register tlb) :
    hw_config -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    satp ↦ᵣ satp0 -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
    tlb ↦ᵣ tlbv -∗
    pc_is pc -∗
    resv_any cpu_id ∗
    ∃ (ms : mword 64) (bmi : bool) (cy ti ip : mword 64) (mc : mword 32)
      (micfg misa0 mseccfg0 senv0 : mword 64) (pmar0 : list PMA_Region)
      (elp0 : type_of_register elp),
      ⌜ misa0 = MISA_C ⌝ ∗
      ⌜ pma_allows_all pmar0 ⌝ ∗
      ⌜ eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ⌝ ∗
      hreg_frame (s_rs pc pc ms bmi cy ti ip mstatus0 pcfg paddr mc micfg
                    misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie_v mdv0
                    menvcfg0 tlbv) s_Drw ∗
      hreg_frame_ro (s_Df_mix dq)
        (s_rs pc pc ms bmi cy ti ip mstatus0 pcfg paddr mc micfg misa0
           mseccfg0 senv0 pmar0 elp0 satp0 mie_v mdv0 menvcfg0 tlbv) s_Dro.
  Proof.
    iIntros "#Hhw Hhs Hpriv Hmst Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc Hpc".
    iDestruct "Hpc" as "(HPC & HnPC & Hmr & Hcr & Hresv)". iFrame "Hresv".
    iDestruct "Hmr" as (ms bmi mc micfg) "(Hms & Hmi & #Hmc & #Hmicfg)".
    iDestruct "Hcr" as (cy ti ip) "(Hcy & Hti & Hip)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmS & %HmC &
        %HmU & %HmM & %Hpmaall & %Hsec1 & %Hsec2 & %Helpnp & %HmA &
        %Hmisaval & %Hsecval & _)".
    iExists ms, bmi, cy, ti, ip, mc, micfg, misa0, mseccfg0,
            (mword_of_int 0 : mword 64), pmar0, elp0.
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitL "HPC HnPC Hms Hmi Hcy Hti Hip Htlbc".
    - rewrite s_rw_split.
      rewrite s_rs_PC s_rs_nPC s_rs_ms s_rs_mi s_rs_cy s_rs_ti s_rs_ip
        s_rs_tlb. iFrame.
    - rewrite s_ro_split_mix.
      rewrite s_rs_priv s_rs_mst s_rs_hart s_rs_pcfg s_rs_paddr s_rs_mc
        s_rs_micfg s_rs_misa s_rs_sec s_rs_pma s_rs_htif s_rs_elp
        s_rs_senv s_rs_satp s_rs_mie s_rs_mdl s_rs_menv.
      iFrame "Hpriv Hmst Hhs Hpcfg Hpaddr Hsatp Hmie Hmdl Hmenv".
      by iFrame "Hmc Hmicfg Hmisa Hmseccfg Hpma Hhtif Help Hsenv".
  Qed.



  (* ------------------------------------------------------------------ *)
  (* THE FRAME OPEN/CLOSE, PROVEN IN A CLEAN GOAL.                        *)
  (*                                                                     *)
  (* MEASURED: doing this INLINE inside the wrapper's proof -- [rewrite   *)
  (* s_rw_split s_ro_split_mix] and then the 25 [s_rs_*] lookups against  *)
  (* the wrapper's [envs_entails] -- is the file's whole cost (>600 s for *)
  (* ONE tactic, against 23 s for the other ~2000 steps).  The same       *)
  (* rewrites in a two-hypothesis goal are milliseconds, which is the     *)
  (* tree's standing rule about tower lookups under a big context.        *)
  (* ------------------------------------------------------------------ *)
  Lemma spt_frames_open
      (dq : dfrac) (pc npc ms : mword 64) (bmi : bool)
      (cy ti ip mst0 : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (mc : mword 32)
      (micfg misa0 mseccfg0 senv0 : mword 64) (pmar0 : list PMA_Region)
      (elp0 : type_of_register elp) (satp0 mie0 mdv0 menv0 : mword 64)
      (tlbv : type_of_register tlb) :
    hreg_frame (s_rs pc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
         senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv) s_Drw -∗
    hreg_frame_ro (s_Df_mix dq)
      (s_rs pc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
         senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv) s_Dro -∗
    ((R_bitvector_64 PC) ↦ᵣ pc ∗ (R_bitvector_64 nextPC) ↦ᵣ npc ∗
     (R_bitvector_64 minstret) ↦ᵣ ms ∗ (R_bool minstret_increment) ↦ᵣ bmi ∗
     (R_bitvector_64 mcycle) ↦ᵣ cy ∗ (R_bitvector_64 mtime) ↦ᵣ ti ∗
     (R_bitvector_64 mip) ↦ᵣ ip ∗ tlb ↦ᵣ tlbv ∗
     cur_privilege ↦ᵣ{ dq } Supervisor ∗ mstatus ↦ᵣ{ dq } mst0 ∗
     hart_state ↦ᵣ{ dq } HART_ACTIVE tt ∗
     pmpcfg_n ↦ᵣ pcfg ∗ pmpaddr_n ↦ᵣ paddr ∗
     reg_pointsto (R_bitvector_32 mcountinhibit) DfracDiscarded mc ∗
     reg_pointsto (R_bitvector_64 minstretcfg) DfracDiscarded micfg ∗
     reg_pointsto misa DfracDiscarded misa0 ∗
     reg_pointsto mseccfg DfracDiscarded mseccfg0 ∗
     reg_pointsto pma_regions DfracDiscarded pmar0 ∗
     reg_pointsto htif_tohost_base DfracDiscarded None ∗
     reg_pointsto elp DfracDiscarded elp0 ∗
     reg_pointsto senvcfg DfracDiscarded senv0 ∗
     satp ↦ᵣ satp0 ∗ mie ↦ᵣ{ dq } mie0 ∗ mideleg ↦ᵣ{ dq } mdv0 ∗
     menvcfg ↦ᵣ{ dq } menv0).
  Proof.
    iIntros "Hrw Hro".
    rewrite s_rw_split s_ro_split_mix.
    rewrite s_rs_PC s_rs_nPC s_rs_ms s_rs_mi s_rs_cy s_rs_ti s_rs_ip
      s_rs_tlb s_rs_priv s_rs_mst s_rs_hart s_rs_pcfg s_rs_paddr s_rs_mc
      s_rs_micfg s_rs_misa s_rs_sec s_rs_pma s_rs_htif s_rs_elp s_rs_senv
      s_rs_satp s_rs_mie s_rs_mdl s_rs_menv.
    iDestruct "Hrw" as "(HPC & HnPC & Hms & Hmi & Hcy & Hti & Hip & Htlbc)".
    iDestruct "Hro" as "(Hpriv & Hmst & Hhs & Hpcfg & Hpaddr & Hmc & Hmicfg &
                         Hmisa & Hsec & Hpma & Hhtif & Help & Hsenv &
                         Hsatp & Hmie & Hmdl & Hmenv)".
    iFrame.
  Qed.

  Lemma spt_frames_close
      (dq : dfrac) (pc npc ms : mword 64) (bmi : bool)
      (cy ti ip mst0 : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (mc : mword 32)
      (micfg misa0 mseccfg0 senv0 : mword 64) (pmar0 : list PMA_Region)
      (elp0 : type_of_register elp) (satp0 mie0 mdv0 menv0 : mword 64)
      (tlbv : type_of_register tlb) :
    ((R_bitvector_64 PC) ↦ᵣ pc ∗ (R_bitvector_64 nextPC) ↦ᵣ npc ∗
     (R_bitvector_64 minstret) ↦ᵣ ms ∗ (R_bool minstret_increment) ↦ᵣ bmi ∗
     (R_bitvector_64 mcycle) ↦ᵣ cy ∗ (R_bitvector_64 mtime) ↦ᵣ ti ∗
     (R_bitvector_64 mip) ↦ᵣ ip ∗ tlb ↦ᵣ tlbv ∗
     cur_privilege ↦ᵣ{ dq } Supervisor ∗ mstatus ↦ᵣ{ dq } mst0 ∗
     hart_state ↦ᵣ{ dq } HART_ACTIVE tt ∗
     pmpcfg_n ↦ᵣ pcfg ∗ pmpaddr_n ↦ᵣ paddr ∗
     reg_pointsto (R_bitvector_32 mcountinhibit) DfracDiscarded mc ∗
     reg_pointsto (R_bitvector_64 minstretcfg) DfracDiscarded micfg ∗
     reg_pointsto misa DfracDiscarded misa0 ∗
     reg_pointsto mseccfg DfracDiscarded mseccfg0 ∗
     reg_pointsto pma_regions DfracDiscarded pmar0 ∗
     reg_pointsto htif_tohost_base DfracDiscarded None ∗
     reg_pointsto elp DfracDiscarded elp0 ∗
     reg_pointsto senvcfg DfracDiscarded senv0 ∗
     satp ↦ᵣ satp0 ∗ mie ↦ᵣ{ dq } mie0 ∗ mideleg ↦ᵣ{ dq } mdv0 ∗
     menvcfg ↦ᵣ{ dq } menv0) -∗
    hreg_frame (s_rs pc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
         senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv) s_Drw ∗
    hreg_frame_ro (s_Df_mix dq)
      (s_rs pc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
         senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv) s_Dro.
  Proof.
    iIntros "(HPC & HnPC & Hms & Hmi & Hcy & Hti & Hip & Htlbc & Hpriv & Hmst
              & Hhs & Hpcfg & Hpaddr & Hmc & Hmicfg & Hmisa & Hsec & Hpma
              & Hhtif & Help & Hsenv & Hsatp & Hmie & Hmdl & Hmenv)".
    rewrite s_rw_split s_ro_split_mix.
    rewrite s_rs_PC s_rs_nPC s_rs_ms s_rs_mi s_rs_cy s_rs_ti s_rs_ip
      s_rs_tlb s_rs_priv s_rs_mst s_rs_hart s_rs_pcfg s_rs_paddr s_rs_mc
      s_rs_micfg s_rs_misa s_rs_sec s_rs_pma s_rs_htif s_rs_elp s_rs_senv
      s_rs_satp s_rs_mie s_rs_mdl s_rs_menv.
    iFrame.
  Qed.

  (* the tower transport the execute obligation needs: the fetch committed
     nextPC by a [register_set], and the cells are read off a tower.
     [HartMFrame.mm_npc_agree]'s S twin. *)
  Lemma s_npc_agree (pc npc npc' ms : mword 64) (bmi : bool)
      (cy ti ip mst0 : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (mc : mword 32)
      (micfg misa0 mseccfg0 senv0 : mword 64) (pmar0 : list PMA_Region)
      (elp0 : type_of_register elp) (satp0 mie0 mdv0 menv0 : mword 64)
      (tlbv : type_of_register tlb) :
    reg_agree_on (s_Drw ∪ s_Dro)
      (register_set (R_bitvector_64 nextPC) npc'
         (s_rs pc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
            mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv))
      (s_rs pc npc' ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
         mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv).
  Proof.
    (* no generic [rewrite]: [s_rs]'s body IS a [register_set] tower, so an
       ssreflect rewrite with [register_lookup_set]'s pattern searches inside
       it and detonates the record-update conversion bomb ([mm_npc_agree]'s
       note).  Goal 2 is the nextPC cell; every other goal is apply-directed. *)
    apply s_rs_agree.
    2:{ apply register_lookup_set. }
    all: (etransitivity;
          [ apply irrelevant_register_set; vm_compute; reflexivity | ]).
    all: by rewrite ?s_rs_PC ?s_rs_ms ?s_rs_mi ?s_rs_cy ?s_rs_ti ?s_rs_ip
              ?s_rs_tlb ?s_rs_priv ?s_rs_mst ?s_rs_hart ?s_rs_pcfg
              ?s_rs_paddr ?s_rs_mc ?s_rs_micfg ?s_rs_misa ?s_rs_sec
              ?s_rs_pma ?s_rs_htif ?s_rs_elp ?s_rs_senv ?s_rs_satp
              ?s_rs_mie ?s_rs_mdl ?s_rs_menv.
  Qed.

  (* ...and back: the frames at a tower ARE the cells the caller handed in. *)
  Lemma spt_frames_elim (dq : dfrac) (npc ms : mword 64) (bmi : bool)
      (cy ti ip : mword 64) (mc : mword 32)
      (micfg misa0 mseccfg0 senv0 : mword 64) (pmar0 : list PMA_Region)
      (elp0 : type_of_register elp)
      (mstatus1 satp1 mie1 mdv1 menvcfg1 : mword 64)
      (pcfg1 : type_of_register pmpcfg_n)
      (paddr1 : type_of_register pmpaddr_n) (tv : type_of_register tlb) :
    resv_any cpu_id -∗
    hreg_frame (s_rs npc npc ms bmi cy ti ip mstatus1 pcfg1 paddr1 mc micfg
                  misa0 mseccfg0 senv0 pmar0 elp0 satp1 mie1 mdv1 menvcfg1 tv)
      s_Drw -∗
    hreg_frame_ro (s_Df_mix dq)
      (s_rs npc npc ms bmi cy ti ip mstatus1 pcfg1 paddr1 mc micfg misa0
         mseccfg0 senv0 pmar0 elp0 satp1 mie1 mdv1 menvcfg1 tv) s_Dro -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt ∗ cur_privilege ↦ᵣ{ dq } Supervisor ∗
    mstatus ↦ᵣ{ dq } mstatus1 ∗ mie ↦ᵣ{ dq } mie1 ∗
    mideleg ↦ᵣ{ dq } mdv1 ∗ menvcfg ↦ᵣ{ dq } menvcfg1 ∗
    satp ↦ᵣ satp1 ∗ pmpcfg_n ↦ᵣ pcfg1 ∗ pmpaddr_n ↦ᵣ paddr1 ∗
    tlb ↦ᵣ tv ∗ pc_is npc.
  Proof.
    iIntros "Hresv Hrw Hro".
    rewrite s_rw_split s_ro_split_mix.
    rewrite s_rs_PC s_rs_nPC s_rs_ms s_rs_mi s_rs_cy s_rs_ti s_rs_ip
      s_rs_tlb.
    rewrite s_rs_priv s_rs_mst s_rs_hart s_rs_pcfg s_rs_paddr s_rs_mc
      s_rs_micfg s_rs_misa s_rs_sec s_rs_pma s_rs_htif s_rs_elp s_rs_senv
      s_rs_satp s_rs_mie s_rs_mdl s_rs_menv.
    iDestruct "Hrw" as "(HPC & HnPC & Hms & Hmi & Hcy & Hti & Hip & Htlbc)".
    iDestruct "Hro" as "(Hpriv & Hmst & Hhs & Hpcfg & Hpaddr & #Hmc & #Hmicfg &
                         #Hmisa & #Hsec & #Hpma & #Hhtif & #Help & #Hsenv &
                         Hsatp & Hmie & Hmdl & Hmenv)".
    iFrame "Hhs Hpriv Hmst Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc".
    rewrite /pc_is /minstret_res /clock_res.
    iFrame "HPC HnPC Hresv".
    iSplitL "Hms Hmi".
    - iExists ms, bmi, mc, micfg. by iFrame "Hms Hmi Hmc Hmicfg".
    - iExists cy, ti, ip. by iFrame.
  Qed.


  (* the regime's fetch translation as the wrapper must ask for it: the
     tower components the wrapper cannot name ([pc_is]'s and [hw_config]'s
     existentials) are ∀-BOUND, which costs a caller nothing --
     [SRegime.sr_swp_translate] is itself ∀-over-files. *)
  Definition spt_fetch_tr (Df : register -> dfrac)
      (Res : type_of_register tlb -> iProp Σ) (pc : mword 64)
      (mst0 satp0 mie0 mdv0 menv0 : mword 64)
      (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) : iProp Σ :=
    (∀ (ms : mword 64) (bmi : bool) (cy ti ip : mword 64) (mc : mword 32)
       (micfg misa0 mseccfg0 senv0 : mword 64) (pmar0 : list PMA_Region)
       (elp0 : type_of_register elp),
       spt_tr_obl Df pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
         mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 Res)%I.

  (* ==================================================================== *)
  (* THE FETCH-TRANSLATION PRODUCER.                                       *)
  (*                                                                      *)
  (* [spt_tr_obl] is [SRegime.sr_swp_translate] at [InstructionFetch tt],  *)
  (* instantiated at THIS wrapper's tower and re-shaped: the walk's        *)
  (* landing file comes back as [rsf = rs \/ exists tv, rsf = register_set *)
  (* tlb tv rs] and the obligation wants it AS A TOWER, at the tlb value   *)
  (* the walk chose.  Three things make the instantiation go through:      *)
  (*                                                                      *)
  (*   - THE REFERENCE STATE IS THIS HART'S OWN FILE                       *)
  (*     ([MState (srs tv) empty dev0_state]), so every agreement premise  *)
  (*     of [sr_swp_translate] -- the [Db] one, the [D_leafchk] one and    *)
  (*     the mstatus one -- is [eq_refl].  This is [spt_dispatch_none]'s   *)
  (*     trick, and it is why the producer needs no agreement hypothesis   *)
  (*     at all;                                                           *)
  (*   - THE RESIDUE CONVERTS BY [sr_swp_res_agree], twice: once at        *)
  (*     [rs := srs tv] on the way in, once at the landing file on the way *)
  (*     out.  Both are two tower lookups ([s_rs_satp], [s_rs_tlb]) --     *)
  (*     satp is unchanged because the walk's ONLY write is the TLB fill;  *)
  (*   - THE LANDING FILE MOVES ONTO THE TOWER by [s_rs_agree] +           *)
  (*     [s_rw_ext] / [s_ro_ext_gen].  [register_set tlb tv' (srs tv)] is  *)
  (*     not syntactically [srs tv'], but it agrees with it on all 25      *)
  (*     footprint cells, which is all a frame can tell.                   *)
  (*                                                                      *)
  (* NOTHING REGIME-SPECIFIC IS LEFT TO THE CALLER.  The side condition    *)
  (* [sr_swp_side] and the admissibility [sr_adm] are the two things only  *)
  (* the regime knows, and the record answers both itself                  *)
  (* ([sr_swp_side_ok] / [sr_adm_of_pin]), so every premise below is a     *)
  (* PURE CONFIG FACT a leaf already holds.                                *)
  (* ==================================================================== *)

  (* one tower lookup through the walk's TLB write-back *)
  Local Ltac tlbpeel := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  Lemma spt_tr_obl_of_regime
      (R : s_regime)
      (Df : register -> dfrac) (Db : register -> bool)
      (pc ms : mword 64) (bmi : bool) (cy ti ip mst0 : mword 64)
      (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
      (satp0 mie0 mdv0 menv0 : mword 64) :
    misa0 = MISA_C ->
    menv0 = MENVCFG_S ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    (forall r : register, Db r = true -> r ∈ s_Drw ∪ s_Dro) ->
    (forall r : register, D_leafchk r = true -> r ∈ s_Drw ∪ s_Dro) ->
    Db mstatus = true -> Db satp = true ->
    sr_swp_satp_ok R satp0 ->
    pmp_ent0_ok pcfg paddr ->
    pma_allows_ram pmar0 ->
    gen_cert -∗
    spt_tr_obl Df pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
      senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 (sr_swp_res_at R satp0).
  Proof.
    intros Hmisa Hmenv HSXL HMPRV HDb HDlc HDm HDs Hsok Hpmp Hpma.
    iIntros "#Hcert". rewrite /spt_tr_obl. iModIntro.
    iIntros (va ppn tv rr) "%Hlt %Hpin #Hat Hfrag HRes Hrw Hro".
    (* the reference state's three pure pins, read off the tower *)
    assert (Lmisa : register_lookup misa
              (MState (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg
                 misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)
                 ∅ dev0_state).(sregs) = MISA_C).
    { cbn [sregs]. rewrite s_rs_misa. exact Hmisa. }
    assert (Lmenv : register_lookup menvcfg
              (MState (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg
                 misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)
                 ∅ dev0_state).(sregs) = MENVCFG_S).
    { cbn [sregs]. rewrite s_rs_menv. exact Hmenv. }
    assert (LSXL : _get_Mstatus_SXL (register_lookup mstatus
              (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv))
              = 'b"10").
    { rewrite s_rs_mst. exact HSXL. }
    (* the residue at the PRE-file *)
    iAssert (sr_swp_res R
               (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                  mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv))
      with "[HRes]" as "HRes'".
    { rewrite -(sr_swp_res_agree R
                  (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                     mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)).
      rewrite s_rs_satp s_rs_tlb. iExact "HRes". }
    (* the regime's own side condition, out of the pure config facts *)
    assert (Hside : sr_swp_side R (InstructionFetch tt) va ppn KP_rx Db
                      s_Drw s_Dro
                      (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg
                 misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)
                      (MState (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg
                 misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)
                         ∅ dev0_state)).
    { apply (sr_swp_side_ok R (InstructionFetch tt) va ppn KP_rx Db
               s_Drw s_Dro).
      - left. reflexivity.
      - rewrite s_rs_satp. exact Hsok.
      - rewrite s_rs_pcfg s_rs_paddr. exact Hpmp.
      - rewrite s_rs_pma. exact Hpma.
      - rewrite s_rs_mst. exact HMPRV.
      - exact HDm.
      - exact HDs.
      - cbn [sregs]. rewrite s_rs_mst. exact HSXL.
      - reflexivity.
      (* the walking regimes' TLB requirement, now on the introduction rather
         than on [sr_swp_translate] -- and the leaf's own frame has it *)
      - rewrite /s_Drw. set_solver. }
    iApply (swp_mono with "[] [-]").
    2:{ iApply (sr_swp_translate R (InstructionFetch tt) s_Drw s_Dro Df
                  (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                     mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)
                  (MState (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg
                     misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)
                     ∅ dev0_state)
                  Db va (pa_of ppn va) ppn KP_rx rr
                  s_disj (or_introl eq_refl) eq_refl
                  s_in_mst s_in_priv s_in_satp s_in_pma s_in_pcfg
                  s_in_paddr s_in_htif
                  HDb (fun r _ => eq_refl) HDlc (fun r _ => eq_refl)
                  ltac:(by apply s_rs_priv) ltac:(by apply s_rs_htif) eq_refl
                  Lmisa Lmenv LSXL
                  (exec_effectivePrivilege_fetch _ Supervisor _)
                  (goodb_effectivePrivilege_fetch Db _ Supervisor _)
                  (exec_is_shadow_stack_fetch _)
                  (goodb_is_shadow_stack_fetch Db _)
                  (lo_canonical va Hlt) eq_refl
                  (sr_adm_of_pin R va ppn Hpin) Hside
                  with "Hat Hcert Hfrag HRes' Hrw Hro"). }
    iIntros (r) "(-> & %rsf & %Hshape & Hrw & Hro & HRes & Hany)".
    iSplitR; [done |].
    destruct Hshape as [-> | (tvx & ->)].
    - (* the TLB hit: the file did not move *)
      iExists tv. iFrame "Hany Hrw Hro".
      iEval (rewrite -(sr_swp_res_agree R
                (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                   mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv))
             s_rs_satp s_rs_tlb) in "HRes".
      iExact "HRes".
    - (* the walk FILLED the tlb: move the landing file onto the tower *)
      assert (Lsatp : register_lookup satp
                (register_set tlb tvx
                   (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                      mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv))
                = satp0).
      { tlbpeel; apply s_rs_satp. }
      assert (Ltlbv : register_lookup tlb
                (register_set tlb tvx
                   (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                      mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv))
                = tvx)
        by apply register_lookup_set.
      assert (Hag : reg_agree_on (s_Drw ∪ s_Dro)
                (register_set tlb tvx
                   (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                      mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv))
                (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                   mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tvx)).
      { apply (s_rs_agree pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tvx);
          [ tlbpeel; apply s_rs_PC
          | tlbpeel; apply s_rs_nPC
          | tlbpeel; apply s_rs_ms
          | tlbpeel; apply s_rs_mi
          | tlbpeel; apply s_rs_cy
          | tlbpeel; apply s_rs_ti
          | tlbpeel; apply s_rs_ip
          | exact Ltlbv
          | tlbpeel; apply s_rs_priv
          | tlbpeel; apply s_rs_mst
          | tlbpeel; apply s_rs_hart
          | tlbpeel; apply s_rs_pcfg
          | tlbpeel; apply s_rs_paddr
          | tlbpeel; apply s_rs_mc
          | tlbpeel; apply s_rs_micfg
          | tlbpeel; apply s_rs_misa
          | tlbpeel; apply s_rs_sec
          | tlbpeel; apply s_rs_pma
          | tlbpeel; apply s_rs_htif
          | tlbpeel; apply s_rs_elp
          | tlbpeel; apply s_rs_senv
          | exact Lsatp
          | tlbpeel; apply s_rs_mie
          | tlbpeel; apply s_rs_mdl
          | tlbpeel; apply s_rs_menv ]. }
      iDestruct (s_rw_ext _ _ Hag with "Hrw") as "Hrw".
      iDestruct (s_ro_ext_gen Df _ _ Hag with "Hro") as "Hro".
      iExists tvx. iFrame "Hany Hrw Hro".
      iEval (rewrite -(sr_swp_res_agree R
                (register_set tlb tvx
                   (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                      mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)))
             Lsatp Ltlbv) in "HRes".
      iExact "HRes".
  Qed.

  (* ==================================================================== *)
  (* wp_instr_s_config_regime -- THE RAW-CELL S-MODE WRAPPER.              *)
  (*                                                                      *)
  (* [WpInstrConfig.wp_instr_config]'s S twin.  Same surface as the        *)
  (* exec-based rule it replaces on the CONFIG side (the five cells at a   *)
  (* caller-chosen fraction, only the SIE fact required -- it is what      *)
  (* pins the dispatch to [None]), and the four cells the regime used to   *)
  (* hide inside [sr_inv R] now handed over raw, beside the regime's       *)
  (* non-cell RESIDUE [Res] at the tlb value the cell carries.             *)
  (*                                                                      *)
  (* The obligation is a [swp] over [execute i] instead of a fupd handing  *)
  (* back a whole successor sigma -- the one difference per-node stepping  *)
  (* forces, exactly as in [wp_instr_config] -- and it is quantified over  *)
  (* the tlb value the FETCH landed on, because the fetch walks.           *)
  (* ==================================================================== *)
  (* NOT PROVED.  What is left is assembly, and it is listed here so the
     next agent does not have to re-derive it:
       1. [spt_frames_intro], then [spt_cycle] at
          [Q rs2 := ∃ npc tv', rs2 = <the post tower>] and
          [Psi rs2 := Res (register_lookup tlb rs2) ∗ Rl];
       2. the body: [spt_run_hart_active_instr_S] (PROVED above), with
          - the DISPATCH pinned to [None] by
            [WpIntrCore.swp_dispatchInterrupt_S] at [dst := MState (srs tv)
            ∅ dev0_state] (so its agreement premise is [reflexivity]) and
            [Db := misa ∪ mstatus]; [s_dispatch]'s guard is
            [eq_vec (_get_Mstatus_SIE mst0) ('b"1")], which the first
            premise makes [false];
          - the EXECUTE obligation: [s_npc_agree] + [s_rw_ext]/[s_ro_ext]
            to move the frames off the [register_set nextPC] onto the
            tower, then [s_rw_split]/[s_ro_split_mix] to hand the leaf its
            cells and take them back;
       3. the continuation: [WpSFrames.s_tick_agree] + the two frame
          extensions + [spt_frames_elim].
     Step 1 is what [spt_cycle] is admitted for; steps 2 and 3 are
     mechanical over lemmas that are proved above. *)
  Lemma wp_instr_s_config_regime
      (Res : type_of_register tlb -> iProp Σ)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 satp0 : mword 64)
      (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (tlbv : type_of_register tlb)
      (mie1 menvcfg1 satp1 : mword 64)
      (pcfg1 : type_of_register pmpcfg_n)
      (paddr1 : type_of_register pmpaddr_n)
      (Rl : mword 64 -> mword 64 -> mword 64 -> iProp Σ) {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* the PMP grant, off the cells the wrapper now takes raw -- it used to
       ride inside [SmodePte.pmp_config] within [sr_inv R].  Taken WHOLE
       ([pmp_ent0_ok], all six conjuncts) rather than as the four the FETCH
       needs, because the leaf's obligation is handed it as well: a data
       access checks W/R too, and it cannot recover them from the residue
       (Bare's is [True]). *)
    pmp_ent0_ok pcfg paddr ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    satp ↦ᵣ satp0 -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
    tlb ↦ᵣ tlbv -∗ Res tlbv -∗
    pc_is pc -∗
    instr pc is_rvc i -∗
    spt_fetch_tr (s_Df_mix dq) Res pc mstatus0 satp0 mie_v mdv0 menvcfg0
      pcfg paddr -∗
    (* THE LEAF'S OBLIGATION.  Three things travel into it that a
       register-only leaf does not need and no MEMORY leaf can do without:

         - the PMP grant, because [HartSMem]'s checks and
           [SRegime.sr_swp_side_ok] both take it and neither is
           recoverable inside the obligation (the residue is the regime's,
           and Bare's is [True]);
         - the three CLOCK cells ([MinstretInv.clock_res], mcycle / mtime
           / mip -- already in [s_Drw]), without which [csrr time],
           [csrr sip] and [csrw stimecmp] cannot be written at all.  They
           are handed over at EXISTENTIAL values, because the wrapper's own
           come out of [spt_frames_intro]'s existentials, and they come
           back the same way -- the tick runs at the cycle BOUNDARY, so
           nothing inside the instruction has to name them;
         - and the leaf CHOOSES the post mstatus and mideleg.  That is
           forced: [csrsi]/[csrci sstatus] and [sret] MOVE SIE, so a caller
           on the SIE = 0 arm cannot name the mstatus the instruction
           leaves behind.  They ride in ONE existential with the landing
           pc, because the rider is keyed on all three. *)
    (∀ tv' : type_of_register tlb,
       ⌜ pmp_ent0_ok pcfg paddr ⌝ -∗
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       satp ↦ᵣ satp0 -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
       tlb ↦ᵣ tv' -∗ Res tv' -∗
       clock_res -∗
       (R_bitvector_64 PC) ↦ᵣ pc -∗
       (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       resv_any cpu_id -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   cur_privilege ↦ᵣ{ dq } Supervisor ∗
                   mie ↦ᵣ{ dq } mie1 ∗
                   menvcfg ↦ᵣ{ dq } menvcfg1 ∗
                   satp ↦ᵣ satp1 ∗ pmpcfg_n ↦ᵣ pcfg1 ∗
                   pmpaddr_n ↦ᵣ paddr1 ∗
                   (∃ tv2 : type_of_register tlb, tlb ↦ᵣ tv2 ∗ Res tv2) ∗
                   clock_res ∗
                   (∃ ms1 mdv1 npc : mword 64,
                      mstatus ↦ᵣ{ dq } ms1 ∗ mideleg ↦ᵣ{ dq } mdv1 ∗
                      (R_bitvector_64 PC) ↦ᵣ pc ∗
                      (R_bitvector_64 nextPC) ↦ᵣ npc ∗ Rl npc ms1 mdv1) ∗
                   resv_any cpu_id)) -∗
    ▷ (∀ (npc ms1 mdv1 : mword 64) (tv1 : type_of_register tlb),
         hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
         cur_privilege ↦ᵣ{ dq } Supervisor -∗
         mstatus ↦ᵣ{ dq } ms1 -∗
         mie ↦ᵣ{ dq } mie1 -∗
         mideleg ↦ᵣ{ dq } mdv1 -∗
         menvcfg ↦ᵣ{ dq } menvcfg1 -∗
         satp ↦ᵣ satp1 -∗ pmpcfg_n ↦ᵣ pcfg1 -∗ pmpaddr_n ↦ᵣ paddr1 -∗
         tlb ↦ᵣ tv1 -∗ Res tv1 -∗
         pc_is npc -∗ Rl npc ms1 mdv1 -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL Hmm HPBMTE Hmenvval Hpmp.
    pose proof Hpmp as (HA & Hord & HX & HW & HR & Hcov).
    iIntros "#Hhw #Hminv Hhs Hpriv Hmst Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr
             Htlbc HRes Hpc Hinstr Htr Hex Hcont".
    iDestruct (spt_frames_intro dq pc mstatus0 mie_v mdv0 menvcfg0 satp0 pcfg
                 paddr tlbv
                 with "Hhw Hhs Hpriv Hmst Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr
                       Htlbc Hpc") as "[Hfrag Hfr]".
    iDestruct "Hfr" as (ms bmi cy ti ip mc micfg misa0 mseccfg0 senv0 pmar0 elp0)
      "(%Hmisaval & %Hpmaall & %Helpnp & Hrw & Hro)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof ("Htr" $! ms (minstret_inc_flag mc micfg Supervisor) cy ti ip mc
                  micfg misa0 mseccfg0 senv0 pmar0 elp0) as "#Htr0".
    iApply (spt_cycle (s_Df_mix dq) pc
              (fun rs2 => (Res (register_lookup tlb rs2) ∗ resv_any cpu_id
                           ∗ Rl (register_lookup (R_bitvector_64 nextPC) rs2)
                                (register_lookup mstatus rs2)
                                (register_lookup mideleg rs2))%I)
              (fun rs2 => exists (npc ms1 mdv1 cy1 ti1 ip1 : mword 64)
                            (tv : type_of_register tlb),
                 rs2 = s_rs pc npc ms (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1 pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp1 mie1 mdv1 menvcfg1 tv)
              ms bmi cy ti ip mstatus0 mc micfg misa0 mseccfg0 senv0 pmar0 elp0
              satp0 mie_v mdv0 menvcfg0 pcfg paddr tlbv
              ltac:(intros rs2 (npc & ms1 & mdv1 & cy1 & ti1 & ip1 & tv & ->);
                    apply s_rs_hart)
              ltac:(intros rs2 (npc & ms1 & mdv1 & cy1 & ti1 & ip1 & tv & ->);
                    apply s_rs_mi)
              with "Hcert Hfrag Hrw Hro [Hex HRes Hinstr] [Hcont]").
    2:{ (* ---- the continuation ---- *)
        iNext. iIntros (rs3 rs2 mi) "[%HQ %Hag] Hrw Hro (HRes & Hfrag & HRl)".
        destruct HQ as (npc & ms1 & mdv1 & cy1 & ti1 & ip1 & tv & ->).
        iEval (rewrite s_rs_tlb) in "HRes".
        iEval (rewrite s_rs_nPC s_rs_mst s_rs_mdl) in "HRl".
        pose proof (s_tick_agree pc npc ms
                      (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1
                      pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0
                      satp1 mie1 mdv1 menvcfg1 tv mi rs3 Hag) as Hag'.
        iDestruct (s_rw_ext _ _ Hag' with "Hrw") as "Hrw".
        iDestruct (s_ro_ext_gen (s_Df_mix dq) _ _ Hag' with "Hro") as "Hro".
        iDestruct (spt_frames_elim dq npc mi
                     (minstret_inc_flag mc micfg Supervisor) _ _ _ mc micfg
                     misa0 mseccfg0 senv0 pmar0 elp0 ms1 satp1 mie1 mdv1
                     menvcfg1 pcfg1 paddr1 tv with "Hfrag Hrw Hro")
          as "(Hhs & Hpriv & Hmst & Hmie & Hmdl & Hmenv & Hsatp & Hpcfg &
               Hpaddr & Htlbc & Hpc)".
        iApply ("Hcont" $! npc ms1 mdv1 tv with "Hhs Hpriv Hmst Hmie Hmdl Hmenv
                  Hsatp Hpcfg Hpaddr Htlbc HRes Hpc HRl"). }
    (* ---- the body ---- *)
    iIntros "Hfrag Hrw Hro".
    iApply (swp_mono with "[] [-]");
      [| iApply (spt_run_hart_active_instr_S (s_Df_mix dq) pc ms
                   (minstret_inc_flag mc micfg Supervisor) cy ti ip mstatus0
                   pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0
                   mie_v mdv0 menvcfg0 Res tlbv is_rvc i
                   (fun rs2 => exists (npc ms1 mdv1 cy1 ti1 ip1 : mword 64)
                                 (tv : type_of_register tlb),
                      rs2 = s_rs pc npc ms (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1 pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp1 mie1 mdv1 menvcfg1 tv)
                   (fun rs2 => (Res (register_lookup tlb rs2)
                                ∗ resv_any cpu_id
                                ∗ Rl (register_lookup (R_bitvector_64 nextPC) rs2)
                                     (register_lookup mstatus rs2)
                                     (register_lookup mideleg rs2))%I)
                   emp%I (fun _ _ => False%I)
                   Hmisaval Hmenvval Helpnp (pma_all_ram Hpmaall)
                   HA Hord HX Hcov
                   with "Hcert Hinstr [] Hfrag HRes Hrw Hro [] Htr0
                         [Hex]") ].
    - iIntros (st) "[Hi | Hr]".
      + iDestruct "Hi" as (ii pr) "(_ & Hf)". iDestruct "Hf" as %[].
      + iDestruct "Hr" as (w) "(-> & Hr)".
        iDestruct "Hr" as (rs2) "(%HQ & Hrw & Hro & HPsi)".
        iExists rs2. iSplitR; [done|]. iFrame.
    - done.
    - iApply (spt_dispatch_none (s_Df_mix dq) pc ms
                (minstret_inc_flag mc micfg Supervisor) cy ti ip mstatus0 pcfg
                paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie_v mdv0
                menvcfg0 Res tlbv emp%I (fun _ _ => False%I) Hmisaval HSIE Hmm
                with "Hcert").
    - (* THE LEAF, at the file the fetch landed on *)
      iIntros (tv') "_ HRes' Hany Hrw Hro".
      pose proof (s_npc_agree pc pc
                    (add_vec_int pc (if is_rvc then 2 else 4)) ms
                    (minstret_inc_flag mc micfg Supervisor) cy ti ip mstatus0
                    pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0
                    mie_v mdv0 menvcfg0 tv') as Hnp.
      iDestruct (s_rw_ext _ _ Hnp with "Hrw") as "Hrw".
      iDestruct (s_ro_ext_gen (s_Df_mix dq) _ _ Hnp with "Hro") as "Hro".
      iDestruct (spt_frames_open dq pc
                   (add_vec_int pc (if is_rvc then 2 else 4)) ms
                   (minstret_inc_flag mc micfg Supervisor) cy ti ip mstatus0
                   pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0
                   mie_v mdv0 menvcfg0 tv' with "Hrw Hro")
        as "(HPC & HnPC & Hms & Hmi & Hcy & Hti & Hip & Htlbc & Hpriv & Hmst
             & Hhs & Hpcfg & Hpaddr & #Hmc & #Hmicfg & #Hmisa & #Hsec & #Hpma
             & #Hhtif & #Help & #Hsenv & Hsatp & Hmie & Hmdl & Hmenv)".
      iSpecialize ("Hex" $! tv' with "[%]"); [ exact Hpmp | ].
      iAssert clock_res with "[Hcy Hti Hip]" as "Hclk".
      { iExists cy, ti, ip. iFrame "Hcy Hti Hip". }
      iApply (swp_mono with "[Hms Hmi Hhs] [-]");
        [| iApply ("Hex" with "Hpriv Hmst Hmie Hmdl Hmenv Hsatp Hpcfg
                     Hpaddr Htlbc HRes' Hclk HPC HnPC Hany") ].
      iIntros (e) "(-> & Hpriv & Hmie & Hmenv & Hsatp & Hpcfg &
                    Hpaddr & Htlbr & Hclk & Hcfg & Hany)".
      (* the leaf may have FILLED THE TLB (a data access walks too), so the
         cell and the regime residue come back at the leaf's own landing
         value, not at the one the fetch handed it; the clock cells and the
         post mstatus / mideleg come back the same way *)
      iDestruct "Htlbr" as (tv2) "(Htlbc & HRes')".
      iDestruct "Hclk" as (cy1 ti1 ip1) "(Hcy & Hti & Hip)".
      iDestruct "Hcfg" as (ms1 mdv1 npc) "(Hmst & Hmdl & HPC & HnPC & HRl)".
      iSplitR; [done|].
      iExists (s_rs pc npc ms (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1 pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp1 mie1 mdv1 menvcfg1 tv2).
      iSplitR;
        [ iPureIntro; by exists npc, ms1, mdv1, cy1, ti1, ip1, tv2 |].
      iDestruct (spt_frames_close dq pc npc ms
                   (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1
                   pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp1
                   mie1 mdv1 menvcfg1 tv2
                   with "[HPC HnPC Hms Hmi Hcy Hti Hip Htlbc Hpriv Hmst Hhs
                          Hpcfg Hpaddr Hsatp Hmie Hmdl Hmenv]")
        as "[Hrw Hro]".
      { iFrame "HPC HnPC Hms Hmi Hcy Hti Hip Htlbc Hpriv Hmst Hhs Hpcfg
                Hpaddr Hsatp Hmie Hmdl Hmenv".
        by iFrame "Hmc Hmicfg Hmisa Hsec Hpma Hhtif Help Hsenv". }
      rewrite s_rs_tlb s_rs_nPC s_rs_mst s_rs_mdl.
      iFrame "Hrw Hro HRes' Hany HRl".
  Qed.

  (* ==================================================================== *)
  (* wp_instr_s_regime -- the same engine on the BUNDLE.                   *)
  (*                                                                      *)
  (* [WpInstr.wp_instr]'s S twin: [SmodeCore.smode_config] in and the same *)
  (* bundle back, so the leaf never sees the cells' values (the bundle     *)
  (* quantifies them) -- which is why its obligation is ∀ over them and    *)
  (* returns them UNCHANGED.  A leaf that WRITES a config cell takes       *)
  (* [wp_instr_s_config_regime] instead, exactly as M-mode splits          *)
  (* [wp_instr] from [wp_instr_config].                                    *)
  (* ==================================================================== *)
  (* NOT PROVED: [wp_instr_s_config_regime] plus
     [SmodeCore.smode_config_unbundle] / [_rebuild] on both sides. *)
  Lemma wp_instr_s_regime
      (Res : type_of_register tlb -> iProp Σ) (γ : gname)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (satp0 : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (tlbv : type_of_register tlb)
      (Rl : mword 64 -> iProp Σ) {dq : dfrac} :
    pmp_ent0_ok pcfg paddr ->
    smode_config γ dq -∗
    satp ↦ᵣ satp0 -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
    tlb ↦ᵣ tlbv -∗ Res tlbv -∗
    pc_is pc -∗
    instr pc is_rvc i -∗
    (∀ (mstatus0 mie_v mdv0 menvcfg0 : mword 64),
       ⌜ eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ⌝ -∗
       ⌜ _get_Mstatus_SXL mstatus0 = 'b"10" ⌝ -∗
       ⌜ and_vec mie_v (not_vec mdv0) = zeros' 64 ⌝ -∗
       ⌜ menvcfg0 = MENVCFG_S ⌝ -∗
       spt_fetch_tr (s_Df_mix dq) Res pc mstatus0 satp0 mie_v mdv0 menvcfg0
         pcfg paddr) -∗
    (∀ (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
       (tv' : type_of_register tlb),
       ⌜ pmp_ent0_ok pcfg paddr ⌝ -∗
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       satp ↦ᵣ satp0 -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
       tlb ↦ᵣ tv' -∗ Res tv' -∗
       clock_res -∗
       (R_bitvector_64 PC) ↦ᵣ pc -∗
       (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       resv_any cpu_id -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   cur_privilege ↦ᵣ{ dq } Supervisor ∗
                   mstatus ↦ᵣ{ dq } mstatus0 ∗
                   mie ↦ᵣ{ dq } mie_v ∗
                   mideleg ↦ᵣ{ dq } mdv0 ∗
                   menvcfg ↦ᵣ{ dq } menvcfg0 ∗
                   satp ↦ᵣ satp0 ∗ pmpcfg_n ↦ᵣ pcfg ∗
                   pmpaddr_n ↦ᵣ paddr ∗
                   (∃ tv2 : type_of_register tlb, tlb ↦ᵣ tv2 ∗ Res tv2) ∗
                   clock_res ∗
                   (∃ npc : mword 64,
                      (R_bitvector_64 PC) ↦ᵣ pc ∗
                      (R_bitvector_64 nextPC) ↦ᵣ npc ∗ Rl npc) ∗
                   resv_any cpu_id)) -∗
    ▷ (∀ (npc : mword 64) (tv1 : type_of_register tlb),
         smode_config γ dq -∗
         satp ↦ᵣ satp0 -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
         tlb ↦ᵣ tv1 -∗ Res tv1 -∗
         pc_is npc -∗ Rl npc -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hpmp.
    iIntros "Hsm Hsatp Hpcfg Hpaddr Htlbc HRes Hpc Hinstr Htr Hex Hcont".
    iDestruct (smode_config_unbundle with "Hsm")
      as "(#Hhw & #Hminv & Hhs & Hpriv & Hmst & Hmiebundle & Hmenvbundle)".
    iDestruct "Hmst" as (mstatus0)
      "(Hmstatus & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmiebundle" as (mie_v mdv0) "(Hmiec & Hmdlc & %Hmm)".
    iDestruct "Hmenvbundle" as (menvcfg0)
      "(Hmenvc & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval)".
    (* the BUNDLE cannot take the config-existential post: [smode_config]
       requires SIE = 0 of the mstatus it re-bundles, and a leaf that MOVED
       SIE is exactly what the existential is for.  So this wrapper keeps a
       FIXED post config and carries the two equations through the rider,
       which is what lets the raw-cell wrapper stay existential underneath. *)
    iApply (wp_instr_s_config_regime Res pc is_rvc i mstatus0 mie_v mdv0
              menvcfg0 satp0 pcfg paddr tlbv mie_v menvcfg0
              satp0 pcfg paddr
              (fun npc ms1 mdv1 =>
                 (⌜ ms1 = mstatus0 ⌝ ∗ ⌜ mdv1 = mdv0 ⌝ ∗ Rl npc)%I) (dq := dq)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval Hpmp
              with "Hhw Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp
                    Hpcfg Hpaddr Htlbc HRes Hpc Hinstr [Htr] [Hex]
                    [Hcont Hsie]").
    - iApply ("Htr" $! mstatus0 mie_v mdv0 menvcfg0 with "[%] [%] [%] [%]");
        [ exact HSIE | exact HSXL | exact Hmm | exact Hmenvval ].
    - iIntros (tv') "_ Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp Hpcfg Hpaddr
                     Htlbc HRes Hclk HPC HnPC Hany".
      iApply (swp_mono with "[] [-]");
        [| iApply ("Hex" $! mstatus0 mie_v mdv0 menvcfg0 tv' with "[%] Hpriv
             Hmstatus Hmiec Hmdlc Hmenvc Hsatp Hpcfg Hpaddr Htlbc HRes Hclk
             HPC HnPC Hany") ].
      2:{ exact Hpmp. }
      iIntros (e) "(-> & Hpriv & Hmstatus & Hmiec & Hmdlc & Hmenvc & Hsatp &
                    Hpcfg & Hpaddr & Htlbr & Hclk & Hpcs & Hany)".
      iDestruct "Hpcs" as (npc) "(HPC & HnPC & HRl)".
      iFrame "Hpriv Hmiec Hmenvc Hsatp Hpcfg Hpaddr Htlbr Hclk Hany".
      iSplitR; [done|].
      iExists mstatus0, mdv0, npc. iFrame "Hmstatus Hmdlc HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iExact "HRl".
    - iNext. iIntros (npc ms1 mdv1 tv1)
        "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp Hpcfg Hpaddr Htlbc
         HRes Hpc (-> & -> & HRl)".
      iApply ("Hcont" $! npc tv1 with
                "[Hhs Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc] Hsatp Hpcfg
                 Hpaddr Htlbc HRes Hpc HRl").
      iApply (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval
                with "Hhw Hminv Hhs Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc").
  Qed.

  (* =================================================================== *)
  (* Sv39-kernel instances under the ORIGINAL names/signatures: nothing   *)
  (* downstream moves.  [sr_inv (kpt_share_regime root_ppn)] IS            *)
  (* [tlb_res_pt root_ppn] definitionally, so [exact] closes each          *)
  (* restatement.                                                         *)
  (* =================================================================== *)
  Lemma tlb_inv_pt_fetch `{KTR : !CurKtier} (root_ppn : mword 44) (σ : mstate)
      (pc : mword 64) (r : FetchResult) (E : coPset) :
    ↑kptN ⊆ E ->
    register_lookup PC σ.(sregs) = pc ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    mstate_interp σ -∗
    tlb_res_pt root_ppn -∗
    instr_bytes pc r ={E}=∗
    ∃ σf : mstate,
      ⌜ exec (fetch tt) σ = Some (r, σf) ⌝ ∗
      ⌜ σf.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ forall rr, register_beq rr tlb = false ->
          register_lookup rr σf.(sregs) = register_lookup rr σ.(sregs) ⌝ ∗
      mstate_interp σf ∗
      tlb_res_pt root_ppn.
  Proof.
    (* the shared-kernel-table regime's witness is [emp] at EVERY tier
       ([sr_ktier_wit_kpt_share]), so this restatement stays a one-liner and
       is itself tier-generic. *)
    intros HE Lpc Lpriv Lmisa Lmenv Lhtif LSXL Lpma.
    iIntros "Hsi Hinv Hb".
    iApply (s_regime_fetch (kpt_share_regime root_ppn) σ pc r E
              HE Lpc Lpriv Lmisa Lmenv Lhtif LSXL Lpma
              with "[] Hsi Hinv Hb").
    iApply sr_ktier_wit_kpt_share.
  Qed.

  (* the Sv39-kernel regime's residue as a function of the tlb value:
     [SRegime.kpt_swp_res root_ppn rs] with the file's [tlb] read off. *)
  Definition spt_res_pt (root_ppn : mword 44) (tv : type_of_register tlb)
    : iProp Σ := (tlb_snap_ok tv ∗ kpt_inv root_ppn)%I.

  (* ==================================================================== *)
  (* wp_instr_s_config_tlbinv_pt -- the Sv39-kernel instance, on the       *)
  (* SHARED table's per-hart residue [KptShare.tlb_res_pt].  The bundle's  *)
  (* satp / pmp values are its own existentials, so the leaf's obligation  *)
  (* is ∀ over them; the continuation gets the bundle back.                *)
  (* ==================================================================== *)
  (* NOT PROVED: [tlb_res_pt_intro] / its destructuring around
     [wp_instr_s_config_regime] at [Res := spt_res_pt root_ppn]. *)
  Lemma wp_instr_s_config_tlbinv_pt (root_ppn : mword 44)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (Rl : mword 64 -> mword 64 -> mword 64 -> iProp Σ) {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_res_pt root_ppn -∗
    pc_is pc -∗
    instr pc is_rvc i -∗
    (∀ (satp0 : mword 64) (pcfg : type_of_register pmpcfg_n)
       (paddr : type_of_register pmpaddr_n),
       spt_fetch_tr (s_Df_mix dq) (spt_res_pt root_ppn) pc mstatus0 satp0
         mie_v mdv0 menvcfg0 pcfg paddr) -∗
    (∀ (satp0 : mword 64) (pcfg : type_of_register pmpcfg_n)
       (paddr : type_of_register pmpaddr_n) (tv' : type_of_register tlb),
       ⌜ pmp_ent0_ok pcfg paddr ⌝ -∗
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       satp ↦ᵣ satp0 -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
       tlb ↦ᵣ tv' -∗ spt_res_pt root_ppn tv' -∗
       clock_res -∗
       (R_bitvector_64 PC) ↦ᵣ pc -∗
       (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       resv_any cpu_id -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   cur_privilege ↦ᵣ{ dq } Supervisor ∗
                   mie ↦ᵣ{ dq } mie_v ∗
                   menvcfg ↦ᵣ{ dq } menvcfg0 ∗
                   satp ↦ᵣ satp0 ∗ pmpcfg_n ↦ᵣ pcfg ∗
                   pmpaddr_n ↦ᵣ paddr ∗
                   (∃ tv2 : type_of_register tlb,
                      tlb ↦ᵣ tv2 ∗ spt_res_pt root_ppn tv2) ∗
                   clock_res ∗
                   (∃ ms1 mdv1 npc : mword 64,
                      mstatus ↦ᵣ{ dq } ms1 ∗ mideleg ↦ᵣ{ dq } mdv1 ∗
                      (R_bitvector_64 PC) ↦ᵣ pc ∗
                      (R_bitvector_64 nextPC) ↦ᵣ npc ∗ Rl npc ms1 mdv1) ∗
                   resv_any cpu_id)) -∗
    ▷ (∀ npc ms1 mdv1 : mword 64,
         hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
         cur_privilege ↦ᵣ{ dq } Supervisor -∗
         mstatus ↦ᵣ{ dq } ms1 -∗
         mie ↦ᵣ{ dq } mie_v -∗
         mideleg ↦ᵣ{ dq } mdv1 -∗
         menvcfg ↦ᵣ{ dq } menvcfg0 -∗
         tlb_res_pt root_ppn -∗
         pc_is npc -∗ Rl npc ms1 mdv1 -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL Hmm HPBMTE Hmenvval.
    iIntros "#Hhw #Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Htlbres
             Hpc Hinstr Htr Hex Hcont".
    iDestruct "Htlbres" as (satp0 tlbv)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlbc & Hsnap & Hpmp & #Hkpt)".
    iDestruct "Hpmp" as (pcfg paddr)
      "(Hpcfg & Hpaddr & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iApply (wp_instr_s_config_regime (spt_res_pt root_ppn) pc is_rvc i
              mstatus0 mie_v mdv0 menvcfg0 satp0 pcfg paddr tlbv
              mie_v menvcfg0 satp0 pcfg paddr Rl (dq := dq)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval
              ltac:(unfold pmp_ent0_ok; split_and!; assumption)
              with "Hhw Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp
                    Hpcfg Hpaddr Htlbc [Hsnap] Hpc Hinstr [Htr] [Hex]
                    [Hcont]").
    - rewrite /spt_res_pt. iFrame "Hsnap Hkpt".
    - iApply ("Htr" $! satp0 pcfg paddr).
    - iApply ("Hex" $! satp0 pcfg paddr).
    - iNext. iIntros (npc ms1 mdv1 tv1)
        "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp Hpcfg Hpaddr Htlbc
         HRes Hpc HRl".
      iDestruct "HRes" as "[Hsnap _]".
      iDestruct "Hsnap" as (t0) "[%Hok #Hlb]".
      iApply ("Hcont" $! npc ms1 mdv1 with
                "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc
                 [Hsatp Htlbc Hpcfg Hpaddr] Hpc HRl").
      iApply (tlb_res_pt_intro root_ppn satp0 tv1 t0 Hmode Hasid Hppn Hok
                with "Hsatp Htlbc Hlb [Hpcfg Hpaddr] Hkpt").
      iApply (pmp_config_intro root_ppn pcfg paddr HA Hord HX HW HR Hcov
                with "Hpcfg Hpaddr").
  Qed.

  (* ==================================================================== *)
  (* THE [sr_inv R] SURFACE.                                              *)
  (*                                                                      *)
  (* Everything above takes the regime's four CELLS and a residue family   *)
  (* [Res], which is what the swp engine needs and what no LEAF can carry: *)
  (* a leaf carries [SRegime.sr_inv R].  These two wrappers restore that   *)
  (* surface, using the record's bundle face ([sr_swp_open] /              *)
  (* [sr_swp_close], added with this layer): open it into the cells and    *)
  (* the (satp,tlb)-indexed residue on the way in, close it back on the    *)
  (* way out at the tlb value the fetch's walk landed on.                  *)
  (*                                                                      *)
  (* satp / pmpcfg_n / pmpaddr_n come back UNCHANGED (the leaf returns     *)
  (* them at the values it got), so [sr_swp_close]'s two pure premises are *)
  (* the very facts [sr_swp_open] produced -- which is why the regime is   *)
  (* re-formed without the caller ever naming a satp value.                *)
  (* ==================================================================== *)
  Lemma wp_instr_s_config_sr (R : s_regime)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (mie1 menvcfg1 : mword 64)
      (Rl : mword 64 -> mword 64 -> mword 64 -> iProp Σ) {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗
    instr pc is_rvc i -∗
    (* the regime's fetch translation, at whatever cell values the bundle
       turns out to hold *)
    (∀ (satp0 : mword 64) (pcfg : type_of_register pmpcfg_n)
       (paddr : type_of_register pmpaddr_n),
       ⌜ sr_swp_satp_ok R satp0 ⌝ -∗ ⌜ pmp_ent0_ok pcfg paddr ⌝ -∗
       spt_fetch_tr (s_Df_mix dq) (sr_swp_res_at R satp0) pc mstatus0
         satp0 mie_v mdv0 menvcfg0 pcfg paddr) -∗
    (* THE LEAF'S OBLIGATION, at the bundle's cells and the walk's landing
       tlb value *)
    (∀ (satp0 : mword 64) (pcfg : type_of_register pmpcfg_n)
       (paddr : type_of_register pmpaddr_n) (tv' : type_of_register tlb),
       ⌜ sr_swp_satp_ok R satp0 ⌝ -∗ ⌜ pmp_ent0_ok pcfg paddr ⌝ -∗
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       satp ↦ᵣ satp0 -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
       tlb ↦ᵣ tv' -∗ sr_swp_res_at R satp0 tv' -∗
       clock_res -∗
       (R_bitvector_64 PC) ↦ᵣ pc -∗
       (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       resv_any cpu_id -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   cur_privilege ↦ᵣ{ dq } Supervisor ∗
                   mie ↦ᵣ{ dq } mie1 ∗
                   menvcfg ↦ᵣ{ dq } menvcfg1 ∗
                   satp ↦ᵣ satp0 ∗ pmpcfg_n ↦ᵣ pcfg ∗
                   pmpaddr_n ↦ᵣ paddr ∗
                   (∃ tv2 : type_of_register tlb,
                      tlb ↦ᵣ tv2 ∗ sr_swp_res_at R satp0 tv2) ∗
                   clock_res ∗
                   (∃ ms1 mdv1 npc : mword 64,
                      mstatus ↦ᵣ{ dq } ms1 ∗ mideleg ↦ᵣ{ dq } mdv1 ∗
                      (R_bitvector_64 PC) ↦ᵣ pc ∗
                      (R_bitvector_64 nextPC) ↦ᵣ npc ∗ Rl npc ms1 mdv1) ∗
                   resv_any cpu_id)) -∗
    ▷ (∀ npc ms1 mdv1 : mword 64,
         hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
         cur_privilege ↦ᵣ{ dq } Supervisor -∗
         mstatus ↦ᵣ{ dq } ms1 -∗
         mie ↦ᵣ{ dq } mie1 -∗
         mideleg ↦ᵣ{ dq } mdv1 -∗
         menvcfg ↦ᵣ{ dq } menvcfg1 -∗
         sr_inv R -∗
         pc_is npc -∗ Rl npc ms1 mdv1 -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL Hmm HPBMTE Hmenvval.
    iIntros "#Hhw #Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hinv Hpc
             Hinstr Htr Hex Hcont".
    iDestruct (sr_swp_open R with "Hinv") as (satp0 tlbv pcfg paddr)
      "(%Hsatpok & %Hpmpok & Hsatp & Htlbc & Hpcfg & Hpaddr & HRes)".
    iApply (wp_instr_s_config_regime (sr_swp_res_at R satp0) pc is_rvc i
              mstatus0 mie_v mdv0 menvcfg0 satp0 pcfg paddr tlbv
              mie1 menvcfg1 satp0 pcfg paddr Rl (dq := dq)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval Hpmpok
              with "Hhw Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp
                    Hpcfg Hpaddr Htlbc HRes Hpc Hinstr [Htr] [Hex] [Hcont]").
    - iApply ("Htr" $! satp0 pcfg paddr with "[%] [%]");
        [ exact Hsatpok | exact Hpmpok ].
    - iIntros (tv') "_".
      iApply ("Hex" $! satp0 pcfg paddr tv' with "[%] [%]");
        [ exact Hsatpok | exact Hpmpok ].
    - iNext. iIntros (npc ms1 mdv1 tv1)
        "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp Hpcfg Hpaddr Htlbc
         HRes Hpc HRl".
      iApply ("Hcont" $! npc ms1 mdv1 with
                "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc
                 [Hsatp Htlbc Hpcfg Hpaddr HRes] Hpc HRl").
      iApply (sr_swp_close R satp0 tv1 pcfg paddr Hsatpok Hpmpok
                with "Hsatp Htlbc Hpcfg Hpaddr HRes").
  Qed.

  (* the bundle twin, on [SmodeCore.smode_config] *)
  (* NOTE: the leaf's obligation is ∀ over the config values because
     [smode_config] quantifies them, exactly as [wp_instr_s_regime] does. *)
  Lemma wp_instr_s_sr (R : s_regime) (γ : gname)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (Rl : mword 64 -> iProp Σ) {dq : dfrac} :
    smode_config γ dq -∗
    sr_inv R -∗
    pc_is pc -∗
    instr pc is_rvc i -∗
    (∀ (mstatus0 mie_v mdv0 menvcfg0 satp0 : mword 64)
       (pcfg : type_of_register pmpcfg_n)
       (paddr : type_of_register pmpaddr_n),
       ⌜ eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ⌝ -∗
       ⌜ _get_Mstatus_SXL mstatus0 = 'b"10" ⌝ -∗
       ⌜ and_vec mie_v (not_vec mdv0) = zeros' 64 ⌝ -∗
       ⌜ menvcfg0 = MENVCFG_S ⌝ -∗
       ⌜ sr_swp_satp_ok R satp0 ⌝ -∗ ⌜ pmp_ent0_ok pcfg paddr ⌝ -∗
       spt_fetch_tr (s_Df_mix dq) (sr_swp_res_at R satp0) pc mstatus0
         satp0 mie_v mdv0 menvcfg0 pcfg paddr) -∗
    (∀ (mstatus0 mie_v mdv0 menvcfg0 satp0 : mword 64)
       (pcfg : type_of_register pmpcfg_n)
       (paddr : type_of_register pmpaddr_n) (tv' : type_of_register tlb),
       ⌜ sr_swp_satp_ok R satp0 ⌝ -∗ ⌜ pmp_ent0_ok pcfg paddr ⌝ -∗
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       satp ↦ᵣ satp0 -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
       tlb ↦ᵣ tv' -∗ sr_swp_res_at R satp0 tv' -∗
       clock_res -∗
       (R_bitvector_64 PC) ↦ᵣ pc -∗
       (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       resv_any cpu_id -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   cur_privilege ↦ᵣ{ dq } Supervisor ∗
                   mstatus ↦ᵣ{ dq } mstatus0 ∗
                   mie ↦ᵣ{ dq } mie_v ∗
                   mideleg ↦ᵣ{ dq } mdv0 ∗
                   menvcfg ↦ᵣ{ dq } menvcfg0 ∗
                   satp ↦ᵣ satp0 ∗ pmpcfg_n ↦ᵣ pcfg ∗
                   pmpaddr_n ↦ᵣ paddr ∗
                   (∃ tv2 : type_of_register tlb,
                      tlb ↦ᵣ tv2 ∗ sr_swp_res_at R satp0 tv2) ∗
                   clock_res ∗
                   (∃ npc : mword 64,
                      (R_bitvector_64 PC) ↦ᵣ pc ∗
                      (R_bitvector_64 nextPC) ↦ᵣ npc ∗ Rl npc) ∗
                   resv_any cpu_id)) -∗
    ▷ (∀ npc : mword 64,
         smode_config γ dq -∗ sr_inv R -∗ pc_is npc -∗ Rl npc -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hsm Hinv Hpc Hinstr Htr Hex Hcont".
    iDestruct (smode_config_unbundle with "Hsm")
      as "(#Hhw & #Hminv & Hhs & Hpriv & Hmst & Hmiebundle & Hmenvbundle)".
    iDestruct "Hmst" as (mstatus0)
      "(Hmstatus & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmiebundle" as (mie_v mdv0) "(Hmiec & Hmdlc & %Hmm)".
    iDestruct "Hmenvbundle" as (menvcfg0)
      "(Hmenvc & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval)".
    iApply (wp_instr_s_config_sr R pc is_rvc i mstatus0 mie_v mdv0 menvcfg0
              mie_v menvcfg0
              (fun npc ms1 mdv1 =>
                 (⌜ ms1 = mstatus0 ⌝ ∗ ⌜ mdv1 = mdv0 ⌝ ∗ Rl npc)%I) (dq := dq)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval
              with "Hhw Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hinv Hpc
                    Hinstr [Htr] [Hex] [Hcont Hsie]").
    - iIntros (satp0 pcfg paddr) "%Hsok %Hpok".
      iApply ("Htr" $! mstatus0 mie_v mdv0 menvcfg0 satp0 pcfg paddr
                with "[%] [%] [%] [%] [%] [%]");
        [ exact HSIE | exact HSXL | exact Hmm | exact Hmenvval
        | exact Hsok | exact Hpok ].
    - (* the BUNDLE keeps a FIXED post config ([smode_config] requires
         SIE = 0 of what it re-bundles); the two equations ride the rider *)
      iIntros (satp0 pcfg paddr tv') "%Hsok %Hpok Hpriv Hmstatus Hmiec Hmdlc
               Hmenvc Hsatp Hpcfg Hpaddr Htlbc HRes Hclk HPC HnPC Hany".
      iApply (swp_mono with "[] [-]");
        [| iApply ("Hex" $! mstatus0 mie_v mdv0 menvcfg0 satp0 pcfg paddr tv'
             with "[%] [%] Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp Hpcfg
                   Hpaddr Htlbc HRes Hclk HPC HnPC Hany") ].
      2:{ exact Hsok. }
      2:{ exact Hpok. }
      iIntros (e) "(-> & Hpriv & Hmstatus & Hmiec & Hmdlc & Hmenvc & Hsatp &
                    Hpcfg & Hpaddr & Htlbr & Hclk & Hpcs & Hany)".
      iDestruct "Hpcs" as (npc) "(HPC & HnPC & HRl)".
      iFrame "Hpriv Hmiec Hmenvc Hsatp Hpcfg Hpaddr Htlbr Hclk Hany".
      iSplitR; [done|].
      iExists mstatus0, mdv0, npc. iFrame "Hmstatus Hmdlc HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iExact "HRl".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hinv Hpc (-> & -> & HRl)".
      iApply ("Hcont" $! npc with
                "[Hhs Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc] Hinv Hpc HRl").
      iApply (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval
                with "Hhw Hminv Hhs Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc").
  Qed.

End SmodeCorePt.
