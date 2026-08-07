(** * WeakFetch2.v — THE TWO 2-ALIGNED FETCH ARMS, at [exec_eff] (M4 batch 0b gap)

    [WeakFetchEff] mirrors the 4-aligned [F_Base] arm of
    [WeakFunnel.exec_fetch_flat] and [WeakFetchRvc] the [F_RVC] arm at a
    4-aligned pc.  This file closes the remaining gap: the two arms at a pc
    that is 2- but NOT 4-aligned — which xv6's kernel text does reach, after
    an odd number of compressed instructions.

      - [F_Base] at a 2-aligned pc performs TWO 2-byte reads (the low half at
        [pc], then — [isRVC] of the low half being false — the high half at
        [pc+2]) and reassembles the word ([RiscvFetchExec.exec_fetch_F_Base_2]).
        Its trace therefore has TWO elements,
        [[WEread wak_plain pc 2; WEread wak_plain (add_vec_int pc 2) 2]],
        and a leaf over it needs the THREE-element certificate family §5
        provides (off [WeakEff.wcert_*_gen], whose [nowrite_trace] prefix the
        split fetch's 2-element trace satisfies immediately).
      - [F_RVC] at a 2-aligned pc performs ONE 2-byte read
        ([RiscvFetchExec.exec_fetch_RVC_2]); its trace is the single element
        [[WEread wak_plain pc 2]], so [WeakCert]'s own certificates apply at
        [nf := 2] verbatim (§5 states the instances).

    Everything register-only that the two arms name is REUSED, not
    re-mirrored: the PMP cone ([WeakPmpEff]), the interrupt gate and the
    [within_*]/[translateAddr]/[effectivePrivilege] prefix ([WeakFetchEff]
    §1/§5), the [Ext_Zca] probe ([WeakFetchRvc] §1 — the misaligned-pc guard
    evaluates it, which is why both arms take the misa.C bit), the tick
    ([WeakFetchEff] §7) and the decode bridge ([WeakFetchEff] §6).  What is
    NEW here is only the width-2 memory chain at [exec_eff]
    ([exec_read_ram_plain_2] and the stack over it) and the two-chunk trace
    composition.

    Sections:
      §1  the width-2 memory chain: read_ram -> checked_mem_read -> mem_read
          -> fetch_bytes, each with the ONE trace element threaded through
      §2  the two fetch arms: [exec_eff_fetch_RVC_2] / [exec_eff_fetch_F_Base_2]
      §3  the [fetch_flat_ok] wrappers, [WeakFunnel.exec_fetch_flat]'s
          2-aligned arms at [exec_eff]
      §4  the recipes: [wP_eff_of_leaf_base2] / [wP_eff_of_leaf_rvc2]
      §5  the certificates at the 2-aligned fetch prefixes, and the
          end-to-end join check
*)
From Stdlib Require Import ZArith Zquot Zwf.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff.
Require Import WeakRacy.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import WeakEffSkel.
Require Import WeakPmpEff.
Require Import WeakFunnel.
Require Import WpDecodeBridge.
Require Import WeakTickEff.
Require Import WeakLeafEffCommon.
Require Import WeakFetchEff.
Require Import WeakFetchRvc.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE WIDTH-2 MEMORY CHAIN, with the trace threaded through

    [RiscvFetchExec]'s width-2 stack ([exec_read_ram_plain_2] ->
    [exec_checked_mem_read_ram_2] -> [exec_mem_read_fetch_2] ->
    [exec_fetch_bytes_2]) replayed at [exec_eff], exactly as [WeakFetchEff]
    §2–§3 replays the width-4 stack.  [fetch_bytes] is generalised over the
    fetched address [pc2] (the SC tree proves [pc2 := pc] as a Section and
    the [pc+2] instance inline; ONE lemma here serves both chunks of the
    split fetch). *)

(** The PMP corollary at width 2 — [WeakPmpEff]'s reduction, with
    [RiscvFetchExec.exec_pmpCheck_machine_unlocked_ifetch2]'s fit
    arithmetic: a 2-byte access at a 2-aligned address stays inside one
    aligned 4-byte grain cell. *)
Lemma exec_eff_pmpCheck_machine_unlocked_ifetch2
    (addr : SailStdpp.Values.mword 64) s :
  (forall i, pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false) ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  exec_eff (pmpCheck (Physaddr addr) 2 (InstructionFetch tt) Machine) s
    = Some (None, s, []).
Proof.
  intros HL Halign.
  apply exec_eff_pmpCheck_machine_unlocked;
    [exact HL | intros ent; eexists; reflexivity |].
  unfold is_aligned_paddr in Halign. apply Z.eqb_eq in Halign.
  apply Zrem_divides in Halign. destruct Halign as [k Hk].
  change (bits_of_physaddr (Physaddr addr)) with addr.
  replace (uint (to_bits 64 2)) with 2 by (vm_compute; reflexivity).
  rewrite Hk.
  pose proof (Z.mod_pos_bound (2 * k) 4 ltac:(lia)).
  pose proof (Z.div_mod (2 * k) 4 ltac:(lia)).
  lia.
Qed.

(** The ONE effect of each 2-byte chunk.  [WeakFetchEff.exec_eff_read_ram_plain_4]
    at width 2. *)
Lemma exec_eff_read_ram_plain_2 (addr : SailStdpp.Values.mword 64) (w : bv 16) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 2)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec_eff (read_ram Read_plain (Physaddr addr) 2 false) s
    = Some ((w, default_meta), s, [WEread wak_plain addr 2]).
Proof.
  intros Hdev Hbytes.
  unfold read_ram. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_read. cbn beta zeta.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  cbn [exec_eff]. cbn [Interface.ReadReq.pa Interface.ReadReq.access_kind].
  rewrite Hdev.
  rewrite (read_bytes_of_bytes (mem s) addr (Z.to_N 2) w
             (fun j Hj => Hbytes j ltac:(lia))).
  cbn [Interface.iMon_bind]. cbn match beta iota.
  reflexivity.
Qed.

Lemma exec_eff_pmaCheck_ram_2 (addr : SailStdpp.Values.mword 64)
    (pbmt : page_based_mem_type) (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2
    = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec_eff (pmaCheck (Physaddr addr) 2 (InstructionFetch tt) pbmt false) s
    = Some (None, s, []).
Proof.
  intros Hmatch Halign Hexec.
  unfold pmaCheck.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hexec |- *.
  rewrite Halign. cbn [negb].
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM None s)).
  cbn match beta.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM _ s)).
  rewrite Hexec. cbn [andb negb].
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_checked_mem_read_ram_2 (pbmt : page_based_mem_type)
    (addr : SailStdpp.Values.mword 64) (region : PMA_Region) (w : bv 16) s :
  exec_eff (pmpCheck (Physaddr addr) 2 (InstructionFetch tt) Machine) s
    = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2
    = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec_eff (within_clint (Physaddr addr) 2) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 2) s = Some (false, s, []) ->
  exec_eff (within_htif_readable (Physaddr addr) 2) s = Some (false, s, []) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 2)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec_eff (checked_mem_read (InstructionFetch tt) pbmt Machine
              (Physaddr addr) 2 false false false false) s
    = Some (Ok (w, default_meta), s, [WEread wak_plain addr 2]).
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes.
  unfold checked_mem_read.
  (* phys_access_check = None, trace [] *)
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (phys_access_check _ _ _ _ _ _) s = Some (None, s, []))).
  2:{ unfold phys_access_check.
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hpmp). cbn match.
      rewrite (exec_eff_bind_nil _ _ _ _ _
                (exec_eff_pmaCheck_ram_2 addr pbmt region s Hmatch Halign Hexec)).
      cbn match. apply exec_eff_returnM. }
  (* within_mmio_readable = false, trace [] *)
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (within_mmio_readable (Physaddr addr) 2) s
                 = Some (false, s, []))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hc). cbn match.
      rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (read_kind_of_flags _ _ _) s = Some (Read_plain, s, []))).
  2:{ unfold read_kind_of_flags. apply exec_eff_returnM. }
  (* the ONE memory step *)
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
            (exec_eff_read_ram_plain_2 addr w s Hdev Hbytes)).
  rewrite exec_eff_returnM. reflexivity.
Qed.

Lemma exec_eff_mem_read_fetch_2 (pbmt : page_based_mem_type)
    (addr : SailStdpp.Values.mword 64) (region : PMA_Region) (w : bv 16) s :
  exec_eff (pmpCheck (Physaddr addr) 2 (InstructionFetch tt) Machine) s
    = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2
    = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec_eff (within_clint (Physaddr addr) 2) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 2) s = Some (false, s, []) ->
  exec_eff (within_htif_readable (Physaddr addr) 2) s = Some (false, s, []) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 2)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 2 false false false) s
    = Some (Ok w, s, [WEread wak_plain addr 2]).
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes Hpriv.
  unfold mem_read.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_effectivePrivilege_fetch _ _ s)).
  rewrite Hpriv.
  unfold mem_read_priv.
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
            (_ : exec_eff (mem_read_priv_meta _ _ _ _ 2 _ _ _ _) s
                 = Some (Ok (w, default_meta), s, [WEread wak_plain addr 2]))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_eff_bind_Some _ _ _ _ _ _
                (_ : exec_eff (checked_mem_read _ _ _ _ 2 _ _ _ _) s
                     = Some (Ok (w, default_meta), s, [WEread wak_plain addr 2]))).
      2:{ cbn match.
          apply exec_eff_checked_mem_read_ram_2 with (region := region); assumption. }
      cbn match. unfold mem_read_callback. rewrite exec_eff_returnM.
      by rewrite app_nil_r. }
  cbn [MemoryOpResult_drop_meta]. rewrite exec_eff_returnM.
  by rewrite app_nil_r.
Qed.

(** [fetch_bytes pc pc2 2] — [RiscvFetchExec.exec_fetch_bytes_2] replayed and
    generalised over the fetched address [pc2], so ONE lemma serves the low
    chunk ([pc2 := pc]) and the high chunk ([pc2 := add_vec_int pc 2]) of the
    split fetch. *)
Lemma exec_eff_fetch_bytes_2 (pc pc2 : SailStdpp.Values.mword 64)
    (region : PMA_Region) (w : SailStdpp.Values.mword 16) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (pmpCheck (Physaddr (fetch_pa pc2)) 2 (InstructionFetch tt) Machine) s
    = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs))
    (Physaddr (fetch_pa pc2)) 2 = Some region ->
  is_aligned_paddr (Physaddr (fetch_pa pc2)) 2 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  exec_eff (within_clint (Physaddr (fetch_pa pc2)) 2) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr (fetch_pa pc2)) 2) s = Some (false, s, []) ->
  exec_eff (within_htif_readable (Physaddr (fetch_pa pc2)) 2) s
    = Some (false, s, []) ->
  dev_addr (fetch_pa pc2) = false ->
  (forall j : nat, (N.of_nat j < 2)%N ->
     s.(mem) !! (pa_add (fetch_pa pc2) j) = Some (nth_byte w j)) ->
  exec_eff (fetch_bytes pc pc2 2) s
    = Some (@FetchBytes_Success 2 w, s, [WEread wak_plain (fetch_pa pc2) 2]).
Proof.
  intros Hpriv Hpmp Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes.
  unfold fetch_bytes.
  rewrite exec_eff_catch_early_return.
  change (ext_fetch_check_pc pc pc2) with (@None unit). cbv iota beta.
  rewrite (execR_eff_bind_nil _ _ _ _ _
    (_ : execR_eff (Defs.bind0 (Defs.returnR _ tt)
            (Defs.liftR (translateAddr (Virtaddr pc2) (InstructionFetch tt)))) s
         = Some (inr (Ok (Physaddr (fetch_pa pc2), PBMT_PMA, init_ext_ptw)), s, []))).
  2:{ rewrite (execR_eff_bind0_nil _ _ _ _ (execR_eff_returnR tt s)).
      rewrite execR_eff_liftR. rewrite (exec_eff_translateAddr_identity pc2 s Hpriv).
      cbn match. reflexivity. }
  cbv iota beta.
  rewrite (execR_eff_bind_nil _ _ _ _ _
             (execR_eff_returnR (Physaddr (fetch_pa pc2), PBMT_PMA) s)).
  cbv iota beta.
  rewrite (execR_eff_bind_cat _ _ _ _ _ _
    (_ : execR_eff (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA
                                 (Physaddr (fetch_pa pc2)) 2 false false false)) s
         = Some (inr (Ok w), s, [WEread wak_plain (fetch_pa pc2) 2]))).
  2:{ rewrite execR_eff_liftR.
      rewrite (exec_eff_mem_read_fetch_2 PBMT_PMA (fetch_pa pc2) region w s
                 Hpmp Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes Hpriv).
      cbn match. reflexivity. }
  cbv iota beta. rewrite autocast_mword_id_16.
  rewrite execR_eff_returnR. cbn match. cbn [app]. reflexivity.
Qed.

(* ====================================================================== *)
(** ** 2. THE TWO FETCH ARMS

    [RiscvFetchExec.exec_fetch_RVC_2] / [exec_fetch_F_Base_2] replayed, with
    the chunk traces joined by [execR_eff_liftR_cat].  The misaligned-pc
    guard evaluates the [Ext_Zca] probe (bit 1 of the pc is set), which is
    where the misa.C premise enters — [WeakFetchRvc]'s
    [exec_eff_currentlyEnabled_Zca], reused. *)

Section FetchRVC2Eff.
  Context (pc : SailStdpp.Values.mword 64) (region : PMA_Region)
          (w : SailStdpp.Values.mword 16) (s : mstate).
  Let addr := fetch_pa pc.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp :
    exec_eff (pmpCheck (Physaddr addr) 2 (InstructionFetch tt) Machine) s
      = Some (None, s, []).
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 2 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 2 = true.
  Hypothesis Hexec :
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec_eff (within_clint (Physaddr addr) 2) s = Some (false, s, []).
  Hypothesis Hsig : exec_eff (within_sig (Physaddr addr) 2) s = Some (false, s, []).
  Hypothesis Hh : exec_eff (within_htif_readable (Physaddr addr) 2) s
      = Some (false, s, []).
  Hypothesis Hdev : dev_addr addr = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 2)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).
  Hypothesis Hbit0 : neq_vec (access_vec_dec pc 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec pc 1) ('b"0") = true.
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = false.
  Hypothesis HmisaC :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis HisRVC : isRVC w = true.

  Lemma exec_eff_fetch_RVC_2 :
    exec_eff (fetch tt) s = Some (F_RVC w, s, [WEread wak_plain addr 2]).
  Proof using All.
    assert (HrdPC : exec_eff (Defs.read_reg PC : M _) s = Some (pc, s, [])).
    { rewrite (exec_eff_read_reg PC s). rewrite HpcPC. reflexivity. }
    unfold fetch.
    rewrite exec_eff_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    (* the misalignment guard = false: bit0 clear, bit1 set, Zca enabled *)
    rewrite (execR_eff_bind_nil _ _ _ false s).
    2:{ rewrite (execR_eff_bind0_nil _ _ _ _ (execR_eff_returnR tt s)).
        unfold Defs.or_boolM.
        rewrite (execR_eff_bind_nil _ _ _ false s).
        2:{ rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0.
            apply execR_eff_returnR. }
        cbv iota beta.
        unfold Defs.and_boolM.
        rewrite (execR_eff_bind_nil _ _ _ true s).
        2:{ rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1.
            apply execR_eff_returnR. }
        cbv iota beta.
        rewrite (execR_eff_bind_nil _ _ _ true s).
        2:{ rewrite execR_eff_liftR.
            rewrite (exec_eff_currentlyEnabled_Zca s HmisaC). cbn match.
            apply execR_eff_returnR. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    (* the (4-aligned && Ziccif) guard = false: not 4-aligned *)
    rewrite (execR_eff_bind_nil _ _ _ false s).
    2:{ unfold Defs.and_boolM.
        rewrite (execR_eff_bind_nil _ _ _ false s).
        2:{ rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign.
            apply execR_eff_returnR. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    (* the 2-byte read, and the RVC dispatch on its result *)
    rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_eff_liftR_cat _ _ _ _ _ _
               (exec_eff_fetch_bytes_2 pc pc region w s Hpriv Hpmp Hmatch Halign
                  Hexec Hc Hsig Hh Hdev Hbytes)).
    cbv iota beta. rewrite HisRVC. cbv iota beta.
    rewrite execR_eff_returnR. cbn match. cbn [app]. reflexivity.
  Qed.
End FetchRVC2Eff.

Section FetchFBase2Eff.
  Context (pc : SailStdpp.Values.mword 64) (regl regh : PMA_Region)
          (w : SailStdpp.Values.mword 32) (s : mstate).
  Let addr := fetch_pa pc.
  Let addrh := fetch_pa (add_vec_int pc 2).
  Let ilo : SailStdpp.Values.mword 16 := subrange_vec_dec w 15 0.
  Let ihi : SailStdpp.Values.mword 16 := subrange_vec_dec w 31 16.

  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmpl :
    exec_eff (pmpCheck (Physaddr addr) 2 (InstructionFetch tt) Machine) s
      = Some (None, s, []).
  Hypothesis Hpmph :
    exec_eff (pmpCheck (Physaddr addrh) 2 (InstructionFetch tt) Machine) s
      = Some (None, s, []).
  Hypothesis Hmatchl : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 2 = Some regl.
  Hypothesis Hmatchh : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addrh) 2 = Some regh.
  Hypothesis Halignl : is_aligned_paddr (Physaddr addr) 2 = true.
  Hypothesis Halignh : is_aligned_paddr (Physaddr addrh) 2 = true.
  Hypothesis Hexecl :
    (override_PMA (PMA_Region_attributes regl) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hexech :
    (override_PMA (PMA_Region_attributes regh) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hcl : exec_eff (within_clint (Physaddr addr) 2) s = Some (false, s, []).
  Hypothesis Hsigl : exec_eff (within_sig (Physaddr addr) 2) s = Some (false, s, []).
  Hypothesis Hhl : exec_eff (within_htif_readable (Physaddr addr) 2) s
      = Some (false, s, []).
  Hypothesis Hch : exec_eff (within_clint (Physaddr addrh) 2) s = Some (false, s, []).
  Hypothesis Hsigh : exec_eff (within_sig (Physaddr addrh) 2) s = Some (false, s, []).
  Hypothesis Hhh : exec_eff (within_htif_readable (Physaddr addrh) 2) s
      = Some (false, s, []).
  Hypothesis Hdevl : dev_addr addr = false.
  Hypothesis Hdevh : dev_addr addrh = false.
  Hypothesis Hbytesl : forall j : nat, (N.of_nat j < 2)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte ilo j).
  Hypothesis Hbytesh : forall j : nat, (N.of_nat j < 2)%N ->
      s.(mem) !! (pa_add addrh j) = Some (nth_byte ihi j).
  Hypothesis Hbit0 : neq_vec (access_vec_dec pc 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec pc 1) ('b"0") = true.
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = false.
  Hypothesis HmisaC :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis HnotRVC : isRVC ilo = false.
  Hypothesis Hconcat : concat_vec ihi ilo = w.

  Lemma exec_eff_fetch_F_Base_2 :
    exec_eff (fetch tt) s
      = Some (F_Base w, s, [WEread wak_plain addr 2; WEread wak_plain addrh 2]).
  Proof using All.
    assert (HrdPC : exec_eff (Defs.read_reg PC : M _) s = Some (pc, s, [])).
    { rewrite (exec_eff_read_reg PC s). rewrite HpcPC. reflexivity. }
    unfold fetch.
    rewrite exec_eff_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    (* the misalignment guard = false: bit0 clear, bit1 set, Zca enabled *)
    rewrite (execR_eff_bind_nil _ _ _ false s).
    2:{ rewrite (execR_eff_bind0_nil _ _ _ _ (execR_eff_returnR tt s)).
        unfold Defs.or_boolM.
        rewrite (execR_eff_bind_nil _ _ _ false s).
        2:{ rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0.
            apply execR_eff_returnR. }
        cbv iota beta.
        unfold Defs.and_boolM.
        rewrite (execR_eff_bind_nil _ _ _ true s).
        2:{ rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1.
            apply execR_eff_returnR. }
        cbv iota beta.
        rewrite (execR_eff_bind_nil _ _ _ true s).
        2:{ rewrite execR_eff_liftR.
            rewrite (exec_eff_currentlyEnabled_Zca s HmisaC). cbn match.
            apply execR_eff_returnR. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    (* the (4-aligned && Ziccif) guard = false: not 4-aligned *)
    rewrite (execR_eff_bind_nil _ _ _ false s).
    2:{ unfold Defs.and_boolM.
        rewrite (execR_eff_bind_nil _ _ _ false s).
        2:{ rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign.
            apply execR_eff_returnR. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    (* the LOW chunk, [isRVC] false *)
    rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_eff_liftR_cat _ _ _ _ _ _
               (exec_eff_fetch_bytes_2 pc pc regl ilo s Hpriv Hpmpl Hmatchl Halignl
                  Hexecl Hcl Hsigl Hhl Hdevl Hbytesl)).
    cbv iota beta. rewrite HnotRVC. cbv iota beta.
    (* the HIGH chunk, and the reassembly *)
    rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_eff_liftR_cat _ _ _ _ _ _
               (exec_eff_fetch_bytes_2 pc (add_vec_int pc 2) regh ihi s Hpriv Hpmph
                  Hmatchh Halignh Hexech Hch Hsigh Hhh Hdevh Hbytesh)).
    cbv iota beta.
    rewrite execR_eff_returnR. cbn match. rewrite Hconcat. cbn [app]. reflexivity.
  Qed.
End FetchFBase2Eff.

(* ====================================================================== *)
(** ** 3. THE FUNNEL'S FETCH, AT [exec_eff] — the two 2-aligned arms

    [WeakFunnel.exec_fetch_flat]'s remaining two arms, mirrored exactly as
    [WeakFetchEff.exec_eff_fetch_flat_base4] / [WeakFetchRvc]'s
    [exec_eff_fetch_flat_rvc4] mirror the first two.  [fetch_flat_ok]'s
    footprint is always the FOUR bytes of one word at [pc], so the split
    fetch's two halves are carved out of it by
    [InstrBytes.nth_byte_subrange_lo]/[_hi], as the SC arm does. *)

Lemma exec_eff_fetch_flat_base2 (t : mstate) (pc : SailStdpp.Values.mword 64)
    (w : SailStdpp.Values.mword 32) :
  pmp_allows_all (register_lookup pmpcfg_n t.(sregs)) ->
  pma_allows_all (register_lookup pma_regions t.(sregs)) ->
  eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
  register_lookup PC t.(sregs) = pc ->
  register_lookup cur_privilege t.(sregs) = Machine ->
  register_lookup htif_tohost_base t.(sregs) = None ->
  is_aligned_vaddr (Virtaddr pc) 4 = false ->
  fetch_flat_ok t pc (F_Base w) ->
  exec_eff (fetch tt) t
    = Some (F_Base w, t,
            [WEread wak_plain pc 2; WEread wak_plain (add_vec_int pc 2) 2]).
Proof.
  intros Hpmp Hpma HmisaC Lpc Lpriv Lhtif Hal (H2al & Hram & w0 & Hr & Hbytes).
  destruct Hr as [<- HnotRVC].
  assert (Hram0 : addr_is_ram (fetch_pa pc)).
  { rewrite fetch_pa_id. rewrite <- (RiscvExtras.pa_add_0 pc). apply Hram. lia. }
  assert (Hram3 : addr_is_ram (pa_add (fetch_pa pc) 3)).
  { rewrite fetch_pa_id. apply Hram. lia. }
  assert (Hbf : forall j : nat, (N.of_nat j < 4)%N ->
            t.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j)).
  { intros j Hj. rewrite fetch_pa_id. apply Hbytes. lia. }
  pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
  pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
  destruct (InstrBytes.align2_not4_facts pc H2al Hal) as (Halignl & Hbit0 & Hbit1).
  pose proof (InstrBytes.align2_plus2 pc H2al) as Halignh.
  assert (Haddr : forall j : nat, (N.of_nat j < 2)%N ->
            pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j)).
  { intros j _. rewrite !fetch_pa_id. unfold pa_add.
    rewrite InstrBytes.avi_assoc. f_equal. lia. }
  assert (Hoff : fetch_pa (add_vec_int pc 2) = pa_add (fetch_pa pc) 2).
  { specialize (Haddr 0%nat ltac:(lia)).
    rewrite RiscvExtras.pa_add_0 in Haddr. exact Haddr. }
  assert (Hramh : addr_is_ram (fetch_pa (add_vec_int pc 2))).
  { rewrite Hoff fetch_pa_id. apply Hram. lia. }
  assert (Hramh1 : addr_is_ram (pa_add (fetch_pa (add_vec_int pc 2)) 1)).
  { rewrite (Haddr 1%nat ltac:(lia)). change (2 + 1)%nat with 3%nat.
    exact Hram3. }
  pose proof (addr_is_ram_not_in_clint _ Hramh) as Hnch.
  pose proof (addr_is_ram_not_in_sig _ Hramh) as Hnsh.
  destruct (pma_all_ram Hpma (fetch_pa pc) 2
             (pma_access_ram _ _ _ Hram0 Hram3
                (pma_width_ok 2 eq_refl eq_refl) eq_refl eq_refl))
    as (regl & Hml & Hxl & _ & _).
  destruct (pma_all_ram Hpma (fetch_pa (add_vec_int pc 2)) 2
             (pma_access_ram _ _ _ Hramh Hramh1
                (pma_width_ok 2 eq_refl eq_refl) eq_refl eq_refl))
    as (regh & Hmh & Hxh & _ & _).
  assert (Hbl : forall j : nat, (N.of_nat j < 2)%N ->
            t.(mem) !! (pa_add (fetch_pa pc) j)
              = Some (nth_byte (subrange_vec_dec w 15 0
                                : SailStdpp.Values.mword 16) j)).
  { intros j Hj. rewrite InstrBytes.nth_byte_subrange_lo; [|exact Hj].
    apply Hbf. lia. }
  assert (Hbh : forall j : nat, (N.of_nat j < 2)%N ->
            t.(mem) !! (pa_add (fetch_pa (add_vec_int pc 2)) j)
              = Some (nth_byte (subrange_vec_dec w 31 16
                                : SailStdpp.Values.mword 16) j)).
  { intros j Hj. rewrite InstrBytes.nth_byte_subrange_hi; [|exact Hj].
    rewrite (Haddr j Hj). apply Hbf. lia. }
  pose proof (exec_eff_fetch_F_Base_2 pc regl regh w t Lpc Lpriv
       (exec_eff_pmpCheck_machine_unlocked_ifetch2 (fetch_pa pc) t Hpmp Halignl)
       (exec_eff_pmpCheck_machine_unlocked_ifetch2 (fetch_pa (add_vec_int pc 2)) t
          Hpmp Halignh)
       Hml Hmh Halignl Halignh Hxl Hxh
       (exec_eff_within_clint_false (fetch_pa pc) 2 t Hnc ltac:(lia))
       (exec_eff_within_sig_false   (fetch_pa pc) 2 t Hns ltac:(lia))
       (exec_eff_within_htif_false  (fetch_pa pc) 2 t Lhtif)
       (exec_eff_within_clint_false (fetch_pa (add_vec_int pc 2)) 2 t Hnch ltac:(lia))
       (exec_eff_within_sig_false   (fetch_pa (add_vec_int pc 2)) 2 t Hnsh ltac:(lia))
       (exec_eff_within_htif_false  (fetch_pa (add_vec_int pc 2)) 2 t Lhtif)
       (addr_is_ram_not_dev _ Hram0) (addr_is_ram_not_dev _ Hramh)
       Hbl Hbh Hbit0 Hbit1 Hal HmisaC HnotRVC
       (InstrBytes.concat_subranges_id w)) as Hf.
  rewrite !fetch_pa_id in Hf. exact Hf.
Qed.

Lemma exec_eff_fetch_flat_rvc2 (t : mstate) (pc : SailStdpp.Values.mword 64)
    (h : SailStdpp.Values.mword 16) :
  pmp_allows_all (register_lookup pmpcfg_n t.(sregs)) ->
  pma_allows_all (register_lookup pma_regions t.(sregs)) ->
  eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
  register_lookup PC t.(sregs) = pc ->
  register_lookup cur_privilege t.(sregs) = Machine ->
  register_lookup htif_tohost_base t.(sregs) = None ->
  is_aligned_vaddr (Virtaddr pc) 4 = false ->
  fetch_flat_ok t pc (F_RVC h) ->
  exec_eff (fetch tt) t = Some (F_RVC h, t, [WEread wak_plain pc 2]).
Proof.
  intros Hpmp Hpma HmisaC Lpc Lpriv Lhtif Hal (H2al & Hram & w & Hr & Hbytes).
  destruct Hr as [Hsub HisRVC].
  assert (Hram0 : addr_is_ram (fetch_pa pc)).
  { rewrite fetch_pa_id. rewrite <- (RiscvExtras.pa_add_0 pc). apply Hram. lia. }
  assert (Hram1 : addr_is_ram (pa_add (fetch_pa pc) 1)).
  { rewrite fetch_pa_id. apply Hram. lia. }
  assert (Hbf : forall j : nat, (N.of_nat j < 4)%N ->
            t.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j)).
  { intros j Hj. rewrite fetch_pa_id. apply Hbytes. lia. }
  pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
  pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
  destruct (InstrBytes.align2_not4_facts pc H2al Hal) as (Halign & Hbit0 & Hbit1).
  destruct (pma_all_ram Hpma (fetch_pa pc) 2
             (pma_access_ram _ _ _ Hram0 Hram1
                (pma_width_ok 2 eq_refl eq_refl) eq_refl eq_refl))
    as (region & Hmatch & Hexec0 & _ & _).
  assert (Hbh : forall j : nat, (N.of_nat j < 2)%N ->
            t.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte h j)).
  { intros j Hj. rewrite <- Hsub.
    rewrite InstrBytes.nth_byte_subrange_lo; [|exact Hj]. apply Hbf. lia. }
  pose proof (exec_eff_fetch_RVC_2 pc region h t Lpc Lpriv
       (exec_eff_pmpCheck_machine_unlocked_ifetch2 (fetch_pa pc) t Hpmp Halign)
       Hmatch Halign Hexec0
       (exec_eff_within_clint_false (fetch_pa pc) 2 t Hnc ltac:(lia))
       (exec_eff_within_sig_false   (fetch_pa pc) 2 t Hns ltac:(lia))
       (exec_eff_within_htif_false  (fetch_pa pc) 2 t Lhtif)
       (addr_is_ram_not_dev _ Hram0) Hbh Hbit0 Hbit1 Hal HmisaC HisRVC) as Hf.
  rewrite fetch_pa_id in Hf. exact Hf.
Qed.

(* ====================================================================== *)
(** ** 4. THE RECIPES — [wP_eff_of_leaf_base] / [_rvc4] at a 2-aligned pc

    [WeakFetchEff.wP_eff_of_leaf_base] (resp. [WeakFetchRvc.wP_eff_of_leaf_rvc4])
    with the 4-alignment premise replaced by the 2-but-not-4 pair, the misa.C
    bit added (the misaligned-pc guard probes [Ext_Zca] on this path), and the
    fetch's trace the arm's own — two elements for [F_Base], one for [F_RVC].
    Everything else — the window, the config tower, the decode bridge, the
    [execute] fact, the tick — is IDENTICAL, and reused from [WeakFetchEff].

    The window binder is [(W : _)] for the instance-trap reason recorded at
    [wP_eff_of_leaf_base]; keep it that way at every call site. *)

Lemma wP_eff_of_leaf_base2
    (cid : nat) (σ : wmstate) (W : _)
    (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
    (i : instruction) (es_x : list weff)
    (D : register -> bool) (dst : mstate) :
  (* --- the window (porting guide §2, items 1-3) --- *)
  wlog_wf (wm_log σ) ->
  (forall a, a ∈ W -> pa_z a <> 0) ->
  (forall a, a ∈ W -> pinned_read σ (pa_z a)) ->
  (* --- the M-mode config tower: the SAME facts [wwp_instr] collects --- *)
  register_lookup PC (wm_regs σ) = pc ->
  register_lookup cur_privilege (wm_regs σ) = Machine ->
  pmp_allows_all (register_lookup pmpcfg_n (wm_regs σ)) ->
  pma_allows_all (register_lookup pma_regions (wm_regs σ)) ->
  register_lookup htif_tohost_base (wm_regs σ) = None ->
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
  eq_vec (_get_Misa_S (register_lookup misa (wm_regs σ))) ('b"1") = true ->
  eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ))) ('b"1") = true ->
  eq_vec (_get_Mstatus_MIE (register_lookup mstatus (wm_regs σ))) ('b"1")
    = false ->
  eq_vec (register_lookup elp (wm_regs σ))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  (* --- (a) the text word, IN THE CONFINED MEMORY, at a 2-not-4-aligned pc --- *)
  is_aligned_vaddr (Virtaddr pc) 2 = true ->
  is_aligned_vaddr (Virtaddr pc) 4 = false ->
  (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)) ->
  (forall j : nat, (j < 4)%nat ->
     wmem_restrict σ W !! pa_add pc j = Some (nth_byte w j)) ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  (* --- (b) the DECODE, exactly as the decode library states it --- *)
  (forall r, D r = true ->
     register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
  D (R_bool minstret_increment) = false ->
  goodb0 D (ext_decode w) dst = true ->
  exec (ext_decode w) dst = Some (i, dst) ->
  is_lpad_instruction i = false ->
  (* --- (c) the [execute]'s own [exec_eff] fact, and its register frame --- *)
  (forall b : bool, exists s_exec : mstate,
     exec_eff (execute i)
       (set_reg (set_reg (MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ))
                   (R_bool minstret_increment) b)
                nextPC (add_vec_int pc 4))
       = Some (RETIRE_SUCCESS, s_exec, es_x)
     /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
     /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b
     /\ dom (mem s_exec) ⊆ W) ->
  (* --- the certificate's whole obligation --- *)
  wP_eff (Some cid)
    ([WEread wak_plain pc 2; WEread wak_plain (add_vec_int pc 2) 2] ++ es_x) σ.
Proof.
  intros Hwf HW0 HWp Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmisaC LmIE Lelp
         Hal2 Hal4 Hram Htext HnotRVC Hagree HDmi Hgood Hdec Hnlpad Hexec.
  set (sconf := MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ)).
  apply (wP_eff_of_window cid _ σ W Hwf HW0 HWp).
  intros tick.
  (* the funnel's own choice of the [minstret_increment] flag *)
  destruct (exec_eff_should_inc_minstret_Some
              (register_lookup cur_privilege (sregs sconf)) sconf) as [b Hsi].
  destruct (Hexec b) as (s_exec & Hex & Hhe & Hmie & Hdom).
  (* every register fact, moved past the [minstret_increment] pre-write *)
  assert (Lpriv_a : register_lookup cur_privilege
            (sregs (set_reg sconf (R_bool minstret_increment) b)) = Machine)
    by (rewrite (set_mi_lookup cur_privilege _ b eq_refl); exact Lpriv).
  assert (Lpc_a : register_lookup PC
            (sregs (set_reg sconf (R_bool minstret_increment) b)) = pc)
    by (rewrite (set_mi_lookup PC _ b eq_refl); exact Lpc).
  assert (Lhart_a : register_lookup hart_state
            (sregs (set_reg sconf (R_bool minstret_increment) b))
            = HART_ACTIVE tt)
    by (rewrite (set_mi_lookup hart_state _ b eq_refl); exact Lhart).
  assert (Lelp_a : eq_vec (register_lookup elp
            (sregs (set_reg sconf (R_bool minstret_increment) b)))
            (landing_pad_bits_backwards LP_EXPECTED) = false)
    by (rewrite (set_mi_lookup elp _ b eq_refl); exact Lelp).
  (* the interrupt gate ([WeakFetchEff] §5) *)
  assert (Hdisp : exec_eff (dispatchInterrupt Machine)
            (set_reg sconf (R_bool minstret_increment) b)
            = Some (None, set_reg sconf (R_bool minstret_increment) b, [])).
  { apply exec_eff_dispatchInterrupt_machine_none.
    - rewrite (set_mi_lookup misa _ b eq_refl). exact LmisaS.
    - rewrite (set_mi_lookup mstatus _ b eq_refl). exact LmIE. }
  (* the fetch (§3), at the post-write state: only the MEMORY matters *)
  assert (Hfetch : exec_eff (fetch tt)
            (set_reg sconf (R_bool minstret_increment) b)
            = Some (F_Base w, set_reg sconf (R_bool minstret_increment) b,
                    [WEread wak_plain pc 2; WEread wak_plain (add_vec_int pc 2) 2])).
  { apply (exec_eff_fetch_flat_base2 _ pc w).
    - rewrite (set_mi_lookup pmpcfg_n _ b eq_refl). exact Lpmp.
    - rewrite (set_mi_lookup pma_regions _ b eq_refl). exact Lpma.
    - rewrite (set_mi_lookup misa _ b eq_refl). exact LmisaC.
    - exact Lpc_a.
    - exact Lpriv_a.
    - rewrite (set_mi_lookup htif_tohost_base _ b eq_refl). exact Lhtif.
    - exact Hal4.
    - split; [exact Hal2|]. split; [exact Hram|].
      exists w. split; [split; [reflexivity|exact HnotRVC]|].
      intros j Hj. rewrite mem_set_reg. exact (Htext j Hj). }
  (* the decode, through [WeakFetchEff] §6's bridge *)
  assert (Hdec_a : exec_eff (ext_decode w)
            (set_reg sconf (R_bool minstret_increment) b)
            = Some (i, set_reg sconf (R_bool minstret_increment) b, [])).
  { refine (exec_eff_decode_bridge D (ext_decode w) dst _ i _ Hgood Hdec).
    intros r HDr.
    assert (Hne : register_beq r (R_bool minstret_increment) = false).
    { destruct (register_beq r (R_bool minstret_increment)) eqn:Hb;
        [|reflexivity].
      exfalso. rewrite (register_beq_eq _ _ Hb) in HDr.
      by rewrite HDmi in HDr. }
    rewrite (set_mi_lookup r _ b Hne). exact (Hagree r HDr). }
  (* the whole step, from the fetch's 2-element trace and the [execute]'s *)
  pose proof (exec_eff_riscv_step_base sconf s_exec w i pc b
                [WEread wak_plain pc 2; WEread wak_plain (add_vec_int pc 2) 2]
                es_x Hsi Lhart_a Lpriv_a Hdisp
                Hfetch Hdec_a Lelp_a Hnlpad Lpc_a Hex Hhe Hmie) as Hstep.
  (* ... at BOTH ticks, with the SAME trace ([WeakFetchEff] §7) *)
  destruct (exec_eff_riscv_step_all_ticks sconf _ _ Hstep tick)
    as (t' & Ht' & Hmt').
  exists t'. split; [exact Ht'|].
  rewrite Hmt'. destruct b; cbn [mem set_reg]; exact Hdom.
Qed.

Lemma wP_eff_of_leaf_rvc2
    (cid : nat) (σ : wmstate) (W : _)
    (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
    (w : SailStdpp.Values.mword 32)
    (i0 i : instruction) (es_x : list weff)
    (D D0 : register -> bool) (dst : mstate) :
  wlog_wf (wm_log σ) ->
  (forall a, a ∈ W -> pa_z a <> 0) ->
  (forall a, a ∈ W -> pinned_read σ (pa_z a)) ->
  register_lookup PC (wm_regs σ) = pc ->
  register_lookup cur_privilege (wm_regs σ) = Machine ->
  pmp_allows_all (register_lookup pmpcfg_n (wm_regs σ)) ->
  pma_allows_all (register_lookup pma_regions (wm_regs σ)) ->
  register_lookup htif_tohost_base (wm_regs σ) = None ->
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
  eq_vec (_get_Misa_S (register_lookup misa (wm_regs σ))) ('b"1") = true ->
  eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ))) ('b"1") = true ->
  eq_vec (_get_Mstatus_MIE (register_lookup mstatus (wm_regs σ))) ('b"1")
    = false ->
  eq_vec (register_lookup elp (wm_regs σ))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  (* (a) the text word, IN THE CONFINED MEMORY, at a 2-not-4-aligned pc *)
  is_aligned_vaddr (Virtaddr pc) 2 = true ->
  is_aligned_vaddr (Virtaddr pc) 4 = false ->
  (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)) ->
  (forall j : nat, (j < 4)%nat ->
     wmem_restrict σ W !! pa_add pc j = Some (nth_byte w j)) ->
  subrange_vec_dec w 15 0 = h ->
  isRVC h = true ->
  (* (b) the COMPRESSED decode, and the expansion *)
  (forall r, D r = true ->
     register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
  D (R_bool minstret_increment) = false ->
  goodb0 D (ext_decode_compressed h) dst = true ->
  exec (ext_decode_compressed h) dst = Some (i0, dst) ->
  (forall s : mstate, goodb0 D0 (execute i0) s = true) ->
  (forall s : mstate, exec (execute i0) s = Some (ExecuteAs i, s)) ->
  (* (c) the EXPANDED instruction's [execute], at [exec_eff] *)
  (forall b : bool, exists s_exec : mstate,
     exec_eff (execute i)
       (set_reg (set_reg (MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ))
                   (R_bool minstret_increment) b)
                nextPC (add_vec_int pc 2))
       = Some (RETIRE_SUCCESS, s_exec, es_x)
     /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
     /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b
     /\ dom (mem s_exec) ⊆ W) ->
  wP_eff (Some cid) ([WEread wak_plain pc 2] ++ es_x) σ.
Proof.
  intros Hwf HW0 HWp Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmisaC LmIE Lelp
         Hal2 Hal4 Hram Htext Hsub HisRVC Hagree HDmi Hgood Hdec Hgood0 Hexp
         Hexec.
  set (sconf := MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ)).
  apply (wP_eff_of_window cid _ σ W Hwf HW0 HWp).
  intros tick.
  destruct (exec_eff_should_inc_minstret_Some
              (register_lookup cur_privilege (sregs sconf)) sconf) as [b Hsi].
  destruct (Hexec b) as (s_exec & Hex & Hhe & Hmie & Hdom).
  assert (Lpriv_a : register_lookup cur_privilege
            (sregs (set_reg sconf (R_bool minstret_increment) b)) = Machine)
    by (rewrite (set_mi_lookup cur_privilege _ b eq_refl); exact Lpriv).
  assert (Lpc_a : register_lookup PC
            (sregs (set_reg sconf (R_bool minstret_increment) b)) = pc)
    by (rewrite (set_mi_lookup PC _ b eq_refl); exact Lpc).
  assert (Lhart_a : register_lookup hart_state
            (sregs (set_reg sconf (R_bool minstret_increment) b))
            = HART_ACTIVE tt)
    by (rewrite (set_mi_lookup hart_state _ b eq_refl); exact Lhart).
  assert (Lelp_a : eq_vec (register_lookup elp
            (sregs (set_reg sconf (R_bool minstret_increment) b)))
            (landing_pad_bits_backwards LP_EXPECTED) = false)
    by (rewrite (set_mi_lookup elp _ b eq_refl); exact Lelp).
  assert (Hdisp : exec_eff (dispatchInterrupt Machine)
            (set_reg sconf (R_bool minstret_increment) b)
            = Some (None, set_reg sconf (R_bool minstret_increment) b, [])).
  { apply exec_eff_dispatchInterrupt_machine_none.
    - rewrite (set_mi_lookup misa _ b eq_refl). exact LmisaS.
    - rewrite (set_mi_lookup mstatus _ b eq_refl). exact LmIE. }
  assert (Hzca : exec_eff (currentlyEnabled Ext_Zca)
            (set_reg sconf (R_bool minstret_increment) b)
            = Some (true, set_reg sconf (R_bool minstret_increment) b, [])).
  { apply exec_eff_currentlyEnabled_Zca.
    rewrite (set_mi_lookup misa _ b eq_refl). exact LmisaC. }
  assert (Hfetch : exec_eff (fetch tt)
            (set_reg sconf (R_bool minstret_increment) b)
            = Some (F_RVC h, set_reg sconf (R_bool minstret_increment) b,
                    [WEread wak_plain pc 2])).
  { apply (exec_eff_fetch_flat_rvc2 _ pc h).
    - rewrite (set_mi_lookup pmpcfg_n _ b eq_refl). exact Lpmp.
    - rewrite (set_mi_lookup pma_regions _ b eq_refl). exact Lpma.
    - rewrite (set_mi_lookup misa _ b eq_refl). exact LmisaC.
    - exact Lpc_a.
    - exact Lpriv_a.
    - rewrite (set_mi_lookup htif_tohost_base _ b eq_refl). exact Lhtif.
    - exact Hal4.
    - split; [exact Hal2|]. split; [exact Hram|].
      exists w. split; [split; [exact Hsub|exact HisRVC]|].
      intros j Hj. rewrite mem_set_reg. exact (Htext j Hj). }
  assert (Hne : forall r, D r = true ->
            register_beq r (R_bool minstret_increment) = false).
  { intros r HDr.
    destruct (register_beq r (R_bool minstret_increment)) eqn:Hb; [|reflexivity].
    exfalso. rewrite (register_beq_eq _ _ Hb) in HDr. by rewrite HDmi in HDr. }
  assert (Hdec_a : exec_eff (ext_decode_compressed h)
            (set_reg sconf (R_bool minstret_increment) b)
            = Some (i0, set_reg sconf (R_bool minstret_increment) b, [])).
  { refine (exec_eff_decode_bridge D (ext_decode_compressed h) dst _ i0 _
              Hgood Hdec).
    intros r HDr. rewrite (set_mi_lookup r _ b (Hne r HDr)).
    exact (Hagree r HDr). }
  (* the expansion, through the SAME bridge at the state itself *)
  assert (Hexp_a : exec_eff (execute i0)
            (set_reg (set_reg sconf (R_bool minstret_increment) b) nextPC
                     (add_vec_int pc 2))
            = Some (ExecuteAs i,
                    set_reg (set_reg sconf (R_bool minstret_increment) b) nextPC
                            (add_vec_int pc 2), [])).
  { apply (exec_eff_of_goodb0_self D0); [apply Hgood0 | apply Hexp]. }
  pose proof (exec_eff_riscv_step_rvc sconf s_exec h i0 i pc b
                [WEread wak_plain pc 2] es_x Hsi Lhart_a Lpriv_a Hdisp
                Hfetch Hdec_a Lelp_a Lpc_a Hzca Hexp_a Hex Hhe Hmie) as Hstep.
  destruct (exec_eff_riscv_step_all_ticks sconf _ _ Hstep tick)
    as (t' & Ht' & Hmt').
  exists t'. split; [exact Ht'|].
  rewrite Hmt'. destruct b; cbn [mem set_reg]; exact Hdom.
Qed.

(* ====================================================================== *)
(** ** 5. THE CERTIFICATES AT THE 2-ALIGNED FETCH PREFIXES, and the join

    The split [F_Base] fetch contributes TWO trace elements, so its
    certificates are [WeakEff]'s [_gen] family at the 2-element write-free
    prefix (the "3-element family" the batch-0b block priced): the prefix's
    [nowrite_trace] is immediate, and at [post := []] the [_gen] conclusion
    IS [prefix ++ es_x] on the nose ([e :: [] ] is [[e]]).  The [F_RVC]-at-2
    fetch is ONE element, so [WeakCert]'s own certificates apply at
    [nf := 2] verbatim — stated here as the [_rvc2] instances.  In both
    cases the recipe's conclusion (§4) and the certificate's [P] are the
    SAME term: no adapter, no [app] lemma, no peeling. *)

Lemma nowrite_nil : nowrite_trace [].
Proof. constructor. Qed.

Lemma nowrite_fetch2 (pc : SailStdpp.Values.mword 64) :
  nowrite_trace [WEread wak_plain pc 2; WEread wak_plain (add_vec_int pc 2) 2].
Proof. repeat constructor. Qed.

(** *** 5a. The three certificates over the TWO-element fetch prefix. *)

Lemma wcert_load_base2 (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akl : akinfo) (ea : Arch.pa) :
  ak_coh akl = false ->
  wstep_cert cid pc
    (wP_eff (Some cid)
       ([WEread wak_plain pc 2; WEread wak_plain (add_vec_int pc 2) 2]
          ++ [WEread akl ea 4]))
    (wQ_load ea).
Proof.
  intros Hcoh.
  exact (wcert_load_gen cid pc _ [] akl ea Hcoh (nowrite_fetch2 pc) nowrite_nil).
Qed.

Lemma wcert_store_base2 (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akw : akinfo) (ea : Arch.pa) (v : bv 32) :
  wstep_cert cid pc
    (wP_eff (Some cid)
       ([WEread wak_plain pc 2; WEread wak_plain (add_vec_int pc 2) 2]
          ++ [WEwrite akw ea 4 v]))
    (wQ_store (Some cid) ea v).
Proof.
  exact (wcert_store_gen cid pc _ [] akw ea v (nowrite_fetch2 pc) nowrite_nil).
Qed.

Lemma wcert_amo_aq_base2 (cid : nat) (pc : SailStdpp.Values.mword 64)
    (aka akw : akinfo) (ea : Arch.pa) (v : bv 32) :
  ak_coh aka = false -> ak_sync aka = true ->
  wstep_cert cid pc
    (wP_eff (Some cid)
       ([WEread wak_plain pc 2; WEread wak_plain (add_vec_int pc 2) 2]
          ++ [WEread aka ea 4; WEwrite akw ea 4 v]))
    (wQ_amo_aq (Some cid) ea v).
Proof.
  intros Hcoh Hsync.
  exact (wcert_amo_aq_gen cid pc _ [] aka akw ea v Hcoh Hsync
           (nowrite_fetch2 pc) nowrite_nil).
Qed.

Lemma wcert_fence_base2 (cid : nat) (pc : SailStdpp.Values.mword 64)
    (b : barrier_kind) :
  wstep_cert cid pc
    (wP_eff (Some cid)
       ([WEread wak_plain pc 2; WEread wak_plain (add_vec_int pc 2) 2]
          ++ [WEbar b]))
    (wQ_fence b).
Proof.
  exact (wcert_fence_gen cid pc _ [] b (nowrite_fetch2 pc) nowrite_nil).
Qed.

(** *** 5b. The [F_RVC]-at-2 instances: [WeakCert]'s certificates at the
    ONE-element width-2 fetch prefix ([nf := 2]).  These are the exact twins
    of [WeakFetchEff] §9a. *)

Lemma wcert_load_rvc2 (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akl : akinfo) (ea : Arch.pa) :
  ak_coh akl = false ->
  wstep_cert cid pc
    (wP_eff (Some cid) ([WEread wak_plain pc 2] ++ [WEread akl ea 4]))
    (wQ_load ea).
Proof. intros Hcoh. exact (wcert_load cid pc wak_plain pc 2 akl ea Hcoh). Qed.

Lemma wcert_store_rvc2 (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akw : akinfo) (ea : Arch.pa) (v : bv 32) :
  wstep_cert cid pc
    (wP_eff (Some cid) ([WEread wak_plain pc 2] ++ [WEwrite akw ea 4 v]))
    (wQ_store (Some cid) ea v).
Proof. exact (wcert_store cid pc wak_plain pc 2 akw ea v). Qed.

Lemma wcert_amo_aq_rvc2 (cid : nat) (pc : SailStdpp.Values.mword 64)
    (aka akw : akinfo) (ea : Arch.pa) (v : bv 32) :
  ak_coh aka = false -> ak_sync aka = true ->
  wstep_cert cid pc
    (wP_eff (Some cid)
       ([WEread wak_plain pc 2] ++ [WEread aka ea 4; WEwrite akw ea 4 v]))
    (wQ_amo_aq (Some cid) ea v).
Proof.
  intros Hcoh Hsync.
  exact (wcert_amo_aq cid pc wak_plain pc 2 aka akw ea v Hcoh Hsync).
Qed.

(** *** 5c. The end-to-end join check, for the genuinely NEW shape — the
    3-element trace of a load under a split fetch.  The whole body is one
    [exact] of §4's recipe at [es_x := [WEread akl ea 4]]: its conclusion is
    [wcert_load_base2]'s [P] on the nose, because [[a; b] ++ [c]] IS
    [[a; b; c]].  No adapter, no peeling — the batch-0b claim, at the
    2-aligned arm. *)
Lemma wP_load_of_leaf_base2
    (cid : nat) (σ : wmstate) (W : _)
    (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
    (i : instruction) (akl : akinfo) (ea : Arch.pa)
    (D : register -> bool) (dst : mstate) :
  wlog_wf (wm_log σ) ->
  (forall a, a ∈ W -> pa_z a <> 0) ->
  (forall a, a ∈ W -> pinned_read σ (pa_z a)) ->
  register_lookup PC (wm_regs σ) = pc ->
  register_lookup cur_privilege (wm_regs σ) = Machine ->
  pmp_allows_all (register_lookup pmpcfg_n (wm_regs σ)) ->
  pma_allows_all (register_lookup pma_regions (wm_regs σ)) ->
  register_lookup htif_tohost_base (wm_regs σ) = None ->
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
  eq_vec (_get_Misa_S (register_lookup misa (wm_regs σ))) ('b"1") = true ->
  eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ))) ('b"1") = true ->
  eq_vec (_get_Mstatus_MIE (register_lookup mstatus (wm_regs σ))) ('b"1")
    = false ->
  eq_vec (register_lookup elp (wm_regs σ))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  is_aligned_vaddr (Virtaddr pc) 2 = true ->
  is_aligned_vaddr (Virtaddr pc) 4 = false ->
  (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)) ->
  (forall j : nat, (j < 4)%nat ->
     wmem_restrict σ W !! pa_add pc j = Some (nth_byte w j)) ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  (forall r, D r = true ->
     register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
  D (R_bool minstret_increment) = false ->
  goodb0 D (ext_decode w) dst = true ->
  exec (ext_decode w) dst = Some (i, dst) ->
  is_lpad_instruction i = false ->
  (forall b : bool, exists s_exec : mstate,
     exec_eff (execute i)
       (set_reg (set_reg (MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ))
                   (R_bool minstret_increment) b)
                nextPC (add_vec_int pc 4))
       = Some (RETIRE_SUCCESS, s_exec, [WEread akl ea 4])
     /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
     /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b
     /\ dom (mem s_exec) ⊆ W) ->
  wP_eff (Some cid)
    ([WEread wak_plain pc 2; WEread wak_plain (add_vec_int pc 2) 2]
       ++ [WEread akl ea 4]) σ.
Proof. exact (wP_eff_of_leaf_base2 cid σ W pc w i _ D dst). Qed.

(* ====================================================================== *)
(** ** 6. Soundness check *)

Print Assumptions exec_eff_fetch_F_Base_2.
Print Assumptions exec_eff_fetch_RVC_2.
Print Assumptions exec_eff_fetch_flat_base2.
Print Assumptions exec_eff_fetch_flat_rvc2.
Print Assumptions wP_eff_of_leaf_base2.
Print Assumptions wP_eff_of_leaf_rvc2.
Print Assumptions wcert_load_base2.
Print Assumptions wP_load_of_leaf_base2.
