/-
Weak: **the RACY absorption theorem** -- the TLB-miss walk certified at the stale mirror
(walk-bridge §8.3 item 5), and the PEEL of the translation it feeds.

Rocq: `iris/WeakKptStale.v` @ xxvzwolszwmp (one file: ~1260 lines, elaborates in seconds).

The Rocq header, in substance.  `wtlbResPtTranslateAddrAt`'s twin over
`execStaleTranslateAddrPtMissCases`: the same invariant opening, the same collapse conjuncts,
but the translation stated at `execStale la 8 pv` -- the mirror in which the walk's PLAIN leaf
read returns the racy variant `pv` while the CAS's exclusive re-read returns the
coherence-latest word -- for EVERY admissible variant at once (the peel producer's family), plus
the SIXTH outcome disjunct (gate fires on the racy word, the fresh one needs nothing: four
reads, NO write).  THREE deltas against the `execEff` original:
  - the headline fact becomes a FAMILY -- `∀ av dv` with `pteAdLe (pteSetAD w0 av dv) lw`, a run
    of the translation at `execStale la 8 (pteSetAD w0 av dv)`.  The ghost arm (log unchanged vs
    appended) is family-UNIFORM: the write-back event is decided by the LATEST word alone
    (`updatePTEBitsFiresMono`), which lets one fupd commit one ghost outcome for the family;
  - the read-only arm's trace enumeration grows by ONE disjunct -- `walk ++ CAS-read`;
  - the registers come back as a WAND keyed on the actual family member: `execStale` is a
    function, so the caller's equation for the member that ran pins `sg'` against the stored
    family analysis, and the wand advances `regInterp` to `sg'.regs` and re-establishes the
    residue (`AxPtProt.tlbOkPtFill` holds for an entry carrying ANY A/D variant of the leaf).
Every fact a fetch-walking consumer owes about the translation is owed at the
post-`minstret_increment`-write state `s.setReg .minstret_increment bf`, for all `bf` (the
model's `try_step` writes that flag before it fetches; Rocq's `set_mi` notation, inlined here).
The write-back message class is PINNED at `.WCexcl` (the walk's write-back is `ak_latest`).

§1 slot geometry: a pointer slot and a leaf slot are disjoint; §2 the pure dispatch at the stale
mirror `wptreeTranslateAddrStaleCases`; §2bis `wtlbRegsPreserved` (every register but `tlb`
survives the translation); §3 THE RACY ABSORPTION THEOREM `wtlbResPtTranslateAddrStaleAt`;
§4 the peel `wwalkPeelOfExports` (pure, from §3's exports: five trace shapes through the stale
producer `wstepOkRacyTrueOfStaleWindow`, the TLB-hit write-back `[excl-read, write]` back
through `execEffOfExecStale` and the confined producer `wstepEffConfinedPin`).

**Deviations from Rocq.**
1. VOCABULARY as `Weak/WeakKpt.lean` deviation 1 and `Weak/WeakWalkStale.lean` deviation 1
   (`set_mi s b` ↦ `s.setReg .minstret_increment b`, inlined; `register_lookup r (sregs s)` ↦
   `s.regs r`; `register_set tlb v (sregs s)` ↦ `s.regs.set .tlb v`; `register_set
   (R_bool minstret_increment) bf (wm_regs σ)` ↦ `σ.wmRegs.set .minstret_increment bf`;
   `mem`/`mdev`/`sregs` ↦ `.mem`/`.dev`/`.regs`; `write_bytes m a 8 v` ↦ `bmWrite m a 8 v`;
   `register_beq r tlb = false` ↦ `r ≠ .tlb`; `AkInfo false true false` ↦ `⟨false, true, false⟩`
   (= `wakExcl`); `pa_add a j` ↦ `a + BitVec.ofNat 64 j`; stdpp `Forall P es` ↦
   `∀ e, e ∈ es → P e`).  Statement-level `let`s are kept as Lean `let`s (§2, §4) or inlined
   (§3, as in `Weak/WeakKpt2.lean`).
2. `pt_slot_mem` ↦ `WeakWalkEff.ptSlotMem` (`BytesAt ∧ inRam a 8 ∧ aligned`, WeakWalkEff
   deviation 6), so `pt_slot_mem_acc_wf` goes through `wslotGeomAccWf`.
3. §3 follows `Weak/WeakKpt2.lean` (WeakKpt deviations 2–5): contexts `[MachGS hlc GF]
   [WeakGS GF] [WeakKpt.KptGS GF]` and an explicit `cpu`; `kmap_at (svpn_of va) ppn pc` ↦
   `kmapAt (WeakKpt.svpnOf va) (kLeaf ppn pc 0#1 0#1)`; `mk_pte ppn (kperm_flags pc)` ↦
   `mkPte ppn pc.flags`; `P -∗ … ={E}=∗ R` ↦ `P ∗ … ⊢ |={E}=> R`; the wand's `==∗` ↦ `-∗ |==>`;
   `pma_allows_all` ↦ `σ.wmRegs .pma_regions = bootPMA`; the write-back value `lw'` is
   `pteSetAD e a1 d1` (`e` the canonical leaf; = Rocq's `pte_set_ad lw a1 d1`).
4. O2 (WeakKpt deviation 2): the collapse conjunct of §3 and the collapse premise of §4 are for
   `rak.akIfetch = false` reads (the peel uses it at `wakPlain`).
5. O2: `wwalkEvOk`'s read arm also demands `ak.akIfetch = false`: Lean's `tracePinOff` asks
   `readPinned` (the FETCH pin for an i-cache read) and `fetchFresh` (`WeakStale` deviation 3).
   Every walk event (`wakPlain`, `wakExcl`) satisfies it, so no consumer-facing statement moves.
6. `wwalk_win_conf`'s `pa_add b j ∈ dom (wmem_restrict …)` ↦ `(wmemRestrict … _).isSome = true`
   (`WeakStale` deviation 1).  Rocq's `walk_evs` Ltac ↦ the Lean-only macro `wwalk_evs`;
   `pinned_trace` ↦ `WeakWalkStale`'s `walk_stale_trace`; `Print Assumptions` are not
   declarations.
7. Lean-only helpers (file-qualified): `WeakKptStale.readPteAt`, `WeakKptStale.readPteExclAt`,
   `WeakKptStale.writePteAt` (the three slot bricks at a state whose registers agree with `sg`
   off `minstret_increment` -- Rocq transports each premise by `irrelevant_register_set`
   inline); `WeakKptStale.fetchFreshNoIfetch` (deviation 5).

**Rocq → Lean name map.**  `pt_slot_mem_acc_wf` `ptSlotMemAccWf`; `pt_slot_mem_det`
`ptSlotMemDet`; `pt_slot_racc_disj` `ptSlotRaccDisj`; `wptree_translateAddr_stale_cases`
`wptreeTranslateAddrStaleCases`; `wtlb_regs_preserved` `wtlbRegsPreserved`;
`wtlb_res_pt_translateAddr_stale_at` `wtlbResPtTranslateAddrStaleAt`; `wwalk_filter`
`wwalkFilter`; `wwalk_slots_in2/1/0` `wwalkSlotsIn2/1/0`; `wwalk_win_nonzero`
`wwalkWinNonzero`; `wwalk_win_conf` `wwalkWinConf`; `wwalk_ev_ok` `wwalkEvOk`;
`trace_rdom_of_evs` `traceRdomOfEvs`; `trace_wdom_of_evs` `traceWdomOfEvs`;
`trace_pin_off_of_evs` `tracePinOffOfEvs`; `trace_stale_walk_shapes` `traceStaleWalkShapes`;
`wstep_ok_racy_true_of_walk_family` `wstepOkRacyTrueOfWalkFamily`; `wwalk_peel_of_exports`
`wwalkPeelOfExports`.  (No name is in the duplicated-name table.)

**Dropped:** nothing -- 2 `Definition`s + 17 `Lemma`s (19 Rocq declarations), all ported
(19 Lean declarations, plus the 4 Lean-only helpers and the `wwalk_evs` macro).
-/
import Weak.WeakKpt2
import Weak.WeakWalkStale

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. Slot geometry: two slots holding a POINTER and a LEAF are disjoint -/

theorem ptSlotMemAccWf (sg : ExecSt) (a v : BitVec 64) :
    WeakWalkEff.ptSlotMem sg a v → accWf a 8 :=
  fun ⟨_, hram, hal⟩ => wslotGeomAccWf a ⟨hram, hal⟩

theorem ptSlotMemDet (sg : ExecSt) (a v v' : BitVec 64) :
    WeakWalkEff.ptSlotMem sg a v → WeakWalkEff.ptSlotMem sg a v' → v = v' := by
  rintro ⟨hb, -⟩ ⟨hb', -⟩
  apply bvEqOfBytes (n := 8)
  intro j hj
  have h1 := hb j hj
  have h2 := hb' j hj
  rw [h1] at h2
  exact Option.some.inj h2

theorem ptSlotRaccDisj (sg : ExecSt) (la a lv v : BitVec 64) :
    WeakWalkEff.ptSlotMem sg la lv → WeakWalkEff.ptSlotMem sg a v →
    pteLeaf lv → ptePtr v →
    raccDisj la 8 a 8 := by
  intro hla ha hleaf hptr
  have hall : la.toNat % 8 = 0 := isAlignedVaddrMod la 8 (by decide) hla.2.2
  have hala : a.toNat % 8 = 0 := isAlignedVaddrMod a 8 (by decide) ha.2.2
  by_cases heq : la = a
  · subst heq
    have hv := ptSlotMemDet sg la lv v hla ha
    subst hv
    unfold pteLeaf at hleaf
    unfold ptePtr at hptr
    rw [hleaf] at hptr
    cases hptr
  · have hne : la.toNat ≠ a.toNat := fun h => heq (BitVec.eq_of_toNat_eq h)
    unfold raccDisj paZ
    omega

/-! ## 2. The pure dispatch at the stale mirror -/

/-- Lean-only: `wptReadPteSlot` at a state whose registers agree with `sg` off the flag. -/
theorem WeakKptStale.readPteAt (sg s : ExecSt) (a w : BitVec 64)
    (hregs : ∀ r, r ≠ .minstret_increment → s.regs r = sg.regs r)
    (hslot : WeakWalkEff.ptSlotMem s a w)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (sg.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (sg.regs .pmpaddr_n)[0]! = false)
    (hR : (_get_Pmpcfg_ent_R (sg.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hcov : ramEnd ≤ (sg.regs .pmpaddr_n)[0]!.toNat * 4)
    (hpmar : WeakKpt.pmaAllowsPteRead (sg.regs .pma_regions))
    (hhtif : sg.regs .htif_tohost_base = none) :
    execEff (read_pte (.Physaddr a) 8) s = some (.Ok w, s, [.WEread wakPlain a 8]) := by
  obtain ⟨region, hm, hs⟩ := hpmar a hslot.2.1
  exact wptReadPteSlot s a w region hslot (by rw [hregs _ (by decide)]; exact hA)
    (by rw [hregs _ (by decide)]; exact hlt) (by rw [hregs _ (by decide)]; exact hR)
    (by rw [hregs _ (by decide)]; exact hcov) (by rw [hregs _ (by decide)]; exact hm) hs
    (by rw [hregs _ (by decide)]; exact hhtif)

/-- Lean-only: `wptReadPteExclusiveSlot` likewise. -/
theorem WeakKptStale.readPteExclAt (sg s : ExecSt) (a w : BitVec 64)
    (hregs : ∀ r, r ≠ .minstret_increment → s.regs r = sg.regs r)
    (hslot : WeakWalkEff.ptSlotMem s a w)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (sg.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (sg.regs .pmpaddr_n)[0]! = false)
    (hR : (_get_Pmpcfg_ent_R (sg.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hcov : ramEnd ≤ (sg.regs .pmpaddr_n)[0]!.toNat * 4)
    (hpmar : WeakKpt.pmaAllowsPteRead (sg.regs .pma_regions))
    (hhtif : sg.regs .htif_tohost_base = none) :
    execEff (read_pte_exclusive (.Physaddr a) 8) s =
      some (.Ok w, s, [.WEread ⟨false, true, false⟩ a 8]) := by
  obtain ⟨region, hm, hs⟩ := hpmar a hslot.2.1
  exact wptReadPteExclusiveSlot s a w region hslot (by rw [hregs _ (by decide)]; exact hA)
    (by rw [hregs _ (by decide)]; exact hlt) (by rw [hregs _ (by decide)]; exact hR)
    (by rw [hregs _ (by decide)]; exact hcov) (by rw [hregs _ (by decide)]; exact hm) hs
    (by rw [hregs _ (by decide)]; exact hhtif)

/-- Lean-only: `execEffWritePteConditionalRam` likewise. -/
theorem WeakKptStale.writePteAt (sg s : ExecSt) (a w w' : BitVec 64)
    (hregs : ∀ r, r ≠ .minstret_increment → s.regs r = sg.regs r)
    (hslot : WeakWalkEff.ptSlotMem s a w)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (sg.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (sg.regs .pmpaddr_n)[0]! = false)
    (hW : (_get_Pmpcfg_ent_W (sg.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hcov : ramEnd ≤ (sg.regs .pmpaddr_n)[0]!.toNat * 4)
    (hpmaw : WeakKpt.pmaAllowsPteWrite (sg.regs .pma_regions))
    (hhtif : sg.regs .htif_tohost_base = none) :
    execEff (write_pte_conditional (.Physaddr a) 8 w') s =
      some (.Ok true, s.setMem (bmWrite s.mem a 8 w'), [.WEwrite ⟨false, true, false⟩ a 8 w']) := by
  obtain ⟨region, hm, hw⟩ := hpmaw a hslot.2.1
  exact execEffWritePteConditionalRam a w' region s hslot.2.1 hslot.2.2
    (by rw [hregs _ (by decide)]; exact hA) (by rw [hregs _ (by decide)]; exact hlt)
    (by rw [hregs _ (by decide)]; exact hW) (by rw [hregs _ (by decide)]; exact hcov)
    (by rw [hregs _ (by decide)]; exact hm) hw (by rw [hregs _ (by decide)]; exact hhtif)

/-- Rocq `wptree_translateAddr_stale_cases`: `wptreeTranslateAddrEffCases`' twin at the stale
mirror -- the per-variant FAMILY, split by whether a write-back happens (family-uniform), at
the flag-modified states. -/
theorem wptreeTranslateAddrStaleCases (acc : MemoryAccessType mem_payload) (p : Privilege)
    (root : BitVec 44) (va w pa satp0 : BitVec 64) (t : PTree)
    (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) (p2 p1 : BitVec 64) (a0 d0 : BitVec 1) (sg : ExecSt) :
    let vpn := WeakKpt.svpnOf va
    let p0 := pteSetAD w a0 d0
    let a2w := uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)
    let a1w := uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    (∀ (a d : BitVec 1) (mxr dosum : Bool), wpteCheckOk acc p mxr dosum (pteSetAD w a d)) →
    (∀ a d : BitVec 1, wpteValid (pteSetAD w a d)) →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    zero_extend (m := 64) (ppn0 w +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa →
    (∀ a d : BitVec 1, ptePbmt0 (pteSetAD w a d)) →
    wpteValid p2 → wpteValid p1 →
    t.base = root →
    AxPtProt.ptreeMaps t vpn p2 p1 p0 →
    AxPtProt.tlbOkPt 0#16 t tlbvec →
    WeakWalkEff.ptSlotMem sg (AxPtProt.ptAddr2 t vpn) p2 →
    WeakWalkEff.ptSlotMem sg (AxPtProt.ptAddr1 p2 vpn) p1 →
    WeakWalkEff.ptSlotMem sg (AxPtProt.ptAddr0 p1 vpn) p0 →
    sg.regs .misa = misaC →
    sg.regs .menvcfg = menvcfgS →
    sg.regs .htif_tohost_base = none →
    sg.regs .cur_privilege = p →
    (∀ bf : Bool, execEff (translationMode p) (sg.setReg .minstret_increment bf) =
      some (.Sv39, sg.setReg .minstret_increment bf, [])) →
    (∀ bf : Bool, execEff (effectivePrivilege acc (sg.regs .mstatus) p) (sg.setReg .minstret_increment bf) =
      some (p, sg.setReg .minstret_increment bf, [])) →
    (∀ bf : Bool, execEff (is_shadow_stack_access acc) (sg.setReg .minstret_increment bf) =
      some (false, sg.setReg .minstret_increment bf, [])) →
    sg.regs .satp = satp0 →
    BitVec.setWidth 44 (satp_to_ppn satp0) = root →
    zero_extend (m := 16) (satp_to_asid satp0) = 0#16 →
    sg.regs .tlb = tlbvec →
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (sg.regs .pmpcfg_n)[0]!) = .TOR →
    zopz0zKzJ_u (zeros (n := 64)) (sg.regs .pmpaddr_n)[0]! = false →
    (_get_Pmpcfg_ent_R (sg.regs .pmpcfg_n)[0]! == 1#1) = true →
    (_get_Pmpcfg_ent_W (sg.regs .pmpcfg_n)[0]! == 1#1) = true →
    ramEnd ≤ (sg.regs .pmpaddr_n)[0]!.toNat * 4 →
    WeakKpt.pmaAllowsPteRead (sg.regs .pma_regions) →
    WeakKpt.pmaAllowsPteWrite (sg.regs .pma_regions) →
    raccDisj la 8 a2w 8 ∧ raccDisj la 8 a1w 8 ∧
    ( -- READ-ONLY: no family member writes
      (∀ av dv : BitVec 1, pteAdLe (pteSetAD w av dv) p0 → ∀ bf : Bool,
        ∃ (sg' : ExecSt) (es : List Weff),
          execStale la 8 (pteSetAD w av dv) (translateAddr (.Virtaddr va) acc)
              (sg.setReg .minstret_increment bf) =
            some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', es) ∧
          sg'.mem = sg.mem ∧ sg'.dev = sg.dev ∧
          (sg'.regs = (sg.setReg .minstret_increment bf).regs ∨
            ∃ ae de : BitVec 1, sg'.regs = (sg.setReg .minstret_increment bf).regs.set .tlb
              (vectorUpdate tlbvec (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 (pteSetAD w ae de) 0#16)))) ∧
          (es = [] ∨
           es = [.WEread wakPlain a2w 8, .WEread wakPlain a1w 8, .WEread wakPlain la 8] ∨
           es = [.WEread ⟨false, true, false⟩ la 8] ∨
           es = [.WEread wakPlain a2w 8, .WEread wakPlain a1w 8, .WEread wakPlain la 8,
                 .WEread ⟨false, true, false⟩ la 8])) ∨
      -- WRITE-BACK: every member writes the SAME word, with the SAME trace shape
      (∃ (a1 d1 : BitVec 1) (wtr : Bool),
        update_PTE_Bits p0 acc = some (pteSetAD p0 a1 d1) ∧
        ∀ av dv : BitVec 1, pteAdLe (pteSetAD w av dv) p0 → ∀ bf : Bool,
          ∃ (sg' : ExecSt) (es : List Weff),
            execStale la 8 (pteSetAD w av dv) (translateAddr (.Virtaddr va) acc)
                (sg.setReg .minstret_increment bf) =
              some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', es) ∧
            sg'.mem = bmWrite sg.mem la 8 (pteSetAD p0 a1 d1) ∧
            sg'.dev = sg.dev ∧
            (∃ ae de : BitVec 1, sg'.regs = (sg.setReg .minstret_increment bf).regs.set .tlb
              (vectorUpdate tlbvec (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 (pteSetAD w ae de) 0#16)))) ∧
            es = (if wtr then
                    [.WEread wakPlain a2w 8, .WEread wakPlain a1w 8, .WEread wakPlain la 8,
                     .WEread ⟨false, true, false⟩ la 8,
                     .WEwrite ⟨false, true, false⟩ la 8 (pteSetAD p0 a1 d1)]
                  else
                    [.WEread ⟨false, true, false⟩ la 8,
                     .WEwrite ⟨false, true, false⟩ la 8 (pteSetAD p0 a1 d1)]))) := by
  intro vpn p0 a2w a1w la hchk hval hcanon hout hvarp hwv2 hwv1 hbase hmaps htlbok hsm2 hsm1 hsm0 hmisa
    hmenv hhtif hcp htm heff hss hsatp hppn hasid htlbv hA hord hR hW hcov hpmar hpmaw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hn2, -, hn1, -, hl0, hnap, -⟩ := id hmaps
  have ha2 : AxPtProt.ptAddr2 t vpn = a2w := by
    unfold AxPtProt.ptAddr2; rw [hbase]; rfl
  have hsm2' : WeakWalkEff.ptSlotMem sg a2w p2 := ha2 ▸ hsm2
  have hsm1' : WeakWalkEff.ptSlotMem sg a1w p1 := hsm1
  have hsm0' : WeakWalkEff.ptSlotMem sg la p0 := hsm0
  -- §1: the window's geometry and its disjointness from the pointer slots
  have hwf2 := ptSlotMemAccWf sg _ _ hsm2'
  have hwf1 := ptSlotMemAccWf sg _ _ hsm1'
  have hwf0 := ptSlotMemAccWf sg _ _ hsm0'
  have hd2 := ptSlotRaccDisj sg _ _ _ _ hsm0' hsm2' hl0 hn2
  have hd1 := ptSlotRaccDisj sg _ _ _ _ hsm0' hsm1' hl0 hn1
  refine ⟨hd2, hd1, ?_⟩
  -- every `sg`-level register fact, transported past the flag write
  have hreg : ∀ (bf : Bool) (r : Register), r ≠ .minstret_increment →
      (sg.setReg .minstret_increment bf).regs r = sg.regs r :=
    fun bf r h => WeakFetchEff.saLookup r sg bf h
  have hregp : ∀ (bf : Bool) (pv : BitVec 64) (r : Register), r ≠ .minstret_increment →
      (mpatch la 8 pv (sg.setReg .minstret_increment bf)).regs r = sg.regs r :=
    fun bf _ r h => WeakFetchEff.saLookup r sg bf h
  have hmisab : ∀ bf : Bool, (sg.setReg .minstret_increment bf).regs .misa = misaC :=
    fun bf => (hreg bf _ (by decide)).trans hmisa
  have hmenvb : ∀ bf : Bool, (sg.setReg .minstret_increment bf).regs .menvcfg = menvcfgS :=
    fun bf => (hreg bf _ (by decide)).trans hmenv
  have hcpb : ∀ bf : Bool, (sg.setReg .minstret_increment bf).regs .cur_privilege = p :=
    fun bf => (hreg bf _ (by decide)).trans hcp
  have hsatpb : ∀ bf : Bool, (sg.setReg .minstret_increment bf).regs .satp = satp0 :=
    fun bf => (hreg bf _ (by decide)).trans hsatp
  have htlbvb : ∀ bf : Bool, (sg.setReg .minstret_increment bf).regs .tlb = tlbvec :=
    fun bf => (hreg bf _ (by decide)).trans htlbv
  have heffb : ∀ bf : Bool, execEff (effectivePrivilege acc ((sg.setReg .minstret_increment bf).regs .mstatus) p)
      (sg.setReg .minstret_increment bf) = some (p, sg.setReg .minstret_increment bf, []) := by
    intro bf; rw [hreg bf .mstatus (by decide)]; exact heff bf
  -- the CAS's exclusive read and its write half, at the modified states
  have hrdxb : ∀ bf : Bool, execEff (read_pte_exclusive (.Physaddr la) 8) (sg.setReg .minstret_increment bf) =
      some (.Ok p0, sg.setReg .minstret_increment bf, [.WEread ⟨false, true, false⟩ la 8]) :=
    fun bf => WeakKptStale.readPteExclAt sg _ la p0 (hreg bf) hsm0' hA hord hR hcov hpmar hhtif
  have hwriteb : ∀ (bf : Bool) (q : BitVec 64),
      execEff (write_pte_conditional (.Physaddr la) 8 q) (sg.setReg .minstret_increment bf) =
        some (.Ok true, (sg.setReg .minstret_increment bf).setMem
          (bmWrite (sg.setReg .minstret_increment bf).mem la 8 q), [.WEwrite ⟨false, true, false⟩ la 8 q]) :=
    fun bf q => WeakKptStale.writePteAt sg _ la p0 q (hreg bf) hsm0' hA hord hW hcov hpmaw hhtif
  -- identity geometry
  have hid : zero_extend (m := 64) (ppn0 p0 +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa := by
    show zero_extend (m := 64) (PPN_of_PTE (pteSetAD w a0 d0) +++ _) = pa
    rw [ppn_of_pteSetAD]; exact hout
  have hpbmte : (_get_MEnvcfg_PBMTE menvcfgS == 0#1) = true := by decide
  have hadue : (_get_MEnvcfg_ADUE menvcfgS == 1#1) = true := by decide
  -- the TLB slot: a miss (for every flag value), or this vpn's own entry
  have hcase : (∀ bf : Bool, execEff (lookup_TLB 39 0#16 vpn) (sg.setReg .minstret_increment bf) =
        some (none, sg.setReg .minstret_increment bf, [])) ∨
      ∃ a' d' : BitVec 1, tlbvec[tlb_hash 39 vpn]! = some (uWalkEntry vpn p2 p1 (pteSetAD p0 a' d') 0#16) := by
    cases hslot : tlbvec[tlb_hash 39 vpn]! with
    | none => exact Or.inl fun bf => execEffLookupTLBMiss vpn 0#16 tlbvec _ (htlbvb bf) hslot
    | some ent =>
      obtain ⟨vpn0, q2, q1, qp0, a', d', hm0', -, hent⟩ := htlbok vpn ent hslot
      by_cases hne : vpn0 = vpn
      · rw [hne] at hm0' hent
        obtain ⟨h2, h1, h0⟩ := AxPtProt.ptreeMapsDet t vpn q2 q1 qp0 p2 p1 p0 hm0' hmaps
        rw [h2, h1, h0] at hent
        exact Or.inr ⟨a', d', by rw [hent]⟩
      · exact Or.inl fun bf => execEffLookupTLBNomatchS vpn 0#16 ent tlbvec _ (htlbvb bf) hslot
          (by rw [hent]; exact WeakWalkEff.uweMatchOther vpn0 vpn q2 q1 (pteSetAD qp0 a' d') 0#16 hne)
  rcases hcase with hlk | ⟨a', d', hslot⟩
  · -- ================= THE MISS PATH: the stale walk, per member =================
    have hfam : ∀ (bf : Bool) (av dv : BitVec 1), ∃ (sg' : ExecSt) (es : List Weff),
        execStale la 8 (pteSetAD w av dv) (translateAddr (.Virtaddr va) acc) (sg.setReg .minstret_increment bf) =
          some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', es) ∧
        sg'.dev = sg.dev ∧
        (∃ ae de : BitVec 1, sg'.regs = (sg.setReg .minstret_increment bf).regs.set .tlb
          (vectorUpdate tlbvec (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 (pteSetAD w ae de) 0#16)))) ∧
        ((sg'.mem = sg.mem ∧
          ((update_PTE_Bits (pteSetAD w av dv) acc = none ∧
            es = [.WEread wakPlain a2w 8, .WEread wakPlain a1w 8, .WEread wakPlain la 8]) ∨
           (update_PTE_Bits p0 acc = none ∧
            es = [.WEread wakPlain a2w 8, .WEread wakPlain a1w 8, .WEread wakPlain la 8,
                  .WEread ⟨false, true, false⟩ la 8]))) ∨
         (∃ q : BitVec 64, update_PTE_Bits p0 acc = some q ∧ sg'.mem = bmWrite sg.mem la 8 q ∧
           es = [.WEread wakPlain a2w 8, .WEread wakPlain a1w 8, .WEread wakPlain la 8,
                 .WEread ⟨false, true, false⟩ la 8, .WEwrite ⟨false, true, false⟩ la 8 q])) := by
      intro bf av dv
      have hleafv : pteLeaf (pteSetAD w av dv) :=
        (AxPtProt.pteSetAdLeaf w av dv).2 ((AxPtProt.pteSetAdLeaf w a0 d0).1 hl0)
      have hnapv : AxPtProt.pteNoNapot (pteSetAD w av dv) :=
        (AxPtProt.pteSetAdNoNapot w av dv).2 ((AxPtProt.pteSetAdNoNapot w a0 d0).1 hnap)
      have hidv : zero_extend (m := 64)
          (ppn0 (pteSetAD w av dv) +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa := by
        show zero_extend (m := 64) (PPN_of_PTE (pteSetAD w av dv) +++ _) = pa
        rw [ppn_of_pteSetAD]; exact hout
      have habs : p0 = pteSetAD (pteSetAD w av dv) a0 d0 := (pteSetAD_pteSetAD w av dv a0 d0).symm
      -- the three walk reads, at the PATCHED state
      have hsm2p := ptSlotMemMpatchDisj la 8 (pteSetAD w av dv) (sg.setReg .minstret_increment bf) a2w p2
        hwf0 hwf2 hd2 hsm2'
      have hsm1p := ptSlotMemMpatchDisj la 8 (pteSetAD w av dv) (sg.setReg .minstret_increment bf) a1w p1
        hwf0 hwf1 hd1 hsm1'
      have hsm0p := ptSlotMemMpatchWin la (pteSetAD w av dv) (sg.setReg .minstret_increment bf) p0 hwf0 hsm0'
      have hrd2p := WeakKptStale.readPteAt sg _ a2w p2 (hregp bf _) hsm2p hA hord hR hcov hpmar hhtif
      have hrd1p := WeakKptStale.readPteAt sg _ a1w p1 (hregp bf _) hsm1p hA hord hR hcov hpmar hhtif
      have hrd0p := WeakKptStale.readPteAt sg _ la (pteSetAD w av dv) (hregp bf _) hsm0p hA hord hR hcov
        hpmar hhtif
      obtain ⟨sg', es, heq, hdev, ⟨ae, de, hsr⟩, harm⟩ := execStaleTranslateAddrPtMissCases acc p vpn root p2 p1
        (pteSetAD w av dv) p0 a0 d0 satp0 va pa menvcfgS (sg.setReg .minstret_increment bf) hwf0 (heffb bf)
        (hss bf) (hcpb bf) (htm bf) (hsatpb bf) hppn hasid hcanon rfl (hlk bf) hidv hwv2 hn2 hwv1 hn1
        (hval av dv) hleafv (fun mxr ds => hchk av dv mxr ds) hnapv habs (hval a0 d0) hl0
        (fun mxr ds => hchk a0 d0 mxr ds) hnap hrd2p hrd1p hrd0p (hrdxb bf)
        (fun q _ => hwriteb bf q) (hmisab bf) (hmenvb bf) hpbmte hadue
      refine ⟨sg', es, heq, hdev, ⟨ae, de, ?_⟩, ?_⟩
      · rw [hsr, htlbvb bf, pteSetAD_pteSetAD]
      · rcases harm with ⟨hmem, ⟨hg, hes⟩ | ⟨hg, hes⟩⟩ | ⟨q, hq, hmem, hes⟩
        · exact Or.inl ⟨hmem, Or.inl ⟨hg, hes⟩⟩
        · exact Or.inl ⟨hmem, Or.inr ⟨hg, hes⟩⟩
        · exact Or.inr ⟨q, hq, hmem, hes⟩
    -- the top-level arm is decided by the LATEST word, uniformly
    cases hup : update_PTE_Bits p0 acc with
    | some p0' =>
      obtain ⟨a1, d1, hq⟩ := PtAdBits.updatePTEBitsSetAd _ _ _ hup
      refine Or.inr ⟨a1, d1, true, by rw [← hq], fun av dv hle bf => ?_⟩
      obtain ⟨sg', es, heq, hdev, hsr, harm⟩ := hfam bf av dv
      rcases harm with ⟨_, ⟨hg, _⟩ | ⟨hg, _⟩⟩ | ⟨q, hq', hmem, hes⟩
      · have hf := updatePTEBitsFiresMono (pteSetAD w av dv) p0 acc hle (by rw [hup]; rfl)
        rw [hg] at hf; cases hf
      · rw [hup] at hg; cases hg
      · rw [hup] at hq'
        have hqe : q = pteSetAD p0 a1 d1 := (Option.some.inj hq').symm.trans hq
        subst hqe
        exact ⟨sg', es, heq, hmem, hdev, hsr, hes⟩
    | none =>
      refine Or.inl fun av dv _ bf => ?_
      obtain ⟨sg', es, heq, hdev, hsr, harm⟩ := hfam bf av dv
      rcases harm with ⟨hmem, ⟨_, hes⟩ | ⟨_, hes⟩⟩ | ⟨q, hq', _, _⟩
      · exact ⟨sg', es, heq, hmem, hdev, Or.inr hsr, Or.inr (Or.inl hes)⟩
      · exact ⟨sg', es, heq, hmem, hdev, Or.inr hsr, Or.inr (Or.inr (Or.inr hes))⟩
      · rw [hup] at hq'; cases hq'
  · -- ================= HIT on this vpn's own (A/D-variant) entry =================
    -- no PLAIN read runs, so the whole family rides the `execEff` run unchanged
    have habs : pteSetAD p0 a' d' = pteSetAD w a' d' := pteSetAD_pteSetAD w a0 d0 a' d'
    have hchkc : ∀ mxr dosum, wpteCheckOk acc p mxr dosum (pteSetAD p0 a' d') := by
      intro mxr dosum; rw [habs]; exact hchk a' d' mxr dosum
    have hpbc : ptePbmt0 (pteSetAD p0 a' d') := by rw [habs]; exact hvarp a' d'
    have hidc : zero_extend (m := 64)
        (ppn0 (pteSetAD p0 a' d') +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa := by
      show zero_extend (m := 64) (PPN_of_PTE (pteSetAD p0 a' d') +++ _) = pa
      rw [ppn_of_pteSetAD]; exact hid
    have hlkhit : ∀ bf : Bool, execEff (lookup_TLB 39 0#16 vpn) (sg.setReg .minstret_increment bf) =
        some (some (tlb_hash 39 vpn, uWalkEntry vpn p2 p1 (pteSetAD p0 a' d') 0#16),
          sg.setReg .minstret_increment bf, []) := fun bf => execEffLookupTLBHitEnt vpn 0#16 tlbvec _
      (sg.setReg .minstret_increment bf) (htlbvb bf) hslot (WeakKpt.uweMatchSelf vpn p2 p1 (pteSetAD p0 a' d') 0#16)
    cases hupq : update_PTE_Bits (pteSetAD p0 a' d') acc with
    | some q0' =>
      have hvarm : ∃ a2 d2 : BitVec 1, p0 = pteSetAD (pteSetAD p0 a' d') a2 d2 :=
        ⟨a0, d0, by
          show pteSetAD w a0 d0 = pteSetAD (pteSetAD (pteSetAD w a0 d0) a' d') a0 d0
          rw [pteSetAD_pteSetAD, pteSetAD_pteSetAD]⟩
      cases hupm : update_PTE_Bits p0 acc with
      | some p0' =>
        -- O3, hit path: the CAS pair lands
        obtain ⟨a1, d1, hq⟩ := PtAdBits.updatePTEBitsSetAd _ _ _ hupm
        subst hq
        have hqw : pteSetAD p0 a1 d1 = pteSetAD w a1 d1 := pteSetAD_pteSetAD w a0 d0 a1 d1
        refine Or.inr ⟨a1, d1, false, rfl, fun av dv _ bf => ?_⟩
        have hrun := execEffTranslateAddrPtFront acc p vpn root (ppn0 (pteSetAD p0 a' d')) satp0 va pa _
          (sg.setReg .minstret_increment bf) _ (heffb bf) (hss bf) (hcpb bf) (htm bf) (hsatpb bf) hppn hasid
          hcanon rfl (fun mxr dosum =>
            execEffTranslateHitUser vpn root 0#16 (tlb_hash 39 vpn) _ acc p mxr dosum _
              (sg.setReg .minstret_increment bf) _ _ (hlkhit bf)
              (execEffTranslateTLBHitPtUpd acc p mxr dosum vpn p2 p1 (pteSetAD p0 a' d') q0' p0 _ menvcfgS
                0#16 (tlb_hash 39 vpn) _ _ _ (sg.setReg .minstret_increment bf) (hchkc mxr dosum) hupq hpbc
                (hmenvb bf) hadue (hrdxb bf) (hval a0 d0) hl0 (hchk a0 d0 mxr dosum) hnap (hmisab bf) hpbmte
                hvarm hupm (hwriteb bf _) rfl)) hidc
        refine ⟨_, _, execStaleOfExecEff la 8 (pteSetAD w av dv) _ hwf0 _ _ _ _ hrun
          (traceOffWinPinned _ _ _ (by walk_stale_trace)), rfl, rfl, ⟨a1, d1, ?_⟩, rfl⟩
        show (sg.setReg .minstret_increment bf).regs.set .tlb (vectorUpdate
          ((sg.setReg .minstret_increment bf).regs .tlb) (tlb_hash 39 vpn)
            (some (uWalkEntry vpn p2 p1 (pteSetAD p0 a1 d1) 0#16))) = _
        rw [htlbvb bf, hqw]
      | none =>
        -- O2', hit path: refresh only -- the trace is the CAS read
        refine Or.inl fun av dv _ bf => ?_
        have hrun := execEffTranslateAddrPtFront acc p vpn root (ppn0 (pteSetAD p0 a' d')) satp0 va pa _
          (sg.setReg .minstret_increment bf) _ (heffb bf) (hss bf) (hcpb bf) (htm bf) (hsatpb bf) hppn hasid
          hcanon rfl (fun mxr dosum =>
            execEffTranslateHitUser vpn root 0#16 (tlb_hash 39 vpn) _ acc p mxr dosum _
              (sg.setReg .minstret_increment bf) _ _ (hlkhit bf)
              (execEffTranslateTLBHitPtRefresh acc p mxr dosum vpn p2 p1 (pteSetAD p0 a' d') q0' p0 menvcfgS
                0#16 (tlb_hash 39 vpn) _ (sg.setReg .minstret_increment bf) (hchkc mxr dosum) hupq hpbc
                (hmenvb bf) hadue (hrdxb bf) (hval a0 d0) hl0 (hchk a0 d0 mxr dosum) hnap (hmisab bf) hpbmte
                hvarm hupm)) hidc
        refine ⟨_, _, execStaleOfExecEff la 8 (pteSetAD w av dv) _ hwf0 _ _ _ _ hrun
          (traceOffWinPinned _ _ _ (by walk_stale_trace)), rfl, rfl, Or.inr ⟨a0, d0, ?_⟩,
          Or.inr (Or.inr (Or.inl rfl))⟩
        show (sg.setReg .minstret_increment bf).regs.set .tlb (vectorUpdate
          ((sg.setReg .minstret_increment bf).regs .tlb) (tlb_hash 39 vpn)
            (some (uWalkEntry vpn p2 p1 p0 0#16))) = _
        rw [htlbvb bf]
    | none =>
      -- O1: hit, the cached variant needs nothing -- no access at all
      refine Or.inl fun av dv _ bf => ?_
      have hrun := execEffTranslateAddrPtFront acc p vpn root (ppn0 (pteSetAD p0 a' d')) satp0 va pa []
        (sg.setReg .minstret_increment bf) (sg.setReg .minstret_increment bf) (heffb bf) (hss bf) (hcpb bf)
        (htm bf) (hsatpb bf) hppn hasid hcanon rfl (fun mxr dosum =>
          execEffTranslateHitUser vpn root 0#16 (tlb_hash 39 vpn) _ acc p mxr dosum _
            (sg.setReg .minstret_increment bf) _ _ (hlkhit bf)
            (execEffTranslateTLBHitPt acc p mxr dosum vpn p2 p1 (pteSetAD p0 a' d') 0#16 (tlb_hash 39 vpn)
              (sg.setReg .minstret_increment bf) (hchkc mxr dosum) hupq hpbc)) hidc
      exact ⟨_, _, execStaleOfExecEff la 8 (pteSetAD w av dv) _ hwf0 _ _ _ _ hrun
        (traceOffWinPinned _ _ _ (by walk_stale_trace)), rfl, rfl, Or.inl rfl, Or.inl rfl⟩

/-! ## 2bis. The sregs description, weakened to the usable form -/

/-- Rocq `wtlb_regs_preserved`: every register but `tlb` survives the translation. -/
theorem wtlbRegsPreserved (rs rs' : RegFile) :
    (rs' = rs ∨ ∃ tv, rs' = rs.set .tlb tv) →
    ∀ r : Register, r ≠ .tlb → rs' r = rs r := by
  rintro (rfl | ⟨tv, rfl⟩) r hr
  · rfl
  · exact RegFile.set_other _ _ _ _ hr

/-! ## 3. THE RACY ABSORPTION THEOREM -/

section WeakKptStaleAbsorb

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF] [WeakKpt.KptGS GF]

/-- Rocq `wtlb_res_pt_translateAddr_stale_at`: `wtlbResPtTranslateAddrAt`'s twin at the stale
mirror -- the per-variant family at the flag-modified states, the register WAND keyed on the
member that ran, and the ghost outcome (log unchanged / one `WCexcl` message) family-uniform. -/
theorem wtlbResPtTranslateAddrStaleAt (acc : MemoryAccessType mem_payload) (cpu : CPU) (root : BitVec 44)
    (T_kpt : Nat) (tid : Option Nat) (va pa : BitVec 64) (ppn : BitVec 44) (pc : KPerm) (σ : Wmstate)
    (E : CoPset) :
    (↑wkptN : CoPset) ⊆ E →
    (∀ (a d : BitVec 1) (mxr dosum : Bool),
      wpteCheckOk acc .Supervisor mxr dosum (pteSetAD (mkPte ppn pc.flags) a d)) →
    (∀ a d : BitVec 1, wpteValid (pteSetAD (mkPte ppn pc.flags) a d)) →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    zero_extend (m := 64) (ppn +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa →
    wlogWf σ.wmLog →
    σ.wmRegs .misa = misaC →
    σ.wmRegs .menvcfg = menvcfgS →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .cur_privilege = .Supervisor →
    _get_Mstatus_SXL (σ.wmRegs .mstatus) = 2#2 →
    (∀ bf : Bool, execEff (effectivePrivilege acc (σ.wmRegs .mstatus) .Supervisor)
        ((wflatSt σ).setReg .minstret_increment bf) =
      some (.Supervisor, (wflatSt σ).setReg .minstret_increment bf, [])) →
    (∀ bf : Bool, execEff (is_shadow_stack_access acc) ((wflatSt σ).setReg .minstret_increment bf) =
      some (false, (wflatSt σ).setReg .minstret_increment bf, [])) →
    σ.wmRegs .pma_regions = bootPMA →
    T_kpt ≤ σ.wmWs.wVrNew →
    kmapAt (hlc := hlc) (WeakKpt.svpnOf va) (kLeaf ppn pc 0#1 0#1) ∗
      regInterp cpu σ.wmRegs ∗
      wlogAuth (GF := GF) σ.wmLog ∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗
      wtlbResPt (hlc := hlc) (GF := GF) cpu root T_kpt ⊢
    |={E}=> ∃ (p2 p1 lw : BitVec 64),
      ⌜∃ a d : BitVec 1, lw = pteSetAD (mkPte ppn pc.flags) a d⌝ ∗
      ⌜WeakWalkEff.ptSlotMem (wflatSt σ)
          (uPteAddr root (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 26 18)) p2 ∧
        WeakWalkEff.ptSlotMem (wflatSt σ)
          (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 17 9)) p1 ∧
        WeakWalkEff.ptSlotMem (wflatSt σ)
          (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) lw⌝ ∗
      ⌜∀ j : Nat, j < 8 →
        pinnedRead σ (WeakInterp.accAddr (uPteAddr root (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 26 18)) j) ∧
        pinnedRead σ (WeakInterp.accAddr
          (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 17 9)) j)⌝ ∗
      ⌜raccDisj (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8
          (uPteAddr root (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 26 18)) 8 ∧
        raccDisj (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8
          (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 17 9)) 8⌝ ∗
      ⌜∀ (rak : AkInfo) (wv : BitVec (8 * 8)), rak.akIfetch = false →
        wadm σ rak (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 wv →
        (∃ a d : BitVec 1, wv = pteSetAD (mkPte ppn pc.flags) a d) ∧ pteAdLe wv lw⌝ ∗
      ⌜∀ j : Nat, j < 8 → nvFree σ.wmLog (WeakInterp.accAddr
        (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) j)⌝ ∗
      regInterp cpu σ.wmRegs ∗
      -- the REGISTER WAND, keyed on the member that ran and on the flag
      (∀ (bf : Bool) (av dv : BitVec 1) (sg' : ExecSt) (es : List Weff),
        ⌜pteAdLe (pteSetAD (mkPte ppn pc.flags) av dv) lw⌝ -∗
        ⌜execStale (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8
            (pteSetAD (mkPte ppn pc.flags) av dv) (translateAddr (.Virtaddr va) acc)
            ((wflatSt σ).setReg .minstret_increment bf) =
          some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', es)⌝ -∗
        regInterp cpu (σ.wmRegs.set .minstret_increment bf) -∗
        |==> (regInterp cpu sg'.regs ∗ wtlbResPt (hlc := hlc) (GF := GF) cpu root T_kpt)) ∗
      ( -- READ-ONLY: the log does not move
        (⌜∀ av dv : BitVec 1, pteAdLe (pteSetAD (mkPte ppn pc.flags) av dv) lw → ∀ bf : Bool,
          ∃ (sg' : ExecSt) (es : List Weff),
            execStale (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8
                (pteSetAD (mkPte ppn pc.flags) av dv) (translateAddr (.Virtaddr va) acc)
                ((wflatSt σ).setReg .minstret_increment bf) =
              some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', es) ∧
            sg'.mem = wflatMem σ.wmImg σ.wmLog ∧
            sg'.dev = σ.wmDev ∧
            (∀ r : Register, r ≠ .tlb → sg'.regs r = ((wflatSt σ).setReg .minstret_increment bf).regs r) ∧
            (es = [] ∨
             es = [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 26 18)) 8,
                   .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 17 9)) 8,
                   .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8] ∨
             es = [.WEread ⟨false, true, false⟩
                     (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8] ∨
             es = [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 26 18)) 8,
                   .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 17 9)) 8,
                   .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8,
                   .WEread ⟨false, true, false⟩
                     (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8])⌝ ∗
          wlogAuth (GF := GF) σ.wmLog ∗ wlatInterp (GF := GF) σ.wmImg σ.wmLog) ∨
        -- WRITE-BACK: one `WCexcl` message, the same for every family member
        (∃ lw' : BitVec 64,
          ⌜update_PTE_Bits lw acc = some lw'⌝ ∗
          ⌜∃ wtr : Bool, ∀ av dv : BitVec 1, pteAdLe (pteSetAD (mkPte ppn pc.flags) av dv) lw → ∀ bf : Bool,
            ∃ (sg' : ExecSt) (es : List Weff),
              execStale (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8
                  (pteSetAD (mkPte ppn pc.flags) av dv) (translateAddr (.Virtaddr va) acc)
                  ((wflatSt σ).setReg .minstret_increment bf) =
                some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', es) ∧
              sg'.mem = bmWrite (wflatMem σ.wmImg σ.wmLog)
                (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 lw' ∧
              sg'.dev = σ.wmDev ∧
              (∀ r : Register, r ≠ .tlb → sg'.regs r = ((wflatSt σ).setReg .minstret_increment bf).regs r) ∧
              es = (if wtr then
                      [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 26 18)) 8,
                       .WEread wakPlain
                         (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 17 9)) 8,
                       .WEread wakPlain
                         (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8,
                       .WEread ⟨false, true, false⟩
                         (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8,
                       .WEwrite ⟨false, true, false⟩
                         (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 lw']
                    else
                      [.WEread ⟨false, true, false⟩
                         (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8,
                       .WEwrite ⟨false, true, false⟩
                         (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 lw'])⌝ ∗
          wlogAuth (GF := GF) (σ.wmLog ++ [wwriteMsg tid .WCexcl
            (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 lw']) ∗
          wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [wwriteMsg tid .WCexcl
            (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 lw']))) := by
  intro hE hchk hval hcanon hid4k hwlog hmisa hmenv hhtif hcp hsxl heff hss hpma hrcpt
  iintro ⟨#Hat, Hri, Hla, Hi, Hres⟩
  iunfold wtlbResPt at Hres
  icases Hres with ⟨%satp0, %tlbvec, Hsatp, %hmode, %hasid, %hppn, Htlb, Hsnap, Hpmp, #Hkinv⟩
  iunfold WeakKpt.tlbSnapOk at Hsnap
  icases Hsnap with ⟨%t0, %htlbok0, #Hlb0⟩
  icases keepPure (wand_intro (reg_valid cpu σ.wmRegs .satp (DFrac.own 1) satp0)) $$ Hri Hsatp
    with ⟨%hsatpv, Hri, Hsatp⟩
  icases keepPure (wand_intro (reg_valid cpu σ.wmRegs .tlb (DFrac.own 1) tlbvec)) $$ Hri Htlb
    with ⟨%htlbv, Hri, Htlb⟩
  iunfold WeakKpt.pmpConfig at Hpmp
  icases Hpmp with ⟨%pmpcfg0, %pmpaddr00, Hpc, Hpa, %hA, %hord, %hX, %hW, %hR, %hcov⟩
  icases keepPure (wand_intro (reg_valid cpu σ.wmRegs .pmpcfg_n (DFrac.own 1) pmpcfg0)) $$ Hri Hpc
    with ⟨%hpcv, Hri, Hpc⟩
  icases keepPure (wand_intro (reg_valid cpu σ.wmRegs .pmpaddr_n (DFrac.own 1) pmpaddr00)) $$ Hri Hpa
    with ⟨%hpav, Hri, Hpa⟩
  have hpmaw : WeakKpt.pmaAllowsPteWrite (σ.wmRegs .pma_regions) := by
    rw [hpma]; exact WeakKpt.pmaAllowsBootPteWrite
  have hpmar : WeakKpt.pmaAllowsPteRead (σ.wmRegs .pma_regions) := by
    rw [hpma]; exact WeakKpt.pmaAllowsBootPteRead
  have hA' : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (σ.wmRegs .pmpcfg_n)[0]!) = .TOR := by
    rw [hpcv]; exact hA
  have hord' : zopz0zKzJ_u (zeros (n := 64)) (σ.wmRegs .pmpaddr_n)[0]! = false := by
    rw [hpav]; exact hord
  have hR' : (_get_Pmpcfg_ent_R (σ.wmRegs .pmpcfg_n)[0]! == 1#1) = true := by rw [hpcv]; exact hR
  have hW' : (_get_Pmpcfg_ent_W (σ.wmRegs .pmpcfg_n)[0]! == 1#1) = true := by rw [hpcv]; exact hW
  have hcov' : ramEnd ≤ (σ.wmRegs .pmpaddr_n)[0]!.toNat * 4 := by rw [hpav]; exact hcov
  -- the flag write frames every register lookup; the RUN is re-run at each modified state
  have hregb : ∀ (bf : Bool) (r : Register), r ≠ .minstret_increment →
      ((wflatSt σ).setReg .minstret_increment bf).regs r = σ.wmRegs r :=
    fun bf r h => WeakFetchEff.saLookup r (wflatSt σ) bf h
  have htm : ∀ bf : Bool, execEff (translationMode .Supervisor) ((wflatSt σ).setReg .minstret_increment bf) =
      some (.Sv39, (wflatSt σ).setReg .minstret_increment bf, []) := fun bf =>
    execEffTranslationModeSSv39 satp0 _ (by rw [hregb bf .mstatus (by decide)]; exact hsxl)
      (by rw [hregb bf .satp (by decide)]; exact hsatpv) hmode
  -- ---- open the shared table ----
  iunfold wkptInv at Hkinv
  imod (inv_acc (E := E) (N := wkptN) (P := wkptBody (hlc := hlc) (GF := GF) root T_kpt) hE) $$ Hkinv
    with ⟨Hbody, Hclose⟩
  imod (wkpt_body_timeless (hlc := hlc) (GF := GF) root T_kpt).timeless $$ Hbody with Hbody
  iunfold wkptBody at Hbody
  icases Hbody with ⟨%t, %M, #Hlbt, #HM, %hspec, Hmap⟩
  ihave %hMlk := (wand_intro (WeakKpt.kmapAtLookup (hlc := hlc) (GF := GF) M (WeakKpt.svpnOf va) ppn pc))
    $$ HM Hat
  ihave %hcan0 := (wand_intro (WeakKpt.kptLbAgree (GF := GF) t0 t)) $$ Hlb0 Hlbt
  have htlbok : AxPtProt.tlbOkPt 0#16 t tlbvec := AxPtProt.tlbOkPtCanon 0#16 t0 t tlbvec hcan0 htlbok0
  obtain ⟨hbase, hkeys, -⟩ := id hspec
  obtain ⟨e, he⟩ : ∃ e : BitVec 64, e = kLeaf ppn pc 0#1 0#1 := ⟨_, rfl⟩
  rw [← he] at hMlk
  have hkv : ∀ a d : BitVec 1, pteSetAD e a d = pteSetAD (mkPte ppn pc.flags) a d := by
    intro a d; rw [he]; exact pteSetAD_pteSetAD _ _ _ a d
  have hchk' : ∀ (a d : BitVec 1) (mxr dosum : Bool), wpteCheckOk acc .Supervisor mxr dosum (pteSetAD e a d) := by
    intro a d mxr dosum; rw [hkv]; exact hchk a d mxr dosum
  have hval' : ∀ a d : BitVec 1, wpteValid (pteSetAD e a d) := by
    intro a d; rw [hkv]; exact hval a d
  have hvarp : ∀ a d : BitVec 1, ptePbmt0 (pteSetAD e a d) := by
    intro a d
    rw [hkv, show pteSetAD (mkPte ppn pc.flags) a d = kLeaf ppn pc a d from rfl]
    unfold ptePbmt0; rw [ext_of_kLeaf]; rfl
  have hout : zero_extend (m := 64) (ppn0 e +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa := by
    show zero_extend (m := 64) (PPN_of_PTE e +++ _) = pa
    rw [he, ppn_of_kLeaf]; exact hid4k
  -- ---- the vpn's bundle ----
  icases (WeakKpt.bigSepMVpnDelete (fun v e => wvpnRes (GF := GF) T_kpt t v e) M (WeakKpt.svpnOf va) e hMlk)
    $$ Hmap with ⟨Hvpn, Hrest⟩
  iunfold wvpnRes at Hvpn
  icases Hvpn with ⟨%p2, %p1, %a0, %d0, %hmaps, #Hptr2, #Hptr1, Hleaf⟩
  iunfold wptr8 at Hptr2 Hptr1
  icases Hptr2 with ⟨%ts2, %hts2, %hg2, %hwv2, #Hel2⟩
  icases Hptr1 with ⟨%ts1, %hts1, %hg1, %hwv1, #Hel1⟩
  iunfold wleafRes at Hleaf
  icases Hleaf with ⟨%ts, %T0, %log0, %hg0, %hbnds, %hinst0, %hvars0, %hfresh0, #Hlblog, Hel0⟩
  obtain ⟨hT01, hT0K, hT0ts, htslen⟩ := hbnds
  -- ---- the slots at the flat state ----
  icases keepPure (wlat8FlatGen σ (AxPtProt.ptAddr2 t (WeakKpt.svpnOf va)) DFrac.discard ts2 p2 hwlog
    (wslotGeomAccWf _ hg2)) $$ Hi Hel2 with ⟨%hfl2, Hi, -⟩
  icases keepPure (wlat8FlatGen σ (AxPtProt.ptAddr1 p2 (WeakKpt.svpnOf va)) DFrac.discard ts1 p1 hwlog
    (wslotGeomAccWf _ hg1)) $$ Hi Hel1 with ⟨%hfl1, Hi, -⟩
  icases keepPure (wlat8FlatGen σ (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va)) (DFrac.own 1) ts
    (pteSetAD e a0 d0) hwlog (wslotGeomAccWf _ hg0)) $$ Hi Hel0 with ⟨%hfl0, Hi, Hel0⟩
  obtain ⟨hflat2, hlat2⟩ := hfl2
  obtain ⟨hflat1, hlat1⟩ := hfl1
  obtain ⟨hflat0, hlat0⟩ := hfl0
  have hsm2 := wslotMemOfFlat σ _ p2 hg2 hflat2
  have hsm1 := wslotMemOfFlat σ _ p1 hg1 hflat1
  have hsm0 := wslotMemOfFlat σ _ (pteSetAD e a0 d0) hg0 hflat0
  -- ---- the clipped closure, extended to the current log ----
  icases keepPure (wand_intro (wlogValid (GF := GF) σ.wmLog log0)) $$ Hla Hlblog with ⟨%hpref, Hla, -⟩
  have hlen0 : log0.length ≤ σ.wmLog.length := prefix_length hpref
  have hnw := wwinNoWriteAbove σ (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va)) ts hlat0
  have hvars : wlogVariantsFrom T0 σ.wmLog (paZ (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va))) e :=
    wlogVariantsFromExt T0 log0 σ.wmLog _ e hvars0 hpref
      (fun i m hm hge j hj => hnw i m hm (by omega) j hj)
  have hfresh : ∀ img : Image, wfreshFrom T0 img σ.wmLog (paZ (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va))) := by
    intro img
    refine wfreshFromExt T0 img log0 σ.wmLog _ (hfresh0 img) hpref (fun i m hm hge => ?_)
    have h := hnw i m hm (by omega) 0 (by omega)
    rwa [WeakInterp.accAddr0] at h
  have hinst : wwinInstall σ.wmLog T0 (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va)) :=
    wwinInstallPrefix log0 σ.wmLog T0 _ hinst0 hpref
  have hcovg : T0 ≤ σ.wmWs.wVrNew := by omega
  -- ---- the racy-leaf collapse facts ----
  icases keepPure (wlat8WinLatest σ (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va)) (DFrac.own 1) ts
    (pteSetAD e a0 d0)) $$ Hi Hel0 with ⟨%hwlat, Hi, Hel0⟩
  icases keepPure (nvFreeWlat8 σ.wmImg σ.wmLog (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va)) (DFrac.own 1) ts
    (pteSetAD e a0 d0)) $$ Hi Hel0 with ⟨%hnvfree, Hi, Hel0⟩
  have hcoll : ∀ (rak : AkInfo) (wv : BitVec (8 * 8)), rak.akIfetch = false →
      wadm σ rak (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 wv →
      (∃ a d : BitVec 1, wv = pteSetAD (mkPte ppn pc.flags) a d) ∧ pteAdLe wv (pteSetAD e a0 d0) := by
    intro rak wv hif hadm
    refine ⟨?_, wadmPteAdLeLatestFrom σ rak _ e T0 wv _ hvars (hfresh (wimg σ)) hinst hif hcovg hwlat hadm⟩
    obtain ⟨a, d, hw⟩ := wadmVariantFrom σ rak _ e T0 wv hvars hinst hif hcovg hadm
    exact ⟨a, d, by rw [hw, hkv]⟩
  -- ---- pointer pinnedness for the caller's trace_pin ----
  have ha2 : AxPtProt.ptAddr2 t (WeakKpt.svpnOf va) =
      uPteAddr root (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 26 18) := by
    unfold AxPtProt.ptAddr2; rw [hbase]; rfl
  have hpin : ∀ j : Nat, j < 8 →
      pinnedRead σ (WeakInterp.accAddr (uPteAddr root (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 26 18)) j) ∧
      pinnedRead σ (WeakInterp.accAddr
        (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 17 9)) j) := by
    intro j hj
    refine ⟨?_, ?_⟩
    · unfold pinnedRead; rw [← ha2, hlat2 j hj]; omega
    · unfold pinnedRead; rw [show (WeakInterp.accAddr
        (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 17 9)) j) =
        WeakInterp.accAddr (AxPtProt.ptAddr1 p2 (WeakKpt.svpnOf va)) j from rfl, hlat1 j hj]; omega
  have hslots : WeakWalkEff.ptSlotMem (wflatSt σ)
        (uPteAddr root (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 26 18)) p2 ∧
      WeakWalkEff.ptSlotMem (wflatSt σ)
        (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 17 9)) p1 ∧
      WeakWalkEff.ptSlotMem (wflatSt σ)
        (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) (pteSetAD e a0 d0) :=
    ⟨ha2 ▸ hsm2, hsm1, hsm0⟩
  -- ---- the leaf's latest value, for the write-back arm ----
  have hlatbyte : ∀ img : Image,
      logByte img σ.wmLog (latestTs σ.wmLog (paZ (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va))))
        (paZ (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va))) = some (nthByte (n := 8) (pteSetAD e a0 d0) 0) := by
    have hts0 := hlat0 0 (by omega)
    obtain ⟨t', hlv⟩ := hwlat 0 (by omega)
    have htt : t' = ts := (latestValTs _ _ _ _ _ hlv).symm.trans hts0
    have hb0 := hlv.1
    rw [htt] at hb0
    intro img
    rw [← WeakInterp.accAddr0, hts0, logByteImgIrrel img (wimg σ) σ.wmLog ts _ (by omega)]
    exact hb0
  -- ---- run the STALE dispatch at the flat state ----
  obtain ⟨hdj2, hdj1, hfam | ⟨a1, d1, wtr, hupd, hfam⟩⟩ := wptreeTranslateAddrStaleCases acc .Supervisor root
    va e pa satp0 t tlbvec p2 p1 a0 d0 (wflatSt σ) hchk' hval' hcanon hout hvarp hwv2 hwv1 hbase hmaps htlbok
    hsm2 hsm1 hsm0 hmisa hmenv hhtif hcp htm heff hss hsatpv hppn hasid htlbv hA' hord' hR' hW' hcov' hpmar
    hpmaw
  · -- ================= READ-ONLY: nothing moved =================
    imod Hclose $$ [Hrest Hel0]
    · inext
      iunfold wkptBody
      iexists t, M
      isplitr
      · iexact Hlbt
      isplitr
      · iexact HM
      isplitr
      · ipureintro; exact hspec
      iapply (WeakKpt.bigSepMVpnInsert (fun v e => wvpnRes (GF := GF) T_kpt t v e) M (WeakKpt.svpnOf va) e hMlk)
      iframe Hrest
      iunfold wvpnRes
      iexists p2, p1, a0, d0
      isplitr
      · ipureintro; exact hmaps
      isplitr
      · iunfold wptr8
        iexists ts2
        iframe Hel2
        ipureintro; exact ⟨hts2, hg2, hwv2⟩
      isplitr
      · iunfold wptr8
        iexists ts1
        iframe Hel1
        ipureintro; exact ⟨hts1, hg1, hwv1⟩
      iunfold wleafRes
      iexists ts, T0, log0
      iframe Hel0 Hlblog
      ipureintro
      exact ⟨hg0, ⟨hT01, hT0K, hT0ts, htslen⟩, hinst0, hvars0, hfresh0⟩
    imodintro
    iexists p2, p1, (pteSetAD e a0 d0)
    isplitr
    · ipureintro; exact ⟨a0, d0, hkv a0 d0⟩
    isplitr
    · ipureintro; exact hslots
    isplitr
    · ipureintro; exact hpin
    isplitr
    · ipureintro; exact ⟨hdj2, hdj1⟩
    isplitr
    · ipureintro; exact hcoll
    isplitr
    · ipureintro; exact hnvfree
    isplitl [Hri]
    · iexact Hri
    isplitl [Hsatp Htlb Hpc Hpa]
    · -- ---- the REGISTER WAND (read-only arm) ----
      iintro %bf %av %dv %sgc %esc %hle %hrun Hri
      rw [← hkv av dv] at hle hrun
      obtain ⟨sgx, esx, hrunx, -, -, hsrx, -⟩ := hfam av dv hle bf
      rw [hrun] at hrunx
      simp only [Option.some.injEq, Prod.mk.injEq] at hrunx
      obtain ⟨-, hsg, -⟩ := hrunx
      subst hsg
      rcases hsrx with hsr | ⟨ae, de, hsr⟩
      · -- no register moved
        have hsr' : sgc.regs = σ.wmRegs.set .minstret_increment bf := hsr
        imodintro
        isplitl [Hri]
        · ieval (rewrite [hsr'])
          iexact Hri
        · iapply (wtlbResPtIntro (hlc := hlc) (GF := GF) cpu root T_kpt satp0 tlbvec t hmode hasid hppn htlbok)
          isplitl [Hsatp]
          · iexact Hsatp
          isplitl [Htlb]
          · iexact Htlb
          isplitr
          · iexact Hlbt
          isplitl [Hpc Hpa]
          · iapply (WeakKpt.pmpConfigIntro (hlc := hlc) (GF := GF) cpu root pmpcfg0 pmpaddr00 hA hord hX hW hR hcov)
            isplitl [Hpc]
            · iexact Hpc
            · iexact Hpa
          · iunfold wkptInv
            iexact Hkinv
      · -- a TLB entry carrying an A/D variant of the mapped leaf
        have hsr' : sgc.regs = (σ.wmRegs.set .minstret_increment bf).set .tlb
            (vectorUpdate tlbvec (tlb_hash 39 (WeakKpt.svpnOf va))
              (some (uWalkEntry (WeakKpt.svpnOf va) p2 p1 (pteSetAD e ae de) 0#16))) := hsr
        have hokf := AxPtProt.tlbOkPtFill 0#16 t tlbvec (WeakKpt.svpnOf va) p2 p1 (pteSetAD e a0 d0)
          (pteSetAD e ae de) hmaps ⟨ae, de, (pteSetAD_pteSetAD e a0 d0 ae de).symm⟩ htlbok
        imod reg_update cpu (σ.wmRegs.set .minstret_increment bf) .tlb tlbvec
          (vectorUpdate tlbvec (tlb_hash 39 (WeakKpt.svpnOf va))
            (some (uWalkEntry (WeakKpt.svpnOf va) p2 p1 (pteSetAD e ae de) 0#16))) $$ [Hri Htlb] with ⟨Hri, Htlb⟩
        · iframe Hri Htlb
        imodintro
        isplitl [Hri]
        · ieval (rewrite [hsr'])
          iexact Hri
        · iapply (wtlbResPtIntro (hlc := hlc) (GF := GF) cpu root T_kpt satp0 _ t hmode hasid hppn hokf)
          isplitl [Hsatp]
          · iexact Hsatp
          isplitl [Htlb]
          · iexact Htlb
          isplitr
          · iexact Hlbt
          isplitl [Hpc Hpa]
          · iapply (WeakKpt.pmpConfigIntro (hlc := hlc) (GF := GF) cpu root pmpcfg0 pmpaddr00 hA hord hX hW hR hcov)
            isplitl [Hpc]
            · iexact Hpc
            · iexact Hpa
          · iunfold wkptInv
            iexact Hkinv
    ileft
    isplitr
    · ipureintro
      intro av dv hle bf
      rw [← hkv av dv] at hle ⊢
      obtain ⟨sgx, esx, h1, h2, h3, h4, h5⟩ := hfam av dv hle bf
      exact ⟨sgx, esx, h1, h2, h3, wtlbRegsPreserved _ _ (h4.imp id fun ⟨_, _, h⟩ => ⟨_, h⟩), h5⟩
    isplitl [Hla]
    · iexact Hla
    · iexact Hi
  · -- ================= WRITE-BACK, absorbed =================
    have hla0 : AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va) =
        uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0) := rfl
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hv0, hl0, hn0, hpb0⟩ := id hmaps
    have habs : pteSetAD (pteSetAD e a0 d0) a1 d1 = pteSetAD e a1 d1 := pteSetAD_pteSetAD _ _ _ _ _
    have hv' := (AxPtProt.pteSetAdValidLeaf _ a1 d1 hl0).2 hv0
    have hl' := (AxPtProt.pteSetAdLeaf _ a1 d1).2 hl0
    have hn' := (AxPtProt.pteSetAdNoNapot _ a1 d1).2 hn0
    have hp' := (AxPtProt.pteSetAdPbmt0 _ a1 d1).2 hpb0
    -- the tree moves by the leaf write; the canonical table does not
    have hcan' := AxPtProt.ptreeCanonSetLeaf t (WeakKpt.svpnOf va) p2 p1 (pteSetAD e a0 d0) a1 d1 hmaps
    have hspec' := WeakKpt.kptTreeSpecGenSetLeaf root M t (WeakKpt.svpnOf va) e p2 p1 (pteSetAD e a0 d0) a1 d1
      hspec hmaps hMlk ⟨a0, d0, rfl⟩
    have hbase' : (AxPtProt.ptreeSetLeaf t (WeakKpt.svpnOf va) (pteSetAD (pteSetAD e a0 d0) a1 d1)).base =
        t.base := WeakKpt.ptreeSetLeafBase _ _ _
    have hmaps' := AxPtProt.ptreeSetLeafMapsSelf t (WeakKpt.svpnOf va) p2 p1 (pteSetAD e a0 d0) _ hmaps
      hv' hl' hn' hp'
    have htlbokt := AxPtProt.tlbOkPtSetLeaf 0#16 t tlbvec (WeakKpt.svpnOf va) p2 p1 (pteSetAD e a0 d0) a1 d1
      hmaps hv' hl' hn' hp' htlbok
    ihave #Hlb' := (WeakKpt.kptLbCanon (GF := GF) t
      (AxPtProt.ptreeSetLeaf t (WeakKpt.svpnOf va) (pteSetAD (pteSetAD e a0 d0) a1 d1)) hcan'.symm) $$ Hlbt
    -- ghost: append the message, retarget the leaf element
    imod (wlogUpdate (GF := GF) σ.wmLog [wwriteMsg tid .WCexcl (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va)) 8
      (pteSetAD e a1 d1)]) $$ Hla with Hla
    icases (wlogSnapshot (GF := GF) _) $$ Hla with ⟨Hla, #Hlb''⟩
    imod (WeakKpt.wlat8StoreExcl (GF := GF) tid σ (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va)) ts
      (pteSetAD e a0 d0) (pteSetAD e a1 d1)) $$ Hi Hel0 with ⟨Hi, Hel0'⟩
    -- the new leaf bundle's clipped facts
    have hupd' : update_PTE_Bits (pteSetAD e a0 d0) acc = some (pteSetAD e a1 d1) := by rw [hupd, habs]
    have hvars' : wlogVariantsFrom T0
        (σ.wmLog ++ [wwriteMsg tid .WCexcl (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va)) 8 (pteSetAD e a1 d1)])
        (paZ (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va))) e :=
      wlogVariantsFromSnoc T0 σ.wmLog _ e _ hvars
        (wmsgVariantWrite tid .WCexcl _ (pteSetAD e a1 d1) _ e rfl ⟨a1, d1, rfl⟩)
    have hfresh' : ∀ img : Image, wfreshFrom T0 img
        (σ.wmLog ++ [wwriteMsg tid .WCexcl (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va)) 8 (pteSetAD e a1 d1)])
        (paZ (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va))) :=
      fun img => wfreshFromWriteback T0 img σ.wmLog tid .WCexcl _ acc (pteSetAD e a0 d0) (pteSetAD e a1 d1)
        (pteSetAD e a1 d1) (hlatbyte img) hupd' rfl (hfresh img)
    have hinst' : wwinInstall
        (σ.wmLog ++ [wwriteMsg tid .WCexcl (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va)) 8 (pteSetAD e a1 d1)])
        T0 (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va)) :=
      wwinInstallPrefix σ.wmLog _ T0 _ hinst ⟨_, rfl⟩
    -- re-close the invariant at the new tree
    imod Hclose $$ [Hrest Hel0']
    · inext
      iunfold wkptBody
      iexists (AxPtProt.ptreeSetLeaf t (WeakKpt.svpnOf va) (pteSetAD (pteSetAD e a0 d0) a1 d1)), M
      isplitr
      · iexact Hlb'
      isplitr
      · iexact HM
      isplitr
      · ipureintro; exact hspec'
      iapply (WeakKpt.bigSepMVpnInsert (fun v e' => wvpnRes (GF := GF) T_kpt
        (AxPtProt.ptreeSetLeaf t (WeakKpt.svpnOf va) (pteSetAD (pteSetAD e a0 d0) a1 d1)) v e') M
        (WeakKpt.svpnOf va) e hMlk)
      isplitl [Hel0']
      · iunfold wvpnRes
        iexists p2, p1, a1, d1
        have haddr2 : AxPtProt.ptAddr2 (AxPtProt.ptreeSetLeaf t (WeakKpt.svpnOf va)
            (pteSetAD (pteSetAD e a0 d0) a1 d1)) (WeakKpt.svpnOf va) = AxPtProt.ptAddr2 t (WeakKpt.svpnOf va) := by
          unfold AxPtProt.ptAddr2; rw [hbase']
        isplitr
        · ipureintro; rw [← habs]; exact hmaps'
        isplitr
        · rw [haddr2]
          iunfold wptr8
          iexists ts2
          iframe Hel2
          ipureintro; exact ⟨hts2, hg2, hwv2⟩
        isplitr
        · iunfold wptr8
          iexists ts1
          iframe Hel1
          ipureintro; exact ⟨hts1, hg1, hwv1⟩
        iunfold wleafRes
        iexists σ.wmLog.length + 1, T0,
          (σ.wmLog ++ [wwriteMsg tid .WCexcl (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va)) 8 (pteSetAD e a1 d1)])
        iframe Hel0' Hlb''
        ipureintro
        refine ⟨hg0, ⟨hT01, hT0K, by omega, by simp only [List.length_append, List.length_singleton]; omega⟩,
          hinst', hvars', hfresh'⟩
      · iapply (BigSepM.bigSepM_mono (fun {k v} hk => ?_)) $$ Hrest
        obtain ⟨hne, hk'⟩ := LawfulPartialMap.get?_delete_some_iff.1 hk
        apply wvpnResMapsMono T_kpt t _ (BitVec.ofNat 27 k) v _ (by rw [hbase'])
        intro q2 q1 q0 hm'
        refine AxPtProt.ptreeSetLeafMapsOther t (WeakKpt.svpnOf va) (BitVec.ofNat 27 k) q2 q1 q0 _ ?_ hm'
        intro hbv
        apply hne
        have hk27 := hkeys k v hk'
        rw [← hbv]
        simp only [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt hk27
    imodintro
    iexists p2, p1, (pteSetAD e a0 d0)
    isplitr
    · ipureintro; exact ⟨a0, d0, hkv a0 d0⟩
    isplitr
    · ipureintro; exact hslots
    isplitr
    · ipureintro; exact hpin
    isplitr
    · ipureintro; exact ⟨hdj2, hdj1⟩
    isplitr
    · ipureintro; exact hcoll
    isplitr
    · ipureintro; exact hnvfree
    isplitl [Hri]
    · iexact Hri
    isplitl [Hsatp Htlb Hpc Hpa]
    · -- ---- the REGISTER WAND (write-back arm) ----
      iintro %bf %av %dv %sgc %esc %hle %hrun Hri
      rw [← hkv av dv] at hle hrun
      obtain ⟨sgx, esx, hrunx, -, -, ⟨ae, de, hsr⟩, -⟩ := hfam av dv hle bf
      rw [hrun] at hrunx
      simp only [Option.some.injEq, Prod.mk.injEq] at hrunx
      obtain ⟨-, hsg, -⟩ := hrunx
      subst hsg
      have hsr' : sgc.regs = (σ.wmRegs.set .minstret_increment bf).set .tlb
          (vectorUpdate tlbvec (tlb_hash 39 (WeakKpt.svpnOf va))
            (some (uWalkEntry (WeakKpt.svpnOf va) p2 p1 (pteSetAD e ae de) 0#16))) := hsr
      have hokf := AxPtProt.tlbOkPtFill 0#16 _ tlbvec (WeakKpt.svpnOf va) p2 p1 _ (pteSetAD e ae de) hmaps'
        ⟨ae, de, by rw [pteSetAD_pteSetAD, pteSetAD_pteSetAD]⟩ htlbokt
      imod reg_update cpu (σ.wmRegs.set .minstret_increment bf) .tlb tlbvec
        (vectorUpdate tlbvec (tlb_hash 39 (WeakKpt.svpnOf va))
          (some (uWalkEntry (WeakKpt.svpnOf va) p2 p1 (pteSetAD e ae de) 0#16))) $$ [Hri Htlb] with ⟨Hri, Htlb⟩
      · iframe Hri Htlb
      imodintro
      isplitl [Hri]
      · ieval (rewrite [hsr'])
        iexact Hri
      · iapply (wtlbResPtIntro (hlc := hlc) (GF := GF) cpu root T_kpt satp0 _
          (AxPtProt.ptreeSetLeaf t (WeakKpt.svpnOf va) (pteSetAD (pteSetAD e a0 d0) a1 d1)) hmode hasid hppn hokf)
        isplitl [Hsatp]
        · iexact Hsatp
        isplitl [Htlb]
        · iexact Htlb
        isplitr
        · iexact Hlb'
        isplitl [Hpc Hpa]
        · iapply (WeakKpt.pmpConfigIntro (hlc := hlc) (GF := GF) cpu root pmpcfg0 pmpaddr00 hA hord hX hW hR hcov)
          isplitl [Hpc]
          · iexact Hpc
          · iexact Hpa
        · iunfold wkptInv
          iexact Hkinv
    iright
    iexists (pteSetAD e a1 d1)
    isplitr
    · ipureintro; exact hupd'
    isplitr
    · ipureintro
      refine ⟨wtr, fun av dv hle bf => ?_⟩
      rw [← hkv av dv] at hle ⊢
      obtain ⟨sgx, esx, h1, h2, h3, ⟨_, _, h4⟩, h5⟩ := hfam av dv hle bf
      rw [habs] at h2 h5
      exact ⟨sgx, esx, h1, h2, h3, wtlbRegsPreserved _ _ (Or.inr ⟨_, h4⟩), h5⟩
    ieval (rewrite [hla0]) at Hla Hi
    isplitl [Hla]
    · iexact Hla
    · iexact Hi

end WeakKptStaleAbsorb

/-! ## 4. THE PEEL OF THE TRANSLATION

§3's exports turned into a `wstepOkRacy` object for the translation.  It is PURE: the
absorption theorem's exported facts are premises.  THE VALUE FILTER `wwalkFilter`: the words the
window may hand the walk are the A/D variants of the canonical leaf below the coherence-latest
one; its side condition (`wadmFilter`) IS the collapse fact.  Five of the six trace shapes go
through the stale producer (`wstepOkRacyTrueOfStaleWindow`); the TLB-HIT write-back
`[excl-read, write]` transfers back to `execEff` (`execEffOfExecStale`) and takes the ordinary
confined producer (`wstepEffConfinedPin`) plus the phase-`false` embedding and phase
monotonicity. -/

def wwalkFilter (w0 lw : BitVec 64) : (Nat → BitVec 8) → Prop :=
  fun bs => ∃ wv : BitVec (8 * 8), bs = (fun j : Nat => nthByte wv j) ∧
    (∃ a d : BitVec 1, wv = pteSetAD w0 a d) ∧ pteAdLe wv lw

/-! ### 4a. The window: the 24 bytes of the three slots -/

theorem wwalkSlotsIn2 (a2 a1 la : PAddr) (j : Nat) :
    j < 8 → a2 + BitVec.ofNat 64 j ∈ accWin [a2, a1, la] 8 :=
  fun hj => accWinIn _ _ _ _ (by simp) hj

theorem wwalkSlotsIn1 (a2 a1 la : PAddr) (j : Nat) :
    j < 8 → a1 + BitVec.ofNat 64 j ∈ accWin [a2, a1, la] 8 :=
  fun hj => accWinIn _ _ _ _ (by simp) hj

theorem wwalkSlotsIn0 (a2 a1 la : PAddr) (j : Nat) :
    j < 8 → la + BitVec.ofNat 64 j ∈ accWin [a2, a1, la] 8 :=
  fun hj => accWinIn _ _ _ _ (by simp) hj

/-- RAM starts at `0x80000000`, so no byte of a slot is the null address. -/
theorem wwalkWinNonzero (sg : ExecSt) (a2 a1 la p2 p1 lw : BitVec 64) :
    WeakWalkEff.ptSlotMem sg a2 p2 → WeakWalkEff.ptSlotMem sg a1 p1 → WeakWalkEff.ptSlotMem sg la lw →
    ∀ a, a ∈ accWin [a2, a1, la] 8 → paZ a ≠ 0 := by
  intro hs2 hs1 hs0 a ha
  obtain ⟨b, j, hb, hj, rfl⟩ := accWinInv _ _ _ ha
  have hram : inRam b 8 ∧ accWf b 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact ⟨hs2.2.1, ptSlotMemAccWf _ _ _ hs2⟩
    · exact ⟨hs1.2.1, ptSlotMemAccWf _ _ _ hs1⟩
    · exact ⟨hs0.2.1, ptSlotMemAccWf _ _ _ hs0⟩
  obtain ⟨⟨hr1, -⟩, hacc⟩ := hram
  rw [accWfByte b 8 j hacc hj]
  unfold WeakInterp.accAddr paZ
  simp only [ramBase] at hr1
  omega

/-- The slot bytes ARE in the confined map (deviation 4: `∈ dom` ↦ `isSome`). -/
theorem wwalkWinConf (σ : Wmstate) (l : List PAddr) (b v : BitVec 64) :
    WeakWalkEff.ptSlotMem (wflatSt σ) b v → b ∈ l →
    ∀ j : Nat, j < 8 → (wmemRestrict σ (accWin l 8) (b + BitVec.ofNat 64 j)).isSome = true := by
  rintro ⟨hb, -⟩ hbl j hj
  rw [wmemRestrictLookup σ _ _ (nthByte (n := 8) v j) (accWinIn l 8 b j hbl hj) (hb j hj)]
  rfl

/-! ### 4b. The traces of the walk, classified -/

/-- Rocq `wwalk_ev_ok` (deviation 5: a read is also not an i-cache read). -/
def wwalkEvOk (a2 a1 la : PAddr) : Weff → Prop
  | .WEread ak pa n => ak.akIfetch = false ∧ n = 8 ∧ (pa = a2 ∨ pa = a1 ∨ pa = la)
  | .WEwrite _ pa n _ => n = 8 ∧ pa = la
  | .WEbar _ => True

/-- Rocq's `walk_evs` (Lean-only tactic). -/
macro "wwalk_evs" : tactic => `(tactic| (simp [wwalkEvOk, wakPlain, wakExcl]))

theorem traceRdomOfEvs (σ : Wmstate) (a2 a1 la p2 p1 lw : BitVec 64) (es : List Weff) :
    (∀ e, e ∈ es → wwalkEvOk a2 a1 la e) →
    WeakWalkEff.ptSlotMem (wflatSt σ) a2 p2 →
    WeakWalkEff.ptSlotMem (wflatSt σ) a1 p1 →
    WeakWalkEff.ptSlotMem (wflatSt σ) la lw →
    traceRdom (wmemRestrict σ (accWin [a2, a1, la] 8)) es := by
  intro hall hs2 hs1 hs0 ak pa n hin j hj
  obtain ⟨-, rfl, h⟩ := hall _ hin
  rcases h with rfl | rfl | rfl
  · exact wwalkWinConf σ _ _ p2 hs2 (by simp) j hj
  · exact wwalkWinConf σ _ _ p1 hs1 (by simp) j hj
  · exact wwalkWinConf σ _ _ lw hs0 (by simp) j hj

theorem traceWdomOfEvs (a2 a1 la : PAddr) (es : List Weff) :
    (∀ e, e ∈ es → wwalkEvOk a2 a1 la e) →
    traceWdom (accWin [a2, a1, la] 8) es := by
  intro hall ak pa n v hin j hj
  obtain ⟨rfl, rfl⟩ := hall _ hin
  exact wwalkSlotsIn0 a2 a1 _ j hj

/-- Lean-only: a trace without i-cache reads is `fetchFresh`. -/
theorem WeakKptStale.fetchFreshNoIfetch (es : List Weff) :
    (∀ (ak : AkInfo) (pa : PAddr) (n : Nat), Weff.WEread ak pa n ∈ es → ak.akIfetch = false) →
    fetchFresh es := by
  induction es with
  | nil => intro; trivial
  | cons e es ih =>
    intro h
    refine ⟨fun ak pa n hin hif => ?_, ih (fun ak pa n hin => h ak pa n (List.mem_cons_of_mem _ hin))⟩
    rw [h ak pa n (List.mem_cons_of_mem _ hin)] at hif
    cases hif

/-- Pinnedness off the window: the two POINTER slots are pinned; the leaf read is exempt. -/
theorem tracePinOffOfEvs (σ : Wmstate) (a2 a1 la : PAddr) (es : List Weff) :
    (∀ e, e ∈ es → wwalkEvOk a2 a1 la e) →
    (∀ j : Nat, j < 8 →
      pinnedRead σ (WeakInterp.accAddr a2 j) ∧ pinnedRead σ (WeakInterp.accAddr a1 j)) →
    tracePinOff σ la 8 es := by
  intro hall hpin
  refine ⟨fun ak pa n hin _ hdisj j hj => ?_, WeakKptStale.fetchFreshNoIfetch es
    (fun ak pa n hin => (hall _ hin).1)⟩
  obtain ⟨hif, rfl, h⟩ := hall _ hin
  simp only [readPinned, hif, Bool.false_eq_true, ↓reduceIte]
  rcases h with rfl | rfl | rfl
  · exact (hpin j hj).1
  · exact (hpin j hj).2
  · exact absurd hdisj (raccDisjIrrefl _ 8 (by decide))

/-- The five shapes the STALE producer accepts. -/
theorem traceStaleWalkShapes (a2 a1 la : PAddr) (lw' : BitVec 64) (es : List Weff) :
    raccDisj la 8 a2 8 → raccDisj la 8 a1 8 →
    (es = [] ∨
     es = [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8] ∨
     es = [.WEread wakExcl la 8] ∨
     es = [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8, .WEread wakExcl la 8] ∨
     es = [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8, .WEread wakExcl la 8,
           .WEwrite wakExcl la 8 lw']) →
    traceStale wakPlain la 8 es := by
  rintro hd2 hd1 (rfl | rfl | rfl | rfl | rfl)
  · trivial
  · exact Or.inr (Or.inl ⟨rfl, hd2, Or.inr (Or.inl ⟨rfl, hd1, Or.inr (Or.inr ⟨rfl, rfl, rfl,
      traceOffWinPinned _ _ _ (by walk_stale_trace)⟩)⟩)⟩)
  · exact Or.inl ⟨rfl, trivial⟩
  · exact Or.inr (Or.inl ⟨rfl, hd2, Or.inr (Or.inl ⟨rfl, hd1, Or.inr (Or.inr ⟨rfl, rfl, rfl,
      traceOffWinPinned _ _ _ (by walk_stale_trace)⟩)⟩)⟩)
  · exact Or.inr (Or.inl ⟨rfl, hd2, Or.inr (Or.inl ⟨rfl, hd1, Or.inr (Or.inr ⟨rfl, rfl, rfl,
      traceOffWinPinned _ _ _ (by walk_stale_trace)⟩)⟩)⟩)

/-! ### 4c. ROUTE A: the stale producer, for any family of walk-shaped runs -/

theorem wstepOkRacyTrueOfWalkFamily (tid : Option Nat) (σ : Wmstate) (a2 a1 la p2 p1 w0 lw : BitVec 64)
    {X : Type} (m : SailM X) :
    wlogWf σ.wmLog →
    WeakWalkEff.ptSlotMem (wflatSt σ) a2 p2 →
    WeakWalkEff.ptSlotMem (wflatSt σ) a1 p1 →
    WeakWalkEff.ptSlotMem (wflatSt σ) la lw →
    (∀ j : Nat, j < 8 →
      pinnedRead σ (WeakInterp.accAddr a2 j) ∧ pinnedRead σ (WeakInterp.accAddr a1 j)) →
    (∃ a d : BitVec 1, lw = pteSetAD w0 a d) →
    (∀ av dv : BitVec 1, pteAdLe (pteSetAD w0 av dv) lw →
      ∃ (x : X) (sg' : ExecSt) (es : List Weff),
        execStale la 8 (pteSetAD w0 av dv) m (wflatSt σ) = some (x, sg', es) ∧
        (∀ e, e ∈ es → wwalkEvOk a2 a1 la e) ∧
        traceStale wakPlain la 8 es) →
    wstepOkRacy tid la 8 wakPlain (wwalkFilter w0 lw) wDAny True true m σ := by
  intro hwf hs2 hs1 hs0 hpin hvar hfam
  have hwf0 := ptSlotMemAccWf _ _ _ hs0
  have hW0 := wwalkWinNonzero (wflatSt σ) a2 a1 la p2 p1 lw hs2 hs1 hs0
  refine wstepOkRacyTrueOfStaleWindow tid la 8 wakPlain (wwalkFilter w0 lw) True m σ (accWin [a2, a1, la] 8)
    hwf0 (by decide) rfl ⟨lw, lw, rfl, hvar, pteAdLeRefl lw⟩ hwf hW0 (fun j hj => wwalkSlotsIn0 a2 a1 la j hj)
    ?_
  rintro w ⟨wv, hbs, ⟨a, d, hwv⟩, hle⟩
  have hweq : w = wv := bvEqOfBytes (n := 8) w wv (fun j _ => congrFun hbs j)
  subst hweq
  subst hwv
  obtain ⟨x, sg', es, hrun, hev, hst⟩ := hfam a d hle
  obtain ⟨t'', hrun'', -, -, -, hdom''⟩ := execStaleRestrict la 8 (pteSetAD w0 a d) m (wflatSt σ)
    (wmemRestrict σ (accWin [a2, a1, la] 8)) (accWin [a2, a1, la] 8) x sg' es hrun (wmemRestrictSub σ _)
    (wmemRestrictDom σ _) (traceRdomOfEvs σ a2 a1 la p2 p1 lw es hev hs2 hs1 hs0) (traceWdomOfEvs a2 a1 la es hev)
  exact ⟨x, t'', es, hrun'', hdom'', tracePinOffOfEvs σ a2 a1 la es hev hpin, hst⟩

/-! ### 4d. THE PEEL -/

/-- Rocq `wwalk_peel_of_exports` (deviation 6: the collapse premise is the absorption
theorem's, for non-i-cache reads). -/
theorem wwalkPeelOfExports (acc : MemoryAccessType mem_payload) (tid : Option Nat) (σ : Wmstate)
    (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64) :
    let vpn := WeakKpt.svpnOf va
    let a2 := uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)
    let a1 := uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    (∃ a d : BitVec 1, lw = pteSetAD w0 a d) →
    wlogWf σ.wmLog →
    WeakWalkEff.ptSlotMem (wflatSt σ) a2 p2 →
    WeakWalkEff.ptSlotMem (wflatSt σ) a1 p1 →
    WeakWalkEff.ptSlotMem (wflatSt σ) la lw →
    (∀ j : Nat, j < 8 →
      pinnedRead σ (WeakInterp.accAddr a2 j) ∧ pinnedRead σ (WeakInterp.accAddr a1 j)) →
    raccDisj la 8 a2 8 →
    raccDisj la 8 a1 8 →
    (∀ (rak : AkInfo) (wv : BitVec (8 * 8)), rak.akIfetch = false → wadm σ rak la 8 wv →
      (∃ a d : BitVec 1, wv = pteSetAD w0 a d) ∧ pteAdLe wv lw) →
    ( -- READ-ONLY
      (∀ av dv : BitVec 1, pteAdLe (pteSetAD w0 av dv) lw →
        ∃ (sg' : ExecSt) (es : List Weff),
          execStale la 8 (pteSetAD w0 av dv) (translateAddr (.Virtaddr va) acc) (wflatSt σ) =
            some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', es) ∧
          sg'.mem = wflatMem σ.wmImg σ.wmLog ∧
          sg'.dev = σ.wmDev ∧
          (es = [] ∨
           es = [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8] ∨
           es = [.WEread wakExcl la 8] ∨
           es = [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8,
                 .WEread wakExcl la 8])) ∨
      -- WRITE-BACK
      (∃ (lw' : BitVec 64) (wtr : Bool),
        update_PTE_Bits lw acc = some lw' ∧
        ∀ av dv : BitVec 1, pteAdLe (pteSetAD w0 av dv) lw →
          ∃ (sg' : ExecSt) (es : List Weff),
            execStale la 8 (pteSetAD w0 av dv) (translateAddr (.Virtaddr va) acc) (wflatSt σ) =
              some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', es) ∧
            sg'.mem = bmWrite (wflatMem σ.wmImg σ.wmLog) la 8 lw' ∧
            sg'.dev = σ.wmDev ∧
            es = (if wtr then
                    [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8,
                     .WEread wakExcl la 8, .WEwrite wakExcl la 8 lw']
                  else [.WEread wakExcl la 8, .WEwrite wakExcl la 8 lw']))) →
    wstepOkRacy tid la 8 wakPlain (wwalkFilter w0 lw) wDAny True true (translateAddr (.Virtaddr va) acc) σ ∧
    wadmFilter σ wakPlain la 8 (wwalkFilter w0 lw) := by
  intro vpn a2 a1 la hvar hwf hs2 hs1 hs0 hpin hd2 hd1 hcoll harm
  have hwf0 := ptSlotMemAccWf _ _ _ hs0
  refine ⟨?_, fun wv hadm => ⟨wv, rfl, hcoll wakPlain wv rfl hadm⟩⟩
  rcases harm with hro | ⟨lw', wtr, -, hfam⟩
  · -- READ-ONLY: all four shapes are stale-friendly
    refine wstepOkRacyTrueOfWalkFamily tid σ a2 a1 la p2 p1 w0 lw _ hwf hs2 hs1 hs0 hpin hvar
      (fun av dv hle => ?_)
    obtain ⟨sg', es, hrun, -, -, hes⟩ := hro av dv hle
    refine ⟨_, sg', es, hrun, ?_, traceStaleWalkShapes a2 a1 la lw es hd2 hd1 ?_⟩
    · rcases hes with rfl | rfl | rfl | rfl <;> wwalk_evs
    · rcases hes with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · cases wtr with
    | true =>
      -- MISS write-back: the five-event walk, still stale-friendly
      refine wstepOkRacyTrueOfWalkFamily tid σ a2 a1 la p2 p1 w0 lw _ hwf hs2 hs1 hs0 hpin hvar
        (fun av dv hle => ?_)
      obtain ⟨sg', es, hrun, -, -, hes⟩ := hfam av dv hle
      simp only [↓reduceIte] at hes
      refine ⟨_, sg', es, hrun, by rw [hes]; wwalk_evs, traceStaleWalkShapes a2 a1 la lw' es hd2 hd1
        (Or.inr (Or.inr (Or.inr (Or.inr hes))))⟩
    | false =>
      -- HIT write-back: the ORDINARY route (the family is constant: one member carries it)
      obtain ⟨ad, dd, hlw⟩ := hvar
      have hle0 : pteAdLe (pteSetAD w0 ad dd) lw := by rw [← hlw]; exact pteAdLeRefl lw
      obtain ⟨sg', es, hrun, -, -, hes⟩ := hfam ad dd hle0
      simp only [Bool.false_eq_true, ↓reduceIte] at hes
      have hev : ∀ e, e ∈ es → wwalkEvOk a2 a1 la e := by rw [hes]; wwalk_evs
      have hoff : traceOffWin la 8 es := by
        rw [hes]; exact traceOffWinPinned _ _ _ (by walk_stale_trace)
      have hpoff := tracePinOffOfEvs σ a2 a1 la es hev hpin
      obtain ⟨t'', hrun'', -, -, -, hdom''⟩ := execStaleRestrict la 8 (pteSetAD w0 ad dd)
        (translateAddr (.Virtaddr va) acc) (wflatSt σ) (wmemRestrict σ (accWin [a2, a1, la] 8))
        (accWin [a2, a1, la] 8) _ sg' es hrun (wmemRestrictSub σ _) (wmemRestrictDom σ _)
        (traceRdomOfEvs σ a2 a1 la p2 p1 lw es hev hs2 hs1 hs0) (traceWdomOfEvs a2 a1 la es hev)
      apply wstepOkRacyPhaseMono
      apply wstepOkRacyFalseOfWstepOk
      exact (wstepEffConfinedPin tid (translateAddr (.Virtaddr va) acc) σ (wmemRestrict σ (accWin [a2, a1, la] 8))
        (accWin [a2, a1, la] 8) _ t'' es hwf (wwalkWinNonzero (wflatSt σ) a2 a1 la p2 p1 lw hs2 hs1 hs0)
        (tracePinOfOffWin σ la 8 es hoff hpoff) (wmemRestrictDom σ _) (wmemRestrictSub σ _) hdom''
        (execEffOfExecStale la 8 _ _ hwf0 _ _ _ _ hrun'' hoff)).1

end Weak
