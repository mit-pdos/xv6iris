/-
Weak: **the unmap-side prototype -- pinnedness from delivery, and the fault it licenses**.

Rocq: `iris/WkUnmapMp.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `WkClipAdvance` is the pessimistic half (after `uvmunmap`'s
`*pte = 0` every RACILY observable value of the slot is an A/D variant of zero).  THIS file is
the optimistic half, the one the real xv6 argument runs on: ONCE THE ZERO STORE HAS BEEN
DELIVERED to a hart (its read floor `wVrNew` covers the store's timestamp) AND NOTHING HAS
WRITTEN THE SLOT SINCE, THE SLOT IS PINNED for that hart, and its walk needs no racy machinery.

1. `wunmapLatestTs` / `wunmapPinned` / `wunmapPinnedLast` / `wunmapPinnedAndFaults` -- under the
   log shape `(log ++ [wwriteMsg … la 8 z]) ++ rest` with `rest` writing no window byte, the
   unmap write IS `latestTs` of every window byte (via `latestTsEq`, `wwinInstallLogByte`,
   `wwinInstallPrefix`, `wreinstallInstall`), so delivery is literally `pinnedRead`; with
   `wclipUnmapFaults` the leaf read is both NON-RACY and FAULTING.
2. `wunmapTranslateFaultsEff` / `wunmapWalkFaultsEff` -- the fault at the instrumented
   interpreter, over an abstract `sg` with `ptSlotMem` premises, the leaf slot holding
   `pteSetAD 0 a d`: `translate` (via `execEffTranslatePtBlocksL0`) and the `translateAddr`
   front (via `execEffTranslateAddrPtFrontErr`); state unchanged, trace the three plain reads.
   The fault arm needs no `misa`/`menvcfg`/write-side PMP/PMA premises.
3. `wakPlainNotPinning` / `wtracePinThreeReads` / `wunmapNoRacyNeeded` / `wunmapWalkTracePin` --
   the `tracePin` side condition of the ORDINARY certification for the fault walk's trace: the
   two pointer slots pinned by premise, the leaf window by §1.  No `WeakRacy` obligation.

The Iris MP handoff (release/acquire raising the resuming hart's floor over the store) is NOT
here (as in Rocq).

**Deviations from Rocq.**

1. Vocabulary as `Weak/WkClipAdvance.lean` deviation 1 and `Weak/WeakKpt.lean` deviation 1
   (`S (length log)` ↦ `log.length + 1`, `wm_log σ` ↦ `σ.wmLog`, `w_vrNew (wm_ws σ)` ↦
   `σ.wmWs.wVrNew`, `acc_addr` ↦ `WeakInterp.accAddr`, `mword_of_int 0` ↦ `0#64`/`0#16`,
   `register_lookup r sg.(sregs)` ↦ `sg.regs r`, `svpn_of` ↦ `WeakKpt.svpnOf`,
   `pma_allows_pte_read` ↦ `WeakKpt.pmaAllowsPteRead`, `pt_slot_mem` ↦ `WeakWalkEff.ptSlotMem`,
   `subrange_vec_dec v hi lo` ↦ `Sail.BitVec.extractLsb v hi lo`, `tt` ↦ `()`, the PMP premises
   in `wptReadPteSlot`'s spelling).  Section `WkUnmapWalk`'s context `acc p` are theorem
   arguments.
2. O2: `wunmapPinnedAndFaults` takes `rak.akIfetch = false` (just before the cover premise),
   inherited from `wclipUnmapFaults` (`WeakKpt` deviation 2).
3. O2: Lean's `tracePin` is `readPinned` on non-self-pinning reads plus `fetchFresh`; the
   statements are unchanged -- `readPinned σ wakPlain = pinnedRead σ` and `fetchFresh` holds
   vacuously (no i-cache read in the trace), discharged inside `wtracePinThreeReads`.
4. The trace of `wunmapTranslateFaultsEff` is the literal three-read list (the
   `es2 ++ (es1 ++ es0)` of `execEffTranslatePtBlocksL0` at singletons, definitionally).
5. Rocq's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `wunmap_latest_ts` `wunmapLatestTs`; `wunmap_pinned`
`wunmapPinned`; `wunmap_pinned_last` `wunmapPinnedLast`; `wunmap_pinned_and_faults`
`wunmapPinnedAndFaults`; `wunmap_translate_faults_eff` `wunmapTranslateFaultsEff`;
`wunmap_walk_faults_eff` `wunmapWalkFaultsEff`; `wak_plain_not_pinning` `wakPlainNotPinning`;
`wtrace_pin_three_reads` `wtracePinThreeReads`; `wunmap_no_racy_needed` `wunmapNoRacyNeeded`;
`wunmap_walk_trace_pin` `wunmapWalkTracePin`.  (None is a duplicated Rocq name.)

**Dropped:** nothing -- all 10 Rocq lemmas are ported; no Lean-only declarations.
-/
import Weak.WkClipAdvance

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail
open LeanRV64D LeanRV64D.Functions

/-! ## 1. Pinnedness from delivery -/

/-- §1a: the unmap write is the latest writer of each window byte. -/
theorem wunmapLatestTs (σ : Wmstate) (la : PAddr) (log rest : List Wmsg)
    (tid : Option Nat) (kcls : WmClass) (z : BitVec (8 * 8)) (j : Nat) :
    σ.wmLog = (log ++ [wwriteMsg tid kcls la 8 z]) ++ rest →
    (∀ (i : Nat) (m : Wmsg),
       σ.wmLog[i]? = some m → log.length + 1 ≤ i →
       ∀ j : Nat, j < 8 → msgByte m (WeakInterp.accAddr la j) = none) →
    j < 8 →
    latestTs σ.wmLog (WeakInterp.accAddr la j) = log.length + 1 := by
  intro hlog hno hj
  apply latestTsEq (wimg σ) σ.wmLog (WeakInterp.accAddr la j) (log.length + 1)
  refine ⟨?_, ?_⟩
  · -- (i) the write's timestamp holds a value for byte `j`
    apply wwinInstallLogByte (wimg σ) σ.wmLog (log.length + 1) la j hj
    exact wwinInstallPrefix _ σ.wmLog (log.length + 1) la (wreinstallInstall tid kcls la log z)
      (by rw [hlog]; exact ⟨rest, rfl⟩)
  · -- (ii) nothing strictly above it writes byte `j`
    rintro ⟨t, hlo, -, m, hm, hs⟩
    obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
    rw [Nat.add_sub_cancel] at hm
    rw [hno i m hm (by omega) j hj] at hs
    simp at hs

/-- §1b: THE PINNEDNESS -- delivery plus "nobody wrote since" is the whole hypothesis. -/
theorem wunmapPinned (σ : Wmstate) (la : PAddr) (log rest : List Wmsg)
    (tid : Option Nat) (kcls : WmClass) (z : BitVec (8 * 8)) :
    σ.wmLog = (log ++ [wwriteMsg tid kcls la 8 z]) ++ rest →
    (∀ (i : Nat) (m : Wmsg),
       σ.wmLog[i]? = some m → log.length + 1 ≤ i →
       ∀ j : Nat, j < 8 → msgByte m (WeakInterp.accAddr la j) = none) →
    log.length + 1 ≤ σ.wmWs.wVrNew →
    ∀ j : Nat, j < 8 → pinnedRead σ (WeakInterp.accAddr la j) := by
  intro hlog hno hcov j hj
  unfold pinnedRead
  rw [wunmapLatestTs σ la log rest tid kcls z j hlog hno hj]
  omega

/-- The `rest = []` instance (the read immediately after delivery). -/
theorem wunmapPinnedLast (σ : Wmstate) (la : PAddr) (log : List Wmsg)
    (tid : Option Nat) (kcls : WmClass) (z : BitVec (8 * 8)) :
    σ.wmLog = log ++ [wwriteMsg tid kcls la 8 z] →
    log.length + 1 ≤ σ.wmWs.wVrNew →
    ∀ j : Nat, j < 8 → pinnedRead σ (WeakInterp.accAddr la j) := by
  intro hlog hcov
  apply wunmapPinned σ la log [] tid kcls z (by rw [hlog, List.append_nil]) _ hcov
  intro i m hi hge j hj
  exfalso
  have := lookup_lt_Some hi
  rw [hlog] at this
  simp at this
  omega

/-- THE HEADLINE OF §1: after delivery the slot is pinned AND every admissible (non-fetch) read
of it is an invalid PTE (deviation 2). -/
theorem wunmapPinnedAndFaults (σ : Wmstate) (rak : AkInfo) (la : PAddr)
    (log : List Wmsg) (tid : Option Nat) (kcls : WmClass) (z : BitVec (8 * 8)) :
    z = 0#64 →
    σ.wmLog = log ++ [wwriteMsg tid kcls la 8 z] →
    rak.akIfetch = false →
    log.length + 1 ≤ σ.wmWs.wVrNew →
    (∀ j : Nat, j < 8 → pinnedRead σ (WeakInterp.accAddr la j)) ∧
    (∀ w : BitVec (8 * 8), wadm σ rak la 8 w → wpteInvalid w) := by
  intro hz hlog hif hcov
  exact ⟨wunmapPinnedLast σ la log tid kcls z hlog hcov,
    fun w hadm => wclipUnmapFaults σ rak la log tid kcls z w hz hlog hif hcov hadm⟩

/-! ## 2. The fault at the instrumented interpreter -/

/-- §2a: the `translate`-level fault over an abstract `sg`; state UNCHANGED, trace the three
plain PTE reads in walk order. -/
theorem wunmapTranslateFaultsEff (acc : MemoryAccessType mem_payload) (p : Privilege)
    (root : BitVec 44) (vpn : BitVec 27) (p2 p1 : BitVec 64) (a0 d0 : BitVec 1)
    (mxr dosum : Bool) (sg : ExecSt) :
    wpteValid p2 → ptePtr p2 →
    wpteValid p1 → ptePtr p1 →
    WeakWalkEff.ptSlotMem sg (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) p2 →
    WeakWalkEff.ptSlotMem sg (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) p1 →
    WeakWalkEff.ptSlotMem sg (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))
      (pteSetAD 0#64 a0 d0) →
    execEff (lookup_TLB 39 0#16 vpn) sg = some (none, sg, []) →
    sg.regs .htif_tohost_base = none →
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (sg.regs .pmpcfg_n)[0]!) = .TOR →
    zopz0zKzJ_u (zeros (n := 64)) (sg.regs .pmpaddr_n)[0]! = false →
    (_get_Pmpcfg_ent_R (sg.regs .pmpcfg_n)[0]! == 1#1) = true →
    ramEnd ≤ (sg.regs .pmpaddr_n)[0]!.toNat * 4 →
    WeakKpt.pmaAllowsPteRead (sg.regs .pma_regions) →
    execEff (translate 39 0#16 root vpn acc p mxr dosum ()) sg =
      some (.Err (.PTW_Invalid_PTE (), ()), sg,
        [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8,
         .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8,
         .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8]) := by
  intro hv2 hn2 hv1 hn1 hsm2 hsm1 hsm0 hlk hhtif hA hord hR hcov hpmar
  obtain ⟨region2, hm2, hs2⟩ := hpmar _ hsm2.2.1
  obtain ⟨region1, hm1, hs1⟩ := hpmar _ hsm1.2.1
  obtain ⟨region0, hm0, hs0⟩ := hpmar _ hsm0.2.1
  have hrd2 := wptReadPteSlot sg _ p2 region2 hsm2 hA hord hR hcov hm2 hs2 hhtif
  have hrd1 := wptReadPteSlot sg _ p1 region1 hsm1 hA hord hR hcov hm1 hs1 hhtif
  have hrd0 := wptReadPteSlot sg _ _ region0 hsm0 hA hord hR hcov hm0 hs0 hhtif
  exact execEffTranslatePtBlocksL0 acc p mxr dosum vpn root p2 p1 (pteSetAD 0#64 a0 d0) _ _ _ sg
    hrd2 hv2 hn2 hrd1 hv1 hn1 hrd0 (pteSetAdZeroInvalid a0 d0) hlk

/-- §2b: ... and the same at the `translateAddr` front (`vpn = WeakKpt.svpnOf va`, so the
front's `hvpn` is `rfl`; the exception word `e` is a caller premise, as on the SC side). -/
theorem wunmapWalkFaultsEff (acc : MemoryAccessType mem_payload) (p : Privilege)
    (root : BitVec 44) (va satp0 : BitVec 64) (p2 p1 : BitVec 64) (a0 d0 : BitVec 1)
    (e : ExceptionType) (sg : ExecSt) :
    let vpn := WeakKpt.svpnOf va
    wpteValid p2 → ptePtr p2 →
    wpteValid p1 → ptePtr p1 →
    WeakWalkEff.ptSlotMem sg (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) p2 →
    WeakWalkEff.ptSlotMem sg (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) p1 →
    WeakWalkEff.ptSlotMem sg (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))
      (pteSetAD 0#64 a0 d0) →
    execEff (lookup_TLB 39 0#16 vpn) sg = some (none, sg, []) →
    sg.regs .htif_tohost_base = none →
    sg.regs .cur_privilege = p →
    execEff (translationMode p) sg = some (.Sv39, sg, []) →
    execEff (effectivePrivilege acc (sg.regs .mstatus) p) sg = some (p, sg, []) →
    execEff (is_shadow_stack_access acc) sg = some (false, sg, []) →
    sg.regs .satp = satp0 →
    BitVec.setWidth 44 (satp_to_ppn satp0) = root →
    zero_extend (m := 16) (satp_to_asid satp0) = 0#16 →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (sg.regs .pmpcfg_n)[0]!) = .TOR →
    zopz0zKzJ_u (zeros (n := 64)) (sg.regs .pmpaddr_n)[0]! = false →
    (_get_Pmpcfg_ent_R (sg.regs .pmpcfg_n)[0]! == 1#1) = true →
    ramEnd ≤ (sg.regs .pmpaddr_n)[0]!.toNat * 4 →
    WeakKpt.pmaAllowsPteRead (sg.regs .pma_regions) →
    execEff (translationException acc (.PTW_Invalid_PTE ())) sg = some (e, sg, []) →
    execEff (translateAddr (.Virtaddr va) acc) sg =
      some (.Err (e, ()), sg,
        [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8,
         .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8,
         .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8]) := by
  intro vpn hv2 hn2 hv1 hn1 hsm2 hsm1 hsm0 hlk hhtif hcp htm heff hss hsatp hppn hasid hcanon
    hA hord hR hcov hpmar hte
  exact execEffTranslateAddrPtFrontErr acc p vpn root (.PTW_Invalid_PTE ()) e satp0 va _ sg
    heff hss hcp htm hsatp hppn hasid hcanon rfl
    (fun mxr dosum => wunmapTranslateFaultsEff acc p root vpn p2 p1 a0 d0 mxr dosum sg
      hv2 hn2 hv1 hn1 hsm2 hsm1 hsm0 hlk hhtif hA hord hR hcov hpmar) hte

/-! ## 3. The pinned-reads corollary -- "no racy machinery needed" -/

/-- `wakPlain` does not pin itself -- the reason §3 has any content. -/
theorem wakPlainNotPinning : akPins wakPlain = false := rfl

/-- §3a: three plain 8-byte reads at pinned windows satisfy `tracePin` (deviation 3). -/
theorem wtracePinThreeReads (σ : Wmstate) (b2 b1 b0 : PAddr) :
    (∀ j : Nat, j < 8 → pinnedRead σ (WeakInterp.accAddr b2 j)) →
    (∀ j : Nat, j < 8 → pinnedRead σ (WeakInterp.accAddr b1 j)) →
    (∀ j : Nat, j < 8 → pinnedRead σ (WeakInterp.accAddr b0 j)) →
    tracePin σ [.WEread wakPlain b2 8, .WEread wakPlain b1 8, .WEread wakPlain b0 8] := by
  intro hb2 hb1 hb0
  -- every read of the trace is a `wakPlain` one
  have hplain : ∀ (ak : AkInfo) (pa : PAddr) (n : Nat),
      Weff.WEread ak pa n ∈ [Weff.WEread wakPlain b2 8, .WEread wakPlain b1 8, .WEread wakPlain b0 8] →
      ∃ b, ak = wakPlain ∧ pa = b ∧ n = 8 ∧ ∀ k : Nat, k < 8 → pinnedRead σ (WeakInterp.accAddr b k) := by
    intro ak pa n hin
    rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hin
    rcases hin with h | h | h <;> (injection h with h1 h2 h3; subst h1 h2 h3)
    · exact ⟨_, rfl, rfl, rfl, hb2⟩
    · exact ⟨_, rfl, rfl, rfl, hb1⟩
    · exact ⟨_, rfl, rfl, rfl, hb0⟩
  -- `fetchFresh` is vacuous on a trace without i-cache reads
  have hff : ∀ es : List Weff,
      (∀ (ak : AkInfo) (pa : PAddr) (n : Nat), Weff.WEread ak pa n ∈ es → ak.akIfetch = false) →
      fetchFresh es := by
    intro es
    induction es with
    | nil => intro _; trivial
    | cons e es ih =>
      intro h
      refine ⟨fun ak pa n hin hif => ?_, ih (fun ak pa n hin => h ak pa n (List.mem_cons_of_mem _ hin))⟩
      have := h ak pa n (List.mem_cons_of_mem _ hin)
      rw [hif] at this
      exact absurd this (by decide)
  refine ⟨?_, hff _ ?_⟩
  · intro ak pa n hin _ j hj
    obtain ⟨b, rfl, rfl, rfl, hb⟩ := hplain ak pa n hin
    show pinnedRead σ _
    exact hb j hj
  · intro ak pa n hin
    obtain ⟨b, rfl, -, -, -⟩ := hplain ak pa n hin
    rfl

/-- §3b: THE COROLLARY tying §1 to §2's trace: the fault walk's three plain reads satisfy the
ORDINARY certification's pinnedness side condition. -/
theorem wunmapNoRacyNeeded (σ : Wmstate) (b2 b1 la : PAddr)
    (log rest : List Wmsg) (tid : Option Nat) (kcls : WmClass) (z : BitVec (8 * 8)) :
    σ.wmLog = (log ++ [wwriteMsg tid kcls la 8 z]) ++ rest →
    (∀ (i : Nat) (m : Wmsg),
       σ.wmLog[i]? = some m → log.length + 1 ≤ i →
       ∀ j : Nat, j < 8 → msgByte m (WeakInterp.accAddr la j) = none) →
    log.length + 1 ≤ σ.wmWs.wVrNew →
    (∀ j : Nat, j < 8 → pinnedRead σ (WeakInterp.accAddr b2 j)) →
    (∀ j : Nat, j < 8 → pinnedRead σ (WeakInterp.accAddr b1 j)) →
    tracePin σ [.WEread wakPlain b2 8, .WEread wakPlain b1 8, .WEread wakPlain la 8] := by
  intro hlog hno hcov hp2 hp1
  exact wtracePinThreeReads σ b2 b1 la hp2 hp1 (wunmapPinned σ la log rest tid kcls z hlog hno hcov)

/-- The same, spelled at §2's slot addresses, so the two halves visibly compose. -/
theorem wunmapWalkTracePin (σ : Wmstate) (root : BitVec 44) (vpn : BitVec 27) (p2 p1 : BitVec 64)
    (log rest : List Wmsg) (tid : Option Nat) (kcls : WmClass) (z : BitVec (8 * 8)) :
    σ.wmLog = (log ++ [wwriteMsg tid kcls
                        (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 z]) ++ rest →
    (∀ (i : Nat) (m : Wmsg),
       σ.wmLog[i]? = some m → log.length + 1 ≤ i →
       ∀ j : Nat, j < 8 →
         msgByte m (WeakInterp.accAddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) j) =
           none) →
    log.length + 1 ≤ σ.wmWs.wVrNew →
    (∀ j : Nat, j < 8 →
       pinnedRead σ (WeakInterp.accAddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) j)) →
    (∀ j : Nat, j < 8 →
       pinnedRead σ (WeakInterp.accAddr (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) j)) →
    tracePin σ
      [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8,
       .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8,
       .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8] := by
  intro hlog hno hcov hp2 hp1
  exact wunmapNoRacyNeeded σ _ _ _ log rest tid kcls z hlog hno hcov hp2 hp1

end Weak
