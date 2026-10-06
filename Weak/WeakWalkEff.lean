/-
Weak: **the page-walk effect certificate** (M4 batch 6a): the Sv39 page-table-walk
READ cone at `execEff` -- the S-mode PTE read, the three-level walk (success and
faults), the TLB lookup/fill/hit, the `translate` dispatch and the `translateAddr`
front heads, every statement with its EXACT trace.

Rocq: `iris/WeakWalkEff.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The mirror of `CommonWalk`'s 3-level walk core,
`SmodePte`'s checked 8-byte PTE read, `PtTree` §8's abstract-word translate layer and
`PtTreeAdue` §5's `translateAddr` front heads (Lean SC twins: `Weak/ExecSC2/3/4/6/9`),
at the instrumented interpreter `WeakCert.execEff`.  Parametric over the access type
and the privilege; the leaf word is abstract (A/D enter only through the hypotheses).
A walk's weak-memory effect is its PTE reads and nothing else: one `.WEread wakPlain a 8`
per level; the success walk's trace is `es2 ++ (es1 ++ es0)` over the per-level read
premises (at `wptReadPteSlot`'s singletons the literal three reads).  The TLB-hit path
and every register-only probe carry the EMPTY trace, mirrored (not detected).  SCOPE:
the `update_PTE_Bits = none` outcomes only (O1 TLB hit, O2 walk + fill) and the fault
walks; the A/D write-back arm is not mirrored.  The PTE-word probes are taken in their
`execEff` form (`wpteValid` & co.), each projecting to its SC twin.

**O2 (`notes/weak-port-o2-design.md` §1.6).**  The Lean model's `read_pte` reads with
`Read_ttw` (`checked_mem_read`'s `(.Load .PageTableEntry, false)` arm), i.e. access
kind `AK_ttw`, and `classify (.AK_ttw ()) = ⟨false, false, false⟩ = wakPlain`: the
walker's trace elements are Rocq's literally (`.WEread wakPlain a 8`).  Rocq's header
sentence "`read_pte` goes through `read_kind_of_flags` = `Read_plain`" does not hold in
Lean (deviation 2).  No fetch appears in this file.

**Deviations from Rocq.**
1. VOCABULARY as `Weak/ExecSC*.lean` and `Weak/WeakFetchEff.lean` deviation 1
   (`register_lookup r s.(sregs)` ↦ `s.regs r`, `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`,
   `vec_access_dec` ↦ `v[i]!`, `vec_update_dec` ↦ `vectorUpdate`, `uint` ↦ `toNat`,
   `Z` indices ↦ `Nat`, `tt` ↦ `()`, `mword_of_int 0` ↦ `0#16`, `autocast` ↦ the model's
   `BitVec.setWidth`, `autocast (PPN_of_PTE pte0)` ↦ `ppn0 pte0`, the byte window ↦
   `BytesAt s a 8 w`).  The walk is Lean's well-founded `pt_walk` (ExecSC9 deviation 1):
   no `Acc` argument, the `∀ g' a` sub-walk premises are `∀ g'`, the leaf record is
   `uWalkOut`.  Section variables/hypotheses are theorem arguments (each lemma takes the
   ones its Rocq twin uses); the section `Let`s `addr2/1/0` are inlined; Rocq's
   right-nested `es2 ++ es1 ++ es0` is written `es2 ++ (es1 ++ es0)`.  The two `Local
   Ltac`s (`walk_eff_peel_asserts`, `walk_eff_peel_read`) have no twin: the scripts use
   `WeakLeafEff8`'s `exec_eff_run` with `erw` at the trace-carrying steps.
2. O2 (above): the one memory step is the Lean-only `WeakWalkEff.execEffReadRamTtw8`
   (`read_ram .Read_ttw`, trace `[.WEread wakPlain addr 8]`), not Rocq's
   `exec_eff_read_ram_plain_8`.
3. `execEffCurrentlyEnabledSvnapot` is proved directly (as
   `ExecSC2.execCurrentlyEnabledSvnapot`), not through the decode bridge; `MISA_C` ↦
   `misaC`.
4. `execEffIsShadowStackUAcc` is stated over `WeakWalkEff.uAcc6`, Rocq's six-arm
   `UserPtTree.u_acc` verbatim (`ExecSC2.uAcc` keeps only three arms;
   `WeakWalkEff.uAcc6OfUAcc` converts).
5. `execEffPmpReadAddrRegVal` is `WeakPmpEff.execEffPmpReadAddrReg` (grain 0, no case
   split).  `execEffPmpCheckSupervisorGrantLoad`'s loop is lean-sail's `IntRange`
   `forIn`, its first-iteration exit `WeakWalkEff.execREffForInFirstEarly` (a copy of
   `WeakPmpTorEff`'s, which clashes with `WeakPmpEff` on `execEffPmpReadAddrReg`).
6. `PtTree` pieces not in the Lean tree are ported here, file-qualified, over
   `AxPtProt`'s `PtTree` vocabulary: `pt_slot_mem` ↦ `WeakWalkEff.ptSlotMem` (Rocq's
   `addr_is_ram a ∧ addr_is_ram (pa_add a 7)` ↦ `inRam a 8`, WeakFunnel deviation 2),
   `ptree_blocks` ↦ `WeakWalkEff.ptreeBlocks`, `pte_valid_invalid_excl` ↦
   `WeakWalkEff.pteValidInvalidExcl`, `ptree_maps_blocks_excl` ↦
   `WeakWalkEff.ptreeMapsBlocksExcl`, `uwe_match_other` ↦ `WeakWalkEff.uweMatchOther`.
   `wptReadPteSlot`'s `ram_base + ram_size ≤ uint pmpaddr0 * 4` ↦ `ramEnd ≤ … .toNat * 4`;
   its CLINT/SIG/dev side conditions come from `inRam` (`within_clint_ram`,
   `devAddrRam`).
7. §8: the Lean model's `translateAddr` tests the shadow stack after `translationMode`
   and computes `sv_width` as an `Int`; the premises keep Rocq's list and shapes
   (`BitVec.setWidth 44 (satp_to_ppn satp0) = root`, `zero_extend (m := 16)
   (satp_to_asid satp0) = 0#16`, `(va != sign_extend (m := 64) (extractLsb va 38 0)) =
   false`, `BitVec.setWidth 27 (extractLsb (extractLsb va 38 0) 38 pagesize_bits) = vpn`,
   `zero_extend (m := 64) (ppnv +++ extractLsb va (pagesize_bits - 1) 0) = pa`).  Rocq's
   unused let-binder `(f := PTW_Invalid_Addr tt)` of the non-canonical head is dropped.
8. Rocq's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `wpte_valid` `wpteValid`, `wpte_invalid` `wpteInvalid`,
`wpte_check_ok` `wpteCheckOk`, `wpte_check_denied` `wpteCheckDenied`,
`wpte_valid_pte_valid` `wpteValidPteValid`, `wpte_invalid_pte_invalid`
`wpteInvalidPteInvalid`, `wpte_check_ok_pte_check_ok` `wpteCheckOkPteCheckOk`,
`wpte_check_denied_pte_check_denied` `wpteCheckDeniedPteCheckDenied`,
`exec_eff_currentlyEnabled_Svnapot` `execEffCurrentlyEnabledSvnapot`,
`exec_eff_currentlyEnabled_Svadu` `WeakWalkEff.execEffCurrentlyEnabledSvadu` (duplicated
name), `exec_eff_architecture_Supervisor` `execEffArchitectureSupervisor`,
`exec_eff_translationMode_S_sv39` `execEffTranslationModeSSv39`,
`exec_eff_effectivePrivilege_mprv0` `execEffEffectivePrivilegeMprv0`,
`exec_eff_is_shadow_stack_u_acc` `execEffIsShadowStackUAcc`, `exec_eff_lookup_TLB_miss`
`execEffLookupTLBMiss`, `exec_eff_lookup_TLB_nomatch_s` `execEffLookupTLBNomatchS`,
`exec_eff_lookup_TLB_hit_ent` `execEffLookupTLBHitEnt`, `exec_eff_uwe_pbmt`
`execEffUwePbmt`, `exec_eff_pmpMatchAddr_TOR_match` `execEffPmpMatchAddrTORMatch`,
`exec_eff_pmpReadAddrReg_val` `execEffPmpReadAddrRegVal`,
`exec_eff_pmpCheck_supervisor_grant_load` `execEffPmpCheckSupervisorGrantLoad`,
`exec_eff_is_mag_applicable_load_pte` `execEffIsMagApplicableLoadPte`,
`exec_eff_pmaCheck_ram_pte` `execEffPmaCheckRamPte`, `exec_eff_read_pte_S`
`execEffReadPteS`, `wpt_read_pte_slot` `wptReadPteSlot`, `exec_eff_check_leaf_pte_leaf0`
`execEffCheckLeafPteLeaf0`, `exec_eff_rec_walk_leaf` `execEffRecWalkLeaf`,
`exec_eff_rec_walk_l1` `execEffRecWalkL1`, `exec_eff_pt_walk_user` `execEffPtWalkUser`,
`exec_eff_add_to_TLB_user` `execEffAddToTLBUser`, `exec_eff_translate_TLB_miss_user`
`execEffTranslateTLBMissUser`, `exec_eff_check_leaf_pte_invalid`
`execEffCheckLeafPteInvalid`, `exec_eff_check_leaf_pte_noperm0`
`execEffCheckLeafPteNoperm0`, `exec_eff_rec_walk_leaf_invalid`
`execEffRecWalkLeafInvalid`, `exec_eff_rec_walk_leaf_noperm` `execEffRecWalkLeafNoperm`,
`exec_eff_rec_walk_l1_invalid` `execEffRecWalkL1Invalid`, `exec_eff_rec_walk_l1_sub`
`execEffRecWalkL1Sub`, `exec_eff_pt_walk_user_l2_invalid` `execEffPtWalkUserL2Invalid`,
`exec_eff_pt_walk_user_sub` `execEffPtWalkUserSub`,
`exec_eff_translate_TLB_miss_user_walk_err` `execEffTranslateTLBMissUserWalkErr`,
`exec_eff_translate_miss_user` `execEffTranslateMissUser`,
`exec_eff_translate_hit_user` `execEffTranslateHitUser`,
`exec_eff_translate_TLB_hit_pt` `execEffTranslateTLBHitPt`,
`exec_eff_translate_TLB_hit_denied_pt` `execEffTranslateTLBHitDeniedPt`,
`exec_eff_translate_pt_blocks_l2/l1/l0` `execEffTranslatePtBlocksL2/L1/L0`,
`exec_eff_translate_pt_blocks` `execEffTranslatePtBlocks`,
`exec_eff_translate_pt_denied` `execEffTranslatePtDenied`, `wtlb_ok_pt_lookup_blocked`
`wtlbOkPtLookupBlocked`, `exec_eff_translateAddr_pt_front`
`execEffTranslateAddrPtFront`, `exec_eff_translateAddr_pt_front_err`
`execEffTranslateAddrPtFrontErr`, `exec_eff_translateAddr_pt_front_noncanon`
`execEffTranslateAddrPtFrontNoncanon`.  Lean-only (file-qualified):
`WeakWalkEff.uAcc6`, `WeakWalkEff.uAcc6OfUAcc`, `WeakWalkEff.execREffForInFirstEarly`,
`WeakWalkEff.execEffReadRamTtw8`, `WeakWalkEff.ptSlotMem`, `WeakWalkEff.ptreeBlocks`,
`WeakWalkEff.pteValidInvalidExcl`, `WeakWalkEff.ptreeMapsBlocksExcl`,
`WeakWalkEff.uweMatchOther`.

**Dropped:** nothing -- 4 Rocq `Definition`s + 49 `Lemma`s, all ported (53 Lean
declarations, plus the 9 Lean-only ones); the 3 section `Let`s are inlined and the 2
`Local Ltac`s replaced by `exec_eff_run` (deviation 1).
-/
import Weak.WeakFetchEff
import Weak.AxPtProt

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. The eff predicate twins and their SC projections -/

/-- Rocq `wpte_valid`. -/
def wpteValid (w : BitVec 64) : Prop :=
  ∀ s, execEff (pte_is_invalid (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0)) (ext_bits_of_PTE w)) s =
    some (false, s, [])

/-- Rocq `wpte_invalid`. -/
def wpteInvalid (w : BitVec 64) : Prop :=
  ∀ s, execEff (pte_is_invalid (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0)) (ext_bits_of_PTE w)) s =
    some (true, s, [])

/-- Rocq `wpte_check_ok`. -/
def wpteCheckOk (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool) (w : BitVec 64) :
    Prop :=
  ∀ s, execEff (check_PTE_permission acc p mxr dosum (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0))
    (ext_bits_of_PTE w) ()) s = some (.PTE_Check_Success (), s, [])

/-- Rocq `wpte_check_denied`. -/
def wpteCheckDenied (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (f : pte_check_failure) (w : BitVec 64) : Prop :=
  ∀ s, execEff (check_PTE_permission acc p mxr dosum (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0))
    (ext_bits_of_PTE w) ()) s = some (.PTE_Check_Failure ((), f), s, [])

/-- Rocq `wpte_valid_pte_valid`. -/
theorem wpteValidPteValid (w : BitVec 64) : wpteValid w → pteValid w :=
  fun h s => execEffExec _ _ _ _ _ (h s)

/-- Rocq `wpte_invalid_pte_invalid`. -/
theorem wpteInvalidPteInvalid (w : BitVec 64) : wpteInvalid w → pteInvalid w :=
  fun h s => execEffExec _ _ _ _ _ (h s)

/-- Rocq `wpte_check_ok_pte_check_ok`. -/
theorem wpteCheckOkPteCheckOk (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (w : BitVec 64) : wpteCheckOk acc p mxr dosum w → pteCheckOk acc p mxr dosum w :=
  fun h s => execEffExec _ _ _ _ _ (h s)

/-- Rocq `wpte_check_denied_pte_check_denied`. -/
theorem wpteCheckDeniedPteCheckDenied (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (f : pte_check_failure) (w : BitVec 64) :
    wpteCheckDenied acc p mxr dosum f w → pteCheckDenied acc p mxr dosum f w :=
  fun h s => execEffExec _ _ _ _ _ (h s)

/-! ## 2. The register-only probes, at the empty trace -/

/-- Rocq `exec_eff_currentlyEnabled_Svnapot` (deviation 3). -/
theorem execEffCurrentlyEnabledSvnapot (s : ExecSt) (hmisa : s.regs .misa = misaC) :
    execEff (currentlyEnabled .Ext_Svnapot) s = some (true, s, []) := by
  have hs : (_get_Misa_S (s.regs .misa) == 1#1) = true := by rw [hmisa]; decide
  have h39 : execEff (currentlyEnabled .Ext_Sv39) s = some (true, s, []) := by
    rw [currentlyEnabled]
    simp only [execEffHartSupportsSv39, ↓reduceIte, WeakLeafEffCommon.execEffCurrentlyEnabledS, hs]
  rw [currentlyEnabled]
  have hn : hartSupports .Ext_Svnapot = true := by decide +kernel
  simp only [hn, ↓reduceIte, h39]

/-- Rocq `exec_eff_currentlyEnabled_Svadu` (duplicated name). -/
theorem WeakWalkEff.execEffCurrentlyEnabledSvadu (s : ExecSt) :
    execEff (currentlyEnabled .Ext_Svadu) s = some (true, s, []) := by
  rw [currentlyEnabled]
  have : hartSupports .Ext_Svadu = true := by decide +kernel
  simp only [this, execEffReturnm]

/-- Rocq `exec_eff_architecture_Supervisor`. -/
theorem execEffArchitectureSupervisor (s : ExecSt)
    (hsxl : _get_Mstatus_SXL (s.regs .mstatus) = 2#2) :
    execEff (architecture .Supervisor) s = some (.RV64, s, []) := by
  unfold architecture
  exec_eff_run [hsxl]
  rfl

/-- Rocq `exec_eff_translationMode_S_sv39`. -/
theorem execEffTranslationModeSSv39 (satp0 : BitVec 64) (s : ExecSt)
    (hsxl : _get_Mstatus_SXL (s.regs .mstatus) = 2#2) (hsatp : s.regs .satp = satp0)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4) :
    execEff (translationMode .Supervisor) s = some (.Sv39, s, []) := by
  unfold translationMode
  simp only [show (Privilege.Supervisor == Privilege.Machine) = false from rfl, Bool.false_eq_true,
    ↓reduceIte]
  rw [execEffBindNil _ _ _ _ _ (execEffArchitectureSupervisor s hsxl)]
  exec_eff_run [hsatp, hmode]
  rfl

/-- Rocq `exec_eff_effectivePrivilege_mprv0`. -/
theorem execEffEffectivePrivilegeMprv0 (acc : MemoryAccessType mem_payload) (m : BitVec 64)
    (pr : Privilege) (s : ExecSt) (h : (_get_Mstatus_MPRV m == 1#1) = false) :
    execEff (effectivePrivilege acc m pr) s = some (pr, s, []) := by
  unfold effectivePrivilege
  simp only [h, Bool.and_false, Bool.false_eq_true, ↓reduceIte, execEffReturnm]

/-- Rocq `UserPtTree.u_acc` verbatim (Lean-only twin, deviation 4): `ExecSC2.uAcc`
keeps only the first three arms. -/
def WeakWalkEff.uAcc6 (acc : MemoryAccessType mem_payload) : Prop :=
  acc = .InstructionFetch () ∨ acc = .Load .Data ∨ acc = .Store .Data ∨
  (∃ aq rl, acc = .LoadReserved (aq, rl, .Data)) ∨
  (∃ aq rl, acc = .StoreConditional (aq, rl, .Data)) ∨
  (∃ op aq rl, acc = .Atomic (op, aq, rl, .Data, .Data))

/-- `ExecSC2.uAcc` is the first three arms of `WeakWalkEff.uAcc6` (Lean-only). -/
theorem WeakWalkEff.uAcc6OfUAcc (acc : MemoryAccessType mem_payload) (h : uAcc acc) :
    WeakWalkEff.uAcc6 acc := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

/-- Rocq `exec_eff_is_shadow_stack_u_acc` (deviation 4). -/
theorem execEffIsShadowStackUAcc (acc : MemoryAccessType mem_payload) (s : ExecSt)
    (h : WeakWalkEff.uAcc6 acc) :
    execEff (is_shadow_stack_access acc) s = some (false, s, []) := by
  rcases h with rfl | rfl | rfl | ⟨aq, rl, rfl⟩ | ⟨aq, rl, rfl⟩ | ⟨op, aq, rl, rfl⟩ <;> rfl

/-- Rocq `exec_eff_lookup_TLB_miss`. -/
theorem execEffLookupTLBMiss (vpn : BitVec 27) (asid : BitVec 16) (tlbvec : Vector (Option TLB_Entry) 64)
    (s : ExecSt) (htlb : s.regs .tlb = tlbvec) (hnone : tlbvec[tlb_hash 39 vpn]! = none) :
    execEff (lookup_TLB 39 asid vpn) s = some (none, s, []) := by
  unfold lookup_TLB
  exec_eff_run [htlb]
  rw [hnone]
  rfl

/-- Rocq `exec_eff_lookup_TLB_nomatch_s`. -/
theorem execEffLookupTLBNomatchS (vpn : BitVec 27) (asid : BitVec 16) (ent' : TLB_Entry)
    (tlbvec : Vector (Option TLB_Entry) 64) (s : ExecSt) (htlb : s.regs .tlb = tlbvec)
    (hsome : tlbvec[tlb_hash 39 vpn]! = some ent')
    (hm : match_TLB_Entry ent' asid (sign_extend (m := 57 - 12) vpn) = false) :
    execEff (lookup_TLB 39 asid vpn) s = some (none, s, []) := by
  unfold lookup_TLB
  rw [execEffBindNil _ _ _ _ _ (execEffReadReg .tlb s)]
  dsimp only
  rw [htlb, hsome]
  show execEff (if match_TLB_Entry ent' asid (sign_extend (m := 57 - 12) vpn) = true then
    pure (some (tlb_hash 39 vpn, ent')) else pure none) s = _
  rw [hm]; rfl

/-- Rocq `exec_eff_lookup_TLB_hit_ent`. -/
theorem execEffLookupTLBHitEnt (vpn : BitVec 27) (asid : BitVec 16)
    (tlbvec : Vector (Option TLB_Entry) 64) (ent : TLB_Entry) (s : ExecSt) (htlb : s.regs .tlb = tlbvec)
    (hsome : tlbvec[tlb_hash 39 vpn]! = some ent)
    (hm : match_TLB_Entry ent asid (sign_extend (m := 57 - 12) vpn) = true) :
    execEff (lookup_TLB 39 asid vpn) s = some (some (tlb_hash 39 vpn, ent), s, []) := by
  unfold lookup_TLB
  rw [execEffBindNil _ _ _ _ _ (execEffReadReg .tlb s)]
  dsimp only
  rw [htlb, hsome]
  show execEff (if match_TLB_Entry ent asid (sign_extend (m := 57 - 12) vpn) = true then
    pure (some (tlb_hash 39 vpn, ent)) else pure none) s = _
  rw [hm]; rfl

/-- Rocq `exec_eff_uwe_pbmt`. -/
theorem execEffUwePbmt (vpn : BitVec 27) (p2 p1 q0 : BitVec 64) (asid : BitVec 16) (s : ExecSt)
    (hpb : ptePbmt0 q0) :
    execEff (tlb_get_pbmt (uWalkEntry vpn p2 p1 q0 asid)) s = some (.PBMT_PMA, s, []) := by
  have hpte : (uWalkEntry vpn p2 p1 q0 asid).pte = q0 := by
    show zero_extend (m := 64) q0 = q0
    simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.setWidth_eq]
  unfold tlb_get_pbmt
  rw [hpte]
  unfold ptePbmt0 at hpb
  dsimp only
  rw [hpb]
  rfl

/-! ## 3. The S-mode PMP grant and the PTE-read PMA gate -/

/-- Rocq `exec_eff_pmpMatchAddr_TOR_match`. -/
theorem execEffPmpMatchAddrTORMatch (addr width : BitVec 64) (ent : BitVec 8) (pmpaddr prev : BitVec 64)
    (s : ExecSt) (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = .TOR)
    (hlt : zopz0zKzJ_u prev pmpaddr = false)
    (hr : pmpRangeMatch (prev.toNat * 4) (pmpaddr.toNat * 4) addr.toNat width.toNat = .PMP_Match) :
    execEff (pmpMatchAddr (.Physaddr addr) width ent pmpaddr prev) s = some (.PMP_Match, s, []) := by
  unfold pmpMatchAddr
  simp only [hA, hlt, Bool.false_eq_true, ↓reduceIte, toNatInt_mul4_toNat, toNatInt_toNat, hr]
  rfl

/-- Rocq `exec_eff_pmpReadAddrReg_val` (deviation 5). -/
theorem execEffPmpReadAddrRegVal (n : Nat) (s : ExecSt) :
    execEff (pmpReadAddrReg n) s = some ((s.regs .pmpaddr_n)[n]!, s, []) :=
  execEffPmpReadAddrReg n s

/-- The first iteration of an `IntRange` loop early-returns (Lean-only; the
`execEff` twin of `ExecSC2.execRForInFirstEarly`, as `WeakPmpTorEff`'s, which
cannot be imported next to `WeakPmpEff`). -/
theorem WeakWalkEff.execREffForInFirstEarly {R : Type} (range : IntRange)
    (f : Int → Unit → SailME R (ForInStep Unit)) (s s' : ExecSt) (r : R) (es : List Weff)
    (h0 : range.start ∈ range) (hf : execREff (f range.start ()) s = some (.inl r, s', es)) :
    execREff (forIn range () f) s = some (.inl r, s', es) := by
  show execREff (IntRange.forIn'.loop range (fun a _ b => f a b) () range.start (by simp)) s = _
  rw [IntRange.loop_unfold]
  simp only [dif_pos h0]
  rw [execREffBindEq, hf]

/-- Rocq `exec_eff_pmpCheck_supervisor_grant_load`. -/
theorem execEffPmpCheckSupervisorGrantLoad (a : BitVec 64) (width : Nat) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) a.toNat
      (to_bits (l := 64) width).toNat = .PMP_Match)
    (hR : (_get_Pmpcfg_ent_R (s.regs .pmpcfg_n)[0]! == 1#1) = true) :
    execEff (pmpCheck (.Physaddr a) width (.Load .PageTableEntry) .Supervisor) s = some (none, s, []) := by
  have hA' : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[(0 : Int)]!) =
      .TOR := hA
  have hm := execEffPmpMatchAddrTORMatch a (to_bits (l := 64) width) _ (s.regs .pmpaddr_n)[0]!
    (zeros (n := 64)) s hA' hlt hr
  have hrd : execEff (pmpReadAddrReg (0 : Int).toNat) s = some ((s.regs .pmpaddr_n)[0]!, s, []) :=
    execEffPmpReadAddrReg 0 s
  have hrwx : execEff (pmpCheckRWX (s.regs .pmpcfg_n)[(0 : Int)]! (.Load .PageTableEntry)) s =
      some (true, s, []) := by
    unfold pmpCheckRWX
    have hR' : (_get_Pmpcfg_ent_R (s.regs .pmpcfg_n)[(0 : Int)]! == 1#1) = true := hR
    rw [hR']; rfl
  unfold pmpCheck
  rw [execEffCatchEarlyReturn]
  have hc : (sys_pmp_count == 0) = false := by decide
  simp only [hc, Bool.false_eq_true, ↓reduceIte]
  rw [execREffBindEq, WeakWalkEff.execREffForInFirstEarly _ _ s s none [] (by decide)]
  dsimp only
  rw [if_neg (by decide)]
  rw [execREffBindNil _ _ _ _ _ (wpeExecREffReturnmFwd _ s),
    execREffLiftRSeq _ _ _ _ _ (execEffReadReg .pmpcfg_n s),
    execREffBindNil _ _ _ _ _ (wpeExecREffReturnmFwd _ s),
    execREffLiftRSeq _ _ _ _ _ hrd, execREffLiftRSeq _ _ _ _ _ hm]
  dsimp only
  rw [execREffLiftRSeq _ _ _ _ _ hrwx]
  rfl

/-- Rocq `exec_eff_is_mag_applicable_load_pte`. -/
theorem execEffIsMagApplicableLoadPte (width : Nat) (s : ExecSt) :
    execEff (is_mag_applicable_access (.Load .PageTableEntry) width) s = some (false, s, []) := rfl

/-- Rocq `exec_eff_pmaCheck_ram_pte`. -/
theorem execEffPmaCheckRamPte (addr : BitVec 64) (region : PMA_Region) (roc : Bool) (s : ExecSt)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hr : (override_PMA region.attributes .PBMT_PMA).supports_pte_read = true) :
    execEff (pmaCheck (.Physaddr addr) 8 (.Load .PageTableEntry) .PBMT_PMA roc) s =
      some (.Ok pmaOkAligned, s, []) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  pma_ok_eff_peel hm hr (execEffIsMagApplicableLoadPte 8 s) hal

/-! ## 4. THE PTE READ -- where the walk's trace element is born -/

/-- The walker's one memory step (Lean-only, deviation 2): `read_ram .Read_ttw`,
classified as the PLAIN read `wakPlain` (O2: `classify (.AK_ttw ()) =
⟨false, false, false⟩`). -/
theorem WeakWalkEff.execEffReadRamTtw8 (addr w : BitVec 64) (s : ExecSt) (hdev : devAddr addr = false)
    (hb : BytesAt s addr 8 w) :
    execEff (read_ram .Read_ttw (.Physaddr addr) 8 false) s =
      some ((w, default_meta), s, [.WEread wakPlain addr 8]) := by
  have hr : bmRead s.mem addr 8 = some w := bmRead_of_bytes _ _ _ _ hb
  have hm : ∀ k, mmioAcc addr k = false := fun k => by simp [mmioAcc, hdev]
  unfold read_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_read PreSail.sail_mem_read
  exec_eff_run [hm, hr]
  rfl

/-- Rocq `exec_eff_read_pte_S` (deviation 2). -/
theorem execEffReadPteS (addr : BitVec 64) (region : PMA_Region) (w : BitVec 64) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) addr.toNat
      (to_bits (l := 64) 8).toNat = .PMP_Match)
    (hR : (_get_Pmpcfg_ent_R (s.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hpte : (override_PMA region.attributes .PBMT_PMA).supports_pte_read = true)
    (hc : execEff (within_clint (.Physaddr addr) 8) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 8) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr addr) 8) s = some (false, s, []))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 8 w) :
    execEff (read_pte (.Physaddr addr) 8) s = some (.Ok w, s, [.WEread wakPlain addr 8]) := by
  have hpma := execEffPmaCheckRamPte addr region false s hm hal hpte
  have hpmp := execEffPmpCheckSupervisorGrantLoad addr 8 s hA hlt hr hR
  have hmm := execEffWithinMmioReadableFalse addr 8 s hc hsig hh
  have hrr := WeakWalkEff.execEffReadRamTtw8 addr w s hdev hb
  have hck : execEff (checked_mem_read (.Load .PageTableEntry) .PBMT_PMA .Supervisor (.Physaddr addr) 8
      false false false false) s = some (.Ok (w, default_meta), s, [.WEread wakPlain addr 8]) := by
    unfold checked_mem_read check_pma_with_pmp_priority
    rw [execEffCatchEarlyReturn]
    exec_eff_mem [hpma]
    exec_eff_mem [hpmp, hmm, hrr, read_kind_of_flags]
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.setWidth_eq]
    congr
    simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
    bv_decide
  unfold read_pte mem_read_priv mem_read_priv_meta
  exec_eff_run [hck]
  rfl

/-- Rocq `PtTree.pt_slot_mem` (Lean-only twin, deviation 6): the slot's 8 bytes
present, the slot in RAM, 8-byte aligned. -/
def WeakWalkEff.ptSlotMem (sg : ExecSt) (a w : BitVec 64) : Prop :=
  BytesAt sg a 8 w ∧ inRam a 8 ∧ is_aligned_paddr (.Physaddr a) 8 = true

/-- Rocq `wpt_read_pte_slot` (deviation 6). -/
theorem wptReadPteSlot (sg : ExecSt) (a w : BitVec 64) (region : PMA_Region)
    (hslot : WeakWalkEff.ptSlotMem sg a w)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (sg.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (sg.regs .pmpaddr_n)[0]! = false)
    (hR : (_get_Pmpcfg_ent_R (sg.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hcov : ramEnd ≤ (sg.regs .pmpaddr_n)[0]!.toNat * 4)
    (hm : matching_pma_region (sg.regs .pma_regions) (.Physaddr a) 8 = some region)
    (hpte : (override_PMA region.attributes .PBMT_PMA).supports_pte_read = true)
    (hhtif : sg.regs .htif_tohost_base = none) :
    execEff (read_pte (.Physaddr a) 8) sg = some (.Ok w, sg, [.WEread wakPlain a 8]) := by
  obtain ⟨hb, hram, hal⟩ := hslot
  have hz : (zeros (n := 64)).toNat = 0 := rfl
  have h8 : (to_bits (l := 64) 8).toNat = 8 := by decide
  have hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((sg.regs .pmpaddr_n)[0]!.toNat * 4) a.toNat
      (to_bits (l := 64) 8).toNat = .PMP_Match := by
    rw [hz, h8]
    exact pmpRangeMatch_full _ _ _ _ (Nat.zero_le _) (by decide) (by have := hram.2; omega)
  have hc : execEff (within_clint (.Physaddr a) 8) sg = some (false, sg, []) := by
    rw [within_clint_ram a 8 hram]; rfl
  have hsig : execEff (within_sig (.Physaddr a) 8) sg = some (false, sg, []) := by
    first
    | rfl
    | (simp only [within_sig, plat_have_sig, Functions.not]; rfl)
  exact execEffReadPteS a region w sg hA hlt hr hR hm hal hpte hc hsig (execEffWithinHtifFalse a 8 sg hhtif)
    (devAddrRam a 8 hram) hb

/-! ## 5. THE SUCCESS WALK -- `CommonWalk` section `UserWalk` replayed

The Rocq section's variables and hypotheses (`vpn root pte2 pte1 pte0 acc p mxr
do_sum`, `H2i … H0N`) are theorem arguments; each lemma takes the ones its Rocq
twin uses.  The section `Let`s `addr2/1/0` are inlined (`uPteAddr …`). -/

/-- Rocq `exec_eff_check_leaf_pte_leaf0`. -/
theorem execEffCheckLeafPteLeaf0 (vpn : BitVec 27) (pte0 : BitVec 64) (acc : MemoryAccessType mem_payload)
    (p : Privilege) (mxr dosum : Bool)
    (h0i : wpteValid pte0) (h0nl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte0 7 0)) = false)
    (hchk0 : wpteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (pa : physaddr) (menvcfg0 : BitVec 64) (s : ExecSt)
    (hmisa : s.regs .misa = misaC) (hmenv : s.regs .menvcfg = menvcfg0)
    (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    execEff (check_leaf_pte 39 vpn acc p mxr dosum pte0 pa 0 ()) s =
      some (.Ok (ppn0 pte0, .PBMT_PMA, ()), s, []) := by
  unfold check_leaf_pte
  rw [execEffCatchEarlyReturn]
  exec_eff_run
  erw [h0i s]
  exec_eff_run
  erw [h0nl]
  exec_eff_run
  erw [hchk0 s]
  exec_eff_run [execEffCurrentlyEnabledSvnapot s hmisa]
  erw [h0N]
  exec_eff_run [hmenv, hpbmte]
  rfl

set_option simprocs false in
/-- Rocq `exec_eff_rec_walk_leaf` (deviation 1). -/
theorem execEffRecWalkLeaf (vpn : BitVec 27) (pte1 pte0 : BitVec 64) (acc : MemoryAccessType mem_payload)
    (p : Privilege) (mxr dosum : Bool)
    (h0i : wpteValid pte0) (h0nl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte0 7 0)) = false)
    (hchk0 : wpteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (g : Bool) (menvcfg0 : BitVec 64) (es0 : List Weff) (s : ExecSt)
    (hmisa : s.regs .misa = misaC)
    (hrd0 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok pte0, s, es0))
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    execEff (pt_walk 39 vpn acc p mxr dosum (uNextBase pte1) 0 g ()) s =
      some (.Ok (uWalkOut (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) pte0
        (g || uGbit pte0), ()), s, es0) := by
  rw [pt_walk]
  exec_eff_run
  erw [hrd0]
  exec_eff_run
  erw [h0i s]
  exec_eff_run [Functions.not, wteExecEffIte]
  erw [execEffCheckLeafPteLeaf0 vpn pte0 acc p mxr dosum h0i h0nl hchk0 h0N _ menvcfg0 s hmisa hmenv hpbmte]
  first | (exec_eff_run [Bool.not_true]; done) | (exec_eff_run [Bool.not_true]; rfl)

set_option simprocs false in
/-- Rocq `exec_eff_rec_walk_l1` (deviation 1). -/
theorem execEffRecWalkL1 (vpn : BitVec 27) (pte2 pte1 pte0 : BitVec 64) (acc : MemoryAccessType mem_payload)
    (p : Privilege) (mxr dosum : Bool)
    (h1i : wpteValid pte1) (h1nl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte1 7 0)) = true)
    (h0i : wpteValid pte0) (h0nl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte0 7 0)) = false)
    (hchk0 : wpteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (g : Bool) (menvcfg0 : BitVec 64) (es1 es0 : List Weff) (s : ExecSt)
    (hmisa : s.regs .misa = misaC)
    (hrd1 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase pte2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok pte1, s, es1))
    (hrd0 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok pte0, s, es0))
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    execEff (pt_walk 39 vpn acc p mxr dosum (uNextBase pte2) 1 g ()) s =
      some (.Ok (uWalkOut (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) pte0
        ((g || uGbit pte1) || uGbit pte0), ()), s, es1 ++ es0) := by
  rw [pt_walk]
  exec_eff_run
  erw [hrd1]
  exec_eff_run
  erw [h1i s]
  exec_eff_run [Functions.not, wteExecEffIte]
  erw [h1nl]
  exec_eff_run [wteExecEffIte]
  erw [execEffRecWalkLeaf vpn pte1 pte0 acc p mxr dosum h0i h0nl hchk0 h0N _ menvcfg0 es0 s hmisa hrd0 hmenv
    hpbmte]
  rfl

set_option simprocs false in
/-- Rocq `exec_eff_pt_walk_user`: the full three-level walk, trace
`es2 ++ (es1 ++ es0)`. -/
theorem execEffPtWalkUser (vpn : BitVec 27) (root : BitVec 44) (pte2 pte1 pte0 : BitVec 64)
    (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (h2i : wpteValid pte2) (h2nl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte2 7 0)) = true)
    (h1i : wpteValid pte1) (h1nl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte1 7 0)) = true)
    (h0i : wpteValid pte0) (h0nl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte0 7 0)) = false)
    (hchk0 : wpteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (menvcfg0 : BitVec 64) (es2 es1 es0 : List Weff) (s : ExecSt)
    (hmisa : s.regs .misa = misaC)
    (hrd2 : execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
      some (.Ok pte2, s, es2))
    (hrd1 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase pte2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok pte1, s, es1))
    (hrd0 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok pte0, s, es0))
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    execEff (pt_walk 39 vpn acc p mxr dosum root 2 false ()) s =
      some (.Ok (uWalkOut (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) pte0
        (uGlobal pte2 pte1 pte0), ()), s, es2 ++ (es1 ++ es0)) := by
  rw [pt_walk]
  exec_eff_run
  erw [hrd2]
  exec_eff_run
  erw [h2i s]
  exec_eff_run [Functions.not, wteExecEffIte]
  erw [h2nl]
  exec_eff_run [wteExecEffIte]
  erw [execEffRecWalkL1 vpn pte2 pte1 pte0 acc p mxr dosum h1i h1nl h0i h0nl hchk0 h0N _ menvcfg0 es1 es0 s
    hmisa hrd1 hrd0 hmenv hpbmte]
  rfl

/-- Rocq `exec_eff_add_to_TLB_user`: the TLB fill, register-only. -/
theorem execEffAddToTLBUser (vpn : BitVec 27) (pte2 pte1 pte0 : BitVec 64) (asid : BitVec 16) (s : ExecSt) :
    execEff (add_to_TLB 39 asid vpn (ppn0 pte0) pte0
        (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 0 (uGlobal pte2 pte1 pte0)) s =
      some ((), s.setReg .tlb (vectorUpdate (s.regs .tlb) (tlb_hash 39 vpn)
        (some (uWalkEntry vpn pte2 pte1 pte0 asid))), []) := by
  unfold add_to_TLB
  exec_eff_run
  rfl

/-- Rocq `exec_eff_translate_TLB_miss_user` (O2: walk + fill, no A/D update). -/
theorem execEffTranslateTLBMissUser (vpn : BitVec 27) (root : BitVec 44) (pte2 pte1 pte0 : BitVec 64)
    (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (h2i : wpteValid pte2) (h2nl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte2 7 0)) = true)
    (h1i : wpteValid pte1) (h1nl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte1 7 0)) = true)
    (h0i : wpteValid pte0) (h0nl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte0 7 0)) = false)
    (hchk0 : wpteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (asid : BitVec 16) (menvcfg0 : BitVec 64) (es2 es1 es0 : List Weff) (s : ExecSt)
    (hmisa : s.regs .misa = misaC) (hnoupd : update_PTE_Bits pte0 acc = none)
    (hrd2 : execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
      some (.Ok pte2, s, es2))
    (hrd1 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase pte2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok pte1, s, es1))
    (hrd0 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok pte0, s, es0))
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    execEff (translate_TLB_miss 39 asid root vpn acc p mxr dosum ()) s =
      some (.Ok (ppn0 pte0, .PBMT_PMA, ()),
        s.setReg .tlb (vectorUpdate (s.regs .tlb) (tlb_hash 39 vpn) (some (uWalkEntry vpn pte2 pte1 pte0 asid))),
        es2 ++ (es1 ++ es0)) := by
  unfold translate_TLB_miss
  exec_eff_run
  erw [execEffPtWalkUser vpn root pte2 pte1 pte0 acc p mxr dosum h2i h2nl h1i h1nl h0i h0nl hchk0 h0N menvcfg0
    es2 es1 es0 s hmisa hrd2 hrd1 hrd0 hmenv hpbmte]
  unfold uWalkOut update_and_write_pte
  exec_eff_run
  erw [hnoupd]
  exec_eff_run
  erw [execEffAddToTLBUser vpn pte2 pte1 pte0 asid s]
  simp only [List.append_nil]

/-! ## 6. THE FAULT WALKS -- `CommonWalk` section `UserWalkFault` replayed -/

/-- Rocq `exec_eff_check_leaf_pte_invalid`. -/
theorem execEffCheckLeafPteInvalid (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (pte : BitVec 64) (pa : physaddr) (lvl : Nat) (s : ExecSt) (hinv : wpteInvalid pte) :
    execEff (check_leaf_pte 39 vpn acc p mxr dosum pte pa lvl ()) s =
      some (.Err (.PTW_Invalid_PTE (), ()), s, []) := by
  unfold check_leaf_pte
  rw [execEffCatchEarlyReturn]
  exec_eff_run
  erw [hinv s]
  rfl

/-- Rocq `exec_eff_check_leaf_pte_noperm0`. -/
theorem execEffCheckLeafPteNoperm0 (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (pte : BitVec 64) (pa : physaddr) (f : pte_check_failure) (s : ExecSt)
    (hinv : wpteValid pte) (hnl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0)) = false)
    (hchk : wpteCheckDenied acc p mxr dosum f pte) :
    execEff (check_leaf_pte 39 vpn acc p mxr dosum pte pa 0 ()) s =
      some (.Err (ext_get_ptw_error f, ()), s, []) := by
  unfold check_leaf_pte
  rw [execEffCatchEarlyReturn]
  exec_eff_run
  erw [hinv s]
  exec_eff_run
  erw [hnl]
  exec_eff_run
  erw [hchk s]
  rfl

set_option simprocs false in
/-- Rocq `exec_eff_rec_walk_leaf_invalid` (deviation 1). -/
theorem execEffRecWalkLeafInvalid (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (base : BitVec 44) (pte : BitVec 64) (g : Bool) (es0 : List Weff) (s : ExecSt)
    (hrd : execEff (read_pte (.Physaddr (uPteAddr base (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok pte, s, es0))
    (hinv : wpteInvalid pte) :
    execEff (pt_walk 39 vpn acc p mxr dosum base 0 g ()) s = some (.Err (.PTW_Invalid_PTE (), ()), s, es0) := by
  rw [pt_walk]
  exec_eff_run
  erw [hrd]
  exec_eff_run
  erw [hinv s]
  exec_eff_run [Functions.not, wteExecEffIte]
  erw [execEffCheckLeafPteInvalid vpn acc p mxr dosum pte _ 0 s hinv]
  first | (exec_eff_run [Bool.not_true]; done) | (exec_eff_run [Bool.not_true]; rfl)

set_option simprocs false in
/-- Rocq `exec_eff_rec_walk_leaf_noperm` (deviation 1). -/
theorem execEffRecWalkLeafNoperm (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (base : BitVec 44) (pte : BitVec 64) (g : Bool) (f : pte_check_failure)
    (es0 : List Weff) (s : ExecSt)
    (hrd : execEff (read_pte (.Physaddr (uPteAddr base (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok pte, s, es0))
    (hinv : wpteValid pte) (hnl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0)) = false)
    (hchk : wpteCheckDenied acc p mxr dosum f pte) :
    execEff (pt_walk 39 vpn acc p mxr dosum base 0 g ()) s = some (.Err (ext_get_ptw_error f, ()), s, es0) := by
  rw [pt_walk]
  exec_eff_run
  erw [hrd]
  exec_eff_run
  erw [hinv s]
  exec_eff_run [Functions.not, wteExecEffIte]
  erw [execEffCheckLeafPteNoperm0 vpn acc p mxr dosum pte _ f s hinv hnl hchk]
  first | (exec_eff_run [Bool.not_true]; done) | (exec_eff_run [Bool.not_true]; rfl)

set_option simprocs false in
/-- Rocq `exec_eff_rec_walk_l1_invalid` (deviation 1). -/
theorem execEffRecWalkL1Invalid (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (base : BitVec 44) (pte : BitVec 64) (g : Bool) (es1 : List Weff) (s : ExecSt)
    (hrd : execEff (read_pte (.Physaddr (uPteAddr base (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok pte, s, es1))
    (hinv : wpteInvalid pte) :
    execEff (pt_walk 39 vpn acc p mxr dosum base 1 g ()) s = some (.Err (.PTW_Invalid_PTE (), ()), s, es1) := by
  rw [pt_walk]
  exec_eff_run
  erw [hrd]
  exec_eff_run
  erw [hinv s]
  exec_eff_run [Functions.not, wteExecEffIte]
  erw [execEffCheckLeafPteInvalid vpn acc p mxr dosum pte _ 1 s hinv]
  first | (exec_eff_run [Bool.not_true]; done) | (exec_eff_run [Bool.not_true]; rfl)

set_option simprocs false in
/-- Rocq `exec_eff_rec_walk_l1_sub` (deviation 1: the sub-walk premise is `∀ g'`). -/
theorem execEffRecWalkL1Sub (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (base : BitVec 44) (pte : BitVec 64) (g : Bool)
    (r : Result (PTW_Output 39 × Unit) (PTW_Error × Unit)) (es1 es_sub : List Weff) (s : ExecSt)
    (hrd : execEff (read_pte (.Physaddr (uPteAddr base (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok pte, s, es1))
    (hinv : wpteValid pte) (hnl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0)) = true)
    (hsub : ∀ g', execEff (pt_walk 39 vpn acc p mxr dosum (uNextBase pte) 0 g' ()) s = some (r, s, es_sub)) :
    execEff (pt_walk 39 vpn acc p mxr dosum base 1 g ()) s = some (r, s, es1 ++ es_sub) := by
  rw [pt_walk]
  exec_eff_run
  erw [hrd]
  exec_eff_run
  erw [hinv s]
  exec_eff_run [Functions.not, wteExecEffIte]
  erw [hnl]
  exec_eff_run [wteExecEffIte]
  erw [hsub]

set_option simprocs false in
/-- Rocq `exec_eff_pt_walk_user_l2_invalid`. -/
theorem execEffPtWalkUserL2Invalid (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (root : BitVec 44) (pte : BitVec 64) (es2 : List Weff) (s : ExecSt)
    (hrd : execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
      some (.Ok pte, s, es2))
    (hinv : wpteInvalid pte) :
    execEff (pt_walk 39 vpn acc p mxr dosum root 2 false ()) s =
      some (.Err (.PTW_Invalid_PTE (), ()), s, es2) := by
  rw [pt_walk]
  exec_eff_run
  erw [hrd]
  exec_eff_run
  erw [hinv s]
  exec_eff_run [Functions.not, wteExecEffIte]
  erw [execEffCheckLeafPteInvalid vpn acc p mxr dosum pte _ 2 s hinv]
  first | (exec_eff_run [Bool.not_true]; done) | (exec_eff_run [Bool.not_true]; rfl)

set_option simprocs false in
/-- Rocq `exec_eff_pt_walk_user_sub` (deviation 1). -/
theorem execEffPtWalkUserSub (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (root : BitVec 44) (pte : BitVec 64)
    (r : Result (PTW_Output 39 × Unit) (PTW_Error × Unit)) (es2 es_sub : List Weff) (s : ExecSt)
    (hrd : execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
      some (.Ok pte, s, es2))
    (hinv : wpteValid pte) (hnl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0)) = true)
    (hsub : ∀ g', execEff (pt_walk 39 vpn acc p mxr dosum (uNextBase pte) 1 g' ()) s = some (r, s, es_sub)) :
    execEff (pt_walk 39 vpn acc p mxr dosum root 2 false ()) s = some (r, s, es2 ++ es_sub) := by
  rw [pt_walk]
  exec_eff_run
  erw [hrd]
  exec_eff_run
  erw [hinv s]
  exec_eff_run [Functions.not, wteExecEffIte]
  erw [hnl]
  exec_eff_run [wteExecEffIte]
  erw [hsub]

/-- Rocq `exec_eff_translate_TLB_miss_user_walk_err`. -/
theorem execEffTranslateTLBMissUserWalkErr (vpn : BitVec 27) (acc : MemoryAccessType mem_payload)
    (p : Privilege) (mxr dosum : Bool) (asid : BitVec 16) (root : BitVec 44) (f : PTW_Error)
    (es : List Weff) (s : ExecSt)
    (hwalk : execEff (pt_walk 39 vpn acc p mxr dosum root 2 false ()) s = some (.Err (f, ()), s, es)) :
    execEff (translate_TLB_miss 39 asid root vpn acc p mxr dosum ()) s = some (.Err (f, ()), s, es) := by
  unfold translate_TLB_miss
  exec_eff_run
  erw [hwalk]
  exec_eff_run

/-! ## 7. THE `translate`-LEVEL DISPATCH, and the `PtTree` §8 mirrors -/

/-- Rocq `exec_eff_translate_miss_user`. -/
theorem execEffTranslateMissUser (vpn : BitVec 27) (root : BitVec 44) (asid : BitVec 16)
    (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (r : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit)) (s s' : ExecSt) (es : List Weff)
    (hlk : execEff (lookup_TLB 39 asid vpn) s = some (none, s, []))
    (hmiss : execEff (translate_TLB_miss 39 asid root vpn acc p mxr dosum ()) s = some (r, s', es)) :
    execEff (translate 39 asid root vpn acc p mxr dosum ()) s = some (r, s', es) := by
  unfold translate
  rw [execEffBindNil _ _ _ _ _ hlk]
  exact hmiss

/-- Rocq `exec_eff_translate_hit_user`. -/
theorem execEffTranslateHitUser (vpn : BitVec 27) (root : BitVec 44) (asid : BitVec 16) (idx : Nat)
    (ent : TLB_Entry) (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (r : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit)) (s s' : ExecSt) (es : List Weff)
    (hlk : execEff (lookup_TLB 39 asid vpn) s = some (some (idx, ent), s, []))
    (hhit : execEff (translate_TLB_hit 39 asid vpn acc p mxr dosum () idx ent) s = some (r, s', es)) :
    execEff (translate 39 asid root vpn acc p mxr dosum ()) s = some (r, s', es) := by
  unfold translate
  rw [execEffBindNil _ _ _ _ _ hlk]
  exact hhit

/-- Rocq `exec_eff_translate_TLB_hit_pt` (O1: state unchanged, empty trace). -/
theorem execEffTranslateTLBHitPt (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (p2 p1 q0 : BitVec 64) (asid : BitVec 16) (idx : Nat) (s : ExecSt)
    (hchk : wpteCheckOk acc p mxr dosum q0) (hupd : update_PTE_Bits q0 acc = none) (hpb : ptePbmt0 q0) :
    execEff (translate_TLB_hit 39 asid vpn acc p mxr dosum () idx (uWalkEntry vpn p2 p1 q0 asid)) s =
      some (.Ok (ppn0 q0, .PBMT_PMA, ()), s, []) := by
  unfold translate_TLB_hit
  simp only [tlbGetPteUwe, tlbGetPpnUwe]
  exec_eff_run
  erw [hchk s]
  unfold update_and_write_pte
  exec_eff_run
  erw [hupd]
  exec_eff_run
  erw [execEffUwePbmt vpn p2 p1 q0 asid s hpb]

/-- Rocq `exec_eff_translate_TLB_hit_denied_pt`. -/
theorem execEffTranslateTLBHitDeniedPt (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (vpn : BitVec 27) (p2 p1 q0 : BitVec 64) (asid : BitVec 16) (idx : Nat) (s : ExecSt)
    (hden : wpteCheckDenied acc p mxr dosum (.PTE_No_Permission ()) q0) :
    execEff (translate_TLB_hit 39 asid vpn acc p mxr dosum () idx (uWalkEntry vpn p2 p1 q0 asid)) s =
      some (.Err (.PTW_No_Permission (), ()), s, []) := by
  unfold translate_TLB_hit
  simp only [tlbGetPteUwe]
  exec_eff_run
  erw [hden s]
  rfl

/-- Rocq `exec_eff_translate_pt_blocks_l2`. -/
theorem execEffTranslatePtBlocksL2 (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (root : BitVec 44) (w2 : BitVec 64) (es2 : List Weff) (s : ExecSt)
    (hrd2 : execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
      some (.Ok w2, s, es2))
    (hi2 : wpteInvalid w2) (hlk : execEff (lookup_TLB 39 0#16 vpn) s = some (none, s, [])) :
    execEff (translate 39 0#16 root vpn acc p mxr dosum ()) s =
      some (.Err (.PTW_Invalid_PTE (), ()), s, es2) :=
  execEffTranslateMissUser vpn root _ acc p mxr dosum _ s s _ hlk
    (execEffTranslateTLBMissUserWalkErr vpn acc p mxr dosum _ root _ _ s
      (execEffPtWalkUserL2Invalid vpn acc p mxr dosum root w2 es2 s hrd2 hi2))

/-- Rocq `exec_eff_translate_pt_blocks_l1`. -/
theorem execEffTranslatePtBlocksL1 (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (root : BitVec 44) (p2 w1 : BitVec 64) (es2 es1 : List Weff) (s : ExecSt)
    (hrd2 : execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
      some (.Ok p2, s, es2))
    (hv2 : wpteValid p2) (hn2 : ptePtr p2)
    (hrd1 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok w1, s, es1))
    (hi1 : wpteInvalid w1) (hlk : execEff (lookup_TLB 39 0#16 vpn) s = some (none, s, [])) :
    execEff (translate 39 0#16 root vpn acc p mxr dosum ()) s =
      some (.Err (.PTW_Invalid_PTE (), ()), s, es2 ++ es1) :=
  execEffTranslateMissUser vpn root _ acc p mxr dosum _ s s _ hlk
    (execEffTranslateTLBMissUserWalkErr vpn acc p mxr dosum _ root _ _ s
      (execEffPtWalkUserSub vpn acc p mxr dosum root p2 _ es2 es1 s hrd2 hv2 hn2 (fun g' =>
        execEffRecWalkL1Invalid vpn acc p mxr dosum (uNextBase p2) w1 g' es1 s hrd1 hi1)))

/-- Rocq `exec_eff_translate_pt_blocks_l0`. -/
theorem execEffTranslatePtBlocksL0 (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (root : BitVec 44) (p2 p1 w0 : BitVec 64) (es2 es1 es0 : List Weff) (s : ExecSt)
    (hrd2 : execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
      some (.Ok p2, s, es2))
    (hv2 : wpteValid p2) (hn2 : ptePtr p2)
    (hrd1 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok p1, s, es1))
    (hv1 : wpteValid p1) (hn1 : ptePtr p1)
    (hrd0 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok w0, s, es0))
    (hi0 : wpteInvalid w0) (hlk : execEff (lookup_TLB 39 0#16 vpn) s = some (none, s, [])) :
    execEff (translate 39 0#16 root vpn acc p mxr dosum ()) s =
      some (.Err (.PTW_Invalid_PTE (), ()), s, es2 ++ (es1 ++ es0)) :=
  execEffTranslateMissUser vpn root _ acc p mxr dosum _ s s _ hlk
    (execEffTranslateTLBMissUserWalkErr vpn acc p mxr dosum _ root _ _ s
      (execEffPtWalkUserSub vpn acc p mxr dosum root p2 _ es2 (es1 ++ es0) s hrd2 hv2 hn2 (fun g' =>
        execEffRecWalkL1Sub vpn acc p mxr dosum (uNextBase p2) p1 g' _ es1 es0 s hrd1 hv1 hn1 (fun g'' =>
          execEffRecWalkLeafInvalid vpn acc p mxr dosum (uNextBase p1) w0 g'' es0 s hrd0 hi0))))

/-- Rocq `exec_eff_translate_pt_blocks`: the `PtTree.exec_translate_pt_blocks`-shaped
wrapper, the trace existential. -/
theorem execEffTranslatePtBlocks (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (root : BitVec 44) (s : ExecSt)
    (h : (∃ w2 es2, execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
            some (.Ok w2, s, es2) ∧ wpteInvalid w2) ∨
         (∃ p2 w1 es2 es1,
          execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
            some (.Ok p2, s, es2) ∧ wpteValid p2 ∧ ptePtr p2 ∧
          execEff (read_pte (.Physaddr (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
            some (.Ok w1, s, es1) ∧ wpteInvalid w1) ∨
         (∃ p2 p1 w0 es2 es1 es0,
          execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
            some (.Ok p2, s, es2) ∧ wpteValid p2 ∧ ptePtr p2 ∧
          execEff (read_pte (.Physaddr (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
            some (.Ok p1, s, es1) ∧ wpteValid p1 ∧ ptePtr p1 ∧
          execEff (read_pte (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
            some (.Ok w0, s, es0) ∧ wpteInvalid w0))
    (hlk : execEff (lookup_TLB 39 0#16 vpn) s = some (none, s, [])) :
    ∃ es, execEff (translate 39 0#16 root vpn acc p mxr dosum ()) s =
      some (.Err (.PTW_Invalid_PTE (), ()), s, es) := by
  rcases h with ⟨w2, es2, hrd2, hi2⟩ | ⟨p2, w1, es2, es1, hrd2, hv2, hn2, hrd1, hi1⟩ |
    ⟨p2, p1, w0, es2, es1, es0, hrd2, hv2, hn2, hrd1, hv1, hn1, hrd0, hi0⟩
  · exact ⟨_, execEffTranslatePtBlocksL2 acc p mxr dosum vpn root w2 es2 s hrd2 hi2 hlk⟩
  · exact ⟨_, execEffTranslatePtBlocksL1 acc p mxr dosum vpn root p2 w1 es2 es1 s hrd2 hv2 hn2 hrd1 hi1 hlk⟩
  · exact ⟨_, execEffTranslatePtBlocksL0 acc p mxr dosum vpn root p2 p1 w0 es2 es1 es0 s hrd2 hv2 hn2 hrd1
      hv1 hn1 hrd0 hi0 hlk⟩

/-- Rocq `exec_eff_translate_pt_denied`. -/
theorem execEffTranslatePtDenied (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (root : BitVec 44) (p2 p1 p0 : BitVec 64) (es2 es1 es0 : List Weff) (s : ExecSt)
    (hv2 : wpteValid p2) (hn2 : ptePtr p2) (hv1 : wpteValid p1) (hn1 : ptePtr p1) (hv0 : wpteValid p0)
    (hl0 : pteLeaf p0) (hden : wpteCheckDenied acc p mxr dosum (.PTE_No_Permission ()) p0)
    (hrd2 : execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
      some (.Ok p2, s, es2))
    (hrd1 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok p1, s, es1))
    (hrd0 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok p0, s, es0))
    (hlk : execEff (lookup_TLB 39 0#16 vpn) s = some (none, s, [])) :
    execEff (translate 39 0#16 root vpn acc p mxr dosum ()) s =
      some (.Err (.PTW_No_Permission (), ()), s, es2 ++ (es1 ++ es0)) :=
  execEffTranslateMissUser vpn root _ acc p mxr dosum _ s s _ hlk
    (execEffTranslateTLBMissUserWalkErr vpn acc p mxr dosum _ root _ _ s
      (execEffPtWalkUserSub vpn acc p mxr dosum root p2 _ es2 (es1 ++ es0) s hrd2 hv2 hn2 (fun g' =>
        execEffRecWalkL1Sub vpn acc p mxr dosum (uNextBase p2) p1 g' _ es1 es0 s hrd1 hv1 hn1 (fun g'' =>
          execEffRecWalkLeafNoperm vpn acc p mxr dosum (uNextBase p1) p0 g'' (.PTE_No_Permission ()) es0 s
            hrd0 hv0 hl0 hden))))

/-- Rocq `PtTree.ptree_blocks` (Lean-only twin, deviation 6): the walk of `vpn`
stops at an INVALID word at level 2, 1 or 0. -/
def WeakWalkEff.ptreeBlocks (t : PTree) (vpn : BitVec 27) : Prop :=
  (t.kids (AxPtProt.vpnIdx 2 vpn) = none ∧ pteInvalid (t.ents (AxPtProt.vpnIdx 2 vpn))) ∨
  (∃ c1, t.kids (AxPtProt.vpnIdx 2 vpn) = some c1 ∧
    c1.kids (AxPtProt.vpnIdx 1 vpn) = none ∧
    pteValid (t.ents (AxPtProt.vpnIdx 2 vpn)) ∧
    ptePtr (t.ents (AxPtProt.vpnIdx 2 vpn)) ∧
    uNextBase (t.ents (AxPtProt.vpnIdx 2 vpn)) = c1.base ∧
    pteInvalid (c1.ents (AxPtProt.vpnIdx 1 vpn))) ∨
  (∃ c1 c0, t.kids (AxPtProt.vpnIdx 2 vpn) = some c1 ∧
    c1.kids (AxPtProt.vpnIdx 1 vpn) = some c0 ∧
    pteValid (t.ents (AxPtProt.vpnIdx 2 vpn)) ∧
    ptePtr (t.ents (AxPtProt.vpnIdx 2 vpn)) ∧
    pteValid (c1.ents (AxPtProt.vpnIdx 1 vpn)) ∧
    ptePtr (c1.ents (AxPtProt.vpnIdx 1 vpn)) ∧
    uNextBase (t.ents (AxPtProt.vpnIdx 2 vpn)) = c1.base ∧
    uNextBase (c1.ents (AxPtProt.vpnIdx 1 vpn)) = c0.base ∧
    pteInvalid (c0.ents (AxPtProt.vpnIdx 0 vpn)))

/-- Rocq `PtTree.pte_valid_invalid_excl` (Lean-only twin, deviation 6). -/
theorem WeakWalkEff.pteValidInvalidExcl (w : BitVec 64) : pteValid w → pteInvalid w → False := by
  intro hv hi
  have h := (hv ⟨zeroRegs, fun _ => none, testDevs⟩).symm.trans (hi ⟨zeroRegs, fun _ => none, testDevs⟩)
  simp at h

/-- Rocq `PtTree.ptree_maps_blocks_excl` (Lean-only twin, deviation 6). -/
theorem WeakWalkEff.ptreeMapsBlocksExcl (t : PTree) (vpn : BitVec 27) (p2 p1 p0 : BitVec 64) :
    AxPtProt.ptreeMaps t vpn p2 p1 p0 → WeakWalkEff.ptreeBlocks t vpn → False := by
  rintro ⟨c1, c0, hk2, hk1, -, -, he0, -, -, -, -, -, -, hv0, -⟩
    (⟨hk2n, -⟩ | ⟨c1', hk2', hk1n, -⟩ | ⟨c1', c0', hk2', hk1', -, -, -, -, -, -, hinv0⟩)
  · rw [hk2] at hk2n; cases hk2n
  · rw [hk2] at hk2'
    cases hk2'
    rw [hk1] at hk1n; cases hk1n
  · rw [hk2] at hk2'
    cases hk2'
    rw [hk1] at hk1'
    cases hk1'
    rw [he0] at hinv0
    exact WeakWalkEff.pteValidInvalidExcl p0 hv0 hinv0

/-- Rocq `PtTree.uwe_match_other` (Lean-only twin, deviation 6): a walk entry
never matches a foreign vpn. -/
theorem WeakWalkEff.uweMatchOther (vpn vpn' : BitVec 27) (p2 p1 q0 : BitVec 64) (asid : BitVec 16)
    (hne : vpn ≠ vpn') :
    match_TLB_Entry (uWalkEntry vpn p2 p1 q0 asid) asid (sign_extend (m := 57 - 12) vpn') = false := by
  unfold match_TLB_Entry uWalkEntry ptFillEnt
  simp only [zero_extend, sign_extend, ones, Sail.BitVec.zeroExtend, Sail.BitVec.signExtend]
  have h1 : sail_ones 0 = 0#0 := by decide
  rw [h1]
  simp only [beq_self_eq_true, Bool.or_true, Bool.true_and, beq_eq_false_iff_ne, ne_eq]
  intro h
  apply hne
  bv_decide

/-- Rocq `wtlb_ok_pt_lookup_blocked`: under `tlbOkPt` a BLOCKED vpn is never
TLB-resident. -/
theorem wtlbOkPtLookupBlocked (t : PTree) (vpn : BitVec 27) (tlbvec : Vector (Option TLB_Entry) (2 ^ 6))
    (s : ExecSt) (hok : AxPtProt.tlbOkPt 0#16 t tlbvec) (hblk : WeakWalkEff.ptreeBlocks t vpn)
    (htlb : s.regs .tlb = tlbvec) :
    execEff (lookup_TLB 39 0#16 vpn) s = some (none, s, []) := by
  cases hslot : tlbvec[tlb_hash 39 vpn]! with
  | none => exact execEffLookupTLBMiss vpn 0#16 tlbvec s htlb hslot
  | some ent =>
    obtain ⟨vpn0, q2, q1, q0, a', d', hm0, -, rfl⟩ := hok vpn ent hslot
    apply execEffLookupTLBNomatchS vpn 0#16 _ tlbvec s htlb hslot
    apply WeakWalkEff.uweMatchOther
    rintro rfl
    exact WeakWalkEff.ptreeMapsBlocksExcl t vpn0 q2 q1 q0 hm0 hblk

/-! ## 8. THE `translateAddr` FRONT HEADS -/

/-- Rocq `exec_eff_translateAddr_pt_front` (deviation 7). -/
theorem execEffTranslateAddrPtFront (acc : MemoryAccessType mem_payload) (p : Privilege) (vpn : BitVec 27)
    (root ppnv : BitVec 44) (satp0 va pa : BitVec 64) (estr : List Weff) (s s' : ExecSt)
    (heff : execEff (effectivePrivilege acc (s.regs .mstatus) p) s = some (p, s, []))
    (hss : execEff (is_shadow_stack_access acc) s = some (false, s, []))
    (hcp : s.regs .cur_privilege = p)
    (htm : execEff (translationMode p) s = some (.Sv39, s, []))
    (hsatp : s.regs .satp = satp0)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = root)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hcanon : (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false)
    (hvpn : BitVec.setWidth 27 (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb va 38 0) 38 Functions.pagesize_bits) = vpn)
    (htr : ∀ mxr dosum, execEff (translate 39 0#16 root vpn acc p mxr dosum ()) s =
      some (.Ok (ppnv, .PBMT_PMA, ()), s', estr))
    (hident : zero_extend (m := 64) (ppnv +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa) :
    execEff (translateAddr (.Virtaddr va) acc) s = some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), s', estr) := by
  have hw : execEff (satp_mode_width_forwards .Sv39) s = some (39, s, []) := rfl
  have hgs : execEff (get_satp 39) s = some (satp0, s, []) := by
    unfold get_satp
    exec_eff_run [hsatp]
    show some (BitVec.setWidth 64 satp0, s, []) = _
    rw [BitVec.setWidth_eq]
  unfold translateAddr
  rw [execEffCatchEarlyReturn]
  exec_eff_run [hcp, heff, htm, hss, hw, Int.reduceToNat, Int.reduceSub, hgs, bits_of_virtaddr]
  erw [hgs]
  exec_eff_run [hcanon]
  erw [hasid, hppn, hvpn, htr]
  exec_eff_run
  subst hident
  rfl

/-- Rocq `exec_eff_translateAddr_pt_front_err` (deviation 7). -/
theorem execEffTranslateAddrPtFrontErr (acc : MemoryAccessType mem_payload) (p : Privilege) (vpn : BitVec 27)
    (root : BitVec 44) (f : PTW_Error) (e : ExceptionType) (satp0 va : BitVec 64) (estr : List Weff)
    (s : ExecSt)
    (heff : execEff (effectivePrivilege acc (s.regs .mstatus) p) s = some (p, s, []))
    (hss : execEff (is_shadow_stack_access acc) s = some (false, s, []))
    (hcp : s.regs .cur_privilege = p)
    (htm : execEff (translationMode p) s = some (.Sv39, s, []))
    (hsatp : s.regs .satp = satp0)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = root)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hcanon : (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false)
    (hvpn : BitVec.setWidth 27 (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb va 38 0) 38 Functions.pagesize_bits) =
      vpn)
    (htr : ∀ mxr dosum, execEff (translate 39 0#16 root vpn acc p mxr dosum ()) s = some (.Err (f, ()), s, estr))
    (hte : execEff (translationException acc f) s = some (e, s, [])) :
    execEff (translateAddr (.Virtaddr va) acc) s = some (.Err (e, ()), s, estr) := by
  have hw : execEff (satp_mode_width_forwards .Sv39) s = some (39, s, []) := rfl
  have hgs : execEff (get_satp 39) s = some (satp0, s, []) := by
    unfold get_satp
    exec_eff_run [hsatp]
    show some (BitVec.setWidth 64 satp0, s, []) = _
    rw [BitVec.setWidth_eq]
  unfold translateAddr
  rw [execEffCatchEarlyReturn]
  exec_eff_run [hcp, heff, htm, hss, hw, Int.reduceToNat, Int.reduceSub, hgs, bits_of_virtaddr]
  erw [hgs]
  exec_eff_run [hcanon]
  erw [hasid, hppn, hvpn, htr]
  exec_eff_run [hte]

/-- Rocq `exec_eff_translateAddr_pt_front_noncanon` (deviation 7): the fault
fires at the canonicality test, the trace is EMPTY. -/
theorem execEffTranslateAddrPtFrontNoncanon (acc : MemoryAccessType mem_payload) (p : Privilege)
    (e : ExceptionType) (satp0 va : BitVec 64) (s : ExecSt)
    (heff : execEff (effectivePrivilege acc (s.regs .mstatus) p) s = some (p, s, []))
    (hss : execEff (is_shadow_stack_access acc) s = some (false, s, []))
    (hcp : s.regs .cur_privilege = p)
    (htm : execEff (translationMode p) s = some (.Sv39, s, []))
    (hsatp : s.regs .satp = satp0)
    (hcanon : (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = true)
    (hte : execEff (translationException acc (.PTW_Invalid_Addr ())) s = some (e, s, [])) :
    execEff (translateAddr (.Virtaddr va) acc) s = some (.Err (e, ()), s, []) := by
  have hw : execEff (satp_mode_width_forwards .Sv39) s = some (39, s, []) := rfl
  have hgs : execEff (get_satp 39) s = some (satp0, s, []) := by
    unfold get_satp
    exec_eff_run [hsatp]
    show some (BitVec.setWidth 64 satp0, s, []) = _
    rw [BitVec.setWidth_eq]
  unfold translateAddr
  rw [execEffCatchEarlyReturn]
  exec_eff_run [hcp, heff, htm, hss, hw, Int.reduceToNat, Int.reduceSub, hgs, bits_of_virtaddr]
  erw [hgs]
  exec_eff_run [hcanon, hte]

end Weak
