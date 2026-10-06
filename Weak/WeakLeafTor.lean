/-
Weak: **the two COMPRESSED width-8 leaves under a WRITTEN TOR PMP entry** (M4,
seam 2 of the weak `start()`/`timerinit()` port): `c.ldsp`/`c.sdsp`-class loads
and stores, at either fetch alignment, after `start()` has programmed
pmpaddr0/pmpcfg0 with a TOR entry covering RAM.

Rocq: `iris/WeakLeafTor.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `timerinit()`'s prologue/epilogue are a
`c.sdsp` and a `c.ldsp` through `sp`, executed AFTER `start()` wrote a TOR
entry, so `pmpAllOff` (which every batch-2 leaf demands) is unavailable.  THREE
DELTAS over `WeakLeafLd8` / `WeakLeafSd8` (everything else is cloned):
(1) THE PMP PREMISE: `pmpAllOff` becomes the pair `pmpAllowsAll` (the FETCH
side, all the funnel needs) plus `pmpTor0Grants pmpcfg pmpaddr ea 8` (the DATA
side); inside, the `execEff` pmpCheck fact is the TOR entry-0 arm instead of
the all-off arm.  (2) COMPRESSED, AT BOTH ALIGNMENTS: each leaf takes an
`al4 : Bool`; §0's `wPEffOfLeafRvc` is the union of
`WeakFetchRvc.wPEffOfLeafRvc4` and `WeakFetch2.wPEffOfLeafRvc2` (both fetch
arms read ONE element, of width `if al4 then 4 else 2`), so the width-generic
certificates `wcertLoadW 8` / `wcertStoreW 8` cover both alignments with one
term.  (3) THE PC BUMP IS 2: §1's `execute` lemmas take a generic `npc` (the
now-unused `pc` argument is dropped), the continuation is `pcIs (pc + 2)`.

**Deviations from Rocq.**
1. NAMES / VOCABULARY: as `Weak/WeakLeafLd8.lean` / `Weak/WeakLeafSd8.lean`
   deviation 1 (`register_lookup r s.(sregs)` ↦ `s.regs r`, `set_reg` ↦
   `ExecSt.setReg`, `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`,
   `subrange_vec_dec w 15 0` ↦ `Sail.BitVec.extractLsb w 15 0`, `add_vec_int`
   ↦ `BitVec.addInt`, `write_bytes` ↦ `bmWrite`, `RETIRE_SUCCESS` ↦
   `.Retire_Success ()`, `fin_to_nat cpu_id` ↦ `cpu.val`, `S (length l)` ↦
   `l.length + 1`); GPR reads are `s.gpr r` (stated at `(wflatSt σ).gpr` in
   the `wPEff` halves), GPR cells `gpr cpu r (DFrac.own 1) v`, the GPR write
   `setGpr`, `regval_into_reg v` is `v`; the byte window premise is
   `BytesAt`; `∀ j < n, addr_is_ram (pa_add a j)` ↦ `inRam a n`;
   `pma_allows_all` ↦ `pma_regions = bootPMA`; `pmp_allows_all` ↦
   `pmpAllowsAll`; `WpMmodeLeafBase.pmp_tor0_grants` ↦ `ExecSC3.pmpTor0Grants`.
2. O2 (owner decision): the fetch element is
   `.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)` (Rocq
   `WEread wak_plain …`).  `wPEffOfLeafRvc` takes the extra premise
   `fetchPin σ (…)` (as `wPEffOfLeafRvc4`/`wPEffOfLeafRvc2`); the `wPEff`
   halves discharge it from the text bytes (`winstrTextPinned`) through the
   Lean-only `WeakLeafTor.fetchPinRvc`.
3. THE PMP TOR ARM: `WeakPmpTorEff` cannot be imported next to `WeakPmpEff`
   (which every leaf imports through `WeakFetchEff`; they clash on
   `execEffPmpReadAddrReg`).  Its three pieces are therefore re-proved here,
   file-qualified (`WeakLeafTor.execEffPmpMatchAddrTor0Match`,
   `WeakLeafTor.execREffForInFirstEarly`,
   `WeakLeafTor.execEffPmpCheckMachineTor0`), over `WeakPmpEff`'s
   `execEffPmpReadAddrReg` (same statement).
4. THE CONFIG INTERFACE (owner decision Q3; `Weak/WeakFunnel.lean`
   deviation 7): Rocq `mmode_config (DfracOwn q)` ∗ `pmpcfg_n ↦ᵣ{q} pmpcfg0`
   ∗ `pmpaddr_n ↦ᵣ{q} pmpaddrs` is `mConf cpu (DFrac.own q) c ∗ clockCells cpu`
   with `pmpcfg0 := c.pmpcfg`, `pmpaddrs := c.pmpaddr` (both are `mConf`'s own
   cells), plus the premise `MConf.mok c`; the continuation gets back
   `mConf cpu (DFrac.own q) c` and `clockCells cpu`.  Because the funnel holds
   `mConf` (pmpaddr cell included) and does not read `pmpaddr_n`, the leaf
   splits `mConf` into two halves (Lean-only `WeakLeafTor.mConfHalves`, from
   the register cells' `Fractional` instance, `WeakLeafTor.regSplit`), runs the
   funnel at `q.half`, reads `pmpaddr_n` off the kept half inside the callback
   (`WeakLeafTor.mConfPmpaddr`; Rocq `reg_valid_dq` + `reg_at_flat`), and joins
   the halves in the continuation (`WeakLeafTor.mConfJoinHalves`).
   `GenId`/`CpuId` are the explicit `gen`/`cpu`, `WWP Loop` is
   `wwpTriv ⊤ (WExpr.loop gen cpu)`, `pc_is` is `pcIs`, `hart_ws` is `hartWs`;
   the callback passes the `mtime`/`mip` cells back untouched.
5. STATEMENT SHAPES: `A -∗ B -∗ ⌜φ⌝` ↦ `A ⊢ B -∗ ⌜φ⌝`; the agreement premise
   quantifies over a `RegFile` with `mword_of_int 0` ↦ `0#64`.
6. `exec_eff_sd8_tor_at`'s successor `MState (sregs s) (write_bytes s0.(mem)
   ea 8 vs) s0.(mdev)` is the literal `⟨s.regs, bmWrite s0.mem ea 8 vs,
   s0.dev⟩` (as `WeakLeafSd8` deviation 5).
7. Rocq §4's `Print Assumptions` are not declarations.

**Rocq → Lean name map.**  `wP_eff_of_leaf_rvc` `wPEffOfLeafRvc`,
`exec_eff_ld8_tor_at` `execEffLd8TorAt`, `exec_eff_sd8_tor_at`
`execEffSd8TorAt`, `wP_eff_ld8_tor` `wPEffLd8Tor`, `wP_eff_ld8_tor_own`
`wPEffLd8TorOwn`, `wP_eff_sd8_tor` `wPEffSd8Tor`, `wwp_ld8_tor_rvc_leaf`
`wwpLd8TorRvcLeaf`, `wwp_ld8_tor_rvc_leaf_own` `wwpLd8TorRvcLeafOwn`,
`wwp_sd8_tor_rvc_leaf` `wwpSd8TorRvcLeaf` (none in the duplicated-name table).
Lean-only (file-qualified): `WeakLeafTor.execEffPmpMatchAddrTor0Match`,
`WeakLeafTor.execREffForInFirstEarly`, `WeakLeafTor.execEffPmpCheckMachineTor0`,
`WeakLeafTor.ltFetchW`, `WeakLeafTor.fetchPinRvc`, `WeakLeafTor.regSplit`,
`WeakLeafTor.regJoin`, `WeakLeafTor.mConfSplit`, `WeakLeafTor.mConfJoin`,
`WeakLeafTor.mConfHalves`, `WeakLeafTor.mConfJoinHalves`,
`WeakLeafTor.mConfPmpaddr`.

**Dropped:** nothing (Rocq 9 lemmas; Lean 9 theorems + 12 Lean-only).
-/
import Weak.WeakLeafLd8
import Weak.WeakLeafSd8
import Weak.WeakFetch2

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 0. THE ALIGNMENT-UNION COMPRESSED RECIPE -/

/-- Rocq `wP_eff_of_leaf_rvc` (deviation 2): `wPEffOfLeafRvc4` ∪
`wPEffOfLeafRvc2`, the alignment facts `2-aligned = true` / `4-aligned = al4`. -/
theorem wPEffOfLeafRvc (al4 : Bool) (cid : Nat) (σ : Wmstate) (W : GSet PAddr)
    (pc : BitVec 64) (h : BitVec 16) (w : BitVec 32) (i0 i : instruction) (es_x : List Weff)
    (D D0 : Register → Bool) (dst : ExecSt) :
    wlogWf σ.wmLog →
    (∀ a, a ∈ W → paZ a ≠ 0) →
    (∀ a, a ∈ W → pinnedRead σ (paZ a)) →
    fetchPin σ ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++ es_x) →
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    pmpAllowsAll (σ.wmRegs .pmpcfg_n) →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    -- (a) the text word, IN THE CONFINED MEMORY, at EITHER alignment
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → wmemRestrict σ W (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    Sail.BitVec.extractLsb w 15 0 = h →
    isRVC h = true →
    -- (b) the COMPRESSED decode, and the expansion
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs i, s)) →
    -- (c) the EXPANDED instruction's `execute`, at `execEff`
    (∀ b : Bool, ∃ sExec : ExecSt,
      execEff (execute i)
        (((⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).setReg .minstret_increment b).setReg .nextPC
          (BitVec.addInt pc 2)) = some (.Retire_Success (), sExec, es_x) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b ∧
      bmDomSub sExec.mem W) →
    wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++ es_x) σ := by
  intro hwf hW0 hWp hfp lpc lpriv lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext
    hsub hisRVC hagree hDmi hgood hdec hgood0 hexp hexec
  cases al4
  · exact wPEffOfLeafRvc2 cid σ W pc h w i0 i es_x D D0 dst hwf hW0 hWp hfp lpc lpriv lpmp lpma lhtif
      lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext hsub hisRVC hagree hDmi hgood hdec hgood0 hexp
      hexec
  · exact wPEffOfLeafRvc4 cid σ W pc h w i0 i es_x D D0 dst hwf hW0 hWp hfp lpc lpriv lpmp lpma lhtif
      lhart lmisaS lmisaC lmIE lelp hal4 hram htext hsub hisRVC hagree hDmi hgood hdec hgood0 hexp hexec

/-- Lean-only: a byte of the compressed fetch is one of the four text bytes. -/
theorem WeakLeafTor.ltFetchW (al4 : Bool) (j : Nat) : j < (if al4 then 4 else 2) → j < 4 := by
  intro hj
  split at hj <;> omega

/-- Lean-only (deviation 2): the O2 fetch obligation of a compressed fetch
followed by one non-fetch element. -/
theorem WeakLeafTor.fetchPinRvc (al4 : Bool) (σ : Wmstate) (pc : BitVec 64) (e : Weff)
    (he : ∀ ak pa n, Weff.WEread ak pa n = e → ak.akIfetch = false) :
    (∀ j : Nat, j < 4 → fetchPinned σ (WeakInterp.accAddr pc j)) →
    fetchPin σ ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++ [e]) := by
  intro h
  refine ⟨fun ak pa n hin hif j hj => ?_, by simp [fetchFresh, weffWrites]⟩
  simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with hin | hin
  · cases hin
    exact h j (WeakLeafTor.ltFetchW al4 j hj)
  · rw [he ak pa n hin] at hif
    cases hif

/-! ## 0b. THE PMP TOR ENTRY-0 ARM (deviation 3: `WeakPmpTorEff`'s, re-proved) -/

/-- Lean-only (deviation 3): `WeakPmpTorEff.execEffPmpMatchAddrTor0Match`. -/
theorem WeakLeafTor.execEffPmpMatchAddrTor0Match (a wbv : BitVec 64) (ent : BitVec 8)
    (paddr : BitVec 64) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = .TOR)
    (hw : 0 < wbv.toNat) (hin : a.toNat + wbv.toNat ≤ paddr.toNat * 4) :
    execEff (pmpMatchAddr (.Physaddr a) wbv ent paddr (zeros (n := 64))) s =
      some (.PMP_Match, s, []) := by
  have hz : (zeros (n := 64)).toNat = 0 := rfl
  have hlt : zopz0zKzJ_u (zeros (n := 64)) paddr = false := by
    unfold zopz0zKzJ_u
    simp only [decide_eq_false_iff_not, BitVec.toNatInt, Int.ofNat_eq_natCast, hz]
    omega
  have hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) (paddr.toNat * 4) a.toNat wbv.toNat =
      .PMP_Match :=
    pmpRangeMatch_full _ _ _ _ (by rw [hz]; exact Nat.zero_le _) hw hin
  unfold pmpMatchAddr
  simp only [hA, hlt, Bool.false_eq_true, ↓reduceIte, toNatInt_mul4_toNat, toNatInt_toNat, hr]
  rfl

/-- Lean-only (deviation 3): `WeakPmpTorEff.execREffForInFirstEarly`. -/
theorem WeakLeafTor.execREffForInFirstEarly {R : Type} (range : IntRange)
    (f : Int → Unit → SailME R (ForInStep Unit)) (s s' : ExecSt) (r : R) (es : List Weff)
    (h0 : range.start ∈ range) (hf : execREff (f range.start ()) s = some (.inl r, s', es)) :
    execREff (forIn range () f) s = some (.inl r, s', es) := by
  show execREff (IntRange.forIn'.loop range (fun a _ b => f a b) () range.start (by simp)) s = _
  rw [IntRange.loop_unfold]
  simp only [dif_pos h0]
  rw [execREffBindEq, hf]

/-- Lean-only (deviation 3): `WeakPmpTorEff.execEffPmpCheckMachineTor0`. -/
theorem WeakLeafTor.execEffPmpCheckMachineTor0 (addr : BitVec 64) (width : Nat)
    (access : MemoryAccessType mem_payload) (s : ExecSt)
    (hg : pmpTor0Grants (s.regs .pmpcfg_n) (s.regs .pmpaddr_n) addr width)
    (hrwx : ∀ ent, ∃ b, execEff (pmpCheckRWX ent access) s = some (b, s, []))
    (hwidth : (to_bits (l := 64) width).toNat = width) :
    execEff (pmpCheck (.Physaddr addr) width access .Machine) s = some (none, s, []) := by
  obtain ⟨hA, hL, hw, hin⟩ := hg
  have hA' : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[(0 : Int)]!) =
      .TOR := hA
  have hL' : pmpLocked (s.regs .pmpcfg_n)[(0 : Int)]! = false := hL
  obtain ⟨b, hb⟩ := hrwx (s.regs .pmpcfg_n)[(0 : Int)]!
  have hm := WeakLeafTor.execEffPmpMatchAddrTor0Match addr (to_bits (l := 64) width) _
    (s.regs .pmpaddr_n)[0]! s hA' (by rw [hwidth]; exact hw) (by rw [hwidth]; exact hin)
  have hrd : execEff (pmpReadAddrReg (0 : Int).toNat) s = some ((s.regs .pmpaddr_n)[0]!, s, []) :=
    execEffPmpReadAddrReg 0 s
  unfold pmpCheck
  rw [execEffCatchEarlyReturn]
  have hc : (sys_pmp_count == 0) = false := by decide
  simp only [hc, Bool.false_eq_true, ↓reduceIte]
  rw [execREffBindEq, WeakLeafTor.execREffForInFirstEarly _ _ s s none [] (by decide)]
  dsimp only
  rw [if_neg (by decide)]
  rw [execREffBindNil _ _ _ _ _ (wpeExecREffReturnmFwd _ s),
    execREffLiftRSeq _ _ _ _ _ (execEffReadReg .pmpcfg_n s),
    execREffBindNil _ _ _ _ _ (wpeExecREffReturnmFwd _ s),
    execREffLiftRSeq _ _ _ _ _ hrd, execREffLiftRSeq _ _ _ _ _ hm]
  dsimp only
  rw [execREffLiftRSeq _ _ _ _ _ hb]
  cases b
  · simp only [hL', Bool.false_or, Functions.not]
    rfl
  · rfl

/-! ## 1. THE TWO `execute` LEMMAS, AT A GENERIC `s0` AND A GENERIC `npc` -/

/-- Rocq `exec_eff_ld8_tor_at` (deviations 1, 3). -/
theorem execEffLd8TorAt (s0 : ExecSt) (b : Bool) (npc : BitVec 64) (rs1 rd : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (v : BitVec 64) :
    rd.toNat ≠ 0 →
    s0.regs .cur_privilege = .Machine →
    (_get_Mstatus_MPRV (s0.regs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (s0.regs .mseccfg)) = .PMM_Disabled →
    pmpTor0Grants (s0.regs .pmpcfg_n) (s0.regs .pmpaddr_n) ea 8 →
    s0.regs .pma_regions = bootPMA →
    s0.regs .htif_tohost_base = none →
    s0.gpr rs1 + sign_extend (m := 64) imm = ea →
    is_aligned_paddr (.Physaddr ea) 8 = true →
    inRam ea 8 →
    BytesAt s0 ea 8 v →
    execEff (execute (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)))
        ((s0.setReg .minstret_increment b).setReg .nextPC npc) =
      some (.Retire_Success (),
        ((s0.setReg .minstret_increment b).setReg .nextPC npc).setGpr rd v,
        [.WEread wakPlain ea 8]) := by
  intro hrd lpriv lmprv lpmm htor lpma lhtif hea hal hram hbytes
  -- every config register, moved past the funnel's two pre-writes
  have lpriv_s : ((s0.setReg .minstret_increment b).setReg .nextPC npc).regs
      .cur_privilege = .Machine := by
    leaf_peel .cur_privilege; exact lpriv
  have lms_s : ((s0.setReg .minstret_increment b).setReg .nextPC npc).regs
      .mstatus = s0.regs .mstatus := by
    leaf_peel .mstatus
  have lsec_s : ((s0.setReg .minstret_increment b).setReg .nextPC npc).regs
      .mseccfg = s0.regs .mseccfg := by
    leaf_peel .mseccfg
  have lpmpc_s : ((s0.setReg .minstret_increment b).setReg .nextPC npc).regs
      .pmpcfg_n = s0.regs .pmpcfg_n := by
    leaf_peel .pmpcfg_n
  -- THE ONE NEW PEEL: the address register the TOR grant is about
  have lpaddr_s : ((s0.setReg .minstret_increment b).setReg .nextPC npc).regs
      .pmpaddr_n = s0.regs .pmpaddr_n := by
    leaf_peel .pmpaddr_n
  have lpma_s : ((s0.setReg .minstret_increment b).setReg .nextPC npc).regs
      .pma_regions = s0.regs .pma_regions := by
    leaf_peel .pma_regions
  have lhtif_s : ((s0.setReg .minstret_increment b).setReg .nextPC npc).regs
      .htif_tohost_base = none := by
    leaf_peel .htif_tohost_base; exact lhtif
  -- the base register
  have hbase : ((s0.setReg .minstret_increment b).setReg .nextPC npc).gpr rs1 = s0.gpr rs1 :=
    uxaXget_congr _ _ (fun r hr => by
      rw [setLookupNe r .nextPC _ _ (WeakLeafLd8.gprsNe r hr).2,
        setLookupNe r .minstret_increment _ _ (WeakLeafLd8.gprsNe r hr).1]) rs1
  have hea' : ((s0.setReg .minstret_increment b).setReg .nextPC npc).gpr rs1 +
      sign_extend (m := 64) imm = ea := by rw [hbase]; exact hea
  have h := execEffExecuteLOAD8Gpr rs1 rd imm v ramRegion
    ((s0.setReg .minstret_increment b).setReg .nextPC npc) hrd lpriv_s
    (by rw [lms_s]; exact lmprv) (by rw [lsec_s]; exact lpmm) (by rw [hea']; exact hal)
    (by
      rw [hea']
      -- THE TOR ARM, in place of `execEffPmpCheckMachineNone`
      exact WeakLeafTor.execEffPmpCheckMachineTor0 ea 8 _ _
        (by rw [lpmpc_s, lpaddr_s]; exact htor) (fun _ => ⟨_, rfl⟩) (by decide))
    (by rw [lpma_s, lpma, hea']; exact matching_pma_ram ea 8 hram (by decide) (by decide))
    (by rw [hea']; exact hal)
    (by first | rfl | decide +kernel)
    (by rw [hea', within_clint_ram ea 8 hram]; rfl)
    (by
      first
      | rfl
      | (simp only [within_sig, plat_have_sig, Functions.not]; rfl))
    (by rw [hea']; exact execEffWithinHtifFalse _ 8 _ lhtif_s)
    (by rw [hea']; exact devAddrRam ea 8 hram)
    (by rw [hea']; exact hbytes)
  rw [hea', WeakLeafLd8.extendValueFalse64] at h
  exact h

/-- Rocq `exec_eff_sd8_tor_at` (deviations 1, 3, 6). -/
theorem execEffSd8TorAt (s0 : ExecSt) (b : Bool) (npc : BitVec 64) (rs1 rs2 : BitVec 5)
    (imm : BitVec 12) (ea vs : BitVec 64) :
    s0.regs .cur_privilege = .Machine →
    (_get_Mstatus_MPRV (s0.regs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (s0.regs .mseccfg)) = .PMM_Disabled →
    pmpTor0Grants (s0.regs .pmpcfg_n) (s0.regs .pmpaddr_n) ea 8 →
    s0.regs .pma_regions = bootPMA →
    s0.regs .htif_tohost_base = none →
    s0.gpr rs1 + sign_extend (m := 64) imm = ea →
    s0.gpr rs2 = vs →
    is_aligned_paddr (.Physaddr ea) 8 = true →
    inRam ea 8 →
    execEff (execute (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)))
        ((s0.setReg .minstret_increment b).setReg .nextPC npc) =
      some (RETIRE_SUCCESS,
        ⟨((s0.setReg .minstret_increment b).setReg .nextPC npc).regs,
          bmWrite s0.mem ea 8 vs, s0.dev⟩,
        [.WEwrite wakPlain ea 8 vs]) := by
  intro lpriv lmprv lpmm htor lpma lhtif hea hvs hal hram
  obtain ⟨s, hs⟩ : ∃ s, s = (s0.setReg .minstret_increment b).setReg .nextPC npc := ⟨_, rfl⟩
  rw [← hs]
  have lpriv_s : s.regs .cur_privilege = .Machine := by rw [hs]; leaf_peel .cur_privilege; exact lpriv
  have lms_s : s.regs .mstatus = s0.regs .mstatus := by rw [hs]; leaf_peel .mstatus
  have lsec_s : s.regs .mseccfg = s0.regs .mseccfg := by rw [hs]; leaf_peel .mseccfg
  have lpmpc_s : s.regs .pmpcfg_n = s0.regs .pmpcfg_n := by rw [hs]; leaf_peel .pmpcfg_n
  have lpaddr_s : s.regs .pmpaddr_n = s0.regs .pmpaddr_n := by rw [hs]; leaf_peel .pmpaddr_n
  have lpma_s : s.regs .pma_regions = bootPMA := by rw [hs]; leaf_peel .pma_regions; exact lpma
  have lhtif_s : s.regs .htif_tohost_base = none := by
    rw [hs]; leaf_peel .htif_tohost_base; exact lhtif
  have hgea : s.gpr rs1 + sign_extend (m := 64) imm = ea := by
    rw [hs, WeakLeafSd8.gprSetRegNe _ _ _ _ (by decide), WeakLeafSd8.gprSetRegNe _ _ _ _ (by decide)]
    exact hea
  have hgvs : s.gpr rs2 = vs := by
    rw [hs, WeakLeafSd8.gprSetRegNe _ _ _ _ (by decide), WeakLeafSd8.gprSetRegNe _ _ _ _ (by decide)]
    exact hvs
  have hmem : s.mem = s0.mem := by rw [hs]; rfl
  have hdev : s.dev = s0.dev := by rw [hs]; rfl
  have key := execEffExecuteSTORE8Gpr rs2 rs1 imm ramRegion s lpriv_s
    (by rw [lms_s]; exact lmprv) (by rw [lsec_s]; exact lpmm) (by rw [hgea]; exact hal)
    (by
      rw [hgea]
      exact WeakLeafTor.execEffPmpCheckMachineTor0 ea 8 _ s
        (by rw [lpmpc_s, lpaddr_s]; exact htor) (fun _ => ⟨_, rfl⟩) (by decide))
    (by rw [hgea, lpma_s]; exact matching_pma_ram ea 8 hram (by omega) (by omega))
    (by rw [hgea]; exact hal)
    (by first | rfl | decide +kernel)
    (by rw [hgea, within_clint_ram ea 8 hram]; rfl)
    (by
      first
      | rfl
      | (simp only [within_sig, plat_have_sig, Functions.not]; rfl))
    (by rw [hgea]; exact execEffWithinHtifWFalse ea 8 s lhtif_s)
    (by rw [hgea]; exact devAddrRam ea 8 hram)
  rw [hgea, hgvs, hmem] at key
  rw [key, ← hdev]
  rfl

/-! ## 2. THE THREE `wPEff` HALVES -/

section wPEffHalves
variable {GF : BundledGFunctors} [WeakGS GF]

/-- Rocq `wP_eff_ld8_tor` (deviations 1-2, 5). -/
theorem wPEffLd8Tor (al4 : Bool) (cid : Nat) (σ : Wmstate) (pc : BitVec 64) (h : BitVec 16)
    (rs1 rd : BitVec 5) (imm : BitVec 12) (i0 : instruction) (ea : PAddr) (v : BitVec 64)
    (dq : DFrac) (D D0 : Register → Bool) (dst : ExecSt) :
    wlogWf σ.wmLog →
    -- the M-mode config tower, at σ's own registers
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    pmpAllowsAll (σ.wmRegs .pmpcfg_n) →
    pmpTor0Grants (σ.wmRegs .pmpcfg_n) (σ.wmRegs .pmpaddr_n) ea 8 →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (_get_Mstatus_MPRV (σ.wmRegs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (σ.wmRegs .mseccfg)) = .PMM_Disabled →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    -- the instruction's pure geometry
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rd.toNat ≠ 0 →
    (wflatSt σ).gpr rs1 + sign_extend (m := 64) imm = ea →
    inRam ea 8 →
    -- the COMPRESSED decode and its expansion
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s =
      some (.ExecuteAs (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)), s)) →
    -- the resources
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      winstrBytes (GF := GF) pc (.F_RVC h) -∗
      vwpHold (wpt8 (GF := GF) ea dq v) σ.wmWs -∗
      ⌜wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++
        [.WEread wakPlain ea 8]) σ⌝ := by
  intro hwf lpc lpriv lpmp htor lpma lhtif lhart lmisaS lmisaC lmIE lmprv lpmm lelp hal2 hal4 hrd
    hea hram8 hagree hDmi hgood hdec hgood0 hexp
  iintro Hlat #Hbs Hpt
  ihave %haccpc := winstrBytesAccWf pc (.F_RVC h) $$ Hbs
  icases keepPure (winstrBytesLookup σ pc (.F_RVC h) hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc (.F_RVC h) hwf) $$ Hlat Hbs with ⟨%htp, Hlat, -⟩
  icases keepPure1 (wpt8Align ea dq v σ.wmWs) $$ Hpt with ⟨%halea, Hpt⟩
  ihave %hld := wwpLd8 σ ea dq v hwf $$ Hlat Hpt
  ipureintro
  obtain ⟨⟨haccea, hpinea⟩, hflat8⟩ := hld
  obtain ⟨-, ⟨-, hrampc, w, ⟨hsub, hisRVC⟩, htext⟩⟩ := hfok
  apply wPEffOfLeafRvc al4 cid σ (wwin pc ea 8) pc h w i0 (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8))
    [.WEread wakPlain ea 8] D D0 dst hwf
    (wwinNonzero pc ea 8 (fun j hj => WeakLeafWin.inRamByte pc 4 j hrampc hj)
      (fun j hj => WeakLeafWin.inRamByte ea 8 j hram8 hj))
    (wwinPinned σ pc ea 8 haccpc haccea (fun j hj => (htp j hj).1) hpinea)
  · exact WeakLeafTor.fetchPinRvc al4 σ pc _ (fun ak pa n he => by cases he; rfl)
      (fun j hj => (htp j hj).2)
  · exact lpc
  · exact lpriv
  · exact lpmp
  · exact lpma
  · exact lhtif
  · exact lhart
  · exact lmisaS
  · exact lmisaC
  · exact lmIE
  · exact lelp
  · exact hal2
  · exact hal4
  · exact hrampc
  · exact wwinConfText σ pc ea 8 w htext
  · exact hsub
  · exact hisRVC
  · exact hagree
  · exact hDmi
  · exact hgood
  · exact hdec
  · exact hgood0
  · exact hexp
  · intro b
    have hfacts := loadSexecFacts ⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ b
      (BitVec.addInt pc 2) rd v
    have hea_c : (⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ : ExecSt).gpr rs1 +
        sign_extend (m := 64) imm = ea := by
      unfold ExecSt.gpr at hea ⊢; exact hea
    have hbytes_c := WeakLeafLd8.confBytes σ (wwin pc ea 8) ea 8 v
      (fun j hj => wwinData pc ea 8 j hj) hflat8
    have hrun := execEffLd8TorAt ⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ b
      (BitVec.addInt pc 2) rs1 rd imm ea v hrd lpriv lmprv lpmm htor lpma lhtif hea_c halea hram8
      hbytes_c
    refine ⟨_, hrun, ?_, ?_, ?_⟩
    · rw [hfacts.1]; exact lhart
    · exact hfacts.2.1
    · rw [hfacts.2.2.1]
      exact WeakLeafLd8.confDom σ (wwin pc ea 8) σ.wmRegs σ.wmDev

/-- Rocq `wP_eff_ld8_tor_own` (deviations 1-2, 5): `wPEffLd8Tor` over the
OWNED doubleword. -/
theorem wPEffLd8TorOwn (al4 : Bool) (cid : Nat) (σ : Wmstate) (pc : BitVec 64) (h : BitVec 16)
    (rs1 rd : BitVec 5) (imm : BitVec 12) (i0 : instruction) (ea : PAddr) (v : BitVec 64)
    (cid8 : CPU) (D D0 : Register → Bool) (dst : ExecSt) :
    wlogWf σ.wmLog →
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    pmpAllowsAll (σ.wmRegs .pmpcfg_n) →
    pmpTor0Grants (σ.wmRegs .pmpcfg_n) (σ.wmRegs .pmpaddr_n) ea 8 →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (_get_Mstatus_MPRV (σ.wmRegs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (σ.wmRegs .mseccfg)) = .PMM_Disabled →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rd.toNat ≠ 0 →
    (wflatSt σ).gpr rs1 + sign_extend (m := 64) imm = ea →
    inRam ea 8 →
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s =
      some (.ExecuteAs (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)), s)) →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      winstrBytes (GF := GF) pc (.F_RVC h) -∗
      vwpHold (wpt8Own (GF := GF) cid8 ea v) σ.wmWs -∗
      ⌜wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++
        [.WEread wakPlain ea 8]) σ⌝ := by
  intro hwf lpc lpriv lpmp htor lpma lhtif lhart lmisaS lmisaC lmIE lmprv lpmm lelp hal2 hal4 hrd
    hea hram8 hagree hDmi hgood hdec hgood0 hexp
  iintro Hlat #Hbs Hpt
  ihave %haccpc := winstrBytesAccWf pc (.F_RVC h) $$ Hbs
  icases keepPure (winstrBytesLookup σ pc (.F_RVC h) hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc (.F_RVC h) hwf) $$ Hlat Hbs with ⟨%htp, Hlat, -⟩
  icases keepPure1 (wpt8OwnAlign cid8 ea v σ.wmWs) $$ Hpt with ⟨%halea, Hpt⟩
  ihave %hld := wwpLd8Own cid8 σ ea v hwf $$ Hlat Hpt
  ipureintro
  obtain ⟨⟨haccea, hpinea⟩, hflat8⟩ := hld
  obtain ⟨-, ⟨-, hrampc, w, ⟨hsub, hisRVC⟩, htext⟩⟩ := hfok
  apply wPEffOfLeafRvc al4 cid σ (wwin pc ea 8) pc h w i0 (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8))
    [.WEread wakPlain ea 8] D D0 dst hwf
    (wwinNonzero pc ea 8 (fun j hj => WeakLeafWin.inRamByte pc 4 j hrampc hj)
      (fun j hj => WeakLeafWin.inRamByte ea 8 j hram8 hj))
    (wwinPinned σ pc ea 8 haccpc haccea (fun j hj => (htp j hj).1) hpinea)
  · exact WeakLeafTor.fetchPinRvc al4 σ pc _ (fun ak pa n he => by cases he; rfl)
      (fun j hj => (htp j hj).2)
  · exact lpc
  · exact lpriv
  · exact lpmp
  · exact lpma
  · exact lhtif
  · exact lhart
  · exact lmisaS
  · exact lmisaC
  · exact lmIE
  · exact lelp
  · exact hal2
  · exact hal4
  · exact hrampc
  · exact wwinConfText σ pc ea 8 w htext
  · exact hsub
  · exact hisRVC
  · exact hagree
  · exact hDmi
  · exact hgood
  · exact hdec
  · exact hgood0
  · exact hexp
  · intro b
    have hfacts := loadSexecFacts ⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ b
      (BitVec.addInt pc 2) rd v
    have hea_c : (⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ : ExecSt).gpr rs1 +
        sign_extend (m := 64) imm = ea := by
      unfold ExecSt.gpr at hea ⊢; exact hea
    have hbytes_c := WeakLeafLd8.confBytes σ (wwin pc ea 8) ea 8 v
      (fun j hj => wwinData pc ea 8 j hj) hflat8
    have hrun := execEffLd8TorAt ⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ b
      (BitVec.addInt pc 2) rs1 rd imm ea v hrd lpriv lmprv lpmm htor lpma lhtif hea_c halea hram8
      hbytes_c
    refine ⟨_, hrun, ?_, ?_, ?_⟩
    · rw [hfacts.1]; exact lhart
    · exact hfacts.2.1
    · rw [hfacts.2.2.1]
      exact WeakLeafLd8.confDom σ (wwin pc ea 8) σ.wmRegs σ.wmDev

/-- Rocq `wP_eff_sd8_tor` (deviations 1-2, 5). -/
theorem wPEffSd8Tor (al4 : Bool) (cid : Nat) (σ : Wmstate) (pc : BitVec 64) (h : BitVec 16)
    (rs1 rs2 : BitVec 5) (imm : BitVec 12) (i0 : instruction) (ea : PAddr) (vold vs : BitVec 64)
    (cid8 : CPU) (D D0 : Register → Bool) (dst : ExecSt) :
    wlogWf σ.wmLog →
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    pmpAllowsAll (σ.wmRegs .pmpcfg_n) →
    pmpTor0Grants (σ.wmRegs .pmpcfg_n) (σ.wmRegs .pmpaddr_n) ea 8 →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (_get_Mstatus_MPRV (σ.wmRegs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (σ.wmRegs .mseccfg)) = .PMM_Disabled →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    (wflatSt σ).gpr rs1 + sign_extend (m := 64) imm = ea →
    (wflatSt σ).gpr rs2 = vs →
    inRam ea 8 →
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s =
      some (.ExecuteAs (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)), s)) →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      winstrBytes (GF := GF) pc (.F_RVC h) -∗
      vwpHold (wpt8Own (GF := GF) cid8 ea vold) σ.wmWs -∗
      ⌜wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++
        [.WEwrite wakPlain ea 8 vs]) σ⌝ := by
  intro hwf lpc lpriv lpmp htor lpma lhtif lhart lmisaS lmisaC lmIE lmprv lpmm lelp hal2 hal4 hea
    hvs hram hagree hDmi hgood hdec hgood0 hexp
  iintro Hlat #Hbs Hpt
  ihave %haccpc := winstrBytesAccWf pc (.F_RVC h) $$ Hbs
  icases keepPure (winstrBytesLookup σ pc (.F_RVC h) hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc (.F_RVC h) hwf) $$ Hlat Hbs with ⟨%htp, Hlat, -⟩
  icases keepPure1 (wpt8OwnAlign cid8 ea vold σ.wmWs) $$ Hpt with ⟨%halea, Hpt⟩
  ihave %hfp := wpt8OwnFlatPin cid8 σ ea vold hwf $$ Hlat Hpt
  ipureintro
  obtain ⟨haccea, hflatpin⟩ := hfp
  obtain ⟨-, ⟨-, hrampc, w, ⟨hsub, hisRVC⟩, htext⟩⟩ := hfok
  apply wPEffOfLeafRvc al4 cid σ (wwin pc ea 8) pc h w i0 (.STORE (imm, .Regidx rs2, .Regidx rs1, 8))
    [.WEwrite wakPlain ea 8 vs] D D0 dst hwf
    (wwinNonzero pc ea 8 (fun j hj => WeakLeafWin.inRamByte pc 4 j hrampc hj)
      (fun j hj => WeakLeafWin.inRamByte ea 8 j hram hj))
    (wwinPinned σ pc ea 8 haccpc haccea (fun j hj => (htp j hj).1) (fun j hj => (hflatpin j hj).2))
  · exact WeakLeafTor.fetchPinRvc al4 σ pc _ (fun ak pa n he => by cases he)
      (fun j hj => (htp j hj).2)
  · exact lpc
  · exact lpriv
  · exact lpmp
  · exact lpma
  · exact lhtif
  · exact lhart
  · exact lmisaS
  · exact lmisaC
  · exact lmIE
  · exact lelp
  · exact hal2
  · exact hal4
  · exact hrampc
  · exact wwinConfText σ pc ea 8 w htext
  · exact hsub
  · exact hisRVC
  · exact hagree
  · exact hDmi
  · exact hgood
  · exact hdec
  · exact hgood0
  · exact hexp
  · intro b
    have hfacts := storeRegsFacts ⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ b
      (BitVec.addInt pc 2)
    have hea_c : (⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ : ExecSt).gpr rs1 +
        sign_extend (m := 64) imm = ea := by
      unfold ExecSt.gpr at hea ⊢; exact hea
    have hvs_c : (⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ : ExecSt).gpr rs2 = vs := by
      unfold ExecSt.gpr at hvs ⊢; exact hvs
    have hrun := execEffSd8TorAt ⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ b
      (BitVec.addInt pc 2) rs1 rs2 imm ea vs lpriv lmprv lpmm htor lpma lhtif hea_c hvs_c halea hram
    refine ⟨_, hrun, ?_, ?_, ?_⟩
    · exact hfacts.1.trans lhart
    · exact hfacts.2.1
    · dsimp only
      exact wwinWdom σ pc ea 8 vs

end wPEffHalves

/-! ## 2b. THE CONFIG HALVES (deviation 4, Lean-only) -/

section confHalves
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- Lean-only: a register cell at `p + q` is the two cells at `p` and `q`. -/
theorem WeakLeafTor.regSplit (cpu : CPU) (r : Register) (p q : Qp) (v : RegisterType r) :
    regPointsTo (hlc := hlc) (GF := GF) cpu r (DFrac.own (p + q)) v ⊢
      regPointsTo cpu r (DFrac.own p) v ∗ regPointsTo cpu r (DFrac.own q) v := by
  unfold regPointsTo regPointsToAt
  exact ((ghost_map_elem_fractional _ _ _).fractional p q).mp

/-- Lean-only: ... and back. -/
theorem WeakLeafTor.regJoin (cpu : CPU) (r : Register) (p q : Qp) (v : RegisterType r) :
    regPointsTo (hlc := hlc) (GF := GF) cpu r (DFrac.own p) v ⊢
      regPointsTo cpu r (DFrac.own q) v -∗ regPointsTo cpu r (DFrac.own (p + q)) v := by
  unfold regPointsTo regPointsToAt
  exact wand_intro ((ghost_map_elem_fractional _ _ _).fractional p q).mpr

/-- Lean-only: `mConf` at `p + q` is `mConf` at `p` and at `q`. -/
theorem WeakLeafTor.mConfSplit (cpu : CPU) (p q : Qp) (c : MConf) :
    mConf (GF := GF) cpu (DFrac.own (p + q)) c ⊢
      mConf cpu (DFrac.own p) c ∗ mConf cpu (DFrac.own q) c := by
  iintro H
  icases mConf_cases cpu _ c $$ H with
    ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, #Hhw⟩
  icases WeakLeafTor.regSplit cpu _ p q _ $$ H1 with ⟨A1, B1⟩
  icases WeakLeafTor.regSplit cpu _ p q _ $$ H2 with ⟨A2, B2⟩
  icases WeakLeafTor.regSplit cpu _ p q _ $$ H3 with ⟨A3, B3⟩
  icases WeakLeafTor.regSplit cpu _ p q _ $$ H4 with ⟨A4, B4⟩
  icases WeakLeafTor.regSplit cpu _ p q _ $$ H5 with ⟨A5, B5⟩
  icases WeakLeafTor.regSplit cpu _ p q _ $$ H6 with ⟨A6, B6⟩
  icases WeakLeafTor.regSplit cpu _ p q _ $$ H7 with ⟨A7, B7⟩
  icases WeakLeafTor.regSplit cpu _ p q _ $$ H8 with ⟨A8, B8⟩
  icases WeakLeafTor.regSplit cpu _ p q _ $$ H9 with ⟨A9, B9⟩
  icases WeakLeafTor.regSplit cpu _ p q _ $$ H10 with ⟨A10, B10⟩
  icases WeakLeafTor.regSplit cpu _ p q _ $$ H11 with ⟨A11, B11⟩
  icases WeakLeafTor.regSplit cpu _ p q _ $$ H12 with ⟨A12, B12⟩
  icases WeakLeafTor.regSplit cpu _ p q _ $$ H13 with ⟨A13, B13⟩
  icases WeakLeafTor.regSplit cpu _ p q _ $$ H14 with ⟨A14, B14⟩
  ihave Hp := mConf_introW cpu (DFrac.own p) c $$ A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 Hhw
  ihave Hq := mConf_introW cpu (DFrac.own q) c $$ B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 B13 B14 Hhw
  isplitl [Hp]
  · iexact Hp
  · iexact Hq

/-- Lean-only: ... and back. -/
theorem WeakLeafTor.mConfJoin (cpu : CPU) (p q : Qp) (c : MConf) :
    mConf (GF := GF) cpu (DFrac.own p) c ⊢
      mConf cpu (DFrac.own q) c -∗ mConf cpu (DFrac.own (p + q)) c := by
  iintro Hp Hq
  icases mConf_cases cpu _ c $$ Hp with
    ⟨A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, #Hhw⟩
  icases mConf_cases cpu _ c $$ Hq with
    ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, -⟩
  ihave C1 := WeakLeafTor.regJoin cpu _ p q _ $$ A1 B1
  ihave C2 := WeakLeafTor.regJoin cpu _ p q _ $$ A2 B2
  ihave C3 := WeakLeafTor.regJoin cpu _ p q _ $$ A3 B3
  ihave C4 := WeakLeafTor.regJoin cpu _ p q _ $$ A4 B4
  ihave C5 := WeakLeafTor.regJoin cpu _ p q _ $$ A5 B5
  ihave C6 := WeakLeafTor.regJoin cpu _ p q _ $$ A6 B6
  ihave C7 := WeakLeafTor.regJoin cpu _ p q _ $$ A7 B7
  ihave C8 := WeakLeafTor.regJoin cpu _ p q _ $$ A8 B8
  ihave C9 := WeakLeafTor.regJoin cpu _ p q _ $$ A9 B9
  ihave C10 := WeakLeafTor.regJoin cpu _ p q _ $$ A10 B10
  ihave C11 := WeakLeafTor.regJoin cpu _ p q _ $$ A11 B11
  ihave C12 := WeakLeafTor.regJoin cpu _ p q _ $$ A12 B12
  ihave C13 := WeakLeafTor.regJoin cpu _ p q _ $$ A13 B13
  ihave C14 := WeakLeafTor.regJoin cpu _ p q _ $$ A14 B14
  ihave Hm := mConf_introW cpu (DFrac.own (p + q)) c $$ C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 Hhw
  iexact Hm

/-- Lean-only: `mConf` at `q` is two halves. -/
theorem WeakLeafTor.mConfHalves (cpu : CPU) (q : Qp) (c : MConf) :
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      mConf cpu (DFrac.own q.half) c ∗ mConf cpu (DFrac.own q.half) c := by
  have h := WeakLeafTor.mConfSplit (GF := GF) cpu q.half q.half c
  rw [Qp.half_add_half] at h
  exact h

/-- Lean-only: two halves are `mConf` at `q`. -/
theorem WeakLeafTor.mConfJoinHalves (cpu : CPU) (q : Qp) (c : MConf) :
    mConf (GF := GF) cpu (DFrac.own q.half) c ⊢
      mConf cpu (DFrac.own q.half) c -∗ mConf cpu (DFrac.own q) c := by
  have h := WeakLeafTor.mConfJoin (GF := GF) cpu q.half q.half c
  rw [Qp.half_add_half] at h
  exact h

/-- Lean-only (Rocq `reg_valid_dq` on the `pmpaddr_n` cell): what `mConf`
pins of `pmpaddr_n` at a register file. -/
theorem WeakLeafTor.mConfPmpaddr (cpu : CPU) (dq : DFrac) (c : MConf) (f : RegFile) :
    regInterp (hlc := hlc) (GF := GF) cpu f ⊢ mConf cpu dq c -∗ ⌜f .pmpaddr_n = c.pmpaddr⌝ := by
  iintro Hr Hm
  icases mConf_cases cpu dq c $$ Hm with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, H14, -⟩
  ihave %E := wand_intro (reg_valid cpu f .pmpaddr_n dq c.pmpaddr) $$ Hr H14
  ipureintro
  exact E

end confHalves

/-! ## 3. THE THREE LEAVES -/

section leaves
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_ld8_tor_rvc_leaf` (deviations 1-4): the compressed width-8 LOAD. -/
theorem wwpLd8TorRvcLeaf (al4 : Bool) (gen : Nat) (cpu : CPU) (pc : BitVec 64) (h : BitVec 16)
    (rs1 rd : BitVec 5) (imm : BitVec 12) (i0 : instruction) (ea : PAddr) (v : BitVec 64)
    (dqv : DFrac) (q : Qp) (c : MConf) (rs1v rd0 npc0 : BitVec 64) (D D0 : Register → Bool)
    (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    pmpTor0Grants c.pmpcfg c.pmpaddr ea 8 →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rs1.toNat ≠ 0 →
    rd.toNat ≠ 0 →
    rs1v + sign_extend (m := 64) imm = ea →
    inRam ea 8 →
    -- the decode, in the two shapes its two consumers ask for
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      ∃ i0' : instruction,
        exec (decodeFetch (.F_RVC h)) t = some (i0', t) ∧
        is_lpad_instruction i0' = false ∧
        (∀ s : ExecSt, exec (execute i0') s =
          some (.ExecuteAs (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)), s))) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s =
      some (.ExecuteAs (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)), s)) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrBytes (GF := GF) pc (.F_RVC h) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold (wpt8 (GF := GF) ea dqv v) ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rd (DFrac.own 1) v -∗
        hartWs cpu ws' -∗
        vwpHold (wpt8 (GF := GF) ea dqv v) ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp htor hal2 hal4 hrs1nz hrd hea hram8 hdecf hagree hDmi hgood hdec hgood0 hexp
  iintro Hm Hclk Hpc Hnpc Hrs1c Hrdc #Hbs Hhws Hpt Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_RVC h) $$ Hbs
  have hdecW : winstrDec (.F_RVC h) (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)) := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc true (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8))
    (.F_RVC h) (by first | rfl | decide) rfl hdecW $$ Hbs
  -- half of the config goes to the funnel; the other half pins `pmpaddr_n`
  icases WeakLeafTor.mConfHalves cpu q c $$ Hm with ⟨Hm1, Hm2⟩
  have hcert : wstepCert cpu.val pc
      (wPEff (some cpu.val) ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++
        [.WEread wakPlain ea 8])) (wQLoadW 8 ea) :=
    wcertLoadW 8 cpu.val pc WeakFetchEff.wakIfetch pc (if al4 then 4 else 2) wakPlain ea rfl
  iapply wwpInstr gen cpu pc true (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)) c (DFrac.own q.half)
    (wPEff (some cpu.val) ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++
      [.WEread wakPlain ea 8]))
    (wQFr (wQLoadW 8 ea) (some cpu.val)
      ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++ [.WEread wakPlain ea 8]))
    hgid haccpc hmok hpmp (wstepCertFr _ _ _ _ hcert) $$ Hm1 Hclk Hpc Hwi
  unfold wwpCb
  iintro %σ %b %mt %ip %Lpc0 %hcfg Hlat Hreg Hnorg Hti Hip
  unfold wmstateNorg
  icases Hnorg with ⟨%hbnd, %hnv, %hwf, Hdev, Hlogauth, Hwsauth⟩
  ihave ⟨%hws, Hwsauth, Hhws⟩ := persistent_entails_right (hartWsAgree cpu σ.wmWs ws) $$ [Hwsauth Hhws]
  · iframe Hwsauth Hhws
  subst hws
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, Lmprv, Lpmm, Lelp⟩ := hcfg
  have LmisaC : (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true := by rw [Lmisa]; decide
  -- the TWO registers the funnel does not read: pmpaddr_n and the base
  icases keepPure (WeakLeafTor.mConfPmpaddr cpu _ c _) $$ Hreg Hm2 with ⟨%Lpaddra, Hreg, Hm2⟩
  have Lpaddr : σ.wmRegs .pmpaddr_n = c.pmpaddr :=
    (regAtFlat .pmpaddr_n σ b (by decide)).symm.trans Lpaddra
  icases keepPure (WeakLeafLw4.gprValid cpu _ rs1 _ rs1v hrs1nz) $$ Hreg Hrs1c with ⟨%Lrs1a, Hreg, Hrs1c⟩
  have Lrs1 : (wflatSt σ).gpr rs1 = rs1v := by
    rw [← WeakLeafLw4.gprSetNe (wflatSt σ) .minstret_increment b rs1 (by decide)]
    exact Lrs1a
  have hea_σ : (wflatSt σ).gpr rs1 + sign_extend (m := 64) imm = ea := by rw [Lrs1]; exact hea
  have hag_σ : ∀ r, D r = true → σ.wmRegs r = dst.regs r := hagree _ Lpriv Lmisa Lsec
  have lpmp_σ : pmpAllowsAll (σ.wmRegs .pmpcfg_n) := by rw [Lpmpc]; exact hpmp
  have htor_σ : pmpTor0Grants (σ.wmRegs .pmpcfg_n) (σ.wmRegs .pmpaddr_n) ea 8 := by
    rw [Lpmpc, Lpaddr]; exact htor
  -- ---- the certificate's precondition (§2) ----
  icases WeakLeafLw4.keepPure2 (wPEffLd8Tor al4 cpu.val σ pc h rs1 rd imm i0 ea v dqv D D0 dst hwf Lpc0
      Lpriv lpmp_σ htor_σ Lpma Lhtif Lhart LmisaS LmisaC LmIE Lmprv Lpmm Lelp hal2 hal4 hrd hea_σ hram8
      hag_σ hDmi hgood hdec hgood0 hexp) $$ Hlat Hbs Hpt with ⟨%HP, Hlat, -, Hpt⟩
  -- ---- the flat facts ----
  icases keepPure (wwpLd8 σ ea dqv v hwf) $$ Hlat Hpt with ⟨%hld, Hlat, Hpt⟩
  icases keepPure (winstrUnwritten σ pc (.F_RVC h) hwf) $$ Hlat Hbs with ⟨%hunw, Hlat, -⟩
  icases keepPure (nvOkWpt8 cpu σ.wmImg σ.wmLog ea dqv v σ.wmWs) $$ Hlat Hpt with ⟨%hnvea, Hlat, Hpt⟩
  icases keepPure1 (wpt8Align ea dqv v σ.wmWs) $$ Hpt with ⟨%halea, Hpt⟩
  -- ---- the run, at the FLAT state ----
  have hexf := execEffLd8TorAt (wflatSt σ) b (BitVec.addInt pc 2) rs1 rd imm ea v hrd Lpriv Lmprv Lpmm
    htor_σ Lpma Lhtif hea_σ halea hram8 hld.2
  have hfacts := loadSexecFacts (wflatSt σ) b (BitVec.addInt pc 2) rd v
  -- ---- the two register writes the `execute` performs ----
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 2))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [show (((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 2)) =
      (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).regs from rfl]
  imod WeakLeafLw4.gprUpdate cpu (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
      (BitVec.addInt pc 2)) rd rd0 v hrd $$ Hreg Hrdc with ⟨Hreg, Hrdc⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).setGpr rd v)
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ hexf
  isplitl [Hreg]
  · iexact Hreg
  isplitl [Hti Hip]
  · iexists mt, ip
    iframe Hti Hip
  inext
  iintro %tick %σ' %t %hstep %hdevt0 %hpost %hQ Hm' Hclk' Hpc'
  have hdevt : t.dev = σ.wmDev := by rw [hdevt0, hfacts.2.2.2.1]; rfl
  obtain ⟨hregs, hdevs, hmems, himgs, hlogs, hwsle, hwf', hbnd'⟩ := hpost
  obtain ⟨⟨hQi, hQl, -⟩, hQeff⟩ := hQ
  imod hartWsUpdate cpu σ.wmWs σ.wmWs σ'.wmWs $$ [$Hwsauth $Hhws] with ⟨Hwsauth, Hhws⟩
  imod Hclose
  -- the PC the funnel hands back IS pc+2
  rw [hfacts.2.2.2.2]
  imodintro
  isplitl [Hlat]
  · rw [hQi, hQl]; iexact Hlat
  isplitl [Hdev Hlogauth Hwsauth]
  · isplitr
    · ipureintro; exact hbnd'
    isplitr
    · ipureintro
      apply nvHartOfWQEffOk cpu σ σ' _ hQeff hnv
      intro a ha
      rw [hQl]
      rcases weffsTouchApp _ _ a ha with ha | ha
      · obtain ⟨j, hj, rfl⟩ := weffsTouchRead1 _ pc _ a ha
        exact nvOkUnwritten _ _ _ (hunw j (WeakLeafTor.ltFetchW al4 j hj))
      · obtain ⟨j, hj, rfl⟩ := weffsTouchRead1 _ ea _ a ha
        exact hnvea j hj
    isplitr
    · ipureintro; exact hwf'
    rw [hdevs, hdevt, hQl]
    iframe Hdev Hlogauth Hwsauth
  ihave Hpt' := wwpLd8Carry σ σ' t ea dqv v ⟨hregs, hdevs, hmems, himgs, hlogs, hwsle, hwf', hbnd'⟩ $$ Hpt
  -- the two config halves, joined
  ihave Hm := WeakLeafTor.mConfJoinHalves cpu q c $$ Hm' Hm2
  iapply Hcont $$ %σ'.wmWs %hwsle Hm Hclk' [Hpc' Hnpc] Hrs1c Hrdc Hhws Hpt'
  unfold pcIs
  iframe Hpc' Hnpc

/-- Rocq `wwp_ld8_tor_rvc_leaf_own` (deviations 1-4): `wwpLd8TorRvcLeaf` over
the OWNED doubleword `wpt8Own cpu ea v`. -/
theorem wwpLd8TorRvcLeafOwn (al4 : Bool) (gen : Nat) (cpu : CPU) (pc : BitVec 64) (h : BitVec 16)
    (rs1 rd : BitVec 5) (imm : BitVec 12) (i0 : instruction) (ea : PAddr) (v : BitVec 64)
    (q : Qp) (c : MConf) (rs1v rd0 npc0 : BitVec 64) (D D0 : Register → Bool)
    (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    pmpTor0Grants c.pmpcfg c.pmpaddr ea 8 →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rs1.toNat ≠ 0 →
    rd.toNat ≠ 0 →
    rs1v + sign_extend (m := 64) imm = ea →
    inRam ea 8 →
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      ∃ i0' : instruction,
        exec (decodeFetch (.F_RVC h)) t = some (i0', t) ∧
        is_lpad_instruction i0' = false ∧
        (∀ s : ExecSt, exec (execute i0') s =
          some (.ExecuteAs (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)), s))) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s =
      some (.ExecuteAs (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)), s)) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrBytes (GF := GF) pc (.F_RVC h) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold (wpt8Own (GF := GF) cpu ea v) ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rd (DFrac.own 1) v -∗
        hartWs cpu ws' -∗
        vwpHold (wpt8Own (GF := GF) cpu ea v) ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp htor hal2 hal4 hrs1nz hrd hea hram8 hdecf hagree hDmi hgood hdec hgood0 hexp
  iintro Hm Hclk Hpc Hnpc Hrs1c Hrdc #Hbs Hhws Hpt Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_RVC h) $$ Hbs
  have hdecW : winstrDec (.F_RVC h) (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)) := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc true (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8))
    (.F_RVC h) (by first | rfl | decide) rfl hdecW $$ Hbs
  icases WeakLeafTor.mConfHalves cpu q c $$ Hm with ⟨Hm1, Hm2⟩
  have hcert : wstepCert cpu.val pc
      (wPEff (some cpu.val) ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++
        [.WEread wakPlain ea 8])) (wQLoadW 8 ea) :=
    wcertLoadW 8 cpu.val pc WeakFetchEff.wakIfetch pc (if al4 then 4 else 2) wakPlain ea rfl
  iapply wwpInstr gen cpu pc true (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)) c (DFrac.own q.half)
    (wPEff (some cpu.val) ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++
      [.WEread wakPlain ea 8]))
    (wQFr (wQLoadW 8 ea) (some cpu.val)
      ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++ [.WEread wakPlain ea 8]))
    hgid haccpc hmok hpmp (wstepCertFr _ _ _ _ hcert) $$ Hm1 Hclk Hpc Hwi
  unfold wwpCb
  iintro %σ %b %mt %ip %Lpc0 %hcfg Hlat Hreg Hnorg Hti Hip
  unfold wmstateNorg
  icases Hnorg with ⟨%hbnd, %hnv, %hwf, Hdev, Hlogauth, Hwsauth⟩
  ihave ⟨%hws, Hwsauth, Hhws⟩ := persistent_entails_right (hartWsAgree cpu σ.wmWs ws) $$ [Hwsauth Hhws]
  · iframe Hwsauth Hhws
  subst hws
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, Lmprv, Lpmm, Lelp⟩ := hcfg
  have LmisaC : (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true := by rw [Lmisa]; decide
  icases keepPure (WeakLeafTor.mConfPmpaddr cpu _ c _) $$ Hreg Hm2 with ⟨%Lpaddra, Hreg, Hm2⟩
  have Lpaddr : σ.wmRegs .pmpaddr_n = c.pmpaddr :=
    (regAtFlat .pmpaddr_n σ b (by decide)).symm.trans Lpaddra
  icases keepPure (WeakLeafLw4.gprValid cpu _ rs1 _ rs1v hrs1nz) $$ Hreg Hrs1c with ⟨%Lrs1a, Hreg, Hrs1c⟩
  have Lrs1 : (wflatSt σ).gpr rs1 = rs1v := by
    rw [← WeakLeafLw4.gprSetNe (wflatSt σ) .minstret_increment b rs1 (by decide)]
    exact Lrs1a
  have hea_σ : (wflatSt σ).gpr rs1 + sign_extend (m := 64) imm = ea := by rw [Lrs1]; exact hea
  have hag_σ : ∀ r, D r = true → σ.wmRegs r = dst.regs r := hagree _ Lpriv Lmisa Lsec
  have lpmp_σ : pmpAllowsAll (σ.wmRegs .pmpcfg_n) := by rw [Lpmpc]; exact hpmp
  have htor_σ : pmpTor0Grants (σ.wmRegs .pmpcfg_n) (σ.wmRegs .pmpaddr_n) ea 8 := by
    rw [Lpmpc, Lpaddr]; exact htor
  icases WeakLeafLw4.keepPure2 (wPEffLd8TorOwn al4 cpu.val σ pc h rs1 rd imm i0 ea v cpu D D0 dst hwf
      Lpc0 Lpriv lpmp_σ htor_σ Lpma Lhtif Lhart LmisaS LmisaC LmIE Lmprv Lpmm Lelp hal2 hal4 hrd hea_σ
      hram8 hag_σ hDmi hgood hdec hgood0 hexp) $$ Hlat Hbs Hpt with ⟨%HP, Hlat, -, Hpt⟩
  icases keepPure (wwpLd8Own cpu σ ea v hwf) $$ Hlat Hpt with ⟨%hld, Hlat, Hpt⟩
  icases keepPure (winstrUnwritten σ pc (.F_RVC h) hwf) $$ Hlat Hbs with ⟨%hunw, Hlat, -⟩
  icases keepPure (nvOkWpt8Own cpu σ.wmImg σ.wmLog ea v σ.wmWs) $$ Hlat Hpt with ⟨%hnvea, Hlat, Hpt⟩
  icases keepPure1 (wpt8OwnAlign cpu ea v σ.wmWs) $$ Hpt with ⟨%halea, Hpt⟩
  have hexf := execEffLd8TorAt (wflatSt σ) b (BitVec.addInt pc 2) rs1 rd imm ea v hrd Lpriv Lmprv Lpmm
    htor_σ Lpma Lhtif hea_σ halea hram8 hld.2
  have hfacts := loadSexecFacts (wflatSt σ) b (BitVec.addInt pc 2) rd v
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 2))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [show (((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 2)) =
      (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).regs from rfl]
  imod WeakLeafLw4.gprUpdate cpu (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
      (BitVec.addInt pc 2)) rd rd0 v hrd $$ Hreg Hrdc with ⟨Hreg, Hrdc⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).setGpr rd v)
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ hexf
  isplitl [Hreg]
  · iexact Hreg
  isplitl [Hti Hip]
  · iexists mt, ip
    iframe Hti Hip
  inext
  iintro %tick %σ' %t %hstep %hdevt0 %hpost %hQ Hm' Hclk' Hpc'
  have hdevt : t.dev = σ.wmDev := by rw [hdevt0, hfacts.2.2.2.1]; rfl
  obtain ⟨hregs, hdevs, hmems, himgs, hlogs, hwsle, hwf', hbnd'⟩ := hpost
  obtain ⟨⟨hQi, hQl, -⟩, hQeff⟩ := hQ
  imod hartWsUpdate cpu σ.wmWs σ.wmWs σ'.wmWs $$ [$Hwsauth $Hhws] with ⟨Hwsauth, Hhws⟩
  imod Hclose
  rw [hfacts.2.2.2.2]
  imodintro
  isplitl [Hlat]
  · rw [hQi, hQl]; iexact Hlat
  isplitl [Hdev Hlogauth Hwsauth]
  · isplitr
    · ipureintro; exact hbnd'
    isplitr
    · ipureintro
      apply nvHartOfWQEffOk cpu σ σ' _ hQeff hnv
      intro a ha
      rw [hQl]
      rcases weffsTouchApp _ _ a ha with ha | ha
      · obtain ⟨j, hj, rfl⟩ := weffsTouchRead1 _ pc _ a ha
        exact nvOkUnwritten _ _ _ (hunw j (WeakLeafTor.ltFetchW al4 j hj))
      · obtain ⟨j, hj, rfl⟩ := weffsTouchRead1 _ ea _ a ha
        exact hnvea j hj
    isplitr
    · ipureintro; exact hwf'
    rw [hdevs, hdevt, hQl]
    iframe Hdev Hlogauth Hwsauth
  ihave Hpt' := wwpLd8OwnCarry cpu σ σ' t ea v ⟨hregs, hdevs, hmems, himgs, hlogs, hwsle, hwf', hbnd'⟩
    $$ Hpt
  ihave Hm := WeakLeafTor.mConfJoinHalves cpu q c $$ Hm' Hm2
  iapply Hcont $$ %σ'.wmWs %hwsle Hm Hclk' [Hpc' Hnpc] Hrs1c Hrdc Hhws Hpt'
  unfold pcIs
  iframe Hpc' Hnpc

/-- Rocq `wwp_sd8_tor_rvc_leaf` (deviations 1-4, 6): the compressed width-8
STORE.  The window comes back at the STORED value and the successor's view;
the continuation gains the store's timestamp `T` with its per-byte floor fact
and the release payload `R` frozen at `viewScl T`. -/
theorem wwpSd8TorRvcLeaf (al4 : Bool) (gen : Nat) (cpu : CPU) (pc : BitVec 64) (h : BitVec 16)
    (rs1 rs2 : BitVec 5) (imm : BitVec 12) (i0 : instruction) (ea : PAddr) (vold : BitVec 64)
    (R : VProp GF) (q : Qp) (c : MConf) (rs1v rs2v npc0 : BitVec 64) (D D0 : Register → Bool)
    (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    pmpTor0Grants c.pmpcfg c.pmpaddr ea 8 →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rs1.toNat ≠ 0 →
    rs2.toNat ≠ 0 →
    rs1v + sign_extend (m := 64) imm = ea →
    inRam ea 8 →
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      ∃ i0' : instruction,
        exec (decodeFetch (.F_RVC h)) t = some (i0', t) ∧
        is_lpad_instruction i0' = false ∧
        (∀ s : ExecSt, exec (execute i0') s =
          some (.ExecuteAs (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)), s))) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s =
      some (.ExecuteAs (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)), s)) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      gpr cpu rs2 (DFrac.own 1) rs2v -∗
      winstrBytes (GF := GF) pc (.F_RVC h) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold (wpt8Own (GF := GF) cpu ea vold) ws -∗
      vwpHold R ws -∗
      (∀ (ws' : Wstate) (T : Nat),
        ⌜wsLe ws ws'⌝ -∗
        ⌜∀ j : Nat, j < 8 → T ≤ flr (wsView ws') (WeakInterp.accAddr ea j)⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rs2 (DFrac.own 1) rs2v -∗
        hartWs cpu ws' -∗
        vwpHold (wpt8Own (GF := GF) cpu ea rs2v) ws' -∗
        R.monPred_at (viewScl T) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp htor hal2 hal4 hrs1nz hrs2nz hea hram hdecf hagree hDmi hgood hdec hgood0 hexp
  iintro Hm Hclk Hpc Hnpc Hrs1c Hrs2c #Hbs Hhws Hpt HR Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_RVC h) $$ Hbs
  have hdecW : winstrDec (.F_RVC h) (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc true (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) (.F_RVC h)
    (by first | rfl | decide) rfl hdecW $$ Hbs
  icases WeakLeafTor.mConfHalves cpu q c $$ Hm with ⟨Hm1, Hm2⟩
  have hcert : wstepCert cpu.val pc
      (wPEff (some cpu.val) ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++
        [.WEwrite wakPlain ea 8 rs2v])) (wQStore8 (some cpu.val) ea rs2v) :=
    wcertStoreW 8 cpu.val pc WeakFetchEff.wakIfetch pc (if al4 then 4 else 2) wakPlain ea rs2v
  iapply wwpInstr gen cpu pc true (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) c (DFrac.own q.half)
    (wPEff (some cpu.val) ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++
      [.WEwrite wakPlain ea 8 rs2v]))
    (wQFr (wQStore8 (some cpu.val) ea rs2v) (some cpu.val)
      ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++ [.WEwrite wakPlain ea 8 rs2v]))
    hgid haccpc hmok hpmp (wstepCertFr _ _ _ _ hcert) $$ Hm1 Hclk Hpc Hwi
  unfold wwpCb
  iintro %σ %b %mt %ip %Lpc0 %hcfg Hlat Hreg Hnorg Hti Hip
  unfold wmstateNorg
  icases Hnorg with ⟨%hbnd, %hnv, %hwf, Hdev, Hlogauth, Hwsauth⟩
  ihave ⟨%hws, Hwsauth, Hhws⟩ := persistent_entails_right (hartWsAgree cpu σ.wmWs ws) $$ [Hwsauth Hhws]
  · iframe Hwsauth Hhws
  subst hws
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, Lmprv, Lpmm, Lelp⟩ := hcfg
  have LmisaC : (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true := by rw [Lmisa]; decide
  -- the THREE registers the funnel does not read: pmpaddr_n, base, data
  icases keepPure (WeakLeafTor.mConfPmpaddr cpu _ c _) $$ Hreg Hm2 with ⟨%Lpaddra, Hreg, Hm2⟩
  have Lpaddr : σ.wmRegs .pmpaddr_n = c.pmpaddr :=
    (regAtFlat .pmpaddr_n σ b (by decide)).symm.trans Lpaddra
  icases keepPure (WeakLeafLw4.gprValid cpu _ rs1 _ rs1v hrs1nz) $$ Hreg Hrs1c with ⟨%Lrs1a, Hreg, Hrs1c⟩
  icases keepPure (WeakLeafLw4.gprValid cpu _ rs2 _ rs2v hrs2nz) $$ Hreg Hrs2c with ⟨%Lrs2a, Hreg, Hrs2c⟩
  have Lrs1 : (wflatSt σ).gpr rs1 = rs1v := by
    rw [← WeakLeafLw4.gprSetNe (wflatSt σ) .minstret_increment b rs1 (by decide)]
    exact Lrs1a
  have Lrs2 : (wflatSt σ).gpr rs2 = rs2v := by
    rw [← WeakLeafLw4.gprSetNe (wflatSt σ) .minstret_increment b rs2 (by decide)]
    exact Lrs2a
  have hea_σ : (wflatSt σ).gpr rs1 + sign_extend (m := 64) imm = ea := by rw [Lrs1]; exact hea
  have hag_σ : ∀ r, D r = true → σ.wmRegs r = dst.regs r := hagree _ Lpriv Lmisa Lsec
  have lpmp_σ : pmpAllowsAll (σ.wmRegs .pmpcfg_n) := by rw [Lpmpc]; exact hpmp
  have htor_σ : pmpTor0Grants (σ.wmRegs .pmpcfg_n) (σ.wmRegs .pmpaddr_n) ea 8 := by
    rw [Lpmpc, Lpaddr]; exact htor
  -- ---- the certificate's precondition (§2) ----
  icases WeakLeafLw4.keepPure2 (wPEffSd8Tor al4 cpu.val σ pc h rs1 rs2 imm i0 ea vold rs2v cpu D D0 dst
      hwf Lpc0 Lpriv lpmp_σ htor_σ Lpma Lhtif Lhart LmisaS LmisaC LmIE Lmprv Lpmm Lelp hal2 hal4 hea_σ
      Lrs2 hram hag_σ hDmi hgood hdec hgood0 hexp) $$ Hlat Hbs Hpt with ⟨%HP, Hlat, -, Hpt⟩
  icases keepPure1 (wpt8OwnAlign cpu ea vold σ.wmWs) $$ Hpt with ⟨%halea, Hpt⟩
  -- ---- the run, at the FLAT state ----
  have hexf := execEffSd8TorAt (wflatSt σ) b (BitVec.addInt pc 2) rs1 rs2 imm ea rs2v Lpriv Lmprv Lpmm
    htor_σ Lpma Lhtif hea_σ Lrs2 halea hram
  obtain ⟨sE, hsE⟩ : ∃ sE : ExecSt, sE =
      ⟨(((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).regs,
        bmWrite (wflatSt σ).mem ea 8 rs2v, (wflatSt σ).dev⟩ := ⟨_, rfl⟩
  rw [← hsE] at hexf
  have hsEregs : sE.regs = (((wflatSt σ).setReg .minstret_increment b).regs).set .nextPC
      (BitVec.addInt pc 2) := by rw [hsE]; rfl
  have hsEdev : sE.dev = σ.wmDev := by rw [hsE]; rfl
  have hsEnpc : sE.regs .nextPC = BitVec.addInt pc 2 := by
    rw [hsE]; exact (storeRegsFacts (wflatSt σ) b (BitVec.addInt pc 2)).2.2
  -- ---- the ONE register write the wrapper expects: nextPC ----
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 2))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [← hsEregs]
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists sE
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ hexf
  isplitl [Hreg]
  · iexact Hreg
  isplitl [Hti Hip]
  · iexists mt, ip
    iframe Hti Hip
  inext
  iintro %tick %σ' %t %hstep %hdevt %hpost %hQ Hm' Hclk' Hpc'
  obtain ⟨-, hdevs, -, -, -, hwsle, hwf', hbnd'⟩ := hpost
  obtain ⟨⟨hQi, ⟨kc, hQl, -⟩, -, hQv⟩, hQeff⟩ := hQ
  -- the release deposit: freeze R at the store's own timestamp
  ihave HRdep := wwpReleaseDeposit R σ hbnd $$ HR
  -- THE WINDOW UPDATE: retarget the eight elements at the message `wQStore8` names
  icases wpt8OwnAtElems cpu ea vold σ.wmWs $$ Hpt with
    ⟨%halea2, %haccea, %t0, %t1, %t2, %t3, %t4, %t5, %t6, %t7,
      H0, S0, H1, S1, H2, S2, H3, S3, H4, S4, H5, S5, H6, S6, H7, S7⟩
  imod wlat8StorePrimOwn cpu kc σ ea rs2v t0 t1 t2 t3 t4 t5 t6 t7 _ _ _ _ _ _ _ _
      $$ Hlat H0 S0 H1 S1 H2 S2 H3 S3 H4 S4 H5 S5 H6 S6 H7 S7 with ⟨Hlat, Hl8⟩
  icases keepPure (winstrNv cpu _ _ pc _) $$ Hlat Hbs with ⟨%hnvpc, Hlat, -⟩
  icases keepPure (nvOkWlat8Own cpu _ _ ea _ rs2v) $$ Hlat Hl8 with ⟨%hnvea, Hlat, Hl8⟩
  imod wlogUpdate σ.wmLog [wwriteMsg (some cpu.val) kc ea 8 rs2v] $$ Hlogauth with Hlogauth
  imod hartWsUpdate cpu σ.wmWs σ.wmWs σ'.wmWs $$ [$Hwsauth $Hhws] with ⟨Hwsauth, Hhws⟩
  imod Hclose
  -- the PC the funnel hands back IS pc+2
  rw [hsEnpc]
  ihave Hpt' := wlat8OwnWpt8Own cpu ea (σ.wmLog.length + 1) rs2v σ'.wmWs halea2 haccea
    (fun j hj => hQv j hj) $$ Hl8
  imodintro
  isplitl [Hlat]
  · rw [hQi, hQl]; iexact Hlat
  isplitl [Hdev Hlogauth Hwsauth]
  · isplitr
    · ipureintro; exact hbnd'
    isplitr
    · ipureintro
      apply nvHartOfWQEffOk cpu σ σ' _ hQeff hnv
      intro a ha
      rw [hQl]
      rcases weffsTouchApp _ _ a ha with ha | ha
      · obtain ⟨j, hj, rfl⟩ := weffsTouchRead1 _ pc _ a ha
        exact hnvpc j (WeakLeafTor.ltFetchW al4 j hj)
      · obtain ⟨j, hj, rfl⟩ := weffsTouchWrite1 _ ea _ _ a ha
        exact hnvea j hj
    isplitr
    · ipureintro; exact hwf'
    rw [hdevs, hdevt, hsEdev, hQl]
    iframe Hdev Hlogauth Hwsauth
  ihave Hm := WeakLeafTor.mConfJoinHalves cpu q c $$ Hm' Hm2
  iapply Hcont $$ %σ'.wmWs %(σ.wmLog.length + 1) %hwsle %(fun j hj => hQv j hj) Hm Hclk'
    [Hpc' Hnpc] Hrs1c Hrs2c Hhws Hpt' HRdep
  unfold pcIs
  iframe Hpc' Hnpc

end leaves

end Weak
