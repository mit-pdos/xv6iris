/-
Weak: **the weak-memory M-mode instruction funnel** (M4-prep): the fetch lemma
made pure, the weak instruction resource `winstr`, and the funnel `wwpInstr`
(a weak leaf owes ONE `execute` fact, as an SC leaf does).

Rocq: `iris/WeakFunnel.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance.  Every SC leaf goes through `InstrBytes.wp_instr`
and owes ONE `execute` fact; the weak leaf-facing rule `WeakInstr.wpWinstr`
owes the WHOLE `exec (riscvStep tick) (wflatSt σ)`.  This file bridges the
two.  §1 `execFetchFlat`: the fetch with all the Iris removed -- the config
registers and the bytes become PURE hypotheses (`fetchFlatOk`); weak addresses
are physical (`fetchPa_eq`); all three alignment arms are kept.  §2 `winstr`:
the weak twin of `InstrBytes.instr` -- bytes in `wkernelText`'s spelling
(objective, persistent), the decode field a pure `exec` statement at an
arbitrary state.  §3 `wwp_instr`: the funnel, doing the entire `riscv_step`
wrapper (minstret flag, fetch, dispatch, decode, `run_hart_active`, PC tick,
minstret bump, `tick_clock`) so the leaf owes one `execute` fact; the leaf
borrows `wmstateNorg` (`wmstateRest` minus the registers).  §4: the funnel
composing with `wstepCertConfNone`.

**Deviations from Rocq.**
1. NAMES / VOCABULARY: the tree's camelCase (map below); no name is in the
   duplicated-name table.  As `Weak/WeakInstr.lean` deviation 1 /
   `Weak/ExecSC5.lean` conventions: `mstate` ↦ `ExecSt`, `register_lookup r
   s.(sregs)` ↦ `s.regs r`, `set_reg` ↦ `ExecSt.setReg`, `eq_vec x 'b"1" = b` ↦
   `(x == 1#1) = b`, `subrange_vec_dec w 15 0` ↦ `Sail.BitVec.extractLsb w 15 0`,
   `pa_add a j` ↦ `a + BitVec.ofNat 64 j`, `nth_byte w j` ↦ `nthByte (n := 4) w j`,
   `pa_z` ↦ `paZ`, `acc_addr` ↦ `WeakInterp.accAddr`, `fetch_is_rvc` ↦
   `MachCSL.fetchIsRvc`, `MISA_C` ↦ `misaC`, `MENVCFG_S` ↦ `menvcfgS`,
   `cpu_id` ↦ the explicit `cpu`; the per-byte memory window is `BytesAt`.
2. RAM AND PMA: Rocq's per-byte `addr_is_ram (pa_add pc j)` (j < 4) is the
   window form `inRam pc 4` (equivalent: RAM ends below 2^64); Rocq's abstract
   `pma_allows_all` is the concrete `pma_regions = bootPMA` (what
   `MachCSL.hwConfig` pins); the CLINT/SIG/HTIF/device side conditions are
   discharged by the Lean-only `execWithinClintRam`/`execWithinSigFalse`/
   `execWithinHtifNone`/`devAddrRam` (Rocq `RiscvExtras`).
3. STATEMENT SHAPES (WeakInstr deviation 3): Rocq `A -∗ B -∗ ⌜φ⌝` is
   `A ⊢ B -∗ ⌜φ⌝`; pure Rocq premises before the wands are Lean premises;
   `winstr_intro`'s `winstr_bytes pc r -∗ winstr …` is an entailment.
4. `winstr_bytes`' `[∗ list] j ∈ seq 0 4` is spelled as four explicit
   conjuncts at `paZ (pc + BitVec.ofNat 64 j)`; the word/result `match` is the
   Lean-only `fetchWordOk`, the decode field the Lean-only `winstrDec`.
5. `wcfg_regs`: `pma_allows_all` ↦ `= bootPMA` (deviation 2); `elp` as
   `(elp == landing_pad_bits_backwards .LP_EXPECTED) = false`.
   `set_mi_lookup`'s `register_beq r … = false` is `r ≠ .minstret_increment`.
6. O2 (owner decision; `Weak/WeakCert.lean` deviation 4): the Lean-only
   `winstrTextPinned` gives `wpWinstr`'s text obligation (`pinnedRead ∧
   fetchPinned`); `winstrPinned` keeps Rocq's statement.  For §4, the
   Lean-only `wPConfText pc` is Rocq's `wP_conf` with `WeakCert.wPConf`'s
   `fetchPin` replaced by the leaf's own trace facts (`fetchInWindow pc`,
   `fetchFresh`), and `wstepCertConfText` supplies the fetch pin from the
   certificate's text pin (as `WeakAcquire.wstepCertText`).
7. THE CONFIG INTERFACE (owner decision Q3, option A) -- the one every leaf
   that took Rocq's `mmode_config` follows.  Rocq `mmode_config dq` ↦
   `mConf cpu dq c ∗ clockCells cpu`; Rocq's separate `pmpcfg_n ↦ᵣ{dq}
   pmpcfg0` ↦ `mConf`'s own cell (`pmpcfg0 := c.pmpcfg`, so `wcfgRegs σ
   c.pmpcfg` and the premise `pmpAllowsAll c.pmpcfg`); Rocq's mstatus facts
   (MIE/MPRV clear) ↦ the premise `MConf.mok c` (SXL and
   `mstatus_kernel_facts` are not needed by the funnel and are dropped; a leaf
   knows `c.mstatus`).  `MinstretInv` is NOT ported: Rocq's `minstret_inv`/
   `clock_inv` bodies are the five owned `clockCells` (no invariant, so every
   mask `⊤ ∖ ↑minstretN` is `⊤`; `wwpCb` is `={⊤,∅}=∗` and its continuation
   `|={∅,⊤}=>`).  The funnel holds `clockCells` across the step, writes
   `minstret_increment := b` before the callback, `PC`/`minstret` after it and
   `mcycle`/`mtime`/`mip` on the tick branch.  `wwpCb` vs Rocq `wwp_cb`:
   (a) it is also `∀ mt ip` and takes `mtime ↦ᵣ mt ∗ mip ↦ᵣ ip`, returning
   `∃ mt' ip'` of them next to `regInterp cpu sExec.regs` (Rocq: a leaf could
   open `clock_inv` inside its fupd; Lean's `execSpecClk` shape) -- a leaf
   that does not touch the clock just passes them back; (b) its continuation
   receives `mConf cpu dq c`, `clockCells cpu` and `PC ↦ᵣ nextPC` (Rocq:
   `mmode_config dq`, `pmpcfg_n ↦ᵣ{dq}`, `PC ↦ᵣ`); (c) the post-write
   registers are `((wflatSt σ).setReg .minstret_increment b).regs`.
   `wwpInstr` is `mConf cpu dq c ⊢ clockCells cpu -∗ PC ↦ᵣ pc -∗ winstr … -∗
   wwpCb … -∗ WWP` (Rocq's `mmode_config dq -∗ pmpcfg_n ↦ᵣ{dq} pmpcfg0 -∗ PC ↦ᵣ
   pc -∗ winstr … -∗ wwp_cb … -∗ WWP Loop`); `wwpInstrConf` is at
   `wPConfText pc` (deviation 6).
8. Lean-only (28): the Rocq SC vocabulary `pmpAllowsAll`, `privMSU`, `cfgOk`,
   `decodeFetch`; `fetchWordOk`, `winstrDec`; the RAM-fetch helpers
   `execWithinClintRam`, `execWithinSigFalse`, `execWithinHtifNone`,
   `devAddrRam`, `ramRegionExec`, `nthByteLo`, `nthByteHi`, `addIntTwo`,
   `toNatAddOfRam`, `fetchM4Of`, `fetchM2Of`; `winstrTextPinned`;
   `hartActiveSFinalDev`, `execDispatchFunnel`, `wwpStepExec` (the exec chain
   of `wwp_instr`'s proof, as one lemma); `wPConfText`, `wstepCertConfText`;
   the interface helpers `mConfFacts`, `wcfgRegsOf`, `mConfRegFacts`,
   `wwpRetireRegs`, `wwpTickRegs`.  (26 Rocq + 28 Lean-only = 54.)

**Rocq → Lean name map.**  `fetch_flat_ok` `fetchFlatOk`, `fetch_flat_ok_mem`
`fetchFlatOkMem`, `exec_fetch_flat` `execFetchFlat`, `winstr_bytes`
`winstrBytes`, `winstr_bytes_persistent` `winstrBytes_persistent`, `winstr`
`winstr`, `winstr_persistent` `winstr_persistent`, `winstr_bytes_of_text`
`winstrBytesOfText`, `winstr_intro` `winstrIntro`, `winstr_bytes_acc_wf`
`winstrBytesAccWf`, `winstr_bytes_lookup` `winstrBytesLookup`, `winstr_flat`
`winstrFlat`, `winstr_pinned` `winstrPinned`, `winstr_nv` `winstrNv`,
`winstr_unwritten` `winstrUnwritten`, `wcfg_regs` `wcfgRegs`,
`wcfg_regs_cfg_ok` `wcfgRegsCfgOk`, `wmstate_norg` `wmstateNorg`,
`wmstate_rest_split` `wmstateRestSplit`, `wmstate_interp_split_regs`
`wmstateInterpSplitRegs`, `wmstate_norg_facts` `wmstateNorgFacts`,
`wmstate_norg_nv` `wmstateNorgNv`, `set_mi_lookup` `setMiLookup`, `wwp_cb`
`wwpCb`, `wwp_instr` `wwpInstr`, `wwp_instr_conf` `wwpInstrConf`.

**Dropped:** nothing -- every Rocq definition and lemma has a Lean twin.

**Statements checked** (by hand, against Rocq): all; the changed ones are
listed under the deviations.
-/
import Weak.WeakAcquire
import Weak.ExecSC7
import MachCSL.Instr
import MachCSL.PlatformFacts
import MachCSL.WpCycleDefs

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 0. Rocq SC vocabulary the funnel states itself over (Lean-only)

`RiscvFetchExec.pmp_allows_all`, `priv_mSU`, `cfg_ok` and
`InstrBytes.decode_fetch` have no Lean twin (the SC tier is stated over `swp`,
not `exec`); they are restated here, literally. -/

/-- Rocq `RiscvFetchExec.pmp_allows_all`: no PMP entry is locked. -/
def pmpAllowsAll (cfg : RegisterType .pmpcfg_n) : Prop := ∀ i : Nat, pmpLocked cfg[i]! = false

/-- Rocq `RiscvFetchExec.priv_mSU`. -/
def privMSU : Privilege → Bool
  | .Machine | .Supervisor | .User => true
  | .VirtualSupervisor | .VirtualUser => false

/-- Rocq `RiscvFetchExec.cfg_ok`: the config precondition of the decode bridge. -/
def cfgOk (s : ExecSt) : Prop :=
  (s.regs .cur_privilege = .Machine ∧ s.regs .mseccfg = 0#64) ∨
  (s.regs .cur_privilege = .Supervisor ∧ s.regs .menvcfg = menvcfgS)

/-- Rocq `InstrBytes.decode_fetch`. -/
noncomputable def decodeFetch : FetchResult → SailM instruction
  | .F_Base w => ext_decode w
  | .F_RVC h => ext_decode_compressed h
  | _ => ext_decode 0#32

/-! ## 1. THE FETCH LEMMA, MADE PURE

`fetchFlatOk t pc r` is everything `exec (fetch ()) t = some (r, t)` needs
BEYOND the fetch configuration registers: the geometry, the RAM class of the
four bytes at `pc`, and what the memory holds there.  The footprint is ALWAYS
the four bytes of one 32-bit word `w` at `pc`, with `r` saying how `w` is read
(`F_Base w` itself, or `F_RVC` of its low half). -/

/-- How the fetch result `r` reads the word `w` (Rocq: the `match` inlined in
`fetch_flat_ok` and `winstr_bytes`; Lean-only name). -/
def fetchWordOk (r : FetchResult) (w : BitVec 32) : Prop :=
  match r with
  | .F_Base w' => w' = w ∧ isRVC (Sail.BitVec.extractLsb w 15 0) = false
  | .F_RVC h => Sail.BitVec.extractLsb w 15 0 = h ∧ isRVC h = true
  | _ => False

def fetchFlatOk (t : ExecSt) (pc : BitVec 64) (r : FetchResult) : Prop :=
  is_aligned_vaddr (.Virtaddr pc) 2 = true ∧
  inRam pc 4 ∧
  ∃ w : BitVec 32, fetchWordOk r w ∧ BytesAt t pc 4 w

/-- Only the MEMORY of `t` is looked at. -/
theorem fetchFlatOkMem (t t' : ExecSt) (pc : BitVec 64) (r : FetchResult) :
    t'.mem = t.mem → fetchFlatOk t pc r → fetchFlatOk t' pc r := by
  rintro hm ⟨h2, hram, w, hr, hb⟩
  refine ⟨h2, hram, w, hr, fun j hj => ?_⟩
  rw [hm]
  exact hb j hj

/-! ### The platform side conditions of a RAM fetch (Lean-only helpers; Rocq
`RiscvExtras.within_*_false`, `addr_is_ram_not_dev`) -/

theorem execWithinClintRam (pa : BitVec 64) (n : Nat) (s : ExecSt) (h : inRam pa n) :
    exec (within_clint (.Physaddr pa) n) s = some (false, s) := by
  rw [within_clint_ram pa n h]; rfl

theorem execWithinSigFalse (pa : BitVec 64) (n : Nat) (s : ExecSt) :
    exec (within_sig (.Physaddr pa) n) s = some (false, s) := by
  first
  | rfl
  | (simp only [within_sig, plat_have_sig, Functions.not]; rfl)

theorem execWithinHtifNone (pa : BitVec 64) (n : Nat) (s : ExecSt)
    (h : s.regs .htif_tohost_base = none) :
    exec (within_htif_readable (.Physaddr pa) n) s = some (false, s) := by
  unfold within_htif_readable within_htif_writable
  exec_run [h]

theorem devAddrRam (pa : BitVec 64) (n : Nat) (h : inRam pa n) : devAddr pa = false := by
  unfold inRam ramBase at h
  simp only [devAddr, devBound, decide_eq_false_iff_not]
  omega

theorem ramRegionExec : (override_PMA ramRegion.attributes .PBMT_PMA).executable = true := by
  first
  | rfl
  | decide +kernel

/-- The low half of a word, byte by byte. -/
theorem nthByteLo (w : BitVec 32) (j : Nat) (hj : j < 2) :
    nthByte (n := 2) (Sail.BitVec.extractLsb w 15 0) j = nthByte (n := 4) w j := by
  rcases j with _ | _ | j
  · exact nthByte_lo0 w
  · exact nthByte_lo1 w
  · omega

/-- The high half of a word, byte by byte. -/
theorem nthByteHi (w : BitVec 32) (j : Nat) (hj : j < 2) :
    nthByte (n := 2) (Sail.BitVec.extractLsb w 31 16) j = nthByte (n := 4) w (2 + j) := by
  rcases j with _ | _ | j
  · exact nthByte_hi0 w
  · exact nthByte_hi1 w
  · omega

theorem addIntTwo (pc : BitVec 64) : Sail.BitVec.addInt pc 2 = pc + BitVec.ofNat 64 2 := rfl

/-- `inRam pc 4` keeps the window off the top of the address space. -/
theorem toNatAddOfRam (pc : BitVec 64) (j : Nat) (h : inRam pc 4) (hj : j < 4) :
    (pc + BitVec.ofNat 64 j).toNat = pc.toNat + j := by
  unfold inRam ramEnd at h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : j % 2 ^ 64 = j := Nat.mod_eq_of_lt (by omega)
  rw [this]
  exact Nat.mod_eq_of_lt (by omega)

/-- The four-byte M-mode section premises, at a RAM word. -/
theorem fetchM4Of (pc : BitVec 64) (w : BitVec 32) (t : ExecSt) (hpc : t.regs .PC = pc)
    (hpriv : t.regs .cur_privilege = .Machine) (hpmp : pmpAllowsAll (t.regs .pmpcfg_n))
    (hpma : t.regs .pma_regions = bootPMA) (hhtif : t.regs .htif_tohost_base = none)
    (hram : inRam pc 4) (hb : BytesAt t pc 4 w) (hal : is_aligned_vaddr (.Virtaddr pc) 4 = true) :
    FetchM4 pc ramRegion w t where
  hpc := hpc
  hpriv := hpriv
  hpmp := hpmp
  hmatch := by rw [hpma, fetchPa_eq]; exact matching_pma_ram pc 4 hram (by decide) (by decide)
  hx := ramRegionExec
  hc := by rw [fetchPa_eq]; exact execWithinClintRam pc 4 t hram
  hsig := execWithinSigFalse _ _ _
  hh := execWithinHtifNone _ _ _ hhtif
  hdev := by rw [fetchPa_eq]; exact devAddrRam pc 4 hram
  hb := by rw [fetchPa_eq]; exact hb
  hvalign := hal

/-- The two-byte M-mode section premises, at a 2-aligned RAM halfword. -/
theorem fetchM2Of (pc : BitVec 64) (h : BitVec 16) (t : ExecSt)
    (hpriv : t.regs .cur_privilege = .Machine) (hpmp : pmpAllowsAll (t.regs .pmpcfg_n))
    (hpma : t.regs .pma_regions = bootPMA) (hhtif : t.regs .htif_tohost_base = none)
    (hram : inRam pc 2) (hb : BytesAt t pc 2 h) (hal : pc.toNat % 2 = 0) :
    FetchM2 pc ramRegion h t where
  hpriv := hpriv
  hpmp := hpmp
  hmatch := by rw [hpma, fetchPa_eq]; exact matching_pma_ram pc 2 hram (by decide) (by decide)
  hal := by rw [fetchPa_eq]; exact is_aligned_paddr_of pc 2 (by decide) hal
  hx := ramRegionExec
  hc := by rw [fetchPa_eq]; exact execWithinClintRam pc 2 t hram
  hsig := execWithinSigFalse _ _ _
  hh := execWithinHtifNone _ _ _ hhtif
  hdev := by rw [fetchPa_eq]; exact devAddrRam pc 2 hram
  hb := by rw [fetchPa_eq]; exact hb

theorem execFetchFlat (t : ExecSt) (pc : BitVec 64) (r : FetchResult) :
    pmpAllowsAll (t.regs .pmpcfg_n) →
    t.regs .pma_regions = bootPMA →
    (_get_Misa_C (t.regs .misa) == 1#1) = true →
    t.regs .PC = pc →
    t.regs .cur_privilege = .Machine →
    t.regs .htif_tohost_base = none →
    fetchFlatOk t pc r →
    exec (fetch ()) t = some (r, t) := by
  rintro hpmp hpma hmisaC hpc hpriv hhtif ⟨h2, hram, w, hr, hb⟩
  have hm2 : pc.toNat % 2 = 0 := isAlignedVaddrMod pc 2 (by decide) h2
  -- the 2-aligned-not-4 arm's facts
  have h24 : is_aligned_vaddr (.Virtaddr pc) 4 = false → pc.toNat % 4 = 2 := by
    intro h4
    by_cases hm : pc.toNat % 4 = 0
    · rw [is_aligned_vaddr_of pc 4 hm] at h4; exact absurd h4 (by decide)
    · omega
  have hramLo : inRam pc 2 := by unfold inRam at hram ⊢; omega
  have hbLo : BytesAt t pc 2 (Sail.BitVec.extractLsb w 15 0) := by
    intro j hj
    rw [nthByteLo w j hj]
    exact hb j (by omega)
  have hramHi : inRam (Sail.BitVec.addInt pc 2) 2 := by
    rw [addIntTwo]
    have := toNatAddOfRam pc 2 hram (by omega)
    unfold inRam at hram ⊢
    omega
  have hbHi : BytesAt t (Sail.BitVec.addInt pc 2) 2 (Sail.BitVec.extractLsb w 31 16) := by
    intro j hj
    have e : (BitVec.ofNat 64 2 + BitVec.ofNat 64 j) = BitVec.ofNat 64 (2 + j) := by
      rcases j with _ | _ | j
      · rfl
      · rfl
      · omega
    rw [nthByteHi w j hj, addIntTwo, BitVec.add_assoc, e]
    exact hb (2 + j) (by omega)
  have hmHi : (Sail.BitVec.addInt pc 2).toNat % 2 = 0 := by
    rw [addIntTwo, toNatAddOfRam pc 2 hram (by omega)]
    omega
  cases r with
  | F_Error e => exact hr.elim
  | F_Ext_Error e => exact hr.elim
  | F_Base w' =>
    obtain ⟨rfl, hnot⟩ := hr
    cases hal : is_aligned_vaddr (.Virtaddr pc) 4
    · -- 2-aligned, not 4-aligned: two 2-byte reads at pc and pc+2
      have hm4 := h24 hal
      exact execFetchFBase2 pc ramRegion ramRegion w' t
        (fetchM2Of pc _ t hpriv hpmp hpma hhtif hramLo hbLo hm2)
        (fetchM2Of _ _ t hpriv hpmp hpma hhtif hramHi hbHi hmHi)
        hpc (bit0_clear_of_even pc hm2) (bit1_set_of_mod4 pc hm4) hal hmisaC hnot
    · -- 4-aligned: one 4-byte read
      exact execFetchDone pc ramRegion w' t (fetchM4Of pc w' t hpc hpriv hpmp hpma hhtif hram hb hal) hnot
  | F_RVC h =>
    obtain ⟨rfl, hrvc⟩ := hr
    cases hal : is_aligned_vaddr (.Virtaddr pc) 4
    · have hm4 := h24 hal
      exact execFetchRVC2 pc ramRegion _ t (fetchM2Of pc _ t hpriv hpmp hpma hhtif hramLo hbLo hm2) hpc
        (bit0_clear_of_even pc hm2) (bit1_set_of_mod4 pc hm4) hal hmisaC hrvc
    · exact execFetchRVC4 pc ramRegion w t (fetchM4Of pc w t hpc hpriv hpmp hpma hhtif hram hb hal) hrvc

/-! ## 2. THE WEAK INSTRUCTION RESOURCE

`MachCSL.instr` cannot be reused: its bytes are `imgBytes` (the SC heap) and
its decode field is an `swp`.  `winstr` is the twin: the bytes are
`WeakInstr.wkernelText`'s spelling (`wlatPointsto (paZ a) DFrac.discard 0 b`,
OBJECTIVE and PERSISTENT) and the decode field is a pure statement about
`exec` at an arbitrary state. -/

/-- The decode field of `winstr` (Rocq: inlined in `winstr` and `winstr_intro`;
Lean-only name). -/
def winstrDec (r : FetchResult) (i : instruction) : Prop :=
  ∀ t : ExecSt,
    privMSU (t.regs .cur_privilege) = true →
    (_get_Misa_C (t.regs .misa) == 1#1) = true →
    (_get_Misa_A (t.regs .misa) == 1#1) = true →
    t.regs .misa = misaC →
    cfgOk t →
    if fetchIsRvc r then
      ∃ i0 : instruction,
        exec (decodeFetch r) t = some (i0, t) ∧
        is_lpad_instruction i0 = false ∧
        (∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs i, s))
    else exec (decodeFetch r) t = some (i, t)

section winstr
variable {GF : BundledGFunctors} [WeakGS GF]

def winstrBytes (pc : BitVec 64) (r : FetchResult) : IProp GF :=
  iprop(⌜is_aligned_vaddr (.Virtaddr pc) 2 = true⌝ ∗
    ⌜accWf pc 4⌝ ∗
    ⌜inRam pc 4⌝ ∗
    ∃ w : BitVec 32, ⌜fetchWordOk r w⌝ ∗
      wlatPointsto (GF := GF) (paZ (pc + BitVec.ofNat 64 0)) DFrac.discard 0 (nthByte (n := 4) w 0) ∗
      wlatPointsto (GF := GF) (paZ (pc + BitVec.ofNat 64 1)) DFrac.discard 0 (nthByte (n := 4) w 1) ∗
      wlatPointsto (GF := GF) (paZ (pc + BitVec.ofNat 64 2)) DFrac.discard 0 (nthByte (n := 4) w 2) ∗
      wlatPointsto (GF := GF) (paZ (pc + BitVec.ofNat 64 3)) DFrac.discard 0 (nthByte (n := 4) w 3))

instance winstrBytes_persistent (pc : BitVec 64) (r : FetchResult) :
    Persistent (winstrBytes (GF := GF) pc r) := by
  unfold winstrBytes; infer_instance

def winstr (pc : BitVec 64) (is_rvc : Bool) (i : instruction) : IProp GF :=
  iprop(⌜is_lpad_instruction i = false⌝ ∗
    ∃ r : FetchResult, ⌜fetchIsRvc r = is_rvc⌝ ∗ winstrBytes (GF := GF) pc r ∗ ⌜winstrDec r i⌝)

instance winstr_persistent (pc : BitVec 64) (is_rvc : Bool) (i : instruction) :
    Persistent (winstr (GF := GF) pc is_rvc i) := by
  unfold winstr; infer_instance

/-! ### 2a. The constructors a decode file uses -/

/-- The bytes, off the objective kernel-text resource. -/
theorem winstrBytesOfText (bs : GMapF PAddr (BitVec 8)) (pc : BitVec 64) (r : FetchResult)
    (w : BitVec 32) :
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    accWf pc 4 →
    inRam pc 4 →
    fetchWordOk r w →
    wkernelText (GF := GF) bs ⊢
      ⌜∀ j : Nat, j < 4 → get? bs (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)⌝ -∗
        winstrBytes (GF := GF) pc r := by
  intro h2 hacc hram hr
  unfold wkernelText winstrBytes
  iintro #Ht %hlk
  ihave #H0 := BigSepM.bigSepM_lookup
    (Φ := fun a b => wlatPointsto (GF := GF) (paZ a) DFrac.discard 0 b) (hlk 0 (by omega)) $$ Ht
  ihave #H1 := BigSepM.bigSepM_lookup
    (Φ := fun a b => wlatPointsto (GF := GF) (paZ a) DFrac.discard 0 b) (hlk 1 (by omega)) $$ Ht
  ihave #H2 := BigSepM.bigSepM_lookup
    (Φ := fun a b => wlatPointsto (GF := GF) (paZ a) DFrac.discard 0 b) (hlk 2 (by omega)) $$ Ht
  ihave #H3 := BigSepM.bigSepM_lookup
    (Φ := fun a b => wlatPointsto (GF := GF) (paZ a) DFrac.discard 0 b) (hlk 3 (by omega)) $$ Ht
  isplitr
  · ipureintro; exact h2
  isplitr
  · ipureintro; exact hacc
  isplitr
  · ipureintro; exact hram
  iexists w
  isplitr
  · ipureintro; exact hr
  iframe H0 H1 H2 H3

/-- ... and the whole resource, from the bytes plus the PURE decode fact. -/
theorem winstrIntro (pc : BitVec 64) (is_rvc : Bool) (i : instruction) (r : FetchResult) :
    is_lpad_instruction i = false →
    fetchIsRvc r = is_rvc →
    winstrDec r i →
    winstrBytes (GF := GF) pc r ⊢ winstr (GF := GF) pc is_rvc i := by
  intro hlpad hrvc hdec
  unfold winstr
  iintro #Hb
  isplitr
  · ipureintro; exact hlpad
  iexists r
  isplitr
  · ipureintro; exact hrvc
  isplitr
  · iexact Hb
  ipureintro; exact hdec

/-! ### 2b. The eliminators the funnel uses -/

theorem winstrBytesAccWf (pc : BitVec 64) (r : FetchResult) :
    winstrBytes (GF := GF) pc r ⊢ ⌜accWf pc 4⌝ := by
  unfold winstrBytes
  iintro ⟨-, %h, -⟩
  ipureintro; exact h

/-- The per-byte element determines the flat byte AND its timestamp. -/
theorem winstrBytesLookup (σ : Wmstate) (pc : BitVec 64) (r : FetchResult) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      winstrBytes (GF := GF) pc r -∗
        ⌜(∀ j : Nat, j < 4 → latestTs σ.wmLog (paZ (pc + BitVec.ofNat 64 j)) = 0) ∧
          fetchFlatOk (wflatSt σ) pc r⌝ := by
  intro hwf
  unfold winstrBytes
  iintro Hi ⟨%h2, %hacc, %hram, %w, %hr, H0, H1, H2, H3⟩
  icases keepPure (wptImgFlatLookup σ _ DFrac.discard _ hwf) $$ Hi H0 with ⟨%E0, Hi, -⟩
  icases keepPure (wptImgFlatLookup σ _ DFrac.discard _ hwf) $$ Hi H1 with ⟨%E1, Hi, -⟩
  icases keepPure (wptImgFlatLookup σ _ DFrac.discard _ hwf) $$ Hi H2 with ⟨%E2, Hi, -⟩
  ihave %E3 := wptImgFlatLookup σ _ DFrac.discard _ hwf $$ Hi H3
  ipureintro
  refine ⟨fun j hj => ?_, h2, hram, w, hr, fun j hj => ?_⟩
  · rcases j with _ | _ | _ | _ | j
    · exact E0.2
    · exact E1.2
    · exact E2.2
    · exact E3.2
    · omega
  · rcases j with _ | _ | _ | _ | j
    · exact E0.1
    · exact E1.1
    · exact E2.1
    · exact E3.1
    · omega

/-- The FLAT half: `fetchFlatOk` at the flat projection. -/
theorem winstrFlat (σ : Wmstate) (pc : BitVec 64) (r : FetchResult) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      winstrBytes (GF := GF) pc r -∗ ⌜fetchFlatOk (wflatSt σ) pc r⌝ := by
  intro hwf
  iintro Hi #Hb
  ihave %h := winstrBytesLookup σ pc r hwf $$ Hi Hb
  ipureintro; exact h.2

/-- THE UNWRITTEN HALF: no message writes a text byte. -/
theorem winstrUnwritten (σ : Wmstate) (pc : BitVec 64) (r : FetchResult) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      winstrBytes (GF := GF) pc r -∗
        ⌜∀ j : Nat, j < 4 → latestTs σ.wmLog (WeakInterp.accAddr pc j) = 0⌝ := by
  intro hwf
  iintro Hi #Hb
  ihave %hacc := winstrBytesAccWf pc r $$ Hb
  ihave %h := winstrBytesLookup σ pc r hwf $$ Hi Hb
  ipureintro
  intro j hj
  rw [← accWfByte pc 4 j hacc hj]
  exact h.1 j hj

/-- The PINNED half -- Rocq `winstr_pinned` (`pinnedRead` over the window). -/
theorem winstrPinned (σ : Wmstate) (pc : BitVec 64) (r : FetchResult) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      winstrBytes (GF := GF) pc r -∗
        ⌜∀ j : Nat, j < 4 → pinnedRead σ (WeakInterp.accAddr pc j)⌝ := by
  intro hwf
  iintro Hi #Hb
  ihave %h := winstrUnwritten σ pc r hwf $$ Hi Hb
  ipureintro
  exact fun j hj => pinnedReadUnwritten σ _ (h j hj)

/-- O2: both pins at once, the text obligation of `wpWinstr` (Lean-only). -/
theorem winstrTextPinned (σ : Wmstate) (pc : BitVec 64) (r : FetchResult) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      winstrBytes (GF := GF) pc r -∗
        ⌜∀ j : Nat, j < 4 →
          pinnedRead σ (WeakInterp.accAddr pc j) ∧ fetchPinned σ (WeakInterp.accAddr pc j)⌝ := by
  intro hwf
  iintro Hi #Hb
  ihave %h := winstrUnwritten σ pc r hwf $$ Hi Hb
  ipureintro
  exact fun j hj => ⟨pinnedReadUnwritten σ _ (h j hj), fetchPinnedUnwritten σ _ (h j hj)⟩

/-- THE φ FORM: `nvOk` at an ARBITRARY log (the text fragments are discarded,
hence clean, at any log). -/
theorem winstrNv (c : CPU) (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (pc : BitVec 64)
    (r : FetchResult) :
    wlatInterp (GF := GF) img log ⊢
      winstrBytes (GF := GF) pc r -∗ ⌜∀ j : Nat, j < 4 → nvOk log c (WeakInterp.accAddr pc j)⌝ := by
  iintro Hi #Hb
  ihave %hacc := winstrBytesAccWf pc r $$ Hb
  unfold winstrBytes
  icases Hb with ⟨-, -, -, %w, -, H0, H1, H2, H3⟩
  icases keepPure (wand_intro (nvOkOfPointsto img log c _ DFrac.discard 0 _)) $$ Hi H0 with ⟨%E0, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfPointsto img log c _ DFrac.discard 0 _)) $$ Hi H1 with ⟨%E1, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfPointsto img log c _ DFrac.discard 0 _)) $$ Hi H2 with ⟨%E2, Hi, -⟩
  ihave %E3 := wand_intro (nvOkOfPointsto img log c _ DFrac.discard 0 _) $$ Hi H3
  ipureintro
  intro j hj
  rw [← accWfByte pc 4 j hacc hj]
  rcases j with _ | _ | _ | _ | j
  · exact E0
  · exact E1
  · exact E2
  · exact E3
  · omega

end winstr

/-! ## 3. THE FUNNEL

`wcfgRegs σ pmpcfg0` is everything the funnel reads off the M-mode
configuration, restated at `σ`'s OWN register file. -/

def wcfgRegs (σ : Wmstate) (pmpcfg0 : RegisterType .pmpcfg_n) : Prop :=
  σ.wmRegs .cur_privilege = .Machine ∧
  σ.wmRegs .hart_state = .HART_ACTIVE () ∧
  σ.wmRegs .misa = misaC ∧
  σ.wmRegs .mseccfg = 0#64 ∧
  σ.wmRegs .pmpcfg_n = pmpcfg0 ∧
  σ.wmRegs .pma_regions = bootPMA ∧
  σ.wmRegs .htif_tohost_base = none ∧
  (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true ∧
  (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false ∧
  (_get_Mstatus_MPRV (σ.wmRegs .mstatus) == 1#1) = false ∧
  pmm_mode_backwards (_get_Seccfg_PMM (σ.wmRegs .mseccfg)) = .PMM_Disabled ∧
  (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false

/-- The decode bridge's config precondition, at the flat state. -/
theorem wcfgRegsCfgOk (σ : Wmstate) (pmpcfg0 : RegisterType .pmpcfg_n) :
    wcfgRegs σ pmpcfg0 → cfgOk (wflatSt σ) :=
  fun h => .inl ⟨h.1, h.2.2.2.1⟩

section norg
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- `wmstateRest` minus the registers. -/
def wmstateNorg (cpu : CPU) (σ : Wmstate) : IProp GF :=
  iprop(⌜wsBounded σ.wmWs σ.wmLog.length⌝ ∗
    ⌜nvHart σ.wmLog cpu σ.wmWs⌝ ∗
    ⌜wlogWf σ.wmLog⌝ ∗
    devInterpAt (MachGS.era (hlc := hlc) (GF := GF)) σ.wmDev ∗
    wlogAuth σ.wmLog ∗
    wwsAuth cpu σ.wmWs)

theorem wmstateRestSplit (cpu : CPU) (σ : Wmstate) :
    wmstateRest (hlc := hlc) (GF := GF) cpu σ ⊣⊢
      regInterp cpu σ.wmRegs ∗ wmstateNorg (hlc := hlc) (GF := GF) cpu σ := by
  unfold wmstateRest wmstateNorg
  constructor
  · iintro ⟨%hb, %hn, %hw, Hr, Hd, Hl, Hws⟩
    iframe Hr
    isplitr
    · ipureintro; exact hb
    isplitr
    · ipureintro; exact hn
    isplitr
    · ipureintro; exact hw
    iframe Hd Hl Hws
  · iintro ⟨Hr, %hb, %hn, %hw, Hd, Hl, Hws⟩
    isplitr
    · ipureintro; exact hb
    isplitr
    · ipureintro; exact hn
    isplitr
    · ipureintro; exact hw
    iframe Hr Hd Hl Hws

theorem wmstateInterpSplitRegs (cpu : CPU) (σ : Wmstate) :
    wmstateInterp (hlc := hlc) (GF := GF) cpu σ ⊣⊢
      regInterp cpu σ.wmRegs ∗ wlatInterp σ.wmImg σ.wmLog ∗ wmstateNorg (hlc := hlc) (GF := GF) cpu σ := by
  refine (wmstateInterpSplit cpu σ).trans ?_
  constructor
  · iintro ⟨Hlat, H⟩
    icases (wmstateRestSplit cpu σ).mp $$ H with ⟨Hr, Hn⟩
    iframe Hr Hlat Hn
  · iintro ⟨Hr, Hlat, Hn⟩
    iframe Hlat
    iapply (wmstateRestSplit cpu σ).mpr
    iframe Hr Hn

theorem wmstateNorgFacts (cpu : CPU) (σ : Wmstate) :
    wmstateNorg (hlc := hlc) (GF := GF) cpu σ ⊢
      ⌜wsBounded σ.wmWs σ.wmLog.length ∧ wlogWf σ.wmLog⌝ := by
  unfold wmstateNorg
  iintro ⟨%hb, -, %hw, -⟩
  ipureintro; exact ⟨hb, hw⟩

/-- The φ conjunct, read off the borrowed bundle. -/
theorem wmstateNorgNv (cpu : CPU) (σ : Wmstate) :
    wmstateNorg (hlc := hlc) (GF := GF) cpu σ ⊢ ⌜nvHart σ.wmLog cpu σ.wmWs⌝ := by
  unfold wmstateNorg
  iintro ⟨-, %hn, -⟩
  ipureintro; exact hn

end norg

/-- The one register-tower fact the whole wrapper needs: the
`minstret_increment` pre-write is invisible to every OTHER register. -/
theorem setMiLookup (r : Register) (s : ExecSt) (b : Bool) :
    r ≠ .minstret_increment → (s.setReg .minstret_increment b).regs r = s.regs r :=
  fun h => RegFile.set_other _ _ _ _ h

/-! ### 3a. The wrapper's exec chain, pure (Lean-only)

Everything `wwp_instr`'s proof derives at the `exec` level -- fetch, interrupt
dispatch, decode, `run_hart_active`, the `try_step` wrapper and the clock tick
-- from the config reads, the fetch footprint, the decode field and the leaf's
ONE `execute` fact.  (Rocq does these steps inline in `wwp_instr`.) -/

/-- The post-step state's devices are the execute stage's. -/
theorem hartActiveSFinalDev (s : ExecSt) (b : Bool) : (hartActiveSFinal s b).dev = s.dev := by
  unfold hartActiveSFinal hartActiveSTick
  cases b <;> rfl

theorem execDispatchFunnel (s : ExecSt) (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true)
    (hmie : (_get_Mstatus_MIE (s.regs .mstatus) == 1#1) = false) :
    exec (dispatchInterrupt .Machine) s = some (none, s) :=
  execDispatchInterruptNone _ s (execGetPendingSetMachineNone s _ (execCurrentlyEnabledS s) hS hmie)

theorem wwpStepExec (σ : Wmstate) (pc : BitVec 64) (is_rvc : Bool) (i : instruction)
    (pmpcfg0 : RegisterType .pmpcfg_n) (r : FetchResult) (b : Bool) (sExec : ExecSt) :
    wcfgRegs σ pmpcfg0 →
    pmpAllowsAll pmpcfg0 →
    σ.wmRegs .PC = pc →
    fetchFlatOk (wflatSt σ) pc r →
    fetchIsRvc r = is_rvc →
    is_lpad_instruction i = false →
    winstrDec r i →
    exec (should_inc_minstret (σ.wmRegs .cur_privilege)) (wflatSt σ) = some (b, wflatSt σ) →
    exec (execute i)
        (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
          (Sail.BitVec.addInt pc (if is_rvc then 2 else 4))) =
      some (RETIRE_SUCCESS, sExec) →
    sExec.regs .hart_state = .HART_ACTIVE () →
    sExec.regs .minstret_increment = b →
    exec (riscvStep false) (wflatSt σ) = some ((), hartActiveSFinal sExec b) ∧
    ∃ c ti p : BitVec 64,
      exec (riscvStep true) (wflatSt σ) =
        some ((), (((hartActiveSFinal sExec b).setReg .mcycle c).setReg .mtime ti).setReg .mip p) := by
  intro hcfg hpmp hpc hfok hrvc hnlpad hdec hsi hexec hhs hmi
  obtain ⟨Lpriv, Lhs, Lmisa, Lmseccfg, Lpmpc, Lpma, Lhtif, HmisaS, HmIE, -, -, Help⟩ := hcfg
  -- the state the run really starts from
  let sA := (wflatSt σ).setReg .minstret_increment b
  have Lpriv_a : sA.regs .cur_privilege = .Machine := by
    rw [setMiLookup _ _ _ (by decide)]; exact Lpriv
  have Lpc_a : sA.regs .PC = pc := by rw [setMiLookup _ _ _ (by decide)]; exact hpc
  have Lmisa_a : sA.regs .misa = misaC := by rw [setMiLookup _ _ _ (by decide)]; exact Lmisa
  have Lms_a : sA.regs .mstatus = σ.wmRegs .mstatus := setMiLookup _ _ _ (by decide)
  have Lelp_a : (sA.regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false := by
    rw [setMiLookup _ _ _ (by decide)]; exact Help
  have Lmsec_a : sA.regs .mseccfg = 0#64 := by rw [setMiLookup _ _ _ (by decide)]; exact Lmseccfg
  have Lhs_a : sA.regs .hart_state = .HART_ACTIVE () := by
    rw [setMiLookup _ _ _ (by decide)]; exact Lhs
  have HmisaC : (_get_Misa_C (sA.regs .misa) == 1#1) = true := by rw [Lmisa_a]; decide
  have HmisaA : (_get_Misa_A (sA.regs .misa) == 1#1) = true := by rw [Lmisa_a]; decide
  -- fetch, at the post-write state (only the MEMORY matters, and it moved not)
  have hfetch : exec (fetch ()) sA = some (r, sA) := by
    apply execFetchFlat sA pc r
    · rw [setMiLookup _ _ _ (by decide)]; show pmpAllowsAll (σ.wmRegs .pmpcfg_n); rw [Lpmpc]; exact hpmp
    · rw [setMiLookup _ _ _ (by decide)]; exact Lpma
    · exact HmisaC
    · exact Lpc_a
    · exact Lpriv_a
    · rw [setMiLookup _ _ _ (by decide)]; exact Lhtif
    · exact fetchFlatOkMem (wflatSt σ) sA pc r rfl hfok
  -- the interrupt dispatch is a no-op: misa.S set, mstatus.MIE clear
  have hdisp : exec (dispatchInterrupt .Machine) sA = some (none, sA) := by
    apply execDispatchFunnel
    · rw [Lmisa_a]; decide
    · rw [Lms_a]; exact HmIE
  -- the decode obligation, discharged from the PURE field of `winstr`
  have hdec' := hdec sA (by rw [Lpriv_a]; rfl) HmisaC HmisaA Lmisa_a (.inl ⟨Lpriv_a, Lmsec_a⟩)
  -- the `run_hart_active` progress fact, by width
  obtain ⟨_, _, wfw, hrm, _⟩ := hfok
  have hha : ∃ retval : BitVec 32, exec (run_hart_active 0) sA =
      some (.Step_Execute (.Retire_Success (), retval), sExec) := by
    cases r with
    | F_Error e => exact hrm.elim
    | F_Ext_Error e => exact hrm.elim
    | F_Base w =>
      simp only [fetchIsRvc] at hrvc hdec'
      subst hrvc
      exact ⟨_, execHartActiveProgressBaseGen .Machine sA sA sExec w i pc RETIRE_SUCCESS
        Lpriv_a hdisp hfetch hdec' Lelp_a hnlpad Lpc_a hexec trivial⟩
    | F_RVC h =>
      simp only [fetchIsRvc] at hrvc hdec'
      subst hrvc
      obtain ⟨i0, hdec0, -, hexp⟩ := hdec'
      exact ⟨_, execHartActiveProgressRVCGen .Machine sA sA sExec h i0 i pc RETIRE_SUCCESS
        Lpriv_a hdisp hfetch hdec0 Lelp_a Lpc_a (execCurrentlyEnabledZca sA HmisaC) (hexp _) hexec⟩
  obtain ⟨retval, hha⟩ := hha
  have hst0 := execRiscvStepHartActive (wflatSt σ) sExec retval b hsi Lhs_a hha hhs hmi
  refine ⟨hst0, ?_⟩
  obtain ⟨c, ti, p, htick⟩ := execTickClock (hartActiveSFinal sExec b)
  exact ⟨c, ti, p, execRiscvStepTick _ _ _ hst0 htick⟩

/-! ### 3b. THE O2 FETCH OBLIGATION OF `wP_conf`, supplied (Lean-only)

`WeakCert.wPConf` carries `fetchPin` for every trace of the confined run
(WeakCert deviation 4).  `wPConfText pc` is Rocq's `wP_conf` with that
replaced by what a leaf knows of its own trace -- its i-cache reads lie in the
text window at `pc` and nothing is fetched after a write
(`WeakAcquire.fetchInWindow`, `WeakCert.fetchFresh`) -- and the certificate's
own text pin supplies the rest (`WeakAcquire.fetchPinOfText`). -/

def wPConfText (pc : BitVec 64) : Wmstate → Prop :=
  fun s => wlogWf s.wmLog ∧
    ∃ W : GSet PAddr,
      (∀ a, a ∈ W → paZ a ≠ 0) ∧
      (∀ a, a ∈ W → pinnedRead s (paZ a)) ∧
      (∀ tick : Bool, ∃ t' : ExecSt,
        exec (riscvStep tick) ⟨s.wmRegs, wmemRestrict s W, s.wmDev⟩ = some ((), t') ∧
        bmDomSub t'.mem W) ∧
      (∀ (tick : Bool) (t' : ExecSt) (es : List Weff),
        execEff (riscvStep tick) ⟨s.wmRegs, wmemRestrict s W, s.wmDev⟩ = some ((), t', es) →
        fetchInWindow pc es ∧ fetchFresh es)

theorem wstepCertConfText (cid : Nat) (pc : BitVec 64) : wstepCert cid pc (wPConfText pc) wQNone := by
  intro σ tick hpc hacc htext hP
  obtain ⟨hwf, W, hW0, hWp, hrun, hfi⟩ := hP
  refine wstepCertConfNone cid pc σ tick hpc hacc htext ⟨hwf, W, hW0, hWp, hrun, ?_⟩
  intro tick' t' es hes
  obtain ⟨hw, hf⟩ := hfi tick' t' es hes
  exact fetchPinOfText σ pc es hw hf fun j hj => (htext j hj).2


/-! ## 3c. THE FUNNEL (owner decision Q3, option A)

Rocq's `InstrBytes.mmode_config dq` is restated as the Lean SC tree's
`mConf cpu dq c` (the M-mode configuration cells at fraction `dq`, with
`hwConfig`) PLUS the five OWNED clock cells `clockCells cpu` (Rocq's
`minstret_inv` ∗ `clock_inv` bodies: `minstret_increment`, `minstret`,
`mcycle`, `mtime`, `mip`); no invariant is opened, so every mask `⊤ ∖ ↑minstretN`
is `⊤`.  Rocq's separate `pmpcfg_n ↦ᵣ{dq} pmpcfg0` is `mConf`'s own cell
(`pmpcfg0 := c.pmpcfg`), and Rocq's mstatus facts are `MConf.mok c`. -/

/-- What the funnel reads off `mConf` at a register file (Lean-only). -/
def mConfFacts (f : RegFile) (c : MConf) : Prop :=
  f .cur_privilege = .Machine ∧ f .hart_state = .HART_ACTIVE () ∧ f .mstatus = c.mstatus ∧
  f .pmpcfg_n = c.pmpcfg ∧ f .misa = misaC ∧ f .mseccfg = 0#64 ∧ f .pma_regions = bootPMA ∧
  f .htif_tohost_base = none ∧ f .elp = 0#1

theorem wcfgRegsOf (σ : Wmstate) (c : MConf) (hmok : MConf.mok c) (h : mConfFacts σ.wmRegs c) :
    wcfgRegs σ c.pmpcfg := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h5, h6, h4, h7, h8, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h5]; decide
  · rw [h3, get_Mstatus_MIE_eq, hmok.1]; rfl
  · rw [h3, get_Mstatus_MPRV_eq, hmok.2]; rfl
  · rw [h6]; rfl
  · rw [h9]; decide

section funnel
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- The register reads of `mConf` (Lean-only; Rocq's `reg_valid_dq` block). -/
theorem mConfRegFacts (cpu : CPU) (dq : DFrac) (c : MConf) (f : RegFile) :
    regInterp (hlc := hlc) (GF := GF) cpu f ⊢ mConf cpu dq c -∗ ⌜mConfFacts f c⌝ := by
  iintro Hr Hm
  icases mConf_cases cpu dq c $$ Hm with ⟨H1, H2, H3, -, -, -, -, -, -, -, -, -, H13, -, #Hhw⟩
  ihave #Hmisa := hwConfig_reg cpu .misa misaC rfl $$ Hhw
  ihave #Hsec := hwConfig_reg cpu .mseccfg (0#64) rfl $$ Hhw
  ihave #Hpma := hwConfig_reg cpu .pma_regions bootPMA rfl $$ Hhw
  ihave #Hhtif := hwConfig_reg cpu .htif_tohost_base none rfl $$ Hhw
  ihave #Help := hwConfig_reg cpu .elp (0#1) rfl $$ Hhw
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr H1 with ⟨%E1, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr H2 with ⟨%E2, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr H3 with ⟨%E3, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr H13 with ⟨%E4, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr Hmisa with ⟨%E5, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr Hsec with ⟨%E6, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr Hpma with ⟨%E7, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr Hhtif with ⟨%E8, Hr, -⟩
  ihave %E9 := wand_intro (reg_valid cpu f _ _ _) $$ Hr Help
  ipureintro
  exact ⟨E1, E2, E3, E4, E5, E6, E7, E8, E9⟩

/-- The wrapper's own register writes after a retiring execute: tick PC, maybe
bump minstret (Lean-only; Rocq's inline `reg_update`s). -/
theorem wwpRetireRegs (cpu : CPU) (sExec : ExecSt) (b : Bool) (pc0 m0 : BitVec 64) :
    regInterp (hlc := hlc) (GF := GF) cpu sExec.regs ⊢
      Register.PC ↦ᵣ[cpu] pc0 -∗ Register.minstret ↦ᵣ[cpu] m0 -∗
        |==> (regInterp cpu (hartActiveSFinal sExec b).regs ∗
          Register.PC ↦ᵣ[cpu] (sExec.regs .nextPC) ∗ ∃ m : BitVec 64, Register.minstret ↦ᵣ[cpu] m) := by
  iintro Hr Hpc Hm
  imod (wand_intro (reg_update cpu _ .PC pc0 (sExec.regs .nextPC))) $$ Hr Hpc with ⟨Hr, Hpc⟩
  cases b
  · rw [show (hartActiveSFinal sExec false).regs = sExec.regs.set .PC (sExec.regs .nextPC) from rfl]
    imodintro
    iframe Hr Hpc
    iexists m0
    iexact Hm
  · rw [show (hartActiveSFinal sExec true).regs =
        (sExec.regs.set .PC (sExec.regs .nextPC)).set .minstret
          (BitVec.addInt ((sExec.regs.set .PC (sExec.regs .nextPC)) .minstret) 1) from rfl]
    imod (wand_intro (reg_update cpu _ .minstret m0
      (BitVec.addInt ((sExec.regs.set .PC (sExec.regs .nextPC)) .minstret) 1))) $$ Hr Hm with ⟨Hr, Hm⟩
    imodintro
    iframe Hr Hpc
    iexists _
    iexact Hm

/-- `tick_clock`'s three cells (Lean-only; Rocq opens `clock_inv` for them). -/
theorem wwpTickRegs (cpu : CPU) (t : ExecSt) (cy ti ip cy0 ti0 ip0 : BitVec 64) :
    regInterp (hlc := hlc) (GF := GF) cpu t.regs ⊢
      Register.mcycle ↦ᵣ[cpu] cy0 -∗ Register.mtime ↦ᵣ[cpu] ti0 -∗ Register.mip ↦ᵣ[cpu] ip0 -∗
        |==> (regInterp cpu (((t.setReg .mcycle cy).setReg .mtime ti).setReg .mip ip).regs ∗
          Register.mcycle ↦ᵣ[cpu] cy ∗ Register.mtime ↦ᵣ[cpu] ti ∗ Register.mip ↦ᵣ[cpu] ip) := by
  rw [show (((t.setReg .mcycle cy).setReg .mtime ti).setReg .mip ip).regs =
      ((t.regs.set .mcycle cy).set .mtime ti).set .mip ip from rfl]
  iintro Hr Hc Ht Hp
  imod (wand_intro (reg_update cpu _ .mcycle cy0 cy)) $$ Hr Hc with ⟨Hr, Hc⟩
  imod (wand_intro (reg_update cpu _ .mtime ti0 ti)) $$ Hr Ht with ⟨Hr, Ht⟩
  imod (wand_intro (reg_update cpu _ .mip ip0 ip)) $$ Hr Hp with ⟨Hr, Hp⟩
  imodintro
  iframe Hr Hc Ht Hp

/-- THE LEAF'S OBLIGATION (Rocq `wwp_cb`, on the option-A interface).  The leaf
receives, besides Rocq's (the PC, the config record, the latest-write
authority, the registers with the funnel's `minstret_increment := b` already
written, `wmstateNorg`), the `mtime`/`mip` cells (Rocq: `clock_inv`, which a
leaf could open inside its own fupd) and hands them back at some value; after
the step its continuation gets back `mConf`, the whole `clockCells` and the
stepped PC. -/
def wwpCb (gen : Nat) (cpu : CPU) (pc : BitVec 64) (is_rvc : Bool) (i : instruction) (c : MConf)
    (dq : DFrac) (P : Wmstate → Prop) (Q : Wmstate → Wmstate → Prop) : IProp GF :=
  iprop(∀ (σ : Wmstate) (b : Bool) (mt ip : BitVec 64),
    ⌜σ.wmRegs .PC = pc⌝ -∗
    ⌜wcfgRegs σ c.pmpcfg⌝ -∗
    wlatInterp σ.wmImg σ.wmLog -∗
    regInterp cpu ((wflatSt σ).setReg .minstret_increment b).regs -∗
    wmstateNorg (hlc := hlc) (GF := GF) cpu σ -∗
    Register.mtime ↦ᵣ[cpu] mt -∗
    Register.mip ↦ᵣ[cpu] ip ={⊤, ∅}=∗
      ⌜P σ⌝ ∗
      ∃ sExec : ExecSt,
        ⌜exec (execute i)
            (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
              (Sail.BitVec.addInt pc (if is_rvc then 2 else 4))) =
          some (RETIRE_SUCCESS, sExec)⌝ ∗
        regInterp cpu sExec.regs ∗
        (∃ mt' ip' : BitVec 64, Register.mtime ↦ᵣ[cpu] mt' ∗ Register.mip ↦ᵣ[cpu] ip') ∗
        ▷ (∀ (tick : Bool) (σ' : Wmstate) (t : ExecSt),
            ⌜exec (riscvStep tick) (wflatSt σ) = some ((), t)⌝ -∗
            ⌜t.dev = sExec.dev⌝ -∗
            ⌜wstepPost σ σ' t⌝ -∗
            ⌜Q σ σ'⌝ -∗
            mConf cpu dq c -∗
            clockCells cpu -∗
            Register.PC ↦ᵣ[cpu] (sExec.regs .nextPC) -∗
            |={∅, ⊤}=> (wlatInterp σ'.wmImg σ'.wmLog ∗
              wmstateNorg (hlc := hlc) (GF := GF) cpu σ' ∗
              wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))))

theorem wwpInstr (gen : Nat) (cpu : CPU) (pc : BitVec 64) (is_rvc : Bool) (i : instruction)
    (c : MConf) (dq : DFrac) (P : Wmstate → Prop) (Q : Wmstate → Wmstate → Prop) :
    gen = 0 →
    accWf pc 4 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    wstepCert cpu.val pc P Q →
    mConf (GF := GF) cpu dq c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      winstr pc is_rvc i -∗
      wwpCb (hlc := hlc) gen cpu pc is_rvc i c dq P Q -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hacc hmok hpmp hcert
  iintro Hm Hclk Hpc #Hinstr H
  unfold winstr wwpCb
  icases Hinstr with ⟨%hnlpad, %r, %hrvc, #Hb, %hdec⟩
  icases clockCells_cases cpu $$ Hclk with ⟨%mi0, %mst0, %cy0, %ti0, %ip0, Hmi, Hmst, Hcy, Hti, Hip⟩
  iapply wpWinstr gen cpu pc P Q hgen hacc hcert
  iintro %σ Hσ
  icases (wmstateInterpSplitRegs cpu σ).mp $$ Hσ with ⟨Hreg, Hlat, Hnorg⟩
  icases keepPure1 (wmstateNorgFacts cpu σ) $$ Hnorg with ⟨%hfacts, Hnorg⟩
  obtain ⟨_, hwf⟩ := hfacts
  -- every register the wrapper / fetch / decode reads, at `σ.wmRegs`
  icases keepPure (wand_intro (reg_valid cpu σ.wmRegs .PC _ pc)) $$ Hreg Hpc with ⟨%Lpc, Hreg, Hpc⟩
  icases keepPure (mConfRegFacts cpu dq c σ.wmRegs) $$ Hreg Hm with ⟨%hregs, Hreg, Hm⟩
  have hcfg : wcfgRegs σ c.pmpcfg := wcfgRegsOf σ c hmok hregs
  -- the two facts the weak fetch needs, off the text elements
  icases keepPure (winstrFlat σ pc r hwf) $$ Hlat Hb with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc r hwf) $$ Hlat Hb with ⟨%htext, Hlat, -⟩
  -- the funnel's own choice of the increment flag
  obtain ⟨b, hsi⟩ := execShouldIncMinstretSome (σ.wmRegs .cur_privilege) (wflatSt σ)
  imod (wand_intro (reg_update cpu σ.wmRegs .minstret_increment mi0 b)) $$ Hreg Hmi with ⟨Hreg, Hmi⟩
  rw [show σ.wmRegs.set .minstret_increment b = ((wflatSt σ).setReg .minstret_increment b).regs from rfl]
  -- the leaf's obligation
  imod H $$ %σ %b %ti0 %ip0 %Lpc %hcfg Hlat Hreg Hnorg Hti Hip
    with ⟨%hP, %sExec, %hexec, Hreg, ⟨%mt1, %ip1, Hti, Hip⟩, Hk⟩
  icases keepPure (mConfRegFacts cpu dq c sExec.regs) $$ Hreg Hm with ⟨%hregsE, Hreg, Hm⟩
  icases keepPure (wand_intro (reg_valid cpu sExec.regs .minstret_increment _ b)) $$ Hreg Hmi
    with ⟨%Lmi, Hreg, Hmi⟩
  obtain ⟨hst0, cc, tt, pp, hst1⟩ := wwpStepExec σ pc is_rvc i c.pmpcfg r b sExec hcfg hpmp Lpc hfok
    hrvc hnlpad hdec hsi hexec hregsE.2.1 Lmi
  have hdev0 : (hartActiveSFinal sExec b).dev = sExec.dev := hartActiveSFinalDev sExec b
  have hdev1 : ((((hartActiveSFinal sExec b).setReg .mcycle cc).setReg .mtime tt).setReg .mip pp).dev =
      sExec.dev := hdev0
  -- the wrapper's own register writes: tick PC, maybe bump minstret
  imod wwpRetireRegs cpu sExec b pc mst0 $$ Hreg Hpc Hmst with ⟨Hreg, Hpc, %mst1, Hmst⟩
  -- hand the two successors to `wpWinstr`
  imodintro
  isplitr
  · ipureintro; exact Lpc
  isplitr
  · ipureintro; exact htext
  isplitr
  · ipureintro; exact hP
  iexists (hartActiveSFinal sExec b),
    ((((hartActiveSFinal sExec b).setReg .mcycle cc).setReg .mtime tt).setReg .mip pp)
  isplitr
  · ipureintro; exact hst0
  isplitr
  · ipureintro; exact hst1
  inext
  iintro %tick %σ' %hpost %hQ
  cases tick
  · -- NO TICK: the registers are already those of `t0`
    simp only [Bool.false_eq_true, ↓reduceIte] at hpost
    have hregs' : σ'.wmRegs = (hartActiveSFinal sExec b).regs := hpost.1
    ihave Hclk := clockCells_introW cpu b mst1 cy0 mt1 ip1 $$ Hmi Hmst Hcy Hti Hip
    imod Hk $$ %false %σ' %(hartActiveSFinal sExec b) %hst0 %hdev0 %hpost %hQ Hm Hclk Hpc
      with ⟨Hlat', Hnorg', Hwp⟩
    imodintro
    isplitl [Hreg Hlat' Hnorg']
    · iapply (wmstateInterpSplitRegs cpu σ').mpr
      rw [hregs']
      iframe Hreg Hlat' Hnorg'
    · iexact Hwp
  · -- TICK: `tick_clock` wrote mcycle / mtime / mip
    simp only [↓reduceIte] at hpost
    have hregs' : σ'.wmRegs =
        ((((hartActiveSFinal sExec b).setReg .mcycle cc).setReg .mtime tt).setReg .mip pp).regs := hpost.1
    imod wwpTickRegs cpu (hartActiveSFinal sExec b) cc tt pp cy0 mt1 ip1 $$ Hreg Hcy Hti Hip
      with ⟨Hreg, Hcy, Hti, Hip⟩
    ihave Hclk := clockCells_introW cpu b mst1 cc tt pp $$ Hmi Hmst Hcy Hti Hip
    imod Hk $$ %true %σ' %((((hartActiveSFinal sExec b).setReg .mcycle cc).setReg .mtime tt).setReg .mip pp)
      %hst1 %hdev1 %hpost %hQ Hm Hclk Hpc with ⟨Hlat', Hnorg', Hwp⟩
    imodintro
    isplitl [Hreg Hlat' Hnorg']
    · iapply (wmstateInterpSplitRegs cpu σ').mpr
      rw [hregs']
      iframe Hreg Hlat' Hnorg'
    · iexact Hwp

/-! ## 4. SMOKE TEST: the funnel composing with a certificate

`wstepCertConfText` (§3b; Rocq `WeakCert.wstep_cert_conf_none`) discharges the
certificate for `P := wPConfText pc` and `Q := wQNone`. -/

theorem wwpInstrConf (gen : Nat) (cpu : CPU) (pc : BitVec 64) (is_rvc : Bool) (i : instruction)
    (c : MConf) (dq : DFrac) :
    gen = 0 →
    accWf pc 4 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    mConf (GF := GF) cpu dq c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      winstr pc is_rvc i -∗
      wwpCb (hlc := hlc) gen cpu pc is_rvc i c dq (wPConfText pc) wQNone -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) :=
  fun hgen hacc hmok hpmp =>
    wwpInstr gen cpu pc is_rvc i c dq _ _ hgen hacc hmok hpmp (wstepCertConfText cpu.val pc)

end funnel

end Weak
