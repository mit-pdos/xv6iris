/-
Weak: **the S-mode kernel regime `ctrlOkS` / `textAtS` and its FETCH field**, symbolically (for
every state in the regime).

Rocq: `iris/AxSpineOk6.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`ctrlOkS` is the PURE twin of the SC tier's S-mode kernel regime (`IntrDefs.sconf` +
`RiscvFetchExec.hw_config` + `KptShare.tlb_res_pt`, SIE=0 arm): priv = S, hart active,
misa = `misaC`, menvcfg = `menvcfgS`, no HTIF, elp ≠ LP_EXPECTED, the platform PMA table, the
`mstatus` facts with SIE = 0, `mie ∧ ¬mideleg = 0`, satp = the kernel satp `satp0` (Sv39, ASID 0,
root = `T.base`), the TLB holds only EXACT walk entries of the image tree `T` (`tlbExact`, D3),
and the kernel PMP entry 0 (TOR, R/X, covering RAM).  Not twinned: the SC `kpt_inv` (replaced by
the image hypotheses: the tree's slots are bytes of the fixed image `σi`) and the SIE=1 arm.
`textAtS pc h`: `pc`'s page is mapped by `T` (three slots in the image), the leaf passes the
fetch check with A preset, and the image at the translated pa holds `h` (2-aligned) / a word with
low half `h` (4-aligned) in RAM.  `sptFetchS`: THE FETCH FIELD — TLB hit (state unchanged) and
TLB miss (3 image PTE reads + fill), via `execATranslateAddrImg` + `execAFetchRVC{4,2}SGen` + the
`execA ⇒ EvA` bridge `execAEvA`.

## Deviations from Rocq

1. SPELLING (as `AxSpineOk3`/`AxSpineOk4` deviation 1/2): `mword n` ↦ `BitVec n`,
   `register_lookup r rs` ↦ `rs r`, `register_set r v rs` ↦ `rs.set r v`, `mstate` ↦ `ExecSt`,
   `eq_vec x y = b` ↦ `(x == y) = b`, `vec_access_dec v 0` ↦ `v[0]!`, `uint` ↦ `toNat`,
   `zeros' 64` ↦ `zeros (n := 64)` / `0#64`, `and_vec`/`not_vec` ↦ `&&&`/`~~~`,
   `ram_base + ram_size` ↦ `ramEnd`, `MISA_C` ↦ `misaC`, `MENVCFG_S` ↦ `menvcfgS`,
   `pt_base T` ↦ `T.base`, `svpn_of` ↦ `WeakKpt.svpnOf`, `ptree_maps`/`pt_addr2/1/0` ↦
   `AxPtProt.*`, `pt_slot_mem` ↦ `WeakWalkEff.ptSlotMem`, the image byte window
   `σi.(mem) !! pa_add pa j = Some (nth_byte w j)` ↦ `BytesAt σi pa n w`, `uint pa + n ≤ 2^64` ↦
   `paZ pa + n ≤ 2 ^ 64`; the `satp0` hypotheses take `AxSpineOk4` deviation 7's shapes.
2. `pma_allows_all (pma_regions)` ↦ `rs .pma_regions = bootPMA` (`WeakFetchEff` deviation 5,
   `WeakKpt` deviation 4); the PTE-read PMA fact is `WeakKpt.pmaAllowsBootPteRead`.
3. `IntrDefs.sconf_ms_facts` (not in the Lean tree; `MachCSL.smFacts` is a different, bit-slice
   bundle) is the Lean-only verbatim twin `AxSpineOk6.sconfMsFacts` (`have_nom_val` ↦
   `haveNomVal`).
4. `addr_is_ram pa ∧ addr_is_ram (pa_add pa k)` (k = n - 1) ↦ `inRam pa n` (`WeakFunnel`
   deviation 2), in `textAtS` and `ramFetchFacts`.  `ramFetchFacts` therefore drops Rocq's `k`
   and `Z.of_nat k = n - 1`, and its width bound is `0 < n ≤ 16` (Rocq `1 ≤ n ≤ 4096`; the PMA
   lemma `matching_pma_ram` is stated up to 16 — the only uses are n = 2, 4).
5. The Ltac `nseip` is dropped (pin tests are decided; `AxSpineOk3` deviation 5).
6. Section variables `σi T satp0` and hypotheses `Hmode Hasid Hppn` are explicit arguments (each
   declaration takes those it uses).

**Rocq → Lean name map.**  `pmp_ok` `AxSpineOk6.pmpOk` (file-qualified: `MachCSL.pmpOk` exists),
`ctrl_regs` `ctrlRegs`, `ctrl_ok_S` `ctrlOkS`,
`img_S` `imgS`, `text_at_S` `textAtS`, `ctrl_ok_S_agree` `ctrlOkSAgree`, `ram_fetch_facts`
`ramFetchFacts`, `ctrl_ok_S_tlb_fill` `ctrlOkSTlbFill`, `spt_fetch_S` `sptFetchS`.  None is in
the duplicated-name table.  Lean-only (file-qualified): `AxSpineOk6.sconfMsFacts`.

**Dropped:** the Ltac `nseip` (deviation 5).  Rocq 9 definitions/lemmas, Lean 9 + 1 Lean-only.
-/
import Weak.AxSpineOk4
import Weak.AxSpineOk5
import Weak.WeakLeafEffCommon

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- (Lean-only, deviation 3) Rocq `IntrDefs.sconf_ms_facts`, verbatim. -/
def AxSpineOk6.sconfMsFacts (ms : BitVec 64) : Prop :=
  (_get_Mstatus_MPRV ms == 1#1) = false ∧
  _get_Mstatus_SXL ms = 2#2 ∧
  (_get_Mstatus_MXR ms == 0#1) = true ∧
  (_get_Mstatus_TSR ms == 1#1) = false ∧
  _get_Mstatus_XS ms = extStatus_map_forwards .Off ∧
  _get_Mstatus_FS ms = extStatus_map_forwards .Off ∧
  _get_Mstatus_VS ms = extStatus_map_forwards .Off ∧
  _get_Mstatus_SD ms = 0#1 ∧
  haveNomVal (_get_Mstatus_MPP ms) = true ∧
  (_get_Mstatus_TVM ms == 1#1) = false ∧
  -- (Lean-only, 2026-11-04) SPELP/MPELP clear: with no Zicfilp the `sstatus` legalisation forces
  -- them to 0, so the identity of a no-op `csrrci sstatus` needs them 0 (`legalizeSieClearIdem`)
  (_get_Mstatus_SPELP ms = 0#1 ∧ _get_Mstatus_MPELP ms = 0#1)

/-- Rocq `pmp_ok`: the kernel PMP entry 0 (TOR, R/X, covering RAM). -/
def AxSpineOk6.pmpOk (rs : RegFile) : Prop :=
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (rs .pmpcfg_n)[0]!) = .TOR ∧
  zopz0zKzJ_u (zeros (n := 64)) (rs .pmpaddr_n)[0]! = false ∧
  (_get_Pmpcfg_ent_X (rs .pmpcfg_n)[0]! == 1#1) = true ∧
  (_get_Pmpcfg_ent_R (rs .pmpcfg_n)[0]! == 1#1) = true ∧
  ramEnd ≤ (rs .pmpaddr_n)[0]!.toNat * 4

/-- Rocq `ctrl_regs`: the registers the regime constrains. -/
def ctrlRegs : List Register :=
  [.cur_privilege, .hart_state, .misa, .menvcfg, .htif_tohost_base, .elp, .pma_regions, .mstatus,
   .mie, .mideleg, .satp, .tlb, .pmpcfg_n, .pmpaddr_n]

/-- Rocq `ctrl_ok_S`: the S-mode kernel regime (SIE = 0 arm), as facts about the register file. -/
def ctrlOkS (T : PTree) (satp0 : BitVec 64) (rs : RegFile) : Prop :=
  rs .cur_privilege = .Supervisor ∧
  rs .hart_state = .HART_ACTIVE () ∧
  rs .misa = misaC ∧
  rs .menvcfg = menvcfgS ∧
  rs .htif_tohost_base = none ∧
  (rs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false ∧
  rs .pma_regions = bootPMA ∧
  AxSpineOk6.sconfMsFacts (rs .mstatus) ∧
  (_get_Mstatus_SIE (rs .mstatus) == 1#1) = false ∧
  (rs .mie &&& ~~~(rs .mideleg)) = 0#64 ∧
  rs .satp = satp0 ∧
  tlbExact T (rs .tlb) ∧
  AxSpineOk6.pmpOk rs

/-- Rocq `img_S`. -/
def imgS (σi : ExecSt) : Image := imgOf σi

/-- Rocq `text_at_S pc h` (deviation 4). -/
def textAtS (σi : ExecSt) (T : PTree) (pc : BitVec 64) (h : BitVec 16) : Prop :=
  ∃ (p2 p1 w pa : BitVec 64),
    AxPtProt.ptreeMaps T (WeakKpt.svpnOf pc) p2 p1 w ∧
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr2 T (WeakKpt.svpnOf pc)) p2 ∧
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr1 p2 (WeakKpt.svpnOf pc)) p1 ∧
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf pc)) w ∧
    (∀ mxr dosum : Bool, pteCheckOk (.InstructionFetch ()) .Supervisor mxr dosum w) ∧
    update_PTE_Bits w (.InstructionFetch ()) = none ∧
    ptePbmt0 w ∧
    (pc != sign_extend (m := 64) (Sail.BitVec.extractLsb pc 38 0)) = false ∧
    zero_extend (m := 64) (ppn0 w +++ Sail.BitVec.extractLsb pc (Functions.pagesize_bits - 1) 0)
      = pa ∧
    (Sail.BitVec.access pc 0 != 0#1) = false ∧
    isRVC h = true ∧
    (if is_aligned_vaddr (.Virtaddr pc) 4 then
       ∃ w32 : BitVec 32, Sail.BitVec.extractLsb w32 15 0 = h ∧
         inRam pa 4 ∧ is_aligned_paddr (.Physaddr pa) 4 = true ∧ BytesAt σi pa 4 w32
     else
       (Sail.BitVec.access pc 1 != 0#1) = true ∧
         inRam pa 2 ∧ is_aligned_paddr (.Physaddr pa) 2 = true ∧ BytesAt σi pa 2 h)

/-- Rocq `ctrl_ok_S_agree`. -/
theorem ctrlOkSAgree (T : PTree) (satp0 : BitVec 64) (rs rs' : RegFile) :
    (∀ r, r ∈ ctrlRegs → rs' r = rs r) → ctrlOkS T satp0 rs → ctrlOkS T satp0 rs' := by
  intro hag hc
  unfold ctrlOkS AxSpineOk6.pmpOk at hc ⊢
  rw [hag .cur_privilege (by simp [ctrlRegs]), hag .hart_state (by simp [ctrlRegs]),
    hag .misa (by simp [ctrlRegs]), hag .menvcfg (by simp [ctrlRegs]),
    hag .htif_tohost_base (by simp [ctrlRegs]), hag .elp (by simp [ctrlRegs]),
    hag .pma_regions (by simp [ctrlRegs]), hag .mstatus (by simp [ctrlRegs]),
    hag .mie (by simp [ctrlRegs]), hag .mideleg (by simp [ctrlRegs]),
    hag .satp (by simp [ctrlRegs]), hag .tlb (by simp [ctrlRegs]),
    hag .pmpcfg_n (by simp [ctrlRegs]), hag .pmpaddr_n (by simp [ctrlRegs])]
  exact hc

/-- Rocq `ram_fetch_facts` (deviation 4): a regime fact, read at a state with the regime's
registers. -/
theorem ramFetchFacts (T : PTree) (satp0 : BitVec 64) (s : ExecSt) (pa : BitVec 64) (n : Nat) :
    ctrlOkS T satp0 s.regs → 0 < n → n ≤ 16 → (to_bits (l := 64) n).toNat = n →
    inRam pa n →
    ∃ region,
      pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) pa.toNat
        (to_bits (l := 64) n).toNat = .PMP_Match ∧
      matching_pma_region (s.regs .pma_regions) (.Physaddr pa) n = some region ∧
      (override_PMA region.attributes .PBMT_PMA).executable = true ∧
      exec (within_clint (.Physaddr pa) n) s = some (false, s) ∧
      exec (within_sig (.Physaddr pa) n) s = some (false, s) ∧
      exec (within_htif_readable (.Physaddr pa) n) s = some (false, s) ∧
      devAddr pa = false ∧ paZ pa + n ≤ 2 ^ 64 := by
  intro hc hn hn16 hu hram
  obtain ⟨-, -, -, -, hhtif, -, hpma, -, -, -, -, -, -, -, -, -, hcov⟩ := hc
  refine ⟨ramRegion, ?_, ?_, ramRegionExec, execWithinClintRam pa n s hram,
    execWithinSigFalse pa n s, execWithinHtifNone pa n s hhtif, devAddrRam pa n hram, ?_⟩
  · have hz : (zeros (n := 64)).toNat = 0 := rfl
    rw [hz, hu]
    exact pmpRangeMatch_full _ _ _ _ (Nat.zero_le _) hn (by have := hram.2; omega)
  · rw [hpma]; exact matching_pma_ram pa n hram hn hn16
  · have := hram.2
    unfold ramEnd at this
    unfold paZ
    omega

/-- Rocq `ctrl_ok_S_tlb_fill`. -/
theorem ctrlOkSTlbFill (T : PTree) (satp0 : BitVec 64) (rs : RegFile)
    (v : Vector (Option TLB_Entry) (2 ^ 6)) (p2 p1 w : BitVec 64) (vpn : BitVec 27) :
    ctrlOkS T satp0 rs → AxPtProt.ptreeMaps T vpn p2 p1 w → rs .tlb = v →
    ctrlOkS T satp0 (rs.set .tlb (vectorUpdate v (tlb_hash 39 vpn)
      (some (uWalkEntry vpn p2 p1 w 0#16)))) := by
  intro hc hmaps hv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hc
  unfold ctrlOkS AxSpineOk6.pmpOk at *
  simp (disch := decide) only [RegFile.set_same, RegFile.set_other]
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, h13⟩
  exact tlbExactFill T v vpn p2 p1 w hmaps (hv ▸ h12)

/-- Rocq `spt_fetch_S`: THE FETCH FIELD. -/
theorem sptFetchS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (t : ExecSt) (pc : BitVec 64) (h : BitVec 16) :
    ctrlOkS T satp0 t.regs → t.regs .PC = pc → textAtS σi T pc h →
    ∃ t1, tlbFrame t t1 ∧ ctrlOkS T satp0 t1.regs ∧
      EvA (imgS σi) (fun _ _ => False) (fun r t' => r = .F_RVC h ∧ t' = t1) (fetch ()) t := by
  intro hc hPC ⟨p2, p1, w, pa, hmaps, hs2, hs1, hs0, hchk, hupd, hpb, hcanon, hout, hb0, hRVC, hal⟩
  let σ : ExecSt := ⟨t.regs, σi.mem, t.dev⟩
  have hc0 := hc
  obtain ⟨hpriv, -, hmisa, hmenv, hhtif, -, hpma, hms, -, -, hsatp, htlbx, hA, hord, -, hR, hcov⟩ :=
    hc0
  obtain ⟨-, hSXL, -⟩ := hms
  have htm := execTranslationModeSSv39 satp0 σ hSXL hsatp hmode
  have heff := execEffectivePrivilegeFetch (σ.regs .mstatus) .Supervisor σ
  have hss := execIsShadowStackFetch σ
  have hpmar : WeakKpt.pmaAllowsPteRead (σ.regs .pma_regions) := by
    show WeakKpt.pmaAllowsPteRead (t.regs .pma_regions)
    rw [hpma]; exact WeakKpt.pmaAllowsBootPteRead
  -- the image slots are slots of σ (same memory)
  have hs2' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr2 T (WeakKpt.svpnOf pc)) p2 := hs2
  have hs1' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr1 p2 (WeakKpt.svpnOf pc)) p1 := hs1
  have hs0' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf pc)) w := hs0
  obtain ⟨σ', htr, hσ'⟩ := execATranslateAddrImg (.InstructionFetch ()) .Supervisor T.base pc w pa
    satp0 T (σ.regs .tlb) p2 p1 σ hchk hupd hcanon hout hpb rfl hmaps htlbx hs2' hs1' hs0' hmisa
    hmenv hhtif hpriv htm heff hss hsatp hppn hasid rfl hA hord hR hcov hpmar
  have hc' : ctrlOkS T satp0 σ'.regs := by
    rcases hσ' with rfl | rfl
    · exact hc
    · exact ctrlOkSTlbFill T satp0 t.regs _ p2 p1 w _ hc hmaps rfl
  have hmem' : σ'.mem = σi.mem := by rcases hσ' with rfl | rfl <;> rfl
  have hc'0 := hc'
  obtain ⟨hpriv', -, -, -, -, -, -, -, -, -, -, -, hA', hord', hX', -, -⟩ := hc'0
  have hf : execA (fetch ()) σ = some (.F_RVC h, σ') := by
    cases hal4 : is_aligned_vaddr (.Virtaddr pc) 4
    · rw [hal4] at hal
      simp only [Bool.false_eq_true, ↓reduceIte] at hal
      obtain ⟨hb1, hram, halp, hbytes⟩ := hal
      obtain ⟨region, hrange, hm, hx, hcl, hsig, hh, hdev, hwf⟩ :=
        ramFetchFacts T satp0 σ' pa 2 hc' (by decide) (by decide) (by decide) hram
      have hmC : (_get_Misa_C (σ.regs .misa) == 1#1) = true := by
        show (_get_Misa_C (t.regs .misa) == 1#1) = true
        rw [hmisa]; decide
      exact execAFetchRVC2SGen pc pa h σ σ' region hPC hmC hb0 hb1 hal4 htr hA' hord' hrange hX' hm
        halp hx hcl hsig hh hdev hwf (by intro j hj; rw [hmem']; exact hbytes j hj) hpriv' hRVC
    · rw [hal4] at hal
      simp only [↓reduceIte] at hal
      obtain ⟨w32, hlow, hram, halp, hbytes⟩ := hal
      obtain ⟨region, hrange, hm, hx, hcl, hsig, hh, hdev, hwf⟩ :=
        ramFetchFacts T satp0 σ' pa 4 hc' (by decide) (by decide) (by decide) hram
      subst hlow
      exact execAFetchRVC4SGen pc pa w32 σ σ' region hPC hal4 htr hA' hord' hrange hX' hm halp hx
        hcl hsig hh hdev hwf (by intro j hj; rw [hmem']; exact hbytes j hj) hpriv' hRVC
  refine ⟨⟨σ'.regs, t.mem, t.dev⟩, ?_, hc', ?_⟩
  · rcases hσ' with rfl | rfl
    · left; rfl
    · right; exact ⟨_, rfl⟩
  · have hE := execAEvA (fetch ()) σ _ σ' hf t rfl
    refine EvAMono (imgS σi) _ _ _ _ (fetch ()) t (fun _ _ hf => hf) ?_ hE
    rintro x ⟨r', m', d'⟩ ⟨rfl, hr, hm1, hd1⟩
    exact ⟨rfl, by simp only at hr hm1 hd1; subst hr hm1 hd1; rfl⟩

end Weak
