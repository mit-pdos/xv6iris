/-
Weak: **PHASE 5 ROW-DIRECTED POSITIONAL ENGINE, part 1 (pure, Sail-level)**: the POSITIONAL
(`BFin`) whole-instruction `AxCert.Cert` spine at the S-mode data regime `ctrlOkSW`, WARM-TLB form.

Rocq: `iris/AxSpinE.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxCert2.wpdInstrOfCertM` reports the continuation's row position only through the
certificate's READ BUDGET (at `BFin n` the row has exactly `n` items left).  The existing
whole-instruction spines (`spineCertXT`, `spineCertXT2`, `AxSymCtl2.spineCertC`) are at `BInf`,
so none of the X leaves can report the position; this file is the `BFin` spine.
§1 `cntFetchBase4SGen`: the 4-byte fetch's read count is the translation's
   (`cntFetchRVC4SGen` for `F_Base`).
§2 THE WARM FETCH: `fetchHitS` (compressed) / `fetch4HitS` (4-byte): at a regime state whose TLB
   HITS the pc's Sv39 page (`hitW`), the fetch is an `EvB` at every budget leaving the state
   UNCHANGED (no TLB fill).
§3 `Cert` at `BFin` from read-free / counted pieces: `CertNrd` (an `EvA` fact of a read-free
   tree keeps the budget), `CertEvBc` (a counted `EvB` fact consumes its count), `CertExecACnt`,
   and the `BFin` twins of the `run_hart_active` / `try_step` pieces (`CertHartActiveRvcB`,
   `CertHartActiveBaseB`, `CertTryStepActiveB`).
§4 THE POSITIONAL SPINE `AxSpinE.spineCertB` (both widths): from a boundary of the regime whose
   TLB hits the pc's page, with the text fact `textOkB` and an `execute` certificate `CertB`
   consuming exactly `e` row items, `riscvStep tick` (both ticks, every pin answer) is a `Cert`
   at `BFin (e + b)` ending at `BFin b` in `GoodB` (= `GoodC` + the TLB unchanged, so the next
   instruction's fetch still hits).  `CertBOfCertC`: every register-only / control instruction
   with an SC `exec` fact (`CertC`, `rfF` footprint) has a `CertB` with `e = 0`.
SCOPE (as Rocq): WARM TLB only (a cold fetch consumes the walk's reads and may evict a page).

## Deviations from Rocq

1. O2 STAGE C COUNTS (`AxSymCtl4` deviation 1): the instruction read of a fetch is the pinned
   admin step and consumes NO row item.  So on a TLB hit the fetch consumes 0 row items (Rocq 1):
   * `cntFetchBase4SGen` concludes `cntA (fetch ()) s = ntr` (Rocq `ntr + 1`);
   * `fetchHitS` / `fetch4HitS` have post `b = b'` (Rocq `b = b' + 1`);
   * `CertHartActiveRvcB` / `CertHartActiveBaseB` take that fetch fact and go from `BFin b` to
     `BFin b` (Rocq `BFin (b + 1)`);
   * `AxSpinE.spineCertB` starts at `BFin (e + b)` (Rocq `BFin (e + b + 1)`): the instruction
     consumes EXACTLY `e` row items (Rocq `e + 1`).
2. Q7 (as `AxSymCtl2` deviation 2 / `AxCert4` deviation 1): the 4-byte arm announces the word,
   so `textOkB`'s base arm carries `sfAnnB 32 w = false` after `textAt4S σi T pc w`, and
   `CertHartActiveBaseB` takes `hw : sfAnnB 32 w = false` (after `Qx`).
3. THE PINS: `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg` (Ltac `nseipE` dropped; pin
   tests decided).  Spellings as `AxSymCtl4`/`AxCert4`: `register_lookup r s.(sregs)` ↦
   `s.regs r`, `set_reg` ↦ `setReg`, `add_vec_int` ↦ `BitVec.addInt`, `mstate` ↦ `ExecSt`,
   `MState r m d` ↦ `⟨r, m, d⟩`, `CS d b r` ↦ `⟨d, b, r⟩`, `svpn_of` ↦ `WeakKpt.svpnOf`,
   `tlb_hitv` ↦ `tlbHitv`, `gpr_agree` ↦ `gprAgree`, `ow_ok` ↦ `owOk`, `img_of` ↦ `imgOf`.
4. Section variables (`σi T satp0`, `Hmode Hasid Hppn`, `img dok kind`) are explicit arguments;
   `textOkB`/`CertB`/`GoodB`/`tickFrameCtrlSW` take `σi T satp0` (and `dok kind`) explicitly.
   The Rocq section notations `CM`/`EvM`/`EvN` are unfolded; the Ltac `lk` is replaced by
   `RegFile.set_*` rewrites.
5. `CertExecACnt` states the run at `⟨t.regs, σ.mem, t.dev⟩` and the post at
   `⟨s1.regs, t.mem, t.dev⟩`, as Rocq.

**Rocq → Lean name map.**  `cnt_fetch_Base_4_S_gen` `cntFetchBase4SGen`, `mstate_ext`
`mstateExt`, `hitW` `hitW`, `hitW_agree` `hitWAgree`, `fetch_hit_S` `fetchHitS`, `fetch4_hit_S`
`fetch4HitS`, `Cert_nrd` `CertNrd`, `Cert_EvBc` `CertEvBc`, `Cert_execA_cnt` `CertExecACnt`,
`Cert_hart_active_rvcB` `CertHartActiveRvcB`, `Cert_hart_active_baseB` `CertHartActiveBaseB`,
`Cert_try_step_activeB` `CertTryStepActiveB`, `text_okB` `textOkB`, `CertB` `CertB`, `GoodB`
`GoodB`, `tick_frame_ctrl_SW` `tickFrameCtrlSW`, `spine_certB` `AxSpinE.spineCertB` (duplicated
name: also AxSymEngine3), `CertB_of_CertC` `CertBOfCertC`.  Lean-only (file-qualified):
`AxSpinE.certOfEvBF` (the `EvB` embedding with an empty exception post), `AxSpinE.cRUseB` /
`AxSpinE.cFactUseB` (the `BFin` twins of `AxCert4.cRUse` / `cFactUse`: an `EvA` fact of a
read-free tree keeps the budget).

**Dropped:** nothing (Rocq 18 definitions/lemmas + 2 Ltacs; Lean 18 + 3 Lean-only).
**Not ported:** the Ltacs `nseipE`, `lk` (deviation 3, 4); the `Print Assumptions` lines (the
lint's axiom check covers them).
-/
import Weak.AxLeafS
import Weak.AxCert4
import Weak.AxSymCtl4

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. The 4-byte fetch's read count -/

/-- Rocq `cnt_fetch_Base_4_S_gen` (deviation 1: `= ntr`, Rocq `ntr + 1`). -/
theorem cntFetchBase4SGen (va pa : BitVec 64) (w : BitVec 32) (s s1 : ExecSt)
    (region : PMA_Region) (ntr : Nat) (hpc : s.regs .PC = va)
    (hvalign : is_aligned_vaddr (.Virtaddr va) 4 = true)
    (htr : execA (translateAddr (.Virtaddr va) (.InstructionFetch ())) s
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1))
    (htrc : cntA (translateAddr (.Virtaddr va) (.InstructionFetch ())) s = ntr)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s1.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s1.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s1.regs .pmpaddr_n)[0]!.toNat * 4) pa.toNat
      (to_bits (l := 64) 4).toNat = .PMP_Match)
    (hX : (_get_Pmpcfg_ent_X (s1.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hm : matching_pma_region (s1.regs .pma_regions) (.Physaddr pa) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr pa) 4 = true)
    (hx : (override_PMA region.attributes .PBMT_PMA).executable = true)
    (hc : exec (within_clint (.Physaddr pa) 4) s1 = some (false, s1))
    (hsig : exec (within_sig (.Physaddr pa) 4) s1 = some (false, s1))
    (hh : exec (within_htif_readable (.Physaddr pa) 4) s1 = some (false, s1))
    (hdev : devAddr pa = false) (hwf : paZ pa + 4 ≤ 2 ^ 64) (hb : BytesAt s1 pa 4 w)
    (hpriv : s1.regs .cur_privilege = .Supervisor)
    (hrvc : isRVC (Sail.BitVec.extractLsb w 15 0) = false) :
    cntA (fetch ()) s = ntr := by
  have hmr := execAMemReadFetch4S .PBMT_PMA pa region w s1 hA hlt hr hX hm hal hx hc hsig hh hdev hwf
    hb hpriv
  have hmrc := cntMemReadFetch4S .PBMT_PMA pa region w s1 hA hlt hr hX hm hal hx hc hsig hh hdev hwf
    hb hpriv
  have hfb := AxSpineOk3.execAFetchBytesOk va va pa 4 .PBMT_PMA w s s1 htr hmr
  have hfbc := AxSymCtl4.cntFetchBytesOk va va pa 4 .PBMT_PMA w s s1 ntr 0 htr htrc hmr hmrc
  unfold fetch ext_fetch_check_pc get_config_rvfi
  rw [cntACatchEarlyReturn]
  simp (config := { decide := true }) only [AxSymCtl4.cntARBind, execARBind, cntARLiftR,
    execARLiftR, execARReturnRFwd, cntARReturnR, readReg, PreSail.readReg, PreSail.emit, execA,
    cntA, hpc, bit0ClearOfAligned4 va hvalign, bit1ClearOfAligned4 va hvalign, hvalign,
    execACurrentlyEnabledZiccif, AxSymCtl4.cntCurrentlyEnabledZiccif, hfb, hfbc, hrvc, ↓reduceIte,
    Bool.false_eq_true, Functions.not, Nat.reduceMul, BitVec.setWidth_eq, Nat.add_zero,
    Nat.zero_add]

/-! # 2. The WARM fetch: state unchanged (Stage C: no row item) -/

/-- Rocq `mstate_ext`. -/
theorem mstateExt (t t' : ExecSt) :
    t'.regs = t.regs → t'.mem = t.mem → t'.dev = t.dev → t' = t := by
  intro h1 h2 h3
  cases t; cases t'
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

/-- Rocq `hitW`: the TLB hits `va`'s Sv39 page. -/
def hitW (rs : RegFile) (va : BitVec 64) : Prop :=
  tlbHitv (rs .tlb) (WeakKpt.svpnOf va) = true

/-- Rocq `hitW_agree`. -/
theorem hitWAgree (rs rs' : RegFile) (va : BitVec 64) :
    rs' .tlb = rs .tlb → hitW rs va → hitW rs' va := by
  intro h; unfold hitW; rw [h]; exact id

section fetchhit
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-- Rocq `fetch_hit_S` (deviation 1: post `b = b'`, Rocq `b = b' + 1`). -/
theorem fetchHitS (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (t : ExecSt) (pc : BitVec 64) (h : BitVec 16) :
    ctrlOkS T satp0 t.regs → t.regs .PC = pc → textAtS σi T pc h → hitW t.regs pc →
    ∀ b, EvB (imgS σi) (fun _ _ => False)
      (fun b' r t' => b = b' ∧ r = .F_RVC h ∧ t' = t) (fetch ()) t b := by
  intro hc hPC ⟨p2, p1, w, pa, hmaps, hs2, hs1, hs0, hchk, hupd, hpb, hcanon, hout, hb0, hRVC, hal⟩
    hhit
  let σ : ExecSt := ⟨t.regs, σi.mem, t.dev⟩
  have hc0 := hc
  obtain ⟨hpriv, -, hmisa, hmenv, hhtif, -, hpma, hms, -, -, hsatp, htlbx, hA, hord, hX, hR, hcov⟩ :=
    hc0
  obtain ⟨-, hSXL, -⟩ := hms
  have htm := execTranslationModeSSv39 satp0 σ hSXL hsatp hmode
  have heff := execEffectivePrivilegeFetch (σ.regs .mstatus) .Supervisor σ
  have hss := execIsShadowStackFetch σ
  have hpmar : WeakKpt.pmaAllowsPteRead (σ.regs .pma_regions) := by
    show WeakKpt.pmaAllowsPteRead (t.regs .pma_regions)
    rw [hpma]; exact WeakKpt.pmaAllowsBootPteRead
  have hs2' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr2 T (WeakKpt.svpnOf pc)) p2 := hs2
  have hs1' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr1 p2 (WeakKpt.svpnOf pc)) p1 := hs1
  have hs0' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf pc)) w := hs0
  obtain ⟨htr, htrc⟩ := cntTranslateAddrImg (.InstructionFetch ()) .Supervisor T.base pc w pa
    satp0 T (σ.regs .tlb) p2 p1 σ hchk hupd hcanon hout hpb rfl hmaps htlbx hs2' hs1' hs0' hmisa
    hmenv hhtif hpriv htm heff hss hsatp hppn hasid rfl hA hord hR hcov hpmar
  have hhit' : tlbHitv (σ.regs .tlb) (WeakKpt.svpnOf pc) = true := hhit
  rw [hhit'] at htr htrc
  simp only [↓reduceIte] at htr htrc
  have hf : execA (fetch ()) σ = some (.F_RVC h, σ) ∧
      cntA (fetch ()) σ = cntA (translateAddr (.Virtaddr pc) (.InstructionFetch ())) σ := by
    cases hal4 : is_aligned_vaddr (.Virtaddr pc) 4
    · rw [hal4] at hal
      simp only [Bool.false_eq_true, ↓reduceIte] at hal
      obtain ⟨hb1, hram, halp, hbytes⟩ := hal
      obtain ⟨region, hrange, hm, hx, hcl, hsig, hh, hdev, hwf⟩ :=
        ramFetchFacts T satp0 σ pa 2 hc (by decide) (by decide) (by decide) hram
      have hmC : (_get_Misa_C (σ.regs .misa) == 1#1) = true := by
        show (_get_Misa_C (t.regs .misa) == 1#1) = true
        rw [hmisa]; decide
      have hb' : BytesAt σ pa 2 h := fun j hj => hbytes j hj
      exact ⟨execAFetchRVC2SGen pc pa h σ σ region hPC hmC hb0 hb1 hal4 htr hA hord hrange hX hm
          halp hx hcl hsig hh hdev hwf hb' hpriv hRVC,
        cntFetchRVC2SGen pc pa h σ σ region _ hPC hmC hb0 hb1 hal4 htr rfl hA hord hrange hX hm
          halp hx hcl hsig hh hdev hwf hb' hpriv hRVC⟩
    · rw [hal4] at hal
      simp only [↓reduceIte] at hal
      obtain ⟨w32, hlow, hram, halp, hbytes⟩ := hal
      obtain ⟨region, hrange, hm, hx, hcl, hsig, hh, hdev, hwf⟩ :=
        ramFetchFacts T satp0 σ pa 4 hc (by decide) (by decide) (by decide) hram
      subst hlow
      have hb' : BytesAt σ pa 4 w32 := fun j hj => hbytes j hj
      exact ⟨execAFetchRVC4SGen pc pa w32 σ σ region hPC hal4 htr hA hord hrange hX hm halp hx
          hcl hsig hh hdev hwf hb' hpriv hRVC,
        cntFetchRVC4SGen pc pa w32 σ σ region _ hPC hal4 htr rfl hA hord hrange hX hm halp hx
          hcl hsig hh hdev hwf hb' hpriv hRVC⟩
  obtain ⟨hf, hfc⟩ := hf
  intro b
  have hE := execAEvB (fetch ()) σ _ _ hf t rfl b
  refine EvBMono (imgS σi) _ _ _ _ (fetch ()) t b (fun _ _ hf => hf) ?_ hE
  rintro b' x ⟨r', m', d'⟩ ⟨hb, rfl, hr, hm1, hd1⟩
  refine ⟨?_, rfl, ?_⟩
  · rw [hb, hfc, htrc]; rfl
  · simp only at hr hm1 hd1; subst hr hm1 hd1; rfl

/-- Rocq `fetch4_hit_S` (deviation 1: post `b = b'`, Rocq `b = b' + 1`). -/
theorem fetch4HitS (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (t : ExecSt) (pc : BitVec 64) (w32 : BitVec 32) :
    ctrlOkS T satp0 t.regs → t.regs .PC = pc → textAt4S σi T pc w32 → hitW t.regs pc →
    ∀ b, EvB (imgS σi) (fun _ _ => False)
      (fun b' r t' => b = b' ∧ r = .F_Base w32 ∧ t' = t) (fetch ()) t b := by
  intro hc hPC
    ⟨p2, p1, w, pa, hmaps, hs2, hs1, hs0, hchk, hupd, hpb, hcanon, hout, hal4, hnRVC, hram, halp,
      hbytes⟩ hhit
  let σ : ExecSt := ⟨t.regs, σi.mem, t.dev⟩
  have hc0 := hc
  obtain ⟨hpriv, -, hmisa, hmenv, hhtif, -, hpma, hms, -, -, hsatp, htlbx, hA, hord, hX, hR, hcov⟩ :=
    hc0
  obtain ⟨-, hSXL, -⟩ := hms
  have htm := execTranslationModeSSv39 satp0 σ hSXL hsatp hmode
  have heff := execEffectivePrivilegeFetch (σ.regs .mstatus) .Supervisor σ
  have hss := execIsShadowStackFetch σ
  have hpmar : WeakKpt.pmaAllowsPteRead (σ.regs .pma_regions) := by
    show WeakKpt.pmaAllowsPteRead (t.regs .pma_regions)
    rw [hpma]; exact WeakKpt.pmaAllowsBootPteRead
  have hs2' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr2 T (WeakKpt.svpnOf pc)) p2 := hs2
  have hs1' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr1 p2 (WeakKpt.svpnOf pc)) p1 := hs1
  have hs0' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf pc)) w := hs0
  obtain ⟨htr, htrc⟩ := cntTranslateAddrImg (.InstructionFetch ()) .Supervisor T.base pc w pa
    satp0 T (σ.regs .tlb) p2 p1 σ hchk hupd hcanon hout hpb rfl hmaps htlbx hs2' hs1' hs0' hmisa
    hmenv hhtif hpriv htm heff hss hsatp hppn hasid rfl hA hord hR hcov hpmar
  have hhit' : tlbHitv (σ.regs .tlb) (WeakKpt.svpnOf pc) = true := hhit
  rw [hhit'] at htr htrc
  simp only [↓reduceIte] at htr htrc
  obtain ⟨region, hrange, hm, hx, hcl, hsig, hh, hdev, hwf⟩ :=
    ramFetchFacts T satp0 σ pa 4 hc (by decide) (by decide) (by decide) hram
  have hb' : BytesAt σ pa 4 w32 := fun j hj => hbytes j hj
  have hf := execAFetchBase4SGen pc pa w32 σ σ region hPC hal4 htr hA hord hrange hX hm halp hx
    hcl hsig hh hdev hwf hb' hpriv hnRVC
  have hfc := cntFetchBase4SGen pc pa w32 σ σ region _ hPC hal4 htr htrc hA hord hrange hX hm halp
    hx hcl hsig hh hdev hwf hb' hpriv hnRVC
  intro b
  have hE := execAEvB (fetch ()) σ _ _ hf t rfl b
  refine EvBMono (imgS σi) _ _ _ _ (fetch ()) t b (fun _ _ hf => hf) ?_ hE
  rintro b' x ⟨r', m', d'⟩ ⟨hb, rfl, hr, hm1, hd1⟩
  refine ⟨?_, rfl, ?_⟩
  · rw [hb, hfc]; rfl
  · simp only at hr hm1 hd1; subst hr hm1 hd1; rfl

end fetchhit

/-! # 3. `Cert` at `BFin` from read-free and counted pieces -/

/-- (Lean-only) the `EvB` embedding with an empty exception post. -/
theorem AxSpinE.certOfEvBF (img : Image) (dok : Int → Nat → Prop) (kind : Dkind) {X : Type}
    (Q : Nat → X → ExecSt → Prop) (d : Cdata) (r : Bool) (m : SailM X) (t : ExecSt) (b : Nat) :
    EvB img (fun _ _ => False) Q m t b →
    AxCert.Cert img dok kind (fun _ _ _ => False)
      (fun s x t' => ∃ b', s = ⟨d, .BFin b', r⟩ ∧ Q b' x t') ⟨d, .BFin b, r⟩ m t := fun H =>
  CertMono img dok kind _ _ _ _ _ m t (fun _ _ _ ⟨_, _, h⟩ => h.elim) (fun _ _ _ h => h)
    (CertOfEvB img dok kind _ _ d r m t b H)

section certB
variable (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)

/-- Rocq `Cert_nrd`: a read-free `EvA` fact keeps the budget. -/
theorem CertNrd {X : Type} (P : X → ExecSt → Prop) (m : SailM X) (d : Cdata) (b : Nat) (r : Bool)
    (t : ExecSt) :
    EvA img (fun _ _ => False) P m t → nrd m →
    AxCert.Cert img dok kind (fun _ _ _ => False)
      (fun s x t' => s = ⟨d, .BFin b, r⟩ ∧ P x t') ⟨d, .BFin b, r⟩ m t := by
  intro H Hn
  refine CertMono img dok kind _ _ _ _ _ m t (fun _ _ _ h => h) ?_
    (AxSpinE.certOfEvBF img dok kind _ d r m t b (EvBOfEvA img _ _ m t H Hn b))
  rintro s x t' ⟨b', rfl, rfl, HP⟩
  exact ⟨rfl, HP⟩

/-- Rocq `Cert_EvBc`: a counted `EvB` fact consumes its count. -/
theorem CertEvBc {X : Type} (P : X → ExecSt → Prop) (m : SailM X) (c : Nat) (d : Cdata) (r : Bool)
    (t : ExecSt) :
    (∀ b, EvB img (fun _ _ => False) (fun b' x t' => b = b' + c ∧ P x t') m t b) →
    ∀ b, AxCert.Cert img dok kind (fun _ _ _ => False)
      (fun s x t' => s = ⟨d, .BFin b, r⟩ ∧ P x t') ⟨d, .BFin (b + c), r⟩ m t := by
  intro H b
  refine CertMono img dok kind _ _ _ _ _ m t (fun _ _ _ h => h) ?_
    (AxSpinE.certOfEvBF img dok kind _ d r m t (b + c) (H (b + c)))
  rintro s x t' ⟨b', rfl, Hb, HP⟩
  have e : b' = b := by omega
  subst e
  exact ⟨rfl, HP⟩

/-- Rocq `Cert_execA_cnt`: an `execA` fact with a read count `c`. -/
theorem CertExecACnt {X : Type} (Q : Cst → X → ExecSt → Prop) (σ : ExecSt) (m : SailM X) (x : X)
    (s1 : ExecSt) (c : Nat) (d : Cdata) (r : Bool) (b : Nat) (t : ExecSt) :
    img = imgOf σ →
    execA m ⟨t.regs, σ.mem, t.dev⟩ = some (x, s1) →
    cntA m ⟨t.regs, σ.mem, t.dev⟩ = c →
    Q ⟨d, .BFin b, r⟩ x ⟨s1.regs, t.mem, t.dev⟩ →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨d, .BFin (b + c), r⟩ m t := by
  intro himg He Hc HQ
  subst himg
  have HE := execAEvB m ⟨t.regs, σ.mem, t.dev⟩ x s1 He t rfl (b + c)
  rw [Hc] at HE
  refine CertMono (imgOf σ) dok kind _ _ _ _ _ m t (fun _ _ _ h => h) ?_
    (AxSpinE.certOfEvBF (imgOf σ) dok kind _ d r m t (b + c) HE)
  rintro s x' t' ⟨b', rfl, Hb, rfl, Hr, Hm, Hd⟩
  have e : b' = b := by omega
  subst e
  have Ht' : t' = ⟨s1.regs, t.mem, t.dev⟩ := mstateExt _ _ Hr Hm Hd
  rw [Ht']
  exact HQ

end certB

/-! ### (Lean-only) the `BFin` twins of `AxCert4.cRUse` / `AxCert4.cFactUse` -/

section kitB
variable {img : Image} {dok : Int → Nat → Prop} {kind : Dkind}
  {QE : Cst → Sail.Error exception → ExecSt → Prop}

/-- use a read-free `EvA` fact in the early-return monad (budget kept) -/
theorem AxSpinE.cRUseB {R X Y : Type}
    {Q : Cst → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {m : SailM Y} {f : Y → SailME R X} {d : Cdata} {b : Nat} {r : Bool} {t t1 : ExecSt} {a : Y}
    (Hm : EvA img (fun _ _ => False) (fun x t' => x = a ∧ t' = t1) m t) (Hn : nrd m)
    (H : AxCert.Cert img dok kind QE Q ⟨d, .BFin b, r⟩ (ExceptT.run (f a)) t1) :
    AxCert.Cert img dok kind QE Q ⟨d, .BFin b, r⟩ (ExceptT.run (liftM m >>= f)) t :=
  AxCert4.cFactLift (CertNrd img dok kind _ m d b r t Hm Hn)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

/-- use a read-free `EvA` fact (budget kept) -/
theorem AxSpinE.cFactUseB {X Y : Type} {Q : Cst → Y → ExecSt → Prop} {m : SailM X}
    {f : X → SailM Y} {d : Cdata} {b : Nat} {r : Bool} {t t1 : ExecSt} {a : X}
    (Hm : EvA img (fun _ _ => False) (fun x t' => x = a ∧ t' = t1) m t) (Hn : nrd m)
    (H : AxCert.Cert img dok kind QE Q ⟨d, .BFin b, r⟩ (f a) t1) :
    AxCert.Cert img dok kind QE Q ⟨d, .BFin b, r⟩ (m >>= f) t :=
  AxCert4.cFactQ (CertNrd img dok kind _ m d b r t Hm Hn)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

end kitB

section certB2
variable (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)

/-- Rocq `Cert_hart_active_rvcB` (deviation 1: the warm fetch keeps the budget, so `BFin b` to
`BFin b`; Rocq `BFin (b + 1)`). -/
theorem CertHartActiveRvcB (t : ExecSt) (h : BitVec 16) (i0 ins : instruction) (pc : BitVec 64)
    (d : Cdata) (r : Bool) (b : Nat) (Qx : Cst → ExecSt → Prop) :
    EvA img (fun _ _ => False) (fun r t' => r = none ∧ t' = t)
      (dispatchInterrupt (t.regs .cur_privilege)) t →
    (∀ b, EvB img (fun _ _ => False) (fun b' r t' => b = b' ∧ r = .F_RVC h ∧ t' = t)
      (fetch ()) t b) →
    EvA img (fun _ _ => False) (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed h) t →
    nrd (ext_decode_compressed h) →
    EvA img (fun _ _ => False) (fun x t' => x = false ∧ t' = t) (is_landing_pad_expected ()) t →
    EvA img (fun _ _ => False) (fun x t' => x = true ∧ t' = t) (currentlyEnabled .Ext_Zca) t →
    t.regs .PC = pc →
    EvA img (fun _ _ => False)
      (fun x t' => x = .ExecuteAs ins ∧ t' = t.setReg .nextPC (BitVec.addInt pc 2))
      (execute i0) (t.setReg .nextPC (BitVec.addInt pc 2)) →
    nrd (execute i0) →
    AxCert.Cert img dok kind (fun _ _ _ => False) (fun s x t' => x = RETIRE_SUCCESS ∧ Qx s t')
      ⟨d, .BFin b, r⟩ (execute ins) (t.setReg .nextPC (BitVec.addInt pc 2)) →
    AxCert.Cert img dok kind (fun _ _ _ => False)
      (fun s x t' => x = .Step_Execute (RETIRE_SUCCESS, zero_extend (m := 32) h) ∧ Qx s t')
      ⟨d, .BFin b, r⟩ (run_hart_active 0) t := by
  intro Hdisp Hfetch Hdec Hden Hlpad Hzca HPC Hexp Hexn Hexec
  subst HPC
  unfold run_hart_active
  apply CertCatchEarlyReturn
  ax_cert4_go
  refine AxSpinE.cRUseB Hdisp (nrdDispatchInterrupt _) ?_
  ax_cert4_go
  refine AxCert4.cFactLift (AxSpinE.certOfEvBF img dok kind _ d r _ t b (Hfetch b)) ?_
  rintro _ _ _ ⟨b', rfl, rfl, rfl, rfl⟩
  ax_cert4_go
  refine AxSpinE.cRUseB Hdec Hden ?_
  ax_cert4_go
  refine AxSpinE.cRUseB Hlpad nrdLpad ?_
  ax_cert4_go
  refine AxSpinE.cRUseB Hzca nrdZca ?_
  ax_cert4_go
  refine AxSpinE.cRUseB Hexp Hexn ?_
  ax_cert4_go
  refine AxCert4.cFactLift Hexec ?_
  rintro _ _ t' ⟨rfl, hq⟩
  ax_cert4_go
  exact .cRet _ _ _ ⟨rfl, hq⟩

/-- Rocq `Cert_hart_active_baseB` (deviations 1, 2). -/
theorem CertHartActiveBaseB (t : ExecSt) (w : BitVec 32) (ins : instruction) (pc : BitVec 64)
    (d : Cdata) (r : Bool) (b : Nat) (Qx : Cst → ExecSt → Prop) (hw : sfAnnB 32 w = false) :
    EvA img (fun _ _ => False) (fun r t' => r = none ∧ t' = t)
      (dispatchInterrupt (t.regs .cur_privilege)) t →
    (∀ b, EvB img (fun _ _ => False) (fun b' r t' => b = b' ∧ r = .F_Base w ∧ t' = t)
      (fetch ()) t b) →
    EvA img (fun _ _ => False) (fun x t' => x = ins ∧ t' = t) (ext_decode w) t →
    nrd (ext_decode w) →
    EvA img (fun _ _ => False) (fun x t' => x = false ∧ t' = t) (is_landing_pad_expected ()) t →
    t.regs .PC = pc →
    AxCert.Cert img dok kind (fun _ _ _ => False) (fun s x t' => x = RETIRE_SUCCESS ∧ Qx s t')
      ⟨d, .BFin b, r⟩ (execute ins) (t.setReg .nextPC (BitVec.addInt pc 4)) →
    AxCert.Cert img dok kind (fun _ _ _ => False)
      (fun s x t' => x = .Step_Execute (RETIRE_SUCCESS, zero_extend (m := 32) w) ∧ Qx s t')
      ⟨d, .BFin b, r⟩ (run_hart_active 0) t := by
  intro Hdisp Hfetch Hdec Hden Hlpad HPC Hexec
  subst HPC
  unfold run_hart_active
  apply CertCatchEarlyReturn
  ax_cert4_go
  refine AxSpinE.cRUseB Hdisp (nrdDispatchInterrupt _) ?_
  ax_cert4_go
  refine AxCert4.cFactLift (AxSpinE.certOfEvBF img dok kind _ d r _ t b (Hfetch b)) ?_
  rintro _ _ _ ⟨b', rfl, rfl, rfl, rfl⟩
  ax_cert4_go
  refine AxCert4.cRAnn32 hw ?_
  ax_cert4_go
  refine AxSpinE.cRUseB Hdec Hden ?_
  ax_cert4_go
  refine AxSpinE.cRUseB Hlpad nrdLpad ?_
  ax_cert4_go
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  ax_cert4_go
  refine AxCert4.cFactLift Hexec ?_
  rintro _ _ t' ⟨rfl, hq⟩
  ax_cert4_go
  exact .cRet _ _ _ ⟨rfl, hq⟩

/-- Rocq `Cert_try_step_activeB`. -/
theorem CertTryStepActiveB (t : ExecSt) (bb : Bool) (bits : BitVec 32) (d : Cdata) (r : Bool)
    (b : Nat) (Qx Qf : Cst → ExecSt → Prop) :
    EvA img (fun _ _ => False) (fun x t' => x = bb ∧ t' = t)
      (should_inc_minstret (t.regs .cur_privilege)) t →
    (t.setReg .minstret_increment bb).regs .hart_state = .HART_ACTIVE () →
    AxCert.Cert img dok kind (fun _ _ _ => False)
      (fun s x t' => x = .Step_Execute (RETIRE_SUCCESS, bits) ∧ Qx s t') ⟨d, .BFin b, r⟩
      (run_hart_active 0) (t.setReg .minstret_increment bb) →
    (∀ s tx, Qx s tx → tx.regs .hart_state = .HART_ACTIVE () ∧
      tx.regs .minstret_increment = bb ∧ Qf s (tfinal bb tx)) →
    AxCert.Cert img dok kind (fun _ _ _ => False) (fun s x t' => x = false ∧ Qf s t')
      ⟨d, .BFin b, r⟩ (try_step 0 false) t := by
  intro Hsi Hha Hrun Hfin
  unfold try_step
  dsimp only
  ax_cert4_go
  refine AxSpinE.cFactUseB Hsi (nrdShouldIncMinstret _) ?_
  ax_cert4_go
  apply CertBind
  ax_cert4_go
  simp only [Hha]
  refine CertMono img dok kind _ _ _ _ _ _ _ (fun _ _ _ h => h) ?_ Hrun
  rintro s _ tx ⟨rfl, HQ⟩
  obtain ⟨Hhx, Hmix, HQf⟩ := Hfin s tx HQ
  ax_cert4_go
  simp only [Hhx]
  ax_cert4_go
  simp only [Hhx]
  ax_cert4_go
  have hmi : (tx.setReg .PC (tx.regs .nextPC)).regs .minstret_increment = bb := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]
    exact Hmix
  simp only [hmi]
  cases bb <;> ax_cert4_go <;> exact .cRet _ _ _ ⟨rfl, HQf⟩

end certB2

/-! # 4. THE POSITIONAL SPINE -/

section spineB
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-- Rocq `text_okB`: the per-instruction text fact, both widths — the word at `pc`, its decode
(and, compressed, its expansion) read-free (deviation 2: the base word is not an sfence word). -/
def textOkB (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) : Prop :=
  if is_rvc then
    ∃ h i0, textAtS σi T pc h ∧
      (∀ t : ExecSt, ctrlOkSW T satp0 t.regs →
        EvA (imgS σi) (fun _ _ => False) (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed h) t) ∧
      nrd (ext_decode_compressed h) ∧
      (∀ t : ExecSt, EvA (imgS σi) (fun _ _ => False) (fun x t' => x = .ExecuteAs ins ∧ t' = t)
        (execute i0) t) ∧
      nrd (execute i0)
  else
    ∃ w, textAt4S σi T pc w ∧ sfAnnB 32 w = false ∧
      (∀ t : ExecSt, ctrlOkSW T satp0 t.regs →
        EvA (imgS σi) (fun _ _ => False) (fun x t' => x = ins ∧ t' = t) (ext_decode w) t) ∧
      nrd (ext_decode w)

/-- Rocq `CertB`: THE POSITIONAL EXECUTE CERTIFICATE — from every regime state at `pc` (nextPC
ticked, GPRs and TLB of `rs`), `execute ins` consumes EXACTLY `e` row items, ending in
`wrOpt (ow d) (npcOpt ot tpc)` with final data state / release flag in `PX`. -/
def CertB (dok : Int → Nat → Prop) (kind : Dkind) (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (e : Nat) (ot : Option (BitVec 64))
    (ow : Cdata → Option (BitVec 5 × BitVec 64)) (d0 : Cdata) (r0 : Bool)
    (PX : Cdata → Bool → Prop) : Prop :=
  ∀ tpc : ExecSt, ctrlOkSW T satp0 tpc.regs → tpc.regs .PC = pc →
    tpc.regs .nextPC = BitVec.addInt pc (incr is_rvc) →
    gprAgree tpc.regs rs → tpc.regs .tlb = rs .tlb → ∀ b,
    AxCert.Cert (imgS σi) dok kind (fun _ _ _ => False)
      (fun s x t' => x = RETIRE_SUCCESS ∧ ∃ d r, s = ⟨d, .BFin b, r⟩ ∧ PX d r ∧
        t' = wrOpt (ow d) (npcOpt ot tpc))
      ⟨d0, .BFin (e + b), r0⟩ (execute ins) tpc

/-- Rocq `GoodB`: the boundary post — `GoodC` + the TLB unchanged. -/
def GoodB (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (ot : Option (BitVec 64))
    (ow : Option (BitVec 5 × BitVec 64)) (rs' : RegFile) : Prop :=
  GoodC (ctrlOkSW T satp0) is_rvc rs pc ot ow rs' ∧ rs' .tlb = rs .tlb

/-- Rocq `tick_frame_ctrl_SW`. -/
theorem tickFrameCtrlSW (t t' : ExecSt) :
    tickFrame t t' → ctrlOkSW T satp0 t.regs → ctrlOkSW T satp0 t'.regs := fun hf ⟨hc, hw⟩ =>
  ⟨tickFrameCtrlS T satp0 t t' hf hc, pTick pmpW pmpWDep t t' hf hw⟩

/-- Rocq `spine_certB` (duplicated name): THE POSITIONAL SPINE (deviation 1: the instruction
consumes exactly `e` row items, `BFin (e + b)` to `BFin b`; Rocq `e + 1`). -/
theorem AxSpinE.spineCertB (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (dok : Int → Nat → Prop) (kind : Dkind)
    (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) (e : Nat)
    (ot : Option (BitVec 64)) (ow : Cdata → Option (BitVec 5 × BitVec 64)) (d0 : Cdata) (r0 : Bool)
    (PX : Cdata → Bool → Prop) :
    ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc → textOkB σi T satp0 pc is_rvc ins →
    (∀ d r, PX d r → owOk (ow d)) → CertB σi T satp0 dok kind rs pc is_rvc ins e ot ow d0 r0 PX →
    ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs → ∀ b,
      AxCert.Cert (imgS σi) dok kind (fun _ _ _ => False)
        (fun s _ t' => ∃ d r, s = ⟨d, .BFin b, r⟩ ∧ PX d r ∧
          GoodB T satp0 rs pc is_rvc ot (ow d) t'.regs)
        ⟨d0, .BFin (e + b), r0⟩ (riscvStep tick) t := by
  intro Hct HPC Hhit Htx How Hcert tick t Hag b
  have Hsp := SpineOkTSW σi T satp0 hmode hasid hppn
  have Hct_t : ctrlOkSW T satp0 t.regs := Hsp.sptSeip _ _ Hct Hag
  have HPC_t : t.regs .PC = pc := by
    rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))]; exact HPC
  have Htlb_t : t.regs .tlb = rs .tlb := Hag .tlb (AxSymEngine2.notPin _ (by decide) (by decide))
  obtain ⟨bb, Hb⟩ := Hsp.sptInc t Hct_t
  have Hct_a : ctrlOkSW T satp0 (t.setReg .minstret_increment bb).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inl rfl))) Hct_t
  have HPC_a : (t.setReg .minstret_increment bb).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_t
  have Htlb_a : (t.setReg .minstret_increment bb).regs .tlb = rs .tlb := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact Htlb_t
  have Hhit_a : hitW (t.setReg .minstret_increment bb).regs pc := hitWAgree _ _ _ Htlb_a Hhit
  have Hgag : gprAgree
      ((t.setReg .minstret_increment bb).setReg .nextPC (BitVec.addInt pc (incr is_rvc))).regs rs := by
    intro r _
    simp only [ExecSt.setReg_regs]
    rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide), AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
    exact AxSymEngine2.uxaXgetAgree _ _ Hag r
  have Hct_pc : ctrlOkSW T satp0
      ((t.setReg .minstret_increment bb).setReg .nextPC (BitVec.addInt pc (incr is_rvc))).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inl rfl)) Hct_a
  have HPC_pc : ((t.setReg .minstret_increment bb).setReg .nextPC
      (BitVec.addInt pc (incr is_rvc))).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_a
  have Hnpc_pc : ((t.setReg .minstret_increment bb).setReg .nextPC
      (BitVec.addInt pc (incr is_rvc))).regs .nextPC = BitVec.addInt pc (incr is_rvc) := by
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  have Htlb_pc : ((t.setReg .minstret_increment bb).setReg .nextPC
      (BitVec.addInt pc (incr is_rvc))).regs .tlb = rs .tlb := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact Htlb_a
  have Hexec := Hcert _ Hct_pc HPC_pc Hnpc_pc Hgag Htlb_pc b
  have Hrun : ∃ bits, AxCert.Cert (imgS σi) dok kind (fun _ _ _ => False)
      (fun s x t' => x = .Step_Execute (RETIRE_SUCCESS, bits) ∧
        ∃ d r, s = ⟨d, .BFin b, r⟩ ∧ PX d r ∧ t' = wrOpt (ow d) (npcOpt ot
          ((t.setReg .minstret_increment bb).setReg .nextPC (BitVec.addInt pc (incr is_rvc)))))
      ⟨d0, .BFin (e + b), r0⟩ (run_hart_active 0) (t.setReg .minstret_increment bb) := by
    cases is_rvc with
    | true =>
      rw [textOkB, if_pos rfl] at Htx
      obtain ⟨h, i0, Hat, Hdec, Hden, Hexp, Hexn⟩ := Htx
      exact ⟨zero_extend (m := 32) h,
        CertHartActiveRvcB (imgS σi) dok kind _ h i0 ins pc d0 r0 (e + b) _
          (Hsp.sptDisp _ Hct_a)
          (fetchHitS σi T satp0 hmode hasid hppn _ pc h Hct_a.1 HPC_a Hat Hhit_a)
          (Hdec _ Hct_a) Hden (Hsp.sptLpad _ Hct_a) (Hsp.sptZca _ Hct_a) HPC_a (Hexp _) Hexn
          Hexec⟩
    | false =>
      rw [textOkB, if_neg Bool.false_ne_true] at Htx
      obtain ⟨w, Hat, Hsf, Hdec, Hden⟩ := Htx
      exact ⟨zero_extend (m := 32) w,
        CertHartActiveBaseB (imgS σi) dok kind _ w ins pc d0 r0 (e + b) _ Hsf
          (Hsp.sptDisp _ Hct_a)
          (fetch4HitS σi T satp0 hmode hasid hppn _ pc w Hct_a.1 HPC_a Hat Hhit_a)
          (Hdec _ Hct_a) Hden (Hsp.sptLpad _ Hct_a) HPC_a Hexec⟩
  obtain ⟨bits, Hrun⟩ := Hrun
  refine CertRiscvStep (imgS σi) dok kind tick ⟨d0, .BFin (e + b), r0⟩ t
    (fun s t' => ∃ d r, s = ⟨d, .BFin b, r⟩ ∧ PX d r ∧ GoodB T satp0 rs pc is_rvc ot (ow d) t'.regs)
    _ ?_ ?_
  · have HT := CertTryStepActiveB (imgS σi) dok kind t bb bits d0 r0 (e + b) _
      (fun s t' => ∃ d r, s = ⟨d, .BFin b, r⟩ ∧ PX d r ∧ GoodB T satp0 rs pc is_rvc ot (ow d) t'.regs)
      Hb (Hsp.sptHart _ Hct_a) Hrun ?_
    · exact CertMono (imgS σi) dok kind _ _ _ _ _ _ t (fun _ _ _ h => h) (fun _ _ _ h => h.2) HT
    · rintro s _ ⟨d, r, rfl, HP, rfl⟩
      have Hct_x := wrNpcCtrl (imgS σi) (ctrlOkSW T satp0) (textAtS σi T) Hsp (ow d) ot _ Hct_pc
      have How' := How d r HP
      refine ⟨?_, ?_, d, r, rfl, HP, ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [wrNpcOther _ _ _ _ (by decide) (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hsp.sptHart _ Hct_a
      · rw [wrNpcOther _ _ _ _ (by decide) (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide), RegFile.set_same]
      · unfold tfinal
        cases bb
        · exact Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x
        · exact Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            (Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x)
      · rw [tfinalPC, wrNpcNextPC]
        cases ot with
        | none => exact Hnpc_pc
        | some tg => rfl
      · intro r1 Hr
        rw [tfinalGpr, wrNpcGpr _ _ _ _ Hr How']
        exact gprPostAgree _ _ _ _ Hgag Hr
      · have Hx : (wrOpt (ow d) (npcOpt ot ((t.setReg .minstret_increment bb).setReg .nextPC
            (BitVec.addInt pc (incr is_rvc))))).regs .tlb = rs .tlb := by
          rw [wrNpcOther _ _ _ _ (by decide) (by decide)]; exact Htlb_pc
        unfold tfinal
        cases bb
        · simp only [ExecSt.setReg_regs, Bool.false_eq_true, ↓reduceIte]
          rw [RegFile.set_other _ _ _ _ (by decide)]
          exact Hx
        · simp only [ExecSt.setReg_regs, ↓reduceIte]
          rw [RegFile.set_other _ _ _ _ (by decide), RegFile.set_other _ _ _ _ (by decide)]
          exact Hx
  · rintro s' t' ⟨d, r, rfl, HP, HG⟩
    cases tick with
    | false => exact ⟨d, r, rfl, HP, HG⟩
    | true =>
      refine CertMono (imgS σi) dok kind _ _ _ _ _ _ t' (fun _ _ _ h => h) ?_
        (CertNrd (imgS σi) dok kind _ _ d b r t' (sptTickFrame (imgS σi) t') nrdTickClock)
      rintro _ _ t'' ⟨rfl, Hf⟩
      obtain ⟨⟨Hc, HG2, HG3⟩, Htl⟩ := HG
      obtain ⟨Hk1, Hk2⟩ := tickFrameKeep t' t'' Hf
      refine ⟨d, r, rfl, HP, ⟨tickFrameCtrlSW T satp0 t' t'' Hf Hc, Hk1.trans HG2,
        fun r1 Hr => (Hk2 r1).trans (HG3 r1 Hr)⟩, ?_⟩
      rw [Hf .tlb (by decide) (by decide) (by decide)]
      exact Htl

/-- Rocq `CertB_of_CertC`: register-only / control instructions — an SC `exec` fact (`CertC`)
of an `rfF` execute is a `CertB` consuming nothing. -/
theorem CertBOfCertC (dok : Int → Nat → Prop) (kind : Dkind) (rs : RegFile) (pc : BitVec 64)
    (is_rvc : Bool) (ins : instruction) (ot : Option (BitVec 64))
    (ow : Option (BitVec 5 × BitVec 64)) (d0 : Cdata) (r0 : Bool) :
    rfF (execute ins) → CertC (ctrlOkSW T satp0) rs pc is_rvc ins ot ow →
    CertB σi T satp0 dok kind rs pc is_rvc ins 0 ot (fun _ => ow) d0 r0
      (fun d r => d = d0 ∧ r = r0) := by
  intro Hrf Hc tpc Hct HPC Hn Hg _ b
  have HE := EvAOfRfF (imgS σi) _ Hrf tpc _ _ (Hc tpc Hct HPC Hn Hg)
  rw [Nat.zero_add]
  refine CertMono (imgS σi) dok kind _ _ _ _ _ _ tpc (fun _ _ _ h => h) ?_
    (CertNrd (imgS σi) dok kind _ _ d0 b r0 tpc HE (nrdOfRfF _ Hrf))
  rintro s x t' ⟨rfl, rfl, rfl⟩
  exact ⟨rfl, d0, r0, rfl, ⟨rfl, rfl⟩, rfl⟩

end spineB

end Weak
