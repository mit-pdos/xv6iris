/-
Weak: **the weak absorption theorem** (batch-6 P4, §5 of `iris/WeakKpt.v`).

Rocq: `iris/WeakKpt.v` @ xxvzwolszwmp, §5 (split from `Weak/WeakKpt.lean`, which holds §§1–4
and the full Rocq header, the deviations and the name map; the split is the protocol's
length rule: the single file exceeded ~1500 lines).

`wtlbResPtTranslateAddrAt` -- the `tlb_res_pt_translateAddr_at` mirror: keyed on the caller's
`kmapAt` claim it opens `wkptN` mask-carrying, runs `wptreeTranslateAddrEffCases` at the
coherent flat projection `wflatSt σ`, and returns the exact translation fact and trace, the
racy-leaf collapse facts, the pointer pins, the leaf slot's `nvFree`, and the re-closed residue
and invariant -- the ghost state unchanged on the quiet arms and at the appended log on the
write-back arm.

**Deviations from Rocq.**  As `Weak/WeakKpt.lean` deviations 2, 4, 5, 6, 7.  In addition:
1. the collapse conjunct quantifies over `rak.akIfetch = false` reads (WeakKpt deviation 2);
2. the leaf element's write-back message is spelled with the leaf value as a variant of the
   canonical leaf (`pteSetAD e a1 d1`, equal to Rocq's `pte_set_ad lw a1 d1` by
   `pteSetAD_pteSetAD`); the conclusion's `lw'` is that value.
3. Lean-only helpers (file-qualified): `WeakKpt.ofNatToNat27`, `WeakKpt.bigSepMVpnDelete`,
   `WeakKpt.bigSepMVpnInsert`, `WeakKpt.wlat8StoreExcl`.

**Rocq → Lean name map.**  `wslot_mem_of_flat` `wslotMemOfFlat`; `wvpn_res_maps_mono`
`wvpnResMapsMono`; `wtlb_res_pt_translateAddr_at` `wtlbResPtTranslateAddrAt`.

**Dropped:** nothing (the 3 Rocq lemmas of §5; the `Print Assumptions` block is not a
declaration).
-/
import Weak.WeakKpt

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 5. THE ABSORPTION THEOREM -/

/-- A slot's `ptSlotMem` at the flat state, from the invariant's stored geometry + the
elements' flat lookups. -/
theorem wslotMemOfFlat (σ : Wmstate) (a : PAddr) (w : BitVec 64) :
    wslotGeom a →
    (∀ j : Nat, j < 8 → wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (nthByte (n := 8) w j)) →
    WeakWalkEff.ptSlotMem (wflatSt σ) a w := by
  rintro ⟨hram, hal⟩ hb
  exact ⟨hb, hram, hal⟩

/-- Lean-only: a 27-bit vpn survives the `Nat` key round trip. -/
theorem WeakKpt.ofNatToNat27 (v : BitVec 27) : BitVec.ofNat 27 v.toNat = v := by
  simp

section WeakKptAbsorb

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF] [WeakKpt.KptGS GF]

/-- Lean-only: the body's `[∗ map]`, focused on one vpn. -/
theorem WeakKpt.bigSepMVpnDelete (Φ : BitVec 27 → BitVec 64 → IProp GF) (M : RegMapF (BitVec 64))
    (vpn : BitVec 27) (e : BitVec 64) (h : get? M vpn.toNat = some e) :
    ([∗map] k ↦ v ∈ M, Φ (BitVec.ofNat 27 k) v) ⊢
      Φ vpn e ∗ [∗map] k ↦ v ∈ delete M vpn.toNat, Φ (BitVec.ofNat 27 k) v := by
  refine (BigSepM.bigSepM_delete (Φ := fun k v => Φ (BitVec.ofNat 27 k) v) h).1.trans ?_
  rw [WeakKpt.ofNatToNat27]

/-- Lean-only: ... and put back. -/
theorem WeakKpt.bigSepMVpnInsert (Φ : BitVec 27 → BitVec 64 → IProp GF) (M : RegMapF (BitVec 64))
    (vpn : BitVec 27) (e : BitVec 64) (h : get? M vpn.toNat = some e) :
    Φ vpn e ∗ ([∗map] k ↦ v ∈ delete M vpn.toNat, Φ (BitVec.ofNat 27 k) v) ⊢
      [∗map] k ↦ v ∈ M, Φ (BitVec.ofNat 27 k) v := by
  refine Entails.trans ?_ (BigSepM.bigSepM_delete (Φ := fun k v => Φ (BitVec.ofNat 27 k) v) h).2
  rw [WeakKpt.ofNatToNat27]

/-- The per-vpn bundle transports along a maps-preserving, base-preserving tree change -- the
frame step for the OTHER vpns at a write-back. -/
theorem wvpnResMapsMono (T_kpt : Nat) (t t2 : PTree) (vpn' : BitVec 27) (e' : BitVec 64) :
    (∀ p2 p1 q0 : BitVec 64, AxPtProt.ptreeMaps t vpn' p2 p1 q0 → AxPtProt.ptreeMaps t2 vpn' p2 p1 q0) →
    t2.base = t.base →
    wvpnRes (GF := GF) T_kpt t vpn' e' ⊢ wvpnRes (GF := GF) T_kpt t2 vpn' e' := by
  intro hmono hb
  have ha2 : AxPtProt.ptAddr2 t2 vpn' = AxPtProt.ptAddr2 t vpn' := by
    unfold AxPtProt.ptAddr2; rw [hb]
  unfold wvpnRes
  rw [ha2]
  iintro ⟨%p2, %p1, %a, %d, %hm, H2, H1, HL⟩
  iexists p2, p1, a, d
  iframe H2 H1 HL
  ipureintro
  exact hmono _ _ _ hm

/-- Lean-only: the write-back arm's element step (`wlat8StorePrim` at the bundle). -/
theorem WeakKpt.wlat8StoreExcl (tid : Option Nat) (σ : Wmstate) (la : PAddr) (ts : Nat) (lw lw' : BitVec 64) :
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢ wlat8 (GF := GF) la (DFrac.own 1) ts lw -∗
      |==> (wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [wwriteMsg tid .WCexcl la 8 lw']) ∗
        wlat8 (GF := GF) la (DFrac.own 1) (σ.wmLog.length + 1) lw') := by
  rw [wlat8Unfold la (DFrac.own 1) ts lw]
  iintro Hi ⟨E0, E1, E2, E3, E4, E5, E6, E7⟩
  iapply (wlat8StorePrim tid .WCexcl σ la lw' ts ts ts ts ts ts ts ts _ _ _ _ _ _ _ _ (by decide))
    $$ Hi E0 E1 E2 E3 E4 E5 E6 E7

/-- THE ABSORPTION THEOREM (Rocq `wtlb_res_pt_translateAddr_at`, deviations 2, 4, 5, 6). -/
theorem wtlbResPtTranslateAddrAt (acc : MemoryAccessType mem_payload) (cpu : CPU) (root : BitVec 44)
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
    execEff (effectivePrivilege acc (σ.wmRegs .mstatus) .Supervisor) (wflatSt σ) =
      some (.Supervisor, wflatSt σ, []) →
    execEff (is_shadow_stack_access acc) (wflatSt σ) = some (false, wflatSt σ, []) →
    σ.wmRegs .pma_regions = bootPMA →
    -- the per-hart receipt's pure shadow: the hart's read floor covers the kvminit horizon
    T_kpt ≤ σ.wmWs.wVrNew →
    kmapAt (hlc := hlc) (WeakKpt.svpnOf va) (kLeaf ppn pc 0#1 0#1) ∗
      regInterp cpu σ.wmRegs ∗
      wlogAuth (GF := GF) σ.wmLog ∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗
      wtlbResPt (hlc := hlc) (GF := GF) cpu root T_kpt ⊢
    |={E}=> ∃ (sg' : ExecSt) (es : List Weff) (p2 p1 lw : BitVec 64),
      ⌜execEff (translateAddr (.Virtaddr va) acc) (wflatSt σ) =
        some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', es)⌝ ∗
      ⌜sg'.dev = σ.wmDev⌝ ∗
      ⌜sg'.regs = σ.wmRegs ∨ ∃ tv, sg'.regs = σ.wmRegs.set .tlb tv⌝ ∗
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
      ⌜∀ (rak : AkInfo) (wv : BitVec (8 * 8)), rak.akIfetch = false →
        wadm σ rak (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 wv →
        (∃ a d : BitVec 1, wv = pteSetAD (mkPte ppn pc.flags) a d) ∧ pteAdLe wv lw⌝ ∗
      ⌜∀ j : Nat, j < 8 → nvFree σ.wmLog (WeakInterp.accAddr
        (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) j)⌝ ∗
      regInterp cpu sg'.regs ∗
      wtlbResPt (hlc := hlc) (GF := GF) cpu root T_kpt ∗
      ((⌜sg'.mem = wflatMem σ.wmImg σ.wmLog ∧
          (es = [] ∨
           es = [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 26 18)) 8,
                 .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 17 9)) 8,
                 .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8] ∨
           es = [.WEread ⟨false, true, false⟩
                   (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8])⌝ ∗
        wlogAuth (GF := GF) σ.wmLog ∗ wlatInterp (GF := GF) σ.wmImg σ.wmLog) ∨
       (∃ (lw' : BitVec 64) (kcls : WmClass),
          ⌜update_PTE_Bits lw acc = some lw'⌝ ∗
          ⌜sg'.mem = bmWrite (wflatMem σ.wmImg σ.wmLog)
            (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 lw'⌝ ∗
          ⌜es = [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 26 18)) 8,
                 .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 17 9)) 8,
                 .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8,
                 .WEread ⟨false, true, false⟩
                   (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8,
                 .WEwrite ⟨false, true, false⟩
                   (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 lw'] ∨
            es = [.WEread ⟨false, true, false⟩
                   (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8,
                  .WEwrite ⟨false, true, false⟩
                   (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 lw']⌝ ∗
          wlogAuth (GF := GF) (σ.wmLog ++ [wwriteMsg tid kcls
            (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 lw']) ∗
          wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [wwriteMsg tid kcls
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
  have htm : execEff (translationMode .Supervisor) (wflatSt σ) = some (.Sv39, wflatSt σ, []) :=
    execEffTranslationModeSSv39 satp0 (wflatSt σ) hsxl hsatpv hmode
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
  -- ---- run the dispatch at the flat state ----
  obtain ⟨sg', es, htrans, harm⟩ := wptreeTranslateAddrEffCases acc .Supervisor root va e pa satp0 t tlbvec
    p2 p1 a0 d0 (wflatSt σ) hchk' hval' hcanon hout hvarp hwv2 hwv1 hbase hmaps htlbok hsm2 hsm1 hsm0
    hmisa hmenv hhtif hcp htm heff hss hsatpv hppn hasid htlbv hA' hord' hR' hW' hcov' hpmar hpmaw
  rcases harm with ⟨hsg', hes⟩ | ⟨hsg', hes⟩ | ⟨a1, d1, hupd, hsg', hes⟩
  · -- O1: nothing moved
    have hregs : sg'.regs = σ.wmRegs := by rw [hsg']; rfl
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
    iexists sg', es, p2, p1, (pteSetAD e a0 d0)
    isplitr
    · ipureintro; exact htrans
    isplitr
    · ipureintro; rw [hsg']; rfl
    isplitr
    · ipureintro; exact Or.inl hregs
    isplitr
    · ipureintro; exact ⟨a0, d0, hkv a0 d0⟩
    isplitr
    · ipureintro; exact hslots
    isplitr
    · ipureintro; exact hpin
    isplitr
    · ipureintro; exact hcoll
    isplitr
    · ipureintro; exact hnvfree
    isplitl [Hri]
    · ieval (rewrite [hregs])
      iexact Hri
    isplitl [Hsatp Htlb Hpc Hpa]
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
    ileft
    isplitr
    · ipureintro; exact ⟨by rw [hsg']; rfl, Or.inl hes⟩
    isplitl [Hla]
    · iexact Hla
    · iexact Hi
  · -- O2: TLB fill (walk) or in-place refresh
    have hregs : sg'.regs = σ.wmRegs.set .tlb (vectorUpdate tlbvec (tlb_hash 39 (WeakKpt.svpnOf va))
        (some (uWalkEntry (WeakKpt.svpnOf va) p2 p1 (pteSetAD e a0 d0) 0#16))) := by rw [hsg']; rfl
    have htlbok' := WeakKpt.tlbOkPtFillSelf 0#16 t tlbvec (WeakKpt.svpnOf va) p2 p1 (pteSetAD e a0 d0) hmaps htlbok
    imod reg_update cpu σ.wmRegs .tlb tlbvec (vectorUpdate tlbvec (tlb_hash 39 (WeakKpt.svpnOf va))
      (some (uWalkEntry (WeakKpt.svpnOf va) p2 p1 (pteSetAD e a0 d0) 0#16))) $$ [Hri Htlb] with ⟨Hri, Htlb⟩
    · iframe Hri Htlb
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
    iexists sg', es, p2, p1, (pteSetAD e a0 d0)
    isplitr
    · ipureintro; exact htrans
    isplitr
    · ipureintro; rw [hsg']; rfl
    isplitr
    · ipureintro; exact Or.inr ⟨_, hregs⟩
    isplitr
    · ipureintro; exact ⟨a0, d0, hkv a0 d0⟩
    isplitr
    · ipureintro; exact hslots
    isplitr
    · ipureintro; exact hpin
    isplitr
    · ipureintro; exact hcoll
    isplitr
    · ipureintro; exact hnvfree
    isplitl [Hri]
    · ieval (rewrite [hregs])
      iexact Hri
    isplitl [Hsatp Htlb Hpc Hpa]
    · iapply (wtlbResPtIntro (hlc := hlc) (GF := GF) cpu root T_kpt satp0 _ t hmode hasid hppn htlbok')
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
    · ipureintro; exact ⟨by rw [hsg']; rfl, Or.inr hes⟩
    isplitl [Hla]
    · iexact Hla
    · iexact Hi
  · -- O3: the write-back, absorbed
    have hregs : sg'.regs = σ.wmRegs.set .tlb (vectorUpdate tlbvec (tlb_hash 39 (WeakKpt.svpnOf va))
        (some (uWalkEntry (WeakKpt.svpnOf va) p2 p1 (pteSetAD (pteSetAD e a0 d0) a1 d1) 0#16))) := by
      rw [hsg']; rfl
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
    have htlbok' := WeakKpt.tlbOkPtFillSelf 0#16 _ tlbvec (WeakKpt.svpnOf va) p2 p1 _ hmaps'
      (AxPtProt.tlbOkPtSetLeaf 0#16 t tlbvec (WeakKpt.svpnOf va) p2 p1 (pteSetAD e a0 d0) a1 d1 hmaps
        hv' hl' hn' hp' htlbok)
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
    -- the register update
    imod reg_update cpu σ.wmRegs .tlb tlbvec (vectorUpdate tlbvec (tlb_hash 39 (WeakKpt.svpnOf va))
      (some (uWalkEntry (WeakKpt.svpnOf va) p2 p1 (pteSetAD (pteSetAD e a0 d0) a1 d1) 0#16))) $$ [Hri Htlb]
      with ⟨Hri, Htlb⟩
    · iframe Hri Htlb
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
    iexists sg', es, p2, p1, (pteSetAD e a0 d0)
    isplitr
    · ipureintro; exact htrans
    isplitr
    · ipureintro; rw [hsg']; rfl
    isplitr
    · ipureintro; exact Or.inr ⟨_, hregs⟩
    isplitr
    · ipureintro; exact ⟨a0, d0, hkv a0 d0⟩
    isplitr
    · ipureintro; exact hslots
    isplitr
    · ipureintro; exact hpin
    isplitr
    · ipureintro; exact hcoll
    isplitr
    · ipureintro; exact hnvfree
    isplitl [Hri]
    · ieval (rewrite [hregs])
      iexact Hri
    isplitl [Hsatp Htlb Hpc Hpa]
    · iapply (wtlbResPtIntro (hlc := hlc) (GF := GF) cpu root T_kpt satp0 _
        (AxPtProt.ptreeSetLeaf t (WeakKpt.svpnOf va) (pteSetAD (pteSetAD e a0 d0) a1 d1)) hmode hasid hppn
        htlbok')
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
    iexists (pteSetAD e a1 d1), WmClass.WCexcl
    isplitr
    · ipureintro; exact hupd'
    isplitr
    · ipureintro; rw [← habs, hsg']; rfl
    isplitr
    · ipureintro; rw [← habs]; exact hes
    ieval (rewrite [hla0]) at Hla Hi
    isplitl [Hla]
    · iexact Hla
    · iexact Hi

end WeakKptAbsorb

end Weak
