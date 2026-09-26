/-
**Proof of sh's `pipecmd`** (Rocq `UkShPipeCmd.wp_kshp_pipecmd`, pinned
`1900b8a43`).

    0x260..0x26c  the six-word prologue (ra, s0, s1, s2, s3 spilled)
    0x26e  mv s2,a0 ; 0x270  mv s3,a1            -- left, right
    0x272..0x27e  the allocation (`UshAlloc.ush_alloc_core`, 24 bytes)
    0x282  li a5,3 ; 0x284  sw a5,0(s1)          -- cmd->type = PIPE
    0x286  sd s2,8(s1) ; 0x28a  sd s3,16(s1)
    0x28e  mv a0,s1
    0x290..0x29c  the epilogue

Deviations from Rocq: as in `SpecShPipecmd`; the allocation run is the
shared `ush_alloc_core`.
-/
import Xv6.SpecShPipecmd
import Xv6.UshAlloc

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open LeanRV64D LeanRV64D.Functions
open Std (ExtTreeSet)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CtokG GF] [SG : UexecSG GF] [PS : UprogSG GF]
  [GhostMapG GF Nat (BitVec 8) RegMapF] [GhostVarG GF Nat] [GhostMapG GF (Option Nat) UfdCell UfdMapF]
  [GhostVarG GF (ExtTreeSet GName compare)] [GhostVarG GF Int]

/-- **Rocq `wp_kshp_pipecmd`**. -/
theorem wp_shPipecmd (UL : UK_LEAVES) (MS : USH_MEMSET) (N : UkNames GF) (h : CPU) (m : RegMap) (pl pr : Nat)
    (Sub : IProp GF) (n : Nat) (UM UM' Pex : IProp GF) (hM : ushmMallocTyLe (hlc := hlc) N 168 UM UM')
    (ha0 : m.get 10#5 = BitVec.ofNat 64 pl) (ha1 : m.get 11#5 = BitVec.ofNat 64 pr) :
    ⊢ ushCode N.t -∗ UM -∗ □ (Pex -∗ N.pay (-1)) -∗ Pex -∗ Sub -∗
      urun (hlc := hlc) N h m (BitVec.ofNat 64 User.Sh.Sym.«pipecmd») (6 + (10 + n)) -∗
      (∀ (h' : CPU) (m' : RegMap) (t : Nat), ⌜ucalleeSaved m m'⌝ -∗ ⌜m'.get 10#5 = BitVec.ofNat 64 t⌝ -∗
        ⌜0 < t ∧ t % 16 = 0 ∧ t + 24 < 2 ^ 38⌝ -∗ ushPipeNode N t pl pr -∗ Sub -∗ UM' -∗ Pex -∗
        urun (hlc := hlc) N h' m' (retPc (m.get 1#5)) (6 + (10 + n)) -∗ wpLoop h') -∗
      wpLoop h := by
  rw [show User.Sh.Sym.«pipecmd» = 0x260 from rfl]
  iintro #Hc HM #Hpx Hpay HSub Hrun Hk
  -- the prologue
  iapply ush_frame_pro UL N 6 [1#5, 8#5, 9#5, 18#5, 19#5] 1 0x260 0x26e (ushI_260 N.t)
    ⟨ushI_262 N.t, ushI_264 N.t, ushI_266 N.t, ushI_268 N.t, ushI_26a N.t, trivial⟩ (ushI_26c N.t) h m (10 + n)
    $$ Hc Hrun
  iintro %hst Hsv Hloc %h1 Hrun
  obtain ⟨hal, hroom⟩ := hst
  simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil]
  let sp0 := m.get spIdx
  have hroom' : 8 * (6 + (10 + n)) ≤ sp0.toNat := hroom
  let m1 := ukWr (ukWr m spIdx (sp0 + BitVec.ofInt 64 (-((8 * 6 : Nat) : Int)))) 8#5 sp0
  -- 0x26e  mv s2,a0 ; 0x270  mv s3,a1
  iapply ushS_mv UL N (ushI_26e N.t) 0x270 h1 m1 (10 + n) (BitVec.ofNat 64 pl)
    (by show (ukWr (ukWr m _ _) _ _).get _ = _; ureg; exact ha0) $$ Hc Hrun
  iintro %h2 Hrun
  iapply ushS_mv UL N (ushI_270 N.t) 0x272 h2 _ (10 + n) (BitVec.ofNat 64 pr)
    (by show (ukWr (ukWr (ukWr m _ _) _ _) _ _).get _ = _; ureg; exact ha1) $$ Hc Hrun
  iintro %h3 Hrun
  let mb := ukWr (ukWr m1 18#5 (BitVec.ofNat 64 pl)) 19#5 (BitVec.ofNat 64 pr)
  -- the allocation
  iapply ush_alloc_core UL MS N 0x272 0x274 0x278 0x27a 0x27c 0x27e 0x282 24 (ushI_272 N.t) (ushI_274 N.t)
    (ushI_278 N.t) (ushI_27a N.t) (ushI_27c N.t) (ushI_27e N.t) h3 mb n UM UM' Pex hM $$ Hc HM Hpx Hpay Hrun
  iintro %h7 %m7 %p %hk7 %hs1 %hpb Hz HM' Hpay Hrun
  obtain ⟨hp0, hp16, hp38⟩ := hpb
  have hv : ∀ r v, r ≠ 9#5 → mb.get r = v → ucalleeSavedIdx r = true → m7.get r = v := by
    intro r v h9 he hr; rw [hk7 r hr h9, he]
  have h7_18 : m7.get 18#5 = BitVec.ofNat 64 pl := hv _ _ (by decide) (by show (ukWr _ _ _).get _ = _; ureg) rfl
  have h7_19 : m7.get 19#5 = BitVec.ofNat 64 pr := hv _ _ (by decide) (by show (ukWr _ _ _).get _ = _; ureg) rfl
  have h7sp : m7.get spIdx = sp0 + BitVec.ofInt 64 (-((8 * 6 : Nat) : Int)) :=
    hv _ _ (by decide) (by show (ukWr _ _ _).get _ = _; ureg) rfl
  -- 0x282  li a5,3
  iapply ushS_li UL N (ushI_282 N.t) 0x284 h7 m7 (10 + n) 3 $$ Hc Hrun
  iintro %h8 Hrun
  let m8 := ukWr m7 15#5 (BitVec.ofNat 64 3)
  have g : ∀ r, r ≠ 15#5 → m8.get r = m7.get r := fun r hr => ukWr_get_other _ _ _ _ hr
  have hp64 : p < 2 ^ 64 := by omega
  -- the node's 24 bytes: type, pad, left, right
  icases ush_peel0 N.d p 4 20 $$ Hz with ⟨Ht, Hz⟩
  icases ush_peel0 N.d (p + 4) 4 16 $$ Hz with ⟨Hpad, Hz⟩
  icases ush_peel0 N.d (p + 4 + 4) 8 8 $$ Hz with ⟨Hc8, Hc16⟩
  rw [show p + 4 + 4 = p + 8 by omega, show p + 8 + 8 = p + 16 by omega]
  -- 0x284  sw a5,0(s1)
  iapply ushS_store UL N (k := 4) (ushI_284 N.t) 0x286 h8 m8 (10 + n) p (0#32) (Or.inr (Or.inr (Or.inl rfl)))
    (by rw [g _ (by decide), hs1]; exact ush_fld p 0 _ rfl hp64) (by omega) $$ Hc [Ht] Hrun
  · iapply ush_ubytes_ext $$ Ht; intro j _; exact (ush_nthByte32_zero j).symm
  iintro Ht %h9 Hrun
  -- 0x286  sd s2,8(s1) ; 0x28a  sd s3,16(s1)
  ihave Hc8 := ush_zero_word N.d _ $$ Hc8
  iapply ushS_sd UL N (ushI_286 N.t) 0x28a h9 m8 (10 + n) (p + 8) 0#64
    (by rw [g _ (by decide), hs1]; exact ush_fld p 8 _ rfl hp64) (by omega) $$ Hc Hc8 Hrun
  iintro Hc8 %h10 Hrun
  ihave Hc16 := ush_zero_word N.d _ $$ Hc16
  iapply ushS_sd UL N (ushI_28a N.t) 0x28e h10 m8 (10 + n) (p + 16) 0#64
    (by rw [g _ (by decide), hs1]; exact ush_fld p 16 _ rfl hp64) (by omega) $$ Hc Hc16 Hrun
  iintro Hc16 %h11 Hrun
  -- 0x28e  mv a0,s1
  iapply ushS_mv UL N (ushI_28e N.t) 0x290 h11 m8 (10 + n) (BitVec.ofNat 64 p) (by rw [g _ (by decide), hs1])
    $$ Hc Hrun
  iintro %h12 Hrun
  let m12 := ukWr m8 10#5 (BitVec.ofNat 64 p)
  have g12 : ∀ r, r ≠ 10#5 → r ≠ 15#5 → m12.get r = m7.get r := fun r h10 h15 => by
    rw [ukWr_get_other _ _ _ _ h10, g r h15]
  -- the epilogue
  iapply ush_frame_epi UL N 6 [1#5, 8#5, 9#5, 18#5, 19#5] 1 0x290
    [m.get 1#5, m.get 8#5, m.get 9#5, m.get 18#5, m.get 19#5]
    ⟨ushI_290 N.t, ushI_292 N.t, ushI_294 N.t, ushI_296 N.t, ushI_298 N.t, trivial⟩ (ushI_29a N.t) (ushI_29c N.t)
    sp0 h12 m12 (10 + n) (by rw [g12 _ (by decide) (by decide)]; exact h7sp) hal (by omega) rfl
    $$ Hc Hsv Hloc Hrun
  iintro %h13 Hrun
  have hvs : [m.get 1#5, m.get 8#5, m.get 9#5, m.get 18#5, m.get 19#5] = [1#5, 8#5, 9#5, 18#5, 19#5].map m.get := rfl
  rw [hvs, ush_ret_ra m12 m _ (by simp)]
  iapply Hk $$ %h13 %_ %p [] [] %⟨hp0, hp16, hp38⟩ [Ht Hpad Hc8 Hc16] HSub HM' Hpay Hrun
  · ipureintro
    apply ush_cs_epi m m12 _ sp0 rfl
    intro r hr hsp hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hmem
    obtain ⟨h1, h8, h9, h18, h19⟩ := hmem
    rw [g12 r (ucs_ne r 10#5 hr (by decide)) (ucs_ne r 15#5 hr (by decide)), hk7 r hr h9]
    show (ukWr (ukWr (ukWr (ukWr m _ _) _ _) _ _) _ _).get r = _
    rw [ukWr_get_other _ _ _ _ h19, ukWr_get_other _ _ _ _ h18, ukWr_get_other _ _ _ _ h8,
      ukWr_get_other _ _ _ _ hsp]
  · ipureintro
    rw [ukWr_get_other _ _ _ _ (by decide), ushWrs_get_nmem _ _ _ _ (by decide)]
    exact ukWr_get_same _ _ _ (by decide)
  · unfold ushPipeNode
    isplitr; · ipureintro; exact hp0
    isplitr; · ipureintro; omega
    isplitr; · ipureintro; omega
    isplitl [Ht Hpad]
    · isplitl [Ht]
      · iapply ush_ubytes_ext $$ Ht
        intro j _
        show nthByte (n := 8) ((ukWr m7 15#5 _).get 15#5) j = _
        rw [ukWr_get_same _ _ _ (by decide), show BitVec.ofInt 32 3 = BitVec.ofNat 32 3 by decide]
        exact ush_nthByte_64_32 3 j (by decide)
      · iexists _; iexact Hpad
    isplitl [Hc8]; · rw [g _ (by decide), h7_18]; iexact Hc8
    · rw [g _ (by decide), h7_19]; iexact Hc16

/-- **sh's `pipecmd` holds** (at the engine `UL` and memset `MS`). -/
theorem shPipecmd_holds (UL : UK_LEAVES) (MS : USH_MEMSET) : SH_PIPECMD :=
  ⟨fun N h m pl pr Sub n UM UM' Pex hM ha0 ha1 => wp_shPipecmd UL MS N h m pl pr Sub n UM UM' Pex hM ha0 ha1⟩

end

end Xv6
