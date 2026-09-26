/-
**Proof of sh's `redircmd`** (Rocq `UkShRedirCmd.wp_kshp_redircmd_n`, pinned
`1900b8a43`).

    0x200..0x212  the eight-word prologue (ra, s0, s1..s6 spilled)
    0x214..0x21c  s2..s6 := subcmd, file, efile, mode, fd
    0x21e..0x22e  the allocation (`UshAlloc.ush_alloc_core`, 40 bytes)
    0x232  li a5,2 ; 0x234  sw a5,0(s1)            -- cmd->type = REDIR
    0x236  sd s2,8(s1) ; 0x23a  sd s3,16(s1) ; 0x23e  sd s4,24(s1)
    0x242  sw s5,32(s1) ; 0x246  sw s6,36(s1)
    0x24a  mv a0,s1
    0x24c..0x25e  the epilogue

Deviations from Rocq: as in `SpecShRedircmd`; the allocation run is the
shared `ush_alloc_core`.
-/
import Xv6.SpecShRedircmd
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

/-- **Rocq `wp_kshp_redircmd_n`**. -/
theorem wp_shRedircmd (UL : UK_LEAVES) (MS : USH_MEMSET) (N : UkNames GF) (h : CPU) (m : RegMap) (s0 sub : Nat)
    (mode fd : Int) (Sub : IProp GF) (q eq n : Nat) (UM UM' Pex : IProp GF) (hM : ushmMallocTyLe (hlc := hlc) N 168 UM UM')
    (ha0 : m.get 10#5 = BitVec.ofNat 64 sub) (ha1 : m.get 11#5 = BitVec.ofNat 64 (s0 + q))
    (ha2 : m.get 12#5 = BitVec.ofNat 64 (s0 + eq)) (ha3 : m.get 13#5 = BitVec.ofInt 64 mode)
    (ha4 : m.get 14#5 = BitVec.ofInt 64 fd) (hm0 : 0 ≤ mode) (hm1 : mode < 2 ^ 31) (hf0 : 0 ≤ fd) (hf1 : fd < 2 ^ 31) :
    ⊢ ushCode N.t -∗ UM -∗ □ (Pex -∗ N.pay (-1)) -∗ Pex -∗ Sub -∗
      urun (hlc := hlc) N h m (BitVec.ofNat 64 User.Sh.Sym.«redircmd») (8 + (10 + n)) -∗
      (∀ (h' : CPU) (m' : RegMap) (p : Nat), ⌜ucalleeSaved m m'⌝ -∗ ⌜m'.get 10#5 = BitVec.ofNat 64 p⌝ -∗
        ⌜0 < p ∧ p % 16 = 0 ∧ p + 40 < 2 ^ 38⌝ -∗ ushRedirNode N s0 p sub q eq mode fd -∗ Sub -∗ UM' -∗ Pex -∗
        urun (hlc := hlc) N h' m' (retPc (m.get 1#5)) (8 + (10 + n)) -∗ wpLoop h') -∗
      wpLoop h := by
  rw [show User.Sh.Sym.«redircmd» = 0x200 from rfl]
  iintro #Hc HM #Hpx Hpay HSub Hrun Hk
  -- the prologue
  iapply ush_frame_pro UL N 8 [1#5, 8#5, 9#5, 18#5, 19#5, 20#5, 21#5, 22#5] 0 0x200 0x214 (ushI_200 N.t)
    ⟨ushI_202 N.t, ushI_204 N.t, ushI_206 N.t, ushI_208 N.t, ushI_20a N.t, ushI_20c N.t, ushI_20e N.t,
      ushI_210 N.t, trivial⟩ (ushI_212 N.t) h m (10 + n) $$ Hc Hrun
  iintro %hst Hsv Hloc %h1 Hrun
  obtain ⟨hal, hroom⟩ := hst
  simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil]
  let sp0 := m.get spIdx
  have hroom' : 8 * (8 + (10 + n)) ≤ sp0.toNat := hroom
  let m1 := ukWr (ukWr m spIdx (sp0 + BitVec.ofInt 64 (-((8 * 8 : Nat) : Int)))) 8#5 sp0
  -- 0x214..0x21c  the five moves
  iapply ushS_mv UL N (ushI_214 N.t) 0x216 h1 m1 (10 + n) (BitVec.ofNat 64 sub)
    (by show (ukWr (ukWr m _ _) _ _).get _ = _; ureg; exact ha0) $$ Hc Hrun
  iintro %h2 Hrun
  iapply ushS_mv UL N (ushI_216 N.t) 0x218 h2 _ (10 + n) (BitVec.ofNat 64 (s0 + q))
    (by show (ukWr (ukWr (ukWr m _ _) _ _) _ _).get _ = _; ureg; exact ha1) $$ Hc Hrun
  iintro %h3 Hrun
  iapply ushS_mv UL N (ushI_218 N.t) 0x21a h3 _ (10 + n) (BitVec.ofNat 64 (s0 + eq))
    (by show (ukWr (ukWr (ukWr (ukWr m _ _) _ _) _ _) _ _).get _ = _; ureg; exact ha2) $$ Hc Hrun
  iintro %h4 Hrun
  iapply ushS_mv UL N (ushI_21a N.t) 0x21c h4 _ (10 + n) (BitVec.ofInt 64 mode)
    (by show (ukWr (ukWr (ukWr (ukWr (ukWr m _ _) _ _) _ _) _ _) _ _).get _ = _; ureg; exact ha3) $$ Hc Hrun
  iintro %h5 Hrun
  iapply ushS_mv UL N (ushI_21c N.t) 0x21e h5 _ (10 + n) (BitVec.ofInt 64 fd)
    (by show (ukWr (ukWr (ukWr (ukWr (ukWr (ukWr m _ _) _ _) _ _) _ _) _ _) _ _).get _ = _; ureg; exact ha4)
    $$ Hc Hrun
  iintro %h6 Hrun
  let mb := ukWr (ukWr (ukWr (ukWr (ukWr m1 18#5 (BitVec.ofNat 64 sub)) 19#5 (BitVec.ofNat 64 (s0 + q))) 20#5
    (BitVec.ofNat 64 (s0 + eq))) 21#5 (BitVec.ofInt 64 mode)) 22#5 (BitVec.ofInt 64 fd)
  -- the allocation
  iapply ush_alloc_core UL MS N 0x21e 0x222 0x226 0x228 0x22c 0x22e 0x232 40 (ushI_21e N.t) (ushI_222 N.t)
    (ushI_226 N.t) (ushI_228 N.t) (ushI_22c N.t) (ushI_22e N.t) h6 mb n UM UM' Pex hM $$ Hc HM Hpx Hpay Hrun
  iintro %h7 %m7 %p %hk7 %hs1 %hpb Hz HM' Hpay Hrun
  obtain ⟨hp0, hp16, hp38⟩ := hpb
  have hk7' : ∀ r, ucalleeSavedIdx r = true → r ≠ 9#5 → r ≠ 8#5 → r ≠ spIdx → r ≠ 18#5 → r ≠ 19#5 →
      r ≠ 20#5 → r ≠ 21#5 → r ≠ 22#5 → m7.get r = m.get r := by
    intro r hr h9 h8 hsp h18 h19 h20 h21 h22
    rw [hk7 r hr h9]
    show (ukWr (ukWr (ukWr (ukWr (ukWr (ukWr (ukWr m _ _) _ _) _ _) _ _) _ _) _ _) _ _).get r = _
    rw [ukWr_get_other _ _ _ _ h22, ukWr_get_other _ _ _ _ h21, ukWr_get_other _ _ _ _ h20,
      ukWr_get_other _ _ _ _ h19, ukWr_get_other _ _ _ _ h18, ukWr_get_other _ _ _ _ h8, ukWr_get_other _ _ _ _ hsp]
  have hv : ∀ r v, r ≠ 9#5 → mb.get r = v → ucalleeSavedIdx r = true → m7.get r = v := by
    intro r v h9 he hr; rw [hk7 r hr h9, he]
  have h7_18 : m7.get 18#5 = BitVec.ofNat 64 sub := hv _ _ (by decide) (by show (ukWr _ _ _).get _ = _; ureg) rfl
  have h7_19 : m7.get 19#5 = BitVec.ofNat 64 (s0 + q) := hv _ _ (by decide) (by show (ukWr _ _ _).get _ = _; ureg) rfl
  have h7_20 : m7.get 20#5 = BitVec.ofNat 64 (s0 + eq) := hv _ _ (by decide)
    (by show (ukWr _ _ _).get _ = _; ureg) rfl
  have h7_21 : m7.get 21#5 = BitVec.ofInt 64 mode := hv _ _ (by decide) (by show (ukWr _ _ _).get _ = _; ureg) rfl
  have h7_22 : m7.get 22#5 = BitVec.ofInt 64 fd := hv _ _ (by decide) (by show (ukWr _ _ _).get _ = _; ureg) rfl
  have h7sp : m7.get spIdx = sp0 + BitVec.ofInt 64 (-((8 * 8 : Nat) : Int)) :=
    hv _ _ (by decide) (by show (ukWr _ _ _).get _ = _; ureg) rfl
  -- 0x232  li a5,2
  iapply ushS_li UL N (ushI_232 N.t) 0x234 h7 m7 (10 + n) 2 $$ Hc Hrun
  iintro %h8 Hrun
  let m8 := ukWr m7 15#5 (BitVec.ofNat 64 2)
  have g : ∀ r, r ≠ 15#5 → m8.get r = m7.get r := fun r hr => ukWr_get_other _ _ _ _ hr
  have hp64 : p < 2 ^ 64 := by omega
  -- the node's 40 bytes: type, pad, cmd, file, efile, mode, fd
  icases ush_peel0 N.d p 4 36 $$ Hz with ⟨Ht, Hz⟩
  icases ush_peel0 N.d (p + 4) 4 32 $$ Hz with ⟨Hpad, Hz⟩
  icases ush_peel0 N.d (p + 4 + 4) 8 24 $$ Hz with ⟨Hc8, Hz⟩
  icases ush_peel0 N.d (p + 4 + 4 + 8) 8 16 $$ Hz with ⟨Hc16, Hz⟩
  icases ush_peel0 N.d (p + 4 + 4 + 8 + 8) 8 8 $$ Hz with ⟨Hc24, Hz⟩
  icases ush_peel0 N.d (p + 4 + 4 + 8 + 8 + 8) 4 4 $$ Hz with ⟨Hc32, Hc36⟩
  rw [show p + 4 + 4 = p + 8 by omega, show p + 8 + 8 = p + 16 by omega, show p + 16 + 8 = p + 24 by omega,
    show p + 24 + 8 = p + 32 by omega, show p + 32 + 4 = p + 36 by omega]
  -- 0x234  sw a5,0(s1)
  iapply ushS_store UL N (k := 4) (ushI_234 N.t) 0x236 h8 m8 (10 + n) p (0#32) (Or.inr (Or.inr (Or.inl rfl)))
    (by rw [g _ (by decide), hs1]; exact ush_fld p 0 _ rfl hp64) (by omega) $$ Hc [Ht] Hrun
  · iapply ush_ubytes_ext $$ Ht; intro j _; exact (ush_nthByte32_zero j).symm
  iintro Ht %h9 Hrun
  -- 0x236  sd s2,8(s1) ; 0x23a  sd s3,16(s1) ; 0x23e  sd s4,24(s1)
  ihave Hc8 := ush_zero_word N.d _ $$ Hc8
  iapply ushS_sd UL N (ushI_236 N.t) 0x23a h9 m8 (10 + n) (p + 8) 0#64
    (by rw [g _ (by decide), hs1]; exact ush_fld p 8 _ rfl hp64) (by omega) $$ Hc Hc8 Hrun
  iintro Hc8 %h10 Hrun
  ihave Hc16 := ush_zero_word N.d _ $$ Hc16
  iapply ushS_sd UL N (ushI_23a N.t) 0x23e h10 m8 (10 + n) (p + 16) 0#64
    (by rw [g _ (by decide), hs1]; exact ush_fld p 16 _ rfl hp64) (by omega) $$ Hc Hc16 Hrun
  iintro Hc16 %h11 Hrun
  ihave Hc24 := ush_zero_word N.d _ $$ Hc24
  iapply ushS_sd UL N (ushI_23e N.t) 0x242 h11 m8 (10 + n) (p + 24) 0#64
    (by rw [g _ (by decide), hs1]; exact ush_fld p 24 _ rfl hp64) (by omega) $$ Hc Hc24 Hrun
  iintro Hc24 %h12 Hrun
  -- 0x242  sw s5,32(s1) ; 0x246  sw s6,36(s1)
  iapply ushS_store UL N (k := 4) (ushI_242 N.t) 0x246 h12 m8 (10 + n) (p + 32) (0#32)
    (Or.inr (Or.inr (Or.inl rfl))) (by rw [g _ (by decide), hs1]; exact ush_fld p 32 _ rfl hp64) (by omega)
    $$ Hc [Hc32] Hrun
  · iapply ush_ubytes_ext $$ Hc32; intro j _; exact (ush_nthByte32_zero j).symm
  iintro Hc32 %h13 Hrun
  iapply ushS_store UL N (k := 4) (ushI_246 N.t) 0x24a h13 m8 (10 + n) (p + 36) (0#32)
    (Or.inr (Or.inr (Or.inl rfl))) (by rw [g _ (by decide), hs1]; exact ush_fld p 36 _ rfl hp64) (by omega)
    $$ Hc [Hc36] Hrun
  · iapply ush_ubytes_ext $$ Hc36; intro j _; exact (ush_nthByte32_zero j).symm
  iintro Hc36 %h14 Hrun
  -- 0x24a  mv a0,s1
  iapply ushS_mv UL N (ushI_24a N.t) 0x24c h14 m8 (10 + n) (BitVec.ofNat 64 p) (by rw [g _ (by decide), hs1])
    $$ Hc Hrun
  iintro %h15 Hrun
  let m15 := ukWr m8 10#5 (BitVec.ofNat 64 p)
  have g15 : ∀ r, r ≠ 10#5 → r ≠ 15#5 → m15.get r = m7.get r := fun r h10 h15 => by
    rw [ukWr_get_other _ _ _ _ h10, g r h15]
  -- the epilogue
  iapply ush_frame_epi UL N 8 [1#5, 8#5, 9#5, 18#5, 19#5, 20#5, 21#5, 22#5] 0 0x24c
    [m.get 1#5, m.get 8#5, m.get 9#5, m.get 18#5, m.get 19#5, m.get 20#5, m.get 21#5, m.get 22#5]
    ⟨ushI_24c N.t, ushI_24e N.t, ushI_250 N.t, ushI_252 N.t, ushI_254 N.t, ushI_256 N.t, ushI_258 N.t,
      ushI_25a N.t, trivial⟩ (ushI_25c N.t) (ushI_25e N.t) sp0 h15 m15 (10 + n)
    (by rw [g15 _ (by decide) (by decide)]; exact h7sp) hal (by omega) rfl $$ Hc Hsv Hloc Hrun
  iintro %h16 Hrun
  have hvs : [m.get 1#5, m.get 8#5, m.get 9#5, m.get 18#5, m.get 19#5, m.get 20#5, m.get 21#5, m.get 22#5] =
      [1#5, 8#5, 9#5, 18#5, 19#5, 20#5, 21#5, 22#5].map m.get := rfl
  rw [hvs, ush_ret_ra m15 m _ (by simp)]
  iapply Hk $$ %h16 %_ %p [] [] %⟨hp0, hp16, hp38⟩ [Ht Hpad Hc8 Hc16 Hc24 Hc32 Hc36] HSub HM' Hpay Hrun
  · ipureintro
    apply ush_cs_epi m m15 _ sp0 rfl
    intro r hr hsp hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hmem
    obtain ⟨h1, h8, h9, h18, h19, h20, h21, h22⟩ := hmem
    rw [g15 r (ucs_ne r 10#5 hr (by decide)) (ucs_ne r 15#5 hr (by decide))]
    exact hk7' r hr h9 h8 hsp h18 h19 h20 h21 h22
  · ipureintro
    rw [ukWr_get_other _ _ _ _ (by decide), ushWrs_get_nmem _ _ _ _ (by decide)]
    exact ukWr_get_same _ _ _ (by decide)
  · unfold ushRedirNode
    isplitr; · ipureintro; exact hp0
    isplitr; · ipureintro; omega
    isplitr; · ipureintro; omega
    isplitl [Ht Hpad]
    · isplitl [Ht]
      · iapply ush_ubytes_ext $$ Ht
        intro j _
        show nthByte (n := 8) ((ukWr m7 15#5 _).get 15#5) j = _
        rw [ukWr_get_same _ _ _ (by decide), show BitVec.ofInt 32 2 = BitVec.ofNat 32 2 by decide]
        exact ush_nthByte_64_32 2 j (by decide)
      · iexists _; iexact Hpad
    isplitl [Hc8]; · rw [g _ (by decide), h7_18]; iexact Hc8
    isplitl [Hc16]; · rw [g _ (by decide), h7_19]; iexact Hc16
    isplitl [Hc24]; · rw [g _ (by decide), h7_20]; iexact Hc24
    isplitl [Hc32]
    · iapply ush_ubytes_ext $$ Hc32
      intro j _; rw [g _ (by decide), h7_21]; exact ush_nthByte_64_32i mode j hm0 hm1
    · iapply ush_ubytes_ext $$ Hc36
      intro j _; rw [g _ (by decide), h7_22]; exact ush_nthByte_64_32i fd j hf0 hf1

/-- **sh's `redircmd` holds** (at the engine `UL` and memset `MS`). -/
theorem shRedircmd_holds (UL : UK_LEAVES) (MS : USH_MEMSET) : SH_REDIRCMD :=
  ⟨fun N h m s0 sub mode fd Sub q eq n UM UM' Pex hM ha0 ha1 ha2 ha3 ha4 hm0 hm1 hf0 hf1 =>
    wp_shRedircmd UL MS N h m s0 sub mode fd Sub q eq n UM UM' Pex hM ha0 ha1 ha2 ha3 ha4 hm0 hm1 hf0 hf1⟩

end

end Xv6
