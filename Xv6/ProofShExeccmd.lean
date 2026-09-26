/-
**Proof of sh's `execcmd`** (Rocq `UkShParseLex.wp_kshp_execcmd`, pinned
`1900b8a43`).

    0x1d2..0x1da  the four-word prologue (ra, s0, s1 spilled)
    0x1dc..0x1ec  li a0,168; jal malloc; mv s1,a0; li a2,168; li a1,0; jal memset
                  (`UshAlloc.ush_alloc_core`: the NULL arm dies in memset)
    0x1f0  li a5,1 ; 0x1f2  sw a5,0(s1)     -- cmd->type = EXEC
    0x1f4  mv a0,s1
    0x1f6..0x1fe  the epilogue

The node's 168 zeroed bytes are the type word (now 1), four bytes of padding
and the two ten-slot vectors, every slot the memset's zero
(`UshNodes.ush_slots_nil0`): `ushExecPre s0 p []`.

Deviations from Rocq: as in `SpecShExeccmd`; the allocation run is the
shared `ush_alloc_core`.
-/
import Xv6.SpecShExeccmd
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

/-- The zeroed node, the type word stored: an EXEC node with no tokens. -/
theorem ush_exec_pre_nil (N : UkNames GF) (s0 p : Nat) (hp : 0 < p) (hp8 : p % 8 = 0) :
    ubytes N.d p 4 (nthByte (n := 4) (BitVec.ofInt 32 (ushpTy (.exec [])))) ∗
      ubytes N.d (p + 4) 164 (fun _ => ubyte0) ⊢ ushExecPre N s0 p [] := by
  iintro ⟨Hty, Hz⟩
  icases ush_peel0 N.d (p + 4) 4 160 $$ Hz with ⟨Hpad, Hz⟩
  icases ush_peel0 N.d (p + 4 + 4) 80 80 $$ Hz with ⟨Ha, He⟩
  rw [show p + 4 + 4 = p + 8 by omega, show p + 8 + 80 = p + 88 by omega]
  unfold ushExecPre ushTypeAt
  isplitr; · ipureintro; simp
  isplitr; · ipureintro; exact hp
  isplitr; · ipureintro; exact hp8
  isplitl [Hty Hpad]
  · iframe Hty; iexists _; iexact Hpad
  isplitl [Ha]
  · iapply ush_slots_nil0 $$ Ha
  · iapply ush_slots_nil0 $$ He

/-- **Rocq `wp_kshp_execcmd`**. -/
theorem wp_shExeccmd (UL : UK_LEAVES) (MS : USH_MEMSET) (N : UkNames GF) (h : CPU) (m : RegMap) (s0 n : Nat)
    (UM UM' Pex : IProp GF) (hM : ushmMallocTyLe (hlc := hlc) N 168 UM UM') :
    ⊢ ushCode N.t -∗ UM -∗ □ (Pex -∗ N.pay (-1)) -∗ Pex -∗
      urun (hlc := hlc) N h m (BitVec.ofNat 64 User.Sh.Sym.«execcmd») (4 + (10 + n)) -∗
      (∀ (h' : CPU) (m' : RegMap) (p : Nat), ⌜ucalleeSaved m m'⌝ -∗ ⌜m'.get 10#5 = BitVec.ofNat 64 p⌝ -∗
        ⌜0 < p ∧ p % 16 = 0 ∧ p + 168 < 2 ^ 38⌝ -∗ ushExecPre N s0 p [] -∗ UM' -∗ Pex -∗
        urun (hlc := hlc) N h' m' (retPc (m.get 1#5)) (4 + (10 + n)) -∗ wpLoop h') -∗
      wpLoop h := by
  rw [show User.Sh.Sym.«execcmd» = 0x1d2 from rfl]
  iintro #Hc HM #Hpx Hpay Hrun Hk
  -- the prologue
  iapply ush_frame_pro UL N 4 [1#5, 8#5, 9#5] 1 0x1d2 0x1dc (ushI_1d2 N.t)
    ⟨ushI_1d4 N.t, ushI_1d6 N.t, ushI_1d8 N.t, trivial⟩ (ushI_1da N.t) h m (10 + n) $$ Hc Hrun
  iintro %hst Hsv Hloc %h1 Hrun
  obtain ⟨hal, hroom⟩ := hst
  simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil]
  let sp0 := m.get spIdx
  have hroom' : 8 * (4 + (10 + n)) ≤ sp0.toNat := hroom
  have hal' : sp0.toNat % 8 = 0 := hal
  let m1 := ukWr (ukWr m spIdx (sp0 + BitVec.ofInt 64 (-((8 * 4 : Nat) : Int)))) 8#5 sp0
  -- the allocation
  iapply ush_alloc_core UL MS N 0x1dc 0x1e0 0x1e4 0x1e6 0x1ea 0x1ec 0x1f0 168 (ushI_1dc N.t) (ushI_1e0 N.t)
    (ushI_1e4 N.t) (ushI_1e6 N.t) (ushI_1ea N.t) (ushI_1ec N.t) h1 m1 n UM UM' Pex hM $$ Hc HM Hpx Hpay Hrun
  iintro %h2 %m2 %p %hk2 %hs1 %hpb Hz HM' Hpay Hrun
  obtain ⟨hp0, hp16, hp38⟩ := hpb
  -- 0x1f0  li a5,1
  iapply ushS_li UL N (ushI_1f0 N.t) 0x1f2 h2 m2 (10 + n) 1 $$ Hc Hrun
  iintro %h3 Hrun
  let m3 := ukWr m2 15#5 (BitVec.ofNat 64 1)
  have h3s1 : m3.get 9#5 = BitVec.ofNat 64 p := by show (ukWr m2 _ _).get _ = _; ureg; exact hs1
  -- 0x1f2  sw a5,0(s1) : cmd->type = EXEC
  icases ush_peel0 N.d p 4 164 $$ Hz with ⟨Ht, Hz⟩
  iapply ushS_store UL N (k := 4) (ushI_1f2 N.t) 0x1f4 h3 m3 (10 + n) p (0#32) (Or.inr (Or.inr (Or.inl rfl)))
    (by rw [h3s1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; rfl) (by omega) $$ Hc [Ht] Hrun
  · iapply ush_ubytes_ext $$ Ht
    intro j _; exact (ush_nthByte32_zero j).symm
  iintro Ht %h4 Hrun
  -- 0x1f4  mv a0,s1
  iapply ushS_mv UL N (ushI_1f4 N.t) 0x1f6 h4 m3 (10 + n) (BitVec.ofNat 64 p) h3s1 $$ Hc Hrun
  iintro %h5 Hrun
  let m5 := ukWr m3 10#5 (BitVec.ofNat 64 p)
  have hk5 : ∀ r, ucalleeSavedIdx r = true → r ≠ 9#5 → m5.get r = m1.get r := by
    intro r hr h9
    show (ukWr (ukWr m2 _ _) _ _).get r = _
    rw [ukWr_get_other _ _ _ _ (ucs_ne r 10#5 hr (by decide)), ukWr_get_other _ _ _ _ (ucs_ne r 15#5 hr (by decide)),
      hk2 r hr h9]
  -- the epilogue
  iapply ush_frame_epi UL N 4 [1#5, 8#5, 9#5] 1 0x1f6 [m.get 1#5, m.get 8#5, m.get 9#5]
    ⟨ushI_1f6 N.t, ushI_1f8 N.t, ushI_1fa N.t, trivial⟩ (ushI_1fc N.t) (ushI_1fe N.t) sp0 h5 m5 (10 + n)
    (by rw [hk5 spIdx (by decide) (by decide)]; show (ukWr (ukWr m _ _) _ _).get _ = _; ureg)
    hal (by omega) rfl $$ Hc Hsv Hloc Hrun
  iintro %h6 Hrun
  have hvs : [m.get 1#5, m.get 8#5, m.get 9#5] = [1#5, 8#5, 9#5].map m.get := rfl
  rw [hvs, ush_ret_ra m5 m _ (by simp)]
  iapply Hk $$ %h6 %_ %p [] [] %⟨hp0, hp16, hp38⟩ [Ht Hz] HM' Hpay Hrun
  · ipureintro
    apply ush_cs_epi m m5 _ sp0 rfl
    intro r hr hsp hmem
    have h8 : r ≠ 8#5 := fun he => hmem (by simp [he])
    have h9 : r ≠ 9#5 := fun he => hmem (by simp [he])
    rw [hk5 r hr h9]
    show (ukWr (ukWr m _ _) _ _).get r = _
    rw [ukWr_get_other _ _ _ _ h8, ukWr_get_other _ _ _ _ hsp]
  · ipureintro
    rw [ukWr_get_other _ _ _ _ (by decide), ushWrs_get_nmem _ _ _ _ (by decide)]
    show (ukWr m3 _ _).get _ = _; ureg
  · iapply ush_exec_pre_nil N s0 p hp0 (by omega)
    isplitl [Ht]
    · iapply ush_ubytes_ext $$ Ht
      intro j _
      show nthByte (n := 8) ((ukWr m2 15#5 _).get 15#5) j = _
      rw [ukWr_get_same _ _ _ (by decide), show BitVec.ofInt 32 (ushpTy (.exec [])) = BitVec.ofNat 32 1 by decide]
      exact ush_nthByte_64_32 1 j (by decide)
    · iexact Hz

/-- **sh's `execcmd` holds** (at the engine `UL` and memset `MS`). -/
theorem shExeccmd_holds (UL : UK_LEAVES) (MS : USH_MEMSET) : SH_EXECCMD :=
  ⟨fun N h m s0 n UM UM' Pex hM => wp_shExeccmd UL MS N h m s0 n UM UM' Pex hM⟩

end

end Xv6
