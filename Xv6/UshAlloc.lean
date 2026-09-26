/-
**sh's constructors: the allocation core** (sh-parse lane; stage file of
`ProofShExeccmd`/`ProofShRedircmd`/`ProofShPipecmd`; Rocq repeats this run
inline in `UkShParseLex.wp_kshp_execcmd`, `UkShRedirCmd.wp_kshp_redircmd_n`
and `UkShPipeCmd.wp_kshp_pipecmd`, pinned `1900b8a43`).

All five of sh's constructors open the same way:

    li a0,SZ ; jal malloc ; mv s1,a0 ; li a2,SZ ; li a1,0 ; jal memset

`ush_alloc_core` is that run once, at any pcs: the allocator's contract
(`ushmMallocTy`), and then either its NULL arm -- `memset(0, 0, SZ)` stores
into the text page at address 0 and the process DIES, paying its exit out
of the lend `Pex` (Rocq `UkSh.wp_ksh_memset_null`) -- or its success arm,
which hands back the node's `SZ` bytes ZEROED, `s1 = p`, and every other
callee-saved register as it was.

Deviation from Rocq: the run is one lemma (Rocq writes it out per
constructor); `memset` is the parameter `USH_MEMSET` (UshTreeDefs
deviation 2).
-/
import Xv6.UshNodes

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open LeanRV64D LeanRV64D.Functions
open Std (ExtTreeSet)

set_option linter.unusedSectionVars false

section UshAlloc
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CtokG GF] [SG : UexecSG GF] [PS : UprogSG GF]
  [GhostMapG GF Nat (BitVec 8) RegMapF] [GhostVarG GF Nat] [GhostMapG GF (Option Nat) UfdCell UfdMapF]
  [GhostVarG GF (ExtTreeSet GName compare)] [GhostVarG GF Int]

/-- sh's text byte at address 0 (the NULL page is text). -/
theorem ush_text0 (N : UkNames GF) : ushCode (GF := GF) N.t ⊢ utext N.t 0 1#8 :=
  User.utextImg_byte (utext N.t) User.Sh.code.byte 0 1#8 (by decide)

/-- **THE ALLOCATION CORE** (see the header). -/
theorem ush_alloc_core (UL : UK_LEAVES) (MS : USH_MEMSET) (N : UkNames GF)
    (x0 x1 x2 x3 x4 x5 x6 sz : Nat) {r0 r3 r4 : Bool} {i0 i3 : BitVec 12} {j1 j5 : BitVec 21}
    (hi0 : ushCode (GF := GF) N.t ⊢ uinstrIs N.t (BitVec.ofNat 64 x0) r0 (.ITYPE (i0, .Regidx 0#5, .Regidx 10#5, .ADDI)))
    (hi1 : ushCode (GF := GF) N.t ⊢ uinstrIs N.t (BitVec.ofNat 64 x1) false (.JAL (j1, .Regidx 1#5)))
    (hi2 : ushCode (GF := GF) N.t ⊢ uinstrIs N.t (BitVec.ofNat 64 x2) true
      (.RTYPE (.Regidx 10#5, .Regidx 0#5, .Regidx 9#5, .ADD)))
    (hi3 : ushCode (GF := GF) N.t ⊢ uinstrIs N.t (BitVec.ofNat 64 x3) r3 (.ITYPE (i3, .Regidx 0#5, .Regidx 12#5, .ADDI)))
    (hi4 : ushCode (GF := GF) N.t ⊢ uinstrIs N.t (BitVec.ofNat 64 x4) r4 (.ITYPE (0#12, .Regidx 0#5, .Regidx 11#5, .ADDI)))
    (hi5 : ushCode (GF := GF) N.t ⊢ uinstrIs N.t (BitVec.ofNat 64 x5) false (.JAL (j5, .Regidx 1#5)))
    (h : CPU) (m : RegMap) (n : Nat) (UM UM' Pex : IProp GF) (hM : ushmMallocTyLe (hlc := hlc) N 168 UM UM')
    (hsz0 : 0 < sz := by decide) (hsz : sz ≤ 168 := by decide) (hsz31 : sz < 2 ^ 31 := by decide)
    (hx1 : x0 + (if r0 then 2 else 4) = x1 := by decide) (hx2 : x1 + 4 = x2 := by decide)
    (hx3 : x2 + 2 = x3 := by decide) (hx4 : x3 + (if r3 then 2 else 4) = x4 := by decide)
    (hx5 : x4 + (if r4 then 2 else 4) = x5 := by decide) (hx6 : x5 + 4 = x6 := by decide)
    (hs0 : BitVec.signExtend 64 i0 = BitVec.ofNat 64 sz := by decide)
    (hs3 : BitVec.signExtend 64 i3 = BitVec.ofNat 64 sz := by decide)
    (ht1 : BitVec.ofNat 64 x1 + BitVec.signExtend 64 j1 = BitVec.ofNat 64 User.Sh.Sym.«malloc» := by decide)
    (ht5 : BitVec.ofNat 64 x5 + BitVec.signExtend 64 j5 = BitVec.ofNat 64 User.Sh.Sym.«memset» := by decide)
    (he2 : x2 % 2 = 0 ∧ x2 < 2 ^ 64 := by decide) (he6 : x6 % 2 = 0 ∧ x6 < 2 ^ 64 := by decide) :
    ⊢ ushCode N.t -∗ UM -∗ □ (Pex -∗ N.pay (-1)) -∗ Pex -∗
      urun (hlc := hlc) N h m (BitVec.ofNat 64 x0) (10 + n) -∗
      (∀ (h' : CPU) (m' : RegMap) (p : Nat),
        ⌜∀ r, ucalleeSavedIdx r = true → r ≠ 9#5 → m'.get r = m.get r⌝ -∗ ⌜m'.get 9#5 = BitVec.ofNat 64 p⌝ -∗
        ⌜0 < p ∧ p % 16 = 0 ∧ p + sz < 2 ^ 38⌝ -∗ ubytes N.d p sz (fun _ => ubyte0) -∗ UM' -∗ Pex -∗
        urun (hlc := hlc) N h' m' (BitVec.ofNat 64 x6) (10 + n) -∗ wpLoop h') -∗
      wpLoop h := by
  iintro #Hc HM #Hpx Hpay Hrun Hk
  -- li a0,SZ
  iapply ushS_li UL N hi0 x1 h m (10 + n) sz hs0 hx1 $$ Hc Hrun
  iintro %h1 Hrun
  -- jal malloc
  iapply ushS_jal UL N hi1 _ x2 h1 _ (10 + n) ht1 hx2 (by decide) $$ Hc Hrun
  iintro %h2 Hrun
  let m2 := ukWr (ukWr m 10#5 (BitVec.ofNat 64 sz)) 1#5 (BitVec.ofNat 64 x2)
  iapply hM h2 m2 sz n (by show (ukWr (ukWr m _ _) _ _).get _ = _; ureg) hsz0 hsz $$ Hc HM Hrun
  iintro %h3 %m3 %hcs3 Hres Hrun
  have hra2 : m2.get 1#5 = BitVec.ofNat 64 x2 := by show (ukWr (ukWr m _ _) _ _).get _ = _; ureg
  rw [hra2, ush_retPc x2 he2.1 he2.2]
  -- the callee-saved registers of m, through the malloc
  have hk3 : ∀ r, ucalleeSavedIdx r = true → m3.get r = m.get r := by
    intro r hr
    rw [hcs3 r hr]
    show (ukWr (ukWr m _ _) _ _).get r = _
    rw [ukWr_get_other _ _ _ _ (ucs_ne r 1#5 hr (by decide)), ukWr_get_other _ _ _ _ (ucs_ne r 10#5 hr (by decide))]
  icases Hres with (%hnull | ⟨%p, %g, %hp, %hpb, Hbuf, HM'⟩)
  · -- THE NULL ARM: memset stores through NULL and dies
    iapply ushS_mv UL N hi2 x3 h3 m3 (10 + n) 0#64 hnull (by simpa using hx3) $$ Hc Hrun
    iintro %h4 Hrun
    iapply ushS_li UL N hi3 x4 h4 _ (10 + n) sz hs3 hx4 $$ Hc Hrun
    iintro %h5 Hrun
    iapply ushS_li UL N hi4 x5 h5 _ (10 + n) 0 (by decide) hx5 $$ Hc Hrun
    iintro %h6 Hrun
    iapply ushS_jal UL N hi5 _ x6 h6 _ (10 + n) ht5 hx6 (by decide) $$ Hc Hrun
    iintro %h7 Hrun
    ihave #Ht0 := ush_text0 N $$ Hc
    ihave Hdie := Hpx $$ Hpay
    rw [show 10 + n = 2 + (8 + n) by omega]
    iapply MS.wp_ushMemsetNull N h7 _ 0 sz 1#8 (8 + n) (by omega)
      (by show (ukWr (ukWr (ukWr (ukWr m3 _ _) _ _) _ _) _ _).get _ = _; ureg; exact hnull)
      (by show (ukWr (ukWr (ukWr (ukWr m3 _ _) _ _) _ _) _ _).get _ = _; ureg) hsz0 hsz31
      $$ Hc Ht0 Hdie Hrun
  · -- THE SUCCESS ARM
    iapply ushS_mv UL N hi2 x3 h3 m3 (10 + n) (BitVec.ofNat 64 p) hp (by simpa using hx3) $$ Hc Hrun
    iintro %h4 Hrun
    iapply ushS_li UL N hi3 x4 h4 _ (10 + n) sz hs3 hx4 $$ Hc Hrun
    iintro %h5 Hrun
    iapply ushS_li UL N hi4 x5 h5 _ (10 + n) 0 (by decide) hx5 $$ Hc Hrun
    iintro %h6 Hrun
    iapply ushS_jal UL N hi5 _ x6 h6 _ (10 + n) ht5 hx6 (by decide) $$ Hc Hrun
    iintro %h7 Hrun
    let m7 := ukWr (ukWr (ukWr (ukWr m3 9#5 (BitVec.ofNat 64 p)) 12#5 (BitVec.ofNat 64 sz)) 11#5
      (BitVec.ofNat 64 0)) 1#5 (BitVec.ofNat 64 x6)
    rw [show 10 + n = 2 + (8 + n) by omega]
    iapply MS.wp_ushMemset N h7 m7 p sz g (8 + n)
      (by show (ukWr (ukWr (ukWr (ukWr m3 _ _) _ _) _ _) _ _).get _ = _; ureg; exact hp)
      (by show (ukWr (ukWr (ukWr (ukWr m3 _ _) _ _) _ _) _ _).get _ = _; ureg) hsz0 hsz31
      $$ Hc Hbuf Hrun
    iintro Hbuf %h8 %m8 %hcs8 Hrun
    have h7_1 : m7.get 1#5 = BitVec.ofNat 64 x6 := by show (ukWr (ukWr (ukWr (ukWr m3 _ _) _ _) _ _) _ _).get _ = _; ureg
    have h7_11 : m7.get 11#5 = BitVec.ofNat 64 0 := by
      show (ukWr (ukWr (ukWr (ukWr m3 _ _) _ _) _ _) _ _).get _ = _; ureg
    rw [h7_1, ush_retPc x6 he6.1 he6.2, h7_11, show 2 + (8 + n) = 10 + n by omega]
    iapply Hk $$ %h8 %m8 %p [] [] %(⟨hpb.1, hpb.2.1, hpb.2.2⟩) [Hbuf] HM' Hpay Hrun
    · ipureintro
      intro r hr h9
      rw [hcs8 r hr]
      show (ukWr (ukWr (ukWr (ukWr m3 _ _) _ _) _ _) _ _).get r = _
      rw [ukWr_get_other _ _ _ _ (ucs_ne r 1#5 hr (by decide)), ukWr_get_other _ _ _ _ (ucs_ne r 11#5 hr (by decide)),
        ukWr_get_other _ _ _ _ (ucs_ne r 12#5 hr (by decide)), ukWr_get_other _ _ _ _ h9, hk3 r hr]
    · ipureintro
      rw [hcs8 9#5 (by decide)]
      show (ukWr (ukWr (ukWr (ukWr m3 _ _) _ _) _ _) _ _).get _ = _
      ureg
    · iapply ush_ubytes_ext N.d p sz _ _ (fun j _ => ?_) $$ Hbuf
      show nthByte (n := 8) (BitVec.ofNat 64 0) 0 = ubyte0
      exact ush_nthByte_zero 0

end UshAlloc

end Xv6
