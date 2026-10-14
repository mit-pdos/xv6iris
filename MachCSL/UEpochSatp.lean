/-
MachCSL: **the `satp` writes' ghost steps** (W8 (f3-utext) [OWN.89] (W-R),
F-REGS): the four `MachCSL.satpStep`s xv6's `satp` writes take, each moving
the interpretation's user-epoch record (`MachCSL.uepModelAt`,
`MachCSL.uepLink`):

* `satpStep_bare` -- `start`'s `w_satp(0)`, in machine mode (no epoch is
  open in machine mode);
* `satpStep_kern` -- installing the kernel table with no epoch open
  (`kvminithart`): the record learns the kernel root, from the installed
  table's root ghost and root word (`MachCSL.KptInv.kptOn`);
* `satpStep_open` -- installing a user table over the kernel's (`userret`):
  the hart's epoch opens at the user root;
* `satpStep_close` -- reinstalling the kernel table over a user table
  (`uservec`): the hart's epoch closes.

The kernel root a thread names (`kptRootName`, discarded once the kernel
table is sealed) agrees with the record's (`MachCSL.uepKsatAt_agree`), which
is how a step tells "the kernel's table" from "a user table" by the root
alone.
-/
import MachCSL.Wp
import MachCSL.KptInv
import MachCSL.SConfDefs
import MachCSL.SConfAtDefs

namespace MachCSL

open Iris Iris.BI Iris.ProofMode Std
open LeanRV64D

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

theorem sConfOf_satp (tier : KTier) (root : BitVec 44) (ms mdl mepc stc : BitVec 64) (lf : SLeft) :
    (sConfOf tier root ms mdl mepc stc lf).satp = satpOf tier root := rfl

theorem satpTable_satpOf (root : BitVec 44) : satpTable (satpOf KTier.kpt root) = some root := by
  unfold satpOf
  exact satpTable_sv39 root

theorem satpTable_satpOf_bare (root : BitVec 44) : satpTable (satpOf KTier.bare root) = none := by
  unfold satpOf
  exact satpTable_zero

/-- The table a kernel-shaped configuration's `satp` names. -/
theorem satpTable_of_sconfKpt {c : MConf} {root : BitVec 44} {sie : Bool} (h : SConfKpt (GF := GF) c root sie) :
    satpTable c.satp = some root := by
  unfold satpTable
  rw [if_pos h.2.1, h.2.2.2.1]

/-- A machine-mode `satp` write of Bare: no epoch is open in machine mode. -/
theorem satpStep_bare (cpu : CPU) (dq : DFrac) (s0 : BitVec 64) :
    ⊢ satpStep (GF := GF) cpu s0 0#64 iprop(Register.cur_privilege ↦ᵣ[cpu]{dq} Privilege.Machine)
        iprop(Register.cur_privilege ↦ᵣ[cpu]{dq} Privilege.Machine) := by
  unfold satpStep
  iintro %σ %_ Hregs Hmem Hmm Huep Hp
  ihave %hp : ⌜σ.regs cpu Register.cur_privilege = Privilege.Machine⌝ $$ [Hregs Hp]
  · icases reg_valid cpu (σ.regs cpu) Register.cur_privilege dq Privilege.Machine $$ [$Hregs $Hp] with %_
    itrivial
  imodintro
  iframe Hregs Hmem Hmm Hp
  iapply uepModelAt_regs _ σ cpu _ ?_ $$ Huep
  intro ksat oe hl
  rw [RegFile.set_same, RegFile.set_other _ _ _ _ (by decide)]
  rw [hp] at hl ⊢
  rw [uepLink_machine hl]
  exact uepLink_boot ksat _

theorem pteAddr_zero_eq (rk : BitVec 44) : pteAddr rk 0#9 = BitVec.setWidth 64 rk <<< 12 := by
  unfold pteAddr zero_extend Sail.BitVec.zeroExtend
  bv_decide

/-- The record's kernel root, newly known, from the installed table's root
ghost and root word. -/
theorem uepKsatAt_of_kptRootW (kroot : BitVec 44) (S : Nat) :
    (MachGS.kptRootName (hlc := hlc) (GF := GF) ↪VAR{.discard} kroot) ∗ kptRootW kroot S ⊢@{IProp GF}
      uepKsatAt (MachGS.era (hlc := hlc) (GF := GF)) (some kroot) := by
  unfold uepKsatAt kptRootW histBytes
  iintro ⟨#Hr, %ra, %Hr, %⟨hra, hhd⟩, #Hb⟩
  isplitl []
  · iexact Hr
  iexists ra, S, Hr
  isplitr
  · ipureintro; exact ⟨hra, fun j hj => by rw [← pteAddr_zero_eq]; exact hhd j hj⟩
  iexact Hb

/-- The installed kernel table's root ghost and root word. -/
theorem kptOn_root [CurCtx] (t : PTree) (M : RegMapF (BitVec 64)) :
    kptOn (GF := GF) t M ⊢
      (MachGS.kptRootName (hlc := hlc) (GF := GF) ↪VAR{.discard} t.base) ∗ ∃ S, kptRootW t.base S := by
  unfold kptOn kptCore
  iintro ⟨_, _, #Hr, %fl, ⟨%S, _, _, _, #Hw, _, _, _⟩, _⟩
  iframe Hr
  iexists S
  iexact Hw

/-- **Installing the kernel table with no epoch open** (`kvminithart`; the
old `satp` Bare or the kernel's already): the record learns the kernel
root. -/
theorem satpStep_kern (cpu : CPU) (dq : DFrac) (p : Privilege) (hp : p ≠ Privilege.User) (s0 : BitVec 64)
    (kroot : BitVec 44) (hs0 : satpTable s0 = none ∨ satpTable s0 = some kroot) (S : Nat) :
    ⊢ satpStep (GF := GF) cpu s0 (satpOf KTier.kpt kroot)
        iprop(Register.cur_privilege ↦ᵣ[cpu]{dq} p ∗
          ((MachGS.kptRootName (hlc := hlc) (GF := GF) ↪VAR{.discard} kroot) ∗ kptRootW kroot S))
        iprop(Register.cur_privilege ↦ᵣ[cpu]{dq} p ∗ emp) := by
  unfold satpStep
  iintro %σ %hs Hregs Hmem Hmm Huep ⟨Hp, #Hkr, #Hkw⟩
  ihave %hpv : ⌜σ.regs cpu Register.cur_privilege = p⌝ $$ [Hregs Hp]
  · icases reg_valid cpu (σ.regs cpu) Register.cur_privilege dq p $$ [$Hregs $Hp] with %_
    itrivial
  icases uepModelAt_acc _ σ cpu $$ Huep with ⟨%k, #Hk, Hc, Hclose⟩
  ihave %hk := uepKsatAt_agree _ k kroot $$ [Hk Hkr]
  · iframe Hk Hkr
  unfold uepHartAt
  icases Hc with ⟨%oe, %hl, Hcells⟩
  have hoe : oe = none := by
    cases oe with
    | none => rfl
    | some e =>
      exfalso
      obtain ⟨h1, h2, h3, -⟩ := hl.1 e rfl
      rw [hs] at h1
      rcases hs0 with h0 | h0
      · rw [h0] at h1; exact nomatch h1
      · rw [h0] at h1
        obtain ⟨rk, hrk⟩ := Option.isSome_iff_exists.1 h2
        rw [hrk, hk rk hrk, Option.some.inj h1] at h3
        exact h3 rfl
  subst hoe
  ihave Hks := uepKsatAt_of_kptRootW kroot S $$ [Hkr Hkw]
  · iframe Hkr Hkw
  have hkc : some kroot = k ∨ k = none := by
    cases k with
    | none => exact Or.inr rfl
    | some rk => exact Or.inl (by rw [hk rk rfl])
  imodintro
  iframe Hregs Hmem Hmm Hp
  iapply Hclose $$ %(σ.setReg cpu Register.satp (satpOf KTier.kpt kroot)) %(some kroot)
    %⟨fun c hc => by simp [updCpu, hc], fun _ => Nat.le_refl _, hkc⟩ Hks
  iexists none
  isplitr [Hcells]
  · ipureintro
    simp only [updCpu, if_true, RegFile.set_same]
    rw [RegFile.set_other _ _ _ _ (by decide), hpv]
    exact uepLink_none_kern kroot _ p (satpTable_satpOf kroot) hp
  · unfold uepCellsAt; iempintro

/-- **Installing a user table over the kernel's** (`userret`): the hart's
epoch opens at the user root. -/
theorem satpStep_open (cpu : CPU) (dq : DFrac) (s0 : BitVec 64) (kroot r : BitVec 44)
    (hs0 : satpTable s0 = some kroot) (hne : r ≠ kroot) :
    ⊢ satpStep (GF := GF) cpu s0 (satpOf KTier.kpt r)
        iprop(Register.cur_privilege ↦ᵣ[cpu]{dq} Privilege.Supervisor ∗
          (MachGS.kptRootName (hlc := hlc) (GF := GF) ↪VAR{.discard} kroot))
        iprop(Register.cur_privilege ↦ᵣ[cpu]{dq} Privilege.Supervisor ∗ emp) := by
  unfold satpStep
  iintro %σ %hs Hregs Hmem Hmm Huep ⟨Hp, #Hkr⟩
  ihave %hpv : ⌜σ.regs cpu Register.cur_privilege = Privilege.Supervisor⌝ $$ [Hregs Hp]
  · icases reg_valid cpu (σ.regs cpu) Register.cur_privilege dq Privilege.Supervisor $$ [$Hregs $Hp] with %_
    itrivial
  icases uepModelAt_acc _ σ cpu $$ Huep with ⟨%k, #Hk, Hc, Hclose⟩
  ihave %hk := uepKsatAt_agree _ k kroot $$ [Hk Hkr]
  · iframe Hk Hkr
  unfold uepHartAt
  icases Hc with ⟨%oe, %hl, Hcells⟩
  rw [hs, hpv] at hl
  have hoe : oe = none := by
    cases oe with
    | none => rfl
    | some e =>
      exfalso
      obtain ⟨h1, h2, h3, -⟩ := hl.1 e rfl
      rw [hs0] at h1
      obtain ⟨rk, hrk⟩ := Option.isSome_iff_exists.1 h2
      rw [hrk, hk rk hrk, Option.some.inj h1] at h3
      exact h3 rfl
  subst hoe
  have hks : k = some kroot := by
    rcases (hl.2 rfl).2 (by intro h; cases h) with h0 | ⟨_, h0⟩
    · rw [hs0] at h0; exact nomatch h0
    · rw [hs0] at h0; exact h0.symm
  subst hks
  imodintro
  iframe Hregs Hmem Hmm Hp
  iapply Hclose $$ %(σ.setReg cpu Register.satp (satpOf KTier.kpt r)) %(some kroot)
    %⟨fun c hc => by simp [updCpu, hc], fun _ => Nat.le_refl _, Or.inl rfl⟩ Hk
  iexists some ⟨r⟩
  isplitr [Hcells]
  · ipureintro
    simp only [updCpu, if_true, RegFile.set_same]
    rw [RegFile.set_other _ _ _ _ (by decide), hpv]
    exact uepLink_open kroot r _ _ (satpTable_satpOf r) hne (by intro h; cases h)
  · unfold uepCellsAt; iempintro

/-- **Reinstalling the kernel table over a user table** (`uservec`): the
hart's epoch closes. -/
theorem satpStep_close (cpu : CPU) (dq : DFrac) (s0 : BitVec 64) (kroot r : BitVec 44)
    (hs0 : satpTable s0 = some r) (hne : r ≠ kroot) :
    ⊢ satpStep (GF := GF) cpu s0 (satpOf KTier.kpt kroot)
        iprop(Register.cur_privilege ↦ᵣ[cpu]{dq} Privilege.Supervisor ∗
          (MachGS.kptRootName (hlc := hlc) (GF := GF) ↪VAR{.discard} kroot))
        iprop(Register.cur_privilege ↦ᵣ[cpu]{dq} Privilege.Supervisor ∗ emp) := by
  unfold satpStep
  iintro %σ %hs Hregs Hmem Hmm Huep ⟨Hp, #Hkr⟩
  ihave %hpv : ⌜σ.regs cpu Register.cur_privilege = Privilege.Supervisor⌝ $$ [Hregs Hp]
  · icases reg_valid cpu (σ.regs cpu) Register.cur_privilege dq Privilege.Supervisor $$ [$Hregs $Hp] with %_
    itrivial
  icases uepModelAt_acc _ σ cpu $$ Huep with ⟨%k, #Hk, Hc, Hclose⟩
  ihave %hk := uepKsatAt_agree _ k kroot $$ [Hk Hkr]
  · iframe Hk Hkr
  unfold uepHartAt
  icases Hc with ⟨%oe, %hl, Hcells⟩
  rw [hs, hpv] at hl
  have hkk : k = some kroot := by
    cases oe with
    | none =>
      exact (uepLink_none_ne hl (by intro h; cases h) hs0
        (fun rk h => by rw [hk rk h]; exact hne)).elim
    | some e =>
      obtain ⟨-, h2, -, -⟩ := hl.1 e rfl
      obtain ⟨rk, hrk⟩ := Option.isSome_iff_exists.1 h2
      rw [hrk, hk rk hrk]
  subst hkk
  imodintro
  iframe Hregs Hmem Hmm Hp
  iapply Hclose $$ %(σ.setReg cpu Register.satp (satpOf KTier.kpt kroot)) %(some kroot)
    %⟨fun c hc => by simp [updCpu, hc], fun _ => Nat.le_refl _, Or.inl rfl⟩ Hk
  iexists none
  isplitr [Hcells]
  · ipureintro
    simp only [updCpu, if_true, RegFile.set_same]
    rw [RegFile.set_other _ _ _ _ (by decide), hpv]
    exact uepLink_none_kern kroot _ _ (satpTable_satpOf kroot) (by intro h; cases h)
  · unfold uepCellsAt; iempintro

end MachCSL
