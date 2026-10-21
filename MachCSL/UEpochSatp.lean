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
import MachCSL.PteClass

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
  iintro ⟨_, _, #Hr, %fl, %fr, ⟨%S, _, _, _, #Hw, _⟩, _⟩
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

/-! ## The opening deposit

At `userret`'s `csrw satp` the client hands the interpretation a quarter of
every text byte and table-slot byte, each history headed at or below the
stamp `K` (the `fence.i` just before raised the instruction view to `K`).
The slot discipline (`uslotHistOk`) follows from the heads and the
histories' order (`histOk`: newest first), which the step reads off the
interpretation. -/

/-- One slot's deposit: its eight bytes' histories, headed at or below `K` by
the bytes of its value. -/
abbrev uslotPreCell (K : Nat) (p : Nat × KSlot) : IProp GF := iprop%
  ∃ L : List (Nat × Nat), landedAll L ∗
  [∗list] j ∈ List.range 8, ∃ (x : HEnt) (H : Hist),
    pointsTo (G := (MachGS.era (hlc := hlc) (GF := GF)).mem) (p.2.addr + BitVec.ofNat 64 j)
      (DFrac.own Qp.quarter) (x :: H) ∗
      ⌜(x.t = 0 ∨ ∃ q, (x.t, q) ∈ L ∧ q ≤ K) ∧ x.v = nthByte (n := 8) p.2.c j⌝

/-- **The opening deposit** of an epoch: `uepCellsE` with each slot's
discipline still to be read off its histories. -/
def uepPreE (h : CPU) (e : UEp) : IProp GF :=
  iprop(⌜uepFacts e⌝ ∗ MonoNat.lb_own ((MachGS.era (hlc := hlc) (GF := GF)).iviewName h) (.ofNat e.K) ∗
      ([∗list] a ∈ e.text, ∃ (x : HEnt) (H : Hist),
        pointsTo (G := (MachGS.era (hlc := hlc) (GF := GF)).mem) a (DFrac.own Qp.quarter) (x :: H) ∗
          (⌜x.t = 0⌝ ∨ ∃ q : Nat, landedAt x.t q ∗ ⌜q ≤ e.K⌝)) ∗
      [∗list] p ∈ e.slots, uslotPreCell e.K p)

/-- Per-byte headed histories as one history map. -/
theorem preBytes_hist (pa : PAddr) (dq : DFrac) (P : Nat → HEnt → Prop) : ∀ n : Nat,
    ([∗list] j ∈ List.range n, ∃ (x : HEnt) (H : Hist), (pa + BitVec.ofNat 64 j) ↦ₕ{dq} (x :: H) ∗ ⌜P j x⌝)
      ⊢@{IProp GF} ∃ Hs : Nat → Hist, ([∗list] j ∈ List.range n, (pa + BitVec.ofNat 64 j) ↦ₕ{dq} Hs j) ∗
        ⌜∀ j, j < n → ∃ x H, Hs j = x :: H ∧ P j x⌝
  | 0 => by
    iintro _
    iexists (fun _ => [])
    isplitl []
    · simp only [List.range_zero, Iris.Algebra.BigOpL.bigOpL_nil]; iempintro
    · ipureintro; intro j hj; omega
  | n + 1 => by
    rw [List.range_succ]
    iintro Hb
    icases BigSepL.bigSepL_snoc.1 $$ Hb with ⟨Hb1, %x, %H, Hpt, %hx⟩
    icases preBytes_hist pa dq P n $$ Hb1 with ⟨%Hs1, H1, %h1⟩
    have hmem : ∀ {k y : Nat}, (List.range n)[k]? = some y → y ≠ n := by
      intro k y hk hy
      have := List.mem_of_getElem? hk
      rw [List.mem_range] at this
      omega
    iexists (fun j => if j = n then x :: H else Hs1 j)
    have heq : ([∗list] j ∈ List.range n, (pa + BitVec.ofNat 64 j) ↦ₕ{dq}
        (fun j => if j = n then x :: H else Hs1 j) j) =
        ([∗list] j ∈ List.range n, (pa + BitVec.ofNat 64 j) ↦ₕ{dq} Hs1 j : IProp GF) := by
      apply BigSepL.bigSepL_eq
      intro k y hk
      simp only [hmem hk, if_false]
    isplitl [H1 Hpt]
    · iapply BigSepL.bigSepL_snoc.2
      simp only [if_true]
      rw [heq]
      iframe H1 Hpt
    · ipureintro
      intro j hj
      by_cases hjn : j = n
      · subst hjn; exact ⟨x, H, by simp, hx⟩
      · simp only [hjn, if_false]; exact h1 j (by omega)

/-- **A slot's certified discipline at the opening** (route P, D11): headed by its value, the head
the image's or landed at or below `K` (certified); nothing above it yet. -/
theorem uslotHistOkL_of_pre (K : Nat) (d : KSlot) (Hs : Nat → Hist) (L : List (Nat × Nat))
    (hp : ∀ j, j < 8 → ∃ x H, Hs j = x :: H ∧ (x.t = 0 ∨ ∃ q, (x.t, q) ∈ L ∧ q ≤ K) ∧
      x.v = nthByte (n := 8) d.c j) : uslotHistOkL K d Hs L := by
  refine ⟨⟨d.c, fun j hj => ?_, ?_⟩, fun j hj => ?_⟩
  · obtain ⟨x, H, hx, -, hxv⟩ := hp j hj
    rw [hx]; simp [hxv]
  · split
    · rfl
    · exact pteAD_refl d.c
  · obtain ⟨x, H, hx, hxc, hxv⟩ := hp j hj
    exact ⟨[], x, H, by rw [hx]; rfl, hxv, hxc, fun e he => by cases he⟩

/-- **A slot's discipline at the opening**: headed at or below `K` by its
value, newest first. -/
theorem uslotHistOk_of_pre (K : Nat) (d : KSlot) (Hs : Nat → Hist)
    (hp : ∀ j, j < 8 → ∃ x H, Hs j = x :: H ∧ x.t ≤ K ∧ x.v = nthByte (n := 8) d.c j)
    (hs : ∀ j, j < 8 → (Hs j).Pairwise (fun e e' => e'.t ≤ e.t)) : uslotHistOk K d Hs := by
  refine ⟨fun j hj => ?_, ⟨d.c, fun j hj => ?_, ?_⟩, fun j hj e he hlt => ?_⟩
  · obtain ⟨x, H, hx, hxt, hxv⟩ := hp j hj
    rw [hx, List.find?_cons_of_pos (by simpa using hxt)]
    simp [hxv]
  · obtain ⟨x, H, hx, -, hxv⟩ := hp j hj
    rw [hx]; simp [hxv]
  · split
    · rfl
    · exact pteAD_refl d.c
  · exfalso
    obtain ⟨x, H, hx, hxt, -⟩ := hp j hj
    have hsj := hs j hj
    rw [hx] at he hsj
    rcases List.mem_cons.1 he with rfl | he'
    · omega
    · have := List.rel_of_pairwise_cons hsj he'
      omega

/-- The deposit's slots, their discipline read off the heap. -/
theorem uslotPre_cells (m : FlatMem) (K : Nat) : ∀ sl : List (Nat × KSlot),
    genHeapInterp m ∗ ([∗list] p ∈ sl, uslotPreCell K p) ⊢@{IProp GF}
      genHeapInterp m ∗ [∗list] p ∈ sl, ∃ (Hs : Nat → Hist) (L : List (Nat × Nat)),
        ([∗list] j ∈ List.range 8, pointsTo (G := (MachGS.era (hlc := hlc) (GF := GF)).mem)
          (p.2.addr + BitVec.ofNat 64 j) (DFrac.own Qp.quarter) (Hs j)) ∗ landedAll L ∗ ⌜uslotHistOkL K p.2 Hs L⌝
  | [] => by
    iintro ⟨Hm, _⟩
    iframe Hm
    simp only [Iris.Algebra.BigOpL.bigOpL_nil]; iempintro
  | p :: sl => by
    iintro ⟨Hm, Hl⟩
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hp, Hl⟩
    icases uslotPre_cells m K sl $$ [Hm Hl] with ⟨Hm, Hl⟩
    · iframe
    icases Hp with ⟨%L, #HL, Hp⟩
    icases preBytes_hist (GF := GF) p.2.addr (DFrac.own Qp.quarter)
      (fun j x => (x.t = 0 ∨ ∃ q, (x.t, q) ∈ L ∧ q ≤ K) ∧ x.v = nthByte (n := 8) p.2.c j) 8 $$ Hp with ⟨%Hs, Hh, %hh⟩
    iframe Hm
    iapply BigSepL.bigSepL_cons.2
    iframe Hl
    iexists Hs, L
    iframe Hh HL
    ipureintro
    exact uslotHistOkL_of_pre K p.2 Hs L (fun j hj => by
      obtain ⟨x, H, h1, h2, h3⟩ := hh j hj; exact ⟨x, H, h1, h2, h3⟩)

/-- **Installing a user table over the kernel's** (`userret`): the hart's
epoch opens at the user root, the interpretation taking the epoch's custody
(`uepCellsE`: half of every text byte and table slot, W8 (f3-utext)). -/
theorem satpStep_open (cpu : CPU) (dq : DFrac) (s0 : BitVec 64) (kroot : BitVec 44) (e : UEp)
    (hs0 : satpTable s0 = some kroot) (hne : e.root ≠ kroot) :
    ⊢ satpStep (GF := GF) cpu s0 (satpOf KTier.kpt e.root)
        iprop(Register.cur_privilege ↦ᵣ[cpu]{dq} Privilege.Supervisor ∗
          ((MachGS.kptRootName (hlc := hlc) (GF := GF) ↪VAR{.discard} kroot) ∗
            uepPreE cpu e))
        iprop(Register.cur_privilege ↦ᵣ[cpu]{dq} Privilege.Supervisor ∗ emp) := by
  unfold satpStep
  iintro %σ %hs Hregs Hmem Hmm Huep ⟨Hp, #Hkr, Hdep⟩
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
  ihave %hmm := memModel_mmOk _ σ $$ Hmm
  unfold uepPreE
  icases Hdep with ⟨%hf, #Hiv, Htext, Hslots⟩
  icases uslotPre_cells σ.mem e.K e.slots $$ [Hmem Hslots] with ⟨Hmem, Hslots⟩
  · iframe
  imodintro
  iframe Hregs Hmem Hmm Hp
  iapply Hclose $$ %(σ.setReg cpu Register.satp (satpOf KTier.kpt e.root)) %(some kroot)
    %⟨fun c hc => by simp [updCpu, hc], fun _ => Nat.le_refl _, Or.inl rfl⟩ Hk
  iexists some e
  isplitr [Htext Hslots]
  · ipureintro
    simp only [updCpu, if_true, RegFile.set_same]
    rw [RegFile.set_other _ _ _ _ (by decide), hpv]
    exact uepLink_open kroot e _ _ (satpTable_satpOf e.root) hne (by intro h; cases h)
  · rw [uepCellsAt_some]
    unfold uepCellsE
    iframe Hiv Htext Hslots
    ipureintro; exact hf

/-- **Reinstalling the kernel table over a user table** (`uservec`): the
hart's epoch closes, the interpretation handing its custody back. -/
theorem satpStep_close (cpu : CPU) (dq : DFrac) (s0 : BitVec 64) (kroot r : BitVec 44)
    (hs0 : satpTable s0 = some r) (hne : r ≠ kroot) :
    ⊢ satpStep (GF := GF) cpu s0 (satpOf KTier.kpt kroot)
        iprop(Register.cur_privilege ↦ᵣ[cpu]{dq} Privilege.Supervisor ∗
          (MachGS.kptRootName (hlc := hlc) (GF := GF) ↪VAR{.discard} kroot))
        iprop(Register.cur_privilege ↦ᵣ[cpu]{dq} Privilege.Supervisor ∗
          ∃ e : UEp, ⌜e.root = r⌝ ∗ uepCellsE (MachGS.era (hlc := hlc) (GF := GF)) cpu e) := by
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
  cases oe with
  | none =>
    exact (uepLink_none_ne hl (by intro h; cases h) hs0
      (fun rk h => by rw [hk rk h]; exact hne)).elim
  | some e =>
  obtain ⟨h1, h2, -, -⟩ := hl.1 e rfl
  have her : e.root = r := by rw [hs0] at h1; exact (Option.some.inj h1).symm
  have hkk : k = some kroot := by
    obtain ⟨rk, hrk⟩ := Option.isSome_iff_exists.1 h2
    rw [hrk, hk rk hrk]
  subst hkk
  imodintro
  iframe Hregs Hmem Hmm Hp
  isplitr [Hcells]
  · iapply Hclose $$ %(σ.setReg cpu Register.satp (satpOf KTier.kpt kroot)) %(some kroot)
      %⟨fun c hc => by simp [updCpu, hc], fun _ => Nat.le_refl _, Or.inl rfl⟩ Hk
    iexists none
    isplitr
    · ipureintro
      simp only [updCpu, if_true, RegFile.set_same]
      rw [RegFile.set_other _ _ _ _ (by decide), hpv]
      exact uepLink_none_kern kroot _ _ (satpTable_satpOf kroot) (by intro h; cases h)
    · unfold uepCellsAt; iempintro
  · iexists e
    isplitr
    · ipureintro; exact her
    rw [uepCellsAt_some]
    iexact Hcells

end MachCSL
