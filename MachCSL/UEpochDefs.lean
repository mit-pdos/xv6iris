/-
MachCSL: **the user-epoch record's pure vocabulary** (W8 (f3-utext) [OWN.89]
(W-R), part F-REGS: the hart's privilege and `satp` made visible to the state
interpretation).

The state interpretation keeps, per hart, a USER EPOCH (`UEp`): open from the
`csrw satp` that installs a user table (xv6: `userret`) to the `csrw satp`
that reinstalls the kernel's (xv6: `uservec`).  The record is read off the
register file: `uepLink` ties a hart's epoch to its `satp` and its privilege,
so that a pure statement of the machine (privilege, `satp`) is enough to know
the epoch is open.

* `satpTable s` -- the root PPN an Sv39 `satp` value names (MODE = 8, the
  privileged spec's `satp` layout: MODE in bits 63..60, the PPN in bits
  43..0); `none` in Bare (and every other) mode.
* `UEp` -- one open epoch: the root it installed.
* `uepLink ksat s p oe` -- the record of a hart whose `satp` is `s` and whose
  privilege is `p`: an OPEN epoch names exactly the table `satp` names, which
  is not the kernel's (`ksat`, the kernel table's root once a hart installed
  it); with NO epoch open the hart is not in user mode, and outside machine
  mode its `satp` is Bare or the kernel's.

Spec: the privileged spec's `satp` (MODE/ASID/PPN fields; Sail
`Mk_Satp64`/`_get_Satp64_Mode`); user-mode translation is governed by `satp`
(no MPRV in user mode); machine mode does not translate (xv6 keeps
`mstatus.MPRV = 0`), so the link says nothing of a machine-mode hart's `satp`
(the power-on value is arbitrary, `MachCSL.BootReset`).
-/
import MachCSL.Resources

namespace MachCSL

open LeanRV64D
open Iris Iris.BI Iris.ProofMode Std

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- A Bare `satp` names no table. -/
theorem satpTable_zero : satpTable 0#64 = none := by
  unfold satpTable
  rw [if_neg (by decide)]

/-- The Sv39 `satp` value of a root, at ASID 0 (`MachCSL.satpOf .kpt`). -/
theorem satpTable_sv39 (root : BitVec 44) : satpTable (8#4 ++ 0#16 ++ root) = some root := by
  unfold satpTable
  have h1 : BitVec.extractLsb' 60 4 (8#4 ++ 0#16 ++ root) = 8#4 := by bv_decide
  have h2 : BitVec.extractLsb' 0 44 (8#4 ++ 0#16 ++ root) = root := by bv_decide
  rw [if_pos h1, h2]

/-- **A step the record survives** (`MachCSL.uepModelAt_stable`): every
hart's `satp` and privilege unchanged, every instruction view at least where
it was. -/
def uepStable (σ σ' : MState) : Prop :=
  (∀ c : CPU, σ'.regs c Register.satp = σ.regs c Register.satp ∧
    σ'.regs c Register.cur_privilege = σ.regs c Register.cur_privilege) ∧
  ∀ c : CPU, σ.itv c ≤ σ'.itv c

theorem uepStable_refl (σ : MState) : uepStable σ σ :=
  ⟨fun _ => ⟨rfl, rfl⟩, fun _ => Nat.le_refl _⟩

theorem uepStable_trans {σ₁ σ₂ σ₃ : MState} (h₁ : uepStable σ₁ σ₂) (h₂ : uepStable σ₂ σ₃) : uepStable σ₁ σ₃ :=
  ⟨fun c => ⟨(h₂.1 c).1.trans (h₁.1 c).1, (h₂.1 c).2.trans (h₁.1 c).2⟩,
   fun c => Nat.le_trans (h₁.2 c) (h₂.2 c)⟩

/-- A step that moves neither the register files nor the instruction views. -/
theorem uepStable_of_eq {σ σ' : MState} (hr : σ'.regs = σ.regs) (hi : σ'.itv = σ.itv) : uepStable σ σ' :=
  ⟨fun c => by rw [hr]; exact ⟨rfl, rfl⟩, fun c => by rw [hi]; exact Nat.le_refl _⟩

/-- A fence moves no instruction view down (`fence.i` raises its hart's). -/
theorem uepStable_fence (σ : MState) (cpu : CPU) (b : barrier_kind) : uepStable σ (σ.fence cpu b) := by
  refine ⟨fun _ => ⟨rfl, rfl⟩, fun c => ?_⟩
  by_cases hc : c = cpu
  · subst hc
    simp only [updCpu, if_true]
    split
    · exact Nat.le_max_left _ _
    · exact Nat.le_refl _
  · simp only [updCpu, hc, if_false]
    exact Nat.le_refl _

/-- The power-on record: no epoch, the hart in machine mode. -/
theorem uepLink_boot (ksat : Option (BitVec 44)) (s : BitVec 64) :
    uepLink ksat s Privilege.Machine none :=
  ⟨fun _ h => (nomatch h), fun _ => ⟨fun h => (nomatch h), fun h => absurd rfl h⟩⟩

/-- The record of an open epoch reads only `satp` and the kernel root: the
privilege may move, outside machine mode. -/
theorem uepLink_some_priv {ksat : Option (BitVec 44)} {s : BitVec 64} {p : Privilege} {e : UEp}
    (h : uepLink ksat s p (some e)) (p' : Privilege) (hp' : p' ≠ Privilege.Machine) :
    uepLink ksat s p' (some e) :=
  ⟨fun e' he' => ⟨(h.1 e' he').1, (h.1 e' he').2.1, (h.1 e' he').2.2.1, hp'⟩, fun h0 => (nomatch h0)⟩

/-- A machine-mode hart has no epoch open. -/
theorem uepLink_machine {ksat : Option (BitVec 44)} {s : BitVec 64} {oe : Option UEp}
    (h : uepLink ksat s Privilege.Machine oe) : oe = none := by
  cases oe with
  | none => rfl
  | some e => exact absurd rfl (h.1 e rfl).2.2.2

/-- The kernel root becoming known keeps every record. -/
theorem uepLink_ksat {s : BitVec 64} {p : Privilege} {oe : Option UEp} (h : uepLink none s p oe)
    (rk : BitVec 44) : uepLink (some rk) s p oe := by
  refine ⟨fun e he => ?_, fun h0 => ⟨(h.2 h0).1, fun hp => ?_⟩⟩
  · have := (h.1 e he).2.1
    exact absurd this (by decide)
  · rcases (h.2 h0).2 hp with h1 | ⟨h1, _⟩
    · exact Or.inl h1
    · exact absurd h1 (by decide)

/-- An open epoch's root is the `satp` table. -/
theorem uepLink_some_root {ksat : Option (BitVec 44)} {s : BitVec 64} {p : Privilege} {e : UEp}
    (h : uepLink ksat s p (some e)) : satpTable s = some e.root :=
  (h.1 e rfl).1

/-- A privilege move between two non-user privileges that does not leave
machine mode keeps a closed record. -/
theorem uepLink_none_priv {ksat : Option (BitVec 44)} {s : BitVec 64} {p p' : Privilege}
    (h : uepLink ksat s p none) (hp' : p' ≠ Privilege.User)
    (hm : p ≠ Privilege.Machine ∨ p' = Privilege.Machine) : uepLink ksat s p' none := by
  refine ⟨fun _ h0 => (nomatch h0), fun _ => ⟨hp', fun hpm => ?_⟩⟩
  rcases hm with hm | hm
  · exact (h.2 rfl).2 hm
  · exact absurd hm hpm

/-- Entering supervisor mode out of machine mode with a Bare `satp` keeps a
closed record (xv6's `start`: `w_satp(0)`, then `mret`). -/
theorem uepLink_none_bare (ksat : Option (BitVec 44)) (s : BitVec 64) (p : Privilege)
    (hs : satpTable s = none) (hp : p ≠ Privilege.User) : uepLink ksat s p none :=
  ⟨fun _ h0 => (nomatch h0), fun _ => ⟨hp, fun _ => Or.inl hs⟩⟩

/-- The kernel table installed with no epoch open. -/
theorem uepLink_none_kern (rk : BitVec 44) (s : BitVec 64) (p : Privilege)
    (hs : satpTable s = some rk) (hp : p ≠ Privilege.User) : uepLink (some rk) s p none :=
  ⟨fun _ h0 => (nomatch h0), fun _ => ⟨hp, fun _ => Or.inr ⟨rfl, hs⟩⟩⟩

/-- A user table installed: the epoch at its root, past the kernel's. -/
theorem uepLink_open (rk r : BitVec 44) (s : BitVec 64) (p : Privilege) (hs : satpTable s = some r)
    (hne : r ≠ rk) (hp : p ≠ Privilege.Machine) : uepLink (some rk) s p (some ⟨r⟩) :=
  ⟨fun e he => by
    obtain rfl := Option.some.inj he
    exact ⟨hs, rfl, fun h => hne (Option.some.inj h).symm, hp⟩, fun h0 => (nomatch h0)⟩

/-- A closed record whose hart's `satp` names a table other than the
kernel's (`rk`) is impossible outside machine mode. -/
theorem uepLink_none_ne {ksat : Option (BitVec 44)} {s : BitVec 64} {p : Privilege} (h : uepLink ksat s p none)
    (hp : p ≠ Privilege.Machine) {r : BitVec 44} (hs : satpTable s = some r) (hk : ∀ rk, ksat = some rk → r ≠ rk) :
    False := by
  rcases (h.2 rfl).2 hp with h0 | ⟨_, h0⟩
  · rw [hs] at h0; exact nomatch h0
  · rw [hs] at h0
    exact hk r h0.symm rfl

/-- Whether a privilege is machine mode. -/
def privMachine : Privilege → Bool
  | .Machine => true
  | _ => false

theorem privMachine_ne {p : Privilege} (h : privMachine p = false) : p ≠ Privilege.Machine := by
  rintro rfl; exact nomatch h

theorem privMachine_eq {p : Privilege} (h : privMachine p = true) : p = Privilege.Machine := by
  cases p <;> first | rfl | exact nomatch h

theorem privUser_ne {p : Privilege} (h : privUser p = false) : p ≠ Privilege.User := by
  rintro rfl; exact nomatch h

theorem privUser_of_ne {p : Privilege} (h : p ≠ Privilege.User) : privUser p = false := by
  cases p <;> first | rfl | exact absurd rfl h

/-- Leaving user mode for a non-machine privilege keeps the record (it is
open). -/
theorem uepLink_uexit {ksat : Option (BitVec 44)} {s : BitVec 64} {oe : Option UEp}
    (h : uepLink ksat s Privilege.User oe) (p' : Privilege) (hp' : p' ≠ Privilege.Machine) :
    uepLink ksat s p' oe := by
  cases oe with
  | none => exact absurd rfl (h.2 rfl).1
  | some e => exact uepLink_some_priv h p' hp'

/-- A privilege write that crosses neither the user boundary nor the machine
boundary keeps the record. -/
theorem uepLink_quiet {ksat : Option (BitVec 44)} {s : BitVec 64} {p p' : Privilege} {oe : Option UEp}
    (h : uepLink ksat s p oe) (hu : privUser p = privUser p') (hm : privMachine p = privMachine p') :
    uepLink ksat s p' oe := by
  cases oe with
  | some e =>
    have hp : p ≠ Privilege.Machine := (h.1 e rfl).2.2.2
    have hpm : privMachine p = false := by
      cases p <;> first | rfl | exact absurd rfl hp
    exact uepLink_some_priv h p' (privMachine_ne (hm ▸ hpm))
  | none =>
    have hpu : privUser p = false := privUser_of_ne (h.2 rfl).1
    refine ⟨fun _ h0 => (nomatch h0), fun _ => ⟨privUser_ne (hu ▸ hpu), fun hp' => ?_⟩⟩
    have hp'm : privMachine p' = false := by
      cases p' <;> first | rfl | exact absurd rfl hp'
    exact (h.2 rfl).2 (privMachine_ne (hm.trans hp'm))

/-- An open epoch's hart is never at the kernel's table. -/
theorem uepLink_some_ne {ksat : Option (BitVec 44)} {s : BitVec 64} {p : Privilege} {e : UEp}
    (h : uepLink ksat s p (some e)) (rk : BitVec 44) (hk : ksat = some rk) : e.root ≠ rk := by
  intro he
  exact (h.1 e rfl).2.2.1 (by rw [hk, he])

/-! ## The record's laws (era level) -/

/-- The cells move with a step that keeps the hart's instruction view at
least where it was. -/
theorem uepCellsAt_mono [MachFixedGS hlc GF] (E : EraGS) {σ σ' : MState} (h : CPU)
    (_hi : σ.itv h ≤ σ'.itv h) (oe : Option UEp) : uepCellsAt (GF := GF) E σ h oe ⊢ uepCellsAt E σ' h oe := by
  unfold uepCellsAt
  exact .rfl

theorem uepCellsAt_stable [MachFixedGS hlc GF] (E : EraGS) {σ σ' : MState} (hs : uepStable σ σ') (h : CPU)
    (oe : Option UEp) : uepCellsAt (GF := GF) E σ h oe ⊢ uepCellsAt E σ' h oe :=
  uepCellsAt_mono E h (hs.2 h) oe

/-- **The record survives a step that keeps every `satp` and privilege and
moves no instruction view down.** -/
theorem uepModelAt_stable [MachFixedGS hlc GF] (E : EraGS) {σ σ' : MState} (hs : uepStable σ σ') :
    uepModelAt (GF := GF) E σ ⊢ uepModelAt E σ' := by
  unfold uepModelAt
  iintro ⟨%k, #Hk, H⟩
  iexists k
  iframe Hk
  iapply BigSepL.bigSepL_mono _ $$ H
  intro _ h _
  unfold uepHartAt
  iintro ⟨%oe, %hl, Hc⟩
  iexists oe
  rw [(hs.1 h).1, (hs.1 h).2]
  isplitr [Hc]
  · ipureintro; exact hl
  iapply uepCellsAt_stable E hs h oe $$ Hc

/-- A hart's record moves to a state with the same `satp` and privilege, its
instruction view no lower, and a kernel root that is the old one or newly
known. -/
theorem uepHartAt_mono [MachFixedGS hlc GF] (E : EraGS) {σ σ' : MState} {ksat ksat' : Option (BitVec 44)}
    (h : CPU) (hr : σ'.regs h Register.satp = σ.regs h Register.satp ∧
      σ'.regs h Register.cur_privilege = σ.regs h Register.cur_privilege)
    (hi : σ.itv h ≤ σ'.itv h) (hk : ksat' = ksat ∨ ksat = none) :
    uepHartAt (GF := GF) E σ ksat h ⊢ uepHartAt E σ' ksat' h := by
  unfold uepHartAt
  iintro ⟨%oe, %hl, Hc⟩
  iexists oe
  rw [hr.1, hr.2]
  isplitr [Hc]
  · ipureintro
    rcases hk with rfl | rfl
    · exact hl
    · cases ksat' with
      | none => exact hl
      | some rk => exact uepLink_ksat hl rk
  iapply uepCellsAt_mono E h hi oe $$ Hc

/-- **One hart's record out of the conjunct**, to be put back at a state
that keeps every other hart's `satp` and privilege, moves no instruction view
down, and at a kernel root that is the old one or newly known. -/
theorem uepModelAt_acc [MachFixedGS hlc GF] (E : EraGS) (σ : MState) (cpu : CPU) :
    uepModelAt (GF := GF) E σ ⊢ ∃ ksat : Option (BitVec 44), uepKsatAt E ksat ∗ uepHartAt E σ ksat cpu ∗
      ∀ (σ' : MState) (ksat' : Option (BitVec 44)),
        ⌜(∀ c, c ≠ cpu → σ'.regs c Register.satp = σ.regs c Register.satp ∧
            σ'.regs c Register.cur_privilege = σ.regs c Register.cur_privilege) ∧
          (∀ c, σ.itv c ≤ σ'.itv c) ∧ (ksat' = ksat ∨ ksat = none)⌝ -∗
        uepKsatAt E ksat' -∗ uepHartAt E σ' ksat' cpu -∗ uepModelAt E σ' := by
  have hget := cpus_get? cpu
  unfold uepModelAt
  iintro ⟨%k, #Hk, H⟩
  icases BigSepL.bigSepL_lookup_acc_impl (Φ := fun _ c => uepHartAt (GF := GF) E σ k c) hget $$ H
    with ⟨Hc, Hclose⟩
  iexists k
  iframe Hk Hc
  iintro %σ' %k' %⟨hr, hi, hk⟩ #Hk' Hc'
  iexists k'
  iframe Hk'
  iapply Hclose $$ %(fun _ c => uepHartAt E σ' k' c)
  · imodintro
    iintro %j %y %hj %hne Hy
    have hy : y ≠ cpu := cpus_get?_ne hj cpu hne
    iapply uepHartAt_mono E y (hr y hy) (hi y) hk $$ Hy
  · iexact Hc'

/-- A register update of one hart that every record of it survives. -/
theorem uepModelAt_regs [MachFixedGS hlc GF] (E : EraGS) (σ : MState) (cpu : CPU) (f : RegFile)
    (h : ∀ ksat oe, uepLink ksat (σ.regs cpu Register.satp) (σ.regs cpu Register.cur_privilege) oe →
      uepLink ksat (f Register.satp) (f Register.cur_privilege) oe) :
    uepModelAt (GF := GF) E σ ⊢ uepModelAt E { σ with regs := updCpu σ.regs cpu f } := by
  iintro H
  icases uepModelAt_acc E σ cpu $$ H with ⟨%k, #Hk, Hc, Hclose⟩
  iapply Hclose $$ %({ σ with regs := updCpu σ.regs cpu f }) %k
    %⟨fun c hc => by simp [updCpu, hc], fun _ => Nat.le_refl _, Or.inl rfl⟩ Hk
  unfold uepHartAt
  icases Hc with ⟨%oe, %hl, Hc⟩
  iexists oe
  isplitr [Hc]
  · ipureintro; simp only [updCpu, if_true]; exact h k oe hl
  iapply uepCellsAt_mono E (σ := σ) (σ' := { σ with regs := updCpu σ.regs cpu f }) cpu (Nat.le_refl _) oe $$ Hc

/-- The kernel root the record knows is the one a thread's root ghost
names. -/
theorem uepKsatAt_agree [MachFixedGS hlc GF] (E : EraGS) (k : Option (BitVec 44)) (kroot : BitVec 44) :
    uepKsatAt (GF := GF) E k ∗ (E.kptRootName ↪VAR{.discard} kroot) ⊢ ⌜∀ rk, k = some rk → rk = kroot⌝ := by
  cases k with
  | none =>
    iintro _
    ipureintro
    intro rk h
    exact nomatch h
  | some rk =>
    unfold uepKsatAt
    iintro ⟨⟨Hr, _⟩, Hr'⟩
    ihave %he := ghost_var_agree E.kptRootName rk _ kroot _ $$ Hr Hr'
    ipureintro
    intro rk' h
    obtain rfl := Option.some.inj h
    exact he

/-- **The S→U privilege write keeps the record**, given the `satp` table
is not the kernel's (the thread's root ghost `kroot`): the epoch is open. -/
theorem uepModelAt_uenter [MachFixedGS hlc GF] (E : EraGS) (σ : MState) (cpu : CPU) (f : RegFile)
    (kroot r : BitVec 44) (hs : satpTable (σ.regs cpu Register.satp) = some r) (hne : r ≠ kroot)
    (hp : σ.regs cpu Register.cur_privilege = Privilege.Supervisor)
    (hf : f Register.satp = σ.regs cpu Register.satp) (hfp : f Register.cur_privilege = Privilege.User) :
    uepModelAt (GF := GF) E σ ∗ (E.kptRootName ↪VAR{.discard} kroot) ⊢
      uepModelAt E { σ with regs := updCpu σ.regs cpu f } := by
  iintro ⟨H, #Hr⟩
  icases uepModelAt_acc E σ cpu $$ H with ⟨%k, #Hk, Hc, Hclose⟩
  ihave %hk := uepKsatAt_agree E k kroot $$ [Hk Hr]
  · iframe Hk Hr
  iapply Hclose $$ %({ σ with regs := updCpu σ.regs cpu f }) %k
    %⟨fun c hc => by simp [updCpu, hc], fun _ => Nat.le_refl _, Or.inl rfl⟩ Hk
  unfold uepHartAt
  icases Hc with ⟨%oe, %hl, Hc⟩
  iexists oe
  isplitr [Hc]
  · ipureintro
    simp only [updCpu, if_true]
    rw [hf, hfp]
    cases oe with
    | none =>
      rw [hp] at hl
      exact (uepLink_none_ne hl (by intro h; cases h) hs (fun rk h => by rw [hk rk h]; exact hne)).elim
    | some e =>
      exact uepLink_some_priv hl _ (by intro h; cases h)
  iapply uepCellsAt_mono E (σ := σ) (σ' := { σ with regs := updCpu σ.regs cpu f }) cpu (Nat.le_refl _) oe $$ Hc

/-- **The power-on record**: every hart in machine mode, no epoch open, no
kernel root known. -/
theorem uepModelAt_boot [MachFixedGS hlc GF] (E : EraGS) (σ : MState)
    (h : ∀ c, σ.regs c Register.cur_privilege = Privilege.Machine) : ⊢@{IProp GF} uepModelAt E σ := by
  unfold uepModelAt
  iexists none
  isplitr
  · unfold uepKsatAt; iempintro
  suffices H : ∀ l : List CPU, ⊢@{IProp GF} [∗list] c ∈ l, uepHartAt E σ none c from H cpus
  intro l
  induction l with
  | nil => exact BigSepL.bigSepL_nil_intro
  | cons c l ih =>
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · unfold uepHartAt
      iexists none
      isplitr
      · ipureintro; rw [h c]; exact uepLink_boot none _
      · unfold uepCellsAt; iempintro
    · iapply ih


end MachCSL
