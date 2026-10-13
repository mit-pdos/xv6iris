/-
MachCSL: THE CHAIN CERTIFICATES' LAWS (W8 (f2-ctx); `MachCSL.ChainDefs`,
`MachCSL.chainModelAt`, `PROGRESS-W8f2.md`).

What the state interpretation's certificate map gives and takes:

* `memModel_chainCert` / `memModel_chainLb` / `memModel_gate`: an issued
  certificate is VALID of the machine -- a sync chain through the static
  spinlocks' lock bytes, own entries before the deadline, or the boot hop --
  and an issued gate is a hart past the boot gate;
* `memModel_certIssue` / `memModel_gateIssue`: a valid certificate / gate may
  be issued (a ghost update under the interpretation; re-issuing hands out
  the element already there);
* `memModel_chainRetime` -- **the release's record**: a chain lower bound
  to the releasing hart, re-dated to the next position of the order (where
  the release store lands), because every entry of the memory, every chain's
  last acquire among them, is at or below the top;
* `memModel_chainHop` -- **the acquire's extension**: on a lock byte whose
  history is headed by the winning AMO's entry over the release entry over
  a nonzero entry (`MachCSL.syncHop_of_head`), a lower bound to the releaser
  before the release becomes one to the acquirer -- a boot-hop cover of the
  releaser through the acquirer's own gate.

The lock rules (`MachCSL.WpLock`) are where the last two run; nothing here
names a lock invariant.
-/
import MachCSL.WpAtomic

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std Std
open LeanRV64D

variable {hlc : HasLC} {GF : BundledGFunctors}

section era
variable [MachFixedGS hlc GF] (E : EraGS)

/-- An issued certificate is valid of the machine. -/
theorem memModel_chainCert (σ : MState) (c : ChainCert) :
    memModelAt E σ ∗ chainCertAt E c ⊢@{IProp GF} ⌜c.valid (chainEnv (hlc := hlc) (GF := GF) σ)⌝ := by
  unfold memModelAt rsvModelAt chainModelAt chainCertAt
  iintro ⟨⟨_, _, _, _, _, _, _, %Z, HZ, %hZ, _⟩, %v, Hc⟩
  ihave %Hl := ghost_map_lookup $$ HZ Hc
  ipureintro
  exact hZ.1 c (by rw [Hl]; rfl)

/-- An issued gate is a hart past the gate. -/
theorem memModel_gate (σ : MState) (j : CPU) :
    memModelAt E σ ∗ gatePassedAt E j ⊢@{IProp GF} ⌜gateOk (chainEnv (hlc := hlc) (GF := GF) σ) j⌝ := by
  unfold memModelAt rsvModelAt chainModelAt gatePassedAt
  iintro ⟨⟨_, _, _, _, _, _, _, %Z, HZ, %hZ, _⟩, Hg⟩
  icases Hg with ⟨%hw | ⟨%v, Hc⟩⟩
  · ipureintro
    intro f w hp hj
    exact absurd (hw f w hp).symm hj
  · ihave %Hl := ghost_map_lookup $$ HZ Hc
    ipureintro
    exact hZ.2 j (by rw [Hl]; rfl)

/-- A chain lower bound: boot-image entries, or a valid certificate. -/
theorem memModel_chainLb (σ : MState) (h : CPU) (t : Nat) (j : CPU) (τ : Nat) :
    memModelAt E σ ∗ chainLbAt E h t j τ ⊢@{IProp GF}
      ⌜t = 0 ∨ ChainCert.valid (chainEnv (hlc := hlc) (GF := GF) σ) ⟨h, t, j, τ⟩⌝ := by
  iintro ⟨Hmm, Hlb⟩
  unfold chainLbAt
  icases Hlb with ⟨%h0 | ⟨%t0, %τ0, %hle, Hc⟩⟩
  · ipureintro
    rcases h0 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (Or.inl h0)
  · ihave %hv := memModel_chainCert E σ ⟨h, t0, j, τ0⟩ $$ [Hmm Hc]
    · iframe Hmm Hc
    ipureintro
    exact Or.inr (ChainCert.valid_le hv hle.1 hle.2)

/-- The certificate map's two halves, opened (shared by the two issues). -/
theorem memModel_chainIssueKey (σ : MState) (k : Nat)
    (hv : ∀ Z : RegMapF Agent, certsOk (chainEnv (hlc := hlc) (GF := GF) σ) Z →
      certsOk (chainEnv (hlc := hlc) (GF := GF) σ) (Iris.Std.PartialMap.insert Z k (0 : Agent))) :
    memModelAt E σ ⊢@{IProp GF} |==> (memModelAt E σ ∗ ∃ v : Agent, E.chainName ↪◯MAP[k]{.discard} v) := by
  unfold memModelAt rsvModelAt chainModelAt
  iintro ⟨Htop, Hauth, Hviews, Hresv, %hmm, Hreg, Hh, %Z, HZ, %hZ, #Hels⟩
  cases hk : get? Z k with
  | some v =>
    imodintro
    iframe Htop Hauth Hviews Hresv Hreg Hh
    isplitl [HZ]
    · isplit
      · ipureintro; exact hmm
      · iexists Z
        iframe HZ Hels
        ipureintro; exact hZ
    · iexists v
      unfold chainElemsAt
      iapply Hels $$ %k %v %hk
  | none =>
    imod ghost_map_insert_persist k (0 : Agent) hk $$ HZ with ⟨HZ, #Hc⟩
    imodintro
    iframe Htop Hauth Hviews Hresv Hreg Hh
    isplitl [HZ]
    · isplit
      · ipureintro; exact hmm
      · iexists (Iris.Std.PartialMap.insert Z k (0 : Agent))
        iframe HZ
        isplit
        · ipureintro; exact hv Z hZ
        · unfold chainElemsAt
          imodintro
          iintro %k' %v' %hk'
          by_cases he : k = k'
          · subst he
            rw [LawfulPartialMap.get?_insert_eq rfl] at hk'
            cases hk'
            iexact Hc
          · rw [LawfulPartialMap.get?_insert_ne he] at hk'
            iapply Hels $$ %k' %v' %hk'
    · iexists 0
      iexact Hc

/-- A valid certificate may be issued. -/
theorem memModel_certIssue (σ : MState) (c : ChainCert)
    (hv : c.valid (chainEnv (hlc := hlc) (GF := GF) σ)) :
    memModelAt E σ ⊢@{IProp GF} |==> (memModelAt E σ ∗ chainCertAt E c) := by
  unfold chainCertAt
  exact memModel_chainIssueKey E σ c.key (fun Z hZ => certsOk_insert hZ c hv 0)

/-- A hart past the gate may be issued its gate. -/
theorem memModel_gateIssue (σ : MState) (j : CPU) (hv : gateOk (chainEnv (hlc := hlc) (GF := GF) σ) j) :
    memModelAt E σ ⊢@{IProp GF} |==> (memModelAt E σ ∗ gatePassedAt E j) := by
  iintro Hmm
  imod memModel_chainIssueKey E σ (gateKey j) (fun Z hZ => certsOk_insertGate hZ j hv 0) $$ Hmm with ⟨Hmm, Hg⟩
  imodintro
  iframe Hmm
  unfold gatePassedAt
  iright
  iexact Hg

/-- **The release's record**: a chain lower bound to the releasing hart `A`,
re-dated to the next position of the order. -/
theorem memModel_chainRetime (σ : MState) (h : CPU) (t : Nat) (A : CPU) (τ : Nat)
    (hown : h = A → t ≤ σ.top) :
    memModelAt E σ ∗ chainLbAt E h t A τ ⊢@{IProp GF}
      |==> (memModelAt E σ ∗ chainLbAt E h t A (σ.top + 1)) := by
  iintro ⟨Hmm, #Hlb⟩
  ihave %hmm := memModel_mmOk E σ $$ Hmm
  ihave %hv := memModel_chainLb E σ h t A τ $$ [Hmm Hlb]
  · iframe Hmm Hlb
  rcases hv with h0 | hv
  · subst h0
    imodintro
    iframe Hmm
    iapply chainLbAt_0
  · have hv' : ChainCert.valid (chainEnv (hlc := hlc) (GF := GF) σ) ⟨h, t, A, σ.top + 1⟩ :=
      ChainCert.valid_retime hv
        (fun b H e hb he => by
          have := ((hmm.1 b H hb).2 e he).1
          simp only [MState.top]
          omega)
        (fun hh => by have := hown hh; omega)
    imod memModel_certIssue E σ _ hv' $$ Hmm with ⟨Hmm, #Hc⟩
    imodintro
    iframe Hmm
    iapply chainLbAt_of_cert E _ $$ Hc

/-- **The acquire's extension**: the lock byte `b`'s history headed by the
winning AMO's entry `⟨a, B, va⟩` (the newest entry of the memory) over the
release entry `⟨r, A, 0⟩` over a nonzero entry; a lower bound to `A` before
`r` is one to `B` past `a`, given `B`'s gate. -/
theorem memModel_chainHop (σ : MState) (b : PAddr) (A B : CPU) (r a : Nat) (va : BitVec 8) (e0 : HEnt)
    (H2 : Hist) (hb : σ.mem[b]? = some (⟨a, hartAgent B, va⟩ :: ⟨r, hartAgent A, 0⟩ :: e0 :: H2))
    (hva : va ≠ 0) (he0 : e0.v ≠ 0) (hlk : rsvLockByte (hlc := hlc) (GF := GF) b) (ha : σ.top = a)
    (h : CPU) (t : Nat) :
    memModelAt E σ ∗ gatePassedAt E B ∗ chainLbAt E h t A r ⊢@{IProp GF}
      |==> (memModelAt E σ ∗ chainLbAt E h t B (a + 1)) := by
  iintro ⟨Hmm, #Hg, #Hlb⟩
  ihave %hmm := memModel_mmOk E σ $$ Hmm
  ihave %hrsv := memModel_rsvOk E σ $$ Hmm
  ihave %hg := memModel_gate E σ B $$ [Hmm Hg]
  · iframe Hmm Hg
  ihave %hv := memModel_chainLb E σ h t A r $$ [Hmm Hlb]
  · iframe Hmm Hlb
  rcases hv with h0 | hv
  · subst h0
    imodintro
    iframe Hmm
    iapply chainLbAt_0
  · have hv' : ChainCert.valid (chainEnv (hlc := hlc) (GF := GF) σ) ⟨h, t, B, a + 1⟩ :=
      ChainCert.valid_hop hv hlk (syncHop_of_head hb hva he0)
        (fun b' H e hb' he => by
          have := ((hmm.1 b' H hb').2 e he).1
          simp only [MState.top] at ha this
          omega)
        (pubOneShot_of_rsv hrsv) hg
    imod memModel_certIssue E σ _ hv' $$ Hmm with ⟨Hmm, #Hc⟩
    imodintro
    iframe Hmm
    iapply chainLbAt_of_cert E _ $$ Hc

end era

end MachCSL
