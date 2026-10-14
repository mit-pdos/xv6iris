/-
Weak: **W9a (B) B3 + B4 — the `ret` demotion and the announced word** (plan
`notes/weak-allocproc-plan.md` rev 51 §C "W9a (B)", parts (B3) and (B4); spike
`notes/W9aB-spike.md` §0.2, §3; rulings [OWN.60], [OWN.68]).  Lean-only, no Rocq twin.

**B3 (s3) — DEMOTE `kexec+0x1b4` from the claim (§1–§3).**  The spike found ONE certified walk
that executes a `ret` before it pins: `kexec+0x1b4` (`0x80004b24`, `ld s5,72(a0)`, table row
`PDep uvmalloc+0xe true`, `Weak/KernelPins.lean:1444`).  A `ret` in a descended callee is
aligned with the walk only if the reloaded `ra` equals the walk's return-stack pc — a frame
fact.  Instead of proving it, the claim's pin set `pinsW9a` is the table `pins` with that ONE
row turned into `PResidue` (the classified residue W9b / W8 (ii)–(iii) handle):
  §1  a generic visited-set DFS `WeakRvwmoPinBridge4.gdfs` over any step function, and its
      soundness (`gdfsSound`, the `pdfsSoundAux` invariant restated generically);
  §2  `retFreeb own pc`: the DFS over `pstepNR` (= `pstep`, but a `ret` state FAILS) — every
      walk state reachable from the load along ANY arms is not a `ret` (`retFreeSound`, stated
      on PinBridge3's `preach`); the per-chunk re-check `retFree0`…`retFree16`
      (`decide +kernel`): every walk-certifying row (`PDep`/`PCtrl`/`PFence`) but the demoted
      one is `ret`-free; and the demoted one really is not (`retSiteHasRet`);
  §3  `pinsW9a` and what changed: the pcs are the table's (`pinsW9aPcs`, so `pinsCover`'s
      census stays exhaustive), every row re-checks (`pinsW9aPinnedb`), the certifying rows are
      the table's MINUS the one demoted row (`pinsW9aCertErase`; counts `pinsW9aCensus`:
      walk-certifying 470 → 469, `own = true` 58 → 57, residue `PCall`+`PResidue` 182 → 183),
      and **`pinsW9aRetFree`**: at a walk-certifying row of `pinsW9a`, NO state the alignment
      can reach is a `ret` (`reachesANoRet`, `psitesANoRet`) — so B5's alignment owes no
      frame-`ret` fact on any claimed site.
  WHAT THE DEMOTION REMOVES: exactly one site, `(kexec+0x1b4, PDep uvmalloc+0xe true)`, from the
  segPinC-certified set; it joins the residue.  The theorem statements are UNCHANGED: no
  statement of the tree mentions `pins` (T-alloc-RVWMO / `l2ClaimAtC` / W11 (v) quantify
  segments, not table rows; the only other reader, `PinHoldingCtrl.holdingCtrlTableResidue`, is
  a fact about one other row).

**B4 — the announced word = `kword pc` from the fetch clause (§4–§6).**
  §4  the image on the text: `kTextImg im` (every text byte is `kbyte`), PROVED for the boot
      image (`kTextImgBoot`: `imgZ bootImage`, `MachCSL.bootImage_get?`);
  §5  the FETCH CLAUSE gives text bytes: `kFetchText em` — every administrative `LIFetch` item's
      byte at a text address is `kbyte` — from the PINNED clause (`kFetchTextOfPin`,
      `emFetchImg`) and from the ZIFENCEI clause + the pristine text (`kFetchTextOfZif`,
      `emZifencei` + `kTextUnwritten G`: no graph write to a text byte — (Z1) then forces
      timestamp 0); per bundle: `xv6ConfSFetchText` (pinned), `xv6ConfSZFetchText` (G6-2's
      `xv6ConfSZ`);
  §6  the bytes give the word / role, per Sail fetch arm (`LeanRV64D/Fetch.lean:233-288`,
      `Step.lean:335-404`): a 4-byte ifetch read `w` (the node clause's `nthByte w j`, Lean
      `WeakEvInst.pnodeStep`'s i-cache arm) is `kword pc` (`kwordOfBytes`); `F_Base w` announces
      `krole pc`'s word (`annRoleBase4`); `F_RVC (extractLsb w 15 0)` announces a word whose
      ROLE is `krole pc` (`annRoleRvc4`; the high half of `kword pc` is the next instruction's,
      harmless: `depsOfBitsLo16`, a compressed role reads bits ≤ 15 only); the 2-aligned arm's
      halfwords (`annRoleRvc`, `annRoleBase22`: `ihi +++ ilo`).  Composed with §5:
      `annRoleFetch4`, `annRoleFetch2` — the role B1's glue needs (`dfScanGrpOkb`'s
      `krole pc = ro` with `ro = depsOfIb ib.ibBits`).

**What B4 does NOT prove (named for B5; spec-first in the report).**  (r1) Sail's `fetch` passes
the i-cache read's value to `instr_announce` in one of the four arm shapes above (the value
chain `fetch` → `fetch_bytes` → `mem_read` → `read_ram`); (r2) the fetch's address IS the pc:
`LIFetch (paZ pa)` with `pa = translateAddr (Virtaddr PC)` — on kernel text `pa = PC` needs the
kernel page table's identity map (S-mode, Sv39) or `satp` bare; (r3) `kTextUnwritten` at the
graph, from `xv6TextAdequacy_closed` through the realization (W11's hull: `MachOfPf.noWriteOfPristine`
is the pf-run form).  (r4) the image premise is discharged here (`kTextImgBoot`).

Spec: no trusted text.  Sail (`Fetch.lean`, `Step.lean`) is the reference for the arms; the
Zifencei clause is G1's `gzFetch` (unchanged); RVWMO/riscv.cat have no fetch model; a `ret` is
not an ordering point anywhere.  FAITHFUL (B3 shrinks the claimed PIN SET, not a theorem).
Every Lean-only helper is file-qualified `WeakRvwmoPinBridge4.*`.
-/
import Weak.WeakRvwmoPinBridge3
import Weak.KernelPins
import Weak.GraphFabConf

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open KernelPinsDef
open WeakRvwmoPinBridge3 (preach)

/-! # 1. A generic visited-set DFS and its soundness -/

/-- `pdfs` over an arbitrary step function. -/
def WeakRvwmoPinBridge4.gdfs (st : PState → Option (List PState)) :
    Nat → List PState → List PState → Bool
  | 0, _, _ => false
  | f + 1, seen, work =>
      match work with
      | [] => true
      | s :: w' =>
          if seen.any (pstateEqb s) then WeakRvwmoPinBridge4.gdfs st f seen w'
          else match st s with
            | none => false
            | some ns => WeakRvwmoPinBridge4.gdfs st f (s :: seen) (ns ++ w')

/-- `preach` over an arbitrary step function. -/
inductive WeakRvwmoPinBridge4.greach (st : PState → Option (List PState)) :
    PState → PState → Nat → Prop where
  | refl (s : PState) : WeakRvwmoPinBridge4.greach st s s 0
  | step (s s' x : PState) (l : List PState) (n : Nat) :
      st s = some l → s' ∈ l → WeakRvwmoPinBridge4.greach st s' x n →
      WeakRvwmoPinBridge4.greach st s x (n + 1)

open WeakRvwmoPinBridge4 (gdfs greach)

theorem WeakRvwmoPinBridge4.gdfsUnfold (st : PState → Option (List PState)) (f : Nat)
    (seen : List PState) (s : PState) (w' : List PState) :
    gdfs st (f + 1) seen (s :: w')
      = if seen.any (pstateEqb s) then gdfs st f seen w'
        else match st s with
          | none => false
          | some ns => gdfs st f (s :: seen) (ns ++ w') := rfl

/-- THE DFS INVARIANT (`pdfsSoundAux`, any step function). -/
theorem WeakRvwmoPinBridge4.gdfsSoundAux (st : PState → Option (List PState)) :
    ∀ (f : Nat) (seen work : List PState), gdfs st f seen work = true →
    ∀ s, s ∈ work → ∀ x n, greach st s x n → st x = none →
      ∃ y m, y ∈ seen ∧ m ≤ n ∧ greach st y x m := by
  intro f
  induction f with
  | zero => intro seen work h; exact absurd h Bool.false_ne_true
  | succ f ih =>
    intro seen work h
    cases work with
    | nil => intro s hs; cases hs
    | cons s0 w' =>
      rw [WeakRvwmoPinBridge4.gdfsUnfold] at h
      by_cases hseen : seen.any (pstateEqb s0) = true
      · rw [if_pos hseen] at h
        intro s hs x n hr hbad
        rcases List.mem_cons.mp hs with rfl | hs
        · obtain ⟨y, hy, he⟩ := List.any_eq_true.mp hseen
          rw [WeakRvwmoPinBridge3.pstateEqbEq _ _ he] at hr
          exact ⟨y, n, hy, Nat.le_refl n, hr⟩
        · exact ih seen w' h s hs x n hr hbad
      · rw [if_neg hseen] at h
        cases hps : st s0 with
        | none => rw [hps] at h; exact absurd h Bool.false_ne_true
        | some ns =>
          rw [hps] at h
          have ih' := ih (s0 :: seen) (ns ++ w') h
          have key : ∀ n x, greach st s0 x n → st x = none →
              ∃ y m, y ∈ seen ∧ m ≤ n ∧ greach st y x m := by
            intro n
            induction n using Nat.strongRecOn with
            | _ n ihn =>
              intro x hr hbad
              cases hr with
              | refl => rw [hps] at hbad; cases hbad
              | step _ s' _ l n' hp hm hr' =>
                rw [hps] at hp
                cases hp
                obtain ⟨y, m, hy, hmn, hyr⟩ :=
                  ih' s' (List.mem_append_left _ hm) x n' hr' hbad
                rcases List.mem_cons.mp hy with rfl | hy
                · obtain ⟨y', m', hy', hm', hyr'⟩ := ihn m (by omega) x hyr hbad
                  exact ⟨y', m', hy', by omega, hyr'⟩
                · exact ⟨y, m, hy, by omega, hyr⟩
          intro s hs x n hr hbad
          rcases List.mem_cons.mp hs with rfl | hs
          · exact key n x hr hbad
          · obtain ⟨y, m, hy, hmn, hyr⟩ := ih' s (List.mem_append_right _ hs) x n hr hbad
            rcases List.mem_cons.mp hy with rfl | hy
            · obtain ⟨y', m', hy', hm', hyr'⟩ := key m x hyr hbad
              exact ⟨y', m', hy', by omega, hyr'⟩
            · exact ⟨y, m, hy, hmn, hyr⟩

/-- **`gdfs` IS SOUND**: an accepted start has no reachable failing state. -/
theorem WeakRvwmoPinBridge4.gdfsSound (st : PState → Option (List PState)) (f : Nat)
    (s0 : PState) :
    gdfs st f [] [s0] = true → ∀ x n, greach st s0 x n → st x ≠ none := by
  intro h x n hr hbad
  obtain ⟨y, _, hy, _⟩ :=
    WeakRvwmoPinBridge4.gdfsSoundAux st f [] [s0] h s0 (List.mem_singleton_self _) x n hr hbad
  cases hy

/-! # 2. `ret`-freedom of a walk -/

/-- A `ret` word (`jalr x0, 0(ra)` / `c.jr ra`). -/
def WeakRvwmoPinBridge4.isRet : Kflow → Bool
  | .FLret => true
  | _ => false

/-- The checker's step, except that a `ret` state FAILS. -/
def WeakRvwmoPinBridge4.pstepNR (own : Bool) (s : PState) : Option (List PState) :=
  if WeakRvwmoPinBridge4.isRet (kflowOf s.psPc) then none else pstep own s

open WeakRvwmoPinBridge4 (isRet pstepNR)

/-- **THE `ret`-FREE CHECK**: the all-paths DFS from the load, failing at every `ret`. -/
def retFreeb (own : Bool) (pc : Int) : Bool :=
  gdfs (pstepNR own) pdfsFuel [] [pinStart pc]

theorem WeakRvwmoPinBridge4.isRetFalse (k : Kflow) : isRet k = false → k ≠ .FLret := by
  intro h e; subst e; cases h

/-- A state from which every `pstepNR`-path is non-failing reaches no `ret` along ANY `pstep`
arms. -/
theorem WeakRvwmoPinBridge4.noRetOfNR (own : Bool) (s x : PState) (n : Nat) :
    preach own s x n →
    (∀ y m, greach (pstepNR own) s y m → pstepNR own y ≠ none) →
    kflowOf x.psPc ≠ .FLret := by
  intro hr
  induction hr with
  | prRefl s =>
    intro hok
    have h0 := hok s 0 (.refl s)
    unfold pstepNR at h0
    cases hk : isRet (kflowOf s.psPc) with
    | true => rw [hk] at h0; exact absurd rfl h0
    | false => exact WeakRvwmoPinBridge4.isRetFalse _ hk
  | prStep s s' x l n hp hm _ ih =>
    intro hok
    have h0 := hok s 0 (.refl s)
    have hnr : pstepNR own s = some l := by
      unfold pstepNR at h0 ⊢
      cases hk : isRet (kflowOf s.psPc) with
      | true => rw [hk] at h0; exact absurd rfl h0
      | false => simpa using hp
    exact ih (fun y m hy => hok y (m + 1) (.step s s' y l m hnr hm hy))

/-- **`retFreeb` IS SOUND**: when the check accepts a load site, no state reachable from the
walk's start along ANY arms is a `ret`. -/
theorem retFreeSound (own : Bool) (pc : Int) :
    retFreeb own pc = true → ∀ x n, preach own (pinStart pc) x n → kflowOf x.psPc ≠ .FLret :=
  fun h x n hr =>
    WeakRvwmoPinBridge4.noRetOfNR own _ x n hr
      (WeakRvwmoPinBridge4.gdfsSound (pstepNR own) pdfsFuel (pinStart pc) h)

/-- The demoted site: `kexec+0x1b4` (`0x80004b24`, `ld s5,72(a0)`). -/
def retSitePc : Int := (KernelSyms.«kexec» : Int) + 0x1b4

/-- Its table row: `PDep` at `uvmalloc+0xe` (`sd s5,24(sp)`), with the sp-frame assumption. -/
def retSiteRow : Int × Pin := (retSitePc, .PDep ((KernelSyms.«uvmalloc» : Int) + 0xe) true)

theorem WeakRvwmoPinBridge4.retSitePcVal : retSitePc = 0x80004b24 := by decide

theorem retSiteRowMem : retSiteRow ∈ pins := by decide +kernel

/-- ... and its walk REALLY executes a `ret` before it pins: the demotion is needed. -/
theorem retSiteHasRet : retFreeb true retSitePc = false := by decide +kernel

/-- A walk-certifying witness: its `own` bit, if it certifies through the all-paths walk. -/
def WeakRvwmoPinBridge4.walkOwn : Pin → Option Bool
  | .PDep _ own | .PCtrl _ own | .PFence _ own => some own
  | _ => none

/-- The per-row check: a walk-certifying row other than the demoted one is `ret`-free. -/
def WeakRvwmoPinBridge4.retFreeOk (p : Int × Pin) : Bool :=
  match WeakRvwmoPinBridge4.walkOwn p.2 with
  | some own => (p.1 == retSitePc) || retFreeb own p.1
  | none => true

open WeakRvwmoPinBridge4 (walkOwn retFreeOk)

theorem retFree0 : pins0.all retFreeOk = true := by decide +kernel
theorem retFree1 : pins1.all retFreeOk = true := by decide +kernel
theorem retFree2 : pins2.all retFreeOk = true := by decide +kernel
theorem retFree3 : pins3.all retFreeOk = true := by decide +kernel
theorem retFree4 : pins4.all retFreeOk = true := by decide +kernel
theorem retFree5 : pins5.all retFreeOk = true := by decide +kernel
theorem retFree6 : pins6.all retFreeOk = true := by decide +kernel
theorem retFree7 : pins7.all retFreeOk = true := by decide +kernel
theorem retFree8 : pins8.all retFreeOk = true := by decide +kernel
theorem retFree9 : pins9.all retFreeOk = true := by decide +kernel
theorem retFree10 : pins10.all retFreeOk = true := by decide +kernel
theorem retFree11 : pins11.all retFreeOk = true := by decide +kernel
theorem retFree12 : pins12.all retFreeOk = true := by decide +kernel
theorem retFree13 : pins13.all retFreeOk = true := by decide +kernel
theorem retFree14 : pins14.all retFreeOk = true := by decide +kernel
theorem retFree15 : pins15.all retFreeOk = true := by decide +kernel
theorem retFree16 : pins16.all retFreeOk = true := by decide +kernel

/-- Every walk-certifying row of the table but the demoted one is `ret`-free. -/
theorem retFreeAll : pins.all retFreeOk = true := by
  simp only [pins, List.all_append, Bool.true_and,
    retFree0, retFree1, retFree2, retFree3, retFree4, retFree5, retFree6, retFree7, retFree8,
    retFree9, retFree10, retFree11, retFree12, retFree13, retFree14, retFree15, retFree16]

/-! # 3. The claim's pin set `pinsW9a` -/

/-- Demote the one `ret` row to the residue. -/
def WeakRvwmoPinBridge4.demote (p : Int × Pin) : Int × Pin :=
  if p.1 == retSitePc then (p.1, .PResidue) else p

open WeakRvwmoPinBridge4 (demote)

/-- **THE CLAIM'S PIN SET** (B3 (s3)): the table with `kexec+0x1b4` demoted to `PResidue`. -/
def pinsW9a : List (Int × Pin) := pins.map demote

theorem WeakRvwmoPinBridge4.demoteFst (p : Int × Pin) : (demote p).1 = p.1 := by
  unfold demote; split <;> rfl

/-- Same sites, same order: `pinsCover`'s census stays exhaustive for `pinsW9a`. -/
theorem pinsW9aPcs : pinsW9a.map Prod.fst = pinPcs := by
  unfold pinsW9a pinPcs
  rw [List.map_map]
  exact List.map_congr_left (fun p _ => WeakRvwmoPinBridge4.demoteFst p)

theorem WeakRvwmoPinBridge4.retSiteResidue :
    pinnedb pinFuel retSitePc .PResidue = true := by decide +kernel

/-- Every row of `pinsW9a` survives the re-check. -/
theorem pinsW9aPinnedb : pinsW9a.all (fun p => pinnedb pinFuel p.1 p.2) = true := by
  unfold pinsW9a
  rw [List.all_map, List.all_eq_true]
  intro p hp
  have h := List.all_eq_true.mp imagePinnedb p hp
  show pinnedb pinFuel (demote p).1 (demote p).2 = true
  unfold demote
  split
  · next he =>
    rw [beq_iff_eq] at he
    rw [he]; exact WeakRvwmoPinBridge4.retSiteResidue
  · exact h

/-- **WHAT THE DEMOTION REMOVES**: the certifying rows of `pinsW9a` are the table's minus the
ONE demoted row. -/
theorem pinsW9aCertErase :
    pinsW9a.filter (fun p => pinCertifies p.2) =
      (pins.filter (fun p => pinCertifies p.2)).erase retSiteRow := by decide +kernel

/-- The census after the demotion: walk-certifying 469 (was 470), `own = true` 57 (was 58),
residue `PCall` + `PResidue` 183 (was 182). -/
theorem pinsW9aCensus :
    (pinsW9a.filter (fun p => (walkOwn p.2).isSome)).length = 469 ∧
    (pins.filter (fun p => (walkOwn p.2).isSome)).length = 470 ∧
    (pinsW9a.filter (fun p => pinOwned p.2)).length = 57 ∧
    (pins.filter (fun p => pinOwned p.2)).length = 58 ∧
    (pinsW9a.filter (fun p => !pinCertifies p.2)).length = 183 ∧
    (pins.filter (fun p => !pinCertifies p.2)).length = 182 := by decide +kernel

/-- A certifying row of `pinsW9a` is a row of the table: nothing new is certified. -/
theorem pinsW9aSub (p : Int × Pin) :
    p ∈ pinsW9a → pinCertifies p.2 = true → p ∈ pins ∧ p.1 ≠ retSitePc := by
  unfold pinsW9a
  intro hp hc
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  unfold demote at hc ⊢
  split at hc
  · cases hc
  · next he =>
    rw [if_neg he]
    exact ⟨hq, fun e => he (beq_iff_eq.mpr e)⟩

/-- **B3 HEADLINE**: at a walk-certifying row of `pinsW9a`, no walk state reachable from the load
along ANY arms is a `ret` — the claimed pin set owes NO frame-`ret` fact. -/
theorem pinsW9aRetFree (pc pc' : Int) (own : Bool) (w : Pin) :
    (pc, w) ∈ pinsW9a → (w = .PDep pc' own ∨ w = .PCtrl pc' own ∨ w = .PFence pc' own) →
    ∀ x n, preach own (pinStart pc) x n → kflowOf x.psPc ≠ .FLret := by
  intro hm hw
  have hc : pinCertifies w = true := by
    rcases hw with rfl | rfl | rfl <;> rfl
  obtain ⟨hp, hne⟩ := pinsW9aSub (pc, w) hm hc
  have hok := List.all_eq_true.mp retFreeAll (pc, w) hp
  have hwo : walkOwn w = some own := by
    rcases hw with rfl | rfl | rfl <;> rfl
  unfold retFreeOk at hok
  rw [hwo] at hok
  simp only [Bool.or_eq_true, beq_iff_eq] at hok
  rcases hok with e | h
  · exact absurd e hne
  · exact retFreeSound own pc h

/-- ... so the any-path alignment (`reachesA`) never stands at a `ret`. -/
theorem reachesANoRet (pc pc' : Int) (own : Bool) (w : Pin) (mid : List Eitem) (s : PState) :
    (pc, w) ∈ pinsW9a → (w = .PDep pc' own ∨ w = .PCtrl pc' own ∨ w = .PFence pc' own) →
    reachesA own (pinStart pc) mid s → kflowOf s.psPc ≠ .FLret := by
  intro hm hw hr
  obtain ⟨n, hn⟩ := WeakRvwmoPinBridge3.preachOfReachesA own _ _ _ hr
  exact pinsW9aRetFree pc pc' own w hm hw s n hn

/-- ... nor does the site oracle `psitesA`. -/
theorem psitesANoRet (pc pc' : Int) (own : Bool) (w : Pin) (base pre : List Eitem) (s : PState) :
    (pc, w) ∈ pinsW9a → (w = .PDep pc' own ∨ w = .PCtrl pc' own ∨ w = .PFence pc' own) →
    psitesA pc own base pre s → kflowOf s.psPc ≠ .FLret := by
  rintro hm hw ⟨mid, -, hr⟩
  exact reachesANoRet pc pc' own w mid s hm hw hr

/-! # 4. The image on the kernel text -/

/-- The image holds the tracked text bytes (`kbyte`) on `[textLo, textHi)`. -/
def kTextImg (im : Image) : Prop :=
  ∀ a : Int, textLo ≤ a → a < textHi → im a = some (BitVec.ofNat 8 (kbyte a))

/-- A text byte is a byte. -/
theorem WeakRvwmoPinBridge4.kbyteLt (a : Int) : kbyte a < 256 := by
  unfold kbyte KernelElf.elfByte KernelElf.rowByte
  split
  · exact Nat.mod_lt _ (by decide)
  · decide

/-- **THE BOOT IMAGE IS THE TRACKED TEXT** on `[textLo, textHi)`. -/
theorem kTextImgBoot : kTextImg (imgZ bootImage) := by
  intro a h1 h2
  have hlo : textLo = 0x80000000 := rfl
  have hhi : textHi = 0x80006126 := rfl
  rw [hlo] at h1
  rw [hhi] at h2
  have hz : (zPa a).toNat = a.toNat := by
    unfold zPa
    rw [BitVec.toNat_ofInt]
    have : a % (2 ^ 64 : Nat) = a := Int.emod_eq_of_lt (by omega) (by omega)
    rw [this]
  unfold imgZ
  rw [bootImage_get?, if_pos (by unfold inRam ramBase ramEnd; omega)]
  refine congrArg some ?_
  unfold bootByte kbyte
  rw [if_pos (by unfold KernelElf.elfBase KernelElf.elfEnd; omega),
    if_pos (by rw [hlo, hhi]; omega)]
  have he : (zPa a).toNat - KernelElf.elfBase = (a - (KernelElf.elfBase : Int)).toNat := by
    rw [hz]; unfold KernelElf.elfBase; omega
  rw [he]

/-! # 5. The fetch clause gives text bytes -/

/-- Every administrative fetch item's byte at a text address is the tracked text byte. -/
def kFetchText (em : Hemission) : Prop :=
  ∀ (n : Nat) (base : Int) (tvs : List (Nat × BitVec 8)),
    em.emItems[n]? = some (Wlabel.LIFetch base tvs, none) →
    ∀ j : Nat, j < tvs.length → textLo ≤ base + (j : Int) → base + (j : Int) < textHi →
      (tvs.map Prod.snd)[j]? = some (BitVec.ofNat 8 (kbyte (base + (j : Int))))

/-- **PINNED** (`emFetchImg`, the stage-C clause). -/
theorem kFetchTextOfPin (im : Image) (em : Hemission) :
    kTextImg im → emFetchImg im em → kFetchText em := by
  intro hti hpin n base tvs hn j hj h1 h2
  have hl : Wlabel.LIFetch base tvs ∈ emLabels em := by
    unfold emLabels
    exact List.mem_map.2 ⟨_, List.mem_of_getElem? hn, rfl⟩
  obtain ⟨-, himg⟩ := hpin _ hl
  rw [← himg j hj, hti _ h1 h2]

/-- No write of the graph touches a text byte (the graph form of the pristine text). -/
def kTextUnwritten (G : Gexec) : Prop :=
  ∀ (w : Geid) (a : Int) (v : BitVec 8), textLo ≤ a → a < textHi → ¬ gwritesByte G w a v

/-- **ZIFENCEI** (`emZifencei` + the pristine text): (Z1) answers the byte from the log at the
fetch's timestamp; a non-zero timestamp names a write of that text byte, so it is 0 and the
byte is the image's. -/
theorem kFetchTextOfZif (G : Gexec) (i : Nat) (em : Hemission) :
    kTextImg G.gxImg → kTextUnwritten G → emZifencei G i em → kFetchText em := by
  intro hti hnw hz n base tvs hn j hj h1 h2
  have hg := hz n base tvs hn
  obtain ⟨⟨t, v⟩, htv⟩ : ∃ p, tvs[j]? = some p := ⟨_, List.getElem?_eq_getElem hj⟩
  obtain ⟨hv, -, -⟩ := hg j t v htv
  rw [List.getElem?_map, htv]
  cases t with
  | zero =>
    rw [logByte0, hti _ h1 h2] at hv
    simp only [Option.map_some]
    exact hv.symm
  | succ k =>
    rw [logByteS, GraphFetchRetime.gwlogLookup] at hv
    exfalso
    cases hw : (gwrites G)[k]? with
    | none => rw [hw] at hv; cases hv
    | some w =>
      rw [hw] at hv
      cases hm : WeakRvwmoLin.gmsg G w with
      | none => simp [hm] at hv
      | some m =>
        simp only [Option.bind_some, hm] at hv
        exact hnw w _ v h1 h2 (gmsgByteInv G w m _ v hm hv)

/-- The per-row fetch fact of a PINNED bundle. -/
theorem xv6ConfSFetchText (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GT : GfexecT) :
    xv6ConfS boot d0 im nh GT → kTextImg im →
    ∀ (i : Nat) (row : List Lbl), GT.gfGd.gtG.gxProg[i]? = some row →
      ∃ (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
        hartConff i row (boot i) dvi dvo tq em ∧ kFetchText em := by
  rintro ⟨himg, -, fab, -, -, -, hrows⟩ hti i row hrow
  obtain ⟨em, dvi, dvo, tq, hem, -, -, hpin, -⟩ := hrows i row hrow
  exact ⟨em, dvi, dvo, tq, hem, kFetchTextOfPin _ em (himg ▸ hti) hpin⟩

/-- The per-row fetch fact of the ZIFENCEI bundle (W5d-G G6-2's `xv6ConfSZ`), given the
pristine text at the graph. -/
theorem xv6ConfSZFetchText (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GT : GfexecT) :
    xv6ConfSZ boot d0 im nh GT → kTextImg im → kTextUnwritten GT.gfGd.gtG →
    ∀ (i : Nat) (row : List Lbl), GT.gfGd.gtG.gxProg[i]? = some row →
      ∃ (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
        hartConff i row (boot i) dvi dvo tq em ∧ kFetchText em := by
  rintro ⟨himg, -, fab, -, -, -, hrows⟩ hti hnw i row hrow
  obtain ⟨em, dvi, dvo, tq, hem, -, -, ⟨hz, -⟩, -⟩ := hrows i row hrow
  exact ⟨em, dvi, dvo, tq, hem, kFetchTextOfZif _ i em (himg ▸ hti) hnw hz⟩

/-! # 6. The bytes give the announced word (per Sail fetch arm) -/

theorem WeakRvwmoPinBridge4.nthByteToNat {n : Nat} (w : BitVec (8 * n)) (j : Nat) :
    (nthByte w j).toNat = w.toNat / 2 ^ (8 * j) % 256 := by
  unfold nthByte
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- Four bytes of the text, little-endian, as a number. -/
theorem WeakRvwmoPinBridge4.toNatOfBytes4 (pc : Int) (w : BitVec 32) :
    (∀ j, j < 4 → nthByte (n := 4) w j = BitVec.ofNat 8 (kbyte (pc + (j : Int)))) →
    w.toNat = kw pc := by
  intro h
  have e : ∀ j : Nat, j < 4 → w.toNat / 2 ^ (8 * j) % 256 = kbyte (pc + (j : Int)) := by
    intro j hj
    have := congrArg BitVec.toNat (h j hj)
    rw [WeakRvwmoPinBridge4.nthByteToNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (WeakRvwmoPinBridge4.kbyteLt _)] at this
    exact this
  have e0 : w.toNat % 256 = kbyte pc := by have := e 0 (by decide); simpa using this
  have e1 : w.toNat / 256 % 256 = kbyte (pc + 1) := by have := e 1 (by decide); simpa using this
  have e2 : w.toNat / 65536 % 256 = kbyte (pc + 2) := by have := e 2 (by decide); simpa using this
  have e3 : w.toNat / 16777216 % 256 = kbyte (pc + 3) := by
    have := e 3 (by decide); simpa using this
  have hlt := w.isLt
  unfold kw
  omega

/-- **THE 4-BYTE READ IS `kword pc`**. -/
theorem kwordOfBytes (pc : Int) (w : BitVec 32) :
    (∀ j, j < 4 → nthByte (n := 4) w j = BitVec.ofNat 8 (kbyte (pc + (j : Int)))) →
    w = kword pc := by
  intro h
  apply BitVec.eq_of_toNat_eq
  rw [WeakRvwmoPinBridge4.toNatOfBytes4 pc w h]
  unfold kword
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := WeakRvwmoPinBridge4.kbyteLt pc
  have := WeakRvwmoPinBridge4.kbyteLt (pc + 1)
  have := WeakRvwmoPinBridge4.kbyteLt (pc + 2)
  have := WeakRvwmoPinBridge4.kbyteLt (pc + 3)
  unfold kw
  omega

/-- `ibits` at a field within bits `[15:0]` reads only the low halfword. -/
theorem WeakRvwmoPinBridge4.ibitsLo16 (w w' : BitVec 32) (h : w.toNat % 65536 = w'.toNat % 65536) :
    ∀ hi lo : Nat, lo ≤ hi → hi ≤ 15 → ibits w hi lo = ibits w' hi lo := by
  intro hi lo hlo hhi
  unfold ibits
  congr 1
  have key : ∀ x : Nat, (x >>> lo) % 2 ^ (hi - lo + 1) = ((x % 65536) >>> lo) % 2 ^ (hi - lo + 1) := by
    intro x
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
      Nat.testBit_shiftRight, show (65536 : Nat) = 2 ^ 16 from rfl, Nat.testBit_mod_two_pow]
    by_cases hi' : i < hi - lo + 1
    · have : lo + i < 16 := by omega
      simp [hi', this]
    · simp [hi']
  rw [key w.toNat, key w'.toNat, h]

/-- **A COMPRESSED ROLE READS THE LOW HALFWORD ONLY**: two words that agree on bits `[15:0]`, at
a compressed encoding (bits `[1:0] ≠ 3`), have the same role. -/
theorem depsOfBitsLo16 (w w' : BitVec 32) (h : w.toNat % 65536 = w'.toNat % 65536)
    (hc : ibits w 1 0 ≠ 3) : depsOfBits w = depsOfBits w' := by
  have e := WeakRvwmoPinBridge4.ibitsLo16 w w' h
  have e10 := e 1 0 (by decide) (by decide)
  have hlt : ibits w 1 0 < 4 := by
    unfold ibits
    have := Nat.mod_lt (w.toNat >>> 0) (show 0 < 2 ^ (1 - 0 + 1) by decide)
    omega
  have hge : 0 ≤ ibits w 1 0 := by unfold ibits; omega
  unfold depsOfBits
  rw [← e10]
  have hcase : ibits w 1 0 = 0 ∨ ibits w 1 0 = 1 ∨ ibits w 1 0 = 2 := by omega
  rcases hcase with h0 | h0 | h0 <;> rw [h0]
  · show depsOfC0 w = depsOfC0 w'
    unfold depsOfC0
    simp (disch := decide) only [e]
  · show depsOfC1 w = depsOfC1 w'
    unfold depsOfC1
    simp (disch := decide) only [e]
  · show depsOfC2 w = depsOfC2 w'
    unfold depsOfC2
    simp (disch := decide) only [e]

/-- Sail's `isRVC` is the role decoder's compressed test. -/
theorem WeakRvwmoPinBridge4.ibitsOfIsRvc (h : BitVec 16) :
    LeanRV64D.Functions.isRVC h = true → ibits (ibOfBvn h) 1 0 ≠ 3 := by
  unfold LeanRV64D.Functions.isRVC
  intro hr
  have hne : Sail.BitVec.extractLsb h 1 0 ≠ 3#2 := by
    intro e; rw [e] at hr; revert hr; decide
  have hx : (Sail.BitVec.extractLsb h 1 0).toNat = h.toNat % 4 := by
    unfold Sail.BitVec.extractLsb
    rw [BitVec.extractLsb_toNat, Nat.shiftRight_zero]
  have hn : h.toNat % 4 ≠ 3 := by
    intro e
    apply hne
    apply BitVec.eq_of_toNat_eq
    rw [hx, e]; rfl
  unfold ibits ibOfBvn
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.isLt (by decide)), Nat.shiftRight_zero]
  omega

/-- **`F_Base w`** (the 4-byte read, 4-aligned pc): the announced word IS `kword pc`. -/
theorem annRoleBase4 (pc : Int) (w : BitVec 32) :
    (∀ j, j < 4 → nthByte (n := 4) w j = BitVec.ofNat 8 (kbyte (pc + (j : Int)))) →
    ibOfBvn w = kword pc ∧ depsOfIb (ibAnn (ibOfBvn w)).ibBits = krole pc := by
  intro h
  have hw : ibOfBvn w = w := by
    apply BitVec.eq_of_toNat_eq
    unfold ibOfBvn
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt w.isLt]
  rw [hw, kwordOfBytes pc w h]
  exact ⟨rfl, rfl⟩

/-- **`F_RVC h`** (a compressed halfword at `pc`): the announced word's ROLE is `krole pc`. -/
theorem annRoleRvc (pc : Int) (h : BitVec 16) :
    h.toNat = kbyte pc + 256 * kbyte (pc + 1) → LeanRV64D.Functions.isRVC h = true →
    depsOfIb (ibAnn (ibOfBvn h)).ibBits = krole pc := by
  intro hv hr
  show depsOfBits (ibOfBvn h) = depsOfBits (kword pc)
  refine depsOfBitsLo16 _ _ ?_ (WeakRvwmoPinBridge4.ibitsOfIsRvc h hr)
  unfold ibOfBvn kword kw
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.isLt (by decide))]
  have := WeakRvwmoPinBridge4.kbyteLt pc
  have := WeakRvwmoPinBridge4.kbyteLt (pc + 1)
  have := WeakRvwmoPinBridge4.kbyteLt (pc + 2)
  have := WeakRvwmoPinBridge4.kbyteLt (pc + 3)
  omega

/-- Two text bytes, little-endian, as a halfword. -/
theorem WeakRvwmoPinBridge4.toNatOfBytes2 (pc : Int) (h : BitVec 16) :
    (∀ j, j < 2 → nthByte (n := 2) h j = BitVec.ofNat 8 (kbyte (pc + (j : Int)))) →
    h.toNat = kbyte pc + 256 * kbyte (pc + 1) := by
  intro hb
  have e : ∀ j : Nat, j < 2 → h.toNat / 2 ^ (8 * j) % 256 = kbyte (pc + (j : Int)) := by
    intro j hj
    have := congrArg BitVec.toNat (hb j hj)
    rw [WeakRvwmoPinBridge4.nthByteToNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (WeakRvwmoPinBridge4.kbyteLt _)] at this
    exact this
  have e0 : h.toNat % 256 = kbyte pc := by have := e 0 (by decide); simpa using this
  have e1 : h.toNat / 256 % 256 = kbyte (pc + 1) := by have := e 1 (by decide); simpa using this
  have hlt := h.isLt
  omega

/-- **`F_RVC (extractLsb w 15 0)`** (the 4-aligned fetch of a compressed instruction): the
announced halfword's ROLE is `krole pc`; only bytes 0 and 1 of the read are needed. -/
theorem annRoleRvc4 (pc : Int) (w : BitVec 32) :
    (∀ j, j < 2 → nthByte (n := 4) w j = BitVec.ofNat 8 (kbyte (pc + (j : Int)))) →
    LeanRV64D.Functions.isRVC (Sail.BitVec.extractLsb w 15 0) = true →
    depsOfIb (ibAnn (ibOfBvn (Sail.BitVec.extractLsb w 15 0))).ibBits = krole pc := by
  intro hb hr
  refine annRoleRvc pc _ ?_ hr
  have e : ∀ j : Nat, j < 2 → w.toNat / 2 ^ (8 * j) % 256 = kbyte (pc + (j : Int)) := by
    intro j hj
    have := congrArg BitVec.toNat (hb j hj)
    rw [WeakRvwmoPinBridge4.nthByteToNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (WeakRvwmoPinBridge4.kbyteLt _)] at this
    exact this
  have e0 : w.toNat % 256 = kbyte pc := by have := e 0 (by decide); simpa using this
  have e1 : w.toNat / 256 % 256 = kbyte (pc + 1) := by have := e 1 (by decide); simpa using this
  unfold Sail.BitVec.extractLsb
  rw [BitVec.extractLsb_toNat, Nat.shiftRight_zero]
  show w.toNat % 65536 = _
  omega

/-- **`F_Base (ihi +++ ilo)`** (a 4-byte instruction at `pc ≡ 2 mod 4`: two halfword reads): the
announced word IS `kword pc`. -/
theorem annRoleBase22 (pc : Int) (ilo ihi : BitVec 16) :
    ilo.toNat = kbyte pc + 256 * kbyte (pc + 1) →
    ihi.toNat = kbyte (pc + 2) + 256 * kbyte (pc + 2 + 1) →
    ibOfBvn (ihi ++ ilo) = kword pc ∧ depsOfIb (ibAnn (ibOfBvn (ihi ++ ilo))).ibBits = krole pc := by
  intro hlo hhi
  have hw : ibOfBvn (ihi ++ ilo) = kword pc := by
    apply BitVec.eq_of_toNat_eq
    unfold ibOfBvn kword kw
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_append,
      Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt ilo.isLt,
      Nat.shiftLeft_eq]
    have := WeakRvwmoPinBridge4.kbyteLt pc
    have := WeakRvwmoPinBridge4.kbyteLt (pc + 1)
    have := WeakRvwmoPinBridge4.kbyteLt (pc + 2)
    have := WeakRvwmoPinBridge4.kbyteLt (pc + 3)
    have e3 : pc + 2 + 1 = pc + 3 := by omega
    rw [e3] at hhi
    omega
  rw [hw]
  exact ⟨rfl, rfl⟩

/-- A fetch item's text byte, read through the i-cache node's value clause. -/
theorem WeakRvwmoPinBridge4.nthByteOfFetch {k : Nat} (em : Hemission) (hft : kFetchText em)
    (n : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) (w : BitVec (8 * k)) :
    em.emItems[n]? = some (Wlabel.LIFetch base tvs, none) → tvs.length = k →
    (∀ j : Nat, j < k → (tvs.map Prod.snd)[j]? = some (nthByte w j)) →
    ∀ j : Nat, j < k → textLo ≤ base + (j : Int) → base + (j : Int) < textHi →
      nthByte w j = BitVec.ofNat 8 (kbyte (base + (j : Int))) := by
  intro hn hlen hw j hj h1 h2
  have := hft n base tvs hn j (hlen ▸ hj) h1 h2
  rw [hw j hj] at this
  exact Option.some.inj this

/-- **B4 HEADLINE, 4-aligned arm**: at a fetch item `LIFetch pc tvs` of a `kFetchText` emission
(pinned or Zifencei bundle, §5) whose i-cache read returned `w` (the node clause), Sail's two
outcomes announce `krole pc`'s role: `F_Base w` (the word is `kword pc`), `F_RVC (w[15:0])`. -/
theorem annRoleFetch4 (em : Hemission) (hft : kFetchText em) (n : Nat) (pc : Int)
    (tvs : List (Nat × BitVec 8)) (w : BitVec 32) :
    em.emItems[n]? = some (Wlabel.LIFetch pc tvs, none) → tvs.length = 4 →
    (∀ j : Nat, j < 4 → (tvs.map Prod.snd)[j]? = some (nthByte (n := 4) w j)) →
    textLo ≤ pc →
    (pc + 3 < textHi → depsOfIb (ibAnn (ibOfBvn w)).ibBits = krole pc ∧ ibOfBvn w = kword pc) ∧
    (pc + 1 < textHi → LeanRV64D.Functions.isRVC (Sail.BitVec.extractLsb w 15 0) = true →
      depsOfIb (ibAnn (ibOfBvn (Sail.BitVec.extractLsb w 15 0))).ibBits = krole pc) := by
  intro hn hlen hw hlo
  have hb := WeakRvwmoPinBridge4.nthByteOfFetch (k := 4) em hft n pc tvs w hn hlen hw
  refine ⟨fun hhi => ?_, fun hhi hr => ?_⟩
  · obtain ⟨h1, h2⟩ := annRoleBase4 pc w (fun j hj => hb j hj (by omega) (by omega))
    exact ⟨h2, h1⟩
  · exact annRoleRvc4 pc w (fun j hj => hb j (by omega) (by omega) (by omega)) hr

/-- **B4 HEADLINE, 2-aligned arm**: the halfword read `ilo` at `pc` (item `LIFetch pc tvs`) and,
for a 4-byte instruction, `ihi` at `pc + 2` (item `LIFetch (pc + 2) tvs'`): `F_RVC ilo` and
`F_Base (ihi +++ ilo)` announce `krole pc`'s role (the latter IS `kword pc`). -/
theorem annRoleFetch2 (em : Hemission) (hft : kFetchText em) (n : Nat) (pc : Int)
    (tvs : List (Nat × BitVec 8)) (ilo : BitVec 16) :
    em.emItems[n]? = some (Wlabel.LIFetch pc tvs, none) → tvs.length = 2 →
    (∀ j : Nat, j < 2 → (tvs.map Prod.snd)[j]? = some (nthByte (n := 2) ilo j)) →
    textLo ≤ pc → pc + 1 < textHi →
    (LeanRV64D.Functions.isRVC ilo = true → depsOfIb (ibAnn (ibOfBvn ilo)).ibBits = krole pc) ∧
    (∀ (n' : Nat) (tvs' : List (Nat × BitVec 8)) (ihi : BitVec 16),
      em.emItems[n']? = some (Wlabel.LIFetch (pc + 2) tvs', none) → tvs'.length = 2 →
      (∀ j : Nat, j < 2 → (tvs'.map Prod.snd)[j]? = some (nthByte (n := 2) ihi j)) →
      pc + 3 < textHi →
      ibOfBvn (ihi ++ ilo) = kword pc ∧
        depsOfIb (ibAnn (ibOfBvn (ihi ++ ilo))).ibBits = krole pc) := by
  intro hn hlen hw hlo hhi
  have hlo2 := WeakRvwmoPinBridge4.toNatOfBytes2 pc ilo
    (fun j hj => WeakRvwmoPinBridge4.nthByteOfFetch (k := 2) em hft n pc tvs ilo hn hlen hw j hj
      (by omega) (by omega))
  refine ⟨fun hr => annRoleRvc pc ilo hlo2 hr, fun n' tvs' ihi hn' hlen' hw' hhi' => ?_⟩
  have hhi2 := WeakRvwmoPinBridge4.toNatOfBytes2 (pc + 2) ihi
    (fun j hj => WeakRvwmoPinBridge4.nthByteOfFetch (k := 2) em hft n' (pc + 2) tvs' ihi hn'
      hlen' hw' j hj (by omega) (by omega))
  exact annRoleBase22 pc ilo ihi hlo2 hhi2

end Weak
