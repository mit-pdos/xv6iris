/-
Weak/Prom: **E-a4 — the lifecycle protocol: the windowed re-split, the slots, the death, the acquire** (stage E-a4;
G4-review3.md §5 A-3″; plan rev 7 §3 "Lock birth and deferred deposits", "Acquire", "Atomicity", R-a4).

* `resplit7` — AT A BIRTH `b` (round `k`): every hart's lock-shaped words above `b` and the junk above `b` become
  the protocol `lkB b k` (window release slots by author, the death's slot, the acquirers' parts) and the page
  owner's kept part + the junk BEYOND the window (the page bag's remainder, which flows to the next birth).
  Pure classification by `inW`/`isD`/`bey` (functions of `M`); no program fact, no acquirer identity.
* `dead7` — THE DEATH REFUTATION: a participant of round `k` (holding its token `ek h k`) never sees a message
  at or beyond the death of its lock fulfilled: the death's slot then holds the death mark `dM k`.
* `l2_byte7`, `chain7`, `claim7`, `acq7` — E-a2's acquire over the window: the birth (deferred, through the
  shape-only birth slot named in the publication), a window release (its slot's content: the resource, or the
  death mark — absurd for a participant), an acquire word (held).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAE4Defs

namespace Weak.Prom.OA.E4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open Weak.Prom.OA.P (L1 J SV bSlot dshotD dpendD msgAt_of cAt5 bslot_claim)
open Weak.Prom.OA.E
open Weak.Prom.OA.EP (tL1 tL2 isL2O isCO cB src_floor)
open Weak.Prom.OA.E2
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

section lock

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-! ## 1. The re-split at a birth -/

theorem bsl_cut (F : Nat → IProp GF) (p q r s : Nat → Bool) (hr : ∀ t, (p t && q t) = r t)
    (hs : ∀ t, (p t && !q t) = s t) (l : List Nat) :
    ([∗list] t ∈ l.filter p, F t) ⊢ ([∗list] t ∈ l.filter r, F t) ∗ [∗list] t ∈ l.filter s, F t := by
  refine (bsl_filter_split F q (l.filter p)).trans ?_
  rw [filter_filter_of hr l, filter_filter_of hs l]

/-- One hart's words above `b`: window release slots, its kept part. -/
theorem split_h (g : AGN) (M : List PMsg) (tk : Nat → GName) (ek : Nat → Nat → GName) (h b k : Nat) :
    fpt (GF := GF) g M tk h b ⊢ |={⊤}=>
      ([∗list] r ∈ (rng M).filter (fun t => inW M b t && isR2 M t && byH M h t), rSl g M tk ek k r) ∗
      prt g M tk h b b := by
  unfold fpt prt rA rB
  iintro ⟨Ho, Hr⟩
  ihave ⟨Hw, Hb⟩ := bsl_cut (pend (GF := GF) g) _ (inW M b) (fun t => inW M b t && isR2 M t && byH M h t)
    (fun t => decide (b < t) && isR2 M t && byH M h t && bey M b t)
    (fun t => by simp only [inW]; cases decide (b < t) <;> cases isR2 M t <;> cases byH M h t <;> simp)
    (fun t => by simp only [inW, bey]; cases decide (b < t) <;> cases isR2 M t <;> cases byH M h t <;> simp)
    (rng M) $$ Hr
  imod bsl_fupd (G := fun r => rSl (GF := GF) g M tk ek k r) (fun r => by
    iintro Hp; unfold rSl; iapply inv_alloc; inext; ileft; iexact Hp) _ $$ Hw with #Hw
  imodintro; iframe Hw Ho Hb

/-- **THE RE-SPLIT AT A BIRTH** (see the header). -/
theorem resplit7 (g : AGN) (M : List PMsg) (tk : Nat → GName) (ak ek : Nat → Nat → GName) (b k : Nat) :
    fpt (GF := GF) g M tk 0 b ∗ fpt g M tk 1 b ∗ fpt g M tk 2 b ∗ ([∗list] t ∈ jA M b, pend g t) ⊢
      |={⊤}=> lkB g M tk ak ek b k ∗ prt g M tk 0 b b ∗ [∗list] t ∈ jB M b b, pend g t := by
  iintro ⟨H0, H1, H2, HJ⟩
  imod split_h g M tk ek 0 b k $$ H0 with ⟨#R0, P0⟩
  imod split_h g M tk ek 1 b k $$ H1 with ⟨#R1, P1⟩
  imod split_h g M tk ek 2 b k $$ H2 with ⟨#R2, P2⟩
  unfold jA jB
  ihave ⟨HD, HJ⟩ := bsl_cut (pend (GF := GF) g) _ (noJ M b) (isD M b)
    (fun t => decide (b < t) && isJ2 M t && bey M b t)
    (fun t => by simp only [isD, inW]; cases decide (b < t) <;> cases isJ2 M t <;> cases noJ M b t <;> simp)
    (fun t => by simp only [bey]; cases decide (b < t) <;> cases isJ2 M t <;> cases noJ M b t <;> simp)
    (rng M) $$ HJ
  imod bsl_fupd (G := fun d => dSl (GF := GF) g ek k d) (fun d => by
    iintro Hp; unfold dSl; iapply inv_alloc; inext; ileft; iexact Hp) _ $$ HD with #HD
  imod inv_alloc (ndot (ndot hN7 1) k) ⊤ iprop(prt (GF := GF) g M tk 1 b b ∨ token (ak 1 k)) $$ [P1] with #S1
  · inext; ileft; iexact P1
  imod inv_alloc (ndot (ndot hN7 2) k) ⊤ iprop(prt (GF := GF) g M tk 2 b b ∨ token (ak 2 k)) $$ [P2] with #S2
  · inext; ileft; iexact P2
  imodintro
  iframe P0 HJ
  unfold lkB hSl
  iframe HD S1 S2
  rw [show List.range 3 = [0, 1, 2] from rfl]
  iapply (BigSepL.bigSepL_cons).2; iframe R0
  iapply (BigSepL.bigSepL_cons).2; iframe R1
  iapply (BigSepL.bigSepL_cons).2; iframe R2
  iapply (BigSepL.bigSepL_nil).2; itrivial

/-- An acquirer takes its part of round `k`. -/
theorem hclaim7 (g : AGN) (M : List PMsg) (tk : Nat → GName) (ak ek : Nat → Nat → GName) {h b k : Nat}
    (hh : h = 1 ∨ h = 2) : lkB (GF := GF) g M tk ak ek b k ∗ token (ak h k) ⊢ |={⊤}=> prt g M tk h b b := by
  iintro ⟨#Hlk, Ht⟩
  unfold lkB
  icases Hlk with ⟨-, -, #S1, #S2⟩
  ihave #S : hSl (GF := GF) g M tk ak h b k $$ []
  · rcases hh with rfl | rfl
    · iexact S1
    · iexact S2
  unfold hSl
  imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ S with ⟨Hb, Hclose⟩
  icases Hb with (Hp | Ht')
  · imod Hclose $$ [Ht] with -
    · iright; iexact Ht
    imodintro; iexact Hp
  · iexfalso; iapply token_exclusive; iframe Ht Ht'

/-! ## 2. Slots -/

theorem eP_eD (ek : Nat → Nat → GName) (h k : Nat) : eP (GF := GF) ek h k ⊢ |==> eD ek h k := by
  unfold eP eD
  iintro H
  imod ghost_var_update true _ false $$ H with H
  iapply ghost_var_persist $$ H

theorem dM_alloc (ek : Nat → Nat → GName) (k : Nat) :
    eP (GF := GF) ek 0 k ∗ eP ek 1 k ∗ eP ek 2 k ⊢ |={⊤}=> dM ek k := by
  iintro ⟨H0, H1, H2⟩
  imod eP_eD ek 0 k $$ H0 with H0
  imod eP_eD ek 1 k $$ H1 with H1
  imod eP_eD ek 2 k $$ H2 with H2
  imodintro; unfold dM; iframe H0 H1 H2

/-- A participant refutes the death mark of its round. -/
theorem dM_tok (ek : Nat → Nat → GName) {h k : Nat} (hh : h < 3) :
    dM (GF := GF) ek k ∗ eP ek h k ⊢ False := by
  have e : ∀ h, eD (GF := GF) ek h k ∗ eP ek h k ⊢ False := fun h => by
    unfold eD eP
    iintro ⟨H1, H2⟩
    ihave %hv := ghost_var_valid_2 $$ H1 H2
    exact absurd hv.2 (by decide)
  unfold dM
  iintro ⟨⟨#T0, #T1, #T2⟩, Ht⟩
  rcases (by omega : h = 0 ∨ h = 1 ∨ h = 2) with rfl | rfl | rfl
  · iapply e 0; iframe T0 Ht
  · iapply e 1; iframe T1 Ht
  · iapply e 2; iframe T2 Ht

/-- A deposit into a `pend ∨ (shot ∗ C)` slot with persistent content. -/
theorem slot_dep {N : Namespace} (g : AGN) (r : Nat) (C : IProp GF) [Persistent C] :
    inv N iprop(pend g r ∨ (shot g r ∗ C)) ∗ C ⊢ |={⊤}=> shot g r := by
  iintro ⟨#Hs, #HC⟩
  imod inv_acc (E := ⊤) CoPset.subseteq_top $$ Hs with ⟨Hb, Hclose⟩
  icases Hb with (>Hp | ⟨>#Hsh, _⟩)
  · imod shoot $$ Hp with #Hsh
    imod Hclose $$ [] with -
    · inext; iright; iframe Hsh HC
    imodintro; iexact Hsh
  · imod Hclose $$ [] with -
    · inext; iright; iframe Hsh HC
    imodintro; iexact Hsh

theorem pclaim7 (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) (t : Nat) :
    pSl (GF := GF) g M sv ak ek t ∗ shot g t ∗ £ 1 ⊢ |={⊤}=> Pub7 g M sv ak ek t := by
  iintro ⟨#Hs, #Hsh, Hc⟩
  unfold pSl
  imod inv_acc (E := ⊤) CoPset.subseteq_top $$ Hs with ⟨Hb, Hclose⟩
  imod (lc_fupd_elim_later (E := ⊤ \ ↑(ndot pN7 t))
      (P := iprop(pend g t ∨ (shot g t ∗ Pub7 g M sv ak ek t)))) $$ Hc Hb with Hb
  icases Hb with (Hp | ⟨_, #HP⟩)
  · iexfalso; iapply pend_shot; iframe Hp Hsh
  · imod Hclose $$ [] with -
    · inext; iright; iframe Hsh HP
    imodintro; iexact HP

theorem ndep7 (g : AGN) (M : List PMsg) (tk : Nat → GName) (ek : Nat → Nat → GName) (h t : Nat) :
    nSl (GF := GF) g M tk ek h t ∗ Dn7 g M tk ek h t ⊢ |={⊤}=> shot g t := by
  iintro ⟨#Hs, HD⟩
  unfold nSl
  imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hs with ⟨Hb, Hclose⟩
  icases Hb with (Hp | ⟨#Hsh, HB⟩)
  · imod shoot $$ Hp with #Hsh
    imod Hclose $$ [HD] with -
    · iright; iframe Hsh; ileft; iexact HD
    imodintro; iexact Hsh
  · imod Hclose $$ [HB] with -
    · iright; iframe Hsh HB
    imodintro; iexact Hsh

theorem nclaim7 (g : AGN) (M : List PMsg) (tk : Nat → GName) (ek : Nat → Nat → GName) (h t : Nat) :
    nSl (GF := GF) g M tk ek h t ∗ shot g t ∗ token (tk t) ⊢ |={⊤}=> Dn7 g M tk ek h t := by
  iintro ⟨#Hs, #Hsh, Ht⟩
  unfold nSl
  imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hs with ⟨Hb, Hclose⟩
  icases Hb with (Hp | ⟨_, (HD | Ht')⟩)
  · iexfalso; iapply pend_shot; iframe Hp Hsh
  · imod Hclose $$ [Ht] with -
    · iright; iframe Hsh; iright; iexact Ht
    imodintro; iexact HD
  · iexfalso; iapply token_exclusive; iframe Ht Ht'

/-- **A RELEASE'S DEPOSIT** (the author decides: the resource, or the death mark). -/
theorem rdep7 (g : AGN) (M : List PMsg) (tk : Nat → GName) (ek : Nat → Nat → GName) (k r : Nat) :
    rSl (GF := GF) g M tk ek k r ∗ token (tk r) ∗ (Rs5 g M r ∨ dM ek k) ⊢ |={⊤}=> shot g r := by
  iintro ⟨#Hs, Ht, HR⟩
  unfold rSl
  imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hs with ⟨Hb, Hclose⟩
  icases Hb with (Hp | ⟨_, Ht', _⟩)
  · imod shoot $$ Hp with #Hsh
    imod Hclose $$ [Ht HR] with -
    · iright; iframe Hsh Ht
      icases HR with (HR | HR)
      · ileft; iexact HR
      · iright; ileft; iexact HR
    imodintro; iexact Hsh
  · iexfalso; iapply token_exclusive; iframe Ht Ht'

/-! ## 3. Refutations below the frontier -/

theorem J2_msg {M : List PMsg} {t : Nat} (h : isJ2 M t = true) : 1 ≤ t ∧ t ≤ M.length := by
  unfold isJ2 isL2O tL2 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨m, hm, _⟩ := clsB_iff.1 h.1.1.1
  exact msgAt_le hm

/-- Flag junk below the frontier is absurd. -/
theorem fj_front (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) (hdd : g.dd = fun _ => False)
    {π : Proto} {img : Image} {ws1 : PState} {v : Nat} (hvM : 1 ≤ v ∧ v ≤ M.length) (hv : v ≤ wfr ws1)
    (hJ : fJ7 M v = true) : ctx7 (GF := GF) g M sv ak ek ∗ frontA g π img M ws1 ⊢ |={⊤}=> False := by
  iintro ⟨#Hctx, #Hfr⟩
  unfold ctx7
  icases Hctx with ⟨Hdoom, -, -, -, Hjs, -⟩
  imod frontS g M hdd (π := π) (img := img) (ws := ws1) v ⟨hvM.1, hvM.2, hv⟩ $$ [] with #Hs
  · iframe Hdoom Hfr
  ihave #Hj := bsl_mem (F := fun t => lkJunk g t) (List.mem_filter.2 ⟨mem_rng.2 hvM, hJ⟩) $$ Hjs
  iapply junk_shot g v; iframe Hj Hs

/-- **THE DEATH REFUTATION** (see the header). -/
theorem dead7 (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) (hdd : g.dd = fun _ => False)
    {π : Proto} {img : Image} {ws1 : PState} {h b k t : Nat} (hh : h < 3) (htM : t ≤ M.length)
    (ht : t ≤ wfr ws1) (hD : isD M b t = true ∨ bey M b t = true) :
    ctx7 (GF := GF) g M sv ak ek ∗ lkB g M sv.tk ak ek b k ∗ frontA g π img M ws1 ∗ eP ek h k ⊢
      |={⊤}=> False := by
  iintro ⟨#Hctx, #Hlk, #Hfr, Ht⟩
  obtain ⟨d, hdt, hd⟩ : ∃ d, d ≤ t ∧ isD M b d = true := by
    rcases hD with h | h
    · exact ⟨t, Nat.le_refl _, h⟩
    · obtain ⟨d, h1, h2⟩ := bey_death t t (Nat.le_refl _) h; exact ⟨d, by omega, h2⟩
  have hdM : 1 ≤ d ∧ d ≤ M.length := J2_msg (isD_J hd)
  unfold ctx7
  icases Hctx with ⟨Hdoom, -⟩
  imod frontS g M hdd (π := π) (img := img) (ws := ws1) d ⟨hdM.1, hdM.2, by omega⟩ $$ [] with #Hsh
  · iframe Hdoom Hfr
  unfold lkB
  icases Hlk with ⟨-, Hds, -⟩
  ihave #Hsl := bsl_mem (F := fun d => dSl g ek k d) (List.mem_filter.2 ⟨mem_rng.2 hdM, hd⟩) $$ Hds
  unfold dSl
  imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hsl with ⟨Hb, -⟩
  icases Hb with (Hp | ⟨_, #HdM⟩)
  · iexfalso; iapply pend_shot; iframe Hp Hsh
  · iexfalso; iapply dM_tok ek hh; iframe HdM Ht

/-! ## 4. Reading the lock word -/

/-- The byte value an L2 read returns from the birth, an acquire or a release. -/
theorem l2_val7 {M : List PMsg} {t j : Nat} {v : BitVec 8} (hj : j < 4)
    (hv : memByte img7 M t (Lk + j) = some v) (hc : zw M t = true ∨ isA2 M t = true ∨ isR2 M t = true) :
    some v = (toBytes (if isA2 M t = true then 1 else 0) 4)[j]? := by
  have hsrc : ∀ m d, msgAt M t = some m → m.pa = Lk → m.data = d → some v = d[j]? := fun m d hm hp hd => by
    cases t with
    | zero => cases hm
    | succ k =>
      obtain ⟨m', hm', hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hv)
      have : m' = m := by simpa [msgAt, hm'] using hm
      subst this; rw [← hba, ← hp, byteAt_off rfl, hd]
  rcases hc with hz | hA | hR
  · obtain ⟨m, hm, hp, hd, _⟩ := clsB_iff.1 hz
    have hA : isA2 M t = false := by
      cases h : isA2 M t
      · rfl
      · unfold isA2 at h; obtain ⟨m', hm', _, hd'⟩ := clsB_iff.1 (Bool.and_eq_true_iff.1 h).2
        rw [hm] at hm'; cases hm'; rw [hd] at hd'; exact absurd hd' (by decide)
    rw [hA]; exact hsrc m _ hm hp hd
  · unfold isA2 at hA
    obtain ⟨m, hm, ⟨hp, _⟩, hd⟩ := clsB_iff.1 (Bool.and_eq_true_iff.1 hA).2
    rw [show isA2 M t = true by unfold isA2; exact hA, if_pos rfl]; exact hsrc m _ hm hp hd
  · rw [R2_A2 hR]; unfold isR2 at hR
    obtain ⟨m, hm, ⟨hp, _⟩, hd⟩ := clsB_iff.1 (Bool.and_eq_true_iff.1 hR).2
    exact hsrc m _ hm hp hd

/-- **ONE L2 BYTE** of a participant (R-a4 over the window): floor at the birth, below the frontier: the birth, or
an acquire or release word of the window. -/
theorem l2_byte7 (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) (hdd : g.dd = fun _ => False)
    {π : Proto} {ws1 : PState} {h b k t j fl : Nat} {v : BitVec 8} (hh : h < 3) (hj : j < 4) (hb : zw M b = true)
    (hfl : b ≤ fl) (hm : memByte img7 M t (Lk + j) = some v) (hr : ¬ writesIn M (Lk + j) t fl)
    (ht : t ≤ wfr ws1) :
    ctx7 (GF := GF) g M sv ak ek ∗ lkB g M sv.tk ak ek b k ∗ frontA g π img7 M ws1 ∗ eP ek h k ⊢
      |={⊤}=> eP ek h k ∗ ⌜t = b ∨ (inW M b t = true ∧ (isA2 M t = true ∨ isR2 M t = true))⌝ := by
  iintro ⟨#Hctx, #Hlk, #Hfr, Ht⟩
  have hbt := src_floor (zw_wr hj hb) hfl hr
  by_cases heq : t = b
  · imodintro; iframe Ht; ipureintro; exact .inl heq
  cases t with
  | zero => omega
  | succ n =>
    obtain ⟨m, hm', hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hm)
    have hmt : msgAt M (n + 1) = some m := by simpa [msgAt] using hm'
    have htM := msgAt_le hmt
    rcases l2_src hmt hj (by rw [hba]; rfl) with hO | hF
    · rcases inW_or_bey (M := M) (by omega : b < n + 1) with hW | hB
      · rcases l2_cls hO with hA | hR | hJ
        · imodintro; iframe Ht; ipureintro; exact .inr ⟨hW, .inl hA⟩
        · imodintro; iframe Ht; ipureintro; exact .inr ⟨hW, .inr hR⟩
        · imod dead7 g M sv ak ek hdd hh htM.2 ht (.inl (by rw [isD, hW, hJ])) $$ [Ht] with %hf
          · iframe Hctx Hlk Hfr Ht
          exact hf.elim
      · imod dead7 g M sv ak ek hdd hh htM.2 ht (.inr hB) $$ [Ht] with %hf
        · iframe Hctx Hlk Hfr Ht
        exact hf.elim
    · imod fj_front g M sv ak ek hdd htM ht (fJ_of_L2 hmt hj (by rw [hba]; rfl) (by
        unfold fJ at hF; exact (Bool.and_eq_true_iff.1 hF).1)) $$ [] with %hf
      · iframe Hctx Hfr
      exact hf.elim

/-- **THE ATOMICITY STEP** (as E-a2's `chain5`, over the window and the death). -/
theorem chain7 (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) (h : Nat)
    (hdd : g.dd = fun _ => False) {π : Proto} {ws1 ws : PState} {b k lo s0 ts vpre : Nat} (hh : h < 3)
    (hbs : b ≤ s0) (hs0 : s0 < ts) (hts : ts ≤ wfr ws1) (hwts : wrB M Lk ts) (hlo : lo ≤ max vpre (coh ws Lk))
    (hr : ¬ writesIn M Lk s0 (max vpre (coh ws Lk)))
    (hx : ¬ writesInBy M (fun tid => tid ≠ some h) Lk s0 (ts - 1)) :
    ctx7 (GF := GF) g M sv ak ek ∗ lkB g M sv.tk ak ek b k ∗ frontA g π img7 M ws1 ∗ obg g M sv.tk h lo ts ∗
      ([∗list] t ∈ rB M h b lo, pend g t) ∗ eP ek h k ⊢
      |={⊤}=> obg g M sv.tk h lo ts ∗ ([∗list] t ∈ rB M h b lo, pend g t) ∗ eP ek h k ∗ ⌜nxtL M s0 ts⌝ := by
  iintro ⟨#Hctx, #Hlk, #Hfr, Hbag, HrB, Ht⟩
  by_cases hn : nxtL M s0 ts
  · imodintro; iframe Hbag HrB Ht; ipureintro; exact hn
  have hex : ∃ v, s0 < v ∧ v < ts ∧ wrB M Lk v := by
    apply Classical.byContradiction; intro hne
    exact hn ⟨hs0, hwts, fun v h1 h2 h3 => hne ⟨v, h1, h2, h3⟩⟩
  obtain ⟨v, hv1, hv2, hwv⟩ := hex
  obtain ⟨m, hmv, hbv⟩ := hwv
  have hvM := msgAt_le hmv
  have htid : tidAt M v = some h := by
    apply Classical.byContradiction; intro hne
    exact chain_excl hv1 hv2 ⟨m, hmv, hbv⟩ hne hx
  have hvl : lo < v := by
    apply Classical.byContradiction; intro hle
    obtain ⟨n, rfl⟩ : ∃ n, v = n + 1 := ⟨v - 1, by omega⟩
    exact hr ⟨n + 1, hv1, by omega, m, by simpa [msgAt] using hmv, hbv⟩
  have hbyH : byH M h v = true := by simp [byH, htid]
  have hvf : v ≤ wfr ws1 := by omega
  imod frontS g M hdd (π := π) (img := img7) (ws := ws1) v ⟨hvM.1, hvM.2, hvf⟩ $$ [] with #Hsh
  · unfold ctx7; icases Hctx with ⟨Hdoom, -⟩; iframe Hdoom Hfr
  rcases l2_src hmv (j := 0) (by decide) (by simpa using hbv) with hO | hF
  · rcases inW_or_bey (M := M) (by omega : b < v) with hW | hB
    · rcases l2_cls hO with hA | hR | hJ
      · unfold obg bgA
        icases Hbag with ⟨HbA, -⟩
        icases bsl_filter_take (pend g) (fun t => decide (lo < t) && decide (t ≠ ts) && isA2 M t && byH M h t)
          (fun _ => false) v (by simp [hvl, show v ≠ ts by omega, hA, hbyH])
          (fun _ h => by cases h) (rng M) (mem_rng.2 hvM) (nodup_rng M) $$ HbA with ⟨Hp, -⟩
        iexfalso; iapply pend_shot; iframe Hp Hsh
      · unfold obg bgL
        icases Hbag with ⟨-, HbL⟩
        icases bsl_filter_take (fun t => token (sv.tk t))
          (fun t => decide (lo < t) && decide (t ≠ ts) && (isA2 M t || isR2 M t) && byH M h t) (fun _ => false) v
          (by simp [hvl, show v ≠ ts by omega, hR, hbyH]) (fun _ h => by cases h) (rng M) (mem_rng.2 hvM)
          (nodup_rng M) $$ HbL with ⟨Htk, -⟩
        unfold lkB
        icases Hlk with ⟨Hrs, -⟩
        ihave #Hrh := bsl_mem (F := fun h => [∗list] r ∈ (rng M).filter (fun t => inW M b t && isR2 M t &&
          byH M h t), rSl g M sv.tk ek k r) (List.mem_range.2 hh) $$ Hrs
        ihave #Hslot := bsl_mem (F := fun r => rSl g M sv.tk ek k r)
          (List.mem_filter.2 ⟨mem_rng.2 hvM, by simp [hW, hR, hbyH]⟩) $$ Hrh
        unfold rSl
        imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hslot with ⟨Hb, -⟩
        icases Hb with (Hp | ⟨_, Ht', _⟩)
        · iexfalso; iapply pend_shot; iframe Hp Hsh
        · iexfalso; iapply token_exclusive; iframe Htk Ht'
      · imod dead7 g M sv ak ek hdd hh hvM.2 hvf (.inl (by rw [isD, hW, hJ])) $$ [Ht] with %hf
        · iframe Hctx Hlk Hfr Ht
        exact hf.elim
    · imod dead7 g M sv ak ek hdd hh hvM.2 hvf (.inr hB) $$ [Ht] with %hf
      · iframe Hctx Hlk Hfr Ht
      exact hf.elim
  · imod fj_front g M sv ak ek hdd hvM hvf (fJ_of_L2 hmv (j := 0) (by decide) (by simpa using hbv) (by
      unfold fJ at hF; exact (Bool.and_eq_true_iff.1 hF).1)) $$ [] with %hf
    · iframe Hctx Hfr
    exact hf.elim

/-- **THE CLAIM**: the AMO `ts` with `nxtL M s0 ts` takes the resource of its source — the birth's deferred slot,
or a window release's slot (whose death-mark content is absurd for a participant). -/
theorem claim7 (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) (hdd : g.dd = fun _ => False)
    {π : Proto} {ws1 : PState} {h b k c sp s0 ts : Nat} (hh : h < 3) (hn : nxtL M s0 ts)
    (hs0 : s0 = b ∨ (inW M b s0 = true ∧ isR2 M s0 = true)) (hts : ts ≤ wfr ws1) :
    ctx7 (GF := GF) g M sv ak ek ∗ lkB g M sv.tk ak ek b k ∗ hdl M sv b (Rb7 g M c sp) ∗ frontA g π img7 M ws1 ∗
      token (sv.tk ts) ∗ eP ek h k ∗ £ 1 ⊢
      |={⊤}=> eP ek h k ∗ ∃ lw sq, ⌜(lw ≤ s0 ∧ sq ≤ s0) ∨ (lw = c ∧ sq = sp)⌝ ∗ cPts5 g M lw ∗ pPts5 g M sq := by
  iintro ⟨#Hctx, #Hlk, #Hl, #Hfr, Htk, Hek, Hc⟩
  rcases hs0 with rfl | ⟨hW, hR⟩
  · unfold hdl
    icases Hl with ⟨-, #Hds, #HsQ, #Hslot⟩
    imod bslot_claim M sv s0 ts hn (Rb7 g M c sp) $$ [Htk Hc] with HR
    · iframe Hslot Hds HsQ Htk Hc
    unfold Rb7
    icases HR with >⟨HC, HP⟩
    imodintro; iframe Hek; iexists c; iexists sp; iframe HC HP; ipureintro; exact .inr ⟨rfl, rfl⟩
  · obtain ⟨m, hm, ⟨hp, hl, htid⟩, _⟩ := clsB_iff.1 (Bool.and_eq_true_iff.1 hR).2
    have hsM := msgAt_le hm
    obtain ⟨a, ha, hba⟩ : ∃ a, a < 3 ∧ byH M a s0 = true := by
      rcases htid with h0 | h0 | h0
      · exact ⟨0, by decide, by simp [byH, tidAt, hm, h0]⟩
      · exact ⟨1, by decide, by simp [byH, tidAt, hm, h0]⟩
      · exact ⟨2, by decide, by simp [byH, tidAt, hm, h0]⟩
    unfold ctx7
    icases Hctx with ⟨Hdoom, -⟩
    imod frontS g M hdd (π := π) (img := img7) (ws := ws1) s0 ⟨hsM.1, hsM.2, by have := hn.1; omega⟩ $$ []
      with #Hsh
    · iframe Hdoom Hfr
    unfold lkB
    icases Hlk with ⟨Hrs, -⟩
    ihave #Hrh := bsl_mem (F := fun h => [∗list] r ∈ (rng M).filter (fun t => inW M b t && isR2 M t &&
      byH M h t), rSl g M sv.tk ek k r) (List.mem_range.2 ha) $$ Hrs
    ihave #Hslot := bsl_mem (F := fun r => rSl g M sv.tk ek k r)
      (List.mem_filter.2 ⟨mem_rng.2 hsM, by simp [hW, hR, hba]⟩) $$ Hrh
    unfold rSl
    imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hslot with ⟨Hb, Hclose⟩
    icases Hb with (Hp | ⟨_, Ha, (HR | #HdM | Hn)⟩)
    · iexfalso; iapply pend_shot; iframe Hp Hsh
    · imod Hclose $$ [Htk Ha] with -
      · iright; iframe Hsh Ha; iright; iright; unfold nxtTok; iexists ts; iframe Htk; ipureintro; exact hn
      unfold Rs5
      icases HR with ⟨⟨%lw, %hlw, HC⟩, HP⟩
      imodintro; iframe Hek; iexists lw; iexists s0; iframe HC HP; ipureintro; exact .inl ⟨hlw, Nat.le_refl _⟩
    · iexfalso; iapply dM_tok ek hh; iframe HdM Hek
    · unfold nxtTok
      icases Hn with ⟨%u, %hu, Ht'⟩
      rw [nxtL_unique hu hn] at *
      iexfalso; iapply token_exclusive; iframe Htk Ht'

/-- `loadOk` per byte, with the coherence floor (no invalidations). -/
theorem loadOk_fl {img : Image} {M : List PMsg} {ws : PState} {vpre : Nat} {base : Int}
    {tvs : List (Nat × BitVec 8)} (h : loadOk img M ws vpre base tvs) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    bytesAll (fun a t v => memByte img M t a = some v ∧ ¬ writesIn M a t (max vpre (coh ws a))) base tvs := by
  unfold loadOk at h
  refine bytesAll_mono (fun a t v hp => ⟨hp.1, ?_⟩) base tvs h
  rcases hp.2 with h1 | ⟨ti, hc, _⟩
  · exact fun hc => h1 (writesIn_mono hc (by split <;> omega))
  · exact absurd hc (hnoinv _ _)

/-- **THE ACQUIRE** of a participant: value `1` (held), or `0` with the claimed resource. -/
theorem acq7 (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) (h : Nat) (hdd : g.dd = fun _ => False)
    {π : Proto} {ws ws2 ws1 : PState} {tvs : List (Nat × BitVec 8)} {b k c sp ts lo vpre : Nat} (hh : h < 3)
    (hb : zw M b = true) (hlen : tvs.length = 4)
    (hlo1 : loadOk img7 M ws vpre Lk tvs) (hex : exclOk M h Lk (tvs.map Prod.fst) ts)
    (hsrc : bytesAll (fun x u _ => u ≤ coh ws2 x) Lk tvs) (hcohB : ∀ j : Nat, j < 4 → coh ws2 (Lk + j) < ts)
    (hbv : ∀ j : Nat, j < 4 → b ≤ max vpre (coh ws (Lk + j))) (hlo : lo ≤ max vpre (coh ws Lk))
    (hts : ts ≤ wfr ws1) (hwts : wrB M Lk ts) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    ctx7 (GF := GF) g M sv ak ek ∗ lkB g M sv.tk ak ek b k ∗ hdl M sv b (Rb7 g M c sp) ∗
      frontA g π img7 M ws1 ∗ obg g M sv.tk h lo ts ∗ ([∗list] t ∈ rB M h b lo, pend g t) ∗ eP ek h k ∗
      token (sv.tk ts) ∗ £ 1 ⊢
      |={⊤}=> obg g M sv.tk h lo ts ∗ ([∗list] t ∈ rB M h b lo, pend g t) ∗ eP ek h k ∗
        (⌜tvs.map Prod.snd = toBytes 1 4⌝ ∨
         (⌜tvs.map Prod.snd = toBytes 0 4⌝ ∗
          ∃ lw sq, ⌜(lw < ts ∧ sq < ts) ∨ (lw = c ∧ sq = sp)⌝ ∗ cPts5 g M lw ∗ pPts5 g M sq)) := by
  iintro ⟨#Hctx, #Hlk, #Hl, #Hfr, Hbag, HrB, Hek, Htok, Hc⟩
  obtain ⟨t0, v0, t1, v1, t2, v2, t3, v3, rfl⟩ : ∃ t0 v0 t1 v1 t2 v2 t3 v3,
      tvs = [(t0, v0), (t1, v1), (t2, v2), (t3, v3)] := by
    match tvs, hlen with
    | [(a, b), (c, d), (e, f), (i, j)], _ => exact ⟨a, b, c, d, e, f, i, j, rfl⟩
  have hw := loadOk_fl hlo1 hnoinv
  have hbyte : ∀ (j t : Nat) (v : BitVec 8), j < 4 → [(t0, v0), (t1, v1), (t2, v2), (t3, v3)][j]? = some (t, v) →
      memByte img7 M t (Lk + j) = some v ∧ t < ts ∧ ¬ writesIn M (Lk + j) t (max vpre (coh ws (Lk + j))) :=
    fun j t v hj hg => by
      have h1 := bytesAll_get hw hg
      exact ⟨h1.1, Nat.lt_of_le_of_lt (bytesAll_get hsrc hg) (hcohB j hj), h1.2⟩
  have step : ∀ (j t : Nat) (v : BitVec 8), j < 4 → [(t0, v0), (t1, v1), (t2, v2), (t3, v3)][j]? = some (t, v) →
      ctx7 (GF := GF) g M sv ak ek ∗ lkB g M sv.tk ak ek b k ∗ frontA g π img7 M ws1 ∗ eP ek h k ⊢
        |={⊤}=> eP ek h k ∗ ⌜(t = b ∨ (inW M b t = true ∧ (isA2 M t = true ∨ isR2 M t = true))) ∧
          some v = (toBytes (if isA2 M t = true then 1 else 0) 4)[j]?⌝ := fun j t v hj hg => by
    obtain ⟨hm, hlt, hr⟩ := hbyte j t v hj hg
    iintro H
    imod l2_byte7 g M sv ak ek hdd hh hj hb (hbv j hj) hm hr (by omega) $$ H with ⟨Ht, %hc⟩
    imodintro; iframe Ht; ipureintro
    refine ⟨hc, l2_val7 hj hm ?_⟩
    rcases hc with rfl | ⟨_, h | h⟩
    · exact .inl hb
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  imod step 0 t0 v0 (by decide) rfl $$ [Hek] with ⟨Hek, %⟨hc0, hv0⟩⟩
  · iframe Hctx Hlk Hfr Hek
  imod step 1 t1 v1 (by decide) rfl $$ [Hek] with ⟨Hek, %⟨-, hv1⟩⟩
  · iframe Hctx Hlk Hfr Hek
  imod step 2 t2 v2 (by decide) rfl $$ [Hek] with ⟨Hek, %⟨-, hv2⟩⟩
  · iframe Hctx Hlk Hfr Hek
  imod step 3 t3 v3 (by decide) rfl $$ [Hek] with ⟨Hek, %⟨-, hv3⟩⟩
  · iframe Hctx Hlk Hfr Hek
  have hword : [v0, v1, v2, v3] = toBytes (if isA2 M t0 = true then 1 else 0) 4 :=
    lk_word (by split <;> simp) (by split <;> simp) (by split <;> simp) (by split <;> simp) hv0 hv1 hv2 hv3
  have hmap : [(t0, v0), (t1, v1), (t2, v2), (t3, v3)].map Prod.snd = [v0, v1, v2, v3] := rfl
  by_cases hA0 : isA2 M t0 = true
  · rw [if_pos hA0] at hword
    imodintro; iframe Hbag HrB Hek; ileft; ipureintro; rw [hmap, hword]
  · rw [if_neg hA0] at hword
    have hc0' : t0 = b ∨ (inW M b t0 = true ∧ isR2 M t0 = true) := by
      rcases hc0 with h | ⟨h1, h | h⟩
      · exact .inl h
      · exact absurd h hA0
      · exact .inr ⟨h1, h⟩
    obtain ⟨_, hs0, _⟩ := hbyte 0 t0 v0 (by decide) rfl
    obtain ⟨_, hr0⟩ := loadOk_b0 hlo1
    have hr0 : ¬ writesIn M Lk t0 (max vpre (coh ws Lk)) := by
      rcases hr0 with h | ⟨ti, hci, _⟩
      · exact h
      · exact absurd hci (hnoinv _ _)
    have hbs : b ≤ t0 := by
      rcases hc0' with h | ⟨h, _⟩
      · omega
      · simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at h; omega
    imod chain7 g M sv ak ek h hdd (ws1 := ws1) (ws := ws) (π := π) (b := b) (k := k) (lo := lo) (s0 := t0)
      (ts := ts) (vpre := vpre) hh hbs hs0 hts hwts hlo hr0 hex.1 $$ [Hbag HrB Hek]
      with ⟨Hbag, HrB, Hek, %hn⟩
    · iframe Hctx Hlk Hfr Hbag HrB Hek
    imod claim7 g M sv ak ek hdd (ws1 := ws1) (π := π) (c := c) (sp := sp) hh hn hc0' hts $$ [Htok Hek Hc]
      with ⟨Hek, %lw, %sq, %hls, HC, HP⟩
    · iframe Hctx Hlk Hl Hfr Htok Hek Hc
    imodintro; iframe Hbag HrB Hek; iright
    isplitr
    · ipureintro; rw [hmap, hword]
    · iexists lw; iexists sq; iframe HC HP; ipureintro
      rcases hls with h | h
      · exact .inl ⟨by omega, by omega⟩
      · exact .inr h

end lock

end Weak.Prom.OA.E4
