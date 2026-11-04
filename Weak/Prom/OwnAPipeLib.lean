/-
Weak/Prom: **G4 target (4) on track (a): the resource library — saved-proposition deposits and claims, the L1 slot,
the two acquires' byte classifications** (stage S4a part 4; plan rev 7 §3 "The rev-4 design: per-t one-shot saved
propositions" (deposit, "Deposited", opening), "Lock birth and deferred deposits", "Acquire", R-a4).

* `bslot_deposit` — THE DEFERRED DEPOSIT (plan §3: "The author opens the invariant, updates … to R_t …, and
  persists its own half … The deposit … also issues the persistent `deposited_t`"): the holder of the full saved
  proposition `σ_b ↦ True` (the author of the plain birth `b`) chooses `Q` NOW (it may name ghost state allocated
  after adequacy start) and obtains `dshotD b` and the public `σ_b ↦□ Q`.
* `bslot_claim` — OPENING (plan §3 "Opening": "uses savedAt t R_t with saved_prop_agree to turn the invariant's P
  into R_t.  Agreement holds under ▷, and the opening step's ▷/£1 pays for it.  It then swaps its claim token for
  R_t"): `▷ Q`.
* `l1_deposit` / `l1_claim` — L1's release slot (deposit at the release-class fulfil; claim with the token).
* `l1_acq` — the L1 acquire AMO (hart 1, the only acquirer): the word is 1, or 0 with `Pub1 s` claimed from the
  release `s` it read, or free mode.
* `l2_acq` — the L2 acquire AMO: given the birth `b ≤` the read's pre-view, the word is 1, or 0 read from `b`, or
  free mode.  R-a4: bytes below `b` (the junk `j`, the image) are excluded by coherence; bytes above `b` are hart 1's
  own AMO writes, or messages whose `pend` hart 1 holds (hart 0's later L2 words, from the handle; its own L2
  releases) — fulfilled by the frontier, absurd — or dead.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAPipeDefs

namespace Weak.Prom.OA.P

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

section lib

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- Rewriting a saved proposition's content along its agreement (as MachCSL `crashPerm_rewrite`). -/
theorem saved_rewrite (P Q : IProp GF) : ▷ internalEq P Q ∗ ▷ P ⊢ ▷ Q := by
  refine (sep_mono_left (internalEq_rewrite_contractive P Q (fun X => iprop(▷ X)))).trans ?_
  exact sep_and.trans imp_elim_left

/-- The full saved proposition and a persisted one cannot coexist. -/
theorem saved_full_disc (γ : GName) (P Q : IProp GF) :
    saved_prop_own (GF := GF) γ (.own 1) P ∗ saved_prop_own γ .discard Q ⊢ False := by
  iintro H
  ihave %h := ((saved_prop_valid_2 γ (.own 1) .discard P Q).trans and_elim_l) $$ H
  exact absurd (DFrac.valid_own_op_discard.1 h) (by simp)

/-- **THE DEFERRED DEPOSIT** (see the header). -/
theorem bslot_deposit (M : List PMsg) (sv : SV) (b : Nat) (Q : IProp GF) :
    bSlot (GF := GF) M sv b ∗ saved_prop_own (sv.σ b) (.own 1) iprop(True) ∗ Q ∗ £ 1 ⊢
      |={⊤}=> dshotD sv b ∗ saved_prop_own (sv.σ b) .discard Q := by
  iintro ⟨#Hs, Hsv, HQ, Hc⟩
  unfold bSlot
  imod inv_acc (E := ⊤) CoPset.subseteq_top $$ Hs with ⟨Hb, Hclose⟩
  imod (lc_fupd_elim_later (E := ⊤ \ ↑(ndot bN b)) (P := iprop(dpendD sv b ∨
      (dshotD sv b ∗ ∃ P : IProp GF, saved_prop_own (sv.σ b) .discard P ∗ (P ∨ nxtTok M sv.tk b)))))
    $$ Hc Hb with Hb
  icases Hb with (Hp | ⟨_, %P, Hsp, _⟩)
  rotate_left
  · iexfalso; iapply saved_full_disc; iframe Hsv Hsp
  imod saved_prop_update Q (sv.σ b) iprop(True) $$ Hsv with Hsv
  imod saved_prop_persist $$ Hsv with #Hsv
  unfold dpendD
  imod ghost_var_update true _ false $$ Hp with Hp
  imod ghost_var_persist $$ Hp with #Hp
  imod Hclose $$ [HQ] with -
  · inext; iright; isplitr [HQ]
    · unfold dshotD; iexact Hp
    · iexists Q; isplitr [HQ]
      · iexact Hsv
      · ileft; iexact HQ
  imodintro
  unfold dshotD; iframe Hp Hsv

/-- **OPENING** a deposited saved-proposition slot (see the header): the claim token (the token of the AMO `u`
whose read source is `b`, `nxtL M b u`) for `▷ Q`. -/
theorem bslot_claim (M : List PMsg) (sv : SV) (b u : Nat) (hn : nxtL M b u) (Q : IProp GF) :
    bSlot (GF := GF) M sv b ∗ dshotD sv b ∗ saved_prop_own (sv.σ b) .discard Q ∗ token (sv.tk u) ∗ £ 1 ⊢
      |={⊤}=> ▷ Q := by
  iintro ⟨#Hs, #Hd, #HsQ, Ht, Hc⟩
  unfold bSlot
  imod inv_acc (E := ⊤) CoPset.subseteq_top $$ Hs with ⟨Hb, Hclose⟩
  imod (lc_fupd_elim_later (E := ⊤ \ ↑(ndot bN b)) (P := iprop(dpendD sv b ∨
      (dshotD sv b ∗ ∃ P : IProp GF, saved_prop_own (sv.σ b) .discard P ∗ (P ∨ nxtTok M sv.tk b)))))
    $$ Hc Hb with Hb
  icases Hb with (Hp | ⟨_, %P, #HsP, (HP | Ht')⟩)
  · iexfalso; iapply dpendD_dshotD; iframe Hp Hd
  · imod Hclose $$ [Ht] with -
    · inext; iright; isplitr [Ht]
      · iexact Hd
      · iexists P; isplitr [Ht]
        · iexact HsP
        · iright; unfold nxtTok; iexists u; iframe Ht; ipureintro; exact hn
    imodintro
    ihave Heq := saved_prop_agree (sv.σ b) .discard .discard P Q $$ [HsP HsQ]
    · iframe HsP HsQ
    iapply saved_rewrite P Q
    iframe Heq
    inext; iexact HP
  · unfold nxtTok
    icases Ht' with ⟨%u', %hn', Ht'⟩
    rw [nxtL_unique hn' hn]
    iexfalso; iapply token_exclusive; iframe Ht Ht'

/-- **L1's DEPOSIT** at its release-class fulfil `r`: `pend r` out of the slot, shot; `Pub1 r` in. -/
theorem l1_deposit (g : AGN) (M : List PMsg) (sv : SV) (r : Nat) :
    l1Slot (GF := GF) g M sv r ∗ Pub1 g M sv r ⊢ |={⊤}=> shot g r := by
  iintro ⟨#Hs, HP⟩
  unfold l1Slot
  imod inv_acc (E := ⊤) CoPset.subseteq_top $$ Hs with ⟨Hb, Hclose⟩
  icases Hb with (>Hp | ⟨>#Hsh, HB⟩)
  · imod shoot $$ Hp with #Hsh
    imod Hclose $$ [HP] with -
    · inext; iright; iframe Hsh; ileft; iexact HP
    imodintro; iexact Hsh
  · imod Hclose $$ [HB] with -
    · inext; iright; iframe Hsh; iexact HB
    imodintro; iexact Hsh

/-- **L1's CLAIM**: knowing `shot s` and holding the token of `s`, `Pub1 s`. -/
theorem l1_claim (g : AGN) (M : List PMsg) (sv : SV) (s : Nat) :
    l1Slot (GF := GF) g M sv s ∗ shot g s ∗ token (sv.tk s) ∗ £ 1 ⊢ |={⊤}=> Pub1 g M sv s := by
  iintro ⟨#Hs, #Hsh, Ht, Hc⟩
  unfold l1Slot
  imod inv_acc (E := ⊤) CoPset.subseteq_top $$ Hs with ⟨Hb, Hclose⟩
  imod (lc_fupd_elim_later (E := ⊤ \ ↑(ndot l1N s))
      (P := iprop(pend g s ∨ (shot g s ∗ (Pub1 g M sv s ∨ token (sv.tk s)))))) $$ Hc Hb with Hb
  icases Hb with (Hp | ⟨_, (HR | Ht')⟩)
  · iexfalso; iapply pend_shot; iframe Hp Hsh
  · imod Hclose $$ [Ht] with -
    · inext; iright; iframe Hsh; iright; iexact Ht
    imodintro; iexact HR
  · iexfalso; iapply token_exclusive; iframe Ht Ht'

/-! ## Dead messages -/

theorem pCtx_dead (g : AGN) (M : List PMsg) (sv : SV) {t : Nat} (ht : 1 ≤ t ∧ t ≤ M.length) (hk : knd M t = 0) :
    pCtx (GF := GF) g M sv ⊢ deadInv g t := by
  iintro #Hctx
  unfold pCtx
  icases Hctx with ⟨-, -, -, Hdd⟩
  iapply bsl_mem (F := fun t => deadInv g t) (List.mem_filter.2 ⟨mem_rng.2 ht, by simp [isK, hk]⟩) $$ Hdd

/-- READING a dead message: free mode. -/
theorem pCtx_read_dead (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = dd4 M) {t : Nat}
    (ht : 1 ≤ t ∧ t ≤ M.length) (hk : knd M t = 0) :
    pCtx (GF := GF) g M sv ⊢ |={⊤}=> dfree g ∗ dshot g := by
  iintro #Hctx
  ihave #Hd := pCtx_dead g M sv ht hk $$ Hctx
  unfold pCtx
  icases Hctx with ⟨Hdoom, -⟩
  iapply dead_doom g M t ht (by rw [hdd]; exact ⟨ht.1, hk⟩)
  iframe Hdoom Hd

/-- Free mode implies doom. -/
theorem pCtx_free (g : AGN) (M : List PMsg) (sv : SV) :
    pCtx (GF := GF) g M sv ∗ dfree g ⊢ |={⊤}=> dfree g ∗ dshot g := by
  iintro ⟨#Hctx, #Hf⟩
  unfold pCtx
  icases Hctx with ⟨Hdoom, -⟩
  imod dfree_dshot (E := ⊤) CoPset.subseteq_top g M $$ [] with #Hd
  · iframe Hdoom Hf
  imodintro; iframe Hf Hd

/-- A cache-block operation is dead. -/
theorem cmo_knd {M : List PMsg} {ti : Nat} {a : Int} (h1 : 1 ≤ ti) (h : cmoAt M isInvalK ti a) :
    knd M ti = 0 ∧ ti ≤ M.length := by
  obtain ⟨m, k, len, hm, hc, _⟩ := h
  have hmt := msgAt_of h1 hm
  refine ⟨?_, (msgAt_le hmt).2⟩
  rw [knd_of hmt]
  unfold kind
  have e1 : ¬ cmP m := fun h => by rw [h.2.2.1] at hc; cases hc
  have e2 : ¬ a1P m := fun h => by rw [h.2.2.1] at hc; cases hc
  have e3 : ¬ r1P m := fun h => by rw [h.2.2.1] at hc; cases hc
  have e4 : ¬ a2P m := fun h => by rw [h.2.2.1] at hc; cases hc
  have e5 : ¬ r2P m := fun h => by rw [h.2.2.1] at hc; cases hc
  have e6 : ¬ z0P m := fun h => by rw [h.2.2.1] at hc; cases hc
  rw [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5, if_neg e6]

/-! ## The L1 acquire -/

/-- An L1 byte below the frontier came from the image, hart 1's AMO writes, hart 0's releases, or free mode. -/
theorem l1_src (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = dd4 M) {t j : Nat} {v : BitVec 8}
    (hj : j < 4) (hb : memByte img4 M t (L1 + j) = some v) :
    pCtx (GF := GF) g M sv ⊢ |={⊤}=> (dfree g ∗ dshot g) ∨ ⌜t = 0 ∨ knd M t = 2 ∨ knd M t = 3⌝ := by
  iintro #Hctx
  cases t with
  | zero => imodintro; iright; ipureintro; exact .inl rfl
  | succ k =>
    obtain ⟨m, hm, hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hb)
    have hmt : msgAt M (k + 1) = some m := by simpa [msgAt] using hm
    rcases kind_L1 hj (by rw [hba]; rfl) with h | h | h
    · imodintro; iright; ipureintro; exact .inr (.inl (by rw [knd_of hmt]; exact h))
    · imodintro; iright; ipureintro; exact .inr (.inr (by rw [knd_of hmt]; exact h))
    · imod pCtx_read_dead g M sv hdd (msgAt_le hmt) (by rw [knd_of hmt]; exact h) $$ Hctx with ⟨#Hf, #Hd⟩
      imodintro; ileft; iframe Hf Hd

/-- The L1 byte a classified source holds. -/
theorem l1_val {M : List PMsg} {t j : Nat} {v : BitVec 8} (hj : j < 4) (hb : memByte img4 M t (L1 + j) = some v)
    (hc : t = 0 ∨ knd M t = 2 ∨ knd M t = 3) :
    some v = (toBytes (if knd M t = 3 then 0 else 1) 4)[j]? := by
  rcases hc with rfl | hk | hk
  · have h0 : knd M 0 = 0 := rfl
    rw [h0]; simp only [show (0 : Nat) ≠ 3 by decide, if_false]
    rw [← img4_L1 j hj]; exact hb.symm
  · cases t with
    | zero => cases hk
    | succ k =>
      obtain ⟨m, hm, hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hb)
      have hmt : msgAt M (k + 1) = some m := by simpa [msgAt] using hm
      rw [knd_of hmt] at hk ⊢
      rw [hk]; simp only [show (2 : Nat) ≠ 3 by decide, if_false]
      have ha := kind_2 hk
      rw [← hba, ← ha.2.1, ← ha.1, byteAt_off rfl]
  · cases t with
    | zero => cases hk
    | succ k =>
      obtain ⟨m, hm, hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hb)
      have hmt : msgAt M (k + 1) = some m := by simpa [msgAt] using hm
      rw [knd_of hmt] at hk ⊢
      rw [hk]; simp only [if_true]
      have ha := kind_3 hk
      rw [← hba, ← ha.2.1, ← ha.1, byteAt_off rfl]

/-- The L1 release tokens. -/
def tk1 (M : List PMsg) (sv : SV) : IProp GF := iprop([∗list] t ∈ (rng M).filter (isK M 3), token (sv.tk t))

/-- **THE L1 ACQUIRE** (see the header): at the AMO's continuation (frontier `≥ ts`, one credit). -/
theorem l1_acq (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = dd4 M) {π : Proto}
    {ws2 ws1 : PState} {tvs : List (Nat × BitVec 8)} {ts : Nat} (hlen : tvs.length = 4)
    (hm : bytesAll (fun a t v => memByte img4 M t a = some v) L1 tvs)
    (hsrc : bytesAll (fun x u _ => u ≤ coh ws2 x) L1 tvs) (hcohB : ∀ j : Nat, j < 4 → coh ws2 (L1 + j) < ts)
    (hts : ts ≤ wfr ws1) :
    pCtx (GF := GF) g M sv ∗ frontA g π img4 M ws1 ∗ tk1 M sv ∗ £ 1 ⊢
      |={⊤}=> (dfree g ∗ dshot g) ∨ (tk1 M sv ∗ ⌜tvs.map Prod.snd = toBytes 1 4⌝) ∨
        (⌜tvs.map Prod.snd = toBytes 0 4⌝ ∗ ∃ s, ⌜s < ts⌝ ∗ Pub1 g M sv s) := by
  iintro ⟨#Hctx, #Hfr, Htk, Hc⟩
  obtain ⟨t0, v0, t1, v1, t2, v2, t3, v3, rfl⟩ : ∃ t0 v0 t1 v1 t2 v2 t3 v3,
      tvs = [(t0, v0), (t1, v1), (t2, v2), (t3, v3)] := by
    match tvs, hlen with
    | [(a, b), (c, d), (e, f), (i, j)], _ => exact ⟨a, b, c, d, e, f, i, j, rfl⟩
  have hb : ∀ (j t : Nat) (v : BitVec 8), j < 4 → [(t0, v0), (t1, v1), (t2, v2), (t3, v3)][j]? = some (t, v) →
      memByte img4 M t (L1 + j) = some v ∧ t < ts := fun j t v hj hg =>
    ⟨bytesAll_get hm hg, Nat.lt_of_le_of_lt (bytesAll_get hsrc hg) (hcohB j hj)⟩
  obtain ⟨hb0, hs0⟩ := hb 0 t0 v0 (by decide) rfl
  obtain ⟨hb1, _⟩ := hb 1 t1 v1 (by decide) rfl
  obtain ⟨hb2, _⟩ := hb 2 t2 v2 (by decide) rfl
  obtain ⟨hb3, _⟩ := hb 3 t3 v3 (by decide) rfl
  imod l1_src g M sv hdd (j := 0) (by decide) hb0 $$ Hctx with (⟨#Hf, #Hd⟩ | %hc0)
  · imodintro; ileft; iframe Hf Hd
  imod l1_src g M sv hdd (j := 1) (by decide) hb1 $$ Hctx with (⟨#Hf, #Hd⟩ | %hc1)
  · imodintro; ileft; iframe Hf Hd
  imod l1_src g M sv hdd (j := 2) (by decide) hb2 $$ Hctx with (⟨#Hf, #Hd⟩ | %hc2)
  · imodintro; ileft; iframe Hf Hd
  imod l1_src g M sv hdd (j := 3) (by decide) hb3 $$ Hctx with (⟨#Hf, #Hd⟩ | %hc3)
  · imodintro; ileft; iframe Hf Hd
  have hword : [v0, v1, v2, v3] = toBytes (if knd M t0 = 3 then 0 else 1) 4 :=
    lk_word (by split <;> simp) (by split <;> simp) (by split <;> simp) (by split <;> simp)
      (l1_val (by decide) hb0 hc0) (l1_val (by decide) hb1 hc1) (l1_val (by decide) hb2 hc2)
      (l1_val (by decide) hb3 hc3)
  have hmap : [(t0, v0), (t1, v1), (t2, v2), (t3, v3)].map Prod.snd = [v0, v1, v2, v3] := rfl
  by_cases h3 : knd M t0 = 3
  · rw [if_pos h3] at hword
    have ht0 : 1 ≤ t0 := by
      cases t0 with
      | zero => cases h3
      | succ k => omega
    have ht0M : t0 ≤ M.length := by
      cases hmt : msgAt M t0 with
      | none => unfold knd at h3; rw [hmt] at h3; cases h3
      | some m => exact (msgAt_le hmt).2
    ihave #Hft := frontA_get t0 $$ Hfr %⟨ht0, ht0M, by omega⟩
    unfold fulT
    icases Hft with (#Hsh | ⟨#Hf, _⟩)
    · unfold tk1
      icases bsl_filter_take (fun t => token (GF := GF) (sv.tk t)) (isK M 3) (fun _ => false) t0
        (by simp [isK, h3]) (fun _ h => by cases h) (rng M) (mem_rng.2 ⟨ht0, ht0M⟩) (nodup_rng M) $$ Htk
        with ⟨Ht, -⟩
      unfold pCtx
      icases Hctx with ⟨-, Hl1, -⟩
      ihave #Hsl := bsl_mem (F := fun t => l1Slot g M sv t)
        (List.mem_filter.2 ⟨mem_rng.2 ⟨ht0, ht0M⟩, by simp [isK, h3]⟩) $$ Hl1
      imod l1_claim g M sv t0 $$ [Ht Hc] with HP
      · iframe Hsl Hsh Ht Hc
      imodintro; iright; iright
      isplitr
      · ipureintro; rw [hmap, hword]
      · iexists t0; iframe HP; ipureintro; exact hs0
    · imod pCtx_free g M sv $$ [] with ⟨#Hf', #Hd⟩
      · iframe Hctx Hf
      imodintro; ileft; iframe Hf' Hd
  · rw [if_neg h3] at hword
    imodintro; iright; ileft; iframe Htk; ipureintro; rw [hmap, hword]

/-! ## The L2 acquire -/

/-- Hart 1's L2 releases (its own; `pend`s). -/
def r2Bag (g : AGN) (M : List PMsg) : IProp GF := iprop([∗list] t ∈ bagK M 5 0, pend g t)

instance (g : AGN) (M : List PMsg) : Timeless (r2Bag (GF := GF) g M) := by
  unfold r2Bag; exact BigSepL.bigSepL_timeless (fun _ => inferInstance)

/-- The birth writes every L2 byte. -/
theorem bth_wr {M : List PMsg} {b j : Nat} (hj : j < 4) (hb : bthAt M Lk b) : wrB M (Lk + j) b := by
  obtain ⟨m, hm, hp, hd, _⟩ := hb
  refine ⟨m, hm, ?_⟩
  rw [← hp, byteAt_off rfl, hd, List.getElem?_eq_getElem (by rw [toBytes_length]; exact hj)]; rfl

/-- **AN L2 BYTE** read with a floor above the birth `b`, below the frontier: from `b`, from hart 1's AMO writes, or
free mode (R-a4: the junk and the image lie below `b`; hart 0's later words and hart 1's own releases are held). -/
theorem l2_src (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = dd4 M) {π : Proto} {ws1 : PState}
    {b t j fl : Nat} {v : BitVec 8} (hj : j < 4) (hb : bthAt M Lk b) (hbf : b ≤ fl)
    (hm : memByte img4 M t (Lk + j) = some v) (hr : ¬ writesIn M (Lk + j) t fl) (ht : t ≤ wfr ws1) :
    pCtx (GF := GF) g M sv ∗ frontA g π img4 M ws1 ∗ r2Bag g M ∗ zBag g M b ⊢
      |={⊤}=> (dfree g ∗ dshot g) ∨ (r2Bag g M ∗ zBag g M b ∗ ⌜t = b ∨ knd M t = 4⌝) := by
  iintro ⟨#Hctx, #Hfr, Hr2, Hz⟩
  have hwb := bth_wr hj hb
  have hbt : b ≤ t := by
    apply Classical.byContradiction; intro hlt
    obtain ⟨m, hm', hba⟩ := hwb
    obtain ⟨k, hk⟩ : ∃ k, b = k + 1 := by
      cases b with
      | zero => cases hm'
      | succ k => exact ⟨k, rfl⟩
    exact hr ⟨b, by omega, hbf, m, by rw [hk] at hm' ⊢; simpa [msgAt] using hm', hba⟩
  by_cases heq : t = b
  · imodintro; iright; iframe Hr2 Hz; ipureintro; exact .inl heq
  have hlt : b < t := by omega
  cases t with
  | zero => omega
  | succ k =>
    obtain ⟨m, hm', hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hm)
    have hmt : msgAt M (k + 1) = some m := by simpa [msgAt] using hm'
    have htM := msgAt_le hmt
    ihave #Hft := frontA_get (k + 1) $$ Hfr %⟨htM.1, htM.2, ht⟩
    rcases kind_L2 hj (by rw [hba]; rfl) with h | h | h | h
    · imodintro; iright; iframe Hr2 Hz; ipureintro; exact .inr (by rw [knd_of hmt]; exact h)
    · -- hart 1's own release, not yet fulfilled: its `pend` is held
      unfold r2Bag bagK
      icases bsl_filter_take (pend g) (fun t => decide (0 < t) && isK M 5 t) (fun _ => false) (k + 1)
        (by simp [isK, knd_of hmt, h]) (fun _ h => by cases h) (rng M) (mem_rng.2 htM) (nodup_rng M) $$ Hr2
        with ⟨Hp, -⟩
      unfold fulT
      icases Hft with (#Hsh | ⟨#Hf, _⟩)
      · iexfalso; iapply pend_shot; iframe Hp Hsh
      · imod pCtx_free g M sv $$ [] with ⟨#Hf', #Hd⟩
        · iframe Hctx Hf
        imodintro; ileft; iframe Hf' Hd
    · -- hart 0's later L2 word: its `pend` came with the handle
      unfold zBag bagK
      icases bsl_filter_take (pend g) (fun t => decide (b < t) && isK M 6 t) (fun _ => false) (k + 1)
        (by simp [isK, knd_of hmt, h]; omega) (fun _ h => by cases h) (rng M) (mem_rng.2 htM) (nodup_rng M)
        $$ Hz with ⟨Hp, -⟩
      unfold fulT
      icases Hft with (#Hsh | ⟨#Hf, _⟩)
      · iexfalso; iapply pend_shot; iframe Hp Hsh
      · imod pCtx_free g M sv $$ [] with ⟨#Hf', #Hd⟩
        · iframe Hctx Hf
        imodintro; ileft; iframe Hf' Hd
    · imod pCtx_read_dead g M sv hdd htM (by rw [knd_of hmt]; exact h) $$ Hctx with ⟨#Hf, #Hd⟩
      imodintro; ileft; iframe Hf Hd

/-- The L2 byte a classified source holds. -/
theorem l2_val {M : List PMsg} {b t j : Nat} {v : BitVec 8} (hj : j < 4) (hb : bthAt M Lk b)
    (hm : memByte img4 M t (Lk + j) = some v) (hc : t = b ∨ knd M t = 4) :
    some v = (toBytes (if knd M t = 4 then 1 else 0) 4)[j]? := by
  rcases hc with rfl | hk
  · obtain ⟨m, hmt, hp, hd, _⟩ := hb
    have hk : knd M t ≠ 4 := by
      rw [knd_of hmt]; intro h4; have := (kind_4 h4).2.1; rw [hd] at this; exact absurd this (by decide)
    rw [if_neg hk]
    cases t with
    | zero => cases hmt
    | succ k =>
      have hm' : M[k]? = some m := by simpa [msgAt] using hmt
      simp only [memByte, hm', Option.bind_some] at hm
      rw [← hm, ← hd, ← hp, byteAt_off rfl]
  · cases t with
    | zero => cases hk
    | succ k =>
      obtain ⟨m, hm', hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hm)
      have hmt : msgAt M (k + 1) = some m := by simpa [msgAt] using hm'
      rw [knd_of hmt] at hk ⊢
      rw [hk]; simp only [if_true]
      have ha := kind_4 hk
      rw [← hba, ← ha.2.1, ← ha.1, byteAt_off rfl]

/-- **THE L2 ACQUIRE** (see the header): at the AMO's continuation (frontier `≥ ts`). -/
theorem l2_acq (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = dd4 M) {π : Proto}
    {ws ws2 ws1 : PState} {tvs : List (Nat × BitVec 8)} {ts vpre b : Nat} (hlen : tvs.length = 4)
    (hlo1 : loadOk img4 M ws vpre Lk tvs) (hb : bthAt M Lk b) (hbv : b ≤ vpre)
    (hsrc : bytesAll (fun x u _ => u ≤ coh ws2 x) Lk tvs) (hcohB : ∀ j : Nat, j < 4 → coh ws2 (Lk + j) < ts)
    (hts : ts ≤ wfr ws1) :
    pCtx (GF := GF) g M sv ∗ frontA g π img4 M ws1 ∗ r2Bag g M ∗ zBag g M b ⊢
      |={⊤}=> (dfree g ∗ dshot g) ∨ (r2Bag g M ∗ zBag g M b ∗
        ⌜tvs.map Prod.snd = toBytes 1 4 ∨ tvs.map Prod.snd = toBytes 0 4⌝) := by
  iintro ⟨#Hctx, #Hfr, Hr2, Hz⟩
  obtain ⟨t0, v0, t1, v1, t2, v2, t3, v3, rfl⟩ : ∃ t0 v0 t1 v1 t2 v2 t3 v3,
      tvs = [(t0, v0), (t1, v1), (t2, v2), (t3, v3)] := by
    match tvs, hlen with
    | [(a, b), (c, d), (e, f), (i, j)], _ => exact ⟨a, b, c, d, e, f, i, j, rfl⟩
  have hw := loadOk_weak hlo1
  -- each byte: its value, below the frontier, and either no write between it and a floor above `b`, or dead
  have hbyte : ∀ (j t : Nat) (v : BitVec 8), j < 4 → [(t0, v0), (t1, v1), (t2, v2), (t3, v3)][j]? = some (t, v) →
      memByte img4 M t (Lk + j) = some v ∧ t ≤ wfr ws1 ∧
        ((∃ fl, b ≤ fl ∧ ¬ writesIn M (Lk + j) t fl) ∨ ∃ ti, 1 ≤ ti ∧ cmoAt M isInvalK ti (Lk + j)) :=
    fun j t v hj hg => by
      have h1 := bytesAll_get hw hg
      refine ⟨h1.1, by have := Nat.lt_of_le_of_lt (bytesAll_get hsrc hg) (hcohB j hj); omega, ?_⟩
      rcases h1.2 with ⟨fl, hfl, h⟩ | ⟨fl, hfl, ti, hc, hti, _⟩
      · exact .inl ⟨fl, by omega, h⟩
      · exact .inr ⟨ti, by omega, hc⟩
  have step : ∀ (j t : Nat) (v : BitVec 8), j < 4 → [(t0, v0), (t1, v1), (t2, v2), (t3, v3)][j]? = some (t, v) →
      pCtx (GF := GF) g M sv ∗ frontA g π img4 M ws1 ∗ r2Bag g M ∗ zBag g M b ⊢
        |={⊤}=> (dfree g ∗ dshot g) ∨ (r2Bag g M ∗ zBag g M b ∗ ⌜some v = (toBytes (if knd M t = 4 then 1 else 0) 4)[j]?
          ∧ (t = b ∨ knd M t = 4)⌝) := fun j t v hj hg => by
    obtain ⟨hm, hwf, hr⟩ := hbyte j t v hj hg
    iintro ⟨#Hctx', #Hfr', Hr2, Hz⟩
    rcases hr with ⟨fl, hfl, hr⟩ | ⟨ti, hti, hc⟩
    · imod l2_src g M sv hdd (π := π) (ws1 := ws1) hj hb hfl hm hr hwf $$ [Hr2 Hz] with (⟨#Hf, #Hd⟩ | ⟨Hr2, Hz, %hc⟩)
      · iframe Hctx' Hfr' Hr2 Hz
      · imodintro; ileft; iframe Hf Hd
      · imodintro; iright; iframe Hr2 Hz; ipureintro; exact ⟨l2_val hj hb hm hc, hc⟩
    · obtain ⟨hk, hle⟩ := cmo_knd hti hc
      imod pCtx_read_dead g M sv hdd ⟨hti, hle⟩ hk $$ Hctx' with ⟨#Hf, #Hd⟩
      imodintro; ileft; iframe Hf Hd
  imod step 0 t0 v0 (by decide) rfl $$ [Hr2 Hz] with (⟨#Hf, #Hd⟩ | ⟨Hr2, Hz, %hc0⟩)
  · iframe Hctx Hfr Hr2 Hz
  · imodintro; ileft; iframe Hf Hd
  imod step 1 t1 v1 (by decide) rfl $$ [Hr2 Hz] with (⟨#Hf, #Hd⟩ | ⟨Hr2, Hz, %hc1⟩)
  · iframe Hctx Hfr Hr2 Hz
  · imodintro; ileft; iframe Hf Hd
  imod step 2 t2 v2 (by decide) rfl $$ [Hr2 Hz] with (⟨#Hf, #Hd⟩ | ⟨Hr2, Hz, %hc2⟩)
  · iframe Hctx Hfr Hr2 Hz
  · imodintro; ileft; iframe Hf Hd
  imod step 3 t3 v3 (by decide) rfl $$ [Hr2 Hz] with (⟨#Hf, #Hd⟩ | ⟨Hr2, Hz, %hc3⟩)
  · iframe Hctx Hfr Hr2 Hz
  · imodintro; ileft; iframe Hf Hd
  have hword : [v0, v1, v2, v3] = toBytes (if knd M t0 = 4 then 1 else 0) 4 :=
    lk_word (by split <;> simp) (by split <;> simp) (by split <;> simp) (by split <;> simp)
      hc0.1 hc1.1 hc2.1 hc3.1
  have hmap : [(t0, v0), (t1, v1), (t2, v2), (t3, v3)].map Prod.snd = [v0, v1, v2, v3] := rfl
  imodintro; iright; iframe Hr2 Hz; ipureintro
  rw [hmap, hword]
  by_cases h4 : knd M t0 = 4
  · rw [if_pos h4]; exact .inl rfl
  · rw [if_neg h4]; exact .inr rfl

/-- In the 0 case, byte 0 came from the birth. -/
theorem l2_src0 (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = dd4 M) {π : Proto}
    {ws ws2 ws1 : PState} {tvs : List (Nat × BitVec 8)} {ts vpre b : Nat} (hlen : tvs.length = 4)
    (hlo1 : loadOk img4 M ws vpre Lk tvs) (hb : bthAt M Lk b) (hbv : b ≤ vpre)
    (hsrc : bytesAll (fun x u _ => u ≤ coh ws2 x) Lk tvs) (hcohB : ∀ j : Nat, j < 4 → coh ws2 (Lk + j) < ts)
    (hts : ts ≤ wfr ws1) (h0 : tvs.map Prod.snd = toBytes 0 4) :
    pCtx (GF := GF) g M sv ∗ frontA g π img4 M ws1 ∗ r2Bag g M ∗ zBag g M b ⊢
      |={⊤}=> (dfree g ∗ dshot g) ∨ (r2Bag g M ∗ zBag g M b ∗ ⌜∃ v r, tvs = (b, v) :: r⌝) := by
  iintro ⟨#Hctx, #Hfr, Hr2, Hz⟩
  obtain ⟨t0, v0, r, rfl⟩ := tvs_cons hlen (by decide)
  have hw := loadOk_weak hlo1
  have h1 := bytesAll_get (j := 0) hw rfl
  have hwf : t0 ≤ wfr ws1 := by
    have := Nat.lt_of_le_of_lt (bytesAll_get (j := 0) hsrc rfl) (hcohB 0 (by decide)); omega
  rcases h1.2 with ⟨fl, hfl, hr⟩ | ⟨fl, hfl, ti, hc, hti, _⟩
  · imod l2_src g M sv hdd (π := π) (ws1 := ws1) (j := 0) (by decide) hb (by omega) h1.1 hr hwf
      $$ [Hr2 Hz] with (⟨#Hf, #Hd⟩ | ⟨Hr2, Hz, %hc⟩)
    · iframe Hctx Hfr Hr2 Hz
    · imodintro; ileft; iframe Hf Hd
    · rcases hc with hc | hk
      · imodintro; iright; iframe Hr2 Hz; ipureintro; exact ⟨v0, r, by rw [hc]⟩
      · have hv := l2_val (j := 0) (by decide) hb h1.1 (.inr hk)
        rw [if_pos hk] at hv
        have hv0 : some v0 = (toBytes 0 4)[0]? := by
          have : (List.map Prod.snd ((t0, v0) :: r))[0]? = (toBytes 0 4)[0]? := by rw [h0]
          simpa using this
        rw [hv0] at hv; exact absurd hv (by decide)
  · obtain ⟨hk, hle⟩ := cmo_knd (by omega) hc
    imod pCtx_read_dead g M sv hdd ⟨by omega, hle⟩ hk $$ Hctx with ⟨#Hf, #Hd⟩
    imodintro; ileft; iframe Hf Hd

/-- **THE ATOMICITY STEP of L2** (plan §3 "Atomicity", as (1a)'s `lk_chain`): the AMO at `ts` that read byte 0 of L2
from `b` is the first L2 write after `b` — another hart's write in between contradicts `exclOk`; one of hart 1's own
writes at or below its coherence floor contradicts coherence; one above it is held in its bag (or its release
bag) and fulfilled by the frontier — absurd — or dead. -/
theorem l2_chain (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = dd4 M) {π : Proto} {ws1 ws : PState}
    {lo b ts vpre : Nat} (hbt : b < ts) (hts : ts ≤ wfr ws1) (hwts : wrB M Lk ts) (hlo : lo ≤ coh ws Lk)
    (hr : ¬ writesIn M Lk b (max vpre (coh ws Lk)))
    (hx : ¬ writesInBy M (fun tid => tid ≠ some 1) Lk b (ts - 1)) :
    pCtx (GF := GF) g M sv ∗ frontA g π img4 M ws1 ∗ ob2 g M sv lo ts ∗ r2Bag g M ⊢
      |={⊤}=> (ob2 g M sv lo ts ∗ r2Bag g M ∗ ⌜nxtL M b ts⌝) ∨ (dfree g ∗ dshot g) := by
  iintro ⟨#Hctx, #Hfr, Hbag, Hr2⟩
  by_cases hn : nxtL M b ts
  · imodintro; ileft; iframe Hbag Hr2; ipureintro; exact hn
  have hex : ∃ v, b < v ∧ v < ts ∧ wrB M Lk v := by
    apply Classical.byContradiction; intro hne
    exact hn ⟨hbt, hwts, fun v h1 h2 h3 => hne ⟨v, h1, h2, h3⟩⟩
  obtain ⟨v, hv1, hv2, hwv⟩ := hex
  obtain ⟨m, hmv, hbv⟩ := hwv
  have hvM := msgAt_le hmv
  have htid : tidAt M v = some 1 := by
    apply Classical.byContradiction; intro hne
    exact chain_excl hv1 hv2 ⟨m, hmv, hbv⟩ hne hx
  have hvl : lo < v := by
    apply Classical.byContradiction; intro hle
    exact chain_coh hv1 (by omega) ⟨m, hmv, hbv⟩ hr
  ihave #Hft := frontA_get v $$ Hfr %⟨hvM.1, hvM.2, by omega⟩
  have hb0 : (m.byteAt (Lk + ((0 : Nat) : Int))).isSome = true := by simpa using hbv
  rcases kind_L2 (by decide) hb0 with h | h | h | h
  · -- an own L2 AMO write above the floor: its `pend` is in the bag
    unfold ob2 bagKX
    icases Hbag with ⟨Hb, -⟩
    icases bsl_filter_take (pend g) (fun t => decide (lo < t) && decide (t ≠ ts) && isK M 4 t) (fun _ => false) v
      (by simp [hvl, show v ≠ ts by omega, isK, knd_of hmv, h]) (fun _ h => by cases h) (rng M) (mem_rng.2 hvM)
      (nodup_rng M) $$ Hb with ⟨Hp, -⟩
    unfold fulT
    icases Hft with (#Hsh | ⟨#Hf, _⟩)
    · iexfalso; iapply pend_shot; iframe Hp Hsh
    · imod pCtx_free g M sv $$ [] with ⟨#Hf', #Hd⟩
      · iframe Hctx Hf
      imodintro; iright; iframe Hf' Hd
  · -- an own L2 release
    unfold r2Bag bagK
    icases bsl_filter_take (pend g) (fun t => decide (0 < t) && isK M 5 t) (fun _ => false) v
      (by simp [isK, knd_of hmv, h]; omega) (fun _ h => by cases h) (rng M) (mem_rng.2 hvM) (nodup_rng M) $$ Hr2
      with ⟨Hp, -⟩
    unfold fulT
    icases Hft with (#Hsh | ⟨#Hf, _⟩)
    · iexfalso; iapply pend_shot; iframe Hp Hsh
    · imod pCtx_free g M sv $$ [] with ⟨#Hf', #Hd⟩
      · iframe Hctx Hf
      imodintro; iright; iframe Hf' Hd
  · -- hart 0's word: not hart 1's
    have := (kind_6 h).2.2.2
    simp [tidAt, hmv, this] at htid
  · -- dead
    ihave #Hdi := pCtx_dead g M sv hvM (by rw [knd_of hmv]; exact h) $$ Hctx
    unfold pCtx
    icases Hctx with ⟨Hdoom, -⟩
    imod dead_shot g M v $$ [] with ⟨#Hf, #Hs⟩
    · iframe Hdoom Hdi Hft
    imodintro; iright; iframe Hf Hs

end lib

end Weak.Prom.OA.P
