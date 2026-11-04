/-
Weak/Prom: **G4 (4) on track (b): the hart steps of the lock-birth protocol** (stage S4b part 3, tag S4b3; plan
rev 7 §3 "Lock birth and deferred deposits", §4 (b1-def)).  See OwnLock4Defs.lean for the test and the protocol.

* `h0_init` — THE BIRTH STORE (plain, any class): H0's progress 2, the birth cell `ti`, THE RUNTIME NAME `γ`; the
  other pending birth-shaped promises die;
* `h0_cnt` — the data store (42); `h0_pub` — THE PUBLISH (release-class, in place): THE DEFERRED DEPOSIT (R's
  place 0 → 1), with `ti, tc < tf` from H0's views;
* `h1_flag` — H1's read of the flag: the publish (so deposited) or a dead message;
* `h1_src` — THE ACQUIRE'S SOURCE: an acquire above the publish whose byte-0 answer is 0 read the born cell `ti`
  (H0's `ti` is the last other-hart write below it, `exclOk`) or a dead message; `h1_take` (R's place 1 → 2) /
  `h1_fail`;
* `h1_cread` — the holder's read of the counter: 42 or a dead message; `i4_setBad`, `i4_fin`, `i4_final`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnLock4Defs

namespace Weak.Prom.Own.L4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert Weak.Prom.Own
open Weak.Prom.Own.MP (wrA au memByte_take wrA_of_memByte memByte_inj take_get)
open Weak.Prom.Own.MPL (X Y XRec xVal wrX toBytes_get relPrG xMsg xMsg_byte bytesAll_get map_snd_of)
open Weak.Prom.Own.Lk (pend ful_facts pend_iff)
open Weak.Prom.Ref (Instr Test two64)
open PLabel

section steps2

variable {img : Image} {M : List PMsg}

/-- **THE BIRTH STORE** `sw x0,0(x10)` (plain; a promise or in place): the lock is born at `ts`, and THE RUNTIME
NAME `γ` of R's ghost is recorded. -/
theorem h0_init {σ σ' : OSt (List Nat)} {g : S4} {ts : Nat} {rc : Prop} (hok : I4 img M σ g)
    (hp0 : g.p0 = 1) (hful : fulO M 0 σ rc ts σ') (hM : M[ts - 1]? = some initMsg) (γc : Nat) :
    I4 img M σ' { g with p0 := 2, ti := ts, γ := some γc,
                         Dd := fun t => g.Dd t ∨ (pend M σ' t ∧ M[t - 1]? = some initMsg) } := by
  obtain ⟨hdone, hn1, hn2, htsn, hts1, hpr, hcase⟩ := ful_facts hok.pr hful
  have hnd : ¬ g.Dd ts := fun hd => by have := hok.dd_i ts hd hM; omega
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, hp⟩ := i4_frame (g' := { g with p0 := 2, ti := ts, γ := some γc,
                                                                      Dd := fun t => g.Dd t ∨ (pend M σ' t ∧ M[t - 1]? = some initMsg) }) hok hful hnd
    (fun t => ⟨fun h => by rcases h with h | ⟨h1, h2⟩; exact .inl h; exact .inr ⟨h1, .inl ⟨h2, by simp⟩⟩,
      fun h => by rcases h with h | ⟨h1, ⟨h2, _⟩ | ⟨_, h3⟩⟩; exact .inl h; exact .inr ⟨h1, h2⟩; simp at h3⟩)
    (by simp only; omega)
  refine ⟨f1, f2, f3, f4, f5, f6, f7, fun hb => ?_, by simp, fun _ => ?_, fun _ => ⟨hts1, htsn, hM⟩,
    fun h => by simp at h, fun h => by simp at h, fun t h1 h2 h3 => ?_, by simp, ?_, hok.p1le, fun h => ?_,
    fun h => ?_, fun h => ?_, hok.bd1, fun gg hg => hok.done gg (by rw [← hdone]; exact hg)⟩
  · obtain ⟨t, ht⟩ := hok.bad hb; exact ⟨t, .inl ht⟩
  · obtain ⟨u1, u2, u3⟩ := hok.h0j (by omega); exact ⟨u1, by show g.tj ≤ σ'.n; omega, u3⟩
  · by_cases e : t = ts
    · exact .inr (.inl ⟨by simp, e⟩)
    · obtain ⟨u1, u2⟩ := ful_old hok hful h2 e h3
      rcases hok.ful t h1 u1 u2 with ⟨_, u⟩ | ⟨u, _⟩ | ⟨u, _⟩ | ⟨u, _⟩ | u
      · exact .inl ⟨by simp, u⟩
      · omega
      · omega
      · omega
      · exact .inr (.inr (.inr (.inr u)))
  · obtain ⟨r1, r2, r3⟩ := hok.rp_ok
    exact ⟨r1, by show g.rp = 0 ↔ 2 < 4; rw [r2, hp0]; simp, r3⟩
  · have := (hok.p1a h).1; omega
  · obtain ⟨u1, u2, u3⟩ := hok.p1t h; exact ⟨u1, by show g.ta ≤ σ'.n; omega, u3⟩
  · have := (hok.p1a (.inr h)).1; omega

/-- **THE DATA STORE** `sd x5,(x11)` (c := 42; a promise or in place). -/
theorem h0_cnt {σ σ' : OSt (List Nat)} {g : S4} {ts : Nat} {rc : Prop} (hok : I4 img M σ g)
    (hp0 : g.p0 = 2) (hful : fulO M 0 σ rc ts σ') (hM : M[ts - 1]? = some xMsg) :
    I4 img M σ' { g with p0 := 3, tc := ts, Dd := fun t => g.Dd t ∨ (pend M σ' t ∧ M[t - 1]? = some xMsg) } := by
  obtain ⟨hdone, hn1, hn2, htsn, hts1, hpr, hcase⟩ := ful_facts hok.pr hful
  have hpi := pend_iff (M := M) hpr
  have hnd : ¬ g.Dd ts := fun hd => by have := hok.dd_c ts hd hM; omega
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, hp⟩ := i4_frame (g' := { g with p0 := 3, tc := ts,
                                                                      Dd := fun t => g.Dd t ∨ (pend M σ' t ∧ M[t - 1]? = some xMsg) }) hok hful hnd
    (fun t => ⟨fun h => by rcases h with h | ⟨h1, h2⟩; exact .inl h; exact .inr ⟨h1, .inr ⟨h2, by simp⟩⟩,
      fun h => by
        rcases h with h | ⟨h1, ⟨h2, _⟩ | ⟨h2, _⟩⟩
        · exact .inl h
        · left
          rcases hok.cand_i t ((hpi t).1 h1).1 h2 with u | u
          · omega
          · exact u
        · exact .inr ⟨h1, h2⟩⟩)
    (by simp only; omega)
  refine ⟨f1, f2, f3, f4, f5, f6, f7, fun hb => ?_, by simp, fun _ => ?_, fun _ => ?_, fun _ => ⟨hts1, htsn, hM⟩,
    fun h => by simp at h, fun t h1 h2 h3 => ?_, ?_, ?_, hok.p1le, fun h => ?_,
    fun h => ?_, fun h => ?_, hok.bd1, fun gg hg => hok.done gg (by rw [← hdone]; exact hg)⟩
  · obtain ⟨t, ht⟩ := hok.bad hb; exact ⟨t, .inl ht⟩
  · obtain ⟨u1, u2, u3⟩ := hok.h0j (by omega); exact ⟨u1, by show g.tj ≤ σ'.n; omega, u3⟩
  · obtain ⟨u1, u2, u3⟩ := hok.h0i (by omega); exact ⟨u1, by show g.ti ≤ σ'.n; omega, u3⟩
  · by_cases e : t = ts
    · exact .inr (.inr (.inl ⟨by simp, e⟩))
    · obtain ⟨u1, u2⟩ := ful_old hok hful h2 e h3
      rcases hok.ful t h1 u1 u2 with ⟨_, u⟩ | ⟨_, u⟩ | ⟨u, _⟩ | ⟨u, _⟩ | u
      · exact .inl ⟨by simp, u⟩
      · exact .inr (.inl ⟨by simp, u⟩)
      · omega
      · omega
      · exact .inr (.inr (.inr (.inr u)))
  · show g.γ = none ↔ 3 < 2
    have := hok.γ_ok; rw [hp0] at this; simp at this; simp [this]
  · obtain ⟨r1, r2, r3⟩ := hok.rp_ok
    exact ⟨r1, by show g.rp = 0 ↔ 3 < 4; rw [r2, hp0]; simp, r3⟩
  · have := (hok.p1a h).1; omega
  · obtain ⟨u1, u2, u3⟩ := hok.p1t h; exact ⟨u1, by show g.ta ≤ σ'.n; omega, u3⟩
  · have := (hok.p1a (.inr h)).1; omega

/-- **THE PUBLISH** `sd x7,(x12)` after `fence rw,w` (release-class: in place) — THE DEFERRED DEPOSIT of the birth
store: R's place 0 → 1 (the born cell). H0's views give `ti, tc < tf`. -/
theorem h0_pub {σ σ' : OSt (List Nat)} {g : S4} {ts : Nat} {rc : Prop} (hok : I4 img M σ g)
    (hp0 : g.p0 = 3) (hrc : rc) (hful : fulO M 0 σ rc ts σ') (hM : M[ts - 1]? = some flagMsg)
    (hti : g.ti < ts) (htc : g.tc < ts) :
    I4 img M σ' { g with p0 := 4, tf := ts, rp := 1 } := by
  obtain ⟨hdone, hn1, hn2, htsn, hts1, hpr, hcase⟩ := ful_facts hok.pr hful
  have hpi := pend_iff (M := M) hpr
  obtain ⟨ets, hn', _, _⟩ : ts = σ.n + 1 ∧ σ'.n = σ.n + 1 ∧ rc ∧ au M ts = some 0 := by
    rcases hcase with ⟨_, _, hnr⟩ | h4
    · exact absurd hrc hnr
    · exact h4
  have hnd : ¬ g.Dd ts := fun hd => by have := (pend_le hok (hok.dd ts hd)).2; omega
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, hp⟩ := i4_frame (g' := { g with p0 := 4, tf := ts, rp := 1 }) hok hful hnd
    (fun t => ⟨fun h => .inl h, fun h => by
      rcases h with h | ⟨h1, ⟨h2, _⟩ | ⟨h2, _⟩⟩
      · exact h
      · rcases hok.cand_i t ((hpi t).1 h1).1 h2 with u | u
        · omega
        · exact u
      · rcases hok.cand_c t ((hpi t).1 h1).1 h2 with u | u
        · omega
        · exact u⟩)
    (by simp only; omega)
  refine ⟨f1, f2, f3, f4, f5, f6, f7, hok.bad, by simp, fun _ => ?_, fun _ => ?_, fun _ => ?_,
    fun _ => ⟨hts1, htsn, hM, hti, htc⟩, fun t h1 h2 h3 => ?_, ?_, ?_, hok.p1le, fun h => ?_,
    fun h => ?_, fun h => ?_, hok.bd1, fun gg hg => hok.done gg (by rw [← hdone]; exact hg)⟩
  · obtain ⟨u1, u2, u3⟩ := hok.h0j (by omega); exact ⟨u1, by show g.tj ≤ σ'.n; omega, u3⟩
  · obtain ⟨u1, u2, u3⟩ := hok.h0i (by omega); exact ⟨u1, by show g.ti ≤ σ'.n; omega, u3⟩
  · obtain ⟨u1, u2, u3⟩ := hok.h0c (by omega); exact ⟨u1, by show g.tc ≤ σ'.n; omega, u3⟩
  · by_cases e : t = ts
    · exact .inr (.inr (.inr (.inl ⟨by simp, e⟩)))
    · obtain ⟨u1, u2⟩ := ful_old hok hful h2 e h3
      rcases hok.ful t h1 u1 u2 with ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ | ⟨u, _⟩ | u
      · exact .inl ⟨by simp, u⟩
      · exact .inr (.inl ⟨by simp, u⟩)
      · exact .inr (.inr (.inl ⟨by simp, u⟩))
      · omega
      · exact .inr (.inr (.inr (.inr u)))
  · show g.γ = none ↔ 4 < 2
    have := hok.γ_ok; rw [hp0] at this; simp at this; simp [this]
  · obtain ⟨r1, r2, r3⟩ := hok.rp_ok
    refine ⟨by simp, by simp, ?_⟩
    show 1 = 2 ↔ g.p1 = 2
    have : g.p1 ≠ 2 := fun e => by have := (hok.p1a (.inr e)).1; omega
    simp [this]
  · have := (hok.p1a h).1; omega
  · obtain ⟨u1, u2, u3⟩ := hok.p1t h; exact ⟨u1, by show g.ta ≤ σ'.n; omega, u3⟩
  · have := (hok.p1a (.inr h)).1; omega

/-- H1 saw the publication (`a1 := tf`). -/
theorem h1_saw {σ : OSt (List Nat)} {g : S4} (hok : I4 img M σ g) (hp1 : g.p1 = 0) (hp0 : g.p0 = 4) :
    I4 img M σ { g with p1 := 1, a1 := g.tf } := by
  obtain ⟨r1, r2, r3⟩ := hok.rp_ok
  refine ⟨hok.pr, hok.dd, hok.dd_i, hok.dd_c, hok.cls, hok.cand_i, hok.cand_c, hok.bad, hok.p0le, hok.h0j,
    hok.h0i, hok.h0c, hok.h0f, fun t h1 h2 h3 => ?_, hok.γ_ok, ⟨r1, r2, ?_⟩, by simp, fun _ => ⟨hp0, rfl⟩,
    fun h => by simp at h, fun h => by simp at h, hok.bd1, hok.done⟩
  · rcases hok.ful t h1 h2 h3 with u | u | u | u | ⟨u, _⟩
    · exact .inl u
    · exact .inr (.inl u)
    · exact .inr (.inr (.inl u))
    · exact .inr (.inr (.inr (.inl u)))
    · omega
  · show g.rp = 2 ↔ 1 = 2
    have : g.rp ≠ 2 := fun e => by have := r3.1 e; omega
    simp [this]

/-- **H1's READ OF THE FLAG**: a nonzero byte comes from the publish (so R is deposited) or a dead message. -/
theorem h1_flag {σ : OSt (List Nat)} {g : S4} {t j : Nat} {b : BitVec 8} (hok : I4 img M σ g)
    (hz : ∀ a, img a = some 0) (hj : j < 8) (hmb : memByte img M t (F + j) = some b) (htn : t ≤ σ.n)
    (hb : b ≠ 0) : (g.p0 = 4 ∧ t = g.tf) ∨ g.Dd t := by
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · simp only [memByte] at hmb; rw [hz] at hmb; cases hmb; exact absurd rfl hb
    · exact h
  have hwf : wrF M t := ⟨j, hj, wrA_of_memByte ht1 hmb⟩
  by_cases hp : pend M σ t
  · rcases hok.cls t hp with u | u | u
    · exact .inr u
    · exact absurd hwf (init_not_F u)
    · exact absurd hwf (xMsg_not_F u)
  · rcases hok.ful t ht1 htn hp with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨h4, rfl⟩ | ⟨_, rfl⟩
    · exact absurd hwf (junk_not_F (hok.h0j (by omega)).2.2)
    · exact absurd hwf (init_not_F (hok.h0i (by omega)).2.2)
    · exact absurd hwf (xMsg_not_F (hok.h0c (by omega)).2.2)
    · exact .inl ⟨by have := hok.p0le; omega, rfl⟩
    · exact absurd hwf (acq1_not_F (hok.p1t (by omega)).2.2)

/-- **THE ACQUIRE'S SOURCE** (plan (b1-def)): H1 (which saw the publication) acquires at `ts` above `tf`; a byte-0
answer 0 from `t0` with no H0 write to the lock byte in `(t0, ts)` is the born cell `ti` or a dead message. -/
theorem h1_src {σ : OSt (List Nat)} {g : S4} {t0 ts : Nat} {b0 : BitVec 8} (hok : I4 img M σ g)
    (hz : ∀ a, img a = some 0) (hp1 : g.p1 = 1) (htf : g.tf < ts) (hmb : memByte img M t0 Y = some b0)
    (ht0n : t0 ≤ σ.n) (hb0 : b0 = 0)
    (hwin : ∀ t, t0 < t → t < ts → wrL M t → au M t = some 1) : t0 = g.ti ∨ g.Dd t0 := by
  obtain ⟨hp0, _⟩ := hok.p1a (.inl hp1)
  obtain ⟨i1, i2, i3⟩ := hok.h0i (by omega)
  obtain ⟨_, _, _, h4, _⟩ := hok.h0f (by omega)
  have hti : g.ti ≤ t0 := by
    refine Classical.byContradiction fun hlt => ?_
    have := hwin g.ti (by omega) (by omega) ⟨initMsg, i3, by simp [init_b0]⟩
    simp [au, i3, initMsg] at this
  rcases Nat.lt_or_ge g.ti t0 with hlt | hge
  · right
    have ht1 : 1 ≤ t0 := by omega
    have hwl : wrL M t0 := wrA_of_memByte ht1 hmb
    have hbyte : ∀ m, M[t0 - 1]? = some m → m.byteAt Y = some 0 := by
      intro m hm; rw [memByte_of ht1 hm] at hmb; rw [hmb, hb0]
    by_cases hp : pend M σ t0
    · rcases hok.cls t0 hp with u | u | u
      · exact u
      · rcases hok.cand_i t0 hp u with v | v
        · omega
        · exact v
      · exact absurd hwl (xMsg_not_L u)
    · exfalso
      rcases hok.ful t0 ht1 ht0n hp with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨u, _⟩
      · have := hbyte _ (hok.h0j (by omega)).2.2; rw [junk_b0] at this; cases this
      · omega
      · exact xMsg_not_L (hok.h0c (by omega)).2.2 hwl
      · exact flag_not_L (hok.h0f (by omega)).2.2.1 hwl
      · omega
  · exact .inl (by omega)

/-- **THE TAKE** (H1's acquire, in place, read the born cell): R's place 1 → 2. -/
theorem h1_take {σ σ' : OSt (List Nat)} {g : S4} {ts : Nat} {rc : Prop} (hok : I4 img M σ g)
    (hp1 : g.p1 = 1) (hrc : rc) (hful : fulO M 1 σ rc ts σ') (hM : M[ts - 1]? = some acq1) :
    I4 img M σ' { g with p1 := 2, ta := ts, rp := 2, b1 := g.γ } ∧ g.rp = 1 := by
  obtain ⟨hdone, hn1, hn2, htsn, hts1, hpr, hcase⟩ := ful_facts hok.pr hful
  obtain ⟨ets, hn', _, _⟩ : ts = σ.n + 1 ∧ σ'.n = σ.n + 1 ∧ rc ∧ au M ts = some 1 := by
    rcases hcase with ⟨_, _, hnr⟩ | h4
    · exact absurd hrc hnr
    · exact h4
  have hnd : ¬ g.Dd ts := fun hd => by have := (pend_le hok (hok.dd ts hd)).2; omega
  obtain ⟨hp0, ha1⟩ := hok.p1a (.inl hp1)
  obtain ⟨r1, r2, r3⟩ := hok.rp_ok
  have hrp : g.rp = 1 := by
    have h0 : g.rp ≠ 0 := fun e => by have := r2.1 e; omega
    have h2 : g.rp ≠ 2 := fun e => by have := r3.1 e; omega
    omega
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, hp⟩ := i4_frame (g' := { g with p1 := 2, ta := ts, rp := 2, b1 := g.γ })
    hok hful hnd
    (fun t => ⟨fun h => .inl h, fun h => by
      rcases h with h | ⟨h1, ⟨h2, _⟩ | ⟨h2, _⟩⟩
      · exact h
      · rcases hok.cand_i t ((pend_iff (M := M) hpr t).1 h1).1 h2 with u | u
        · omega
        · exact u
      · rcases hok.cand_c t ((pend_iff (M := M) hpr t).1 h1).1 h2 with u | u
        · omega
        · exact u⟩)
    (Nat.le_refl _)
  refine ⟨⟨f1, f2, f3, f4, f5, f6, f7, hok.bad, hok.p0le, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun t h1 h2 h3 => ?_, hok.γ_ok, ⟨by simp, by simp; omega, by simp⟩, by simp, fun _ => ⟨hp0, ha1⟩,
    fun _ => ⟨hts1, htsn, hM⟩, fun _ => rfl, hok.bd1, fun gg hg => hok.done gg (by rw [← hdone]; exact hg)⟩, hrp⟩
  · obtain ⟨u1, u2, u3⟩ := hok.h0j h; exact ⟨u1, by show g.tj ≤ σ'.n; omega, u3⟩
  · obtain ⟨u1, u2, u3⟩ := hok.h0i h; exact ⟨u1, by show g.ti ≤ σ'.n; omega, u3⟩
  · obtain ⟨u1, u2, u3⟩ := hok.h0c h; exact ⟨u1, by show g.tc ≤ σ'.n; omega, u3⟩
  · obtain ⟨u1, u2, u3, u4, u5⟩ := hok.h0f h; exact ⟨u1, by show g.tf ≤ σ'.n; omega, u3, u4, u5⟩
  · by_cases e : t = ts
    · exact .inr (.inr (.inr (.inr ⟨by simp, e⟩)))
    · obtain ⟨u1, u2⟩ := ful_old hok hful h2 e h3
      rcases hok.ful t h1 u1 u2 with u | u | u | u | ⟨u, _⟩
      · exact .inl u
      · exact .inr (.inl u)
      · exact .inr (.inr (.inl u))
      · exact .inr (.inr (.inr (.inl u)))
      · omega

/-- H1's acquire (in place) did not take R. -/
theorem h1_fail {σ σ' : OSt (List Nat)} {g : S4} {ts : Nat} {rc : Prop} (hok : I4 img M σ g)
    (hp1 : g.p1 ≤ 1) (hrc : rc) (hful : fulO M 1 σ rc ts σ') (hM : M[ts - 1]? = some acq1) :
    I4 img M σ' { g with p1 := 3, ta := ts } := by
  obtain ⟨hdone, hn1, hn2, htsn, hts1, hpr, hcase⟩ := ful_facts hok.pr hful
  obtain ⟨ets, hn', _, _⟩ : ts = σ.n + 1 ∧ σ'.n = σ.n + 1 ∧ rc ∧ au M ts = some 1 := by
    rcases hcase with ⟨_, _, hnr⟩ | h4
    · exact absurd hrc hnr
    · exact h4
  have hnd : ¬ g.Dd ts := fun hd => by have := (pend_le hok (hok.dd ts hd)).2; omega
  obtain ⟨r1, r2, r3⟩ := hok.rp_ok
  have hrp : g.rp ≠ 2 := fun e => by have := r3.1 e; omega
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, hp⟩ := i4_frame (g' := { g with p1 := 3, ta := ts }) hok hful hnd
    (fun t => ⟨fun h => .inl h, fun h => by
      rcases h with h | ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩
      · exact h
      · rcases hok.cand_i t ((pend_iff (M := M) hpr t).1 h1).1 h2 with u | u
        · simp at h3; omega
        · exact u
      · rcases hok.cand_c t ((pend_iff (M := M) hpr t).1 h1).1 h2 with u | u
        · simp at h3; omega
        · exact u⟩)
    (Nat.le_refl _)
  refine ⟨f1, f2, f3, f4, f5, f6, f7, hok.bad, hok.p0le, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun t h1 h2 h3 => ?_, hok.γ_ok, ⟨r1, r2, by simp [hrp]⟩, by simp, fun h => by simp at h,
    fun _ => ⟨hts1, htsn, hM⟩, fun h => by simp at h, hok.bd1, fun gg hg => hok.done gg (by rw [← hdone]; exact hg)⟩
  · obtain ⟨u1, u2, u3⟩ := hok.h0j h; exact ⟨u1, by show g.tj ≤ σ'.n; omega, u3⟩
  · obtain ⟨u1, u2, u3⟩ := hok.h0i h; exact ⟨u1, by show g.ti ≤ σ'.n; omega, u3⟩
  · obtain ⟨u1, u2, u3⟩ := hok.h0c h; exact ⟨u1, by show g.tc ≤ σ'.n; omega, u3⟩
  · obtain ⟨u1, u2, u3, u4, u5⟩ := hok.h0f h; exact ⟨u1, by show g.tf ≤ σ'.n; omega, u3, u4, u5⟩
  · by_cases e : t = ts
    · exact .inr (.inr (.inr (.inr ⟨by simp, e⟩)))
    · obtain ⟨u1, u2⟩ := ful_old hok hful h2 e h3
      rcases hok.ful t h1 u1 u2 with u | u | u | u | ⟨u, _⟩
      · exact .inl u
      · exact .inr (.inl u)
      · exact .inr (.inr (.inl u))
      · exact .inr (.inr (.inr (.inl u)))
      · omega

/-- **THE HOLDER'S READ OF THE COUNTER**: a byte whose floor covers `tc` is 42's or a dead message's. -/
theorem h1_cread {σ : OSt (List Nat)} {g : S4} {t j P : Nat} {b : BitVec 8} (hok : I4 img M σ g)
    (hp0 : g.p0 = 4) (hP : g.tc ≤ P) (hj : j < 8) (hmb : memByte img M t (X + j) = some b) (htn : t ≤ σ.n)
    (hnw : ¬ writesIn (M.take σ.n) (X + j) t P) : (toBytes 42 8)[j]? = some b ∨ g.Dd t := by
  obtain ⟨c1, c2, c3⟩ := hok.h0c (by omega)
  have hcw : (xMsg.byteAt (X + j)).isSome = true := by rw [xMsg_byte j hj]; simp [toBytes, Weak.Prom.Ref.byteList]; omega
  have hge : g.tc ≤ t := by
    refine Classical.byContradiction fun hlt => hnw ⟨g.tc, by omega, hP, xMsg, ?_, hcw⟩
    rw [List.getElem?_take, if_pos (by omega)]; exact c3
  rcases Nat.lt_or_ge g.tc t with hlt | hle
  · right
    have ht1 : 1 ≤ t := by omega
    have hwx : wrX M t := ⟨j, hj, wrA_of_memByte ht1 hmb⟩
    by_cases hp : pend M σ t
    · rcases hok.cls t hp with u | u | u
      · exact u
      · exact absurd hwx (init_not_X u)
      · rcases hok.cand_c t hp u with v | v
        · omega
        · exact v
    · exfalso
      rcases hok.ful t ht1 htn hp with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨u, rfl⟩
      · exact junk_not_X (hok.h0j (by omega)).2.2 hwx
      · exact init_not_X (hok.h0i (by omega)).2.2 hwx
      · omega
      · exact flag_not_X (hok.h0f (by omega)).2.2.1 hwx
      · exact acq1_not_X (hok.p1t u).2.2 hwx
  · left
    have e : t = g.tc := by omega
    subst e
    rw [memByte_of c1 c3, xMsg_byte j hj] at hmb; exact hmb

/-- A dead message witnesses `bad`; H1 records it. -/
theorem i4_setBad {σ : OSt (List Nat)} {g : S4} (hok : I4 img M σ g) {t : Nat} (hd : g.Dd t) :
    I4 img M σ { g with bad := true, bd1 := true } :=
  ⟨hok.pr, hok.dd, hok.dd_i, hok.dd_c, hok.cls, hok.cand_i, hok.cand_c, fun _ => ⟨t, hd⟩, hok.p0le, hok.h0j,
    hok.h0i, hok.h0c, hok.h0f, hok.ful, hok.γ_ok, hok.rp_ok, hok.p1le, hok.p1a, hok.p1t, hok.b1, fun _ => rfl,
    fun gg hg => .inr rfl⟩

/-- THE END of a hart. -/
theorem i4_fin {σ : OSt (List Nat)} {g : S4} {h : Nat} {gg : List Nat} (hok : I4 img M σ g)
    (hk : h = 1 → spec4 gg ∨ g.bad = true) : I4 img M { σ with done := upd σ.done h (some gg) } g := by
  refine ⟨hok.pr, hok.dd, hok.dd_i, hok.dd_c, hok.cls, hok.cand_i, hok.cand_c, hok.bad, hok.p0le, hok.h0j,
    hok.h0i, hok.h0c, hok.h0f, hok.ful, hok.γ_ok, hok.rp_ok, hok.p1le, hok.p1a, hok.p1t, hok.b1, hok.bd1,
    fun gg' hg => ?_⟩
  by_cases e : h = 1
  · subst e; simp only [upd_eq] at hg; cases hg; exact hk rfl
  · simp only [upd_ne _ _ (Ne.symm e)] at hg; exact hok.done gg' hg

/-- **THE FINAL EXTRACTION** (G4 (4)): at the end of a valid run nothing is dead, so not `bad`. -/
theorem i4_final {σ : OSt (List Nat)} {g : S4} (hok : I4 img M σ g) (hpr : ∀ a, σ.pr a = ∅) :
    ∀ gg, σ.done 1 = some gg → spec4 gg := by
  intro gg hg
  rcases hok.done gg hg with h | h
  · exact h
  · obtain ⟨t, ht⟩ := hok.bad h
    obtain ⟨a, _, ha⟩ := hok.dd t ht
    rw [hpr a] at ha; exact absurd ha notElemOfEmpty

end steps2

end Weak.Prom.Own.L4
