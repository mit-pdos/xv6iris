/-
Weak/Mini: **E1 — MiniRef = the full reference on F, possibly-infinite executions** (mini plan rev 4 §2 L1 E1, K7: an
a/b pair).

* `toFull P cond X` — the full execution of `P.toTest cond` (any outcome condition: no execution notion reads it)
  with X's load values as bytes (`nuOf`), X's gmo, and every hart REPLAYED along the branch outcomes under those values.
* `e1a` — `miniExec P X ↔ infExec (P.toTest cond) (toFull P cond X)`.
* `e1b` — every full execution `E` of `P.toTest cond` is `toFull` of a mini execution: the same events, the same
  events' contents, the same gmo (`E.ev` is compared on existing events only: `IExec.ev` of a non-event is
  unconstrained, review-R2 F1).
Both for well-formed F programs (`MProg.wf`: a RISC-V size, aligned image, targets inside the texts, registers < 32).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.EqRefSim

namespace Weak.Mini

open Weak.Prom.Ref
open Weak.Prom.Pfx

/-! ## 1. Mini runs: the event list only grows -/

theorem wr_evs (m : MSt) (r : Nat) (x : Nat × List Nat) : (m.wr r x).evs = m.evs := by
  unfold MSt.wr; split <;> rfl

theorem mstep_prefix (P : MProg) (V : EvId → Nat) (h : Nat) (m : MSt) : m.evs <+: (mstep P V h m).evs := by
  unfold mstep
  split
  · rename_i mi _
    cases mi <;> simp only [exec, MSt.adv, MSt.emit, wr_evs] <;>
      first | exact List.prefix_refl _ | exact List.prefix_append _ _
  · exact List.prefix_refl _

theorem mrun_mono (P : MProg) (V : EvId → Nat) (h : Nat) {k k' : Nat} (hk : k ≤ k') :
    (mrun P V h k).evs <+: (mrun P V h k').evs := by
  induction k' with
  | zero => rw [Nat.le_zero.1 hk]; exact List.prefix_refl _
  | succ k' ih =>
    rcases Nat.lt_or_eq_of_le hk with hlt | heq
    · exact (ih (by omega)).trans (mstep_prefix P V h _)
    · rw [heq]; exact List.prefix_refl _

theorem mrun_get (P : MProg) (V : EvId → Nat) (h i : Nat) {k k' : Nat} (hk : i < (mrun P V h k).evs.length)
    (hk' : i < (mrun P V h k').evs.length) : (mrun P V h k).evs[i] = (mrun P V h k').evs[i] := by
  have h1 := mrun_mono P V h (Nat.le_max_left k k')
  have h2 := mrun_mono P V h (Nat.le_max_right k k')
  rw [h1.getElem hk, h2.getElem hk']

theorem MExec.ev_eq (P : MProg) (X : MExec) {e : EvId} {k : Nat} (hk : e.2 < (mrun P X.V e.1 k).evs.length) :
    X.ev P e = (mrun P X.V e.1 k).evs[e.2] := by
  unfold MExec.ev
  rw [dif_pos ⟨k, hk⟩]
  exact mrun_get P X.V e.1 e.2 _ _

/-! ## 2. toFull -/

/-- The bytes of the mini load values. -/
def nuOf (sz : Nat) (V : EvId → Nat) : Val := fun e => byteList (V e) sz

/-- **`toFull P cond X`**: the full execution with X's load values, X's gmo, and the replayed harts. -/
def toFull (P : MProg) (cond : OC) (X : MExec) : IExec :=
  { T := P.toTest cond, st := fun h k => replay (P.toTest cond) h (nuOf P.sz X.V) k, ν := nuOf P.sz X.V,
    gmo := X.gmo }

theorem agree_nuOf (sz : Nat) (V : EvId → Nat) : Agree sz V (nuOf sz V) := by
  intro e
  simp only [nuOf]
  rw [List.take_of_length_le (by rw [byteList_length]; exact Nat.le_refl _), bytesVal_byteList, Nat.mod_mod]

theorem harts_toTest (P : MProg) (cond : OC) : (P.toTest cond).harts.length = P.harts.length := by
  simp [MProg.toTest]

theorem tgtOk_of_wf {P : MProg} (hwf : P.wf) (h : Nat) : TgtOk P h := fun i hi => (hwf.2.2 h i hi).1

/-! ## 3. A simulated full execution is the mini event set -/

/-- The concrete full event of a simulated symbolic event. -/
theorem concEv_eq {sz h i : Nat} {V : EvId → Nat} {ν : Val} {se : SEv} {me : MEv} (H : SimEv sz h i V ν se me)
    (hl : me.kind = .ld → ν (h, i) = byteList me.v sz) : concEv ν h i se = me.toEv sz := by
  obtain ⟨sk, addr, wval⟩ := se
  obtain ⟨kd, ii, pa, v, ad, dd, cd⟩ := me
  have hsk := H.sk; have hpa := H.pa; have hwv := H.wv
  simp only at hsk hpa hwv hl
  subst hsk
  unfold concEv MEv.toEv
  simp only [hpa]
  cases kd with
  | ld => simp [MK.toKind, MK.szOf, Kind.isLoad, Kind.isStore, hl rfl]
  | st =>
    simp [MK.toKind, MK.szOf, Kind.isLoad, Kind.isStore]
    rw [← hwv rfl, byteList_mod]
  | fence f => simp [MK.toKind, MK.szOf, Kind.isLoad, Kind.isStore]

section simE

variable {P : MProg} {cond : OC} {X : MExec} {E : IExec}

/-- The hypotheses: `E` runs `P.toTest cond`, every hart simulated by X's mini run, with X's gmo. -/
structure SimE (P : MProg) (cond : OC) (X : MExec) (E : IExec) : Prop where
  T : E.T = P.toTest cond
  sim : ∀ h < P.harts.length, ∀ k, SimSt P.sz h X.V E.ν (mrun P X.V h k) (E.st h k)
  gmo : E.gmo = X.gmo

theorem SimE.has (H : SimE P cond X E) (e : EvId) : E.has e ↔ X.has P e := by
  unfold IExec.has MExec.has
  rw [H.T, harts_toTest]
  constructor
  · rintro ⟨h1, k, h2⟩; exact ⟨h1, k, by rw [← (H.sim e.1 h1 k).evl]; exact h2⟩
  · rintro ⟨h1, k, h2⟩; exact ⟨h1, k, by rw [(H.sim e.1 h1 k).evl]; exact h2⟩

/-- `E`'s event `e` is simulated by the mini event `e`. -/
theorem SimE.simEv (H : SimE P cond X E) {e : EvId} (he : X.has P e) :
    SimEv P.sz e.1 e.2 X.V E.ν (E.sev e) (X.ev P e) := by
  have hE := (H.has e).2 he
  unfold IExec.sev
  rw [dif_pos hE]
  have hk := Classical.choose_spec hE.2
  have hS := H.sim e.1 he.1 (Classical.choose hE.2)
  have hk' : e.2 < (mrun P X.V e.1 (Classical.choose hE.2)).evs.length := by rw [← hS.evl]; exact hk
  rw [MExec.ev_eq P X hk']
  exact hS.ev e.2 hk hk'

theorem SimE.aligned_iff (H : SimE P cond X E) :
    (X.evs P).aligned P.sz ↔ ∀ h < P.harts.length, ∀ k, evsAligned E.ν (E.st h k) = true := by
  constructor
  · intro hal h hh k
    have hS := H.sim h hh k
    unfold evsAligned
    rw [List.all_eq_true]
    intro se hse
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hse
    have hi' : i < (mrun P X.V h k).evs.length := by rw [← hS.evl]; exact hi
    have hEv := hS.ev i hi hi'
    have hx : X.has P (h, i) := ⟨hh, k, hi'⟩
    have hev : X.ev P (h, i) = (mrun P X.V h k).evs[i] := MExec.ev_eq P X (e := (h, i)) hi'
    rw [hEv.sk, hEv.pa]
    generalize (mrun P X.V h k).evs[i] = me at hev ⊢
    obtain ⟨kd, ii, pa, v, ad, dd, cd⟩ := me
    cases kd with
    | fence f => simp [MEv.toEv, MK.toKind, Kind.isAcc, Kind.isMem]
    | ld =>
      have h1 := hal (h, i) ⟨hx, .inl (by show (X.ev P (h, i)).kind = .ld; rw [hev])⟩
      have h2 : (X.ev P (h, i)).pa % P.sz = 0 := h1
      rw [hev] at h2
      simp [MEv.toEv, MK.toKind, MK.szOf, Kind.isAcc, Kind.isMem, h2]
    | st =>
      have h1 := hal (h, i) ⟨hx, .inr (by show (X.ev P (h, i)).kind = .st; rw [hev])⟩
      have h2 : (X.ev P (h, i)).pa % P.sz = 0 := h1
      rw [hev] at h2
      simp [MEv.toEv, MK.toKind, MK.szOf, Kind.isAcc, Kind.isMem, h2]
  · intro hal e ⟨⟨hh, k, hk⟩, hm⟩
    have hS := H.sim e.1 hh k
    have ha := hal e.1 hh k
    unfold evsAligned at ha
    rw [List.all_eq_true] at ha
    have hk2 : e.2 < (E.st e.1 k).evs.length := by rw [hS.evl]; exact hk
    have := ha _ (List.getElem_mem hk2)
    have hEv := hS.ev e.2 hk2 hk
    have hev : X.ev P e = (mrun P X.V e.1 k).evs[e.2] := MExec.ev_eq P X hk
    show (X.ev P e).pa % P.sz = 0
    have hm' : (X.ev P e).kind = .ld ∨ (X.ev P e).kind = .st := hm
    rw [hEv.sk, hEv.pa] at this
    rw [hev] at hm' ⊢
    generalize (mrun P X.V e.1 k).evs[e.2] = me at this hm' ⊢
    obtain ⟨kd, ii, pa, v, ad, dd, cd⟩ := me
    rcases hm' with hmk | hmk <;> simp only at hmk <;> subst hmk <;>
      simpa [MEv.toEv, MK.toKind, MK.szOf, Kind.isAcc, Kind.isMem] using this

theorem ini_lt (P : MProg) (a : Nat) : P.ini a < 2 ^ (8 * P.sz) := Nat.mod_lt _ (Nat.two_pow_pos _)

/-- A full execution whose events are simulated by the mini events `A` (load values `V`), with `A`'s gmo. -/
structure SimA (P : MProg) (cond : OC) (A : MEvs) (V : EvId → Nat) (E : IExec) : Prop where
  T : E.T = P.toTest cond
  has : ∀ e, E.has e ↔ A.has e
  sev : ∀ e, A.has e → SimEv P.sz e.1 e.2 V E.ν (E.sev e) (A.ev e)
  gmo : E.gmo = A.gmo

theorem SimE.toA (H : SimE P cond X E) : SimA P cond (X.evs P) X.V E :=
  ⟨H.T, H.has, fun _ he => H.simEv he, H.gmo⟩

/-- **The correspondence** for a simulated full execution. -/
theorem SimA.corr {A : MEvs} {V : EvId → Nat} (hwf : P.wf) (H : SimA P cond A V E) (hal : A.aligned P.sz)
    (hl : ∀ e, A.has e → (A.ev e).kind = .ld → E.ν e = byteList (V e) P.sz) : Corr P.sz P.ini A E := by
  refine ⟨hwf.sz_pos, by rw [H.T]; rfl, H.has, fun e he => ?_, H.gmo, hal, ?_, ini_lt P,
    fun a k ha hk => by rw [H.T]; exact imgF_toTest P cond hwf.2.1 a k ha hk⟩
  · have hS := H.sev e he
    unfold IExec.ev
    apply concEv_eq hS
    intro hk
    rw [hS.lv hk, byteList_mod]
    exact hl e he hk
  · intro e he hm
    have hS := H.sev e he
    rcases hm with hm | hm
    · rw [hS.lv hm]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · rw [← hS.wv hm]; exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem imgF_lt {P : MProg} {cond : OC} (hwf : P.wf) {a k : Nat} (ha : a % P.sz = 0) (hk : k < P.sz) :
    (P.toTest cond).imgF (a + k) < 256 := by
  rw [imgF_toTest P cond hwf.2.1 a k ha hk]; exact byte_lt _ _

/-- In a full execution of an F program, every existing load returns the bytes of a value (evWfI: `sz` of them;
the load value axiom: each a byte of a store or of the image). -/
theorem SimA.bytes {A : MEvs} {V : EvId → Nat} (hwf : P.wf) (H : SimA P cond A V E) (hal : A.aligned P.sz)
    (hev : E.evWfI) (hlv : E.loadValueAxI) (e : EvId) (he : A.has e) (hk : (A.ev e).kind = .ld) :
    E.ν e = byteList (bytesVal ((E.ν e).take P.sz)) P.sz := by
  have hS := H.sev e he
  have hEh := (H.has e).2 he
  have hsk : E.sk e = ((A.ev e).toEv P.sz).sk := by
    unfold IExec.sk IExec.ev concEv; exact hS.sk
  have hld : (E.sk e).kind.isLoad = true := by rw [hsk]; simp [MEv.toEv, hk, MK.toKind, Kind.isLoad]
  have hszE : (E.sk e).sz = P.sz := by rw [hsk]; simp [MEv.toEv, hk, MK.szOf]
  have hrd : (E.ev e).rdat = E.ν e := by
    unfold IExec.ev concEv
    have : (E.sev e).sk.kind.isLoad = true := hld
    simp only [this, if_true]
  have hlen : (E.ν e).length = P.sz := by rw [← hrd, ← hszE]; exact (hev e hEh).1 hld
  have hio : E.isIoI e = false := by simp [IExec.isIoI, H.T, MProg.toTest]
  have hb : ∀ b ∈ E.ν e, b < 256 := by
    intro b hb
    obtain ⟨k, hkk, rfl⟩ := List.getElem_of_mem hb
    obtain ⟨o, _, ho⟩ := hlv e hEh hld hio k (by rw [hszE]; rw [hlen] at hkk; exact hkk)
    rw [hrd, List.getElem?_eq_getElem hkk, Option.some.injEq] at ho
    rw [ho]
    cases o with
    | none =>
      show E.T.imgF _ < 256
      rw [H.T]
      have hpa : (E.ev e).pa = (A.ev e).pa := by
        unfold IExec.ev concEv; exact hS.pa
      rw [hpa]
      exact imgF_lt hwf (hal e ⟨he, .inl hk⟩) (by rw [hlen] at hkk; exact hkk)
    | some w =>
      show wbyte (E.ev w) _ < 256
      unfold wbyte
      cases hw : (E.ev w).wdat[(E.ev e).pa + k - (E.ev w).pa]? with
      | none => simp
      | some b' =>
        simp only [Option.getD_some]
        have hmem := List.mem_of_getElem? hw
        unfold IExec.ev concEv at hmem
        by_cases hs : (E.sev w).sk.kind.isStore = true
        · simp only [hs, if_true] at hmem; exact byteList_lt _ _ b' hmem
        · simp [hs] at hmem
  rw [List.take_of_length_le (by rw [hlen]; exact Nat.le_refl _), ← hlen, byteList_bytesVal _ hb]

end simE

/-! ## 4. toFull is simulated -/

theorem lstep_of_fstep {p : List Instr} {h : Nat} {ν : Val} {s s' : SSt} (hs : FStep p h ν s s') : LStep p h s s' := by
  rcases hs with h1 | ⟨i, hi, hc⟩
  · exact .inl h1
  · refine .inr ⟨i, hi, ?_⟩
    cases hr : stepL h p.length s i with
    | stuck => rw [hr] at hc; cases hc
    | next s'' => rw [hr] at hc; cases hc; exact .inl rfl
    | fork t f =>
      rw [hr] at hc
      simp only [chosen, Option.some.injEq] at hc
      refine .inr ⟨t, f, rfl, ?_⟩
      split at hc
      · exact .inl hc.symm
      · exact .inr hc.symm

theorem simE_toFull {P : MProg} (hwf : P.wf) (cond : OC) (X : MExec) : SimE P cond X (toFull P cond X) :=
  ⟨rfl, fun h _ k => (replay_sim (agree_nuOf P.sz X.V) (tgtOk_of_wf hwf h) k).1, rfl⟩

theorem toFull_lds (P : MProg) (cond : OC) (X : MExec) (e : EvId) :
    (toFull P cond X).ν e = byteList (X.V e) P.sz := rfl

/-! ## 5. E1a -/

/-- **E1a**: a mini execution is exactly a full execution of `toFull`. -/
theorem e1a (P : MProg) (hwf : P.wf) (cond : OC) (X : MExec) :
    miniExec P X ↔ infExec (P.toTest cond) (toFull P cond X) := by
  have H := simE_toFull hwf cond X
  have hrs := fun h k => replay_sim (cond := cond) (agree_nuOf P.sz X.V) (tgtOk_of_wf hwf h) k
  have hconf : (toFull P cond X).conforms := by
    intro h _
    exact ⟨rfl, fun k => lstep_of_fstep (hrs h k).2.1⟩
  have hal : (X.evs P).aligned P.sz ↔ (toFull P cond X).condsOkI := by
    rw [H.aligned_iff]
    unfold IExec.condsOkI
    simp only [toFull, harts_toTest, condsOk_single, Bool.and_eq_true]
    constructor
    · intro ha h hh k; exact ⟨(hrs h k).2.2, ha h hh k⟩
    · intro ha h hh k; exact (ha h hh k).2
  constructor
  · rintro ⟨ha, hx⟩
    exact ⟨rfl, hconf, hal.1 ha, (corr_iff (H.toA.corr hwf ha (fun e _ _ => rfl))).2 hx⟩
  · rintro ⟨_, _, hc, hr⟩
    have ha := hal.2 hc
    exact ⟨ha, (corr_iff (H.toA.corr hwf ha (fun e _ _ => rfl))).1 hr⟩

/-! ## 6. E1b -/

/-- The mini execution of a full execution: each load's value is its bytes' value, gmo is `E`'s. -/
def ofFull (P : MProg) (E : IExec) : MExec := ⟨fun e => bytesVal ((E.ν e).take P.sz), E.gmo⟩

/-- **E1b**: every full execution of an F program is `toFull` of a mini execution (same events, same contents on
existing events, same gmo). -/
theorem e1b (P : MProg) (hwf : P.wf) (cond : OC) (E : IExec) (hE : infExec (P.toTest cond) E) :
    ∃ X, miniExec P X ∧ (∀ e, E.has e ↔ (toFull P cond X).has e) ∧
      (∀ e, E.has e → E.ev e = (toFull P cond X).ev e) ∧ E.gmo = (toFull P cond X).gmo := by
  obtain ⟨hT, hconf, hcond, href⟩ := hE
  let X := ofFull P E
  have hA : Agree P.sz X.V E.ν := fun e => by simp only [X, ofFull]
  have hsim : ∀ h < P.harts.length, ∀ k, SimSt P.sz h X.V E.ν (mrun P X.V h k) (E.st h k) := by
    intro h hh
    have hh' : h < E.T.harts.length := by rw [hT, harts_toTest]; exact hh
    obtain ⟨h0, hl⟩ := hconf h hh'
    rw [hT] at h0 hl
    apply sim_run hA (tgtOk_of_wf hwf h) (E.st h) h0
    intro k _
    apply fstep_of_lstep (hl k)
    have := hcond h hh' (k + 1)
    rw [condsOk_single, Bool.and_eq_true] at this
    exact this.1
  have H : SimE P cond X E := ⟨hT, hsim, rfl⟩
  have hal : (X.evs P).aligned P.sz := by
    rw [H.aligned_iff]
    intro h hh k
    have hh' : h < E.T.harts.length := by rw [hT, harts_toTest]; exact hh
    have := hcond h hh' k
    rw [condsOk_single, Bool.and_eq_true] at this
    exact this.2
  have hl : ∀ e, X.has P e → (X.ev P e).kind = .ld → E.ν e = byteList (X.V e) P.sz :=
    fun e he hk => H.toA.bytes hwf hal href.2.1 href.2.2.2.1 e he hk
  have hC := H.toA.corr hwf hal hl
  have hF := simE_toFull hwf cond X
  have hC' := hF.toA.corr hwf hal (fun e _ _ => rfl)
  refine ⟨X, ⟨hal, (corr_iff hC).1 href⟩, fun e => by rw [hC.has, hC'.has], fun e he => ?_, rfl⟩
  have he' := (hC.has e).1 he
  rw [hC.ev e he', hC'.ev e he']

end Weak.Mini
