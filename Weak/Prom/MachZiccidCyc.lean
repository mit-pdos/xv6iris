/-
Weak/Prom: **[MachZiccid] no thin-air instruction fetch under the Ziccid fetch arm** (owner ruling [OWN.P22]
"Ziccid rule now", context.md item 30; brief `~/dev/weak-orch/promising/MachZiccid_prompt.txt` (2), (3);
`~/dev/weak-orch/promising/FetchArm-review.md` §1, §2 (D)).

Finding S-0 (PROGRESS-SailS0.md): the Zifencei-only fetch arm let a hart fetch an outstanding promise — its own —
execute it, and fulfil it later.  Ziccid forbids that: "An instruction fetch is a memory read operation that appears
in the global memory order, in program order with respect to other instruction fetches from the same hart"
(Ziccid_fetch_global_order), "memory supplies the value written by the most recent store that precedes the read in
global memory order" (Ziccid_fetch_value), and "Instruction fetches appear in the global memory order before any
explicit memory accesses to which they give rise" (Ziccid_fetch_before_access).  So a fetch F reading a store S has
S <gmo F, and an access of an instruction fetched at F' po-after F has F ≤gmo F' <gmo access.

The machine-level form, stated GENERALLY (every arm, every run, any program half `pstep`, any fabric):
* `memStep_ifv_mono` — the fetch view `wIfv` is NON-DECREASING under every arm;
* `memStep_fetch_src` — a fetch sets `wIfv` at or above each source timestamp it returns;
* `memStep_fulfil_gt` — every fulfil (store, SC, fused AMO, AMO write half, CMO) has `ts > wIfv`;
* `pmSteps_fetch_lt` — in any run, every timestamp a hart fetched is below every timestamp it fulfils LATER;
* corollaries `no_fetch_own_then_fulfil` (the S-0 cycle: fetch your own promise, fulfil it later — impossible) and
  `no_fetch_cross` (hart A fetches B's promise and later fulfils its own, B fetches A's and later fulfils its own —
  impossible).
NON-VACUITY (3): `fetch_image_ok` — a fetch of never-written text returning the image bytes is admissible at every
`vf ∈ [max wIfv wIfl, |log|]`; `fetch_image_vf0` — from any state with `wIfv = wIfl = 0` the image fetch at `vf = 0`
is admissible against ANY log (stale fetch, zifencei.adoc:67–69, survives); `fetch_image_psInit_mpFF` — the
instance at mpFF's first text word with a log that has overwritten it.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.Machine

namespace Weak.Prom.Ziccid

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom
open PLabel

/-! ## 1. `wIfv` along the per-byte folds -/

theorem loadBytes_ifv (aq : Bool) (vpre : Nat) : ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)),
    (loadBytes aq vpre ws a tvs).wIfv = ws.wIfv
  | _, _, [] => rfl
  | ws, a, (t, _) :: r => (loadBytes_ifv aq vpre (loadByte ws aq vpre a t) (a + 1) r).trans rfl

theorem storeBytes_ifv : ∀ (ws : PState) (a : Int) (n ts fv : Nat), (storeBytes ws a n ts fv).wIfv = ws.wIfv
  | _, _, 0, _, _ => rfl
  | ws, a, n + 1, ts, fv => (storeBytes_ifv _ (a + 1) n ts fv).trans rfl

theorem cohRaise_ifv : ∀ (ws : PState) (a : Int) (n ts : Nat), (cohRaise ws a n ts).wIfv = ws.wIfv
  | _, _, 0, _ => rfl
  | ws, a, n + 1, ts => (cohRaise_ifv _ (a + 1) n ts).trans rfl

theorem loadRun_ifv (ws : PState) (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRun ws aq rl va base tvs).wIfv = ws.wIfv := loadBytes_ifv aq _ ws base tvs

theorem loadRunV_ifv (ws : PState) (aq rl : Bool) (va vi : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRunV ws aq rl va vi base tvs).wIfv = ws.wIfv := loadBytes_ifv aq _ ws base tvs

theorem storeRun_ifv (ws : PState) (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    (storeRun ws rl va fv base n ts).wIfv = ws.wIfv := storeBytes_ifv ws base n ts fv

/-- The sources of an admissible fetch are at most its fetch view. -/
theorem fetchOk_le {img : Image} {log : List PMsg} {vf : Nat} :
    ∀ {a : Int} {r : List (Nat × BitVec 8)}, bytesAll (fetchByteOk img log vf) a r → bytesAll (fun _ t _ => t ≤ vf) a r
  | _, [], _ => trivial
  | _, (_, _) :: _, ⟨h1, h2⟩ => ⟨h1.2.1, fetchOk_le h2⟩

theorem bytesAll_lt_of_le {x y : Nat} (hxy : x < y) :
    ∀ {a : Int} {r : List (Nat × BitVec 8)}, bytesAll (fun _ t _ => t ≤ x) a r → bytesAll (fun _ t _ => t < y) a r
  | _, [], _ => trivial
  | _, (_, _) :: _, ⟨h1, h2⟩ => ⟨by simp only at h1 ⊢; omega, bytesAll_lt_of_le hxy h2⟩

/-! ## 2. The three arm facts -/

section arms

variable {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
  {ots : Option Nat} {ws' : PState} {prom' : GSet Nat}

/-- **`wIfv` IS NON-DECREASING UNDER EVERY ARM** (Ziccid_fetch_global_order: the hart's fetches are in program
order in gmo; `LInstr` no longer resets it). -/
theorem memStep_ifv_mono (h : memStep img log i prom ws l ots ws' prom') : ws.wIfv ≤ ws'.wIfv := by
  cases h with
  | silent => exact Nat.le_refl _
  | load aq rl base tvs asrc _ vi _ => exact Nat.le_of_eq (loadRunV_ifv ..).symm
  | store aq rl base data asrc vsrc ts =>
    show ws.wIfv ≤ (storeRun ws rl (srcsView ws asrc) (max (srcsView ws asrc) (srcsView ws vsrc)) base
      data.length ts).wIfv
    rw [storeRun_ifv]; exact Nat.le_refl _
  | rmw aq rl base tvs data asrc vsrc ts _ _ _ _ _ _ _ vi =>
    show ws.wIfv ≤ (storeRun (loadRunV ws aq false (srcsView ws asrc) vi base tvs) rl (srcsView ws asrc) ts base
      data.length ts).wIfv
    rw [storeRun_ifv, loadRunV_ifv]; exact Nat.le_refl _
  | amoLd aq base tvs asrc _ vi _ => exact Nat.le_of_eq (loadRunV_ifv ..).symm
  | amoSt rl base data asrc vsrc ts R =>
    show ws.wIfv ≤ (storeRun ws rl (srcsView ws asrc) ts base data.length ts).wIfv
    rw [storeRun_ifv]; exact Nat.le_refl _
  | fence => exact Nat.le_refl _
  | fenceI => exact Nat.le_refl _
  | dev => exact Nat.le_refl _
  | regW => exact Nat.le_refl _
  | ctrl => exact Nat.le_refl _
  | instr => exact Nat.le_refl _
  | lr aq rl base tvs asrc _ vi _ => exact Nat.le_of_eq (loadRunV_ifv ..).symm
  | sc aq rl base data asrc vsrc ts R =>
    show ws.wIfv ≤ (storeRun ws rl (srcsView ws asrc) ts base data.length ts).wIfv
    rw [storeRun_ifv]; exact Nat.le_refl _
  | scFail => exact Nat.le_refl _
  | fetch base tvs vf hv _ _ => show ws.wIfv ≤ vf; omega
  | cmo k base len asrc ts => exact Nat.le_of_eq (cohRaise_ifv ..).symm

/-- **A FETCH SETS `wIfv` AT OR ABOVE EACH SOURCE** (Ziccid_fetch_value: each byte is the latest store at or below
the fetch's gmo position `vf`, and the post is `wIfv := vf`). -/
theorem memStep_fetch_src {b : Int} {tvs : List (Nat × BitVec 8)}
    (h : memStep img log i prom ws (LIFetch b tvs) ots ws' prom') : bytesAll (fun _ t _ => t ≤ ws'.wIfv) b tvs := by
  cases h with
  | fetch base tvs vf _ _ hok => exact fetchOk_le hok

/-- **EVERY FULFIL IS ABOVE THE FETCH VIEW** (Ziccid_fetch_before_access with the monotone view: each write label's
pre-view, `stPre`/`stPreA` and the SC's and CMO's, contains `wIfv`, and EXT puts the fulfil above it). -/
theorem memStep_fulfil_gt {ts : Nat} (h : memStep img log i prom ws l (some ts) ws' prom') : ws.wIfv < ts := by
  cases h with
  | store aq rl base data asrc vsrc ts _ _ _ hext => unfold stPreA stPre at hext; omega
  | rmw aq rl base tvs data asrc vsrc ts _ _ _ _ _ _ hext =>
    unfold stPre at hext; rw [loadRun_ifv] at hext; omega
  | amoSt rl base data asrc vsrc ts R _ _ _ _ _ _ _ hext => unfold stPre at hext; omega
  | sc aq rl base data asrc vsrc ts R _ _ _ _ _ _ hext => unfold stPreA stPre at hext; omega
  | cmo k base len asrc ts _ _ _ hext => unfold stPre at hext; omega

end arms

/-! ## 3. Runs -/

section runs

variable {P D : Type} {pstep : P → D → PLabel → P → D → Prop}

/-- One machine step keeps agent `i` and does not lower its fetch view. -/
theorem pmStep_ifv {c c1 : PCfg P D} {e : PEvt} (h : pmStep pstep c e c1) {i : Nat} {ag : PAgent P}
    (hag : c.pcAgs[i]? = some ag) : ∃ ag1, c1.pcAgs[i]? = some ag1 ∧ ag.paWs.wIfv ≤ ag1.paWs.wIfv := by
  have hlt : i < c.pcAgs.length := (List.getElem?_eq_some_iff.1 hag).1
  cases h with
  | promise j ag' m hj _ _ =>
    by_cases hij : j = i
    · subst hij
      rw [hj] at hag; cases hag
      exact ⟨⟨ag.paSt, ag.paWs, {c.pcLog.length + 1} ∪ ag.paProm⟩, by rw [List.getElem?_set_self hlt],
        Nat.le_refl _⟩
    · exact ⟨ag, by rw [List.getElem?_set_ne hij]; exact hag, Nat.le_refl _⟩
  | state j ag' l ots st' d' ws' prom' hj _ hm =>
    by_cases hij : j = i
    · subst hij
      rw [hj] at hag; cases hag
      exact ⟨⟨st', ws', prom'⟩, by rw [List.getElem?_set_self hlt], memStep_ifv_mono hm⟩
    · exact ⟨ag, by rw [List.getElem?_set_ne hij]; exact hag, Nat.le_refl _⟩

/-- In any run, every later fulfil of agent `i` is above `i`'s fetch view at the start. -/
theorem pmSteps_fulfil_gt {c c' : PCfg P D} {evs : List PEvt} (h : pmSteps pstep c evs c') :
    ∀ {i : Nat} {ag : PAgent P}, c.pcAgs[i]? = some ag →
      ∀ (p : Nat) (l : PLabel) (ts : Nat), evs[p]? = some (.st i l (some ts)) → ag.paWs.wIfv < ts := by
  induction h with
  | refl => intro _ _ _ p l ts he; simp at he
  | step c0 c1 c2 e es hst _ ih =>
    intro i ag hag p l ts he
    cases p with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      cases hst with
      | state _ ag' _ _ _ _ _ _ hj _ hm =>
        rw [hj] at hag; cases hag
        exact memStep_fulfil_gt hm
    | succ q =>
      simp only [List.getElem?_cons_succ] at he
      obtain ⟨ag1, h1, h2⟩ := pmStep_ifv hst hag
      have := ih h1 q l ts he
      omega

/-- **EVERY TIMESTAMP A HART FETCHED IS BELOW EVERY TIMESTAMP IT FULFILS LATER** (any run, any `pstep`, any
fabric): the general form of Ziccid's "no code from nowhere" (F reads S ⇒ S ≤gmo F; F ≤gmo F' <gmo later store). -/
theorem pmSteps_fetch_lt {c c' : PCfg P D} {evs : List PEvt} (h : pmSteps pstep c evs c') :
    ∀ {i : Nat} {b : Int} {tvs : List (Nat × BitVec 8)} {l : PLabel} {ts p1 p2 : Nat}, p1 < p2 →
      evs[p1]? = some (.st i (LIFetch b tvs) none) → evs[p2]? = some (.st i l (some ts)) →
      bytesAll (fun _ t _ => t < ts) b tvs := by
  induction h with
  | refl => intro _ _ _ _ _ p1 _ _ he; simp at he
  | step c0 c1 c2 e es hst hrest ih =>
    intro i b tvs l ts p1 p2 hp h1 h2
    obtain ⟨q, rfl⟩ : ∃ q, p2 = q + 1 := ⟨p2 - 1, by omega⟩
    simp only [List.getElem?_cons_succ] at h2
    cases p1 with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h1
      subst h1
      cases hst with
      | state _ ag l' ots st' d' ws' prom' hj _ hm =>
        have hsrc := memStep_fetch_src hm
        have hlt : i < c0.pcAgs.length := (List.getElem?_eq_some_iff.1 hj).1
        have hgt := pmSteps_fulfil_gt hrest (ag := ⟨st', ws', prom'⟩)
          (by show (c0.pcAgs.set i ⟨st', ws', prom'⟩)[i]? = _; rw [List.getElem?_set_self hlt]) q l ts h2
        exact bytesAll_lt_of_le hgt hsrc
    | succ p =>
      simp only [List.getElem?_cons_succ] at h1
      exact ih (by omega) h1 h2

theorem bytesAll_lt_not_any {ts : Nat} : ∀ {b : Int} {tvs : List (Nat × BitVec 8)},
    bytesAll (fun _ t _ => t < ts) b tvs → ¬ bytesAny (fun _ t _ => t = ts) b tvs
  | _, [], _, h => h
  | _, (_, _) :: _, ⟨h1, h2⟩, h => h.elim (fun e => by simp only at h1 e; omega) (bytesAll_lt_not_any h2)

/-- **THE S-0 CYCLE IS IMPOSSIBLE**: no run has a hart fetch a byte of timestamp `t` (its own outstanding promise,
or anything else) and LATER fulfil `t`.  (Machine v2 before [MachZiccid] admitted it: SailS0Fetch.lean, the
replaced `fetch_own_then_fulfil`.) -/
theorem no_fetch_own_then_fulfil {c c' : PCfg P D} {evs : List PEvt} (h : pmSteps pstep c evs c') {i : Nat}
    {b : Int} {tvs : List (Nat × BitVec 8)} {l : PLabel} {t p1 p2 : Nat} (hp : p1 < p2)
    (h1 : evs[p1]? = some (.st i (LIFetch b tvs) none)) (h2 : evs[p2]? = some (.st i l (some t))) :
    ¬ bytesAny (fun _ t' _ => t' = t) b tvs :=
  bytesAll_lt_not_any (pmSteps_fetch_lt h hp h1 h2)

/-- **THE TWO-HART CROSS CYCLE IS IMPOSSIBLE**: hart `i` fetches a byte of `tB` and later fulfils `tA`, hart `j`
fetches a byte of `tA` and later fulfils `tB` (any interleaving): `pmSteps_fetch_lt` twice gives `tB < tA < tB`. -/
theorem no_fetch_cross {c c' : PCfg P D} {evs : List PEvt} (h : pmSteps pstep c evs c') {i j : Nat}
    {bi bj : Int} {tvi tvj : List (Nat × BitVec 8)} {li lj : PLabel} {tA tB p1 p2 q1 q2 : Nat}
    (hp : p1 < p2) (hi1 : evs[p1]? = some (.st i (LIFetch bi tvi) none)) (hi2 : evs[p2]? = some (.st i li (some tA)))
    (hq : q1 < q2) (hj1 : evs[q1]? = some (.st j (LIFetch bj tvj) none)) (hj2 : evs[q2]? = some (.st j lj (some tB)))
    (hiB : bytesAny (fun _ t _ => t = tB) bi tvi) (hjA : bytesAny (fun _ t _ => t = tA) bj tvj) : False := by
  have key : ∀ {b : Int} {tvs : List (Nat × BitVec 8)} {x y : Nat}, bytesAll (fun _ t _ => t < y) b tvs →
      bytesAny (fun _ t _ => t = x) b tvs → x < y := by
    intro b tvs x y ha hn
    induction tvs generalizing b with
    | nil => exact hn.elim
    | cons tv r ih =>
      obtain ⟨t, v⟩ := tv
      rcases hn with e | e
      · have := ha.1; simp only at this e; omega
      · exact ih ha.2 e
  have h1 := key (pmSteps_fetch_lt h hp hi1 hi2) hiB
  have h2 := key (pmSteps_fetch_lt h hq hj1 hj2) hjA
  omega

end runs

/-! ## 4. Non-vacuity: image fetches of never-written text -/

section nonvac

variable {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState}

/-- **NON-VACUITY**: a fetch of NEVER-WRITTEN text returning the image's bytes (timestamp 0) is admissible at EVERY
fetch view `vf ∈ [max wIfv wIfl, |log|]` (Ziccid_fetch_value: the latest store at or below `vf` is the initial
value). -/
theorem fetch_image_ok {base : Int} {tvs : List (Nat × BitVec 8)} {vf : Nat} (hv : max ws.wIfv ws.wIfl ≤ vf)
    (hvl : vf ≤ log.length) (himg : bytesAll (fun a t v => t = 0 ∧ img a = some v) base tvs)
    (hnw : bytesAll (fun a _ _ => ¬ writesIn log a 0 log.length) base tvs) :
    memStep img log i prom ws (LIFetch base tvs) none
      { ws with wIfr := max ws.wIfr (bytesMax (fun _ t => t) base tvs), wIfv := vf } prom := by
  refine memStep.fetch prom ws base tvs vf hv hvl ?_
  have key : ∀ {a : Int} {r : List (Nat × BitVec 8)}, bytesAll (fun a t v => t = 0 ∧ img a = some v) a r →
      bytesAll (fun a _ _ => ¬ writesIn log a 0 log.length) a r → bytesAll (fetchByteOk img log vf) a r := by
    intro a r
    induction r generalizing a with
    | nil => intro _ _; trivial
    | cons tv r ih =>
      obtain ⟨t, v⟩ := tv
      rintro ⟨⟨rfl, hi⟩, hr⟩ ⟨hn, hn'⟩
      exact ⟨⟨hi, Nat.zero_le _, fun ⟨t', h1, h2, hm⟩ => hn ⟨t', h1, by omega, hm⟩⟩, ih hr hn'⟩
  exact key himg hnw

/-- **NON-VACUITY at `vf = 0`**: from any state with `wIfv = wIfl = 0` (e.g. `psInit`), the image fetch at `vf = 0`
is admissible against ANY log — whatever was written later (a stale fetch, zifencei.adoc:67–69, survives
Ziccid: "no requirement that younger instruction fetches appear in the global memory order later than older
explicit memory accesses"). -/
theorem fetch_image_vf0 {base : Int} {tvs : List (Nat × BitVec 8)} (hv : ws.wIfv = 0) (hl : ws.wIfl = 0)
    (himg : bytesAll (fun a t v => t = 0 ∧ img a = some v) base tvs) :
    memStep img log i prom ws (LIFetch base tvs) none
      { ws with wIfr := max ws.wIfr (bytesMax (fun _ t => t) base tvs), wIfv := 0 } prom := by
  refine memStep.fetch prom ws base tvs 0 (by omega) (Nat.zero_le _) ?_
  have key : ∀ {a : Int} {r : List (Nat × BitVec 8)}, bytesAll (fun a t v => t = 0 ∧ img a = some v) a r →
      bytesAll (fetchByteOk img log 0) a r := by
    intro a r
    induction r generalizing a with
    | nil => intro _; trivial
    | cons tv r ih =>
      obtain ⟨t, v⟩ := tv
      rintro ⟨⟨rfl, hi⟩, hr⟩
      exact ⟨⟨hi, Nat.le_refl _, fun ⟨t', h1, h2, _⟩ => by omega⟩, ih hr⟩
  exact key himg

end nonvac

/-- The instance at the assembled `mpFF`'s first text word (`0x80400000`, `sw x5,0(x6)` = `0x00532023`): from
`psInit`, with a log whose only message OVERWRITES that word (with `addi x5,x5,1`), the image fetch at `vf = 0` is
admissible (and the fetch of the message at `vf = 1` too — `fetchByteOk` at `t = 1`). -/
theorem fetch_image_psInit_mpFF (prom : GSet Nat) (img : Image)
    (himg : ∀ k : Nat, k < 4 → img (0x80400000 + k) = some ([0x23#8, 0x20#8, 0x53#8, 0x00#8][k]!)) :
    let m : PMsg := ⟨0x80400000, [0x93#8, 0x82#8, 0x12#8, 0x00#8], some 0, .plain⟩
    memStep img [m] 0 prom psInit
      (LIFetch 0x80400000 [(0, 0x23#8), (0, 0x20#8), (0, 0x53#8), (0, 0x00#8)]) none
      { psInit with
        wIfr := max psInit.wIfr (bytesMax (fun _ t => t) 0x80400000
          [(0, 0x23#8), (0, 0x20#8), (0, 0x53#8), (0, 0x00#8)])
        wIfv := 0 } prom := by
  intro m
  refine fetch_image_vf0 rfl rfl ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩
  · simpa using himg 0 (by omega)
  · simpa using himg 1 (by omega)
  · have := himg 2 (by omega); simpa [show (0x80400000 : Int) + 1 + 1 = 0x80400000 + 2 by omega] using this
  · have := himg 3 (by omega)
    simpa [show (0x80400000 : Int) + 1 + 1 + 1 = 0x80400000 + 3 by omega] using this

end Weak.Prom.Ziccid

#print axioms Weak.Prom.Ziccid.pmSteps_fetch_lt
#print axioms Weak.Prom.Ziccid.no_fetch_own_then_fulfil
#print axioms Weak.Prom.Ziccid.no_fetch_cross
#print axioms Weak.Prom.Ziccid.fetch_image_ok
#print axioms Weak.Prom.Ziccid.fetch_image_psInit_mpFF
