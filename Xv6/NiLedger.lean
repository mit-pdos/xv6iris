/-
**THE NI FILING LEDGER** (NI M2-W2c; design of record
`claude-notes/projects/noninterference.md`, "M2-W2 design (2026-10-02)" §1,
rulings O1/O2/O6): every user ENTER in the machine's history is FILED exactly
once, either as a ROUND (the exit it resumes, the cause, the trapped and the
resumed keys, lawful by `roundOkKeys`, same pid) or as an ORIGIN (an
incarnation's first key).

* §1 `tfGprs`, the trapframe's `x1..x31` in the order a boundary event names
  them (`MachCSL.gprList`, `x_k` at trapframe word `4 + k`), and the bridge
  `gprList_tfResumeGpr0`: the file userret rebuilds IS `tfGprs`.
* §2 `exitFits` / `enterFits`: an event read at a key; `niFit`, the meaning
  of an entry's evidence (`MachFixedGS.uFit`'s Xv6 reading, ruling O2),
  with the round's getpid row (`niPidRow`, M2-W2d) and wait row
  (`niWaitRow`, NI G1d: the answer's shape, carried by the round).
* §3 `NiEntry`, `niOk h F` (every filing is valid in `h`, every enter in `h`
  is filed once): the ledger's pure fact (ruling O6: `∃ F`); `niOk_snoc`
  steps it blind on non-enter events, `niOk_file` files an enter.
* §4 `NiFitIs`: the Prop class that tells the kernel's proofs (generic in the
  `MachGS` instance) that the record's `uFit` accepts `niFit`'s evidence
  and (M2-W2d) that a fork ecall's exit claim is an origin ticket.
* §5 (M2-W2d) the one-shot claims: `niForkExit`, the keys, `niOneShot`
  (pure), the tokens, `niClaims` (the authority), `niR γ h := ∃ F, ⌜niOk h
  F⌝ ∗ niClaims γ h F`, and its steps `niR_alloc`/`niR_snoc`/`niR_exit`/
  `niR_powerOn`/`niR_enter`/`niR_pure`.

**F3: `satp` is not an identity.**  A root is freed at exit / kill / a
successful exec and a later `kalloc` can hand the page to a new process, so
traces are NOT read per `satp`: they are read per FILING (O1: incarnations by
(era, pid), read off the filings by W4).

**F4: origins are not free (M2-W2d).**  `niFit none e` is "some key fits
these registers", which is always satisfiable, so the filing itself is made
honest by ONE-SHOT CLAIMS (§5): the ledger mints, at each exit at position
`i`, a round claim (`roundClaim γ i`) and, at a fork ecall's exit, a
child-origin claim (`originClaim γ i`); at each power-on at `b`, initproc's
origin claim (`initClaim γ b`).  A filing spends the claim it cites
(`niR_enter`), and the authority (`niClaims`) records it, so each exit is
cited once as a round, each fork exit once more as an origin, each power-on
once as an origin: `niOneShot`, read off `niR` by `niR_pure`.

## Deviations from the design text

1. **`NiFitIs` is an implication, not an equation** (design O2: `eq :
   MachFixedGS.uFit = niFit`).  The kernel only ever PRODUCES `uFit` evidence
   from `niFit` evidence, so `fit : niFit ox e → uFit ox e` is all its proofs
   use; and the equation would force the system record (`xv6FixedGS`, named
   in `xv6PowerAdequacy`'s statement) to carry `niFit`, pulling this file and
   its closure (`UhistDefs`, `UexecRound`, ...) into that root's trusted base.
   The system theorems keep the blind record (`uFit := True`, instance by
   `trivial`); W4's theorem instantiates a record at `uFit := niFit` (instance
   by `id`).
2. `niOk`'s per-entry clause is the named `niEntryOk` rather than an inline
   `match` (same meaning; the lemmas case on it).

PURE but for the class and §5's resources.
-/
import Xv6.UhistDefs

namespace Xv6

open Iris Iris.BI Iris.ProofMode Std MachCSL

/-! ## §1 The trapframe's GPRs -/

/-- **The trapframe's `x1..x31`** (words `5..35`), in the order a boundary
event names a register file (`MachCSL.gprList`): `x_k` is word `4 + k`. -/
def tfGprs (tf : List (BitVec 64)) : List (BitVec 64) := (List.range 31).map (fun k => tfW tf (5 + k))

/-- **The bridge**: the register file userret rebuilds (`tfResumeGpr0`, the
`sret`'s file off `x0`) reads, as an event's GPR list, the trapframe's
`tfGprs`. -/
theorem gprList_tfResumeGpr0 (ws : List (BitVec 64)) : gprList (tfResumeGpr0 ws) = tfGprs ws := by
  unfold gprList gprIdxs tfGprs tfResumeGpr0 tfResumeGpr
  simp [List.range_succ]

/-! ## §2 Events read at keys -/

/-- An exit event is the trap of key `W` at cause `sc`: the trapped pc and
registers are the key's trapframe's. -/
def exitFits (x : Obs) (sc : BitVec 64) (W : Uvis) : Prop :=
  ∃ (cpu : CPU) (s : BitVec 64), x = .uExit cpu s sc (tfW W.tf tfEpcIdx) (tfGprs W.tf)

/-- An enter event resumes key `W`: its registers are the key's trapframe's,
and it lands at the key's resume pc. -/
def enterFits (e : Obs) (W : Uvis) : Prop :=
  ∃ (cpu : CPU) (s ep : BitVec 64), e = .uEnter cpu s ep (tfGprs W.tf) ∧ retPc ep = tfResumePc W.tf

/-- getpid's answer at a round (M2-W2d, W4's request): an ecall round whose
effective number (at the trapped key's mask and run frame) is getpid
answers the key's pid -- `UserretClosedRows.urc_post`'s `hpidrow`. -/
def niPidRow (sc : BitVec 64) (W W' : Uvis) : Prop :=
  sc = uecallScause →
    usysRetPid (usysEff W.secc (tfOf (tfResumeGpr0 W.tf) (retPc (tfW W.tf tfEpcIdx))))
      (tfW W'.tf (tfArgIdx 0)) W.pid

/-- wait's answer at a round (NI G1d, W4's wait conjunct): an ecall round
whose effective number is wait answers `-1` or a reaped pid in `[1,
PIDMAX]`, sign-extended -- the kernel's row (`SpecSyscall.SyscRows.wait`,
kwait's led answer) carried by the round (`usysMemOk`'s wait branch,
`niWaitRow_of_round`); supplied at `UserretClosedRound.urc_exit`. -/
def niWaitRow (sc : BitVec 64) (W W' : Uvis) : Prop :=
  sc = uecallScause →
    usysEff W.secc (tfOf (tfResumeGpr0 W.tf) (retPc (tfW W.tf tfEpcIdx))) = USYS_wait →
      usysWaitRet (tfW W'.tf (tfArgIdx 0))

/-- **The round carries wait's row**: a lawful round at a wait ecall
answered with wait's shape (`usysMemOk_waitRet` at the bumped `a0`). -/
theorem niWaitRow_of_round {sc : BitVec 64} {W W' : Uvis} (hr : roundOkKeys sc W W') :
    niWaitRow sc W W' := by
  intro hsc hw
  unfold roundOkKeys at hr
  rw [hsc] at hr
  rcases uroundOk_ecall hr with ⟨hexec, -⟩ | ⟨-, r, ⟨hb1, -⟩, hm, -⟩
  · rw [hw] at hexec; exact absurd hexec (by decide)
  · have ha0 : tfW W'.tf (tfArgIdx 0) = r := by
      have := congrFun hb1 10#5
      rw [tfResumeGpr0, tfResumeGpr_a0] at this
      rw [this]; simp
    rw [hw] at hm
    rw [ha0]; exact usysMemOk_waitRet hm

/-- **The evidence's meaning** (the Xv6 reading of `MachFixedGS.uFit`): an
origin is any key the enter fits (the CLAIM it spends makes it honest, §5,
F4); a round cites the exit it resumes, read at the trapped key `W`, and the
resumed key `W'` is lawful from it, keeps its pid, and (M2-W2d) answers
getpid with it and (NI G1d) wait with wait's shape. -/
def niFit : Option (Nat × Obs) → Obs → Prop
  | none, e => ∃ W0, enterFits e W0
  | some (_, x), e => ∃ (sc : BitVec 64) (W W' : Uvis),
      exitFits x sc W ∧ enterFits e W' ∧ roundOkKeys sc W W' ∧ W'.pid = W.pid ∧ niPidRow sc W W' ∧
        niWaitRow sc W W'

/-! ## §3 The filing -/

/-- One filing: an origin at position `j` with the incarnation's first key
and (M2-W2d) the position `p` of the claim it spent -- the parent's fork
exit, or the power-on (initproc) -- or a round from the exit at `i` to the
enter at `j`. -/
inductive NiEntry where
  | origin (j : Nat) (W0 : Uvis) (p : Nat)
  | round (i j : Nat) (sc : BitVec 64) (W W' : Uvis)

/-- The enter a filing files. -/
def NiEntry.j : NiEntry → Nat
  | .origin j _ _ => j
  | .round _ j _ _ _ => j

/-- One filing is valid in history `h`. -/
def niEntryOk (h : List Obs) : NiEntry → Prop
  | .origin j W0 _ => ∃ e, h[j]? = some e ∧ enterFits e W0
  | .round i j sc W W' => i < j ∧ (∃ x, h[i]? = some x ∧ exitFits x sc W) ∧
      (∃ e, h[j]? = some e ∧ enterFits e W') ∧ roundOkKeys sc W W' ∧ W'.pid = W.pid ∧
      niPidRow sc W W' ∧ niWaitRow sc W W'

/-- **THE LEDGER'S FACT**: every filing is valid, and every enter in `h` is
filed exactly once (`∃!`, spelled out). -/
def niOk (h : List Obs) (F : List NiEntry) : Prop :=
  (∀ f ∈ F, niEntryOk h f) ∧
  (∀ (j : Nat) (e : Obs), h[j]? = some e → isUEnter e = true →
    ∃ f, (f ∈ F ∧ f.j = j) ∧ ∀ f', f' ∈ F → f'.j = j → f' = f)

/-- A valid filing names a position of the history. -/
theorem niEntryOk_lt {h : List Obs} {f : NiEntry} (hf : niEntryOk h f) : f.j < h.length := by
  cases f with
  | origin j W0 p =>
    obtain ⟨e, he, -⟩ := hf
    exact (List.getElem?_eq_some_iff.mp he).1
  | round i j sc W W' =>
    obtain ⟨-, -, ⟨e, he, -⟩, -⟩ := hf
    exact (List.getElem?_eq_some_iff.mp he).1

/-- A valid filing stays valid as the history grows. -/
theorem niEntryOk_snoc {h : List Obs} {f : NiEntry} (e : Obs) (hf : niEntryOk h f) :
    niEntryOk (h ++ [e]) f := by
  have hlt := niEntryOk_lt hf
  cases f with
  | origin j W0 p =>
    have hlt' : j < h.length := hlt
    obtain ⟨e', he', hfit⟩ := hf
    exact ⟨e', by rw [List.getElem?_append_left hlt']; exact he', hfit⟩
  | round i j sc W W' =>
    obtain ⟨hij, ⟨x, hx, hxf⟩, ⟨e', he', hef⟩, hr, hp, hq⟩ := hf
    have hlt' : j < h.length := hlt
    exact ⟨hij, ⟨x, by rw [List.getElem?_append_left (by omega)]; exact hx, hxf⟩,
      ⟨e', by rw [List.getElem?_append_left hlt']; exact he', hef⟩, hr, hp, hq⟩

/-- The new last position reads the appended event. -/
theorem niLast {h : List Obs} {e e' : Obs} {j : Nat} (hj : (h ++ [e])[j]? = some e')
    (hle : h.length ≤ j) : j = h.length ∧ e' = e := by
  rw [List.getElem?_append_right hle] at hj
  have h1 := (List.getElem?_eq_some_iff.mp hj).1
  simp only [List.length_singleton] at h1
  have hj' : j = h.length := by omega
  subst hj'
  simp at hj
  exact ⟨rfl, hj.symm⟩

/-- The empty history, filed by nothing. -/
theorem niOk_nil : niOk [] [] :=
  ⟨fun _ hf => absurd hf List.not_mem_nil, fun j e hj _ => by simp at hj⟩

/-- **A non-enter event steps the ledger blind** (exits, power, UART). -/
theorem niOk_snoc {h : List Obs} {F : List NiEntry} {e : Obs} (he : isUEnter e = false)
    (hF : niOk h F) : niOk (h ++ [e]) F := by
  obtain ⟨hv, hc⟩ := hF
  refine ⟨fun f hf => niEntryOk_snoc e (hv f hf), fun j e' hj hu => ?_⟩
  by_cases hlt : j < h.length
  · rw [List.getElem?_append_left hlt] at hj
    exact hc j e' hj hu
  · obtain ⟨-, rfl⟩ := niLast hj (by omega)
    rw [he] at hu
    cases hu

/-- **The filing an enter's evidence makes** (M2-W2d: named, so the claim it
cites is known): at position `h.length`, a round citing the exit at `i` or
an origin spending the claim at `p`. -/
def niFiling (h : List Obs) (ox : Option (Nat × Obs)) (W0 : Uvis) (p : Nat) (sc : BitVec 64)
    (W W' : Uvis) : NiEntry :=
  match ox with
  | none => .origin h.length W0 p
  | some (i, _) => .round i h.length sc W W'

/-- **An enter's evidence is a valid filing** at the new position. -/
theorem niFiling_ok {h : List Obs} {e : Obs} {ox : Option (Nat × Obs)} (hfit : niFit ox e)
    (hrc : ∀ i x, ox = some (i, x) → i < h.length ∧ h[i]? = some x) (p : Nat) :
    ∃ (W0 : Uvis) (sc : BitVec 64) (W W' : Uvis), niEntryOk (h ++ [e]) (niFiling h ox W0 p sc W W') := by
  have hlast : (h ++ [e])[h.length]? = some e := by simp
  cases ox with
  | none =>
    obtain ⟨W0, hW0⟩ := hfit
    exact ⟨W0, 0#64, W0, W0, e, hlast, hW0⟩
  | some ix =>
    obtain ⟨i, x⟩ := ix
    obtain ⟨sc, W, W', hx, hen, hr, hp, hq, hw⟩ := hfit
    obtain ⟨hi, hxi⟩ := hrc i x rfl
    exact ⟨W, sc, W, W', hi, ⟨x, by rw [List.getElem?_append_left hi]; exact hxi, hx⟩,
      ⟨e, hlast, hen⟩, hr, hp, hq, hw⟩

/-- **Filing one more enter** (the coverage half): a valid filing of the new
last position extends the filing. -/
theorem niOk_file {h : List Obs} {F : List NiEntry} {e : Obs} {fn : NiEntry}
    (hfnj : fn.j = h.length) (hfn : niEntryOk (h ++ [e]) fn) (hF : niOk h F) :
    niOk (h ++ [e]) (F ++ [fn]) := by
  obtain ⟨hv, hc⟩ := hF
  refine ⟨fun f hf => ?_, fun j e' hj hu => ?_⟩
  · rcases List.mem_append.mp hf with hf | hf
    · exact niEntryOk_snoc e (hv f hf)
    · rw [List.mem_singleton.mp hf]; exact hfn
  · by_cases hlt : j < h.length
    · rw [List.getElem?_append_left hlt] at hj
      obtain ⟨f, ⟨hfF, hfj⟩, hu1⟩ := hc j e' hj hu
      refine ⟨f, ⟨List.mem_append_left _ hfF, hfj⟩, fun y hyF hyj => ?_⟩
      rcases List.mem_append.mp hyF with hyF | hyF
      · exact hu1 y hyF hyj
      · rw [List.mem_singleton.mp hyF] at hyj; omega
    · obtain ⟨rfl, -⟩ := niLast hj (by omega)
      refine ⟨fn, ⟨List.mem_append_right _ (List.mem_singleton.mpr rfl), hfnj⟩, fun y hyF hyj => ?_⟩
      rcases List.mem_append.mp hyF with hyF | hyF
      · have := niEntryOk_lt (hv y hyF); omega
      · exact List.mem_singleton.mp hyF

/-- **An enter is filed** at its evidence: a round citing the exit at `i`
(which the history holds there), or an origin. -/
theorem niOk_enter {h : List Obs} {F : List NiEntry} {e : Obs} {ox : Option (Nat × Obs)}
    (_he : isUEnter e = true) (hfit : niFit ox e)
    (hrc : ∀ i x, ox = some (i, x) → i < h.length ∧ h[i]? = some x)
    (hF : niOk h F) : ∃ F', niOk (h ++ [e]) F' := by
  obtain ⟨W0, sc, W, W', hfn⟩ := niFiling_ok hfit hrc 0
  refine ⟨_, niOk_file ?_ hfn hF⟩
  cases ox with
  | none => rfl
  | some ix => obtain ⟨i, x⟩ := ix; rfl

/-! ## §3b The one-shot claims, pure (NI M2-W2d, F4) -/

/-- **A fork ecall's exit**, read off the event: the ecall cause and `a7`
(GPR list index 16, `x17`) reading `fork` as a signed 32-bit number.  The
raw number, not the effective one (the mask is not in the event): a fork
the mask denies still mints its claim, which the kernel then drops. -/
def niForkExit : Obs → Bool
  | .uExit _ _ sc _ gs =>
      decide (sc = uecallScause) && decide ((BitVec.extractLsb' 0 32 (gs.getD 16 0#64)).toInt = USYS_fork)
  | _ => false

/-- The trapframe's `a7` is `tfGprs`' index 16. -/
theorem tfGprs_a7 (tf : List (BitVec 64)) : (tfGprs tf).getD 16 0#64 = tfW tf (tfArgIdx 7) := by
  unfold tfGprs tfArgIdx
  simp

/-- **The kernel's reading**: an exit that fits a key trapped at an ecall
whose effective number is fork is a fork exit. -/
theorem niForkExit_of_fits {x : Obs} {sc : BitVec 64} {W : Uvis} (hx : exitFits x sc W)
    (hec : sc = uecallScause) (hn : usysEff W.secc W.tf = USYS_fork) : niForkExit x = true := by
  obtain ⟨cpu, s, rfl⟩ := hx
  have hraw : usysNum W.tf = USYS_fork := by
    unfold usysEff at hn
    split at hn
    · exact hn
    · exact absurd hn (by decide)
  simp only [niForkExit]
  rw [tfGprs_a7]
  unfold usysNum at hraw
  simp [hec, hraw]

/-- **The claim a filing spent**, as a key: a round's at `2 i` (the exit it
cites), an origin's at `2 p + 1` (the fork exit or power-on it names). -/
def NiEntry.key : NiEntry → Nat
  | .origin _ _ p => 2 * p + 1
  | .round i _ _ _ _ => 2 * i

/-- **A key minted in `h`**: a round claim at an exit, an origin claim at a
fork exit or a power-on. -/
def niKeyOk (h : List Obs) (k : Nat) : Prop :=
  (k % 2 = 0 ∧ ∃ x, h[k / 2]? = some x ∧ isUExit x = true) ∨
  (k % 2 = 1 ∧ ∃ x, h[k / 2]? = some x ∧ (niForkExit x = true ∨ x = .powerOn))

/-- **THE ONE-SHOT FACT** (pure, for W4): distinct filings spent distinct
claims, each minted in `h` strictly before the enter it files. -/
def niOneShot (h : List Obs) (F : List NiEntry) : Prop :=
  (F.map NiEntry.key).Nodup ∧ ∀ f ∈ F, niKeyOk h f.key ∧ f.key / 2 < f.j

theorem niKeyOk_lt {h : List Obs} {k : Nat} (hk : niKeyOk h k) : k / 2 < h.length := by
  rcases hk with ⟨-, x, hx, -⟩ | ⟨-, x, hx, -⟩ <;> exact (List.getElem?_eq_some_iff.mp hx).1

theorem niKeyOk_snoc {h : List Obs} {k : Nat} (e : Obs) (hk : niKeyOk h k) : niKeyOk (h ++ [e]) k := by
  have hlt := niKeyOk_lt hk
  rcases hk with ⟨h2, x, hx, hp⟩ | ⟨h2, x, hx, hp⟩
  · exact Or.inl ⟨h2, x, by rw [List.getElem?_append_left hlt]; exact hx, hp⟩
  · exact Or.inr ⟨h2, x, by rw [List.getElem?_append_left hlt]; exact hx, hp⟩

theorem niOneShot_nil : niOneShot [] [] := ⟨List.nodup_nil, fun _ hf => absurd hf List.not_mem_nil⟩

theorem niOneShot_snoc {h : List Obs} {F : List NiEntry} (e : Obs) (hF : niOneShot h F) :
    niOneShot (h ++ [e]) F :=
  ⟨hF.1, fun f hf => ⟨niKeyOk_snoc e (hF.2 f hf).1, (hF.2 f hf).2⟩⟩

/-- **Filing spends a fresh claim**: a filing at the new position whose key
was minted and not yet spent keeps the fact. -/
theorem niOneShot_file {h : List Obs} {F : List NiEntry} {e : Obs} {fn : NiEntry}
    (hF : niOneShot h F) (hk : niKeyOk h fn.key) (hfresh : fn.key ∉ F.map NiEntry.key)
    (hj : fn.j = h.length) : niOneShot (h ++ [e]) (F ++ [fn]) := by
  refine ⟨?_, fun f hf => ?_⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨hF.1, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro a ha b hb hab
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb hab
    exact hfresh ha
  · rcases List.mem_append.mp hf with hf | hf
    · exact ⟨niKeyOk_snoc e (hF.2 f hf).1, (hF.2 f hf).2⟩
    · rw [List.mem_singleton.mp hf]
      exact ⟨niKeyOk_snoc e hk, by rw [hj]; exact niKeyOk_lt hk⟩

/-! ## §4 The kernel's carrier (ruling O2) -/

section
variable {hlc : HasLC}

/-- **The record accepts `niFit`'s evidence** (ruling O2's Prop class, as
`SchedCtx.ClaimIs`; deviation 1: an implication).  The boot instantiates it
beside `ClaimIs` (`SystemBootEra`); the closed trap loop's cone takes it. -/
class NiFitIs (GF : BundledGFunctors) [MachGS hlc GF] : Prop where
  fit : ∀ (ox : Option (Nat × Obs)) (e : Obs), niFit ox e → MachFixedGS.uFit (hlc := hlc) (GF := GF) ox e
  /-- (NI M2-W2d) the extra claim a fork ecall's exit mints is an origin
  ticket (the kernel routes it to the child's park) -/
  fork : ∀ (i : Nat) (x : Obs), niForkExit x = true →
    MachFixedGS.uClaimX (hlc := hlc) (GF := GF) i x ⊢ MachFixedGS.uClaimO (hlc := hlc) (GF := GF)

theorem uFit_of_niFit {GF : BundledGFunctors} [MachGS hlc GF] [NiFitIs (hlc := hlc) GF]
    (ox : Option (Nat × Obs)) (e : Obs) (h : niFit ox e) : MachFixedGS.uFit (hlc := hlc) (GF := GF) ox e :=
  NiFitIs.fit ox e h

theorem uClaimO_of_fork {GF : BundledGFunctors} [MachGS hlc GF] [NiFitIs (hlc := hlc) GF]
    (i : Nat) (x : Obs) (h : niForkExit x = true) :
    MachFixedGS.uClaimX (hlc := hlc) (GF := GF) i x ⊢ MachFixedGS.uClaimO (hlc := hlc) (GF := GF) :=
  NiFitIs.fork i x h

end

/-! ## §5 THE ONE-SHOT CLAIMS, AS RESOURCES (NI M2-W2d, F4)

The authority is a `Nat ↦ ()` ghost map (the shared `Xv6G.gmUnitG` camera,
told apart by its name `γ`, born with the trace slot): the keys it holds are
the claims minted and not yet spent; a token is its exclusive fragment.
Minting inserts at the new position's keys (fresh: every key the map holds,
and every key spent, is below `2 * h.length`); spending deletes. -/

section claims
variable {GF : BundledGFunctors} [Xv6G GF]

/-- **The round claim** of the exit at position `i`. -/
def roundClaim (γ : GName) (i : Nat) : IProp GF := γ ↪◯MAP[2 * i] ()

/-- **The child-origin claim** of the fork exit at position `i`. -/
def originClaim (γ : GName) (i : Nat) : IProp GF := γ ↪◯MAP[2 * i + 1] ()

/-- **initproc's origin claim** of the power-on at position `b` (the same
key family as `originClaim`: a position is an exit or a power-on, never
both). -/
def initClaim (γ : GName) (b : Nat) : IProp GF := γ ↪◯MAP[2 * b + 1] ()

/-- **The origin ticket** the kernel carries to a first resume
(`MachFixedGS.uClaimO`'s NI reading): some origin claim. -/
def niOriginTicket (γ : GName) : IProp GF := iprop(∃ p : Nat, γ ↪◯MAP[2 * p + 1] ())

/-- **What an exit mints beside its round claim** (`MachFixedGS.uClaimX`'s
NI reading): a fork exit's child-origin claim. -/
def niExitMint (γ : GName) (i : Nat) (x : Obs) : IProp GF :=
  if niForkExit x then originClaim γ i else iprop(emp)

/-- **What an entry spends** (`uClaimFor`'s NI reading). -/
def niSpend (γ : GName) (ox : Option (Nat × Obs)) : IProp GF :=
  uClaimForRaw (roundClaim γ) (niOriginTicket γ) ox

/-- The NI record's fork law (`NiFitIs.fork`'s instance). -/
theorem niExitMint_fork (γ : GName) (i : Nat) (x : Obs) (h : niForkExit x = true) :
    niExitMint (GF := GF) γ i x ⊢ niOriginTicket γ := by
  unfold niExitMint originClaim niOriginTicket
  rw [if_pos h]
  iintro H
  iexists i
  iexact H

theorem initClaim_ticket (γ : GName) (b : Nat) : initClaim (GF := GF) γ b ⊢ niOriginTicket γ := by
  unfold initClaim niOriginTicket
  iintro H
  iexists b
  iexact H

/-- **THE CLAIM AUTHORITY**: the unspent claims, each minted in `h` and not
spent by `F`; and the one-shot fact of `F`. -/
def niClaims (γ : GName) (h : List Obs) (F : List NiEntry) : IProp GF :=
  iprop(∃ m : RegMapF Unit, (γ ↪●MAP m) ∗
    ⌜niOneShot h F ∧ ∀ k, get? m k = some () → niKeyOk h k ∧ k ∉ F.map NiEntry.key⌝)

/-- **THE LEDGER** (ruling O6: the filing is part of the run's witness;
M2-W2d: with the claim authority at `γ`). -/
def niR (γ : GName) (h : List Obs) : IProp GF := iprop(∃ F, ⌜niOk h F⌝ ∗ niClaims γ h F)

instance niR_timeless (γ : GName) (h : List Obs) : Timeless (niR (GF := GF) γ h) := by
  unfold niR niClaims; infer_instance

/-- **What W4 reads at the end of the trace**: the filing, and that it is
one-shot. -/
theorem niR_pure (γ : GName) (h : List Obs) :
    niR (GF := GF) γ h ⊢ ⌜∃ F, niOk h F ∧ niOneShot h F⌝ := by
  unfold niR niClaims
  iintro ⟨%F, %hF, %m, -, %⟨h1, -⟩⟩
  ipureintro
  exact ⟨F, hF, h1⟩

/-- **The birth**: a fresh authority, at the empty history. -/
theorem niR_alloc : ⊢@{IProp GF} |==> ∃ γ, niR γ [] := by
  imod (ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Unit) (H := RegMapF)) with ⟨%γ, Ha⟩
  imodintro
  iexists γ
  unfold niR niClaims
  iexists []
  isplitr
  · ipureintro; exact niOk_nil
  iexists ∅
  iframe Ha
  ipureintro
  refine ⟨niOneShot_nil, fun k hk => ?_⟩
  rw [get?_empty] at hk
  cases hk

/-- A key the authority holds is below the new position's keys. -/
theorem niClaims_fresh {h : List Obs} {F : List NiEntry} {m : RegMapF Unit}
    (hm : ∀ k, get? m k = some () → niKeyOk h k ∧ k ∉ F.map NiEntry.key) (k : Nat)
    (hk : h.length ≤ k / 2) : get? m k = none := by
  cases hg : get? m k with
  | none => rfl
  | some u =>
    cases u
    have := niKeyOk_lt (hm k hg).1
    omega

/-- A spent key is below the new position's keys. -/
theorem niOneShot_key_lt {h : List Obs} {F : List NiEntry} (hF : niOneShot h F) (k : Nat)
    (hk : k ∈ F.map NiEntry.key) : k / 2 < h.length := by
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hk
  exact niKeyOk_lt (hF.2 f hf).1

/-- **`niR_snoc`**: an event that is not an enter steps the ledger blind
(minting nothing). -/
theorem niR_snoc (γ : GName) (h : List Obs) (e : Obs) (he : isUEnter e = false) :
    niR (GF := GF) γ h ⊢ niR γ (h ++ [e]) := by
  unfold niR niClaims
  iintro ⟨%F, %hF, %m, Ha, %⟨h1, hm⟩⟩
  iexists F
  isplitr
  · ipureintro; exact niOk_snoc he hF
  iexists m
  iframe Ha
  ipureintro
  exact ⟨niOneShot_snoc e h1, fun k hk => ⟨niKeyOk_snoc e (hm k hk).1, (hm k hk).2⟩⟩

/-- **`niR_exit`, THE MINT**: an exit at position `h.length` mints its round
claim and, at a fork exit, the child's origin claim. -/
theorem niR_exit (γ : GName) (h : List Obs) (e : Obs) (he : isUExit e = true) :
    niR (GF := GF) γ h ⊢ |==> (niR γ (h ++ [e]) ∗ roundClaim γ h.length ∗ niExitMint γ h.length e) := by
  have hne : isUEnter e = false := by
    cases e <;> simp_all [isUExit, isUEnter]
  unfold niR niClaims
  iintro ⟨%F, %hF, %m, Ha, %⟨h1, hm⟩⟩
  have hfr0 : get? m (2 * h.length) = none := niClaims_fresh hm _ (by omega)
  imod ghost_map_insert (2 * h.length) () hfr0 $$ Ha with ⟨Ha, Hr⟩
  -- the round key is minted
  have hkR : niKeyOk (h ++ [e]) (2 * h.length) :=
    Or.inl ⟨by omega, e, by rw [show 2 * h.length / 2 = h.length by omega]; simp, he⟩
  have hnR : 2 * h.length ∉ F.map NiEntry.key := fun hk => by
    have := niOneShot_key_lt h1 _ hk; omega
  have hm1 : ∀ k, get? (insert m (2 * h.length) ()) k = some () →
      niKeyOk (h ++ [e]) k ∧ k ∉ F.map NiEntry.key := by
    intro k hk
    by_cases hkk : 2 * h.length = k
    · subst hkk; exact ⟨hkR, hnR⟩
    · rw [get?_insert_ne hkk] at hk
      exact ⟨niKeyOk_snoc e (hm k hk).1, (hm k hk).2⟩
  cases hfk : niForkExit e
  · imodintro
    unfold niExitMint
    simp only [hfk, Bool.false_eq_true, ↓reduceIte]
    isplitl [Ha]
    · iexists F
      isplitr
      · ipureintro; exact niOk_snoc hne hF
      iexists insert m (2 * h.length) ()
      iframe Ha
      ipureintro
      exact ⟨niOneShot_snoc e h1, hm1⟩
    unfold roundClaim
    iframe Hr
  · have hfr1 : get? (insert m (2 * h.length) ()) (2 * h.length + 1) = none := by
      rw [get?_insert_ne (by omega)]
      exact niClaims_fresh hm _ (by omega)
    imod ghost_map_insert (2 * h.length + 1) () hfr1 $$ Ha with ⟨Ha, Ho⟩
    imodintro
    unfold niExitMint
    simp only [hfk, ↓reduceIte]
    isplitl [Ha]
    · iexists F
      isplitr
      · ipureintro; exact niOk_snoc hne hF
      iexists insert (insert m (2 * h.length) ()) (2 * h.length + 1) ()
      iframe Ha
      ipureintro
      refine ⟨niOneShot_snoc e h1, fun k hk => ?_⟩
      by_cases hkk : 2 * h.length + 1 = k
      · subst hkk
        refine ⟨Or.inr ⟨by omega, e, by rw [show (2 * h.length + 1) / 2 = h.length by omega]; simp,
          Or.inl hfk⟩, fun hk => ?_⟩
        have := niOneShot_key_lt h1 _ hk; omega
      · rw [get?_insert_ne hkk] at hk
        exact hm1 k hk
    unfold roundClaim originClaim
    iframe Hr Ho

/-- **`niR_powerOn`, initproc's claim**: a power-on at position `h.length`
mints the origin claim `initproc`'s first resume will spend. -/
theorem niR_powerOn (γ : GName) (h : List Obs) :
    niR (GF := GF) γ h ⊢ |==> (niR γ (h ++ [.powerOn]) ∗ initClaim γ h.length) := by
  unfold niR niClaims
  iintro ⟨%F, %hF, %m, Ha, %⟨h1, hm⟩⟩
  have hfr : get? m (2 * h.length + 1) = none := niClaims_fresh hm _ (by omega)
  imod ghost_map_insert (2 * h.length + 1) () hfr $$ Ha with ⟨Ha, Hi⟩
  imodintro
  isplitl [Ha]
  · iexists F
    isplitr
    · ipureintro; exact niOk_snoc rfl hF
    iexists insert m (2 * h.length + 1) ()
    iframe Ha
    ipureintro
    refine ⟨niOneShot_snoc _ h1, fun k hk => ?_⟩
    by_cases hkk : 2 * h.length + 1 = k
    · subst hkk
      refine ⟨Or.inr ⟨by omega, .powerOn, by rw [show (2 * h.length + 1) / 2 = h.length by omega]; simp,
        Or.inr rfl⟩, fun hk => ?_⟩
      have := niOneShot_key_lt h1 _ hk; omega
    · rw [get?_insert_ne hkk] at hk
      exact ⟨niKeyOk_snoc _ (hm k hk).1, (hm k hk).2⟩
  unfold initClaim
  iexact Hi

/-- **`niR_enter`, THE FILING** (M2-W2d: SPENDING the cited claim): an enter
with its evidence (`niFit`), the cited receipt's reading, and the claim its
filing spends -- the round claim of the exit it resumes, or an origin
ticket. -/
theorem niR_enter (γ : GName) (h : List Obs) (e : Obs) (ox : Option (Nat × Obs))
    (he : isUEnter e = true) (hfit : niFit ox e)
    (hrc : ∀ i x, ox = some (i, x) → i < h.length ∧ h[i]? = some x) :
    niSpend (GF := GF) γ ox ∗ niR γ h ⊢ |==> niR γ (h ++ [e]) := by
  unfold niR niClaims niSpend
  iintro ⟨Hc, %F, %hF, %m, Ha, %⟨h1, hm⟩⟩
  -- the claim's key, out of the token
  ihave Hk : (∃ k : Nat, ⌜∀ (W0 : Uvis) (sc : BitVec 64) (W W' : Uvis),
      (niFiling h ox W0 (k / 2) sc W W').key = k⌝ ∗ γ ↪◯MAP[k] ()) $$ [Hc]
  · cases ox with
    | none =>
      unfold uClaimForRaw niOriginTicket
      icases Hc with ⟨%p, Hc⟩
      iexists 2 * p + 1
      iframe Hc
      ipureintro
      intro W0 sc W W'
      show 2 * ((2 * p + 1) / 2) + 1 = 2 * p + 1
      omega
    | some ix =>
      obtain ⟨i, x⟩ := ix
      unfold uClaimForRaw roundClaim
      iexists 2 * i
      iframe Hc
      ipureintro
      intro W0 sc W W'
      rfl
  icases Hk with ⟨%k, %hkey, Hk⟩
  ihave %hlk := ghost_map_lookup $$ Ha Hk
  obtain ⟨hkok, hkfresh⟩ := hm k hlk
  imod ghost_map_delete k () $$ Ha Hk with Ha
  obtain ⟨W0, sc, W, W', hfn⟩ := niFiling_ok hfit hrc (k / 2)
  have hj : (niFiling h ox W0 (k / 2) sc W W').j = h.length := by
    cases ox with
    | none => rfl
    | some ix => obtain ⟨i, x⟩ := ix; rfl
  imodintro
  iexists F ++ [niFiling h ox W0 (k / 2) sc W W']
  isplitr
  · ipureintro; exact niOk_file hj hfn hF
  iexists delete m k
  iframe Ha
  ipureintro
  refine ⟨niOneShot_file h1 (by rw [hkey]; exact hkok) (by rw [hkey]; exact hkfresh) hj, fun k' hk' => ?_⟩
  by_cases hkk : k = k'
  · subst hkk; rw [get?_delete_eq rfl] at hk'; cases hk'
  · rw [get?_delete_ne hkk] at hk'
    refine ⟨niKeyOk_snoc e (hm k' hk').1, fun hin => ?_⟩
    rw [List.map_append, List.mem_append] at hin
    rcases hin with hin | hin
    · exact (hm k' hk').2 hin
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hin
      rw [hkey] at hin
      exact hkk hin.symm

end claims

end Xv6
