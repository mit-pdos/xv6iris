/-
MachCSL: the power thread.

`wp_power` is the rule for `Expr.power`, the one thread that spans eras.  Its
two arms are the machine's power events:

* `PowerOff` bumps the generation counter (`genAuth`) and drops the current
  era's interpretation: every resource of the dying generation is abandoned,
  and its harts, whose `wpHart` was stated under that generation's
  certificate, are dead from now on (`wp_dead`).
* `PowerOn` mints a fresh era -- new register maps for every hart and a new
  memory heap, allocated at the booted machine -- registers it for the new
  generation, and hands the *boot client* everything it owns
  (`powerBootRes`) together with the fact that the machine is booted
  (`bootFacts`).  The client owes back the WPs of the new generation's harts,
  which the arm forks.

The boot obligation `Hboot` is the client's whole proof of the system,
quantified over the era's ghost names and generation: it instantiates the
ambient `MachGS` with that era and generation and discharges each hart's
`wpLoop` from the boot resources -- the same shape as the Rocq prototype's
`RiscvAdequacy.wp_power_loop`.
-/
import MachCSL.Wp

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF]

/-! ## A whole register file as a ghost map -/

/-- Every register (the model's `Register` has 180 constructors). -/
def allRegs : List Register := (List.range 180).map Register.ofNat

theorem ctorIdx_lt (r : Register) : r.ctorIdx < 180 := by cases r <;> decide

theorem mem_allRegs (r : Register) : r ∈ allRegs :=
  List.mem_map.mpr ⟨r.ctorIdx, List.mem_range.mpr (ctorIdx_lt r), Register.ofNat_ctorIdx r⟩

/-- The register map holding the whole file `f`. -/
def regMapOf (f : RegFile) : RegMapF RegVal :=
  allRegs.foldl (fun m r => insert m (regIdx r) (⟨r, f r⟩ : RegVal)) ∅

private theorem foldl_get?_notin (f : RegFile) (l : List Register) (a : Register)
    (m : RegMapF RegVal) (h : a ∉ l) :
    get? (l.foldl (fun m r => insert m (regIdx r) (⟨r, f r⟩ : RegVal)) m) (regIdx a) =
      get? m (regIdx a) := by
  induction l generalizing m with
  | nil => rfl
  | cons b l ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun hm => h (List.mem_cons_of_mem _ hm))]
    exact get?_insert_ne (fun hb => h (by rw [regIdx_injective hb]; exact List.mem_cons.mpr (Or.inl rfl)))

private theorem foldl_get?_mem (f : RegFile) (l : List Register) (a : Register)
    (m : RegMapF RegVal) (h : a ∈ l) :
    get? (l.foldl (fun m r => insert m (regIdx r) (⟨r, f r⟩ : RegVal)) m) (regIdx a) =
      some ⟨a, f a⟩ := by
  induction l generalizing m with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.foldl_cons]
    by_cases hl : a ∈ l
    · exact ih _ hl
    · have hab : a = b := by
        rcases List.mem_cons.mp h with h | h
        · exact h
        · exact absurd h hl
      subst hab
      rw [foldl_get?_notin f l a _ hl]
      exact get?_insert_eq rfl

theorem regAgree_regMapOf (f : RegFile) : regAgree (regMapOf f) f :=
  fun r => foldl_get?_mem f allRegs r ∅ (mem_allRegs r)

/-- The fully owned cells of a whole register file, at register map `γ`. -/
def regCells (γ : GName) (f : RegFile) : IProp GF := iprop%
  [∗map] k ↦ v ∈ regMapOf f, γ ↪◯MAP[k] v

/-- Take one register's cell out of a whole file's cells. -/
theorem regCells_take (γ : GName) (f : RegFile) (r : Register) :
    regCells γ f ⊢@{IProp GF}
      regPointsToAt γ r (DFrac.own 1) (f r) ∗
      [∗map] k ↦ v ∈ delete (regMapOf f) (regIdx r), γ ↪◯MAP[k] v := by
  unfold regCells regPointsToAt
  iintro H
  icases (BigSepM.bigSepM_delete (regAgree_regMapOf f r)).1 $$ H with ⟨Hr, Hrest⟩
  iframe Hr Hrest

/-- Allocate one hart's register map at the file `f`. -/
theorem regs_alloc_one (f : RegFile) :
    ⊢@{IProp GF} |==> ∃ γ, regInterpAt γ f ∗ regCells γ f := by
  imod (ghost_map_alloc (regMapOf f)) with ⟨%γ, Hauth, Hcells⟩
  imodintro
  iexists γ
  unfold regCells
  iframe Hcells
  unfold regInterpAt
  iexists (regMapOf f)
  iframe Hauth
  ipureintro
  exact regAgree_regMapOf f

/-- Allocate the register maps of the (distinct) harts in `l`. -/
theorem regs_alloc_list (F : CPU → RegFile) (l : List CPU) (hl : l.Nodup) :
    ⊢@{IProp GF} |==> ∃ names : CPU → GName,
      ([∗list] cpu ∈ l, regInterpAt (names cpu) (F cpu)) ∗
      ([∗list] cpu ∈ l, regCells (names cpu) (F cpu)) := by
  induction l with
  | nil =>
    imodintro
    iexists (fun _ => 0)
    isplit <;> exact BigSepL.bigSepL_nil_intro
  | cons c l ih =>
    have hc : c ∉ l := (List.nodup_cons.mp hl).1
    imod (ih (List.nodup_cons.mp hl).2) with ⟨%names, Hi, Hc⟩
    imod (regs_alloc_one (F c)) with ⟨%γ, Hic, Hcc⟩
    imodintro
    iexists (fun c' => if c' = c then γ else names c')
    have ei : (([∗list] cpu ∈ l, regInterpAt (if cpu = c then γ else names cpu) (F cpu)) : IProp GF) =
        [∗list] cpu ∈ l, regInterpAt (names cpu) (F cpu) :=
      BigSepL.bigSepL_eq fun {k x} hk => by
        rw [if_neg (fun (h : x = c) => hc (h ▸ List.mem_of_getElem? hk))]
    have ec : (([∗list] cpu ∈ l, regCells (if cpu = c then γ else names cpu) (F cpu)) : IProp GF) =
        [∗list] cpu ∈ l, regCells (names cpu) (F cpu) :=
      BigSepL.bigSepL_eq fun {k x} hk => by
        rw [if_neg (fun (h : x = c) => hc (h ▸ List.mem_of_getElem? hk))]
    isplitl [Hic Hi]
    · iapply BigSepL.bigSepL_cons.2
      simp only [if_true]
      rw [ei]
      iframe Hic Hi
    · iapply BigSepL.bigSepL_cons.2
      simp only [if_true]
      rw [ec]
      iframe Hcc Hc

/-- Allocate every hart's register map at the files `F`. -/
theorem regs_alloc (F : CPU → RegFile) :
    ⊢@{IProp GF} |==> ∃ names : CPU → GName,
      ([∗list] cpu ∈ cpus, regInterpAt (names cpu) (F cpu)) ∗
      ([∗list] cpu ∈ cpus, regCells (names cpu) (F cpu)) :=
  regs_alloc_list F cpus (List.nodup_finRange NCPU)

/-! ## The power thread -/

/-- Allocate one ghost name per (distinct) hart in `l`, each with the
resources `P` (a generic list allocator, the shape of `regs_alloc_list`). -/
theorem names_alloc_list (P : GName → CPU → IProp GF)
    (halloc : ∀ c, ⊢@{IProp GF} |==> ∃ γ, P γ c) (l : List CPU) (hl : l.Nodup) :
    ⊢@{IProp GF} |==> ∃ names : CPU → GName, [∗list] cpu ∈ l, P (names cpu) cpu := by
  induction l with
  | nil =>
    imodintro
    iexists (fun _ => 0)
    exact BigSepL.bigSepL_nil_intro
  | cons c l ih =>
    have hc : c ∉ l := (List.nodup_cons.mp hl).1
    imod (ih (List.nodup_cons.mp hl).2) with ⟨%names, Hl⟩
    imod (halloc c) with ⟨%γ, Hc⟩
    imodintro
    iexists (fun c' => if c' = c then γ else names c')
    have e : (([∗list] cpu ∈ l, P (if cpu = c then γ else names cpu) cpu) : IProp GF) =
        [∗list] cpu ∈ l, P (names cpu) cpu :=
      BigSepL.bigSepL_eq fun {k x} hk => by
        rw [if_neg (fun (h : x = c) => hc (h ▸ List.mem_of_getElem? hk))]
    iapply BigSepL.bigSepL_cons.2
    simp only [if_true]
    rw [e]
    iframe Hc Hl

theorem names_alloc (P : GName → CPU → IProp GF) (halloc : ∀ c, ⊢@{IProp GF} |==> ∃ γ, P γ c) :
    ⊢@{IProp GF} |==> ∃ names : CPU → GName, [∗list] cpu ∈ cpus, P (names cpu) cpu :=
  names_alloc_list P halloc cpus (List.nodup_finRange NCPU)

/-- A monotone counter at 0, with its receipt. -/
theorem mono0_alloc :
    ⊢@{IProp GF} |==> ∃ γ, MonoNat.auth_own γ (DFrac.own 1) (.ofNat 0) ∗ MonoNat.lb_own γ (.ofNat 0) :=
  MonoNat.own_alloc (.ofNat 0)

/-- A monotone counter at 0. -/
theorem mono0_alloc' : ⊢@{IProp GF} |==> ∃ γ, MonoNat.auth_own γ (DFrac.own 1) (.ofNat 0) := by
  imod (MonoNat.own_alloc (.ofNat 0)) with ⟨%γ, H, _⟩
  imodintro
  iexists γ
  iexact H

/-- Peel a map big-op along the harts: one element per hart of `l`. -/
theorem bigSepM_cpus {V : Type} (Φ : Nat → V → IProp GF) (f : CPU → V) :
    ∀ (l : List CPU) (m : RegMapF V), l.Nodup → (∀ c ∈ l, get? m c.val = some (f c)) →
      ([∗map] k ↦ v ∈ m, Φ k v) ⊢@{IProp GF} [∗list] c ∈ l, Φ c.val (f c)
  | [], _, _, _ => BigSepL.bigSepL_nil_intro
  | c :: l, m, hl, hm => by
    have hc : c ∉ l := (List.nodup_cons.mp hl).1
    iintro H
    icases (BigSepM.bigSepM_delete (hm c List.mem_cons_self)).1 $$ H with ⟨Hc, Hrest⟩
    iapply BigSepL.bigSepL_cons.2
    iframe Hc
    iapply (bigSepM_cpus Φ f l (delete m c.val) (List.nodup_cons.mp hl).2 (by
      intro c' hc'
      have hne : c.val ≠ c'.val := fun h => hc (by rw [Fin.ext h]; exact hc')
      rw [LawfulPartialMap.get?_delete_ne hne]
      exact hm c' (List.mem_cons_of_mem _ hc'))) $$ Hrest

/-- A fresh running context for hart `cpu` at boot: bound 0, empty dirty set,
tied to the hart by its view receipt at 0 (the prototype's
`own_context_boot`). -/
theorem ownCtx_boot (E : EraGS GF) (cpu : CPU) :
    MonoNat.lb_own (E.viewName cpu) (.ofNat 0) ⊢@{IProp GF} |==> ∃ ξ : CtxId, ownCtxAt E cpu ξ := by
  iintro HK
  imod (MonoNat.own_alloc (.ofNat 0)) with ⟨%γb, Hb, _⟩
  imod (ghost_map_alloc_empty (K := Nat) (V := CPU) (H := RegMapF)) with ⟨%γd, Hd⟩
  imodintro
  iexists ⟨γb, γd⟩
  unfold ownCtxAt ctxAt viewLbAt
  iexists 0, 0, 0, ∅
  iframe Hb Hd HK
  isplit
  · iapply topLbAt_0
  isplit
  · ipureintro; exact Nat.le_refl _
  isplit
  · iapply topLbAt_0
  isplit
  · ipureintro
    intro k h hk
    rw [LawfulPartialMap.get?_empty] at hk
    simp at hk
  · unfold dirtyElems
    imodintro
    iintro %k %h %hk
    rw [LawfulPartialMap.get?_empty] at hk
    simp at hk

theorem ctxs_boot (E : EraGS GF) :
    ([∗list] c ∈ cpus, MonoNat.lb_own (E.viewName c) (.ofNat 0)) ⊢@{IProp GF}
      |==> [∗list] c ∈ cpus, ∃ ξ : CtxId, ownCtxAt E c ξ := by
  iintro H
  iapply BigSepL.bigSepL_bupd
  iapply BigSepL.bigSepL_mono (fun {_ c} _ => ownCtx_boot E c) $$ H

theorem ctxTok_boot_elem (E : EraGS GF) (c : CPU) :
    (∃ ξ : CtxId, ownCtxAt E c ξ) ∗ resvFragAt E c none false ⊢@{IProp GF} ∃ ξ : CtxId, ctxTokAt E c ξ := by
  iintro ⟨⟨%ξ, H⟩, Hf⟩
  iexists ξ
  unfold ctxTokAt
  iframe H Hf

/-- Every byte history of the memory `m`, fully owned, in era `E`'s heap. -/
def memCells (E : EraGS GF) (m : MemF Hist) : IProp GF := iprop%
  [∗map] a ↦ H ∈ m, pointsTo (G := E.mem) a (DFrac.own 1) H

/-- What a `PowerOn` hands the boot client of era `E`, generation `gen`, at
the booted machine `σ`: the generation's certificate, every hart's register
cells, every byte's history (the image's byte at timestamp 0), and, per
hart, a fresh running context with its memory token. -/
def powerBootRes (E : EraGS GF) (gen : Nat) (σ : MState) : IProp GF := iprop%
  genCertAt gen E ∗
  ([∗list] cpu ∈ cpus, regCells (E.regName cpu) (σ.regs cpu)) ∗
  memCells E σ.mem ∗
  ([∗list] cpu ∈ cpus, ∃ ξ : CtxId, ctxTokAt E cpu ξ) ∗
  ([∗list] cpu ∈ cpus, lockSetAt E cpu [])

/-- A hart at its cycle boundary, as the power thread forks it. -/
theorem hartWP_loop (gen : Nat) (cpu : CPU) :
    hartWP (GF := GF) gen cpu (pure ()) =
      WP (Loop gen cpu) @ Stuckness.NotStuck; ⊤ {{ IrisGS_gen.forkPost Expr GState Obs }} := rfl

theorem registryOk_insert {R : RegMapF (EraGS GF)} {n : Nat} (h : registryOk R n) (E : EraGS GF) :
    registryOk (insert R n E) (n + 1) := by
  intro k
  by_cases hk : k = n
  · subst hk
    rw [get?_insert_eq rfl]
    simp
  · rw [get?_insert_ne (Ne.symm hk), h k]
    omega

theorem registryOk_none {R : RegMapF (EraGS GF)} {n : Nat} (h : registryOk R n) :
    get? R n = none := by
  have := h n
  cases hh : get? R n
  · rfl
  · rw [hh] at this
    simp at this

/-- The power thread is safe, given the boot client: at every `PowerOn`, from
the boot resources of the fresh era at the booted machine, the WPs of the new
generation's harts. -/
theorem wp_power
    (Hboot : ∀ (E : EraGS GF) (gen : Nat) (σ : MState) (image : Mem), bootFacts σ image →
      powerBootRes E gen σ ⊢@{IProp GF} |={⊤}=> [∗list] cpu ∈ cpus, hartWP gen cpu (pure ())) :
    ⊢@{IProp GF} WP Expr.power @ Stuckness.NotStuck; ⊤ {{ _v, True }} := by
  iloeb as IH
  iapply wp_lift_step rfl
  iintro %g %ns %obs %obs' %nt Hσ
  rw [stateInterp_eq]
  unfold powerInterp
  icases Hσ with ⟨Hgen, Hstart, %R, HR, %Hok, Hcur⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  cases hpow : g.pow
  · -- powered off: `PowerOn`
    rw [eraCur_false hpow]
    have hcount : startCount g = g.gen := by simp [startCount, hpow]
    rw [hcount] at Hok
    rw [hcount]
    isplit
    · ipureintro
      exact ⟨[.powerOn], .power, bootWitness g, powerFork g.gen,
        primStep_power_on hpow (bootShape_bootWitness g)⟩
    inext
    iintro %e₂ %g₂ %eₜ %Hstep _
    obtain ⟨rfl, h⟩ := primStep_power_inv Hstep
    rcases h with ⟨hp, _, _, _⟩ | ⟨_, rfl, rfl, hgen, hpow', himg, hbf⟩
    · rw [hpow] at hp
      exact absurd hp (by decide)
    imod Hclose
    -- the new era's ghosts
    have hbf' := hbf
    obtain ⟨hmem0, hlog0, hhart0, _⟩ := hbf'
    imod (regs_alloc g₂.m.regs) with ⟨%names, Hri, Hrc⟩
    imod (genHeap_init (L := PAddr) (V := Hist) (H := MemF) g₂.m.mem) with ⟨%G, Hheap, Hpts, _⟩
    imod (names_alloc (fun γ _ => iprop(MonoNat.auth_own γ (DFrac.own 1) (.ofNat 0) ∗
      MonoNat.lb_own γ (.ofNat 0))) (fun _ => mono0_alloc)) with ⟨%vn, Hv⟩
    imod (names_alloc (fun γ _ => MonoNat.auth_own γ (DFrac.own 1) (.ofNat 0)) (fun _ => mono0_alloc'))
      with ⟨%ivn, Hiv⟩
    imod (names_alloc (fun γ _ => MonoNat.auth_own γ (DFrac.own 1) (.ofNat 0)) (fun _ => mono0_alloc'))
      with ⟨%rvn, Hrv⟩
    imod (MonoNat.own_alloc (.ofNat 0)) with ⟨%γtop, Htop, _⟩
    imod (ghost_map_alloc_empty (K := Nat) (V := Agent) (H := RegMapF)) with ⟨%γauth, Hauth⟩
    imod (ghost_map_alloc (resvMap g₂.m)) with ⟨%γresv, Hresv, Hfrags⟩
    imod (names_alloc (fun γ _ => γ ↪●MAP (∅ : StrMapF Unit))
      (fun _ => ghost_map_alloc_empty (K := String) (V := Unit) (H := StrMapF))) with ⟨%lsn, Hls⟩
    icases BigSepL.bigSepL_sep_eqv.1 $$ Hv with ⟨Hva, Hvlb⟩
    imod (ctxs_boot ⟨names, G, vn, ivn, rvn, γtop, γauth, γresv, lsn⟩) $$ Hvlb with Hctx
    imod registry_insert R g.gen ⟨names, G, vn, ivn, rvn, γtop, γauth, γresv, lsn⟩ (registryOk_none Hok)
      $$ HR with ⟨HR, #Hreg⟩
    imod startAuth_bump _ $$ Hstart with ⟨Hstart, #Hstarted⟩
    ihave #Hborn := genAuth_get_born _ $$ Hgen
    -- the reservation fragments, one per hart
    ihave Hfrags' := bigSepM_cpus (fun k v => γresv ↪◯MAP[k] v)
      (fun c => (g₂.m.resv c, (g₂.m.hr c).acq)) cpus (resvMap g₂.m) (List.nodup_finRange NCPU)
      (fun c _ => resvMap_get? g₂.m c) $$ Hfrags
    have hfrag : ∀ c : CPU, (γresv ↪◯MAP[c.val] ((g₂.m.resv c, (g₂.m.hr c).acq) : ResvVal)) ⊢@{IProp GF}
        resvFragAt ⟨names, G, vn, ivn, rvn, γtop, γauth, γresv, lsn⟩ c none false := by
      intro c
      unfold resvFragAt
      rw [(hhart0 c).2.2.2, (hhart0 c).2.2.1]
      show (γresv ↪◯MAP[c.val] ((none, false) : ResvVal)) ⊢ γresv ↪◯MAP[c.val] ((none, false) : ResvVal)
      iintro H
      iexact H
    -- the boot client
    ihave Hres : powerBootRes ⟨names, G, vn, ivn, rvn, γtop, γauth, γresv, lsn⟩ g.gen g₂.m $$ [Hrc Hpts Hctx Hfrags' Hls]
    · unfold powerBootRes genCertAt memCells
      iframe Hrc Hpts
      isplitr [Hctx Hfrags' Hls]
      · isplit
        · iexact Hborn
        isplit
        · iexact Hstarted
        · iexact Hreg
      · isplitl [Hctx Hfrags']
        · iapply BigSepL.bigSepL_mono (fun {_ c} _ => ctxTok_boot_elem _ c)
          iapply BigSepL.bigSepL_sep_eqv.2
          iframe Hctx
          iapply BigSepL.bigSepL_mono (fun {_ c} _ => hfrag c) $$ Hfrags'
        · unfold lockSetAt locksMap
          iexact Hls
    imod (Hboot ⟨names, G, vn, ivn, rvn, γtop, γauth, γresv, lsn⟩ g.gen g₂.m g.image hbf) $$ Hres with Hwps
    imodintro
    -- the state interpretation at the booted state
    rw [stateInterp_eq]
    unfold powerInterp
    rw [hgen, show startCount g₂ = g.gen + 1 by simp [startCount, hgen, hpow']]
    iframe Hgen Hstart
    isplitl [HR Hheap Hri Hva Hiv Hrv Htop Hauth Hresv]
    · iexists (insert R g.gen ⟨names, G, vn, ivn, rvn, γtop, γauth, γresv, lsn⟩)
      iframe HR
      isplit
      · ipureintro
        exact registryOk_insert Hok _
      rw [eraCur_true hpow', hgen]
      iexists ⟨names, G, vn, ivn, rvn, γtop, γauth, γresv, lsn⟩
      isplit
      · ipureintro
        exact get?_insert_eq rfl
      unfold eraInterp memModelAt
      iframe Hheap Hri Hresv
      rw [show g₂.m.top = 0 by simp [MState.top, hlog0], hlog0, authMap_nil]
      iframe Htop Hauth
      isplitl [Hva Hiv Hrv]
      · rw [BigSepL.bigSepL_eq (Φ := fun _ c => hartViewsAt ⟨names, G, vn, ivn, rvn, γtop, γauth, γresv, lsn⟩ g₂.m c)
          (Ψ := fun _ c => iprop(MonoNat.auth_own (vn c) (DFrac.own 1) (.ofNat 0) ∗
            MonoNat.auth_own (ivn c) (DFrac.own 1) (.ofNat 0) ∗
            MonoNat.auth_own (rvn c) (DFrac.own 1) (.ofNat 0)))
          (fun {_ c} _ => by
            unfold hartViewsAt
            obtain ⟨h1, h2, h3, _⟩ := hhart0 c
            simp only [h1, h2, h3]
            rfl)]
        iapply BigSepL.bigSepL_sep_eqv.2
        iframe Hva
        iapply BigSepL.bigSepL_sep_eqv.2
        iframe Hiv Hrv
      · ipureintro
        exact mmOk_boot g₂.m g.image hbf
    isplitr [Hwps]
    · iexact IH
    · unfold powerFork
      rw [BigSepL.bigSepL_map, BigSepL.bigSepL_eq (fun _ => (hartWP_loop g.gen _).symm)]
      iexact Hwps
  · -- powered on: `PowerOff`
    rw [eraCur_true hpow]
    have hcount : startCount g = g.gen + 1 := by simp [startCount, hpow]
    rw [hcount] at Hok
    isplit
    · ipureintro
      exact ⟨[.powerOff], .power, _, [], primStep_power_off hpow⟩
    inext
    iintro %e₂ %g₂ %eₜ %Hstep _
    obtain ⟨rfl, h⟩ := primStep_power_inv Hstep
    rcases h with ⟨_, rfl, rfl, rfl⟩ | ⟨hp, _, _, _⟩
    · imod Hclose
      imod genAuth_bump _ $$ Hgen with Hgen
      imodintro
      rw [stateInterp_eq]
      unfold powerInterp
      rw [show startCount { g with gen := g.gen + 1, pow := false } = g.gen + 1 by
        simp [startCount], hcount]
      iframe Hgen Hstart
      isplitl [HR]
      · iexists R
        iframe HR
        isplit
        · ipureintro
          exact Hok
        rw [eraCur_false (g := { g with gen := g.gen + 1, pow := false }) rfl]
        ipureintro
        trivial
      isplit
      · iexact IH
      · exact BigSepL.bigSepL_nil_intro
    · rw [hpow] at hp
      exact absurd hp (by decide)

end MachCSL

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF]

/-! ## Instantiating a client at a fresh era

A client proves its harts at the ambient instance (`∀ [MachGS hlc GF], … ⊢
wpLoop cpu`).  `Hboot` hands it an era and a generation; `MachGS.ofEra`
is the ambient instance at those, and `wpLoop_ofEra` turns the client's
`wpLoop` into the `hartWP` the power thread forks. -/

/-- The ambient instance at era `E`, generation `gen`. -/
@[reducible] def MachGS.ofEra (E : EraGS GF) (gen : Nat) : MachGS hlc GF :=
  { regName := E.regName, mem := E.mem, viewName := E.viewName, iviewName := E.iviewName,
    rviewName := E.rviewName, topName := E.topName, authName := E.authName, resvName := E.resvName,
    lockSetName := E.lockSetName, gen := gen }

theorem wpLoop_ofEra (E : EraGS GF) (gen : Nat) (cpu : CPU) :
    genCertAt gen E ∗ @wpLoop hlc GF (MachGS.ofEra E gen) cpu ⊢@{IProp GF}
      hartWP gen cpu (pure ()) := by
  iintro ⟨Hcert, Hwp⟩
  unfold wpLoop wpHart
  rw [show @genId hlc GF (MachGS.ofEra E gen) = gen from rfl,
    show @genCert hlc GF (MachGS.ofEra E gen) = genCertAt gen E from rfl]
  iapply Hwp
  iexact Hcert

end MachCSL
