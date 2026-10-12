/-
Weak: **R-2: THE CERTIFICATION WALK** (§1–§4; §4.5–§4.6 are `WeakRvwmoWalkb`, §5 is
`WeakRvwmoWalk3`).

Rocq: `iris/WeakRvwmoWalk.v` @ xxvzwolszwmp (split in three at its section boundaries).

## The Rocq header, in substance

`WeakRvwmoGlue2` reduces the glue's (G-3) to ONE named supply, `walkSupply`: from a consistent,
`gdexecQconf`-conformant graph, hand back a `segsRun` whose endpoint boots from `boot`/`d0`,
carries the graph's image, and whose LOG is `logOf` of the WHOLE graph.  This leaf builds that
walk.  The walk processes the graph's WRITES IN GMO ORDER, one segment per write: at log length
`n` the next segment runs the hart of `G`'s `(n+1)`-st write from its current position through
that write (`WeakRvwmoGlue2.walkExitsGmoForced` shows the order is forced).  THE START IS FREE:
the empty trace over `G.gxImg` with `pst` constantly `boot <$> seq 0 N`.

  §1  THE LOG PREFIX `wlogPfx G n log` with its nil/snoc steps; `logOfOfPfx`: at
      `n = (gwrites G).length` it IS `logOf`.
  §2  THE WALK ENGINE: `wlkInv`, `wlkStep`, `wlkRun`, `walkSupplyOfSteps` (a per-state segment
      supply IS a `walkSupply`).
  §3  THE SEGMENT'S LOG ARITHMETIC: a "non-writes, then one store" segment appends exactly the
      exit write's message (`segStepMsgs`/`wlkStepOfSeg`); a row's emission splits at every
      prefix (`hemitApp`).
  §4  THE POLICY: `wlkSegOfCert` — the segment IS what `certSegment''` delivers at
      `Ctx := wctx`, with the read policy DISCHARGED (`wpolOfSites`: `G`'s own label at a
      non-witness position, the candidate's latest-source read at a witness one) and (W-2)
      `wub` the remaining honest premise; `walkPolicy` bundles the per-state supply,
      `walkSupplyOfPolicy` is the theorem.

§4.5–§4.6 (the chained walk) and §5 (the capstone shape) are the two later files; §6 (the
`Print Assumptions` audit) and §7 (the ledger) are Rocq commands/comments.

## Deviations from Rocq

1. NAMES / VOCABULARY: camelCase (map below); `S n` ↦ `n + 1`; `l !! n` ↦ `l[n]?`; `agent` ↦
   `Nat`; `M unit` ↦ `SailM Unit`, `regstate` ↦ `RegFile`, `oib32` ↦ `Ibch`, `wreg` ↦ `Nat`,
   `register` ↦ `Register`, `dev_state` ↦ `Efab` (as `WeakRvwmoCert2` deviation 1);
   `Forall P l` ↦ `∀ x ∈ l, P x`; `es.*1` ↦ `es.map Prod.fst`, `tvs2.*1/.*2` ↦
   `tvs2.map Prod.fst/Prod.snd`; `EStep x lb` ↦ `⟨x, lb⟩`; `WMsg b v t k` ↦ `⟨b, v, t, k⟩`;
   `CSt`/`Cand` literals ↦ anonymous constructors; `gmsg` ↦ `WeakRvwmoKillArms.gmsg` (the one
   Rocq's import order resolves to); `seq 0 N` ↦ `List.range' 0 N`; `bool_decide (k ≤ kz)` ↦
   the decidable `if`.  Rocq's `ofence` is the local notation `Ofence`.
2. O2 / STAGE C — THE PINNED POLICY (`WeakRvwmoCert2` deviation 4, `WeakRvwmoCert4` deviation 4).
   The fetch is administrative, so Stage B's fetch-inertness datum (`wfetchSite`, the sixth
   conjunct of `wsiteOk`) and the `lbFetchInert` conjunct of the policies are DELETED: `wsiteOk`
   is Rocq's four conjuncts again.  `segStepOfSegment`'s policy takes and returns
   `WeakRvwmoCert2.cblkPin c0.cdImg` blocks (admin labels pinned to the candidate's image), so:
   - `wpol` and `wblkPolAt` take and return `cblkPin c0.cdImg` blocks (the true route mirrors
     through `WeakRvwmoCert2.certBlockMirrorG` at `lbPin c0.cdImg`);
   - the witness datum `wwitNd` is stated on PINNED blocks, at any image: `∀ im`, a block pinned
     to `im` has its witness re-run pinned to `im` (Rocq: plain `cblk`);
   - `wlkSegOfCert` takes `WeakRvwmoCert2.esPin St.cstC.cdImg es` after `LDev ∉ es.map
     Prod.fst` (`segStepOfSegment`'s new premise; `WeakRvwmoWalkb.wemit` carries it).
   `wpolFlat` (the refuted, over-quantified policy; no segment is built from it), `wrdsFree`,
   `wndOk` keep Rocq's unpinned `cblk`.
3. `rdsOkDec`'s case split is classical (`Classical.em`), Rocq's `decide` over `Forall` (here
   in `WeakRvwmoWalkb`); `wsrcOrWwit` likewise splits on `∃ t ∈ ts, n < t` by `by_cases`.

**Rocq → Lean name map.**  `wlog_pfx` `wlogPfx`, `wlog_pfx_nil` `wlogPfxNil`, `wlog_pfx_snoc`
`wlogPfxSnoc`, `log_of_of_pfx` `logOfOfPfx`, `wlk_inv` `wlkInv`, `wlk_step` `wlkStep`,
`wlk_inv_step` `wlkInvStep`, `wlk_run` `wlkRun`, `wlk_start` `wlkStart`, `wlk_start_inv`
`wlkStartInv`, `walk_steps` `walkSteps`, `walk_supply_of_steps` `walkSupplyOfSteps`,
`hemit_app` `hemitApp`, `es_msg_notw` `esMsgNotw`, `tr_msgs_notw` `trMsgsNotw`,
`seg_step_log` `segStepLog`, `seg_step_msgs` `segStepMsgs`, `wlk_step_of_seg` `wlkStepOfSeg`,
`wsrc_le` `WeakRvwmoWalk.wsrcLe`, `wwit` `wwit`, `wsrc_le_not_wwit` `wsrcLeNotWwit`,
`not_wwit_wsrc_le` `notWwitWsrcLe`, `wwit_not_w` `wwitNotW`, `wsrc_or_wwit` `wsrcOrWwit`,
`wrow_in_log` `wrowInLog`, `wnw` `wnw`, `wnw_of_pfx` `wnwOfPfx`, `wcls_at` `wclsAt`,
`wcls_of_pfx` `wclsOfPfx`, `gmsg_byte` `WeakRvwmoWalk.gmsgByte`, `src_in_log_of_pfx`
`srcInLogOfPfx`, `wQnd` `wQnd`, `wnd` `wnd`, `wnd_start` `wndStart`, `ndreach_fix`
`ndreachFix`, `wnd_fix` `wndFix`, `wnd_ok` `wndOk`, `wnd_wnd_ok` `wndWndOk`, `wrds_free`
`wrdsFree`, `wrds_free_nil` `wrdsFreeNil`, `wub` `wub`, `wnw_seg` `wnwSeg`, `wpol_flat`
`wpolFlat`, `wwit_nd` `wwitNd`, `wwit_site` `wwitSite`, `wsite_ok` `wsiteOk`, `wlogn` `wlogn`,
`wctx` `wctx`, `wQ` `wQ`, `wQ_rmwfree` `wQRmwfree`, `wQ_lbl` `wQLbl`, `wpol` `wpol`,
`wcls_of_wit` `wclsOfWit`, `wblk_pol_at` `wblkPolAt`, `wpol_of_sites` `wpolOfSites`,
`wctx_pres` `wctxPres`, `wlk_seg_of_cert` `wlkSegOfCert`, `walk_policy` `walkPolicy`,
`walk_policy_steps` `walkPolicySteps`, `walk_supply_of_policy` `walkSupplyOfPolicy`.

**File-qualified names:** `WeakRvwmoWalk.wsrcLe`, `WeakRvwmoWalk.gmsgByte` (in
`notes/weak-port-dupnames.json`); Lean-only:
`WeakRvwmoWalk.wlognLe`/`WeakRvwmoWalk.wlognGt` (the two `wlogn` branches, Rocq's inline
`bool_decide_eq_true_2`/`bool_decide_eq_false_2` rewrites).

**Dropped:** none (§1–§4: Rocq 60 declarations; Lean 62 = 60 + the 2 Lean-only).

**W13 (I) (plan `notes/weak-allocproc-plan.md` §C W13 (I); [OWN.27]).** the `LIo` arm of the true route's `mstepOk` is `trivial` (was refuted by `gwf`'s `False` arm).
-/
import Weak.WeakRvwmoGlue2

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

/-- The parked-fence field, abbreviated (as in `WeakRvwmoCert2`). -/
local notation "Ofence" => Option (Bool × Bool × Bool × Bool)

/-! # 1. THE LOG PREFIX -/

def wlogPfx (G : Gexec) (n : Nat) (log : List Wmsg) : Prop :=
  log.length = n ∧
  ∀ p w, p < n → gwriteAt G (p + 1) = some w → WeakRvwmoKillArms.gmsg G w = log[p]?

theorem wlogPfxNil (G : Gexec) : wlogPfx G 0 [] :=
  ⟨rfl, fun _ _ hp => absurd hp (Nat.not_lt_zero _)⟩

theorem wlogPfxSnoc (G : Gexec) (n : Nat) (log : List Wmsg) (w : Geid) (m : Wmsg) :
    wlogPfx G n log →
    gwriteAt G (n + 1) = some w → WeakRvwmoKillArms.gmsg G w = some m →
    wlogPfx G (n + 1) (log ++ [m]) := by
  rintro ⟨hlen, hpfx⟩ hw hm
  refine ⟨by rw [List.length_append, hlen]; rfl, ?_⟩
  intro p w' hp hw'
  by_cases hlt : p < n
  · rw [lookup_app_l (by omega)]
    exact hpfx p w' hlt hw'
  · have hpn : p = n := by omega
    subst hpn
    rw [hw] at hw'
    cases hw'
    rw [lookup_app_r (by omega), hlen, Nat.sub_self]
    exact hm

/-- THE PAYOFF: at the full write count the prefix IS `logOf`. -/
theorem logOfOfPfx (G : Gexec) (log : List Wmsg) :
    wlogPfx G (gwrites G).length log → logOf G log := by
  rintro ⟨hlen, hpfx⟩ p m
  constructor
  · intro hp
    have hlt : p < (gwrites G).length := by
      have := lookup_lt_Some hp
      omega
    obtain ⟨w, hw⟩ := someOfIsSome (lookup_lt_is_Some_2 hlt)
    refine ⟨w, hw, ?_⟩
    rw [hpfx p w hlt hw]
    exact hp
  · rintro ⟨w, hw, hm⟩
    have hlt : p < (gwrites G).length := lookup_lt_Some (show (gwrites G)[p]? = some w from hw)
    rw [← hpfx p w hlt hw]
    exact hm

/-! # 2. THE WALK ENGINE -/

def wlkInv (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) (St : CycState) (n : Nat) :
    Prop :=
  cstOk d0 St ∧
  St.cstC.cdImg = G.gxImg ∧
  St.cstPst 0 = (List.range' 0 N).map boot ∧
  St.cstDv 0 = d0 ∧
  wlogPfx G n (cdLogEnd St.cstC)

/-- ONE STEP: a certified segment whose appended messages are exactly the one message of
`G`'s `(n+1)`-st write. -/
def wlkStep (G : Gexec) (d0 : Efab) (St : CycState) (n : Nat) : Prop :=
  ∃ (o : Segout) (St' : CycState) (w : Geid) (m : Wmsg),
    segStep d0 o St St' ∧
    St'.cstC.cdImg = St.cstC.cdImg ∧
    St'.cstPst 0 = St.cstPst 0 ∧
    St'.cstDv 0 = St.cstDv 0 ∧
    gwriteAt G (n + 1) = some w ∧
    WeakRvwmoKillArms.gmsg G w = some m ∧
    cdLogEnd St'.cstC = cdLogEnd St.cstC ++ [m]

theorem wlkInvStep (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) (St : CycState)
    (n : Nat) :
    wlkInv boot d0 N G St n →
    wlkStep G d0 St n →
    ∃ o St', segStep d0 o St St' ∧ wlkInv boot d0 N G St' (n + 1) := by
  rintro ⟨_, himg, hpst, hdv, hlog⟩ ⟨o, St', w, m, hst, himg', hpst', hdv', hw, hm, hlog'⟩
  refine ⟨o, St', hst, hst.2.1, by rw [himg', himg], by rw [hpst', hpst], by rw [hdv', hdv], ?_⟩
  rw [hlog']
  exact wlogPfxSnoc G n _ w m hlog hw hm

/-- THE ITERATION.  `k` is the number of writes that remain. -/
theorem wlkRun (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec)
    (Hsup : ∀ St n, wlkInv boot d0 N G St n → n < (gwrites G).length → wlkStep G d0 St n)
    (k : Nat) :
    ∀ n St, wlkInv boot d0 N G St n → n + k = (gwrites G).length →
      ∃ l Sf, segsRun d0 l St Sf ∧ wlkInv boot d0 N G Sf (gwrites G).length := by
  induction k with
  | zero =>
    intro n St hinv hn
    refine ⟨[], St, .segsDone St hinv.1, ?_⟩
    rw [← hn, Nat.add_zero]
    exact hinv
  | succ k ih =>
    intro n St hinv hn
    obtain ⟨o, St', hst, hinv'⟩ := wlkInvStep boot d0 N G St n hinv (Hsup St n hinv (by omega))
    obtain ⟨l, Sf, hrun, hfin⟩ := ih (n + 1) St' hinv' (by omega)
    exact ⟨o :: l, Sf, .segsMore o l St St' Sf hst hrun, hfin⟩

/-! ## 2.1 THE START: the empty candidate over the graph's image -/

def wlkStart (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) : CycState :=
  ⟨⟨G.gxImg, []⟩, fun _ => (List.range' 0 N).map boot, fun _ => d0⟩

theorem wlkStartInv (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) :
    wlkInv boot d0 N G (wlkStart boot d0 N G) 0 := by
  refine ⟨⟨?_, ?_, rfl⟩, rfl, rfl, rfl, wlogPfxNil G⟩
  · apply srvwmoOfWf
    refine (candReachable _ ?_).1
    intro k s hs
    simp [wlkStart] at hs
  · intro k s hs
    change ([] : List Estep)[k]? = some s at hs
    simp at hs

/-! ## 2.2 THE THEOREM: a per-state segment supply IS a `walkSupply` -/

def walkSteps (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) : Prop :=
  ∀ St n, wlkInv boot d0 N G St n → n < (gwrites G).length → wlkStep G d0 St n

theorem walkSupplyOfSteps (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (N : Nat) :
    (∀ GD : Gdexec,
       rvwmoMinusDepsConsistent GD → gdexecQconf boot d0 im nh GD →
       walkSteps boot d0 N GD.gdG) →
    walkSupply boot d0 im nh N := by
  intro hsup GD _ _ _ _ _ hcons hq _ _ _ _
  obtain ⟨l, Sf, hrun, _, himg, hpst, hdv, hlog⟩ :=
    wlkRun boot d0 N GD.gdG (hsup GD hcons hq) (gwrites GD.gdG).length 0
      (wlkStart boot d0 N GD.gdG) (wlkStartInv boot d0 N GD.gdG) (Nat.zero_add _)
  exact ⟨l, wlkStart boot d0 N GD.gdG, Sf, hrun, himg, hpst, hdv, logOfOfPfx _ _ hlog⟩

/-! # 3. THE SEGMENT'S LOG ARITHMETIC -/

/-! ## 3.1 A row's emission SPLITS at every prefix -/

theorem hemitApp (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row1 row2 : List Lbl) (p : Pexv6)
    (es : List Eitem) (pfin : Pexv6) :
    hemit dv k ws (row1 ++ row2) p es pfin →
    ∃ (pm : Pexv6) (es1 es2 : List Eitem),
      hemit dv k ws row1 p es1 pm ∧
      hemit dv (k + row1.length) (rowWsAux k ws row1) row2 pm es2 pfin ∧
      es = es1 ++ es2 := by
  induction row1 generalizing k ws p es with
  | nil =>
    intro hem
    exact ⟨p, [], es, .HEnil k ws p, hem, rfl⟩
  | cons lb row1 ih =>
    intro hem
    rw [List.cons_append] at hem
    have hlen : k + (lb :: row1).length = k + 1 + row1.length := by
      rw [List.length_cons]; omega
    cases hem with
    | HEone _ _ _ _ _ ls pa da l p' es' _ har hre hst hem' =>
      obtain ⟨pm, es1, es2, h1, h2, rfl⟩ := ih (k + 1) _ p' es' hem'
      refine ⟨pm, eadm ls ++ (l, some k) :: es1, es2,
        .HEone k ws lb row1 p ls pa da l p' es1 pm har hre hst h1, ?_, by simp⟩
      rw [hlen]
      exact h2
    | HEpair _ _ _ _ _ ls1 pa da l1 pm0 dm ls2 pm2 dm2 l2 p' es' _ har1 hre hst1 har2 hst2
        hem' =>
      obtain ⟨pm, es1, es2, h1, h2, rfl⟩ := ih (k + 1) _ p' es' hem'
      refine ⟨pm, eadm ls1 ++ (l1, some k) :: (eadm ls2 ++ (l2, some k) :: es1), es2,
        .HEpair k ws lb row1 p ls1 pa da l1 pm0 dm ls2 pm2 dm2 l2 p' es1 pm har1 hre hst1 har2
          hst2 h1, ?_, by simp⟩
      rw [hlen]
      exact h2

/-! ## 3.2 A non-write step contributes no message -/

theorem esMsgNotw (s : Estep) : lbIsW s.esLb = false → esMsg s = [] := by
  obtain ⟨ag, lb⟩ := s
  cases lb <;> simp [esMsg, lbWr, lbIsW]

theorem trMsgsNotw (tr : List Estep) :
    (∀ s ∈ tr, lbIsW s.esLb = false) → trMsgs tr = [] := by
  induction tr with
  | nil => intro _; rfl
  | cons s tr ih =>
    intro h
    show esMsg s ++ trMsgs tr = []
    rw [esMsgNotw s (h s (List.mem_cons_self ..)),
      ih (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))]
    rfl

/-! ## 3.3 A `segStep`'s log grows by its trace's messages -/

theorem segStepLog (d0 : Efab) (o : Segout) (St St' : CycState) :
    segStep d0 o St St' →
    cdLogEnd St'.cstC = cdLogEnd St.cstC ++ trMsgs o.soTr := by
  rintro ⟨_, _, _, htr, _, _⟩
  rw [cdLogEndFull, cdLogEndFull, htr, trMsgsApp]

/-! ## 3.4 A "non-writes, then one store" segment appends ONE message -/

theorem segStepMsgs (d0 : Efab) (o : Segout) (St St' : CycState) (pre : List Lbl) (rl : Bool)
    (base : Int) (vs : List (BitVec 8)) (kc : WmClass) :
    segStep d0 o St St' →
    o.soRow = pre ++ [Lbl.LStore rl base vs kc] →
    (∀ lb ∈ pre, lbIsW lb = false) →
    cdLogEnd St'.cstC = cdLogEnd St.cstC ++ [⟨base, vs, some o.soHart, kc⟩] := by
  intro hst hrow hpre
  have hlog := segStepLog d0 o St St' hst
  obtain ⟨_, _, _, _, hag, hf2⟩ := hst
  rw [hrow] at hf2
  have hf2' := Forall2_fmap_r.1 hf2
  obtain ⟨t1, t2, h1, h2, htr⟩ := Forall2_app_inv_l.1 hf2'
  obtain ⟨s, hs, hnil⟩ : ∃ s, lblReidxW (Lbl.LStore rl base vs kc) s.esLb ∧ t2 = [s] := by
    cases h2 with
    | cons hab hrest => cases hrest; exact ⟨_, hab, rfl⟩
  subst hnil
  have hes : s.esLb = Lbl.LStore rl base vs kc := lblReidxWStore rl base vs kc _ hs
  -- the prefix contributes nothing
  have key : ∀ (l1 : List Lbl) (l2 : List Estep),
      List.Forall₂ (fun lb s => lblReidxW lb s.esLb) l1 l2 →
      (∀ lb ∈ l1, lbIsW lb = false) → ∀ s' ∈ l2, lbIsW s'.esLb = false := by
    intro l1 l2 h
    induction h with
    | nil => intro _ s' h; exact absurd h List.not_mem_nil
    | @cons a b l1 l2 hab _ ih =>
      intro hp s' hs'
      rcases List.mem_cons.1 hs' with rfl | hs'
      · exact lblReidxWNotw a _ hab (hp a (List.mem_cons_self ..))
      · exact ih (fun lb hlb => hp lb (List.mem_cons_of_mem _ hlb)) s' hs'
  have hpre' : ∀ s' ∈ t1, lbIsW s'.esLb = false := key pre t1 h1 hpre
  have hsag : s.esAg = o.soHart := hag s (by rw [htr]; simp)
  rw [hlog, htr, trMsgsApp, trMsgsNotw t1 hpre', List.nil_append]
  show cdLogEnd St.cstC ++ (esMsg s ++ []) = _
  rw [List.append_nil]
  simp [esMsg, hes, lbWr, lbCls, hsag]

/-! ## 3.5 … hence one `wlkStep` -/

theorem wlkStepOfSeg (G : Gexec) (d0 : Efab) (St St' : CycState) (n : Nat) (o : Segout)
    (pre : List Lbl) (rl : Bool) (base : Int) (vs : List (BitVec 8)) (kc : WmClass)
    (w : Geid) :
    segStep d0 o St St' →
    o.soRow = pre ++ [Lbl.LStore rl base vs kc] →
    (∀ lb ∈ pre, lbIsW lb = false) →
    St'.cstC.cdImg = St.cstC.cdImg →
    St'.cstPst 0 = St.cstPst 0 →
    St'.cstDv 0 = St.cstDv 0 →
    gwriteAt G (n + 1) = some w →
    WeakRvwmoKillArms.gmsg G w = some ⟨base, vs, some o.soHart, kc⟩ →
    wlkStep G d0 St n :=
  fun hst hrow hpre himg hpst hdv hw hm =>
    ⟨o, St', w, ⟨base, vs, some o.soHart, kc⟩, hst, himg, hpst, hdv, hw, hm,
      segStepMsgs d0 o St St' pre rl base vs kc hst hrow hpre⟩

/-! # 4. THE POLICY -/

def WeakRvwmoWalk.wsrcLe (G : Gexec) (n : Nat) (e : Geid) : Prop :=
  ∀ aq base ts vs, gxLbl G e = some (Lbl.LLoad aq base ts vs) →
    ∀ (j : Nat) (t : Nat), ts[j]? = some t → t ≤ n

/-- … and its negation, POSITIVELY: the walk's witness set at log length `n`. -/
def wwit (G : Gexec) (n : Nat) (e : Geid) : Prop :=
  ∃ aq base ts vs,
    gxLbl G e = some (Lbl.LLoad aq base ts vs) ∧
    ∃ (j : Nat) (t : Nat), ts[j]? = some t ∧ n < t

theorem wsrcLeNotWwit (G : Gexec) (n : Nat) (e : Geid) :
    WeakRvwmoWalk.wsrcLe G n e → ¬ wwit G n e := by
  rintro hle ⟨aq, base, ts, vs, hl, j, t, hj, hlt⟩
  have := hle aq base ts vs hl j t hj
  omega

theorem notWwitWsrcLe (G : Gexec) (n : Nat) (e : Geid) :
    ¬ wwit G n e → WeakRvwmoWalk.wsrcLe G n e := by
  intro hnw aq base ts vs hl j t hj
  by_cases hle : t ≤ n
  · exact hle
  · exact absurd ⟨aq, base, ts, vs, hl, j, t, hj, by omega⟩ hnw

/-- (W-4)'s content: a WRITE position is never a witness. -/
theorem wwitNotW (G : Gexec) (n : Nat) (e : Geid) (l : Lbl) :
    gxLbl G e = some l → lbIsW l = true → ¬ wwit G n e := by
  rintro hl hw ⟨aq, base, ts, vs, hl', _⟩
  rw [hl'] at hl
  cases hl
  cases hw

/-- THE CLASSIFICATION IS LOG-DECIDED. -/
theorem wsrcOrWwit (G : Gexec) (n : Nat) (e : Geid) (lb : Lbl) :
    gxLbl G e = some lb → WeakRvwmoWalk.wsrcLe G n e ∨ wwit G n e := by
  intro hl
  cases lb with
  | LLoad aq base ts vs =>
    by_cases hex : ∃ t ∈ ts, n < t
    · right
      obtain ⟨t, hin, hlt⟩ := hex
      obtain ⟨j, hj⟩ := elem_of_list_lookup.1 hin
      exact ⟨aq, base, ts, vs, hl, j, t, hj, hlt⟩
    · left
      intro aq0 base0 ts0 vs0 hl0 j t hj
      rw [hl] at hl0
      cases hl0
      by_cases hle : t ≤ n
      · exact hle
      · exact absurd ⟨t, elem_of_list_lookup_2 hj, by omega⟩ hex
  | LStore => left; intro _ _ _ _ hl0; rw [hl] at hl0; cases hl0
  | LFence => left; intro _ _ _ _ hl0; rw [hl] at hl0; cases hl0
  | LRmw => left; intro _ _ _ _ hl0; rw [hl] at hl0; cases hl0
  | LIo => left; intro _ _ _ _ hl0; rw [hl] at hl0; cases hl0

/-- THE GRAPH-SIDE DATUM the walk carries for the hart it is running. -/
def wrowInLog (G : Gexec) (x : Nat) (n : Nat) : Prop :=
  ∀ k, 1 ≤ k → WeakRvwmoWalk.wsrcLe G n (x, k)

def wnw (W : Geid → Prop) (x : Nat) : Prop :=
  ∀ c0 : Cand, ¬ W (x, gcnt x c0.cdTr + 1)

/-- (W-4), DISCHARGED. -/
theorem wnwOfPfx (G : Gexec) (x : Nat) (n : Nat) : wrowInLog G x n → wnw (wwit G n) x :=
  fun hrow c0 => wsrcLeNotWwit _ _ _ (hrow _ (by omega))

/-! ## 4.0a (W-3): the classification, read off the log -/

def wclsAt (G : Gexec) (W : Geid → Prop) (x : Nat) (c0 : Cand) (lb' : Lbl) : Prop :=
  cstepCls G W x c0 lb' ∧
  (lbIsW lb' = true → gwix G (x, gcnt x c0.cdTr) = (cdLogEnd c0).length + 1) ∧
  -- THE POISONED STEP'S FLOOR OBLIGATION at the appended label
  cstepPoisOk G x c0 lb'

theorem wclsOfPfx (G : Gexec) (W : Geid → Prop) (n : Nat) (x : Nat) (c0 : Cand) (lb' : Lbl) :
    wlogPfx G n (cdLogEnd c0) →
    gxLbl G (x, gcnt x c0.cdTr) = some lb' →
    ¬ W (x, gcnt x c0.cdTr) →
    (lbIsW lb' = true → gwix G (x, gcnt x c0.cdTr) = n + 1) →
    wclsAt G W x c0 lb' := by
  rintro ⟨hlen, _⟩ hl hnW hix
  exact ⟨.inl ⟨hnW, hl⟩, fun hw => by rw [hix hw, hlen], fun _ hne _ => absurd hl hne⟩

/-- A log message's byte IS the graph write's byte. -/
theorem WeakRvwmoWalk.gmsgByte (G : Gexec) (w : Geid) (a : Int) (v : BitVec 8) (m : Wmsg) :
    gwritesByte G w a v → WeakRvwmoKillArms.gmsg G w = some m → msgByte m a = some v := by
  rintro ⟨l, base, vs, j, hl, hwr, hj, hb⟩ hm
  simp only [WeakRvwmoKillArms.gmsg, hl, hwr, Option.some.injEq] at hm
  subst hm
  subst hb
  unfold msgByte accAddr
  simp only
  rw [if_pos (by omega)]
  have hj' : (base + (j : Int) - base).toNat = j := by omega
  rw [hj']
  exact hj

/-- (W-3)'s READ half. -/
theorem srcInLogOfPfx (G : Gexec) (n : Nat) (c : Cand) (e : Geid) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) :
    gloadValue G →
    c.cdImg = G.gxImg →
    wlogPfx G n (cdLogEnd c) →
    gxLbl G e = some (Lbl.LLoad aq base ts vs) →
    vs.length = ts.length →
    WeakRvwmoWalk.wsrcLe G n e →
    srcInLog c base ts vs := by
  rintro hlv himg ⟨_, hpfx⟩ hl hlenv hle
  refine ⟨hlenv, ?_⟩
  intro j t v hj hv
  have hrb : greadsByte G e (accAddr base j) t v := ⟨_, base, ts, vs, j, hl, rfl, hj, hv, rfl⟩
  have hval := (hlv _ _ _ _ hrb).1
  have ht : t ≤ n := hle aq base ts vs hl j t hj
  cases t with
  | zero =>
    rw [logByte0, himg]
    exact hval
  | succ t' =>
    obtain ⟨w, hw, hwb, _⟩ := hval
    rw [logByteS, ← hpfx t' w (by omega) hw]
    cases hm : WeakRvwmoKillArms.gmsg G w with
    | some mm => exact WeakRvwmoWalk.gmsgByte G w _ v mm hwb hm
    | none =>
      exfalso
      obtain ⟨l', base', vs', j', hl', hwr, _⟩ := hwb
      simp [WeakRvwmoKillArms.gmsg, hl', hwr] at hm

/-! ## 4.0a' THE NODE, CARRIED -/

def wQnd (G : Gexec) (x : Nat) (k : Nat) (lb : Lbl) : Prop :=
  gxLbl G (x, k) = some lb

def wnd (d0 : Efab) (G : Gexec) (boot : Nat → Pexv6) (x : Nat) (k : Nat) (cpu : CPU)
    (m : SailM Unit) : Prop :=
  ∃ (m0 : SailM Unit) (rs0 : RegFile) (fn0 : Ofence) (ib0 : Ibch),
    boot x = .PHart cpu m0 rs0 fn0 ib0 ∧
    ndreach cpu d0 (wQnd G x) 0 m0 k m

theorem wndStart (d0 : Efab) (G : Gexec) (boot : Nat → Pexv6) (x : Nat) (cpu : CPU)
    (m0 : SailM Unit) (rs0 : RegFile) (fn0 : Ofence) (ib0 : Ibch) :
    boot x = .PHart cpu m0 rs0 fn0 ib0 → wnd d0 G boot x 0 cpu m0 :=
  fun h => ⟨m0, rs0, fn0, ib0, h, .ndStart⟩

/-- THE INVERSION THE SITES USE. -/
theorem ndreachFix (cpu : CPU) (d0 : Efab) (Q : Nat → Lbl → Prop) (P : SailM Unit → Prop)
    (m0 : SailM Unit) :
    P m0 →
    (∀ (m1 m2 : SailM Unit) (rs1 rs2 : RegFile) (fn1 fn2 : Ofence) (ib1 ib2 : Ibch)
       (ls : List Wlabel) (rds : List Nat) (wrs : List Register) (ann : Bool),
       P m1 → (∀ l0, l0 ∈ ls → lbAdmin true l0) →
       phrun cpu ls rds wrs ann m1 rs1 fn1 ib1 d0 m2 rs2 fn2 ib2 d0 → P m2) →
    ∀ (k : Nat) (m : SailM Unit), ndreach cpu d0 Q 0 m0 k m → k = 0 → P m := by
  intro h0 ha k m hr
  induction hr with
  | ndStart => intro _; exact h0
  | ndAdm k m m' rs rs' fn fn' ib ib' ls rds wrs ann _ hadm hrun ih =>
    intro hk
    exact ha m m' rs rs' fn fn' ib ib' ls rds wrs ann (ih hk) hadm hrun
  | ndBlk => intro hk; omega
  | ndBlkp => intro hk; omega

theorem wndFix (d0 : Efab) (G : Gexec) (boot : Nat → Pexv6) (x : Nat) (P : SailM Unit → Prop)
    (cpu : CPU) (m : SailM Unit) :
    (∀ m0 rs0 fn0 ib0, boot x = .PHart cpu m0 rs0 fn0 ib0 → P m0) →
    (∀ (m1 m2 : SailM Unit) (rs1 rs2 : RegFile) (fn1 fn2 : Ofence) (ib1 ib2 : Ibch)
       (ls : List Wlabel) (rds : List Nat) (wrs : List Register) (ann : Bool),
       P m1 → (∀ l0, l0 ∈ ls → lbAdmin true l0) →
       phrun cpu ls rds wrs ann m1 rs1 fn1 ib1 d0 m2 rs2 fn2 ib2 d0 → P m2) →
    wnd d0 G boot x 0 cpu m → P m := by
  rintro hb ha ⟨m0, rs0, fn0, ib0, hbx, hreach⟩
  exact ndreachFix cpu d0 (wQnd G x) P m0 (hb m0 rs0 fn0 ib0 hbx) ha 0 m hreach rfl

/-- THE CLOSURE LAWS, as one bundle at a fixed hart. -/
def wndOk (cpu : CPU) (d0 : Efab) (Q : Nat → Lbl → Prop)
    (Nd : Nat → CPU → SailM Unit → Prop) : Prop :=
  (∀ (k : Nat) (m m' : SailM Unit) (rs rs' : RegFile) (fn fn' : Ofence) (ib ib' : Ibch)
     (ls : List Wlabel) (rds : List Nat) (wrs : List Register) (ann : Bool),
     Nd k cpu m → (∀ l0, l0 ∈ ls → lbAdmin true l0) →
     phrun cpu ls rds wrs ann m rs fn ib d0 m' rs' fn' ib' d0 →
     Nd k cpu m') ∧
  (∀ (k : Nat) (m m' : SailM Unit) (ws : Wstate) (lb : Lbl) (l : Wlabel) (rds : List Nat)
     (wrs : List Register) (rs rs' : RegFile) (fn fn' : Ofence) (ib ib' : Ibch),
     Nd k cpu m → Q k lb →
     cblk cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' →
     Nd (k + 1) cpu m') ∧
  (∀ (k : Nat) (m m' : SailM Unit) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel) (rds : List Nat)
     (wrs : List Register) (rs rs' : RegFile) (fn fn' : Ofence) (ib ib' : Ibch),
     Nd k cpu m → Q k lb →
     cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' →
     Nd (k + 1) cpu m')

theorem wndWndOk (cpu : CPU) (d0 : Efab) (G : Gexec) (boot : Nat → Pexv6) (x : Nat)
    (Q : Nat → Lbl → Prop) :
    (∀ k lb, Q k lb → gxLbl G (x, k) = some lb) →
    wndOk cpu d0 Q (wnd d0 G boot x) := by
  intro hQ
  refine ⟨?_, ?_, ?_⟩
  · rintro k m m' rs rs' fn fn' ib ib' ls rds wrs ann ⟨m0, rs0, fn0, ib0, hb, hnd⟩ ha hr
    exact ⟨m0, rs0, fn0, ib0, hb, .ndAdm k m m' rs rs' fn fn' ib ib' ls rds wrs ann hnd ha hr⟩
  · rintro k m m' ws lb l rds wrs rs rs' fn fn' ib ib' ⟨m0, rs0, fn0, ib0, hb, hnd⟩ hq hblk
    exact ⟨m0, rs0, fn0, ib0, hb,
      .ndBlk k m m' ws lb l rds wrs rs rs' fn fn' ib ib' hnd (hQ k lb hq) hblk⟩
  · rintro k m m' ws lb l1 l2 rds wrs rs rs' fn fn' ib ib' ⟨m0, rs0, fn0, ib0, hb, hnd⟩ hq hblk
    exact ⟨m0, rs0, fn0, ib0, hb,
      .ndBlkp k m m' ws lb l1 l2 rds wrs rs rs' fn fn' ib ib' hnd (hQ k lb hq) hblk⟩

/-- THE DEPENDENCY-FREEDOM SIDE CONDITION, at every emitted block. -/
def wrdsFree (d0 : Efab) (T : List Nat) : Prop :=
  ∀ (cpu : CPU) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel) (rds : List Nat)
    (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch),
    (cblk cpu d0 ws lb l1 rds wrs m rs fn ib m' rs' fn' ib' ∨
     cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib') →
    rdsOk (fun nn => nn ∉ T) rds

theorem wrdsFreeNil (d0 : Efab) : wrdsFree d0 [] := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ nn _
  exact List.not_mem_nil

/-! ## 4.0b THE OBLIGATIONS, AND THE POSITION-INDEXED POLICY -/

def wub (G : Gexec) (W : Geid → Prop) (x : Nat) : Prop :=
  ∀ (c0 : Cand) (lb' : Lbl) (ev' : Nat → Geid),
    CtracePrefix G (candSnoc c0 ⟨x, lb'⟩) ev' W →
    witFenceUb G (candSnoc c0 ⟨x, lb'⟩) ev' W (x, gcnt x c0.cdTr + 1)

/-- (W-4) RESTRICTED TO THE SEGMENT. -/
def wnwSeg (G : Gexec) (n : Nat) (x : Nat) (k0 kz : Nat) : Prop :=
  ∀ k, k0 ≤ k → k ≤ kz → ¬ wwit G n (x, k + 1)

/-- THE OLD, OVER-QUANTIFIED POLICY (kept ONLY as the subject of `WeakRvwmoWalkb`'s refutation;
Rocq's, deviation 2). -/
def wpolFlat (G : Gexec) (W : Geid → Prop) (x : Nat) (cpu : CPU) (d0 : Efab) (T : List Nat)
    (Q : Lbl → Prop) : Prop :=
  ∀ (c0 : Cand) (ws : Wstate) (lb : Lbl) (l : Wlabel) (rds : List Nat) (wrs : List Register)
    (m : SailM Unit) (rs1 rs2 : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch),
    srvwmoConsistent c0 →
    cpolCtx G W x c0 →
    Q lb →
    ((candLastSt c0).msWs x).wRelp = ws.wRelp →
    dregAgree (fun nn => nn ∉ T) rs1 rs2 →
    cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ lb' l' rds' wrs' rs2',
      cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m' rs2' fn' ib' ∧
      mstepOk (candLastSt c0) x lb' ∧
      lblReidxW lb lb' ∧
      wclsAt G W x c0 lb' ∧
      dregAgree (fun nn => nn ∉ T) rs1' rs2'

/-- THE WITNESS SITE DATUM's machine-side clause (deviation 2: on blocks pinned to any image
`im`). -/
def wwitNd (d0 : Efab) (T : List Nat) (Nd : Nat → CPU → SailM Unit → Prop) (p : Nat) : Prop :=
  ∀ (im : Image) (cpu : CPU) (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8))
    (l : Wlabel) (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs : RegFile)
    (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch)
    (tvs2 : List (Nat × BitVec 8)),
    Nd p cpu m →
    WeakRvwmoCert2.cblkPin im cpu d0 ws (Lbl.LLoad aq base ts vs) l rds wrs m rs fn ib m' rs'
      fn' ib' →
    tvs2.length = ts.length →
    ∃ (l2 : Wlabel) (rds2 : List Nat) (wrs2 : List Register) (m2 : SailM Unit),
      WeakRvwmoCert2.cblkPin im cpu d0 ws
        (Lbl.LLoad aq base (tvs2.map Prod.fst) (tvs2.map Prod.snd))
        l2 rds2 wrs2 m rs fn ib m2 rs' fn' ib' ∧
      csync T m' rs' fn' ib' m2 rs' fn' ib'

def wwitSite (G : Gexec) (d0 : Efab) (T : List Nat) (Nd : Nat → CPU → SailM Unit → Prop)
    (n : Nat) (x : Nat) (p : Nat) : Prop :=
  (∀ (c : Cand) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)),
     c.cdImg = G.gxImg →
     wlogPfx G n (cdLogEnd c) →
     gxLbl G (x, p) = some (Lbl.LLoad aq base ts vs) →
     aq = false ∧ latestBytesOk c base ts.length) ∧
  wwitNd d0 T Nd p

/-- THE SITE DATUM. -/
def wsiteOk (G : Gexec) (d0 : Efab) (T : List Nat) (Nd : Nat → CPU → SailM Unit → Prop)
    (n : Nat) (x : Nat) (p : Nat) (lb : Lbl) : Prop :=
  gxLbl G (x, p) = some lb ∧
  (lbIsW lb = true → gwix G (x, p) = n + 1) ∧
  lbRmwfree lb ∧
  (wwit G n (x, p) → wwitSite G d0 T Nd n x p)

/-- The log length a candidate at row position `k` of the segment carries. -/
def wlogn (n kz k : Nat) : Nat :=
  if k ≤ kz then n else n + 1

theorem WeakRvwmoWalk.wlognLe (n kz k : Nat) : k ≤ kz → wlogn n kz k = n := by
  intro h; unfold wlogn; rw [if_pos h]

theorem WeakRvwmoWalk.wlognGt (n kz k : Nat) : kz < k → wlogn n kz k = n + 1 := by
  intro h; unfold wlogn; rw [if_neg (by omega)]

/-- THE WALK'S CARRIED CONTEXT, INDEXED BY ROW POSITION. -/
def wctx (G : Gexec) (n : Nat) (x : Nat) (kz : Nat) (k : Nat) (c : Cand) : Prop :=
  cpolCtx G (wwit G n) x c ∧
  gcnt x c.cdTr = k ∧
  wlogPfx G (wlogn n kz k) (cdLogEnd c)

/-- THE SEGMENT PREDICATE, INDEXED BY ROW POSITION. -/
def wQ (G : Gexec) (d0 : Efab) (T : List Nat) (Nd : Nat → CPU → SailM Unit → Prop) (n : Nat)
    (x : Nat) (k0 kz : Nat) (k : Nat) (lb : Lbl) : Prop :=
  k0 ≤ k ∧ k ≤ kz ∧
  wsiteOk G d0 T Nd n x k lb ∧
  (lbIsW lb = true ↔ k = kz)

theorem wQRmwfree (G : Gexec) (d0 : Efab) (T : List Nat) (Nd : Nat → CPU → SailM Unit → Prop)
    (n x k0 kz k : Nat) (lb : Lbl) : wQ G d0 T Nd n x k0 kz k lb → lbRmwfree lb :=
  fun h => h.2.2.1.2.2.1

theorem wQLbl (G : Gexec) (d0 : Efab) (T : List Nat) (Nd : Nat → CPU → SailM Unit → Prop)
    (n x k0 kz k : Nat) (lb : Lbl) : wQ G d0 T Nd n x k0 kz k lb → gxLbl G (x, k) = some lb :=
  fun h => h.2.2.1.1

/-! ## 4.0c THE POLICY AT AN ALIGNED CANDIDATE, AND ITS DISCHARGE -/

/-- (deviation 2: on blocks pinned to the candidate's image.) -/
def wpol (G : Gexec) (n : Nat) (x : Nat) (cpu : CPU) (d0 : Efab) (T : List Nat)
    (Nd : Nat → CPU → SailM Unit → Prop) (k0 kz : Nat) : Prop :=
  ∀ (k : Nat) (c0 : Cand) (ws : Wstate) (lb : Lbl) (l : Wlabel) (rds : List Nat)
    (wrs : List Register) (m : SailM Unit) (rs1 rs2 : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch),
    srvwmoConsistent c0 →
    wctx G n x kz k c0 →
    wQ G d0 T Nd n x k0 kz k lb →
    ((candLastSt c0).msWs x).wRelp = ws.wRelp →
    dregAgree (fun nn => nn ∉ T) rs1 rs2 →
    rdsOk (fun nn => nn ∉ T) rds →
    Nd k cpu m →
    WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ (lb' : Lbl) (l' : Wlabel) (rds' : List Nat) (wrs' : List Register) (rs2' : RegFile)
      (m2' : SailM Unit) (fn2' : Ofence) (ib2' : Ibch),
      WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m2' rs2' fn2' ib2' ∧
      mstepOk (candLastSt c0) x lb' ∧
      lblReidxW lb lb' ∧
      wclsAt G (wwit G n) x c0 lb' ∧
      csync T m' rs1' fn' ib' m2' rs2' fn2' ib2' ∧
      (lbIsW lb = true → clockstep T m' rs1' fn' ib' m2' rs2' fn2' ib2')

/-- THE CLASSIFICATION AT A WITNESS. -/
theorem wclsOfWit (G : Gexec) (W : Geid → Prop) (x : Nat) (c0 : Cand) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) :
    gxLbl G (x, gcnt x c0.cdTr) = some (Lbl.LLoad false base ts vs) →
    W (x, gcnt x c0.cdTr) →
    wclsAt G W x c0 (latestReadLbl c0 false base ts.length) := by
  intro hl hW
  refine ⟨.inr (.inl ⟨hW, base, ts.length, ts, vs, hl, rfl, rfl⟩), ?_, ?_⟩
  · intro hw
    rw [latestReadNotW] at hw
    cases hw
  · intro _ _ hnw
    exact absurd ⟨base, ts.length, ts, vs, hl, rfl, rfl⟩ hnw

/-- THE TWO READ ROUTES, AS ONE BLOCK POLICY (deviation 2: on pinned blocks). -/
theorem wblkPolAt (G : Gexec) (n : Nat) (x : Nat) (cpu : CPU) (d0 : Efab) (T : List Nat)
    (Nd : Nat → CPU → SailM Unit → Prop) (c0 : Cand) (ws : Wstate) (lb : Lbl) (l : Wlabel)
    (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs1 rs2 : RegFile) (fn : Ofence)
    (ib : Ibch) (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    rvwmoMinusConsistent G →
    WPolocClosed G (wwit G n) →
    srvwmoConsistent c0 →
    c0.cdImg = G.gxImg →
    wlogPfx G n (cdLogEnd c0) →
    cpolCtx G (wwit G n) x c0 →
    wsiteOk G d0 T Nd n x (gcnt x c0.cdTr) lb →
    dregAgree (fun nn => nn ∉ T) rs1 rs2 →
    rdsOk (fun nn => nn ∉ T) rds →
    Nd (gcnt x c0.cdTr) cpu m →
    WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ (lb' : Lbl) (l' : Wlabel) (rds' : List Nat) (wrs' : List Register) (rs2' : RegFile)
      (m2' : SailM Unit) (fn2' : Ofence) (ib2' : Ibch),
      WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m2' rs2' fn2' ib2' ∧
      mstepOk (candLastSt c0) x lb' ∧
      lblReidxW lb lb' ∧
      wclsAt G (wwit G n) x c0 lb' ∧
      csync T m' rs1' fn' ib' m2' rs2' fn2' ib2' ∧
      (lbIsW lb = true → clockstep T m' rs1' fn' ib' m2' rs2' fn2' ib2') := by
  intro hcons hpc hc himg hpfx hctx hsite hag hrds hnd hblk
  have hwf : gwf G := hcons.1
  have hlv : gloadValue G := hcons.2.2.1
  obtain ⟨hl, hix, hrmw, hwit⟩ := hsite
  obtain ⟨rs2', hblk2, hag2⟩ := WeakRvwmoCert2.certBlockMirrorG (WeakRvwmoCert2.lbPin c0.cdImg)
    (fun nn => nn ∉ T) cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' rs2 hblk hrds hag
  rcases wsrcOrWwit G n (x, gcnt x c0.cdTr) lb hl with hle | hW
  · -- THE TRUE ROUTE
    have hnW : ¬ wwit G n (x, gcnt x c0.cdTr) := wsrcLeNotWwit _ _ _ hle
    have hok : mstepOk (candLastSt c0) x lb := by
      cases lb with
      | LLoad aq base ts vs =>
        exact cpolRead G (wwit G n) x c0 aq base ts vs hcons hpc hctx hnW hl
          (srcInLogOfPfx G n c0 (x, gcnt x c0.cdTr) aq base ts vs hlv himg hpfx hl
            (WeakRvwmoFloor.gshape G hwf _ _ hl) hle)
      | LStore rl base vs kc =>
        exact certWriteOk c0 x rl base vs kc (WeakRvwmoFloor.gshape G hwf _ _ hl)
      | LFence pr pw sr sw => exact certFenceOk c0 x pr pw sr sw
      | LRmw => exact hrmw.elim
      | LIo => trivial
    exact ⟨lb, l, rds, wrs, rs2', m', fn', ib', hblk2, hok,
      lblReidxWRefl lb, wclsOfPfx G (wwit G n) n x c0 lb hpfx hl hnW hix,
      .inl ⟨rfl, rfl, rfl, hag2⟩, fun _ => ⟨rfl, rfl, rfl, hag2⟩⟩
  · -- THE WITNESS ROUTE
    obtain ⟨aq, base, ts, vs, hl', _⟩ := id hW
    rw [hl'] at hl
    cases hl
    obtain ⟨hgs, hvf⟩ := hwit hW
    obtain ⟨haq, hbytes⟩ := hgs c0 aq base ts vs himg hpfx hl'
    subst haq
    obtain ⟨l2, rds2, wrs2, m2, hblk3, hsync⟩ := hvf c0.cdImg cpu ws false base ts vs l rds wrs
      m rs2 fn ib m' rs2' fn' ib' (witTvs c0 base ts.length) hnd hblk2
      (witTvsLength c0 base ts.length)
    rw [witTvsLbl c0 false base ts.length] at hblk3
    have hok : mstepOk (candLastSt c0) x (latestReadLbl c0 false base ts.length) :=
      certReadWitness c0 x false base ts.length hc hbytes
    refine ⟨latestReadLbl c0 false base ts.length, l2, rds2, wrs2, rs2', m2, fn', ib', hblk3, hok,
      ?_, wclsOfWit G (wwit G n) x c0 base ts vs hl' hW,
      csyncRegs T m' m2 rs2' rs1' rs2' fn' ib' hsync hag2, fun hw => by cases hw⟩
    refine .inr (.inl ?_)
    show false = false ∧ false = false ∧ base = base ∧
      (lrdTs c0 base ts.length).length = ts.length ∧
      (lrdVs c0 base ts.length).length = (lrdTs c0 base ts.length).length
    exact ⟨rfl, rfl, rfl, by simp [lrdTs], lrdLength _ _ _⟩

/-- (W-1), DISCHARGED. -/
theorem wpolOfSites (G : Gexec) (n : Nat) (x : Nat) (cpu : CPU) (d0 : Efab) (T : List Nat)
    (Nd : Nat → CPU → SailM Unit → Prop) (k0 kz : Nat) :
    rvwmoMinusConsistent G →
    WPolocClosed G (wwit G n) →
    wpol G n x cpu d0 T Nd k0 kz := by
  rintro hcons hpc k c0 ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' hc ⟨hctx, hgc, hpfx⟩
    ⟨_, hkz, hsite, _⟩ _ hag hrds hnd hblk
  have himg : c0.cdImg = G.gxImg := by
    obtain ⟨ev, hgt, _⟩ := hctx
    exact hgt.ctpImg
  have hpfx' : wlogPfx G n (cdLogEnd c0) := by
    rw [WeakRvwmoWalk.wlognLe n kz k hkz] at hpfx
    exact hpfx
  subst hgc
  exact wblkPolAt G n x cpu d0 T Nd c0 ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' hcons hpc
    hc himg hpfx' hctx hsite hag hrds hnd hblk

/-! ## 4.0d THE CONTEXT IS PRESERVED — (P-1) at the indexed instance -/

theorem wctxPres (G : Gexec) (d0 : Efab) (T : List Nat) (Nd : Nat → CPU → SailM Unit → Prop)
    (n : Nat) (x : Nat) (k0 kz : Nat) :
    gwf G →
    wub G (wwit G n) x →
    ∀ (k : Nat) (c0 : Cand) (lb lb' : Lbl),
      wctx G n x kz k c0 → srvwmoConsistent c0 →
      wQ G d0 T Nd n x k0 kz k lb →
      lblReidxW lb lb' → mstepOk (candLastSt c0) x lb' →
      wclsAt G (wwit G n) x c0 lb' →
      wctx G n x kz (k + 1) (candSnoc c0 ⟨x, lb'⟩) := by
  rintro hwf hub k c0 lb lb' ⟨hctx, hgc, hpfx⟩ _ ⟨_, hkz, hsite, hiff⟩ hri _ ⟨hcl, hix, hstp⟩
  have hpfxn : wlogPfx G n (cdLogEnd c0) := by
    rw [WeakRvwmoWalk.wlognLe n kz k hkz] at hpfx
    exact hpfx
  have hlen : (cdLogEnd c0).length = n := hpfxn.1
  refine ⟨cpolCtxSnoc G (wwit G n) x c0 lb' hwf hctx hcl hix (fun ev' hev' => hub c0 lb' ev' hev')
    hstp, by rw [gcntCandSnocSelf, hgc], ?_⟩
  rw [cdLogEndSnoc]
  by_cases hkk : k = kz
  · -- THE EXIT STORE: the log grows by G's (n+1)-st write's message
    subst hkk
    have hw : lbIsW lb = true := hiff.2 rfl
    obtain ⟨hl, _, hrmw, _⟩ := hsite
    cases lb with
    | LLoad => cases hw
    | LFence => cases hw
    | LRmw => exact hrmw.elim
    | LIo => cases hw
    | LStore rl base vs kc =>
      have hlb' : lb' = .LStore rl base vs kc := lblReidxWStore rl base vs kc lb' hri
      subst hlb'
      have hnW : ¬ wwit G n (x, gcnt x c0.cdTr) := by
        rw [hgc]
        exact wwitNotW G n (x, k) (.LStore rl base vs kc) hl rfl
      have hlbl : gxLbl G (x, gcnt x c0.cdTr) = some (.LStore rl base vs kc) := by
        rcases hcl with ⟨_, h⟩ | ⟨hW, _⟩ | ⟨_, hpl, _⟩
        · exact h
        · exact absurd hW hnW
        · have := cpoisLblNotw c0 _ hpl
          cases this
      have hwix : gwix G (x, gcnt x c0.cdTr) = n + 1 := by rw [hix rfl, hlen]
      have hmem : (x, gcnt x c0.cdTr) ∈ gwrites G :=
        gisWGwrites G _ hwf (by rw [hlbl]; rfl) (by simp only [gisW, hlbl]; rfl)
      have hat : gwriteAt G (n + 1) = some (x, gcnt x c0.cdTr) := by
        rw [← hwix]
        exact gwriteAtGwix G _ hmem
      have hmsg : WeakRvwmoKillArms.gmsg G (x, gcnt x c0.cdTr) = some ⟨base, vs, some x, kc⟩ := by
        simp [WeakRvwmoKillArms.gmsg, hlbl, lbWr, lbCls]
      rw [WeakRvwmoWalk.wlognGt n k (k + 1) (by omega)]
      exact wlogPfxSnoc G n (cdLogEnd c0) _ _ hpfxn hat hmsg
  · -- A NON-WRITE BLOCK: the log does not move
    have hw : lbIsW lb = false := by
      cases hb : lbIsW lb with
      | false => rfl
      | true => exact absurd (hiff.1 hb) hkk
    have hw' : lbIsW lb' = false := lblReidxWNotw lb lb' hri hw
    rw [esMsgNotw ⟨x, lb'⟩ hw', List.append_nil,
      WeakRvwmoWalk.wlognLe n kz (k + 1) (by omega)]
    exact hpfxn

/-! ## 4.1 THE SEGMENT, from the emission and the REDUCED ledger -/

theorem wlkSegOfCert (G : Gexec) (n : Nat) (x : Nat) (cpu : CPU) (d0 : Efab) (T : List Nat)
    (Nd : Nat → CPU → SailM Unit → Prop) (k0 kz : Nat) (ws0 : Wstate) (rowseg : List Lbl)
    (es : List Eitem) (pfin : Pexv6) (m0 : SailM Unit) (rs10 : RegFile) (fn0 : Ofence)
    (ib0 : Ibch) (St : CycState) (m20 : SailM Unit) (rs20 : RegFile) (fn20 : Ofence)
    (ib20 : Ibch) :
    rvwmoMinusConsistent G →
    WPolocClosed G (wwit G n) →
    -- (W-2)
    wub G (wwit G n) x →
    -- the two side conditions the `csync` iteration names
    wrdsFree d0 T →
    wndOk cpu d0 (wQ G d0 T Nd n x k0 kz) Nd →
    hemit (fun _ => d0) k0 ws0 rowseg (.PHart cpu m0 rs10 fn0 ib0) es pfin →
    (∀ kd ba bs, LDev kd ba bs ∉ es.map Prod.fst) →
    WeakRvwmoCert2.esPin St.cstC.cdImg es →
    (∀ i lb, rowseg[i]? = some lb → wQ G d0 T Nd n x k0 kz (k0 + i) lb) →
    cstOk d0 St →
    wctx G n x kz k0 St.cstC →
    (St.cstPst (cdEnd St.cstC))[x]? = some (.PHart cpu m20 rs20 fn20 ib20) →
    Nd k0 cpu m0 →
    csync T m0 rs10 fn0 ib0 m20 rs20 fn20 ib20 →
    ((candLastSt St.cstC).msWs x).wRelp = ws0.wRelp →
    ∃ (St' : CycState) (tradd : List Estep),
      segStep d0 ⟨x, rowseg, cdEnd St.cstC, tradd⟩ St St' ∧
      wctx G n x kz (k0 + rowseg.length) St'.cstC ∧
      St'.cstC.cdImg = St.cstC.cdImg ∧
      St'.cstPst 0 = St.cstPst 0 ∧
      St'.cstDv 0 = St.cstDv 0 := by
  intro hcons hpc hub hrdsf hNok hem hdev hes hQ hok hctx hp hnd hsync hrelp
  obtain ⟨hNa, hNb, hNbp⟩ := hNok
  have hwf : gwf G := hcons.1
  obtain ⟨St', tradd, hstep, hctx', himg, hpst0, hdv0, -⟩ :=
    segStepOfSegment x cpu d0 (fun _ => T) (wQ G d0 T Nd n x k0 kz) (wctx G n x kz)
      (wclsAt G (wwit G n) x) (fun k m => Nd k cpu m) (fun _ => List.Subset.refl _)
      (wctxPres G d0 T Nd n x k0 kz hwf hub)
      (fun _ lb ws l1 l2 rds wrs m rs fn ib m' rs' fn' ib' _ _ hblk =>
        hrdsf cpu ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' (.inr hblk))
      hNa hNb hNbp
      (fun k c0 ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' hc hcx hQ0 hrp hag hn0 hblk =>
        wpolOfSites G n x cpu d0 T Nd k0 kz hcons hpc k c0 ws lb l rds wrs m rs1 rs2 fn ib m'
          rs1' fn' ib' hc hcx hQ0 hrp hag
          (hrdsf cpu ws lb l l rds wrs m rs1 fn ib m' rs1' fn' ib'
            (.inl (WeakRvwmoCert2.cblkPinCblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hblk))) hn0 hblk)
      (cpolprOfCpolp x cpu d0 T (fun k m => Nd k cpu m) (wctx G n x kz) (wclsAt G (wwit G n) x)
        (wQ G d0 T Nd n x k0 kz)
        (cpolpOfRmwfree x cpu d0 T (wctx G n x kz) (wclsAt G (wwit G n) x)
          (wQ G d0 T Nd n x k0 kz) (fun k lb h => wQRmwfree G d0 T Nd n x k0 kz k lb h)))
      k0 ws0 rowseg es pfin m0 rs10 fn0 ib0 St m20 rs20 fn20 ib20
      hem hdev hes hQ hok hctx hp hnd hsync hrelp
  exact ⟨St', tradd, hstep, hctx', himg, hpst0, hdv0⟩

/-! ## 4.2 THE WALK'S SUPPLY, and the theorem -/

def walkPolicy (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) : Prop :=
  ∀ St n, wlkInv boot d0 N G St n → n < (gwrites G).length →
  ∃ (x : Nat) (rl : Bool) (base : Int) (vs : List (BitVec 8)) (kc : WmClass)
    (pre : List Lbl) (tradd : List Estep) (St' : CycState) (w : Geid),
    -- the graph side: the segment's exit IS `G`'s `(n+1)`-st write
    gwriteAt G (n + 1) = some w ∧
    WeakRvwmoKillArms.gmsg G w = some ⟨base, vs, some x, kc⟩ ∧
    -- the segment: hart `x`'s stretch through that write
    (∀ lb ∈ pre, lbIsW lb = false) ∧
    segStep d0 ⟨x, pre ++ [Lbl.LStore rl base vs kc], cdEnd St.cstC, tradd⟩ St St' ∧
    -- the image and (O-E)
    St'.cstC.cdImg = St.cstC.cdImg ∧
    St'.cstPst 0 = St.cstPst 0 ∧
    St'.cstDv 0 = St.cstDv 0

theorem walkPolicySteps (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) :
    walkPolicy boot d0 N G → walkSteps boot d0 N G := by
  intro hpol St n hinv hn
  obtain ⟨x, rl, base, vs, kc, pre, tradd, St', w, hw, hm, hpre, hstep, himg, hpst, hdv⟩ :=
    hpol St n hinv hn
  exact wlkStepOfSeg G d0 St St' n _ pre rl base vs kc w hstep rfl hpre himg hpst hdv hw hm

/-- THE THEOREM. -/
theorem walkSupplyOfPolicy (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (N : Nat) :
    (∀ GD : Gdexec,
       rvwmoMinusDepsConsistent GD → gdexecQconf boot d0 im nh GD →
       walkPolicy boot d0 N GD.gdG) →
    walkSupply boot d0 im nh N :=
  fun hpol => walkSupplyOfSteps boot d0 im nh N
    (fun GD hcons hq => walkPolicySteps boot d0 N GD.gdG (hpol GD hcons hq))

end Weak
