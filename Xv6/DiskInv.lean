/-
The virtio disk's DEVICE-SIDE proof: the device's own program respects the
invariant of `Xv6/DiskInvDefs.lean`, with NOTHING assumed.

    disk_leaseV     : DevSig.LeaseV .virtio (diskProto γ) (diskTaskRes γ) (diskRoot γ)
    wpDev_disk_inv  : diskInv γ ∗ genCert ∗ diskRoot γ ⊢ devWP .. rootTask (DevM.pure ())

THE TWO PROBLEMS THIS FILE SOLVES.

(1) `Virtio.serve h` reads the descriptors of head `h` at one state and
INSTALLS the request it parsed several steps later.  The install is sound
only because the chain armed at `h` cannot have moved in between, and
"nothing has happened at `h` since I looked" is not a monotone fact, so no
PERSISTENT knowledge context can carry it.  `MachCSL/WpDevDmaStep.lean`'s
`DevM.LeaseL` threads the context LINEARLY, so the task may hold an
exclusive ghost resource -- a SERVE PERMIT -- across its steps.

(2) `Virtio.body` pops like this:

    let v  <- DevM.get                          -- G1
    if live v.cfg then
      let ai <- dma16 (availIdxAddr v.cfg)      -- R1
      if v.seen /= ai then
        let h  <- dma16 (availRingAddr v.cfg v.seen)   -- R2
        let popped <- DevM.get                  -- G2
        if (phase popped h).isSome then pure () else
          DevM.modify (...seen := v.seen + 1)    -- M

and the step `M` must know that position `lo` HAS been published and which
head it names -- facts only R1 and R2 can establish.  Three mechanisms
carry them to `M`:

* the ROOT TASK holds `diskRoot γ`, the other half of the pop counter,
  across every iteration (`MachCSL.DevSig.LeaseV`'s `Cr`), so `v.seen`
  moves at no step but the root's own and the `lo` read at G1 is still the
  invariant's at `M`;
* R1 and R2 use `MachCSL.DevM.LeaseV.dmaReadV`
  (`MachCSL/WpDevDmaStepV.lean`), the read arm whose postcondition may
  depend on the value pinned, so what the answer proves reaches the rest of
  the derivation;
* what they leave behind is PERSISTENT and therefore still true at `M`:
  `diskPubLb γ (lo+1)` (the published count is a mono-nat, so it only
  grows) and `posRec γ lo i` (the published heads are a monotone list, so
  a position's head is fixed for ever).

THE MECHANISM, then, is:

* the POP finds the row for position `lo` -- `ring (lo % NUM) = i` from
  `posRec`, and `st i = .active c` from `queueOk` -- and MINTS the permit
  `permTok γ k h c` there, handing it to the `serve h` task it forks
  (`diskTaskRes γ (.serve h)`).  So a serving task never meets a free
  descriptor, the invariant holds nothing for one, and the install is
  `perm_install`: the permit says the receipt is still `.active c`.
* Each of the five reads of `Virtio.fetch` is pinned by the permit to the
  chain's bytes (`leaseL_fetch_armed`), so the request the device
  assembles IS `c.req`.
* The permit goes back at the completion (`perm_complete`).
* The task is forked with `diskUp γ` as well -- the persistent "the
  configuration is frozen at a live `c0`" -- so every address it computes
  is `c0`'s.

WHAT THE DEAD ARM COSTS.  `Xv6.diskDead` pins `v.usedIdx` and `v.seen` to
zero (the live flip needs them at `nc = lo = 0`), so the two steps that
move those two fields -- `Virtio.complete` at the end of `serve`, and the
pop in `Virtio.body` -- take `diskCfgFrozen γ c0` with
`Virtio.live c0 = true` and REFUTE the dead arm with it.

WHAT THE DRIVER'S SIDE INHERITS.  A permit records a CHAIN, so `permOk`
says its head is armed with that chain: a head the driver holds FREE has
no permit out, which is `disk_publish`'s whole obligation.  What the
driver still owes is the COMPLETION side -- see the head of the
assumed-interface section of `Xv6/DiskAcc.lean`.
-/
import Xv6.DiskInvDefs
import MachCSL.WpDevDmaStep
import MachCSL.WpDevDmaStepV

namespace Xv6

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

/-! ## Pure facts about the moves -/

theorem drain_cfg (v : VirtioState) (k : Nat) : (Virtio.drain v k).cfg = v.cfg := by
  unfold Virtio.drain; cases Virtio.alistGet v.cache k <;> rfl

theorem drain_usedIdx (v : VirtioState) (k : Nat) : (Virtio.drain v k).usedIdx = v.usedIdx := by
  unfold Virtio.drain; cases Virtio.alistGet v.cache k <;> rfl

theorem drain_inflight (v : VirtioState) (k : Nat) : (Virtio.drain v k).inflight = v.inflight := by
  unfold Virtio.drain; cases Virtio.alistGet v.cache k <;> rfl

theorem drain_seen (v : VirtioState) (k : Nat) : (Virtio.drain v k).seen = v.seen := by
  unfold Virtio.drain; cases Virtio.alistGet v.cache k <;> rfl

theorem drain_reqOf (v : VirtioState) (k : Nat) (h : BitVec 16) :
    Virtio.reqOf (Virtio.drain v k) h = Virtio.reqOf v h := by
  unfold Virtio.reqOf Virtio.phase; rw [drain_inflight]

theorem drain_cache_mem (v : VirtioState) (k : Nat) (e : Nat × List (BitVec 8))
    (h : e ∈ (Virtio.drain v k).cache) : e ∈ v.cache := by
  revert h
  unfold Virtio.drain
  cases Virtio.alistGet v.cache k with
  | none => exact id
  | some bs =>
    intro h
    exact (List.mem_filter.1 h).1

theorem setCache_mem (v : VirtioState) (k : Nat) (bs : List (BitVec 8))
    (e : Nat × List (BitVec 8)) (h : e ∈ Virtio.alistSet v.cache k bs) :
    e = (k, bs) ∨ e ∈ v.cache := by
  unfold Virtio.alistSet at h
  rcases List.mem_cons.1 h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_filter.1 h).1

/-! ## Program-shape helpers -/

/-- Inverting a `DevM.guard` step. -/
theorem guard_step_inv {S : Type} (x : Option S) (s' : S) (os : List DevObs)
    (h : (Option.map (fun y => (y, ([] : List DevObs))) x) = some (s', os)) : x = some s' := by
  cases x with
  | none => exact absurd h (by simp)
  | some y =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact congrArg some h.1

theorem DevM_bind_assoc {S T : Type} {α β : Type} (m : DevM S T α) (f : α → DevM S T β)
    (g : β → DevM S T Unit) :
    DevM.bind (DevM.bind m f) g = DevM.bind m (fun a => DevM.bind (f a) g) := by
  induction m with
  | pure a => rfl
  | op o k ih => exact congrArg (DevM.op o) (funext fun r => ih r)

/-- The tail of `Virtio.serve`, after the data phase: the status byte,
the completion gate, the used-ring element, the used index, and the
completion.  Written out so that the three branches of the data phase can
share one proof. -/
def serveTail (h : BitVec 16) (r : VioReq) : Virtio.VM Unit := do
  DevM.modify (fun v => Virtio.setPhase v h (.served r))
  DevM.dmaWriteIf (fun v => decide (Virtio.reqOf v h = some r)) r.status 1 (Virtio.statusOf r)
  DevM.modify (fun v => Virtio.setPhase v h (.status r))
  DevM.guard (fun v =>
    if (Virtio.phase v h).isSome && Virtio.completeOk v r h && Virtio.pushOk v then
      some (Virtio.setPhase v h (.pushed r)) else none)
  let v ← DevM.get
  let ui := v.usedIdx
  let c := v.cfg
  DevM.dmaWriteIf (fun s => decide (Virtio.reqOf s h = some r) && decide (s.usedIdx = ui) &&
      decide (s.cfg = c)) (Virtio.usedElemAddr c ui) 8
    (Virtio.castW (by decide : 64 = 8 * 8) ((Virtio.usedLen r) ++ (r.head.setWidth 32)))
  DevM.dmaWriteIf (fun s => decide (Virtio.reqOf s h = some r) && decide (s.usedIdx = ui) &&
      decide (s.cfg = c)) (Virtio.usedIdxAddr c) 2 (ui + 1#16)
  DevM.modify (fun v => Virtio.complete v h)


section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [DiskG GF]

/-! ## The protocol survives a move that leaves the image alone -/

/-- The protocol is stated on four things only: the configuration, the
used index, the image a read sees, and the requests in flight.  A move
that leaves all four as they were (up to the stated implications) carries
the protocol over unchanged. -/
theorem diskProto_congr (γ : DiskNames) (v v' : VirtioState)
    (hcfg : v'.cfg = v.cfg) (hidx : v'.usedIdx = v.usedIdx) (hseen : v'.seen = v.seen)
    (hview : Virtio.cacheView v' = Virtio.cacheView v)
    (hck : cacheOk v → cacheOk v')
    (hnil : v.cache = [] → v'.cache = [])
    (hcd : ∀ st, cachedOk v st → cachedOk v' st)
    (hfl : ∀ st, inflightOk v st → inflightOk v' st)
    (hni : noInflight v → noInflight v') :
    diskProto (GF := GF) γ v ⊢ diskProto γ v' := by
  have hblk : ∀ bno, blockView v' bno = blockView v bno := by
    intro bno; unfold blockView; rw [hview]
  unfold diskProto
  iintro ⟨%hc0, %pn, %pm, Hpm, %hfr, Harm⟩
  isplitl []
  · ipureintro; exact hck hc0
  iexists pn, pm
  iframe Hpm
  isplitl []
  · ipureintro; exact hfr
  icases Harm with ⟨Hd | ⟨%c0, #Hfr, %hc0', Hl⟩⟩
  · ileft
    unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, Hlo0, HnpM0, Hpos0, HstgA0, Hbs0, Hdn0, %hpure⟩
    obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hpure
    iexists m
    rw [hcfg]
    iframe Hm Hcfg Hlo0 HnpM0 Hpos0 HstgA0 Hbs0 Hdn0
    ipureintro
    refine ⟨p1, hni p2, hnil p3, ?_, p5, by rw [hidx]; exact p6, by rw [hseen]; exact p7⟩
    intro bno bs hb
    rcases p4 bno bs hb with h | h
    · exact absurd h id
    · exact Or.inr (by rw [h, hblk])
  · iright
    iexists c0
    iframe Hfr
    isplitl []
    · ipureintro; exact ⟨by rw [hcfg]; exact hc0'.1, hc0'.2.1, hc0'.2.2⟩
    unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %lo, %ring, %m, %pmap, %stg, %b, %M, %dl, %dl0, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, Hlo, HnpM, Hpos, Hstg, Hui, Hdn, #Hbs, %hpure⟩
    obtain ⟨e1, e2, e3, e4, e5, e5b, e6, e7, e8, e9, e10⟩ := hpure
    iexists st, nc, np, lo, ring, m, pmap, stg, b, M, dl, dl0
    iframe Hm Ha Hr Hu Hav Hnc Hnp Hlo HnpM Hpos Hstg Hui Hdn Hbs
    ipureintro
    refine ⟨by rw [hidx]; exact e1, by rw [hseen]; exact e2, e3, e4, e5, e5b,
      hfl st e6, ?_, hcd st e8, e9, e10⟩
    intro bno bs hb
    rcases e7 bno bs hb with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h, hblk])

/-- The common case: the move touches neither the cache nor the image. -/
theorem diskProto_congr_mem (γ : DiskNames) (v v' : VirtioState)
    (hcfg : v'.cfg = v.cfg) (hidx : v'.usedIdx = v.usedIdx) (hseen : v'.seen = v.seen)
    (hcache : v'.cache = v.cache) (hdisk : v'.disk = v.disk)
    (hfl : ∀ st, inflightOk v st → inflightOk v' st)
    (hni : noInflight v → noInflight v') :
    diskProto (GF := GF) γ v ⊢ diskProto γ v' :=
  diskProto_congr γ v v' hcfg hidx hseen (by unfold Virtio.cacheView; rw [hcache, hdisk])
    (fun h => by unfold cacheOk at *; rw [hcache]; exact h)
    (fun h => by rw [hcache]; exact h)
    (fun st h => by unfold cachedOk at *; rw [hcache]; exact h)
    hfl hni

theorem diskProto_cacheOk (γ : DiskNames) (v : VirtioState) :
    diskProto (GF := GF) γ v ⊢ ⌜cacheOk v⌝ := by
  unfold diskProto
  iintro ⟨%h, _⟩
  ipureintro; exact h

/-! ### The pop -/

theorem diskCfgFrozen_auth_agree (γ : DiskNames) (c c' : VirtioCfg) :
    ⊢@{IProp GF} diskCfgFrozen γ c -∗ diskCfgAuth γ c' -∗ ⌜c = c'⌝ := by
  unfold diskCfgFrozen diskCfgAuth
  iintro H1 H2
  ihave %h := ghost_var_agree γ.cfg _ _ _ _ $$ H1 H2
  ipureintro; exact h

/-- **The pop.**  Three things make it legal, and the root loop's linear
context carries all three: the root's own half of the pop counter pins
`lo` (so `v.seen = wrap16 lo` at THIS state, not merely at the one where
the loop looked), the persistent `diskPubLb γ (lo+1)` minted at the
`avail->idx` read says position `lo` has been published, and the
persistent `posRec γ lo i` says which head was published there.  The
invariant's row for position `lo` then yields the chain armed at `i`, and
the pop MINTS the serve permit the forked task will hold.

It also moves `v.seen`, which the DEAD arm pins to zero, so it needs the
frozen configuration -- `Virtio.body` pops only in its live branch, and
the derivation carries `diskUp γ` there. -/
theorem diskProto_pop_live (γ : DiskNames) (c0 : VirtioCfg) (v : VirtioState) (h : BitVec 16)
    (lo i : Nat) (hlive : Virtio.live c0 = true) (hh : h.toNat = i) :
    diskCfgFrozen (GF := GF) γ c0 ∗ diskLoTok γ lo ∗ diskPubLb γ (lo + 1) ∗ posRec γ lo i ∗
      diskProto γ v ⊢
      |==> (diskProto γ { Virtio.setPhase v h .popped with seen := v.seen + 1#16 } ∗
        diskLoTok γ (lo + 1) ∗ ∃ (k : Nat) (c : Chain), permTok γ k h c) := by
  have hfl : ∀ st, inflightOk v st → inflightOk (Virtio.setPhase v h .popped) st :=
    fun st hok k r hr => inflightOk_setPhase_none v st h .popped rfl hok k r hr
  unfold diskProto
  iintro ⟨#Hfr0, Hlot, #Hlb, #Hrec, %hc, %pn, %pm, Hpm, %hfr, Harm⟩
  icases Harm with ⟨Hd | ⟨%c0', #Hfr, %hc0, Hl⟩⟩
  · unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, Hlo0, HnpM0, Hpos0, HstgA0, Hbs0, Hdn0, %hpure⟩
    ihave %heq := diskCfgFrozen_auth_agree γ c0 v.cfg $$ Hfr0 Hcfg
    rw [heq, hpure.1] at hlive
    exact absurd hlive (by simp)
  · unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %lo', %ring, %m, %pmap, %stg, %b, %M, %dl, %dl0, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, Hlo, HnpM, Hpos, Hstg, Hui, Hdn, #Hbs, %hpure⟩
    obtain ⟨e1, e2, e3, e4, e5, e5b, e6, e7, e8, e9, e10⟩ := hpure
    ihave %hll := diskLo_agree γ lo' lo $$ Hlo Hlot
    subst lo'
    ihave %hlt := diskPubLb_le γ np (lo + 1) $$ HnpM Hlb
    ihave %hrl := posRec_lookup γ pmap lo i $$ Hpos Hrec
    have hri : ring (lo % NUM) = i := by
      have hx := e5.2 lo (Nat.le_refl lo) (by omega)
      rw [hrl] at hx
      exact (Option.some.inj hx).symm
    obtain ⟨hlti, hact⟩ := queueOk_head st ring lo np e4 (by omega)
    rw [hri] at hlti hact
    obtain ⟨c, hst⟩ : ∃ c : Chain, st i = .active c := by
      cases hs : st i with
      | inactive => rw [hs] at hact; exact absurd hact (by simp [HState.isActive])
      | active c => exact ⟨c, rfl⟩
    imod diskLo_update γ lo lo (lo + 1) $$ [Hlo Hlot] with ⟨Hlo, Hlot⟩
    · iframe Hlo Hlot
    unfold permAuth
    imod ghost_map_insert (V := PermVal) pn ((h, c) : PermVal)
        (hfr pn (Nat.le_refl pn)) $$ Hpm with ⟨Hpm, Htok⟩
    imodintro
    iframe Hlot
    isplitl [Hpm Hm Ha Hr Hu Hav Hnc Hnp Hlo HnpM Hpos Hstg Hui Hdn Hfr]
    · isplitl []
      · ipureintro; exact hc
      iexists (pn + 1), (PartialMap.insert pm pn ((h, c) : PermVal))
      iframe Hpm
      isplitl []
      · ipureintro; exact permFresh_insert pm pn h c hfr
      iright
      iexists c0'
      iframe Hfr
      isplitl []
      · ipureintro; exact hc0
      iexists st, nc, np, lo + 1, ring, m, pmap, stg, b, M, dl, dl0
      iframe Hm Ha Hr Hu Hav Hnc Hnp Hlo HnpM Hpos Hstg Hui Hdn Hbs
      ipureintro
      refine ⟨e1, ?_, by omega, queueOk_pop st ring lo np e4, posOk_pop pmap ring lo np e5,
        stageOk_pop stg ring lo np e5b, hfl st e6, e7, e8, ?_, e10⟩
      · show v.seen + 1#16 = wrap16 (lo + 1)
        rw [wrap16_succ, e2]
      · exact permOk_insert pm st pn h c (by omega) (by rw [hh]; exact hst) e9
    · iexists pn, c
      unfold permTok
      iexact Htok

/-! ### The capture latch -/

theorem diskProto_latch (γ : DiskNames) (v : VirtioState) (t : Option (BitVec 16)) :
    diskProto (GF := GF) γ v ⊢ diskProto γ { v with taken := t } :=
  diskProto_congr_mem γ v _ rfl rfl rfl rfl rfl (fun _ h => h) (fun h => h)

/-! ### The drain -/

theorem diskProto_drain (γ : DiskNames) (v : VirtioState) (k : Nat) :
    diskProto (GF := GF) γ v ⊢ diskProto γ (Virtio.drain v k) := by
  iintro H
  ihave %hc := diskProto_cacheOk γ v $$ H
  iapply diskProto_congr γ v (Virtio.drain v k) (drain_cfg v k) (drain_usedIdx v k)
    (drain_seen v k) (cacheView_drain v k hc)
    (fun hok e he => hok e (drain_cache_mem v k e he))
    (fun hnil => by
      have : Virtio.alistGet v.cache k = none := by rw [hnil]; rfl
      unfold Virtio.drain; rw [this]; exact hnil)
    (fun st hok e he => hok e (drain_cache_mem v k e he))
    (fun st hok kk r hr => hok kk r (by rwa [drain_reqOf] at hr))
    (fun hn kk => by rw [drain_reqOf]; exact hn kk) $$ H

/-! ### Reading one descriptor slot -/

theorem headRes_active_wf (γ : DiskNames) (pd : PAddr) (i : Nat) (c : Chain) :
    headRes (GF := GF) γ pd i (.active c) ⊢ ⌜c.hd = i ∧ c.wf⌝ := by
  show iprop(⌜c.hd = i ∧ c.wf⌝ ∗ chainLease pd c ∗ ∃ bs, diskBlock γ c.blk bs) ⊢ _
  iintro ⟨%hw, _⟩
  ipureintro; exact hw

theorem headRes_active_acc (γ : DiskNames) (pd : PAddr) (i : Nat) (c : Chain) :
    headRes (GF := GF) γ pd i (.active c) ⊢
      chainLease pd c ∗ (chainLease pd c -∗ headRes γ pd i (.active c)) := by
  show iprop(⌜c.hd = i ∧ c.wf⌝ ∗ chainLease pd c ∗ ∃ bs, diskBlock γ c.blk bs) ⊢
    iprop(chainLease pd c ∗ (chainLease pd c -∗
      (⌜c.hd = i ∧ c.wf⌝ ∗ chainLease pd c ∗ ∃ bs, diskBlock γ c.blk bs)))
  iintro ⟨%hw, Hl, Hb⟩
  iframe Hl
  iintro Hl2
  iframe Hl2 Hb
  ipureintro; exact hw

theorem headRes_acc' (γ : DiskNames) (pd : PAddr) (st : Nat → HState) (i : Nat) (s : HState)
    (hi : i < NUM) (hst : st i = s) :
    ([∗list] j ∈ List.range NUM, headRes (GF := GF) γ pd j (st j)) ⊢
      headRes γ pd i s ∗ (headRes γ pd i s -∗
        [∗list] j ∈ List.range NUM, headRes γ pd j (st j)) := by
  subst hst; exact headRes_acc γ pd st i hi

theorem headRes_wf_of (γ : DiskNames) (pd : PAddr) (st : Nat → HState) (i : Nat) (c : Chain)
    (hi : i < NUM) (hst : st i = .active c) :
    ([∗list] j ∈ List.range NUM, headRes (GF := GF) γ pd j (st j)) ⊢ ⌜c.hd = i ∧ c.wf⌝ := by
  iintro H
  icases headRes_acc' γ pd st i (.active c) hi hst $$ H with ⟨He, _⟩
  iapply headRes_active_wf γ pd i c $$ He

/-! ### The capture -/

/-- The sector a write request's `i`-th transfer caches, as a block. -/
theorem capture_blk (c : Chain) (r : VioReq) (i : Nat) (hreq : r = c.req) (hwf : c.wf)
    (hn : Virtio.reqSectorLen r i ≠ 0) : Virtio.reqKey r i / SPB = c.blk := by
  subst hreq
  have hlen : (Chain.req c).len.toNat = BSIZE := by
    show (BitVec.ofNat 32 BSIZE).toNat = BSIZE
    unfold BSIZE
    decide
  have hi : i < SPB := by
    unfold Virtio.reqSectorLen at hn
    rw [hlen] at hn
    simp only [SPB_eq, BSIZE_eq, sectorSize_eq] at *
    omega
  have hsec : c.sector.toNat % SPB = 0 := hwf.2.2.2.2.2.2
  show (((Chain.req c).sector.toNat + i) / SPB) = c.sector.toNat / SPB
  have : (Chain.req c).sector = c.sector := rfl
  rw [this]
  simp only [SPB_eq] at *
  omega

theorem diskProto_capture (γ : DiskNames) (v : VirtioState) (h : BitVec 16) (r : VioReq)
    (i : Nat) (bs : List (BitVec 8)) (hin : Virtio.reqOf v h = some r)
    (hlen : bs.length = Virtio.reqSectorLen r i) :
    diskProto (GF := GF) γ v ⊢
      diskProto γ { v with cache := Virtio.alistSet v.cache (Virtio.reqKey r i) bs } := by
  have hbsle : bs.length ≤ Virtio.sectorSize := by
    rw [hlen]; exact Nat.min_le_left _ _
  unfold diskProto
  iintro ⟨%hc, %pn, %pm, Hpm, %hfr, Harm⟩
  isplitl []
  · ipureintro
    intro e he
    rcases setCache_mem v _ bs e he with rfl | he'
    · exact hbsle
    · exact hc e he'
  iexists pn, pm
  iframe Hpm
  isplitl []
  · ipureintro; exact hfr
  icases Harm with ⟨Hd | ⟨%c0, #Hfr, %hc0, Hl⟩⟩
  · unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, Hlo0, HnpM0, Hpos0, HstgA0, Hbs0, Hdn0, %hpure⟩
    obtain ⟨p1, p2, p3, p4⟩ := hpure
    rw [p2 h] at hin
    exact absurd hin (by simp)
  · unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %lo, %ring, %m, %pmap, %stg, %b, %M, %dl, %dl0, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, Hlo, HnpM, Hpos, Hstg, Hui, Hdn, #Hbs, %hpure⟩
    obtain ⟨e1, e2, e3, e4, e5, e5b, e6, e7, e8, e9, e10⟩ := hpure
    obtain ⟨hlt, c, hst, hhd, hreq⟩ := e6 h r hin
    ihave %hwf := headRes_wf_of γ c0.desc st h.toNat c hlt hst $$ Hr
    have hfly : Virtio.reqSectorLen r i ≠ 0 → inFlightBlk st (Virtio.reqKey r i / SPB) := by
      intro hn
      exact ⟨h.toNat, c, hlt, hst, (capture_blk c r i hreq hwf.2 hn).symm⟩
    have key : imgOk { v with cache := Virtio.alistSet v.cache (Virtio.reqKey r i) bs } m
          (inFlightBlk st) ∧
        cachedOk { v with cache := Virtio.alistSet v.cache (Virtio.reqKey r i) bs } st := by
      by_cases hnf : inFlightBlk st (Virtio.reqKey r i / SPB)
      · constructor
        · intro bno bs0 hb
          rcases e7 bno bs0 hb with hx | hx
          · exact Or.inl hx
          · by_cases hbn : Virtio.reqKey r i / SPB = bno
            · exact Or.inl (hbn ▸ hnf)
            · exact Or.inr (by rw [hx, blockView_set_ne v _ bs bno hbn])
        · intro e he hne
          rcases setCache_mem v _ bs e he with rfl | he'
          · exact hnf
          · exact e8 e he' hne
      · have hz : Virtio.reqSectorLen r i = 0 := by
          rcases Nat.eq_zero_or_pos (Virtio.reqSectorLen r i) with hz | hz
          · exact hz
          · exact absurd (hfly (by omega)) hnf
        have hbnil : bs = [] := List.eq_nil_of_length_eq_zero (by rw [hlen, hz])
        subst hbnil
        constructor
        · intro bno bs0 hb
          rcases e7 bno bs0 hb with hx | hx
          · exact Or.inl hx
          · exact Or.inr (by rw [hx, blockView_set_nil v st _ bno e8 hnf])
        · intro e he hne
          rcases setCache_mem v _ [] e he with rfl | he'
          · exact absurd rfl hne
          · exact e8 e he' hne
    iright
    iexists c0
    iframe Hfr
    isplitl []
    · ipureintro; exact hc0
    iexists st, nc, np, lo, ring, m, pmap, stg, b, M, dl, dl0
    iframe Hm Ha Hr Hu Hav Hnc Hnp Hlo HnpM Hpos Hstg Hui Hdn Hbs
    ipureintro
    exact ⟨e1, e2, e3, e4, e5, e5b, fun k rr hr => e6 k rr hr, key.1, key.2, e9, e10⟩

/-! ### The completion -/

/-- **The completion.**  It bumps `v.usedIdx`, which the DEAD arm pins to
zero, so this one needs the frozen configuration -- which the serving task
carries in its `serveCtx`. -/
theorem diskProto_complete (γ : DiskNames) (c0 : VirtioCfg) (v : VirtioState) (h : BitVec 16)
    (hlive : Virtio.live c0 = true) :
    diskCfgFrozen (GF := GF) γ c0 ∗ diskProto γ v ⊢ |==> diskProto γ (Virtio.complete v h) := by
  unfold diskProto
  iintro ⟨#Hfr0, %hc, %pn, %pm, Hpm, %hfr, Harm⟩
  icases Harm with ⟨Hd | ⟨%c0', #Hfr, %hc0, Hl⟩⟩
  · unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, Hlo0, HnpM0, Hpos0, HstgA0, Hbs0, Hdn0, %hpure⟩
    ihave %heq := diskCfgFrozen_auth_agree γ c0 v.cfg $$ Hfr0 Hcfg
    rw [heq, hpure.1] at hlive
    exact absurd hlive (by simp)
  · unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %lo, %ring, %m, %pmap, %stg, %b, %M, %dl, %dl0, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, Hlo, HnpM, Hpos, Hstg, Hui, Hdn, #Hbs, %hpure⟩
    obtain ⟨e1, e2, e3, e4, e5, e5b, e6, e7, e8, e9, e10⟩ := hpure
    imodintro
    isplitl []
    · ipureintro; exact hc
    iexists pn, pm
    iframe Hpm
    isplitl []
    · ipureintro; exact hfr
    iright
    iexists c0'
    iframe Hfr
    isplitl []
    · ipureintro; exact hc0
    iexists st, nc + 1, np, lo, ring, m, pmap, stg, b, M, dl, dl0
    iframe Hm Ha Hr Hu Hav Hnc Hnp Hlo HnpM Hpos Hstg Hui Hdn Hbs
    ipureintro
    refine ⟨?_, e2, e3, e4, e5, e5b, inflightOk_complete v st h e6, e7, e8, e9,
      usedOk_complete dl dl0 nc M e10⟩
    show v.usedIdx + 1#16 = wrap16 (nc + 1)
    rw [wrap16_succ, e1]

/-! ### Opening the protocol at an in-flight head -/

/-- **The device-side accessor.**  At a state where head `h` carries the
request `r`, the protocol yields the chain armed at `h` -- whose request
IS `r` (`inflightOk`) -- together with the used ring, and the way back.
Every DMA write of `Virtio.serve`, `Virtio.xferIn` and `Virtio.xferOut` is
guarded on exactly this, so this one lemma discharges all of them. -/
theorem diskProto_chain_acc (γ : DiskNames) (s : VirtioState) (h : BitVec 16) (r : VioReq)
    (hin : Virtio.reqOf s h = some r) :
    diskProto (GF := GF) γ s ⊢ ∃ (c0 : VirtioCfg) (c : Chain),
      ⌜r = c.req ∧ c.hd = h.toNat ∧ c.wf ∧ s.cfg = c0 ∧ c0.qnum.toNat = NUM⌝ ∗
      chainLease c0.desc c ∗ usedLease c0.used ∗
      ((chainLease c0.desc c ∗ usedLease c0.used) -∗ diskProto γ s) := by
  unfold diskProto
  iintro ⟨%hc, %pn, %pm, Hpm, %hfr, Harm⟩
  icases Harm with ⟨Hd | ⟨%c0, #Hfr, %hc0, Hl⟩⟩
  · unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, Hlo0, HnpM0, Hpos0, HstgA0, Hbs0, Hdn0, %hpure⟩
    rw [hpure.2.1 h] at hin
    exact absurd hin (by simp)
  · unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %lo, %ring, %m, %pmap, %stg, %b, %M, %dl, %dl0, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, Hlo, HnpM, Hpos, Hstg, Hui, Hdn, #Hbs, %hpure⟩
    obtain ⟨e1, e2, e3, e4, e5, e5b, e6, e7, e8, e9, e10⟩ := hpure
    obtain ⟨hlt, c, hst, hhd, hreq⟩ := e6 h r hin
    ihave %hwf := headRes_wf_of γ c0.desc st h.toNat c hlt hst $$ Hr
    icases headRes_acc' γ c0.desc st h.toNat (.active c) hlt hst $$ Hr with ⟨He, Hrback⟩
    icases headRes_active_acc γ c0.desc h.toNat c $$ He with ⟨Hcl, Hclb⟩
    iexists c0, c
    isplitl []
    · ipureintro; exact ⟨hreq, hhd, hwf.2, hc0.1, hc0.2.2⟩
    iframe Hcl Hu
    iintro ⟨Hcl2, Hu2⟩
    isplitl []
    · ipureintro; exact hc
    iexists pn, pm
    iframe Hpm
    isplitl []
    · ipureintro; exact hfr
    iright
    iexists c0
    iframe Hfr
    isplitl []
    · ipureintro; exact hc0
    iexists st, nc, np, lo, ring, m, pmap, stg, b, M, dl, dl0
    iframe Hm Ha Hu2 Hav Hnc Hnp Hlo HnpM Hpos Hstg Hui Hdn Hbs
    isplitl [Hcl2 Hclb Hrback]
    · iapply Hrback
      iapply Hclb $$ Hcl2
    · ipureintro; exact ⟨e1, e2, e3, e4, e5, e5b, e6, e7, e8, e9, e10⟩

/-! ### The four DMA writes -/

theorem mod_NUM_lt (n : Nat) : n % NUM < NUM := Nat.mod_lt _ (by unfold NUM; omega)

theorem bufSector_lease (c : Chain) (i : Nat) (pa : PAddr) (n : Nat)
    (hpa : pa = sectorAddr c.data i) (hn : n = Virtio.sectorSize)
    (w : BitVec (8 * n)) (Q : IProp GF) :
    dmaOwn (GF := GF) (sectorAddr c.data i) Virtio.sectorSize ∗
      (dmaOwn (sectorAddr c.data i) Virtio.sectorSize -∗ Q) ⊢ dmaWriteLease pa n w Q := by
  subst hpa; subst hn
  exact dmaOwn_lease_frame _ _ _ _

theorem reqSectorLen_of_chain (c : Chain) (i : Nat) (hn : Virtio.reqSectorLen c.req i ≠ 0) :
    i < SPB ∧ Virtio.reqSectorLen c.req i = Virtio.sectorSize := by
  have hlen : (Chain.req c).len.toNat = BSIZE := by
    show (BitVec.ofNat 32 BSIZE).toNat = BSIZE
    unfold BSIZE
    decide
  simp only [Virtio.reqSectorLen, hlen, SPB_eq, BSIZE_eq, sectorSize_eq] at hn ⊢
  omega

/-- W1: the status byte. -/
theorem status_write_lease (γ : DiskNames) (s : VirtioState) (h : BitVec 16) (r : VioReq)
    (hin : Virtio.reqOf s h = some r) (w : BitVec (8 * 1)) :
    diskProto (GF := GF) γ s ⊢ dmaWriteLease r.status 1 w (diskProto γ s) := by
  iintro H
  icases diskProto_chain_acc γ s h r hin $$ H with ⟨%c0, %c, %hp, Hcl, Hu, Hback⟩
  obtain ⟨hreq, hhd, hwf, hcfg, hq⟩ := hp
  have hst : r.status = c.status := by rw [hreq]; rfl
  rw [hst]
  unfold chainLease
  icases Hcl with ⟨H0, H1, H2, H3, H4, H5, Hstat, Hbuf⟩
  iapply dmaOwn_lease_frame c.status 1 w (diskProto γ s)
  isplitl [Hstat]
  · iexact Hstat
  · iintro Hstat2
    iapply Hback
    isplitl [H0 H1 H2 H3 H4 H5 Hstat2 Hbuf]
    · iframe H0 H1 H2 H3 H4 H5 Hstat2 Hbuf
    · iexact Hu

/-- W4: one sector of the data transfer. -/
theorem data_write_lease (γ : DiskNames) (s : VirtioState) (h : BitVec 16) (r : VioReq)
    (i : Nat) (hin : Virtio.reqOf s h = some r)
    (w : BitVec (8 * Virtio.reqSectorLen r i)) :
    diskProto (GF := GF) γ s ⊢
      dmaWriteLease (Virtio.reqSectorAddr r i) (Virtio.reqSectorLen r i) w (diskProto γ s) := by
  rcases Nat.eq_zero_or_pos (Virtio.reqSectorLen r i) with hz | hz
  · exact dmaWriteLease_zero _ _ hz w _
  iintro H
  icases diskProto_chain_acc γ s h r hin $$ H with ⟨%c0, %c, %hp, Hcl, Hu, Hback⟩
  obtain ⟨hreq, hhd, hwf, hcfg, hq⟩ := hp
  subst hreq
  obtain ⟨hi, hn⟩ := reqSectorLen_of_chain c i (by omega)
  unfold chainLease
  icases Hcl with ⟨H0, H1, H2, H3, H4, H5, Hstat, Hbuf⟩
  icases bufSector_acc c i hi $$ Hbuf with ⟨Hsec, Hsecb⟩
  iapply bufSector_lease c i (Virtio.reqSectorAddr (Chain.req c) i)
    (Virtio.reqSectorLen (Chain.req c) i) rfl hn w (diskProto γ s)
  isplitl [Hsec]
  · iexact Hsec
  · iintro Hsec2
    iapply Hback
    isplitl [H0 H1 H2 H3 H4 H5 Hstat Hsec2 Hsecb]
    · isplitl [H0]
      · iexact H0
      isplitl [H1]
      · iexact H1
      isplitl [H2]
      · iexact H2
      isplitl [H3]
      · iexact H3
      isplitl [H4]
      · iexact H4
      isplitl [H5]
      · iexact H5
      isplitl [Hstat]
      · iexact Hstat
      · iapply Hsecb $$ Hsec2
    · iexact Hu

/-- W2: the used-ring element. -/
theorem usedElem_write_lease (γ : DiskNames) (s : VirtioState) (h : BitVec 16) (r : VioReq)
    (cc : VirtioCfg) (ui : BitVec 16) (hin : Virtio.reqOf s h = some r) (hcc : s.cfg = cc)
    (w : BitVec (8 * 8)) :
    diskProto (GF := GF) γ s ⊢
      dmaWriteLease (Virtio.usedElemAddr cc ui) 8 w (diskProto γ s) := by
  iintro H
  icases diskProto_chain_acc γ s h r hin $$ H with ⟨%c0, %c, %hp, Hcl, Hu, Hback⟩
  obtain ⟨hreq, hhd, hwf, hcfg, hq⟩ := hp
  have hcc0 : cc = c0 := by rw [← hcc, hcfg]
  subst hcc0
  rw [usedElemAt_eq cc ui hq]
  icases usedElem_acc cc.used (ui.toNat % NUM) (mod_NUM_lt ui.toNat) $$ Hu with ⟨He, Heb⟩
  iapply dmaOwn_lease_frame (usedElemAt cc.used (ui.toNat % NUM)) 8 w (diskProto γ s)
  isplitl [He]
  · iexact He
  · iintro He2
    iapply Hback
    isplitl [Hcl]
    · iexact Hcl
    · iapply Heb $$ He2

/-- W3: the used index. -/
theorem diskProto_usedIdx_acc (γ : DiskNames) (s : VirtioState) (h : BitVec 16) (r : VioReq)
    (hin : Virtio.reqOf s h = some r) :
    diskProto (GF := GF) γ s ⊢ ∃ (c0 : VirtioCfg) (b nc : Nat) (dl : List UsedRec),
      ⌜s.cfg = c0 ∧ s.usedIdx = wrap16 nc⌝ ∗ usedIdxCell (usedIdxAt c0.used) b dl ∗
      (∀ t : Nat, usedIdxCell (usedIdxAt c0.used) b (dl ++ [(nc + 1, t)]) -∗ diskProto γ s) := by
  unfold diskProto
  iintro ⟨%hc, %pn, %pm, Hpm, %hfr, Harm⟩
  icases Harm with ⟨Hd | ⟨%c0, #Hfr, %hc0, Hl⟩⟩
  · unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, Hlo0, HnpM0, Hpos0, HstgA0, Hbs0, Hdn0, %hpure⟩
    rw [hpure.2.1 h] at hin
    exact absurd hin (by simp)
  · unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %lo, %ring, %m, %pmap, %stg, %b, %M, %dl, %dl0, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, Hlo, HnpM, Hpos, Hstg, Hui, Hdn, #Hbs, %hpure⟩
    obtain ⟨e1, e2, e3, e4, e5, e5b, e6, e7, e8, e9, e10⟩ := hpure
    iexists c0, b, nc, dl
    isplitl []
    · ipureintro; exact ⟨hc0.1, e1⟩
    iframe Hui
    iintro %t Hui'
    isplitl []
    · ipureintro; exact hc
    iexists pn, pm
    iframe Hpm
    isplitl []
    · ipureintro; exact hfr
    iright
    iexists c0
    iframe Hfr
    isplitl []
    · ipureintro; exact hc0
    iexists st, nc, np, lo, ring, m, pmap, stg, b, M, (dl ++ [(nc + 1, t)]), dl0
    iframe Hm Ha Hr Hu Hav Hnc Hnp Hlo HnpM Hpos Hstg Hui' Hdn Hbs
    ipureintro
    exact ⟨e1, e2, e3, e4, e5, e5b, e6, e7, e8, e9, usedOk_write dl dl0 nc M t e10⟩

/-- W3: the used index.  The write appends its entry -- the counter the
device's `usedIdx` is about to reach, at the position the machine gives the
store -- to the cell's LOG. -/
theorem usedIdx_write_lease (γ : DiskNames) (s : VirtioState) (h : BitVec 16) (r : VioReq)
    (cc : VirtioCfg) (hin : Virtio.reqOf s h = some r) (hcc : s.cfg = cc)
    (w : BitVec (8 * 2)) (hw : w = s.usedIdx + 1#16) :
    diskProto (GF := GF) γ s ⊢ dmaWriteLease (Virtio.usedIdxAddr cc) 2 w (diskProto γ s) := by
  iintro H
  icases diskProto_usedIdx_acc γ s h r hin $$ H with ⟨%c0, %b, %nc, %dl, %hp, Hui, Hback⟩
  obtain ⟨hcfg, hidx⟩ := hp
  have hcc0 : cc = c0 := by rw [← hcc, hcfg]
  subst hcc0
  rw [usedIdxAt_eq cc, show w = wrap16 (nc + 1) by rw [hw, hidx, wrap16_succ]]
  iapply usedIdxCell_lease (usedIdxAt cc.used) b dl (nc + 1)
    iprop(∀ t : Nat, usedIdxCell (usedIdxAt cc.used) b (dl ++ [(nc + 1, t)]) -∗ diskProto γ s)
    (diskProto γ s)
    (fun t => by
      iintro ⟨H1, H2⟩
      iapply H2 $$ %t H1)
  iframe Hui Hback

/-! ## The serve permit

The device-side counterpart of `Xv6.permTok`: how a task takes a permit,
what it pins while it holds one, and how it gives it back. -/

theorem permTok_lookup (γ : DiskNames) (pm : RegMapF PermVal) (k : Nat) (h : BitVec 16)
    (c : Chain) :
    ⊢@{IProp GF} permAuth γ pm -∗ permTok γ k h c -∗
      ⌜PartialMap.get? pm k = some ((h, c) : PermVal)⌝ := by
  unfold permAuth permTok
  iintro H1 H2
  ihave %hg := ghost_map_lookup $$ H1 H2
  ipureintro; exact hg

/-- A free slot's row is EMPTY: the accounting rules out a fetch there. -/
theorem headRes_inactive_eq (γ : DiskNames) (pd : PAddr) (i : Nat) :
    headRes (GF := GF) γ pd i .inactive = iprop(emp) := rfl

/-- **Opening the protocol in the live world.**  A frozen configuration
rules the dead arm out -- the dead arm holds a HALF of the same ghost
variable, which agrees with the frozen value, and the dead arm's state is
not live.  What comes out is the permit authority and the eight
descriptor rows, with the way back, which may put a DIFFERENT permit map
over the same receipts. -/
theorem diskProto_open_live (γ : DiskNames) (c0 : VirtioCfg) (v : VirtioState)
    (hlive : Virtio.live c0 = true) :
    diskCfgFrozen (GF := GF) γ c0 ∗ diskProto γ v ⊢
      ⌜v.cfg = c0 ∧ c0.qnum.toNat = NUM⌝ ∗
      ∃ (pn : Nat) (pm : RegMapF PermVal) (st : Nat → HState),
        ⌜permFresh pn pm ∧ permOk pm st⌝ ∗ permAuth γ pm ∗
        ([∗list] i ∈ List.range NUM, headRes γ c0.desc i (st i)) ∗
        (∀ (pn' : Nat) (pm' : RegMapF PermVal), ⌜permFresh pn' pm' ∧ permOk pm' st⌝ -∗
          permAuth γ pm' -∗ ([∗list] i ∈ List.range NUM, headRes γ c0.desc i (st i)) -∗
          diskProto γ v) := by
  unfold diskProto
  iintro ⟨#Hfr0, %hc, %pn, %pm, Hpm, %hfr, Harm⟩
  icases Harm with ⟨Hd | ⟨%c0', #Hfr, %hc0, Hl⟩⟩
  · unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, Hlo0, HnpM0, Hpos0, HstgA0, Hbs0, Hdn0, %hpure⟩
    ihave %heq := diskCfgFrozen_auth_agree γ c0 v.cfg $$ Hfr0 Hcfg
    rw [heq, hpure.1] at hlive
    exact absurd hlive (by simp)
  · ihave %hcc := diskCfgFrozen_agree γ c0 c0' $$ [$Hfr0 $Hfr]
    subst hcc
    unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %lo, %ring, %m, %pmap, %stg, %b, %M, %dl, %dl0, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, Hlo, HnpM, Hpos, Hstg, Hui, Hdn, #Hbs, %hpure⟩
    obtain ⟨e1, e2, e3, e4, e5, e5b, e6, e7, e8, e9, e10⟩ := hpure
    isplitl []
    · ipureintro; exact ⟨hc0.1, hc0.2.2⟩
    iexists pn, pm, st
    isplitl []
    · ipureintro; exact ⟨hfr, e9⟩
    iframe Hpm Hr
    iintro %pn' %pm' %hpure' Hpm' Hr'
    isplitl []
    · ipureintro; exact hc
    iexists pn', pm'
    iframe Hpm'
    isplitl []
    · ipureintro; exact hpure'.1
    iright
    iexists c0
    iframe Hfr
    isplitl []
    · ipureintro; exact hc0
    iexists st, nc, np, lo, ring, m, pmap, stg, b, M, dl, dl0
    iframe Hm Ha Hr' Hu Hav Hnc Hnp Hlo HnpM Hpos Hstg Hui Hdn Hbs
    ipureintro
    exact ⟨e1, e2, e3, e4, e5, e5b, e6, e7, e8, hpure'.2, e10⟩

/-- **Giving a permit back**: always sound, and what `disk_collect` will
need to have happened for the head it reclaims. -/
theorem perm_drop (γ : DiskNames) (k : Nat) (h : BitVec 16) (c : Chain) (v : VirtioState) :
    permTok (GF := GF) γ k h c ∗ diskProto γ v ⊢ |==> diskProto γ v := by
  unfold diskProto
  iintro ⟨Htok, %hc, %pn, %pm, Hpm, %hfr, Harm⟩
  unfold permAuth permTok
  imod ghost_map_delete (V := PermVal) k ((h, c) : PermVal) $$ Hpm Htok with Hpm
  imodintro
  isplitl []
  · ipureintro; exact hc
  iexists pn, (PartialMap.delete pm k)
  iframe Hpm
  isplitl []
  · ipureintro; exact permFresh_delete pm pn k hfr
  icases Harm with ⟨Hd | ⟨%c0, #Hfr, %hc0, Hl⟩⟩
  · ileft
    unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, Hlo0, HnpM0, Hpos0, HstgA0, Hbs0, Hdn0, %hpure⟩
    obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hpure
    iexists m
    iframe Hm Hcfg Hlo0 HnpM0 Hpos0 HstgA0 Hbs0 Hdn0
    ipureintro
    exact ⟨p1, p2, p3, p4, permOk_delete pm (fun _ => .inactive) k p5, p6, p7⟩
  · iright
    iexists c0
    iframe Hfr
    isplitl []
    · ipureintro; exact hc0
    unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %lo, %ring, %m, %pmap, %stg, %b, %M, %dl, %dl0, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, Hlo, HnpM, Hpos, Hstg, Hui, Hdn, #Hbs, %hpure⟩
    obtain ⟨e1, e2, e3, e4, e5, e5b, e6, e7, e8, e9, e10⟩ := hpure
    iexists st, nc, np, lo, ring, m, pmap, stg, b, M, dl, dl0
    iframe Hm Ha Hr Hu Hav Hnc Hnp Hlo HnpM Hpos Hstg Hui Hdn Hbs
    ipureintro
    exact ⟨e1, e2, e3, e4, e5, e5b, e6, e7, e8, permOk_delete pm st k e9, e10⟩

/-- What a permit says about the head it names: a descriptor of the queue,
armed with the chain the permit records. -/
theorem perm_state (γ : DiskNames) (pm : RegMapF PermVal) (st : Nat → HState) (k : Nat)
    (h : BitVec 16) (c : Chain) (hok : permOk pm st) :
    ⊢@{IProp GF} permAuth γ pm -∗ permTok γ k h c -∗
      ⌜h.toNat < NUM ∧ st h.toNat = .active c⌝ := by
  iintro Hpm Htok
  ihave %hg := permTok_lookup γ pm k h c $$ Hpm Htok
  ipureintro
  exact hok k h c hg

/-- **What a permit pins**: the chain's descriptors and header, at the
addresses the fetch reads them from. -/
theorem perm_chain_acc (γ : DiskNames) (c0 : VirtioCfg) (k : Nat) (h : BitVec 16) (c : Chain)
    (v : VirtioState) (hlive : Virtio.live c0 = true) :
    diskCfgFrozen (GF := GF) γ c0 ∗ permTok γ k h c ∗ diskProto γ v ⊢
      ⌜v.cfg = c0 ∧ c.hd = h.toNat ∧ c.wf ∧ c0.qnum.toNat = NUM⌝ ∗ chainLease c0.desc c ∗
      (chainLease c0.desc c -∗ (permTok γ k h c ∗ diskProto γ v)) := by
  iintro ⟨#Hfr, Htok, H⟩
  icases diskProto_open_live γ c0 v hlive $$ [$Hfr $H] with ⟨%hcfg, %pn, %pm, %st, %hpp, Hpm, Hr, Hback⟩
  ihave %hst := perm_state γ pm st k h c hpp.2 $$ Hpm Htok
  obtain ⟨hlt, hst'⟩ := hst
  ihave %hwf := headRes_wf_of γ c0.desc st h.toNat c hlt hst' $$ Hr
  icases headRes_acc' γ c0.desc st h.toNat (.active c) hlt hst' $$ Hr with ⟨He, Hrb⟩
  icases headRes_active_acc γ c0.desc h.toNat c $$ He with ⟨Hcl, Hclb⟩
  isplitl []
  · ipureintro; exact ⟨hcfg.1, hwf.1, hwf.2, hcfg.2⟩
  iframe Hcl
  iintro Hcl2
  iframe Htok
  iapply Hback $$ %pn %pm %hpp Hpm
  iapply Hrb
  iapply Hclb $$ Hcl2

/-- The chain a permit names, as a pure fact. -/
theorem perm_chain_wf (γ : DiskNames) (c0 : VirtioCfg) (k : Nat) (h : BitVec 16) (c : Chain)
    (v : VirtioState) (hlive : Virtio.live c0 = true) :
    diskCfgFrozen (GF := GF) γ c0 ∗ permTok γ k h c ∗ diskProto γ v ⊢
      ⌜v.cfg = c0 ∧ c.hd = h.toNat ∧ c.wf ∧ c0.qnum.toNat = NUM⌝ ∗
        (permTok γ k h c ∗ diskProto γ v) := by
  iintro ⟨#Hfr, Htok, H⟩
  icases perm_chain_acc γ c0 k h c v hlive $$ [$Hfr $Htok $H] with ⟨%hp, Hcl, Hback⟩
  icases Hback $$ Hcl with ⟨Htok2, H2⟩
  iframe Htok2 H2
  ipureintro; exact hp

/-! ### The install, and the completion -/

/-- Installing the request of the chain armed at `h` keeps the coupling. -/
theorem inflightOk_setPhase_some (v : VirtioState) (st : Nat → HState) (h : BitVec 16)
    (c : Chain) (ph : VPhase) (hph : ph.req = some c.req) (hlt : h.toNat < NUM)
    (hst : st h.toNat = .active c) (hhd : c.hd = h.toNat) (hok : inflightOk v st) :
    inflightOk (Virtio.setPhase v h ph) st := by
  intro kk r hr
  by_cases hk : kk = h
  · subst hk
    rw [reqOf_setPhase_self, hph] at hr
    cases hr
    exact ⟨hlt, c, hst, hhd, rfl⟩
  · exact hok kk r (by rwa [reqOf_setPhase_other v h kk ph hk] at hr)

/-- **The install.**  This is what the port used to assume: a `serve` task
may record the request it parsed, because the permit the POP minted for it
pins the receipt of `h` to the chain whose descriptors it read. -/
theorem perm_install (γ : DiskNames) (c0 : VirtioCfg) (k : Nat) (h : BitVec 16) (c : Chain)
    (v : VirtioState) (ph : VPhase) (hlive : Virtio.live c0 = true) (hph : ph.req = some c.req) :
    diskCfgFrozen (GF := GF) γ c0 ∗ permTok γ k h c ∗ diskProto γ v ⊢
      |==> (diskProto γ (Virtio.setPhase v h ph) ∗ permTok γ k h c) := by
  unfold diskProto
  iintro ⟨#Hfr0, Htok, %hc, %pn, %pm, Hpm, %hfr, Harm⟩
  icases Harm with ⟨Hd | ⟨%c0', #Hfr, %hc0, Hl⟩⟩
  · unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, Hlo0, HnpM0, Hpos0, HstgA0, Hbs0, Hdn0, %hpure⟩
    ihave %heq := diskCfgFrozen_auth_agree γ c0 v.cfg $$ Hfr0 Hcfg
    rw [heq, hpure.1] at hlive
    exact absurd hlive (by simp)
  · ihave %hcc := diskCfgFrozen_agree γ c0 c0' $$ [$Hfr0 $Hfr]
    subst hcc
    unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %lo, %ring, %m, %pmap, %stg, %b, %M, %dl, %dl0, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, Hlo, HnpM, Hpos, Hstg, Hui, Hdn, #Hbs, %hpure⟩
    obtain ⟨e1, e2, e3, e4, e5, e5b, e6, e7, e8, e9, e10⟩ := hpure
    ihave %hst := perm_state γ pm st k h c e9 $$ Hpm Htok
    obtain ⟨hlt, hst'⟩ := hst
    ihave %hwf := headRes_wf_of γ c0.desc st h.toNat c hlt hst' $$ Hr
    imodintro
    iframe Htok
    isplitl []
    · ipureintro; exact hc
    iexists pn, pm
    iframe Hpm
    isplitl []
    · ipureintro; exact hfr
    iright
    iexists c0
    iframe Hfr
    isplitl []
    · ipureintro; exact hc0
    iexists st, nc, np, lo, ring, m, pmap, stg, b, M, dl, dl0
    iframe Hm Ha Hr Hu Hav Hnc Hnp Hlo HnpM Hpos Hstg Hui Hdn Hbs
    ipureintro
    exact ⟨e1, e2, e3, e4, e5, e5b,
      inflightOk_setPhase_some v st h c ph hph hlt hst' hwf.1 e6, e7, e8, e9, e10⟩

/-- **The completion**, with the permit given back. -/
theorem perm_complete (γ : DiskNames) (c0 : VirtioCfg) (k : Nat) (h : BitVec 16) (c : Chain)
    (hh : BitVec 16) (v : VirtioState) (hlive : Virtio.live c0 = true) :
    diskCfgFrozen (GF := GF) γ c0 ∗ permTok γ k h c ∗ diskProto γ v ⊢
      |==> diskProto γ (Virtio.complete v hh) := by
  iintro ⟨#Hfr, Htok, H⟩
  ihave Hd := perm_drop γ k h c v $$ [$Htok $H]
  imod Hd with H
  iapply diskProto_complete γ c0 v hh hlive $$ [$Hfr $H]

/-! ## The task resources -/

/-- **The world is up**: the configuration is frozen at a live `c0`.
Persistent, and what a `serve` task is forked with -- so a task never has
to cope with the dead arm, which is right, because the pop that forks it
is in the live branch of `Virtio.body`. -/
def diskUp (γ : DiskNames) : IProp GF := iprop%
  ∃ c0 : VirtioCfg, diskCfgFrozen γ c0 ∗ ⌜Virtio.live c0 = true ∧ c0.qnum.toNat = NUM⌝

instance diskUp_persistent (γ : DiskNames) : Persistent (diskUp (GF := GF) γ) := by
  unfold diskUp diskCfgFrozen
  infer_instance

/-- What a forked task starts from (`MachCSL.DevSig.LeaseL`'s `Lt`).  A
`serve h` task is forked BY THE POP, which minted its permit: so the task
starts owning the exclusive right to head `h`'s armed chain, and never has
to cope with a free descriptor. -/
def diskTaskRes (γ : DiskNames) : Virtio.VTask → IProp GF
  | .serve h => iprop(diskUp γ ∗ ∃ (k : Nat) (c : Chain), permTok γ k h c)
  | .xferIn _ _ => iprop(True)
  | .xferOut _ _ => iprop(True)

theorem diskTaskRes_serve (γ : DiskNames) (h : BitVec 16) :
    diskTaskRes (GF := GF) γ (.serve h) =
      iprop(diskUp γ ∗ ∃ (k : Nat) (c : Chain), permTok γ k h c) := rfl

theorem diskTaskRes_xferIn (γ : DiskNames) (h : BitVec 16) (i : Nat) :
    ⊢@{IProp GF} diskTaskRes γ (.xferIn h i) := by
  show ⊢@{IProp GF} iprop(True)
  itrivial

theorem diskTaskRes_xferOut (γ : DiskNames) (h : BitVec 16) (i : Nat) :
    ⊢@{IProp GF} diskTaskRes γ (.xferOut h i) := by
  show ⊢@{IProp GF} iprop(True)
  itrivial

/-- Which arm the invariant is in, as a persistent fact. -/
theorem diskDead_notlive (γ : DiskNames) (v : VirtioState) (pm : RegMapF PermVal) :
    diskDead (GF := GF) γ v pm ⊢ ⌜Virtio.live v.cfg = false⌝ := by
  unfold diskDead
  iintro ⟨%m, _, _, _, _, _, _, _, _, %hp⟩
  ipureintro; exact hp.1

theorem diskProto_arm (γ : DiskNames) (s : VirtioState) :
    diskProto (GF := GF) γ s ⊢
      diskProto γ s ∗ (⌜Virtio.live s.cfg = false⌝ ∨ diskUp γ) := by
  unfold diskProto
  iintro ⟨%hc, %pn, %pm, Hpm, %hfr, Harm⟩
  icases Harm with ⟨Hd | ⟨%c0, #Hfr, %hc0, Hl⟩⟩
  · ihave %hdead := diskDead_notlive γ s pm $$ Hd
    isplitl [Hpm Hd]
    · isplitl []
      · ipureintro; exact hc
      iexists pn, pm
      iframe Hpm
      isplitl []
      · ipureintro; exact hfr
      ileft
      iexact Hd
    · ileft; ipureintro; exact hdead
  · isplitl [Hpm Hl]
    · isplitl []
      · ipureintro; exact hc
      iexists pn, pm
      iframe Hpm
      isplitl []
      · ipureintro; exact hfr
      iright
      iexists c0
      iframe Hfr Hl
      ipureintro; exact hc0
    · iright
      unfold diskUp
      iexists c0
      iframe Hfr
      ipureintro; exact ⟨hc0.2.1, hc0.2.2⟩

/-! ## The knowledge a `serve` task carries -/

/-- What the task learns at its first `get`: the frozen configuration, and
the CHAIN its permit names -- the pop minted the permit, so the head is
armed and the task never meets a free descriptor. -/
structure ServeKnow (h : BitVec 16) where
  c0 : VirtioCfg
  key : Nat
  ch : Chain
  hlive : Virtio.live c0 = true
  hqnum : c0.qnum.toNat = NUM
  hhd : ch.hd = h.toNat
  hwf : ch.wf

/-- The `serve` task's linear context. -/
def serveCtx (γ : DiskNames) (h : BitVec 16) (c0 : VirtioCfg) (key : Nat) (c : Chain)
    (s : VirtioState) : IProp GF := iprop%
  diskCfgFrozen γ c0 ∗ ⌜s.cfg = c0⌝ ∗ permTok γ key h c

theorem serveCtx_cfg (γ : DiskNames) (h : BitVec 16) (c0 : VirtioCfg) (key : Nat) (c : Chain)
    (s : VirtioState) : serveCtx (GF := GF) γ h c0 key c s ⊢ ⌜s.cfg = c0⌝ := by
  unfold serveCtx
  iintro ⟨_, %hcfg, _⟩
  ipureintro; exact hcfg

/-! ### Reading one piece of the armed chain -/

theorem chainLease_acc0 (pd : PAddr) (c : Chain) :
    chainLease (GF := GF) pd c ⊢ dmaHalfAt (descAt pd c.hd) 16 c.d0 ∗
      (dmaHalfAt (descAt pd c.hd) 16 c.d0 -∗ chainLease pd c) := by
  unfold chainLease
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  iframe H0
  iintro H0'
  iframe H0' H1 H2 H3 H4 H5 H6 H7

theorem chainLease_acc1 (pd : PAddr) (c : Chain) :
    chainLease (GF := GF) pd c ⊢ dmaHalfAt (descAt pd c.md) 16 c.d1 ∗
      (dmaHalfAt (descAt pd c.md) 16 c.d1 -∗ chainLease pd c) := by
  unfold chainLease
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  iframe H1
  iintro H1'
  iframe H0 H1' H2 H3 H4 H5 H6 H7

theorem chainLease_acc2 (pd : PAddr) (c : Chain) :
    chainLease (GF := GF) pd c ⊢ dmaHalfAt (descAt pd c.tl) 16 c.d2 ∗
      (dmaHalfAt (descAt pd c.tl) 16 c.d2 -∗ chainLease pd c) := by
  unfold chainLease
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  iframe H2
  iintro H2'
  iframe H0 H1 H2' H3 H4 H5 H6 H7

theorem chainLease_accType (pd : PAddr) (c : Chain) :
    chainLease (GF := GF) pd c ⊢ dmaHalfAt c.hdrAddr 4 c.req.type ∗
      (dmaHalfAt c.hdrAddr 4 c.req.type -∗ chainLease pd c) := by
  unfold chainLease
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  iframe H3
  iintro H3'
  iframe H0 H1 H2 H3' H4 H5 H6 H7

theorem chainLease_accSector (pd : PAddr) (c : Chain) :
    chainLease (GF := GF) pd c ⊢ dmaHalfAt (c.hdrAddr + 8#64) 8 c.sector ∗
      (dmaHalfAt (c.hdrAddr + 8#64) 8 c.sector -∗ chainLease pd c) := by
  unfold chainLease
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  iframe H5
  iintro H5'
  iframe H0 H1 H2 H3 H4 H5' H6 H7

/-- **The fetch's reads are pinned.**  Whatever piece of the armed chain
the device reads, the permit says the chain is still `c`, and the
invariant holds a half of those bytes at the value the driver wrote. -/
theorem serve_chain_pin (γ : DiskNames) (h : BitVec 16) (c0 : VirtioCfg) (key : Nat)
    (c : Chain) (s s' : VirtioState) (n : Nat) (pa : PAddr) (w : BitVec (8 * n))
    (hlive : Virtio.live c0 = true)
    (hacc : chainLease (GF := GF) c0.desc c ⊢
      dmaHalfAt pa n w ∗ (dmaHalfAt pa n w -∗ chainLease c0.desc c)) :
    serveCtx (GF := GF) γ h c0 key c s ∗ diskProto γ s' ⊢
      dmaReadPin pa n (fun v => v = w)
        iprop(diskProto γ s' ∗ serveCtx γ h c0 key c s) := by
  unfold serveCtx
  iintro ⟨⟨#Hfr, %hcfg, Htok⟩, HR⟩
  icases perm_chain_acc γ c0 key h c s' hlive $$ [$Hfr $Htok $HR] with ⟨%hp, Hcl, Hback⟩
  icases hacc $$ Hcl with ⟨Hhalf, Hhb⟩
  iapply dmaHalfAt_pin pa n w _ (fun v => v = w) rfl
  iframe Hhalf
  iintro Hhalf2
  ihave Hcl2 := Hhb $$ Hhalf2
  icases Hback $$ Hcl2 with ⟨Htok, HR⟩
  iframe HR Htok Hfr
  ipureintro; exact hcfg

/-! ## The derivation: the small pieces -/

/-- A `get` that learns nothing. -/
theorem leaseL_get_keep (γ : DiskNames) (C : IProp GF) (s : VirtioState) :
    iprop(C ∗ diskProto γ s) ⊢ |==> (diskProto γ s ∗ ∃ _ : Unit, C) := by
  iintro ⟨HC, HR⟩
  imodintro
  iframe HR
  iexists ()
  iexact HC

/-- Framing the task's context through a DMA-write lease. -/
theorem leaseL_write_frame (γ : DiskNames) (s' : VirtioState) (C : IProp GF) (pa : PAddr)
    (n : Nat) (w : BitVec (8 * n))
    (hl : diskProto (GF := GF) γ s' ⊢ dmaWriteLease pa n w (diskProto γ s')) :
    iprop(C ∗ diskProto γ s') ⊢ dmaWriteLease pa n w iprop(diskProto γ s' ∗ C) := by
  iintro ⟨HC, HR⟩
  iapply dmaWriteLease_frame pa n w (diskProto γ s') C
  isplitl [HR]
  · iapply hl $$ HR
  · iexact HC

/-- A stalled request: the guard never answers. -/
theorem leaseL_stall (γ : DiskNames) (C : IProp GF) :
    DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) iprop(True) C Virtio.stall := by
  unfold Virtio.stall DevM.await DevM.step DevM.lift
  exact DevM.LeaseL.step C C _ _ (fun s s' os hgs => by simp at hgs) (DevM.LeaseL.pure _ () true_intro)

/-- `Virtio.xferIn h i`: one sector of a read request's fill. -/
theorem leaseL_xferIn (γ : DiskNames) (C : IProp GF) (h : BitVec 16) (i : Nat) :
    DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) iprop(True) C (Virtio.xferIn h i) := by
  unfold Virtio.xferIn
  simp only [bind, DevM.bind, DevM.get, DevM.lift, Pure.pure]
  refine DevM.LeaseL.get C (X := Unit) (fun _ _ => C) _ (fun s => leaseL_get_keep γ C s)
    (fun s _ => ?_)
  cases hr : Virtio.reqOf s h with
  | none => exact DevM.LeaseL.pure _ () true_intro
  | some r =>
    unfold Virtio.reqSectorLen DevM.dmaWriteIf DevM.lift
    refine DevM.LeaseL.dmaWrite _ _ _ _ _ _ ?_ (DevM.LeaseL.pure _ () true_intro)
    intro s' hg
    exact leaseL_write_frame γ s' C _ _ _ (data_write_lease γ s' h r i (of_decide_eq_true hg) _)

/-- `Virtio.xferOut h i`: one sector of a write request's capture. -/
theorem leaseL_xferOut (γ : DiskNames) (C : IProp GF) (h : BitVec 16) (i : Nat) :
    DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) iprop(True) C (Virtio.xferOut h i) := by
  unfold Virtio.xferOut
  simp only [bind, DevM.bind, DevM.get, DevM.lift, Pure.pure]
  refine DevM.LeaseL.get C (X := Unit) (fun _ _ => C) _ (fun s => leaseL_get_keep γ C s)
    (fun s _ => ?_)
  cases hr : Virtio.reqOf s h with
  | none => exact DevM.LeaseL.pure _ () true_intro
  | some r =>
    unfold DevM.dmaRead DevM.lift
    refine DevM.LeaseL.dmaRead _ _ _ (fun _ _ => True) _ ?_ (fun w _ => ?_)
    · intro s'
      iintro ⟨HC, HR⟩
      iapply dmaReadPin_any
      iframe HR HC
    · unfold DevM.modify DevM.step DevM.lift
      refine DevM.LeaseL.step _ C _ _ ?_ (DevM.LeaseL.pure _ () true_intro)
      intro s1 s2 os hgs
      have hs2 : s2 = (if Virtio.reqOf s1 h = some r then
          { s1 with cache := Virtio.alistSet s1.cache (Virtio.reqKey r i) (bytesOf w) }
          else s1) := by
        simp only [Option.some.injEq, Prod.mk.injEq] at hgs
        exact hgs.1.symm
      subst hs2
      by_cases hc : Virtio.reqOf s1 h = some r
      · rw [if_pos hc]
        iintro ⟨HC, HR⟩
        imodintro
        iframe HC
        iapply diskProto_capture γ s1 h r i (bytesOf w) hc (by simp [bytesOf]) $$ HR
      · rw [if_neg hc]
        iintro ⟨HC, HR⟩
        imodintro
        iframe HC
        iexact HR

/-! ### Forking the data phase -/

theorem leaseL_bind_join (γ : DiskNames) (C : IProp GF) (l : List TaskId)
    (k : Unit → Virtio.VM Unit)
    (hk : DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) iprop(True) C (k ())) :
    DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) iprop(True) C
      (DevM.bind (List.forM l DevM.join) k) := by
  induction l with
  | nil => exact hk
  | cons t l ih =>
    exact DevM.LeaseL.op C _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
      (fun _ => nofun) (fun _ => nofun) (fun _ _ _ => nofun) (fun _ => ih)

theorem leaseL_bind_fork (γ : DiskNames) (C : IProp GF) (ts : List Virtio.VTask)
    (k : List TaskId → Virtio.VM Unit)
    (hk : ∀ l, DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) iprop(True) C (k l)) :
    (∀ t ∈ ts, (⊢@{IProp GF} diskTaskRes γ t)) → ∀ acc : List TaskId,
      DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) iprop(True) C
        (DevM.bind (List.mapM.loop DevM.fork ts acc) k) := by
  induction ts with
  | nil => intro _ acc; exact hk _
  | cons t ts ih =>
    intro hts acc
    refine DevM.LeaseL.fork C C t _ ?_
      (fun r => ih (fun t' ht' => hts t' (List.mem_cons_of_mem _ ht')) (r :: acc))
    iintro HC
    isplitr []
    · iexact HC
    · iapply hts t (List.mem_cons_self ..)

theorem leaseL_forkJoinAll (γ : DiskNames) (C : IProp GF) (ts : List Virtio.VTask)
    (hts : ∀ t ∈ ts, (⊢@{IProp GF} diskTaskRes γ t)) (k : Unit → Virtio.VM Unit)
    (hk : DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) iprop(True) C (k ())) :
    DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) iprop(True) C
      (DevM.bind (DevM.forkJoinAll ts) k) := by
  show DevM.LeaseL _ _ _ C
    (DevM.bind (DevM.bind (List.mapM.loop DevM.fork ts []) (fun l => List.forM l DevM.join)) k)
  rw [DevM_bind_assoc]
  exact leaseL_bind_fork γ C ts _ (fun l => leaseL_bind_join γ C l _ hk) hts []

/-! ### The tail of a request -/

/-- Installing a phase that carries the request of the armed chain. -/
theorem leaseL_install (γ : DiskNames) (h : BitVec 16) (c0 : VirtioCfg) (key : Nat) (c : Chain)
    (s s1 : VirtioState) (ph : VPhase) (hlive : Virtio.live c0 = true)
    (hph : ph.req = some c.req) :
    iprop(serveCtx (GF := GF) γ h c0 key c s ∗ diskProto γ s1) ⊢
      |==> (diskProto γ (Virtio.setPhase s1 h ph) ∗ serveCtx γ h c0 key c s) := by
  unfold serveCtx
  iintro ⟨⟨#Hfr, %hcfg, Htok⟩, HR⟩
  imod perm_install γ c0 key h c s1 ph hlive hph $$ [$Hfr $Htok $HR] with ⟨HR, Htok⟩
  imodintro
  iframe HR Htok Hfr
  ipureintro; exact hcfg

theorem leaseL_serveTail (γ : DiskNames) (h : BitVec 16) (c0 : VirtioCfg) (key : Nat)
    (c : Chain) (s : VirtioState) (hlive : Virtio.live c0 = true) :
    DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) iprop(True)
      (serveCtx γ h c0 key c s) (serveTail h c.req) := by
  unfold serveTail
  simp only [bind, DevM.bind, DevM.modify, DevM.guard, DevM.step, DevM.lift,
    DevM.dmaWriteIf, DevM.get, Pure.pure]
  refine DevM.LeaseL.step _ (serveCtx γ h c0 key c s) _ _ ?_ ?_
  · intro s1 s2 os hgs
    have hs2 : s2 = Virtio.setPhase s1 h (.served c.req) := by
      simp only [Option.some.injEq, Prod.mk.injEq] at hgs
      exact hgs.1.symm
    subst hs2
    exact leaseL_install γ h c0 key c s s1 (.served c.req) hlive rfl
  · refine DevM.LeaseL.dmaWrite _ _ _ _ _ _ ?_ ?_
    · intro s1 hgg
      exact leaseL_write_frame γ s1 _ _ _ _
        (status_write_lease γ s1 h c.req (of_decide_eq_true hgg) _)
    · refine DevM.LeaseL.step _ (serveCtx γ h c0 key c s) _ _ ?_ ?_
      · intro s1 s2 os hgs
        have hs2 : s2 = Virtio.setPhase s1 h (.status c.req) := by
          simp only [Option.some.injEq, Prod.mk.injEq] at hgs
          exact hgs.1.symm
        subst hs2
        exact leaseL_install γ h c0 key c s s1 (.status c.req) hlive rfl
      · refine DevM.LeaseL.step _ (serveCtx γ h c0 key c s) _ _ ?_ ?_
        · intro s1 s2 os hgs
          have hgs' := guard_step_inv _ s2 os hgs
          replace hgs' : (if ((Virtio.phase s1 h).isSome && Virtio.completeOk s1 c.req h &&
              Virtio.pushOk s1) = true then some (Virtio.setPhase s1 h (.pushed c.req))
              else none) = some s2 := hgs'
          split at hgs'
          · have hs2 : s2 = Virtio.setPhase s1 h (.pushed c.req) := by
              simp only [Option.some.injEq] at hgs'; exact hgs'.symm
            subst hs2
            exact leaseL_install γ h c0 key c s s1 (.pushed c.req) hlive rfl
          · exact absurd hgs' (by simp)
        · refine DevM.LeaseL.get _ (X := Unit)
            (fun _ _ => serveCtx γ h c0 key c s) _
            (fun s1 => leaseL_get_keep γ _ s1) (fun v2 _ => ?_)
          refine DevM.LeaseL.dmaWrite _ _ _ _ _ _ ?_ ?_
          · intro s1 hgg
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hgg
            exact leaseL_write_frame γ s1 _ _ _ _
              (usedElem_write_lease γ s1 h c.req v2.cfg v2.usedIdx hgg.1.1 hgg.2 _)
          · refine DevM.LeaseL.dmaWrite _ _ _ _ _ _ ?_ ?_
            · intro s1 hgg
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hgg
              exact leaseL_write_frame γ s1 _ _ _ _
                (usedIdx_write_lease γ s1 h c.req v2.cfg hgg.1.1 hgg.2 _
                  (by rw [hgg.1.2]))
            · refine DevM.LeaseL.step _ iprop(True) _ _ ?_ (DevM.LeaseL.pure _ () true_intro)
              intro s1 s2 os hgs
              have hs2 : s2 = Virtio.complete s1 h := by
                simp only [Option.some.injEq, Prod.mk.injEq] at hgs
                exact hgs.1.symm
              subst hs2
              unfold serveCtx
              iintro ⟨⟨#Hfr, %hcfg, Htok⟩, HR⟩
              imod perm_complete γ c0 key h c h s1 hlive $$ [$Hfr $Htok $HR] with HR
              imodintro
              iframe HR

/-! ### The fetch -/

theorem descOf_zero_noNext :
    (Virtio.descOf (0 : BitVec (8 * 16))).has Virtio.descFNext = false := by
  simp [Virtio.descOf, Virtio.VqDesc.has, Virtio.descFNext]

theorem chain_d0_addr (c : Chain) : (Virtio.descOf c.d0).addr = c.hdrAddr := by rw [chain_d0]

/-- **The fetch at an ARMED head parses that head's chain.**  Each of the
five reads is pinned by the permit to the bytes the driver wrote, so the
request the device assembles is `c.req` -- which is what makes the install
that follows legal. -/
theorem leaseL_fetch_armed (γ : DiskNames) (h : BitVec 16) (c0 : VirtioCfg) (key : Nat)
    (c : Chain) (s : VirtioState) (hlive : Virtio.live c0 = true) (hqnum : c0.qnum.toNat = NUM)
    (hhd : c.hd = h.toNat) (hwf : c.wf)
    (kf : Option VioReq → Virtio.VM Unit)
    (hkn : DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) iprop(True)
      (serveCtx γ h c0 key c s) (kf none))
    (hks : DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) iprop(True)
      (serveCtx γ h c0 key c s) (kf (some c.req))) :
    DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) iprop(True)
      (serveCtx γ h c0 key c s) (DevM.bind (Virtio.fetch s.cfg h) kf) := by
  unfold Virtio.fetch DevM.dmaRead DevM.lift
  simp only [bind, DevM.bind, Pure.pure]
  split
  · exact hkn
  · refine DevM.LeaseL.dmaRead _ _ 16 (fun _ w => w = c.d0) _ ?_ (fun w0 hw0 => ?_)
    · intro s'
      iintro ⟨Hctx, HR⟩
      ihave %hcfg := serveCtx_cfg γ h c0 key c s $$ Hctx
      rw [hcfg, descAt_eq, ← hhd]
      iapply serve_chain_pin γ h c0 key c s s' 16 _ c.d0 hlive (chainLease_acc0 c0.desc c)
      iframe Hctx HR
    · obtain ⟨_, rfl⟩ := hw0
      simp only [bind, DevM.bind, Pure.pure]
      split
      · exact hkn
      · refine DevM.LeaseL.dmaRead _ _ 16 (fun _ w => w = c.d1) _ ?_ (fun w1 hw1 => ?_)
        · intro s'
          iintro ⟨Hctx, HR⟩
          ihave %hcfg := serveCtx_cfg γ h c0 key c s $$ Hctx
          rw [hcfg, descAt_eq, chain_d0_nextIdx c hwf.2.1]
          iapply serve_chain_pin γ h c0 key c s s' 16 _ c.d1 hlive (chainLease_acc1 c0.desc c)
          iframe Hctx HR
        · obtain ⟨_, rfl⟩ := hw1
          simp only [bind, DevM.bind, Pure.pure]
          split
          · exact hkn
          · refine DevM.LeaseL.dmaRead _ _ 16 (fun _ w => w = c.d2) _ ?_ (fun w2 hw2 => ?_)
            · intro s'
              iintro ⟨Hctx, HR⟩
              ihave %hcfg := serveCtx_cfg γ h c0 key c s $$ Hctx
              rw [hcfg, descAt_eq, chain_d1_nextIdx c hwf.2.2.1]
              iapply serve_chain_pin γ h c0 key c s s' 16 _ c.d2 hlive (chainLease_acc2 c0.desc c)
              iframe Hctx HR
            · obtain ⟨_, rfl⟩ := hw2
              simp only [bind, DevM.bind, Pure.pure]
              split
              · exact hkn
              · refine DevM.LeaseL.dmaRead _ _ 4 (fun _ w => w = c.req.type) _ ?_
                  (fun ty hty => ?_)
                · intro s'
                  iintro ⟨Hctx, HR⟩
                  rw [chain_d0_addr]
                  iapply serve_chain_pin γ h c0 key c s s' 4 _ c.req.type hlive
                    (chainLease_accType c0.desc c)
                  iframe Hctx HR
                · obtain ⟨_, rfl⟩ := hty
                  simp only [bind, DevM.bind, Pure.pure]
                  refine DevM.LeaseL.dmaRead _ _ 8 (fun _ w => w = c.sector) _ ?_
                    (fun sec hsec => ?_)
                  · intro s'
                    iintro ⟨Hctx, HR⟩
                    rw [chain_d0_addr]
                    iapply serve_chain_pin γ h c0 key c s s' 8 _ c.sector hlive
                      (chainLease_accSector c0.desc c)
                    iframe Hctx HR
                  · obtain ⟨_, rfl⟩ := hsec
                    have hhead : BitVec.ofNat 16 c.hd = h := by rw [hhd]; simp
                    have hrec : (⟨h, c.req.type, c.sector, (Virtio.descOf c.d1).addr,
                        (Virtio.descOf c.d1).len, (Virtio.descOf c.d2).addr,
                        (Virtio.descOf c.d1).has Virtio.descFWrite⟩ : VioReq) = c.req := by
                      rw [chain_d1_wr, chain_d1, chain_d2, ← hhead]
                      rfl
                    rw [hrec]
                    exact hks

/-! ## `Virtio.serve`: the whole service of one popped request -/

theorem leaseL_serve (γ : DiskNames) (h : BitVec 16) :
    DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) iprop(True) (diskTaskRes γ (.serve h))
      (Virtio.serve h) := by
  rw [diskTaskRes_serve]
  unfold Virtio.serve
  simp only [bind, DevM.bind, DevM.get, DevM.lift]
  refine DevM.LeaseL.get _ (X := ServeKnow h)
    (fun s x => serveCtx γ h x.c0 x.key x.ch s) _ (fun s => ?_) (fun s x => ?_)
  · unfold diskUp
    iintro ⟨⟨#Hup, %kk, %cc, Htok⟩, HR⟩
    icases Hup with ⟨%c0, #Hfr, %hl⟩
    icases perm_chain_wf γ c0 kk h cc s hl.1 $$ [$Hfr $Htok $HR] with ⟨%hp, Htok, HR⟩
    imodintro
    iframe HR
    iexists (⟨c0, kk, cc, hl.1, hl.2, hp.2.1, hp.2.2.1⟩ : ServeKnow h)
    unfold serveCtx
    iframe Hfr Htok
    ipureintro; exact hp.1
  · obtain ⟨xc0, xkey, c, xhlive, xhqnum, xhhd, xhwf⟩ := x
    refine leaseL_fetch_armed γ h xc0 xkey c s xhlive xhqnum xhhd xhwf _
      (leaseL_stall γ _) ?_
    simp only [bind, DevM.bind, DevM.modify, DevM.step, DevM.lift, Pure.pure]
    refine DevM.LeaseL.step _ (serveCtx γ h xc0 xkey c s) _ _ ?_ ?_
    · intro s1 s2 os hgs
      have hs2 : s2 = Virtio.setPhase s1 h (.fetched c.req) := by
        simp only [Option.some.injEq, Prod.mk.injEq] at hgs
        exact hgs.1.symm
      subst hs2
      exact leaseL_install γ h xc0 xkey c s s1 (.fetched c.req) xhlive rfl
    · split
      · refine DevM.LeaseL.step _ (serveCtx γ h xc0 xkey c s) _ _ ?_ ?_
        · intro s1 s2 os hgs
          have hgs' := guard_step_inv _ s2 os hgs
          replace hgs' : (if s1.taken = none then some { s1 with taken := some h }
              else none) = some s2 := hgs'
          split at hgs'
          · have hs2 : s2 = { s1 with taken := some h } := by
              simp only [Option.some.injEq] at hgs'; exact hgs'.symm
            subst hs2
            iintro ⟨HC, HR⟩
            imodintro
            iframe HC
            iapply diskProto_latch γ s1 (some h) $$ HR
          · exact absurd hgs' (by simp)
        · refine leaseL_forkJoinAll γ _ _ (fun t ht => ?_) _
            (leaseL_serveTail γ h xc0 xkey c s xhlive)
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 ht
          exact diskTaskRes_xferOut γ h i
      · split
        · refine leaseL_forkJoinAll γ _ _ (fun t ht => ?_) _
            (leaseL_serveTail γ h xc0 xkey c s xhlive)
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 ht
          exact diskTaskRes_xferIn γ h i
        · exact leaseL_serveTail γ h xc0 xkey c s xhlive

/-! ## `Virtio.body`: the root loop

The root task holds ONE exclusive resource across every iteration
(`MachCSL.DevSig.LeaseV`'s `Cr`): `diskRoot γ`, the other half of the pop
counter.  Nothing but a step of the root itself can move `v.seen`, so the
value `lo` the loop reads at its first `get` is still the invariant's at
the pop several steps later -- which is what the pop's accounting needs
and what no persistent knowledge could say. -/

/-- The pop counter, as the root's half sees it. -/
theorem diskProto_seen (γ : DiskNames) (s : VirtioState) (n : Nat) :
    ⊢@{IProp GF} diskLoTok γ n -∗ diskProto γ s -∗ ⌜s.seen = wrap16 n⌝ := by
  unfold diskProto
  iintro Hlot HP
  icases HP with ⟨%hc, %pn, %pm, Hpm, %hfr, Harm⟩
  icases Harm with ⟨Hd | ⟨%c0, #Hfr, %hc0, Hl⟩⟩
  · unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, Hlo0, HnpM0, Hpos0, HstgA0, Hbs0, Hdn0, %hp⟩
    ihave %hn := diskLo_agree γ 0 n $$ Hlo0 Hlot
    ipureintro
    rw [hp.2.2.2.2.2.2, ← hn]
    rfl
  · unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %lo, %ring, %m, %pmap, %stg, %b, %M, %dl, %dl0, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, Hlo, HnpM, Hpos, Hstg, Hui, Hdn, #Hbs, %hpure⟩
    ihave %hn := diskLo_agree γ lo n $$ Hlo Hlot
    ipureintro
    rw [← hn]
    exact hpure.2.1

/-- **The frozen configuration, from the arm fact.** -/
theorem diskUp_cfg (γ : DiskNames) (s : VirtioState) (c0 : VirtioCfg)
    (hlive : Virtio.live c0 = true) :
    ⊢@{IProp GF} diskCfgFrozen γ c0 -∗ diskProto γ s -∗ ⌜s.cfg = c0 ∧ c0.qnum.toNat = NUM⌝ := by
  iintro #Hfr HR
  icases diskProto_open_live γ c0 s hlive $$ [$Hfr $HR] with ⟨%hcfg, _⟩
  ipureintro; exact hcfg

/-- What the root's first `get` learns: the value of the pop counter (its
own half agrees with the invariant's), and -- once the loop has seen the
device live -- the frozen configuration, so every queue address the
iteration computes is `c0`'s. -/
def bodyKnow (γ : DiskNames) (s : VirtioState) (lo : Nat) (c0 : VirtioCfg) : IProp GF := iprop%
  diskLoTok γ lo ∗ ⌜s.seen = wrap16 lo⌝ ∗
    (⌜Virtio.live s.cfg = false⌝ ∨
      (diskCfgFrozen γ c0 ∗ ⌜s.cfg = c0 ∧ Virtio.live c0 = true ∧ c0.qnum.toNat = NUM⌝))

theorem bodyKnow_root (γ : DiskNames) (s : VirtioState) (lo : Nat) (c0 : VirtioCfg) :
    bodyKnow (GF := GF) γ s lo c0 ⊢ diskRoot γ := by
  unfold bodyKnow
  iintro ⟨Hlot, _, _⟩
  iapply diskLoTok_root γ lo $$ Hlot

/-- In the live branch the disjunction collapses. -/
theorem bodyKnow_live (γ : DiskNames) (s : VirtioState) (lo : Nat) (c0 : VirtioCfg)
    (hlive : Virtio.live s.cfg = true) :
    bodyKnow (GF := GF) γ s lo c0 ⊢
      diskLoTok γ lo ∗ diskCfgFrozen γ c0 ∗
        ⌜s.seen = wrap16 lo ∧ s.cfg = c0 ∧ Virtio.live c0 = true ∧ c0.qnum.toNat = NUM⌝ := by
  unfold bodyKnow
  iintro ⟨Hlot, %hsn, Hor⟩
  icases Hor with ⟨%hf | ⟨#Hfr, %hp⟩⟩
  · rw [hlive] at hf; exact absurd hf (by simp)
  · iframe Hlot Hfr
    ipureintro; exact ⟨hsn, hp⟩

theorem bodyKnow_seen (γ : DiskNames) (s : VirtioState) (lo : Nat) (c0 : VirtioCfg) :
    bodyKnow (GF := GF) γ s lo c0 ⊢ ⌜s.seen = wrap16 lo⌝ := by
  unfold bodyKnow
  iintro ⟨_, %hsn, _⟩
  ipureintro; exact hsn

theorem leaseV_root_get (γ : DiskNames) (s : VirtioState) :
    iprop(diskRoot (GF := GF) γ ∗ diskProto γ s) ⊢
      |==> (diskProto γ s ∗ ∃ x : Nat × VirtioCfg, bodyKnow γ s x.1 x.2) := by
  unfold diskRoot bodyKnow
  iintro ⟨⟨%n, Hlot⟩, HR⟩
  ihave %hseen := diskProto_seen γ s n $$ Hlot HR
  icases diskProto_arm γ s $$ HR with ⟨HR, #Harm⟩
  icases Harm with ⟨%hdead | #Hup⟩
  · imodintro
    iframe HR
    iexists ((n, Virtio.cfg0) : Nat × VirtioCfg)
    iframe Hlot
    isplitl []
    · ipureintro; exact hseen
    ileft
    ipureintro; exact hdead
  · unfold diskUp
    icases Hup with ⟨%c0, #Hfr, %hl⟩
    ihave %hcfg := diskUp_cfg γ s c0 hl.1 $$ Hfr HR
    imodintro
    iframe HR
    iexists ((n, c0) : Nat × VirtioCfg)
    iframe Hlot
    isplitl []
    · ipureintro; exact hseen
    iright
    iframe Hfr
    ipureintro; exact ⟨hcfg.1, hl.1, hl.2⟩

/-- A `get` of the root loop that only keeps what it already has. -/
theorem leaseV_get_keep (γ : DiskNames) (C : IProp GF) (s : VirtioState) :
    iprop(C ∗ diskProto (GF := GF) γ s) ⊢ |==> (diskProto γ s ∗ ∃ _ : Unit, C) := by
  iintro ⟨HC, HR⟩
  imodintro
  iframe HR
  iexists ()
  iexact HC

theorem leaseV_dmaReadPin_any (γ : DiskNames) (C : IProp GF) (s : VirtioState)
    (pa : PAddr) (n : Nat) :
    iprop(C ∗ diskProto (GF := GF) γ s) ⊢
      dmaReadPin pa n (fun _ => True) iprop(diskProto γ s ∗ C) := by
  iintro ⟨HC, HR⟩
  iapply dmaReadPin_any
  iframe HR HC

/-! ### The two reads of the pop, and what they leave behind -/

/-- A leased half over the whole footprint answers a VALUE-INDEXED pin. -/
theorem dmaHalfAt_pinV (pa : PAddr) (n : Nat) (w : BitVec (8 * n))
    (P : BitVec (8 * n) → IProp GF) (Q : BitVec (8 * n) → Prop) (hQ : Q w) :
    dmaHalfAt pa n w ∗ (dmaHalfAt pa n w -∗ P w) ⊢ dmaReadPinV pa n Q P := by
  unfold dmaReadPinV dmaHalfAt
  iintro ⟨⟨%Hs, Hb, %hh⟩, Hback⟩
  iexists (fun _ => DFrac.own (1 : Qp).half), Hs, w
  iframe Hb
  isplit
  · ipureintro; exact hh
  isplit
  · ipureintro; exact hQ
  iintro Hb2
  iapply Hback
  iexists Hs
  iframe Hb2
  ipureintro; exact hh

/-- **What the `avail->idx` read leaves behind.**  Either the index is
still `wrap16 lo` -- the queue is empty and the loop does nothing -- or
position `lo` HAS been published, which two PERSISTENT facts record: `np`
is past `lo` for ever after (`np` is monotone), and position `lo`'s head
is `i` for ever after (a published position is never republished). -/
def availAnswer (γ : DiskNames) (lo : Nat) (w : BitVec (8 * 2)) : IProp GF := iprop%
  ⌜w.extractLsb' 0 16 = wrap16 lo⌝ ∨
    (∃ i : Nat, ⌜i < NUM⌝ ∗ diskPubLb γ (lo + 1) ∗ posRec γ lo i)

/-- ... and what the RING-CELL read leaves behind: the head itself. -/
def ringAnswer (γ : DiskNames) (lo : Nat) (w : BitVec (8 * 2)) : IProp GF := iprop%
  ∃ i : Nat, ⌜i < NUM ∧ w.extractLsb' 0 16 = BitVec.ofNat 16 i⌝ ∗
    diskPubLb γ (lo + 1) ∗ posRec γ lo i

theorem extract16_self (w : BitVec 16) : w.extractLsb' 0 16 = w := by simp

theorem toNat_ofNat16 (i : Nat) (h : i < NUM) : (BitVec.ofNat 16 i).toNat = i := by
  simp only [BitVec.toNat_ofNat]
  unfold NUM at h
  omega

theorem bodyKnow_mk (γ : DiskNames) (v : VirtioState) (lo : Nat) (c0 : VirtioCfg)
    (hsn : v.seen = wrap16 lo) (hcfg : v.cfg = c0) (hlive : Virtio.live c0 = true)
    (hqnum : c0.qnum.toNat = NUM) :
    ⊢@{IProp GF} diskCfgFrozen γ c0 -∗ diskLoTok γ lo -∗ bodyKnow γ v lo c0 := by
  unfold bodyKnow
  iintro #Hfr Hlot
  iframe Hlot
  isplitl []
  · ipureintro; exact hsn
  iright
  iframe Hfr
  ipureintro; exact ⟨hcfg, hlive, hqnum⟩

/-- **The queue page, borrowed out of the live arm**: the avail-ring lease
beside the counters and the accounting that ties them together. -/
theorem diskProto_open_queue (γ : DiskNames) (c0 : VirtioCfg) (s : VirtioState)
    (hlive : Virtio.live c0 = true) :
    diskCfgFrozen (GF := GF) γ c0 ∗ diskProto γ s ⊢
      ∃ (np lo : Nat) (ring : Nat → Nat) (st : Nat → HState) (pmap : List Nat),
        ⌜s.cfg = c0 ∧ c0.qnum.toNat = NUM ∧ s.seen = wrap16 lo ∧ lo ≤ np ∧
          queueOk st ring lo np ∧ posOk pmap ring lo np⌝ ∗
        diskLoAuth γ lo ∗ diskPubAuthM γ np ∗ posAuth γ pmap ∗ availLease c0.avail np ring ∗
        (diskLoAuth γ lo -∗ diskPubAuthM γ np -∗ posAuth γ pmap -∗
          availLease c0.avail np ring -∗ diskProto γ s) := by
  unfold diskProto
  iintro ⟨#Hfr0, %hc, %pn, %pm, Hpm, %hfr, Harm⟩
  icases Harm with ⟨Hd | ⟨%c0', #Hfr, %hc0, Hl⟩⟩
  · unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, Hlo0, HnpM0, Hpos0, HstgA0, Hbs0, Hdn0, %hpd⟩
    ihave %heq := diskCfgFrozen_auth_agree γ c0 s.cfg $$ Hfr0 Hcfg
    rw [heq, hpd.1] at hlive
    exact absurd hlive (by simp)
  · ihave %hcc := diskCfgFrozen_agree γ c0 c0' $$ [$Hfr0 $Hfr]
    subst hcc
    unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %lo, %ring, %m, %pmap, %stg, %b, %M, %dl, %dl0, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, Hlo, HnpM, Hpos, Hstg, Hui, Hdn, #Hbs, %hpure⟩
    obtain ⟨e1, e2, e3, e4, e5, e5b, e6, e7, e8, e9, e10⟩ := hpure
    iexists np, lo, ring, st, pmap
    isplitl []
    · ipureintro; exact ⟨hc0.1, hc0.2.2, e2, e3, e4, e5⟩
    iframe Hlo HnpM Hpos Hav
    iintro Hlo' HnpM' Hpos' Hav'
    isplitl []
    · ipureintro; exact hc
    iexists pn, pm
    iframe Hpm
    isplitl []
    · ipureintro; exact hfr
    iright
    iexists c0
    iframe Hfr
    isplitl []
    · ipureintro; exact hc0
    iexists st, nc, np, lo, ring, m, pmap, stg, b, M, dl, dl0
    iframe Hm Ha Hr Hu Hav' Hnc Hnp Hlo' HnpM' Hpos' Hstg Hui Hdn Hbs
    ipureintro; exact ⟨e1, e2, e3, e4, e5, e5b, e6, e7, e8, e9, e10⟩

/-- **The `avail->idx` pin.**  The invariant's half of the cell pins it to
`wrap16 np`; what the read leaves in the loop's context is the ANSWER: if
`np = lo` the queue is empty, and otherwise two PERSISTENT facts that
still hold at the pop -- `np` is past `lo`, and position `lo`'s head is
`i`. -/
theorem leaseV_avail_pin (γ : DiskNames) (c0 : VirtioCfg) (lo : Nat) (v s' : VirtioState)
    (hlv : Virtio.live v.cfg = true) :
    iprop(bodyKnow (GF := GF) γ v lo c0 ∗ diskProto γ s') ⊢
      dmaReadPinV (Virtio.availIdxAddr v.cfg) 2 (fun _ => True)
        (fun w => iprop(diskProto γ s' ∗ (bodyKnow γ v lo c0 ∗ availAnswer γ lo w))) := by
  iintro ⟨HC, HR⟩
  icases bodyKnow_live γ v lo c0 hlv $$ HC with ⟨Hlot, #Hfr0, %hp⟩
  obtain ⟨hsn, hcfg, hlive, hqnum⟩ := hp
  icases diskProto_open_queue γ c0 s' hlive $$ [$Hfr0 $HR]
    with ⟨%np, %lo', %ring, %st, %pmap, %hq, Hlo, HnpM, Hpos, Hav, Hback⟩
  ihave %hll := diskLo_agree γ lo' lo $$ Hlo Hlot
  subst lo'
  icases availLease_idx c0.avail np ring $$ Hav with ⟨Hidx, Havb⟩
  rw [hcfg, availIdxAt_eq c0]
  iapply dmaHalfAt_pinV (availIdxAt c0.avail) 2 (wrap16 np)
    (fun w => iprop(diskProto γ s' ∗ (bodyKnow γ v lo c0 ∗ availAnswer γ lo w)))
    (fun _ => True) trivial
  iframe Hidx
  iintro Hidx2
  ihave Hav2 := Havb $$ Hidx2
  ihave Hans : iprop(diskPubAuthM γ np ∗ posAuth γ pmap ∗ availAnswer γ lo (wrap16 np))
      $$ [HnpM Hpos]
  · unfold availAnswer
    by_cases hnp : np = lo
    · iframe HnpM Hpos
      ileft
      ipureintro
      rw [hnp, extract16_self]
    · have hlt : lo + 1 ≤ np := by omega
      obtain ⟨hlti, _⟩ := queueOk_head st ring lo np hq.2.2.2.2.1 (by omega)
      icases diskPubAuthM_lb γ np (lo + 1) hlt $$ HnpM with ⟨HnpM, #Hlb⟩
      icases posRec_get γ pmap lo (ring (lo % NUM))
          (hq.2.2.2.2.2.2 lo (Nat.le_refl lo) (by omega)) $$ Hpos with ⟨Hpos, #Hrec⟩
      iframe HnpM Hpos
      iright
      iexists (ring (lo % NUM))
      isplitl []
      · ipureintro; exact hlti
      iframe Hlb Hrec
  icases Hans with ⟨HnpM, Hpos, Hans⟩
  isplitl [Hback Hlo HnpM Hpos Hav2]
  · iapply Hback $$ Hlo HnpM Hpos Hav2
  · iframe Hans
    iapply bodyKnow_mk γ v lo c0 hsn hcfg hlive hqnum $$ Hfr0 Hlot

/-- **The ring-cell pin.**  The loop knows position `lo` is published and
which head it names, so the cell's value is determined; the invariant's
half of that cell is at exactly that value. -/
theorem leaseV_ring_pin (γ : DiskNames) (c0 : VirtioCfg) (lo : Nat) (v s' : VirtioState)
    (ai : BitVec (8 * 2)) (hlv : Virtio.live v.cfg = true)
    (hne : ai.extractLsb' 0 16 ≠ wrap16 lo) :
    iprop(bodyKnow (GF := GF) γ v lo c0 ∗ availAnswer γ lo ai ∗ diskProto γ s') ⊢
      dmaReadPinV (Virtio.availRingAddr v.cfg v.seen) 2 (fun _ => True)
        (fun w => iprop(diskProto γ s' ∗ (bodyKnow γ v lo c0 ∗ ringAnswer γ lo w))) := by
  iintro ⟨HC, Hans, HR⟩
  icases bodyKnow_live γ v lo c0 hlv $$ HC with ⟨Hlot, #Hfr0, %hp⟩
  obtain ⟨hsn, hcfg, hlive, hqnum⟩ := hp
  unfold availAnswer
  icases Hans with ⟨%hbad | ⟨%i, %hi, #Hlb, #Hrec⟩⟩
  · exact absurd hbad hne
  icases diskProto_open_queue γ c0 s' hlive $$ [$Hfr0 $HR]
    with ⟨%np, %lo', %ring, %st, %pmap, %hq, Hlo, HnpM, Hpos, Hav, Hback⟩
  ihave %hll := diskLo_agree γ lo' lo $$ Hlo Hlot
  subst lo'
  ihave %hlt := diskPubLb_le γ np (lo + 1) $$ HnpM Hlb
  ihave %hrl := posRec_lookup γ pmap lo i $$ Hpos Hrec
  have hri : ring (lo % NUM) = i := by
    have hx := hq.2.2.2.2.2.2 lo (Nat.le_refl lo) (by omega)
    rw [hrl] at hx
    exact (Option.some.inj hx).symm
  obtain ⟨hlti, _⟩ := queueOk_head st ring lo np hq.2.2.2.2.1 (by omega)
  icases availLease_cell c0.avail np ring (lo % NUM) (mod_NUM_lt lo) $$ Hav with ⟨Hcell, Havb⟩
  rw [hcfg, hsn, availRingAt_eq c0 (wrap16 lo) hqnum, wrap16_mod8]
  iapply dmaHalfAt_pinV (availRingAt c0.avail (lo % NUM)) 2
    (BitVec.ofNat 16 (ring (lo % NUM)))
    (fun w => iprop(diskProto γ s' ∗ (bodyKnow γ v lo c0 ∗ ringAnswer γ lo w)))
    (fun _ => True) trivial
  iframe Hcell
  iintro Hcell2
  ihave Hav2 := Havb $$ Hcell2
  isplitl [Hback Hlo HnpM Hpos Hav2]
  · iapply Hback $$ Hlo HnpM Hpos Hav2
  · isplitl [Hlot]
    · iapply bodyKnow_mk γ v lo c0 hsn hcfg hlive hqnum $$ Hfr0 Hlot
    · unfold ringAnswer
      iexists (ring (lo % NUM))
      isplitl []
      · ipureintro; exact ⟨hlti, extract16_self _⟩
      rw [hri]
      iframe Hlb Hrec

/-! ### The loop -/

set_option maxHeartbeats 1000000 in
theorem leaseV_body (γ : DiskNames) :
    DevM.LeaseV (diskProto (GF := GF) γ) (diskTaskRes γ) (diskRoot γ) (diskRoot γ)
      Virtio.body := by
  unfold Virtio.body DevM.chooseLt DevM.choose DevM.get DevM.modify DevM.step DevM.lift
    Virtio.dma16 DevM.dmaRead DevM.fork
  simp only [bind, DevM.bind, Pure.pure]
  refine DevM.LeaseV.op _ _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
    (fun _ => nofun) (fun _ => nofun) (fun _ _ _ => nofun) (fun kk => ?_)
  split
  · refine DevM.LeaseV.get _ (X := Nat × VirtioCfg)
      (fun s x => bodyKnow γ s x.1 x.2) _ (fun s => leaseV_root_get γ s) (fun v x => ?_)
    obtain ⟨lo, c0⟩ := x
    split
    · rename_i hlive
      refine DevM.LeaseV.dmaReadV _ _ 2 (fun _ _ => True)
        (fun w => iprop(bodyKnow γ v lo c0 ∗ availAnswer γ lo w)) _ ?_ (fun ai _ => ?_)
      · intro s'
        exact leaseV_avail_pin γ c0 lo v s' hlive
      · simp only [bind, DevM.bind, Pure.pure]
        split
        · rename_i hne
          refine DevM.LeaseV.dmaReadV _ _ 2 (fun _ _ => True)
            (fun w => iprop(bodyKnow γ v lo c0 ∗ ringAnswer γ lo w)) _ ?_ (fun hw _ => ?_)
          · intro s'
            iintro ⟨⟨HC, Hans⟩, HR⟩
            ihave %hsn := bodyKnow_seen γ v lo c0 $$ HC
            iapply leaseV_ring_pin γ c0 lo v s' ai hlive
              (fun hx => hne (by rw [hsn, hx]))
            iframe HC Hans HR
          · simp only [bind, DevM.bind, Pure.pure]
            refine DevM.LeaseV.get _ (X := Unit)
              (fun _ _ => iprop(bodyKnow γ v lo c0 ∗ ringAnswer γ lo hw)) _
              (fun s1 => leaseV_get_keep γ _ s1) (fun popped _ => ?_)
            split
            · refine DevM.LeaseV.pure _ () ?_
              iintro ⟨HC, _⟩
              iapply bodyKnow_root γ v lo c0 $$ HC
            · refine DevM.LeaseV.step _
                iprop(diskLoTok γ (lo + 1) ∗ diskUp γ ∗
                  ∃ (k : Nat) (c : Chain), permTok γ k (hw.extractLsb' 0 16) c) _ _ ?_ ?_
              · intro s1 s2 os hgs
                have hs2 : s2 = { Virtio.setPhase s1 (hw.extractLsb' 0 16) .popped with
                    seen := s1.seen + 1#16 } := by
                  simp only [Option.some.injEq, Prod.mk.injEq] at hgs
                  exact hgs.1.symm
                subst hs2
                iintro ⟨⟨HC, Hring⟩, HR⟩
                icases bodyKnow_live γ v lo c0 hlive $$ HC with ⟨Hlot, #Hfr, %hp⟩
                unfold ringAnswer
                icases Hring with ⟨%i, %hri, #Hlb, #Hrec⟩
                imod diskProto_pop_live γ c0 s1 (hw.extractLsb' 0 16) lo i hp.2.2.1
                    (by rw [hri.2]; exact toNat_ofNat16 i hri.1)
                    $$ [$Hfr $Hlot $Hlb $Hrec $HR] with ⟨HR, Hlot, Htok⟩
                imodintro
                iframe HR Hlot Htok
                unfold diskUp
                iexists c0
                iframe Hfr
                ipureintro; exact ⟨hp.2.2.1, hp.2.2.2⟩
              · refine DevM.LeaseV.fork _ iprop(diskLoTok γ (lo + 1)) _ _ ?_
                  (fun _ => DevM.LeaseV.pure _ () (diskLoTok_root γ (lo + 1)))
                rw [diskTaskRes_serve]
        · refine DevM.LeaseV.pure _ () ?_
          iintro ⟨HC, _⟩
          iapply bodyKnow_root γ v lo c0 $$ HC
    · refine DevM.LeaseV.pure _ () (bodyKnow_root γ v lo c0)
  · split
    · refine DevM.LeaseV.get _ (X := Unit) (fun _ _ => diskRoot γ) _
        (fun s => leaseV_get_keep γ (diskRoot γ) s) (fun v _ => ?_)
      split
      · exact DevM.LeaseV.pure _ () .rfl
      · refine DevM.LeaseV.op _ _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
          (fun _ => nofun) (fun _ => nofun) (fun _ _ _ => nofun) (fun j => ?_)
        refine DevM.LeaseV.step _ (diskRoot γ) _ _ ?_ (DevM.LeaseV.pure _ () .rfl)
        intro s1 s2 os hgs
        have hs2 : s2 = Virtio.drain s1 (s1.cache.getD (j % v.cache.length) (0, [])).1 := by
          simp only [Option.some.injEq, Prod.mk.injEq] at hgs
          exact hgs.1.symm
        subst hs2
        iintro ⟨HC, HR⟩
        imodintro
        iframe HC
        iapply diskProto_drain γ s1 _ $$ HR
    · exact DevM.LeaseV.pure _ () .rfl

/-! ## The device-side theorem -/

/-- **The disk's programs respect the invariant**: every DMA write is
covered by a lease out of `diskProto`, every DMA read is pinned, and every
move of the device's own state carries the protocol along -- the install
included, which is what the serve permit buys -- and the ROOT LOOP holds
the pop counter's half from one iteration to the next. -/
theorem disk_leaseV (γ : DiskNames) :
    DevSig.LeaseV .virtio (diskProto (GF := GF) γ) (diskTaskRes γ) (diskRoot γ) := by
  refine ⟨leaseV_body γ, fun t => ?_⟩
  cases t with
  | serve h => rw [diskTaskRes_serve]; exact leaseV_of_leaseL _ _ _ _ _ (leaseL_serve γ h)
  | xferIn h i => exact leaseV_of_leaseL _ _ _ _ _ (leaseL_xferIn γ _ h i)
  | xferOut h i => exact leaseV_of_leaseL _ _ _ _ _ (leaseL_xferOut γ _ h i)

/-- **The disk's device thread is safe under its invariant**, with no
assumption left -- the instance of `MachCSL.wpDev_dmaV` the adequacy
theorem forks.  `diskRoot γ` is what the boot client hands the root task
once, at power-on: the other half of the pop counter, whose invariant half
sits beside `⌜v.seen = wrap16 lo⌝`. -/
theorem wpDev_disk_inv (γ : DiskNames) :
    diskInv γ ∗ genCert ∗ diskRoot γ ⊢@{IProp GF}
      devWP (genId (hlc := hlc) (GF := GF)) .virtio rootTask (DevM.pure ()) := by
  unfold diskInv
  iintro ⟨Hinv, Hcert, Hroot⟩
  iapply wpDev_dmaV_root diskN .virtio (diskProto γ) (diskTaskRes γ) (diskRoot γ)
    (disk_leaseV γ)
  iframe Hinv Hcert Hroot

end
