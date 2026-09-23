/-
The virtio disk's DEVICE-SIDE proof: the device's own program respects the
invariant of `Xv6/DiskInvDefs.lean`, with NOTHING assumed.

    disk_leaseL     : DevSig.LeaseL .virtio (diskProto γ) (diskTaskRes γ)
    wpDev_disk_inv  : diskInv γ ∗ genCert ⊢ devWP .. .virtio rootTask (DevM.pure ())

THE PROBLEM THIS FILE SOLVES.  `Virtio.serve h` reads the three
descriptors of head `h` and its request header at one state and INSTALLS
the request it parsed several steps later.  The install is sound only
because the chain armed at `h` cannot have moved in between: the driver
re-arms a head only after reclaiming it, and it may only reclaim a head
that is not in flight.  "Nothing has happened at `h` since I looked" is
not a monotone fact, so no PERSISTENT knowledge context can carry it --
`MachCSL.DevM.Lease`'s obligations are quantified over every state, and
at the state where the head has meanwhile completed, been reclaimed and
been re-armed with another chain, the install genuinely breaks
`inflightOk`.  That is why the previous version of this file ASSUMED
`proto_install`.

THE MECHANISM.  `MachCSL/WpDevDmaStep.lean` threads the knowledge context
LINEARLY (`DevM.LeaseL`), so a task may hold an exclusive ghost resource
across its steps, and its `.get` arm may update the invariant -- the state
does not move, but `R s` is a proposition, so taking a resource out and
recording that it is out re-establishes it.  The disk uses that as
follows.

* At its first `get`, `serve h` TAKES A PERMIT (`Xv6.permTok`, a ghost-map
  element the invariant records in `permOk`) that pins the receipt of `h`
  to whatever it is at that moment.  Taking one is always possible: the
  key is fresh.
* Each of the five reads of `Virtio.fetch` is then PINNED -- to the
  chain's descriptor words and header when the head is armed
  (`leaseL_fetch_armed`), and to the sixteen ZERO bytes `free_desc` left
  behind when it is not (`leaseL_fetch_free`), in which case the
  descriptor has no NEXT flag and the request stalls.  So the request the
  device assembles IS `c.req`.
* The installs (`.fetched`, `.served`, `.status`, `.pushed`) are then
  `perm_install`: the permit says the receipt is still `.active c`, and
  `inflightOk` accepts `c.req` at `h`.
* The permit goes back at the completion (`perm_complete`).
* The task is forked with `diskUp γ` -- the persistent "the configuration
  is frozen at a live `c0`" -- which is what `Virtio.body`'s live branch
  has, so a `serve` task never has to cope with the dead arm, and every
  address it computes from the state at its `get` is `c0`'s.

WHAT THE DEAD ARM COSTS.  `Xv6.diskDead` pins `v.usedIdx` and `v.seen` to
zero (the live flip needs them at `nc = lo = 0`), so the two steps that
move those two fields -- `Virtio.complete` at the end of `serve`, and the
pop in `Virtio.body` -- may no longer be proved against an arbitrary arm:
`diskProto_complete` and `diskProto_pop_live` take `diskCfgFrozen γ c0`
with `Virtio.live c0 = true` and REFUTE the dead arm with it.  Both have
it: the serving task carries the frozen configuration in its `serveCtx`,
and `Virtio.body` pops only inside `if live v.cfg`, where the derivation
already holds `diskUp γ`.

WHAT THE DRIVER'S SIDE INHERITS.  A permit for `h` blocks every move of
`h`'s receipt, so `publish` (arming) and `reclaim` will have to show that
no permit for that head is out.  That is where the queue record's
`nc ≤ lo ≤ np` accounting (`Xv6.VQ.Ok`) belongs: it is what rules out a
pop of a head that is already in flight or was never armed, and so what
bounds the permits on a head to the one `serve` task that is running.
That accounting is NOT here, and cannot be maintained without a change
outside these files: the pop's guard is checked at one state and its
effect happens at another, and the logic has no way to say that the
device's root loop is a single thread.  The argument, and the two-line
fix it needs, are written out at the head of the assumed-interface
section of `Xv6/DiskAcc.lean`.
-/
import Xv6.DiskInvDefs
import MachCSL.WpDevDmaStep

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
    icases Hd with ⟨%m, Hm, Hcfg, %hpure⟩
    obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hpure
    iexists m
    rw [hcfg]
    iframe Hm Hcfg
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
    icases Hl with ⟨%st, %nc, %np, %ring, %m, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, %hpure⟩
    obtain ⟨e1, e2, e3, e4, e5⟩ := hpure
    iexists st, nc, np, ring, m
    iframe Hm Ha Hr Hu Hav Hnc Hnp
    ipureintro
    refine ⟨by rw [hidx]; exact e1, hfl st e2, ?_, hcd st e4, e5⟩
    intro bno bs hb
    rcases e3 bno bs hb with h | h
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

/-- **The pop.**  It moves `v.seen`, which the DEAD arm pins to zero, so
this one needs the frozen configuration: `Virtio.body` pops only in its
live branch, and the derivation carries `diskUp γ` there. -/
theorem diskProto_pop_live (γ : DiskNames) (c0 : VirtioCfg) (v : VirtioState) (h : BitVec 16)
    (ph : VPhase) (hlive : Virtio.live c0 = true) (hph : ph.req = none) :
    diskCfgFrozen (GF := GF) γ c0 ∗ diskProto γ v ⊢
      diskProto γ { Virtio.setPhase v h ph with seen := v.seen + 1#16 } := by
  have hfl : ∀ st, inflightOk v st → inflightOk (Virtio.setPhase v h ph) st :=
    fun st hok k r hr => inflightOk_setPhase_none v st h ph hph hok k r hr
  unfold diskProto
  iintro ⟨#Hfr0, %hc, %pn, %pm, Hpm, %hfr, Harm⟩
  icases Harm with ⟨Hd | ⟨%c0', #Hfr, %hc0, Hl⟩⟩
  · unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, %hpure⟩
    ihave %heq := diskCfgFrozen_auth_agree γ c0 v.cfg $$ Hfr0 Hcfg
    rw [heq, hpure.1] at hlive
    exact absurd hlive (by simp)
  · isplitl []
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
    unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %ring, %m, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, %hpure⟩
    obtain ⟨e1, e2, e3, e4, e5⟩ := hpure
    iexists st, nc, np, ring, m
    iframe Hm Ha Hr Hu Hav Hnc Hnp
    ipureintro
    exact ⟨e1, hfl st e2, e3, e4, e5⟩

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
    icases Hd with ⟨%m, Hm, Hcfg, %hpure⟩
    obtain ⟨p1, p2, p3, p4⟩ := hpure
    rw [p2 h] at hin
    exact absurd hin (by simp)
  · unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %ring, %m, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, %hpure⟩
    obtain ⟨e1, e2, e3, e4, e5⟩ := hpure
    obtain ⟨hlt, c, hst, hhd, hreq⟩ := e2 h r hin
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
          rcases e3 bno bs0 hb with hx | hx
          · exact Or.inl hx
          · by_cases hbn : Virtio.reqKey r i / SPB = bno
            · exact Or.inl (hbn ▸ hnf)
            · exact Or.inr (by rw [hx, blockView_set_ne v _ bs bno hbn])
        · intro e he hne
          rcases setCache_mem v _ bs e he with rfl | he'
          · exact hnf
          · exact e4 e he' hne
      · have hz : Virtio.reqSectorLen r i = 0 := by
          rcases Nat.eq_zero_or_pos (Virtio.reqSectorLen r i) with hz | hz
          · exact hz
          · exact absurd (hfly (by omega)) hnf
        have hbnil : bs = [] := List.eq_nil_of_length_eq_zero (by rw [hlen, hz])
        subst hbnil
        constructor
        · intro bno bs0 hb
          rcases e3 bno bs0 hb with hx | hx
          · exact Or.inl hx
          · exact Or.inr (by rw [hx, blockView_set_nil v st _ bno e4 hnf])
        · intro e he hne
          rcases setCache_mem v _ [] e he with rfl | he'
          · exact absurd rfl hne
          · exact e4 e he' hne
    iright
    iexists c0
    iframe Hfr
    isplitl []
    · ipureintro; exact hc0
    iexists st, nc, np, ring, m
    iframe Hm Ha Hr Hu Hav Hnc Hnp
    ipureintro
    exact ⟨e1, fun k rr hr => e2 k rr hr, key.1, key.2, e5⟩

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
    icases Hd with ⟨%m, Hm, Hcfg, %hpure⟩
    ihave %heq := diskCfgFrozen_auth_agree γ c0 v.cfg $$ Hfr0 Hcfg
    rw [heq, hpure.1] at hlive
    exact absurd hlive (by simp)
  · unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %ring, %m, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, %hpure⟩
    obtain ⟨e1, e2, e3, e4, e5⟩ := hpure
    unfold diskDoneAuth
    imod MonoNat.own_update γ.nc (.ofNat nc) (.ofNat (nc + 1))
      (by simp only [MaxNat.le_toNat]; omega) $$ Hnc with ⟨Hnc, _⟩
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
    iexists st, nc + 1, np, ring, m
    iframe Hm Ha Hr Hu Hav Hnc Hnp
    ipureintro
    refine ⟨?_, inflightOk_complete v st h e2, e3, e4, e5⟩
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
    icases Hd with ⟨%m, Hm, Hcfg, %hpure⟩
    rw [hpure.2.1 h] at hin
    exact absurd hin (by simp)
  · unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %ring, %m, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, %hpure⟩
    obtain ⟨e1, e2, e3, e4, e5⟩ := hpure
    obtain ⟨hlt, c, hst, hhd, hreq⟩ := e2 h r hin
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
    iexists st, nc, np, ring, m
    iframe Hm Ha Hu2 Hav Hnc Hnp
    isplitl [Hcl2 Hclb Hrback]
    · iapply Hrback
      iapply Hclb $$ Hcl2
    · ipureintro; exact ⟨e1, e2, e3, e4, e5⟩

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
theorem usedIdx_write_lease (γ : DiskNames) (s : VirtioState) (h : BitVec 16) (r : VioReq)
    (cc : VirtioCfg) (hin : Virtio.reqOf s h = some r) (hcc : s.cfg = cc)
    (w : BitVec (8 * 2)) :
    diskProto (GF := GF) γ s ⊢ dmaWriteLease (Virtio.usedIdxAddr cc) 2 w (diskProto γ s) := by
  iintro H
  icases diskProto_chain_acc γ s h r hin $$ H with ⟨%c0, %c, %hp, Hcl, Hu, Hback⟩
  obtain ⟨hreq, hhd, hwf, hcfg, hq⟩ := hp
  have hcc0 : cc = c0 := by rw [← hcc, hcfg]
  subst hcc0
  rw [usedIdxAt_eq cc]
  icases usedIdx_acc cc.used $$ Hu with ⟨He, Heb⟩
  iapply dmaOwn_lease_frame (usedIdxAt cc.used) 2 w (diskProto γ s)
  isplitl [He]
  · iexact He
  · iintro He2
    iapply Hback
    isplitl [Hcl]
    · iexact Hcl
    · iapply Heb $$ He2

/-! ## The serve permit

The device-side counterpart of `Xv6.permTok`: how a task takes a permit,
what it pins while it holds one, and how it gives it back. -/

theorem permTok_lookup (γ : DiskNames) (pm : RegMapF PermVal) (k : Nat) (h : BitVec 16)
    (s0 : HState) :
    ⊢@{IProp GF} permAuth γ pm -∗ permTok γ k h s0 -∗
      ⌜PartialMap.get? pm k = some ((h, s0) : PermVal)⌝ := by
  unfold permAuth permTok
  iintro H1 H2
  ihave %hg := ghost_map_lookup $$ H1 H2
  ipureintro; exact hg

/-- A free slot's row IS the half of its sixteen zero bytes. -/
theorem headRes_inactive_eq (γ : DiskNames) (pd : PAddr) (i : Nat) :
    headRes (GF := GF) γ pd i .inactive = dmaHalfAt (descAt pd i) 16 (0 : BitVec (8 * 16)) := rfl

theorem headRes_inactive_acc (γ : DiskNames) (pd : PAddr) (st : Nat → HState) (i : Nat)
    (hi : i < NUM) (hst : st i = .inactive) :
    ([∗list] j ∈ List.range NUM, headRes (GF := GF) γ pd j (st j)) ⊢
      dmaHalfAt (descAt pd i) 16 (0 : BitVec (8 * 16)) ∗
      (dmaHalfAt (descAt pd i) 16 (0 : BitVec (8 * 16)) -∗
        [∗list] j ∈ List.range NUM, headRes γ pd j (st j)) := by
  rw [← headRes_inactive_eq (GF := GF) γ pd i]
  exact headRes_acc' γ pd st i .inactive hi hst

/-- Every armed row is well formed, as a fact about the receipt alone. -/
theorem headRes_wf_all (γ : DiskNames) (pd : PAddr) (st : Nat → HState) (h : BitVec 16) :
    ([∗list] j ∈ List.range NUM, headRes (GF := GF) γ pd j (st j)) ⊢
      ⌜∀ c : Chain, hstateAt st h = .active c → c.hd = h.toNat ∧ c.wf⌝ := by
  by_cases hlt : h.toNat < NUM
  · cases hs : st h.toNat with
    | inactive =>
      iintro _
      ipureintro
      intro c hc
      rw [hstateAt, if_pos hlt, hs] at hc
      exact absurd hc (by simp)
    | active c0 =>
      iintro H
      ihave %hw := headRes_wf_of γ pd st h.toNat c0 hlt hs $$ H
      ipureintro
      intro c hc
      rw [hstateAt, if_pos hlt, hs] at hc
      cases hc
      exact hw
  · iintro _
    ipureintro
    intro c hc
    rw [hstateAt, if_neg hlt] at hc
    exact absurd hc (by simp)

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
    icases Hd with ⟨%m, Hm, Hcfg, %hpure⟩
    ihave %heq := diskCfgFrozen_auth_agree γ c0 v.cfg $$ Hfr0 Hcfg
    rw [heq, hpure.1] at hlive
    exact absurd hlive (by simp)
  · ihave %hcc := diskCfgFrozen_agree γ c0 c0' $$ [$Hfr0 $Hfr]
    subst hcc
    unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %ring, %m, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, %hpure⟩
    obtain ⟨e1, e2, e3, e4, e5⟩ := hpure
    isplitl []
    · ipureintro; exact ⟨hc0.1, hc0.2.2⟩
    iexists pn, pm, st
    isplitl []
    · ipureintro; exact ⟨hfr, e5⟩
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
    iexists st, nc, np, ring, m
    iframe Hm Ha Hr' Hu Hav Hnc Hnp
    ipureintro
    exact ⟨e1, e2, e3, e4, hpure'.2⟩

/-- **Taking a permit.**  Always possible: the key `pn` is free, and the
permit records the receipt the head carries right now. -/
theorem perm_take (γ : DiskNames) (c0 : VirtioCfg) (h : BitVec 16) (v : VirtioState)
    (hlive : Virtio.live c0 = true) :
    diskCfgFrozen (GF := GF) γ c0 ∗ diskProto γ v ⊢ |==> ∃ (k : Nat) (s0 : HState),
      ⌜v.cfg = c0 ∧ c0.qnum.toNat = NUM ∧ (∀ c : Chain, s0 = .active c → c.hd = h.toNat ∧ c.wf)⌝ ∗
      permTok γ k h s0 ∗ diskProto γ v := by
  iintro ⟨#Hfr, H⟩
  icases diskProto_open_live γ c0 v hlive $$ [$Hfr $H] with ⟨%hcfg, %pn, %pm, %st, %hpp, Hpm, Hr, Hback⟩
  ihave %hwf := headRes_wf_all γ c0.desc st h $$ Hr
  unfold permAuth permTok
  imod ghost_map_insert (V := PermVal) pn ((h, hstateAt st h) : PermVal)
      (hpp.1 pn (Nat.le_refl pn)) $$ Hpm with ⟨Hpm, Htok⟩
  imodintro
  iexists pn, (hstateAt st h)
  isplitl []
  · ipureintro; exact ⟨hcfg.1, hcfg.2, hwf⟩
  iframe Htok
  iapply Hback $$ %(pn + 1) %(PartialMap.insert pm pn ((h, hstateAt st h) : PermVal))
    %(⟨permFresh_insert pm pn h _ hpp.1, permOk_insert pm st pn h hpp.2⟩) Hpm Hr

/-- **Giving a permit back**: always sound, and what the driver's future
`reclaim` will need to have happened for every permit on the head it
reclaims. -/
theorem perm_drop (γ : DiskNames) (k : Nat) (h : BitVec 16) (s0 : HState) (v : VirtioState) :
    permTok (GF := GF) γ k h s0 ∗ diskProto γ v ⊢ |==> diskProto γ v := by
  unfold diskProto
  iintro ⟨Htok, %hc, %pn, %pm, Hpm, %hfr, Harm⟩
  unfold permAuth permTok
  imod ghost_map_delete (V := PermVal) k ((h, s0) : PermVal) $$ Hpm Htok with Hpm
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
    icases Hd with ⟨%m, Hm, Hcfg, %hpure⟩
    obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hpure
    iexists m
    iframe Hm Hcfg
    ipureintro
    exact ⟨p1, p2, p3, p4, permOk_delete pm (fun _ => .inactive) k p5, p6, p7⟩
  · iright
    iexists c0
    iframe Hfr
    isplitl []
    · ipureintro; exact hc0
    unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %ring, %m, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, %hpure⟩
    obtain ⟨e1, e2, e3, e4, e5⟩ := hpure
    iexists st, nc, np, ring, m
    iframe Hm Ha Hr Hu Hav Hnc Hnp
    ipureintro
    exact ⟨e1, e2, e3, e4, permOk_delete pm st k e5⟩

/-- What a permit says about the receipt it names. -/
theorem perm_hstate (γ : DiskNames) (pm : RegMapF PermVal) (st : Nat → HState) (k : Nat)
    (h : BitVec 16) (s0 : HState) (hok : permOk pm st) :
    ⊢@{IProp GF} permAuth γ pm -∗ permTok γ k h s0 -∗ ⌜hstateAt st h = s0⌝ := by
  iintro Hpm Htok
  ihave %hg := permTok_lookup γ pm k h s0 $$ Hpm Htok
  ipureintro
  exact (hok k h s0 hg).symm

/-- **What an ARMED permit pins**: the chain's descriptors and header, at
the addresses the fetch reads them from. -/
theorem perm_chain_acc (γ : DiskNames) (c0 : VirtioCfg) (k : Nat) (h : BitVec 16) (c : Chain)
    (v : VirtioState) (hlive : Virtio.live c0 = true) :
    diskCfgFrozen (GF := GF) γ c0 ∗ permTok γ k h (.active c) ∗ diskProto γ v ⊢
      ⌜v.cfg = c0 ∧ c.hd = h.toNat ∧ c.wf ∧ c0.qnum.toNat = NUM⌝ ∗ chainLease c0.desc c ∗
      (chainLease c0.desc c -∗ (permTok γ k h (.active c) ∗ diskProto γ v)) := by
  iintro ⟨#Hfr, Htok, H⟩
  icases diskProto_open_live γ c0 v hlive $$ [$Hfr $H] with ⟨%hcfg, %pn, %pm, %st, %hpp, Hpm, Hr, Hback⟩
  ihave %hst := perm_hstate γ pm st k h (.active c) hpp.2 $$ Hpm Htok
  have hlt : h.toNat < NUM := by
    unfold hstateAt at hst
    split at hst
    · assumption
    · exact absurd hst (by simp)
  have hst' : st h.toNat = .active c := by
    unfold hstateAt at hst
    rw [if_pos hlt] at hst
    exact hst
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

/-- **What a FREE permit pins**: the sixteen zero bytes of the descriptor
the driver has not armed. -/
theorem perm_free_acc (γ : DiskNames) (c0 : VirtioCfg) (k : Nat) (h : BitVec 16)
    (v : VirtioState) (hlive : Virtio.live c0 = true) (hlt : h.toNat < NUM) :
    diskCfgFrozen (GF := GF) γ c0 ∗ permTok γ k h .inactive ∗ diskProto γ v ⊢
      ⌜v.cfg = c0 ∧ c0.qnum.toNat = NUM⌝ ∗
      dmaHalfAt (descAt c0.desc h.toNat) 16 (0 : BitVec (8 * 16)) ∗
      (dmaHalfAt (descAt c0.desc h.toNat) 16 (0 : BitVec (8 * 16)) -∗
        (permTok γ k h .inactive ∗ diskProto γ v)) := by
  iintro ⟨#Hfr, Htok, H⟩
  icases diskProto_open_live γ c0 v hlive $$ [$Hfr $H] with ⟨%hcfg, %pn, %pm, %st, %hpp, Hpm, Hr, Hback⟩
  ihave %hst := perm_hstate γ pm st k h .inactive hpp.2 $$ Hpm Htok
  have hst' : st h.toNat = .inactive := by
    unfold hstateAt at hst
    rw [if_pos hlt] at hst
    exact hst
  icases headRes_inactive_acc γ c0.desc st h.toNat hlt hst' $$ Hr with ⟨He, Hrb⟩
  isplitl []
  · ipureintro; exact hcfg
  isplitl [He]
  · iexact He
  iintro He2
  iframe Htok
  iapply Hback $$ %pn %pm %hpp Hpm
  iapply Hrb $$ He2

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
may record the request it parsed, because the permit it took at its first
`get` pins the receipt of `h` to the chain whose descriptors it read. -/
theorem perm_install (γ : DiskNames) (c0 : VirtioCfg) (k : Nat) (h : BitVec 16) (c : Chain)
    (v : VirtioState) (ph : VPhase) (hlive : Virtio.live c0 = true) (hph : ph.req = some c.req) :
    diskCfgFrozen (GF := GF) γ c0 ∗ permTok γ k h (.active c) ∗ diskProto γ v ⊢
      |==> (diskProto γ (Virtio.setPhase v h ph) ∗ permTok γ k h (.active c)) := by
  unfold diskProto
  iintro ⟨#Hfr0, Htok, %hc, %pn, %pm, Hpm, %hfr, Harm⟩
  icases Harm with ⟨Hd | ⟨%c0', #Hfr, %hc0, Hl⟩⟩
  · unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, %hpure⟩
    ihave %heq := diskCfgFrozen_auth_agree γ c0 v.cfg $$ Hfr0 Hcfg
    rw [heq, hpure.1] at hlive
    exact absurd hlive (by simp)
  · ihave %hcc := diskCfgFrozen_agree γ c0 c0' $$ [$Hfr0 $Hfr]
    subst hcc
    unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %ring, %m, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, %hpure⟩
    obtain ⟨e1, e2, e3, e4, e5⟩ := hpure
    ihave %hst := perm_hstate γ pm st k h (.active c) e5 $$ Hpm Htok
    have hlt : h.toNat < NUM := by
      by_cases hl : h.toNat < NUM
      · exact hl
      · rw [hstateAt, if_neg hl] at hst; exact absurd hst (by simp)
    have hst' : st h.toNat = .active c := by rw [hstateAt, if_pos hlt] at hst; exact hst
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
    iexists st, nc, np, ring, m
    iframe Hm Ha Hr Hu Hav Hnc Hnp
    ipureintro
    exact ⟨e1, inflightOk_setPhase_some v st h c ph hph hlt hst' hwf.1 e2, e3, e4, e5⟩

/-- **The completion**, with the permit given back. -/
theorem perm_complete (γ : DiskNames) (c0 : VirtioCfg) (k : Nat) (h : BitVec 16) (s0 : HState)
    (hh : BitVec 16) (v : VirtioState) (hlive : Virtio.live c0 = true) :
    diskCfgFrozen (GF := GF) γ c0 ∗ permTok γ k h s0 ∗ diskProto γ v ⊢
      |==> diskProto γ (Virtio.complete v hh) := by
  iintro ⟨#Hfr, Htok, H⟩
  ihave Hd := perm_drop γ k h s0 v $$ [$Htok $H]
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

/-- What a forked task starts from (`MachCSL.DevSig.LeaseL`'s `Lt`). -/
def diskTaskRes (γ : DiskNames) : Virtio.VTask → IProp GF
  | .serve _ => diskUp γ
  | .xferIn _ _ => iprop(True)
  | .xferOut _ _ => iprop(True)

theorem diskTaskRes_serve (γ : DiskNames) (h : BitVec 16) :
    diskTaskRes (GF := GF) γ (.serve h) = diskUp γ := rfl

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
  iintro ⟨%m, _, _, %hp⟩
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

/-- What the task learns at its first `get`: the frozen configuration, the
receipt the head carried then, and (in `serveCtx`) the permit that keeps
that receipt still. -/
structure ServeKnow (h : BitVec 16) where
  c0 : VirtioCfg
  key : Nat
  hs : HState
  hlive : Virtio.live c0 = true
  hqnum : c0.qnum.toNat = NUM
  hchain : ∀ c : Chain, hs = .active c → c.hd = h.toNat ∧ c.wf

/-- The `serve` task's linear context. -/
def serveCtx (γ : DiskNames) (h : BitVec 16) (c0 : VirtioCfg) (key : Nat) (hs : HState)
    (s : VirtioState) : IProp GF := iprop%
  diskCfgFrozen γ c0 ∗ ⌜s.cfg = c0⌝ ∗ permTok γ key h hs

theorem serveCtx_cfg (γ : DiskNames) (h : BitVec 16) (c0 : VirtioCfg) (key : Nat) (hs : HState)
    (s : VirtioState) : serveCtx (GF := GF) γ h c0 key hs s ⊢ ⌜s.cfg = c0⌝ := by
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
    serveCtx (GF := GF) γ h c0 key (.active c) s ∗ diskProto γ s' ⊢
      dmaReadPin pa n (fun v => v = w)
        iprop(diskProto γ s' ∗ serveCtx γ h c0 key (.active c) s) := by
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

/-- The free head's descriptor reads as sixteen zero bytes. -/
theorem serve_free_pin (γ : DiskNames) (h : BitVec 16) (c0 : VirtioCfg) (key : Nat)
    (s s' : VirtioState) (hlive : Virtio.live c0 = true) (hlt : h.toNat < NUM) :
    serveCtx (GF := GF) γ h c0 key .inactive s ∗ diskProto γ s' ⊢
      dmaReadPin (descAt c0.desc h.toNat) 16 (fun v => v = (0 : BitVec (8 * 16)))
        iprop(diskProto γ s' ∗ serveCtx γ h c0 key .inactive s) := by
  unfold serveCtx
  iintro ⟨⟨#Hfr, %hcfg, Htok⟩, HR⟩
  icases perm_free_acc γ c0 key h s' hlive hlt $$ [$Hfr $Htok $HR] with ⟨%hp, Hhalf, Hback⟩
  iapply dmaHalfAt_pin _ 16 (0 : BitVec (8 * 16)) _ (fun v => v = (0 : BitVec (8 * 16))) rfl
  iframe Hhalf
  iintro Hhalf2
  icases Hback $$ Hhalf2 with ⟨Htok, HR⟩
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
    DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) C Virtio.stall := by
  unfold Virtio.stall DevM.await DevM.step DevM.lift
  exact DevM.LeaseL.step C C _ _ (fun s s' os hgs => by simp at hgs) (DevM.LeaseL.pure _ ())

/-- `Virtio.xferIn h i`: one sector of a read request's fill. -/
theorem leaseL_xferIn (γ : DiskNames) (C : IProp GF) (h : BitVec 16) (i : Nat) :
    DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) C (Virtio.xferIn h i) := by
  unfold Virtio.xferIn
  simp only [bind, DevM.bind, DevM.get, DevM.lift, Pure.pure]
  refine DevM.LeaseL.get C (X := Unit) (fun _ _ => C) _ (fun s => leaseL_get_keep γ C s)
    (fun s _ => ?_)
  cases hr : Virtio.reqOf s h with
  | none => exact DevM.LeaseL.pure _ ()
  | some r =>
    unfold Virtio.reqSectorLen DevM.dmaWriteIf DevM.lift
    refine DevM.LeaseL.dmaWrite _ _ _ _ _ _ ?_ (DevM.LeaseL.pure _ ())
    intro s' hg
    exact leaseL_write_frame γ s' C _ _ _ (data_write_lease γ s' h r i (of_decide_eq_true hg) _)

/-- `Virtio.xferOut h i`: one sector of a write request's capture. -/
theorem leaseL_xferOut (γ : DiskNames) (C : IProp GF) (h : BitVec 16) (i : Nat) :
    DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) C (Virtio.xferOut h i) := by
  unfold Virtio.xferOut
  simp only [bind, DevM.bind, DevM.get, DevM.lift, Pure.pure]
  refine DevM.LeaseL.get C (X := Unit) (fun _ _ => C) _ (fun s => leaseL_get_keep γ C s)
    (fun s _ => ?_)
  cases hr : Virtio.reqOf s h with
  | none => exact DevM.LeaseL.pure _ ()
  | some r =>
    unfold DevM.dmaRead DevM.lift
    refine DevM.LeaseL.dmaRead _ _ _ (fun _ _ => True) _ ?_ (fun w _ => ?_)
    · intro s'
      iintro ⟨HC, HR⟩
      iapply dmaReadPin_any
      iframe HR HC
    · unfold DevM.modify DevM.step DevM.lift
      refine DevM.LeaseL.step _ C _ _ ?_ (DevM.LeaseL.pure _ ())
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
    (hk : DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) C (k ())) :
    DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) C
      (DevM.bind (List.forM l DevM.join) k) := by
  induction l with
  | nil => exact hk
  | cons t l ih =>
    exact DevM.LeaseL.op C _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
      (fun _ => nofun) (fun _ => nofun) (fun _ _ _ => nofun) (fun _ => ih)

theorem leaseL_bind_fork (γ : DiskNames) (C : IProp GF) (ts : List Virtio.VTask)
    (k : List TaskId → Virtio.VM Unit)
    (hk : ∀ l, DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) C (k l)) :
    (∀ t ∈ ts, (⊢@{IProp GF} diskTaskRes γ t)) → ∀ acc : List TaskId,
      DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) C
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
    (hk : DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) C (k ())) :
    DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) C
      (DevM.bind (DevM.forkJoinAll ts) k) := by
  show DevM.LeaseL _ _ C
    (DevM.bind (DevM.bind (List.mapM.loop DevM.fork ts []) (fun l => List.forM l DevM.join)) k)
  rw [DevM_bind_assoc]
  exact leaseL_bind_fork γ C ts _ (fun l => leaseL_bind_join γ C l _ hk) hts []

/-! ### The tail of a request -/

/-- Installing a phase that carries the request of the armed chain. -/
theorem leaseL_install (γ : DiskNames) (h : BitVec 16) (c0 : VirtioCfg) (key : Nat) (c : Chain)
    (s s1 : VirtioState) (ph : VPhase) (hlive : Virtio.live c0 = true)
    (hph : ph.req = some c.req) :
    iprop(serveCtx (GF := GF) γ h c0 key (.active c) s ∗ diskProto γ s1) ⊢
      |==> (diskProto γ (Virtio.setPhase s1 h ph) ∗ serveCtx γ h c0 key (.active c) s) := by
  unfold serveCtx
  iintro ⟨⟨#Hfr, %hcfg, Htok⟩, HR⟩
  imod perm_install γ c0 key h c s1 ph hlive hph $$ [$Hfr $Htok $HR] with ⟨HR, Htok⟩
  imodintro
  iframe HR Htok Hfr
  ipureintro; exact hcfg

theorem leaseL_serveTail (γ : DiskNames) (h : BitVec 16) (c0 : VirtioCfg) (key : Nat)
    (c : Chain) (s : VirtioState) (hlive : Virtio.live c0 = true) :
    DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ)
      (serveCtx γ h c0 key (.active c) s) (serveTail h c.req) := by
  unfold serveTail
  simp only [bind, DevM.bind, DevM.modify, DevM.guard, DevM.step, DevM.lift,
    DevM.dmaWriteIf, DevM.get, Pure.pure]
  refine DevM.LeaseL.step _ (serveCtx γ h c0 key (.active c) s) _ _ ?_ ?_
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
    · refine DevM.LeaseL.step _ (serveCtx γ h c0 key (.active c) s) _ _ ?_ ?_
      · intro s1 s2 os hgs
        have hs2 : s2 = Virtio.setPhase s1 h (.status c.req) := by
          simp only [Option.some.injEq, Prod.mk.injEq] at hgs
          exact hgs.1.symm
        subst hs2
        exact leaseL_install γ h c0 key c s s1 (.status c.req) hlive rfl
      · refine DevM.LeaseL.step _ (serveCtx γ h c0 key (.active c) s) _ _ ?_ ?_
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
            (fun _ _ => serveCtx γ h c0 key (.active c) s) _
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
                (usedIdx_write_lease γ s1 h c.req v2.cfg hgg.1.1 hgg.2 _)
            · refine DevM.LeaseL.step _ iprop(True) _ _ ?_ (DevM.LeaseL.pure _ ())
              intro s1 s2 os hgs
              have hs2 : s2 = Virtio.complete s1 h := by
                simp only [Option.some.injEq, Prod.mk.injEq] at hgs
                exact hgs.1.symm
              subst hs2
              unfold serveCtx
              iintro ⟨⟨#Hfr, %hcfg, Htok⟩, HR⟩
              imod perm_complete γ c0 key h (.active c) h s1 hlive $$ [$Hfr $Htok $HR] with HR
              imodintro
              iframe HR

/-! ### The fetch -/

theorem descOf_zero_noNext :
    (Virtio.descOf (0 : BitVec (8 * 16))).has Virtio.descFNext = false := by
  simp [Virtio.descOf, Virtio.VqDesc.has, Virtio.descFNext]

theorem chain_d0_addr (c : Chain) : (Virtio.descOf c.d0).addr = c.hdrAddr := by rw [chain_d0]

/-- **The fetch at a FREE head stalls.**  The permit says the receipt is
still `.inactive`, the invariant holds the half of the sixteen zero bytes
`free_desc` left there, so the descriptor the device reads has no NEXT
flag and the chain is refused. -/
theorem leaseL_fetch_free (γ : DiskNames) (h : BitVec 16) (c0 : VirtioCfg) (key : Nat)
    (s : VirtioState) (hlive : Virtio.live c0 = true) (hqnum : c0.qnum.toNat = NUM)
    (kf : Option VioReq → Virtio.VM Unit)
    (hkn : DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ)
      (serveCtx γ h c0 key .inactive s) (kf none)) :
    DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ)
      (serveCtx γ h c0 key .inactive s) (DevM.bind (Virtio.fetch s.cfg h) kf) := by
  unfold Virtio.fetch DevM.dmaRead DevM.lift
  simp only [bind, DevM.bind, Pure.pure]
  split
  · exact hkn
  · rename_i hlt0
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, Decidable.not_not] at hlt0
    refine DevM.LeaseL.dmaRead _ _ 16 (fun _ w => w = (0 : BitVec (8 * 16))) _ ?_ (fun w0 hw0 => ?_)
    · intro s'
      iintro ⟨Hctx, HR⟩
      ihave %hcfg := serveCtx_cfg γ h c0 key .inactive s $$ Hctx
      have hlt : h.toNat < NUM := by rw [hcfg, hqnum] at hlt0; exact hlt0
      rw [hcfg, descAt_eq]
      iapply serve_free_pin γ h c0 key s s' hlive hlt
      iframe Hctx HR
    · obtain ⟨_, rfl⟩ := hw0
      simp only [bind, DevM.bind, Pure.pure]
      split
      · exact hkn
      · rename_i hcond
        rw [descOf_zero_noNext] at hcond
        simp at hcond

/-- **The fetch at an ARMED head parses that head's chain.**  Each of the
five reads is pinned by the permit to the bytes the driver wrote, so the
request the device assembles is `c.req` -- which is what makes the install
that follows legal. -/
theorem leaseL_fetch_armed (γ : DiskNames) (h : BitVec 16) (c0 : VirtioCfg) (key : Nat)
    (c : Chain) (s : VirtioState) (hlive : Virtio.live c0 = true) (hqnum : c0.qnum.toNat = NUM)
    (hhd : c.hd = h.toNat) (hwf : c.wf)
    (kf : Option VioReq → Virtio.VM Unit)
    (hkn : DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ)
      (serveCtx γ h c0 key (.active c) s) (kf none))
    (hks : DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ)
      (serveCtx γ h c0 key (.active c) s) (kf (some c.req))) :
    DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ)
      (serveCtx γ h c0 key (.active c) s) (DevM.bind (Virtio.fetch s.cfg h) kf) := by
  unfold Virtio.fetch DevM.dmaRead DevM.lift
  simp only [bind, DevM.bind, Pure.pure]
  split
  · exact hkn
  · refine DevM.LeaseL.dmaRead _ _ 16 (fun _ w => w = c.d0) _ ?_ (fun w0 hw0 => ?_)
    · intro s'
      iintro ⟨Hctx, HR⟩
      ihave %hcfg := serveCtx_cfg γ h c0 key (.active c) s $$ Hctx
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
          ihave %hcfg := serveCtx_cfg γ h c0 key (.active c) s $$ Hctx
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
              ihave %hcfg := serveCtx_cfg γ h c0 key (.active c) s $$ Hctx
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
    DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) (diskUp γ) (Virtio.serve h) := by
  unfold Virtio.serve
  simp only [bind, DevM.bind, DevM.get, DevM.lift]
  refine DevM.LeaseL.get _ (X := ServeKnow h)
    (fun s x => serveCtx γ h x.c0 x.key x.hs s) _ (fun s => ?_) (fun s x => ?_)
  · unfold diskUp
    iintro ⟨#Hup, HR⟩
    icases Hup with ⟨%c0, #Hfr, %hl⟩
    imod perm_take γ c0 h s hl.1 $$ [$Hfr $HR] with ⟨%kk, %s0, %hp, Htok, HR⟩
    imodintro
    iframe HR
    iexists (⟨c0, kk, s0, hl.1, hl.2, hp.2.2⟩ : ServeKnow h)
    unfold serveCtx
    iframe Hfr Htok
    ipureintro; exact hp.1
  · cases hx : x.hs with
    | inactive =>
      exact leaseL_fetch_free γ h x.c0 x.key s x.hlive x.hqnum _ (leaseL_stall γ _)
    | active c =>
      obtain ⟨hhd, hwf⟩ := x.hchain c hx
      refine leaseL_fetch_armed γ h x.c0 x.key c s x.hlive x.hqnum hhd hwf _
        (leaseL_stall γ _) ?_
      simp only [bind, DevM.bind, DevM.modify, DevM.step, DevM.lift, Pure.pure]
      refine DevM.LeaseL.step _ (serveCtx γ h x.c0 x.key (.active c) s) _ _ ?_ ?_
      · intro s1 s2 os hgs
        have hs2 : s2 = Virtio.setPhase s1 h (.fetched c.req) := by
          simp only [Option.some.injEq, Prod.mk.injEq] at hgs
          exact hgs.1.symm
        subst hs2
        exact leaseL_install γ h x.c0 x.key c s s1 (.fetched c.req) x.hlive rfl
      · split
        · refine DevM.LeaseL.step _ (serveCtx γ h x.c0 x.key (.active c) s) _ _ ?_ ?_
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
              (leaseL_serveTail γ h x.c0 x.key c s x.hlive)
            obtain ⟨i, _, rfl⟩ := List.mem_map.1 ht
            exact diskTaskRes_xferOut γ h i
        · split
          · refine leaseL_forkJoinAll γ _ _ (fun t ht => ?_) _
              (leaseL_serveTail γ h x.c0 x.key c s x.hlive)
            obtain ⟨i, _, rfl⟩ := List.mem_map.1 ht
            exact diskTaskRes_xferIn γ h i
          · exact leaseL_serveTail γ h x.c0 x.key c s x.hlive

/-! ## `Virtio.body`: the root loop -/

theorem leaseL_body (γ : DiskNames) (C : IProp GF) :
    DevM.LeaseL (diskProto (GF := GF) γ) (diskTaskRes γ) C Virtio.body := by
  unfold Virtio.body DevM.chooseLt DevM.choose DevM.get DevM.modify DevM.step DevM.lift
    Virtio.dma16 DevM.dmaRead DevM.fork
  simp only [bind, DevM.bind, Pure.pure]
  refine DevM.LeaseL.op C _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
    (fun _ => nofun) (fun _ => nofun) (fun _ _ _ => nofun) (fun kk => ?_)
  split
  · refine DevM.LeaseL.get _ (X := Unit)
      (fun s _ => iprop(⌜Virtio.live s.cfg = false⌝ ∨ diskUp γ)) _ (fun s => ?_) (fun v _ => ?_)
    · iintro ⟨_, HR⟩
      icases diskProto_arm γ s $$ HR with ⟨HR, #Harm⟩
      imodintro
      iframe HR
      iexists ()
      iexact Harm
    · split
      · rename_i hlive
        refine DevM.LeaseL.dmaRead _ _ 2 (fun _ _ => True) _ ?_ (fun ai _ => ?_)
        · intro s'
          iintro ⟨HC, HR⟩
          iapply dmaReadPin_any
          iframe HR HC
        · simp only [bind, DevM.bind, Pure.pure]
          split
          · refine DevM.LeaseL.dmaRead _ _ 2 (fun _ _ => True) _ ?_ (fun hw _ => ?_)
            · intro s'
              iintro ⟨HC, HR⟩
              iapply dmaReadPin_any
              iframe HR HC
            · simp only [bind, DevM.bind, Pure.pure]
              refine DevM.LeaseL.get _ (X := Unit)
                (fun _ _ => iprop(⌜Virtio.live v.cfg = false⌝ ∨ diskUp γ)) _
                (fun s1 => leaseL_get_keep γ _ s1) (fun popped _ => ?_)
              split
              · exact DevM.LeaseL.pure _ ()
              · refine DevM.LeaseL.step _
                  iprop(⌜Virtio.live v.cfg = false⌝ ∨ diskUp γ) _ _ ?_ ?_
                · intro s1 s2 os hgs
                  have hs2 : s2 = { Virtio.setPhase s1 (hw.extractLsb' 0 16) .popped with
                      seen := s1.seen + 1#16 } := by
                    simp only [Option.some.injEq, Prod.mk.injEq] at hgs
                    exact hgs.1.symm
                  subst hs2
                  unfold diskUp
                  iintro ⟨#HC, HR⟩
                  icases HC with ⟨%hf | ⟨%c0, #Hfr, %hl⟩⟩
                  · rw [hlive] at hf; exact absurd hf (by simp)
                  imodintro
                  isplitl [HR]
                  · iapply diskProto_pop_live γ c0 s1 _ .popped hl.1 rfl $$ [$Hfr $HR]
                  · iright
                    iexists c0
                    iframe Hfr
                    ipureintro; exact hl
                · refine DevM.LeaseL.fork _ iprop(True) _ _ ?_ (fun _ => DevM.LeaseL.pure _ ())
                  rw [diskTaskRes_serve]
                  iintro Hor
                  icases Hor with ⟨%hf | #Hup⟩
                  · rw [hlive] at hf; exact absurd hf (by simp)
                  · isplitr []
                    · itrivial
                    · iexact Hup
          · exact DevM.LeaseL.pure _ ()
      · exact DevM.LeaseL.pure _ ()
  · split
    · refine DevM.LeaseL.get _ (X := Unit) (fun _ _ => C) _ (fun s => leaseL_get_keep γ C s)
        (fun v _ => ?_)
      split
      · exact DevM.LeaseL.pure _ ()
      · refine DevM.LeaseL.op _ _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
          (fun _ => nofun) (fun _ => nofun) (fun _ _ _ => nofun) (fun j => ?_)
        refine DevM.LeaseL.step _ C _ _ ?_ (DevM.LeaseL.pure _ ())
        intro s1 s2 os hgs
        have hs2 : s2 = Virtio.drain s1 (s1.cache.getD (j % v.cache.length) (0, [])).1 := by
          simp only [Option.some.injEq, Prod.mk.injEq] at hgs
          exact hgs.1.symm
        subst hs2
        iintro ⟨HC, HR⟩
        imodintro
        iframe HC
        iapply diskProto_drain γ s1 _ $$ HR
    · exact DevM.LeaseL.pure _ ()

/-! ## The device-side theorem -/

/-- **The disk's programs respect the invariant**: every DMA write is
covered by a lease out of `diskProto`, every DMA read is pinned, and every
move of the device's own state carries the protocol along -- the install
included, which is what the serve permit buys. -/
theorem disk_leaseL (γ : DiskNames) :
    DevSig.LeaseL .virtio (diskProto (GF := GF) γ) (diskTaskRes γ) := by
  refine ⟨leaseL_body γ _, fun t => ?_⟩
  cases t with
  | serve h => rw [diskTaskRes_serve]; exact leaseL_serve γ h
  | xferIn h i => exact leaseL_xferIn γ _ h i
  | xferOut h i => exact leaseL_xferOut γ _ h i

/-- **The disk's device thread is safe under its invariant**, with no
assumption left -- the instance of `MachCSL.wpDev_dmaL` the adequacy
theorem forks. -/
theorem wpDev_disk_inv (γ : DiskNames) :
    diskInv γ ∗ genCert ⊢@{IProp GF}
      devWP (genId (hlc := hlc) (GF := GF)) .virtio rootTask (DevM.pure ()) := by
  unfold diskInv
  iintro H
  iapply wpDev_dmaL_root diskN .virtio (diskProto γ) (diskTaskRes γ) (disk_leaseL γ) $$ H

end
