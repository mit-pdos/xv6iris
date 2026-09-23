/-
The virtio disk's DEVICE-SIDE proof: the device's own program respects the
invariant of `Xv6/DiskInvDefs.lean`.

    disk_lease      : DevSig.Lease .virtio diskRel (diskProto γ)
    wpDev_disk_inv  : diskInv γ ∗ genCert ⊢ devWP .. .virtio rootTask (DevM.pure ())

`diskRel` is the device's own move relation; `diskProto_step` is that the
protocol survives every move (Rocq's `virtio_proto_{pop,fetch,capture,
write,drain}_step`), and the `DevM.Lease` derivation walks `body`,
`serve`, `xferIn` and `xferOut` discharging, at each primitive, the
obligations of `MachCSL.WpDevDma`.
-/
import Xv6.DiskInvDefs

namespace Xv6

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

/-! ## The device's own moves -/

/-- Every move the disk's program makes of its own state.

* `pop` -- `body` takes the available entry at `seen` and records the head
  as `.popped` (no request yet);
* `install` -- `serve` records the request it fetched, and then moves it
  along the phases `.fetched -> .served -> .status -> .pushed`;
* `latch` -- the capture latch of a write request;
* `complete` -- the request leaves the in-flight map and `used->idx` bumps;
* `drain` -- one cached sector reaches the durable image;
* `capture` -- one sector of a write request's payload enters the cache.
  The guard of that step is INSIDE the state update (`Virtio.xferOut`),
  so the relation may carry it: `h` is in flight with the request `r` the
  task holds, and the payload is one sector of it. -/
inductive diskRel : VirtioState → VirtioState → Prop where
  | refl (v : VirtioState) : diskRel v v
  | pop (v : VirtioState) (h : BitVec 16) (ph : VPhase) (hph : ph.req = none) :
      diskRel v { Virtio.setPhase v h ph with seen := v.seen + 1#16 }
  | install (v : VirtioState) (h : BitVec 16) (r : VioReq) (ph : VPhase) (hph : ph.req = some r) :
      diskRel v (Virtio.setPhase v h ph)
  | latch (v : VirtioState) (t : Option (BitVec 16)) : diskRel v { v with taken := t }
  | complete (v : VirtioState) (h : BitVec 16) : diskRel v (Virtio.complete v h)
  | drain (v : VirtioState) (k : Nat) : diskRel v (Virtio.drain v k)
  | capture (v : VirtioState) (h : BitVec 16) (r : VioReq) (i : Nat) (bs : List (BitVec 8))
      (hin : Virtio.reqOf v h = some r) (hlen : bs.length = Virtio.reqSectorLen r i) :
      diskRel v { v with cache := Virtio.alistSet v.cache (Virtio.reqKey r i) bs }

/-! ## Pure facts about the moves -/

theorem drain_cfg (v : VirtioState) (k : Nat) : (Virtio.drain v k).cfg = v.cfg := by
  unfold Virtio.drain; cases Virtio.alistGet v.cache k <;> rfl

theorem drain_usedIdx (v : VirtioState) (k : Nat) : (Virtio.drain v k).usedIdx = v.usedIdx := by
  unfold Virtio.drain; cases Virtio.alistGet v.cache k <;> rfl

theorem drain_inflight (v : VirtioState) (k : Nat) : (Virtio.drain v k).inflight = v.inflight := by
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

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [DiskG GF]

/-! ## The protocol survives a move that leaves the image alone -/

/-- The protocol is stated on four things only: the configuration, the
used index, the image a read sees, and the requests in flight.  A move
that leaves all four as they were (up to the stated implications) carries
the protocol over unchanged. -/
theorem diskProto_congr (γ : DiskNames) (v v' : VirtioState)
    (hcfg : v'.cfg = v.cfg) (hidx : v'.usedIdx = v.usedIdx)
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
  iintro ⟨%hc0, Harm⟩
  isplitl []
  · ipureintro; exact hck hc0
  icases Harm with ⟨Hd | ⟨%c0, #Hfr, %hc0', Hl⟩⟩
  · ileft
    unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, %hpure⟩
    obtain ⟨p1, p2, p3, p4⟩ := hpure
    iexists m
    rw [hcfg]
    iframe Hm Hcfg
    ipureintro
    refine ⟨p1, hni p2, hnil p3, ?_⟩
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
    obtain ⟨e1, e2, e3, e4⟩ := hpure
    iexists st, nc, np, ring, m
    iframe Hm Ha Hr Hu Hav Hnc Hnp
    ipureintro
    refine ⟨by rw [hidx]; exact e1, hfl st e2, ?_, hcd st e4⟩
    intro bno bs hb
    rcases e3 bno bs hb with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h, hblk])

/-- The common case: the move touches neither the cache nor the image. -/
theorem diskProto_congr_mem (γ : DiskNames) (v v' : VirtioState)
    (hcfg : v'.cfg = v.cfg) (hidx : v'.usedIdx = v.usedIdx)
    (hcache : v'.cache = v.cache) (hdisk : v'.disk = v.disk)
    (hfl : ∀ st, inflightOk v st → inflightOk v' st)
    (hni : noInflight v → noInflight v') :
    diskProto (GF := GF) γ v ⊢ diskProto γ v' :=
  diskProto_congr γ v v' hcfg hidx (by unfold Virtio.cacheView; rw [hcache, hdisk])
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

theorem diskProto_pop (γ : DiskNames) (v : VirtioState) (h : BitVec 16) (ph : VPhase)
    (hph : ph.req = none) :
    diskProto (GF := GF) γ v ⊢ diskProto γ { Virtio.setPhase v h ph with seen := v.seen + 1#16 } :=
  diskProto_congr_mem γ v _ rfl rfl rfl rfl
    (fun st hok k r hr => inflightOk_setPhase_none v st h ph hph hok k r hr)
    (fun hn k => noInflight_setPhase_none v h ph hph hn k)

/-! ### The capture latch -/

theorem diskProto_latch (γ : DiskNames) (v : VirtioState) (t : Option (BitVec 16)) :
    diskProto (GF := GF) γ v ⊢ diskProto γ { v with taken := t } :=
  diskProto_congr_mem γ v _ rfl rfl rfl rfl (fun _ h => h) (fun h => h)

/-! ### The drain -/

theorem diskProto_drain (γ : DiskNames) (v : VirtioState) (k : Nat) :
    diskProto (GF := GF) γ v ⊢ diskProto γ (Virtio.drain v k) := by
  iintro H
  ihave %hc := diskProto_cacheOk γ v $$ H
  iapply diskProto_congr γ v (Virtio.drain v k) (drain_cfg v k) (drain_usedIdx v k)
    (cacheView_drain v k hc)
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
  iintro ⟨%hc, Harm⟩
  isplitl []
  · ipureintro
    intro e he
    rcases setCache_mem v _ bs e he with rfl | he'
    · exact hbsle
    · exact hc e he'
  icases Harm with ⟨Hd | ⟨%c0, #Hfr, %hc0, Hl⟩⟩
  · unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, %hpure⟩
    obtain ⟨p1, p2, p3, p4⟩ := hpure
    rw [p2 h] at hin
    exact absurd hin (by simp)
  · unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %ring, %m, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, %hpure⟩
    obtain ⟨e1, e2, e3, e4⟩ := hpure
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
    exact ⟨e1, fun k rr hr => e2 k rr hr, key.1, key.2⟩

/-! ### The completion -/

theorem diskProto_complete (γ : DiskNames) (v : VirtioState) (h : BitVec 16) :
    diskProto (GF := GF) γ v ⊢ |==> diskProto γ (Virtio.complete v h) := by
  unfold diskProto
  iintro ⟨%hc, Harm⟩
  icases Harm with ⟨Hd | ⟨%c0, #Hfr, %hc0, Hl⟩⟩
  · imodintro
    isplitl []
    · ipureintro; exact hc
    ileft
    unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, %hpure⟩
    obtain ⟨p1, p2, p3, p4⟩ := hpure
    iexists m
    rw [show (Virtio.complete v h).cfg = v.cfg from rfl]
    iframe Hm Hcfg
    ipureintro
    exact ⟨p1, noInflight_complete v h p2, p3, p4⟩
  · unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %ring, %m, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, %hpure⟩
    obtain ⟨e1, e2, e3, e4⟩ := hpure
    unfold diskDoneAuth
    imod MonoNat.own_update γ.nc (.ofNat nc) (.ofNat (nc + 1))
      (by simp only [MaxNat.le_toNat]; omega) $$ Hnc with ⟨Hnc, _⟩
    imodintro
    isplitl []
    · ipureintro; exact hc
    iright
    iexists c0
    iframe Hfr
    isplitl []
    · ipureintro; exact hc0
    iexists st, nc + 1, np, ring, m
    iframe Hm Ha Hr Hu Hav Hnc Hnp
    ipureintro
    refine ⟨?_, inflightOk_complete v st h e2, e3, e4⟩
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
  iintro ⟨%hc, Harm⟩
  icases Harm with ⟨Hd | ⟨%c0, #Hfr, %hc0, Hl⟩⟩
  · unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, %hpure⟩
    rw [hpure.2.1 h] at hin
    exact absurd hin (by simp)
  · unfold diskLive
    icases Hl with ⟨%st, %nc, %np, %ring, %m, Hm, Ha, Hr, Hu, Hav, Hnc, Hnp, %hpure⟩
    obtain ⟨e1, e2, e3, e4⟩ := hpure
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
    · ipureintro; exact ⟨e1, e2, e3, e4⟩

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
  icases Hcl with ⟨H0, H1, H2, H3, Hstat, Hbuf⟩
  iapply dmaOwn_lease_frame c.status 1 w (diskProto γ s)
  isplitl [Hstat]
  · iexact Hstat
  · iintro Hstat2
    iapply Hback
    isplitl [H0 H1 H2 H3 Hstat2 Hbuf]
    · iframe H0 H1 H2 H3 Hstat2 Hbuf
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
  icases Hcl with ⟨H0, H1, H2, H3, Hstat, Hbuf⟩
  icases bufSector_acc c i hi $$ Hbuf with ⟨Hsec, Hsecb⟩
  iapply bufSector_lease c i (Virtio.reqSectorAddr (Chain.req c) i)
    (Virtio.reqSectorLen (Chain.req c) i) rfl hn w (diskProto γ s)
  isplitl [Hsec]
  · iexact Hsec
  · iintro Hsec2
    iapply Hback
    isplitl [H0 H1 H2 H3 Hstat Hsec2 Hsecb]
    · isplitl [H0]
      · iexact H0
      isplitl [H1]
      · iexact H1
      isplitl [H2]
      · iexact H2
      isplitl [H3]
      · iexact H3
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

/-! ## The assumed obligation -/

/-- **The one cross-step fact this port assumes.**

`Virtio.serve` reads the three descriptors of head `h` and its request
header at ONE state (`fetch`, five `dmaRead`s) and installs the parsed
request into the device's in-flight map SEVERAL STEPS LATER
(`DevM.modify (setPhase v h (.fetched r))`, and then `.served`, `.status`,
`.pushed`).  `MachCSL.DevM.Lease`'s `.step` arm obliges the client to show
`rel s s'` for EVERY state `s`, and `wpDev_dma`'s `hR` then has to move
the invariant along `rel` with NO access to the read values and no access
to the knowledge context `C` -- and `rel : S -> S -> Prop` could not
mention the chains even if it did, because the device's state does not
record the descriptor table.  So "the request the device installs at `h`
IS the chain the driver armed there" -- the `inflightOk` clause of
`diskLive`, Rocq's `virtio_proto_fetch_step`, which Rocq discharges at a
single state because its model is a step relation -- cannot be
established here and is assumed.

Everything else is proved: the pop, the capture latch, the completion,
the drain, the payload capture, and all four DMA-write leases.

Closing this gap needs a device-program WP with a LINEAR precondition
threaded through the program (so that the task can carry the exclusive
receipt `headTok γ h (.active c)` it obtained at its fetch), in place of
`DevM.Lease`'s persistent knowledge context. -/
structure DISK_LEASE_ASSUMPTIONS (γ : DiskNames) : Prop where
  proto_install : ∀ (v : VirtioState) (h : BitVec 16) (r : VioReq) (ph : VPhase),
    ph.req = some r → diskProto (GF := GF) γ v ⊢ |==> diskProto γ (Virtio.setPhase v h ph)

/-- **The protocol survives every move of the device.** -/
theorem diskProto_step (γ : DiskNames) (HA : DISK_LEASE_ASSUMPTIONS (GF := GF) γ)
    (v v' : VirtioState) (hrel : diskRel v v') :
    diskProto (GF := GF) γ v ⊢ |==> diskProto γ v' := by
  cases hrel with
  | refl => iintro H; imodintro; iexact H
  | pop h ph hph => iintro H; imodintro; iapply diskProto_pop γ v h ph hph $$ H
  | install h r ph hph => exact HA.proto_install v h r ph hph
  | latch t => iintro H; imodintro; iapply diskProto_latch γ v t $$ H
  | complete h => exact diskProto_complete γ v h
  | drain k => iintro H; imodintro; iapply diskProto_drain γ v k $$ H
  | capture h r i bs hin hlen =>
    iintro H; imodintro; iapply diskProto_capture γ v h r i bs hin hlen $$ H

/-! ## Prefixes that touch nothing -/

end

/-- A device program built only from `fork`, `join`, `choose` and
`sample`: it moves no state, performs no bus transaction and reads no
state, so it may be prefixed to any leased continuation.  This is what
`DevM.forkJoinAll` is. -/
inductive PlainOps {S T : Type} : ∀ {α : Type}, DevM S T α → Prop where
  | pure {α : Type} (a : α) : PlainOps (.pure a)
  | op {α : Type} (o : DevOp S T) (k : o.ret → DevM S T α)
      (hw : ∀ g pa n w, o ≠ .dmaWrite g pa n w) (hr : ∀ pa n, o ≠ .dmaRead pa n)
      (hg : o ≠ .get) (hp : ∀ c mm b, o ≠ .setPin c mm b) (hs : ∀ g, o ≠ .step g)
      (hk : ∀ r, PlainOps (k r)) : PlainOps (.op o k)

/-- A device program whose only state updates stay inside `rel`, and which
performs no bus transaction and reads no state: the capture phase of
`Virtio.serve` (a guard, then a fork/join fan-out) is one. -/
inductive RelOps {S T : Type} (rel : S → S → Prop) : ∀ {α : Type}, DevM S T α → Prop where
  | pure {α : Type} (a : α) : RelOps rel (.pure a)
  | op {α : Type} (o : DevOp S T) (k : o.ret → DevM S T α)
      (hw : ∀ g pa n w, o ≠ .dmaWrite g pa n w) (hr : ∀ pa n, o ≠ .dmaRead pa n)
      (hg : o ≠ .get) (hp : ∀ c mm b, o ≠ .setPin c mm b)
      (hs : ∀ g, o = .step g → ∀ s s' os, g s = some (s', os) → rel s s')
      (hk : ∀ r, RelOps rel (k r)) : RelOps rel (.op o k)

theorem plainOps_relOps {S T : Type} {α : Type} (rel : S → S → Prop) (m : DevM S T α)
    (h : PlainOps m) : RelOps rel m := by
  induction h with
  | pure a => exact .pure a
  | op o k hw hr hg hp hs _ ih => exact .op o k hw hr hg hp (fun g hq => absurd hq (hs g)) ih

theorem relOps_bind {S T : Type} {α β : Type} (rel : S → S → Prop) (m : DevM S T α)
    (hm : RelOps rel m) (k : α → DevM S T β) (hk : ∀ a, RelOps rel (k a)) :
    RelOps rel (DevM.bind m k) := by
  induction hm with
  | pure a => exact hk a
  | op o k' hw hr hg hp hs _ ih => exact .op o _ hw hr hg hp hs ih

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

theorem plain_mapM_fork {S T : Type} (ts : List T) (acc : List TaskId) :
    PlainOps (S := S) (List.mapM.loop DevM.fork ts acc) := by
  induction ts generalizing acc with
  | nil => exact .pure _
  | cons t ts ih =>
    exact PlainOps.op (.fork t) _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
      (fun _ _ _ => nofun) (fun _ => nofun) (fun r => ih (r :: acc))

theorem plain_forM_join {S T : Type} (l : List TaskId) :
    PlainOps (S := S) (T := T) (List.forM l DevM.join) := by
  induction l with
  | nil => exact .pure _
  | cons t l ih =>
    exact PlainOps.op (.join t) _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
      (fun _ _ _ => nofun) (fun _ => nofun) (fun _ => ih)

theorem plain_bind {S T : Type} {α β : Type} (m : DevM S T α) (hm : PlainOps m)
    (k : α → DevM S T β) (hk : ∀ a, PlainOps (k a)) : PlainOps (DevM.bind m k) := by
  induction hm with
  | pure a => exact hk a
  | op o k' hw hr hg hp hs _ ih => exact .op o _ hw hr hg hp hs ih

theorem plain_forkJoinAll {S T : Type} (ts : List T) : PlainOps (S := S) (DevM.forkJoinAll ts) :=
  plain_bind _ (plain_mapM_fork ts []) _ (fun l => plain_forM_join l)

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [DiskG GF]

theorem lease_bind_plain {S T : Type} {α : Type} (rel : S → S → Prop) (R : S → IProp GF)
    (C : IProp GF) (m : DevM S T α) (hm : PlainOps m) (k : α → DevM S T Unit)
    (hk : ∀ a, DevM.Lease rel R C (k a)) : DevM.Lease rel R C (DevM.bind m k) := by
  induction hm with
  | pure a => exact hk a
  | op o k' hw hr hg hp hs _ ih =>
    exact DevM.Lease.op C o _ hw hr hg hp (fun g h => absurd h (hs g)) ih

theorem lease_bind_rel {S T : Type} {α : Type} (rel : S → S → Prop) (R : S → IProp GF)
    (C : IProp GF) (m : DevM S T α) (hm : RelOps rel m) (k : α → DevM S T Unit)
    (hk : ∀ a, DevM.Lease rel R C (k a)) : DevM.Lease rel R C (DevM.bind m k) := by
  induction hm with
  | pure a => exact hk a
  | op o k' hw hr hg hp hs _ ih => exact DevM.Lease.op C o _ hw hr hg hp hs ih

theorem lease_forkJoinAll {S T : Type} (rel : S → S → Prop) (R : S → IProp GF) (C : IProp GF)
    (ts : List T) (k : Unit → DevM S T Unit) (hk : DevM.Lease rel R C (k ())) :
    DevM.Lease rel R C (DevM.bind (DevM.forkJoinAll ts) k) := by
  show DevM.Lease rel R C
    (DevM.bind (DevM.bind (List.mapM.loop DevM.fork ts []) (fun l => List.forM l DevM.join)) k)
  rw [DevM_bind_assoc]
  refine lease_bind_plain rel R C _ (plain_mapM_fork ts []) _ (fun l => ?_)
  exact lease_bind_plain rel R C _ (plain_forM_join l) _ (fun u => by cases u; exact hk)

/-! ## The lease derivations -/

/-- Dropping the knowledge context: none of the disk's obligations uses it. -/
theorem lease_dropC (C P Q : IProp GF) (h : P ⊢ Q) : iprop(C ∗ P) ⊢ Q := by
  iintro ⟨_, HP⟩
  iapply h $$ HP

/-- Reading the device's state tells the disk nothing it does not already
know: every obligation below is discharged from the invariant and the
write guard alone. -/
theorem lease_know (C : IProp GF) (R : VirtioState → IProp GF) (s : VirtioState) :
    iprop(C ∗ R s) ⊢ iprop(R s ∗ True) := by
  iintro ⟨_, HR⟩
  iframe HR

/-- `Virtio.xferIn h i`: one sector of a read request's fill. -/
theorem lease_xferIn (γ : DiskNames) (C : IProp GF) (h : BitVec 16) (i : Nat) :
    DevM.Lease diskRel (diskProto (GF := GF) γ) C (Virtio.xferIn h i) := by
  unfold Virtio.xferIn
  simp only [bind, DevM.bind, DevM.get, DevM.lift, Pure.pure]
  refine DevM.Lease.get C (fun _ => iprop(True)) (fun _ => inferInstance) _
    (fun s => lease_know C _ s) (fun s => ?_)
  cases hr : Virtio.reqOf s h with
  | none => exact DevM.Lease.pure _ ()
  | some r =>
    unfold Virtio.reqSectorLen DevM.dmaWriteIf DevM.lift
    refine DevM.Lease.dmaWrite _ _ _ _ _ _ ?_ (DevM.Lease.pure _ ())
    intro s' hg
    refine lease_dropC _ _ _ ?_
    exact data_write_lease γ s' h r i (of_decide_eq_true hg) _

/-- `Virtio.xferOut h i`: one sector of a write request's capture.  The
read is unconstrained -- the device puts what it reads into its cache,
and the invariant exempts an in-flight block from the image coupling --
and the cache update is the `capture` arm of `diskRel`, whose guard is
part of the state update itself. -/
theorem lease_xferOut (γ : DiskNames) (C : IProp GF) (h : BitVec 16) (i : Nat) :
    DevM.Lease diskRel (diskProto (GF := GF) γ) C (Virtio.xferOut h i) := by
  unfold Virtio.xferOut
  simp only [bind, DevM.bind, DevM.get, DevM.lift, Pure.pure]
  refine DevM.Lease.get C (fun _ => iprop(True)) (fun _ => inferInstance) _
    (fun s => lease_know C _ s) (fun s => ?_)
  cases hr : Virtio.reqOf s h with
  | none => exact DevM.Lease.pure _ ()
  | some r =>
    unfold DevM.dmaRead DevM.lift
    refine DevM.Lease.dmaRead _ _ _ (fun _ _ => True) _
      (fun s' => lease_dropC _ _ _ (dmaReadPin_any _ _ _)) (fun w => ?_)
    unfold DevM.modify DevM.step DevM.lift
    refine DevM.Lease.op _ _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
      (fun _ _ _ => nofun) ?_ (fun _ => DevM.Lease.pure _ ())
    intro g hg s1 s2 os hgs
    cases hg
    have hs2 : s2 = (if Virtio.reqOf s1 h = some r then
        { s1 with cache := Virtio.alistSet s1.cache (Virtio.reqKey r i) (bytesOf w) }
        else s1) := by
      simp only [Option.some.injEq, Prod.mk.injEq] at hgs
      exact hgs.1.symm
    subst hs2
    by_cases hc : Virtio.reqOf s1 h = some r
    · rw [if_pos hc]
      exact diskRel.capture s1 h r i (bytesOf w) hc (by simp [bytesOf])
    · rw [if_neg hc]
      exact diskRel.refl s1

/-- `Virtio.body`: the root loop. -/
theorem lease_body (γ : DiskNames) (C : IProp GF) :
    DevM.Lease diskRel (diskProto (GF := GF) γ) C Virtio.body := by
  unfold Virtio.body DevM.chooseLt DevM.choose DevM.get DevM.modify DevM.step DevM.lift
    Virtio.dma16 DevM.dmaRead DevM.fork
  simp only [bind, DevM.bind, Pure.pure]
  refine DevM.Lease.op C _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
    (fun _ _ _ => nofun) (fun _ hq => nomatch hq) (fun kk => ?_)
  split
  · refine DevM.Lease.get _ (fun _ => iprop(True)) (fun _ => inferInstance) _
      (fun s => lease_know _ _ s) (fun v => ?_)
    split
    · refine DevM.Lease.dmaRead _ _ _ (fun _ _ => True) _
        (fun s => lease_dropC _ _ _ (dmaReadPin_any _ _ _)) (fun ai => ?_)
      simp only [bind, DevM.bind, Pure.pure]
      split
      · refine DevM.Lease.dmaRead _ _ _ (fun _ _ => True) _
          (fun s => lease_dropC _ _ _ (dmaReadPin_any _ _ _)) (fun hw => ?_)
        simp only [bind, DevM.bind, Pure.pure]
        refine DevM.Lease.get _ (fun _ => iprop(True)) (fun _ => inferInstance) _
          (fun s => lease_know _ _ s) (fun popped => ?_)
        split
        · exact DevM.Lease.pure _ ()
        · refine DevM.Lease.op _ _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
            (fun _ _ _ => nofun) ?_ (fun _ => ?_)
          · intro g hg s1 s2 os hgs
            cases hg
            have hs2 : s2 = { Virtio.setPhase s1 (hw.extractLsb' 0 16) .popped with
                seen := s1.seen + 1#16 } := by
              simp only [Option.some.injEq, Prod.mk.injEq] at hgs
              exact hgs.1.symm
            subst hs2
            exact diskRel.pop s1 _ .popped rfl
          · exact DevM.Lease.op _ _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
              (fun _ _ _ => nofun) (fun _ hq => nomatch hq) (fun _ => DevM.Lease.pure _ ())
      · exact DevM.Lease.pure _ ()
    · exact DevM.Lease.pure _ ()
  · split
    · refine DevM.Lease.get _ (fun _ => iprop(True)) (fun _ => inferInstance) _
        (fun s => lease_know _ _ s) (fun v => ?_)
      split
      · exact DevM.Lease.pure _ ()
      · refine DevM.Lease.op _ _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
          (fun _ _ _ => nofun) (fun _ hq => nomatch hq) (fun j => ?_)
        refine DevM.Lease.op _ _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
          (fun _ _ _ => nofun) ?_ (fun _ => DevM.Lease.pure _ ())
        intro g hg s1 s2 os hgs
        cases hg
        have hs2 : s2 = Virtio.drain s1 (s1.cache.getD (j % v.cache.length) (0, [])).1 := by
          simp only [Option.some.injEq, Prod.mk.injEq] at hgs
          exact hgs.1.symm
        subst hs2
        exact diskRel.drain s1 _
    · exact DevM.Lease.pure _ ()

/-- `Virtio.fetch`: the five bus reads that parse the chain at `h`.  Every
one of them is UNPINNED (`dmaReadPin`'s trivial arm): the device may read
anything, and what it does with the answer is constrained by the guards of
its later writes, not by the answer. -/
theorem lease_fetch (γ : DiskNames) (c : VirtioCfg) (h : BitVec 16)
    (k : Option VioReq → Virtio.VM Unit)
    (hk : ∀ (C : IProp GF) (o : Option VioReq), DevM.Lease diskRel (diskProto γ) C (k o))
    (C : IProp GF) :
    DevM.Lease diskRel (diskProto (GF := GF) γ) C (DevM.bind (Virtio.fetch c h) k) := by
  unfold Virtio.fetch DevM.dmaRead DevM.lift
  simp only [bind, DevM.bind, Pure.pure]
  split
  · exact hk _ none
  · refine DevM.Lease.dmaRead _ _ _ (fun _ _ => True) _
      (fun s => lease_dropC _ _ _ (dmaReadPin_any _ _ _)) (fun w0 => ?_)
    simp only [bind, DevM.bind, Pure.pure]
    split
    · exact hk _ none
    · refine DevM.Lease.dmaRead _ _ _ (fun _ _ => True) _
        (fun s => lease_dropC _ _ _ (dmaReadPin_any _ _ _)) (fun w1 => ?_)
      simp only [bind, DevM.bind, Pure.pure]
      split
      · exact hk _ none
      · refine DevM.Lease.dmaRead _ _ _ (fun _ _ => True) _
          (fun s => lease_dropC _ _ _ (dmaReadPin_any _ _ _)) (fun w2 => ?_)
        simp only [bind, DevM.bind, Pure.pure]
        split
        · exact hk _ none
        · refine DevM.Lease.dmaRead _ _ _ (fun _ _ => True) _
            (fun s => lease_dropC _ _ _ (dmaReadPin_any _ _ _)) (fun ty => ?_)
          simp only [bind, DevM.bind, Pure.pure]
          refine DevM.Lease.dmaRead _ _ _ (fun _ _ => True) _
            (fun s => lease_dropC _ _ _ (dmaReadPin_any _ _ _)) (fun sec => ?_)
          exact hk _ _

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


theorem lease_serveTail (γ : DiskNames) (C : IProp GF) (h : BitVec 16) (r : VioReq) :
    DevM.Lease diskRel (diskProto (GF := GF) γ) C (serveTail h r) := by
  unfold serveTail
  simp only [bind, DevM.bind, DevM.modify, DevM.guard, DevM.step, DevM.lift,
    DevM.dmaWriteIf, DevM.get, Pure.pure]
  refine DevM.Lease.op _ _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
    (fun _ _ _ => nofun) ?_ (fun _ => ?_)
  · intro g hq s1 s2 os hgs
    cases hq
    have hs2 : s2 = Virtio.setPhase s1 h (.served r) := by
      simp only [Option.some.injEq, Prod.mk.injEq] at hgs
      exact hgs.1.symm
    subst hs2
    exact diskRel.install s1 h r (.served r) rfl
  · refine DevM.Lease.dmaWrite _ _ _ _ _ _ ?_ ?_
    · intro s1 hgg
      refine lease_dropC _ _ _ ?_
      exact status_write_lease γ s1 h r (of_decide_eq_true hgg) _
    · refine DevM.Lease.op _ _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
        (fun _ _ _ => nofun) ?_ (fun _ => ?_)
      · intro g hq s1 s2 os hgs
        cases hq
        have hs2 : s2 = Virtio.setPhase s1 h (.status r) := by
          simp only [Option.some.injEq, Prod.mk.injEq] at hgs
          exact hgs.1.symm
        subst hs2
        exact diskRel.install s1 h r (.status r) rfl
      · refine DevM.Lease.op _ _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
          (fun _ _ _ => nofun) ?_ (fun _ => ?_)
        · intro g hq s1 s2 os hgs
          cases hq
          have hgs' := guard_step_inv _ s2 os hgs
          replace hgs' : (if ((Virtio.phase s1 h).isSome && Virtio.completeOk s1 r h &&
              Virtio.pushOk s1) = true then some (Virtio.setPhase s1 h (.pushed r))
              else none) = some s2 := hgs'
          split at hgs'
          · have hs2 : s2 = Virtio.setPhase s1 h (.pushed r) := by
              simp only [Option.some.injEq] at hgs'; exact hgs'.symm
            subst hs2
            exact diskRel.install s1 h r (.pushed r) rfl
          · exact absurd hgs' (by simp)
        · refine DevM.Lease.get _ (fun _ => iprop(True)) (fun _ => inferInstance) _
            (fun s => lease_know _ _ s) (fun v2 => ?_)
          refine DevM.Lease.dmaWrite _ _ _ _ _ _ ?_ ?_
          · intro s1 hgg
            refine lease_dropC _ _ _ ?_
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hgg
            exact usedElem_write_lease γ s1 h r v2.cfg v2.usedIdx hgg.1.1 hgg.2 _
          · refine DevM.Lease.dmaWrite _ _ _ _ _ _ ?_ ?_
            · intro s1 hgg
              refine lease_dropC _ _ _ ?_
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hgg
              exact usedIdx_write_lease γ s1 h r v2.cfg hgg.1.1 hgg.2 _
            · refine DevM.Lease.op _ _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
                (fun _ _ _ => nofun) ?_ (fun _ => DevM.Lease.pure _ ())
              intro g hq s1 s2 os hgs
              cases hq
              have hs2 : s2 = Virtio.complete s1 h := by
                simp only [Option.some.injEq, Prod.mk.injEq] at hgs
                exact hgs.1.symm
              subst hs2
              exact diskRel.complete s1 h

/-- The capture latch of a write request is a `latch` move. -/
theorem relOps_latch (h : BitVec 16) :
    RelOps diskRel (DevM.guard (T := Virtio.VTask)
      (fun v => if v.taken = none then some { v with taken := some h } else none)) := by
  refine RelOps.op _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
    (fun _ _ _ => nofun) ?_ (fun _ => RelOps.pure ())
  intro g hq s1 s2 os hgs
  cases hq
  have hgs' := guard_step_inv _ s2 os hgs
  replace hgs' : (if s1.taken = none then some { s1 with taken := some h }
      else none) = some s2 := hgs'
  split at hgs'
  · have hs2 : s2 = { s1 with taken := some h } := by
      simp only [Option.some.injEq] at hgs'; exact hgs'.symm
    subst hs2
    exact diskRel.latch s1 (some h)
  · exact absurd hgs' (by simp)

/-- `Virtio.serve h`: the whole service of one popped request. -/
theorem lease_serve (γ : DiskNames) (C : IProp GF) (h : BitVec 16) :
    DevM.Lease diskRel (diskProto (GF := GF) γ) C (Virtio.serve h) := by
  unfold Virtio.serve
  simp only [bind, DevM.bind, DevM.get, DevM.lift]
  refine DevM.Lease.get C (fun _ => iprop(True)) (fun _ => inferInstance) _
    (fun s => lease_know _ _ s) (fun v => ?_)
  refine lease_fetch γ v.cfg h _ (fun C' o => ?_) _
  cases o with
  | none =>
    unfold Virtio.stall DevM.await DevM.step DevM.lift
    exact DevM.Lease.op _ _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
      (fun _ _ _ => nofun) (fun g hq s s' os hgs => by cases hq; simp at hgs)
      (fun _ => DevM.Lease.pure _ ())
  | some r =>
    simp only [bind, DevM.bind, DevM.modify, DevM.step, DevM.lift, Pure.pure]
    refine DevM.Lease.op _ _ _ (fun _ _ _ _ => nofun) (fun _ _ => nofun) nofun
      (fun _ _ _ => nofun) ?_ (fun _ => ?_)
    · intro g hq s1 s2 os hgs
      cases hq
      have hs2 : s2 = Virtio.setPhase s1 h (.fetched r) := by
        simp only [Option.some.injEq, Prod.mk.injEq] at hgs
        exact hgs.1.symm
      subst hs2
      exact diskRel.install s1 h r (.fetched r) rfl
    · split
      · have hR : RelOps diskRel
            (DevM.bind (DevM.guard (T := Virtio.VTask)
              (fun v => if v.taken = none then some { v with taken := some h } else none))
              (fun _ => DevM.forkJoinAll
                ((List.range (Virtio.reqSpan r)).map (Virtio.VTask.xferOut h)))) :=
          relOps_bind _ _ (relOps_latch h) _
            (fun _ => plainOps_relOps _ _ (plain_forkJoinAll _))
        exact lease_bind_rel diskRel (diskProto γ) _ _ hR (fun _ => serveTail h r)
          (fun _ => lease_serveTail γ _ h r)
      · split
        · have hR : RelOps diskRel
              (DevM.forkJoinAll
                ((List.range (Virtio.reqSpan r)).map (Virtio.VTask.xferIn h))) :=
            plainOps_relOps _ _ (plain_forkJoinAll _)
          exact lease_bind_rel diskRel (diskProto γ) _ _ hR (fun _ => serveTail h r)
            (fun _ => lease_serveTail γ _ h r)
        · exact lease_serveTail γ _ h r

/-! ## The device-side theorem -/

/-- **The disk's programs respect the invariant**: every DMA write is
covered by a lease out of `diskProto`, every DMA read is admissible, and
every move of the device's own state stays inside `diskRel`. -/
theorem disk_lease (γ : DiskNames) : DevSig.Lease .virtio diskRel (diskProto (GF := GF) γ) := by
  refine ⟨lease_body γ _, fun t => ?_⟩
  cases t with
  | serve h => exact lease_serve γ _ h
  | xferIn h i => exact lease_xferIn γ _ h i
  | xferOut h i => exact lease_xferOut γ _ h i

/-- **The disk's device thread is safe under its invariant** -- the
instance of `MachCSL.wpDev_dma` the adequacy theorem forks. -/
theorem wpDev_disk_inv (γ : DiskNames) (HA : DISK_LEASE_ASSUMPTIONS (GF := GF) γ) :
    diskInv γ ∗ genCert ⊢@{IProp GF}
      devWP (genId (hlc := hlc) (GF := GF)) .virtio rootTask (DevM.pure ()) := by
  unfold diskInv
  iintro H
  iapply wpDev_dma_root diskN .virtio diskRel (diskProto γ) (disk_lease γ)
    (fun s s' hrel => diskProto_step γ HA s s' hrel) $$ H

end

end Xv6
