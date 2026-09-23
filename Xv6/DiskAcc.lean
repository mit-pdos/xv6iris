/-
The virtio disk driver's ACCESSORS: one lemma per kind of memory access
the driver makes, each of the form

    <credentials>  ⊢  devReadAU / devWriteAU ...        (MMIO)
    <credentials>  ⊢  readAU / writeAU ...              (queue memory)

so that a driver proof discharges an instruction rule
(`MachCSL.wp_s_lw_dev`, `wp_s_sw_dev`, `wp_s_lhu_au`, `wp_s_sh_au`, ...)
by handing it the accessor as the rule's `Ψ`-argument -- exactly the way
`Xv6/UartInv.lean`'s `lsr_read_au` / `thr_write_au` serve the console.

This file is DEFINITIONAL: it may be imported by the `Spec*` layer and by
the `Proof*` files of `virtio_disk_init` / `_rw` / `_intr`; it imports
`Xv6/DiskInv.lean` (the invariant and its device-side lease proof) and
`MachCSL/WpDmaCtx.lean` (the raw/context tier conversions) and nothing
from the code or proof layers.

THE TWO TIERS AGAIN.  `Xv6/DiskInvDefs.lean` puts everything the device
may touch at the RAW history tier inside `diskInv`, and everything the
driver reads or writes at the CONTEXT tier inside the lock payload
`diskRes`.  A cell BOTH of them see (a descriptor word, an avail-ring
cell, `avail->idx`) is split in halves: the invariant's half is a
`dmaHalfAt`, the driver's half a `ctxBytes ... (own ½)`.  So

* a driver READ of a shared cell needs only the driver's half, and goes
  through the ordinary points-to rules -- no accessor (see
  `diskRes_availIdx_acc`);
* a driver WRITE of a shared cell needs BOTH halves, so it opens the
  invariant: `writeAU`, with `MachCSL.rawHalf_ctxHalf_join` to fuse the
  two halves into the `own 1` raw window the accessor must hand out, and
  `MachCSL.ctxBytes_of_pushed` to rebuild the driver's half from the
  history the store pushed;
* a driver READ of a cell that is ENTIRELY the device's (`used->idx`,
  `used->ring[..]`, `info[h].status`) opens the invariant with `readAU`.
-/
import Xv6.DiskInv
import MachCSL.WpDmaCtx
import MachCSL.WpSmodeDev4
import MachCSL.WpSmodeAuRules
import Xv6.PtOwnLemmas

namespace Xv6

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [DiskG GF]

/-! ## The MMIO window, as the fabric sees it

The device signature's `read`/`write` are `Virtio.readN`/`writeN`, which
accept 4-byte accesses only.  These two lemmas are the bridge from the
model's 32-bit `Virtio.read`/`Virtio.write` to them. -/

theorem virtio_readN4 (v : VirtioState) (off : Nat) (w : BitVec 32)
    (h : Virtio.read v off = some w) :
    (devSig .virtio).read v off 4 = some (w, v) := by
  show Virtio.readN v off 4 = _
  unfold Virtio.readN
  rw [dif_pos rfl, h]
  rfl

theorem virtio_writeN4 (v v' : VirtioState) (off : Nat) (w : BitVec 32)
    (h : Virtio.write v off w = some v') :
    (devSig .virtio).write v off 4 w = some v' := by
  show Virtio.writeN v off 4 w = _
  unfold Virtio.writeN
  rw [dif_pos rfl]
  exact h

/-! ## The registers `virtio_disk_init` reads

Each is a function of the CONFIGURATION alone (the identification
registers are constants), which is what makes the driver's tracker
`diskCfgOwn` enough to predict the value. -/

theorem vread_magic (v : VirtioState) :
    Virtio.read v Virtio.offMagicValue = some (BitVec.ofNat 32 Virtio.magicValue) := rfl

theorem vread_version (v : VirtioState) :
    Virtio.read v Virtio.offVersion = some (BitVec.ofNat 32 Virtio.version) := rfl

theorem vread_deviceId (v : VirtioState) :
    Virtio.read v Virtio.offDeviceId = some (BitVec.ofNat 32 Virtio.blkDeviceId) := rfl

theorem vread_vendorId (v : VirtioState) :
    Virtio.read v Virtio.offVendorId = some (BitVec.ofNat 32 Virtio.vendorId) := rfl

theorem vread_deviceFeatures (v : VirtioState) :
    Virtio.read v Virtio.offDeviceFeatures =
      some (BitVec.ofNat 32 (if v.cfg.devfsel = 0#32 then Virtio.deviceFeatures
        else if v.cfg.devfsel = 1#32 then Virtio.deviceFeaturesHi else 0)) := rfl

theorem vread_status (v : VirtioState) : Virtio.read v Virtio.offStatus = some v.cfg.status := rfl

theorem vread_queueReady (v : VirtioState) :
    Virtio.read v Virtio.offQueueReady =
      some (if v.cfg.qsel = 0#32 && v.cfg.ready then 1#32 else 0#32) := rfl

theorem vread_queueNumMax (v : VirtioState) :
    Virtio.read v Virtio.offQueueNumMax =
      some (BitVec.ofNat 32 (if v.cfg.qsel = 0#32 then Virtio.queueNumMax else 0)) := rfl

theorem vread_isr (v : VirtioState) :
    Virtio.read v Virtio.offInterruptStatus = some v.isr := rfl

/-! ## The registers `virtio_disk_init` writes -/

theorem vwrite_status_reset (v : VirtioState) :
    Virtio.write v Virtio.offStatus 0#32 = some (Virtio.reset v) := rfl

theorem vwrite_status_set (v : VirtioState) (w : BitVec 32) (hw : w ≠ 0#32) :
    Virtio.write v Virtio.offStatus w = some { v with cfg := { v.cfg with status := w } } := by
  show (if w = 0#32 then _ else _) = _
  rw [if_neg hw]

theorem vwrite_devFeatSel (v : VirtioState) (w : BitVec 32) :
    Virtio.write v Virtio.offDeviceFeaturesSel w =
      some { v with cfg := { v.cfg with devfsel := w } } := rfl

theorem vwrite_drvFeatSel (v : VirtioState) (w : BitVec 32) :
    Virtio.write v Virtio.offDriverFeaturesSel w =
      some { v with cfg := { v.cfg with dfsel := w } } := rfl

theorem vwrite_drvFeat0 (v : VirtioState) (w : BitVec 32) (h : v.cfg.dfsel = 0#32) :
    Virtio.write v Virtio.offDriverFeatures w =
      some { v with cfg := { v.cfg with dfeat := w } } := by
  show (if v.cfg.dfsel = 0#32 then _ else _) = _
  rw [if_pos h]

theorem vwrite_queueSel (v : VirtioState) (w : BitVec 32) :
    Virtio.write v Virtio.offQueueSel w = some { v with cfg := { v.cfg with qsel := w } } := rfl

theorem vwrite_queueNum (v : VirtioState) (w : BitVec 32) (h0 : v.cfg.qsel = 0#32)
    (hq : Virtio.qsizeOk w.toNat = true) :
    Virtio.write v Virtio.offQueueNum w = some { v with cfg := { v.cfg with qnum := w } } := by
  show (if !(decide (v.cfg.qsel = 0#32)) then _ else if !Virtio.qsizeOk w.toNat then _ else _) = _
  rw [h0, hq]
  simp
  exact h0.symm

theorem vwrite_queueReady (v : VirtioState) (w : BitVec 32) (h0 : v.cfg.qsel = 0#32) :
    Virtio.write v Virtio.offQueueReady w =
      some { v with cfg := { v.cfg with ready := w ≠ 0#32 } } := by
  show (if !(decide (v.cfg.qsel = 0#32)) then _ else _) = _
  rw [h0]
  simp
  exact h0.symm

theorem vwrite_descLo (v : VirtioState) (w : BitVec 32) (h0 : v.cfg.qsel = 0#32) :
    Virtio.write v Virtio.offQueueDescLow w =
      some { v with cfg := { v.cfg with desc := Virtio.setLo v.cfg.desc w } } := by
  show (if !(decide (v.cfg.qsel = 0#32)) then _ else _) = _
  rw [h0]; simp; exact h0.symm

theorem vwrite_descHi (v : VirtioState) (w : BitVec 32) (h0 : v.cfg.qsel = 0#32) :
    Virtio.write v Virtio.offQueueDescHigh w =
      some { v with cfg := { v.cfg with desc := Virtio.setHi v.cfg.desc w } } := by
  show (if !(decide (v.cfg.qsel = 0#32)) then _ else _) = _
  rw [h0]; simp; exact h0.symm

theorem vwrite_availLo (v : VirtioState) (w : BitVec 32) (h0 : v.cfg.qsel = 0#32) :
    Virtio.write v Virtio.offDriverDescLow w =
      some { v with cfg := { v.cfg with avail := Virtio.setLo v.cfg.avail w } } := by
  show (if !(decide (v.cfg.qsel = 0#32)) then _ else _) = _
  rw [h0]; simp; exact h0.symm

theorem vwrite_availHi (v : VirtioState) (w : BitVec 32) (h0 : v.cfg.qsel = 0#32) :
    Virtio.write v Virtio.offDriverDescHigh w =
      some { v with cfg := { v.cfg with avail := Virtio.setHi v.cfg.avail w } } := by
  show (if !(decide (v.cfg.qsel = 0#32)) then _ else _) = _
  rw [h0]; simp; exact h0.symm

theorem vwrite_usedLo (v : VirtioState) (w : BitVec 32) (h0 : v.cfg.qsel = 0#32) :
    Virtio.write v Virtio.offDeviceDescLow w =
      some { v with cfg := { v.cfg with used := Virtio.setLo v.cfg.used w } } := by
  show (if !(decide (v.cfg.qsel = 0#32)) then _ else _) = _
  rw [h0]; simp; exact h0.symm

theorem vwrite_usedHi (v : VirtioState) (w : BitVec 32) (h0 : v.cfg.qsel = 0#32) :
    Virtio.write v Virtio.offDeviceDescHigh w =
      some { v with cfg := { v.cfg with used := Virtio.setHi v.cfg.used w } } := by
  show (if !(decide (v.cfg.qsel = 0#32)) then _ else _) = _
  rw [h0]; simp; exact h0.symm

theorem vwrite_notify (v : VirtioState) (w : BitVec 32) :
    Virtio.write v Virtio.offQueueNotify w = some v := rfl

theorem vwrite_ack (v : VirtioState) (w : BitVec 32) :
    Virtio.write v Virtio.offInterruptAck w = some { v with isr := v.isr &&& ~~~w } := rfl

/-! ## The configuration tracker -/

/-- The invariant's half and the driver's half agree. -/
theorem diskCfg_auth_own_agree (γ : DiskNames) (c c' : VirtioCfg) :
    ⊢@{IProp GF} diskCfgAuth γ c' -∗ diskCfgOwn γ c -∗ ⌜c' = c⌝ := by
  unfold diskCfgAuth diskCfgOwn
  iintro H1 H2
  ihave %h := ghost_var_agree γ.cfg _ _ _ _ $$ H1 H2
  ipureintro; exact h

/-- The FROZEN configuration and the driver's half agree: holding
`diskCfgOwn γ c` with `live c = false` after the device has gone live is
impossible, which is what refutes the live arm in every dead accessor. -/
theorem diskCfg_frozen_own_agree (γ : DiskNames) (c c' : VirtioCfg) :
    ⊢@{IProp GF} diskCfgFrozen γ c' -∗ diskCfgOwn γ c -∗ ⌜c' = c⌝ := by
  unfold diskCfgFrozen diskCfgOwn
  iintro H1 H2
  ihave %h := ghost_var_agree γ.cfg _ _ _ _ $$ H1 H2
  ipureintro; exact h

/-- **Opening the DEAD arm.**  The driver's tracker at a configuration the
device is not live at pins the device's state to the pre-`DRIVER_OK`
world: its configuration is the tracker's, no request is in flight and
the write-back cache is empty. -/
theorem diskProto_dead_pure (γ : DiskNames) (v : VirtioState) (c : VirtioCfg)
    (hdead : Virtio.live c = false) :
    diskProto (GF := GF) γ v ∗ diskCfgOwn γ c ⊢
      ⌜v.cfg = c ∧ noInflight v ∧ v.cache = []⌝ := by
  unfold diskProto
  iintro ⟨⟨%hco, %pn, %pm, Hpm, %hfr, Harm⟩, Htok⟩
  icases Harm with ⟨Hd | ⟨%c0, #Hfr, %hc0, Hl⟩⟩
  · unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, %hp⟩
    ihave %he := diskCfg_auth_own_agree γ c v.cfg $$ Hcfg Htok
    ipureintro
    exact ⟨he, hp.2.1, hp.2.2.1⟩
  · ihave %he := diskCfg_frozen_own_agree γ c c0 $$ Hfr Htok
    rw [he] at hc0
    rw [hc0.2.1] at hdead
    exact absurd hdead (by simp)

theorem diskProto_dead_open (γ : DiskNames) (v : VirtioState) (c : VirtioCfg)
    (hdead : Virtio.live c = false) :
    diskProto (GF := GF) γ v ∗ diskCfgOwn γ c ⊢
      ⌜v.cfg = c ∧ noInflight v ∧ v.cache = []⌝ ∗ (diskProto γ v ∗ diskCfgOwn γ c) := by
  iintro ⟨Hp, Htok⟩
  ihave %hpure : ⌜v.cfg = c ∧ noInflight v ∧ v.cache = []⌝ $$ [Hp Htok]
  · iapply diskProto_dead_pure γ v c hdead $$ [Hp Htok]
    iframe
  isplitl []
  · ipureintro; exact hpure
  iframe Hp Htok

/-! ## MMIO before `DRIVER_OK`

`virtio_disk_init` runs against the DEAD arm: it holds `diskCfgOwn γ c`,
and every register it reads is a function of `c` alone, so the accessor
returns the value as a PURE equation.  Each of the six `unreachable`
panics of the function is refuted by instantiating `hrd` with one of the
`vread_*` lemmas above. -/

/-- **A 4-byte MMIO read before the device is live** (every
`*R(...)` load of `virtio_disk_init`).  `hrd` says the register's value is
a function of the configuration the driver's tracker holds -- see
`vread_magic`, `vread_version`, `vread_deviceId`, `vread_vendorId`,
`vread_deviceFeatures`, `vread_status`, `vread_queueReady`,
`vread_queueNumMax`. -/
theorem disk_reg_read_dead (γ : DiskNames) (c : VirtioCfg) (off : Nat) (w : BitVec 32)
    (hdead : Virtio.live c = false)
    (hrd : ∀ v : VirtioState, v.cfg = c → Virtio.read v off = some w) :
    diskInv (GF := GF) γ ∗ diskCfgOwn γ c ⊢
      devReadAU .virtio off 4 (fun b => iprop(diskCfgOwn γ c ∗ ⌜b = w⌝)) := by
  unfold diskInv devInvR devReadAU
  iintro ⟨#Hinv, Htok⟩
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%v, >Hfrag, >Hproto⟩
  icases diskProto_dead_open γ v c hdead $$ [Hproto Htok] with ⟨%hpure, Hproto, Htok⟩
  · iframe
  have hx : (devSig .virtio).read v off 4 = some (w, v) :=
    virtio_readN4 v off w (hrd v hpure.1)
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists v
  iframe Hfrag
  isplit
  · ipureintro; rw [hx]; rfl
  inext
  iintro %b %v' %hrd' Hfrag
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hx.symm.trans hrd'))
  imod Hmask
  ihave Hcl := Hclose $$ [Hfrag Hproto]
  case' _ =>
    inext
    iexists v
    iframe Hfrag Hproto
  imod Hcl
  imodintro
  iframe Htok
  ipureintro; rfl

/-- What a pre-`DRIVER_OK` register write must do: move the tracker from
`c` to `c'` while keeping the device dead, the cache empty, nothing in
flight and the durable image still.  Every write of `virtio_disk_init`
satisfies it (`deadWrite_cfg`, `deadWrite_reset` below). -/
def deadWriteOk (off : Nat) (w : BitVec 32) (c c' : VirtioCfg) : Prop :=
  Virtio.live c' = false ∧
  ∀ v : VirtioState, v.cfg = c → v.cache = [] → noInflight v →
    ∃ v' : VirtioState, Virtio.write v off w = some v' ∧ v'.cfg = c' ∧ v'.cache = [] ∧
      noInflight v' ∧ v'.disk = v.disk

/-- The ordinary case: the write only moves the configuration. -/
theorem deadWrite_cfg (off : Nat) (w : BitVec 32) (c c' : VirtioCfg)
    (hlive : Virtio.live c' = false)
    (h : ∀ v : VirtioState, v.cfg = c → Virtio.write v off w = some { v with cfg := c' }) :
    deadWriteOk off w c c' := by
  refine ⟨hlive, fun v hv hc hn => ⟨{ v with cfg := c' }, h v hv, rfl, hc, ?_, rfl⟩⟩
  intro k; exact hn k

/-- The RESET (`*R(STATUS) = 0`): the configuration goes to `cfg0`, and
the cache and the in-flight map -- already empty in the dead arm -- go
with it. -/
theorem deadWrite_reset (c : VirtioCfg) : deadWriteOk Virtio.offStatus 0#32 c Virtio.cfg0 := by
  refine ⟨by decide, fun v hv hc hn => ⟨Virtio.reset v, vwrite_status_reset v, rfl, rfl, ?_, rfl⟩⟩
  intro k
  unfold Virtio.reqOf Virtio.phase Virtio.reset Virtio.alistGet
  rfl

/-- **The protocol's dead arm moves with the tracker.** -/
theorem diskProto_dead_write (γ : DiskNames) (v v' : VirtioState) (c c' : VirtioCfg)
    (hdead : Virtio.live c = false) (hlive' : Virtio.live c' = false)
    (hcfg' : v'.cfg = c') (hcache : v'.cache = []) (hni : noInflight v')
    (hdisk : v'.disk = v.disk) :
    diskProto (GF := GF) γ v ∗ diskCfgOwn γ c ⊢ |==> (diskProto γ v' ∗ diskCfgOwn γ c') := by
  unfold diskProto
  iintro ⟨⟨%hco, %pn, %pm, Hpm, %hfr, Harm⟩, Htok⟩
  icases Harm with ⟨Hd | ⟨%c0, #Hfr, %hc0, Hl⟩⟩
  · unfold diskDead
    icases Hd with ⟨%m, Hm, Hcfg, %hp⟩
    have hview : Virtio.cacheView v' = Virtio.cacheView v := by
      funext a
      unfold Virtio.cacheView
      rw [hcache, hp.2.2.1, hdisk]
    have hblk : ∀ bno, blockView v' bno = blockView v bno := by
      intro bno; unfold blockView; rw [hview]
    unfold diskCfgAuth diskCfgOwn
    imod ghost_var_update_halves c' γ.cfg v.cfg c $$ Hcfg Htok with ⟨Hcfg, Htok⟩
    imodintro
    iframe Htok
    isplitl []
    · ipureintro
      intro e he
      rw [hcache] at he
      exact absurd he (by simp)
    iexists pn, pm
    iframe Hpm
    isplitl []
    · ipureintro; exact hfr
    ileft
    iexists m
    rw [hcfg']
    iframe Hm Hcfg
    ipureintro
    refine ⟨hlive', hni, hcache, ?_⟩
    intro bno bs hb
    rcases hp.2.2.2 bno bs hb with h | h
    · exact absurd h id
    · exact Or.inr (by rw [h, hblk])
  · ihave %he := diskCfg_frozen_own_agree γ c c0 $$ Hfr Htok
    rw [he] at hc0
    rw [hc0.2.1] at hdead
    exact absurd hdead (by simp)

/-- **A 4-byte MMIO write before the device is live** (every `*R(...) = x`
of `virtio_disk_init` up to and including `QUEUE_READY = 1`): the driver's
tracker advances with the device. -/
theorem disk_reg_write_dead (γ : DiskNames) (c c' : VirtioCfg) (off : Nat) (w : BitVec 32)
    (hdead : Virtio.live c = false) (hok : deadWriteOk off w c c') :
    diskInv (GF := GF) γ ∗ diskCfgOwn γ c ⊢
      devWriteAU .virtio off 4 w (diskCfgOwn γ c') := by
  unfold diskInv devInvR devWriteAU
  iintro ⟨#Hinv, Htok⟩
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%v, >Hfrag, >Hproto⟩
  icases diskProto_dead_open γ v c hdead $$ [Hproto Htok] with ⟨%hpure, Hproto, Htok⟩
  · iframe
  obtain ⟨v', hw, hcfg', hcache', hni', hdisk'⟩ := hok.2 v hpure.1 hpure.2.2 hpure.2.1
  have hx : (devSig .virtio).write v off 4 w = some v' := virtio_writeN4 v v' off w hw
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists v
  iframe Hfrag
  isplit
  · ipureintro; rw [hx]; rfl
  inext
  iintro %v'' %hwr Hfrag
  obtain rfl : v' = v'' := Option.some.inj (hx.symm.trans hwr)
  imod Hmask
  imod diskProto_dead_write γ v v' c c' hdead hok.1 hcfg' hcache' hni' hdisk' $$ [Hproto Htok]
    with ⟨Hproto, Htok⟩
  · iframe
  ihave Hcl := Hclose $$ [Hfrag Hproto]
  case' _ =>
    inext
    iexists v'
    iframe Hfrag Hproto
  imod Hcl
  imodintro
  iexact Htok

/-! ## MMIO after `DRIVER_OK`: the protocol-neutral registers

`QUEUE_NOTIFY`, `INTERRUPT_STATUS` and `INTERRUPT_ACK` move nothing the
protocol mentions (the notify write is the identity on the device state,
the ack write touches only `isr`, and a read never moves the state), so
these three accessors ask for nothing but the invariant. -/

/-- **`*R(QUEUE_NOTIFY) = 0`** (`virtio_disk_rw`, after the `avail->idx`
bump). -/
theorem disk_notify_write (γ : DiskNames) (w : BitVec 32) :
    diskInv (GF := GF) γ ⊢ devWriteAU .virtio Virtio.offQueueNotify 4 w emp := by
  unfold diskInv devInvR devWriteAU
  iintro #Hinv
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%v, >Hfrag, >Hproto⟩
  have hx : (devSig .virtio).write v Virtio.offQueueNotify 4 w = some v :=
    virtio_writeN4 v v _ w (vwrite_notify v w)
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists v
  iframe Hfrag
  isplit
  · ipureintro; rw [hx]; rfl
  inext
  iintro %v'' %hwr Hfrag
  obtain rfl : v = v'' := Option.some.inj (hx.symm.trans hwr)
  imod Hmask
  ihave Hcl := Hclose $$ [Hfrag Hproto]
  case' _ =>
    inext
    iexists v
    iframe Hfrag Hproto
  imod Hcl
  imodintro
  itrivial

/-- **`*R(INTERRUPT_STATUS)`** (`virtio_disk_intr`): the value is the
device's `isr`, which the protocol does not constrain -- the handler only
feeds it back to `INTERRUPT_ACK`. -/
theorem disk_isr_read (γ : DiskNames) :
    diskInv (GF := GF) γ ⊢
      devReadAU .virtio Virtio.offInterruptStatus 4 (fun _ => emp) := by
  unfold diskInv devInvR devReadAU
  iintro #Hinv
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%v, >Hfrag, >Hproto⟩
  have hx : (devSig .virtio).read v Virtio.offInterruptStatus 4 = some (v.isr, v) :=
    virtio_readN4 v _ v.isr (vread_isr v)
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists v
  iframe Hfrag
  isplit
  · ipureintro; rw [hx]; rfl
  inext
  iintro %b %v' %hrd' Hfrag
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hx.symm.trans hrd'))
  imod Hmask
  ihave Hcl := Hclose $$ [Hfrag Hproto]
  case' _ =>
    inext
    iexists v
    iframe Hfrag Hproto
  imod Hcl
  imodintro
  itrivial

/-- **`*R(INTERRUPT_ACK) = mask`** (`virtio_disk_intr`), for ANY mask: the
write only clears bits of `isr`, which no clause of the invariant
mentions. -/
theorem disk_ack_write (γ : DiskNames) (msk : BitVec 32) :
    diskInv (GF := GF) γ ⊢ devWriteAU .virtio Virtio.offInterruptAck 4 msk emp := by
  unfold diskInv devInvR devWriteAU
  iintro #Hinv
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%v, >Hfrag, >Hproto⟩
  have hx : (devSig .virtio).write v Virtio.offInterruptAck 4 msk =
      some { v with isr := v.isr &&& ~~~msk } :=
    virtio_writeN4 v _ _ msk (vwrite_ack v msk)
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists v
  iframe Hfrag
  isplit
  · ipureintro; rw [hx]; rfl
  inext
  iintro %v'' %hwr Hfrag
  obtain rfl := Option.some.inj (hx.symm.trans hwr)
  imod Hmask
  ihave Hproto := diskProto_congr_mem γ v { v with isr := v.isr &&& ~~~msk } rfl rfl rfl rfl
    (fun _ h => h) (fun h => h) $$ Hproto
  ihave Hcl := Hclose $$ [Hfrag Hproto]
  case' _ =>
    inext
    iexists { v with isr := v.isr &&& ~~~msk }
    iframe Hfrag Hproto
  imod Hcl
  imodintro
  itrivial

/-! ## Queue memory: the two tiers of one shared cell

The avail page is SHARED: the invariant keeps a raw half of `avail->idx`
and of the eight ring cells (`availLease`), the lock payload the context
half (`diskRes`).  A driver STORE therefore needs both halves, so it opens
the invariant: `MachCSL.writeAU`.  What the store's continuation returns is
a RAW window; the driver's half comes back at the raw tier together with
the machine's receipts (`authoredBy t`, `topLb t`), and
`MachCSL.ctxBytes_of_pushed` turns it into a context cell again once the
driver's `kctx` -- which carries `ownCtx cpu curCtx` -- is in hand.  That
last step cannot happen inside the accessor, because the accessor runs
before the instruction rule and never sees the kernel context. -/

/-- Joining the two halves of a shared cell into the `own 1` raw window a
store asks for. -/
theorem dmaHalf_join (pa : PAddr) (n : Nat) (w0 : BitVec (8 * n)) (Hs' : Nat → Hist) :
    dmaHalfAt (GF := GF) pa n w0 ∗ histBytes pa n (fun _ => DFrac.own (1 : Qp).half) Hs' ⊢
      ∃ Hs : Nat → Hist, histBytes pa n (fun _ => DFrac.own 1) Hs := by
  unfold dmaHalfAt
  iintro ⟨⟨%Hs, Hb, %_⟩, Hb'⟩
  iexists Hs
  iapply histBytes_join_half pa n Hs Hs'
  iframe Hb Hb'

/-- Splitting the window a store returned back into the invariant's half
(now at the value stored) and the driver's half. -/
theorem dmaHalf_split (pa : PAddr) (n : Nat) (t : Nat) (ag : Agent) (Hs : Nat → Hist)
    (w : BitVec (8 * n)) :
    histBytes (GF := GF) pa n (fun _ => DFrac.own 1) (pushed Hs t ag w) ⊢
      dmaHalfAt pa n w ∗ histBytes pa n (fun _ => DFrac.own (1 : Qp).half) (pushed Hs t ag w) := by
  iintro H
  icases histBytes_split_half pa n (pushed Hs t ag w) $$ H with ⟨H1, H2⟩
  isplitl [H1]
  · unfold dmaHalfAt
    iexists (pushed Hs t ag w)
    iframe H1
    ipureintro
    exact headsAre_pushed Hs t ag n w
  · iexact H2

/-! ### The geometry and the counters -/

theorem diskGeom_cfg [CurCtx] (γ : DiskNames) (pd pav pu : PAddr) :
    diskGeom (GF := GF) γ pd pav pu ⊢ ∃ c0 : VirtioCfg, diskCfgFrozen γ c0 ∗
      ⌜c0.desc = pd ∧ c0.avail = pav ∧ c0.used = pu ∧ Virtio.live c0 = true ∧
        c0.qnum.toNat = NUM⌝ := by
  unfold diskGeom
  iintro ⟨%c0, #Hfr, %hg, _, _, _⟩
  iexists c0
  iframe Hfr
  ipureintro
  exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1⟩

theorem diskPub_agree (γ : DiskNames) (n n' : Nat) :
    ⊢@{IProp GF} diskPubAuth γ n -∗ diskPub γ n' -∗ ⌜n = n'⌝ := by
  unfold diskPubAuth diskPub
  iintro H1 H2
  ihave %h := ghost_var_agree γ.np _ _ _ _ $$ H1 H2
  ipureintro; exact h

/-- Updating the published count: BOTH halves move, so a bump of
`avail->idx` is only possible with the payload's `diskPub` in hand. -/
theorem diskPub_update (γ : DiskNames) (n n' m : Nat) :
    diskPubAuth (GF := GF) γ n ∗ diskPub γ n' ⊢ |==> (diskPubAuth γ m ∗ diskPub γ m) := by
  unfold diskPubAuth diskPub
  iintro ⟨H1, H2⟩
  imod ghost_var_update_halves m γ.np n n' $$ H1 H2 with ⟨H1, H2⟩
  imodintro
  iframe H1 H2

/-! ### Opening the live arm for the AVAIL page -/

/-- **The avail page, borrowed out of the invariant.**  The device's state
does not move under a hart's store, so everything the live arm says about
`v` is handed straight back; only the ring's contents and the published
count may change. -/
theorem diskProto_avail_acc (γ : DiskNames) (c0 : VirtioCfg) (v : VirtioState) (pav : PAddr)
    (hav : c0.avail = pav) (hlive : Virtio.live c0 = true) :
    diskCfgFrozen (GF := GF) γ c0 ∗ diskProto γ v ⊢
      ∃ (np : Nat) (ring : Nat → Nat), availLease pav np ring ∗ diskPubAuth γ np ∗
        (∀ (np' : Nat) (ring' : Nat → Nat),
          availLease pav np' ring' -∗ diskPubAuth γ np' -∗ diskProto γ v) := by
  subst hav
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
    iexists np, ring
    iframe Hav Hnp
    iintro %np' %ring' Hav' Hnp'
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
    iexists st, nc, np', ring', m
    iframe Hm Ha Hr Hu Hav' Hnc Hnp'
    ipureintro
    exact hpure

/-- One ring cell, borrowed out of `availLease` and put back at a new
value. -/
def updN (f : Nat → Nat) (j x : Nat) : Nat → Nat := fun k => if k = j then x else f k

@[simp] theorem updN_self (f : Nat → Nat) (j x : Nat) : updN f j x j = x := by
  simp [updN]

theorem updN_ne (f : Nat → Nat) (j x k : Nat) (h : k ≠ j) : updN f j x k = f k := by
  simp [updN, h]

theorem availLease_ring_acc (pav : PAddr) (np : Nat) (ring : Nat → Nat) (j : Nat) (hj : j < NUM) :
    availLease (GF := GF) pav np ring ⊢
      dmaHalfAt (availRingAt pav j) 2 (BitVec.ofNat 16 (ring j)) ∗
      (∀ x : Nat, dmaHalfAt (availRingAt pav j) 2 (BitVec.ofNat 16 x) -∗
        availLease pav np (updN ring j x)) := by
  unfold availLease
  iintro ⟨Hidx, Hcells⟩
  icases bigSepL_upd_acc (GF := GF) (List.range NUM) j j (by rw [List.getElem?_range hj])
      (fun k => dmaHalfAt (availRingAt pav k) 2 (BitVec.ofNat 16 (ring k)))
      (fun (x : Nat) k => dmaHalfAt (availRingAt pav k) 2 (BitVec.ofNat 16 (updN ring j x k)))
      (fun x k jj hjj hne => by
        have : jj ≠ j := by
          by_cases hk : k < NUM
          · rw [List.getElem?_range hk] at hjj; cases hjj; exact hne
          · rw [List.getElem?_eq_none (by simp; omega)] at hjj; cases hjj
        rw [updN_ne ring j x jj this]) $$ Hcells with ⟨Hc, Hback⟩
  iframe Hc
  iintro %x Hx
  iframe Hidx
  ihave Hx := (show dmaHalfAt (GF := GF) (availRingAt pav j) 2 (BitVec.ofNat 16 x) ⊢
      dmaHalfAt (availRingAt pav j) 2 (BitVec.ofNat 16 (updN ring j x j)) from by
    rw [updN_self]) $$ Hx
  iapply Hback $$ %x Hx

/-! ### The two stores of `publish` -/

theorem ofNat_toNat16 (h : BitVec 16) : BitVec.ofNat 16 h.toNat = h := by
  simp

/-- **`disk.avail->ring[disk.avail->idx % NUM] = idx[0]`**
(`virtio_disk_rw`, the `sh` that stages the head).  The cell is shared, so
the store opens the invariant; `diskPub γ np` pins the published count
across it.  What comes back is the driver's half AT THE RAW TIER together
with the store's receipts: feed them to `MachCSL.ctxBytes_of_pushed` with
the hart's `ownCtx` to get the payload's context cell at the new value. -/
theorem disk_ring_write [CurCtx] (γ : DiskNames) (pd pav pu : PAddr) (cpu : CPU)
    (np j : Nat) (hj : j < NUM) (w0 h : BitVec 16) :
    diskInv (GF := GF) γ ∗ diskGeom γ pd pav pu ∗ diskPub γ np ∗
      ctxBytes curCtx (availRingAt pav j) 2 (DFrac.own (1 : Qp).half) w0 ⊢
      writeAU cpu (availRingAt pav j) 2 h
        iprop(diskPub γ np ∗ ∃ (t : Nat) (Hs : Nat → Hist),
          authoredBy t (hartAgent cpu) ∗ topLb t ∗
          histBytes (availRingAt pav j) 2 (fun _ => DFrac.own (1 : Qp).half)
            (pushed (n := 2) Hs t (hartAgent cpu) h)) := by
  unfold diskInv devInvR writeAU
  iintro ⟨#Hinv, #Hgeom, Hpub, Hd⟩
  icases diskGeom_cfg γ pd pav pu $$ Hgeom with ⟨%c0, #Hfr, %hg⟩
  icases ctxBytes_forget curCtx (availRingAt pav j) 2 (DFrac.own (1 : Qp).half) w0 $$ Hd
    with ⟨%Hs', Hd⟩
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%v, >Hfrag, >Hproto⟩
  icases diskProto_avail_acc γ c0 v pav hg.2.1 hg.2.2.2.1 $$ [Hfr Hproto]
    with ⟨%np0, %ring, Hav, Hpa, Hback⟩
  · iframe Hfr Hproto
  ihave %hnp : ⌜np0 = np⌝ $$ [Hpa Hpub]
  · iapply diskPub_agree γ np0 np $$ Hpa Hpub
  subst hnp
  icases availLease_ring_acc pav np0 ring j hj $$ Hav with ⟨Hcell, Hring⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  icases dmaHalf_join (availRingAt pav j) 2 (BitVec.ofNat 16 (ring j)) Hs' $$ [Hcell Hd]
    with ⟨%Hs, Hraw⟩
  · iframe Hcell Hd
  iexists Hs
  iframe Hraw
  inext
  iintro %t Hraw #Hau #Ht
  icases dmaHalf_split (availRingAt pav j) 2 t (hartAgent cpu) Hs h $$ Hraw with ⟨Hcell, Hdrv⟩
  imod Hmask
  ihave Hcell := (show dmaHalfAt (GF := GF) (availRingAt pav j) 2 h ⊢
      dmaHalfAt (availRingAt pav j) 2 (BitVec.ofNat 16 h.toNat) from by
    rw [ofNat_toNat16]) $$ Hcell
  ihave Hav := Hring $$ %h.toNat Hcell
  ihave Hproto := Hback $$ %np0 %(updN ring j h.toNat) Hav Hpa
  ihave Hcl := Hclose $$ [Hfrag Hproto]
  case' _ =>
    inext
    iexists v
    iframe Hfrag Hproto
  imod Hcl
  imodintro
  iframe Hpub
  iexists t, Hs
  iframe Hau Ht Hdrv

theorem availLease_idx_acc (pav : PAddr) (np : Nat) (ring : Nat → Nat) :
    availLease (GF := GF) pav np ring ⊢
      dmaHalfAt (availIdxAt pav) 2 (wrap16 np) ∗
      (∀ np' : Nat, dmaHalfAt (availIdxAt pav) 2 (wrap16 np') -∗ availLease pav np' ring) := by
  unfold availLease
  iintro ⟨Hidx, Hcells⟩
  iframe Hidx
  iintro %np' Hidx'
  iframe Hidx' Hcells

/-- **`disk.avail->idx += 1`** (`virtio_disk_rw`, the `sh` that publishes
the staged chain).  The cell is shared, so the store opens the invariant;
BOTH halves of the published count move with it, which is why the payload's
`diskPub` is consumed and returned at `np + 1` -- and why no other hart can
publish while this one holds the lock. -/
theorem disk_avail_idx_write [CurCtx] (γ : DiskNames) (pd pav pu : PAddr) (cpu : CPU) (np : Nat) :
    diskInv (GF := GF) γ ∗ diskGeom γ pd pav pu ∗ diskPub γ np ∗
      ctxBytes curCtx (availIdxAt pav) 2 (DFrac.own (1 : Qp).half) (wrap16 np) ⊢
      writeAU cpu (availIdxAt pav) 2 (wrap16 (np + 1))
        iprop(diskPub γ (np + 1) ∗ ∃ (t : Nat) (Hs : Nat → Hist),
          authoredBy t (hartAgent cpu) ∗ topLb t ∗
          histBytes (availIdxAt pav) 2 (fun _ => DFrac.own (1 : Qp).half)
            (pushed (n := 2) Hs t (hartAgent cpu) (wrap16 (np + 1)))) := by
  unfold diskInv devInvR writeAU
  iintro ⟨#Hinv, #Hgeom, Hpub, Hd⟩
  icases diskGeom_cfg γ pd pav pu $$ Hgeom with ⟨%c0, #Hfr, %hg⟩
  icases ctxBytes_forget curCtx (availIdxAt pav) 2 (DFrac.own (1 : Qp).half) (wrap16 np) $$ Hd
    with ⟨%Hs', Hd⟩
  iinv Hinv with Hbody Hclose
  icases Hbody with ⟨%v, >Hfrag, >Hproto⟩
  icases diskProto_avail_acc γ c0 v pav hg.2.1 hg.2.2.2.1 $$ [Hfr Hproto]
    with ⟨%np0, %ring, Hav, Hpa, Hback⟩
  · iframe Hfr Hproto
  ihave %hnp : ⌜np0 = np⌝ $$ [Hpa Hpub]
  · iapply diskPub_agree γ np0 np $$ Hpa Hpub
  subst hnp
  icases availLease_idx_acc pav np0 ring $$ Hav with ⟨Hcell, Hidx⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  icases dmaHalf_join (availIdxAt pav) 2 (wrap16 np0) Hs' $$ [Hcell Hd] with ⟨%Hs, Hraw⟩
  · iframe Hcell Hd
  iexists Hs
  iframe Hraw
  inext
  iintro %t Hraw #Hau #Ht
  icases dmaHalf_split (availIdxAt pav) 2 t (hartAgent cpu) Hs (wrap16 (np0 + 1)) $$ Hraw
    with ⟨Hcell, Hdrv⟩
  imod Hmask
  imod diskPub_update γ np0 np0 (np0 + 1) $$ [Hpa Hpub] with ⟨Hpa, Hpub⟩
  · iframe Hpa Hpub
  ihave Hav := Hidx $$ %(np0 + 1) Hcell
  ihave Hproto := Hback $$ %(np0 + 1) %ring Hav Hpa
  ihave Hcl := Hclose $$ [Hfrag Hproto]
  case' _ =>
    inext
    iexists v
    iframe Hfrag Hproto
  imod Hcl
  imodintro
  iframe Hpub
  iexists t, Hs
  iframe Hau Ht Hdrv

/-! ## The lock payload, opened

Everything below the invariant: the cells `disk.vdisk_lock` protects.  A
driver READ of `avail->idx` or of a ring cell needs only these -- the
driver's half of a shared cell pins its value, because the DEVICE never
writes the avail page. -/

theorem diskRes_open (γ : DiskNames) [CurCtx] (pd pav pu : PAddr) (ξ : CtxId) :
    diskRes (GF := GF) γ pd pav pu ξ ⊢ ∃ (np nr : Nat) (stg : Option Nat) (ring : Nat → Nat),
      diskPub γ np ∗ diskReadAt γ nr ∗ diskStage γ stg ∗ diskDoneLb γ nr ∗
      wordAtN ξ aUsedIdx 2 (DFrac.own 1) (wrap16 nr) ∗
      ctxBytes ξ (availIdxAt pav) 2 (DFrac.own (1 : Qp).half) (wrap16 np) ∗
      ([∗list] j ∈ List.range NUM,
        ctxBytes ξ (availRingAt pav j) 2 (DFrac.own (1 : Qp).half) (BitVec.ofNat 16 (ring j))) ∗
      ([∗list] i ∈ List.range NUM, slotRes γ ξ pd i) := by
  unfold diskRes
  iintro H
  iexact H

theorem diskRes_close (γ : DiskNames) [CurCtx] (pd pav pu : PAddr) (ξ : CtxId)
    (np nr : Nat) (stg : Option Nat) (ring : Nat → Nat) :
    diskPub (GF := GF) γ np ∗ diskReadAt γ nr ∗ diskStage γ stg ∗ diskDoneLb γ nr ∗
      wordAtN ξ aUsedIdx 2 (DFrac.own 1) (wrap16 nr) ∗
      ctxBytes ξ (availIdxAt pav) 2 (DFrac.own (1 : Qp).half) (wrap16 np) ∗
      ([∗list] j ∈ List.range NUM,
        ctxBytes ξ (availRingAt pav j) 2 (DFrac.own (1 : Qp).half) (BitVec.ofNat 16 (ring j))) ∗
      ([∗list] i ∈ List.range NUM, slotRes γ ξ pd i) ⊢ diskRes γ pd pav pu ξ := by
  unfold diskRes
  iintro H
  iexists np, nr, stg, ring
  iexact H

/-- **`disk.avail->idx`, read out of the payload** (the `lhu` of
`virtio_disk_rw`): the driver's own half of the cell pins the value to
`wrap16 np`, so this read needs NO accessor -- the ordinary load rule at
the fraction `½` does it.  This lemma is the borrow. -/
theorem diskRes_availIdx_acc (γ : DiskNames) [CurCtx] (pd pav pu : PAddr) (ξ : CtxId) :
    diskRes (GF := GF) γ pd pav pu ξ ⊢ ∃ np : Nat,
      diskPub γ np ∗ ctxBytes ξ (availIdxAt pav) 2 (DFrac.own (1 : Qp).half) (wrap16 np) ∗
      (∀ np' : Nat, diskPub γ np' -∗
        ctxBytes ξ (availIdxAt pav) 2 (DFrac.own (1 : Qp).half) (wrap16 np') -∗
        diskRes γ pd pav pu ξ) := by
  iintro HR
  icases diskRes_open γ pd pav pu ξ $$ HR with ⟨%np, %nr, %stg, %ring, Hp, Hr, Hs, Hlb, Hu, Hidx, Hring, Hsl⟩
  iexists np
  iframe Hp Hidx
  iintro %np' Hp' Hidx'
  iapply diskRes_close γ pd pav pu ξ np' nr stg ring
  iframe Hp' Hr Hs Hlb Hu Hidx' Hring Hsl

/-- One ring cell of the payload, borrowed and put back at a new value
(the `sh` of `virtio_disk_rw` writes through it; the invariant's half goes
through `disk_ring_write`). -/
theorem diskRes_ring_acc (γ : DiskNames) [CurCtx] (pd pav pu : PAddr) (ξ : CtxId)
    (j : Nat) (hj : j < NUM) :
    diskRes (GF := GF) γ pd pav pu ξ ⊢ ∃ (np : Nat) (x : Nat),
      diskPub γ np ∗ ctxBytes ξ (availRingAt pav j) 2 (DFrac.own (1 : Qp).half) (BitVec.ofNat 16 x) ∗
      (∀ y : Nat, diskPub γ np -∗
        ctxBytes ξ (availRingAt pav j) 2 (DFrac.own (1 : Qp).half) (BitVec.ofNat 16 y) -∗
        diskRes γ pd pav pu ξ) := by
  iintro HR
  icases diskRes_open γ pd pav pu ξ $$ HR with ⟨%np, %nr, %stg, %ring, Hp, Hr, Hs, Hlb, Hu, Hidx, Hring, Hsl⟩
  icases bigSepL_upd_acc (GF := GF) (List.range NUM) j j (by rw [List.getElem?_range hj])
      (fun k => ctxBytes ξ (availRingAt pav k) 2 (DFrac.own (1 : Qp).half) (BitVec.ofNat 16 (ring k)))
      (fun (y : Nat) k =>
        ctxBytes ξ (availRingAt pav k) 2 (DFrac.own (1 : Qp).half)
          (BitVec.ofNat 16 (updN ring j y k)))
      (fun y k jj hjj hne => by
        have : jj ≠ j := by
          by_cases hk : k < NUM
          · rw [List.getElem?_range hk] at hjj; cases hjj; exact hne
          · rw [List.getElem?_eq_none (by simp; omega)] at hjj; cases hjj
        rw [updN_ne ring j y jj this]) $$ Hring with ⟨Hc, Hback⟩
  iexists np, (ring j)
  iframe Hp Hc
  iintro %y Hp' Hc'
  ihave Hc' := (show ctxBytes (GF := GF) ξ (availRingAt pav j) 2 (DFrac.own (1 : Qp).half)
      (BitVec.ofNat 16 y) ⊢
      ctxBytes ξ (availRingAt pav j) 2 (DFrac.own (1 : Qp).half)
        (BitVec.ofNat 16 (updN ring j y j)) from by rw [updN_self]) $$ Hc'
  ihave Hring := Hback $$ %y Hc'
  iapply diskRes_close γ pd pav pu ξ np nr stg (updN ring j y)
  iframe Hp' Hr Hs Hlb Hu Hidx Hring Hsl

/-- One descriptor slot of the payload, borrowed and put back (the `free[]`
byte, the receipt and the chain's context cells). -/
theorem diskRes_slot_acc (γ : DiskNames) [CurCtx] (pd pav pu : PAddr) (ξ : CtxId)
    (i : Nat) (hi : i < NUM) :
    diskRes (GF := GF) γ pd pav pu ξ ⊢
      slotRes γ ξ pd i ∗ (slotRes γ ξ pd i -∗ diskRes γ pd pav pu ξ) := by
  iintro HR
  icases diskRes_open γ pd pav pu ξ $$ HR with ⟨%np, %nr, %stg, %ring, Hp, Hr, Hs, Hlb, Hu, Hidx, Hring, Hsl⟩
  icases BigSepL.bigSepL_mem_acc (Φ := fun i => slotRes (GF := GF) γ ξ pd i)
      (range_mem i NUM hi) $$ Hsl with ⟨Hi, Hback⟩
  iframe Hi
  iintro Hi'
  ihave Hsl := Hback $$ Hi'
  iapply diskRes_close γ pd pav pu ξ np nr stg ring
  iframe Hp Hr Hs Hlb Hu Hidx Hring Hsl

/-! ## The obligations this port does not discharge

Everything above is PROVED.  What follows is stated but ASSUMED, as an
interface (no `sorry`): each field is an accessor whose proof needs a
clause the invariant of `Xv6/DiskInvDefs.lean` does not carry yet, and
the docstring says which.  The common root is that `Xv6/DiskInv.lean`
deliberately keeps the QUEUE ACCOUNTING (`Xv6.VQ.Ok`: `nr ≤ nc ≤ lo ≤ np`,
"every un-popped position names an armed head") OUT of the invariant,
because the device's `pop` and `complete` are admitted at every state; so
the invariant cannot say what the used ring holds, nor that a head the
driver is about to re-arm or zero is not about to be popped. -/

/-- What `virtio_disk_init` must have in hand at the `DRIVER_OK` store:
BOTH halves of every ghost the live arm splits with the payload, and the
three `kalloc`'d pages -- zeroed by `memset` -- at the context tier and
full ownership. -/
def diskFlipIn [CurCtx] (γ : DiskNames) (pd pav pu : PAddr) : IProp GF := iprop%
  ([∗list] i ∈ List.range NUM, iprop(headAuth γ i .inactive ∗ headTok γ i .inactive)) ∗
  diskPubAuth γ 0 ∗ diskPub γ 0 ∗ diskReadAtAuth γ 0 ∗ diskReadAt γ 0 ∗
  diskStageAuth γ none ∗ diskStage γ none ∗ diskDoneAuth γ 0 ∗
  ([∗list] i ∈ List.range NUM,
    ctxBytes curCtx (descAt pd i) 16 (DFrac.own 1) (0 : BitVec (8 * 16))) ∗
  ctxBytes curCtx (availIdxAt pav) 2 (DFrac.own 1) (0 : BitVec (8 * 2)) ∗
  ([∗list] j ∈ List.range NUM,
    ctxBytes curCtx (availRingAt pav j) 2 (DFrac.own 1) (0 : BitVec (8 * 2))) ∗
  ctxBytes curCtx (usedIdxAt pu) 2 (DFrac.own 1) (0 : BitVec (8 * 2)) ∗
  ([∗list] j ∈ List.range NUM,
    ctxBytes curCtx (usedElemAt pu j) 8 (DFrac.own 1) (0 : BitVec (8 * 8))) ∗
  wordAtN curCtx aUsedIdx 2 (DFrac.own 1) (wrap16 0) ∗
  ([∗list] i ∈ List.range NUM, wordAtN curCtx (aFree i) 1 (DFrac.own 1) 1#8) ∗
  wordPointsTo aDescPtr 8 (DFrac.own 1) pd ∗
  wordPointsTo aAvailPtr 8 (DFrac.own 1) pav ∗
  wordPointsTo aUsedPtr 8 (DFrac.own 1) pu

/-- What comes out of the flip: the persistent geometry and the payload of
`disk.vdisk_lock`. -/
def diskFlipOut [CurCtx] (γ : DiskNames) (pd pav pu : PAddr) : IProp GF := iprop%
  diskGeom γ pd pav pu ∗ diskRes γ pd pav pu curCtx

/-- The accessors whose obligations this port leaves open. -/
structure DISK_ACC_ASSUMPTIONS : Prop where
  /-- **The live flip** (`*R(STATUS) = ... | DRIVER_OK`, the last store of
  `virtio_disk_init`).  Blocked on ONE clause: the live arm demands
  `permOk pm st` with every receipt `.inactive`, and the DEAD arm says
  nothing about the serve permits `pm`, so a permit recording an `.active`
  receipt cannot be ruled out.  The fix is a dead-arm clause
  `permOk pm (fun _ => .inactive)` -- preserved by `perm_drop`
  (`permOk_delete`) and vacuous at allocation, where `pm = ∅` -- which
  means threading a `pm` parameter through `diskDead` and re-proving the
  nine sites of `Xv6/DiskInv.lean` that construct or destruct it. -/
  disk_driver_ok_write : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
      [DiskG GF] [CurCtx] (γ : DiskNames) (c c' : VirtioCfg) (pd pav pu : PAddr) (w : BitVec 32),
    Virtio.live c = false → Virtio.live c' = true → Virtio.wce c' = false →
    c'.qnum.toNat = NUM → c'.desc = pd → c'.avail = pav → c'.used = pu →
    (∀ v : VirtioState, v.cfg = c → Virtio.write v Virtio.offStatus w =
      some { v with cfg := c' }) →
    diskInv (GF := GF) γ ∗ diskCfgOwn γ c ∗ diskFlipIn γ pd pav pu ⊢
      devWriteAU .virtio Virtio.offStatus 4 w (diskFlipOut γ pd pav pu)

  /-- **`publish`**: the view shift that arms head `h` with the chain `c`,
  carried out at the `avail->idx` bump (`disk_avail_idx_write` does the
  bytes).  The chain's cells leave the payload for the invariant: the
  context halves of `c.d0/d1/d2/hdr` become the raw halves of
  `chainLease`, `info[h].status` and `b->data` go over at own 1, and the
  block's image fragment is deposited in the row.  Blocked on: showing
  that NO serve permit is out for `h` (`Xv6.permOk` would otherwise pin
  the receipt to `.inactive`), which is exactly the `VQ.Ok` accounting the
  invariant does not carry. -/
  disk_publish : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
      [DiskG GF] [CurCtx] (γ : DiskNames) (pd pav pu : PAddr) (c : Chain)
      (bs data : List (BitVec 8)),
    c.wf → data.length = BSIZE →
    diskInv (GF := GF) γ ∗ diskGeom γ pd pav pu ∗ headTok γ c.hd .inactive ∗
      diskStage γ (some c.hd) ∗ claimRes curCtx pd c ∗
      wordAtN curCtx c.status 1 (DFrac.own 1) 0xff#8 ∗
      byteBuf c.data (DFrac.own 1) data ∗ diskBlock γ c.blk bs ⊢
      |={⊤}=> (headTok γ c.hd (.active c) ∗ diskStage γ none)

  /-- **`disk.used->idx`, read** (the `lhu` of `virtio_disk_intr`'s loop
  test).  The used page is entirely the device's, and the invariant holds
  it as `dmaOwn` -- FULL ownership at an UNCONSTRAINED value -- so a read
  learns nothing.  The fix is to record the used-index cell's HISTORY:
  every entry's value is `wrap16 m` for some `m ≤ nc`, and the head is
  `wrap16 nc`; then `readsAre` picks an entry and the watermark
  `diskReadAt γ nr` plus `nc - nr < 2^16` recovers a natural number. -/
  disk_used_idx_read : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
      [DiskG GF] [CurCtx] (γ : DiskNames) (pd pav pu : PAddr) (cpu : CPU) (K nr : Nat),
    diskInv (GF := GF) γ ∗ diskGeom γ pd pav pu ∗ diskReadAt γ nr ∗ viewLb cpu K ⊢
      readAU cpu (usedIdxAt pu) 2 K [] (fun w =>
        iprop(diskReadAt γ nr ∗ ∃ nc : Nat, ⌜w = wrap16 nc ∧ nr ≤ nc⌝ ∗ diskDoneLb γ nc))

  /-- **`disk.used->ring[disk.used_idx % NUM].id`, read** (the `lw` of the
  handler's loop).  Blocked on the same absence: nothing says what the
  device wrote there.  The fix is the Rocq `vp_uix`/`disk_ord` row -- a
  PERSISTENT per-position record of the head completed at that position --
  written by the device's `usedElem_write_lease` and read here. -/
  disk_used_elem_read : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
      [DiskG GF] [CurCtx] (γ : DiskNames) (pd pav pu : PAddr) (cpu : CPU) (K nr nc : Nat),
    nr < nc →
    diskInv (GF := GF) γ ∗ diskGeom γ pd pav pu ∗ diskReadAt γ nr ∗ diskDoneLb γ nc ∗
      viewLb cpu K ⊢
      readAU cpu (usedElemAt pu (nr % NUM)) 8 K [] (fun w =>
        iprop(diskReadAt γ nr ∗ ∃ i : Nat,
          ⌜i < NUM ∧ BitVec.extractLsb' 0 32 w = BitVec.ofNat 32 i⌝))

  /-- **`disk.info[id].status`, read** (the byte the `unreachable` of
  `virtio_disk_intr` tests).  The invariant owns it as `dmaOwn c.status 1`
  -- own 1, value unconstrained -- so `0` is not derivable.  The fix is to
  move a COMPLETED request's status byte to `dmaOwnAt .. 1 (statusOf r)`
  in the invariant's row when the device completes it, which is where the
  "done" marking of `deposit` belongs too. -/
  disk_status_read : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
      [DiskG GF] [CurCtx] (γ : DiskNames) (pd pav pu : PAddr) (cpu : CPU) (K nr : Nat)
      (c : Chain),
    diskInv (GF := GF) γ ∗ diskGeom γ pd pav pu ∗ diskReadAt γ nr ∗
      headTok γ c.hd (.active c) ∗ viewLb cpu K ⊢
      readAU cpu c.status 1 K [] (fun b =>
        iprop(diskReadAt γ nr ∗ headTok γ c.hd (.active c) ∗ ⌜b = 0#8⌝))

  /-- **`deposit`**: the handler advances its watermark past position `nr`
  and marks the chain reported, transferring into the payload the TSO
  FLOOR (`ctxFloor`) of the DMA writes of that request -- without it the
  sleeper cannot turn the device-written bytes of `b->data` into context
  cells (`MachCSL.ctxBytes_of_pushedFloor` needs a floor past the disk's
  write position).  Blocked on the invariant recording, per completed
  request, a `topLb` bound on its DMA writes (Rocq's `disk_flr`). -/
  disk_deposit : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
      [DiskG GF] [CurCtx] (γ : DiskNames) (cpu : CPU) (nr K : Nat) (c : Chain),
    diskInv (GF := GF) γ ∗ diskReadAt γ nr ∗ diskDoneLb γ (nr + 1) ∗
      headTok γ c.hd (.active c) ∗ viewLb cpu K ⊢
      |={⊤}=> (diskReadAt γ (nr + 1) ∗ headTok γ c.hd (.active c) ∗
        ∃ T : Nat, ctxFloor curCtx T)

  /-- **`collect`**: the sleeper takes the chain back once `b->disk` is
  `0`.  The descriptors, the header, the status byte and `b->data` return
  to the CONTEXT tier, and the block's image fragment comes back holding
  the transferred bytes.  Blocked twice: on the floor of `disk_deposit`
  (to justify the device's entries at the driver's context) and on the
  invariant's `bufLease` being `dmaOwn` -- the CONTENT of a read's
  transfer is existential, so `bs'` cannot be pinned to `blockView`
  without a generation-keyed snapshot of the block (see
  `Xv6/DiskInvDefs.lean`'s header). -/
  disk_collect : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
      [DiskG GF] [CurCtx] (γ : DiskNames) (pd pav pu : PAddr) (c : Chain) (T : Nat),
    diskInv (GF := GF) γ ∗ diskGeom γ pd pav pu ∗ headTok γ c.hd (.active c) ∗
      ctxFloor curCtx T ⊢
      |={⊤}=> (headTok γ c.hd .inactive ∗ claimRes curCtx pd c ∗
        wordAtN curCtx c.status 1 (DFrac.own 1) 0#8 ∗
        ∃ data : List (BitVec 8), ⌜data.length = BSIZE⌝ ∗
          byteBuf c.data (DFrac.own 1) data ∗ diskBlock γ c.blk data)

  /-- **`free_desc`**: the four stores (`addr`, `len`, `flags`, `next`)
  that zero a reclaimed descriptor.  The cell is shared, so each store
  opens the invariant -- but the invariant's row for a free slot
  (`headRes .inactive`) pins the half to SIXTEEN ZERO BYTES, and the
  descriptor passes through three intermediate values on the way there.
  So `HState` needs a third arm for "being zeroed", and that arm must
  still let `Xv6.leaseL_fetch_free` refute a fetch at the head -- which is
  only possible with the queue accounting that rules out a pop of a head
  the driver has already reclaimed.  Stated here for the whole
  sixteen-byte window, which is the shape the four stores compose to. -/
  disk_free_desc_write : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
      [DiskG GF] [CurCtx] (γ : DiskNames) (pd pav pu : PAddr) (cpu : CPU) (i : Nat)
      (w0 : BitVec (8 * 16)),
    i < NUM →
    diskInv (GF := GF) γ ∗ diskGeom γ pd pav pu ∗ headTok γ i .inactive ∗
      ctxBytes curCtx (descAt pd i) 16 (DFrac.own (1 : Qp).half) w0 ⊢
      writeAU cpu (descAt pd i) 16 (0 : BitVec (8 * 16))
        iprop(headTok γ i .inactive ∗ ∃ (t : Nat) (Hs : Nat → Hist),
          authoredBy t (hartAgent cpu) ∗ topLb t ∗
          histBytes (descAt pd i) 16 (fun _ => DFrac.own (1 : Qp).half)
            (pushed (n := 16) Hs t (hartAgent cpu) (0 : BitVec (8 * 16))))

end

end Xv6
