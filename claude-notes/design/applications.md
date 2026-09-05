# Design: applications — a client's invariant on the abstract file system, its programs, and its trace property

An APPLICATION is a collection of user-level programs plus what it claims:
an invariant on the abstract file-system state, WPs for its programs, and
a pure property of the UART trace.  This file is the design of record for
how an application plugs into the whole-system theorem.  It builds on
[`adequacy.md`](adequacy.md) (the trace slot `Pt`, the hook `Hphi`, the
crash slot `Pc`), [`crash.md`](crash.md) (the fixed layer, the PowerOn
arm's lends), [`fs-syscall-specs.md`](fs-syscall-specs.md) (the AU forms
and the abstract state `aview`), [`user-wp-slot.md`](user-wp-slot.md) and
[`fd-row-pilot.md`](fd-row-pilot.md) (the process's trap contract and how a
process hands the kernel a payload at an ecall).  The worklist for the
first application is [`../projects/app-echo.md`](../projects/app-echo.md).

## 0. The two applications, and what separates them

- **The GENERIC application** (`App.app_triv`): user space does anything,
  the abstract state is anything, the kernel stays correct.  This is
  today's theorem and it must keep its statement: it is the one coupled to
  the generic user-safety WP, and it is what the assumption audit is run
  on (`xv6_fs_adequacy_xv6Σ`).
- **The ECHO application** (`AppEcho`): init spawns sh, a user types
  `echo hello world` at the console, sh forks and execs echo, echo prints
  the string back.  Its invariant is THE FILE SYSTEM IS UNMODIFIED — the
  binaries of init, sh and echo are the image's at every reboot — and its
  trace property is "if every byte ever typed follows the discipline, the
  console's output is the expected one and the durable file system is the
  mkfs image's at every state".

The generic application constrains nothing, so everything it asks of the
kernel is discharged with receipts that say nothing (`FsAbsInvFire`,
`True` families, the generic slot).  The echo application constrains the
state, so every fire point that could change the state, every process
creation, and every reboot has to be paid for.  The scaffold makes those
payments PARAMETERS of the theorem; §5 lists what the echo application
still owes, lane by lane.

## 1. The conditional invariant: `⌜A I⌝ ∨ tainted`, and where the taint lives

The owner's framing is the design: EITHER the console input has followed
the discipline from the beginning of era 0, OR the abstract state is now
arbitrary.  It is realised as a disjunction with a persistent, monotone,
FIXED-LAYER witness on the right:

    fsabs_ok I  :=  ⌜fsc_app I⌝  ∨  tainted
    tainted     :=  client_lb 1              (* mono_nat_lb_own riscv_client_name 1 *)

- **`fsc_app : gmap Z fs_node -> Prop`** is the application's predicate on
  the abstract state, a field of the era's file-system configuration
  record `FsCfg.fscfg` (§2).  Stated over the RAW node map, the form
  `InodeRegion.ftop_body` holds; an application writes it through
  `FsAbsDefs.abs_view` (`fun I => abs_view I = av0`).  Pure, so it costs
  nothing to carry and nothing to state at the boot.
- **The taint is a lower bound on the CLIENT PHASE COUNTER**, a mono-nat
  the machine layer allocates ONCE into the fixed record
  (`RiscvPtsto.riscv_client_name`, typed by the record's own `mono_natG`)
  and hands to the trace slot at its birth (`client_auth 0` beside the
  history's client half).  Fixed-layer for the same reason the durable
  disk's name is: a taint must outlive the era it was minted in — once the
  input has left the discipline, the state is arbitrary in every later
  era too — and every era has to be able to NAME it without learning it,
  which an ambient field gives for free (`riscvGS` is in scope wherever
  `fsabs_ok` is written).  A gname alone would not do — the client cannot
  allocate a resource at a name the machine chose — so the machine
  allocates the counter itself and the client OWNS it: the trace ledger
  holds `client_auth n` and flips `n` from 0 to 1 at the first
  undisciplined byte (§4).  `client_auth 0 ∗ client_lb 1 ⊢ False` is the
  whole content of "untainted".
- **Why not a per-era taint** (a fresh gname in `fscfg`): the next era's
  boot would have to re-derive the taint from the durable state, and the
  durable state does not record WHY it changed.  Why not inside `R` only:
  the fire dischargers (§3) run in the kernel's syscall proofs and cannot
  open the trace slot at the commit mask; they need a witness they can
  hold, and a persistent lower bound is exactly that.

## 2. The invariant's body and its two carriers

`FsAbsInv.fsabs_inv Γc = inv fsabsN (∃ I, client_auth I ∗ frags I ∗ fsabs_ok I)`:
the client copy of the node map at its own gname (FsAbsInv's header says
why a copy and not a share of the kernel's map), every element inside,
and the application conjunct.  The application reaches it as
`fsabs_env := ∃ γa, fsabs_inv (fsabs_client (fs_gamma_L fsc_fs) γa) ∗ fsabs_lic`,
persistent, carried beside the sealed file system in `FirstTok.first_done`
and read by the dispatcher off `syscall_env`.  Two things changed from
the purely-existential body:

- **It is MINTED AT THE ERA MINT, seeded at the founded map.**  The boot
  founds the kernel's `γtop` authority at `fss_inodes S`
  (`FsCfgSnap.fs_cfg_alloc_snap`, off the durable snapshot the power arm
  lent); the client copy is allocated in the same fupd at the same map,
  and rides kit 2 (`FsCfgKits.fs_kit_fsinit_ghost`, LAST row) through
  `FirstTok.first_fsinit` to forkret's boot arm, which PROJECTS it into
  `first_done` instead of minting an empty copy.  The seed's `fsabs_ok`
  is the application's BOOT obligation (§5, `app_boot`): at every era,
  the founded map satisfies the predicate or the run is tainted.  For the
  generic application it is `iLeft`.
- **THE LICENSE, `fsabs_lic`.**  A persistent wand the application owns,
  and the ONE thing a fire discharger needs of it:

      fsabs_lic := □ (∀ I I', fsabs_ok I -∗ fsabs_ok I')

  "the copy may be re-synced to any map".  Every discharger opens the
  invariant, replaces the copy by the map the kernel lent it (the pre-map
  at phase 1, the post-map at phase 2) and closes, paying `fsabs_ok` of
  the new map with the license — exactly today's `fsabs_set`, one premise
  richer.  For the generic application the license is `⊢ fsabs_lic`
  outright (`fsc_app = fun _ => True`); for the echo application it is
  `tainted -∗ fsabs_lic` — so an era can only hold it once tainted, which
  is the honest statement that TODAY the license is era-wide and only the
  generic application can pay it.

  **Why not a delta-indexed license** (`⌜fs_delta (abs_view I) (abs_view I')⌝ -∗ …`,
  over `FsAbsDelta.fs_delta`, the disjunction of the five write-kind deltas
  the AU commits fire — `delta_create`, `delta_trunc`, `delta_write`,
  `delta_unl_ent`, `delta_unl_tgt`, hoisted below `ProcInv` for this
  purpose): at a fire the discharger holds the KERNEL's pre-map `I` (lent)
  and the copy's map `Ic`, and nothing relates them until lane L3 makes
  every mover fire — so `fsabs_ok I` is not derivable from `fsabs_ok Ic`
  and a delta-indexed license cannot be applied.  The delta vocabulary is
  landed and idle; L3 sharpens the license to it, and L2 moves it from
  `fsabs_env` to the process's ecall payload.  (Ruled 2026-09-04, at the
  scaffold's first build.)

**What the copy means, and the gap that is not this design's.**  The copy
is "the abstract state as last observed at a WRITE fire point".  Paths
that move `γtop` without firing (the syscalls still on landed contracts:
mkdir, link, iput's free) leave it stale, and `⌜fsc_app I⌝` on a stale copy
says nothing about the file system.  That is `fs-syscall-specs`' remaining
lanes' business (lane L3 below), and FsAbsInv's header already assigns the
obligation to the application.  The tie that lane needs — one
`ghost_var` half in `ftop_body`, the other in the copy — is a kernel
invariant change and is deferred with it.

## 3. The application record and the theorem (`App.v`)

    Record xv6_app Σ := MkApp {
      app_fs    : gmap Z fs_node -> Prop;              (* §1: fsc_app *)
      app_lend  : (Z -> bv 8) -> iProp Σ;              (* what PowerOn lends the boot about the durable state *)
      app_R     : gname -> list mobs -> iProp Σ;       (* the trace ledger, at the client counter's name *)
      app_phi   : gstate -> list mobs -> Prop;         (* the conclusion *)
    }.

The data only; the obligations are premises of `xv6_app_adequacy`, in the
tree's theorem-with-premises style, so that a partial application (one
that can pay some and not others) is a definition and never a vacuous
theorem:

| premise | what it says | generic app |
|---|---|---|
| `Happ_boot` | `snap_ok S D`, `fs_recovery dk D`, `app_lend dk ⊢ ⌜app_fs (fss_inodes S)⌝ ∨ client_lb γc 1` | `iLeft` |
| `Happ_lic` | `⊢ fsabs_lic` at `fsc_app := app_fs` | trivial |
| `Happ_swap` | the PowerOn arm produces `app_lend dk` beside the FS's own lend, out of `▷ P_fs_named` (the `Hswap` shape) | `emp` |
| `HR0`, `HRt`, `Hpow`, `Htx`, `Hrx` | `xv6_trace_adequacy`'s ledger obligations, with `client_auth γc 0` at the birth | as today |
| `Hphi` | `xv6_power_adequacy_gen`'s, at `Pt := obs_ledger_at (app_R γc)` | as today |

The theorem is `xv6_power_adequacy_gen` at `Pt γobs γc := obs_ledger_at
(app_R γc) γobs`, `Rb dk := P_fs_lend … dk ∗ app_lend dk`, and it threads
`app_fs`, `Happ_boot` and `Happ_lic` to `xv6_boot_era`, which hands them
to `BootShared.boot_shared_alloc` and the mint.  `xv6_trace_adequacy` is
its instance at the fs-trivial application; `xv6_fs_adequacy_xv6Σ` keeps
its statement and its audit.

**Why the boot's lend and not `Hproj`.**  `Hproj` is pure and cannot
carry `tainted`; `Hswap`'s `Rb` is the one resource channel from the
PowerOn arm into a boot (crash.md, "Hswap ALSO CARRIES A RESOURCE OUT"),
and the application's durable knowledge is a resource for exactly the
taint's sake.  For the echo application `app_lend dk :=
⌜pristine (recovery dk)⌝ ∨ client_lb 1`, and `Happ_swap` is a copy-out of
the crash predicate's application conjunct — which does not exist yet
(lane L4).

## 4. The trace side, and the chain across eras

`app_R γc h` owns the client counter and says what the counter means:

    echo_R γc h := client_auth γc (if decide (disc h) then 0 else 1) ∗ echo_out h

`disc h` is the DISCIPLINE, a prefix-closed predicate on the whole history
(uart-trace.md ruling 3: input assumptions are antecedents inside `P`,
never a semantic change): in every power cycle the `ObsUartIn` bytes so
far are a prefix of `(echo hello world\n)*`.  The rx wand keeps the
counter at 0 while the byte keeps the discipline and moves it to 1 the
first time it does not (a `mono_nat_own_update`; monotone, so a later
disciplined byte cannot un-taint).  `echo_out h` is the output-side
resource (lane L7).  The pure export is
`app_phi g h := disc h -> good_out h /\ pristine (v_disk g)`, and `Hphi`
proves it from THREE things it holds at the end of the run: `disc h`
gives `client_auth 0` out of `R`; the crash predicate's application
conjunct (L4) gives `pristine ∨ client_lb 1`; and `client_auth 0 ∗
client_lb 1 ⊢ False` settles it.  No era-local fact is exported, which is
what makes the statement hold across reboots without an identification
gate: the durable side carries the disjunction, the trace side carries
the counter, and they meet only at the end of the trace.

## 5. What the echo application owes, lane by lane

Every lane is a kernel-side or program-side proof; none changes the
record or the theorem.  Priced against the tree as of 2026-09-04.

- **L2 — the license moves to the process.**  Today `fsabs_lic` is
  era-wide in `fsabs_env`, and only the generic application can pay it.
  The echo application needs it PER SYSCALL from the PROCESS: the
  returning-ecall arm of the trap contract gains a persistent give
  `app_lic sc W` (the fd-row pilot's deposit shape at its simplest, the
  `uexecXG.xbundle` precedent for the ambient class), the dispatcher's
  write-kind fires take the license from that give instead of from
  `fsabs_env`, and a verified process pays it at each ecall — trivially
  for read-kind calls and console writes, and by presenting `tainted`
  for anything else.  The generic slot under the echo application is
  `tainted -∗ □ uexec_wp`, minted by sh at the exec that leaves the
  discipline.
- **L3 — every mover fires.**  mkdir, link, iput's free (and any retag
  site the audit `grep ireg_top_retag` names) get AU forms whose fires
  re-sync the copy; then the copy IS the kernel's map (§2's gap).
- **L4 — the crash predicate's application conjunct.**  `P_fs_named`'s
  FS half gains `⌜app_dur D⌝ ∨ client_lb 1` over the committed map,
  re-founded at every group commit from the live copy's `fsabs_ok` (the
  collection at quiescence opens `fsabsN`), framed by every other permit,
  and copied out by `P_fs_swap` into `app_lend`.  "Durable-disk facts
  into `Pc`" (adequacy.md's ruling) is exactly this conjunct.
- **L5 — the console INPUT tie.**  A located receipt on the input side,
  `UartSentLoc`'s twin: the bytes `consoleread` delivers are the
  line-edited image of a segment of the cycle's `ObsUartIn` bytes.  It is
  what lets sh know its input left the discipline, hence what lets sh
  mint `tainted` (L2's last step).  `ConsoleInv.cons_data` holds the raw
  buffer bytes today and nothing ties them to the rx trace.
- **L6 — the programs on the Uk engine with licensed ecalls.**  init and
  sh still run on the old capability engine; echo runs on Uk.  All three
  need the L2 give at every ecall leaf, the exec-site gate at the
  OBSERVED image (`SpecKexecAU`'s slot wand at `/echo`'s bytes, which the
  pristine arm of `fsabs_ok` pins to the image's — `FsShPin`'s shape for
  echo), and fork's real row (the child runs the parent's fork
  continuation, not a generic mint).
- **L7 — the output side.**  `echo_out h` and `good_out`: the console's
  `ObsUartOut` bytes are a prefix of the expected stream for the inputs
  so far, through `UartSentLoc.uart_sent_from` and
  `UartAccepted.run_out_accepted_from`.  Safety only: bytes may never
  appear (uart-trace.md ruling 5).

## 6. Rejected shapes

- **The application predicate as an `iProp` body.**  Needs `Σ` in a
  record that has none (`fscfg`) or a third machine-level slot; a pure
  predicate plus the taint covers the conditional shape the owner asked
  for, and the frag-lending extension (per-node fragments handed to a
  program) is orthogonal to the body's conjunct.
- **A functor/module-type application** (an `APP` module argument on the
  boot chain's Link spine).  The body is used inside DEFINITIONS that ride
  `proc_priv` (`first_tok`), so it must be ambient, not a parameter.  The
  program side (L6's mint sites) IS functor-shaped today (`UEXEC_GEN`) and
  stays so; making the choice reach the top-level theorem is a Link-spine
  sweep priced under L6.
- **The taint pushed into the era's invariant by the rx wand** (the
  ledger naming the era's `fsabs_inv`).  Needs the boot to register its
  names into the ledger at a key it cannot pin (`obs_boots h` versus its
  own `gen_id`), and buys nothing the persistent lower bound does not.
- **An era-side durable tie through `Hproj`.**  Pure; cannot carry the
  taint.  `Rb` is the channel.
- **Exporting the LIVE state at the end of the run.**  `Hphi` cannot name
  an era invariant; only the two fixed-layer slots are nameable
  (adequacy.md).  The durable conjunct (L4) is what is exported.
