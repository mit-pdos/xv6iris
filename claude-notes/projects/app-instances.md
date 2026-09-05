# PROPOSAL: the application predicate at two instances — running ↔ durable by transport

STATUS: DESIGN PROPOSAL (2026-09-05), not built; iterating with the owner.
Supersedes, if adopted, `design/applications.md` §2's client copy, its
license, and §3's `app_lend`/`Hlend`/`Happ_boot`, and it re-scopes lanes
L3 and L4 of `app-echo.md`.  Nothing here is specific to any application.

## 0. The principle

The kernel already has ONE file-system predicate used at TWO instances:
`fs_state Γ dq S` at the era's running names (distributed across the
era's invariants) and at a fresh durable name family (held whole inside
the crash predicate).  It crosses the boundary between them by a
RESOURCE TRANSPORT, never by a pure fact: the commit copies the running
instance into a fresh durable one (`FsDurXfer.fs_state_xfer_tok`), the
PowerOn arm clones the durable one for the boot (`FsDurSnap.P_dur_clone`),
and the boot mints the new era's running instance from the clone
(`FsCfgSnap.fs_cfg_alloc_snap`).

**The application's predicate gets exactly the same life.**  It is one
predicate `app_pred γa I` over the abstract map `I`, at an INSTANCE `γa`
of the application's own ghost names.  It sits beside the running map's
authority in the running instance and beside the snapshot in the durable
one, and it crosses the boundary by an application-supplied transport,
at the three points the kernel's crosses.  No copy, no license, no
lend, no boot obligation: what was durable IS running after a boot, and
what is running IS durable after a commit, as resources.

## 1. The record

    Class appcfg Σ := MkAppcfg {
      app_names : Type;                                     (* the application's own ghost-name record *)
      app_pred  : app_names -> gmap Z fs_node -> iProp Σ;   (* one predicate, any instance *)
      app_run   : app_names;                                (* the ERA's running instance *)
    }.

`app_names` and `app_pred` are the run's; `app_run` is per era, chosen at
the era mint (the record rides `fileG` as it does today, so it is
ambient below the boot and explicit through the kits and the mint).  The
generic application is `app_names := unit`, `app_pred := fun _ _ => True`.

The application's obligations are three, and only the first is new in
kind:

- **TRANSPORT** (the durability obligation, the only one):

      app_xfer : ∀ γa I, app_pred γa I ==∗ app_pred γa I ∗ ∃ γa', app_pred γa' I

  "a copy of my claim about `I` can be made at fresh names, without
  spending the original".  A pure or persistent predicate pays it by
  duplication; a predicate owning an exclusive token pays it by
  allocating a fresh one (the existential is what lets it).  It is the
  application's `fs_state_xfer_tok`.

- **THE MOVER** (the running obligation, today's license at its true home):

      app_step : ∀ I i n n',  ⌜I !! i = Some n⌝ -∗ app_pred app_run I -∗ app_pred app_run (<[i := n']> I)

  supplied by WHOEVER MOVES THE MAP — the syscall proof, which gets it
  from the process's payload (lane L2) or from an era-wide license.  It is
  a premise of the one mover `InodeRegion.ireg_top_retag`, hence of every
  AU fire that retags, hence of the dispatcher's arm.  The generic
  application's is trivial at every site.

- **ERA 0** (the image):

      app_init : ⊢ |==> ∃ γa, app_pred γa I_img

  consumed once, where `FsDurImg.img_P_dur_alloc` builds the first
  snapshot value-first.

Plus the trace side unchanged (`app_R`, its four steps, `app_phi`, `Hphi`).

## 2. Where the two instances live: SEPARATE invariants, tied by half an authority

Owner's rule (2026-09-05): nothing application-specific inside a kernel
file-system invariant.  The two invariants move together; they are not
one.  What ties an application's claim about `I` to the kernel's `I` is
therefore a SHARED PIECE, and the cheapest piece that already exists is
the map authority itself: `ghost_map_auth γ q m` is fractional, any two
fractions AGREE on `m` (`ghost_map_auth_agree`), and an UPDATE needs the
whole.  So:

- **Running.**  `InodeRegion.ftop_body γfs` keeps exactly what it has,
  with the authority at HALF: `ghost_map_auth (fs_top γfs) (1/2) I`.  The
  application's own invariant, `app_inv := inv appN (∃ I, ghost_map_auth
  (fs_top γfs) (1/2) I ∗ app_pred app_run I)`, holds the other half beside
  the claim.  Agreement pins the two `I`s; the one mover
  (`ireg_top_retag`) needs the whole authority, so it opens BOTH
  invariants and re-establishes the claim (`app_step`) — that is what
  "they move together" means as a resource, and it is enforced by
  ownership, not by discipline.  The kernel's invariant names no
  application anything; its only change is `1` → `1/2` and the mover's
  extra opening.
- **Durable.**  `FsDurSnap.fs_snap` keeps its snapshot authority
  `ghost_map_auth (γtop Γ) 1 (fss_inodes S)` at HALF, and the
  application's durable claim is a SEPARATE conjunct of the crash slot,
  `app_dur := ∃ gt γa I, ghost_map_auth gt (1/2) I ∗ app_pred γa I`, tied
  to the current snapshot by the same agreement.  The crash slot at xv6
  becomes `P_fs_named ∗ app_dur`-shaped, two named predicates side by
  side under the one fixed-layer invariant, exactly as `Pc` and `Pt` are
  two slots: the file system's record is untouched in statement, and the
  application's is its own.  (The snapshot's `gt` is existential inside
  `P_dur`; the tie needs no binder to be shared, because the half
  authority IS the identification.)  Neither predicate is timeless once
  the claim is an arbitrary `iProp`; the machine layer already treats
  the crash slot as non-timeless (`◇` in every hook).

## 3. The three crossings, each one `app_xfer`

1. **Commit** (`LogSnapLaw.snap_law`'s proof, at quiescence).  The
   collection lends the running bundle and the `ftop` authority at `I`
   (`FsCollectAll.col_bodies_acc`; `fss_inodes S = I` on the nose,
   `FsCollect.col_state`).  The application's half of the commit is a
   SECOND law beside the file system's: given the kernel's new snapshot
   authority (its half at `gt`) and the application's running claim at
   the same `I` (read through `app_inv` — the two halves agree), run
   `app_xfer` once and produce `app_dur` at `gt`, returning the running
   claim to `app_inv`.  The WAL stays application-agnostic: it runs two
   persistent laws where it ran one, and the second is supplied by the
   application.
2. **PowerOn** (`FsCrash.P_fs_swap`, the clone).  `P_dur_clone` re-mints
   the snapshot at fresh names; the application conjunct is cloned by
   `app_xfer`.  `P_fs_lend` carries the clone to the boot unchanged in
   shape — the application conjunct rides inside it.
3. **Boot** (`FsCfgSnap.fs_cfg_alloc_snap`).  The mint unpacks the clone,
   founds the era's `γtop` at `fss_inodes S`, and founds the running
   application instance from the clone's `app_pred γa' (fss_inodes S)` by
   `app_xfer` (the fresh name becomes `app_run` of the era's record, which
   is why `app_run` is chosen inside the mint, existentially with
   `fileG`).  Era 0's clone comes from `app_init` through
   `img_P_dur_alloc`.

## 4. What the application sees

- **At a syscall it issues:** an AU fire lends the pre-map `I` and
  `app_pred app_run I`, and takes `app_pred app_run I'` back — the
  process's payload discharges `app_step`.  Read-kind fires lend and
  return the claim untouched.  (Today's fires lend the authority and
  nothing about the application; the copy and its license disappear.)
- **At a commit:** nothing.  The kernel copies the claim.
- **At a boot:** the running home holds `app_pred app_run I0` for the map
  the era was founded at — the last committed state, or the image at era
  0.  A process reads it through any fire or by opening `ftopN`.  "What
  is true of the fresh running state" is therefore exactly "what was true
  of the last committed state", as a resource, with no identification
  gate and no pure detour.
- **At the end of the run:** `Hphi` holds `▷ P_fs_named` and reads
  `∃ γa, app_pred γa (fss_inodes S_final)` off it beside the ledger.

## 5. What it costs, and what it deletes

Deleted: `FsAbsInv`'s client copy and `fsabs_env`, the license, the fire
dischargers' `fsabs_set`, `app_lend`/`Hlend`/`Happ_boot`, the era-0
seeding through the kit.  Changed: `ftop_body` (the authority at `1/2`, −timeless is NOT needed
now — the claim is in the application's own invariant),
`ireg_top_retag` (+1 premise: `app_step` at the moved inum) and its ~20
call sites (trivially at the generic application), `fs_snap` (the authority at `1/2`), the crash slot at xv6 (`P_fs_named ∗
app_dur`), a second commit law beside `snap_law` (the application's
transport), the clone (+1 transport on the application's slot), `fs_cfg_alloc_snap` (+1 transport, `app_run` chosen there),
`img_P_dur_alloc` (+`app_init`), the `appcfg` record.  Lane L3 ("every
mover fires") dissolves: the claim is at the map's home, so a mover that
does not fire an AU still re-establishes it — with the generic
application's trivial step until a real application's proof supplies a
real one.  Lane L4 dissolves into the transport.

## 5½. Who proves the transport, and how often

The APPLICATION proves `app_xfer` ONCE, as a Coq lemma about its own
predicate — a closed entailment `⊢ ∀ γa I, app_pred γa I ==∗ …` with no
resource premise.  It reaches the tree as a premise of the system
theorem (beside `HPc`, `Hswap`, `HPt`), so it is a proof term, usable at
every era and every crossing; nothing consumes it.  Inside an era the
kernel needs it as an `iProp` at the commit's law, and a closed
entailment is freely boxed (`□ (∀ γa I, app_pred γa I ==∗ …)` from the
lemma by `bi.intuitionistically_intro`), so the boot parks the boxed
form beside `LogSnapLaw.snap_law` in `log_ctx` once per era and the
committer reads both laws off the ledger.  Nothing is re-proved per
commit; nothing is per era but the parking.

## 6. Open questions for the owner (2026-09-05, the full list)

1. **The instance index.**  RULED (owner, 2026-09-05): a client BIRTH STEP
   and an explicit `Type` field for the fixed names — `app_fixed : Type`
   born once by `⊢ |==> ∃ c, Cl c` and threaded into the machine's record
   as a dependent pair (`riscv_client_T : Type; riscv_client : riscv_client_T`,
   replacing today's mono-nat name), and `app_names : Type` for the
   per-instance part refreshed by every transport.  The earlier note:
   `app_names` splits into a FIXED part
   (born once, nameable by the fixed layer and the machine's record) and a
   PER-INSTANCE part (refreshed by every transport).  Remaining: the fixed
   part's birth.  Proposed: a client birth step `⊢ |==> ∃ γ, Cl γ` run
   first by the power theorem, its name threaded into the record as
   `γobs` is (today's mono-nat at `riscv_client_name` is the special
   case); `app_pred : gname -> app_names -> gmap Z fs_node -> iProp Σ`,
   fixed name first; `app_names : Type`.
2. **Index by `I` or by `S`.**  RULED `I` (owner): the claim is purely
   about the abstract state; nothing invisible to user-level code.
3. ~~Inside `P_dur` or beside it?~~  RULED beside, tied by half an authority.
4. **The mover's premise.**  Proposed raw at the mover (`<[i := n']> I`,
   the only total form — the landed non-AU movers have no delta
   vocabulary and must open the application's invariant like everyone
   else), delta-indexed at the AU fires where the process's payload
   proves it.  A non-trivial application is green only once every retag
   site has a step; the generic application's is trivial everywhere.
5. **Laters at the crossings.**  The commit's law, the boot mint and the
   PowerOn clone are fupds without a step, so the claim arrives as
   `▷ app_pred` and a basic update cannot run under it; `◇` strips only
   timeless laters.  Either require `Timeless (app_pred …)` or state the
   transport under the later,
   `▷ app_pred γa I ==∗ ▷ app_pred γa I ∗ ▷ (∃ γa', app_pred γa' I)`.
   RULED (owner): the later-shaped transport (timeless claims strip;
   claims holding invariants duplicate under the later); `app_step` stays
   a plain wand, which lifts under the later for free.
6. **Who hands out the halves.**  Each fresh-instance operation of the
   kernel returns the guest half: the snapshot law (`ghost_map_auth gt
   (1/2) I` beside `P_dur`), the PowerOn clone (`P_fs_swap`, via
   `P_dur_clone`), the boot mint (the era's `γtop`).  The collection reads
   the map at the kernel's fraction or borrows the application's half
   while it has the application's invariant open.  One uniform interface,
   three lemmas.  RULED (owner): yes.
7. **The crash slot's composition.**  `Pc := P_fs_named ∗ app_dur_named`
   at xv6; `HPc` = `P_fs_alloc` ∗ the era-0 claim at the image's snapshot
   half; `Hproj` frames the application conjunct; `Hswap` = `P_fs_swap`
   returning the clone's guest half, then the application's later-shaped
   clone, then the lend carrying both.  The machine layer is untouched.
