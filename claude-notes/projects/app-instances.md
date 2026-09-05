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

## 2. Where the two instances live

- **Running:** `InodeRegion.ftop_body γfs` gains the conjunct
  `app_pred app_run I` beside `ghost_map_auth (fs_top γfs) 1 I`.  It is
  the abstract map's HOME, so the claim about the map sits with the map:
  a fire that lends the authority lends the claim; a mover that changes
  the map re-establishes it (`app_step`).  `ftop_body` stops being
  timeless; the mover strips the later off the timeless conjuncts only
  and applies `app_step` under `▷` (round 4's shape).
- **Durable:** `FsDurSnap.P_dur D` becomes
  `∃ g gl gt S, fs_snap (snap_gamma g gl gt) g D S ∗ ∃ γa, app_pred γa (fss_inodes S)`,
  sharing the snapshot's `S`.  `P_dur` stops being timeless; the machine
  layer already treats the crash slot as non-timeless (`◇` in every
  hook), and the two in-tree strips of `P_dur`'s later get round 4's
  treatment.  `FsDurSnap` binds `appcfg` as a section Context; every
  consumer above it already binds `fileG` or passes the record.

## 3. The three crossings, each one `app_xfer`

1. **Commit** (`LogSnapLaw.snap_law`'s proof, at quiescence).  The
   collection already lends the running bundle and the `ftop` authority
   at `I` (`FsCollectAll.col_bodies_acc`; `fss_inodes S = I` on the nose,
   `FsCollect.col_state`).  It now also lends `app_pred app_run I`; the
   law runs `app_xfer` once and packs `∃ γa', app_pred γa' I` into the
   new `P_dur`, returning the running claim to the body.  The WAL stays
   application-agnostic: the law is file-system-supplied and persistent,
   as today.
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
seeding through the kit.  Changed: `ftop_body` (+1 conjunct, −timeless),
`ireg_top_retag` (+1 premise: `app_step` at the moved inum) and its ~20
call sites (trivially at the generic application), `P_dur` (+1 conjunct,
−timeless), `snap_law`'s proof (+1 transport), `P_dur_clone` (+1
transport), `fs_cfg_alloc_snap` (+1 transport, `app_run` chosen there),
`img_P_dur_alloc` (+`app_init`), the `appcfg` record.  Lane L3 ("every
mover fires") dissolves: the claim is at the map's home, so a mover that
does not fire an AU still re-establishes it — with the generic
application's trivial step until a real application's proof supplies a
real one.  Lane L4 dissolves into the transport.

## 6. Open questions for the owner

1. **`app_names : Type` in the record**, or existential names inside
   `app_pred` and no instance index at all?  The index is what lets a
   PROCESS name the running instance's ghosts (e.g. hold the other half
   of a variable the claim owns); without it every application ghost is
   invariant-internal.  Cost: one Type field.
2. **Index by `I` (the raw map) or by `S` (`fs_state_rec`)?**  The map is
   what the fires lend and the movers change; `S` adds the superblock,
   the bitmap's used set and the byte view, which no application has
   asked for.  Proposed: `I`, with `fss_inodes S` at the durable instance.
3. **Should the durable conjunct sit inside `P_dur` (sharing the
   snapshot's `S`) or beside it in `P_fs` at `∀ S, snap_ok S D → …`?**
   Inside is proposed: it is the same binder the snapshot uses, and it is
   what lets a resource-valued claim refer to the state it is about.
4. **The mover's premise shape.**  `app_step` at the raw map with the
   changed inum, or at the abstract-view delta (`FsAbsDelta`)?  The mover
   sees the map; the AU fires already know the delta and can derive the
   raw step from it.  Proposed: raw at the mover, delta-indexed at the
   fires.
