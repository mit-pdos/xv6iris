# Project: per-hart Bare honouring (G5, part 3 — surfaced by kpt-share)

GOAL: make the Bare arm of `strans_inv` satisfiable on EVERY hart
simultaneously. Without this, `wp_main_secondary_sconf` is not statable:
a secondary hart spends its whole pre-switch phase (the `started` spin
loop, printk("hart %d starting"), kvminithart's prologue) in its Bare
arm, and today at most ONE hart in the system can ever be in Bare.

## The problem (found while landing kpt-share's final batch)

`SRegime.bare_inv` (SRegime.v:332-337) holds **`kmap_auth kmap_M0` at
fraction 1, literally at the static map** — and that is the Bare arm's
REFUTATION MECHANISM, not decoration: `bare_absorb` must conclude
`pa = va`, and the only route is `KMap.kmap_at_M0_static` (a claim
agreeing against the auth-at-`kmap_M0` is necessarily a static identity
entry; a non-identity claim plus that auth is a contradiction). Two
consequences:

- There is ONE auth in the system, so one hart's Bare arm excludes every
  other's — secondaries cannot even spin on `started`.
- The auth is CONSUMED by `kvm_M_mint` at the boot hart's satp switch
  (the map grows by the tramp/kstack entries), so after boot no Bare arm
  can ever be re-established — which is also why `kpt_inv` (which holds
  the grown `kmap_auth M`) cannot exist while any hart is Bare, forcing
  kvminithart to INTERNALIZE the one-way door (`tlb_inv_pt_share` at the
  `csrw satp` step) rather than take `kpt_inv` as a precondition.

Rejected local patches (all checked): fractional auth (the mint needs 1
and the map grows); persistent "map is still static" (a secondary holding
it plus a payload kstack claim derives False — verifies the secondary
vacuously); static-claims agreement alone (needs "this vpn is statically
classified", which the generic leaf cannot supply — `mem_pointsto`
existentially quantifies `ppn`, so a `↦ₘ` at a kstack va is legitimate).

## The designed fix: claim ADMISSIBILITY as a regime field

Two pieces, which together remove the auth from `bare_inv` entirely:

1. **`sr_adm : mword 64 -> Prop`, a new `s_regime` field**, taken as a
   premise by `sr_absorb`. Instances: `True` for `kpt_share_regime` (the
   KPT arm honours every claim); "va's vpn is statically classified"
   (the `addr_is_ram va ∨ addr_is_text va ∨ addr_is_dev va` range form)
   for `bare_regime`. It cannot be a uniform premise — the KPT arm must
   honour kstack/tramp claims.
2. **Bare honouring by two-element agreement instead of auth:** the fact
   "M restricted to static-range vpns is the identity" is MONOTONE-true
   forever (`kvm_M pas` extends `kmap_M0` only at vpns OUTSIDE the
   static range — tramp at the top of VA, the kstack vpns high), so the
   persistent `kmap_static_claims` (already in `hw_config`) plus
   ghost-map-element agreement at the claim's vpn gives `pa = va` for
   any ADMISSIBLE va — no auth, no exclusivity, any number of harts.

Cost: the ~15 `sr_absorb` call sites gain the `sr_adm` premise (the
masked-absorb sweep already touched all of them — same list); the
Bare-phase leaf tier must carry the premise up to whole-function proofs,
which all run pre-switch at CONCRETE kernel addresses (the spin loop,
printk's cone, kvminithart's prologue, the entry/start seam), so each
discharge is a static-range membership check on a literal address. The
`kvm_M_mint` consumption of the auth then stops mattering to anyone
(the auth can retire into `kpt_inv` at the switch, where it already
lives in the landed design).

SEQUENCING: this lands BEFORE `wp_main_secondary_sconf` (it is what
makes the secondary's pre-switch phase provable) and is independent of
[`sched-hart-generic.md`](sched-hart-generic.md), which can proceed in
parallel.
