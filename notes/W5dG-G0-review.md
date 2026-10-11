# W5d-G G0 — post-merge adversarial review (2026-10-10, 3 lenses: fidelity, slots, Zifencei)

Verdict: OK (no blocking issue). `Weak/GraphFetchSpike.lean` matches `notes/W5dG-spike.md` and plan §B(4)(iii);
deviations R1–R10 in its header are justified. Carry into G1 (after W13 (M), [OWN.24]):

1. **emZifencei slot numbering (R8) — CONFIRMED.** `HEpair` (`Weak/WeakRvwmoConf.lean:703-714`) emits two row items
   tagged `some k` for one slot; the report's gloss "#row items before n" over-counts after a pair (Z2 checked
   against a later own write = weaker than (H3); fence.i sites in [k, k+p) counted as contributors = stronger).
   `emSlot` (first row item's tag at/after n) is hemit's real slot. Owner asked to confirm (non-blocking).
2. `emSlotAdm` covers a block at the HEAD of the list only; add `emSlotShift` (emSlot (pre ++ its) (|pre|+n) =
   emSlot its n when a row item follows) or a hemit-induction corollary in G1.
3. `emSlot`'s past-the-end default double-counts pairs — unreachable for hemit emissions; document or use slot count.
4. **(Z2) is WEAKER than its own named reading (H3)** (copied verbatim from the report, not a re-creation defect):
   (Z2) bounds the source only by the FIRST own write at/after slot k (`gnxw`); under RVWMO a later own store w to a
   different address may be gmo-before nxw, so gzFetch admits a fetch reading the hart's own LATER store — a
   single-hart cycle w →E1 nxw →gpow w that RVWMO alone cannot kill. Fix in G1: state (Z2) as (H3) reads (every own
   write at/after k is gmo-after the source), or adopt R1 (a)'s E1′ (plan:1096), listing it in §B(11) as the
   stronger reading.
5. Docs: header :8 says emZifencei VERBATIM (R8 changed the slot function); gzFetchCut docstring ":262 q ≤
   next-own-write" should read "<"; out-of-scope list should say R1 (a) E1′ will strengthen (Z2)/(H3) in G1.
6. Spec note for §B(11): Sail `fetch` (`LeanRV64D/Fetch.lean:253-288`) does one 4-byte read at 4-aligned pc when
   Ext_Ziccif is on (`PlatformConfig.lean:2157`), so (Z3)'s "one fill instant per label" follows from Sail + Ziccif;
   only (H1)'s no-forwarding half is a stronger hardware reading.
