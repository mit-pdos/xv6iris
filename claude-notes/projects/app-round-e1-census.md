# Round E1 census — every `ireg_top_retag_auto` / `_armed_auto` site at HEAD 70682c6bb

grep gives 35 hits: 4 are comment mentions (FsAbsInvFire.v:28, ProofCreateAU.v:1705,
ProofCreateAUF.v:1726, ProofCreateShared.v:1621) and 31 are real `iMod` sites — 22 `_auto`
and 9 `_armed_auto` (the three `cr_dirty_{arm,retag,clear}` helpers, copied into
ProofCreateShared / ProofCreateAU / ProofCreateAUF).  The 9 helper sites are generic in
`n n'`, so they are classified BY THEIR CALLERS (sub-rows).

Delta vocabulary: fs-syscall-specs.md §4 (δ_create, δ_link, δ_unlink, δ_write, δ_free).
"AU fire?" = whether the site sits inside an AU fire that already carries the contract's
`app_step` (the six write-kind fires in FsAbs*Fire.v pay via `app_top_update`/`app_step_at`
and are NOT `_auto` sites; every `_auto` site below sits OUTSIDE those fires).

| # | file:line | syscall / path | n → n' (what moves in the node) | class | delta | AU fire? | (S) argument |
|---|---|---|---|---|---|---|---|
| 1 | EscrowDeposit.v:243 | iput's free path, the escrow deposit | `ntop` (∃, the freed payload's untied fragment) → `free_node dn'` (type-0 bare record) | D | δ_free (orphan → free) | no — landed non-AU iput | — |
| 2 | ProofIlock.v:1271 | ilock's fresh-inode claim (every create path) | `n0` (∃, untied fragment from `ireg_withdraw`) → claim box `era_node dn bm_empty zeros` (free → typed) | D | δ_create's "i fresh" leg | no — non-AU (called by every create) | — |
| 3 | ProofSysOpen.v:1199 | non-AU open, O_TRUNC (`so_stores`) | `era_node dn bm data` → `era_node (di_trunc dn) bm_empty zeros`: `AFile bs → AFile []` | D | δ_write (delta_trunc) | no — landed non-AU open (the AU open has its own `so_stores_au` + `opf_atrunc_fire`) | — |
| 4 | ProofSysLinkTails.v:1438 | link's bad tail (second instant failed) | `era_node dn bm dat` → `era_node (sl_setnl dn …) bm dat`: nlink lowered back | D | δ_link failure arm (target nlink−1) | no — landed non-AU link | — |
| 5 | ProofFilewrite.v:2314 | non-AU filewrite | `(dnl,bml,datal)` → `(dn',bm',data')`: bytes + size | D | δ_write | no — landed non-AU write | — |
| 6 | ProofFilewriteAU.v:2971 | AU filewrite, "the chunk does not fire" arm (`rz ≠ c`) | `(dnl,bml,datal)` → `(dn',bm',data')`: a SHORT chunk still moves bytes; writei's `-1` sub-arm leaves the node unchanged but `Hjoin` (2676) discards `dn' = dnl`/`bm' = bml`/`data' = datal` | D | δ_write (partial arm) | on the AU contract, but OUTSIDE the fire (the partial arm `fw_au_raw_spend_part` carries no `app_step`) | (`rz = -1` sub-arm would be S if `Hjoin` kept the arm's equalities) |
| 7 | ProofCreateAlloc.v:1244 | non-AU create, successful dirlink at the parent | `era_node dn bm data` → `era_node dn' bm' data'`: entries += name | D | δ_create's directory leg | no | — |
| 8 | ProofCreateShared.v:1634 `cr_dirty_arm` ← ProofCreateAlloc.v:453 | non-AU create, child arm | claim box `era_node dnc bmc datc` → `cr_setf dnc major minor 1`: nlink 0→1 (+major/minor) | D | δ_create's fresh-node leg | no | — |
| 9 | ProofCreateShared.v:1649 `cr_dirty_retag` ← ProofCreateMkdir.v:2500 | non-AU mkdir, parent-append FAILED arm, child | `cr_setf dnc … 1` → `dc2 bm2 dat2`: dots written, nlink → 0 | D | mkdir failure arm (child un-born) | no | — |
| 10 | ProofCreateShared.v:1649 `cr_dirty_retag` ← ProofCreateMkdir.v:2638 | non-AU mkdir, ".." dirlink FAILED arm, child | `cr_setf dnc … 1` → `dc2 bm2 dat2`: "." written, nlink → 0 | D | mkdir failure arm | no | — |
| 11 | ProofCreateShared.v:1649 `cr_dirty_retag` ← ProofCreateMkdir.v:2769 | non-AU mkdir, "." dirlink FAILED arm (`tot1 = 0`), child | `cr_setf dnc … 1` → `dc1 bm1 dat1`: type same (T_DIR, `Hc1ty0`), nlink 1 both (`Hc1nl`), size 0 both (`Hc1szmax`, `Hcsz0`, `Htot10`) | **S** | — | no | both read `MkAnode (ADir ∅) 1`: `dir_nrec_zero` + `dir_view_nil` (new `abs_of_dir_same` + `dir_entries_size_0`) |
| 12 | ProofCreateShared.v:1665 `cr_dirty_clear` ← ProofCreateAlloc.v:830 | non-AU create, FILE arm's disarm | `n = n'` syntactically | **S** | — | no | `eq_refl` |
| 13 | ProofCreateShared.v:1665 `cr_dirty_clear` ← ProofCreateMkdir.v:2344 | non-AU mkdir success, child after dots | `cr_setf dnc … 1` → `dc2 bm2 dat2`: entries "." ".." added | D | δ_create(ADir + dots) | no | — |
| 14 | ProofCreateMkdir.v:2110 | non-AU mkdir success, parent | `era_node dn bm data` → bumped `cr_setf dp3 … (nlink+1)`: append + d.nlink+1 | D | δ_create(ADir) fused d.nlink+1 | no | — |
| 15 | ProofCreateMkdir.v:2500 (parent) | non-AU mkdir, parent-append FAILED arm, parent | `era_node dn bm data` → `era_node dp3 bm3 dat3`: dirlink wrote nothing (`Heqentm`, `Hp3ty`, `Hp3nl`) | **S** | — | no | `dir_entries_dirlink_nop_eq` already in scope; type and nlink ride |
| 16 | ProofCreateFail.v:474 | non-AU create, dirlink FAILED arm, child | `cr_setf dnc … 1` → `cr_setf dnc … 0`: nlink 1→0 | D | create failure arm (child un-born) | no | — |
| 17 | ProofCreateFail.v:722 | non-AU create, dirlink FAILED arm, parent | `era_node dn bm data` → `era_node dn' bm' data'`: nop dirlink (`Heqent0`, `Hty'`, `Hnl'`) | **S** | — | no | `dir_entries_dirlink_nop_eq` in scope |
| 18 | ProofCreateAU.v:1718 `cr_dirty_arm` ← ProofCreateAU.v:4882 | AU create (mknod), child arm | claim box → `cr_setf dnc … 1`: nlink 0→1 | D | δ_create's fresh-node leg | AU contract, OUTSIDE the fire (`FsAbsMknodFire` moves the parent row `d` only) | — |
| 19 | ProofCreateAU.v:1733 `cr_dirty_retag` | (no callers — dead copy; only ProofCreateMkdir uses `cr_dirty_retag`) | — | dead | — | — | delete |
| 20 | ProofCreateAU.v:1749 `cr_dirty_clear` ← ProofCreateAU.v:5187 | AU create, FILE arm's disarm | `n = n'` syntactically | **S** | — | — | `eq_refl` |
| 21 | ProofCreateAU.v:6630 | AU create, dirlink FAILED arm, child | `cr_setf dnc … 1` → `cr_setf dnc … 0`: nlink 1→0 | D | create failure arm | AU contract, outside the fire | — |
| 22 | ProofCreateAU.v:6878 | AU create, dirlink FAILED arm, parent | nop dirlink (`Heqent0`, `Hty'`, `Hnl'`) | **S** | — | — | `dir_entries_dirlink_nop_eq` in scope |
| 23 | ProofCreateAUF.v:1739 `cr_dirty_arm` ← ProofCreateAUF.v:5164 | AU create at T_FILE, child arm | nlink 0→1 | D | δ_create's fresh-node leg | AU contract, outside the fire | — |
| 24 | ProofCreateAUF.v:1754 `cr_dirty_retag` | (no callers — dead copy) | — | dead | — | — | delete |
| 25 | ProofCreateAUF.v:1770 `cr_dirty_clear` ← ProofCreateAUF.v:5470 | AU create at T_FILE, disarm | `n = n'` | **S** | — | — | `eq_refl` |
| 26 | ProofCreateAUF.v:6910 | AU create at T_FILE, dirlink FAILED arm, child | nlink 1→0 | D | create failure arm | AU contract, outside the fire | — |
| 27 | ProofCreateAUF.v:7158 | AU create at T_FILE, dirlink FAILED arm, parent | nop dirlink (`Heqent0`, `Hty'`, `Hnl'`) | **S** | — | — | `dir_entries_dirlink_nop_eq` in scope |
| 28 | ProofSysLink.v:1934 | non-AU link, target | `era_node dn bm dat` → `era_node (sl_incnl dn) bm dat`: nlink+1 | D | δ_link (target nlink+1) | no — landed non-AU link | — |
| 29 | ProofSysLink.v:3091 | non-AU link, new parent, dirlink succeeded | entries += name | D | δ_link (directory leg) | no | — |
| 30 | ProofSysLink.v:3582 | non-AU link, new parent, dirlink wrote nothing (`Htot0`) | nop dirlink (`Heqentd`, `Htyeq`) | **S** | — | no | `dir_entries_dirlink_nop_eq` in scope |
| 31 | ProofSysUnlinkW5File.v:1391 | non-AU unlink (file), parent | entry deleted (`Hentsd`) | D | δ_unlink (parent delete) | no — landed non-AU unlink (the AU unlink is `ProofSysUnlinkAUW5F` + `FsAbsUnlinkFire`) | — |
| 32 | ProofSysUnlinkW5File.v:1777 | non-AU unlink (file), target | `su_setnl`: nlink−1 | D | δ_unlink (target nlink−1) | no | — |
| 33 | ProofSysUnlinkW5Dir.v:1971 | non-AU unlink (dir arm), parent | entry deleted + d.nlink−1 | D | δ_unlink dir arm | no | — |
| 34 | ProofSysUnlinkW5Dir.v:2402 | non-AU unlink (dir arm), child dir | `su_setnl`: nlink−1 (→ 0, orphan) | D | δ_unlink dir arm (child grey) | no | — |

## Totals (31 real mover sites; 34 rows because the 3 shared helpers have several callers)

- **S (view-preserving), convertible now: 9 rows** — #11, #12, #15, #17, #20, #22, #25, #27, #30.
  At the helper level: ProofCreateAU/AUF `cr_dirty_clear` (2 sites, sole callers are `n = n'`)
  become `_armed_same`; ProofCreateShared gains `_same` twins of `cr_dirty_clear`/`cr_dirty_retag`
  for #11/#12 while the `_auto` originals keep serving #9/#10/#13.
- **Dead: 2 sites** — #19, #24 (`cr_dirty_retag` copies with no callers): deleted.
- **D inside an AU fire with the step in scope: 0.**  Every AU fire already pays via
  `app_top_update` + `app_step_at`; no `_auto` site sits inside one.
- **D, stays `_auto` (round E2's worklist): 20 sites** — #1–#10, #13, #14, #16, #18, #21,
  #23, #26, #28, #29, #31–#34.  At the helper level that is 17 `_auto` + 5 `_armed_auto`
  (Shared's arm/retag/clear, AU's arm, AUF's arm) = 22 remaining sites.
