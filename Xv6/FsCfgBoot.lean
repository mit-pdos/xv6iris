/-
**THE BOOT-SIDE FILE-SYSTEM VOCABULARY** -- a PARTIAL port of Rocq
`FsCfgBoot.v` (`/shared/xv6rocq/iris/FsCfgBoot.v`), batch C-0 item CD of
`notes/briefs/crash_layer.md`.

**WHAT IS HERE.**  The inode region's block set (`ireg_blk_set`, Rocq :449)
and its one list/set conversion (`ireg_blk_of_set`, :483): the set the era
fupd peels off `cov` for the inode-region registry.  Its consumer is
`FsCfgSnap` (batch C-5).

**WHAT IS NOT HERE YET, AND WHY (blockers, not deviations).**

1. `img_node` / `img_nodes` and every `img_*` reading (`img_node_rec`/`_ent`/
   `_blk`/`_bare`, `img_inode_local_free`/`_live`/`img_inode_local`,
   `img_inode_ok_at`, `img_nodes_keys`/`_lookup`/`_lookup_inv`,
   `big_sepM_img_nodes`), `image_dinode_fs_dinode`, `fs_tick_count_cons` and
   `fs_bitmap_spent`, and **`fs_boot_image_wf`**.  Every one is stated over
   Rocq `FsImg.v`'s DINODE READER and W3-W9 SWEEPS (`fs_dinode`,
   `fs_data_of`, `fs_blocks_full`, `fsimg_wf`, `fs_region_wf`,
   `fs_region_bare`, `fs_region_nlink`, `fs_links_eq`, `fs_root_no_self`,
   `fs_inode_ok`, `fs_dir_ok`, `fs_tick_count`, `fs_bmap_set`, ...) and
   `FsImgBridge.v` (`img_blkmap`, `img_inode_ok`, `img_dir_uniq`).  The Lean
   `Xv6/FsImg.lean` is SUPERBLOCK-ONLY by its own header (sections 0, 1, 6,
   7; "the rest of FsImg.v arrives with the decoder/tree waves"), and there
   is no Lean `FsImgBridge`.  Needed first: FsImg.v :242-1900 + :2031-2346
   (reader, sweeps and their `_spec` lemmas; about 2.5k Rocq lines) and
   FsImgBridge.v (476).  D34 keeps `Himg` a PREMISE, but the premise still
   needs these DEFINITIONS.  (`FsDurImg`, agent CF, needs the same stack.)
2. **`fs_boot_snap_wf`** (Rocq :671) is stated over `FsState.fs_state_rec` /
   `fss_sb` (batch C-0, agent CA) and `FsDurSnap.snap_ok` (batch C-1, agent
   CE), plus `FsBoot.fs_cov_in` (W8-H).  Every crash-side ingredient is ready
   (`hdrWf`, `hdrWset`, `fsBlocks`, `fsHome`, `logRegion` in
   `Xv6/FsCrashPure.lean` / `Xv6/LogDefs.lean`).
3. **`fs_boot_supply`** / `fs_boot_supply_app_inv` (Rocq :715/:741) bundle
   `FsCfgKits.fs_kit_icache` / `fs_kit_fsinit_ghost`, which this port does
   not have: `Xv6/FirstTok.lean`'s `firstFsinit` spells the kit's rows out
   unbundled (fs-lean-design §5), and batch C-4 adds the crash rows to it.
   The Lean shape of the supply is a boot-chain (W8-H / C-4) decision.

**CLEANUPS (Rocq gunk, checked uses in `/shared/xv6rocq/iris`).**
`region_of_seq` is `Xv6.regionInums_bigSep` (`Xv6/IcacheBootRegion.lean`,
already ported); `big_sepS_of_elements` is iris-lean's
`BigSepS.bigSepS_elements`.  Not ported, no users outside this file:
`fs_live_blocks`, `big_sepL_to_set`, `big_sepL_omap_mono` (FsImg.v :2325
names it in a comment only), `big_sepL_seq_shift` (ByteBuf/InstrBytes use
their own `Local` copies), the empty `FsCfgBootBitmap` section.
`ireg_blk_list_nodup` is kept (it is the proof of `ireg_blk_of_set`).

**DEVIATIONS.**  `Nat` block numbers; the set is a `Std.ExtTreeSet Nat
compare` built with `LawfulSet.ofList`, exactly as `regionInums` is.
-/
import Xv6.IcacheBootRegion

namespace Xv6

open Iris Iris.BI Iris.Std Std

/-- The inode region's blocks, `[ist, ist + nib)` (Rocq `ireg_blk_set`). -/
def iregBlkSet (ist nib : Nat) : ExtTreeSet Nat compare :=
  LawfulSet.ofList ((List.range nib).map (fun bi => ist + bi))

theorem iregBlkList_nodup (ist nib : Nat) :
    ((List.range nib).map (fun bi => ist + bi)).Nodup :=
  MachCSL.nodup_map_of_inj _ (fun _ _ h => Nat.add_left_cancel h) List.nodup_range

/-- Rocq `ireg_blk_set_spec`. -/
theorem iregBlkSet_spec (ist nib b : Nat) : b ∈ iregBlkSet ist nib ↔ ist ≤ b ∧ b < ist + nib := by
  unfold iregBlkSet
  rw [← LawfulSet.mem_ofList, List.mem_map]
  constructor
  · rintro ⟨bi, hbi, rfl⟩; rw [List.mem_range] at hbi; omega
  · intro h; exact ⟨b - ist, List.mem_range.2 (by omega), by omega⟩

/-- The one conversion: the set-indexed big-op over the region's blocks IS
the list-indexed one over block indices (Rocq `ireg_blk_of_set`, stated as
the equivalence it is). -/
theorem iregBlk_of_set {PROP : Type _} [BI PROP] (Φ : Nat → PROP) (ist nib : Nat) :
    ([∗set] b ∈ iregBlkSet ist nib, Φ b) ⊣⊢ [∗list] bi ∈ List.range nib, Φ (ist + bi) := by
  unfold iregBlkSet
  refine (BigSepS.bigSepS_of_list (iregBlkList_nodup ist nib)).trans ?_
  exact BiEntails.of_eq (BigSepL.bigSepL_map (PROP := PROP) (fun bi => ist + bi)
    (Φ := fun _ b => Φ b))

end Xv6
