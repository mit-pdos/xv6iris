/-
**THE FILE SYSTEM's NI VOCABULARY, PURE** (NI M3 private files; design of
record `claude-notes/projects/noninterference.md`, "M3 private files design
(2026-10-05)", findings F3/F4/F7/F8, rulings FS-R2/R3/R5).

Lane FS-0 lands the one type its reasons name: `FsFull`, the three global
tables an fs call can find exhausted -- the inode table (`ialloc: no
inodes`, create's `-1`), the free-block bitmap (`balloc: out of blocks`,
writei's short count, filewrite's and dirlink's `-1`) and the open-file
table (`filealloc` at `NFILE`, open's and pipe's `-1`).  They are the
out-of-resources VERDICTS the design records AS GIVEN (FS-R3): no row can
compute them, so the kernel's word is carried.

F8: this module is self-contained and pure (no ghost state, no kernel
definition), so that the NI roots' trusted base grows by it alone when the
rows come to read it.
-/

namespace Xv6

/-- (NI M3 FS-0) the three global fs tables a call can find exhausted. -/
inductive FsFull where
  /-- the inode table: `ialloc` scanned every dinode and found none free -/
  | inodes
  /-- the free-block bitmap: `balloc` found no clear bit below `sb.size` -/
  | blocks
  /-- the open-file table: `filealloc` found all `NFILE` entries in use -/
  | files
  deriving DecidableEq, Repr

end Xv6
