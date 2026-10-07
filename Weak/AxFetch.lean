/-
Weak/AxFetch.lean — umbrella for the split port of Rocq `AxFetch.v` (4,951 lines; track F, first slice:
acert → fetch/decode → `astepProg`).

The port is split by section (the sections' dependency graph allowed parallel ports):
- `AxFetch1`  — header, §1 row shapes of ld8/sd8, §2.0 register-tower peel, §2.1 ld8 instantiation
  (the full file header — what AxFetch proves, the Stage C deviation, name map — lives there);
- `AxFetch2`  — §2.2–2.4 ld8/sd8 row runs (`AxFetch2.fetchPeel`);
- `AxFetch3`, `AxFetch3b`, `AxFetch3c` — §2.5–2.8 jalr/ret, RVC fetch twin, c.ldsp/c.sdsp, `afCldspContRd`;
- `AxFetch4`  — §3 the two-event demonstration;
- `AxFetch5`  — §4–4.8 the c.jr ra control gate (`afCjrRdsAtNextpc`).

Downstream files import `Weak.AxFetch` (this module) as they imported Rocq's `AxFetch`.
-/
import Weak.AxFetch1
import Weak.AxFetch2
import Weak.AxFetch3
import Weak.AxFetch3b
import Weak.AxFetch3c
import Weak.AxFetch4
import Weak.AxFetch5
