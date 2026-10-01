/-
MachCSL: supervisor-mode data memory at the Bare tier -- the physical read
and write stage lemmas, and the execute stages of the loads and stores
over the register file (`execSpecF_lbu`, `execSpecF_ld`, `execSpecF_lw`,
`execSpecF_sb`, `execSpecF_sd`, `execSpecF_sw`).  This module is the
umbrella: each rule is its own module (`MachCSL.WpSmodeMemLbu` ...), their
shared scripts are `MachCSL.WpSmodeMemTac`, so the six proofs (1.2-2 s each)
run in parallel rather than in sequence in one 9 s file.  Under xv6's PMP
tables every kernel access inside RAM passes; at `satp = Bare` virtual =
physical.
-/
import MachCSL.WpSmodeMemTac
import MachCSL.WpSmodeMemLbu
import MachCSL.WpSmodeMemLd
import MachCSL.WpSmodeMemLw
import MachCSL.WpSmodeMemSb
import MachCSL.WpSmodeMemSd
import MachCSL.WpSmodeMemSw
