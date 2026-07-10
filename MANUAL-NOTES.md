Some high-level ideas that might be interesting for some eventual paper:

- loop language, no real expr
- vcgen
- predicates capturing config registers (mmode_config, smode_config)
- ghost_var to track interesting config register bits (SIE)
- instr predicate (instr memory points-to, abstract 2-byte vs 4-byte, decode)
- tlb_inv
- minstret_inv (invariant counting retired instructions in minstret register)
- fupd-style spec for stepping one cycle, which enables opening inv like minstret_inv
- interrupt handling with a WP for the address in stvec (kernelvec)
- swtch spec
- acquire/release separation logic spec (standard, but does work)
- kalloc/kfree separation-logic-style specs
- re-proving across source code changes (symbolic names, agent does gruntwork)
- background agent does continuous performance optimizations
- perf: concrete decode + equivalence to symbolic (WpDecodeBridge)

Big things that still need to be done/explored:

- weak memory
  - flat model does instruction re-ordering, which means no sequential stepping through instructions
  - promising model requires future-write reasoning
  - DRF-SC is probably not sufficient to cover all kernel code
- devices
- liveness, or at least deadlock avoidance
- file system
- virtual memory / page tables
- switch to user, trampolines, taking syscall

Don't know where else to put this:

- seems like atomic interrupt masking in mstatus might simplify reasoning
