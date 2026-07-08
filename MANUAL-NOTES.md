Some high-level ideas that might be interesting for some eventual paper:

- loop language, no real expr
- vcgen
- predicates capturing config registers (mmode_config, smode_config)
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

Big things that still need to be done/explored:

- weak memory
- devices
- liveness, or at least deadlock avoidance
- file system
- virtual memory / page tables
- switch to user, trampolines, taking syscall

Don't know where else to put this:

- seems like atomic interrupt masking in mstatus might simplify reasoning
