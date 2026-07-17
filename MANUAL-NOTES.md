Some high-level ideas that might be interesting for some eventual paper:

- loop language, no real expr
- vcgen
- predicates capturing config registers (mmode_config, smode_config)
- ghost_var to track interesting config register bits (SIE)
- instr predicate (instr memory points-to, abstract 2-byte vs 4-byte, decode)
- tlb_inv
- minstret_inv (invariant counting retired instructions in minstret register), clock_inv
- fupd-style spec for stepping one cycle, which enables opening inv like minstret_inv
- interrupt handling with a WP for the address in stvec (kernelvec)
- swtch spec
- acquire/release separation logic spec (standard, but does work)
- kalloc/kfree separation-logic-style specs
- re-proving across source code changes (symbolic names, agent does gruntwork)
- background agent does continuous performance optimizations
- perf: concrete decode + equivalence to symbolic (WpDecodeBridge)
- user-mode exec: predicate for all possible decode results (4-byte and 2-byte), then proof for every instruction in that predicate
- shared CLAUDE.md memory in repo
- device model: DevLoop opcode, concurrent WP, shared access to CPU SEIP
- UART ghost append-only log, includes FIFO (uartputc/uartwrite does not wait to flush), ownership proves no race between TX_IDLE check and THR write
- user-mode exec surprise: WRS.NTO instruction can put HART to sleep from user mode
- start was not enabling ADUE; qemu happened to enable ADUE by default which isn't really correct

Big things that still need to be done/explored:

- weak memory
  - flat model does instruction re-ordering, which means no sequential stepping through instructions
  - promising model requires future-write reasoning
  - DRF-SC is probably not sufficient to cover all kernel code
  - not clear what the Iris program logic rules should look like for weak memory
    - https://plv.mpi-sws.org/gps/
    - https://people.mpi-sws.org/~haidang/publications/thesis.pdf
- liveness, or at least deadlock avoidance
- file system
- virtual memory / page tables

Don't know where else to put this:

- seems like atomic interrupt masking in mstatus might simplify reasoning
- rv64d does tick handling in [loop] outside of [try_step], had to add explicitly to [riscv_step]
