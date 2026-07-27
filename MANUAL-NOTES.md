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
- intr_inv and WP wrapper wp_instr_s_intr does induction over any number of interrupts
- sie_inv owns free stack locations, requires sufficient depth for interrupt/kernelvec
- swtch spec
- acquire/release separation logic spec; holding token is CPU-specific (can transfer across swtch but cannot have another CPU do the release)
- kalloc/kfree separation-logic-style specs
- kalloc_avail tracks number of free pages, for early-boot tracking; then switches to None
- re-proving across source code changes (symbolic names, generic decode Ltac, agent does gruntwork)
- background agent does continuous performance optimizations
- perf: concrete decode + equivalence to symbolic (WpDecodeBridge)
- user-mode exec: predicate for all possible decode results (4-byte and 2-byte), then proof for every instruction in that predicate
- shared CLAUDE.md memory in repo
- device model: DevLoop opcode, concurrent WP, shared access to CPU SEIP
- UART ghost append-only log, includes FIFO (uartputc/uartwrite does not wait to flush), ownership proves no race between TX_IDLE check and THR write; should allow concurrent rx + tx
- user-mode exec surprise: WRS.NTO instruction can put HART to sleep from user mode
- start was not enabling ADUE; qemu happened to enable ADUE by default which isn't really correct
- userret: tricky state at second sfence.vma: new page table but old TLB contents (TransPt.v); not needed during kvminithart because Bare has no TLB entries
- kpt_regime: unified Bare + Sv39 page-table configurations
- needed axioms about load_reservation and cancel_reservation, which aren't specified in Sail model
- push_off returns intr_count counting token, which is needed to call pop_off to ensure no panic
- use fable to state specs, opus to prove them
- kernel ptsto: PA own + VA map fact via kmap_at (code RX, data RW), monotonic for Bare-to-Sv39
- page tables need to track kmap_at for intermediate PT pages, to reconstruct data ptsto
- MMIO just needs mapping fact, no memory points-to (because it's not memory)
- kvminithart: need strans_bit to track whether satp is currently Bare or Sv39
- filedup ref overflow: track which [fd_slot] owns a reference; there can't be more than 2^31
- cancellable lock invariant: pipe->lock needs to be cancelled when underlying pipe page is freed; pipe lock invariant conditional on holding a reference on pipe

Big things that still need to be done/explored:

- weak memory
  - flat model does instruction re-ordering, which means no sequential stepping through instructions
  - promising model requires future-write reasoning
  - DRF-SC is probably not sufficient to cover all kernel code
  - not clear what the Iris program logic rules should look like for weak memory
    - https://plv.mpi-sws.org/gps/
    - https://people.mpi-sws.org/~haidang/publications/thesis.pdf
- liveness, or at least deadlock avoidance
  - acquire currently calls panic if already holding lock on same CPU
  - lock ordering could solve deadlock and acquire's panic
- crash reasoning for file system

Don't know where else to put this:

- seems like atomic interrupt masking in mstatus might simplify reasoning
- rv64d does tick handling in [loop] outside of [try_step], had to add explicitly to [riscv_step]
