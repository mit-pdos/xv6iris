# BUMP to XV6_REV 163d39b (two UARTs in the kernel)

Branch `bump-163d39b`.  `main` is untouched and green; this branch is RED.

xv6 itself now drives both 16550s: the console on UART0 and printk/panic on
UART1 (0x1000a000, PLIC source 12 -- the model's `Uart1`, already in the
device model).  06ea57f ("no console output on panic") is GONE from the
`verified` branch -- it was the stopgap that kept the UART out of panic's
cone, and the second port replaces it, so **panic prints again**, on UART1.

THE OWNER'S RULING: **UART1's output is unconstrained.**  Nothing has to
track what printk/panic put on that wire, so printk's cone owes no
`uart_sent`, no ledger and no trace obligation -- only that its stores go
through.  Where a credential has to lose a claim, EMPTY it rather than
delete it (`xv6-bump-playbook.md` §8).

## DONE (the mechanical half, and the PLIC plan)

The ELF rebuilt and re-dumped, the decode layer regenerated, and the four
constant sweeps applied and verified: relayout (1494 substitutions over 394
files, zero residue), `fix_proof_imms` (41 pc-anchored sites), the `.rodata`
content sweep (55 literals) and the `.data`/`.bss` remap through the owning
symbol (11).  Every hand-written file was checked to differ from pre-bump
only in an immediate or an address.

`PlicPlan`: `plicinithart` now writes `(1<<10)|(1<<12)|(1<<1)` = 0x1402, so
`plic_dev_irq_mask`, `plic_claim_ret_ok` and `plic_enabled_srcs` carry the
second UART's source and a claim can return it.

**THE `.rodata` SWEEP MUST RUN ONCE, FROM THE PRE-BUMP TEXT.**  Applied
twice, a literal the first pass rewrote can coincide with a DIFFERENT old
string's address and the second pass moves it again -- SpecProcinit's three
lock names form exactly that chain (`nextpid` -> where `proc` used to be).
The redo is cheap: `git checkout main -- iris/`, then gen-code, relayout
(`RELAYOUT_OLD_REV=main` once the bump is committed), imms, `.rodata`,
`.data`.  The `.data` remap is likewise one-shot -- re-running it moves
everything a second symbol-width.

## WHAT IS LEFT

Eleven functions changed SHAPE.  `plicinit` (+1 store), `plicinithart` (the
enable word), `consputc` and `consolewrite` (a `0` argument), `panic` (its
printks are back) and `kvmmake` (+1 `kvmmap`) are ordinary proof work.  The
rest is where the design sits:

- **`uarts[]` REPLACES TWO STATICS.**  `struct uart { uint64 base; void
  (*rx)(int); struct spinlock tx_lock; }`, `sizeof` = 0x28, the array at
  `uarts` (0x8000a2c0, `.data`), `tx_lock` at +16.  `tx_chan` and `tx_lock`
  are gone from the symbol table, so `UartTxInv` names a symbol that no
  longer exists; the sleep channel is now `u` itself (`&uarts[uid]`), and
  there are TWO tx locks, one per port.
  - `base` and `rx` are never written, so they want the persistent
    discarded-word snapshot the boot chain already mints for the GOT slot
    (`BootShared`'s `entry_got` / `boot_ran_phys_word`).  They are in
    `.data`, which `kernel_data` deliberately does NOT cover (it is
    `[text_end, rodata_end)`), so this is a new boot carve, not a reuse.
  - The MMIO address is therefore LOADED, not a constant.  The S-mode
    device leaves are fine with that: they ask `ea = uart_pa i off`, and how
    the address was computed is the caller's business -- what is new is
    proving `uarts[uid].base = uart_base i` from the image.
- **`uartinitone` is a NEW function** (no `Code`/`Spec`/`Proof`/`Link`, no
  `tools/code_manifest.json` row); `uartinit` becomes a two-call wrapper.
  Note `initlock(&u->tx_lock, name)` with "uart0"/"uart1" -- the string
  "uart" is gone, which is why the `.rodata` sweep reports
  `ProofUartinit.v`'s `uart_name_str` as unresolvable.
- **`uartintr` calls `u->rx(c)` through a FUNCTION POINTER** read from
  `.data`.  There is no indirect-call idiom in the tree yet.
- **`kvmmake` maps UART1**, so the kernel page table gains a leaf: vpn
  0x1000a is the SAME l1 slot 128 as UART0 and lands in `l0_dev 32` at slot
  10 (UART0 is slot 0, VIRTIO slot 1).  `KptPt`'s `kpt_mem`/`kpt_tlb_ent`/
  `P_kpt`/`kpt_ok` and the tree layer above them gain that entry.  This is
  also what makes an S-mode store to UART1 translate at all.
- **`devintr` gains the `irq == UART1_IRQ` arm.**  The PLIC plan already
  admits source 12; what is left is the slot side -- `WpUart`'s
  `plic_payload`/`plic_tracked` give every source but the console's an
  `emp` payload, so source 12's claim hands out nothing, which is what
  `uartintr(1)` needs (it has no receive consumer).
- **printk/printint/printptr/panic move to UART1** through the new
  `prputc`.  With the output unconstrained this is the cheap direction: the
  cone needs `uart_inv Uart1 γ1`, UART1's tx lock and the UART1 mapping, and
  owes nothing about the bytes.

Fourteen files still fail in the first `-k` layer; the cones behind the
reshaped functions have not been attempted yet.
