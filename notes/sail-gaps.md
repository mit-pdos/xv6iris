# Gaps in the Sail model (as used by this proof)

Places where the official Sail RISC-V model, as imported into this tree, does not express what the RISC-V spec
says. Each entry is to be raised again after the capstone ([OWN.142]).

## SAIL-GAP-1: `fence` i/o bits are dropped at decode (recorded 2026-10-21, [OWN.142])

* **Spec.** The RVWMO FENCE instruction orders four kinds of operation: memory reads (`r`), memory writes (`w`),
  device input (`i`) and device output (`o`). Its i/o bits (`pi`/`po`/`si`/`so`) are the ONLY architectural way to
  order RAM accesses against MMIO accesses. Examples: `fence w,o` before a device doorbell, and `fence iorw,iorw`,
  which `__sync_synchronize()` emits.
* **Sail.** Decode maps the fence onto a barrier kind that has no i/o component (`InstsEnd.lean:18299-18314`):
  * `fence iorw,iorw` becomes `fence rw,rw`;
  * `fence w,o` becomes a no-op.
* **Consequence for this proof.**
  * The graph model built on Sail's labels gives device accesses no fence ordering at all (`gfenceCovers`,
    `WeakRvwmoGraph.lean:235-239`): WEAKER than the spec.
  * The gap is compensated by the trusted platform text (R1): "a RAM access program-ordered before a device access
    of the same hart is ordered before it". That text is STRONGER than the spec and true on QEMU-TCG.
  * The final theorem is therefore about a QEMU-like platform on every UART/PLIC/virtio path.
  * The fix for xv6 bug #1 (a fence before `DRIVER_OK`, `notes/xv6-weak-memory-bugs.md`) cannot be checked by the
    present model.
* **Example.** `virtio_disk_rw` stores the descriptors, executes `fence iorw,iorw`, then stores `QUEUE_NOTIFY`; the
  device then reads the descriptors. EX-IO-1 in `notes/rvwmo-machine-examples.md` has the details (from `notes/rvwmo-spec-audit.md` §2 row 7).
* **Ruling.** [OWN.142]: keep (R1) until the capstone. After it, revisit with the NOTIFY-shape spike and with option
  (b): recover the bits from the instruction word and order device accesses faithfully. See
  `notes/rvwmo-spec-audit.md` Q-AUDIT-1.
