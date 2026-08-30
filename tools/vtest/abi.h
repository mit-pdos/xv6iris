/* abi.h -- THE TEST ABI, shared by the .S sources, tools/vtest/vtest.py and
   vtest-rocq/VTest.v.  Any change here must be made in all three.

   A vtest program is a bare-metal M-mode image.  It runs on QEMU and, byte
   for byte the same image, on the Rocq semantics; the two are compared on
   what the program left in the RESULT region and on what it did to the disk.

   THE REGION LIST IS LOAD-BEARING, not bookkeeping.  The Rocq machine's
   memory is a FINITE gmap, so a load or store outside a declared region is
   STUCK -- the model has no transition and the test fails loudly.  That is
   deliberate: on QEMU such an access would silently read the zero the
   machine happens to have there, and the difference would go unnoticed.  A
   program that wants memory must have it declared here. */

#define TEXT_BASE    0x80000000   /* the image (.text/.data), loaded by QEMU -kernel */
#define STACK_BASE   0x80090000   /* zero-filled; sp starts at STACK_BASE+STACK_SIZE */
#define STACK_SIZE   0x1000
#define RESULT_BASE  0x80100000   /* zero-filled; the observation channel */
#define RESULT_SIZE  0x1000
#define DMA_BASE     0x80200000   /* zero-filled; virtqueue + data buffers */
#define DMA_SIZE     0x2000
/* zero-filled, 4 KB-aligned, four pages: room for an Sv39 root plus a full
   three-level walk.  Declared only by tests that enable paging -- every
   declared byte is a gmap insert on the model side, so this is not free. */
#define PT_BASE      0x80300000
#define PT_SIZE      0x4000

/* RESULT layout: +0 done flag, +4 test-defined status, +8.. payload. */
#define RES_DONE     0
#define RES_STATUS   4
#define RES_PAYLOAD  8
#define DONE_MAGIC   0x444f4e45   /* "DONE", written LAST, after a fence */

/* THE M-MODE BACKSTOP MARKER.  A test whose M-mode handler is an
   abort-and-report backstop writes this to RES_STATUS, records mcause/mepc/
   mtval at +56/+64/+72, and THEN sets DONE_MAGIC so the runner is not left
   waiting.  So DONE here means "the test gave up", not "the test finished",
   and a capture tool MUST refuse such a result: capturing it records the
   failure report as though it were an observation, and the model is then
   asked to reproduce a failure, which is meaningless.

   This has bitten twice.  The pt_ family aborts on the U74 at its very first
   instruction (`csrr menvcfg`, which the core does not implement -- finding
   31), and both times the DONE flag made 7 of them look captured.
   tools/vtest/{vtest,board}.py now reject it by this name. */
#define STATUS_MTRAP 0x4D

/* THE TRAP-RECORD AREA, the second half of the result region, used only by a
   test that includes trap.S and points mtvec at [_vtest_trap].  It is up
   here at a fixed offset rather than chosen per test so that the handler can
   find it with one `li` and no saved register -- which is what lets the
   handler clobber only t0 and t1.  Read trap.S's contract before using it.

     +0            the number of traps taken so far
     +16 + 16*n    trap n: mcause, mepc, mtval, 0                         */
#define RES_TRAPS    0x800
#define RES_TRAPN    RES_TRAPS          /* the count */
#define RES_TRAPREC  (RES_TRAPS + 16)   /* the first record */

/* the two devices the model implements, at their QEMU virt addresses */
#define UART0        0x10000000
#define VIRTIO0      0x10001000

/* ======================================================================
   WHICH MACHINE THIS IMAGE IS BUILT FOR.

   Everything above is the QEMU virt board, and it stays the default: with
   no -D on the command line every macro below is the identity and the
   images tools/vtest/vtest.py builds are byte-for-byte what they always
   were.  A BOARD PROFILE (tools/vtest/board.py, currently the VisionFive 2)
   overrides them, so one .S source builds for both machines.

   THIS IS A DEPARTURE FROM "one binary runs on both machines", and it is
   not a small one -- see tools/vtest/README-hw.md, "What a board image is
   allowed to differ in".  The short version: a capture carries its own
   [<name>_text], so two machines running two images is still two honest
   one-directional claims; what it costs is that a divergence can no longer
   be blamed on the machine alone, and every macro below is therefore a
   place a finding could hide.  Keep the list short and keep it here.
   ====================================================================== */

/* Which hart runs [_vtest_body] and owns the DONE flag.  QEMU virt boots
   hart 0; the JH7110's hart 0 is the E24, a 32-bit monitor core that cannot
   execute this image at all, so a board profile names a U74 instead.  The
   prologue biases every hart's stack slot by this, so the primary always
   gets slot 0 and an AP gets slot 1 -- see vtest.S. */
#ifndef PRIMARY_HART
#define PRIMARY_HART 0
#endif

/* ---- THE PLIC CONTEXT THIS HART OWNS ----------------------------------
 *
 * The PLIC's enable bitmaps and threshold/claim pairs are PER CONTEXT, not
 * per hart, and the context NUMBERING depends on the platform's hart
 * layout.  A test that hardcodes hart 0's is only correct on hart 0.
 *
 *   QEMU virt   every hart has an M and an S context, in that order, so
 *               hart h owns contexts 2h (M) and 2h+1 (S).  Hart 0's S
 *               context is 1 -- which is what these tests used to hardcode.
 *
 *   JH7110      hart 0 is the E24, which is M-MODE ONLY and takes context 0
 *               by itself; the four U74s follow, so U74 hart h owns
 *               contexts 2h-1 (M) and 2h (S).  Our primary is hart 2, whose
 *               S context is 4.
 *
 * Getting this wrong is silent: the enable and the claim land on ANOTHER
 * hart's context (on this board, context 1 is the firmware hart's M
 * context), our hart never sees the interrupt, and the test spins until the
 * runner times it out.  That is why every plic_ case that drives an
 * interrupt through a context was uncapturable on the board. */
#ifdef VTEST_BOARD
#define PLIC_SCTX     (2 * PRIMARY_HART)
#else
#define PLIC_SCTX     (2 * PRIMARY_HART + 1)
#endif
#define PLIC_SENABLE  (0x2000 + PLIC_SCTX * 0x80)
#define PLIC_STHRESH  (0x200000 + PLIC_SCTX * 0x1000)
#define PLIC_SCLAIM   (PLIC_STHRESH + 4)

/* THE HART SLOT, for a test BODY that dispatches on which hart it is.
   vtest.S's prologue already biases the slot it uses for the stack and for
   the primary/AP branch, but a BODY that asks the question again gets the
   RAW mhartid -- and `bnez t0, ap` after `csrr t0, mhartid` then sends the
   PRIMARY down the AP path on any machine whose primary is not hart 0.

   Measured, and it is why this macro exists: conc_lost on the VisionFive 2
   ran the whole race correctly -- both rendezvous, a real lost update --
   and then published nothing, because its `out:` block compared mhartid
   against 0 and the primary was hart 2.  The same bug would bite
   `vtest.py gen --hart 1` on QEMU.

   With PRIMARY_HART = 0 this emits exactly the one instruction it always
   did, so no QEMU image moves.  A test that wants the hart's REAL id (to
   record it, or to index a per-hart device register) must still use `csrr`
   directly -- see core_hart.S and clint_msip.S. */
#if PRIMARY_HART == 0
#define HART_SLOT(r)  csrr r, mhartid
#else
#define HART_SLOT(r)  csrr r, mhartid ; addi r, r, -(PRIMARY_HART)
#endif

/* The stride between two 16550 registers, as a shift.  0 on QEMU virt (the
   registers are adjacent bytes).  The JH7110's UART is a Synopsys DW-APB
   with reg-shift 2, so LSR is at 0x14 and not at 5.  EVERY uart test must
   address the register file through UART_REG(); a bare offset is a bug that
   only shows up on one machine. */
#ifndef UART_REG_SHIFT
#define UART_REG_SHIFT 0
#endif
#define UART_REG(n)  ((n) << UART_REG_SHIFT)

/* The CLINT.  Same address on both machines, and -- unlike the UART, the
   PLIC and the disk -- it is NOT part of DevModel.v's fabric: the Sail
   model dispatches this window itself (DevModel.v's header, [within_mmio_
   readable]), so nothing in the QEMU suite has ever touched it. */
#define CLINT0             0x02000000
#define CLINT_MSIP(h)      (CLINT0 + 4 * (h))
#define CLINT_MTIMECMP(h)  (CLINT0 + 0x4000 + 8 * (h))
#define CLINT_MTIME        (CLINT0 + 0xbff8)
