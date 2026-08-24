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

/* the two devices the model implements, at their QEMU virt addresses */
#define UART0        0x10000000
#define VIRTIO0      0x10001000
