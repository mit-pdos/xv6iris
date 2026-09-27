// vtest_tb.cpp -- the Verilator testbench of the CVA6 vtest platform.
//
// Replaces CVA6's corev_apu/tb/ariane_tb.cpp, which drives a run through
// Spike's fesvr (HTIF tohost, the debug transport).  A vtest run needs none
// of that: the ABI (tools/vtest/abi.h) is "the image at TEXT_BASE, the
// declared regions zero, run until the DONE word appears in the RESULT
// region, read the region back".  So this testbench does exactly that, by
// BACKDOOR access to the testharness's DRAM array -- the same array
// ariane_tb.cpp preloads (the tc_sram inside ariane_testharness.i_sram).
//
//   vtest_tb IMAGE.bin RESULT.out UART.out MAX_CYCLES [ADDR:LEN ...]
//
// IMAGE.bin   the flat image, loaded at TEXT_BASE
// RESULT.out  written with the RESULT region (RESULT_SIZE bytes) at the end
// UART.out    the bytes the 16550 SHIFTED OUT on SOUT (decoded off the wire)
// MAX_CYCLES  give up after this many clock cycles
// ADDR:LEN    regions to zero (hex); the stack and result regions always are
//
// Exit status: 0 = DONE seen, 2 = timed out (RESULT.out is still written, so
// a caller can see how far the program got), 1 = usage/load error.
//
// WHY ALL OF DRAM IS ZEROED FIRST, not only the declared regions: the model's
// memory is the image plus the declared regions and NOTHING ELSE, so an
// access outside them is stuck in the model; on this machine it would read
// whatever the simulator's X-initialisation put there.  Zero is the one fill
// that cannot fabricate a pointer or an instruction, and it makes every run
// of the same image bit-for-bit repeatable.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <vector>
#include <memory>
#include "Variane_testharness.h"
#include "Variane_testharness___024root.h"
#include "verilated.h"

static const uint64_t DRAM_BASE   = 0x80000000ull;
static const uint64_t RESULT_BASE = 0x80100000ull;
static const uint64_t RESULT_SIZE = 0x1000;
static const uint64_t STACK_BASE  = 0x80090000ull;
static const uint64_t STACK_SIZE  = 0x1000;
static const uint32_t DONE_MAGIC  = 0x444f4e45;

double sc_time_stamp() { return 0; }

#define MEM (top->rootp->ariane_testharness__DOT__i_sram__DOT__gen_cut__BRA__0__KET____DOT__i_tc_sram_wrapper__DOT__i_tc_sram__DOT__sram.m_storage)

// DRAM is an array of 64-bit words indexed from DRAM_BASE.
struct Dram {
  uint64_t *w; size_t nwords;
  uint8_t get(uint64_t a) const {
    uint64_t o = a - DRAM_BASE; return (uint8_t)(w[o >> 3] >> (8 * (o & 7)));
  }
  void put(uint64_t a, uint8_t b) {
    uint64_t o = a - DRAM_BASE, s = 8 * (o & 7);
    w[o >> 3] = (w[o >> 3] & ~(0xffull << s)) | ((uint64_t)b << s);
  }
  bool in(uint64_t a, uint64_t n) const {
    return a >= DRAM_BASE && a + n <= DRAM_BASE + 8 * nwords;
  }
};

// THE WIRE, not the register.  The model's serial observation is what left
// SOUT ([u_wire]), not what was written to THR -- under LOOPBACK a byte is
// written and never reaches the wire.  So this decodes 8N1 frames off the
// apb_uart's SOUT pin: a falling edge starts a frame, and the bit time is
// read off the uart's own divisor (16 clocks per bit per divisor unit), so it
// follows whatever baud the program programmed.
struct SerialRx {
  int state = 0;          // 0 idle, 1 in frame
  uint64_t t0 = 0; int bit = 0; uint8_t byte = 0; int prev = 1;
  std::vector<uint8_t> out;
  void tick(uint64_t cyc, int sout, uint32_t divisor) {
    uint64_t bt = 16ull * (divisor ? divisor : 1);
    if (state == 0) {
      if (prev == 1 && sout == 0) { state = 1; t0 = cyc; bit = 0; byte = 0; }
    } else {
      // sample data bit k at the middle of bit k+1 (bit 0 is the start bit)
      uint64_t at = t0 + bt * (bit + 1) + bt / 2;
      if (cyc == at) {
        if (bit < 8) byte |= (uint8_t)(sout << bit);
        bit++;
        if (bit == 9) { out.push_back(byte); state = 0; }  // after the stop bit
      }
    }
    prev = sout;
  }
};

int main(int argc, char **argv) {
  if (argc < 5) {
    fprintf(stderr, "usage: %s IMAGE RESULT.out UART.out MAX_CYCLES [ADDR:LEN...]\n", argv[0]);
    return 1;
  }
  const char *image = argv[1], *resf = argv[2], *uartf = argv[3];
  uint64_t max_cycles = strtoull(argv[4], nullptr, 0);

  Verilated::commandArgs(1, argv);   // no plusargs: rvfi_tracer then loads no ELF
  std::unique_ptr<Variane_testharness> top(new Variane_testharness);

  // reset, as ariane_tb.cpp does
  for (int i = 0; i < 10; i++) {
    top->rst_ni = 0; top->clk_i = 0; top->rtc_i = 0; top->eval();
    top->clk_i = 1; top->eval();
  }
  top->rst_ni = 1;

  Dram d{ (uint64_t *)&MEM[0], sizeof(MEM) / sizeof(uint64_t) };
  memset(d.w, 0, d.nwords * 8);

  FILE *f = fopen(image, "rb");
  if (!f) { perror(image); return 1; }
  std::vector<uint8_t> img;
  for (int c; (c = fgetc(f)) != EOF;) img.push_back((uint8_t)c);
  fclose(f);
  if (!d.in(DRAM_BASE, img.size())) { fprintf(stderr, "image too large\n"); return 1; }
  for (size_t i = 0; i < img.size(); i++) d.put(DRAM_BASE + i, img[i]);
  // the declared regions are already zero; the arguments are checked only so
  // a region outside DRAM is an error here and not a silent difference
  for (int i = 5; i < argc; i++) {
    uint64_t a = strtoull(argv[i], nullptr, 16);
    const char *c = strchr(argv[i], ':');
    uint64_t n = c ? strtoull(c + 1, nullptr, 16) : 0;
    if (!d.in(a, n)) { fprintf(stderr, "region %s outside DRAM\n", argv[i]); return 1; }
  }

  SerialRx rx;
  auto *r = top->rootp;
  uint64_t cyc = 0; bool done = false;
  const uint64_t done_word = (RESULT_BASE - DRAM_BASE) / 8;
  while (cyc < max_cycles) {
    top->clk_i = 0; top->eval();
    top->clk_i = 1; top->eval();
    if (cyc % 2 == 0) top->rtc_i ^= 1;      // as ariane_tb.cpp: mtime ticks
    uint32_t div = ((uint32_t)r->ariane_testharness__DOT__i_ariane_peripherals__DOT__gen_uart__DOT__i_apb_uart__DOT__iDLM << 8)
                 |  (uint32_t)r->ariane_testharness__DOT__i_ariane_peripherals__DOT__gen_uart__DOT__i_apb_uart__DOT__iDLL;
    rx.tick(cyc, r->ariane_testharness__DOT__tx, div);
    cyc++;
    if ((cyc & 63) == 0 && (uint32_t)d.w[done_word] == DONE_MAGIC) { done = true; break; }
  }
  // let a byte already on the wire finish (a frame is at most 10 bit times)
  if (done) {
    for (uint64_t k = 0; k < 16 * 10 * 65536 && (rx.state || k < 64); k++) {
      top->clk_i = 0; top->eval(); top->clk_i = 1; top->eval();
      uint32_t div = ((uint32_t)r->ariane_testharness__DOT__i_ariane_peripherals__DOT__gen_uart__DOT__i_apb_uart__DOT__iDLM << 8)
                   |  (uint32_t)r->ariane_testharness__DOT__i_ariane_peripherals__DOT__gen_uart__DOT__i_apb_uart__DOT__iDLL;
      rx.tick(cyc++, r->ariane_testharness__DOT__tx, div);
    }
  }

  FILE *o = fopen(resf, "wb");
  for (uint64_t i = 0; i < RESULT_SIZE; i++) fputc(d.get(RESULT_BASE + i), o);
  fclose(o);
  FILE *u = fopen(uartf, "wb");
  fwrite(rx.out.data(), 1, rx.out.size(), u);
  fclose(u);
  fprintf(stderr, "%s after %llu cycles\n", done ? "DONE" : "TIMEOUT",
          (unsigned long long)cyc);
  top->final();
  return done ? 0 : 2;
}
