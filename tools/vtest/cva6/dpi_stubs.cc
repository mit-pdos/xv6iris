// dpi_stubs.cc -- the debug transport and the ELF reader, disconnected.
//
// ariane_testharness instantiates SimDTM and SimJTAG, whose DPI ticks CVA6's
// own testbench implements over Spike's fesvr (SimDTM.cc, SimJTAG.cc,
// remote_bitbang.cc).  A vtest run uses no debugger, so both are answered
// with an idle bus: no DMI request, JTAG held in reset-released idle.  The
// tick's return value is the exit code the harness would stop on; 0 = keep
// running.
#include <cstdint>
#include "svdpi.h"

extern "C" int debug_tick(svBit *debug_req_valid, svBit debug_req_ready,
                          int *debug_req_bits_addr, int *debug_req_bits_op,
                          int *debug_req_bits_data, svBit debug_resp_valid,
                          svBit *debug_resp_ready, int debug_resp_bits_resp,
                          int debug_resp_bits_data) {
  *debug_req_valid = 0; *debug_req_bits_addr = 0; *debug_req_bits_op = 0;
  *debug_req_bits_data = 0; *debug_resp_ready = 1;
  return 0;
}

extern "C" int jtag_tick(svBit *jtag_TCK, svBit *jtag_TMS, svBit *jtag_TDI,
                         svBit *jtag_TRSTn, svBit jtag_TDO) {
  *jtag_TCK = 0; *jtag_TMS = 0; *jtag_TDI = 0; *jtag_TRSTn = 1;
  return 0;
}

// rvfi_tracer's ELF access.  It reads the ELF only to find a `tohost` symbol
// (the fesvr end-of-test convention) and to preload memory; a vtest run
// needs neither -- the image is loaded by the testbench and the end of a run
// is the DONE word -- so these report "no ELF, no symbol".  CVA6's own
// elfloader.cc is not used because it includes Spike's fesvr headers.
extern "C" void read_elf(const char *filename) {}
extern "C" char get_section(long long *address, long long *len) { return 0; }
extern "C" void read_section_sv(long long address, const svOpenArrayHandle buffer) {}
extern "C" char read_symbol(const char *symbol_name, unsigned long long *address) {
  *address = 0;
  return 0;
}
