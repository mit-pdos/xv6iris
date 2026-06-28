/-
The whole xv6 boot ALL THE WAY THROUGH `consoleinit()`, on the real Sail model:
boot, `start()`/`mret` into supervisor-mode `main`, then `main` calls `cpuid()`
and `consoleinit()` — which runs `initlock`, `uartinit` (UART MMIO at 0x10000000),
`initlock` again, and wires up `devsw` — and returns. 145 real `try_step`s, all in
the right privilege modes (M for boot, S for main/consoleinit).

Built on the whole-machine-state engine `KernelMain.wp_run`: `wp_through_consoleinit`
runs all 145 steps from one operational reduction, and it CHAINS `wp_boot_to_main1`
(its first 56 steps) with `wp_console_from_main1` (89 more), via `runSteps_add`. No
per-instruction lemmas; UART MMIO is just plain memory writes (not `within_mmio`),
and S-mode/privilege transitions need no special handling (all in the one state
cell). Big R/W/X PMA region covers RAM + the UART device. `make kernel-console`.
-/
import Xv6Iris.KernelMain
import LeanRV64D

open Iris Iris.BI Iris.ProgramLogic Std
open Xv6Iris.Model Xv6Iris.Model.KernelMain
open LeanRV64D.Defs LeanRV64D.Functions PreSail

set_option maxRecDepth 16000000
set_option maxHeartbeats 16000000000

namespace Xv6Iris.Model.KernelConsole

noncomputable def bigPMA : PMA := { (default : PMA) with
  executable := true, readable := true, writable := true }
/-- One big region covering RAM (0x80000000+) AND the UART device (0x10000000). -/
noncomputable def bigRegion : PMA_Region :=
  { base := 0x0#64, size := 0x90000000#64, attributes := bigPMA, include_in_device_tree := false }

/-- Kernel text for every function on the path: start/timerinit, main, cpuid,
consoleinit, initlock, uartinit. -/
noncomputable def mem0 (a : Nat) : Option (BitVec 8) :=
  if a = 0xFFFFFFFFFF then some 0
  else if a = 0x8000001c then some 0x41
  else if a = 0x8000001d then some 0x11
  else if a = 0x8000001e then some 0x6
  else if a = 0x8000001f then some 0xe4
  else if a = 0x80000020 then some 0x22
  else if a = 0x80000021 then some 0xe0
  else if a = 0x80000022 then some 0x0
  else if a = 0x80000023 then some 0x8
  else if a = 0x80000024 then some 0xf3
  else if a = 0x80000025 then some 0x27
  else if a = 0x80000026 then some 0xa0
  else if a = 0x80000027 then some 0x30
  else if a = 0x80000028 then some 0x7d
  else if a = 0x80000029 then some 0x57
  else if a = 0x8000002a then some 0x7e
  else if a = 0x8000002b then some 0x17
  else if a = 0x8000002c then some 0xd9
  else if a = 0x8000002d then some 0x8f
  else if a = 0x8000002e then some 0x73
  else if a = 0x8000002f then some 0x90
  else if a = 0x80000030 then some 0xa7
  else if a = 0x80000031 then some 0x30
  else if a = 0x80000032 then some 0xf3
  else if a = 0x80000033 then some 0x27
  else if a = 0x80000034 then some 0x60
  else if a = 0x80000035 then some 0x30
  else if a = 0x80000036 then some 0x93
  else if a = 0x80000037 then some 0xe7
  else if a = 0x80000038 then some 0x27
  else if a = 0x80000039 then some 0x0
  else if a = 0x8000003a then some 0x73
  else if a = 0x8000003b then some 0x90
  else if a = 0x8000003c then some 0x67
  else if a = 0x8000003d then some 0x30
  else if a = 0x8000003e then some 0xf3
  else if a = 0x8000003f then some 0x27
  else if a = 0x80000040 then some 0x10
  else if a = 0x80000041 then some 0xc0
  else if a = 0x80000042 then some 0x37
  else if a = 0x80000043 then some 0x47
  else if a = 0x80000044 then some 0xf
  else if a = 0x80000045 then some 0x0
  else if a = 0x80000046 then some 0x13
  else if a = 0x80000047 then some 0x7
  else if a = 0x80000048 then some 0x7
  else if a = 0x80000049 then some 0x24
  else if a = 0x8000004a then some 0xba
  else if a = 0x8000004b then some 0x97
  else if a = 0x8000004c then some 0x73
  else if a = 0x8000004d then some 0x90
  else if a = 0x8000004e then some 0xd7
  else if a = 0x8000004f then some 0x14
  else if a = 0x80000050 then some 0xa2
  else if a = 0x80000051 then some 0x60
  else if a = 0x80000052 then some 0x2
  else if a = 0x80000053 then some 0x64
  else if a = 0x80000054 then some 0x41
  else if a = 0x80000055 then some 0x1
  else if a = 0x80000056 then some 0x82
  else if a = 0x80000057 then some 0x80
  else if a = 0x80000058 then some 0x41
  else if a = 0x80000059 then some 0x11
  else if a = 0x8000005a then some 0x6
  else if a = 0x8000005b then some 0xe4
  else if a = 0x8000005c then some 0x22
  else if a = 0x8000005d then some 0xe0
  else if a = 0x8000005e then some 0x0
  else if a = 0x8000005f then some 0x8
  else if a = 0x80000060 then some 0xf3
  else if a = 0x80000061 then some 0x27
  else if a = 0x80000062 then some 0x0
  else if a = 0x80000063 then some 0x30
  else if a = 0x80000064 then some 0x79
  else if a = 0x80000065 then some 0x77
  else if a = 0x80000066 then some 0x13
  else if a = 0x80000067 then some 0x7
  else if a = 0x80000068 then some 0xf7
  else if a = 0x80000069 then some 0x7f
  else if a = 0x8000006a then some 0xf9
  else if a = 0x8000006b then some 0x8f
  else if a = 0x8000006c then some 0x5
  else if a = 0x8000006d then some 0x67
  else if a = 0x8000006e then some 0x13
  else if a = 0x8000006f then some 0x7
  else if a = 0x80000070 then some 0x7
  else if a = 0x80000071 then some 0x80
  else if a = 0x80000072 then some 0xd9
  else if a = 0x80000073 then some 0x8f
  else if a = 0x80000074 then some 0x73
  else if a = 0x80000075 then some 0x90
  else if a = 0x80000076 then some 0x7
  else if a = 0x80000077 then some 0x30
  else if a = 0x80000078 then some 0x97
  else if a = 0x80000079 then some 0x17
  else if a = 0x8000007a then some 0x0
  else if a = 0x8000007b then some 0x0
  else if a = 0x8000007c then some 0x93
  else if a = 0x8000007d then some 0x87
  else if a = 0x8000007e then some 0xa7
  else if a = 0x8000007f then some 0xe0
  else if a = 0x80000080 then some 0x73
  else if a = 0x80000081 then some 0x90
  else if a = 0x80000082 then some 0x17
  else if a = 0x80000083 then some 0x34
  else if a = 0x80000084 then some 0x81
  else if a = 0x80000085 then some 0x47
  else if a = 0x80000086 then some 0x73
  else if a = 0x80000087 then some 0x90
  else if a = 0x80000088 then some 0x7
  else if a = 0x80000089 then some 0x18
  else if a = 0x8000008a then some 0xc1
  else if a = 0x8000008b then some 0x67
  else if a = 0x8000008c then some 0xfd
  else if a = 0x8000008d then some 0x17
  else if a = 0x8000008e then some 0x73
  else if a = 0x8000008f then some 0x90
  else if a = 0x80000090 then some 0x27
  else if a = 0x80000091 then some 0x30
  else if a = 0x80000092 then some 0x73
  else if a = 0x80000093 then some 0x90
  else if a = 0x80000094 then some 0x37
  else if a = 0x80000095 then some 0x30
  else if a = 0x80000096 then some 0xf3
  else if a = 0x80000097 then some 0x27
  else if a = 0x80000098 then some 0x40
  else if a = 0x80000099 then some 0x10
  else if a = 0x8000009a then some 0x93
  else if a = 0x8000009b then some 0xe7
  else if a = 0x8000009c then some 0x7
  else if a = 0x8000009d then some 0x22
  else if a = 0x8000009e then some 0x73
  else if a = 0x8000009f then some 0x90
  else if a = 0x800000a0 then some 0x47
  else if a = 0x800000a1 then some 0x10
  else if a = 0x800000a2 then some 0xfd
  else if a = 0x800000a3 then some 0x57
  else if a = 0x800000a4 then some 0xa9
  else if a = 0x800000a5 then some 0x83
  else if a = 0x800000a6 then some 0x73
  else if a = 0x800000a7 then some 0x90
  else if a = 0x800000a8 then some 0x7
  else if a = 0x800000a9 then some 0x3b
  else if a = 0x800000aa then some 0xbd
  else if a = 0x800000ab then some 0x47
  else if a = 0x800000ac then some 0x73
  else if a = 0x800000ad then some 0x90
  else if a = 0x800000ae then some 0x7
  else if a = 0x800000af then some 0x3a
  else if a = 0x800000b0 then some 0xef
  else if a = 0x800000b1 then some 0xf0
  else if a = 0x800000b2 then some 0xdf
  else if a = 0x800000b3 then some 0xf6
  else if a = 0x800000b4 then some 0xf3
  else if a = 0x800000b5 then some 0x27
  else if a = 0x800000b6 then some 0x40
  else if a = 0x800000b7 then some 0xf1
  else if a = 0x800000b8 then some 0x81
  else if a = 0x800000b9 then some 0x27
  else if a = 0x800000ba then some 0x3e
  else if a = 0x800000bb then some 0x82
  else if a = 0x800000bc then some 0x73
  else if a = 0x800000bd then some 0x0
  else if a = 0x800000be then some 0x20
  else if a = 0x800000bf then some 0x30
  else if a = 0x80000e82 then some 0x41
  else if a = 0x80000e83 then some 0x11
  else if a = 0x80000e84 then some 0x6
  else if a = 0x80000e85 then some 0xe4
  else if a = 0x80000e86 then some 0x22
  else if a = 0x80000e87 then some 0xe0
  else if a = 0x80000e88 then some 0x0
  else if a = 0x80000e89 then some 0x8
  else if a = 0x80000e8a then some 0xef
  else if a = 0x80000e8b then some 0x0
  else if a = 0x80000e8c then some 0x50
  else if a = 0x80000e8d then some 0x24
  else if a = 0x80000e8e then some 0x17
  else if a = 0x80000e8f then some 0x97
  else if a = 0x80000e90 then some 0x0
  else if a = 0x80000e91 then some 0x0
  else if a = 0x80000e92 then some 0x13
  else if a = 0x80000e93 then some 0x7
  else if a = 0x80000e94 then some 0x27
  else if a = 0x80000e95 then some 0x37
  else if a = 0x80000e96 then some 0x1d
  else if a = 0x80000e97 then some 0xc5
  else if a = 0x80000e98 then some 0x1c
  else if a = 0x80000e99 then some 0x43
  else if a = 0x80000e9a then some 0x81
  else if a = 0x80000e9b then some 0x27
  else if a = 0x80000e9c then some 0xf5
  else if a = 0x80000e9d then some 0xdf
  else if a = 0x80000e9e then some 0xf
  else if a = 0x80000e9f then some 0x0
  else if a = 0x80000ea0 then some 0x30
  else if a = 0x80000ea1 then some 0x3
  else if a = 0x80000ea2 then some 0xef
  else if a = 0x80000ea3 then some 0x0
  else if a = 0x80000ea4 then some 0xd0
  else if a = 0x80000ea5 then some 0x22
  else if a = 0x80000ea6 then some 0xaa
  else if a = 0x80000ea7 then some 0x85
  else if a = 0x80000ea8 then some 0x17
  else if a = 0x80000ea9 then some 0x65
  else if a = 0x80000eaa then some 0x0
  else if a = 0x80000eab then some 0x0
  else if a = 0x80000eac then some 0x13
  else if a = 0x80000ead then some 0x5
  else if a = 0x80000eae then some 0x5
  else if a = 0x80000eaf then some 0x1f
  else if a = 0x80000eb0 then some 0xef
  else if a = 0x80000eb1 then some 0xf0
  else if a = 0x80000eb2 then some 0xef
  else if a = 0x80000eb3 then some 0xe3
  else if a = 0x80000eb4 then some 0xef
  else if a = 0x80000eb5 then some 0x0
  else if a = 0x80000eb6 then some 0x0
  else if a = 0x80000eb7 then some 0x8
  else if a = 0x80000eb8 then some 0xef
  else if a = 0x80000eb9 then some 0x10
  else if a = 0x80000eba then some 0xa0
  else if a = 0x80000ebb then some 0x57
  else if a = 0x80000ebc then some 0xef
  else if a = 0x80000ebd then some 0x40
  else if a = 0x80000ebe then some 0xc0
  else if a = 0x80000ebf then some 0x59
  else if a = 0x80000ec0 then some 0xef
  else if a = 0x80000ec1 then some 0x0
  else if a = 0x80000ec2 then some 0x90
  else if a = 0x80000ec3 then some 0x6b
  else if a = 0x80000ec4 then some 0xef
  else if a = 0x80000ec5 then some 0xf0
  else if a = 0x80000ec6 then some 0xf
  else if a = 0x80000ec7 then some 0xd5
  else if a = 0x800018ce then some 0x41
  else if a = 0x800018cf then some 0x11
  else if a = 0x800018d0 then some 0x6
  else if a = 0x800018d1 then some 0xe4
  else if a = 0x800018d2 then some 0x22
  else if a = 0x800018d3 then some 0xe0
  else if a = 0x800018d4 then some 0x0
  else if a = 0x800018d5 then some 0x8
  else if a = 0x800018d6 then some 0x12
  else if a = 0x800018d7 then some 0x85
  else if a = 0x800018d8 then some 0x1
  else if a = 0x800018d9 then some 0x25
  else if a = 0x800018da then some 0xa2
  else if a = 0x800018db then some 0x60
  else if a = 0x800018dc then some 0x2
  else if a = 0x800018dd then some 0x64
  else if a = 0x800018de then some 0x41
  else if a = 0x800018df then some 0x1
  else if a = 0x800018e0 then some 0x82
  else if a = 0x800018e1 then some 0x80
  else if a = 0x800018e2 then some 0x41
  else if a = 0x800018e3 then some 0x11
  else if a = 0x80000414 then some 0x41
  else if a = 0x80000415 then some 0x11
  else if a = 0x80000416 then some 0x6
  else if a = 0x80000417 then some 0xe4
  else if a = 0x80000418 then some 0x22
  else if a = 0x80000419 then some 0xe0
  else if a = 0x8000041a then some 0x0
  else if a = 0x8000041b then some 0x8
  else if a = 0x8000041c then some 0x97
  else if a = 0x8000041d then some 0x75
  else if a = 0x8000041e then some 0x0
  else if a = 0x8000041f then some 0x0
  else if a = 0x80000420 then some 0x93
  else if a = 0x80000421 then some 0x85
  else if a = 0x80000422 then some 0x45
  else if a = 0x80000423 then some 0xbe
  else if a = 0x80000424 then some 0x17
  else if a = 0x80000425 then some 0x25
  else if a = 0x80000426 then some 0x1
  else if a = 0x80000427 then some 0x0
  else if a = 0x80000428 then some 0x13
  else if a = 0x80000429 then some 0x5
  else if a = 0x8000042a then some 0xc5
  else if a = 0x8000042b then some 0xdf
  else if a = 0x8000042c then some 0xef
  else if a = 0x8000042d then some 0x0
  else if a = 0x8000042e then some 0xe0
  else if a = 0x8000042f then some 0x74
  else if a = 0x80000430 then some 0xef
  else if a = 0x80000431 then some 0x0
  else if a = 0x80000432 then some 0x80
  else if a = 0x80000433 then some 0x44
  else if a = 0x80000434 then some 0x97
  else if a = 0x80000435 then some 0x27
  else if a = 0x80000436 then some 0x2
  else if a = 0x80000437 then some 0x0
  else if a = 0x80000438 then some 0x93
  else if a = 0x80000439 then some 0x87
  else if a = 0x8000043a then some 0xc7
  else if a = 0x8000043b then some 0xf5
  else if a = 0x8000043c then some 0x17
  else if a = 0x8000043d then some 0x7
  else if a = 0x8000043e then some 0x0
  else if a = 0x8000043f then some 0x0
  else if a = 0x80000440 then some 0x13
  else if a = 0x80000441 then some 0x7
  else if a = 0x80000442 then some 0xe7
  else if a = 0x80000443 then some 0xd2
  else if a = 0x80000444 then some 0x98
  else if a = 0x80000445 then some 0xeb
  else if a = 0x80000446 then some 0x17
  else if a = 0x80000447 then some 0x7
  else if a = 0x80000448 then some 0x0
  else if a = 0x80000449 then some 0x0
  else if a = 0x8000044a then some 0x13
  else if a = 0x8000044b then some 0x7
  else if a = 0x8000044c then some 0x27
  else if a = 0x8000044d then some 0xc8
  else if a = 0x8000044e then some 0x98
  else if a = 0x8000044f then some 0xef
  else if a = 0x80000450 then some 0xa2
  else if a = 0x80000451 then some 0x60
  else if a = 0x80000452 then some 0x2
  else if a = 0x80000453 then some 0x64
  else if a = 0x80000454 then some 0x41
  else if a = 0x80000455 then some 0x1
  else if a = 0x80000456 then some 0x82
  else if a = 0x80000457 then some 0x80
  else if a = 0x80000b7a then some 0x41
  else if a = 0x80000b7b then some 0x11
  else if a = 0x80000b7c then some 0x6
  else if a = 0x80000b7d then some 0xe4
  else if a = 0x80000b7e then some 0x22
  else if a = 0x80000b7f then some 0xe0
  else if a = 0x80000b80 then some 0x0
  else if a = 0x80000b81 then some 0x8
  else if a = 0x80000b82 then some 0xc
  else if a = 0x80000b83 then some 0xe5
  else if a = 0x80000b84 then some 0x23
  else if a = 0x80000b85 then some 0x20
  else if a = 0x80000b86 then some 0x5
  else if a = 0x80000b87 then some 0x0
  else if a = 0x80000b88 then some 0x23
  else if a = 0x80000b89 then some 0x38
  else if a = 0x80000b8a then some 0x5
  else if a = 0x80000b8b then some 0x0
  else if a = 0x80000b8c then some 0xa2
  else if a = 0x80000b8d then some 0x60
  else if a = 0x80000b8e then some 0x2
  else if a = 0x80000b8f then some 0x64
  else if a = 0x80000b90 then some 0x41
  else if a = 0x80000b91 then some 0x1
  else if a = 0x80000b92 then some 0x82
  else if a = 0x80000b93 then some 0x80
  else if a = 0x80000878 then some 0x41
  else if a = 0x80000879 then some 0x11
  else if a = 0x8000087a then some 0x6
  else if a = 0x8000087b then some 0xe4
  else if a = 0x8000087c then some 0x22
  else if a = 0x8000087d then some 0xe0
  else if a = 0x8000087e then some 0x0
  else if a = 0x8000087f then some 0x8
  else if a = 0x80000880 then some 0xb7
  else if a = 0x80000881 then some 0x7
  else if a = 0x80000882 then some 0x0
  else if a = 0x80000883 then some 0x10
  else if a = 0x80000884 then some 0xa3
  else if a = 0x80000885 then some 0x80
  else if a = 0x80000886 then some 0x7
  else if a = 0x80000887 then some 0x0
  else if a = 0x80000888 then some 0x37
  else if a = 0x80000889 then some 0x7
  else if a = 0x8000088a then some 0x0
  else if a = 0x8000088b then some 0x10
  else if a = 0x8000088c then some 0x93
  else if a = 0x8000088d then some 0x6
  else if a = 0x8000088e then some 0x0
  else if a = 0x8000088f then some 0xf8
  else if a = 0x80000890 then some 0xa3
  else if a = 0x80000891 then some 0x1
  else if a = 0x80000892 then some 0xd7
  else if a = 0x80000893 then some 0x0
  else if a = 0x80000894 then some 0x8d
  else if a = 0x80000895 then some 0x46
  else if a = 0x80000896 then some 0x37
  else if a = 0x80000897 then some 0x6
  else if a = 0x80000898 then some 0x0
  else if a = 0x80000899 then some 0x10
  else if a = 0x8000089a then some 0x23
  else if a = 0x8000089b then some 0x0
  else if a = 0x8000089c then some 0xd6
  else if a = 0x8000089d then some 0x0
  else if a = 0x8000089e then some 0xa3
  else if a = 0x8000089f then some 0x80
  else if a = 0x800008a0 then some 0x7
  else if a = 0x800008a1 then some 0x0
  else if a = 0x800008a2 then some 0xa3
  else if a = 0x800008a3 then some 0x1
  else if a = 0x800008a4 then some 0xd7
  else if a = 0x800008a5 then some 0x0
  else if a = 0x800008a6 then some 0x32
  else if a = 0x800008a7 then some 0x87
  else if a = 0x800008a8 then some 0x1d
  else if a = 0x800008a9 then some 0x46
  else if a = 0x800008aa then some 0x23
  else if a = 0x800008ab then some 0x1
  else if a = 0x800008ac then some 0xc7
  else if a = 0x800008ad then some 0x0
  else if a = 0x800008ae then some 0xa3
  else if a = 0x800008af then some 0x80
  else if a = 0x800008b0 then some 0xd7
  else if a = 0x800008b1 then some 0x0
  else if a = 0x800008b2 then some 0x97
  else if a = 0x800008b3 then some 0x65
  else if a = 0x800008b4 then some 0x0
  else if a = 0x800008b5 then some 0x0
  else if a = 0x800008b6 then some 0x93
  else if a = 0x800008b7 then some 0x85
  else if a = 0x800008b8 then some 0xe5
  else if a = 0x800008b9 then some 0x77
  else if a = 0x800008ba then some 0x17
  else if a = 0x800008bb then some 0x25
  else if a = 0x800008bc then some 0x1
  else if a = 0x800008bd then some 0x0
  else if a = 0x800008be then some 0x13
  else if a = 0x800008bf then some 0x5
  else if a = 0x800008c0 then some 0x65
  else if a = 0x800008c1 then some 0xa2
  else if a = 0x800008c2 then some 0xef
  else if a = 0x800008c3 then some 0x0
  else if a = 0x800008c4 then some 0x80
  else if a = 0x800008c5 then some 0x2b
  else if a = 0x800008c6 then some 0xa2
  else if a = 0x800008c7 then some 0x60
  else if a = 0x800008c8 then some 0x2
  else if a = 0x800008c9 then some 0x64
  else if a = 0x800008ca then some 0x41
  else if a = 0x800008cb then some 0x1
  else if a = 0x800008cc then some 0x82
  else if a = 0x800008cd then some 0x80
  else some 0#8

/-- Booting-Machine state at the `start` entry (hart 0); big PMA region. -/
noncomputable def σ0 : MState where
  regs r := match r with
    | .cur_privilege => some Privilege.Machine
    | .PC => some (0x80000058#64)
    | .misa => some 0x8000000003ffffff
    | .mstatus => some 0xA00000000
    | .pma_regions => some [bigRegion]
    | .x1 => some 0x8000001a
    | .x2 => some 0x80100000
    | r => some (decReg r 0)
  mem := mem0

def consRet : BitVec 64 := 0x80000EC8

/-- **Operational: boot all the way through `consoleinit`.** 145 real `try_step`s
reach `consoleinit`'s return point in `main` (0x80000EC8), still in Supervisor mode. -/
theorem console_to_main_ret :
    (runSteps 145 σ0).map (fun s => (s.regs Register.PC, s.regs Register.cur_privilege))
      = some (some consRet, some Privilege.Supervisor) := by
  with_unfolding_all rfl


theorem isSome145 : (runSteps 145 σ0).isSome := by
  obtain ⟨σm, h1, _⟩ := Option.map_eq_some_iff.mp console_to_main_ret; rw [h1]; rfl

/-- Machine state at `consoleinit`'s return (back in `main`). -/
noncomputable def σ_console : MState := (runSteps 145 σ0).get isSome145
theorem run145 : runSteps 145 σ0 = some σ_console := (Option.some_get isSome145).symm

theorem isSome56 : (runSteps 56 σ0).isSome := by
  have hadd : runSteps 145 σ0 = (runSteps 56 σ0).bind (fun s => runSteps 89 s) := runSteps_add 56 89 σ0
  rw [run145] at hadd
  rcases hs : runSteps 56 σ0 with _ | σm
  · rw [hs] at hadd; simp at hadd
  · rfl

/-- Machine state after `main`'s first instruction (the `wp_boot_to_main1` point). -/
noncomputable def σ_main1 : MState := (runSteps 56 σ0).get isSome56
theorem run56 : runSteps 56 σ0 = some σ_main1 := (Option.some_get isSome56).symm

/-- The `consoleinit` run, as 89 steps from the post-main-first state. -/
theorem run_main1_to_console : runSteps 89 σ_main1 = some σ_console := by
  have hadd : runSteps 145 σ0 = (runSteps 56 σ0).bind (fun s => runSteps 89 s) := runSteps_add 56 89 σ0
  rw [run56, run145] at hadd
  exact hadd.symm

theorem σ_console_props :
    σ_console.regs Register.PC = some consRet ∧
    σ_console.regs Register.cur_privilege = some Privilege.Supervisor := by
  obtain ⟨a, h1, h2⟩ := Option.map_eq_some_iff.mp console_to_main_ret
  have ha : a = σ_console := Option.some.inj (h1.symm.trans run145)
  subst ha
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

section
variable {GF : BundledGFunctors} {hlc : HasLC} [D : MainGS hlc GF]

/-- Boot through `main`'s first instruction (= `KernelStart.wp_boot_to_main1`). -/
theorem wp_boot_to_main1 {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF} :
    (machineState σ0 : IProp GF) ⊢
      (▷^[56] (machineState σ_main1 -∗ WP RiscvExpr.Loop @ s; E {{ Φ }})) -∗
        WP RiscvExpr.Loop @ s; E {{ Φ }} :=
  wp_run 56 σ0 σ_main1 run56

/-- **Through all of `consoleinit`, from the post-main-first state** (supervisor
mode: prologue, `cpuid`, `consoleinit` → `initlock`/`uartinit`(UART MMIO)/`initlock`,
`devsw`). -/
theorem wp_console_from_main1 {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF} :
    machineState σ_main1 -∗
      (▷^[89] (machineState σ_console -∗ WP RiscvExpr.Loop @ s; E {{ Φ }})) -∗
        WP RiscvExpr.Loop @ s; E {{ Φ }} := by
  iintro Hm; iapply (wp_run 89 σ_main1 σ_console run_main1_to_console) $$ Hm

/-- **The whole boot all the way through `consoleinit`, chained.** 145 real
`try_step`s — boot, `start()`/`mret`, into supervisor-mode `main`, through
`consoleinit`'s return — = `wp_boot_to_main1` (56) ▸ `wp_console_from_main1` (89). -/
theorem wp_through_consoleinit {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF} :
    (machineState σ0 : IProp GF) ⊢
      (▷^[145] (machineState σ_console -∗ WP RiscvExpr.Loop @ s; E {{ Φ }})) -∗
        WP RiscvExpr.Loop @ s; E {{ Φ }} :=
  wp_run 145 σ0 σ_console run145

end
end Xv6Iris.Model.KernelConsole
