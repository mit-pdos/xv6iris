(* IcacheBox.v -- R3.3 (endgame §4.2): the icache instance of the transit
   box LIVES IN IcacheEscrow.v now -- [ic_escrow] IS the box, [ic_deposit]
   the holder's handle row, [ic_sleeplocks] the genl tier over [ic_slp].
   This file re-exports it for the files that took the skeleton by name. *)
Require Export IcacheEscrow.
