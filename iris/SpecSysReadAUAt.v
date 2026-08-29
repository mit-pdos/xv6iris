(* SpecSysReadAUAt.v -- the read AU at the RAW-MAP commit, the sealable form.

   WHY THIS FILE EXISTS.  [SpecSysReadAU]'s contract predates
   [FsAbsMknodFire]'s give-back finding: its [aread_commit] is
   astate-shaped, and no prover can pay an astate-shaped give-back --
   [astate]'s existential loses the map's identity ON THE WAY OUT
   ([abs_view] is not injective), so [ftop_astate_ro]'s same-[I] wand has
   nothing to bite on.  The dup+read prover lane refuted the seal and
   recorded the minimal fix, which is this file: THE SAME frame and THE
   SAME arms, byte for byte, with only the commit swapped for
   [FsAbsReadFire.aread_commit_at] -- the raw-map single-phase form whose
   give-back names its map.  [aread_commit_at_weaken] (landed beside the
   fire) shows the [_at] form implies the frozen one, so a caller holding
   this contract can still discharge any consumer written against the
   astate-shaped commit; nothing diverges.

   R10: [SpecSysReadAU.v] is byte-identical -- its Module Type stands as
   the record of the pre-finding shape; THIS Module Type is the one the
   prover seals.  The relation is the mknod precedent
   ([SpecSysMknodAUEra] beside the frozen [SYSMKNOD_AU]) one size down:
   here not even the arms move.

   The stable corollary rides along at the same swap: its derivation
   ([FsAbsReadFire.arf_stable_of_arms]) is already proven against
   [read_stable_arms], so the sealer owes only the AU-to-stable
   packaging the frozen file's header describes. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RegFile RiscvExtras WpNext.
Require Import FdSlots ProcInv FileInvDefs.
Require Import SpecFileread.   (* [fread_names] *)
Require Import SpecSysRead.    (* [sys_rw_count] *)
Require Import FsAbs FsBytesGamma.  (* the abstract state; [fs_gamma_L] *)
Require Import Xv6G FsCfg.
Require Import SpecSysReadAU.
Require Import FsAbsReadFire.
Import Defs.

Local Open Scope Z_scope.

(* THE AU FORM AT THE RAW-MAP COMMIT: [wp_sys_read_au_body] with
   [aread_commit] swapped for [aread_commit_at].  Frame and arms are the
   frozen file's, applied verbatim. *)
Definition wp_sys_read_au_at_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (γf : gname)
    (γs : list gname) (j : nat) (γlp : gname)
    (fn : fread_names)
    (pidv : mword 32) (U : ustate)
    (v v2 : mword 64)
    (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
    (fd : nat) (fv : mword 64) (wb : bool) (i : Z)
    (Φr : aview -> nat -> anode -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  let n := sys_rw_count v2 in
  wp_sys_read_au_frame γf γs j γlp fn pidv U v v2 m K eb b lks
    fd fv wb i
    (aread_commit_at Γfs ∅ i Φr)
    (read_arms Γfs i n Φr).

(* THE STABLE COROLLARY at the same swap. *)
Definition wp_sys_read_au_at_stable_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (γf : gname)
    (γs : list gname) (j : nat) (γlp : gname)
    (fn : fread_names)
    (pidv : mword 32) (U : ustate)
    (v v2 : mword 64)
    (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
    (fd : nat) (fv : mword 64) (wb : bool) (i : Z)
    (q : Qp) (bs0 : list (bv 8)) (nl : nat)
    (Φr : aview -> nat -> anode -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  let n := sys_rw_count v2 in
  0 <= sys_rw_count v2 ->
  wp_sys_read_au_frame γf γs j γlp fn pidv U v v2 m K eb b lks
    fd fv wb i
    (nview Γfs q i (MkAnode (AFile bs0) nl)
     ∗ aread_commit_at Γfs ∅ i Φr)%I
    (read_stable_arms Γfs i n q bs0 nl Φr).

Module Type SYSREAD_AU_AT.
  Parameter wp_sys_read_au_at :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (fn : fread_names)
      (pidv : mword 32) (U : ustate)
      (v v2 : mword 64)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (fd : nat) (fv : mword 64) (wb : bool) (i : Z)
      (Φr : aview -> nat -> anode -> iProp Σ),
      wp_sys_read_au_at_body γf γs j γlp fn pidv U v v2 m K eb b lks
        fd fv wb i Φr.

  Parameter wp_sys_read_au_at_stable :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (fn : fread_names)
      (pidv : mword 32) (U : ustate)
      (v v2 : mword 64)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (fd : nat) (fv : mword 64) (wb : bool) (i : Z)
      (q : Qp) (bs0 : list (bv 8)) (nl : nat)
      (Φr : aview -> nat -> anode -> iProp Σ),
      wp_sys_read_au_at_stable_body γf γs j γlp fn pidv U v v2 m K eb b
        lks fd fv wb i q bs0 nl Φr.
End SYSREAD_AU_AT.
