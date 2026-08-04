(* ====================================================================== *)
(* PowerBoot.v -- THE CANONICAL RESET MACHINE, and the witness that a      *)
(* PowerOn has somewhere to go.                                            *)
(*                                                                         *)
(* [RiscvLang.boot_shape] says what the loader and the hardware leave       *)
(* behind at a power-on; [prim_step]'s PowerOn arm quantifies over ANY      *)
(* state of that shape, so the power thread's reducibility obligation needs *)
(* ONE state that has it.  That state is [boot_gstate], built here together *)
(* with the proof [boot_shape_boot_gstate] -- the only place in the tree    *)
(* that has to know how to construct a reset machine.                       *)
(*                                                                         *)
(* Kept out of RiscvLang.v (which holds the SPECIFICATION [boot_shape])     *)
(* because the construction needs the [uint]/[mword_of_int] bridges from    *)
(* RiscvExtras.v, which sits above the language.                            *)
(* ====================================================================== *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap finite bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang.
Require Import RiscvExtras.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The reset REGISTER file: the pinned values written over whatever the  *)
(*    dead generation left.  Everything [reset_regs] does not mention rides *)
(*    through unchanged -- it is exactly the set the boot proof quantifies   *)
(*    over.                                                                 *)
(* ---------------------------------------------------------------------- *)

Definition boot_regs (c : CPU) (rs : regstate) : regstate :=
  register_set PC (boot_w64 0x80000000)
   (register_set nextPC (boot_w64 0x80000000)
    (register_set cur_privilege Machine
    (register_set hart_state (HART_ACTIVE tt)
     (register_set mhartid (boot_w64 (Z.of_nat (fin_to_nat c)))
      (register_set mstatus (boot_w64 0xA00000000)
       (register_set misa (boot_w64 0x800000000014112D)
        (register_set mseccfg (boot_w64 0)
         (register_set menvcfg (boot_w64 0)
          (register_set htif_tohost_base None
           (register_set elp (landing_pad_bits_backwards NO_LP_EXPECTED)
            (register_set pma_regions pma_boot
             (register_set pmpcfg_n pmpcfg_boot rs)))))))))))).

(* peel [register_set]s off a lookup until the one that wrote the register:
   the mismatch side conditions are register disequalities, one [vm_compute]
   each, and the loop stops exactly at the writer (where the disequality is
   false and the side goal fails). *)
Local Ltac reg_peel :=
  repeat (rewrite irrelevant_register_set; [| vm_compute; reflexivity]);
  apply register_lookup_set.

Lemma boot_regs_reset (c : CPU) (rs : regstate) : reset_regs c (boot_regs c rs).
Proof.
  unfold reset_regs, boot_regs. split_and!; reg_peel.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The reset MEMORY: every RAM byte present, holding the loaded image    *)
(*    (zero off it).  A 134M-entry [list_to_map] TERM -- never computed;    *)
(*    the two facts below are proved from [elem_of_seqZ] alone.             *)
(* ---------------------------------------------------------------------- *)

Definition pa_of_z (a : Z) : Arch.pa := SailStdpp.Values.mword_of_int a.

(* The domain is CUT DOWN by a filter rather than by an argument about the
   list's keys: that is what makes "nothing outside RAM" one
   [map_lookup_filter_Some] instead of a walk back through [list_to_map]
   (whose reverse direction, [elem_of_list_to_map_2], produces a proof term
   this file's [Qed] does not come back from). *)
Definition boot_mem_raw : gmap Arch.pa (bv 8) :=
  list_to_map ((fun a : Z => (pa_of_z a, boot_byte a))
                 <$> seqZ ram_lo (ram_hi - ram_lo)).

Definition boot_mem : gmap Arch.pa (bv 8) :=
  base.filter (fun ab : Arch.pa * bv 8 => (ram_lo <= uint ab.1 < ram_hi)%Z)
              boot_mem_raw.

(* the address round-trip, on the RAM range: [ram_hi] is far below 2^64, so
   [mword_of_int] loses nothing *)
Lemma boot_uint_pa (a : Z) : ram_lo <= a < ram_hi -> uint (pa_of_z a) = a.
Proof.
  intro Ha. unfold pa_of_z, ram_lo, ram_hi in *.
  rewrite uint_unsigned, moi64_mod. apply Z.mod_small. lia.
Qed.

(* the OTHER direction of the round trip, and it needs no range premise at
   all: [Z_to_bv] is a left inverse of [bv_unsigned] at every width, so every
   [Arch.pa] IS the [pa_of_z] of its own unsigned value.  This is what pins a
   range filter's DOMAIN -- a key whose [uint] is [a] can only be
   [pa_of_z a] -- which is what turns "the bytes whose address lies in
   [lo, hi)" into an enumerable run (BootCarve's §6). *)
Lemma pa_of_z_uint (p : Arch.pa) : pa_of_z (uint p) = p.
Proof.
  unfold pa_of_z, SailStdpp.Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite uint_unsigned. apply Z_to_bv_bv_unsigned.
Qed.

Lemma pa_of_z_inj (a a' : Z) :
  ram_lo <= a < ram_hi -> ram_lo <= a' < ram_hi -> pa_of_z a = pa_of_z a' -> a = a'.
Proof.
  intros Ha Ha' Heq.
  rewrite <- (boot_uint_pa a Ha), <- (boot_uint_pa a' Ha'), Heq. reflexivity.
Qed.

Local Lemma seqZ_ram_range (a : Z) :
  a ∈ seqZ ram_lo (ram_hi - ram_lo) <-> ram_lo <= a < ram_hi.
Proof.
  rewrite elem_of_seqZ. unfold ram_lo, ram_hi. split; intro; lia.
Qed.

Local Lemma boot_mem_keys_nodup :
  NoDup ((fun ab : Arch.pa * bv 8 => ab.1)
           <$> ((fun a : Z => (pa_of_z a, boot_byte a))
                  <$> seqZ ram_lo (ram_hi - ram_lo))).
Proof.
  rewrite <- list_fmap_compose.
  apply NoDup_fmap_2_strong; [| apply NoDup_seqZ ].
  intros x y Hx Hy Heq. cbn in Heq.
  apply pa_of_z_inj;
    [ apply (proj1 (seqZ_ram_range x) Hx)
    | apply (proj1 (seqZ_ram_range y) Hy)
    | exact Heq ].
Qed.

Local Lemma boot_mem_raw_lookup (a : Z) :
  ram_lo <= a < ram_hi -> boot_mem_raw !! pa_of_z a = Some (boot_byte a).
Proof.
  intro Ha. unfold boot_mem_raw.
  apply elem_of_list_to_map; [ exact boot_mem_keys_nodup |].
  apply elem_of_list_fmap. exists a.
  split; [ reflexivity | apply (proj2 (seqZ_ram_range a) Ha) ].
Qed.

Lemma boot_mem_lookup (a : Z) :
  ram_lo <= a < ram_hi -> boot_mem !! pa_of_z a = Some (boot_byte a).
Proof.
  intro Ha. unfold boot_mem.
  apply map_lookup_filter_Some_2;
    [ apply (boot_mem_raw_lookup a Ha)
    | cbn; rewrite (boot_uint_pa a Ha); exact Ha ].
Qed.

Lemma boot_mem_in_ram (a : Arch.pa) (b : bv 8) :
  boot_mem !! a = Some b -> ram_lo <= uint a < ram_hi.
Proof.
  intro Hl. unfold boot_mem in Hl.
  apply map_lookup_filter_Some in Hl. exact (proj2 Hl).
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The reset MACHINE, and the PowerOn witness.                          *)
(* ---------------------------------------------------------------------- *)

Definition boot_gstate (g : gstate) : gstate :=
  GState (fun c => boot_regs c (g.(gregs) c)) boot_mem
         (DevState uart0_state plic0_state (virtio_reset g.(gdev).(dvirtio)))
         g.(ggen) true.

Lemma boot_shape_boot_gstate (g : gstate) : boot_shape g (boot_gstate g).
Proof.
  unfold boot_shape, boot_facts, boot_gstate.
  cbn [ggen gpow gregs gmem gdev duart dplic dvirtio].
  (* NO blanket [try reflexivity]: on the memory clauses it would try to
     unify a lookup in the 134M-entry [list_to_map] with [Some _] and
     compute the whole list.  One tactic per conjunct. *)
  split_and!.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact boot_mem_in_ram.
  - exact boot_mem_lookup.
  - intro c. apply boot_regs_reset.
  - reflexivity.
  - reflexivity.
  - exists g.(gdev).(dvirtio). reflexivity.
Qed.
