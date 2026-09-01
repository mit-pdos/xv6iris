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
Require Import RiscvLang.
Require Import ColdBoot.   (* the ∃-witness: the closed cold-boot run *)
Require Import RiscvExtras.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The reset REGISTER file.                                              *)
(*                                                                          *)
(*    [boot_facts]' register clause is "the boot program RAN, from SOME       *)
(*    power-on file, and these ARE its output registers", so this             *)
(*    construction's job is                                                  *)
(*    to EXHIBIT one such run -- and [ColdBoot] has it: the chain from the    *)
(*    model's own [init_regstate], computed with the VM.  So the reset        *)
(*    register file no longer depends on the dying generation's registers at  *)
(*    all (it used to be pinned VALUES written over them, which was the       *)
(*    weaker shape this task retired); [init_regstate] is simply one          *)
(*    convenient power-on instance, and [BootReset.reset_regs_of_run] is what *)
(*    says the facts hold at EVERY instance.                                 *)
(* ---------------------------------------------------------------------- *)

Definition boot_hid (c : CPU) : SailStdpp.Values.mword 64 := boot_w64 (Z.of_nat (fin_to_nat c)).

Definition boot_regs (c : CPU) : regstate := cold_regs (boot_hid c).

(* THE WITNESS IS A REAL RUN: the model's boot chain, from [init_regstate] to
   the register file this construction hands over. *)
Lemma boot_regs_run (c : CPU) :
  run (ArchReset.boot_prog (boot_hid c) pma_boot)
      (MState init_regstate ∅ dev0_state) tt
      (MState (cold_regs (boot_hid c)) ∅ dev0_state).
Proof. exact (cold_boot_run_shape (boot_hid c)). Qed.

(* ... and it satisfies [reset_regs], which is the sanity anchor.  It is now
   [ColdBoot]'s theorem verbatim: with no patch layer left, the register file
   this construction hands over IS the closed run's output. *)
Lemma boot_regs_reset (c : CPU) : reset_regs c (boot_regs c).
Proof. exact (reset_regs_cold_boot c). Qed.

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

(* THE ERA WIPE (tso-machine-flip.md §2): a power-on opens a FRESH era, so the
   write log is empty and every hart's view sits at its bottom.  With no
   messages to apply, [flat] is the identity, so the flat cache [gmem] and the
   era-initial image [gimg] are the SAME map -- [boot_mem] -- which is what
   makes [mm_ok] hold at the boot state by [reflexivity] rather than by an
   argument about the log. *)
Definition boot_gstate (g : gstate) : gstate :=
  GState (fun c => boot_regs c) boot_mem
         (DevState uart0_state plic0_state (virtio_reset g.(gdev).(dvirtio)))
         g.(ggen) true (fun _ => None)
         boot_mem [] (fun _ => 0%nat).

Lemma boot_shape_boot_gstate (g : gstate) : boot_shape g (boot_gstate g).
Proof.
  unfold boot_shape, boot_facts, boot_gstate.
  cbn [ggen gpow gregs gmem gdev gresv gimg glog gtv duart dplic dvirtio].
  (* NO blanket [try reflexivity]: on the memory clauses it would try to
     unify a lookup in the 134M-entry [list_to_map] with [Some _] and
     compute the whole list.  One tactic per conjunct. *)
  split_and!.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact boot_mem_in_ram.
  - exact boot_mem_lookup.
  - (* the register clause: the closed cold-boot run is the witness *)
    intro c. exists init_regstate, (cold_regs (boot_hid c)).
    split; [ exact (boot_regs_run c) | reflexivity ].
  - reflexivity.
  - reflexivity.
  - exists g.(gdev).(dvirtio). reflexivity.
  - intro c. reflexivity.
  (* the three TSO clauses, all by construction: empty log, image = cache,
     every view at 0.  No [reflexivity] here touches [boot_mem]'s TERM --
     the [gimg = gmem] clause is syntactically the same map on both sides. *)
  - reflexivity.
  - reflexivity.
  - intro c. reflexivity.
Qed.
