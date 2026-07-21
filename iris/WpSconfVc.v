(* WpSconfVc.v -- the SIE-AGNOSTIC VCgen block executor over
   [sconf]+[sie_cap], WITH sp-move support.

   The executor state [vsstate] extends VcGenS.v's [vstate] with the
   CONCRETE stack-depth accounting [vsu]/[vsx] (current / high-water
   pushed depth below the entry sp -- concrete so a block run
   [vm_compute]s even under a symbolic [sie_cap] count) and a FRAME
   LEDGER [vsf]: the addresses (svals) of stack slots freed by an sp
   push that no store has initialized yet.  Their contents are junk,
   so they cannot live in the vheap (whose cells denote through ρ); at
   the WP level the ledger denotes as [vframe_own] -- one
   existentially-valued [word_pointsto] per address.

   sp moves (c.addi16sp, and c.addi with rd = sp; byte offsets must be
   multiples of 8):
     - PUSH (sp -= 8k): the k freed slot addresses [sp', sp) enter the
       ledger; vsu += k (and vsx tracks the max).
     - POP (sp += 8k): requires k <= vsu (a block never pops above its
       entry sp); each slot address in [sp, sp+8k) is reclaimed from
       the ledger (still junk) or DELETED from the 8-byte vheap (an
       initialized frame slot); vsu -= k.
   8-byte STOREs whose address misses the vheap but hits the ledger
   initialize that slot: the address moves from ledger to a fresh vheap
   cell holding the stored value.  LOADs never read the ledger (junk).
   Everything else delegates to [vc_step_s] (rd = sp writes outside the
   two sp-movers are rejected).

   The WP lemma [wp_vc_block_s_sconf] takes a symbolic entry count [n],
   threads [sie_cap γ root_ppn m (n - vsu st)] and [vframe_own ρ
   (vsf st)] through the block, and needs the ONE pure premise
   [vsx st' <= n] (every intermediate push fits since [vsx] is
   monotone); sp moves go through the push/pop leaves (WpSconfAlu.v),
   everything else through the same [sconf] leaves as before.          *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import WpGpr InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import RegFile.
Require Import VcGen VcGenS.
Require Import StackOwn.
Require Import KptTree.
Require Import IntrDefs.
Require Import WpSconfAlu WpSconfMem.
Local Open Scope Z_scope.
Import Defs.

Local Lemma neq_of_eq_vec_false (a b : mword 5) :
  eq_vec a b = false -> a <> b.
Proof.
  intros Hf He. subst.
  rewrite (proj2 (eq_vec_true_iff b b) eq_refl) in Hf. discriminate.
Qed.

(* ====================================================================== *)
(* 1. The sp-aware executor state and pure helpers.                        *)
(* ====================================================================== *)

(* The stack accounting is kept CONCRETE so a block run [vm_compute]s
   even though the surrounding [sie_cap] count is symbolic: [vsu] is the
   CURRENT pushed depth (slots below the entry sp; 0 at block entry) and
   [vsx] its high-water mark.  The WP lemma takes a symbolic entry count
   [n], threads [sie_cap _ _ _ (n - vsu st)], and needs only the single
   pure premise [vsx st' <= n] -- every intermediate push fits because
   [vsx] is monotone ([vc_block_sp_ux]).  Pops must not go above the
   entry sp (guard [k <= vsu]). *)
Record vsstate := VSS {
  vsb : vstate;        (* pc / regs / heaps, shared with VcGenS *)
  vsu : nat;           (* current pushed depth below the entry sp *)
  vsx : nat;           (* high-water mark of [vsu] *)
  vsf : list sval;     (* ledger: pushed-but-uninitialized slot addresses *)
}.

(* remove the (syntactically) matching address from the ledger *)
Fixpoint frame_remove (fr : list sval) (a : sval) : option (list sval) :=
  match fr with
  | nil => None
  | a' :: t => if sval_beq a' a then Some t
               else match frame_remove t a with
                    | Some t' => Some (a' :: t')
                    | None => None
                    end
  end.

(* POP absorption: reclaim slot [v + 8j] for each j, from the ledger or
   (deleting the cell) from the 8-byte heap. *)
Fixpoint pop_absorb (h : list (sval * sval)) (fr : list sval) (v : sval)
    (js : list nat) : option (list (sval * sval) * list sval) :=
  match js with
  | nil => Some (h, fr)
  | j :: rest =>
      let a := sval_addZ v (8 * Z.of_nat j) in
      match frame_remove fr a with
      | Some fr' => pop_absorb h fr' v rest
      | None =>
          match vheap_find h a with
          | Some (i, _) => pop_absorb (delete i h) fr v rest
          | None => None
          end
      end
  end.

(* zimm12 residues are unsigned 64-bit values: those at or above 2^63
   denote NEGATIVE (downward) sp moves. *)
Definition vsp_half : Z := 9223372036854775808.
Definition vsp_wrap : Z := 18446744073709551616.

Definition lift_base (st : vsstate) (r : option vstate) : option vsstate :=
  match r with
  | Some b' => Some (VSS b' (vsu st) (vsx st) (vsf st))
  | None => None
  end.

Definition vc_step_sp_move (st : vsstate) (pc' : Z) (d : Z) : option vsstate :=
  match (vsb st).(vregs) !! Regidx csp_rs1 with
  | Some v =>
      if negb (sval_is64 v) then None else
      if negb (andb (Z.leb 0 d) (Z.ltb d vsp_wrap)) then None else
      if Z.eqb d 0 then None else
      let v' := sval_addZ v d in
      let vr' := <[Regidx csp_rs1 := v']> (vsb st).(vregs) in
      if Z.ltb d vsp_half then
        (* upward move (sp += d): POP d/8 slots (not above the entry sp) *)
        if negb (Z.eqb (Z.modulo d 8) 0) then None else
        let k := Z.to_nat (Z.div d 8) in
        if negb (Nat.leb k (vsu st)) then None else
        match pop_absorb (vsb st).(vheap) (vsf st) v (seq 0 k) with
        | Some (h', fr') =>
            Some (VSS (VSt pc' vr' h' (vsb st).(vheap4))
                      (vsu st - k)%nat (vsx st) fr')
        | None => None
        end
      else
        (* downward move (sp -= 2^64 - d): PUSH (2^64 - d)/8 slots *)
        if negb (Z.eqb (Z.modulo (vsp_wrap - d) 8) 0) then None else
        let k := Z.to_nat (Z.div (vsp_wrap - d) 8) in
        Some (VSS (VSt pc' vr' (vsb st).(vheap) (vsb st).(vheap4))
                  (vsu st + k)%nat (Nat.max (vsx st) (vsu st + k))
                  (((fun j => sval_addZ v' (8 * Z.of_nat j)) <$> seq 0 k)
                   ++ vsf st))
  | None => None
  end.

(* 8-byte store: overwrite an existing cell, or initialize a ledger slot
   (the address moves from the ledger to a fresh cell). *)
Definition vc_store8_sp (st : vsstate) (pc' : Z) (a : sval) (v2 : sval)
    : option vsstate :=
  match vheap_find (vsb st).(vheap) a with
  | Some (i, _) =>
      Some (VSS (VSt pc' (vsb st).(vregs)
                     (<[i := (a, v2)]> (vsb st).(vheap)) (vsb st).(vheap4))
                (vsu st) (vsx st) (vsf st))
  | None =>
      match frame_remove (vsf st) a with
      | Some fr' =>
          Some (VSS (VSt pc' (vsb st).(vregs)
                         ((vsb st).(vheap) ++ [(a, v2)]) (vsb st).(vheap4))
                    (vsu st) (vsx st) fr')
      | None => None
      end
  end.

Definition vc_step_sp_s (st : vsstate) (op : vop_s) : option vsstate :=
  let pc' := (vsb st).(vpc) + vop_s_w op in
  match op with
  | VScaddi imm rd =>
      if eq_vec rd csp_rs1
      then vc_step_sp_move st pc' (zimm12 (sign_extend' 12 imm))
      else lift_base st (vc_step_s (vsb st) op)
  | VScaddi16sp imm6 =>
      vc_step_sp_move st pc' (zimm12 (caddi16sp_imm imm6))
  | VScaddi4spn _ _ rd | VScldsp _ rd | VSclw _ _ rd | VScaddiw _ rd =>
      if eq_vec rd csp_rs1 then None else lift_base st (vc_step_s (vsb st) op)
  | VSld _ _ _ rd =>
      if eq_vec rd csp_rs1 then None else lift_base st (vc_step_s (vsb st) op)
  | VScsdsp uimm rs2 =>
      match (vsb st).(vregs) !! Regidx csp_rs1, (vsb st).(vregs) !! Regidx rs2 with
      | Some v1, Some v2 =>
          if negb (sval_is64 v1) then None
          else vc_store8_sp st pc' (sval_addZ v1 (zoff6 uimm)) v2
      | _, _ => None
      end
  | VSsd _ imm rs2 rs1 =>
      match (vsb st).(vregs) !! Regidx rs1, (vsb st).(vregs) !! Regidx rs2 with
      | Some v1, Some v2 =>
          if negb (sval_is64 v1) then None
          else vc_store8_sp st pc' (sval_addZ v1 (zimm12 imm)) v2
      | _, _ => None
      end
  | VScsw _ _ _ =>
      lift_base st (vc_step_s (vsb st) op)
  end.

Fixpoint vc_block_sp_s (st : vsstate) (prog : list vop_s) : option vsstate :=
  match prog with
  | nil => Some st
  | op :: rest =>
      match vc_step_sp_s st op with
      | Some st1 => vc_block_sp_s st1 rest
      | None => None
      end
  end.

(* ---- the depth accounting is well-formed and monotone ---- *)
Lemma vc_step_sp_move_ux (st : vsstate) (pc' d : Z) (st1 : vsstate) :
  vc_step_sp_move st pc' d = Some st1 ->
  (vsu st <= vsx st)%nat ->
  (vsu st1 <= vsx st1)%nat /\ (vsx st <= vsx st1)%nat.
Proof.
  unfold vc_step_sp_move.
  destruct (vregs (vsb st) !! Regidx csp_rs1) as [v|]; [|discriminate].
  destruct (sval_is64 v); [|discriminate].
  destruct (andb (Z.leb 0 d) (Z.ltb d vsp_wrap)); [|discriminate].
  destruct (Z.eqb d 0); [discriminate|].
  cbn [negb].
  destruct (Z.ltb d vsp_half).
  - destruct (Z.eqb (d mod 8) 0); [|discriminate]. cbn [negb].
    destruct (Nat.leb (Z.to_nat (d / 8)) (vsu st)); [|discriminate]. cbn [negb].
    destruct (pop_absorb _ _ _ _) as [[h' fr']|]; [|discriminate].
    intros H Hux. injection H as <-. cbn [vsu vsx]. lia.
  - destruct (Z.eqb ((vsp_wrap - d) mod 8) 0); [|discriminate]. cbn [negb].
    intros H Hux. injection H as <-. cbn [vsu vsx]. lia.
Qed.

Lemma lift_base_ux (st : vsstate) (r : option vstate) (st1 : vsstate) :
  lift_base st r = Some st1 -> vsu st1 = vsu st /\ vsx st1 = vsx st.
Proof.
  destruct r as [b'|]; intro H; [injection H as <-; auto | discriminate].
Qed.

Lemma sp_move_inv (st : vsstate) (pc' d : Z) (st1 : vsstate) :
  vc_step_sp_move st pc' d = Some st1 ->
  exists v, (vsb st).(vregs) !! Regidx csp_rs1 = Some v /\ sval_is64 v = true /\
    (0 <= d) /\ (d < vsp_wrap) /\ d <> 0 /\
    (( d < vsp_half /\ d mod 8 = 0 /\ (Z.to_nat (d / 8) <= vsu st)%nat /\
       exists h' fr',
         pop_absorb (vsb st).(vheap) (vsf st) v (seq 0 (Z.to_nat (d / 8)))
           = Some (h', fr') /\
         st1 = VSS (VSt pc' (<[Regidx csp_rs1 := sval_addZ v d]> (vsb st).(vregs))
                            h' (vsb st).(vheap4))
                   (vsu st - Z.to_nat (d / 8))%nat (vsx st) fr' )
     \/
     ( vsp_half <= d /\ (vsp_wrap - d) mod 8 = 0 /\
         st1 = VSS (VSt pc' (<[Regidx csp_rs1 := sval_addZ v d]> (vsb st).(vregs))
                            (vsb st).(vheap) (vsb st).(vheap4))
                   (vsu st + Z.to_nat ((vsp_wrap - d) / 8))%nat
                   (Nat.max (vsx st) (vsu st + Z.to_nat ((vsp_wrap - d) / 8)))
                   (((fun j => sval_addZ (sval_addZ v d) (8 * Z.of_nat j))
                       <$> seq 0 (Z.to_nat ((vsp_wrap - d) / 8))) ++ vsf st) )).
Proof.
  unfold vc_step_sp_move.
  destruct ((vsb st).(vregs) !! Regidx csp_rs1) as [v|] eqn:Hrs1; [|discriminate].
  destruct (sval_is64 v) eqn:H64; cbn [negb]; [|discriminate].
  destruct (andb (Z.leb 0 d) (Z.ltb d vsp_wrap)) eqn:Hrange; cbn [negb]; [|discriminate].
  apply andb_prop in Hrange; destruct Hrange as [Hd0 HdW].
  apply Z.leb_le in Hd0. apply Z.ltb_lt in HdW.
  destruct (Z.eqb d 0) eqn:Hdz; [discriminate|]. apply Z.eqb_neq in Hdz.
  destruct (Z.ltb d vsp_half) eqn:Hdir.
  - apply Z.ltb_lt in Hdir.
    destruct (Z.eqb (d mod 8) 0) eqn:Hmod; cbn [negb]; [|discriminate].
    apply Z.eqb_eq in Hmod.
    destruct (Nat.leb (Z.to_nat (d / 8)) (vsu st)) eqn:Hk; cbn [negb]; [|discriminate].
    apply Nat.leb_le in Hk.
    destruct (pop_absorb (vsb st).(vheap) (vsf st) v (seq 0 (Z.to_nat (d / 8))))
      as [[h' fr']|] eqn:Habs; [|discriminate].
    intro HS; injection HS as <-. exists v.
    split;[reflexivity|]. split;[exact H64|]. split;[exact Hd0|].
    split;[exact HdW|]. split;[exact Hdz|].
    left. split;[exact Hdir|]. split;[exact Hmod|]. split;[exact Hk|].
    exists h', fr'. split;[exact Habs|reflexivity].
  - apply Z.ltb_ge in Hdir.
    destruct (Z.eqb ((vsp_wrap - d) mod 8) 0) eqn:Hmod; cbn [negb]; [|discriminate].
    apply Z.eqb_eq in Hmod.
    intro HS; injection HS as <-. exists v.
    split;[reflexivity|]. split;[exact H64|]. split;[exact Hd0|].
    split;[exact HdW|]. split;[exact Hdz|].
    right. split;[exact Hdir|]. split;[exact Hmod|reflexivity].
Qed.

Lemma vc_store8_sp_ux (st : vsstate) (pc' : Z) (a v2 : sval) (st1 : vsstate) :
  vc_store8_sp st pc' a v2 = Some st1 -> vsu st1 = vsu st /\ vsx st1 = vsx st.
Proof.
  unfold vc_store8_sp.
  destruct (vheap_find _ _) as [[i ?]|].
  - intro H; injection H as <-; auto.
  - destruct (frame_remove _ _); intro H; [injection H as <-; auto | discriminate].
Qed.

Lemma vc_step_sp_ux (st : vsstate) (op : vop_s) (st1 : vsstate) :
  vc_step_sp_s st op = Some st1 ->
  (vsu st <= vsx st)%nat ->
  (vsu st1 <= vsx st1)%nat /\ (vsx st <= vsx st1)%nat.
Proof.
  intros H Hux.
  assert (Hlift : lift_base st (vc_step_s (vsb st) op) = Some st1 ->
            (vsu st1 <= vsx st1)%nat /\ (vsx st <= vsx st1)%nat).
  { intros Hr. destruct (lift_base_ux _ _ _ Hr) as [-> ->].
    split; [exact Hux | lia]. }
  destruct op as [imm rd|rdc nzimm rd|uimm rs2|uimm rd
                 |imm rs1 rd|imm rs2 rs1|imm rd
                 |rvc imm rs2 rs1|rvc imm rs1 rd|imm6];
    cbn [vc_step_sp_s] in H, Hlift.
  - destruct (eq_vec rd csp_rs1).
    + exact (vc_step_sp_move_ux _ _ _ _ H Hux).
    + exact (Hlift H).
  - destruct (eq_vec rd csp_rs1); [discriminate|]. exact (Hlift H).
  - destruct (vregs (vsb st) !! Regidx csp_rs1) as [v1|]; [|discriminate].
    destruct (vregs (vsb st) !! Regidx rs2) as [v2|]; [|discriminate].
    destruct (negb (sval_is64 v1)); [discriminate|].
    destruct (vc_store8_sp_ux _ _ _ _ _ H) as [-> ->]. split; [exact Hux | lia].
  - destruct (eq_vec rd csp_rs1); [discriminate|]. exact (Hlift H).
  - destruct (eq_vec rd csp_rs1); [discriminate|]. exact (Hlift H).
  - exact (Hlift H).
  - destruct (eq_vec rd csp_rs1); [discriminate|]. exact (Hlift H).
  - destruct (vregs (vsb st) !! Regidx rs1) as [v1|]; [|discriminate].
    destruct (vregs (vsb st) !! Regidx rs2) as [v2|]; [|discriminate].
    destruct (negb (sval_is64 v1)); [discriminate|].
    destruct (vc_store8_sp_ux _ _ _ _ _ H) as [-> ->]. split; [exact Hux | lia].
  - destruct (eq_vec rd csp_rs1); [discriminate|]. exact (Hlift H).
  - exact (vc_step_sp_move_ux _ _ _ _ H Hux).
Qed.

Lemma vc_block_sp_ux (prog : list vop_s) (st st' : vsstate) :
  vc_block_sp_s st prog = Some st' ->
  (vsu st <= vsx st)%nat ->
  (vsu st' <= vsx st')%nat /\ (vsx st <= vsx st')%nat.
Proof.
  revert st. induction prog as [|op rest IHp]; intros st H Hux; simpl in H.
  - injection H as <-. split; [exact Hux | lia].
  - destruct (vc_step_sp_s st op) as [st1|] eqn:Hs; [|discriminate].
    destruct (vc_step_sp_ux _ _ _ Hs Hux) as [H1 H2].
    destruct (IHp _ H H1) as [H3 H4]. split; [exact H3 | lia].
Qed.

(* ====================================================================== *)
(* 2. Pure arithmetic bridges: executor guards -> the push/pop leaves'     *)
(* address premises.                                                       *)
(* ====================================================================== *)

Lemma sval_addZ_is64 (v : sval) (d : Z) :
  sval_is64 v = true -> sval_is64 (sval_addZ v d) = true.
Proof. destruct v; simpl; auto. Qed.

Lemma sval_den_addZ_avi (ρ : nat -> mword 64) (v : sval) (d : Z) :
  sval_is64 v = true ->
  sval_den ρ (sval_addZ v d) = add_vec_int (sval_den ρ v) d.
Proof. intro H. rewrite (sval_den_addZ ρ v d H). reflexivity. Qed.

Lemma mword_of_int_mod64 (z1 z2 : Z) :
  (z1 - z2) mod vsp_wrap = 0 ->
  (mword_of_int z1 : mword 64) = mword_of_int z2.
Proof.
  intro H.
  rewrite -(stk_mword_of_int_wrap z1) -(stk_mword_of_int_wrap z2).
  f_equal.
  unfold bv_wrap.
  assert (Hm : bv_modulus 64 = vsp_wrap) by (vm_compute; reflexivity).
  rewrite Hm.
  unfold vsp_wrap in *.
  assert (He : z1 - z2 = 18446744073709551616 * ((z1 - z2) / 18446744073709551616))
    by (apply Z_div_exact_full_2; [lia | exact H]).
  replace z1
    with (z2 + (z1 - z2) / 18446744073709551616 * 18446744073709551616) by lia.
  apply Z_mod_plus_full.
Qed.

Lemma push_addr_eq (sp0 imm64 : mword 64) (k : nat) :
  8 * Z.of_nat k = vsp_wrap - uint imm64 ->
  add_vec sp0 imm64 = pa_stk sp0 k.
Proof.
  intro He. unfold pa_stk, add_vec_int.
  rewrite -(stk_mword_of_int_uint imm64).
  apply f_equal.
  apply mword_of_int_mod64.
  unfold vsp_wrap in *.
  replace (uint imm64 - - (8 * Z.of_nat k)) with 18446744073709551616 by lia.
  apply Z_mod_same_full.
Qed.

Lemma pop_addr_eq (sp0 imm64 : mword 64) (k : nat) :
  8 * Z.of_nat k = uint imm64 ->
  sp0 = pa_stk (add_vec sp0 imm64) k.
Proof.
  intro He. unfold pa_stk.
  rewrite -(stk_mword_of_int_uint imm64).
  change (add_vec sp0 (mword_of_int (uint imm64)))
    with (add_vec_int sp0 (uint imm64)).
  rewrite avi_assoc.
  replace (uint imm64 + - (8 * Z.of_nat k)) with 0 by lia.
  symmetry. apply avi0.
Qed.

Lemma div8_exact (d : Z) :
  0 <= d -> d mod 8 = 0 -> 8 * Z.of_nat (Z.to_nat (d / 8)) = d.
Proof.
  intros Hd Hm.
  rewrite Z2Nat.id; [| apply Z.div_pos; lia].
  pose proof (Z_div_mod_eq_full d 8). lia.
Qed.

(* smoke test: the accounting is fully concrete, so a
   push -> store-into-fresh-frame -> load-back -> pop block runs by
   [vm_compute] even though nothing is known about the registers.
   (c.addi16sp sp,-16 ; c.sdsp ra,8(sp) ; c.ldsp ra,8(sp) ;
    c.addi16sp sp,16 -- net zero: heap, ledger and depth all return
    to the entry state; the high-water mark records the 2-slot frame.) *)

Section WpSconfVc.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  (* ==================================================================== *)
  (* 3. The frame ledger's denotation + the resource algebra of the new    *)
  (* executor steps.                                                       *)
  (* ==================================================================== *)
  Definition vframe_own (ρ : nat -> mword 64) (fr : list sval) : iProp Σ :=
    ([∗ list] a ∈ fr, ∃ w : bv 64,
        word_pointsto (sval_den ρ a) (DfracOwn 1) w)%I.

  Lemma vframe_own_nil (ρ : nat -> mword 64) : ⊢ vframe_own ρ [].
  Proof. rewrite /vframe_own big_sepL_nil. done. Qed.

  Lemma vframe_own_app (ρ : nat -> mword 64) (f1 f2 : list sval) :
    vframe_own ρ (f1 ++ f2) ⊣⊢ vframe_own ρ f1 ∗ vframe_own ρ f2.
  Proof. by rewrite /vframe_own big_sepL_app. Qed.

  Lemma vframe_own_remove (ρ : nat -> mword 64) (fr : list sval) (a : sval)
      (fr' : list sval) :
    frame_remove fr a = Some fr' ->
    vframe_own ρ fr ⊣⊢
    (∃ w : bv 64, word_pointsto (sval_den ρ a) (DfracOwn 1) w) ∗ vframe_own ρ fr'.
  Proof.
    revert fr'. induction fr as [|a0 t IHt]; intros fr' H; simpl in H;
      [discriminate|].
    destruct (sval_beq a0 a) eqn:Hbeq.
    - injection H as <-. apply sval_beq_eq in Hbeq. subst a0.
      by rewrite /vframe_own big_sepL_cons.
    - destruct (frame_remove t a) as [t'|] eqn:Hrec; [|discriminate].
      injection H as <-.
      rewrite /vframe_own !big_sepL_cons.
      rewrite /vframe_own in IHt. rewrite (IHt t' eq_refl).
      iSplit.
      + iIntros "(H0 & Ha & Ht)". iFrame.
      + iIntros "(Ha & H0 & Ht)". iFrame.
  Qed.

  Lemma vheap_own_delete (ρ : nat -> mword 64) (h : list (sval * sval))
      (i : nat) (a v : sval) :
    h !! i = Some (a, v) ->
    vheap_own ρ h ⊣⊢
    ((sval_den ρ a) ↦₈ (sval_den ρ v) ∗ vheap_own ρ (delete i h))%I.
  Proof.
    intro Hi.
    rewrite /vheap_own.
    rewrite -{1}(take_drop_middle h i (a, v) Hi).
    rewrite delete_take_drop.
    rewrite !big_sepL_app big_sepL_cons /=.
    iSplit.
    - iIntros "(Ht & Hc & Hd)". iFrame.
    - iIntros "(Hc & Ht & Hd)". iFrame.
  Qed.

  Lemma vheap_own_snoc (ρ : nat -> mword 64) (h : list (sval * sval))
      (a v : sval) :
    vheap_own ρ (h ++ [(a, v)]) ⊣⊢
    vheap_own ρ h ∗ ((sval_den ρ a) ↦₈ (sval_den ρ v))%I.
  Proof. by rewrite /vheap_own big_sepL_app big_sepL_singleton. Qed.

  (* absorbing a pop's slots: the reclaimed region as base-anchored
     existential words, ready for [stack_own] reassembly. *)
  Lemma pop_absorb_sound (ρ : nat -> mword 64) (v : sval) (js : list nat)
      (h h' : list (sval * sval)) (fr fr' : list sval) :
    sval_is64 v = true ->
    pop_absorb h fr v js = Some (h', fr') ->
    vheap_own ρ h -∗ vframe_own ρ fr -∗
    vheap_own ρ h' ∗ vframe_own ρ fr' ∗
    ([∗ list] j ∈ js, ∃ w : bv 64,
       word_pointsto (add_vec_int (sval_den ρ v) (8 * Z.of_nat j)) (DfracOwn 1) w).
  Proof.
    intros Hv64. revert h fr.
    induction js as [|j rest IHjs]; intros h fr Habs; simpl in Habs.
    - injection Habs as <- <-.
      iIntros "Hh Hf". iFrame "Hh Hf". done.
    - destruct (frame_remove fr (sval_addZ v (8 * Z.of_nat j))) as [fr1|] eqn:Hfrm.
      + iIntros "Hh Hf".
        iEval (rewrite (vframe_own_remove ρ fr _ fr1 Hfrm)) in "Hf".
        iDestruct "Hf" as "[Hslot Hf]".
        iDestruct (IHjs _ _ Habs with "Hh Hf") as "(Hh & Hf & Hrest)".
        iFrame "Hh Hf".
        rewrite big_sepL_cons.
        iSplitL "Hslot"; [| iExact "Hrest"].
        iEval (rewrite (sval_den_addZ_avi ρ v _ Hv64)) in "Hslot".
        iExact "Hslot".
      + destruct (vheap_find h (sval_addZ v (8 * Z.of_nat j))) as [[i vold]|] eqn:Hfind;
          [|discriminate].
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hi.
        iIntros "Hh Hf".
        iEval (rewrite (vheap_own_delete ρ h i _ _ Hi)) in "Hh".
        iDestruct "Hh" as "[Hslot Hh]".
        iDestruct (IHjs _ _ Habs with "Hh Hf") as "(Hh & Hf & Hrest)".
        iFrame "Hh Hf".
        rewrite big_sepL_cons.
        iSplitL "Hslot"; [| iExact "Hrest"].
        iEval (rewrite (sval_den_addZ_avi ρ v _ Hv64)) in "Hslot".
        iExists (sval_den ρ vold). iExact "Hslot".
  Qed.

  (* a pushed frame region, as ledger entries *)
  Lemma vframe_own_of_stack (ρ : nat -> mword 64) (v' : sval) (sp0 : mword 64)
      (k : nat) :
    sval_is64 v' = true ->
    sval_den ρ v' = pa_stk sp0 k ->
    stack_own sp0 k ⊣⊢
    vframe_own ρ ((fun j => sval_addZ v' (8 * Z.of_nat j)) <$> seq 0 k).
  Proof.
    intros Hv64 Hbase.
    rewrite stack_own_base /vframe_own big_sepL_fmap.
    apply big_sepL_proper. intros i j _.
    rewrite (sval_den_addZ_avi ρ v' _ Hv64) Hbase. done.
  Qed.

  (* a pop's absorbed slots, reassembled below the NEW sp *)
  Lemma stack_of_absorbed (ρ : nat -> mword 64) (v : sval) (spN : mword 64)
      (k : nat) :
    sval_den ρ v = pa_stk spN k ->
    ([∗ list] j ∈ seq 0 k, ∃ w : bv 64,
       word_pointsto (add_vec_int (sval_den ρ v) (8 * Z.of_nat j)) (DfracOwn 1) w)
    ⊢ stack_own spN k.
  Proof. intro Hb. rewrite stack_own_base Hb. done. Qed.

  (* ==================================================================== *)
  (* 4. THE block lemma: one symbolic run = one WP, sp moves included.     *)
  (* ==================================================================== *)
  Lemma wp_vc_block_s_sconf_aux (γ : gname) (root_ppn : mword 44)
      (prog : list vop_s) (Φ : mval -> iProp Σ)
      (st st' : vsstate) (ρ : nat -> mword 64)
      (m m0 : regfile) (n : nat) :
    vc_block_sp_s st prog = Some st' ->
    (vsu st <= vsx st)%nat ->
    (vsx st' <= n)%nat ->
    gpr_matches ρ (vsb st).(vregs) m ->
    agree_off (vsb st).(vregs) m m0 ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m (n - vsu st) -∗
    tlb_inv_pt root_ppn -∗
    pc_is (mword_of_int (vsb st).(vpc)) -∗
    gpr_file m -∗
    block_instrs_s (vsb st).(vpc) prog -∗
    vheap_own ρ (vsb st).(vheap) -∗
    vheap4_own ρ (vsb st).(vheap4) -∗
    vframe_own ρ (vsf st) -∗
    ( ∀ mf : regfile,
      ⌜ gpr_matches ρ (vsb st').(vregs) mf ∧ agree_off (vsb st').(vregs) mf m0 ⌝ -∗
      sconf γ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap γ root_ppn mf (n - vsu st') -∗
      tlb_inv_pt root_ppn -∗
      pc_is (mword_of_int (vsb st').(vpc)) -∗
      gpr_file mf -∗
      vheap_own ρ (vsb st').(vheap) -∗
      vheap4_own ρ (vsb st').(vheap4) -∗
      vframe_own ρ (vsf st') -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    revert st m. induction prog as [|op rest IH]; intros st m Hblk Hux Hxn Hmatch Hao.
    - (* empty block *)
      simpl in Hblk. injection Hblk as <-.
      iIntros "Hsc Hhs Hcap Htlbinv Hpc Hgpr _ Hheap Hheap4 Hfr Hcont".
      iApply ("Hcont" $! m with "[//] Hsc Hhs Hcap Htlbinv Hpc Hgpr Hheap Hheap4 Hfr").
    - cbn [vc_block_sp_s] in Hblk.
      destruct (vc_step_sp_s st op) as [st1|] eqn:Hstep; [|discriminate].
      pose proof (vc_step_sp_ux _ _ _ Hstep Hux) as [Hux1 _].
      pose proof (proj2 (vc_block_sp_ux _ _ _ Hblk Hux1)) as Hxmono.
      destruct st as [b u x fr].
      cbn [vsu vsx vsb vsf] in Hux |- *.
      iIntros "Hsc Hhs Hcap Htlbinv Hpc Hgpr [Hi Hbi] Hheap Hheap4 Hfr Hcont".
      destruct op as [imm rd|rdc nzimm rd|uimm rs2|uimm rd
                     |imm rs1 rd|imm rs2 rs1|imm rd
                     |rvc imm rs2 rs1|rvc imm rs1 rd|imm6];
        cbn [vc_step_sp_s vsb vsu vsx vsf vop_s_w] in Hstep.
      + (* VScaddi : sp-move if rd = sp, else delegate *)
        destruct (eq_vec rd csp_rs1) eqn:Hrdsp0.
        * (* ---- c.addi sp, imm : an sp move ---- *)
          pose proof (proj1 (eq_vec_true_iff _ _) Hrdsp0) as Hrdeq. subst rd.
          unfold vc_step_sp_move in Hstep; cbn [vsb vsu vsx vsf] in Hstep.
          destruct (vregs b !! Regidx csp_rs1) as [v|] eqn:Hrs1; [|discriminate].
          destruct (sval_is64 v) eqn:H64; cbn [negb] in Hstep; [|discriminate].
          set (d := zimm12 (sign_extend' 12 imm)) in *.
          destruct (andb (Z.leb 0 d) (Z.ltb d vsp_wrap)) eqn:Hrange;
            cbn [negb] in Hstep; [|discriminate].
          apply andb_prop in Hrange; destruct Hrange as [Hd0 HdW].
          apply Z.leb_le in Hd0. apply Z.ltb_lt in HdW.
          destruct (Z.eqb d 0) eqn:Hdz; [discriminate|].
          pose proof (Hmatch _ _ Hrs1) as Hm1.
          assert (Hval : regval_into_reg
                      (add_vec (m !!! Regidx csp_rs1)
                               (sign_extend' 64 (sign_extend' 12 imm)))
                  = sval_den ρ (sval_addZ v d)).
          { unfold regval_into_reg.
            rewrite (sval_den_addZ ρ v d H64) Hm1.
            unfold d, zimm12. rewrite stk_mword_of_int_uint. reflexivity. }
          destruct (Z.ltb d vsp_half) eqn:Hdir.
          { (* POP: sp += d *)
            destruct (Z.eqb (d mod 8) 0) eqn:Hmod; cbn [negb] in Hstep;
              [|discriminate].
            apply Z.eqb_eq in Hmod.
            set (k := Z.to_nat (d / 8)) in *.
            destruct (Nat.leb k u) eqn:Hku0; cbn [negb] in Hstep; [|discriminate].
            apply Nat.leb_le in Hku0.
            destruct (pop_absorb (vheap b) fr v (seq 0 k)) as [[h' fr']|] eqn:Habs;
              [|discriminate].
            injection Hstep as <-.
            cbn [vsu vsx] in Hux1, Hxmono.
            assert (Hek : 8 * Z.of_nat k = d)
              by (unfold k; apply div8_exact; [lia | exact Hmod]).
            assert (Hw : m !!! Regidx csp_rs1
                         = pa_stk (add_vec (m !!! Regidx csp_rs1)
                                     (sign_extend' 64 (sign_extend' 12 imm))) k).
            { apply pop_addr_eq. rewrite Hek. unfold d, zimm12. reflexivity. }
            iDestruct (pop_absorb_sound ρ v (seq 0 k) (vheap b) h' fr fr' H64 Habs
                         with "Hheap Hfr") as "(Hheap & Hfr & Hslots)".
            assert (Hb' : sval_den ρ v
                          = pa_stk (add_vec (m !!! Regidx csp_rs1)
                                      (sign_extend' 64 (sign_extend' 12 imm))) k)
              by (rewrite -Hm1; exact Hw).
            iDestruct (stack_of_absorbed ρ v _ k Hb' with "Hslots") as "Hframe".
            iApply (wp_caddi_sp_pop_s_sconf γ root_ppn Φ (mword_of_int (vpc b)) imm
                      m (n - u) k Hw
                      with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hframe").
            iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr".
            iEval (rewrite avi_mword) in "Hpc".
            assert (Hnk : ((n - u) + k)%nat = (n - (u - k))%nat) by lia.
            iEval (rewrite Hnk) in "Hcap".
            iApply (IH _ _ Hblk Hux1 Hxn
                      (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                      (agree_off_step Hao)
                      with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont"). }
          { (* PUSH: sp -= 2^64 - d *)
            apply Z.ltb_ge in Hdir.
            destruct (Z.eqb ((vsp_wrap - d) mod 8) 0) eqn:Hmod; cbn [negb] in Hstep;
              [|discriminate].
            apply Z.eqb_eq in Hmod.
            set (k := Z.to_nat ((vsp_wrap - d) / 8)) in *.
            injection Hstep as <-.
            cbn [vsu vsx] in Hux1, Hxmono.
            assert (Hkle0 : (k <= n - u)%nat) by lia.
            assert (Hek : 8 * Z.of_nat k = vsp_wrap - d)
              by (unfold k; apply div8_exact; [unfold vsp_wrap in *; lia | exact Hmod]).
            assert (Hw : add_vec (m !!! Regidx csp_rs1)
                                 (sign_extend' 64 (sign_extend' 12 imm))
                         = pa_stk (m !!! Regidx csp_rs1) k).
            { apply push_addr_eq. rewrite Hek. unfold d, zimm12. reflexivity. }
            iApply (wp_caddi_sp_push_s_sconf γ root_ppn Φ (mword_of_int (vpc b)) imm
                      m (n - u) k Hkle0 Hw
                      with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi").
            iIntros "Hhs Hsc Hcap Hframe Htlbinv Hpc Hgpr".
            iEval (rewrite avi_mword) in "Hpc".
            assert (Hnk : ((n - u) - k)%nat = (n - (u + k))%nat) by lia.
            iEval (rewrite Hnk) in "Hcap".
            assert (Hv'64 : sval_is64 (sval_addZ v d) = true)
              by (apply sval_addZ_is64; exact H64).
            assert (Hbase : sval_den ρ (sval_addZ v d)
                            = pa_stk (m !!! Regidx csp_rs1) k)
              by (rewrite -Hval; exact Hw).
            iEval (rewrite (vframe_own_of_stack ρ (sval_addZ v d) _ k Hv'64 Hbase))
              in "Hframe".
            iAssert (vframe_own ρ
                       (((fun j => sval_addZ (sval_addZ v d) (8 * Z.of_nat j))
                           <$> seq 0 k) ++ fr))
              with "[Hframe Hfr]" as "Hfr".
            { rewrite vframe_own_app. iFrame "Hframe Hfr". }
            iApply (IH _ _ Hblk Hux1 Hxn
                      (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                      (agree_off_step Hao)
                      with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont"). }
        * (* ---- ordinary c.addi rd, imm ---- *)
          pose proof (neq_of_eq_vec_false _ _ Hrdsp0) as Hrdsp.
          unfold lift_base in Hstep; simpl in Hstep.
          destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
          apply Z.eqb_neq in Hrd0.
          destruct (vregs b !! Regidx rd) as [v1|] eqn:Hrs1; [|discriminate].
          destruct (sval_is64 v1) eqn:H64; [|discriminate].
          injection Hstep as <-.
          pose proof (Hmatch _ _ Hrs1) as Hm1.
          iApply (wp_caddi_s_sconf γ root_ppn Φ (mword_of_int (vpc b)) rd imm m (n - u)
                    Hrd0 Hrdsp
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi").
          iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr".
          iEval (rewrite avi_mword) in "Hpc".
          assert (Hval : regval_into_reg
                      (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))
                  = sval_den ρ (sval_addZ v1 (zimm12 (sign_extend' 12 imm)))).
          { unfold regval_into_reg.
            rewrite Hm1 (sval_den_add_imm ρ v1 (sign_extend' 12 imm) H64).
            reflexivity. }
          iApply (IH _ _ Hblk Hux1 Hxn (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                    (agree_off_step Hao)
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont").
      + (* VScaddi4spn *)
        destruct (eq_vec rd csp_rs1) eqn:Hrdsp0; [discriminate|].
        pose proof (neq_of_eq_vec_false _ _ Hrdsp0) as Hrdsp.
        unfold lift_base in Hstep; simpl in Hstep.
        destruct (regidx_eqb (creg2reg_idx rdc) (Regidx rd)) eqn:Hrdc0;
          [|discriminate].
        pose proof (regidx_eqb_eq _ _ Hrdc0) as Hrdc. cbn [negb] in Hstep.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs b !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; [|discriminate].
        injection Hstep as <-.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (vpc b))
                  rdc nzimm rd m (n - u) Hrdc Hrd0 Hrdsp
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi").
        iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Hval : regval_into_reg
                    (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))
                = sval_den ρ (sval_addZ v1 (zimm12 (caddi4spn_imm nzimm)))).
        { unfold regval_into_reg.
          rewrite Hm1 (sval_den_add_imm ρ v1 (caddi4spn_imm nzimm) H64).
          reflexivity. }
        iApply (IH _ _ Hblk Hux1 Hxn (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                  (agree_off_step Hao)
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont").
      + (* VScsdsp : store, cell overwrite or ledger-slot initialization *)
        destruct (vregs b !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vregs b !! Regidx rs2) as [v2|] eqn:Hrs2; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        unfold vc_store8_sp in Hstep; cbn [vsb vsu vsx vsf] in Hstep.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        pose proof (Hmatch _ _ Hrs2) as Hm2.
        assert (Hea : sval_den ρ (sval_addZ v1 (zoff6 uimm))
                      = add_vec (m !!! Regidx csp_rs1)
                                (zero_extend' 64 (concat_vec uimm ('b"000")))).
        { unfold zoff6. rewrite (sval_den_add_off ρ v1 _ H64) Hm1. reflexivity. }
        destruct (vheap_find (vheap b) (sval_addZ v1 (zoff6 uimm)))
          as [[i vold]|] eqn:Hfind.
        * (* existing cell *)
          injection Hstep as <-.
          pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
          rewrite /vheap_own.
          iDestruct (big_sepL_insert_acc _ _ _ _ Hcell with "Hheap")
            as "[Hcell Hheapk]".
          iEval (cbn [fst snd]) in "Hcell".
          iEval (rewrite Hea) in "Hcell".
          iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (vpc b)) uimm rs2
                    m (n - u) (sval_den ρ vold)
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hcell").
          iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hcell".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite Hm2 -Hea) in "Hcell".
          iDestruct ("Hheapk" $! (sval_addZ v1 (zoff6 uimm), v2) with "[Hcell]")
            as "Hheap"; [iExact "Hcell"|].
          iApply (IH _ _ Hblk Hux1 Hxn Hmatch Hao
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont").
        * (* fresh ledger slot *)
          destruct (frame_remove fr (sval_addZ v1 (zoff6 uimm))) as [fr1|] eqn:Hfrm;
            [|discriminate].
          injection Hstep as <-.
          iEval (rewrite (vframe_own_remove ρ fr _ fr1 Hfrm)) in "Hfr".
          iDestruct "Hfr" as "[Hslot Hfr]".
          iDestruct "Hslot" as (wold) "Hslot".
          iEval (rewrite Hea) in "Hslot".
          iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (vpc b)) uimm rs2
                    m (n - u) wold
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hslot").
          iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hslot".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite Hm2 -Hea) in "Hslot".
          iAssert (vheap_own ρ (vheap b ++ [(sval_addZ v1 (zoff6 uimm), v2)]))
            with "[Hheap Hslot]" as "Hheap".
          { rewrite vheap_own_snoc. iFrame "Hheap Hslot". }
          iApply (IH _ _ Hblk Hux1 Hxn Hmatch Hao
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont").
      + (* VScldsp *)
        destruct (eq_vec rd csp_rs1) eqn:Hrdsp0; [discriminate|].
        pose proof (neq_of_eq_vec_false _ _ Hrdsp0) as Hrdsp.
        unfold lift_base in Hstep; simpl in Hstep.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs b !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap b) (sval_addZ v1 (zoff6 uimm)))
          as [[i vv]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        assert (Hea : sval_den ρ (sval_addZ v1 (zoff6 uimm))
                      = add_vec (m !!! Regidx csp_rs1)
                                (zero_extend' 64 (concat_vec uimm ('b"000")))).
        { unfold zoff6. rewrite (sval_den_add_off ρ v1 _ H64) Hm1. reflexivity. }
        rewrite /vheap_own.
        iDestruct (big_sepL_lookup_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (vpc b)) uimm rd
                  m (n - u) (sval_den ρ vv) (dqm:=DfracOwn 1) Hrd0 Hrdsp
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite -Hea) in "Hcell".
        iDestruct ("Hheapk" with "[Hcell]") as "Hheap"; [iExact "Hcell"|].
        assert (Hval : regval_into_reg (sval_den ρ vv) = sval_den ρ vv)
          by reflexivity.
        iApply (IH _ _ Hblk Hux1 Hxn (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                  (agree_off_step Hao)
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont").
      + (* VSclw *)
        destruct (eq_vec rd csp_rs1) eqn:Hrdsp0; [discriminate|].
        pose proof (neq_of_eq_vec_false _ _ Hrdsp0) as Hrdsp.
        unfold lift_base in Hstep; simpl in Hstep.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs b !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap4 b) (sval_addZ v1 (zimm12 imm)))
          as [[i w32]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
        { rewrite (sval_den_add_imm ρ v1 imm H64) Hm1. reflexivity. }
        rewrite /vheap4_own.
        iDestruct (big_sepL_lookup_acc _ _ _ _ Hcell with "Hheap4")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_clw_s_sconf γ root_ppn Φ (mword_of_int (vpc b)) rd rs1 imm
                  m (n - u) (sval32_den ρ w32) (dqm:=DfracOwn 1) Hrd0 Hrdsp
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite -Hea) in "Hcell".
        iDestruct ("Hheapk" with "[Hcell]") as "Hheap4"; [iExact "Hcell"|].
        assert (Hval : regval_into_reg (sign_extend' 64 (sval32_den ρ w32))
                       = sval_den ρ (S32 w32)) by reflexivity.
        iApply (IH _ _ Hblk Hux1 Hxn (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                  (agree_off_step Hao)
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont").
      + (* VScsw *)
        unfold lift_base in Hstep; simpl in Hstep.
        destruct (vregs b !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vregs b !! Regidx rs2) as [v2|] eqn:Hrs2; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap4 b) (sval_addZ v1 (zimm12 imm)))
          as [[i wold]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        pose proof (Hmatch _ _ Hrs2) as Hm2.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
        { rewrite (sval_den_add_imm ρ v1 imm H64) Hm1. reflexivity. }
        rewrite /vheap4_own.
        iDestruct (big_sepL_insert_acc _ _ _ _ Hcell with "Hheap4")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_csw_s_sconf γ root_ppn Φ (mword_of_int (vpc b)) rs2 rs1 imm
                  m (n - u) (sval32_den ρ wold)
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Hsv : trunc32 (m !!! Regidx rs2) = sval32_den ρ (sval_trunc32 v2)).
        { rewrite sval_trunc32_den Hm2. reflexivity. }
        iEval (rewrite Hsv -Hea) in "Hcell".
        iDestruct ("Hheapk" $! (sval_addZ v1 (zimm12 imm), sval_trunc32 v2)
                     with "[Hcell]") as "Hheap4"; [iExact "Hcell"|].
        iApply (IH _ _ Hblk Hux1 Hxn Hmatch Hao
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont").
      + (* VScaddiw *)
        destruct (eq_vec rd csp_rs1) eqn:Hrdsp0; [discriminate|].
        pose proof (neq_of_eq_vec_false _ _ Hrdsp0) as Hrdsp.
        unfold lift_base in Hstep; simpl in Hstep.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs b !! Regidx rd) as [v1|] eqn:Hrs1; [|discriminate].
        injection Hstep as <-.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        iApply (wp_caddiw_s_sconf γ root_ppn Φ (mword_of_int (vpc b)) rd imm m (n - u)
                  Hrd0 Hrdsp
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi").
        iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Hval : regval_into_reg
                    (sign_extend' 64 (subrange_vec_dec
                       (add_vec (m !!! Regidx rd)
                                (sign_extend' 64 (sign_extend' 12 imm))) 31 0))
                = sval_den ρ (S32 (sval32_addZ (sval_trunc32 v1) (zimm32 imm)))).
        { unfold regval_into_reg. rewrite Hm1.
          cbn [sval_den].
          rewrite sval32_den_addZ.
          rewrite sval_trunc32_den.
          unfold zimm32. rewrite mword_of_int_uint32.
          rewrite -trunc32_add.
          rewrite trunc32_subrange. reflexivity. }
        iApply (IH _ _ Hblk Hux1 Hxn (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                  (agree_off_step Hao)
                  with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont").
      + (* VSsd : store, cell overwrite or ledger-slot initialization *)
        destruct (vregs b !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vregs b !! Regidx rs2) as [v2|] eqn:Hrs2; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        unfold vc_store8_sp in Hstep; cbn [vsb vsu vsx vsf] in Hstep.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        pose proof (Hmatch _ _ Hrs2) as Hm2.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
        { rewrite (sval_den_add_imm ρ v1 imm H64) Hm1. reflexivity. }
        destruct (vheap_find (vheap b) (sval_addZ v1 (zimm12 imm)))
          as [[i vold]|] eqn:Hfind.
        * (* existing cell *)
          injection Hstep as <-.
          pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
          rewrite /vheap_own.
          iDestruct (big_sepL_insert_acc _ _ _ _ Hcell with "Hheap")
            as "[Hcell Hheapk]".
          iEval (cbn [fst snd]) in "Hcell".
          iEval (rewrite Hea) in "Hcell".
          destruct rvc.
          -- iApply (wp_csd_s_sconf γ root_ppn Φ (mword_of_int (vpc b)) rs2 rs1 imm
                       m (n - u) (sval_den ρ vold)
                       with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hcell").
             iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hcell".
             iEval (rewrite avi_mword) in "Hpc".
             iEval (rewrite Hm2 -Hea) in "Hcell".
             iDestruct ("Hheapk" $! (sval_addZ v1 (zimm12 imm), v2) with "[Hcell]")
               as "Hheap"; [iExact "Hcell"|].
             iApply (IH _ _ Hblk Hux1 Hxn Hmatch Hao
                       with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont").
          -- iApply (wp_sd_s_sconf γ root_ppn Φ (mword_of_int (vpc b)) rs2 rs1 imm
                       m (n - u) (sval_den ρ vold)
                       with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hcell").
             iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hcell".
             iEval (rewrite avi_mword) in "Hpc".
             iEval (rewrite Hm2 -Hea) in "Hcell".
             iDestruct ("Hheapk" $! (sval_addZ v1 (zimm12 imm), v2) with "[Hcell]")
               as "Hheap"; [iExact "Hcell"|].
             iApply (IH _ _ Hblk Hux1 Hxn Hmatch Hao
                       with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont").
        * (* fresh ledger slot *)
          destruct (frame_remove fr (sval_addZ v1 (zimm12 imm))) as [fr1|] eqn:Hfrm;
            [|discriminate].
          injection Hstep as <-.
          iEval (rewrite (vframe_own_remove ρ fr _ fr1 Hfrm)) in "Hfr".
          iDestruct "Hfr" as "[Hslot Hfr]".
          iDestruct "Hslot" as (wold) "Hslot".
          iEval (rewrite Hea) in "Hslot".
          destruct rvc.
          -- iApply (wp_csd_s_sconf γ root_ppn Φ (mword_of_int (vpc b)) rs2 rs1 imm
                       m (n - u) wold
                       with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hslot").
             iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hslot".
             iEval (rewrite avi_mword) in "Hpc".
             iEval (rewrite Hm2 -Hea) in "Hslot".
             iAssert (vheap_own ρ (vheap b ++ [(sval_addZ v1 (zimm12 imm), v2)]))
               with "[Hheap Hslot]" as "Hheap".
             { rewrite vheap_own_snoc. iFrame "Hheap Hslot". }
             iApply (IH _ _ Hblk Hux1 Hxn Hmatch Hao
                       with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont").
          -- iApply (wp_sd_s_sconf γ root_ppn Φ (mword_of_int (vpc b)) rs2 rs1 imm
                       m (n - u) wold
                       with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hslot").
             iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hslot".
             iEval (rewrite avi_mword) in "Hpc".
             iEval (rewrite Hm2 -Hea) in "Hslot".
             iAssert (vheap_own ρ (vheap b ++ [(sval_addZ v1 (zimm12 imm), v2)]))
               with "[Hheap Hslot]" as "Hheap".
             { rewrite vheap_own_snoc. iFrame "Hheap Hslot". }
             iApply (IH _ _ Hblk Hux1 Hxn Hmatch Hao
                       with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont").
      + (* VSld *)
        destruct (eq_vec rd csp_rs1) eqn:Hrdsp0; [discriminate|].
        pose proof (neq_of_eq_vec_false _ _ Hrdsp0) as Hrdsp.
        unfold lift_base in Hstep; simpl in Hstep.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs b !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap b) (sval_addZ v1 (zimm12 imm)))
          as [[i vv]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
        { rewrite (sval_den_add_imm ρ v1 imm H64) Hm1. reflexivity. }
        rewrite /vheap_own.
        iDestruct (big_sepL_lookup_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        assert (Hval : regval_into_reg (sval_den ρ vv) = sval_den ρ vv) by reflexivity.
        destruct rvc.
        * iApply (wp_cld_s_sconf γ root_ppn Φ (mword_of_int (vpc b)) rd rs1 imm
                    m (n - u) (sval_den ρ vv) (dqm:=DfracOwn 1) Hrd0 Hrdsp
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hcell").
          iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hcell".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite -Hea) in "Hcell".
          iDestruct ("Hheapk" with "[Hcell]") as "Hheap"; [iExact "Hcell"|].
          iApply (IH _ _ Hblk Hux1 Hxn (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                    (agree_off_step Hao)
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont").
        * iApply (wp_ld_s_sconf γ root_ppn Φ (mword_of_int (vpc b)) rd rs1 imm
                    m (n - u) (sval_den ρ vv) (dqm:=DfracOwn 1) Hrd0 Hrdsp
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hcell").
          iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr Hcell".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite -Hea) in "Hcell".
          iDestruct ("Hheapk" with "[Hcell]") as "Hheap"; [iExact "Hcell"|].
          iApply (IH _ _ Hblk Hux1 Hxn (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                    (agree_off_step Hao)
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont").
      + (* VScaddi16sp : an sp move -- invert over abstract d (sp_move_inv) *)
        set (d := zimm12 (caddi16sp_imm imm6)) in *.
        apply sp_move_inv in Hstep.
        cbn [vsb vsu vsx vsf] in Hstep.
        destruct Hstep as (v & Hrs1 & H64 & Hd0 & HdW & Hdz & Hcase).
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        assert (Hval : regval_into_reg
                    (add_vec (m !!! Regidx csp_rs1)
                             (sign_extend' 64 (caddi16sp_imm imm6)))
                = sval_den ρ (sval_addZ v d)).
        { unfold regval_into_reg.
          rewrite (sval_den_addZ ρ v d H64) Hm1.
          unfold d, zimm12. rewrite stk_mword_of_int_uint. reflexivity. }
        destruct Hcase as [ (Hdir & Hmod & Hku0 & h' & fr' & Habs & ->)
                          | (Hdir & Hmod & ->) ].
        * (* POP: sp += d *)
          set (k := Z.to_nat (d / 8)) in *.
          cbn [vsu vsx] in Hux1, Hxmono.
          assert (Hek : 8 * Z.of_nat k = d)
            by (unfold k; apply div8_exact; [lia | exact Hmod]).
          assert (Hw : m !!! Regidx csp_rs1
                       = pa_stk (add_vec (m !!! Regidx csp_rs1)
                                   (sign_extend' 64 (caddi16sp_imm imm6))) k).
          { apply pop_addr_eq. rewrite Hek. unfold d, zimm12. reflexivity. }
          iDestruct (pop_absorb_sound ρ v (seq 0 k) (vheap b) h' fr fr' H64 Habs
                       with "Hheap Hfr") as "(Hheap & Hfr & Hslots)".
          assert (Hb' : sval_den ρ v
                        = pa_stk (add_vec (m !!! Regidx csp_rs1)
                                    (sign_extend' 64 (caddi16sp_imm imm6))) k)
            by (rewrite -Hm1; exact Hw).
          iDestruct (stack_of_absorbed ρ v _ k Hb' with "Hslots") as "Hframe".
          iApply (wp_caddi16sp_pop_s_sconf γ root_ppn Φ (mword_of_int (vpc b)) imm6
                    m (n - u) k Hw
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi Hframe").
          iIntros "Hhs Hsc Hcap Htlbinv Hpc Hgpr".
          iEval (rewrite avi_mword) in "Hpc".
          assert (Hnk : ((n - u) + k)%nat = (n - (u - k))%nat) by lia.
          iEval (rewrite Hnk) in "Hcap".
          iApply (IH _ _ Hblk Hux1 Hxn
                    (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                    (agree_off_step Hao)
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont").
        * (* PUSH: sp -= 2^64 - d *)
          set (k := Z.to_nat ((vsp_wrap - d) / 8)) in *.
          cbn [vsu vsx] in Hux1, Hxmono.
          assert (Hkle0 : (k <= n - u)%nat) by lia.
          assert (Hek : 8 * Z.of_nat k = vsp_wrap - d)
            by (unfold k; apply div8_exact; [unfold vsp_wrap in *; lia | exact Hmod]).
          assert (Hw : add_vec (m !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm imm6))
                       = pa_stk (m !!! Regidx csp_rs1) k).
          { apply push_addr_eq. rewrite Hek. unfold d, zimm12. reflexivity. }
          iApply (wp_caddi16sp_push_s_sconf γ root_ppn Φ (mword_of_int (vpc b)) imm6
                    m (n - u) k Hkle0 Hw
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hi").
          iIntros "Hhs Hsc Hcap Hframe Htlbinv Hpc Hgpr".
          iEval (rewrite avi_mword) in "Hpc".
          assert (Hnk : ((n - u) - k)%nat = (n - (u + k))%nat) by lia.
          iEval (rewrite Hnk) in "Hcap".
          assert (Hv'64 : sval_is64 (sval_addZ v d) = true)
            by (apply sval_addZ_is64; exact H64).
          assert (Hbase : sval_den ρ (sval_addZ v d)
                          = pa_stk (m !!! Regidx csp_rs1) k)
            by (rewrite -Hval; exact Hw).
          iEval (rewrite (vframe_own_of_stack ρ (sval_addZ v d) _ k Hv'64 Hbase))
            in "Hframe".
          iAssert (vframe_own ρ
                     (((fun j => sval_addZ (sval_addZ v d) (8 * Z.of_nat j))
                         <$> seq 0 k) ++ fr))
            with "[Hframe Hfr]" as "Hfr".
          { rewrite vframe_own_app. iFrame "Hframe Hfr". }
          iApply (IH _ _ Hblk Hux1 Hxn
                    (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                    (agree_off_step Hao)
                    with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont").
  Qed.

  (* the [m0 := m] instantiation: entry agreement is reflexive.  The usual
     client shape: [st := VSS b 0 0 []] (block entry: no pushed depth, an
     empty ledger -- supply [vframe_own_nil]), premise [vsx st' <= n] a
     concrete literal vs the spec's stack bound, and [Nat.sub_0_r] to read
     [n - 0] back as [n]. *)
  Lemma wp_vc_block_s_sconf (γ : gname) (root_ppn : mword 44)
      (prog : list vop_s) (Φ : mval -> iProp Σ)
      (st st' : vsstate) (ρ : nat -> mword 64)
      (m : regfile) (n : nat) :
    vc_block_sp_s st prog = Some st' ->
    (vsu st <= vsx st)%nat ->
    (vsx st' <= n)%nat ->
    gpr_matches ρ (vsb st).(vregs) m ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m (n - vsu st) -∗
    tlb_inv_pt root_ppn -∗
    pc_is (mword_of_int (vsb st).(vpc)) -∗
    gpr_file m -∗
    block_instrs_s (vsb st).(vpc) prog -∗
    vheap_own ρ (vsb st).(vheap) -∗
    vheap4_own ρ (vsb st).(vheap4) -∗
    vframe_own ρ (vsf st) -∗
    ( ∀ mf : regfile,
      ⌜ gpr_matches ρ (vsb st').(vregs) mf ∧ agree_off (vsb st').(vregs) mf m ⌝ -∗
      sconf γ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap γ root_ppn mf (n - vsu st') -∗
      tlb_inv_pt root_ppn -∗
      pc_is (mword_of_int (vsb st').(vpc)) -∗
      gpr_file mf -∗
      vheap_own ρ (vsb st').(vheap) -∗
      vheap4_own ρ (vsb st').(vheap4) -∗
      vframe_own ρ (vsf st') -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hblk Hux Hxn Hmatch.
    iIntros "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont".
    iApply (wp_vc_block_s_sconf_aux γ root_ppn prog Φ st st' ρ m m n
              Hblk Hux Hxn Hmatch (fun r _ => eq_refl)
              with "Hsc Hhs Hcap Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hfr Hcont").
  Qed.

End WpSconfVc.
