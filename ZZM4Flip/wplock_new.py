import re
p='WpLock.v'; s=open(p).read()

# ---------------------------------------------------------------- 1. lock_word
old = """  Definition lock_word (lk : mword 64) (v : mword 32) : iProp Σ :=
    (∃ ξ : CtxId, ctx_word4_pointsto ξ lk (DfracOwn 1) v)%I.

  (* the INTRODUCTION leg, which is all the creators need *)
  Lemma lock_word_intro (lk : mword 64) (v : mword 32) :
    lk ↦₄ v ⊢ lock_word lk v.
  Proof. iIntros "H". iExists cur_ctx. iExact "H". Qed."""
new = """  (* >>> A6.84: THE ∃ IS GONE, AND WHAT REPLACED IT IS BETTER.  The ∃ξ
     closed [is_lock]'s term at the cost of an existential nothing could
     eliminate -- "a cell at an unknown ξ licenses no load at ours" -- so
     the two lock leaves that READ the word were unprovable.  At the
     LEDGER tier the cell has no ξ AT ALL: [phys_ledger_word4] is the
     eight-byte carrier's four-byte twin, ξ-free BY CONSTRUCTION, and the
     store gates over it are context-free ([ledger_store_win_at_ok]), so
     release's clear and the AMO's write need no [own_context] either.
     [is_lock] is a closed term for the reason §0.19′ wanted and with no
     residual existential.

     WHAT IT COSTS is the address's MAPPING, which a ledger cell does not
     carry: the invariant keeps the two [lk_addr_claim]s instead.  They
     are PERSISTENT and about the ADDRESS, not the value, so one peek
     serves every leaf ([WpSconfLock.lock_claims]).  <<< *)
  Definition lock_word (lk : mword 64) (v : mword 32) : iProp Σ :=
    TsoCtx.phys_ledger_word4 lk (DfracOwn 1) v.

  (* the INTRODUCTION leg, which is all the creators need.  ONE-WAY, and
     deliberately: the lock's word never goes back to the ctx tower. *)
  Lemma lock_word_intro (lk : mword 64) (v : mword 32) :
    lk ↦₄ v ⊢ lock_word lk v.
  Proof. rewrite /lock_word. iIntros "H". by iApply TsoCtx.ctx_word4_ledger_kt0. Qed."""
assert old in s, "lock_word"; s = s.replace(old, new, 1)

# ---------------------------------------------------------------- 2. the cell
old = """  Definition lk_cpu_res (st : lock_state) (lk : mword 64) (r : string) : iProp Σ :=
    ((∃ ξ : CtxId,
        ctx_word_pointsto ξ (lock_cpu lk) (DfracOwn 1) (lk_cpu_val st)) ∗
     lk_cpu_frag st r)%I."""
new = """  (* THE ADDRESS CLAIM a ledger cell does not carry.  Character for
     character [WpSconfMem.mem_claim] under its alignment -- that file
     sits ABOVE this one, so the content is restated here and
     [WpSconfLock.lock_claims] is the one line that converts (they are
     convertible at [KT0], which is the only tier a lock lives at). *)
  Definition lk_addr_claim (a : Arch.pa) (width : Z) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) width = true⌝ ∗
     ∃ ppn : mword 44,
       kmap_at (svpn_of a) ppn KP_rw ∗
       ⌜(uint a < 274877906944)%Z⌝ ∗
       ⌜addr_is_ram (pa_of ppn a)⌝ ∗
       ⌜ktier_pin KT0 ppn a⌝)%I.

  Global Instance lk_addr_claim_persistent a width :
    Persistent (lk_addr_claim a width).
  Proof. rewrite /lk_addr_claim. apply _. Qed.

  (* a ctx word carries its own claim, which is how the creators pay it *)
  Lemma lk_addr_claim_of4 (lk : mword 64) (dq : dfrac) (v : mword 32) :
    ctx_word4_pointsto (KTR := KT0) cur_ctx lk dq v ⊢ lk_addr_claim lk 4.
  Proof.
    rewrite ctx_word4_pointsto_unfold. iIntros "[%Hal Hb]".
    iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "Hb0".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iEval (rewrite (ctx_pointsto_phys (KTR := KT0))) in "Hb0".
    iDestruct "Hb0" as (ppn) "(#Hk & %Hc & %Hp & Hph)".
    iDestruct (ctx_phys_pointsto_ram with "Hph") as %Hram.
    iSplitR; [done|]. iExists ppn. iFrame "Hk". iPureIntro. split_and!; done.
  Qed.

  (* ---- THE OWNER CELL AT THE LEDGER TIER, WITH THE RACY PAYLOAD ----

     [lk->cpu] is the one cell in the tree that is READ RACILY, by a hart
     that does not hold the lock, and what it must conclude is an
     EXCLUSION ("the recorded owner is not me").  That is a claim about
     the READER'S OWN WRITE HISTORY, so it rides in the ledger element's
     window payload (TsoMemPa §12c/§12d) and NOT in this invariant --
     tso-pin-memo.md §3's rule, and the reason the cell cannot stay in
     the ctx tower. *)
  Definition lk_cpu_pay (lk : mword 64) (v : mword 64)
      (own : agent -> option nat) (lo : nat) : iProp Σ :=
    ([∗ list] j ∈ seq 0 8, ∃ t : nat,
       TsoCtx.phys_ledger_wpay (pa_add (lock_cpu lk) j) (DfracOwn 1)
         (nth_byte v j) t
         (TsoMemPa.TsWin (lock_cpu lk) 8 j lkcpu_z lkcpu_cp own lo))%I.

  (* the AUTHOR's form: the same window with the store's own message
     fragment beside every byte.  That is what makes the HOLDER's read of
     the cell IT wrote exact ([TsoCtx.ledger_read_wpay_vis_ok]) -- and it
     is why the held arm carries more than the free one, which A6.78 §(2)
     named and nothing before it did. *)
  Definition lk_cpu_pay_vis (h : agent) (lk : mword 64) (v : mword 64)
      (own : agent -> option nat) (lo : nat) : iProp Σ :=
    ([∗ list] j ∈ seq 0 8, ∃ t : nat,
       TsoCtx.ledger_vis h 0 t ∗
       TsoCtx.phys_ledger_wpay (pa_add (lock_cpu lk) j) (DfracOwn 1)
         (nth_byte v j) t
         (TsoMemPa.TsWin (lock_cpu lk) 8 j lkcpu_z lkcpu_cp own lo))%I.

  Lemma lk_cpu_pay_vis_forget h lk v own lo :
    lk_cpu_pay_vis h lk v own lo ⊢ lk_cpu_pay lk v own lo.
  Proof.
    rewrite /lk_cpu_pay_vis /lk_cpu_pay.
    iApply big_sepL_impl. iIntros "!>" (k j _) "(%t & _ & H)". by iExists t.
  Qed.

  Global Instance lk_cpu_pay_timeless lk v own lo :
    Timeless (lk_cpu_pay lk v own lo).
  Proof. rewrite /lk_cpu_pay. apply _. Qed.
  Global Instance lk_cpu_pay_vis_timeless h lk v own lo :
    Timeless (lk_cpu_pay_vis h lk v own lo).
  Proof. rewrite /lk_cpu_pay_vis. apply _. Qed.

  (* >>> THE OWN-INVARIANT, AND IT IS ONE SENTENCE: the ONLY agent that
     may be missing an own-last record is the HOLDER.  Acquire's store
     writes the author's own word and REVOKES its entry
     ([ledger_store_wpay_ok]'s second arm); release's writes the clear
     word and RESTORES it (the first).  Every other agent's entry frames.
     A [notheld] reader is a non-holder by definition, so this is exactly
     the premise [lkcpu_read_not_mine] consumes. <<< *)
  Definition lk_own_ok (ex : option CPU) (own : agent -> option nat) : Prop :=
    forall h : agent, own h = None -> exists i : CPU, ex = Some i /\ h = hart_agent i.

  Definition lk_cpu_cell_ex (lk : mword 64) (v : mword 64)
      (ex : option CPU) : iProp Σ :=
    (∃ (own : agent -> option nat) (lo : nat),
       ⌜lk_own_ok ex own⌝ ∗
       match ex with
       | Some i => lk_cpu_pay_vis (hart_agent i) lk v own lo
       | None => lk_cpu_pay lk v own lo
       end)%I.

  Definition lk_cpu_cell (lk : mword 64) (v : mword 64) : iProp Σ :=
    lk_cpu_cell_ex lk v None.

  (* the held cell forgets its author fragment and becomes an ordinary
     one, at the cost of the exactness the holder had *)
  Lemma lk_cpu_cell_ex_forget lk v ex :
    lk_cpu_cell_ex lk v ex ⊢ lk_cpu_cell lk v ∨ ⌜is_Some ex⌝.
  Proof.
    iIntros "(%own & %lo & %Hok & Hb)". destruct ex as [i|].
    - iRight. iPureIntro. by eexists.
    - iLeft. iExists own, lo. by iFrame "Hb".
  Qed.

  (* what [initlock]'s post hands over and every creator takes: the
     window payload at the CLEAR word, plus the address claim the ledger
     cells do not carry. *)
  Definition lk_cpu_fresh (lk : mword 64) : iProp Σ :=
    (lk_addr_claim (lock_cpu lk) 8 ∗ lk_cpu_cell lk (zero_reg : mword 64))%I.

  Definition lk_cpu_res (st : lock_state) (lk : mword 64) (r : string) : iProp Σ :=
    (lk_cpu_cell_ex lk (lk_cpu_val st) (lk_ex st) ∗ lk_cpu_frag st r)%I."""
assert old in s, "lk_cpu_res"; s = s.replace(old, new, 1)

# lk_ex has to be defined before lk_cpu_val's users -- put it next to lk_cpu_val
old = """  Lemma lk_cpu_val_none : lk_cpu_val None = (zero_reg : mword 64)."""
new = """  (* the one agent that may be missing an own-last record in each state:
     the HOLDER, and nobody else (see [lk_own_ok] below). *)
  Definition lk_ex (st : lock_state) : option CPU :=
    match st with Some (i, true) => Some i | _ => None end.

  Lemma lk_cpu_val_none : lk_cpu_val None = (zero_reg : mword 64)."""
assert old in s, "lk_ex"; s = s.replace(old, new, 1)

# ---------------------------------------------------------------- 3. unfolds
old = """  Definition lk_cpu_cell (lk : mword 64) (v : mword 64) : iProp Σ :=
    (∃ ξ : CtxId, ctx_word_pointsto ξ (lock_cpu lk) (DfracOwn 1) v)%I.

  Lemma lk_cpu_cell_intro (lk : mword 64) (v : mword 64) :
    lock_cpu lk ↦₈ v ⊢ lk_cpu_cell lk v.
  Proof. iIntros "H". iExists cur_ctx. iExact "H". Qed.

  (* the free / window form: the whole cell at 0 and no fragment. *)
  Lemma lk_cpu_res_free (lk : mword 64) (r : string) :
    lk_cpu_res None lk r ⊣⊢ lk_cpu_cell lk (zero_reg : mword 64).
  Proof. rewrite /lk_cpu_res /lk_cpu_cell /=. apply bi.sep_emp. Qed.
  Lemma lk_cpu_res_win (i : CPU) (lk : mword 64) (r : string) :
    lk_cpu_res (Some (i, false)) lk r ⊣⊢ lk_cpu_cell lk (zero_reg : mword 64).
  Proof. rewrite /lk_cpu_res /lk_cpu_cell /=. apply bi.sep_emp. Qed.
  Lemma lk_cpu_res_held (i : CPU) (lk : mword 64) (r : string) :
    lk_cpu_res (Some (i, true)) lk r ⊣⊢
    lk_cpu_cell lk (cpus_ptr i) ∗ lk_in i r.
  Proof. rewrite /lk_cpu_res /lk_cpu_cell /=. reflexivity. Qed."""
new = """  (* the free / window form: the whole cell at 0 and no fragment. *)
  Lemma lk_cpu_res_free (lk : mword 64) (r : string) :
    lk_cpu_res None lk r ⊣⊢ lk_cpu_cell lk (zero_reg : mword 64).
  Proof. rewrite /lk_cpu_res /lk_cpu_cell /=. apply bi.sep_emp. Qed.
  Lemma lk_cpu_res_win (i : CPU) (lk : mword 64) (r : string) :
    lk_cpu_res (Some (i, false)) lk r ⊣⊢ lk_cpu_cell lk (zero_reg : mword 64).
  Proof. rewrite /lk_cpu_res /lk_cpu_cell /=. apply bi.sep_emp. Qed.
  (* THE HELD FORM CARRIES MORE THAN THE OTHER TWO, and that is the
     author-fragment point (A6.78 §(2)): the holder's own read of the
     cell must be EXACT, so the held cell keeps the store's message
     fragment beside every byte. *)
  Lemma lk_cpu_res_held (i : CPU) (lk : mword 64) (r : string) :
    lk_cpu_res (Some (i, true)) lk r ⊣⊢
    lk_cpu_cell_ex lk (cpus_ptr i) (Some i) ∗ lk_in i r.
  Proof. rewrite /lk_cpu_res /=. reflexivity. Qed."""
assert old in s, "unfolds"; s = s.replace(old, new, 1)

# ---------------------------------------------------------------- 4. lock_inv
old = """  Definition lock_inv (γ : gname) (lk : mword 64) (s : string)
      (R : CtxId → iProp Σ) : iProp Σ :=
    (∃ (v : mword 32) (st : lock_state),
       lock_word lk v ∗
       lk_cpu_res st lk s ∗
       lock_auth γ st ∗
       (⌜st = None⌝ ∗ ⌜v = (mword_of_int 0 : mword 32)⌝ ∗ lock_frag γ None ∗
          lock_pay R
        ∨ ⌜st ≠ None⌝ ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝))%I."""
new = """  (* THE TWO ADDRESS CLAIMS RIDE HERE, LAST, and outside the ∃: they are
     about the ADDRESSES, so no state mentions them, and they are
     persistent, so one peek serves every leaf.  They are what the ledger
     tier costs (a ledger cell carries no mapping) and they are cheaper
     than what they replaced -- [lock_claims] used to have to take the
     cell APART to read a claim off it, and that is where the last live
     [TsoCtxShim] use lived. *)
  Definition lock_inv (γ : gname) (lk : mword 64) (s : string)
      (R : CtxId → iProp Σ) : iProp Σ :=
    ((∃ (v : mword 32) (st : lock_state),
        lock_word lk v ∗
        lk_cpu_res st lk s ∗
        lock_auth γ st ∗
        (⌜st = None⌝ ∗ ⌜v = (mword_of_int 0 : mword 32)⌝ ∗ lock_frag γ None ∗
           lock_pay R
         ∨ ⌜st ≠ None⌝ ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝)) ∗
     lk_addr_claim lk 4 ∗ lk_addr_claim (lock_cpu lk) 8)%I."""
assert old in s, "lock_inv"; s = s.replace(old, new, 1)

# ---------------------------------------------------------------- 5. finisher
s = s.replace("""      lk ↦₄ (mword_of_int 0 : mword 32) -∗
      lock_cpu lk ↦₈ (zero_reg : mword 64) -∗
      lock_pay R -∗""",
"""      lk ↦₄ (mword_of_int 0 : mword 32) -∗
      lk_cpu_fresh lk -∗
      lock_pay R -∗""", 1)

old = """  Lemma lock_finisher_close γ lk s R D E : ⊢ lock_finisher γ lk s R D emp E.
  Proof.
    iIntros "[Hclose _] Hauth Hfrag Hword Hcpu HR".
    iMod ("Hclose" with "[Hauth Hfrag Hword Hcpu HR]") as "_"; [| by iModIntro].
    iNext. iExists (mword_of_int 0 : mword 32), None.
    iDestruct (lock_word_intro with "Hword") as "Hword".
    rewrite lk_cpu_res_free. iFrame "Hword Hcpu Hauth".
    iLeft. by iFrame "Hfrag HR".
  Qed."""
new = """  Lemma lock_finisher_close γ lk s R D E : ⊢ lock_finisher γ lk s R D emp E.
  Proof.
    iIntros "[Hclose _] Hauth Hfrag Hword [#Hc8 Hcpu] HR".
    iDestruct (lk_addr_claim_of4 with "Hword") as "#Hc4".
    iMod ("Hclose" with "[Hauth Hfrag Hword Hcpu HR]") as "_"; [| by iModIntro].
    iNext. iFrame "Hc4 Hc8".
    iExists (mword_of_int 0 : mword 32), None.
    iDestruct (lock_word_intro with "Hword") as "Hword".
    rewrite lk_cpu_res_free. iFrame "Hword Hcpu Hauth".
    iLeft. by iFrame "Hfrag HR".
  Qed."""
assert old in s, "finisher_close"; s = s.replace(old, new, 1)

old = """    lock_finisher γ lk s R D
      (lk ↦₄ (mword_of_int 0 : mword 32) ∗ lock_cpu lk ↦₈ (zero_reg : mword 64) ∗ Out) E.
  Proof.
    iIntros "Hcomplete [_ Hdispose] Hauth Hfrag Hword Hcpu HR"."""
new = """    lock_finisher γ lk s R D
      (lk ↦₄ (mword_of_int 0 : mword 32) ∗ lk_cpu_fresh lk ∗ Out) E.
  Proof.
    iIntros "Hcomplete [_ Hdispose] Hauth Hfrag Hword Hcpu HR"."""
assert old in s, "finisher_destroy"; s = s.replace(old, new, 1)

# ---------------------------------------------------------------- 6. creators
s = s.replace("""    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_cpu lk ↦₈ (zero_reg : mword 64) -∗
    R cur_ctx ==∗ own_context cur_ctx ∗ ∃ γ : gname, lock_inv γ lk s R.
  Proof.
    iIntros "Hrun Hword Hcpu HR".""",
"""    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lk_cpu_fresh lk -∗
    R cur_ctx ==∗ own_context cur_ctx ∗ ∃ γ : gname, lock_inv γ lk s R.
  Proof.
    iIntros "Hrun Hword [#Hc8 Hcpu] HR".
    iDestruct (lk_addr_claim_of4 with "Hword") as "#Hc4".""", 1)
s = s.replace("""    iModIntro. iExists γ.
    iExists (mword_of_int 0 : mword 32), None.
    iDestruct (lock_word_intro with "Hword") as "Hword".
    rewrite lk_cpu_res_free. iFrame "Hword Hcpu Ha".
    iLeft. iFrame "Hf HR". done.
  Qed.""",
"""    iModIntro. iExists γ. iFrame "Hc4 Hc8".
    iExists (mword_of_int 0 : mword 32), None.
    iDestruct (lock_word_intro with "Hword") as "Hword".
    rewrite lk_cpu_res_free. iFrame "Hword Hcpu Ha".
    iLeft. iFrame "Hf HR". done.
  Qed.""", 1)

s = s.replace("""    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_cpu lk ↦₈ (zero_reg : mword 64) ==∗
    ∃ γ : gname, ∀ (R : CtxId → iProp Σ) (D : iProp Σ),
      ⌜CtxMorph R⌝ -∗ own_context cur_ctx -∗
      R cur_ctx ={E}=∗ own_context cur_ctx ∗ inv lockN (lock_inv γ lk s R ∨ D).
  Proof.
    iIntros "Hword Hcpu".""",
"""    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lk_cpu_fresh lk ==∗
    ∃ γ : gname, ∀ (R : CtxId → iProp Σ) (D : iProp Σ),
      ⌜CtxMorph R⌝ -∗ own_context cur_ctx -∗
      R cur_ctx ={E}=∗ own_context cur_ctx ∗ inv lockN (lock_inv γ lk s R ∨ D).
  Proof.
    iIntros "Hword [#Hc8 Hcpu]".
    iDestruct (lk_addr_claim_of4 with "Hword") as "#Hc4".""", 1)
s = s.replace("""    iApply (inv_alloc lockN E (lock_inv γ lk s R ∨ D)).
    iNext. iLeft. iExists (mword_of_int 0 : mword 32), None.""",
"""    iApply (inv_alloc lockN E (lock_inv γ lk s R ∨ D)).
    iNext. iLeft. iFrame "Hc4 Hc8". iExists (mword_of_int 0 : mword 32), None.""", 1)

s = s.replace("""    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_cpu lk ↦₈ (zero_reg : mword 64) -∗
    R cur_ctx ={E}=∗ own_context cur_ctx ∗ ∃ γ : gname, is_lock γ lk s R.""",
"""    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lk_cpu_fresh lk -∗
    R cur_ctx ={E}=∗ own_context cur_ctx ∗ ∃ γ : gname, is_lock γ lk s R.""", 1)

s = s.replace("""    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_cpu lk ↦₈ (zero_reg : mword 64) ==∗
    ∃ γ : gname, ∀ R : CtxId → iProp Σ,""",
"""    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lk_cpu_fresh lk ==∗
    ∃ γ : gname, ∀ R : CtxId → iProp Σ,""", 1)
s = s.replace("""    iIntros "#Hnm Hword Hcpu".
    iMod (own_alloc ((●E (None : leibnizO lock_state) ⋅ ◯E (None : leibnizO lock_state))
                     : lockUR)) as (γ) "H"; [ apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iModIntro. iExists γ. iIntros (R) "%HmR Hrun HR".""",
"""    iIntros "#Hnm Hword [#Hc8 Hcpu]".
    iDestruct (lk_addr_claim_of4 with "Hword") as "#Hc4".
    iMod (own_alloc ((●E (None : leibnizO lock_state) ⋅ ◯E (None : leibnizO lock_state))
                     : lockUR)) as (γ) "H"; [ apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iModIntro. iExists γ. iIntros (R) "%HmR Hrun HR".""", 1)
s = s.replace("""    iMod (inv_alloc lockN E (lock_inv γ lk s R) with "[Hword Hcpu Ha Hf HR]") as "#Hinv".
    { iNext. iExists (mword_of_int 0 : mword 32), None.""",
"""    iMod (inv_alloc lockN E (lock_inv γ lk s R) with "[Hword Hcpu Ha Hf HR]") as "#Hinv".
    { iNext. iFrame "Hc4 Hc8". iExists (mword_of_int 0 : mword 32), None.""", 1)

open(p,'w').write(s)
print("patched")
