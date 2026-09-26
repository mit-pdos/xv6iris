/-
THE UNION LEDGER'S PURE CARRIER -- the reached part of Rocq `UnionOutPure.v`
(`/shared/xv6rocq/iris/UnionOutPure.v`, 313 lines, pinned `1900b8a43`; cut
C9e', design union.md section 4), row U0-5 of `notes/briefs/union.md`.
Pure.

Rocq's header, abridged: `FileOutPure`'s conclusion body at the union model
`ulmG`: the per-cycle boot states `s0s` of `FileDisc.file_phi` (the first
absent, each later one admissible against the lines typed in strictly
earlier cycles), with the output claim `lmGoodOut ulmG` in place of
`good_out_f` and the antecedent the union's discipline `lmDisc ulmG`.

Names: Rocq's, camelCased (`union_phi` → `unionPhi`, `union_phi_body` →
`unionPhiBody`, `union_phi_of_body` → `unionPhi_of_body`); Rocq's local
notation `U` is written out as `ulmG`.

Deviations from Rocq:
1. Spelling: `!!` is `[·]?`, `Forall2` is `List.Forall₂`, `cycles_of` is
   `cyclesOf`, `S k` is `k + 1`.
2. CONE TRIM (glob walk from `union_adequacy_closed` re-run at the pin: 4 of
   19 declarations reached -- `U`, `union_phi`, `union_phi_body`,
   `union_phi_of_body`).  Not ported, as unreached: section 1 (`um_sess_nonnil`,
   `um_disc_open_seg`, `lm_disc_first_out`; `GenOutHist` states the generic
   first-drain facts the claim reads), the notations `UB`/`UK`,
   `union_phi_body_nil`, `union_st_ok`, `efl_of_first_out_u` and the
   `union_phi_body_step_io/off/on/last_adm/out/drain` steps.
-/
import Xv6.UnionDisc

namespace Xv6

open MachCSL

/-- **Rocq `union_phi`**: THE CONCLUSION -- `FileDisc.file_phi` at the union. -/
def unionPhi (h : List Obs) : Prop :=
  lmDisc ulmG h →
  ∃ s0s : List Fstate,
    s0s.length = (cyclesOf h).length
    ∧ (∀ s, s0s[0]? = some s → s = ∅)
    ∧ (∀ k s, s0s[k + 1]? = some s → fadmBoot (echofLinesBefore h (k + 1)) s)
    ∧ List.Forall₂ (lmGoodOut ulmG) s0s (cyclesOf h)

/-- **Rocq `union_phi_body`**: its body, at given boot states. -/
def unionPhiBody (h : List Obs) (s0s : List Fstate) : Prop :=
  s0s.length = (cyclesOf h).length
  ∧ (∀ s, s0s[0]? = some s → s = ∅)
  ∧ (∀ k s, s0s[k + 1]? = some s → fadmBoot (echofLinesBefore h (k + 1)) s)
  ∧ List.Forall₂ (lmGoodOut ulmG) s0s (cyclesOf h)

theorem unionPhi_of_body (h : List Obs) (s0s : List Fstate)
    (hb : lmDisc ulmG h → unionPhiBody h s0s) : unionPhi h :=
  fun hd => ⟨s0s, hb hd⟩

end Xv6
