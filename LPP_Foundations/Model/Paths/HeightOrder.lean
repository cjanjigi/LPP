/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
import Lean.Elab.Tactic.Omega

/-! Strict height ordering for finite initial segments of up-right paths.

The only input is the finite lattice geometry of Appendix A.4 of the paper cited
below; no passage-time or probabilistic structure is used.
-/

@[expose] public section

namespace LPPDifferentiability

/-- Two up-right paths with the same initial level and no common vertex at any
matching index keep the same strict vertical order from index zero to `N`.
This is the finite entry/exit ordering argument in Georgiou, Rassoul-Agha, and
Seppäläinen, *Geodesics and the competition interface for the corner growth
model*, Appendix A.4, lines 1616–1632. -/
theorem up_right_paths_strict_height_order_iff_of_disjoint
    (p q : ℕ → Lattice) (N : ℕ)
    (hp : ∀ n, p (n+1) = p n + (1,0) ∨ p (n+1) = p n + (0,1))
    (hq : ∀ n, q (n+1) = q n + (1,0) ∨ q (n+1) = q n + (0,1))
    (hLevel : (p 0).1 + (p 0).2 = (q 0).1 + (q 0).2)
    (hAvoid : ∀ n, n ≤ N → p n ≠ q n) :
    ((p 0).2 < (q 0).2 ↔ (p N).2 < (q N).2) := by
  -- Every unit step raises the coordinate sum by one.
  have path_level (r : ℕ → Lattice)
      (hr : ∀ n, r (n+1) = r n + (1,0) ∨ r (n+1) = r n + (0,1)) :
      ∀ n, (r n).1 + (r n).2 = (r 0).1 + (r 0).2 + (n : ℤ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rcases hr n with h | h <;>
          simp only [h, Prod.fst_add, Prod.snd_add, Nat.cast_succ] <;> omega

  -- A unit step keeps height fixed or raises it by one.
  have path_height_step_bounds (r : ℕ → Lattice)
      (hr : ∀ n, r (n+1) = r n + (1,0) ∨ r (n+1) = r n + (0,1)) (n : ℕ) :
      (r n).2 ≤ (r (n+1)).2 ∧ (r (n+1)).2 ≤ (r n).2 + 1 := by
    rcases hr n with h | h <;> simp only [h, Prod.snd_add] <;> omega

  -- A strict height order can fail at the next index only if the paths meet.
  have preserves_strict_height_order
      (r s : ℕ → Lattice)
      (hr : ∀ n, r (n+1) = r n + (1,0) ∨ r (n+1) = r n + (0,1))
      (hs : ∀ n, s (n+1) = s n + (1,0) ∨ s (n+1) = s n + (0,1))
      (hInitialLevel : (r 0).1 + (r 0).2 = (s 0).1 + (s 0).2)
      (hNoMeeting : ∀ n, n ≤ N → r n ≠ s n) :
      (r 0).2 < (s 0).2 → (r N).2 < (s N).2 := by
    intro hInitialOrder
    have same_level (n : ℕ) : (r n).1 + (r n).2 = (s n).1 + (s n).2 := by
      have hrLevel := path_level r hr n
      have hsLevel := path_level s hs n
      omega
    have order_through_index (n : ℕ) : n ≤ N → (r n).2 < (s n).2 := by
      induction n with
      | zero =>
          intro _
          exact hInitialOrder
      | succ n ih =>
          intro hn
          have hPreviousOrder : (r n).2 < (s n).2 := ih (by omega)
          rcases path_height_step_bounds r hr n with ⟨hrLower, hrUpper⟩
          rcases path_height_step_bounds s hs n with ⟨hsLower, hsUpper⟩
          have hNextWeakOrder : (r (n+1)).2 ≤ (s (n+1)).2 := by omega
          have hNextAvoid : r (n+1) ≠ s (n+1) := hNoMeeting (n+1) (by omega)
          have hNextHeightNe : (r (n+1)).2 ≠ (s (n+1)).2 := by
            intro hEqualHeight
            have hEqualVertex : r (n+1) = s (n+1) := by
              apply Prod.ext
              · have hEqualLevel := same_level (n+1)
                omega
              · exact hEqualHeight
            exact hNextAvoid hEqualVertex
          omega
    exact order_through_index N (by omega)

  have hForward : (p 0).2 < (q 0).2 → (p N).2 < (q N).2 :=
    preserves_strict_height_order p q hp hq hLevel hAvoid

  -- Avoidance and the common initial level rule out equal initial heights.
  have hInitialHeightNe : (p 0).2 ≠ (q 0).2 := by
    intro hEqualHeight
    have hEqualVertex : p 0 = q 0 := by
      apply Prod.ext
      · omega
      · exact hEqualHeight
    exact hAvoid 0 (Nat.zero_le N) hEqualVertex

  -- If the final order holds, the opposite initial order would persist for the swapped paths.
  constructor
  · exact hForward
  · intro hFinalOrder
    by_contra hNotInitialOrder
    have hReverseInitial : (q 0).2 < (p 0).2 := by omega
    have hReverseFinal : (q N).2 < (p N).2 :=
      preserves_strict_height_order q p hq hp hLevel.symm
        (fun n hn => (hAvoid n hn).symm) hReverseInitial
    omega

end LPPDifferentiability
