/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.FiniteBusemannEdge
import LPP_Foundations.Model.LastPassage.Locality
import Mathlib.Tactic.FinCases

/-! Deterministic future locality for the actual finite Busemann quantities.
This is the finite-dependence input to JR1810.03580v3, Theorem 4.8(b). -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- Agreement on a site's northeast cone preserves its finite tilted potential.
This is the finite-horizon locality used before the independence conclusion in
JR1810.03580v3, Theorem 4.8(b) and its proof. -/
theorem finiteTiltedPotential_eq_of_eqOn_Ici (ω η : Environment) (h : ℝ × ℝ)
    (x : Lattice) (n : ℤ)
    (hAgree : Set.EqOn ω η (Set.Ici x)) :
    finiteTiltedPotential ω h x n = finiteTiltedPotential η h x n := by
  classical
  by_cases hactive : x.1 + x.2 ≤ n
  · unfold finiteTiltedPotential
    rw [dite_eq_left hactive]
    rw [dite_eq_left hactive]
    let m : ℕ := (n - (x.1 + x.2)).toNat
    let fω : Fin (m + 1) → ℝ := fun k =>
      lastPassage ω x (k.val, m - k.val) +
        h.1 * (k.val : ℝ) + h.2 * ((m - k.val : ℕ) : ℝ)
    let fη : Fin (m + 1) → ℝ := fun k =>
      lastPassage η x (k.val, m - k.val) +
        h.1 * (k.val : ℝ) + h.2 * ((m - k.val : ℕ) : ℝ)
    have hCandidate : ∀ k : Fin (m + 1), fω k = fη k := by
      intro k
      dsimp only [fω, fη]
      -- The endpoint rectangle lies in the given northeast cone.
      have hPassage : lastPassage ω x (k.val, m - k.val) =
          lastPassage η x (k.val, m - k.val) :=
        lastPassage_eq_of_eqOn (fun y hy => hAgree hy.1)
      rw [hPassage]
    have hImage : Finset.univ.image fω = Finset.univ.image fη := by
      apply Finset.image_congr
      intro k hk
      exact hCandidate k
    have hMax : (Finset.univ.image fω).max'
        (Finset.Nonempty.image Finset.univ_nonempty fω) =
        (Finset.univ.image fη).max'
          (Finset.Nonempty.image Finset.univ_nonempty fη) := by
      apply le_antisymm
      · apply Finset.max'_le
        intro value hvalue
        have hvalueη : value ∈ Finset.univ.image fη := by
          rw [← hImage]
          exact hvalue
        exact Finset.le_max' _ _ hvalueη
      · apply Finset.max'_le
        intro value hvalue
        have hvalueω : value ∈ Finset.univ.image fω := by
          rw [hImage]
          exact hvalue
        exact Finset.le_max' _ _ hvalueω
    exact congrArg (fun value : ℝ => (value : EReal)) hMax
  · simp [finiteTiltedPotential, hactive]

/-- Agreement on a site's northeast cone preserves each actual finite edge,
including the inactive zero branch; see JR1810.03580v3, Theorem 4.8(b). -/
theorem finiteBusemannEdge_eq_of_eqOn_Ici (ω η : Environment) (h : ℝ × ℝ)
    (x : Lattice) (n : ℤ) (i : Fin 2)
    (hAgree : Set.EqOn ω η (Set.Ici x)) :
    finiteBusemannEdge ω h x n i = finiteBusemannEdge η h x n i := by
  classical
  by_cases hactive : x.1 + x.2 < n
  · have hNeighbor : x ≤ x + finiteEdgeStep i := by
      fin_cases i
      · change x.1 ≤ x.1 + 1 ∧ x.2 ≤ x.2 + 0
        constructor <;> omega
      · change x.1 ≤ x.1 + 0 ∧ x.2 ≤ x.2 + 1
        constructor <;> omega
    have hFuture : Set.EqOn ω η (Set.Ici (x + finiteEdgeStep i)) := by
      intro y hy
      exact hAgree (le_trans hNeighbor hy)
    -- Locality applies once at the start and once at the outgoing neighbor.
    have hStart := finiteTiltedPotential_eq_of_eqOn_Ici ω η h x n hAgree
    have hEnd := finiteTiltedPotential_eq_of_eqOn_Ici ω η h
      (x + finiteEdgeStep i) n hFuture
    simp only [finiteBusemannEdge, dite_eq_left hactive]
    rw [hStart, hEnd]
  · simp [finiteBusemannEdge, hactive]

end LPP.Busemann
