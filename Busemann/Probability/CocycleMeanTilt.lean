/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The ordinary mean tilt of a Busemann cocycle. -/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- The negative means of the two origin increments, as in Theorem 3.11(c) of
*Strong existence and uniqueness of the tilt-indexed Busemann process in the planar
corner growth model*, Electronic Journal of Probability 31 (2026), 1–35,
https://doi.org/10.1214/26-EJP1634. These are ordinary integrals. Integrability is supplied
by the generalized Busemann hypotheses in applications. -/
noncomputable def meanCocycleTilt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Lattice → Lattice → Ω → ℝ) : ℝ × ℝ :=
  (-(∫ ω, B 0 (1, 0) ω ∂P), -(∫ ω, B 0 (0, 1) ω ∂P))

/-- The mean tilt is `h` exactly when both origin increments have the corresponding
negative means. -/
theorem meanCocycleTilt_eq_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Lattice → Lattice → Ω → ℝ) (h : ℝ × ℝ) :
    meanCocycleTilt P B = h ↔
      (∫ ω, B 0 (1, 0) ω ∂P) = -h.1 ∧ (∫ ω, B 0 (0, 1) ω ∂P) = -h.2 := by
  rcases h with ⟨h₁, h₂⟩
  simp only [meanCocycleTilt, Prod.mk.injEq, neg_eq_iff_eq_neg]

end LPP.Busemann
