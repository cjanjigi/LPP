/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.FiniteBusemannEdge
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

import LPP_Foundations.Probability.PassageIntegrable

/-!
# Integrability of the finite Busemann construction

An integrable marginal makes every finite tilted potential and finite Busemann
edge integrable under the induced environment law. The proof follows the finite
maximum in the construction (JR1810.03580v3).
-/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- The real value of the finite tilted potential is integrable under an
integrable marginal law, for every horizon. This follows from the finite-path
maximum in the construction (JR1810.03580v3). -/
theorem integrable_finiteTiltedPotential_toReal (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : Integrable (fun t : ℝ => t) μ)
    (h : ℝ × ℝ) (x : Lattice) (n : ℤ) :
    Integrable (fun ω : Environment => (finiteTiltedPotential ω h x n).toReal)
      (environmentLaw μ) := by
  classical
  by_cases hactive : x.1 + x.2 ≤ n
  · let m : ℕ := (n - (x.1 + x.2)).toNat
    let candidate : Fin (m + 1) → Environment → ℝ := fun k ω =>
      lastPassage ω x (k.val, m - k.val) +
        h.1 * (k.val : ℝ) + h.2 * ((m - k.val : ℕ) : ℝ)

    -- Each candidate is an integrable passage value plus two constants.
    have hcandidate (k : Fin (m + 1)) :
        Integrable (candidate k) (environmentLaw μ) := by
      dsimp only [candidate]
      have hpassage :
          Integrable (fun ω : Environment =>
            lastPassage ω x (k.val, m - k.val)) (environmentLaw μ) :=
        integrable_lastPassage μ hμ x (k.val, m - k.val)
      have htilt₁ : Integrable
          (fun _ω : Environment => h.1 * (k.val : ℝ)) (environmentLaw μ) :=
        integrable_const _
      have htilt₂ : Integrable
          (fun _ω : Environment => h.2 * ((m - k.val : ℕ) : ℝ))
          (environmentLaw μ) :=
        integrable_const _
      exact (hpassage.add htilt₁).add htilt₂

    -- Integrability passes to the finite pointwise supremum.
    have hmaximum : Integrable
        (Finset.univ.sup' Finset.univ_nonempty candidate)
        (environmentLaw μ) :=
      Finset.sup'_induction
        (p := fun f : Environment → ℝ =>
          Integrable f (environmentLaw μ))
        Finset.univ_nonempty _
        (fun _ hf _ hg => hf.sup hg)
        (fun k _ => hcandidate k)

    -- The source image maximum is this same pointwise supremum.
    have hrepresentation :
        (fun ω : Environment => finiteTiltedPotential ω h x n) =
          fun ω =>
            ((Finset.univ.sup' Finset.univ_nonempty candidate ω : ℝ) : EReal) := by
      funext ω
      simp [finiteTiltedPotential, hactive, m, candidate,
        Finset.max'_eq_sup', Finset.sup'_image]
    have hreal :
        (fun ω : Environment => (finiteTiltedPotential ω h x n).toReal) =
          Finset.univ.sup' Finset.univ_nonempty candidate := by
      funext ω
      have hω := congrFun hrepresentation ω
      rw [hω]
      exact EReal.toReal_coe _
    rw [hreal]
    exact hmaximum
  · have hzero :
        (fun ω : Environment => (finiteTiltedPotential ω h x n).toReal) =
          fun _ω : Environment => 0 := by
      funext ω
      simp [finiteTiltedPotential, hactive]
    rw [hzero]
    exact integrable_const _

/-- The finite Busemann edge is integrable under an integrable marginal law,
including its zero value when its source is inactive. This follows from the
finite potential difference in the construction (JR1810.03580v3). -/
theorem integrable_finiteBusemannEdge (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : Integrable (fun t : ℝ => t) μ)
    (h : ℝ × ℝ) (x : Lattice) (n : ℤ) (i : Fin 2) :
    Integrable (fun ω : Environment => finiteBusemannEdge ω h x n i)
      (environmentLaw μ) := by
  classical
  by_cases hactive : x.1 + x.2 < n
  · have hcurrent : Integrable (fun ω : Environment =>
        (finiteTiltedPotential ω h x n).toReal) (environmentLaw μ) :=
      integrable_finiteTiltedPotential_toReal μ hμ h x n
    have hnext : Integrable (fun ω : Environment =>
        (finiteTiltedPotential ω h (x + finiteEdgeStep i) n).toReal)
        (environmentLaw μ) :=
      integrable_finiteTiltedPotential_toReal μ hμ h
        (x + finiteEdgeStep i) n
    have htilt : Integrable
        (fun _ω : Environment => finiteTiltCoordinate h i)
        (environmentLaw μ) :=
      integrable_const _

    -- On an active source, the edge is the difference of these potentials and the tilt.
    have hrepresentation :
        (fun ω : Environment => finiteBusemannEdge ω h x n i) =
          fun ω =>
            (finiteTiltedPotential ω h x n).toReal -
              (finiteTiltedPotential ω h (x + finiteEdgeStep i) n).toReal -
              finiteTiltCoordinate h i := by
      funext ω
      simp [finiteBusemannEdge, hactive]
    rw [hrepresentation]
    exact (hcurrent.sub hnext).sub htilt
  · have hzero :
        (fun ω : Environment => finiteBusemannEdge ω h x n i) =
          fun _ω : Environment => 0 := by
      funext ω
      simp [finiteBusemannEdge, hactive]
    rw [hzero]
    exact integrable_const _

end LPP.Busemann
