/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.FiniteBusemannArrayAtSharedHorizon
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

import LPP_Foundations.Probability.PassageMeasurable
import Mathlib.MeasureTheory.Order.Lattice

/-!
# Measurability of the literal finite Busemann construction

For fixed finite parameters, the point-to-line value and edge value are
measurable functions of the environment. The array is measurable on the
product of the environment and its single shared finite horizon coordinate.
-/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- For fixed tilt, endpoint and horizon, the literal finite point-to-line
potential from `FiniteTiltedPotential.lean` is measurable in the environment. -/
theorem measurable_finiteTiltedPotential (h : ℝ × ℝ) (x : Lattice) (n : ℤ) :
    Measurable (fun ω : Environment => finiteTiltedPotential ω h x n) := by
  classical
  by_cases hactive : x.1 + x.2 ≤ n
  · let m : ℕ := (n - (x.1 + x.2)).toNat
    let candidate : Fin (m + 1) → Environment → ℝ := fun k ω =>
      lastPassage ω x (k.val, m - k.val) +
        h.1 * (k.val : ℝ) + h.2 * ((m - k.val : ℕ) : ℝ)

    -- Each candidate is a passage time plus a deterministic tilt.
    have hcandidate (k : Fin (m + 1)) : Measurable (candidate k) := by
      dsimp only [candidate]
      have hpassage :
          Measurable (fun ω : Environment => lastPassage ω x (k.val, m - k.val)) :=
        measurable_lastPassage x (k.val, m - k.val)
      exact (hpassage.add measurable_const).add measurable_const

    -- A finite supremum preserves measurability.
    have hmaximum : Measurable
        (Finset.univ.sup' Finset.univ_nonempty candidate) :=
      Finset.measurable_sup' Finset.univ_nonempty (fun k _hk => hcandidate k)

    -- The image maximum in the definition is this same finite supremum.
    have hrepresentation :
        (fun ω : Environment => finiteTiltedPotential ω h x n) =
          fun ω => ((Finset.univ.sup' Finset.univ_nonempty candidate ω : ℝ) : EReal) := by
      funext ω
      simp [finiteTiltedPotential, hactive, m, candidate,
        Finset.max'_eq_sup', Finset.sup'_image]
    rw [hrepresentation]
    exact hmaximum.coe_real_ereal
  · simp [finiteTiltedPotential, hactive]

/-- For fixed parameters, the literal finite edge from
`FiniteBusemannEdge.lean` is measurable in the environment. -/
theorem measurable_finiteBusemannEdge (h : ℝ × ℝ) (x : Lattice) (n : ℤ)
    (i : Fin 2) :
    Measurable (fun ω : Environment => finiteBusemannEdge ω h x n i) := by
  classical
  by_cases hactive : x.1 + x.2 < n
  · have hcurrent : Measurable (fun ω : Environment =>
        (finiteTiltedPotential ω h x n).toReal) :=
      (measurable_finiteTiltedPotential h x n).ereal_toReal
    have hnext : Measurable (fun ω : Environment =>
        (finiteTiltedPotential ω h (x + finiteEdgeStep i) n).toReal) :=
      (measurable_finiteTiltedPotential h (x + finiteEdgeStep i) n).ereal_toReal
    have htilt : Measurable (fun _ω : Environment => finiteTiltCoordinate h i) :=
      measurable_const

    -- In the active branch the edge is the difference of the two finite values and tilt.
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
  · simp [finiteBusemannEdge, hactive]

/-- For each fixed `n` and tilt sequence, the literal array in
`FiniteBusemannArrayAtSharedHorizon.lean` is measurable on its environment and
single shared `Fin (n + 1)` horizon input. -/
theorem measurable_finiteBusemannArrayAtSharedHorizon (n : ℕ)
    (h : ℕ → ℝ × ℝ) :
    Measurable (finiteBusemannArrayAtSharedHorizon n h) := by
  change Measurable (fun p : Environment × Fin (n + 1) =>
    fun j x i => finiteBusemannEdge p.1 (h j) x ((p.2.val + 1 : ℕ) : ℤ) i)
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro i

  -- Each fixed horizon gives a measurable environment section.
  have hsection (k : Fin (n + 1)) :
      Measurable (fun ω : Environment =>
        finiteBusemannEdge ω (h j) x ((k.val + 1 : ℕ) : ℤ) i) :=
    measurable_finiteBusemannEdge (h j) x ((k.val + 1 : ℕ) : ℤ) i

  -- Discrete product measurability selects the horizon from the shared Fin input.
  apply measurable_from_prod_countable_left
  intro k
  simpa only using hsection k

end LPP.Busemann
