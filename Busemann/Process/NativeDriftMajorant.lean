/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.LatticeDriftMajorant
import Busemann.Process.ShiftTopology

public import Busemann.Process.NativeCocycleTriangleShape
public import Martin2004.Shape.ExpectedRateShape
import Martin2004.Shape.ExpectedRateUniform
import ProbabilityBasics.Probability.AbsoluteMomentLowerTail
import ProbabilityBasics.Probability.AbsoluteMomentTail
import LPP_Foundations.Model.RecoveryAntidiagonal
import LPP_Foundations.Analysis.LatticeMajorant
import Mathlib.Tactic

/-! The canonical random drift majorizes the expected-rate shape. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal NNReal BigOperators Topology

namespace LPP.Busemann

/-- Recovery and the native cocycle shape estimate make the canonical conditional
mean a linear majorant on the whole quadrant. This is the majorant step of
JR1810.03580v3, Theorem 4.4 and Lemma 4.5. -/
theorem ae_canonical_drift_majorizes_expected_shape
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hShift : ∀ z : Lattice, MeasurePreserving (processShift z) P P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : is_shift_covariant_cocycle P processShift B)
    (hInt : ∀ x y, Integrable (B x y) P)
    (hRec : recovers_weight_map_ae P processEnvironment B)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) :
    let mProc : MeasurableSpace ProcessSample := inferInstance
    let I : MeasurableSpace ProcessSample :=
      ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (processShift z)
    letI : MeasurableSpace ProcessSample := mProc
    let u : Fin 2 → ProcessSample → ℝ :=
      fun i => P[B 0 (finiteEdgeStep i) | I]
    ∀ᵐ s ∂P, ∀ z : Quadrant,
      g z ≤ u 0 s * (z.1 : ℝ) + u 1 s * (z.2 : ℝ) := by
  exact ae_canonical_drift_majorizes_expected_shape_of_action μ hmoment P processShift processEnvironment measurable_fst hMarginal processShift_zero processShift_add hShift B hB hInt hRec g hg

end LPP.Busemann
