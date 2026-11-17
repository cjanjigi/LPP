-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Busemann.Full.RecoveringCocycleSupport

public import LPP_Foundations.Analysis.QuadrantSuperdifferential
public import LPP_Foundations.Analysis.ClosedUnitDirections
public import Martin2004.Shape.ExpectedRateShape
public import Busemann.Frozen.Definitions.RandomCocycle
public import Busemann.Frozen.Definitions.RecoveryAE
public import Busemann.Frozen.Definitions.InteriorDirection
public import Busemann.Frozen.Definitions.LatticeInvariantSigma
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Topology.MetricSpace.Polish

/-! The joint zero-temperature statement of JR arXiv:1810.03580v3, Lemma 4.5. -/

@[expose] public section

open MeasureTheory LPPDifferentiability LPP.Busemann
open scoped ENNReal

namespace LPP.Busemann

/-- A recovering integrable covariant cocycle has an invariant tilt with interior
support contact. Mean support at a fixed unit direction passes to the random
tilt, and an extreme mean forces that tilt to be almost surely constant.
JR arXiv:1810.03580v3, Lemma 4.5(a,b,c), specialized to zero temperature. -/
theorem recovering_cocycle_support_and_invariant_tilt :
  ∀ (Ω : Type*) [TopologicalSpace Ω] [PolishSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (T : Lattice → Ω → Ω) (weights : Ω → Environment)
    (B : Lattice → Lattice → Ω → ℝ) (g : Quadrant → ℝ),
  (∀ ω : Ω, T 0 ω = ω) →
  (∀ (x y : Lattice) (ω : Ω), T x (T y ω) = T (x + y) ω) →
  (∀ z : Lattice, MeasurePreserving (T z) P P) →
  Measurable weights →
  P.map weights = environmentLaw μ →
  (∀ (z x : Lattice) (ω : Ω), weights (T z ω) x = weights ω (z + x)) →
  (∃ p : ℝ, 2 < p ∧
    (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) →
  (0 < ∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ) →
  IsExpectedRateShape μ g →
  is_shift_covariant_cocycle P T B →
  recovers_weight_map_ae P weights B →
  Integrable (B 0 (1, 0)) P →
  Integrable (B 0 (0, 1)) P →
  let h : Ω → ℝ × ℝ := fun ω =>
    (-(P[B 0 (1, 0) | latticeInvariantSigma T] ω),
      -(P[B 0 (0, 1) | latticeInvariantSigma T] ω))
  let hMean : ℝ × ℝ :=
    (∫ ω, (h ω).1 ∂P, ∫ ω, (h ω).2 ∂P)
  (∀ᵐ ω ∂P, ∃ ξ : InteriorDirection,
    -(h ω) ∈ quadrantSuperdifferential g ξ.val) ∧
  (∀ ξ : Quadrant, ξ ∈ closedUnitDirections →
    -hMean ∈ quadrantSuperdifferential g ξ →
      ∀ᵐ ω ∂P, -(h ω) ∈ quadrantSuperdifferential g ξ) ∧
  (∀ ξ : Quadrant, ξ ∈ closedUnitDirections →
    -hMean ∈ Set.extremePoints ℝ (quadrantSuperdifferential g ξ) →
      ∀ᵐ ω ∂P, h ω = hMean) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact LPP.Busemann.Proof.recovering_cocycle_support_and_invariant_tilt
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end LPP.Busemann

-- FROZEN_ANCHOR_SUFFIX_END
