/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.RandomCocycle
public import LPP_Foundations.Frozen.Analysis.QuadrantSuperdifferential
public import Mathlib.Analysis.Convex.Extreme
public import Busemann.Frozen.Definitions.RecoveryAE
public import Busemann.Frozen.Definitions.LatticeInvariantSigma
public import Busemann.Frozen.Definitions.InteriorDirection
public import LPP_Foundations.Analysis.ClosedUnitDirections
public import Martin2004.Shape.ExpectedRateShape
import Busemann.Probability.CocycleIntegrability
import Busemann.Process.LatticeCocycleTriangleShape
import Busemann.Process.LatticeDriftMajorant
import Busemann.Geometry.RecoveryInteriorContact
import LPP_Foundations.Analysis.ShapeBoundarySuperdifferential
import Busemann.Process.MeanSupportTransfer
import ProbabilityBasics.Probability.ExtremeMean
import LPP_Foundations.Analysis.QuadrantSuperdifferentialGeometry
import Martin2004.Shape.ExpectedRateUniform
import ProbabilityBasics.Probability.AbsoluteMomentTail
import ProbabilityBasics.Probability.AbsoluteMomentLowerTail
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! Recovering cocycle support and its invariant tilt. -/
public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal NNReal BigOperators Topology
namespace LPP.Busemann.Proof

/-- A recovering cocycle has an interior support, transfers fixed mean supports
almost surely, and has constant tilt when its mean is extreme. This is
JR arXiv:1810.03580v3, Lemma 4.5. -/
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
      ∀ᵐ ω ∂P, h ω = hMean) := by
  intro Ω _ _ _ _ P _ μ _ T weights B g hzero hrootAdd hShift hWeightsMeas
    hMarginal _hWeightsShift hmoment hvariance hg hB hRec hEdge1 hEdge2
  let mΩ0 : MeasurableSpace Ω := inferInstance
  let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
  let : MeasurableSpace Ω := mΩ0
  let h : Ω → ℝ × ℝ := fun ω =>
    (-(P[B 0 (1, 0) | I] ω), -(P[B 0 (0, 1) | I] ω))
  let hMean : ℝ × ℝ := (∫ ω, (h ω).1 ∂P, ∫ ω, (h ω).2 ∂P)
  let u : Fin 2 → Ω → ℝ := fun i => P[B 0 (finiteEdgeStep i) | I]
  let Δ : ℕ → Finset Lattice := fun n => insert 0
    (((Finset.Icc (0 : ℤ) (n : ℤ)).product
      (Finset.Icc (0 : ℤ) (n : ℤ))).filter
        (fun x => x.1 + x.2 ≤ (n : ℤ)))
  change (∀ᵐ ω ∂P, ∃ ξ : InteriorDirection,
    -(h ω) ∈ quadrantSuperdifferential g ξ.val) ∧
    (∀ ξ : Quadrant, ξ ∈ closedUnitDirections →
      -hMean ∈ quadrantSuperdifferential g ξ →
      ∀ᵐ ω ∂P, -(h ω) ∈ quadrantSuperdifferential g ξ) ∧
    (∀ ξ : Quadrant, ξ ∈ closedUnitDirections →
      -hMean ∈ Set.extremePoints ℝ (quadrantSuperdifferential g ξ) →
      ∀ᵐ ω ∂P, h ω = hMean)
  have hadd (z w : Lattice) (ω : Ω) : T (z + w) ω = T z (T w ω) :=
    (hrootAdd z w ω).symm
  have hInt : ∀ x y, Integrable (B x y) P :=
    integrable_cocycle_of_integrable_origin_edges P T B hShift hB hEdge1 hEdge2
  obtain ⟨p, hp, hpMoment⟩ := hmoment
  have hmoment' : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞ := ⟨p, hp, hpMoment⟩
  have hpos := (ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment
    μ hp hpMoment).2
  have hneg := ProbabilityBasics.integrated_sqrt_lower_tail_lt_top_of_absolute_moment
    μ hp hpMoment
  obtain ⟨hcont, hhomCoord, hshape⟩ := ae_uniform_of_isExpectedRateShape μ hneg hpos hg
  have hhom (c : ℝ≥0) (z : Quadrant) : g (c • z) = (c : ℝ) * g z := hhomCoord c z
  have hWeights : MeasurePreserving weights P (environmentLaw μ) := ⟨hWeightsMeas, hMarginal⟩
  have hWeightShape := hWeights.quasiMeasurePreserving.ae hshape
  have hTriangle := ae_uniform_recovering_cocycle_triangle_shape_of_action
    μ hmoment' P T weights hWeightsMeas hMarginal hzero hadd hShift B hB hInt hRec
  have hMajor := ae_canonical_drift_majorizes_expected_shape_of_action
    μ hmoment' P T weights hWeightsMeas hMarginal hzero hadd hShift B hB hInt hRec g hg
  have haxes := quadrantSuperdifferential_axes_eq_empty_of_absolute_moment
    μ hmoment' hvariance g hg
  change ∀ᵐ s ∂P, Tendsto (fun n : ℕ =>
    (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _)
      (fun x => |B 0 x s - (u 0 s * (x.1 : ℝ) + u 1 s * (x.2 : ℝ))|) /
      (n : ℝ)) atTop (𝓝 0) at hTriangle
  have hA : ∀ᵐ s ∂P, ∃ ξ : InteriorDirection,
      -(h s) ∈ quadrantSuperdifferential g ξ.val := by
    filter_upwards [hWeightShape, hTriangle, hMajor, hB.2.2, hRec] with s hs ht hm ha hr
    have hcenter : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ d : ℕ × ℕ,
        N ≤ d.1 + d.2 →
        |B 0 ((d.1 : ℤ), (d.2 : ℤ)) s -
          (u 0 s * (d.1 : ℝ) + u 1 s * (d.2 : ℝ))| ≤
            ε * ((d.1 + d.2 : ℕ) : ℝ) := by
      intro ε hε
      have hsmall := ht.eventually (gt_mem_nhds hε)
      obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
      refine ⟨max 1 N, ?_⟩
      intro d hd
      have hn1 : 1 ≤ d.1 + d.2 := (le_max_left 1 N).trans hd
      have hnN : N ≤ d.1 + d.2 := (le_max_right 1 N).trans hd
      have hnpos : (0 : ℝ) < ((d.1 + d.2 : ℕ) : ℝ) := by exact_mod_cast hn1
      have hmem : ((d.1 : ℤ), (d.2 : ℤ)) ∈ Δ (d.1 + d.2) := by
        apply Finset.mem_insert_of_mem
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_product.mpr
          constructor
          · apply Finset.mem_Icc.mpr
            constructor <;> omega
          · apply Finset.mem_Icc.mpr
            constructor <;> omega
        · dsimp
          omega
      have hpoint := Finset.le_sup'
        (fun x : Lattice => |B 0 x s -
          (u 0 s * (x.1 : ℝ) + u 1 s * (x.2 : ℝ))|) hmem
      have hmax := (div_lt_iff₀ hnpos).mp (hN (d.1 + d.2) hnN)
      have hbound := hpoint.trans hmax.le
      simpa only [Int.cast_natCast] using hbound

    have hmajor : ∀ z : Quadrant,
        g z ≤ (-(h s)).1 * (z.1 : ℝ) + (-(h s)).2 * (z.2 : ℝ) := by
      simpa [h, u, finiteEdgeStep] using hm
    have hcenter' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ d : ℕ × ℕ,
        N ≤ d.1 + d.2 →
        |B 0 ((d.1 : ℤ), (d.2 : ℤ)) s -
          ((-(h s)).1 * (d.1 : ℝ) + (-(h s)).2 * (d.2 : ℝ))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ) := by
      simpa [h, u, finiteEdgeStep] using hcenter
    exact exists_interior_contact_of_uniform_recovery_bounds (weights s) (fun x y => B x y s)
      g (-(h s)) ha hr hcont hhom hmajor haxes hs hcenter'
  -- The literal conditional means are integrable, so the original tilt is integrable.
  have hH : Integrable h P := by
    have h1 : Integrable (fun s => -(P[B 0 (1, 0) | I] s)) P := integrable_condExp.neg
    have h2 : Integrable (fun s => -(P[B 0 (0, 1) | I] s)) P := integrable_condExp.neg
    exact h1.prodMk h2
  let X : Ω → ℝ × ℝ := fun s => -(h s)
  have hX : Integrable X P := hH.neg
  have hIntegralX : (∫ s, X s ∂P) = -hMean := by
    apply Prod.ext
    · simp only [X, integral_neg, Prod.fst_neg, hMean, fst_integral hH]
    · simp only [X, integral_neg, Prod.snd_neg, hMean, snd_integral hH]
  have hBpart : ∀ ξ : Quadrant, ξ ∈ closedUnitDirections →
      -hMean ∈ quadrantSuperdifferential g ξ →
      ∀ᵐ s ∂P, -(h s) ∈ quadrantSuperdifferential g ξ := by
    intro ξ _hξ hmean
    have hmean' : (∫ s, X s ∂P) ∈ quadrantSuperdifferential g ξ := by
      rw [hIntegralX]
      exact hmean
    exact ae_mem_quadrantSuperdifferential_of_integral_mem P g X ξ hhom hX hA hmean'
  have hCpart : ∀ ξ : Quadrant, ξ ∈ closedUnitDirections →
      -hMean ∈ Set.extremePoints ℝ (quadrantSuperdifferential g ξ) →
      ∀ᵐ s ∂P, h s = hMean := by
    intro ξ hξ hextreme
    have hmem : -hMean ∈ quadrantSuperdifferential g ξ := (mem_extremePoints.mp hextreme).1
    have hXmem : ∀ᵐ s ∂P, X s ∈ quadrantSuperdifferential g ξ := hBpart ξ hξ hmem
    obtain ⟨hclosed, hconvex⟩ := isClosed_and_convex_quadrantSuperdifferential g ξ
    have hextreme' : (∫ s, X s ∂P) ∈ Set.extremePoints ℝ (quadrantSuperdifferential g ξ) := by
      rw [hIntegralX]
      exact hextreme
    have heq := ProbabilityBasics.ae_eq_integral_of_mem_extremePoints P
      (quadrantSuperdifferential g ξ) X hclosed hconvex hX hXmem hextreme'
    filter_upwards [heq] with s hs
    have hn := congrArg Neg.neg hs
    simpa only [X, hIntegralX, neg_neg] using hn
  exact ⟨hA, hBpart, hCpart⟩

end LPP.Busemann.Proof
