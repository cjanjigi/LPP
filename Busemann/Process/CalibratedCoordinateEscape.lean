/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.CalibratedConfinement
public import Busemann.Process.LatticeCocycleTriangleShape
public import Busemann.Frozen.Process.RecoveringCocycleSupport
public import Busemann.Geometry.NativeSupportGaps
public import Busemann.Geometry.SupportFaceContactInterval
public import Busemann.Geometry.EndpointSequenceBounds
public import Martin2004.Shape.ExpectedRateAllStarts
public import Martin2004.Statements.ShapeFacts
public import LPP_Foundations.Analysis.AbsoluteMomentShape
import Busemann.Probability.CocycleIntegrability
import Martin2004.Frozen.Martin.Shape
import Martin2004.Shape.MartinShapeExpectedRate
import ProbabilityBasics.Probability.AbsoluteMomentLowerTail
import ProbabilityBasics.Probability.AbsoluteMomentTail
import ProbabilityBasics.Probability.NonconstantVariance
import ProbabilityBasics.Probability.SqrtTailMoments
import Mathlib.Tactic

/-! Almost-sure coordinate escape for arbitrary calibrated endpoint families. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal NNReal Topology

namespace LPP.Busemann

/-- Under the iid nonpoint-mass absolute-moment assumptions, every calibrated
finite-path family has both signed endpoint coordinates diverging. The
almost-sure event is fixed before the start, endpoints, or paths are chosen.
GRS arXiv:1510.00860v1, Theorem 4.3 and Appendix A (A.6); the random support
step is JR arXiv:1810.03580v3, Lemma 4.5(a). -/
theorem ae_calibrated_endpoints_tendsto_coordinates_of_action
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω) (weights : Ω → Environment)
    (hzero : ∀ ω, T 0 ω = ω)
    (hadd : ∀ z w ω, T (z + w) ω = T z (T w ω))
    (hShift : ∀ z, MeasurePreserving (T z) P P)
    (hWeightsMeas : Measurable weights)
    (hMarginal : P.map weights = environmentLaw μ)
    (hWeightsShift : ∀ z x ω, weights (T z ω) x = weights ω (z + x))
    (B : Lattice → Lattice → Ω → ℝ)
    (hB : is_shift_covariant_cocycle P T B)
    (hRec : recovers_weight_map_ae P weights B)
    (hInt₁ : Integrable (B 0 (1, 0)) P)
    (hInt₂ : Integrable (B 0 (0, 1)) P) :
    ∀ᵐ ω ∂P, ∀ x : Lattice, ∀ d : ℕ → ℕ × ℕ,
      (∀ n, (d n).1 + (d n).2 = n) →
      ∀ p : (n : ℕ) → LPPDifferentiability.Path x (d n),
        (∀ n, ∀ k : Fin ((d n).1 + (d n).2),
          B ((p n).vertex k.castSucc) ((p n).vertex k.succ) ω =
            weights ω ((p n).vertex k.castSucc)) →
        Tendsto (fun n => x.1 + ((d n).1 : ℤ)) atTop atTop ∧
        Tendsto (fun n => x.2 + ((d n).2 : ℤ)) atTop atTop := by
  classical
  -- The absolute moment supplies both Martin tails and the unique shape.
  let momentOrder : ℝ := Classical.choose hmoment
  have hMomentSpec := Classical.choose_spec hmoment
  have hOrder : 2 < momentOrder := by
    simpa only [momentOrder] using hMomentSpec.1
  have hMoment :
      (∫⁻ t, ENNReal.ofReal (|t| ^ momentOrder) ∂μ) < ∞ := by
    simpa only [momentOrder] using hMomentSpec.2
  have hPositive :=
    ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment
      μ hOrder hMoment
  have hNegative :=
    ProbabilityBasics.integrated_sqrt_lower_tail_lt_top_of_absolute_moment
      μ hOrder hMoment
  obtain ⟨g, hgShape, _⟩ :=
    LPPDifferentiability.exists_unique_shape_martin μ hNegative hPositive.2
  have hg : IsExpectedRateShape μ g :=
    LPPDifferentiability.Martin.martin_shape_tendsto_expected_rate
      μ hNegative hPositive.2 g hgShape

  -- Nonpoint-mass gives the positive centered variance required by JR (a).
  have hnonconstant : ¬ ∃ c : ℝ, ∀ᵐ t ∂μ, t = c :=
    (LPPStatements.notAPointMass_iff_not_ae_const μ).mp hμ
  have hSecondMoment :=
    LPPDifferentiability.sqrt_tail_integrable_sq μ hNegative hPositive.2
  have hVariance :=
    ProbabilityBasics.integral_centered_sq_pos_of_not_ae_const
      μ hSecondMoment hnonconstant

  -- Two integrable origin edges control every signed cocycle increment.
  have hInt : ∀ x y : Lattice, Integrable (B x y) P :=
    integrable_cocycle_of_integrable_origin_edges
      P T B hShift hB hInt₁ hInt₂

  -- The unique shape supplies continuity, homogeneity and concavity.
  have hGeometry := expected_rate_shape_geometry_of_absolute_moment
    μ g hmoment hg
  have hHom : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c • z) = (c : ℝ) * g z := by
    intro c z
    change g (c * z.1, c * z.2) = (c : ℝ) * g z
    exact hGeometry.2.1 c z
  have hConc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a • x + b • y) := by
    intro x y a b hab
    change (a : ℝ) * g x + (b : ℝ) * g y ≤
      g (a * x.1 + b * y.1, a * x.2 + b * y.2)
    exact hGeometry.2.2 x y a b hab

  -- Use conditional edge means on the original full-action invariant sigma algebra.
  let mΩ0 : MeasurableSpace Ω := inferInstance
  let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
  let : MeasurableSpace Ω := mΩ0
  have hI : I ≤ mΩ0 :=
    (iInf_le (fun z : Lattice => @MeasurableSpace.invariants Ω mΩ0 (T z))
      (0 : Lattice)).trans (MeasurableSpace.invariants_le (T 0))
  let : IsFiniteMeasure (P.trim hI) := inferInstance
  let : SigmaFinite (P.trim hI) := inferInstance
  let u : Fin 2 → Ω → ℝ := fun i => P[B 0 (finiteEdgeStep i) | I]
  let Δ : ℕ → Finset Lattice := fun n => insert 0
    (((Finset.Icc (0 : ℤ) (n : ℤ)).product
      (Finset.Icc (0 : ℤ) (n : ℤ))).filter
        (fun v => v.1 + v.2 ≤ (n : ℤ)))

  -- The action triangle estimate controls all origin increments at once.
  have hTriangleRaw := ae_uniform_recovering_cocycle_triangle_shape_of_action
    μ hmoment P T weights hWeightsMeas hMarginal hzero hadd hShift B hB hInt hRec
  change ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
    (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _)
      (fun v => |B 0 v ω -
        (u 0 ω * (v.1 : ℝ) + u 1 ω * (v.2 : ℝ))|) / (n : ℝ))
      atTop (𝓝 0) at hTriangleRaw
  have hTriangle := hTriangleRaw

  -- JR (a) gives support for the random conditional drift, not its mean.
  have hJR :=
    recovering_cocycle_support_and_invariant_tilt Ω P μ T weights B g
      hzero (fun z w ω => (hadd z w ω).symm) hShift hWeightsMeas hMarginal hWeightsShift
      hmoment hVariance hg hB hRec hInt₁ hInt₂
  have hSupport : ∀ᵐ ω ∂P, ∃ ξ : InteriorDirection,
      (u 0 ω, u 1 ω) ∈ quadrantSuperdifferential g ξ.1 := by
    filter_upwards [hJR.1] with ω hω
    obtain ⟨ξ, hξ⟩ := hω
    refine ⟨ξ, ?_⟩
    have hpair :
        -(-P[B 0 (1, 0) | latticeInvariantSigma T] ω,
          -P[B 0 (0, 1) | latticeInvariantSigma T] ω) =
          (P[B 0 (1, 0) | latticeInvariantSigma T] ω,
            P[B 0 (0, 1) | latticeInvariantSigma T] ω) := by
      ext <;> simp
    rw [hpair] at hξ
    change (P[B 0 (1, 0) | I] ω, P[B 0 (0, 1) | I] ω) ∈
      quadrantSuperdifferential g ξ.1
    exact hξ

  -- The all-start passage-shape event transfers through the weight factor.
  have hShapeEnv := LPP.ae_normalized_passage_shape_all_starts
    μ hNegative hPositive.2 g hg
  have hWeightPreserving : MeasurePreserving weights P (environmentLaw μ) :=
    ⟨hWeightsMeas, hMarginal⟩
  have hShape := hWeightPreserving.quasiMeasurePreserving.ae hShapeEnv

  -- Pull both origin estimates back to every signed start before choosing paths.
  have hTriangleAll : ∀ᵐ ω ∂P, ∀ x : Lattice,
      Tendsto (fun n : ℕ =>
        (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _)
          (fun v => |B 0 v (T x ω) -
            (u 0 (T x ω) * (v.1 : ℝ) + u 1 (T x ω) * (v.2 : ℝ))|) /
            (n : ℝ)) atTop (𝓝 0) := by
    apply ae_all_iff.mpr
    intro x
    exact (hShift x).quasiMeasurePreserving.ae hTriangle
  have hSupportAll : ∀ᵐ ω ∂P, ∀ x : Lattice,
      ∃ ξ : InteriorDirection,
        (u 0 (T x ω), u 1 (T x ω)) ∈ quadrantSuperdifferential g ξ.1 := by
    apply ae_all_iff.mpr
    intro x
    exact (hShift x).quasiMeasurePreserving.ae hSupport
  have hCov : ∀ᵐ ω ∂P, ∀ x v : Lattice,
      B x (x + v) ω = B 0 v (T x ω) := by
    apply ae_all_iff.mpr
    intro x
    apply ae_all_iff.mpr
    intro v
    simpa only [zero_add, add_comm v x] using hB.2.1 0 v x

  -- One common sample event precedes all starts and all path families.
  filter_upwards [hShape, hTriangleAll, hSupportAll, hCov, hB.2.2, hRec]
    with ω hShapeω hTriangleω hSupportω hCovω hAddω hRecoverω
  intro x d hlen p hcal

  -- At this start the conditional drift gives a local interior support tilt.
  obtain ⟨ξ, hξ⟩ := hSupportω x
  have hSupportAt :
      SupportsAt g ξ (-u 0 (T x ω), -u 1 (T x ω)) := by
    change ∀ z : Quadrant,
      -(-u 0 (T x ω)) * ((ξ.1.1 : ℝ) - (z.1 : ℝ)) +
        -(-u 1 (T x ω)) * ((ξ.1.2 : ℝ) - (z.2 : ℝ)) ≤ g ξ.1 - g z
    intro z
    simpa only [neg_neg] using hξ z
  let hLocal : SupportTilt g :=
    ⟨(-u 0 (T x ω), -u 1 (T x ω)), ⟨ξ, hSupportAt⟩⟩
  have hGaps := support_tilt_strict_axis_gaps_of_absolute_moment
    μ hmoment hnonconstant g hg hLocal
  obtain ⟨left, right, hLeft, hRight, hLeftMin, hRightMax, hContact⟩ :=
    exists_support_face_interval_with_contact_characterization
      g hGeometry.1 hConc hHom hLocal hGaps.1 hGaps.2
  have hQ : Continuous (fun t : ℝ =>
      ((Real.toNNReal t, Real.toNNReal (1 - t)) : Quadrant)) := by
    exact continuous_real_toNNReal.prodMk
      (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))
  have hContinuous : ContinuousOn (fun t : ℝ =>
      g (Real.toNNReal t, Real.toNNReal (1 - t))) (Set.Icc 0 1) :=
    (hGeometry.1.comp hQ).continuousOn

  -- The shape event supplies passage convergence from this signed start.
  let ρ : ℕ → ℝ := fun n => ((d n).1 : ℝ) / (n : ℝ)
  have hPassage : Tendsto (fun n =>
      lastPassage (weights ω) x (d n) / (n : ℝ) -
        g (Real.toNNReal (ρ n), Real.toNNReal (1 - ρ n))) atTop (𝓝 0) := by
    simpa only [ρ] using hShapeω x d hlen

  -- Each prescribed endpoint lies in the origin triangle at its length.
  have hAtTriangle (n : ℕ) :
      (((d n).1 : ℤ), ((d n).2 : ℤ)) ∈ Δ n := by
    have hlength := hlen n
    have hfirst : (d n).1 ≤ n := by omega
    have hsecond : (d n).2 ≤ n := by omega
    apply Finset.mem_insert_of_mem
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        constructor
        · change (0 : ℤ) ≤ ((d n).1 : ℤ)
          exact_mod_cast Nat.zero_le (d n).1
        · change ((d n).1 : ℤ) ≤ (n : ℤ)
          exact_mod_cast hfirst
      · apply Finset.mem_Icc.mpr
        constructor
        · change (0 : ℤ) ≤ ((d n).2 : ℤ)
          exact_mod_cast Nat.zero_le (d n).2
        · change ((d n).2 : ℤ) ≤ (n : ℤ)
          exact_mod_cast hsecond
    · dsimp
      exact_mod_cast (le_of_eq (hlen n))

  -- Covariance and the triangle bound control the centered endpoint increment.
  have hCenteredAbs : Tendsto (fun n : ℕ =>
      |B x (x + (((d n).1 : ℤ), ((d n).2 : ℤ))) ω -
        (u 0 (T x ω) * ((d n).1 : ℝ) +
          u 1 (T x ω) * ((d n).2 : ℝ))| / (n : ℝ))
      atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun n =>
      div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) ?_ (hTriangleω x)
    filter_upwards [] with n
    have hPoint := Finset.le_sup'
      (fun v : Lattice => |B 0 v (T x ω) -
        (u 0 (T x ω) * (v.1 : ℝ) + u 1 (T x ω) * (v.2 : ℝ))|)
      (hAtTriangle n)
    have hCovPoint := hCovω x
      (((d n).1 : ℤ), ((d n).2 : ℤ))
    have hEndpointPoint :
        |B x (x + (((d n).1 : ℤ), ((d n).2 : ℤ))) ω -
          (u 0 (T x ω) * ((d n).1 : ℝ) +
            u 1 (T x ω) * ((d n).2 : ℝ))| ≤
          (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _)
            (fun v : Lattice => |B 0 v (T x ω) -
              (u 0 (T x ω) * (v.1 : ℝ) + u 1 (T x ω) * (v.2 : ℝ))|) := by
      rw [hCovPoint]
      exact hPoint
    exact div_le_div_of_nonneg_right hEndpointPoint (Nat.cast_nonneg n)

  have hCentered : Tendsto (fun n : ℕ =>
      (B x (x + (((d n).1 : ℤ), ((d n).2 : ℤ))) ω -
        (u 0 (T x ω) * ((d n).1 : ℝ) +
          u 1 (T x ω) * ((d n).2 : ℝ))) / (n : ℝ))
      atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    change Tendsto (fun n : ℕ =>
      |(B x (x + (((d n).1 : ℤ), ((d n).2 : ℤ))) ω -
        (u 0 (T x ω) * ((d n).1 : ℝ) +
          u 1 (T x ω) * ((d n).2 : ℝ))) / (n : ℝ)|)
      atTop (𝓝 0)
    convert hCenteredAbs using 1
    ext n
    rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]

  -- The local tilt is the negative of the conditional mean pair.
  have hEndpoint : Tendsto (fun n =>
      (B x (x + (((d n).1 : ℤ), ((d n).2 : ℤ))) ω +
        hLocal.1.1 * ((d n).1 : ℝ) +
        hLocal.1.2 * ((d n).2 : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
    convert hCentered using 1
    ext n
    simp only [hLocal]
    ring

  -- Calibrated confinement gives two-sided contact-interval bands.
  have hBands := calibrated_endpoints_confined_to_contact_interval
    (weights ω) (fun a b => B a b ω) hAddω hRecoverω g hLocal left right x d hlen p hcal
    hContinuous hContact hPassage hEndpoint

  -- The bands force the limiting endpoint ratio into the contact interval.
  let ρLevel : ℕ → ℝ := fun n =>
    ((d n).1 : ℝ) / (((d n).1 + (d n).2 : ℕ) : ℝ)
  have hRatioBounds (n : ℕ) : 0 ≤ ρLevel n ∧ ρLevel n ≤ 1 := by
    by_cases hn : n = 0
    · have hd : d 0 = (0, 0) := by
        have hzero_len := hlen 0
        apply Prod.ext <;> omega
      simp [ρLevel, hd, hn]
    · have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hlen_n := hlen n
      have hfirst : (d n).1 ≤ n := by omega
      dsimp [ρLevel]
      rw [hlen_n]
      constructor
      · exact div_nonneg (Nat.cast_nonneg _) hnpos.le
      · rw [div_le_iff₀ hnpos]
        have hfirstR : ((d n).1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hfirst
        simpa only [one_mul] using hfirstR
  have hBoundedLower :
      (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) ρLevel :=
    isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall fun n => (hRatioBounds n).1)
  have hBoundedUpper :
      (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) ρLevel :=
    isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall fun n => (hRatioBounds n).2)
  have hRatioLeft : (left.1.1 : ℝ) ≤ liminf ρLevel atTop := by
    rw [Filter.le_liminf_iff hBoundedUpper.isCoboundedUnder_ge hBoundedLower]
    intro t ht
    have hε : 0 < (left.1.1 : ℝ) - t := sub_pos.mpr ht
    filter_upwards [hBands ((left.1.1 : ℝ) - t) hε] with n hn
    have hρ : ρLevel n = ((d n).1 : ℝ) / (n : ℝ) := by
      dsimp [ρLevel]
      rw [hlen n]
    rw [hρ]
    linarith [hn.1]
  have hRatioRight : limsup ρLevel atTop ≤ (right.1.1 : ℝ) := by
    rw [Filter.limsup_le_iff hBoundedLower.isCoboundedUnder_le hBoundedUpper]
    intro t ht
    have hε : 0 < t - (right.1.1 : ℝ) := sub_pos.mpr ht
    filter_upwards [hBands (t - (right.1.1 : ℝ)) hε] with n hn
    have hρ : ρLevel n = ((d n).1 : ℝ) / (n : ℝ) := by
      dsimp [ρLevel]
      rw [hlen n]
    rw [hρ]
    linarith [hn.2]
  have hApproaches : approachesFaceInterval d left right := by
    refine ⟨?_, hRatioLeft, hRatioRight⟩
    simpa only [hlen, Function.id_def] using (tendsto_id : Tendsto id atTop atTop)

  -- The interval is interior, so both natural coordinates and their signed translates diverge.
  have hCoordinates := approachesFaceInterval_tendsto_coordinates d left right hApproaches
  have hFirstInt : Tendsto (fun n => ((d n).1 : ℤ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hCoordinates.1
  have hSecondInt : Tendsto (fun n => ((d n).2 : ℤ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hCoordinates.2
  exact ⟨tendsto_atTop_add_const_left atTop x.1 hFirstInt,
    tendsto_atTop_add_const_left atTop x.2 hSecondInt⟩

end LPP.Busemann
