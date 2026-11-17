/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.CalibratedConfinement
public import Busemann.Process.NativeCocycleAllStarts
public import Busemann.Process.NativeExtremeDriftPinning
public import Busemann.Geometry.SupportFaceContactInterval
public import Busemann.Geometry.NativeSupportGaps
public import Martin2004.Shape.ExpectedRateAllStarts
import LPP_Foundations.Analysis.AbsoluteMomentShape
import ProbabilityBasics.Probability.AbsoluteMomentLowerTail
import ProbabilityBasics.Probability.AbsoluteMomentTail
import Mathlib.Tactic

/-! # Native confinement of calibrated paths at a fixed support tilt -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal NNReal Topology

namespace LPP.Busemann

/-- GRS arXiv:1510.00860v2, Theorem 4.3: for one fixed extreme support
tilt, every calibrated path from every fixed signed start has endpoints
approaching the contact interval of that tilt. -/
theorem ae_native_calibrated_endpoints_confined
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (hnonconstant : ¬ ∃ c : ℝ, ∀ᵐ t ∂μ, t = c)
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hShift : ∀ z : Lattice, MeasurePreserving (processShift z) P P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : is_shift_covariant_cocycle P processShift B)
    (hInt : ∀ x y, Integrable (B x y) P)
    (hRec : recovers_weight_map_ae P processEnvironment B)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g)
    (η : InteriorDirection) (h : SupportTilt g)
    (hh : SupportsAt g η h.1)
    (hext : (∀ k : SupportTilt g, SupportsAt g η k.1 → h.1.1 ≤ k.1.1) ∨
      (∀ k : SupportTilt g, SupportsAt g η k.1 → k.1.1 ≤ h.1.1))
    (hMean : ∀ i : Fin 2,
      (∫ s, B 0 (finiteEdgeStep i) s ∂P) = -finiteTiltCoordinate h.1 i) :
    ∃ left right : InteriorDirection,
      left ∈ supportFace g h ∧ right ∈ supportFace g h ∧
      (∀ ζ ∈ supportFace g h, (left.1.1 : ℝ) ≤ (ζ.1.1 : ℝ)) ∧
      (∀ ζ ∈ supportFace g h, (ζ.1.1 : ℝ) ≤ (right.1.1 : ℝ)) ∧
      ∀ᵐ s ∂P, ∀ x : Lattice, ∀ d : ℕ → ℕ × ℕ,
        (∀ n, (d n).1 + (d n).2 = n) →
        ∀ p : (n : ℕ) → LPPDifferentiability.Path x (d n),
          (∀ n, ∀ k : Fin ((d n).1 + (d n).2),
            B ((p n).vertex k.castSucc) ((p n).vertex k.succ) s =
              processEnvironment s ((p n).vertex k.castSucc)) →
          ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
            (left.1.1 : ℝ) - ε < ((d n).1 : ℝ) / (n : ℝ) ∧
            ((d n).1 : ℝ) / (n : ℝ) < (right.1.1 : ℝ) + ε := by
  classical
  -- The original moment and nonconstancy give the exact one-face contact interval.
  have hGeometry := expected_rate_shape_geometry_of_absolute_moment μ g hmoment hg
  have hHom (c : ℝ≥0) (z : Quadrant) :
      g (c • z) = (c : ℝ) * g z := by
    change g (c * z.1, c * z.2) = (c : ℝ) * g z
    exact hGeometry.2.1 c z
  have hConc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a • x + b • y) := by
    intro x y a b hab
    change (a : ℝ) * g x + (b : ℝ) * g y ≤
      g (a * x.1 + b * y.1, a * x.2 + b * y.2)
    exact hGeometry.2.2 x y a b hab
  have hGaps := support_tilt_strict_axis_gaps_of_absolute_moment
    μ hmoment hnonconstant g hg h
  obtain ⟨left, right, hLeft, hRight, hLeftMin, hRightMax, hContact⟩ :=
    exists_support_face_interval_with_contact_characterization
      g hGeometry.1 hConc hHom h hGaps.1 hGaps.2
  have hQ : Continuous (fun t : ℝ =>
      ((Real.toNNReal t, Real.toNNReal (1 - t)) : Quadrant)) := by
    exact continuous_real_toNNReal.prodMk
      (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))
  have hContinuous : ContinuousOn (fun t : ℝ =>
      g (Real.toNNReal t, Real.toNNReal (1 - t))) (Set.Icc 0 1) :=
    (hGeometry.1.comp hQ).continuousOn

  -- Martin's two tails give one passage-shape event at all fixed signed starts.
  obtain ⟨momentOrder, hOrder, hMomentOrder⟩ := hmoment
  have hPositive := ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment
    μ hOrder hMomentOrder
  have hNegative := ProbabilityBasics.integrated_sqrt_lower_tail_lt_top_of_absolute_moment
    μ hOrder hMomentOrder
  have hShape := LPP.ae_normalized_passage_shape_all_starts
    μ hNegative hPositive.2 g hg
  have hProjection : MeasurePreserving processEnvironment P (environmentLaw μ) :=
    ⟨measurable_fst, hMarginal⟩
  have hProcessShape := hProjection.quasiMeasurePreserving.ae hShape

  -- Both native estimates use the same original full-action conditional means.
  let mProc : MeasurableSpace ProcessSample := inferInstance
  let I : MeasurableSpace ProcessSample :=
    ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (processShift z)
  let : MeasurableSpace ProcessSample := mProc
  let u : Fin 2 → ProcessSample → ℝ := fun i => P[B 0 (finiteEdgeStep i) | I]
  let Δ : ℕ → Finset Lattice := fun n => insert 0
    (((Finset.Icc (0 : ℤ) (n : ℤ)).product
      (Finset.Icc (0 : ℤ) (n : ℤ))).filter
        (fun v => v.1 + v.2 ≤ (n : ℤ)))
  have hTriangle := ae_uniform_recovering_cocycle_triangle_shape_all_starts
    μ ⟨momentOrder, hOrder, hMomentOrder⟩ P hMarginal hShift B hB hInt hRec
  change ∀ᵐ s ∂P, ∀ z : Lattice, Tendsto (fun n : ℕ =>
    (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _)
      (fun v => |B z (z + v) s -
        (u 0 s * (v.1 : ℝ) + u 1 s * (v.2 : ℝ))|) / (n : ℝ))
    atTop (𝓝 0) at hTriangle
  have hPinned := ae_canonical_drift_pinned_at_extreme_support
    μ ⟨momentOrder, hOrder, hMomentOrder⟩ P hMarginal hShift B hB hInt hRec
    g hg η h hh hext hMean
  change ∀ᵐ s ∂P, SupportsAt g η (-u 0 s, -u 1 s) ∧
    ∀ i : Fin 2, u i s = -finiteTiltCoordinate h.1 i at hPinned

  refine ⟨left, right, hLeft, hRight, hLeftMin, hRightMax, ?_⟩
  filter_upwards [hProcessShape, hTriangle, hPinned, hB.2.2, hRec]
    with s hs ht hp ha hr
  intro x d hlen p hcal ε hε
  let C : Lattice → Lattice → ℝ := fun a b => B a b s
  let ρ : ℕ → ℝ := fun n => ((d n).1 : ℝ) / (n : ℝ)
  have hPassage : Tendsto (fun n =>
      lastPassage (processEnvironment s) x (d n) / (n : ℝ) -
        g (Real.toNNReal (ρ n), Real.toNNReal (1 - ρ n))) atTop (𝓝 0) := by
    simpa only [ρ] using hs x d hlen
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
  -- The finite triangle supremum bounds each prescribed endpoint at every n.
  have hCenteredAbs : Tendsto (fun n : ℕ =>
      |B x (x + (((d n).1 : ℤ), ((d n).2 : ℤ))) s -
        (u 0 s * ((d n).1 : ℝ) + u 1 s * ((d n).2 : ℝ))| / (n : ℝ))
      atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun n =>
      div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) ?_ (ht x)
    filter_upwards [] with n
    have hPoint := Finset.le_sup'
      (fun v : Lattice => |B x (x + v) s -
        (u 0 s * (v.1 : ℝ) + u 1 s * (v.2 : ℝ))|)
      (hAtTriangle n)
    exact div_le_div_of_nonneg_right (by simpa only [Int.cast_natCast] using hPoint)
      (Nat.cast_nonneg n)
  have hCentered : Tendsto (fun n : ℕ =>
      (B x (x + (((d n).1 : ℤ), ((d n).2 : ℤ))) s -
        (u 0 s * ((d n).1 : ℝ) + u 1 s * ((d n).2 : ℝ))) / (n : ℝ))
      atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    change Tendsto (fun n : ℕ =>
      |(B x (x + (((d n).1 : ℤ), ((d n).2 : ℤ))) s -
        (u 0 s * ((d n).1 : ℝ) + u 1 s * ((d n).2 : ℝ))) / (n : ℝ)|)
      atTop (𝓝 0)
    convert hCenteredAbs using 1
    ext n
    rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  have huZero : u 0 s = -h.1.1 := by
    simpa only [finiteTiltCoordinate, Fin.val_zero, ite_true] using hp.2 0
  have huOne : u 1 s = -h.1.2 := by
    simpa only [finiteTiltCoordinate, Fin.val_one, one_ne_zero, ite_false] using hp.2 1
  have hEndpoint : Tendsto (fun n =>
      (C x (x + (((d n).1 : ℤ), ((d n).2 : ℤ))) +
        h.1.1 * ((d n).1 : ℝ) + h.1.2 * ((d n).2 : ℝ)) / (n : ℝ))
      atTop (𝓝 0) := by
    convert hCentered using 1
    ext n
    dsimp [C]
    rw [huZero, huOne]
    ring
  -- Calibration is handled by the finite path and contact-gap theorem.
  exact calibrated_endpoints_confined_to_contact_interval
    (processEnvironment s) C ha hr g h left right x d hlen p hcal
    hContinuous hContact hPassage hEndpoint ε hε

end LPP.Busemann
