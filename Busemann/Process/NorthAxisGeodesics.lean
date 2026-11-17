/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.ArbitraryGeodesicBarrier
public import LPP_Foundations.Model.LastPassage.GeodesicSegments
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Statements.ShapeDefinitions
public import Mathlib.Topology.Instances.Real.Lemmas
import Busemann.Process.NativeBoundaryDenseBarriers
import Busemann.Geometry.AxisPrefixStabilization
import ProbabilityBasics.Probability.ContinuousImageFullEvent
import Busemann.Geometry.BoundarySupportMeans
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology
namespace LPP.Busemann

/-! A fixed calibrated barrier has a positive horizontal speed in the
liminf sense. An ordinary north-directed ray eventually lies strictly to
its west. This is the geometric input for the arbitrary-ray comparison. -/
private theorem frequently_west_of_calibrated_barrier
    (u : Lattice) (γ ρ : ℕ → Lattice)
    (hγdir : Tendsto (fun n : ℕ => ((γ n).1 : ℝ) / (n : ℝ)) atTop (𝓝 0))
    (d : ℕ → ℕ × ℕ)
    (hEnd : ∀ n : ℕ,
      (d n).1 + (d n).2 = n ∧
      ρ n = u + (((d n).1 : ℤ), ((d n).2 : ℤ)))
    (left right : InteriorDirection)
    (hFace : approachesFaceInterval d left right) :
    ∃ᶠ n : ℕ in atTop, (γ n).1 < (ρ n).1 := by
  let ratio (n : ℕ) : ℝ := ((d n).1 : ℝ) / (n : ℝ)
  have hLen (n : ℕ) : (d n).1 + (d n).2 = n := (hEnd n).1
  have hNonneg (n : ℕ) : 0 ≤ ratio n := by
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hBounded : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) ratio :=
    isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hNonneg)
  have hLiminf : (left.1.1 : ℝ) ≤ liminf ratio atTop := by
    simpa only [approachesFaceInterval, hLen, ratio] using hFace.2.1
  have hPositive : (0 : ℝ) < (left.1.1 : ℝ) := by
    exact_mod_cast left.2.1
  have hQuarter : (0 : ℝ) < (left.1.1 : ℝ) / 4 := by linarith only [hPositive]
  have hHalf : (left.1.1 : ℝ) / 2 < liminf ratio atTop := by
    linarith only [hPositive, hLiminf]
  have hBarrier : ∀ᶠ n : ℕ in atTop,
      (left.1.1 : ℝ) / 2 < ratio n :=
    eventually_lt_of_lt_liminf hHalf hBounded
  have hRay : ∀ᶠ n : ℕ in atTop,
      ((γ n).1 : ℝ) / (n : ℝ) < (left.1.1 : ℝ) / 4 :=
    Filter.Tendsto.eventually_lt_const hQuarter hγdir
  have hRootLimit : Tendsto (fun n : ℕ => (u.1 : ℝ) / (n : ℝ))
      atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat (u.1 : ℝ)
  have hRoot : ∀ᶠ n : ℕ in atTop,
      -((left.1.1 : ℝ) / 4) < (u.1 : ℝ) / (n : ℝ) :=
    hRootLimit.eventually (Ioi_mem_nhds (by linarith only [hQuarter]))
  have hGap : ∀ᶠ n : ℕ in atTop, (γ n).1 < (ρ n).1 := by
    filter_upwards [hBarrier, hRay, hRoot, eventually_gt_atTop (0 : ℕ)]
      with n hB hG hU hn
    have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hRhoFirst : ((ρ n).1 : ℝ) = (u.1 : ℝ) + ((d n).1 : ℝ) := by
      rw [(hEnd n).2]
      simp only [Prod.fst_add, Int.cast_add, Int.cast_natCast]
    have hDiv : ((γ n).1 : ℝ) / (n : ℝ) < ((ρ n).1 : ℝ) / (n : ℝ) := by
      rw [hRhoFirst, add_div]
      dsimp only [ratio] at hB
      linarith only [hB, hG, hU]
    have hReal : ((γ n).1 : ℝ) < ((ρ n).1 : ℝ) :=
      (div_lt_div_iff_of_pos_right hnReal).mp hDiv
    exact_mod_cast hReal
  exact hGap.frequently

/-- Under the original real iid law, every ordinary maximizing north-directed
ray from every signed root is the canonical north axis on one measurable full
environment event. Direction means that the absolute first coordinate divided
by local time tends to zero. JSP (2025), Lemma 5.1, reflected north-axis
argument; GRS arXiv:1510.00860v1, Lemma 5.1; accepted Strong Existence,
g400(b), line 1662. This statement makes no east-axis claim. -/
theorem exists_full_event_north_directed_geodesic_eq_axis
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) :
    ∃ A : Set LPPDifferentiability.Environment,
      MeasurableSet A ∧ environmentLaw μ A = 1 ∧
      ∀ ω ∈ A, ∀ u : Lattice, ∀ γ : ℕ → Lattice,
        γ 0 = u →
        (∀ n : ℕ,
          γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
            γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ))) →
          LPPDifferentiability.has_maximizing_segments ω γ →
        Tendsto (fun n : ℕ => ((γ n).1 : ℝ) / (n : ℝ)) atTop (𝓝 0) →
        ∀ n : ℕ, γ n = u + ((0 : ℤ), (n : ℤ)) := by
  classical
  have hMomentSource := hmoment
  obtain ⟨g, hg, D, hL, hR, left, right, hDense, _hDiff, hExt,
    _hEndpoints, _hGrad, _hContact, P, Bminus, Bplus, C, E,
    hNative, hBoundary, hEMeas, hESub, hEProb, _hEq, hRays⟩ :=
    exists_native_dense_calibrated_barriers_with_boundary_edge_limits
      μ hμ hMomentSource
  let : IsProbabilityMeasure P := (isProbabilityMeasure_iff).mpr hNative.1

  -- Dense calibrated directions approach both axes, as the boundary theorem requires.
  obtain ⟨ξE, ξN, _kE, _kN, _hMonoE, _hAntiN, _hSupport,
    hξE, hξN, _hMeanE, _hMeanN⟩ :=
    exists_ordered_boundary_contacts μ hMomentSource g hg
  let radius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hRadiusPos (n : ℕ) : 0 < radius n := by
    dsimp only [radius]
    positivity
  have hRadiusZero : Tendsto radius atTop (𝓝 0) := by
    simpa only [radius] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose iE hiE using fun n => hDense.exists_dist_lt (ξE n) (hRadiusPos n)
  choose iN hiN using fun n => hDense.exists_dist_lt (ξN n) (hRadiusPos n)
  have hNearE : Tendsto
      (fun n => dist ((ξE n).1) ((D (iE n)).1)) atTop (𝓝 0) := by
    have h := squeeze_zero
      (fun n => (dist_nonneg : 0 ≤ dist (ξE n) (D (iE n))))
      (fun n => (hiE n).le) hRadiusZero
    simpa only [Subtype.dist_eq] using h
  have hNearN : Tendsto
      (fun n => dist ((ξN n).1) ((D (iN n)).1)) atTop (𝓝 0) := by
    have h := squeeze_zero
      (fun n => (dist_nonneg : 0 ≤ dist (ξN n) (D (iN n))))
      (fun n => (hiN n).le) hRadiusZero
    simpa only [Subtype.dist_eq] using h
  have hApproachE : Tendsto (fun n => (D (iE n)).1)
      atTop (𝓝 ((1, 0) : Quadrant)) := hξE.congr_dist hNearE
  have hApproachN : Tendsto (fun n => (D (iN n)).1)
      atTop (𝓝 ((0, 1) : Quadrant)) := hξN.congr_dist hNearN

  -- Boundary limits make the actual plus-cocycle rays stabilize on finite
  -- prefixes. Both axis approaches are passed to the bundled theorem.
  have hPrefix (s : ProcessSample) (hs : s ∈ E) (u : Lattice) :
      ∀ M : ℕ, ∀ᶠ k : ℕ in atTop, ∀ j : ℕ, j ≤ M →
        rightmostCocyclePath
          (fun a b => Bplus (hL (D (iN k))) a b s) u j =
          u + ((0 : ℤ), (j : ℤ)) := by
    let Be (k : ℕ) (a b : Lattice) : ℝ := Bplus (hL (D (iE k))) a b s
    let Bn (k : ℕ) (a b : Lattice) : ℝ := Bplus (hL (D (iN k))) a b s
    have hsC : s ∈ C := hESub hs
    have hELimits (x : Lattice) :=
      (hBoundary s hsC x Bplus (Or.inr rfl)
        (fun k => D (iE k)) (fun k => hL (D (iE k)))
        (fun k => (hExt (D (iE k))).1)).1 hApproachE
    have hNLimits (x : Lattice) :=
      (hBoundary s hsC x Bplus (Or.inr rfl)
        (fun k => D (iN k)) (fun k => hL (D (iN k)))
        (fun k => (hExt (D (iN k))).1)).2 hApproachN
    have hEastFinite (j : ℕ) : ∃ a : ℝ,
        Tendsto (fun k => Be k (u + ((j : ℤ), (0 : ℤ)))
          (u + ((j : ℤ), (0 : ℤ)) + ((1 : ℤ), (0 : ℤ)))) atTop (𝓝 a) := by
      exact ⟨(processEnvironment s) (u + ((j : ℤ), (0 : ℤ))),
        (hELimits (u + ((j : ℤ), (0 : ℤ)))).1⟩
    have hEastTransverse (j : ℕ) :
        Tendsto (fun k => Be k (u + ((j : ℤ), (0 : ℤ)))
          (u + ((j : ℤ), (0 : ℤ)) + ((0 : ℤ), (1 : ℤ)))) atTop atTop :=
      (hELimits (u + ((j : ℤ), (0 : ℤ)))).2
    have hNorthFinite (j : ℕ) : ∃ a : ℝ,
        Tendsto (fun k => Bn k (u + ((0 : ℤ), (j : ℤ)))
          (u + ((0 : ℤ), (j : ℤ)) + ((0 : ℤ), (1 : ℤ)))) atTop (𝓝 a) := by
      exact ⟨(processEnvironment s) (u + ((0 : ℤ), (j : ℤ))),
        (hNLimits (u + ((0 : ℤ), (j : ℤ)))).1⟩
    have hNorthTransverse (j : ℕ) :
        Tendsto (fun k => Bn k (u + ((0 : ℤ), (j : ℤ)))
          (u + ((0 : ℤ), (j : ℤ)) + ((1 : ℤ), (0 : ℤ)))) atTop atTop :=
      (hNLimits (u + ((0 : ℤ), (j : ℤ)))).2
    exact (rightmostCocyclePath_axis_prefix_stabilizes
      u Be Bn hEastFinite hEastTransverse hNorthFinite hNorthTransverse).2

  -- Every ordinary north-directed maximizing ray is bounded by each
  -- same-root calibrated barrier and then by a stabilized axis prefix.
  have hProcess (s : ProcessSample) (hs : s ∈ E)
      (u : Lattice) (γ : ℕ → Lattice)
      (hstart : γ 0 = u)
      (hsteps : ∀ n : ℕ,
        γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
          γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ)))
      (hsegments : LPPDifferentiability.has_maximizing_segments
        (processEnvironment s) γ)
      (hdir : Tendsto (fun n : ℕ => ((γ n).1 : ℝ) / (n : ℝ)) atTop (𝓝 0)) :
      ∀ n : ℕ, γ n = u + ((0 : ℤ), (n : ℤ)) := by
    have hLower (n : ℕ) : u.1 ≤ (γ n).1 := by
      induction n with
      | zero => simp only [hstart, le_refl]
      | succ n ih =>
        rcases hsteps n with h | h <;>
          simp only [h, Prod.fst_add] <;> omega
    have hFirst (n : ℕ) : (γ n).1 = u.1 := by
      obtain ⟨k, hk⟩ := (hPrefix s hs u n).exists
      let ρ : ℕ → Lattice :=
        rightmostCocyclePath (fun a b => Bplus (hL (D (iN k))) a b s) u
      have hRay := hRays s hs (iN k) true u
      change IsLocallyRightmostGeodesic (processEnvironment s) u ρ ∧
        (∀ j : ℕ, Bplus (hL (D (iN k))) (ρ j) (ρ (j + 1)) s =
          processEnvironment s (ρ j)) ∧
        ∃ d : ℕ → ℕ × ℕ,
          (∀ j : ℕ, (d j).1 + (d j).2 = j ∧
            ρ j = u + (((d j).1 : ℤ), ((d j).2 : ℤ))) ∧
          approachesFaceInterval d (left (D (iN k))) (right (D (iN k))) at hRay
      obtain ⟨hLocal, _hCal, d, hEnd, hFace⟩ := hRay
      have hGap : ∃ᶠ j : ℕ in atTop, (γ j).1 < (ρ j).1 :=
        frequently_west_of_calibrated_barrier u γ ρ hdir d hEnd
          (left (D (iN k))) (right (D (iN k))) hFace
      have hOrder : pathSoutheastLE γ ρ :=
        pathSoutheastLE_of_frequently_lt_locallyRightmostGeodesic
          (processEnvironment s) u γ ρ hstart hsteps hsegments hLocal hGap
      have hSameLevel :
          (γ 0).1 + (γ 0).2 + (n : ℤ) =
            (ρ 0).1 + (ρ 0).2 + (n : ℤ) := by
        simp [hstart, ρ, rightmostCocyclePath]
      have hUpper : (γ n).1 ≤ u.1 := by
        have hAt := (hOrder n n hSameLevel).1
        have hNorth := hk n le_rfl
        change ρ n = u + ((0 : ℤ), (n : ℤ)) at hNorth
        rw [hNorth] at hAt
        simpa only [Prod.fst_add, Prod.fst_zero, add_zero] using hAt
      exact le_antisymm hUpper (hLower n)
    intro n
    induction n with
    | zero => simp only [hstart, Nat.cast_zero, Prod.mk_zero_zero, add_zero]
    | succ n ih =>
      rcases hsteps n with hEast | hNorth
      · have hFirstSucc := hFirst (n + 1)
        rw [hEast, ih] at hFirstSucc
        simp only [Prod.fst_add] at hFirstSucc
        omega
      · rw [hNorth, ih]
        apply Prod.ext <;>
          simp [Prod.add_def, Nat.cast_succ, add_assoc]

  -- A measurable full subset of the continuous environment image supplies
  -- one good process lift for every environment, before any ray quantifier.
  have hContinuous : Continuous (processEnvironment : ProcessSample →
      LPPDifferentiability.Environment) := by
    change Continuous (fun s : ProcessSample => s.1)
    exact continuous_fst
  obtain ⟨A, hAMeas, hAImage, hAFull⟩ :=
    ProbabilityBasics.exists_measurable_full_subset_image_of_continuous
      P processEnvironment hContinuous E hEMeas hEProb
  refine ⟨A, hAMeas, ?_, ?_⟩
  · rw [← hNative.2.1]
    exact hAFull
  · intro ω hω u γ hstart hsteps hsegments hdir
    obtain ⟨s, hs, hω⟩ := hAImage hω
    subst ω
    exact hProcess s hs u γ hstart hsteps hsegments hdir

end LPP.Busemann
