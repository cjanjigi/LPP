/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.NativeDenseCalibratedBarriers
public import LPP_Foundations.Model.LastPassage.GeodesicSegments
public import LPP_Foundations.Frozen.Analysis.ClosedUnitDirections
public import Mathlib.Topology.ClusterPt
import Busemann.Process.NativeBoundaryDenseBarriers
import Busemann.Geometry.ArbitraryGeodesicBarrier
import Busemann.Geometry.StrictSupportFaceSeparation
import Busemann.Geometry.ExtremeEndpointContinuity
import Busemann.Geometry.AxisPrefixStabilization
import ProbabilityBasics.Probability.ContinuousImageFullEvent
import Busemann.Geometry.OrdinaryGeodesicClusterBounds
import Busemann.Geometry.OrdinaryGeodesicSupportFaceBounds
import Busemann.Geometry.BoundarySupportMeans
import LPP_Foundations.Analysis.AbsoluteMomentShape
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal NNReal Topology
namespace LPP.Busemann

/-- Every ordinary maximizing ray has its entire normalized cluster set in
one actual two-face direction interval, on one physical measurable full event.
The global extreme supports belong to the original expected-rate shape.
The axis cases use the source singleton convention, without extending interior
support tilts to the boundary. GRS arXiv:1510.00860v1, Theorem 2.1(i), printed
pages 6 and 18; accepted Strong Existence g400(a), line 1661. -/
theorem exists_full_event_ordinary_geodesics_directed_into_support_faces
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) :
    ∃ g : Quadrant → ℝ, IsExpectedRateShape μ g ∧
    ∃ hL hR : InteriorDirection → SupportTilt g,
      (∀ ξ : InteriorDirection,
        SupportsAt g ξ (hL ξ).1 ∧ SupportsAt g ξ (hR ξ).1 ∧
        ∀ h : SupportTilt g, SupportsAt g ξ h.1 →
          (hL ξ).1.1 ≤ h.1.1 ∧ h.1.1 ≤ (hR ξ).1.1) ∧
    ∃ A : Set LPPDifferentiability.Environment,
      MeasurableSet A ∧ environmentLaw μ A = 1 ∧
      ∀ ω ∈ A, ∀ u : Lattice, ∀ γ : ℕ → Lattice,
        γ 0 = u →
        (∀ n : ℕ,
          γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
            γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ))) →
        LPPDifferentiability.has_maximizing_segments ω γ →
        let v : ℕ → ℝ × ℝ := fun n =>
          (((γ n).1 : ℝ) / (n : ℝ), ((γ n).2 : ℝ) / (n : ℝ))
        ∃ ξ : Quadrant, ξ ∈ closedUnitDirections ∧
          ((ξ = ((0 : ℝ≥0), (1 : ℝ≥0)) ∧
            ∀ η : ℝ × ℝ, MapClusterPt η atTop v → η = ((0 : ℝ), (1 : ℝ))) ∨
          (ξ = ((1 : ℝ≥0), (0 : ℝ≥0)) ∧
            ∀ η : ℝ × ℝ, MapClusterPt η atTop v → η = ((1 : ℝ), (0 : ℝ))) ∨
          ∃ ξI : InteriorDirection, ξI.1 = ξ ∧
            ∀ η : ℝ × ℝ, MapClusterPt η atTop v →
              ∃ ηI : InteriorDirection,
                (((ηI.1.1 : ℝ), (ηI.1.2 : ℝ)) : ℝ × ℝ) = η ∧
                ηI ∈ supportFacesUnion g (hL ξI) (hR ξI)) := by
  classical
  have hMomentSource := hmoment
  obtain ⟨g, hg, D, hL, hR, left, right, hDense, _hDiff, hExtreme,
    hEndpoints, hGradient, _hContact, P, Bminus, Bplus, C, E,
    hNative, hBoundary, hEMeas, hESub, hEProb, _hEq, hRays⟩ :=
    exists_native_dense_calibrated_barriers_with_boundary_edge_limits
      μ hμ hMomentSource
  let : IsProbabilityMeasure P := (isProbabilityMeasure_iff).mpr hNative.1
  obtain ⟨hCont, hHom, hConc⟩ :=
    expected_rate_shape_geometry_of_absolute_moment μ g hMomentSource hg

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
        (fun k => (hExtreme (D (iE k))).1)).1 hApproachE
    have hNLimits (x : Lattice) :=
      (hBoundary s hsC x Bplus (Or.inr rfl)
        (fun k => D (iN k)) (fun k => hL (D (iN k)))
        (fun k => (hExtreme (D (iN k))).1)).2 hApproachN
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

  -- All following arguments take place at a single good process sample.
  -- The final image step will quantify over every ordinary ray at once.
  have hProcess (s : ProcessSample) (hs : s ∈ E)
      (u : Lattice) (γ : ℕ → Lattice)
      (hstart : γ 0 = u)
      (hsteps : ∀ n : ℕ,
        γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
          γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ)))
      (hsegments : LPPDifferentiability.has_maximizing_segments
        (processEnvironment s) γ) :
      let v : ℕ → ℝ × ℝ := fun n =>
        (((γ n).1 : ℝ) / (n : ℝ), ((γ n).2 : ℝ) / (n : ℝ))
      ∃ ξ : Quadrant, ξ ∈ closedUnitDirections ∧
        ((ξ = ((0 : ℝ≥0), (1 : ℝ≥0)) ∧
          ∀ η : ℝ × ℝ, MapClusterPt η atTop v → η = ((0 : ℝ), (1 : ℝ))) ∨
        (ξ = ((1 : ℝ≥0), (0 : ℝ≥0)) ∧
          ∀ η : ℝ × ℝ, MapClusterPt η atTop v → η = ((1 : ℝ), (0 : ℝ))) ∨
        ∃ ξI : InteriorDirection, ξI.1 = ξ ∧
          ∀ η : ℝ × ℝ, MapClusterPt η atTop v →
            ∃ ηI : InteriorDirection,
              (((ηI.1.1 : ℝ), (ηI.1.2 : ℝ)) : ℝ × ℝ) = η ∧
              ηI ∈ supportFacesUnion g (hL ξI) (hR ξI)) := by
    let a : ℕ → ℝ := fun n => (((γ n).1 - u.1 : ℤ) : ℝ) / (n : ℝ)
    let v : ℕ → ℝ × ℝ := fun n =>
      (((γ n).1 : ℝ) / (n : ℝ), ((γ n).2 : ℝ) / (n : ℝ))
    obtain ⟨hABounds, hBNonneg, hSupOne, hCluster⟩ :=
      ordinary_ray_normalized_cluster_bounds u γ hstart hsteps
    let b : ℝ := liminf a atTop
    have hBelow : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) a :=
      isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall fun n => (hABounds n).1)
    have hAbove : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) a :=
      isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall fun n => (hABounds n).2)
    have hb0 : 0 ≤ b := hBNonneg
    have hb1 : b ≤ 1 :=
      (liminf_le_limsup hAbove hBelow).trans hSupOne
    let ray (k : ℕ) : ℕ → Lattice :=
      rightmostCocyclePath (fun x y => Bplus (hL (D k)) x y s) u
    have hRayData (k : ℕ) :
        IsLocallyRightmostGeodesic (processEnvironment s) u (ray k) ∧
        ∃ d : ℕ → ℕ × ℕ,
          (∀ n, (d n).1 + (d n).2 = n ∧
            ray k n = u + (((d n).1 : ℤ), ((d n).2 : ℤ))) ∧
          approachesFaceInterval d (left (D k)) (right (D k)) := by
      have h := hRays s hs k true u
      change IsLocallyRightmostGeodesic (processEnvironment s) u (ray k) ∧
        (∀ j : ℕ, Bplus (hL (D k)) (ray k j) (ray k (j + 1)) s =
          processEnvironment s (ray k j)) ∧
        ∃ d : ℕ → ℕ × ℕ,
          (∀ n, (d n).1 + (d n).2 = n ∧
            ray k n = u + (((d n).1 : ℤ), ((d n).2 : ℤ))) ∧
          approachesFaceInterval d (left (D k)) (right (D k)) at h
      exact ⟨h.1, h.2.2⟩
    have hCompare (k : ℕ) (hsep : b < ((left (D k)).1.1 : ℝ)) :
        pathSoutheastLE γ (ray k) := by
      obtain ⟨hLocal, d, hEnd, hFace⟩ := hRayData k
      have hGap : ∃ᶠ n : ℕ in atTop, (γ n).1 < (ray k n).1 :=
        ordinary_ray_frequently_west_of_barrier u γ (ray k) a
          (fun _ => rfl) hABounds d hEnd (left (D k)) (right (D k)) hFace hsep
      exact pathSoutheastLE_of_frequently_lt_locallyRightmostGeodesic
        (processEnvironment s) u γ (ray k) hstart hsteps hsegments hLocal hGap
    have hCompareLimit (k : ℕ) (hsep : b < ((left (D k)).1.1 : ℝ)) :
        limsup a atTop ≤ ((right (D k)).1.1 : ℝ) := by
      obtain ⟨_hLocal, d, hEnd, hFace⟩ := hRayData k
      let ratio (n : ℕ) : ℝ := ((d n).1 : ℝ) / (n : ℝ)
      have hOrder := hCompare k hsep
      have hComp (n : ℕ) : a n ≤ ratio n := by
        by_cases hn : n = 0
        · subst n
          simp [a, ratio, hstart]
        have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hSameLevel :
            (γ 0).1 + (γ 0).2 + (n : ℤ) =
              (ray k 0).1 + (ray k 0).2 + (n : ℤ) := by
          simp [hstart, ray, rightmostCocyclePath]
        have hAt := (hOrder n n hSameLevel).1
        rw [(hEnd n).2] at hAt
        simp only [Prod.fst_add] at hAt
        have hInt : (γ n).1 - u.1 ≤ ((d n).1 : ℤ) := by omega
        apply (div_le_div_iff_of_pos_right hnReal).mpr
        exact_mod_cast hInt
      have hRatioNonneg (n : ℕ) : 0 ≤ ratio n :=
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hRatioLeOne (n : ℕ) : ratio n ≤ 1 := by
        by_cases hn : n = 0
        · subst n
          simp [ratio]
        have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        apply (div_le_iff₀ hnReal).mpr
        have hd : (d n).1 ≤ n := by have := (hEnd n).1; omega
        simpa only [one_mul] using
          (show ((d n).1 : ℝ) ≤ (n : ℝ) from by exact_mod_cast hd)
      have hRatioBounded : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) ratio :=
        isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall hRatioLeOne)
      have hLim : limsup a atTop ≤ limsup ratio atTop :=
        limsup_le_limsup (Filter.Eventually.of_forall hComp)
          hBelow.isCoboundedUnder_le hRatioBounded
      have hLen (n : ℕ) : (d n).1 + (d n).2 = n := (hEnd n).1
      have hRight : limsup ratio atTop ≤ ((right (D k)).1.1 : ℝ) := by
        simpa only [ratio, hLen] using hFace.2.2
      exact hLim.trans hRight

    -- At b=0, each stabilized north barrier bounds the ordinary ray.
    by_cases hZero : b = 0
    · have hLower (n : ℕ) : u.1 ≤ (γ n).1 := by
        induction n with
        | zero => simp only [hstart, le_refl]
        | succ n ih =>
          rcases hsteps n with h | h <;>
            simp only [h, Prod.fst_add] <;> omega
      have hFirst (n : ℕ) : (γ n).1 = u.1 := by
        obtain ⟨k, hk⟩ := (hPrefix s hs u n).exists
        have hsep : b < ((left (D (iN k))).1.1 : ℝ) := by
          rw [hZero]
          exact_mod_cast (left (D (iN k))).2.1
        have hOrder := hCompare (iN k) hsep
        have hSameLevel :
            (γ 0).1 + (γ 0).2 + (n : ℤ) =
              (ray (iN k) 0).1 + (ray (iN k) 0).2 + (n : ℤ) := by
          simp [hstart, ray, rightmostCocyclePath]
        have hAt := (hOrder n n hSameLevel).1
        have hNorth := hk n le_rfl
        change ray (iN k) n = u + ((0 : ℤ), (n : ℤ)) at hNorth
        rw [hNorth] at hAt
        have hUpper : (γ n).1 ≤ u.1 := by
          simpa only [Prod.fst_add, Prod.fst_zero, add_zero] using hAt
        exact le_antisymm hUpper (hLower n)
      have hAxis (n : ℕ) : γ n = u + ((0 : ℤ), (n : ℤ)) := by
        induction n with
        | zero => simp only [hstart, Nat.cast_zero, Prod.mk_zero_zero, add_zero]
        | succ n ih =>
          rcases hsteps n with hEast | hNorth
          · have hFirstSucc := hFirst (n + 1)
            rw [hEast, ih] at hFirstSucc
            simp only [Prod.fst_add] at hFirstSucc
            omega
          · rw [hNorth, ih]
            apply Prod.ext <;> simp [Prod.add_def, Nat.cast_succ, add_assoc]
      refine ⟨(0, 1), ?_, Or.inl ⟨rfl, ?_⟩⟩
      · change (0 : ℝ) + (1 : ℝ) = 1
        norm_num
      · intro η hη
        have hAZero : a = fun _ => 0 := by
          funext n
          simp [a, hAxis n, Prod.fst_add]
        have hc := hCluster η hη
        change liminf a atTop ≤ η.1 ∧ η.1 ≤ limsup a atTop ∧ η.1 + η.2 = 1 at hc
        rw [hAZero] at hc
        have hηFirst : η.1 = 0 := by
          have hlo : (0 : ℝ) ≤ η.1 := by simpa using hc.1
          have hhi : η.1 ≤ (0 : ℝ) := by simpa using hc.2.1
          exact le_antisymm hhi hlo
        apply Prod.ext
        · exact hηFirst
        · linarith only [hc.2.2, hηFirst]
    by_cases hOne : b = 1
    · refine ⟨(1, 0), ?_, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
      · change (1 : ℝ) + (0 : ℝ) = 1
        norm_num
      · intro η hη
        have hc := hCluster η hη
        have hηFirst : η.1 = 1 := by
          have hlo : (1 : ℝ) ≤ η.1 := by simpa only [← hOne] using hc.1
          exact le_antisymm (hc.2.1.trans hSupOne) hlo
        apply Prod.ext
        · exact hηFirst
        · linarith only [hc.2.2, hηFirst]

    -- For 0<b<1, let β have horizontal coordinate b and take its actual
    -- right face endpoint ξ. The endpoint reciprocity retains the left face.
    have hbPos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hZero)
    have hbLtOne : b < 1 := lt_of_le_of_ne hb1 hOne
    let β : InteriorDirection :=
      ⟨(Real.toNNReal b, Real.toNNReal (1 - b)),
        ⟨Real.toNNReal_pos.mpr hbPos,
          Real.toNNReal_pos.mpr (sub_pos.mpr hbLtOne), by
            rw [Real.coe_toNNReal _ hbPos.le,
              Real.coe_toNNReal _ (sub_nonneg.mpr hbLtOne.le)]
            ring⟩⟩
    have hβ : (β.1.1 : ℝ) = b := Real.coe_toNNReal _ hbPos.le
    let ξ := right β
    have hReciprocal : SupportsAt g β (hL ξ).1 :=
      support_left_at_right_endpoint_of_extreme_face
        g hHom hL hR left right hExtreme
        (fun ζ η => (hEndpoints ζ).2.2 η) β
    have hLeftBound : (left ξ).1.1 ≤ β.1.1 :=
      (((hEndpoints ξ).2.2 β).mp (Or.inl hReciprocal)).1
    obtain ⟨i, hiSide, hiConv⟩ := exists_dense_directions_from_right D hDense ξ
    have hStrictGap (n : ℕ) : b < ((left (D (i n))).1.1 : ℝ) := by
      let ζ := D (i n)
      have hFaceR : ∀ q ∈ supportFace g (hR β),
          (q.1.1 : ℝ) ≤ (ξ.1.1 : ℝ) := by
        intro q hq
        have hq' := (((hEndpoints β).2.2 q).mp (Or.inr hq)).2
        exact_mod_cast hq'
      have hGaps := support_tilt_strict_axis_gaps_of_absolute_moment
        μ hMomentSource (by
          exact (LPPStatements.notAPointMass_iff_not_ae_const μ).mp hμ) g hg (hL ζ)
      obtain ⟨θ, _hθ0, _hθ1, hβθ, hθFace⟩ :=
        exists_strict_threshold_right_of_maximal_support_face
          g hCont hConc hHom β ξ ζ (hR β) (hL ζ)
          (hExtreme β).2.1
          (fun q hq => ((hExtreme β).2.2 q hq).2)
          hFaceR (hExtreme ζ).1 (by exact_mod_cast hiSide n)
          hGaps.1 hGaps.2
      have hSingle : hL ζ = hR ζ := (hGradient (i n)).1
      have hLeftFace : left ζ ∈ supportFace g (hL ζ) := by
        have hm := (hEndpoints ζ).1
        rw [← hSingle, supportFacesUnion, Set.union_self] at hm
        exact hm
      rw [← hβ]
      exact (hβθ.trans (hθFace (left ζ) hLeftFace))
    have hOutward (n : ℕ) : limsup a atTop ≤ ((right (D (i n))).1.1 : ℝ) :=
      hCompareLimit (i n) (hStrictGap n)
    have hRightLimit := tendsto_rightEndpoint_of_tendsto_from_right
      g hCont hConc hHom hL hR left right hExtreme
      (fun ζ η => (hEndpoints ζ).2.2 η) ξ
      (fun n => D (i n)) hiConv (fun n => (hiSide n).le)
    have hRightCoord : Tendsto (fun n => ((right (D (i n))).1.1 : ℝ))
        atTop (𝓝 ((right ξ).1.1 : ℝ)) := by
      have hc : Continuous (fun ζ : InteriorDirection => (ζ.1.1 : ℝ)) := by fun_prop
      exact (hc.tendsto (right ξ)).comp hRightLimit
    have hUpper : limsup a atTop ≤ ((right ξ).1.1 : ℝ) :=
      ge_of_tendsto' hRightCoord hOutward
    refine ⟨ξ.1, ?_, Or.inr (Or.inr ⟨ξ, rfl, ?_⟩)⟩
    · change ((ξ.1.1 : ℝ) + (ξ.1.2 : ℝ) = 1)
      exact ξ.2.2.2
    · intro η hη
      have hc := hCluster η hη
      have hηLow : b ≤ η.1 := hc.1
      have hηHigh : η.1 ≤ ((right ξ).1.1 : ℝ) := hc.2.1.trans hUpper
      have hηPos : 0 < η.1 := hbPos.trans_le hηLow
      have hRightLtOne : ((right ξ).1.1 : ℝ) < 1 := by
        have hp : (0 : ℝ) < ((right ξ).1.2 : ℝ) := by exact_mod_cast (right ξ).2.2.1
        linarith only [(right ξ).2.2.2, hp]
      have hηSecondPos : 0 < η.2 := by
        linarith only [hc.2.2, hηHigh, hRightLtOne]
      let ηI : InteriorDirection :=
        ⟨(Real.toNNReal η.1, Real.toNNReal η.2),
          ⟨Real.toNNReal_pos.mpr hηPos, Real.toNNReal_pos.mpr hηSecondPos, by
            rw [Real.coe_toNNReal _ hηPos.le,
              Real.coe_toNNReal _ hηSecondPos.le]
            exact hc.2.2⟩⟩
      have hηI : (((ηI.1.1 : ℝ), (ηI.1.2 : ℝ)) : ℝ × ℝ) = η := by
        apply Prod.ext <;>
          simp only [ηI, Real.coe_toNNReal _ hηPos.le,
            Real.coe_toNNReal _ hηSecondPos.le]
      have hηCoord : (ηI.1.1 : ℝ) = η.1 := congrArg Prod.fst hηI
      refine ⟨ηI, hηI, ?_⟩
      apply ((hEndpoints ξ).2.2 ηI).mpr
      constructor
      · apply NNReal.coe_le_coe.mp
        rw [hηCoord]
        have hl : ((left ξ).1.1 : ℝ) ≤ b := by
          have hh : ((left ξ).1.1 : ℝ) ≤ (β.1.1 : ℝ) := by
            exact_mod_cast hLeftBound
          rwa [hβ] at hh
        exact hl.trans hηLow
      · apply NNReal.coe_le_coe.mp
        rw [hηCoord]
        exact hηHigh

  -- A compact-image full subset gives one measurable physical event for
  -- every signed start and ordinary maximizing ray at once.
  have hContinuous : Continuous (processEnvironment : ProcessSample →
      LPPDifferentiability.Environment) := by
    change Continuous (fun s : ProcessSample => s.1)
    exact continuous_fst
  obtain ⟨A, hAMeas, hAImage, hAFull⟩ :=
    ProbabilityBasics.exists_measurable_full_subset_image_of_continuous
      P processEnvironment hContinuous E hEMeas hEProb
  refine ⟨g, hg, hL, hR, hExtreme, A, hAMeas, ?_, ?_⟩
  · rw [← hNative.2.1]
    exact hAFull
  · intro ω hω u γ hstart hsteps hsegments
    obtain ⟨s, hs, hω⟩ := hAImage hω
    subst ω
    exact hProcess s hs u γ hstart hsteps hsegments

end LPP.Busemann
