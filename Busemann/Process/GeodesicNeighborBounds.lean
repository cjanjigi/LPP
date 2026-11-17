/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Model.LastPassage.Basic
public import LPP_Foundations.Model.LastPassage.GeodesicSegments
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Statements.ShapeDefinitions
public import Mathlib.Topology.Instances.Real.Lemmas
import Busemann.Process.OrdinaryGeodesicDirectedness
import Busemann.Process.AxisGeodesics
import Busemann.Process.NativeBoundaryDenseBarriers
import Busemann.Geometry.EnvironmentUniformPassageBounds
import Busemann.Geometry.StrictSupportFaceSeparation
import Busemann.Geometry.SupportOrder
import Busemann.Geometry.GeodesicCocycleConfinement
import Busemann.Geometry.GeodesicCocycleFiniteness
import Busemann.Geometry.OrdinaryGeodesicInterior
import Busemann.Geometry.NativeShapeIdentification
import Busemann.Process.RightmostPaths
import LPP_Foundations.Analysis.AbsoluteMomentShape
import LPP_Foundations.Model.LastPassage.GradientOrder
import ProbabilityBasics.Probability.ContinuousImageFullEvent
import Martin2004.Shape.ExpectedRateShape
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal NNReal Topology
namespace LPP.Busemann

/-- On one original-law physical full event, every ordinary ray escaping in
both coordinates has finite upper bounds for both neighboring-start passage
increments, at every signed site and along one common valid tail. This is
the barrier comparison used in Strong Existence g602/g609/g619, lines
1659–1693. It asserts no real-limit field, additivity, recovery or calibration. -/
theorem exists_full_event_geodesic_neighbor_increment_upper_bounds
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
        Tendsto (fun n : ℕ => (γ n).1) atTop atTop →
        Tendsto (fun n : ℕ => (γ n).2) atTop atTop →
        ∀ x : Lattice, ∃ (N : ℕ) (K : ℝ),
          x ≤ γ N ∧
          x + ((1 : ℤ), (0 : ℤ)) ≤ γ N ∧
          x + ((0 : ℤ), (1 : ℤ)) ≤ γ N ∧
          ∀ n : ℕ,
            (lastPassage ω x
                (((γ (N + n)).1 - x.1).toNat, ((γ (N + n)).2 - x.2).toNat) -
              lastPassage ω (x + ((1 : ℤ), (0 : ℤ)))
                (((γ (N + n)).1 - (x + ((1 : ℤ), (0 : ℤ))).1).toNat,
                 ((γ (N + n)).2 - (x + ((1 : ℤ), (0 : ℤ))).2).toNat) ≤ K) ∧
            (lastPassage ω x
                (((γ (N + n)).1 - x.1).toNat, ((γ (N + n)).2 - x.2).toNat) -
              lastPassage ω (x + ((0 : ℤ), (1 : ℤ)))
                (((γ (N + n)).1 - (x + ((0 : ℤ), (1 : ℤ))).1).toNat,
                 ((γ (N + n)).2 - (x + ((0 : ℤ), (1 : ℤ))).2).toNat) ≤ K) := by
  classical
  have hMomentSource := hmoment
  obtain ⟨gOrd, hgOrd, hLOrd, hROrd, hExtremeOrd,
    AOrd, hAOrdMeas, hAOrdFull, hOrd⟩ :=
    exists_full_event_ordinary_geodesics_directed_into_support_faces
      μ hμ hMomentSource
  obtain ⟨AAxis, hAAxisMeas, hAAxisFull, hAxis⟩ :=
    exists_full_event_axis_directed_geodesic_eq_axis μ hμ hMomentSource
  obtain ⟨ANeighbor, hANeighborMeas, hANeighborFull,
    _hNeighborShift, hUniform⟩ :=
    exists_full_environment_event_uniform_interior_neighbor_bounds
      μ hμ hMomentSource
  obtain ⟨g, hg, D, hL, hR, left, right, hDense, _hDiff,
    hExtreme, hEndpoints, hGradient, _hContact,
    P, Bminus, Bplus, C, E, hNative, _hBoundary,
    hEMeas, hESub, hEFull, _hEq, hRays⟩ :=
    exists_native_dense_calibrated_barriers_with_boundary_edge_limits
      μ hμ hMomentSource
  have hShape : gOrd = g :=
    isExpectedRateShape_unique μ hgOrd hg
  subst gOrd
  have hGeometry := expected_rate_shape_geometry_of_absolute_moment μ g hMomentSource hg
  have hHom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z :=
    hGeometry.2.1
  obtain ⟨hLIdent, hRIdent⟩ :=
    extreme_support_selectors_eq g hHom hLOrd hROrd hL hR
      hExtremeOrd hExtreme
  have hNonconstant : ¬ ∃ c : ℝ, ∀ᵐ t ∂μ, t = c := by
    rintro ⟨c, hc⟩
    exact (ne_of_lt (hμ c))
      ((mem_ae_iff_prob_eq_one (measurableSet_singleton c)).mp hc)
  have hGaps (n : ℕ) :
      g (1, 0) < -(hL (D n)).1.1 ∧
      g (0, 1) < -(hL (D n)).1.2 :=
    support_tilt_strict_axis_gaps_of_absolute_moment
      μ hMomentSource hNonconstant g hg (hL (D n))
  let : IsProbabilityMeasure P := (isProbabilityMeasure_iff).mpr hNative.1
  let APhysical : Set LPPDifferentiability.Environment :=
    AOrd ∩ AAxis ∩ ANeighbor
  have hAPhysicalMeas : MeasurableSet APhysical :=
    (hAOrdMeas.inter hAAxisMeas).inter hANeighborMeas
  have hAPhysicalAE : ∀ᵐ ω ∂environmentLaw μ, ω ∈ APhysical := by
    filter_upwards [(mem_ae_iff_prob_eq_one hAOrdMeas).mpr hAOrdFull,
      (mem_ae_iff_prob_eq_one hAAxisMeas).mpr hAAxisFull,
      (mem_ae_iff_prob_eq_one hANeighborMeas).mpr hANeighborFull]
      with ω h₁ h₂ h₃
    exact ⟨⟨h₁, h₂⟩, h₃⟩
  have hContinuous : Continuous (processEnvironment : ProcessSample →
      LPPDifferentiability.Environment) := by
    change Continuous (fun s : ProcessSample => s.1)
    exact continuous_fst
  have hPullAE : ∀ᵐ s ∂P, processEnvironment s ∈ APhysical := by
    have hMap : P.map processEnvironment = environmentLaw μ := hNative.2.1
    apply ae_of_ae_map hContinuous.measurable.aemeasurable
    simpa only [hMap] using hAPhysicalAE
  let E' : Set ProcessSample := E ∩ processEnvironment ⁻¹' APhysical
  have hE'Meas : MeasurableSet E' :=
    hEMeas.inter (hAPhysicalMeas.preimage hContinuous.measurable)
  have hE'AE : ∀ᵐ s ∂P, s ∈ E' := by
    filter_upwards [(mem_ae_iff_prob_eq_one hEMeas).mpr hEFull,
      hPullAE] with s hs hphysical
    exact ⟨hs, hphysical⟩
  have hE'Full : P E' = 1 := (mem_ae_iff_prob_eq_one hE'Meas).mp hE'AE

  have hProcess (s : ProcessSample) (hs : s ∈ E')
      (u : Lattice) (γ : ℕ → Lattice)
      (hstart : γ 0 = u)
      (hsteps : ∀ n : ℕ,
        γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
          γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ)))
      (hsegments : LPPDifferentiability.has_maximizing_segments
        (processEnvironment s) γ)
      (hescape₁ : Tendsto (fun n : ℕ => (γ n).1) atTop atTop)
      (hescape₂ : Tendsto (fun n : ℕ => (γ n).2) atTop atTop) :
      ∀ x : Lattice, ∃ (N : ℕ) (K : ℝ),
        x ≤ γ N ∧ x + ((1 : ℤ), (0 : ℤ)) ≤ γ N ∧
        x + ((0 : ℤ), (1 : ℤ)) ≤ γ N ∧
        ∀ n : ℕ,
          (lastPassage (processEnvironment s) x
              (((γ (N + n)).1 - x.1).toNat, ((γ (N + n)).2 - x.2).toNat) -
            lastPassage (processEnvironment s) (x + ((1 : ℤ), (0 : ℤ)))
              (((γ (N + n)).1 - (x + ((1 : ℤ), (0 : ℤ))).1).toNat,
               ((γ (N + n)).2 - (x + ((1 : ℤ), (0 : ℤ))).2).toNat) ≤ K) ∧
          (lastPassage (processEnvironment s) x
              (((γ (N + n)).1 - x.1).toNat, ((γ (N + n)).2 - x.2).toNat) -
            lastPassage (processEnvironment s) (x + ((0 : ℤ), (1 : ℤ)))
              (((γ (N + n)).1 - (x + ((0 : ℤ), (1 : ℤ))).1).toNat,
               ((γ (N + n)).2 - (x + ((0 : ℤ), (1 : ℤ))).2).toNat) ≤ K) := by
    have hωOrd : processEnvironment s ∈ AOrd := hs.2.1.1
    have hωAxis : processEnvironment s ∈ AAxis := hs.2.1.2
    have hωNeighbor : processEnvironment s ∈ ANeighbor := hs.2.2
    have hsNative : s ∈ E := hs.1
    have hDirections := hOrd (processEnvironment s) hωOrd u γ
      hstart hsteps hsegments
    change ∃ ξ : Quadrant, ξ ∈ closedUnitDirections ∧
      ((ξ = ((0 : ℝ≥0), (1 : ℝ≥0)) ∧
          ∀ η : ℝ × ℝ, MapClusterPt η atTop
            (fun n => (((γ n).1 : ℝ) / (n : ℝ),
              ((γ n).2 : ℝ) / (n : ℝ))) → η = ((0 : ℝ), (1 : ℝ))) ∨
       (ξ = ((1 : ℝ≥0), (0 : ℝ≥0)) ∧
          ∀ η : ℝ × ℝ, MapClusterPt η atTop
            (fun n => (((γ n).1 : ℝ) / (n : ℝ),
              ((γ n).2 : ℝ) / (n : ℝ))) → η = ((1 : ℝ), (0 : ℝ))) ∨
       ∃ ξI : InteriorDirection, ξI.1 = ξ ∧
          ∀ η : ℝ × ℝ, MapClusterPt η atTop
            (fun n => (((γ n).1 : ℝ) / (n : ℝ),
              ((γ n).2 : ℝ) / (n : ℝ))) →
            ∃ ηI : InteriorDirection,
              (((ηI.1.1 : ℝ), (ηI.1.2 : ℝ)) : ℝ × ℝ) = η ∧
              ηI ∈ supportFacesUnion g (hLOrd ξI) (hROrd ξI)) at hDirections
    obtain ⟨ξ, _hξ, hCases⟩ := hDirections
    have hAxisConsequence := hAxis (processEnvironment s) hωAxis
      u γ hstart hsteps hsegments
    have hInterior : ∃ ξI : InteriorDirection,
        ∀ η : ℝ × ℝ, MapClusterPt η atTop
          (fun n => (((γ n).1 : ℝ) / (n : ℝ),
            ((γ n).2 : ℝ) / (n : ℝ))) →
          ∃ ηI : InteriorDirection,
            (((ηI.1.1 : ℝ), (ηI.1.2 : ℝ)) : ℝ × ℝ) = η ∧
            ηI ∈ supportFacesUnion g (hL ξI) (hR ξI) := by
      rcases hCases with hN | hE | hI
      · have hnorm := ordinary_ray_normalized_tendsto_of_unique_cluster
          u γ hstart hsteps 0 (fun η hη => by simpa using hN.2 η hη)
        have hNorth := hAxisConsequence.1 hnorm.fst_nhds
        obtain ⟨M, hM⟩ := eventually_atTop.1
          ((tendsto_atTop.1 hescape₁) (u.1 + 1))
        have hc := hM M le_rfl
        rw [hNorth M] at hc
        simp only [Prod.fst_add] at hc
        omega
      · have hnorm := ordinary_ray_normalized_tendsto_of_unique_cluster
          u γ hstart hsteps 1 (fun η hη => by simpa using hE.2 η hη)
        have hEast : Tendsto (fun n : ℕ => ((γ n).2 : ℝ) / (n : ℝ))
            atTop (𝓝 0) := by simpa using hnorm.snd_nhds
        have hEastAxis := hAxisConsequence.2 hEast
        obtain ⟨M, hM⟩ := eventually_atTop.1
          ((tendsto_atTop.1 hescape₂) (u.2 + 1))
        have hc := hM M le_rfl
        rw [hEastAxis M] at hc
        simp only [Prod.snd_add] at hc
        omega
      · obtain ⟨ξI, _, hAll⟩ := hI
        refine ⟨ξI, ?_⟩
        intro η hη
        obtain ⟨ηI, hηI, hFace⟩ := hAll η hη
        refine ⟨ηI, hηI, ?_⟩
        simpa only [hLIdent, hRIdent] using hFace
    obtain ⟨ξI, hClusterI⟩ := hInterior
    let a : ℕ → ℝ := fun n => (((γ n).1 - u.1 : ℤ) : ℝ) / (n : ℝ)
    have hABounds : ∀ n, 0 ≤ a n ∧ a n ≤ 1 :=
      (ordinary_ray_normalized_cluster_bounds u γ hstart hsteps).1
    have hScalarCluster (z : ℝ) (hz : MapClusterPt z atTop a) :
        ((left ξI).1.1 : ℝ) ≤ z ∧ z ≤ ((right ξI).1.1 : ℝ) := by
      have hv := normalized_ray_cluster_of_horizontal_ratio_cluster
        u γ hstart hsteps z hz
      obtain ⟨ηI, hη, hFace⟩ := hClusterI (z, 1 - z) hv
      have hFaceBounds := ((hEndpoints ξI).2.2 ηI).mp hFace
      have hCoord : (ηI.1.1 : ℝ) = z := congrArg Prod.fst hη
      rw [← hCoord]
      exact ⟨by exact_mod_cast hFaceBounds.1,
        by exact_mod_cast hFaceBounds.2⟩
    obtain ⟨kNW, kSE, hSepNW, hSepSE⟩ :=
      exists_dense_barriers_outside_entire_face_interval
        g hGeometry.1 hGeometry.2.2 hHom D hDense
        hL hR left right hExtreme hEndpoints
        (fun n => (hGradient n).1) hGaps ξI
    let ρNW : ℕ → Lattice :=
      rightmostCocyclePath (fun x y => Bplus (hL (D kNW)) x y s) u
    let ρSE : ℕ → Lattice :=
      rightmostCocyclePath (fun x y => Bplus (hL (D kSE)) x y s) u
    have hNWData := hRays s hsNative kNW true u
    have hSEData := hRays s hsNative kSE true u
    change IsLocallyRightmostGeodesic (processEnvironment s) u ρNW ∧
      (∀ j, Bplus (hL (D kNW)) (ρNW j) (ρNW (j + 1)) s =
        processEnvironment s (ρNW j)) ∧
      ∃ d : ℕ → ℕ × ℕ,
        (∀ j, (d j).1 + (d j).2 = j ∧
          ρNW j = u + (((d j).1 : ℤ), ((d j).2 : ℤ))) ∧
        approachesFaceInterval d (left (D kNW)) (right (D kNW)) at hNWData
    change IsLocallyRightmostGeodesic (processEnvironment s) u ρSE ∧
      (∀ j, Bplus (hL (D kSE)) (ρSE j) (ρSE (j + 1)) s =
        processEnvironment s (ρSE j)) ∧
      ∃ d : ℕ → ℕ × ℕ,
        (∀ j, (d j).1 + (d j).2 = j ∧
          ρSE j = u + (((d j).1 : ℤ), ((d j).2 : ℤ))) ∧
        approachesFaceInterval d (left (D kSE)) (right (D kSE)) at hSEData
    obtain ⟨hNWLocal, _, dNW, hNWEnd, hNWFace⟩ := hNWData
    obtain ⟨hSELocal, _, dSE, hSEEnd, hSEFace⟩ := hSEData
    let qNW (n : ℕ) : ℝ := ((dNW n).1 : ℝ) / (n : ℝ)
    let qSE (n : ℕ) : ℝ := ((dSE n).1 : ℝ) / (n : ℝ)
    have hRatioBounds (d : ℕ → ℕ × ℕ)
        (hLen : ∀ n, (d n).1 + (d n).2 = n) (n : ℕ) :
        0 ≤ ((d n).1 : ℝ) / (n : ℝ) ∧
          ((d n).1 : ℝ) / (n : ℝ) ≤ 1 := by
      by_cases hn : n = 0
      · subst n; simp
      have hp : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hd : (d n).1 ≤ n := by have := hLen n; omega
      exact ⟨div_nonneg (Nat.cast_nonneg _) hp.le,
        (div_le_iff₀ hp).mpr (by
          simpa only [one_mul] using
            (show ((d n).1 : ℝ) ≤ (n : ℝ) from by exact_mod_cast hd))⟩
    have hBetween : ∀ᶠ n : ℕ in atTop, qNW n < a n ∧ a n < qSE n := by
      apply eventually_between_separated_barrier_ratios a qNW qSE
        ((left ξI).1.1 : ℝ) ((right ξI).1.1 : ℝ)
        ((right (D kNW)).1.1 : ℝ) ((left (D kSE)).1.1 : ℝ)
        hABounds
        (hRatioBounds dNW (fun n => (hNWEnd n).1))
        (hRatioBounds dSE (fun n => (hSEEnd n).1))
        hScalarCluster
      · have hEq :
            (fun n => ((dNW n).1 : ℝ) /
              (((dNW n).1 + (dNW n).2 : ℕ) : ℝ)) = qNW := by
          funext n
          simp only [qNW, (hNWEnd n).1]
        simpa only [hEq] using hNWFace.2.2
      · exact hSepNW
      · exact hSepSE
      · have hEq :
            (fun n => ((dSE n).1 : ℝ) /
              (((dSE n).1 + (dSE n).2 : ℕ) : ℝ)) = qSE := by
          funext n
          simp only [qSE, (hSEEnd n).1]
        simpa only [hEq] using hSEFace.2.1
    have hOrderNW : ∀ᶠ n : ℕ in atTop,
        (ρNW n).1 ≤ (γ n).1 := by
      filter_upwards [hBetween, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
      have hreal : ((dNW n).1 : ℝ) < (((γ n).1 - u.1 : ℤ) : ℝ) := by
        exact (div_lt_div_iff_of_pos_right hnR).mp hn.1
      have hint : ((dNW n).1 : ℤ) < (γ n).1 - u.1 := by exact_mod_cast hreal
      rw [(hNWEnd n).2]
      simp only [Prod.fst_add]
      omega
    have hOrderSE : ∀ᶠ n : ℕ in atTop,
        (γ n).1 ≤ (ρSE n).1 := by
      filter_upwards [hBetween, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
      have hreal : (((γ n).1 - u.1 : ℤ) : ℝ) < ((dSE n).1 : ℝ) := by
        exact (div_lt_div_iff_of_pos_right hnR).mp hn.2
      have hint : (γ n).1 - u.1 < ((dSE n).1 : ℤ) := by exact_mod_cast hreal
      rw [(hSEEnd n).2]
      simp only [Prod.fst_add]
      omega
    intro x
    have hBound := eventually_neighbor_upper_bounds_between_face_barriers
      (processEnvironment s) (hUniform (processEnvironment s) hωNeighbor)
      u x γ dNW dSE
      (left (D kNW)) (right (D kNW))
      (left (D kSE)) (right (D kSE))
      hstart hsteps hescape₁ hescape₂ hNWFace hSEFace
      (by exact (hNWEnd 0).2.symm.trans hNWLocal.1)
      (by exact (hSEEnd 0).2.symm.trans hSELocal.1)
      (by
        intro n
        rw [← (hNWEnd (n + 1)).2, ← (hNWEnd n).2]
        exact hNWLocal.2.1 n)
      (by
        intro n
        rw [← (hSEEnd (n + 1)).2, ← (hSEEnd n).2]
        exact hSELocal.2.1 n)
      (by
        filter_upwards [hOrderNW] with n hn
        rw [← (hNWEnd n).2]
        exact hn)
      (by
        filter_upwards [hOrderSE] with n hn
        rw [← (hSEEnd n).2]
        exact hn)
    obtain ⟨K, hEvent⟩ := hBound
    obtain ⟨N, hTail⟩ := eventually_atTop.1 hEvent
    have hValid := (hTail N le_rfl)
    refine ⟨N, K, hValid.1, hValid.2.1, hValid.2.2.1, ?_⟩
    intro n
    exact (hTail (N + n) (Nat.le_add_right N n)).2.2.2

  obtain ⟨A, hAMeas, hAImage, hAFull⟩ :=
    ProbabilityBasics.exists_measurable_full_subset_image_of_continuous
      P processEnvironment hContinuous E' hE'Meas hE'Full
  refine ⟨A, hAMeas, ?_, ?_⟩
  · rw [← hNative.2.1]
    exact hAFull
  · intro ω hω u γ hstart hsteps hsegments hescape₁ hescape₂ x
    obtain ⟨s, hs, hω⟩ := hAImage hω
    subst ω
    exact hProcess s hs u γ hstart hsteps hsegments hescape₁ hescape₂ x

end LPP.Busemann
