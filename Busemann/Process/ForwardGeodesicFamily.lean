/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.ForwardWeightSigma
public import Busemann.Geometry.GeodesicLowerCut
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Probability.TranslationEquiv
public import LPP_Foundations.Model.Paths.Coalescence
import Busemann.Process.GeodesicFamilyHorizontalResampling
import Busemann.Process.GeodesicFamilyVerticalResampling
import LPP_Foundations.Probability.EnvironmentCoordinateVersionIntersection
import LPP_Foundations.Probability.EnvironmentResamplingVersion
import LPP_Foundations.Probability.EnvironmentHalfPlaneResample
import LPP_Foundations.Probability.EnvironmentVerticalHalfPlaneCoupling

/-!
# Forward-measurable versions of a coalescing geodesic family

The two half-plane resampling identities give coordinate versions on the two
axes. Their common version depends only on northeast weights, and translations
carry it to every signed root.
-/

@[expose] public section
open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- A measurable shift-covariant coalescing family of original-space
geodesics has forward-weight-measurable versions at all signed roots.
Strong Existence, `lm:pi-forward`, public source lines 975–1004. -/
theorem exists_forwardWeightSigma_versions_of_coalescing_geodesic_family
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (π : Lattice → Environment → (ℕ → Lattice))
    (hMeas : ∀ u : Lattice, Measurable (π u))
    (hGeo : ∀ u : Lattice, ∀ᵐ ω ∂environmentLaw μ,
      IsLocallyRightmostGeodesic ω u (π u ω))
    (hShift : ∀ u : Lattice, ∀ᵐ ω ∂environmentLaw μ,
      π u ω = (fun n : ℕ => π 0 (environmentTranslationEquiv u ω) n + u))
    (hCoal : ∀ u v : Lattice, ∀ᵐ ω ∂environmentLaw μ,
      paths_coalesce u v (π u ω) (π v ω)) :
    ∀ u : Lattice, ∃ F : Environment → (ℕ → Lattice),
      @Measurable Environment (ℕ → Lattice) (forwardWeightSigma u)
        inferInstance F ∧
      ∀ᵐ ω ∂environmentLaw μ,
        π u ω = F ω := by
  classical
  let P : Measure Environment := environmentLaw μ
  let ray : Environment → (ℕ → Lattice) :=
    fun ω => π 0 ω
  let north : Set Lattice := {z | 0 ≤ z.2}
  let east : Set Lattice := {z | 0 ≤ z.1}
  let quadrant : Set Lattice := north ∩ east

  -- The supplied original-space observable is measurable.
  have hRayMeas : Measurable ray := hMeas 0
  have hPairEqualityMeas : MeasurableSet
      {p : Environment × Environment | ray p.1 = ray p.2} :=
    measurableSet_eq_fun (hRayMeas.comp measurable_fst)
      (hRayMeas.comp measurable_snd)

  -- Pull the horizontal mapped-coupling identity back to its product input.
  have hNorthResampling : ∀ᵐ p : Environment × Environment ∂P.prod P,
      ray p.1 = ray (Set.piecewise north p.1 p.2) := by
    let resampleNorth : Environment × Environment → Environment × Environment :=
      fun q => (q.1, fun z : Lattice => if 0 ≤ z.2 then q.1 z else q.2 z)
    have hCoupled : ∀ᵐ p ∂(P.prod P).map resampleNorth,
        ray p.1 = ray p.2 := by
      simpa only [P, resampleNorth, ray] using
        ae_geodesic_family_eq_horizontal_halfPlane_resample
          μ π hMeas hGeo hShift hCoal
    have hResampleMeas : Measurable resampleNorth := by
      exact measurable_fst.prodMk measurable_horizontal_halfPlane_resample
    have hPull : ∀ᵐ p ∂P.prod P,
        ray (resampleNorth p).1 = ray (resampleNorth p).2 := by
      simpa only [Set.mem_ofPred_eq] using
        (ae_map_iff hResampleMeas.aemeasurable hPairEqualityMeas).1 hCoupled
    filter_upwards [hPull] with p hp
    have hPiecewise : Set.piecewise north p.1 p.2 =
        (fun z : Lattice => if 0 ≤ z.2 then p.1 z else p.2 z) := by
      funext z
      by_cases hz : 0 ≤ z.2 <;> simp [Set.piecewise, north, hz]
    have hp' : ray p.1 =
        ray (fun z : Lattice => if 0 ≤ z.2 then p.1 z else p.2 z) := by
      simpa only [resampleNorth, Prod.fst, Prod.snd] using hp
    rw [hPiecewise]
    exact hp'

  -- The vertical mapped-coupling identity has the same original product input.
  have hEastResampling : ∀ᵐ p : Environment × Environment ∂P.prod P,
      ray p.1 = ray (Set.piecewise east p.1 p.2) := by
    let resampleEast : Environment × Environment → Environment × Environment :=
      fun q => (q.1, fun z : Lattice => if 0 ≤ z.1 then q.1 z else q.2 z)
    have hCoupled : ∀ᵐ p ∂(P.prod P).map resampleEast,
        ray p.1 = ray p.2 := by
      simpa only [P, resampleEast, ray] using
        ae_geodesic_family_eq_vertical_halfPlane_resample
          μ π hMeas hGeo hShift hCoal
    have hResampleMeas : Measurable resampleEast := by
      exact measurable_fst.prodMk measurable_vertical_halfPlane_resample
    have hPull : ∀ᵐ p ∂P.prod P,
        ray (resampleEast p).1 = ray (resampleEast p).2 := by
      simpa only [Set.mem_ofPred_eq] using
        (ae_map_iff hResampleMeas.aemeasurable hPairEqualityMeas).1 hCoupled
    filter_upwards [hPull] with p hp
    have hPiecewise : Set.piecewise east p.1 p.2 =
        (fun z : Lattice => if 0 ≤ z.1 then p.1 z else p.2 z) := by
      funext z
      by_cases hz : 0 ≤ z.1 <;> simp [Set.piecewise, east, hz]
    have hp' : ray p.1 =
        ray (fun z : Lattice => if 0 ≤ z.1 then p.1 z else p.2 z) := by
      simpa only [resampleEast, Prod.fst, Prod.snd] using hp
    rw [hPiecewise]
    exact hp'

  -- Resampling gives one version on each half-plane of retained coordinates.
  obtain ⟨gNorth, hgNorth, hNorthVersion⟩ :=
    exists_measurable_restriction_version_of_ae_resampling_invariant
      μ north ray hRayMeas hNorthResampling
  obtain ⟨gEast, hgEast, hEastVersion⟩ :=
    exists_measurable_restriction_version_of_ae_resampling_invariant
      μ east ray hRayMeas hEastResampling

  -- The one intersection version depends only on the northeast quadrant.
  obtain ⟨gQuadrant, hgQuadrant, hZeroVersion⟩ :=
    exists_measurable_intersection_version_of_coordinate_versions
      μ north east ray gNorth hgNorth hNorthVersion gEast hgEast hEastVersion

  intro u
  let F : Environment → (ℕ → Lattice) := fun ω n =>
    gQuadrant (fun z : quadrant => ω (u + z.1)) n + u
  refine ⟨F, ?_, ?_⟩

  -- Each retained translated coordinate is an original northeast weight.
  have hFMeas : @Measurable Environment (ℕ → Lattice)
      (forwardWeightSigma u) inferInstance F := by
    let : MeasurableSpace Environment := forwardWeightSigma u
    have hCone : Measurable (fun ω : Environment =>
        fun z : {z : Lattice // u ≤ z} => ω z.val) := by
      exact comap_measurable _
    have hRestriction : Measurable
        (fun ω : Environment => fun z : quadrant => ω (u + z.val)) := by
      apply measurable_pi_iff.mpr
      intro z
      let w : {w : Lattice // u ≤ w} := ⟨u + z.val, by
        have hEast : 0 ≤ z.val.1 := by
          change z.val ∈ east
          exact z.property.2
        have hNorth : 0 ≤ z.val.2 := by
          change z.val ∈ north
          exact z.property.1
        change u.1 ≤ (u + z.val).1 ∧ u.2 ≤ (u + z.val).2
        simp only [Prod.fst_add, Prod.snd_add]
        exact ⟨le_add_of_nonneg_right hEast, le_add_of_nonneg_right hNorth⟩⟩
      simpa only [Function.comp_def] using (measurable_pi_apply w).comp hCone
    have hTranslatePath : Measurable (fun p : ℕ → Lattice => fun n => p n + u) := by
      apply Measurable.of_eval
      intro n
      exact (measurable_pi_apply n).add measurable_const
    simpa only [F, Function.comp_def] using hTranslatePath.comp (hgQuadrant.comp hRestriction)
  exact hFMeas

  -- Translate the zero-root almost-sure equality and use the supplied shift law.
  have hShiftedZeroVersion : ∀ᵐ ω ∂P,
      ray (environmentTranslationEquiv u ω) =
        gQuadrant (fun z : quadrant => ω (u + z.1)) := by
    have hShifted :=
      (measurePreserving_environmentTranslationEquiv μ u).quasiMeasurePreserving.ae
        hZeroVersion
    filter_upwards [hShifted] with ω hω
    simpa only [ray, environmentTranslationEquiv_apply] using hω
  filter_upwards [hShift u, hShiftedZeroVersion] with ω hshift hzero
  funext n
  have hShiftAtN := congrArg (fun p : ℕ → Lattice => p n) hshift
  have hVersionAtN := congrArg (fun p : ℕ → Lattice => p n) hzero
  exact hShiftAtN.trans (congrArg (fun z : Lattice => z + u) hVersionAtN)

end LPP.Busemann
