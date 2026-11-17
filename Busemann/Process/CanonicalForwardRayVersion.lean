/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.CoalescingCocycleRepresentation
public import Busemann.Frozen.Definitions.ForwardWeightSigma
import Busemann.Process.CanonicalRayResampling
import Busemann.Process.CanonicalVerticalRayResampling
import Busemann.Process.RightmostPathCovariance
import Busemann.Process.RightmostPathMeasurability
import LPP_Foundations.Probability.EnvironmentCoordinateVersionIntersection
import LPP_Foundations.Probability.EnvironmentResamplingVersion
import LPP_Foundations.Probability.EnvironmentVerticalHalfPlaneCoupling
import LPP_Foundations.Probability.TranslationEquiv
import Lean.Elab.Tactic.Omega

/-!
# A canonical forward-measurable version of the rightmost ray

The two half-plane resampling identities give coordinate versions on the two
axes. Their common version depends only on northeast weights, and translations
carry it to every signed root.
-/

@[expose] public section
open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- The original east-tie rightmost ray has a forward-weight-measurable version
at every signed root, equal to it under the canonical law almost surely.
This is the conclusion of public Strong Existence, lines 975–999. -/
theorem exists_forwardWeightSigma_version_rightmostCocyclePath
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B : Lattice → Lattice → Environment → ℝ)
    (hB : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω)
      (fun ω : Environment => ω) B)
    (hCoal : HasCoalescingRightmostPaths (environmentLaw μ) B) :
    ∀ u : Lattice, ∃ F : Environment → (ℕ → Lattice),
      @Measurable Environment (ℕ → Lattice) (forwardWeightSigma u)
        inferInstance F ∧
      ∀ᵐ ω ∂environmentLaw μ,
        rightmostCocyclePath (fun x y => B x y ω) u = F ω := by
  classical
  let P : Measure Environment := environmentLaw μ
  let ray : Environment → (ℕ → Lattice) :=
    fun ω => rightmostCocyclePath (fun x y => B x y ω) (0, 0)
  let north : Set Lattice := {z | 0 ≤ z.2}
  let east : Set Lattice := {z | 0 ≤ z.1}
  let quadrant : Set Lattice := north ∩ east

  -- The original path-valued observable is measurable in the full environment.
  have hBMeas (x y : Lattice) : Measurable (B x y) := by
    have hSection : Measurable (fun ω : Environment => ((x, y), ω)) :=
      measurable_const.prodMk measurable_id
    simpa only [Function.comp_def] using hB.1.1.comp hSection
  have hRayMeas : Measurable ray := by
    apply Measurable.of_eval
    intro n
    simpa only [ray] using measurable_rightmostCocyclePath B hBMeas (0, 0) n
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
        ae_rightmostCocyclePath_eq_horizontal_halfPlane_resample μ B hB hCoal
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
        ae_rightmostCocyclePath_eq_vertical_halfPlane_resample μ B hB hCoal
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

  -- Translate the zero-root almost-sure equality and use the original covariance.
  have hCovariance : ∀ᵐ ω ∂P, ∀ x y : Lattice,
      B (x + u) (y + u) ω = B x y (environmentTranslationEquiv u ω) := by
    exact ae_all_iff.mpr fun x => ae_all_iff.mpr fun y => hB.1.2.1 x y u
  have hShiftedZeroVersion : ∀ᵐ ω ∂P,
      ray (environmentTranslationEquiv u ω) =
        gQuadrant (fun z : quadrant => ω (u + z.1)) := by
    have hShifted :=
      (measurePreserving_environmentTranslationEquiv μ u).quasiMeasurePreserving.ae
        hZeroVersion
    filter_upwards [hShifted] with ω hω
    simpa only [ray, environmentTranslationEquiv_apply] using hω
  filter_upwards [hCovariance, hShiftedZeroVersion] with ω hcov hzero
  funext n
  have hTranslate := rightmostCocyclePath_translate
      (fun x y => B x y ω)
      (fun x y => B x y (environmentTranslationEquiv u ω))
      u
      (fun x y => (hcov x y).symm)
      (0, 0) n
  have hPath : ray (environmentTranslationEquiv u ω) n + u =
      rightmostCocyclePath (fun x y => B x y ω) u n := by
    have hStart : (0, 0) + u = u := by
      ext <;> simp
    rw [hStart] at hTranslate
    simpa only [ray] using hTranslate
  have hVersionAtN : ray (environmentTranslationEquiv u ω) n =
      gQuadrant (fun z : quadrant => ω (u + z.1)) n := by
    simpa only [ray, environmentTranslationEquiv_apply] using
      congrArg (fun p : ℕ → Lattice => p n) hzero
  rw [hVersionAtN] at hPath
  exact hPath.symm

end LPP.Busemann
