/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.InvariantCocycleTilt
public import Busemann.Frozen.Definitions.ForwardMeasurable
public import LPP_Foundations.Model.LastPassage.PassageDifferenceLimits
public import LPP_Foundations.Model.Paths.Coalescence
public import Busemann.Frozen.Definitions.CoalescingRightmostPaths
public import Busemann.Process.RealQuantileJointLaw
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Probability.TranslationEquiv

import Busemann.Process.PinnedOriginalSpaceCocycleAux
import Busemann.Process.RealQuantileFieldMean
import Busemann.Process.RealQuantileDenseEquality
import Busemann.Process.RealQuantileFieldJointLaw
import Lean.Elab.Tactic.Omega

@[expose] public section
open MeasureTheory Filter ProbabilityTheory LPPDifferentiability
open scoped ENNReal Topology
namespace LPP.Busemann

/-- A pinned coupled cocycle is the pullback of one forward, integrable,
recovering cocycle on the original iid environment. Its canonical rightmost
paths coalesce and its ordinary edge means are the negative of the pinned tilt. This is the
constant-tilt original-space assembly, not random-tilt decomposition.
Strong Existence, lm:Bs-Bhat and lm:orig_space, lines 1055–1103.
Also see Strong Existence, proof of thm:Bhat-B, lines 1141–1145. -/
theorem exists_original_forward_cocycle_of_pinned_coupled_cocycle
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hShift : ∀ z : Lattice, P.map (processShift z) = P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : IsGeneralizedBusemann P processShift processEnvironment B)
    (hCoal : HasCoalescingRightmostPaths P B)
    (h : ℝ × ℝ)
    (hPinned : ∀ᵐ a ∂P,
      invariantCocycleTilt P processShift processEnvironment B hB a = h) :
    ∃ C : Lattice → Lattice → Environment → ℝ,
      IsGeneralizedBusemann (environmentLaw μ)
        (fun z ω => environmentTranslationEquiv z ω)
        (fun ω : Environment => ω) C ∧
      IsForwardMeasurable C ∧
      HasCoalescingRightmostPaths (environmentLaw μ) C ∧
      (∫ ω, C 0 (1, 0) ω ∂environmentLaw μ) = -h.1 ∧
      (∫ ω, C 0 (0, 1) ω ∂environmentLaw μ) = -h.2 ∧
      (∀ᵐ a ∂P, ∀ x y : Lattice,
        B x y a = C x y (processEnvironment a)) := by
  classical
  let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
    fun u => condDistrib
      (fun a : ProcessSample => rightmostCocyclePath
        (fun x y => B x y a) u) processEnvironment P
  obtain ⟨q, hqMeas, hqCDF, hMeanGood⟩ :=
    exists_real_quantile_forward_field_with_pinned_mean_ae_parameter
      μ hμ hmoment P hMarginal hShift B hB hCoal h hPinned
  obtain ⟨R, hRMeas, hRJoint, hRLimit⟩ :=
    exists_measurable_real_quantile_field_with_original_joint_law
      μ hμ hmoment P hMarginal B hB hCoal q hqMeas hqCDF
  have hCoalGood := ae_parameter_coalescing_real_quantile_family
    μ P hMarginal B hB hCoal q hqMeas hqCDF

  let G : unitInterval → Prop := fun s =>
    0 < (s : ℝ) ∧
    (∀ᵐ ω ∂environmentLaw μ, ∀ u v : Lattice,
      paths_coalesce u v (q u ω s) (q v ω s)) ∧
    ∃ C : Lattice → Lattice → Environment → ℝ,
      IsGeneralizedBusemann (environmentLaw μ)
        (fun z ω => environmentTranslationEquiv z ω)
        (fun ω : Environment => ω) C ∧
      IsForwardMeasurable C ∧
      (∫ ω, C 0 (1, 0) ω ∂environmentLaw μ) = -h.1 ∧
      (∫ ω, C 0 (0, 1) ω ∂environmentLaw μ) = -h.2 ∧
      ∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice,
        has_passage_difference_limits ω (q u ω s) (fun x y => C x y ω)
  have hG : ∀ᵐ s ∂(volume : Measure unitInterval), G s := by
    filter_upwards [hMeanGood, hCoalGood] with s hs hc
    exact ⟨hs.1, hc, hs.2⟩
  obtain ⟨D, hDCount, hDDense, hDGood⟩ :=
    countable_dense_subset_of_ae_unitInterval G hG
  let : Countable D := hDCount.to_subtype
  let F : D → Lattice → Lattice → Environment → ℝ := fun r =>
    Classical.choose (hDGood r.1 r.2).2.2
  have hF (r : D) := Classical.choose_spec (hDGood r.1 r.2).2.2
  have hCanonical (r : D) :
      (∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice,
        rightmostCocyclePath (fun x y => F r x y ω) u = q u ω r.1) ∧
      HasCoalescingRightmostPaths (environmentLaw μ) (F r) := by
    apply ae_quantile_paths_eq_canonical_of_finite_field μ hμ hmoment q r.1
      (by filter_upwards [hqCDF] with ω hω; exact fun u => (hω u r.1).1)
      (hDGood r.1 r.2).2.1 (F r) (hF r).1
      (hF r).2.2.2.2

  have hParameterOrder (ω : Environment)
      (hω : ∀ (u : Lattice) (s : unitInterval),
        IsLocallyRightmostGeodesic ω u (q u ω s) ∧
        ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE (q u ω s) γ ↔
            ENNReal.ofReal (s : ℝ) ≤
              (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η γ}))
      (r t : unitInterval) (hrt : r ≤ t) (u : Lattice) :
      pathSoutheastLE (q u ω r) (q u ω t) := by
    have htSelf : pathSoutheastLE (q u ω t) (q u ω t) := by
      intro m n hLevel
      have hmn : m = n := by omega
      subst n
      exact ⟨le_rfl, le_rfl⟩
    have htCut : ENNReal.ofReal (t : ℝ) ≤
        (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η (q u ω t)} :=
      ((hω u t).2 (q u ω t) (hω u t).1).mp htSelf
    have hrtReal : (r : ℝ) ≤ (t : ℝ) := by exact_mod_cast hrt
    have hrCut : ENNReal.ofReal (r : ℝ) ≤
        (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η (q u ω t)} :=
      (ENNReal.ofReal_le_ofReal hrtReal).trans htCut
    exact ((hω u r).2 (q u ω t) (hω u t).1).mpr hrCut

  have hOrdered (r t : D) (hrt : r.1 ≤ t.1) :
      ∀ᵐ ω ∂environmentLaw μ, ∀ x y : Lattice,
        F r x y ω = F t x y ω := by
    have hPaths : ∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice,
        pathSoutheastLE
          (rightmostCocyclePath (fun x y => F r x y ω) u)
          (rightmostCocyclePath (fun x y => F t x y ω) u) := by
      filter_upwards [hqCDF, (hCanonical r).1, (hCanonical t).1]
        with ω hω hr ht
      intro u
      rw [hr u, ht u]
      exact hParameterOrder ω hω r.1 t.1 hrt u
    exact ae_eq_of_ordered_coalescing_fields_with_same_edge_means
      μ (F r) (F t) (hF r).1 (hF t).1
      (hCanonical r).2 (hCanonical t).2
      ((hF r).2.2.1.trans (hF t).2.2.1.symm)
      ((hF r).2.2.2.1.trans (hF t).2.2.2.1.symm) hPaths
  have hPairFields (r t : D) :
      ∀ᵐ ω ∂environmentLaw μ, ∀ x y : Lattice,
        F r x y ω = F t x y ω := by
    rcases le_total r.1 t.1 with hrt | htr
    · exact hOrdered r t hrt
    · filter_upwards [hOrdered t r htr] with ω hω
      intro x y
      exact (hω x y).symm
  have hAllFields : ∀ᵐ ω ∂environmentLaw μ,
      ∀ r t : D, ∀ x y : Lattice,
        F r x y ω = F t x y ω := by
    apply ae_all_iff.mpr
    intro r
    apply ae_all_iff.mpr
    intro t
    exact hPairFields r t
  have hAllCanonical : ∀ᵐ ω ∂environmentLaw μ,
      ∀ r : D, ∀ u : Lattice,
        rightmostCocyclePath (fun x y => F r x y ω) u = q u ω r.1 := by
    apply ae_all_iff.mpr
    intro r
    exact (hCanonical r).1
  have hDensePaths : ∀ᵐ ω ∂environmentLaw μ,
      ∀ r t : D, ∀ u : Lattice,
        q u ω r.1 = q u ω t.1 := by
    filter_upwards [hAllFields, hAllCanonical] with ω hFields hPaths
    intro r t u
    calc
      q u ω r.1 = rightmostCocyclePath (fun x y => F r x y ω) u :=
        (hPaths r u).symm
      _ = rightmostCocyclePath (fun x y => F t x y ω) u := by
        congr 1
        funext x y
        exact hFields r t x y
      _ = q u ω t.1 := hPaths t u

  obtain ⟨s₀, hs₀⟩ : D.Nonempty := hDDense.nonempty
  let r₀ : D := ⟨s₀, hs₀⟩
  let C := F r₀
  have hAllPositive : ∀ᵐ ω ∂environmentLaw μ,
      ∀ s t : unitInterval, 0 < (s : ℝ) → 0 < (t : ℝ) →
        ∀ u : Lattice, q u ω s = q u ω t := by
    filter_upwards [hqCDF, hDensePaths] with ω hω hDense
    exact real_quantile_paths_eq_of_dense_parameter_eq ω κ q hω D
      hDDense (by
        intro r hr t ht u
        exact hDense ⟨r, hr⟩ ⟨t, ht⟩ u)
  have hRawEqualsC := raw_field_eq_fixed_field_of_same_positive_quantile_paths
    μ q s₀ (hDGood s₀ hs₀).1 C R
    (by filter_upwards [hqCDF] with ω hω; exact fun u s => (hω u s).1)
    (hDGood s₀ hs₀).2.1 hAllPositive (hF r₀).2.2.2.2 hRLimit
  have hActualEqualsC := actual_cocycle_eq_of_same_joint_field_law
    μ P B hB.1.1 C (hF r₀).1.1.1 R hRMeas hRJoint hRawEqualsC
  exact ⟨C, (hF r₀).1, (hF r₀).2.1, (hCanonical r₀).2,
    (hF r₀).2.2.1, (hF r₀).2.2.2.1, hActualEqualsC⟩

end LPP.Busemann
