/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.EnvironmentFiniteMaskWeights
import Differentiability.Probability.ForwardHeavyAttachmentMaskEvents

/-! The weight estimate for attachments selected from a finite observed region. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace LPPDifferentiability

/-- The sum of the three geometric failure bounds and the weight failure
bound for the attachments of Lemma B.3. -/
noncomputable def attachmentFailureBound (μ : Measure ℝ) (D s B : ℝ) (m K : ℕ)
    (T p b t : ℝ) : ℝ :=
  let pT := μ.real (Set.Iio (-T))
  let C₁ := ∫ y, max (-y) 0 ∂μ
  let Cₚ := ∫ y, (max (-y) 0)^p ∂μ
  48 * D * s^2 * pT^2 +
    (D * s + 1 + B * ((4 * K + 5 : ℕ) : ℝ)^2) * pT +
    (D * s + 1) * (((((2 * K + 5) * (m + 1) : ℕ) : ℝ) * pT)^K) +
    (D * s + 1) *
      ((2 * m * Cₚ * b^(-p))^K + Real.exp (-t^2 / (2 * b * (2 * C₁ * m + t / 3))))

/-- Remove the weight failure event from the geometric good event. The
weight estimate is applied to the same mask-selected paths used on `G`. -/
theorem exists_attachment_weight_event
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T p b t : ℝ)
    (hp : 1 < p) (hT : 0 < T) (hthreshold : (2 : ℝ≥0∞)⁻¹ ≤ μ (Set.Ici (-T)))
    (hb : 0 < b) (ht : 0 < t)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0)^p) ∂μ) < ∞)
    (J R : Finset Lattice) (m K : ℕ) (hK : 1 ≤ K)
    (start : J → Lattice) (d : J → ℕ × ℕ)
    (q : (mask : R → Bool) → (u : J) → Path (start u) (d u))
    (hlen : ∀ u, (d u).1 + (d u).2 = m)
    (hmem : ∀ mask u i, (q mask u).vertex i ∈ R)
    (c C : ℝ) (hJ : (J.card : ℝ) ≤ C)
    (G : Set Environment) (hG : MeasurableSet G) (hprob : 1 - c ≤ (environmentLaw μ).real G)
    (good : (R → Bool) → Prop)
    (hgood : ∀ ω : Environment, ω ∈ G ↔ good (fun z => if ω z.val < -T then true else false))
    (hsafe : ∀ ω ∈ G, ∀ (u : J) i,
      -T ≤ ω ((q (fun z => if ω z.val < -T then true else false) u).vertex i)) :
    let mask := fun (ω : Environment) (z : R) => if ω z.val < -T then true else false
    let C₁ := ∫ y, max (-y) 0 ∂μ
    let Cₚ := ∫ y, (max (-y) 0)^p ∂μ
    ∃ A : Set Environment, MeasurableSet A ∧
      max 0 (1 - (c + C * ((2 * m * Cₚ * b^(-p))^K +
        Real.exp (-t^2 / (2 * b * (2 * C₁ * m + t / 3)))))) ≤ (environmentLaw μ).real A ∧
      (∀ ω ∈ A, ∀ u, -2 * C₁ * m - (K - 1 : ℕ) * T - t ≤ pathWeight ω (q (mask ω) u)) := by
  classical
  intro mask C₁ Cₚ
  let active (bits : R → Bool) (u : J) :=
    good bits ∧
      ∀ i : Fin ((d u).1 + (d u).2), bits ⟨(q bits u).vertex i.castSucc, hmem bits u _⟩ = false
  have hactive (ω : Environment) (hω : ω ∈ G) (u : J) : active (mask ω) u := by
    refine ⟨(hgood ω).mp hω, ?_⟩
    intro i
    exact ite_eq_right (not_lt.mpr (hsafe ω hω u i.castSucc))
  have hbound := environment_finite_mask_path_weight_failure_le μ T p b t hp hT hthreshold
    hb ht hmoment R m J.card K hK (by simp)
    (fun bits u => decide (active bits u)) (fun _ => start) (fun _ => d) q
    (fun _ u _ => (hlen u).le) (fun bits u _ i => hmem bits u i.castSucc)
    (fun bits u h i => (of_decide_eq_true h : active bits u).2 i)
  let E := {ω : Environment | ∃ u : J, decide (active (mask ω) u) = true ∧
    pathWeight ω (q (mask ω) u) < -2 * C₁ * m - (K - 1 : ℕ) * T - t}
  have hlenR (u : J) : ((d u).1 : ℝ) + ((d u).2 : ℝ) = (m : ℝ) := by
    exact_mod_cast hlen u
  have hE : MeasurableSet E ∧ (environmentLaw μ).real E ≤
      J.card * ((2 * m * Cₚ * b^(-p))^K + Real.exp (-t^2 / (2 * b * (2 * C₁ * m + t / 3)))) := by
    simpa only [E, C₁, Cₚ, hlenR] using hbound
  have hfactor : 0 ≤ (2 * m * Cₚ * b^(-p))^K +
      Real.exp (-t^2 / (2 * b * (2 * C₁ * m + t / 3))) := by
    have hCp : 0 ≤ Cₚ := integral_nonneg (fun _ => Real.rpow_nonneg (le_max_right _ _) _)
    positivity
  have hjoint := measureReal_inter_compl_ge_max_zero μ G E hG hE.1 c _
    hprob (hE.2.trans (mul_le_mul_of_nonneg_right hJ hfactor))
  refine ⟨G ∩ Eᶜ, hjoint.1, hjoint.2, ?_⟩
  intro ω hω u
  by_contra! h
  exact hω.2 ⟨u, decide_eq_true (hactive ω hω.1 u), h⟩

end LPPDifferentiability
