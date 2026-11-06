/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.FiniteMaskFamilyWeights
public import LPP_Foundations.Probability.FiniteEnvironmentLaw
public import LPP_Foundations.Model.Paths.Geometry
public import LPP_Foundations.Frozen.Model.PathWeight

/-! # Actual path weights selected from a fixed finite-region mask

This is the finite-region specialization of the source weights lemma. The
mask observes precisely Q, and all active collected vertices belong to Q and
are good under that same mask. This makes no assertion about arbitrary
families measurable with respect to the whole infinite mask sigma algebra.
-/

public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LPPDifferentiability

/-- Actual terminal-excluded path weights under the original environment law.
Distinctness, the finite coordinate law, conditional moments, independence,
and the finite mask partition are all derived internally. -/
theorem environment_finite_mask_path_weight_failure_le
    {J : Type*} [Fintype J]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T p b t : ℝ)
    (hp : 1 < p) (hT : 0 < T)
    (hthreshold : (2 : ℝ≥0∞)⁻¹ ≤ μ (Set.Ici (-T))) (hb : 0 < b) (ht : 0 < t)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞)
    (Q : Finset Lattice) (n N K : ℕ) (hK : 1 ≤ K) (hJ : Fintype.card J ≤ N)
    (active : (Q → Bool) → J → Bool)
    (starts : (Q → Bool) → J → Lattice) (disps : (Q → Bool) → J → ℕ × ℕ)
    (q : (a : Q → Bool) → (j : J) → Path (starts a j) (disps a j))
    (hlen : ∀ a j, active a j = true → (disps a j).1 + (disps a j).2 ≤ n)
    (hmem : ∀ a j, active a j = true → ∀ i : Fin ((disps a j).1 + (disps a j).2),
      (q a j).vertex i.castSucc ∈ Q)
    (hgood : ∀ (a : Q → Bool) (j : J) (h : active a j = true)
      (i : Fin ((disps a j).1 + (disps a j).2)),
      a ⟨(q a j).vertex i.castSucc, hmem a j h i⟩ = false) :
    let mask := fun ω : Environment => fun z : Q => if ω z.1 < -T then true else false
    let E := {ω : Environment | ∃ j : J, active (mask ω) j = true ∧
      pathWeight ω (q (mask ω) j) <
        -2 * (∫ y, max (-y) 0 ∂μ) * ((disps (mask ω) j).1 + (disps (mask ω) j).2) -
          (K - 1 : ℕ) * T - t}
    MeasurableSet E ∧ (environmentLaw μ).real E ≤
      N * ((2 * n * (∫ y, (max (-y) 0) ^ p ∂μ) * b ^ (-p)) ^ K +
        Real.exp (-t ^ 2 / (2 * b * (2 * (∫ y, max (-y) 0 ∂μ) * n + t / 3)))) := by
  classical
  let eval := fun ω : Environment => fun z : Q => ω z.1
  let mask := fun x : Q → ℝ => fun z => if x z < -T then true else false
  let m := fun (a : Q → Bool) (j : J) => (disps a j).1 + (disps a j).2
  let f := fun (a : Q → Bool) (j : J) (h : active a j = true) (i : Fin (m a j)) =>
    (⟨(q a j).vertex i.castSucc, hmem a j h i⟩ : Q)
  have hinj (a : Q → Bool) (j : J) (h : active a j = true) : Function.Injective (f a j h) := by
    intro i i' heq
    have hvertices : (q a j).vertex i.castSucc = (q a j).vertex i'.castSucc :=
      congrArg Subtype.val heq
    exact Fin.castSucc_injective _ ((q a j).vertex_injective hvertices)
  have hfinite := finite_mask_family_weight_failure_le μ T p b t hp hT hthreshold hb ht hmoment
    n N K hK hJ active m f hlen hinj hgood
  let E := {x : Q → ℝ | ∃ j : J, if h : active (mask x) j = true then
    (∑ k, x (f (mask x) j h k)) <
      -2 * (∫ y, max (-y) 0 ∂μ) * m (mask x) j - (K - 1 : ℕ) * T - t else False}
  have hEm : MeasurableSet E := hfinite.1
  have heval : Measurable eval := measurable_finite_environment_coordinates Subtype.val
  have hlaw : (environmentLaw μ).map eval = Measure.pi (fun _ : Q => μ) :=
    environmentLaw_map_finite_coordinates μ Subtype.val Subtype.val_injective
  have heq : {ω : Environment | ∃ j : J, active (mask (eval ω)) j = true ∧
      pathWeight ω (q (mask (eval ω)) j) <
        -2 * (∫ y, max (-y) 0 ∂μ) * ((disps (mask (eval ω)) j).1 + (disps (mask (eval ω)) j).2) -
          (K - 1 : ℕ) * T - t} = eval ⁻¹' E := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, E]
    apply exists_congr
    intro j
    by_cases h : active (mask (eval ω)) j = true
    · simp only [h, true_and, m, Nat.cast_add]
      rfl
    · simp [h]
  change MeasurableSet {ω : Environment | ∃ j : J, active (mask (eval ω)) j = true ∧
      pathWeight ω (q (mask (eval ω)) j) <
        -2 * (∫ y, max (-y) 0 ∂μ) * ((disps (mask (eval ω)) j).1 + (disps (mask (eval ω)) j).2) -
          (K - 1 : ℕ) * T - t} ∧ _
  rw [heq]
  refine ⟨hEm.preimage heval, ?_⟩
  rw [← map_measureReal_apply heval hEm, hlaw]
  exact hfinite.2

end LPPDifferentiability
