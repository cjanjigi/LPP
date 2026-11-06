/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.CoordinateLaw
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-! The whole canonical iid law is preserved by a fresh single-coordinate update. -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace LPPDifferentiability

/-- The literal operation replacing one coordinate by the fresh real input is measurable. -/
theorem measurable_environment_update (v : Lattice) :
    Measurable (fun p : ℝ × Environment => Function.update p.2 v p.1) := by
  classical
  apply Measurable.of_eval
  intro z
  by_cases hz : z = v
  · subst z
    simpa only [Function.update_self] using measurable_fst
  · simpa only [Function.update_of_ne hz, Function.comp_def] using
      (measurable_environment_eval z).comp (measurable_snd :
        Measurable (Prod.snd : ℝ × Environment → Environment))

/-- Fresh one-site resampling preserves the whole environment law, including every
finite joint distribution, rather than merely the one-site marginals. -/
theorem environmentLaw_map_update (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : Lattice) :
    (μ.prod (environmentLaw μ)).map
      (fun p : ℝ × Environment => Function.update p.2 v p.1) = environmentLaw μ := by
  classical
  change _ = Measure.infinitePi (fun _ : Lattice => μ)
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply (measurable_environment_update v)
    (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  have hpre :
      (fun p : ℝ × Environment => Function.update p.2 v p.1) ⁻¹' Set.pi (↑s) t =
        (if v ∈ s then t v else Set.univ) ×ˢ Set.pi (↑(s.erase v)) t := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod,
      Finset.mem_erase]
    constructor
    · intro hp
      constructor
      · by_cases hv : v ∈ s
        · simpa only [hv, ite_true, Function.update_self] using hp v hv
        · simp only [hv, ite_false, Set.mem_univ]
      · intro z hz
        simpa only [Function.update_of_ne hz.1] using hp z hz.2
    · rintro ⟨hx, hω⟩ z hz
      by_cases hzv : z = v
      · subst z
        simpa only [hz, ite_true, Function.update_self] using hx
      · simpa only [Function.update_of_ne hzv] using hω z ⟨hzv, hz⟩
  rw [hpre, Measure.prod_prod]
  change μ (if v ∈ s then t v else Set.univ) *
    Measure.infinitePi (fun _ : Lattice => μ) (Set.pi (↑(s.erase v)) t) = _
  rw [Measure.infinitePi_pi _ (fun i _ => ht i)]
  by_cases hv : v ∈ s
  · rw [ite_eq_left hv]
    exact Finset.mul_prod_erase s (fun i => μ (t i)) hv
  · rw [ite_eq_right hv, measure_univ, one_mul, Finset.erase_eq_of_notMem hv]

/-- Every measurable real observable has the same integral after literal fresh
one-site resampling. The equality follows from the whole law, including when
the observable depends on the entire selected path. -/
theorem integral_environment_update (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : Lattice) (g : Environment → ℝ) (hg : Measurable g) :
    (∫ p : ℝ × Environment, g (Function.update p.2 v p.1) ∂μ.prod (environmentLaw μ)) =
      ∫ ω : Environment, g ω ∂environmentLaw μ := by
  have h := integral_map (μ := μ.prod (environmentLaw μ))
    (measurable_environment_update v).aemeasurable hg.aestronglyMeasurable
  rw [environmentLaw_map_update μ v] at h
  exact h.symm

end LPPDifferentiability
