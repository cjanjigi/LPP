/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.DiagonalAnimalMaximum
public import Martin2004.Probability.AnimalPositiveMean
public import LPP_Foundations.Probability.CoordinateLaw
import LPP_Foundations.Model.Animals.DiagonalComparison
import Martin2004.Probability.DiagonalAnimalLaw

/-!
# Finite moments of diagonal animal maxima

Finite sums and a finite nonempty maximum preserve integrability. For the
positive-part field, the size-one animal bound supplies the actual
one-site moment from the positive square-root tail alone.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace LPPDifferentiability

/-- Integrable site coordinates give an integrable actual diagonal maximum. -/
theorem integrable_diagonalAnimalMaximum {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (X : Lattice → Ω → ℝ)
    (hX : ∀ v, Integrable (X v) ν) (m n : ℤ) (hmn : m < n) :
    Integrable (fun ω => diagonalAnimalMaximum m n hmn (fun v => X v ω)) ν := by
  classical
  let F := (diagonalAnimalFamily_finite m n).toFinset
  have hF : F.Nonempty :=
    (diagonalAnimalFamily_finite m n).toFinset_nonempty.mpr
      (diagonalAnimalFamily_nonempty m n hmn)
  have hsup : Integrable
      (F.sup' hF (fun s => fun ω => animalWeight (fun v => X v ω) s)) ν := by
    apply Finset.sup'_induction (p := fun f : Ω → ℝ => Integrable f ν)
      hF _ (fun _ hf _ hg => hf.sup hg)
    intro s _
    exact integrable_finsetSum s (fun v _ => hX v)
  have heq : (fun ω => diagonalAnimalMaximum m n hmn (fun v => X v ω)) =
      F.sup' hF (fun s => fun ω => animalWeight (fun v => X v ω) s) := by
    funext ω
    exact (Finset.sup'_apply hF
      (fun s => fun ω => animalWeight (fun v => X v ω) s) ω).symm
  rw [heq]
  exact hsup

/-- The actual positive square-root tail gives a finite positive first marginal
moment, without any condition on the negative tail. -/
theorem integrable_positivePart_of_positive_sqrt_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    Integrable (fun x : ℝ => max x 0) μ := by
  obtain ⟨C, _, hC⟩ := exists_positive_animalMaximum_mean_bound
  have hi := ((hC μ 1 (by norm_num)).2 hpos).1
  have hzero : Integrable (fun ω : Environment => max (ω 0) 0) (environmentLaw μ) := by
    simpa only [animalMaximum_one] using hi
  have hmap : Integrable (fun x : ℝ => max x 0)
      ((environmentLaw μ).map (fun ω : Environment => ω 0)) :=
    (integrable_map_measure
      (measurable_id.max measurable_const).aestronglyMeasurable
      (measurable_environment_eval 0).aemeasurable).2 hzero
  rwa [environmentLaw_map_eval] at hmap

/-- Every actual positive-part coordinate is integrable under the positive
square-root tail condition. -/
theorem integrable_positivePart_environment_eval
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (v : Lattice) :
    Integrable (fun ω : Environment => max (ω v) 0) (environmentLaw μ) := by
  have hmap : Integrable (fun x : ℝ => max x 0)
      ((environmentLaw μ).map (fun ω : Environment => ω v)) := by
    rw [environmentLaw_map_eval]
    exact integrable_positivePart_of_positive_sqrt_tail μ hpos
  exact hmap.comp_measurable (measurable_environment_eval v)

/-- Positive diagonal maxima on every proper integer interval have actual
finite moments under the positive tail condition alone. -/
theorem integrable_positive_diagonalAnimalMaximum
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (m n : ℤ) (hmn : m < n) :
    Integrable
      (fun ω : Environment => diagonalAnimalMaximum m n hmn (fun v => max (ω v) 0))
      (environmentLaw μ) :=
  integrable_diagonalAnimalMaximum (environmentLaw μ)
    (fun v ω => max (ω v) 0) (integrable_positivePart_environment_eval μ hpos) m n hmn

/-- One dimension-only constant bounds the actual origin diagonal maximum.
The finite-tail consequence supplies integrability before its real mean bound. -/
theorem exists_positive_diagonalAnimalMaximum_mean_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
      (n : ℕ) (hn : 1 ≤ n),
      (∫⁻ ω : Environment, ENNReal.ofReal
        (diagonalAnimalMaximum 0 (n : ℤ) (by omega) (fun v => max (ω v) 0))
        ∂environmentLaw μ) ≤ ENNReal.ofReal (C * n) *
          (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) ∧
      ((∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ →
        Integrable (fun ω : Environment =>
          diagonalAnimalMaximum 0 (n : ℤ) (by omega) (fun v => max (ω v) 0))
          (environmentLaw μ) ∧
        (∫ ω : Environment,
          diagonalAnimalMaximum 0 (n : ℤ) (by omega) (fun v => max (ω v) 0)
          ∂environmentLaw μ) ≤
          C * n * (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal) := by
  obtain ⟨C, hC, hmean⟩ := exists_positive_animalMaximum_mean_bound
  have hC3 : 0 < 3 * C := mul_pos (by norm_num) hC
  refine ⟨3 * C, hC3, ?_⟩
  intro μ _ n hn
  have hn3 : 1 ≤ 3 * n := by omega
  have hbound : (∫⁻ ω : Environment, ENNReal.ofReal
      (diagonalAnimalMaximum 0 (n : ℤ) (by omega) (fun v => max (ω v) 0))
      ∂environmentLaw μ) ≤ ENNReal.ofReal ((3 * C) * n) *
        (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) := by
    calc
      _ ≤ ∫⁻ ω : Environment, ENNReal.ofReal
          (animalMaximum (3 * n) hn3 (fun v => max (ω v) 0)) ∂environmentLaw μ := by
        apply lintegral_mono
        intro ω
        apply ENNReal.ofReal_le_ofReal
        exact diagonalAnimalMaximum_zero_le_animalMaximum n hn _ (fun v => le_max_right _ _)
      _ ≤ ENNReal.ofReal (C * ((3 * n : ℕ) : ℝ)) *
          (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) := (hmean μ (3 * n) hn3).1
      _ = _ := by
        have hscale : C * ((3 * n : ℕ) : ℝ) = (3 * C) * n := by
          push_cast
          ring
        rw [hscale]
  refine ⟨hbound, ?_⟩
  intro hpos
  have hm := measurable_diagonalAnimalMaximum
    (fun (v : Lattice) (ω : Environment) => max (ω v) 0)
    (fun v => (measurable_environment_eval v).max measurable_const) 0 (n : ℤ) (by omega)
  have hnn (ω : Environment) :
      0 ≤ diagonalAnimalMaximum 0 (n : ℤ) (by omega) (fun v => max (ω v) 0) :=
    diagonalAnimalMaximum_nonneg_of_forall_nonneg _ _ _ _ (fun v => le_max_right _ _)
  have hf : (∫⁻ ω : Environment, ENNReal.ofReal
      (diagonalAnimalMaximum 0 (n : ℤ) (by omega) (fun v => max (ω v) 0))
      ∂environmentLaw μ) < ∞ :=
    hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hpos)
  have hi : Integrable (fun ω : Environment =>
      diagonalAnimalMaximum 0 (n : ℤ) (by omega) (fun v => max (ω v) 0))
      (environmentLaw μ) :=
    ⟨hm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)).2 hf⟩
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnn)] at hbound
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpos.ne) hbound
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hnn), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg hC3.le (Nat.cast_nonneg n))]
    using hreal

/-- The same universal origin constant bounds every proper integer interval.
Both integrability and expectation transfer through the actual positive-part law. -/
theorem exists_positive_diagonalAnimalMaximum_interval_mean_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
      (m n : ℤ) (hmn : m < n),
      (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ →
        Integrable (fun ω : Environment =>
          diagonalAnimalMaximum m n hmn (fun v => max (ω v) 0)) (environmentLaw μ) ∧
        (∫ ω : Environment,
          diagonalAnimalMaximum m n hmn (fun v => max (ω v) 0) ∂environmentLaw μ) ≤
          C * (n - m : ℤ) *
            (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal := by
  obtain ⟨C, hC, hbase⟩ := exists_positive_diagonalAnimalMaximum_mean_bound
  refine ⟨C, hC, ?_⟩
  intro μ _ m n hmn hpos
  let s : ℕ := (n - m).toNat
  have hs : (s : ℤ) = n - m := by omega
  have hsn : 1 ≤ s := by omega
  have hendpoint : (s : ℤ) + m = n := by omega
  have hlaw : ProbabilityTheory.IdentDistrib
      (fun ω : Environment => diagonalAnimalMaximum m n hmn (fun v => max (ω v) 0))
      (fun ω : Environment => diagonalAnimalMaximum 0 (s : ℤ) (by omega)
        (fun v => max (ω v) 0)) (environmentLaw μ) (environmentLaw μ) := by
    simpa only [zero_add, hendpoint] using
      diagonalAnimalMaximum_comp_identDistrib μ (fun x : ℝ => max x 0)
        (measurable_id.max measurable_const) 0 (s : ℤ) m (by omega)
  obtain ⟨hi, hb⟩ := (hbase μ s hsn).2 hpos
  refine ⟨hlaw.integrable_iff.mpr hi, ?_⟩
  rw [hlaw.integral_eq]
  have hsreal : (s : ℝ) = ((n - m : ℤ) : ℝ) := by exact_mod_cast hs
  simpa only [hsreal] using hb

end LPPDifferentiability
