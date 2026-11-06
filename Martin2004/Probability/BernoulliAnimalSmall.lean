/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.Family
public import Martin2004.Probability.AnimalMaximum
public import ProbabilityBasics.Analysis.BernoulliScales
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! First moments and the small-parameter branch of Martin's Bernoulli animal
estimate. Independence is unnecessary in this branch. -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace LPPDifferentiability

/-- A measurable almost surely zero-one variable is genuinely integrable. -/
theorem integrable_of_ae_zero_or_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Measurable X) (h01 : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    Integrable X μ := by
  apply Integrable.of_bound hX.aestronglyMeasurable 1
  filter_upwards [h01] with ω hω
  rcases hω with hzero | hone
  · simp only [hzero, norm_zero, zero_le_one]
  · simp only [hone, norm_one, le_refl]

/-- The first moment is the actual probability of the one event. -/
theorem integral_of_ae_zero_or_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Measurable X) (h01 : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    ∫ ω, X ω ∂μ = μ.real {ω | X ω = 1} := by
  let A : Set Ω := {ω | X ω = 1}
  have hA : MeasurableSet A := measurableSet_eq_fun hX measurable_const
  have hEq : X =ᵐ[μ] A.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [h01] with ω hω
    rcases hω with hzero | hone
    · simp [A, hzero]
    · simp [A, hone]
  have hInd : Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hA
  have hInt : Integrable X μ := hInd.congr hEq.symm
  calc
    ∫ ω, X ω ∂μ = ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
      integral_congr_ae hEq
    _ = μ.real A := by rw [integral_indicator_const (1 : ℝ) hA]; simp

/-- A finite sum of measurable zero-one sites has a genuine finite first moment. -/
theorem integrable_finset_sum_of_ae_zero_or_one {Ω V : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Finset V) (X : V → Ω → ℝ)
    (hX : ∀ v ∈ U, Measurable (X v))
    (h01 : ∀ v ∈ U, ∀ᵐ ω ∂μ, X v ω = 0 ∨ X v ω = 1) :
    Integrable (fun ω => ∑ v ∈ U, X v ω) μ := by
  exact integrable_finsetSum U (fun v hv =>
    integrable_of_ae_zero_or_one μ (X v) (hX v hv) (h01 v hv))

/-- Linearity computes the actual box sum's mean without any independence. -/
theorem integral_finset_sum_of_ae_zero_or_one {Ω V : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Finset V) (X : V → Ω → ℝ) (p : ℝ)
    (hX : ∀ v ∈ U, Measurable (X v))
    (h01 : ∀ v ∈ U, ∀ᵐ ω ∂μ, X v ω = 0 ∨ X v ω = 1)
    (hp : ∀ v ∈ U, μ.real {ω | X v ω = 1} = p) :
    ∫ ω, ∑ v ∈ U, X v ω ∂μ = (U.card : ℝ) * p := by
  rw [integral_finsetSum U (fun v hv =>
    integrable_of_ae_zero_or_one μ (X v) (hX v hv) (h01 v hv))]
  calc
    ∑ v ∈ U, ∫ ω, X v ω ∂μ = ∑ _v ∈ U, p := by
      apply Finset.sum_congr rfl
      intro v hv
      exact (integral_of_ae_zero_or_one μ (X v) (hX v hv)
        (h01 v hv)).trans (hp v hv)
    _ = (U.card : ℝ) * p := by simp only [Finset.sum_const, nsmul_eq_mul]

/-- Nonnegative site weights bound each actual animal by its containing box. -/
theorem animal_sum_le_integerBox_sum (n : ℕ) (s : Finset Lattice)
    (hs : s ∈ animalFamily n) (w : Lattice → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∑ v ∈ s, w v ≤ ∑ v ∈ integerBox 0 (n - 1), w v := by
  obtain ⟨hconn, hzero, hcard⟩ := (mem_animalFamily_iff n s).mp hs
  have hsub : s ⊆ integerBox 0 (n - 1) := by
    simpa only [hcard] using animal_subset_integerBox s hconn hzero
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => hw v)

/-- The exact animal-radius box has at most `(2n)^2` sites. -/
theorem integerBox_animalRadius_card_le (n : ℕ) (hn : 1 ≤ n) :
    ((integerBox (0 : Lattice) (n - 1)).card : ℝ) ≤ (2 * (n : ℝ)) ^ 2 := by
  rw [integerBox_card]
  have hbase : 2 * (n - 1) + 1 ≤ 2 * n := by omega
  have hpow : (2 * (n - 1) + 1) ^ 2 ≤ (2 * n) ^ 2 := Nat.pow_le_pow_left hbase 2
  exact_mod_cast hpow

private theorem ae_forall_nonneg_of_ae_zero_or_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Lattice → Ω → ℝ)
    (h01 : ∀ v, ∀ᵐ ω ∂μ, X v ω = 0 ∨ X v ω = 1) :
    ∀ᵐ ω ∂μ, ∀ v, 0 ≤ X v ω := by
  filter_upwards [ae_all_iff.2 h01] with ω hω
  intro v
  rcases hω v with hzero | hone
  · simp only [hzero, le_refl]
  · simp only [hone, zero_le_one]

/-- The actual finite-family maximum is bounded by the containing box sum. -/
theorem animalMaximum_le_integerBox_sum (n : ℕ) (hn : 1 ≤ n)
    (w : Lattice → ℝ) (hw : ∀ v, 0 ≤ w v) :
    animalMaximum n hn w ≤ ∑ v ∈ integerBox 0 (n - 1), w v := by
  apply (animalMaximum_le_iff n hn w _).2
  intro s hs
  exact animal_sum_le_integerBox_sum n s hs w hw

/-- The actual maximum of measurable zero-one sites has a finite first moment. -/
theorem integrable_animalMaximum_of_ae_zero_or_one {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 1 ≤ n) (X : Lattice → Ω → ℝ)
    (hX : ∀ v, Measurable (X v))
    (h01 : ∀ v, ∀ᵐ ω ∂μ, X v ω = 0 ∨ X v ω = 1) :
    Integrable (fun ω => animalMaximum n hn (fun v => X v ω)) μ := by
  have hbox := integrable_finset_sum_of_ae_zero_or_one μ
    (integerBox (0 : Lattice) (n - 1)) X
    (fun v _ => hX v) (fun v _ => h01 v)
  have hgood := ae_forall_nonneg_of_ae_zero_or_one μ X h01
  apply hbox.mono_nonneg
    (measurable_animalMaximum X hX n hn).aestronglyMeasurable
  · filter_upwards [hgood] with ω hω
    exact animalMaximum_nonneg_of_forall_nonneg n hn (fun v => X v ω) hω
  · filter_upwards [hgood] with ω hω
    exact animalMaximum_le_integerBox_sum n hn (fun v => X v ω) hω

/-- The first-moment comparison of the animal estimate, with the exact box cardinality. -/
theorem integral_animalMaximum_le_box_card_mul {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 1 ≤ n) (X : Lattice → Ω → ℝ) (p : ℝ)
    (hX : ∀ v, Measurable (X v))
    (h01 : ∀ v, ∀ᵐ ω ∂μ, X v ω = 0 ∨ X v ω = 1)
    (hp : ∀ v, μ.real {ω | X v ω = 1} = p) :
    (∫ ω, animalMaximum n hn (fun v => X v ω) ∂μ) ≤
      ((integerBox (0 : Lattice) (n - 1)).card : ℝ) * p := by
  have hmax := integrable_animalMaximum_of_ae_zero_or_one μ n hn X hX h01
  have hbox := integrable_finset_sum_of_ae_zero_or_one μ
    (integerBox (0 : Lattice) (n - 1)) X
    (fun v _ => hX v) (fun v _ => h01 v)
  have hdom : ∀ᵐ ω ∂μ,
      animalMaximum n hn (fun v => X v ω) ≤
        ∑ v ∈ integerBox 0 (n - 1), X v ω := by
    filter_upwards [ae_forall_nonneg_of_ae_zero_or_one μ X h01] with ω hω
    exact animalMaximum_le_integerBox_sum n hn (fun v => X v ω) hω
  calc
    (∫ ω, animalMaximum n hn (fun v => X v ω) ∂μ) ≤
        ∫ ω, ∑ v ∈ integerBox 0 (n - 1), X v ω ∂μ :=
      integral_mono_ae hmax hbox hdom
    _ = ((integerBox (0 : Lattice) (n - 1)).card : ℝ) * p :=
      integral_finset_sum_of_ae_zero_or_one μ
        (integerBox (0 : Lattice) (n - 1)) X p
        (fun v _ => hX v) (fun v _ => h01 v) (fun v _ => hp v)

/-- Martin's planar small-parameter bound for the actual animal maximum,
including parameter zero. The conclusion records its genuine integrability. -/
theorem bernoulli_animal_small_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (hn : 1 ≤ n)
    (X : Lattice → Ω → ℝ) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hX : ∀ v, Measurable (X v))
    (h01 : ∀ v, ∀ᵐ ω ∂μ, X v ω = 0 ∨ X v ω = 1)
    (hlaw : ∀ v, μ.real {ω | X v ω = 1} = p)
    (ha : (n : ℝ) * Real.sqrt p ≤ 1) :
    Integrable (fun ω => animalMaximum n hn (fun v => X v ω)) μ ∧
      (∫ ω, animalMaximum n hn (fun v => X v ω) ∂μ) ≤
        4 * (n : ℝ) * Real.sqrt p := by
  refine ⟨integrable_animalMaximum_of_ae_zero_or_one μ n hn X hX h01, ?_⟩
  calc
    (∫ ω, animalMaximum n hn (fun v => X v ω) ∂μ) ≤
        ((integerBox (0 : Lattice) (n - 1)).card : ℝ) * p :=
      integral_animalMaximum_le_box_card_mul μ n hn X p hX h01 hlaw
    _ ≤ (2 * (n : ℝ)) ^ 2 * p :=
      mul_le_mul_of_nonneg_right (integerBox_animalRadius_card_le n hn) hp.1
    _ ≤ 4 * (n : ℝ) * Real.sqrt p :=
      bernoulli_small_scale_square_bound n p hn hp.1 ha

end LPPDifferentiability
