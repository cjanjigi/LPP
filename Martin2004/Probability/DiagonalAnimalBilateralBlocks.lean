/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.BilateralBirkhoff
public import ProbabilityBasics.Probability.BirkhoffErgodic
public import Martin2004.Probability.DiagonalAnimalLaw
public import Martin2004.Probability.DiagonalAnimalMean
public import LPP_Foundations.Probability.PassageIntegrable
public import LPP_Foundations.Probability.TranslationEquiv
import Mathlib.Data.Int.Interval

/-! # Bilateral averages of actual signed diagonal blocks

For positive block size every interval used below is proper, including the
negative blocks. The empty average is zero; no diagonal maximum is evaluated.
The only moment premise is the first moment of the marginal law.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace LPPDifferentiability

/-- The signed maximum on the proper block with integer index `j`. -/
noncomputable def diagonalAnimalBlock (k : ℕ) (hk : 0 < k) (j : ℤ)
    (ω : Environment) : ℝ :=
  diagonalAnimalMaximum (j * k) ((j + 1) * k)
    (by
      have hkp : (0 : ℤ) < k := by exact_mod_cast hk
      nlinarith) ω

/-- The zeroth block is the actual origin maximum. -/
@[simp] theorem diagonalAnimalBlock_zero (k : ℕ) (hk : 0 < k) (ω : Environment) :
    diagonalAnimalBlock k hk 0 ω =
      diagonalAnimalMaximum 0 (k : ℤ) (by exact_mod_cast hk) ω := by
  simp only [diagonalAnimalBlock, zero_mul, zero_add, one_mul]

/-- Exactly the `2r` blocks indexed by `-r, ..., r-1`, divided by `2r`. -/
noncomputable def diagonalAnimalBilateralBlockAverage (k : ℕ) (hk : 0 < k)
    (r : ℕ) (ω : Environment) : ℝ :=
  (∑ j ∈ Finset.Ico (-(r : ℤ)) (r : ℤ), diagonalAnimalBlock k hk j ω) /
    (2 * (r : ℝ))

@[simp] theorem diagonalAnimalBilateralBlockAverage_zero (k : ℕ) (hk : 0 < k)
    (ω : Environment) : diagonalAnimalBilateralBlockAverage k hk 0 ω = 0 := by
  simp only [diagonalAnimalBilateralBlockAverage, Nat.cast_zero, neg_zero,
    Finset.Ico_self, Finset.sum_empty, mul_zero, div_zero]

/-- Reindex the literal integer interval by its `2r` positions. -/
theorem sum_diagonalAnimalBlock_Ico_eq_range (k : ℕ) (hk : 0 < k)
    (r : ℕ) (ω : Environment) :
    (∑ j ∈ Finset.Ico (-(r : ℤ)) (r : ℤ), diagonalAnimalBlock k hk j ω) =
      ∑ j ∈ Finset.range (2 * r),
        diagonalAnimalBlock k hk (-(r : ℤ) + (j : ℤ)) ω := by
  symm
  apply Finset.sum_nbij' (fun j : ℕ => -(r : ℤ) + (j : ℤ))
    (fun j : ℤ => (j + (r : ℤ)).toNat)
  · intro j hj; simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Ico]; omega
  · intro j hj; simp only [Finset.mem_Ico] at hj
    simp only [Finset.mem_range]; omega
  · intro j _; omega
  · intro j hj; simp only [Finset.mem_Ico] at hj; omega
  · intro j _; rfl

/-- The same average in the consecutive range convention used for block bounds. -/
theorem diagonalAnimalBilateralBlockAverage_eq_range (k : ℕ) (hk : 0 < k)
    (r : ℕ) (ω : Environment) :
    diagonalAnimalBilateralBlockAverage k hk r ω =
      (∑ j ∈ Finset.range (2 * r),
        diagonalAnimalBlock k hk (-(r : ℤ) + (j : ℤ)) ω) / (2 * (r : ℝ)) := by
  rw [diagonalAnimalBilateralBlockAverage, sum_diagonalAnimalBlock_Ico_eq_range]

private theorem diagonalAnimalBlock_iterate (k : ℕ) (hk : 0 < k)
    (a : ℤ) (n : ℕ) (ω : Environment) :
    diagonalAnimalBlock k hk 0
      (((environmentTranslationEquiv (a, a) : Environment → Environment)^[n]) ω) =
      diagonalAnimalMaximum ((n : ℤ) * a) ((k : ℤ) + (n : ℤ) * a)
        (lt_add_of_pos_left _ (Int.natCast_pos.mpr hk)) ω := by
  have heq : (((environmentTranslationEquiv (a, a) : Environment → Environment)^[n]) ω) =
      fun z => ω (((n : ℤ) * a, (n : ℤ) * a) + z) := by
    have ht : (environmentTranslationEquiv (a, a) : Environment → Environment) =
        (fun η z => η ((a, a) + z)) := by
      funext η z
      exact environmentTranslationEquiv_apply (a, a) η z
    rw [ht]
    funext z
    simpa only [Prod.smul_mk, Int.nsmul_eq_mul] using
      environment_translate_iterate ω (a, a) n z
  rw [heq]
  simpa only [diagonalAnimalBlock, zero_mul, zero_add, one_mul] using
    diagonalAnimalMaximum_translate 0 k ((n : ℤ) * a) (by exact_mod_cast hk) ω

private theorem sum_integer_centered (f : ℤ → ℝ) (r : ℕ) :
    (∑ j ∈ Finset.Ico (-(r : ℤ)) (r : ℤ), f j) =
      (∑ j ∈ Finset.range r, f (j : ℤ)) +
        ∑ j ∈ Finset.range r, f (-((j : ℤ) + 1)) := by
  have hp : (∑ j ∈ Finset.range r, f (j : ℤ)) =
      ∑ j ∈ Finset.Ico (0 : ℤ) (r : ℤ), f j := by
    apply Finset.sum_nbij' (fun j : ℕ => (j : ℤ)) Int.toNat
    · intro j hj; simp only [Finset.mem_range] at hj
      simp only [Finset.mem_Ico]; omega
    · intro j hj; simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_range]; omega
    · intro j _; omega
    · intro j hj; simp only [Finset.mem_Ico] at hj; omega
    · intro j _; rfl
  have hm : (∑ j ∈ Finset.range r, f (-((j : ℤ) + 1))) =
      ∑ j ∈ Finset.Ico (-(r : ℤ)) (0 : ℤ), f j := by
    apply Finset.sum_nbij' (fun j : ℕ => -((j : ℤ) + 1))
      (fun j : ℤ => (-j - 1).toNat)
    · intro j hj; simp only [Finset.mem_range] at hj
      simp only [Finset.mem_Ico]; omega
    · intro j hj; simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_range]; omega
    · intro j _; omega
    · intro j hj; simp only [Finset.mem_Ico] at hj; omega
    · intro j _; rfl
  rw [hp, hm, add_comm, ← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive _ _ _),
    Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]

/-- Finite identification with the centered Birkhoff convention.
The inverse terms have indices `-1, ..., -r`. -/
theorem diagonalAnimalBilateralBlockAverage_eq_centered (k : ℕ) (hk : 0 < k)
    (r : ℕ) (ω : Environment) :
    diagonalAnimalBilateralBlockAverage k hk r ω =
      centeredBirkhoffAverage (environmentTranslationEquiv ((k : ℤ), (k : ℤ)))
        (diagonalAnimalBlock k hk 0) r ω := by
  have hf (j : ℕ) : diagonalAnimalBlock k hk 0
      (((environmentTranslationEquiv ((k : ℤ), (k : ℤ)) : Environment → Environment)^[j]) ω) =
        diagonalAnimalBlock k hk (j : ℤ) ω := by
    rw [diagonalAnimalBlock_iterate]
    simp only [diagonalAnimalBlock, add_mul, one_mul]
    congr 1; ring
  have hb (j : ℕ) : diagonalAnimalBlock k hk 0
      (((((environmentTranslationEquiv ((k : ℤ), (k : ℤ))).symm) :
        Environment → Environment)^[j + 1]) ω) =
        diagonalAnimalBlock k hk (-((j : ℤ) + 1)) ω := by
    have hs : ((environmentTranslationEquiv ((k : ℤ), (k : ℤ))).symm :
        Environment → Environment) =
        (environmentTranslationEquiv (-(k : ℤ), -(k : ℤ)) : Environment → Environment) := rfl
    rw [hs, diagonalAnimalBlock_iterate]
    simp only [diagonalAnimalBlock, Nat.cast_add, Nat.cast_one]
    congr 1 <;> ring
  simp only [diagonalAnimalBilateralBlockAverage, sum_integer_centered,
    centeredBirkhoffAverage, backwardBirkhoffAverage_eq_sum, birkhoffAverage,
    birkhoffSum, smul_eq_mul, hf, hb]
  ring

/-- The actual signed block at the origin has a finite moment. -/
theorem integrable_diagonalAnimalBlock (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (k : ℕ) (hk : 0 < k) (j : ℤ) :
    Integrable (diagonalAnimalBlock k hk j) (environmentLaw μ) :=
  integrable_diagonalAnimalMaximum (environmentLaw μ) (fun v ω => ω v)
    (integrable_environment_eval μ hμ) _ _ _

/-- Every centered finite average and every error about its actual mean is
integrable, including the empty average. -/
theorem integrable_diagonalAnimalBilateralBlockAverage_error
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (k : ℕ) (hk : 0 < k) (r : ℕ) :
    Integrable (diagonalAnimalBilateralBlockAverage k hk r) (environmentLaw μ) ∧
    Integrable (fun ω => |diagonalAnimalBilateralBlockAverage k hk r ω -
      ∫ η, diagonalAnimalBlock k hk 0 η ∂environmentLaw μ|) (environmentLaw μ) := by
  have hi : Integrable (diagonalAnimalBilateralBlockAverage k hk r) (environmentLaw μ) := by
    have heq : diagonalAnimalBilateralBlockAverage k hk r =
        centeredBirkhoffAverage (environmentTranslationEquiv ((k : ℤ), (k : ℤ)))
          (diagonalAnimalBlock k hk 0) r :=
      funext (diagonalAnimalBilateralBlockAverage_eq_centered k hk r)
    rw [heq]
    exact integrable_centeredBirkhoffAverage
      (measurePreserving_environmentTranslationEquiv μ ((k : ℤ), (k : ℤ)))
      (integrable_diagonalAnimalBlock μ hμ k hk 0) r
  exact ⟨hi, (hi.sub (integrable_const _)).abs⟩

/-- Actual signed proper-interval bilateral block averages converge almost
surely and in integral absolute error to the same expectation `E Q(0,k)`.
Independence gives ergodicity of translation by `(k,k)` directly. -/
theorem diagonalAnimalBilateralBlockAverage_tendsto
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (k : ℕ) (hk : 0 < k) :
    (∀ᵐ ω ∂environmentLaw μ, Tendsto
      (fun r : ℕ => diagonalAnimalBilateralBlockAverage k hk r ω) atTop
      (𝓝 (∫ η, diagonalAnimalBlock k hk 0 η ∂environmentLaw μ))) ∧
    Tendsto (fun r : ℕ => ∫ ω,
      |diagonalAnimalBilateralBlockAverage k hk r ω -
        ∫ η, diagonalAnimalBlock k hk 0 η ∂environmentLaw μ| ∂environmentLaw μ)
      atTop (𝓝 0) := by
  let T := environmentTranslationEquiv ((k : ℤ), (k : ℤ))
  let f := diagonalAnimalBlock k hk 0
  have hi := integrable_diagonalAnimalBlock μ hμ k hk 0
  have hm : Measurable f := measurable_diagonalAnimalMaximum
    (fun (v : Lattice) (ω : Environment) => ω v) (fun v => measurable_environment_eval v) _ _ _
  have hT : MeasurePreserving T (environmentLaw μ) (environmentLaw μ) :=
    measurePreserving_environmentTranslationEquiv μ _
  have hn : ((k : ℤ), (k : ℤ)) ≠ (0 : Lattice) := by
    intro h
    have hfst := congrArg Prod.fst h
    change (k : ℤ) = 0 at hfst
    omega
  have he : Ergodic T (environmentLaw μ) := ergodic_environment_translation μ _ hn
  obtain ⟨g, _, hgi, hga, hginv, hmean, hgL1⟩ := exists_birkhoffL1 hT hm hi
  have hgc := ae_eq_integral_of_ergodic_invariant he hgi hginv
  have hfa : ∀ᵐ ω ∂environmentLaw μ, Tendsto
      (fun r : ℕ => birkhoffAverage ℝ T f r ω) atTop
      (𝓝 (∫ η, f η ∂environmentLaw μ)) := by
    filter_upwards [hga, hgc] with ω hω heq
    simpa only [heq, hmean] using hω
  have hfL1 : Tendsto (fun r : ℕ => ∫ ω,
      |birkhoffAverage ℝ T f r ω - ∫ η, f η ∂environmentLaw μ| ∂environmentLaw μ)
      atTop (𝓝 0) := by
    apply hgL1.congr'
    exact Eventually.of_forall fun r => integral_congr_ae (hgc.mono fun ω hω => by
      dsimp only at hω ⊢
      rw [hω, hmean])
  simpa only [diagonalAnimalBilateralBlockAverage_eq_centered] using
    centeredBirkhoffAverage_tendsto_const hT hi _ hfa hfL1

end LPPDifferentiability
