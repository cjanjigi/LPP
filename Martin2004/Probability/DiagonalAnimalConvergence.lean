/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.DiagonalAnimalLaw
public import LPP_Foundations.Model.Animals.DiagonalSuperadditive
public import ProbabilityBasics.Probability.LiggettErgodic
public import Martin2004.Probability.DiagonalAnimalMean

/-!
# Forward limits of Martin's diagonal animal maxima

Only proper intervals are used. The total array required by the generic
Liggett theorem is a local proof device; its unused slots are filled with zero.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace LPPDifferentiability

/-- A nonnegative marginal gives simultaneous nonnegativity of all sites. -/
theorem ae_environment_nonneg_of_ae_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ z : Lattice, 0 ≤ ω z := by
  rw [ae_all_iff]
  intro z
  have hm : ∀ᵐ x ∂(environmentLaw μ).map (fun ω : Environment => ω z), 0 ≤ x := by
    rw [environmentLaw_map_eval]
    exact hμ
  exact ae_of_ae_map (measurable_environment_eval z).aemeasurable hm

/-- Each actual proper-interval maximum is nonnegative almost surely. -/
theorem ae_diagonalAnimalMaximum_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (m n : ℤ) (hmn : m < n) :
    ∀ᵐ ω ∂environmentLaw μ, 0 ≤ diagonalAnimalMaximum m n hmn ω := by
  filter_upwards [ae_environment_nonneg_of_ae_nonneg μ hμ] with ω hω
  exact diagonalAnimalMaximum_nonneg_of_forall_nonneg m n hmn ω hω

/-- Internal application of negated Liggett to the actual proper-interval Q.
The final source theorem discharges the finite means and linear upper bound. -/
theorem exists_diagonalAnimalMaximum_forward_convergence_of_expected_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (hint : ∀ n : ℕ, (hn : 0 < n) → Integrable
      (fun ω : Environment => diagonalAnimalMaximum 0 (n : ℤ) (by omega) ω)
      (environmentLaw μ))
    (c : ℝ)
    (hupper : ∀ n : ℕ, (hn : 0 < n) →
      (∫ ω, diagonalAnimalMaximum 0 (n : ℤ) (by omega) ω ∂environmentLaw μ) ≤
        c * (n : ℝ)) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ c ∧
      Tendsto (fun n : ℕ =>
        (∫ ω, diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω
          ∂environmentLaw μ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q) ∧
      q = sSup (range (fun n : ℕ =>
        (∫ ω, diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω
          ∂environmentLaw μ) / ((n + 1 : ℕ) : ℝ))) ∧
      (∀ᵐ ω ∂environmentLaw μ, Tendsto (fun n : ℕ =>
        diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω /
          ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q)) ∧
      Tendsto (fun n : ℕ => ∫ ω,
        |diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω /
          ((n + 1 : ℕ) : ℝ) - q| ∂environmentLaw μ) atTop (𝓝 0) := by
  classical
  let A : ℕ → ℕ → Environment → ℝ := fun m n ω =>
    if h : m < n then -diagonalAnimalMaximum (m : ℤ) (n : ℤ) (by omega) ω else 0
  have hA (m n : ℕ) (h : m < n) (ω : Environment) :
      A m n ω = -diagonalAnimalMaximum (m : ℤ) (n : ℤ) (by omega) ω := by
    simp only [A, dite_eq_left h]
  have hAf (m n : ℕ) (h : m < n) :
      A m n = fun ω => -diagonalAnimalMaximum (m : ℤ) (n : ℤ) (by omega) ω :=
    funext (hA m n h)
  have hneg : Measurable (fun f : ℕ → ℝ => fun j => -f j) :=
    Measurable.of_eval (fun j => (measurable_pi_apply j).neg)
  have hmeasQ (m n : ℤ) (h : m < n) : Measurable
      (fun ω : Environment => diagonalAnimalMaximum m n h ω) :=
    measurable_diagonalAnimalMaximum (fun (v : Lattice) (ω : Environment) => ω v)
      (fun v => measurable_pi_apply v) m n h
  have hadj (m : ℕ) : IdentDistrib
      (fun ω (j : ℕ) => A (m + 1) (m + 1 + (j + 1)) ω)
      (fun ω (j : ℕ) => A m (m + (j + 1)) ω)
      (environmentLaw μ) (environmentLaw μ) := by
    have h := (diagonalAnimalMaximum_column_identDistrib μ (m : ℤ)).comp hneg
    simpa only [Function.comp_def, A, show ∀ j : ℕ, m + 1 < m + 1 + (j + 1) by omega,
      show ∀ j : ℕ, m < m + (j + 1) by omega, ↓reduceDIte, Nat.cast_add,
      Nat.cast_one] using h
  have hsem (k : ℕ) (hk : 0 < k) : Function.Semiconj
      (fun ω : Environment => fun j : ℕ => A ((j + 1) * k) ((j + 2) * k) ω)
      (fun ω : Environment => fun z => ω (((k : ℤ), (k : ℤ)) + z))
      sequenceShift := by
    intro ω
    funext j
    have h := congrFun (diagonalAnimalMaximum_tailBlocks_semiconj k hk ω) j
    change A ((j + 1) * k) ((j + 2) * k) _ =
      A (((j + 1) + 1) * k) (((j + 1) + 2) * k) ω
    rw [hA _ _ (Nat.mul_lt_mul_of_pos_right (by omega) hk),
      hA _ _ (Nat.mul_lt_mul_of_pos_right (by omega) hk)]
    exact congrArg Neg.neg h
  have hmeasB (k : ℕ) (hk : 0 < k) : Measurable
      (fun ω : Environment => fun j : ℕ => A ((j + 1) * k) ((j + 2) * k) ω) := by
    apply Measurable.of_eval
    intro j
    rw [hAf _ _ (Nat.mul_lt_mul_of_pos_right (by omega) hk)]
    exact (hmeasQ _ _ _).neg
  have hmp (k : ℕ) (hk : 0 < k) : MeasurePreserving
      (fun ω : Environment => fun j : ℕ => A ((j + 1) * k) ((j + 2) * k) ω)
      (environmentLaw μ) _ := ⟨hmeasB k hk, rfl⟩
  have herg (k : ℕ) (hk : 0 < k) : Ergodic sequenceShift
      ((environmentLaw μ).map (fun ω : Environment => fun j : ℕ =>
        A ((j + 1) * k) ((j + 2) * k) ω)) := by
    have hn : ((k : ℤ), (k : ℤ)) ≠ (0 : Lattice) := by
      intro h
      have hh : (k : ℤ) = 0 := congrArg Prod.fst h
      have : k = 0 := Int.natCast_inj.mp hh
      omega
    exact (hmp k hk).ergodic_of_ergodic_semiconj
      (ergodic_environment_translation μ ((k : ℤ), (k : ℤ)) hn)
      measurable_sequenceShift (hsem k hk)
  have hstat (k : ℕ) (hk : 0 < k) : IdentDistrib
      (fun ω (j : ℕ) => A ((j + 2) * k) ((j + 3) * k) ω)
      (fun ω (j : ℕ) => A ((j + 1) * k) ((j + 2) * k) ω)
      (environmentLaw μ) (environmentLaw μ) := by
    have hs := (hmp k hk).of_semiconj
      (measurePreserving_environment_translation μ ((k : ℤ), (k : ℤ)))
      (hsem k hk) measurable_sequenceShift
    have hshift : (fun ω (j : ℕ) => A ((j + 2) * k) ((j + 3) * k) ω) =
        (fun ω => sequenceShift (fun j : ℕ => A ((j + 1) * k) ((j + 2) * k) ω)) := by
      funext ω j
      change A ((j + 2) * k) ((j + 3) * k) ω =
        A (((j + 1) + 1) * k) (((j + 1) + 2) * k) ω
      rw [show j + 1 + 1 = j + 2 by omega, show j + 1 + 2 = j + 3 by omega]
    refine ⟨?_, (hmeasB k hk).aemeasurable, ?_⟩
    · rw [hshift]
      exact (measurable_sequenceShift.comp (hmeasB k hk)).aemeasurable
    · rw [hshift]
      change (environmentLaw μ).map
        (sequenceShift ∘ (fun ω : Environment => fun j : ℕ =>
          A ((j + 1) * k) ((j + 2) * k) ω)) = _
      rw [← Measure.map_map measurable_sequenceShift (hmeasB k hk), hs.map_eq]
  obtain ⟨γ, hmean, hinf, hae, hL1⟩ := exists_liggett_ergodic_convergence
    (environmentLaw μ) A
    (fun n hn => by
      rw [hAf 0 n hn]
      exact (hmeasQ _ _ _).neg)
    (fun n hn => by simpa only [hAf 0 n hn, Nat.cast_zero] using (hint n hn).fun_neg)
    c (fun n hn => by simpa only [hA 0 n hn, Nat.cast_zero, integral_neg] using neg_le_neg (hupper n hn))
    (fun m n hm hmn => ae_of_all _ fun ω => by
      rw [hA 0 n (by omega), hA 0 m hm, hA m n hmn]
      simp only [Nat.cast_zero]
      have h := diagonalAnimalMaximum_superadditive (by omega : (0 : ℤ) < m)
        (by omega : (m : ℤ) < n) ω
      linarith only [h]) hadj hstat herg
  have hmean' : Tendsto (fun n : ℕ =>
      (∫ ω, diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω
        ∂environmentLaw μ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (-γ)) := by
    simpa only [hA 0 _ (Nat.zero_lt_succ _), Nat.cast_zero, integral_neg, neg_div, neg_neg] using hmean.neg
  refine ⟨-γ, ?_, ?_, hmean', ?_, ?_, ?_⟩
  · exact ge_of_tendsto hmean' (Eventually.of_forall (fun n => div_nonneg
      (integral_nonneg_of_ae (ae_diagonalAnimalMaximum_nonneg μ hμ 0
        ((n + 1 : ℕ) : ℤ) (by omega)))
      (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))))
  · apply le_of_tendsto hmean'
    exact Eventually.of_forall (fun n => (div_le_iff₀ (by positivity :
      (0 : ℝ) < ((n + 1 : ℕ) : ℝ))).mpr (hupper (n + 1) (by omega)))
  · rw [hinf, ← Real.sSup_neg]
    congr 1
    ext x
    simp only [Set.mem_neg, mem_range, hA 0 _ (Nat.zero_lt_succ _), Nat.cast_zero, integral_neg, neg_div]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by linarith only [hn]⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by linarith only [hn]⟩
  · filter_upwards [hae] with ω hω
    simpa only [hA 0 _ (Nat.zero_lt_succ _), Nat.cast_zero, neg_div, neg_neg] using hω.neg
  · have habs (x : ℝ) : |(-x) - γ| = |x - (-γ)| := by
      rw [sub_neg_eq_add, ← abs_neg]
      congr 1
      ring
    simpa only [hA 0 _ (Nat.zero_lt_succ _), Nat.cast_zero, neg_div, habs] using hL1

/-- Martin's finite-tail forward conclusion: one dimension-only constant works
for every nonnegative marginal law. The same finite rate gives the expected
limit, the supremum of positive expected rates, and actual-space AE and L1
convergence. Only the positive square-root tail is required. -/
theorem exists_diagonalAnimalMaximum_forward_convergence :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      (∀ᵐ x ∂μ, 0 ≤ x) →
      (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ →
      ∃ q : ℝ, 0 ≤ q ∧
        q ≤ C * (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal ∧
        Tendsto (fun n : ℕ =>
          (∫ ω, diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω
            ∂environmentLaw μ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q) ∧
        q = sSup (range (fun n : ℕ =>
          (∫ ω, diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω
            ∂environmentLaw μ) / ((n + 1 : ℕ) : ℝ))) ∧
        (∀ᵐ ω ∂environmentLaw μ, Tendsto (fun n : ℕ =>
          diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω /
            ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q)) ∧
        Tendsto (fun n : ℕ => ∫ ω,
          |diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω /
            ((n + 1 : ℕ) : ℝ) - q| ∂environmentLaw μ) atTop (𝓝 0) := by
  obtain ⟨C, hC, hmeans⟩ := exists_positive_diagonalAnimalMaximum_mean_bound
  refine ⟨C, hC, ?_⟩
  intro μ _ hμ hpos
  have heq (n : ℕ) (hn : 0 < n) :
      (fun ω : Environment => diagonalAnimalMaximum 0 (n : ℤ) (by omega)
        (fun v => max (ω v) 0)) =ᵐ[environmentLaw μ]
      (fun ω : Environment => diagonalAnimalMaximum 0 (n : ℤ) (by omega) ω) := by
    filter_upwards [ae_environment_nonneg_of_ae_nonneg μ hμ] with ω hω
    have hfield : (fun v => max (ω v) 0) = ω :=
      funext (fun v => max_eq_left (hω v))
    rw [hfield]
  apply exists_diagonalAnimalMaximum_forward_convergence_of_expected_bound μ hμ
    (fun n hn => ((hmeans μ n (by omega)).2 hpos).1.congr (heq n hn))
    (C * (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal)
  intro n hn
  calc
    _ = ∫ ω, diagonalAnimalMaximum 0 (n : ℤ) (by omega)
        (fun v => max (ω v) 0) ∂environmentLaw μ := (integral_congr_ae (heq n hn)).symm
    _ ≤ C * n * (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal :=
      ((hmeans μ n (by omega)).2 hpos).2
    _ = _ := by ring

end LPPDifferentiability
