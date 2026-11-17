/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Probability.PassageMeasurable
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Martin2004.Probability.AnimalPositiveMean
import Martin2004.Probability.UniformTruncationApproximation
import LPP_Foundations.Model.LastPassage.AnimalComparison

/-!
# Uniform mean control of passage clipping errors

The same two remainder fields control every endpoint on a diagonal. Applying
Martin's animal mean estimate before taking a limit therefore gives an
expected maximum bound, rather than only separate endpoint mean bounds.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace LPPDifferentiability

private theorem mapped_positive_animal_mean (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (f : ℝ → ℝ) (hf : Measurable f)
    (C : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hi : Integrable (fun ω : Environment =>
      animalMaximum n hn (fun v => max (ω v) 0)) (environmentLaw (μ.map f)))
    (hb : (∫ ω : Environment, animalMaximum n hn (fun v => max (ω v) 0)
        ∂environmentLaw (μ.map f)) ≤ C) :
    Integrable (fun ω : Environment =>
      animalMaximum n hn (fun v => max (f (ω v)) 0)) (environmentLaw μ) ∧
    (∫ ω : Environment, animalMaximum n hn (fun v => max (f (ω v)) 0)
      ∂environmentLaw μ) ≤ C := by
  have hm := measurable_coordinatewise_environment_map f hf
  have himap : Integrable (fun ω : Environment =>
      animalMaximum n hn (fun v => max (ω v) 0))
      ((environmentLaw μ).map (fun ω : Environment => fun v => f (ω v))) := by
    rw [environmentLaw_map_coordinatewise μ f hf]
    exact hi
  refine ⟨himap.comp_measurable hm, ?_⟩
  have heq := integral_map hm.aemeasurable himap.aestronglyMeasurable
  rw [environmentLaw_map_coordinatewise μ f hf] at heq
  exact heq ▸ hb

/-- Under Martin's two square-root tail conditions, clipping at one sufficiently
large deterministic cutoff makes the expected maximum absolute passage error
on every positive diagonal at most epsilon times its length. This is the
uniform mean version of Martin (2004), Lemma 5.2, using its finite animal bound;
it supplies the truncation step needed near JR1810.03580v3, equation (4.17). -/
theorem exists_uniform_mean_lastPassage_clipping_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℝ, 0 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω : Environment =>
        Finset.univ.sup' Finset.univ_nonempty (fun k : Fin (n + 1) =>
          |lastPassage ω 0 (k.val, n - k.val) -
            lastPassage (fun v => max (-L) (min L (ω v))) 0
              (k.val, n - k.val)|)) (environmentLaw μ) ∧
      (∫ ω : Environment,
        Finset.univ.sup' Finset.univ_nonempty (fun k : Fin (n + 1) =>
          |lastPassage ω 0 (k.val, n - k.val) -
            lastPassage (fun v => max (-L) (min L (ω v))) 0
              (k.val, n - k.val)|) ∂environmentLaw μ) ≤ ε * n := by
  classical
  obtain ⟨C, _, hmean⟩ := exists_positive_animalMaximum_mean_bound
  obtain ⟨L₀, hL₀, hsmall⟩ := exists_remainder_sqrt_tail_cutoff μ hpos hneg C
    (ε / 2) (half_pos hε)
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n hn
  have hLnonneg : 0 ≤ L := hL₀.trans hL
  let tp := (∫⁻ t in Ioi (0 : ℝ),
    ((μ.map (fun x : ℝ => max (x - L) 0)) (Ioi t)) ^ (1 / 2 : ℝ)).toReal
  let tn := (∫⁻ t in Ioi (0 : ℝ),
    ((μ.map (fun x : ℝ => max (-x - L) 0)) (Ioi t)) ^ (1 / 2 : ℝ)).toReal
  obtain ⟨hip, hbp⟩ := (hmean (μ.map (fun x : ℝ => max (x - L) 0)) n hn).2
    (positive_remainder_sqrt_tail_lt_top μ hpos L hLnonneg)
  obtain ⟨hin, hbn⟩ := (hmean (μ.map (fun x : ℝ => max (-x - L) 0)) n hn).2
    (negative_remainder_sqrt_tail_lt_top μ hneg L hLnonneg)
  obtain ⟨hip', hbp'⟩ := mapped_positive_animal_mean μ
    (fun x : ℝ => max (x - L) 0) (by fun_prop) (C * n * tp) n hn hip hbp
  obtain ⟨hin', hbn'⟩ := mapped_positive_animal_mean μ
    (fun x : ℝ => max (-x - L) 0) (by fun_prop) (C * n * tn) n hn hin hbn
  let P : Environment → ℝ := fun ω =>
    animalMaximum n hn (fun v => max (ω v - L) 0)
  let Q : Environment → ℝ := fun ω =>
    animalMaximum n hn (fun v => max (-ω v - L) 0)
  have hiP : Integrable P (environmentLaw μ) := by
    simpa only [max_eq_left (le_max_right _ _)] using hip'
  have hiQ : Integrable Q (environmentLaw μ) := by
    simpa only [max_eq_left (le_max_right _ _)] using hin'
  have hbP : (∫ ω, P ω ∂environmentLaw μ) ≤ C * n * tp := by
    simpa only [max_eq_left (le_max_right _ _)] using hbp'
  have hbQ : (∫ ω, Q ω ∂environmentLaw μ) ≤ C * n * tn := by
    simpa only [max_eq_left (le_max_right _ _)] using hbn'
  let E : Environment → ℝ := fun ω =>
    Finset.univ.sup' Finset.univ_nonempty (fun k : Fin (n + 1) =>
      |lastPassage ω 0 (k.val, n - k.val) -
        lastPassage (fun v => max (-L) (min L (ω v))) 0 (k.val, n - k.val)|)
  have hmE : Measurable E := by
    have hsup : Measurable
        (Finset.univ.sup' Finset.univ_nonempty
          (fun k : Fin (n + 1) => fun ω : Environment =>
            |lastPassage ω 0 (k.val, n - k.val) -
              lastPassage (fun v => max (-L) (min L (ω v))) 0
                (k.val, n - k.val)|)) := by
      apply Finset.measurable_sup' Finset.univ_nonempty
      intro k _
      exact continuous_abs.measurable.comp ((measurable_lastPassage 0 _).sub
        ((measurable_lastPassage 0 _).comp
          (measurable_coordinatewise_environment_map
            (fun x : ℝ => max (-L) (min L x)) (by fun_prop))))
    have heq : E = Finset.univ.sup' Finset.univ_nonempty
        (fun k : Fin (n + 1) => fun ω : Environment =>
          |lastPassage ω 0 (k.val, n - k.val) -
            lastPassage (fun v => max (-L) (min L (ω v))) 0
              (k.val, n - k.val)|) := by
      funext ω
      exact (Finset.sup'_apply Finset.univ_nonempty
        (fun k : Fin (n + 1) => fun ω : Environment =>
          |lastPassage ω 0 (k.val, n - k.val) -
            lastPassage (fun v => max (-L) (min L (ω v))) 0
              (k.val, n - k.val)|) ω).symm
    rw [heq]
    exact hsup
  have hEzero (ω : Environment) : 0 ≤ E ω := by
    exact (abs_nonneg _).trans
      (Finset.le_sup' (s := Finset.univ) (f := fun k : Fin (n + 1) =>
        |lastPassage ω 0 (k.val, n - k.val) -
          lastPassage (fun v => max (-L) (min L (ω v))) 0 (k.val, n - k.val)|)
        (Finset.mem_univ (0 : Fin (n + 1))))
  have hEbound (ω : Environment) : E ω ≤ P ω + Q ω := by
    apply Finset.sup'_le
    intro k _
    have hlength : k.val + (n - k.val) = n := by omega
    have hp := lastPassage_le_animalMaximum_atOrigin
      (fun v => max (ω v - L) 0) (k.val, n - k.val) (by simp only [hlength]; omega)
    have hq := lastPassage_le_animalMaximum_atOrigin
      (fun v => max (-ω v - L) 0) (k.val, n - k.val) (by simp only [hlength]; omega)
    simp only [hlength, max_eq_left (le_max_right _ _)] at hp hq
    exact (lastPassage_sub_clipped_abs_le_remainders ω 0
      (k.val, n - k.val) L hLnonneg).trans (add_le_add hp hq)
  have hiE : Integrable E (environmentLaw μ) :=
    (hiP.add hiQ).mono_nonneg hmE.aestronglyMeasurable
      (Filter.Eventually.of_forall hEzero) (Filter.Eventually.of_forall hEbound)
  refine ⟨hiE, ?_⟩
  calc
    (∫ ω, E ω ∂environmentLaw μ) ≤ ∫ ω, P ω + Q ω ∂environmentLaw μ :=
      integral_mono hiE (hiP.add hiQ) hEbound
    _ = (∫ ω, P ω ∂environmentLaw μ) + ∫ ω, Q ω ∂environmentLaw μ :=
      integral_add hiP hiQ
    _ ≤ C * n * tp + C * n * tn := add_le_add hbP hbQ
    _ = (C * tp + C * tn) * n := by ring
    _ ≤ ε * n := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg n)
      obtain ⟨hsp, hsn⟩ := hsmall L hL
      change C * tp < ε / 2 at hsp
      change C * tn < ε / 2 at hsn
      linarith only [hsp, hsn]

end LPPDifferentiability
