/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.GreedyAnimalAlmostSureBound
public import LPP_Foundations.Model.LastPassage.Basic
import LPP_Foundations.Model.Animals.Extension
import LPP_Foundations.Model.Animals.PathSets
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Uniform passage upper bound over all shorter endpoints

Martin (2004), Lemma 3.5(ii), follows by extending each collected path animal to
the common size in the positive-part field. This includes zero displacement without
introducing an animal maximum at size zero.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace LPPDifferentiability

/-- Signed passage to any shorter endpoint is bounded by the positive-part
animal maximum at the common positive size. Extra sites are nonnegative. -/
theorem lastPassage_le_animalMaximum_of_length_le (ω : Environment)
    (n : ℕ) (hn : 1 ≤ n) (d : ℕ × ℕ) (hdn : d.1 + d.2 ≤ n) :
    lastPassage ω 0 d ≤ animalMaximum n hn (fun z => max (ω z) 0) := by
  classical
  by_cases hd : 0 < d.1 + d.2
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω 0 d
    obtain ⟨hconnected, hzero, hcard⟩ :=
      (mem_animalFamily_iff _ _).1 (Path.collectedSites_mem_animalFamily p hd)
    obtain ⟨s, hs, hsubset⟩ :=
      hconnected.exists_extension_mem_animalFamily hzero n (by omega)
    calc
      lastPassage ω 0 d = pathWeight ω p := hp.symm
      _ = ∑ z ∈ p.collectedSites, ω z := Path.pathWeight_eq_sum_collectedSites ω p
      _ ≤ ∑ z ∈ p.collectedSites, max (ω z) 0 :=
        Finset.sum_le_sum (fun z _ => le_max_left (ω z) 0)
      _ ≤ ∑ z ∈ s, max (ω z) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun z _ _ => le_max_right (ω z) 0)
      _ ≤ animalMaximum n hn (fun z => max (ω z) 0) :=
        animalWeight_le_animalMaximum n hn (fun z => max (ω z) 0) hs
  · have hd0 : d = (0, 0) := Prod.ext (by omega) (by omega)
    rw [hd0, lastPassage_zero]
    exact animalMaximum_nonneg_of_forall_nonneg n hn _ (fun z => le_max_right (ω z) 0)

/-- One universal positive constant bounds passage simultaneously to every
endpoint of length at most `n`, eventually for every positive epsilon on one
full-measure event. Only the positive integrated square-root tail is required. -/
theorem exists_uniform_lastPassage_eventually_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ →
      ∀ᵐ ω ∂environmentLaw μ,
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
          ∀ d : ℕ × ℕ, d.1 + d.2 ≤ n →
            lastPassage ω 0 d < (n : ℝ) *
              (C * (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal + ε) := by
  obtain ⟨C, hC, hbound⟩ := exists_animalMaximum_limsup_and_eventually_bound
  refine ⟨C, hC, ?_⟩
  intro μ _ hpos
  let ν := μ.map (fun x : ℝ => max x 0)
  have htail :
      (∫⁻ t in Ioi (0 : ℝ), (ν (Ioi t)) ^ (1 / 2 : ℝ)) =
        ∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ) :=
    positivePart_sqrt_tail μ
  have hevent := hbound ν (by rw [htail]; exact hpos)
  have hback := ae_positivePart_environment_of_ae μ hevent
  filter_upwards [hback] with ω hω
  intro ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hω.2 ε hε)
  refine ⟨K + 1, by omega, ?_⟩
  intro n hn d hd
  have hnpos : 1 ≤ n := by omega
  have hind : n - 1 + 1 = n := by omega
  have hrate := hK (n - 1) (by omega)
  simp only [hind, htail] at hrate
  have hden : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hmax : animalMaximum n hnpos (fun z => max (ω z) 0) <
      (n : ℝ) *
        (C * (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal + ε) := by
    exact (div_lt_iff₀ hden).1 hrate |>.trans_eq (mul_comm _ _)
  exact (lastPassage_le_animalMaximum_of_length_le ω n hnpos d hd).trans_lt hmax

end LPPDifferentiability
