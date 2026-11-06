/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.GreedyAnimalAlmostSureBound
public import LPP_Foundations.Model.Animals.DiagonalTranslation
public import LPP_Foundations.Model.Animals.Extension
import LPP_Foundations.Probability.TranslationCylinder
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Fixed-root transfer and the source normalization for nonnegative animals. -/

public section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal
namespace LPPDifferentiability

/-- Translate an actual animal to zero, extend it to the specified exact size,
and compare its nonnegative weight with the existing actual finite maximum. -/
theorem animalWeight_le_translated_animalMaximum
    (ω : Environment) (hω : ∀ z, 0 ≤ ω z) (o : Lattice)
    (B : Finset Lattice) (hB : IsConnectedAnimal B) (ho : o ∈ B)
    (n : ℕ) (hn : 1 ≤ n) (hcard : B.card ≤ n) :
    (∑ z ∈ B, ω z) ≤ animalMaximum n hn (fun z => ω (o + z)) := by
  classical
  let S := B.image (fun z => -o + z)
  have hS : IsConnectedAnimal S := hB.image_lattice_add (-o)
  have hzero : (0 : Lattice) ∈ S := by
    exact Finset.mem_image.mpr ⟨o, ho, neg_add_cancel o⟩
  have hsize : S.card ≤ n := by
    rw [show S.card = B.card from card_image_lattice_add (-o) B]
    exact hcard
  obtain ⟨T, hT, hST⟩ := hS.exists_extension_mem_animalFamily hzero n hsize
  have hsum : (∑ z ∈ B, ω z) = ∑ z ∈ S, ω (o + z) := by
    dsimp [S]
    rw [Finset.sum_image]
    · simp only [add_neg_cancel_left]
    · intro x _ y _ h
      exact add_left_cancel h
  rw [hsum]
  exact (Finset.sum_le_sum_of_subset_of_nonneg hST
    (fun z _ _ => hω (o + z))).trans (animalWeight_le_animalMaximum n hn _ hT)

/-- One universal constant gives the source factor two, at every fixed root,
on one full-measure event uniformly over all animals of size at most
`2 * (N + 1)`. No maximum or almost-sure estimate is assumed. -/
theorem exists_rooted_animal_eventually_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      (∀ᵐ x ∂μ, 0 ≤ x) →
      (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ →
      ∀ o : Lattice, ∀ᵐ ω ∂environmentLaw μ,
        ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
          ∀ B : Finset Lattice, IsConnectedAnimal B → o ∈ B →
            B.card ≤ 2 * (N + 1) →
            (∑ z ∈ B, ω z) / (N : ℝ) <
              2 * C * (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal + ε := by
  obtain ⟨C, hC, hsource⟩ := exists_animalMaximum_limsup_and_eventually_bound
  refine ⟨C, hC, ?_⟩
  intro μ _ hnonneg htail o
  have hback := (measurePreserving_environment_translation μ o).quasiMeasurePreserving.ae
    (hsource μ htail)
  filter_upwards [hback, ae_forall_environment_nonneg μ hnonneg] with ω hω hpos
  intro ε hε
  let D : ℝ := C * (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal
  have hsub : Tendsto (fun N : ℕ => 2 * N + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun N hN => by omega⟩
  have hrate := hsub.eventually (hω.2 (ε / 4) (by positivity))
  have hratio : Tendsto (fun N : ℕ => ((2 * (N + 1) : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 (2 : ℝ)) := by
    convert tendsto_add_mul_div_add_mul_atTop_nhds (2 : ℝ) 0 2
      (d := 1) (by norm_num) using 1 <;> push_cast <;> ring
  have hprod : Tendsto
      (fun N : ℕ => (D + ε / 4) * (((2 * (N + 1) : ℕ) : ℝ) / (N : ℝ)))
      atTop (𝓝 ((D + ε / 4) * 2)) := tendsto_const_nhds.mul hratio
  have hsmall := hprod.eventually (gt_mem_nhds
    (show (D + ε / 4) * 2 < 2 * D + ε by linarith only [hε]))
  filter_upwards [hrate, hsmall, eventually_ge_atTop (1 : ℕ)] with N hN hsmallN hNpos
  intro B hB ho hcard
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hsize : (0 : ℝ) < ((2 * (N + 1) : ℕ) : ℝ) := by positivity
  have hcompare := animalWeight_le_translated_animalMaximum ω hpos o B hB ho
    (2 * (N + 1)) (by omega) hcard
  have hrateN : animalMaximum (2 * (N + 1)) (by omega) (fun z => ω (o + z)) /
      ((2 * (N + 1) : ℕ) : ℝ) < D + ε / 4 := by
    convert hN using 1
  have hscaled := mul_lt_mul_of_pos_right hrateN (div_pos hsize hNreal)
  have heq : animalMaximum (2 * (N + 1)) (by omega) (fun z => ω (o + z)) /
      ((2 * (N + 1) : ℕ) : ℝ) *
      (((2 * (N + 1) : ℕ) : ℝ) / (N : ℝ)) =
      animalMaximum (2 * (N + 1)) (by omega) (fun z => ω (o + z)) / (N : ℝ) := by
    field_simp
  rw [heq] at hscaled
  have hbound := (div_le_div_of_nonneg_right hcompare hNreal.le).trans_lt
    (hscaled.trans hsmallN)
  simpa only [D, mul_assoc] using hbound

end LPPDifferentiability
