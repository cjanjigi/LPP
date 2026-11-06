/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.PathSets
public import LPP_Foundations.Model.Paths.Fintype
public import LPP_Foundations.Probability.FiniteEnvironmentLaw

import LPP_Foundations.Model.Paths.Count
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real

/-! # Bad-site bounds for actual up-right paths

The collected vertices of an actual path are distinct and exclude its terminal
vertex. Their finite joint law is derived from the canonical iid environment.
Finite-subset and actual-path union bounds give the bound with factor `4^n`
for all endpoints at a fixed start.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace LPPDifferentiability

private theorem measure_all_sites_in_set_on_finset
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : Set ℝ) (hA : MeasurableSet A)
    (S : Finset Lattice) :
    (environmentLaw μ) {ω : Environment | ∀ z ∈ S, ω z ∈ A} = μ A ^ S.card := by
  classical
  let I := {z : Lattice // z ∈ S}
  let coords : Environment → I → ℝ := fun ω z => ω z.1
  let rectangle : Set (I → ℝ) := Set.univ.pi fun _ => A
  have hIcard : Fintype.card I = S.card := Fintype.card_coe S
  have hcoords : Measurable coords :=
    measurable_pi_iff.mpr fun z => measurable_environment_eval z.1
  have hrectangle : MeasurableSet rectangle := by
    exact MeasurableSet.univ_pi fun _ => hA
  have hpre : coords ⁻¹' rectangle = {ω : Environment | ∀ z ∈ S, ω z ∈ A} := by
    ext ω
    simp only [Set.mem_preimage, rectangle, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_ofPred_eq]
    constructor
    · intro h z hz
      exact h ⟨z, hz⟩
    · intro h z
      exact h z.1 z.2
  have hlaw := environmentLaw_map_finite_coordinates μ
    (fun z : I => z.1) (fun z z' h => Subtype.ext h)
  calc
    (environmentLaw μ) {ω : Environment | ∀ z ∈ S, ω z ∈ A} =
        (environmentLaw μ).map coords rectangle := by
      rw [Measure.map_apply hcoords hrectangle, hpre]
    _ = (Measure.pi (fun _ : I => μ)) rectangle := by
      simpa only [coords] using
        congrArg (fun ν : Measure (I → ℝ) => ν rectangle) hlaw
    _ = μ A ^ S.card := by
      change (Measure.pi (fun _ : I => μ)) (Set.univ.pi (fun _ : I => A)) = _
      rw [Measure.pi_pi]
      simp only [Finset.prod_const, Finset.card_univ, hIcard]

/-- A fixed finite set of distinct actual sites is bad with the product
probability dictated by the original one-site law. -/
private theorem measure_all_bad_on_finset
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : Set ℝ) (hA : MeasurableSet A)
    (S : Finset Lattice) {m : ℕ} (hS : S.card = m) :
    (environmentLaw μ) {ω : Environment | ∀ z ∈ S, ω z ∈ A} = μ A ^ m := by
  rw [measure_all_sites_in_set_on_finset μ A hA S, hS]

/-- For a fixed actual path, the probability that at least `m` of its collected
sites have weights in `A` is at most `choose(n,m) * μ(A)^m`. This includes
zero length and the cases `m = 0` and `m > n`. -/
theorem measure_path_bad_collected_sites_ge_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : Set ℝ) (hA : MeasurableSet A)
    {u : Lattice} {d : ℕ × ℕ} (p : Path u d) (m : ℕ) :
    (environmentLaw μ) {ω : Environment |
      m ≤ (@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _) p.collectedSites).card} ≤
        (Nat.choose (d.1 + d.2) m : ENNReal) * μ A ^ m := by
  classical
  let subsets := p.collectedSites.powersetCard m
  let bad (S : Finset Lattice) : Set Environment := {ω | ∀ z ∈ S, ω z ∈ A}
  have hsubset :
      {ω : Environment | m ≤ (@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _) p.collectedSites).card} ⊆
        ⋃ S ∈ subsets, bad S := by
    intro ω hω
    let F := p.collectedSites.filter fun z => ω z ∈ A
    obtain ⟨S, hSF, hScard⟩ := Finset.exists_subset_card_eq (s := F) hω
    have hS : S ∈ subsets := by
      exact Finset.mem_powersetCard.mpr ⟨hSF.trans (Finset.filter_subset _ _), hScard⟩
    apply Set.mem_iUnion.mpr
    refine ⟨S, Set.mem_iUnion.mpr ⟨hS, ?_⟩⟩
    intro z hz
    exact (Finset.mem_filter.mp (hSF hz)).2
  have hmeasure (S : Finset Lattice) (hS : S ∈ subsets) :
      (environmentLaw μ) (bad S) = μ A ^ m := by
    dsimp only [subsets] at hS
    exact measure_all_bad_on_finset μ A hA S (Finset.mem_powersetCard.mp hS).2
  have hcard : subsets.card = Nat.choose (d.1 + d.2) m := by
    simp only [subsets, Finset.card_powersetCard, p.collectedSites_card]
  calc
    (environmentLaw μ) {ω : Environment |
        m ≤ (@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _) p.collectedSites).card} ≤
        (environmentLaw μ) (⋃ S ∈ subsets, bad S) := measure_mono hsubset
    _ ≤ ∑ S ∈ subsets, (environmentLaw μ) (bad S) := measure_biUnion_finset_le _ _
    _ = ∑ S ∈ subsets, μ A ^ m := by
      apply Finset.sum_congr rfl
      intro S hS
      exact hmeasure S hS
    _ = (Nat.choose (d.1 + d.2) m : ENNReal) * μ A ^ m := by
      rw [show (∑ S ∈ subsets, μ A ^ m) = (subsets.card : ENNReal) * μ A ^ m by simp]
      rw [hcard]

/-- The actual endpoint-free family of paths with `n` steps from `u` has at
most `2^n` members. -/
theorem path_card_endpoint_free_le (u : Lattice) (n : ℕ) :
    Fintype.card (Σ i : Fin (n + 1), Path u (i.val, n - i.val)) ≤ 2 ^ n := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ i : Fin (n + 1), Fintype.card (Path u (i.val, n - i.val))) ≤
        ∑ i : Fin (n + 1), Nat.choose n i.val := by
      apply Finset.sum_le_sum
      intro i hi
      have hlength : i.val + (n - i.val) = n :=
        Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)
      simpa only [hlength] using path_card_le_choose u (i.val, n - i.val)
    _ = ∑ i ∈ Finset.range (n + 1), Nat.choose n i :=
      Fin.sum_univ_eq_sum_range (fun i => Nat.choose n i) (n + 1)
    _ = 2 ^ n := Nat.sum_range_choose n

/-- Across every actual `n`-step path from a fixed start, with any endpoint,
the probability of at least `m` collected sites in `A` is at most
`4^n * μ(A)^m`. -/
theorem measure_exists_path_bad_collected_sites_ge_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : Set ℝ) (hA : MeasurableSet A)
    (u : Lattice) (n m : ℕ) :
    (environmentLaw μ) {ω : Environment |
      ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
        m ≤ (@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _) q.2.collectedSites).card} ≤
      (4 ^ n : ENNReal) * μ A ^ m := by
  classical
  let Q := Σ i : Fin (n + 1), Path u (i.val, n - i.val)
  let bad (q : Q) : Set Environment :=
    {ω | m ≤ (@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _) q.2.collectedSites).card}
  have hcard : Fintype.card Q ≤ 2 ^ n := path_card_endpoint_free_le u n
  have hchoose : (Nat.choose n m : ENNReal) ≤ (2 ^ n : ENNReal) := by
    exact_mod_cast Nat.choose_le_two_pow n m
  have hEvent :
      {ω : Environment | ∃ q : Q,
        m ≤ (@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _) q.2.collectedSites).card} =
        ⋃ q : Q, bad q := by
    ext ω
    simp [bad]
  rw [hEvent]
  calc
    (environmentLaw μ) (⋃ q : Q, bad q) ≤
        ∑ q : Q, (environmentLaw μ) (bad q) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _q : Q, (Nat.choose n m : ENNReal) * μ A ^ m := by
      apply Finset.sum_le_sum
      intro q hq
      have hlength : q.1.val + (n - q.1.val) = n :=
        Nat.add_sub_of_le (Nat.le_of_lt_succ q.1.isLt)
      simpa only [bad, hlength] using
        measure_path_bad_collected_sites_ge_le μ A hA q.2 m
    _ = (Fintype.card Q : ENNReal) *
        ((Nat.choose n m : ENNReal) * μ A ^ m) := by simp
    _ ≤ (2 ^ n : ENNReal) *
        ((Nat.choose n m : ENNReal) * μ A ^ m) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ ≤ (4 ^ n : ENNReal) * μ A ^ m := by
      calc
        (2 ^ n : ENNReal) * ((Nat.choose n m : ENNReal) * μ A ^ m) =
            ((2 ^ n : ENNReal) * (Nat.choose n m : ENNReal)) * μ A ^ m := by ac_rfl
        _ ≤ ((2 ^ n : ENNReal) * (2 ^ n : ENNReal)) * μ A ^ m := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hchoose (by positivity)) (by positivity)
        _ = (4 ^ n : ENNReal) * μ A ^ m := by
          rw [← mul_pow]
          norm_num

end LPPDifferentiability
