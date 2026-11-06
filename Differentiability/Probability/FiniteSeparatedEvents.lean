/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Data.Nat.Dist
public import Mathlib.Probability.Independence.Basic

/-!
# Probability of a finite family of separated bad events

This file bounds the probability that none of the events `G v`, for `v` in a finite set of
lattice sites, occurs. The events of sites that are far apart are independent, and each
complement event `(G v)ᶜ` has probability at most `ζ`. The bound is the power
`ζ ^ (number of sites)`.
-/

public section

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal

namespace LPPDifferentiability

private theorem ennreal_toReal_finset_prod {ι : Type*} (S : Finset ι)
    (f : ι → ℝ≥0∞) :
    ENNReal.toReal (∏ i ∈ S, f i) = ∏ i ∈ S, ENNReal.toReal (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      simp [Finset.prod_insert, hi, ENNReal.toReal_mul, ih]

private theorem measureReal_iInter_compl_eq_prod
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [Fintype ι]
    (G : ι → Set Ω) (hInd : iIndepSet G P) :
    P.real (⋂ i, (G i)ᶜ) = ∏ i, P.real ((G i)ᶜ) := by
  classical
  have hProduct : P (⋂ i, (G i)ᶜ) = ∏ i, P ((G i)ᶜ) := by
    have hInter : (⋂ i : ι, (G i)ᶜ) = ⋂ i ∈ Finset.univ, (G i)ᶜ := by
      ext ω
      simp
    rw [hInter]
    exact (iIndepSet_iff G P).1 hInd Finset.univ
      (f := fun i => (G i)ᶜ)
      (by
        intro i hi
        exact (MeasurableSpace.measurableSet_generateFrom (by simp : G i ∈ {G i})).compl)
  calc
    P.real (⋂ i, (G i)ᶜ) = ENNReal.toReal (P (⋂ i, (G i)ᶜ)) := rfl
    _ = ENNReal.toReal (∏ i, P ((G i)ᶜ)) := congrArg ENNReal.toReal hProduct
    _ = ∏ i, ENNReal.toReal (P ((G i)ᶜ)) :=
      ennreal_toReal_finset_prod Finset.univ (fun i => P ((G i)ᶜ))
    _ = ∏ i, P.real ((G i)ᶜ) := rfl

/-- For an independent family of events, the probability that no event occurs is the product of
the probabilities of the complements. -/
private theorem measureReal_iInter_compl_eq_prod_of_indep
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [Fintype ι]
    (G : ι → Set Ω) (hInd : iIndepSet G P) :
    P.real (⋂ i, (G i)ᶜ) = ∏ i, P.real ((G i)ᶜ) :=
  measureReal_iInter_compl_eq_prod P G hInd

/-- The event that no event `G v` occurs for `v` in a finite set of sites is measurable. -/
theorem measurableSet_all_bad_sites
    {Ω : Type*} [MeasurableSpace Ω]
    (G : ℕ × ℕ → Set Ω) (hG : ∀ v, MeasurableSet (G v))
    (S : Finset (ℕ × ℕ)) :
    MeasurableSet {ω : Ω | ∀ v ∈ S, ω ∉ G v} := by
  classical
  have hEvent :
      {ω : Ω | ∀ v ∈ S, ω ∉ G v} =
        ⋂ v : {u : ℕ × ℕ // u ∈ S}, (G v.1)ᶜ := by
    ext ω
    simp
  rw [hEvent]
  exact MeasurableSet.iInter (fun v => (hG v.1).compl)

/-- For a finite set of sites, the probability that no event `G v` occurs is at most `ζ` raised to
the number of sites, when the events of sites at distance greater than `k` are independent.
Independence is assumed only for finite subsets of sites that are pairwise separated; the product
formula for the complements is proved in the argument. -/
theorem measure_all_bad_sites_le_pow
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ × ℕ → Set Ω) (k : ℕ) (ζ : ℝ)
    (hMarginal : ∀ v, P.real ((G v)ᶜ) ≤ ζ)
    (hSeparatedIndep : ∀ T : Finset (ℕ × ℕ),
      (∀ u ∈ T, ∀ v ∈ T, u ≠ v →
        k < Nat.dist u.1 v.1 ∨ k < Nat.dist u.2 v.2) →
      iIndepSet (fun v : {u : ℕ × ℕ // u ∈ T} => G v.1) P)
    (S : Finset (ℕ × ℕ))
    (hS : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      k < Nat.dist u.1 v.1 ∨ k < Nat.dist u.2 v.2) :
    P.real {ω : Ω | ∀ v ∈ S, ω ∉ G v} ≤ ζ ^ S.card := by
  classical
  have hEvent :
      {ω : Ω | ∀ v ∈ S, ω ∉ G v} =
        ⋂ v : {u : ℕ × ℕ // u ∈ S}, (G v.1)ᶜ := by
    ext ω
    simp
  have hProduct := measureReal_iInter_compl_eq_prod_of_indep P
    (fun v : {u : ℕ × ℕ // u ∈ S} => G v.1) (hSeparatedIndep S hS)
  calc
    P.real {ω : Ω | ∀ v ∈ S, ω ∉ G v} =
        ∏ v : {u : ℕ × ℕ // u ∈ S}, P.real ((G v.1)ᶜ) := by
          rw [hEvent]
          exact hProduct
    _ ≤ ∏ v : {u : ℕ × ℕ // u ∈ S}, ζ := by
      exact Finset.prod_le_prod₀
        (s := Finset.univ)
        (f := fun v : {u : ℕ × ℕ // u ∈ S} => P.real ((G v.1)ᶜ))
        (g := fun _ => ζ)
        (by intro v hv; exact measureReal_nonneg)
        (by intro v hv; exact hMarginal v.1)
    _ = ζ ^ S.card := by simp

end LPPDifferentiability
