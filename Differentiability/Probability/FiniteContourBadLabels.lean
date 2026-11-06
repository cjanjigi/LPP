/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.SeparatedNaturalLatticeSubset
public import Differentiability.Probability.FiniteSeparatedEvents
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Probability bound for separated bad labels

This file bounds the probability that none of the events `G v`, for `v` in a finite set of lattice
sites, occurs. Each `G v` fails with probability at most `ζ`, and the failures are independent on
separated subsets. The bound is a power of `ζ` whose exponent grows with the number of sites.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- The probability that no event `G v` with `v ∈ S` occurs is at most a power of `ζ`, provided
`m ≤ 8 * S.card`. -/
theorem measure_all_bad_natural_sites_le_real_power
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ × ℕ → Set Ω)
    (hG : ∀ v, MeasurableSet (G v))
    (k m : ℕ) (ζ : ℝ) (hζpos : 0 < ζ) (hζlt : ζ < 1)
    (hMarginal : ∀ v, MeasurableSet (G v) → P.real ((G v)ᶜ) ≤ ζ)
    (hSeparatedIndep : ∀ T : Finset (ℕ × ℕ),
      (∀ u ∈ T, ∀ v ∈ T, u ≠ v →
        k < Nat.dist u.1 v.1 ∨ k < Nat.dist u.2 v.2) →
      iIndepSet (fun v : {u : ℕ × ℕ // u ∈ T} => G v.1) P)
    (S : Finset (ℕ × ℕ)) (hm : m ≤ 8 * S.card) :
    P.real {ω : Ω | ∀ v ∈ S, ω ∉ G v} ≤
      Real.rpow ζ ((m : ℝ) / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) := by
  classical
  obtain ⟨T, hTS, hTSeparated, _, hTCard⟩ :=
    exists_separated_natural_lattice_subset S k
  have hBadMarginal (v : ℕ × ℕ) : P.real ((G v)ᶜ) ≤ ζ :=
    hMarginal v (hG v)
  have hTBound : P.real {ω : Ω | ∀ v ∈ T, ω ∉ G v} ≤ ζ ^ T.card :=
    measure_all_bad_sites_le_pow P G k ζ hBadMarginal hSeparatedIndep T hTSeparated
  have hSubset :
      {ω : Ω | ∀ v ∈ S, ω ∉ G v} ⊆ {ω : Ω | ∀ v ∈ T, ω ∉ G v} := by
    intro ω hω v hvT
    exact hω v (hTS hvT)
  have hmReal : (m : ℝ) ≤ 8 * (S.card : ℝ) := by
    exact_mod_cast hm
  have hCardReal :
      (S.card : ℝ) ≤ (((2 * k + 1) ^ 2 : ℕ) : ℝ) * (T.card : ℝ) := by
    exact_mod_cast hTCard
  have hDenomPos : 0 < 8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ) := by
    positivity
  have hExponent :
      (m : ℝ) / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)) ≤ (T.card : ℝ) := by
    rw [div_le_iff₀ hDenomPos]
    calc
      (m : ℝ) ≤ 8 * (S.card : ℝ) := hmReal
      _ ≤ 8 * ((((2 * k + 1) ^ 2 : ℕ) : ℝ) * (T.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hCardReal (by norm_num)
      _ = (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)) * (T.card : ℝ) := by ring
      _ = (T.card : ℝ) * (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)) := by ring
  calc
    P.real {ω : Ω | ∀ v ∈ S, ω ∉ G v} ≤
        P.real {ω : Ω | ∀ v ∈ T, ω ∉ G v} := measureReal_mono hSubset
    _ ≤ ζ ^ T.card := hTBound
    _ = Real.rpow ζ (T.card : ℝ) := (Real.rpow_natCast ζ T.card).symm
    _ ≤ Real.rpow ζ ((m : ℝ) / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_ge hζpos hζlt.le hExponent

end LPPDifferentiability

end
