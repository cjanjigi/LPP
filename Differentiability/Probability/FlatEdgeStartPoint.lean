/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.OrientedPercolation
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Analysis.QuadrantExtension
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Differentiability.Model.AugmentedPassage
import Differentiability.Model.OrientedPercolationLaws
import Differentiability.Probability.AugmentedBlockLaws
import Differentiability.Probability.HalfLineEdge
import Mathlib.Tactic

/-!
# The start point of the lowest augmented site

Run the augmented process from the half-line for `n` blocks of `T` levels with at most `n`
augmentations, and let `N = n T`. Almost surely the lowest site `r_n` of the occupied set has a
start point `u_n = (-k, k)` on the half-line and a displacement `(i, N - i)` with passage time
at least `N + K_n (c₀ - 1)` (`augmentedProcess_passage_lower`). The direction `y = i / N` is at
least `M_n / N`, where `M_n` is the first coordinate of `r_n`. On the Markov good event
`N - a⁰_N ≤ C N`, the start point lies in `{(-k, k) : k ≤ C N}`, so the maximal deviation
`D_N` bounds the passage time minus `g (i, N - i) = N ḡ(y)`.

## Main results

- `ae_exists_flatEdge_startPoint_bound`: the direction `y` and the almost sure lower bound on
  `N ḡ(y)` described above.

## References

- Georgiou, Rassoul-Agha and Seppäläinen (manuscript in preparation), the edge-differentiability
  theorem.
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace LPPDifferentiability

/-- Homogeneity at a lattice displacement on level `N`: `g (i, N - i) = N ḡ(i / N)`. -/
private theorem shape_eq_level_mul_profile (g : Quadrant → ℝ)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (N i : ℕ) (hN : 0 < N) (hi : i ≤ N) :
    g ((i : ℝ≥0), ((N - i : ℕ) : ℝ≥0)) =
      N * quadrantExtension g ((i : ℝ) / N, 1 - (i : ℝ) / N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hy₀ : 0 ≤ (i : ℝ) / N := div_nonneg (Nat.cast_nonneg _) hNpos.le
  have hy₁ : 0 ≤ 1 - (i : ℝ) / N := by
    rw [sub_nonneg, div_le_one hNpos]
    exact_mod_cast hi
  have e1 : (N : ℝ≥0) * (toQuadrant ((i : ℝ) / N, 1 - (i : ℝ) / N)).1 = (i : ℝ≥0) := by
    apply NNReal.eq
    rw [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_natCast]
    show (N : ℝ) * (((i : ℝ) / N).toNNReal : ℝ) = (i : ℝ)
    rw [Real.coe_toNNReal _ hy₀]
    field_simp
  have e2 : (N : ℝ≥0) * (toQuadrant ((i : ℝ) / N, 1 - (i : ℝ) / N)).2 =
      ((N - i : ℕ) : ℝ≥0) := by
    apply NNReal.eq
    rw [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_natCast]
    show (N : ℝ) * ((1 - (i : ℝ) / N).toNNReal : ℝ) = ((N - i : ℕ) : ℝ)
    rw [Real.coe_toNNReal _ hy₁, Nat.cast_sub hi]
    field_simp
  have h := hghom (N : ℝ≥0) (toQuadrant ((i : ℝ) / N, 1 - (i : ℝ) / N))
  rw [e1, e2, NNReal.coe_natCast] at h
  exact h

/-- **Start point of the lowest augmented site.** Let `N = n T` with `n, T ≥ 1` and `c₀ ≤ 1`.
Almost surely there is a direction `y ∈ [0, 1]` with `M_n ≤ y N`, where `M_n` is the largest
first coordinate of the occupied set after `n` blocks (cap `n`, start set the half-line),
such that on the event `N - a⁰_N ≤ C N` the scaled shape `N ḡ(y)` is at least
`N + K_n (c₀ - 1) - D_N`; here `K_n` is the number of augmentations and `D_N` is the maximal
positive deviation over start points `(-k, k)` with `k ≤ C N`. The direction is the first
coordinate of `r_n - u_n` divided by `N`, for the start point `u_n` given by
`augmentedProcess_passage_lower`. -/
theorem ae_exists_flatEdge_startPoint_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (g : Quadrant → ℝ)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ) (hc₀ : c₀ ≤ 1) (n : ℕ) (hn : 1 ≤ n) (C N : ℕ)
    (hN : N = n * T) :
    ∀ᵐ ω ∂environmentLaw ν, ∃ y ∈ Icc (0 : ℝ) 1,
      (maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 : ℝ) ≤ y * N ∧
      ((N : ℝ) - halfLineEdge ω N ≤ C * N →
        (N : ℝ) + ((augmentedProcess ω T c₀ antidiagHalfLine n n).2 : ℝ) * (c₀ - 1) -
            (⨆ (k : Fin (C * N + 1)) (i : Fin (N + 1)),
              max (lastPassage ω (-(k : ℤ), (k : ℤ)) ((i : ℕ), N - i) - ω (-(k : ℤ), (k : ℤ)) +
                ω ((-(k : ℤ), (k : ℤ)) + (((i : ℕ) : ℤ), ((N - i : ℕ) : ℤ))) -
                g (((i : ℕ) : ℝ≥0), ((N - i : ℕ) : ℝ≥0))) 0) ≤
          N * quadrantExtension g (y, 1 - y)) := by
  have hlev : antidiagHalfLine ⊆ levelSet 0 := fun u hu => hu.1
  have hN1 : 1 ≤ N := by
    rw [hN]
    exact Nat.mul_le_mul hn hT
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNz : ((N : ℕ) : ℤ) = (n : ℤ) * (T : ℤ) := by rw [hN, Nat.cast_mul]
  have hNr : ((N : ℕ) : ℝ) = (n : ℝ) * (T : ℝ) := by rw [hN, Nat.cast_mul]
  filter_upwards [ae_lowestPoint_mem_augmentedProcess ν hp₀ T c₀ antidiagHalfLine subset_rfl
      antidiagHalfLine_infinite n,
    ae_openEdge_le_openEdge_augmentedProcess ν hp₀ T c₀ antidiagHalfLine subset_rfl
      antidiagHalfLine_infinite n] with ω hmem hedge
  obtain ⟨M, hMdef⟩ : ∃ M, maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 = M :=
    ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K, (augmentedProcess ω T c₀ antidiagHalfLine n n).2 = K := ⟨_, rfl⟩
  rw [hMdef, hKdef]
  -- The lowest site `r_n = (M, N - M)` is occupied.
  have hr := hmem n
  rw [hMdef, ← hNz] at hr
  -- The plain edge is at most `M` (the edge comparison at `m = 0`).
  have hX0 : openEdge (topSites ω) (augmentedProcess ω T c₀ antidiagHalfLine n n).1 0 = M := by
    rw [openEdge, openReachSet_zero, hMdef]
  have haM : halfLineEdge ω N ≤ M := by
    have h := hedge n 0
    rw [add_zero, ← hN, hX0] at h
    exact h
  -- The start point `u_n` and the displacement `(i, j)` given by the passage lower bound.
  obtain ⟨⟨u₁, u₂⟩, hu, ⟨i, j⟩, hud, hpass⟩ :=
    augmentedProcess_passage_lower ω T hT c₀ hc₀ antidiagHalfLine hlev n n _ hr
  rw [hKdef] at hpass
  have hu₁ : u₁ + u₂ = 0 := hu.1
  have hu₂ : u₁ ≤ 0 := hu.2
  have hcomp := hud
  simp only [Prod.mk_add_mk, Prod.mk.injEq] at hcomp
  obtain ⟨hx, hy⟩ := hcomp
  have hj : j = N - i := by omega
  have hi : i ≤ N := by omega
  subst hj
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = u₂ := ⟨u₂.toNat, Int.toNat_of_nonneg (by omega)⟩
  subst hk
  have hu₁' : u₁ = -(k : ℤ) := by omega
  subst hu₁'
  have hv : ((-(k : ℤ), (k : ℤ)) + ((i : ℤ), ((N - i : ℕ) : ℤ)) : Lattice) =
      (M, (N : ℤ) - M) := hud
  rw [← hv] at hpass
  refine ⟨(i : ℝ) / N, ⟨div_nonneg (Nat.cast_nonneg _) hNpos.le,
    (div_le_one hNpos).mpr (by exact_mod_cast hi)⟩, ?_, ?_⟩
  -- The direction dominates `M_n / N`, since `u_n` has nonpositive first coordinate.
  · rw [div_mul_cancel₀ _ hNpos.ne']
    have hMi : M ≤ (i : ℤ) := by omega
    exact_mod_cast hMi
  -- On the good event the start point has `k ≤ C N`, so `D_N` dominates.
  · intro hG
    have hGz : (N : ℤ) - halfLineEdge ω N ≤ (C : ℤ) * N := by exact_mod_cast hG
    have hkC : k ≤ C * N := by
      have h1 : (k : ℤ) ≤ (C : ℤ) * (N : ℤ) := by
        have : (0 : ℤ) ≤ ((N - i : ℕ) : ℤ) := by positivity
        linarith
      exact_mod_cast h1
    have hDle : lastPassage ω (-(k : ℤ), (k : ℤ)) (i, N - i) - ω (-(k : ℤ), (k : ℤ)) +
          ω ((-(k : ℤ), (k : ℤ)) + ((i : ℤ), ((N - i : ℕ) : ℤ))) -
          g ((i : ℝ≥0), ((N - i : ℕ) : ℝ≥0)) ≤
        ⨆ (k' : Fin (C * N + 1)) (i' : Fin (N + 1)),
          max (lastPassage ω (-(k' : ℤ), (k' : ℤ)) ((i' : ℕ), N - i') -
            ω (-(k' : ℤ), (k' : ℤ)) +
            ω ((-(k' : ℤ), (k' : ℤ)) + (((i' : ℕ) : ℤ), ((N - i' : ℕ) : ℤ))) -
            g (((i' : ℕ) : ℝ≥0), ((N - i' : ℕ) : ℝ≥0))) 0 :=
      le_ciSup_of_le (Set.finite_range _).bddAbove ⟨k, Nat.lt_succ_of_le hkC⟩
        (le_ciSup_of_le (Set.finite_range _).bddAbove ⟨i, Nat.lt_succ_of_le hi⟩
          (le_max_left _ _))
    have hgy := shape_eq_level_mul_profile g hghom N i (by omega) hi
    linarith [hpass, hDle, hgy, hNr]

end LPPDifferentiability
