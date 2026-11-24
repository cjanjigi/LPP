/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatDensitySource.StoppedEdgeExpectation
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Durrett's density subdivision at observation time n, followed by his two limits. -/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology

namespace LPPDifferentiability.FinalDraft

/-- At observation time n, subdivide the density interval into M n equal parts
and sum the first-split estimate over this partition. -/
private theorem subdivided_density_gain {p q : unitInterval} (hp : 0 < (p : ℝ))
    (hpq : p ≤ q) (M n : ℕ) (hM : 0 < M) (hn : 0 < n) :
    (M : ℝ) * (1 - (1 - (((q : ℝ) - (p : ℝ)) / (M : ℝ)) / (n : ℝ)) ^ n) ≤
      expectedBernoulliHalfLineEdge q n / (n : ℝ) -
        expectedBernoulliHalfLineEdge p n / (n : ℝ) := by
  let N := M * n
  let d := (q : ℝ) - (p : ℝ)
  let t := d / (N : ℝ)
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos hM hn)
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hpq) hN.le
  have hNt : (N : ℝ) * t = d := mul_div_cancel₀ _ hN.ne'
  let s (j : ℕ) : unitInterval := ⟨(p : ℝ) + ((min j N : ℕ) : ℝ) * t, by
    have hmin : ((min j N : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast min_le_right j N
    have htop := mul_le_mul_of_nonneg_right hmin ht
    rw [hNt] at htop
    refine ⟨add_nonneg p.2.1 (mul_nonneg (Nat.cast_nonneg _) ht), ?_⟩
    calc
      (p : ℝ) + ((min j N : ℕ) : ℝ) * t ≤ (p : ℝ) + d := add_le_add_right htop (p : ℝ)
      _ = (q : ℝ) := by dsimp only [d]; ring
      _ ≤ 1 := q.2.2⟩
  have hs (j : ℕ) (hj : j ≤ N) : (s j : ℝ) = (p : ℝ) + (j : ℝ) * t := by
    change (p : ℝ) + ((min j N : ℕ) : ℝ) * t = _
    rw [min_eq_left hj]
  have hfirst : s 0 = p := by
    apply Subtype.ext
    rw [hs 0 (Nat.zero_le _)]
    simp
  have hlast : s N = q := by
    apply Subtype.ext
    rw [hs N le_rfl, hNt]
    dsimp only [d]
    ring
  have hinc : ∀ j ∈ Finset.range N, 1 - (1 - t) ^ n ≤
      expectedBernoulliHalfLineEdge (s (j + 1)) n -
        expectedBernoulliHalfLineEdge (s j) n := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have ha := hs j hj'.le
    have hb := hs (j + 1) (Nat.succ_le_of_lt hj')
    have hdiff : ((s (j + 1) : unitInterval) : ℝ) - (s j : ℝ) = t := by
      rw [ha, hb, Nat.cast_add, Nat.cast_one]
      ring
    have hPos : 0 < (s j : ℝ) := by
      rw [ha]
      exact hp.trans_le (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) ht))
    have hMono : s j ≤ s (j + 1) := by
      change (s j : ℝ) ≤ (s (j + 1) : ℝ)
      apply sub_nonneg.mp
      rwa [hdiff]
    simpa only [hdiff] using one_sub_pow_le_expectedBernoulliHalfLineEdge_sub hPos hMono n
  have hsum := Finset.sum_le_sum hinc
  have htel := Finset.sum_range_sub (fun j => expectedBernoulliHalfLineEdge (s j) n) N
  beta_reduce at htel
  rw [hfirst, hlast] at htel
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, htel] at hsum
  have hstep : t = (d / (M : ℝ)) / (n : ℝ) := by
    simp only [t, N, Nat.cast_mul, div_div]
  rw [← sub_div]
  apply (le_div_iff₀ hnR).2
  change (M : ℝ) * (1 - (1 - (d / (M : ℝ)) / (n : ℝ)) ^ n) * (n : ℝ) ≤ _
  rw [← hstep]
  calc
    (M : ℝ) * (1 - (1 - t) ^ n) * (n : ℝ) = (N : ℝ) * (1 - (1 - t) ^ n) := by
      simp only [N, Nat.cast_mul]
      ring
    _ ≤ _ := hsum

/-- For each fixed positive M, take the observation time to infinity while the
number of density subintervals is M n. -/
private theorem fixed_subdivision_parameter_gain {p q : unitInterval} (hp : 0 < (p : ℝ))
    (hpq : p ≤ q) {α β : ℝ}
    (hα : Tendsto (fun n : ℕ => expectedBernoulliHalfLineEdge p n / (n : ℝ)) atTop (𝓝 α))
    (hβ : Tendsto (fun n : ℕ => expectedBernoulliHalfLineEdge q n / (n : ℝ)) atTop (𝓝 β))
    (M : ℕ) (hM : 0 < M) :
    (M : ℝ) * (1 - Real.exp (-(((q : ℝ) - (p : ℝ)) / (M : ℝ)))) ≤ β - α := by
  let δ := ((q : ℝ) - (p : ℝ)) / (M : ℝ)
  have hExp : Tendsto (fun n : ℕ => (1 - δ / (n : ℝ)) ^ n) atTop (𝓝 (Real.exp (-δ))) := by
    simpa only [neg_div, ← sub_eq_add_neg] using Real.tendsto_one_add_div_pow_exp (-δ)
  have hLeft : Tendsto (fun n : ℕ => (M : ℝ) * (1 - (1 - δ / (n : ℝ)) ^ n))
      atTop (𝓝 ((M : ℝ) * (1 - Real.exp (-δ)))) :=
    (tendsto_const_nhds.sub hExp).const_mul (M : ℝ)
  exact le_of_tendsto_of_tendsto hLeft (hβ.sub hα) <|
    (eventually_gt_atTop 0).mono fun n hn => subdivided_density_gain hp hpq M n hM hn

/-- The remaining limit in the subdivision parameter is the total density increase. -/
private theorem tendsto_density_subdivision_parameter (d : ℝ) (hd : 0 ≤ d) :
    Tendsto (fun M : ℕ => (M : ℝ) * (1 - Real.exp (-(d / (M : ℝ)))))
      atTop (𝓝 d) := by
  rcases hd.eq_or_lt with hZero | hPos
  · subst d
    simp
  let a (M : ℕ) := -(d / (M : ℝ))
  have hSmall : Tendsto a atTop (𝓝 0) := by
    simpa only [a, neg_zero] using
      (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)) :
        Tendsto (fun M : ℕ => d / (M : ℝ)) atTop (𝓝 0)).neg
  have hLeft : Tendsto a atTop (𝓝[<] 0) := tendsto_nhdsWithin_iff.2
    ⟨hSmall, (eventually_gt_atTop 0).mono fun M hM =>
      neg_neg_of_pos (div_pos hPos (Nat.cast_pos.mpr hM))⟩
  have hSlope := ((Real.hasDerivAt_exp 0).tendsto_slope_zero_left.comp hLeft).const_mul d
  have hT : Tendsto (fun M : ℕ => d * ((a M)⁻¹ * (Real.exp (a M) - 1))) atTop (𝓝 d) := by
    simpa only [Function.comp_def, smul_eq_mul, zero_add, Real.exp_zero, mul_one] using hSlope
  refine hT.congr' ((eventually_gt_atTop 0).mono fun M hM => ?_)
  dsimp only [a]
  have hm : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM : 0 < (M : ℝ)).ne'
  rw [inv_neg, inv_div]
  field_simp
  ring

/-- Durrett's density increase for the finite infima of the actual Bernoulli
half-line rates. The estimate follows by first taking n to infinity for each
fixed subdivision parameter M and then taking M to infinity. -/
theorem density_sub_le_sub_isGLB_halfLineEdge_bernoulli
    {p q : unitInterval} (hp : 0 < (p : ℝ)) (hpq : p ≤ q) {α β : ℝ}
    (hα : IsGLB (range fun n : ℕ =>
      expectedBernoulliHalfLineEdge p (n + 1) / ((n : ℝ) + 1)) α)
    (hβ : IsGLB (range fun n : ℕ =>
      expectedBernoulliHalfLineEdge q (n + 1) / ((n : ℝ) + 1)) β) :
    (q : ℝ) - (p : ℝ) ≤ β - α := by
  have hQ : 0 < (q : ℝ) := hp.trans_le hpq
  have hP := tendsto_expectedBernoulliHalfLineEdge_div p hp α hα
  have hQ' := tendsto_expectedBernoulliHalfLineEdge_div q hQ β hβ
  exact le_of_tendsto_of_tendsto (tendsto_density_subdivision_parameter _ (sub_nonneg.mpr hpq))
    tendsto_const_nhds ((eventually_gt_atTop 0).mono fun M hM =>
      fixed_subdivision_parameter_gain hp hpq hP hQ' M hM)

/-- A strict rise in positive site density strictly increases the same finite
infimum of the expected half-line rates. -/
theorem isGLB_halfLineEdge_bernoulli_lt_of_density_lt
    {p q : unitInterval} (hp : 0 < (p : ℝ)) (hpq : p < q) {α β : ℝ}
    (hα : IsGLB (range fun n : ℕ =>
      expectedBernoulliHalfLineEdge p (n + 1) / ((n : ℝ) + 1)) α)
    (hβ : IsGLB (range fun n : ℕ =>
      expectedBernoulliHalfLineEdge q (n + 1) / ((n : ℝ) + 1)) β) :
    α < β := by
  have hpq' : (p : ℝ) < (q : ℝ) := hpq
  exact sub_pos.mp ((sub_pos.mpr hpq').trans_le
    (density_sub_le_sub_isGLB_halfLineEdge_bernoulli hp hpq.le hα hβ))

end LPPDifferentiability.FinalDraft
