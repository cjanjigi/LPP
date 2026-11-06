/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.BernoulliShapeBound
public import Martin2004.Probability.BernoulliSplitting
public import Martin2004.Probability.LayerCakePassage

@[expose] public section

/-!
# The finite-box comparison of two mean last-passage values (Martin 2004, Lemma 4.2)

Martin (2004), Lemma 4.2. This module carries the part of the proof that holds in a finite box
`(n, k)`, before any limit is taken:

* `bernoulli_pair_le`: the two Bernoulli last-passage means of the splitting, minus the number of
  sites, are at most `(n + k)(F2 - F1) + 2 sqrt((n + k)(k + 1)) |F1 - F2|^(1/2)`. This applies the
  finite-size form of Lemma 4.1 at `[F2 - F1]_+` and at `1 - [F1 - F2]_+`.
* `integrable_and_integral_cdf_sub`: `F2 - F1` is integrable, with integral
  `m1 - m2`, where `m1` and `m2` are the means.
* `lastPassage_mean_sub_le_cdf_bound`: the finite-box inequality.
-/

open MeasureTheory ProbabilityTheory Set

namespace LPPDifferentiability

/-! ### The pointwise bound at one level -/

/-- The two square-root terms of Lemma 4.1 add up to one square root, because at most one of the
two Bernoulli parameters `x` and `y` is nonzero. -/
private theorem sqrt_pair_le (M : ℝ) (hM : 0 ≤ M) (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hxy : x = 0 ∨ y = 0) :
    Real.sqrt (M * (x * (1 - x))) + Real.sqrt (M * ((1 - y) * (1 - (1 - y)))) ≤
      Real.sqrt M * Real.sqrt (x + y) := by
  rcases hxy with rfl | rfl
  · have h0 : M * (0 * (1 - 0)) = 0 := by ring
    rw [h0, Real.sqrt_zero, zero_add, ← Real.sqrt_mul hM]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg y]) hM)
  · have h0 : M * ((1 - 0) * (1 - (1 - 0))) = 0 := by ring
    rw [h0, Real.sqrt_zero, add_zero, ← Real.sqrt_mul hM]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg x]) hM)

/-- The pointwise bound in the proof of Martin (2004), Lemma 4.2, at one level. For `u = F2(x)` and
`v = F1(x)`, the two Bernoulli last-passage means of the splitting, minus the number of sites
`n + k`, are at most `(n + k)(u - v) + 2 sqrt((n + k)(k + 1)) |u - v|^(1/2)`. -/
theorem bernoulli_pair_le (u v : ℝ) (hu : u - v ≤ 1) (hv : v - u ≤ 1) (n k : ℕ) :
    ∫ ω, lastPassage ω 0 (n, k) ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0
        (Set.projIcc (0 : ℝ) 1 zero_le_one (u - v))) +
      ∫ ω, lastPassage ω 0 (n, k) ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0
        (unitInterval.symm (Set.projIcc (0 : ℝ) 1 zero_le_one (v - u)))) -
      ((n + k : ℕ) : ℝ) ≤
    ((n + k : ℕ) : ℝ) * (u - v) +
      2 * Real.sqrt (((n + k : ℕ) : ℝ) * ((k : ℝ) + 1)) * |u - v| ^ (1 / 2 : ℝ) := by
  set p₁ : unitInterval := Set.projIcc (0 : ℝ) 1 zero_le_one (u - v)
  set p₂ : unitInterval := Set.projIcc (0 : ℝ) 1 zero_le_one (v - u)
  have h1 := integral_lastPassage_le_bernoulli p₁ n k
  have h2 := integral_lastPassage_le_bernoulli (unitInterval.symm p₂) n k
  have hs : ((unitInterval.symm p₂ : unitInterval) : ℝ) = 1 - (p₂ : ℝ) :=
    unitInterval.coe_symm_eq p₂
  rw [hs] at h2
  have hc₁ : (p₁ : ℝ) = max 0 (min 1 (u - v)) := Set.coe_projIcc _ _ _ _
  have hc₂ : (p₂ : ℝ) = max 0 (min 1 (v - u)) := Set.coe_projIcc _ _ _ _
  rw [min_eq_right hu] at hc₁
  rw [min_eq_right hv] at hc₂
  have hp₁0 : 0 ≤ (p₁ : ℝ) := p₁.2.1
  have hp₁1 : (p₁ : ℝ) ≤ 1 := p₁.2.2
  have hp₂0 : 0 ≤ (p₂ : ℝ) := p₂.2.1
  have hp₂1 : (p₂ : ℝ) ≤ 1 := p₂.2.2
  -- at most one of the two parameters is nonzero, and they add to `|u - v|`
  have hcases : ((p₁ : ℝ) = 0 ∨ (p₂ : ℝ) = 0) ∧ (p₁ : ℝ) - p₂ = u - v ∧
      (p₁ : ℝ) + p₂ = |u - v| := by
    rcases le_total v u with h | h
    · have e1 : (p₁ : ℝ) = u - v := by rw [hc₁]; exact max_eq_right (by linarith)
      have e2 : (p₂ : ℝ) = 0 := by rw [hc₂]; exact max_eq_left (by linarith)
      exact ⟨Or.inr e2, by rw [e1, e2]; ring, by rw [e1, e2, abs_of_nonneg (by linarith)]; ring⟩
    · have e1 : (p₁ : ℝ) = 0 := by rw [hc₁]; exact max_eq_left (by linarith)
      have e2 : (p₂ : ℝ) = v - u := by rw [hc₂]; exact max_eq_right (by linarith)
      exact ⟨Or.inl e1, by rw [e1, e2]; ring,
        by rw [e1, e2, abs_of_nonpos (by linarith)]; ring⟩
  obtain ⟨hor, hdiff, hsum⟩ := hcases
  have hM : (0 : ℝ) ≤ ((n + k : ℕ) : ℝ) * ((k : ℝ) + 1) := by positivity
  have key := sqrt_pair_le (((n + k : ℕ) : ℝ) * ((k : ℝ) + 1)) hM p₁ p₂ hp₁0 hp₁1 hp₂0 hp₂1 hor
  rw [hsum] at key
  have hlin : ((n + k : ℕ) : ℝ) * (p₁ : ℝ) - ((n + k : ℕ) : ℝ) * (p₂ : ℝ) =
      ((n + k : ℕ) : ℝ) * (u - v) := by rw [← hdiff]; ring
  rw [← Real.sqrt_eq_rpow]
  nlinarith [h1, h2, key, hlin]

/-! ### The mean of the difference of distribution functions -/

/-- Martin (2004), proof of Lemma 4.2. For two laws with integrable identity, `F2 - F1` is
integrable and its integral is `m1 - m2`. The layer cake `integral_layerCake_sub` is applied on the
product law `mu1 x mu2` to the pair `(x, y)`, and Fubini's theorem exchanges the integral over the
level `s` with the one over the pair; the probability `P(y <= s < x) - P(x <= s < y)` is
`F2(s) - F1(s)` by independence of the pair. -/
theorem integrable_and_integral_cdf_sub (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (h₁ : Integrable (fun t : ℝ => t) μ₁)
    (h₂ : Integrable (fun t : ℝ => t) μ₂) :
    Integrable (fun s : ℝ => μ₂.real (Iic s) - μ₁.real (Iic s)) ∧
      ∫ s : ℝ, (μ₂.real (Iic s) - μ₁.real (Iic s)) =
        (∫ t : ℝ, t ∂μ₁) - ∫ t : ℝ, t ∂μ₂ := by
  set P : Measure (ℝ × ℝ) := μ₁.prod μ₂ with hP
  have ia : Integrable (fun q : ℝ × ℝ => q.1) P := h₁.comp_fst μ₂
  have ib : Integrable (fun q : ℝ × ℝ => q.2) P := h₂.comp_snd μ₁
  let F : (ℝ × ℝ) × ℝ → ℝ := fun r =>
    (Ico r.1.2 r.1.1).indicator (fun _ => (1 : ℝ)) r.2 -
      (Ico r.1.1 r.1.2).indicator (fun _ => (1 : ℝ)) r.2
  have hF : Integrable F (P.prod volume) :=
    (integrable_indicator_Ico_prod P (fun q => q.1) (fun q => q.2) measurable_fst measurable_snd
      ia ib).sub
    (integrable_indicator_Ico_prod P (fun q => q.2) (fun q => q.1) measurable_snd measurable_fst
      ib ia)
  -- for each level `s`, the probabilities of the two events by independence
  have hinner : ∀ s : ℝ, ∫ q, F (q, s) ∂P = μ₂.real (Iic s) - μ₁.real (Iic s) := by
    intro s
    have hA : (fun q : ℝ × ℝ => (Ico q.2 q.1).indicator (fun _ => (1 : ℝ)) s) =
        (Ioi s ×ˢ Iic s).indicator (fun _ => (1 : ℝ)) := by
      funext q
      by_cases h : s ∈ Ico q.2 q.1
      · rw [indicator_of_mem h, indicator_of_mem]
        exact ⟨h.2, h.1⟩
      · rw [indicator_of_notMem h, indicator_of_notMem]
        exact fun hq => h ⟨hq.2, hq.1⟩
    have hB : (fun q : ℝ × ℝ => (Ico q.1 q.2).indicator (fun _ => (1 : ℝ)) s) =
        (Iic s ×ˢ Ioi s).indicator (fun _ => (1 : ℝ)) := by
      funext q
      by_cases h : s ∈ Ico q.1 q.2
      · rw [indicator_of_mem h, indicator_of_mem]
        exact ⟨h.1, h.2⟩
      · rw [indicator_of_notMem h, indicator_of_notMem]
        exact fun hq => h ⟨hq.1, hq.2⟩
    have hA' : ∫ q, (Ico q.2 q.1).indicator (fun _ => (1 : ℝ)) s ∂P =
        μ₁.real (Ioi s) * μ₂.real (Iic s) := by
      rw [hA, integral_indicator_const _ (measurableSet_Ioi.prod measurableSet_Iic)]
      simp [Measure.real, hP, Measure.prod_prod, ENNReal.toReal_mul]
    have hB' : ∫ q, (Ico q.1 q.2).indicator (fun _ => (1 : ℝ)) s ∂P =
        μ₁.real (Iic s) * μ₂.real (Ioi s) := by
      rw [hB, integral_indicator_const _ (measurableSet_Iic.prod measurableSet_Ioi)]
      simp [Measure.real, hP, Measure.prod_prod, ENNReal.toReal_mul]
    have hiA : Integrable (fun q : ℝ × ℝ => (Ico q.2 q.1).indicator (fun _ => (1 : ℝ)) s) P := by
      rw [hA]
      exact (integrable_indicator_iff (measurableSet_Ioi.prod measurableSet_Iic)).2
        (integrableOn_const (by simp) (by simp))
    have hiB : Integrable (fun q : ℝ × ℝ => (Ico q.1 q.2).indicator (fun _ => (1 : ℝ)) s) P := by
      rw [hB]
      exact (integrable_indicator_iff (measurableSet_Iic.prod measurableSet_Ioi)).2
        (integrableOn_const (by simp) (by simp))
    have hc₁ : μ₁.real (Ioi s) = 1 - μ₁.real (Iic s) := by
      rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ]
    have hc₂ : μ₂.real (Ioi s) = 1 - μ₂.real (Iic s) := by
      rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ]
    show ∫ q, ((Ico q.2 q.1).indicator (fun _ => (1 : ℝ)) s -
      (Ico q.1 q.2).indicator (fun _ => (1 : ℝ)) s) ∂P = _
    rw [integral_sub hiA hiB, hA', hB', hc₁, hc₂]
    ring
  have hint : Integrable (fun s : ℝ => ∫ q, F (q, s) ∂P) volume := hF.integral_prod_right
  have hfun : (fun s : ℝ => ∫ q, F (q, s) ∂P) =
      fun s : ℝ => μ₂.real (Iic s) - μ₁.real (Iic s) := funext hinner
  rw [hfun] at hint
  refine ⟨hint, ?_⟩
  have hswap : ∫ q, ∫ s, F (q, s) ∂volume ∂P = ∫ s, ∫ q, F (q, s) ∂P ∂volume :=
    integral_integral_swap hF
  calc ∫ s : ℝ, (μ₂.real (Iic s) - μ₁.real (Iic s))
      = ∫ s : ℝ, ∫ q, F (q, s) ∂P := by simp only [hinner]
    _ = ∫ q, ∫ s, F (q, s) ∂volume ∂P := hswap.symm
    _ = ∫ q : ℝ × ℝ, (q.1 - q.2) ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall fun q => integral_layerCake_sub q.1 q.2)
    _ = (∫ t : ℝ, t ∂μ₁) - ∫ t : ℝ, t ∂μ₂ := by
        rw [integral_sub ia ib, hP, integral_fun_fst (fun t : ℝ => t),
          integral_fun_snd (fun t : ℝ => t)]
        simp

/-! ### The finite-box inequality -/

/-- Martin (2004), proof of Lemma 4.2, in a finite box `(n, k)`. If the square root of `|F1 - F2|`
is integrable, the mean last passage for law `mu1` minus that for law `mu2` is at most
`(n + k)(m1 - m2) + 2 sqrt((n + k)(k + 1))` times the integral of `|F1 - F2|^(1/2)`. -/
theorem lastPassage_mean_sub_le_cdf_bound (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (h₁ : Integrable (fun t : ℝ => t) μ₁)
    (h₂ : Integrable (fun t : ℝ => t) μ₂)
    (hG : Integrable (fun s : ℝ => |μ₁.real (Iic s) - μ₂.real (Iic s)| ^ (1 / 2 : ℝ)))
    (n k : ℕ) :
    ∫ ω, lastPassage ω 0 (n, k) ∂environmentLaw μ₁ -
        ∫ ω, lastPassage ω 0 (n, k) ∂environmentLaw μ₂ ≤
      ((n + k : ℕ) : ℝ) * ((∫ t : ℝ, t ∂μ₁) - ∫ t : ℝ, t ∂μ₂) +
        2 * Real.sqrt (((n + k : ℕ) : ℝ) * ((k : ℝ) + 1)) *
          ∫ s : ℝ, |μ₁.real (Iic s) - μ₂.real (Iic s)| ^ (1 / 2 : ℝ) := by
  obtain ⟨hI, hm⟩ := integrable_and_integral_cdf_sub μ₁ μ₂ h₁ h₂
  have hsplit := lastPassage_mean_sub_le_integral_bernoulli μ₁ μ₂ h₁ h₂ (n, k)
  have hintg := integrable_bernoulli_splitting_integrand μ₁ μ₂ h₁ h₂ (n, k)
  have hR : Integrable (fun s : ℝ =>
      ((n + k : ℕ) : ℝ) * (μ₂.real (Iic s) - μ₁.real (Iic s)) +
        2 * Real.sqrt (((n + k : ℕ) : ℝ) * ((k : ℝ) + 1)) *
          |μ₁.real (Iic s) - μ₂.real (Iic s)| ^ (1 / 2 : ℝ)) :=
    (hI.const_mul _).add (hG.const_mul _)
  have hmono := integral_mono hintg hR fun s => by
    have h := bernoulli_pair_le (μ₂.real (Iic s)) (μ₁.real (Iic s))
      (by linarith [measureReal_le_one (μ := μ₂) (s := Iic s),
        measureReal_nonneg (μ := μ₁) (s := Iic s)])
      (by linarith [measureReal_le_one (μ := μ₁) (s := Iic s),
        measureReal_nonneg (μ := μ₂) (s := Iic s)]) n k
    rw [abs_sub_comm] at h
    exact h
  rw [integral_add (hI.const_mul _) (hG.const_mul _), integral_const_mul, integral_const_mul,
    hm] at hmono
  exact hsplit.trans hmono

end LPPDifferentiability
