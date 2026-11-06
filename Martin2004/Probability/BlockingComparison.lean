/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Model.LastPassage.RowBlocks
public import Martin2004.Model.LastPassage.RowBlocksFine
public import Martin2004.Probability.RowBlockLaw
public import Martin2004.Shape.ExpectedRateShape
import LPP_Foundations.Model.LastPassage.Bounds
import LPP_Foundations.Probability.EnvironmentLaw
import LPP_Foundations.Probability.PassageMeasurable

/-!
# Lemma 4.4 of Martin (2004): blocking `r` sites of each row

Source: J. B. Martin, "Limiting shape for directed percolation models", Ann. Probab. 32 (2004).
For a weight law `F` with bounded support (`|X| <= K` almost surely)
and `F^(r)` the law of the sum of `r` independent copies, the shape functions satisfy

    `g_F(1, a) - g_{F^(r)}(1, a r) / r <= a r K`   (in the proof of Lemma 4.4).

If `r(a)` is a positive integer with `r(a) -> infinity` and `r(a) sqrt a -> 0` as `a` decreases to
`0`, then `(g_F(1, a) - g_{F^(r)}(1, a r) / r) / sqrt a -> 0` (Lemma 4.4 itself).

The proof follows Martin's argument. By the path correspondence (`RowBlocks.lean`) and the law
of the
block environment (`RowBlockLaw.lean`), the expected passage times to `(n r, m)` in the original
environment and to `(n, m)` in the block environment differ by at most `(r - 1) m K`. Divide by
`n r`, put `m = floor(a n r)` and let `n` tend to infinity along a fixed `r`.

The shape functions are given by their defining limits (`IsExpectedRateShape`), as in the
shape API; their existence is a hypothesis, supplied by the existence theorems.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace LPPDifferentiability

/-- Almost surely every site weight of the environment is at most `K` in absolute value. -/
private theorem ae_forall_abs_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (K : ℝ)
    (hK : ∀ᵐ t ∂μ, |t| ≤ K) : ∀ᵐ ω ∂environmentLaw μ, ∀ z : Lattice, |ω z| ≤ K := by
  rw [ae_all_iff]
  intro z
  have hmap : (environmentLaw μ).map (fun ω : Environment => ω z) = μ :=
    Measure.infinitePi_map_eval (fun _ : Lattice => μ) z
  exact ae_of_ae_map (p := fun t : ℝ => |t| ≤ K) (measurable_pi_apply z).aemeasurable
    (by rw [hmap]; exact hK)

/-- In the proof of Lemma 4.4, using (4.6): the expected passage times to `(n r, m)` in the original
environment and to `(n, m)` in the block environment differ by at most `(r - 1) m K`. -/
private theorem abs_integral_sub_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (K : ℝ)
    (hK : ∀ᵐ t ∂μ, |t| ≤ K) (r n m : ℕ) (hr : 1 ≤ r) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = (Measure.pi (fun _ : Fin r => μ)).map (fun y => ∑ i, y i)) :
    |(∫ ω, lastPassage ω 0 (n * r, m) ∂environmentLaw μ) -
        ∫ ω, lastPassage ω 0 (n, m) ∂environmentLaw ν| ≤ ((r : ℝ) - 1) * (m : ℝ) * K := by
  have hae := ae_forall_abs_le μ K hK
  have hBmeas : Measurable (fun (ω : Environment) (z : Lattice) =>
      ∑ j ∈ Finset.range r, ω ((r : ℤ) * z.1 + (j : ℤ), z.2)) :=
    measurable_pi_iff.2 fun z => Finset.measurable_sum _ fun j _ => measurable_pi_apply _
  -- the integral over the block environment is an integral over the original environment
  have hint : ∫ ω, lastPassage ω 0 (n, m) ∂environmentLaw ν =
      ∫ ω, lastPassage (fun z => ∑ j ∈ Finset.range r, ω ((r : ℤ) * z.1 + (j : ℤ), z.2))
        0 (n, m) ∂environmentLaw μ := by
    rw [← map_environmentLaw_blockField μ r hr ν hν]
    exact integral_map hBmeas.aemeasurable (measurable_lastPassage 0 (n, m)).aestronglyMeasurable
  -- the weights in the lattice are bounded, so both passage times differ by at most the constant
  have hdet : ∀ᵐ ω ∂environmentLaw μ,
      |lastPassage ω 0 (n * r, m) -
        lastPassage (fun z => ∑ j ∈ Finset.range r, ω ((r : ℤ) * z.1 + (j : ℤ), z.2)) 0 (n, m)| ≤
        ((r : ℝ) - 1) * (m : ℝ) * K :=
    hae.mono fun ω hω => abs_lastPassage_sub_blockPassage_le r n m hr K ω _ hω (fun z => rfl)
  have hf : Integrable (fun ω => lastPassage ω 0 (n * r, m)) (environmentLaw μ) :=
    Integrable.of_bound (measurable_lastPassage 0 (n * r, m)).aestronglyMeasurable
      (((n * r + m : ℕ) : ℝ) * K)
      (hae.mono fun ω hω => by
        rw [Real.norm_eq_abs]
        exact lastPassage_abs_le ω 0 (n * r, m) K hω)
  have hg : Integrable (fun ω => lastPassage
      (fun z => ∑ j ∈ Finset.range r, ω ((r : ℤ) * z.1 + (j : ℤ), z.2)) 0 (n, m))
      (environmentLaw μ) :=
    Integrable.of_bound ((measurable_lastPassage 0 (n, m)).comp hBmeas).aestronglyMeasurable
      (((n * r + m : ℕ) : ℝ) * K + ((r : ℝ) - 1) * (m : ℝ) * K)
      (by
        filter_upwards [hae, hdet] with ω hω hd
        rw [Real.norm_eq_abs]
        have h1 := abs_le.1 (show |lastPassage ω 0 (n * r, m)| ≤ ((n * r + m : ℕ) : ℝ) * K from
          lastPassage_abs_le ω 0 (n * r, m) K hω)
        have h2 := abs_le.1 hd
        exact abs_le.2 ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩)
  rw [hint, ← integral_sub hf hg]
  have hnorm := norm_integral_le_of_norm_le_const (μ := environmentLaw μ)
    (f := fun ω => lastPassage ω 0 (n * r, m) -
      lastPassage (fun z => ∑ j ∈ Finset.range r, ω ((r : ℤ) * z.1 + (j : ℤ), z.2)) 0 (n, m))
    (C := ((r : ℝ) - 1) * (m : ℝ) * K)
    (hdet.mono fun ω h => by rwa [Real.norm_eq_abs])
  simpa [Real.norm_eq_abs] using hnorm

/-- The arithmetic at the end of the proof of Lemma 4.4: dividing the comparison of expectations
by `n r` and using `m <= a n r` gives the bound `a r K`. -/
private theorem abs_quotient_sub_le {I J K α : ℝ} {n r M : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hM : (M : ℝ) ≤ n * (α * r))
    (hd : |I - J| ≤ ((r : ℝ) - 1) * (M : ℝ) * K) :
    |I / ((n * r : ℕ) : ℝ) - J / (n : ℝ) / (r : ℝ)| ≤ α * r * K := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hnr : (0 : ℝ) < (n : ℝ) * r := mul_pos hn' (by linarith)
  have hsub : I / ((n * r : ℕ) : ℝ) - J / (n : ℝ) / (r : ℝ) = (I - J) / ((n : ℝ) * r) := by
    push_cast
    rw [div_div, ← sub_div]
  rw [hsub, abs_div, abs_of_pos hnr, div_le_iff₀ hnr]
  have hpos : 0 ≤ (n : ℝ) * α * r * K := by positivity
  calc |I - J| ≤ ((r : ℝ) - 1) * (M : ℝ) * K := hd
    _ ≤ ((r : ℝ) - 1) * ((n : ℝ) * (α * r)) * K :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM (by linarith)) hK
    _ ≤ α * r * K * ((n : ℝ) * r) := by nlinarith [hpos]

/-- Martin (2004), Lemma 4.4, the explicit estimate in its proof: if `|X| <= K` almost surely, then
`|g_F(1, a) - g_{F^(r)}(1, a r) / r| <= a r K` for every positive integer `r`. Martin's display
has no absolute value; the argument bounds both signs, so the absolute value is kept here. Here `ν`
is the law of the sum of `r` independent copies of `μ`, and `g`, `G` are the shape functions of
`μ` and `ν`. -/
theorem abs_shape_sub_blockShape_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (K : ℝ)
    (hK : ∀ᵐ t ∂μ, |t| ≤ K) (r : ℕ) (hr : 1 ≤ r)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = (Measure.pi (fun _ : Fin r => μ)).map (fun y => ∑ i, y i))
    {g G : Quadrant → ℝ} (hg : IsExpectedRateShape μ g) (hG : IsExpectedRateShape ν G)
    (α : ℝ≥0) :
    |g (1, α) - G (1, α * (r : ℝ≥0)) / (r : ℝ)| ≤ (α : ℝ) * (r : ℝ) * K := by
  have hK0 : 0 ≤ K := by
    obtain ⟨t, ht⟩ := hK.exists
    exact le_trans (abs_nonneg t) ht
  have hu : Tendsto (fun n : ℕ => n * r) atTop atTop :=
    tendsto_atTop_mono (fun n => le_mul_of_one_le_right (Nat.zero_le n) hr) tendsto_id
  -- the first term tends to `g(1, a)` along the subsequence `n r`
  have ha : Tendsto (fun n : ℕ =>
      (∫ ω, lastPassage ω 0 (n * r, ⌊(n : ℝ) * ((α * (r : ℝ≥0) : ℝ≥0) : ℝ)⌋₊)
        ∂environmentLaw μ) / ((n * r : ℕ) : ℝ)) atTop (𝓝 (g (1, α))) := by
    refine Tendsto.congr (fun n => ?_) ((hg (1, α)).comp hu)
    have e1 : ⌊((n * r : ℕ) : ℝ) * ((1 : ℝ≥0) : ℝ)⌋₊ = n * r := by
      simp only [NNReal.coe_one, mul_one, Nat.floor_natCast]
    have e2 : ⌊((n * r : ℕ) : ℝ) * (α : ℝ)⌋₊ = ⌊(n : ℝ) * ((α * (r : ℝ≥0) : ℝ≥0) : ℝ)⌋₊ := by
      congr 1
      push_cast
      ring
    show (∫ ω, lastPassage ω 0 (⌊((n * r : ℕ) : ℝ) * ((1 : ℝ≥0) : ℝ)⌋₊,
        ⌊((n * r : ℕ) : ℝ) * (α : ℝ)⌋₊) ∂environmentLaw μ) / ((n * r : ℕ) : ℝ) = _
    rw [e1, e2]
  -- the second term tends to `G(1, a r)`
  have hb : Tendsto (fun n : ℕ =>
      (∫ ω, lastPassage ω 0 (n, ⌊(n : ℝ) * ((α * (r : ℝ≥0) : ℝ≥0) : ℝ)⌋₊)
        ∂environmentLaw ν) / (n : ℝ)) atTop (𝓝 (G (1, α * (r : ℝ≥0)))) := by
    refine Tendsto.congr (fun n => ?_) (hG (1, α * (r : ℝ≥0)))
    have e3 : ⌊(n : ℝ) * ((1 : ℝ≥0) : ℝ)⌋₊ = n := by simp
    show (∫ ω, lastPassage ω 0 (⌊(n : ℝ) * ((1 : ℝ≥0) : ℝ)⌋₊,
        ⌊(n : ℝ) * ((α * (r : ℝ≥0) : ℝ≥0) : ℝ)⌋₊) ∂environmentLaw ν) / (n : ℝ) = _
    rw [e3]
  -- the bound `a r K` holds for every `n`, hence in the limit
  have hbound : ∀ n : ℕ,
      |(∫ ω, lastPassage ω 0 (n * r, ⌊(n : ℝ) * ((α * (r : ℝ≥0) : ℝ≥0) : ℝ)⌋₊)
          ∂environmentLaw μ) / ((n * r : ℕ) : ℝ) -
        (∫ ω, lastPassage ω 0 (n, ⌊(n : ℝ) * ((α * (r : ℝ≥0) : ℝ≥0) : ℝ)⌋₊)
          ∂environmentLaw ν) / (n : ℝ) / (r : ℝ)| ≤ (α : ℝ) * (r : ℝ) * K := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.zero_mul, Nat.cast_zero, div_zero, zero_div, sub_zero, abs_zero]
      positivity
    · have hM : (⌊(n : ℝ) * ((α * (r : ℝ≥0) : ℝ≥0) : ℝ)⌋₊ : ℝ) ≤ n * ((α : ℝ) * r) := by
        have := Nat.floor_le (a := (n : ℝ) * ((α * (r : ℝ≥0) : ℝ≥0) : ℝ)) (by positivity)
        simpa using this
      exact abs_quotient_sub_le hr hn hK0 α.2 hM
        (abs_integral_sub_le μ K hK r n _ hr ν hν)
  exact le_of_tendsto ((ha.sub (hb.div_const (r : ℝ))).abs) (Eventually.of_forall hbound)

/-- Martin (2004), Lemma 4.4. Let `F` have bounded support, let `F^(k)`
be the law of the sum of `k` independent copies, and let `r(a)` be a positive integer with
`r(a) -> infinity` and `r(a) sqrt a -> 0` as `a` decreases to `0`. Then
`(g_F(1, a) - g_{F^(r(a))}(1, a r(a)) / r(a)) / sqrt a -> 0`. The shape functions `g` of `μ` and
`G k` of the `k`-fold sum law are given by their defining limits. -/
theorem martin_lemma_4_4 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hK : ∃ K : ℝ, ∀ᵐ t ∂μ, |t| ≤ K)
    (r : ℝ≥0 → ℕ)
    (hr : Tendsto (fun α => (r α : ℝ)) (𝓝[>] (0 : ℝ≥0)) atTop)
    (hrα : Tendsto (fun α : ℝ≥0 => (r α : ℝ) * Real.sqrt (α : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝 0))
    (ν : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (ν k)]
    (hν : ∀ k, ν k = (Measure.pi (fun _ : Fin k => μ)).map (fun y => ∑ i, y i))
    {g : Quadrant → ℝ} (hg : IsExpectedRateShape μ g)
    {G : ℕ → Quadrant → ℝ} (hG : ∀ k, 1 ≤ k → IsExpectedRateShape (ν k) (G k)) :
    Tendsto (fun α : ℝ≥0 =>
      (g (1, α) - G (r α) (1, α * (r α : ℝ≥0)) / (r α : ℝ)) / Real.sqrt (α : ℝ))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
  obtain ⟨K, hK⟩ := hK
  -- the bound `a r K` is `o(sqrt a)` when `r sqrt a -> 0`
  have hr1 : ∀ᶠ α in 𝓝[>] (0 : ℝ≥0), 1 ≤ r α := by
    filter_upwards [hr.eventually (eventually_ge_atTop (1 : ℝ))] with α hα
    exact_mod_cast hα
  have hpos : ∀ᶠ α in 𝓝[>] (0 : ℝ≥0), 0 < α := self_mem_nhdsWithin
  have hlim : Tendsto (fun α : ℝ≥0 => K * ((r α : ℝ) * Real.sqrt (α : ℝ)))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
    simpa using hrα.const_mul K
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hr1, hpos] with α hα1 hαpos
  have hest := abs_shape_sub_blockShape_le μ K hK (r α) hα1 (ν (r α)) (hν (r α)) hg
    (hG (r α) hα1) α
  have hs : 0 < Real.sqrt (α : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hαpos)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hs, div_le_iff₀ hs]
  have hsq : (α : ℝ) = Real.sqrt (α : ℝ) * Real.sqrt (α : ℝ) :=
    (Real.mul_self_sqrt α.2).symm
  calc |g (1, α) - G (r α) (1, α * (r α : ℝ≥0)) / (r α : ℝ)|
      ≤ (α : ℝ) * (r α : ℝ) * K := hest
    _ = (Real.sqrt (α : ℝ) * Real.sqrt (α : ℝ)) * (r α : ℝ) * K := by rw [← hsq]
    _ = K * ((r α : ℝ) * Real.sqrt (α : ℝ)) * Real.sqrt (α : ℝ) := by ring

end LPPDifferentiability
