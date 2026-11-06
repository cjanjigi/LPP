/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.TiltLimit
public import Differentiability.Probability.ShortCrossingAbundance
public import Martin2004.Probability.WeakNegativeShape
public import Differentiability.Analysis.RecordScales

/-!
# Characteristic lengths and record scales

Proposition 4.3 and Lemma 4.4 of the differentiability preprint, for the crossing probabilities
`P k n = P(E(2^k, n))` from Lemma 4.2 of the preprint. The record-scale arithmetic needs two
inputs: for large `k`, `P k (2^(3k)) ≤ q0`, which is Lemma 4.2 at `s = 2^k` (where
`⌈(2^k)³⌉₊ = 2^(3k)`), and the short-crossing estimate (4.4) of the preprint, whose shape is
identified with `g` by uniqueness of the shape function.
-/

public section

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

/-- `⌈(2^k)³⌉₊ = 2^(3k)`: at `s = 2^k` the cubic length is a natural power of two. -/
private theorem ceil_two_pow_cube (k : ℕ) : ⌈((2 : ℝ) ^ k) ^ 3⌉₊ = 2 ^ (3 * k) := by
  have h : ((2 : ℝ) ^ k) ^ 3 = ((2 ^ (3 * k) : ℕ) : ℝ) := by
    push_cast
    ring
  rw [h, Nat.ceil_natCast]

/-- Proposition 4.3 and Lemma 4.4 of the differentiability preprint, for the crossing
probabilities `P k n = P(E(2^k, n))`, where `E(s, n)` is the crossing event of Lemma 4.2
(free start on level `0`, strip `8 s`, weight above
`g(ξ) n - K s`, `K = 100 (1 + |dl| + |dr|)`). The conclusion is that of
`scale_record_arithmetic` for this `P` and `q0`: the dyadic characteristic
lengths `2^(m k)` with `m k ≤ 3 k`, `2^(m k)/2^k → ∞` and the threshold
property, their minimizers `nk k`, an infinite set of record indices, and the
trial-probability and mesh bounds at record indices. -/
theorem characteristic_length_records
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0:ℝ), (μ (Ioi t)) ^ (1/2:ℝ)) < ∞)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (Gtop : ℝ)
    (htop : Tendsto (fun m : ℕ => (∫ ω : Environment, lastPassage (fun z =>
      if (ω z : EReal) = sSup ((fun t : ℝ => (t : EReal)) '' μ.support) then (1 : ℝ) else 0)
        0 (⌊(m : ℝ) * a⌋₊, ⌊(m : ℝ) * (1 - a)⌋₊) ∂environmentLaw μ) / (m : ℝ))
      atTop (𝓝 Gtop))
    (hgap : Gtop < 1) (q0 : ℝ) (hq0₀ : 0 < q0) (hq0₁ : q0 < 1) :
    let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
    let dl : ℝ := derivWithin H (Iio 0) 0
    let dr : ℝ := derivWithin H (Ioi 0) 0
    let K : ℝ := 100 * (1 + |dl| + |dr|)
    let P : ℕ → ℕ → ℝ := fun k n => (environmentLaw μ).real {ω : Environment |
      ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
        (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤
          8 * (2 : ℝ) ^ k) ∧
          g (toQuadrant (a, 1 - a)) * (n : ℝ) - K * (2 : ℝ) ^ k < pathWeight ω q}
    ∃ k0 : ℕ, 0 < k0 ∧ ∃ (m nk : ℕ → ℕ) (K : Set ℕ),
      Tendsto (fun k : ℕ => (2 : ℝ) ^ m k / 2 ^ k) atTop atTop ∧
      (∀ k : ℕ, k0 ≤ k →
        (∃ n : ℕ, (2 : ℝ) ^ m k / 2 < n ∧ (n : ℝ) ≤ 2 ^ m k ∧ P k n ≤ q0) ∧
        (∀ j : ℕ, (∃ n : ℕ, (2 : ℝ) ^ j / 2 < n ∧ (n : ℝ) ≤ 2 ^ j ∧ P k n ≤ q0) →
          m k ≤ j) ∧
        m k ≤ 3 * k ∧
        (∀ n : ℕ, 1 ≤ n → (n : ℝ) < 2 ^ m k / 2 → q0 < P k n) ∧
        ((2 : ℝ) ^ m k / 2 < nk k ∧ (nk k : ℝ) ≤ 2 ^ m k ∧ P k (nk k) ≤ q0 ∧
          ∀ n : ℕ, (2 : ℝ) ^ m k / 2 < n → (n : ℝ) ≤ 2 ^ m k → P k (nk k) ≤ P k n)) ∧
      K.Infinite ∧
      (∀ k ∈ K, k0 ≤ k ∧ ∀ j : ℕ, j ≤ k - k0 →
        (2 : ℝ) ^ m k / 2 ^ (4 * j) ≤ 2 ^ m (k - j)) ∧
      (∀ k ∈ K, 4 * k0 + 3 ≤ k → ∀ j : ℕ, j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
        (∀ l : ℕ, 1 ≤ l → (l : ℝ) < 2 ^ (m k - 4 * j - 1) → q0 < P (k - j) l) ∧
        (1 < (2 : ℝ) ^ (m k - 4 * j - 1) →
          (2 : ℝ) ^ (m k - 4 * j - 1) ≤ ((2 : ℝ) ^ (k - j)) ^ 3 / 2)) := by
  intro H dl dr K P
  have hpow : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  -- Input (i): Lemma 4.2 at `s = 2^k`, where `⌈(2^k)³⌉₊ = 2^(3k)`.
  have hA := tilt_crossing_tendsto_zero μ hneg hpos g hgcont hghom hgconc hgshape
    a ha₀ ha₁ Gtop htop hgap
  dsimp only at hA
  have htilt : ∀ᶠ k : ℕ in atTop, P k (2 ^ (3 * k)) ≤ q0 := by
    filter_upwards [(hA.comp hpow).eventually (gt_mem_nhds hq0₀)] with k hk
    simp only [Function.comp_apply] at hk
    rw [ceil_two_pow_cube k] at hk
    exact hk.le
  -- Input (ii): the estimate (4.4), with its shape identified with `g` by uniqueness.
  obtain ⟨g', ⟨hg'c, hg'h, hg'conc, hg'shape, habund⟩, -⟩ :=
    short_crossing_abundance μ hneg hpos
  obtain ⟨_, -, huniq⟩ := exists_unique_shape_of_negative_moment_and_positive_tail μ hneg hpos
  have hgg : g' = g := (huniq g' ⟨hg'c, hg'h, hg'conc, hg'shape⟩).trans
    (huniq g ⟨hgcont, hghom, hgconc, hgshape⟩).symm
  rw [hgg] at habund
  have hK : 0 < K := by
    change 0 < 100 * (1 + |dl| + |dr|)
    positivity
  have hshort : ∀ C : ℝ, 0 < C → ∀ c : ℝ, c < 1 →
      ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ C * 2 ^ k → c < P k n := by
    intro C hC c hc
    obtain ⟨s0, hs0⟩ := habund a ha₀ ha₁ K C hK hC c hc
    filter_upwards [hpow.eventually_ge_atTop s0] with k hk n hn hnC
    exact hs0 _ hk n hn hnC
  exact scale_record_arithmetic P q0 hq0₁ htilt hshort

end LPPDifferentiability
