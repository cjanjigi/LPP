/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.CoarseBlackBlocks
public import Differentiability.Probability.BlackBlockIndependence
public import Differentiability.Probability.HalfLineEdgeDeviation
public import Differentiability.Probability.SparseCoarsePaths
public import Differentiability.Probability.WhiteBlockBound
import LPP_Foundations.Model.LastPassage.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Decay of the top passage time beyond the edge

Assume the weights are at most one, equal to one with positive probability, and that the
mean half-line edge at some length `L` is below `c L`. Let `c < s ≤ 1`. Then for some
`δ, A, B > 0`, the probability that the top passage time to `(k, ℓ)` is at least
`(1 - δ)(k + ℓ)` is at most `A e^{-B k}`, whenever `s (k + ℓ) ≤ k`. The proof also gives the
bound `A e^{-B (k + ℓ)}`.

The proof is a coarse-graining argument:

* Pick `c₁` strictly between `c` and `s`, a scale `N` and a density `ρ` between
  `(1 - s) / (1 - c₁)` and `1`.
* The block-white probability is at most `(N + 1)` times the edge deviation at scale `N`
  (`white_block_probability_le` and `halfLineEdge_upper_deviation`). Choose `N` so that it is
  below the cutoff of the sparse-path lemma (`exists_sparse_good_coarse_path_cutoff`).
* Black blocks at separation larger than two are independent. The sparse-path lemma
  then bounds the chance that some coarse path has at most a `ρ` fraction of black blocks.
* A dense top path yields such a coarse path (`exists_coarse_of_dense_passage`), once the
  density `δ` is replaced by `δ + 1 / (k + ℓ)`. This absorbs the one-site difference between
  the start-collected passage time and the end-collected count used there.
* The coarse path has `⌊(k + ℓ) / N⌋ - 2` steps; this indexing differs slightly from the
  written argument. The resulting slack and the case `3 N > k + ℓ` are absorbed in `A`.

## Main results

- `top_passage_beyond_edge_decay_total`: the decay bound `A e^{-B (k + ℓ)}`.
- `top_passage_beyond_edge_decay`: the decay bound `A e^{-B k}`.

## References

- Georgiou, Rassoul-Agha and Seppäläinen (manuscript in preparation), the proposition on
  exponential decay of the top passage time beyond the edge.
-/

@[expose] public section

namespace LPPDifferentiability

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

/-- Two filters over a finite type with pointwise equivalent predicates have equal size. -/
private theorem card_filter_congr {α : Type*} [Fintype α] {p q : α → Prop}
    {i1 : DecidablePred p} {i2 : DecidablePred q} (h : ∀ a, p a ↔ q a) :
    (@Finset.filter α p i1 Finset.univ).card = (@Finset.filter α q i2 Finset.univ).card := by
  have e : @Finset.filter α p i1 Finset.univ = @Finset.filter α q i2 Finset.univ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h a
  rw [e]

/-- The start-collected weight of a path exceeds the end-collected weight by at most one,
because the 0/1 top field lies in `[0, 1]`. -/
private theorem pathWeight_topField_le_succ_sum (ω : Environment) {k ℓ : ℕ}
    (p : Path 0 (k, ℓ)) :
    pathWeight (topField ω) p - 1 ≤ ∑ i : Fin (k + ℓ), topField ω (p.vertex i.succ) := by
  have h0 : topField ω (p.vertex 0) ≤ 1 := by
    unfold topField
    split_ifs <;> norm_num
  have hl : 0 ≤ topField ω (p.vertex (Fin.last (k + ℓ))) := by
    unfold topField
    split_ifs <;> norm_num
  have e1 : ∑ i : Fin (k + ℓ + 1), topField ω (p.vertex i) =
      topField ω (p.vertex 0) + ∑ i : Fin (k + ℓ), topField ω (p.vertex i.succ) :=
    Fin.sum_univ_succ _
  have e2 : ∑ i : Fin (k + ℓ + 1), topField ω (p.vertex i) =
      ∑ i : Fin (k + ℓ), topField ω (p.vertex i.castSucc) +
        topField ω (p.vertex (Fin.last (k + ℓ))) :=
    Fin.sum_univ_castSucc _
  have hpw : pathWeight (topField ω) p =
      ∑ i : Fin (k + ℓ), topField ω (p.vertex i.castSucc) := rfl
  rw [hpw]
  linarith

open Classical in
/-- A top path of density `1 - δ` from the origin gives a coarse path with few black blocks,
with `δ` replaced by `δ + 1 / (k + ℓ)` (the difference between the two collection
conventions) and the extra `1` written out. -/
private theorem exists_coarse_of_dense_passage (ω : Environment) (N : ℕ) (hN : 0 < N)
    (c₁ s δ : ℝ) (hc₁ : c₁ < 1) (k ℓ : ℕ) (hks : s * (k + ℓ) ≤ k) (hlen : 3 * N ≤ k + ℓ)
    (hω : (1 - δ) * (k + ℓ) ≤ lastPassage (topField ω) 0 (k, ℓ)) :
    ∃ q : Fin ((k + ℓ) / N - 2 + 1) → ℕ × ℕ, q 0 = (0, 0) ∧
      (∀ i : Fin ((k + ℓ) / N - 2), q i.succ = q i.castSucc + (1, 0) ∨
        q i.succ = q i.castSucc + (0, 1)) ∧
      ((Finset.univ.filter fun j =>
          IsBlackBlock (topSites ω) N c₁ (((q j).1 : ℤ), ((q j).2 : ℤ))).card : ℝ) ≤
        δ * (k + ℓ) + 1 + (1 - s) * (k + ℓ) / ((1 - c₁) * N) := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage (topField ω) 0 (k, ℓ)
  have hpos : (0 : ℝ) < (k : ℝ) + ℓ := by
    have h3 : 0 < k + ℓ := lt_of_lt_of_le (by omega) hlen
    exact_mod_cast h3
  have hinv : ((k : ℝ) + ℓ)⁻¹ * ((k : ℝ) + ℓ) = 1 := inv_mul_cancel₀ hpos.ne'
  have hsum : (1 - (δ + 1 / ((k : ℝ) + ℓ))) * ((k : ℝ) + ℓ) ≤
      ∑ i : Fin (k + ℓ), (if p.vertex i.succ ∈ topSites ω then (1 : ℝ) else 0) := by
    have h1 := pathWeight_topField_le_succ_sum ω p
    have h2 : ∑ i : Fin (k + ℓ), (if p.vertex i.succ ∈ topSites ω then (1 : ℝ) else 0) =
        ∑ i : Fin (k + ℓ), topField ω (p.vertex i.succ) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hz : ω (p.vertex i.succ) = 1 <;> simp [topField, topSites, hz]
    have h3 : (1 - (δ + 1 / ((k : ℝ) + ℓ))) * ((k : ℝ) + ℓ) =
        (1 - δ) * ((k : ℝ) + ℓ) - 1 := by
      linear_combination (-1 : ℝ) * hinv
    rw [h2, h3]
    linarith
  obtain ⟨q, hq0, hqs, hqc⟩ := coarse_path_few_black_blocks (topSites ω) N hN c₁ s
    (δ + 1 / ((k : ℝ) + ℓ)) hc₁ k ℓ hks hlen p (by convert hsum)
  refine ⟨q, hq0, hqs, ?_⟩
  have h4 : (δ + 1 / ((k : ℝ) + ℓ)) * ((k : ℝ) + ℓ) = δ * ((k : ℝ) + ℓ) + 1 := by
    linear_combination hinv
  linarith



/-- The scale `N`: `(N + 1) A e^{-B N}` is eventually below any positive cutoff. -/
private theorem exists_scale (A B ζ : ℝ) (hB : 0 < B) (hζ : 0 < ζ) :
    ∃ N : ℕ, 0 < N ∧ ((N : ℝ) + 1) * (A * Real.exp (-(B * N))) ≤ ζ := by
  have hg : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hlin : Tendsto (fun N : ℕ => B * (N : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hB tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun N : ℕ => (B * (N : ℝ)) * Real.exp (-(B * (N : ℝ)))) atTop (𝓝 0) :=
    hg.comp hlin
  have h2 : Tendsto (fun N : ℕ => Real.exp (-(B * (N : ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  have h4 : Tendsto (fun N : ℕ => A * (B⁻¹ * ((B * (N : ℝ)) * Real.exp (-(B * (N : ℝ)))) +
      Real.exp (-(B * (N : ℝ))))) atTop (𝓝 (A * (B⁻¹ * 0 + 0))) :=
    ((h1.const_mul B⁻¹).add h2).const_mul A
  rw [show A * (B⁻¹ * 0 + 0) = 0 by ring] at h4
  have hB' : B⁻¹ * B = 1 := inv_mul_cancel₀ hB.ne'
  have ht : Tendsto (fun N : ℕ => ((N : ℝ) + 1) * (A * Real.exp (-(B * (N : ℝ)))))
      atTop (𝓝 0) := by
    refine Tendsto.congr (fun N => ?_) h4
    linear_combination (A * (N : ℝ) * Real.exp (-(B * (N : ℝ)))) * hB'
  obtain ⟨N, hN⟩ := ((ht.eventually (ge_mem_nhds hζ)).and (eventually_gt_atTop 0)).exists
  exact ⟨N, hN.2, hN.1⟩

/-- The number `⌊n / N⌋ - 2` of coarse steps is at least `n / N - 3`. This is the slack
between `m + 3` and `m + 1` in the indexing fix. -/
private theorem floor_div_bounds (n N : ℕ) (hN : 0 < N) (h3 : 3 * N ≤ n) :
    (n : ℝ) / N - 3 < (((n / N - 2 : ℕ)) : ℝ) := by
  have hQ3 : 3 ≤ n / N := (Nat.le_div_iff_mul_le hN).2 h3
  have hMn : n / N - 2 + 2 = n / N := Nat.sub_add_cancel (by omega)
  have hMQ : (((n / N - 2 : ℕ)) : ℝ) + 2 = ((n / N : ℕ) : ℝ) := by exact_mod_cast hMn
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdm : (N : ℝ) * ((n / N : ℕ) : ℝ) + ((n % N : ℕ) : ℝ) = n := by
    exact_mod_cast Nat.div_add_mod n N
  have hmod : ((n % N : ℕ) : ℝ) < N := by exact_mod_cast Nat.mod_lt n hN
  have hxN : ((n : ℝ) / N) * N = n := (eq_div_iff hNr.ne').1 rfl
  have h5 : ((n : ℝ) / N) * N < ((((n / N : ℕ) : ℝ)) + 1) * N := by
    linarith
  have hxQ := lt_of_mul_lt_mul_right h5 hNr.le
  linarith

/-- A lower bound `4 ≤ η x` from `4 N / η ≤ x N`. -/
private theorem scaled_ge (N x η n : ℝ) (hN : 0 < N) (hη : 0 < η) (hx : x * N = n)
    (h : 4 * N / η ≤ n) : 4 ≤ η * x := by
  have h7 := (div_le_iff₀ hη).1 h
  rw [← hx] at h7
  have h8 : 4 * N ≤ (η * x) * N := le_of_le_of_eq h7 (by ring)
  exact le_of_mul_le_mul_right h8 hN

/-- The real inequality behind the density bound: if `ρ (M + 1)` dominates `ρ (x - 2)` and
`(ρ - r) x ≥ 4`, then the budget `(ρ - r) x / 4 + 1 + r x` fits under `ρ (M + 1)`. -/
private theorem density_arith (ρ r x M : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hx4 : 4 ≤ (ρ - r) * x) (hM : x - 2 ≤ M + 1) :
    (ρ - r) * x / 4 + 1 + r * x ≤ ρ * (M + 1) := by
  nlinarith [mul_nonneg hρ0.le (sub_nonneg.2 hM)]

/-- For `k + ℓ` large compared with `N`, the black-block budget of the dense path fits under
`ρ` times the number of coarse sites (the choice of `δ`, `n₀` in the proof). -/
private theorem budget_le (N k ℓ : ℕ) (hN : 0 < N) (s c₁ ρ r : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hrdef : r = (1 - s) / (1 - c₁)) (hη : 0 < ρ - r)
    (hn₀ : 4 * (N : ℝ) / (ρ - r) ≤ (k : ℝ) + ℓ) (h3N : 3 * N ≤ k + ℓ) :
    (ρ - r) / (4 * N) * ((k : ℝ) + ℓ) + 1 + (1 - s) * ((k : ℝ) + ℓ) / ((1 - c₁) * N) ≤
      ρ * ((((k + ℓ) / N - 2 : ℕ) : ℝ) + 1) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = ((k : ℝ) + ℓ) / N := ⟨_, rfl⟩
  have hxN : x * N = (k : ℝ) + ℓ := (eq_div_iff hNr.ne').1 hx
  have hfl : x - 3 < (((k + ℓ) / N - 2 : ℕ) : ℝ) := by
    have h := floor_div_bounds (k + ℓ) N hN h3N
    rw [Nat.cast_add] at h
    rw [hx]
    exact h
  have hx4 := scaled_ge N x (ρ - r) ((k : ℝ) + ℓ) hNr hη hxN hn₀
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = 1 - c₁ := ⟨_, rfl⟩
  rw [← hw] at hrdef ⊢
  have e1 : (ρ - r) / (4 * N) * ((k : ℝ) + ℓ) = (ρ - r) * x / 4 := by
    rw [hx]
    ring
  have e2 : (1 - s) * ((k : ℝ) + ℓ) / (w * N) = r * x := by
    rw [hrdef, hx]
    ring
  rw [e1, e2]
  exact density_arith ρ r x _ hρ0 hρ1 hx4 (by linarith)

/-- The exponential bound for large `k + ℓ`: `a e^{-b M} ≤ (a e^{3 b}) e^{-(b/N) n}` once
`M ≥ n / N - 3`. -/
private theorem exp_tail (a b N n M : ℝ) (ha : 0 < a) (hb : 0 < b) (hM : n / N - 3 < M) :
    a * Real.exp (-(b * M)) ≤ (a * Real.exp (3 * b)) * Real.exp (-(b / N * n)) := by
  have hbn : b / N * n = b * (n / N) := by ring
  have h : -(b * M) ≤ 3 * b + -(b / N * n) := by
    rw [hbn]
    nlinarith [mul_nonneg hb.le (sub_nonneg.2 hM.le)]
  calc a * Real.exp (-(b * M)) ≤ a * Real.exp (3 * b + -(b / N * n)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h) ha.le
    _ = (a * Real.exp (3 * b)) * Real.exp (-(b / N * n)) := by
        rw [Real.exp_add]
        ring

/-- **Exponential decay, total form.** The top passage time beyond the edge decays
exponentially in the total length `k + ℓ`. The weights have law `ν`, at most one almost
surely (the top weight is `1`, with positive probability). If the mean half-line edge at some
length `L` is below `c L` and `c < s ≤ 1`, then there are `δ, A, B > 0` such that for all
`(k, ℓ)` with `s (k + ℓ) ≤ k`, the probability that the top passage time to `(k, ℓ)` reaches
`(1 - δ) (k + ℓ)` is at most `A e^{-B (k + ℓ)}`. This form holds with `s = 0` and needs no
separate treatment of `k = 0`.

This is the decay estimate in the proof of the proposition on exponential decay beyond the edge
in Georgiou, Rassoul-Agha and Seppäläinen (manuscript in preparation). That proposition states
the bound `e^{-B k}`; the total form is the stronger intermediate result of the proof, and the
indexing of the coarse path differs slightly from the written argument. -/
theorem top_passage_beyond_edge_decay_total (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (c : ℝ) (L : ℕ) (hL : 0 < L)
    (hc : ∫ ω, (halfLineEdge ω L : ℝ) ∂environmentLaw ν < c * L)
    (s : ℝ) (hcs : c < s) (hs₁ : s ≤ 1) :
    ∃ δ A B : ℝ, 0 < δ ∧ 0 < A ∧ 0 < B ∧ ∀ k ℓ : ℕ, s * (k + ℓ) ≤ k →
      (environmentLaw ν).real
          {ω | (1 - δ) * (k + ℓ) ≤ lastPassage (topField ω) 0 (k, ℓ)} ≤
        A * Real.exp (-(B * (k + ℓ))) := by
  classical
  -- the speed `c₁` strictly between `c` and `s`
  obtain ⟨c₁, hcc₁, hc₁s⟩ : ∃ c₁ : ℝ, c < c₁ ∧ c₁ < s := ⟨(c + s) / 2, by linarith, by linarith⟩
  have hc₁1 : c₁ < 1 := lt_of_lt_of_le hc₁s hs₁
  have h1c₁ : 0 < 1 - c₁ := by linarith
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hc' : ∫ ω, (halfLineEdge ω L : ℝ) ∂environmentLaw ν < c₁ * L :=
    lt_of_lt_of_le hc (mul_le_mul_of_nonneg_right hcc₁.le hLpos.le)
  -- exponential deviation of the edge at speed `c₁`
  obtain ⟨A₃, B₃, -, hB₃, h3⟩ := halfLineEdge_upper_deviation ν hp₀ c₁ L hL hc'
  -- the black density `ρ` between `r = (1 - s) / (1 - c₁)` and `1`
  obtain ⟨r, hr1, hrdef⟩ : ∃ r : ℝ, r < 1 ∧ r = (1 - s) / (1 - c₁) := by
    refine ⟨(1 - s) / (1 - c₁), ?_, rfl⟩
    rw [div_lt_one h1c₁]
    linarith
  have hr0 : 0 ≤ r := by
    rw [hrdef]
    exact div_nonneg (by linarith) h1c₁.le
  obtain ⟨ρ, hρ0, hρ1, hrρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ r < ρ :=
    ⟨(1 + r) / 2, by linarith, by linarith, by linarith⟩
  have hη : 0 < ρ - r := sub_pos.2 hrρ
  -- the sparse-path lemma with separation 2
  obtain ⟨ζ, hζ0, -, hN4⟩ := exists_sparse_good_coarse_path_cutoff ρ hρ0 hρ1 2
  -- the scale `N`: the white probability is below `ζ`
  obtain ⟨N, hNpos, hNζ⟩ := exists_scale A₃ B₃ ζ hB₃ hζ0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  -- the block events: measurability, white probability, independence
  obtain ⟨hmeas, -, hindep⟩ := blackBlock_measurable_stationary_independent ν N c₁
  have hwhite : ∀ v : ℕ × ℕ, (environmentLaw ν).real
      {ω : Environment | ¬ IsBlackBlock (topSites ω) N c₁ ((v.1 : ℤ), (v.2 : ℤ))} ≤ ζ := by
    intro v
    refine le_trans (white_block_probability_le ν N c₁ _) ?_
    refine le_trans (mul_le_mul_of_nonneg_left (h3 N) (by positivity)) ?_
    exact hNζ
  obtain ⟨a, b, ha, hb, hab⟩ := hN4 (environmentLaw ν)
    (fun v : ℕ × ℕ => {ω : Environment | IsBlackBlock (topSites ω) N c₁ ((v.1 : ℤ), (v.2 : ℤ))})
    (fun v => hmeas _) hwhite hindep
  -- the constants of the conclusion
  obtain ⟨n₀, hn₀1, hn₀2⟩ : ∃ n₀ : ℕ, 3 * N ≤ n₀ ∧ 4 * (N : ℝ) / (ρ - r) ≤ n₀ :=
    ⟨⌈4 * (N : ℝ) / (ρ - r)⌉₊ + 3 * N, by omega,
      le_trans (Nat.le_ceil _) (by exact_mod_cast Nat.le_add_right _ _)⟩
  have hδ : 0 < (ρ - r) / (4 * N) := div_pos hη (by positivity)
  refine ⟨(ρ - r) / (4 * N), max (a * Real.exp (3 * b)) (Real.exp (b / (N : ℝ) * (n₀ : ℝ))),
    b / N, hδ, lt_max_of_lt_left (by positivity), by positivity, ?_⟩
  intro k ℓ hks
  have hBpos : 0 < b / (N : ℝ) := by positivity
  by_cases hn : n₀ ≤ k + ℓ
  · -- large `k + ℓ`: use the coarse-path bound
    have h3N : 3 * N ≤ k + ℓ := le_trans hn₀1 hn
    have hQ3 : 3 ≤ (k + ℓ) / N := (Nat.le_div_iff_mul_le hNpos).2 h3N
    have hM1 : 1 ≤ (k + ℓ) / N - 2 := by omega
    have hn₀' : 4 * (N : ℝ) / (ρ - r) ≤ (k : ℝ) + ℓ := le_trans hn₀2 (by exact_mod_cast hn)
    have hbound := budget_le N k ℓ hNpos s c₁ ρ r hρ0 hρ1 hrdef hη hn₀' h3N
    have hfl : ((k : ℝ) + ℓ) / N - 3 < (((k + ℓ) / N - 2 : ℕ) : ℝ) := by
      have h := floor_div_bounds (k + ℓ) N hNpos h3N
      rw [Nat.cast_add] at h
      exact h
    have hP := hab ((k + ℓ) / N - 2) hM1
    have hincl : (environmentLaw ν).real
        {ω | (1 - (ρ - r) / (4 * N)) * (k + ℓ) ≤ lastPassage (topField ω) 0 (k, ℓ)} ≤
        a * Real.exp (-(b * (((k + ℓ) / N - 2 : ℕ) : ℝ))) := by
      refine le_trans (measureReal_mono ?_) hP
      intro ω hω
      obtain ⟨q, hq0, hqs, hqc⟩ := exists_coarse_of_dense_passage ω N hNpos c₁ s
        ((ρ - r) / (4 * N)) hc₁1 k ℓ hks h3N hω
      refine ⟨q, hq0, hqs, ?_⟩
      refine le_trans (le_of_eq (congrArg (Nat.cast : ℕ → ℝ) ?_)) (le_trans hqc hbound)
      refine card_filter_congr ?_
      intro j
      exact Iff.rfl
    refine le_trans hincl ?_
    refine le_trans (exp_tail a b N ((k : ℝ) + ℓ) _ ha hb hfl) ?_
    have hmax := le_max_left (a * Real.exp (3 * b)) (Real.exp (b / (N : ℝ) * (n₀ : ℝ)))
    exact mul_le_mul_of_nonneg_right hmax (Real.exp_pos _).le
  · -- small `k + ℓ`: the probability is at most one and the constant is large
    have hlt : k + ℓ < n₀ := lt_of_not_ge hn
    have hkn₀ : (k : ℝ) + ℓ ≤ n₀ := by exact_mod_cast hlt.le
    have h1 : 1 ≤ Real.exp (b / (N : ℝ) * (n₀ : ℝ)) *
        Real.exp (-(b / (N : ℝ) * ((k : ℝ) + ℓ))) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      rw [← sub_eq_add_neg]
      exact sub_nonneg.2 (mul_le_mul_of_nonneg_left hkn₀ hBpos.le)
    refine le_trans measureReal_le_one ?_
    refine le_trans h1 ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- **Exponential decay of the top passage time beyond the edge.** The weights have
law `ν`, at most one almost surely (the top weight is `1`, with positive probability). If the
mean half-line edge at some length `L` is below `c L` and `c < s ≤ 1`, then there are
`δ, A, B > 0` such that for all `(k, ℓ)` with `s (k + ℓ) ≤ k`, the probability that the top
passage time to `(k, ℓ)` reaches `(1 - δ) (k + ℓ)` is at most `A e^{-B k}`. It follows from
the total form `top_passage_beyond_edge_decay_total`, because `e^{-B (k + ℓ)} ≤ e^{-B k}`.

This is the proposition on exponential decay beyond the edge in Georgiou, Rassoul-Agha and
Seppäläinen (manuscript in preparation). -/
theorem top_passage_beyond_edge_decay (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (c : ℝ) (L : ℕ) (hL : 0 < L)
    (hc : ∫ ω, (halfLineEdge ω L : ℝ) ∂environmentLaw ν < c * L)
    (s : ℝ) (hcs : c < s) (hs₁ : s ≤ 1) :
    ∃ δ A B : ℝ, 0 < δ ∧ 0 < A ∧ 0 < B ∧ ∀ k ℓ : ℕ, s * (k + ℓ) ≤ k →
      (environmentLaw ν).real
          {ω | (1 - δ) * (k + ℓ) ≤ lastPassage (topField ω) 0 (k, ℓ)} ≤
        A * Real.exp (-(B * k)) := by
  obtain ⟨δ, A, B, hδ, hA, hB, h⟩ :=
    top_passage_beyond_edge_decay_total ν hp₀ c L hL hc s hcs hs₁
  refine ⟨δ, A, B, hδ, hA, hB, ?_⟩
  intro k ℓ hks
  have hkn : (k : ℝ) ≤ (k : ℝ) + ℓ := le_add_of_nonneg_right (Nat.cast_nonneg ℓ)
  refine le_trans (h k ℓ hks) ?_
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hkn hB.le))) hA.le

end LPPDifferentiability
