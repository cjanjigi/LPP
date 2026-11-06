/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.GridConnectionsGeneral
public import Differentiability.Probability.HeavyCrossingTrials
import Differentiability.Model.CoarseCrossingBlocks
import Differentiability.Probability.FiniteHeavyVertices
import Differentiability.Analysis.GridScaleSums
import Differentiability.Analysis.GridScaleCounts
import Mathlib.Tactic

/-! # Probability of the coarse good event and the scale sums, for general weights

The coarse failure bound is (5.22) of the differentiability preprint. It uses item (C3),
Lemma B.7 (heavy vertices), and item (C7). The union bound and the scale sums are
(5.31) to (5.33) of that paper, used in item (ii) of Lemma 5.7.

* `coarse_good_event_prob_le`: at a coarse grid interval `(j, I, h)` the event `¬ CoarseGoodAt` has
  probability at most `exp (-(q₀/2) j²)`: the `j²` blocks are disjoint, each crossing event meets
  the no-heavy-vertex event of its block with probability at least `q₀/2`, and the trials are
  independent (`heavy_crossing_trials_indep`).
* `grid_union_measure_le`, `grid_scale_tail_le`: the union bound over scales, grid levels and bins,
  and the tail sum `β_J / c_{A,R}` with the exponent `q₀/2` of item (C7).
* `grid_pow_sub_jstar_ge`: `2^(k - j*(k))` is eventually larger than any fixed number.
* `neg_integral_neg_part_le_integral_grid`: `-C_m ≤ E ω₀`.
-/

public section

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

/-- The measure of a union over scales, grid levels and bins is at most the sum of the
per-triple bounds ((5.31) of the differentiability preprint). No measurability is needed. -/
theorem grid_union_measure_le (ν : Measure Environment) [IsFiniteMeasure ν] (J jstar : ℕ)
    (S H : ℕ → Finset ℤ) (Bad : ℕ → ℤ → ℤ → Set Environment) (q : ℕ → ℝ)
    (hq : ∀ j ∈ Finset.Icc J jstar, ∀ I ∈ S j, ∀ h ∈ H j, ν.real (Bad j I h) ≤ q j) :
    ν.real (⋃ j ∈ Finset.Icc J jstar, ⋃ I ∈ S j, ⋃ h ∈ H j, Bad j I h) ≤
      ∑ j ∈ Finset.Icc J jstar, ((S j).card : ℝ) * ((H j).card : ℝ) * q j := by
  refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  calc ∑ I ∈ S j, ν.real (⋃ h ∈ H j, Bad j I h) ≤ ∑ _I ∈ S j, ((H j).card : ℝ) * q j := by
        refine Finset.sum_le_sum fun I hI => ?_
        refine (measureReal_biUnion_finset_le _ _).trans ?_
        calc ∑ h ∈ H j, ν.real (Bad j I h) ≤ ∑ _h ∈ H j, q j :=
              Finset.sum_le_sum fun h hh => hq j hj I hI h hh
          _ = ((H j).card : ℝ) * q j := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((S j).card : ℝ) * ((H j).card : ℝ) * q j := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- The splitting bound (5.32) and the tail sum (5.33) of the differentiability preprint,
with the exponent `q₀/2` of item (C7). If every scale has `|𝒢_{j,k}| |ℋ_{j,k}| ≤ C 2^{5j}`,
the crossing terms sum to at most
`C ∑_{i} 2^{5(i+J)} e^{-(q₀/2)(i+J)²}`, the tail sum `β_J / c_{A,R}`. -/
theorem grid_scale_tail_le {q0 C : ℝ} (hq : 0 < q0) (hC : 0 ≤ C) (J jstar : ℕ)
    (S H : ℕ → Finset ℤ)
    (hcard : ∀ j ∈ Finset.Icc J jstar, ((S j).card : ℝ) * ((H j).card : ℝ) ≤ C * 2 ^ (5 * j)) :
    ∑ j ∈ Finset.Icc J jstar,
        ((S j).card : ℝ) * ((H j).card : ℝ) * Real.exp (-(q0 / 2 * (j : ℝ) ^ 2)) ≤
      C * ∑' i : ℕ, (2 : ℝ) ^ (5 * (i + J)) * Real.exp (-(q0 / 2 * ((i + J : ℕ) : ℝ) ^ 2)) := by
  have hq2 : 0 < q0 / 2 := by positivity
  have hnn : ∀ j : ℕ, 0 ≤ (2 : ℝ) ^ (5 * j) * Real.exp (-(q0 / 2 * (j : ℝ) ^ 2)) :=
    fun j => by positivity
  calc ∑ j ∈ Finset.Icc J jstar,
        ((S j).card : ℝ) * ((H j).card : ℝ) * Real.exp (-(q0 / 2 * (j : ℝ) ^ 2))
      ≤ ∑ j ∈ Finset.Icc J jstar,
          C * ((2 : ℝ) ^ (5 * j) * Real.exp (-(q0 / 2 * (j : ℝ) ^ 2))) := by
        refine Finset.sum_le_sum fun j hj => ?_
        calc ((S j).card : ℝ) * ((H j).card : ℝ) * Real.exp (-(q0 / 2 * (j : ℝ) ^ 2))
            ≤ C * 2 ^ (5 * j) * Real.exp (-(q0 / 2 * (j : ℝ) ^ 2)) :=
              mul_le_mul_of_nonneg_right (hcard j hj) (Real.exp_pos _).le
          _ = C * ((2 : ℝ) ^ (5 * j) * Real.exp (-(q0 / 2 * (j : ℝ) ^ 2))) := by ring
    _ = C * ∑ j ∈ Finset.Icc J jstar,
          (2 : ℝ) ^ (5 * j) * Real.exp (-(q0 / 2 * (j : ℝ) ^ 2)) := by rw [Finset.mul_sum]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        calc ∑ j ∈ Finset.Icc J jstar,
              (2 : ℝ) ^ (5 * j) * Real.exp (-(q0 / 2 * (j : ℝ) ^ 2))
            = ∑ i ∈ Finset.range (jstar + 1 - J),
              (2 : ℝ) ^ (5 * (i + J)) * Real.exp (-(q0 / 2 * ((i + J : ℕ) : ℝ) ^ 2)) := by
              have hI : Finset.Icc J jstar = Finset.Ico J (jstar + 1) := by
                ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
              rw [hI, Finset.sum_Ico_eq_sum_range]
              exact Finset.sum_congr rfl fun i _ => by rw [add_comm J i]
          _ ≤ _ := ((summable_nat_add_iff J).2 (grid_beta_summable hq2)).sum_le_tsum _
              fun i _ => hnn (i + J)

/-- For every `X` there is `k₂` such that `X ≤ 2 ^ (k - j*(k))` for `k ≥ k₂`, where
`j*(k) = ⌈(m_k - 1)/4⌉₊` and `m_k ≤ 3 k`: indeed `4 j* ≤ m_k + 2 ≤ 3k + 2`. -/
theorem grid_pow_sub_jstar_ge (X : ℝ) (k0 : ℕ) (m : ℕ → ℕ)
    (hm3 : ∀ k : ℕ, k0 ≤ k → m k ≤ 3 * k) :
    ∃ k2 : ℕ, ∀ k : ℕ, k2 ≤ k →
      X ≤ ((2 ^ (k - ⌈((m k : ℝ) - 1) / 4⌉₊) : ℕ) : ℝ) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt X (one_lt_two : (1 : ℝ) < 2)
  refine ⟨4 * k0 + 4 * n + 3, fun k hk => ?_⟩
  have hmk : m k ≤ 3 * k := hm3 k (by omega)
  have hjb := (grid_jstar_bounds (m := m k) (jstar := ⌈((m k : ℝ) - 1) / 4⌉₊) rfl).2
  have hnk : n ≤ k - ⌈((m k : ℝ) - 1) / 4⌉₊ := by omega
  have h2 : (2 : ℝ) ^ n ≤ ((2 ^ (k - ⌈((m k : ℝ) - 1) / 4⌉₊) : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hnk
  exact hn.le.trans h2

/-- `-C_m ≤ E ω₀` with `C_m = E ω₀⁻` (the integral of the negative part). -/
theorem neg_integral_neg_part_le_integral_grid (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    -(∫ x : ℝ, max (-x) 0 ∂μ) ≤ ∫ x : ℝ, x ∂μ := by
  by_cases hx : Integrable (fun x : ℝ => x) μ
  · have hn : Integrable (fun x : ℝ => max (-x) 0) μ := hx.neg.pos_part
    rw [← integral_neg]
    refine integral_mono hn.neg hx fun x => ?_
    rcases le_total (-x) 0 with h | h
    · simp only [max_eq_right h]; linarith
    · simp only [max_eq_left h]; linarith
  · rw [integral_undef hx]
    have : 0 ≤ ∫ x : ℝ, max (-x) 0 ∂μ := integral_nonneg fun x => le_max_right _ _
    linarith

/-- The probability that some vertex of a set `S` with at most `17 w^4` vertices has
weight above `w = 2^(k-j)` is at most `17 C_p 2^{-(p-4)(k-3)/4}`. This is the proof of
Lemma B.7 of the differentiability preprint, with `k ≤ 4 (k - j) + 3`. -/
private theorem heavy_block_failure_le (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ}
    (hp : 4 < p) (hmomp : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (S : Finset Lattice) (w : ℝ) (k j : ℕ) (hw : w = (2 : ℝ) ^ (k - j))
    (hk4 : k ≤ 4 * (k - j) + 3) (hS : (S.card : ℝ) ≤ 17 * w ^ 4) :
    (environmentLaw μ).real {ω : Environment | ¬ ∀ z ∈ S, ω z ≤ w} ≤
      17 * (∫ x : ℝ, (max x 0) ^ p ∂μ) * (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4) := by
  have hwpos : (0 : ℝ) < w := by rw [hw]; exact pow_pos zero_lt_two _
  have hCp0 : 0 ≤ ∫ x : ℝ, (max x 0) ^ p ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (le_max_right x 0) p
  have hb := (measureReal_exists_upper_heavy_site_le_and_safe_ge μ (by linarith only [hp])
    hmomp w hwpos S).2.1
  have hset : {ω : Environment | ¬ ∀ z ∈ S, ω z ≤ w} =
      {ω : Environment | ∃ z ∈ S, w < ω z} := by
    ext ω
    simp [not_le]
  rw [hset]
  have hx0 : (0 : ℝ) < (2 : ℝ) ^ (((k : ℝ) - 3) / 4) := Real.rpow_pos_of_pos zero_lt_two _
  have hxw : (2 : ℝ) ^ (((k : ℝ) - 3) / 4) ≤ w := by
    have hk4R : (k : ℝ) ≤ 4 * ((k - j : ℕ) : ℝ) + 3 := by exact_mod_cast hk4
    rw [hw, ← Real.rpow_natCast (2 : ℝ) (k - j)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hk4R])
  have hfour : w ^ 4 = w ^ (4 : ℝ) := (Real.rpow_natCast w 4).symm
  have hpowsub : w ^ (4 : ℝ) * w ^ (-p) = w ^ (4 - p) := by
    rw [← Real.rpow_add hwpos, sub_eq_add_neg]
  have hdecay : w ^ (4 - p) ≤ (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4) := by
    calc w ^ (4 - p) ≤ ((2 : ℝ) ^ (((k : ℝ) - 3) / 4)) ^ (4 - p) :=
          Real.rpow_le_rpow_of_nonpos hx0 hxw (by linarith only [hp])
      _ = (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4) := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring
  calc (environmentLaw μ).real {ω : Environment | ∃ z ∈ S, w < ω z}
      ≤ (S.card : ℝ) * (∫ x : ℝ, (max x 0) ^ p ∂μ) * w ^ (-p) := hb
    _ ≤ (17 * w ^ 4) * (∫ x : ℝ, (max x 0) ^ p ∂μ) * w ^ (-p) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hS hCp0)
          (Real.rpow_nonneg hwpos.le _)
    _ = 17 * (∫ x : ℝ, (max x 0) ^ p ∂μ) * (w ^ (4 : ℝ) * w ^ (-p)) := by
        rw [hfour]
        ring
    _ ≤ 17 * (∫ x : ℝ, (max x 0) ^ p ∂μ) * (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4) := by
        rw [hpowsub]
        exact mul_le_mul_of_nonneg_left hdecay (mul_nonneg (by norm_num) hCp0)

/-- **The coarse good event fails with probability at most `exp (-(q₀/2) j²)`**
((5.22) of the differentiability preprint, item (C3)). At a coarse scale
(`8 c_* j² w ≤ l`, `w = 2^(k-j)`, `l = 2^(m_k - 4j - 1)`), suppose that a crossing of
length `l - 2⌈c_* j² w⌉` has probability above `q₀` (hypothesis `hP`), that the mesh
satisfies `l ≤ w³/2` (hypothesis `hhalf`), and that the heavy-vertex failure bound of one
block is at most `q₀/2` (hypothesis `hsm`). Then the event `¬ CoarseGoodAt` has
probability at most `exp (-(q₀/2) j²)`. -/
theorem coarse_good_event_prob_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : 4 < p)
    (hmomp : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (a G0 K cstar q0 : ℝ) (hcstar : 1 ≤ cstar) (k j mk : ℕ) (hj : 1 ≤ j)
    (hk4 : k ≤ 4 * (k - j) + 3)
    (hcoarse : 8 * cstar * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) ≤
      ((2 ^ (mk - 4 * j - 1) : ℕ) : ℝ))
    (hhalf : 1 < (2 : ℝ) ^ (mk - 4 * j - 1) →
      (2 : ℝ) ^ (mk - 4 * j - 1) ≤ ((2 : ℝ) ^ (k - j)) ^ 3 / 2)
    (hP : ∀ n : ℕ, 1 ≤ n → (n : ℝ) < (2 : ℝ) ^ (mk - 4 * j - 1) →
      q0 < (environmentLaw μ).real {ω : Environment |
        ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
          (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤
            8 * (2 : ℝ) ^ (k - j)) ∧
          G0 * (n : ℝ) - K * (2 : ℝ) ^ (k - j) < pathWeight ω q})
    (hsm : 17 * (∫ x : ℝ, (max x 0) ^ p ∂μ) * (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4) ≤ q0 / 2)
    (I h : ℤ) :
    (environmentLaw μ).real {ω : Environment | ¬ CoarseGoodAt ω a G0 K cstar mk k j I h} ≤
      Real.exp (-(q0 / 2 * (j : ℝ) ^ 2)) := by
  classical
  have hwc : (((2 ^ (k - j) : ℕ)) : ℝ) = (2 : ℝ) ^ (k - j) := by push_cast; ring
  have hlc : (((2 ^ (mk - 4 * j - 1) : ℕ)) : ℝ) = (2 : ℝ) ^ (mk - 4 * j - 1) := by
    push_cast; ring
  set W : ℕ := 2 ^ (k - j)
  set l : ℕ := 2 ^ (mk - 4 * j - 1)
  set mm : ℕ := ⌈cstar * ((j : ℝ) ^ 2 * (W : ℝ))⌉₊ with hmm
  -- scalar facts on the scale
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hw1 : (1 : ℝ) ≤ (W : ℝ) := by rw [hwc]; exact one_le_pow₀ (by norm_num)
  have hj2 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := one_le_pow₀ hj1
  have hX : 1 ≤ cstar * (j : ℝ) ^ 2 * (W : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hcstar hj2) hw1
  have hell8 : (8 : ℝ) ≤ (l : ℝ) := by nlinarith only [hcoarse, hX]
  have hmesh : (1 : ℝ) < (2 : ℝ) ^ (mk - 4 * j - 1) := by
    rw [← hlc]; linarith only [hell8]
  have hhalf' : (l : ℝ) ≤ (W : ℝ) ^ 3 / 2 := by rw [hlc, hwc]; exact hhalf hmesh
  have hmmR : (mm : ℝ) < cstar * ((j : ℝ) ^ 2 * (W : ℝ)) + 1 := by
    rw [hmm]; exact Nat.ceil_lt_add_one (by nlinarith only [hX])
  have hmmpos : 0 < mm := by
    rw [hmm]; exact Nat.ceil_pos.2 (by nlinarith only [hX])
  have hmmlt : 2 * mm < l := by
    have h2 : (2 * mm : ℝ) < l := by nlinarith only [hmmR, hcoarse, hell8, hX]
    exact_mod_cast h2
  -- the blocks of the crossing trials
  obtain ⟨c, B, hlevel, hround, hB, -, -, hB17, -⟩ :=
    exists_coarse_crossing_blocks a (h : ℝ) (W : ℝ) I l mm (j ^ 2) hw1 hmmlt hhalf'
  -- the crossing events and the untranslated crossing event
  let E : Fin (j ^ 2) → Set Environment := fun ν => {ω : Environment |
    ∃ (u : Lattice) (d : ℕ × ℕ) (x : Path u d),
      u.1 + u.2 = I + (mm : ℤ) ∧ d.1 + d.2 = l - 2 * mm ∧
      (∀ i, |(1 - a) * ((x.vertex i).1 : ℝ) - a * ((x.vertex i).2 : ℝ) -
        ((1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ))| ≤ 8 * (W : ℝ)) ∧
      G0 * ((l - 2 * mm : ℕ) : ℝ) - K * (W : ℝ) < pathWeight ω x}
  let E0 : Set Environment := {ω : Environment |
    ∃ (u : Lattice) (d : ℕ × ℕ) (x : Path u d),
      u.1 + u.2 = 0 ∧ d.1 + d.2 = l - 2 * mm ∧
      (∀ i, |(1 - a) * ((x.vertex i).1 : ℝ) - a * ((x.vertex i).2 : ℝ)| ≤ 8 * (W : ℝ)) ∧
      G0 * ((l - 2 * mm : ℕ) : ℝ) - K * (W : ℝ) < pathWeight ω x}
  have hn1 : 1 ≤ l - 2 * mm := by omega
  have hn2 : ((l - 2 * mm : ℕ) : ℝ) < (2 : ℝ) ^ (mk - 4 * j - 1) := by
    rw [← hlc]; exact_mod_cast (by omega : l - 2 * mm < l)
  have hqE0 : q0 < (environmentLaw μ).real E0 := by
    refine (hP (l - 2 * mm) hn1 hn2).trans_le (le_of_eq (congrArg (environmentLaw μ).real ?_))
    ext ω
    simp only [E0, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hu, e, he, q, hq, hw⟩
      exact ⟨u, e, q, hu, he, by rw [hwc]; exact hq, by rw [hwc]; exact hw⟩
    · rintro ⟨u, e, q, hu, he, hq, hw⟩
      exact ⟨u, hu, e, he, q, by rw [← hwc]; exact hq, by rw [← hwc]; exact hw⟩
  -- the heavy-vertex failure probability of one block is at most `q0 / 2`
  have hsmall : ∀ ν, (environmentLaw μ).real {ω : Environment | ¬ ∀ z ∈ B ν, ω z ≤ (W : ℝ)} ≤
      q0 / 2 := fun ν =>
    (heavy_block_failure_le μ hp hmomp (B ν) (W : ℝ) k j hwc hk4 (hB17 ν)).trans hsm
  -- all the trials fail with probability at most `exp (-(q0/2) j²)`
  obtain ⟨-, -, hall⟩ := heavy_crossing_trials_indep μ a G0 K (W : ℝ) (h : ℝ) hw1 I l mm
    (j ^ 2) hmmlt.le c hlevel hround E (fun ν => rfl) E0 rfl B hB q0 hqE0 hsmall
  -- the bad event is inside the event that all the trials fail
  have hsub : {ω : Environment | ¬ CoarseGoodAt ω a G0 K cstar mk k j I h} ⊆
      ⋂ ν, (E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ (W : ℝ)})ᶜ := by
    intro ω hω
    have hω' : ¬ CoarseGoodAt ω a G0 K cstar mk k j I h := hω
    rw [Set.mem_iInter]
    intro ν hν
    obtain ⟨hEν, hHν⟩ := hν
    obtain ⟨x₀, d, x, hx0, hd, hxloc, hxw⟩ := hEν
    apply hω'
    dsimp only [CoarseGoodAt]
    refine ⟨ν.val + 1, Nat.le_add_left 1 ν.val, Nat.succ_le_of_lt ν.isLt, c ν, hround ν,
      ⟨x₀, d, x, hx0, hd, hxloc, hxw⟩, ?_⟩
    intro z hz1 hz2 hz3
    exact hHν z ((hB ν z).2 ⟨hz1, hz2, hz3⟩)
  calc (environmentLaw μ).real {ω : Environment | ¬ CoarseGoodAt ω a G0 K cstar mk k j I h}
      ≤ (environmentLaw μ).real
          (⋂ ν, (E ν ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ (W : ℝ)})ᶜ) :=
        measureReal_mono hsub
    _ ≤ Real.exp (-(q0 / 2 * (((j ^ 2 : ℕ)) : ℝ))) := hall
    _ = Real.exp (-(q0 / 2 * (j : ℝ) ^ 2)) := by simp only [Nat.cast_pow]

end LPPDifferentiability
