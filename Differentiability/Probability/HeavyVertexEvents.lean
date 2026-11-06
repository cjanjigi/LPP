/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Analysis.HeavyVertexDecay
public import Differentiability.Analysis.RecordScales
public import Differentiability.Model.CoarseCrossingBlocks
public import Differentiability.Model.HeavyWorkingRegion
public import Differentiability.Probability.FiniteHeavyVertices
import Mathlib.Tactic

/-!
# Heavy-vertex events at generic scales

This file proves the probability bounds in Lemma B.7 (heavy vertices) of the differentiability
preprint for laws with a finite positive-part `p`-th moment, `p > 4`. The scale data
are the exponent function `m` with characteristic length `2 ^ m k`, the scale
`s_k = 2 ^ k` and the threshold `t_k = ε₀ * s_k / k`.

* `heavy_working_region_event_tendsto`: the probability that some vertex of the working region
  is above `t_k` tends to zero.
* `heavy_coarse_block_events`: at a coarse scale index `j`, every block of the crossing family has
  a vertex above `w = 2 ^ (k - j)` with probability at most
  `17 * C_p * 2 ^ (-(p - 4) * (k - 3) / 4)`, uniformly in the grid level `I`, the bin `h`
  and the block number; and if a trial event has
  probability above `q₀` for each block, its intersection with the no-heavy-vertex event has
  probability at least `q₀ / 2` once that bound is at most `q₀ / 2`.
* `heavy_coarse_block_events_eventually`: the bound tends to zero, and the previous conclusion
  holds for all large `k`.

Independence of the events over the block number is not part of this file.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LPPDifferentiability

private theorem not_safe_measureReal_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : 0 < p)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (t : ℝ) (ht : 0 < t) (S : Finset Lattice) :
    MeasurableSet {ω : Environment | ∀ z ∈ S, ω z ≤ t} ∧
      (environmentLaw μ).real {ω : Environment | ¬ ∀ z ∈ S, ω z ≤ t} ≤
        (S.card : ℝ) * (∫ x : ℝ, (max x 0) ^ p ∂μ) * t ^ (-p) := by
  obtain ⟨-, hbad, hsafe, -⟩ :=
    measureReal_exists_upper_heavy_site_le_and_safe_ge μ hp hmoment t ht S
  refine ⟨hsafe, ?_⟩
  have hset : {ω : Environment | ¬ ∀ z ∈ S, ω z ≤ t} =
      {ω : Environment | ∃ z ∈ S, t < ω z} := by
    ext ω
    simp [not_le]
  rw [hset]
  exact hbad

/-- The probability that some vertex of the working region `Q_k` has weight above
`t_k = ε₀ * 2 ^ k / k` tends to zero. The region `Q_k` is the finite set with the
membership condition of the construction (`ℓ_k = 2 ^ m k`, `s_k = 2 ^ k`), whose size is
at most a constant times `s_k ^ 4`. -/
theorem heavy_working_region_event_tendsto
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : 4 < p)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (m : ℕ → ℕ) (k0 : ℕ) (hm : ∀ k : ℕ, k0 ≤ k → m k ≤ 3 * k)
    (a A R c₁ ε₀ : ℝ) (hA : 0 < A) (hR : 0 < R) (hc₁ : 0 ≤ c₁) (hε₀ : 0 < ε₀) :
    ∃ Q : ℕ → Finset Lattice,
      (∀ k : ℕ, k0 ≤ k → ∀ z : Lattice, z ∈ Q k ↔
        |((z.1 + z.2 : ℤ) : ℝ)| ≤ (A + 5) * (2 : ℝ) ^ m k ∧
          |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ (R + 2 * c₁ + 10) * (2 : ℝ) ^ k) ∧
      Tendsto (fun k : ℕ => (environmentLaw μ).real
        {ω : Environment | ¬ ∀ z ∈ Q k, ω z ≤ ε₀ * (2 : ℝ) ^ k / (k : ℝ)})
        atTop (𝓝 0) := by
  classical
  have hex : ∀ k : ℕ, ∃ Q : Finset Lattice, k0 ≤ k →
      ((∀ z : Lattice, z ∈ Q ↔
        |((z.1 + z.2 : ℤ) : ℝ)| ≤ (A + 5) * (2 : ℝ) ^ m k ∧
          |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ (R + 2 * c₁ + 10) * (2 : ℝ) ^ k) ∧
        (Q.card : ℝ) ≤ (2 * A + 11) * (2 * R + 4 * c₁ + 21) * ((2 : ℝ) ^ k) ^ 4) := by
    intro k
    by_cases hk : k0 ≤ k
    · have hs : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      have hell : 1 ≤ 2 ^ m k := Nat.one_le_two_pow
      have hells : ((2 ^ m k : ℕ) : ℝ) ≤ ((2 : ℝ) ^ k) ^ 3 := by
        push_cast
        calc (2 : ℝ) ^ m k ≤ 2 ^ (3 * k) := pow_le_pow_right₀ (by norm_num) (hm k hk)
          _ = ((2 : ℝ) ^ k) ^ 3 := by ring
      obtain ⟨Q, hmem, hcard⟩ := exists_finset_heavy_working_region a A R c₁ ((2 : ℝ) ^ k)
        (2 ^ m k) hA hR hc₁ hs hell hells
      refine ⟨Q, fun _ => ⟨fun z => ?_, hcard⟩⟩
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hmem z
    · exact ⟨∅, fun h => absurd h hk⟩
  choose Q hQ using hex
  refine ⟨Q, fun k hk => (hQ k hk).1, ?_⟩
  have hCp0 : 0 ≤ ∫ x : ℝ, (max x 0) ^ p ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (le_max_right x 0) p
  have hK0 : 0 ≤ (2 * A + 11) * (2 * R + 4 * c₁ + 21) :=
    mul_nonneg (by linarith) (by linarith)
  have hlim := heavy_vertex_global_tail_decay
    (C := (2 * A + 11) * (2 * R + 4 * c₁ + 21) * ∫ x : ℝ, (max x 0) ^ p ∂μ) hp hε₀
    (mul_nonneg hK0 hCp0)
  refine squeeze_zero' (Eventually.of_forall fun k => measureReal_nonneg) ?_ hlim
  filter_upwards [eventually_ge_atTop k0, eventually_gt_atTop 0] with k hk0 hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hspos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos zero_lt_two k
  have ht : 0 < ε₀ * (2 : ℝ) ^ k / (k : ℝ) := by positivity
  obtain ⟨-, hb⟩ := not_safe_measureReal_le μ (by linarith) hmoment _ ht (Q k)
  have hpow : (ε₀ * (2 : ℝ) ^ k / (k : ℝ)) ^ (-p) =
      ((k : ℝ) / ε₀) ^ p * ((2 : ℝ) ^ k) ^ (-p) := by
    have hnn : (0 : ℝ) ≤ (k : ℝ) / ε₀ := by positivity
    have hform : ε₀ * (2 : ℝ) ^ k / (k : ℝ) = ((k : ℝ) / ε₀)⁻¹ * (2 : ℝ) ^ k := by
      rw [inv_div]
      ring
    rw [hform, Real.mul_rpow (inv_nonneg.2 hnn) hspos.le, Real.inv_rpow hnn,
      Real.rpow_neg hnn, inv_inv]
  calc (environmentLaw μ).real
        {ω : Environment | ¬ ∀ z ∈ Q k, ω z ≤ ε₀ * (2 : ℝ) ^ k / (k : ℝ)}
      ≤ ((Q k).card : ℝ) * (∫ x : ℝ, (max x 0) ^ p ∂μ) *
          (ε₀ * (2 : ℝ) ^ k / (k : ℝ)) ^ (-p) := hb
    _ ≤ ((2 * A + 11) * (2 * R + 4 * c₁ + 21) * ((2 : ℝ) ^ k) ^ 4) *
          (∫ x : ℝ, (max x 0) ^ p ∂μ) * (ε₀ * (2 : ℝ) ^ k / (k : ℝ)) ^ (-p) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hQ k hk0).2 hCp0)
          (Real.rpow_nonneg ht.le _)
    _ = (2 * A + 11) * (2 * R + 4 * c₁ + 21) * (∫ x : ℝ, (max x 0) ^ p ∂μ) *
          ((2 : ℝ) ^ k) ^ 4 * (((k : ℝ) / ε₀) ^ p) * ((2 : ℝ) ^ k) ^ (-p) := by
        rw [hpow]
        ring

/-- At a coarse scale index `j` with mesh `ell = 2 ^ (m k - 4 j - 1)`, trimmed margin
`mm = ⌈c_* j ^ 2 w⌉` and width `w = 2 ^ (k - j)`, the blocks of `exists_coarse_crossing_blocks`
(`N = j ^ 2` of them) have the following property, for every grid level `I` and bin `h`:
the event that no vertex of block `ν` has weight above `w` has probability at least
`1 - 17 * C_p * 2 ^ (-(p - 4) * (k - 3) / 4)`; and if the bound is at most `q₀ / 2`, any event `E`
with probability above `q₀` at each block centre meets it in probability at least `q₀ / 2`.
The record inequality `hrec` is (4.8) of the differentiability preprint at `k`. -/
theorem heavy_coarse_block_events
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : 4 < p)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (m : ℕ → ℕ) (k0 : ℕ) (hm : ∀ k : ℕ, k0 ≤ k → m k ≤ 3 * k)
    (cstar : ℝ) (hcstar : 1 ≤ cstar) (a q0 : ℝ)
    (k j : ℕ) (hk : 4 * k0 + 3 ≤ k)
    (hrec : ∀ i : ℕ, i ≤ k - k0 → (2 : ℝ) ^ m k / 2 ^ (4 * i) ≤ 2 ^ m (k - i))
    (hj : 1 ≤ j) (hjstar : j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊)
    (ell mm : ℕ) (hell : ell = 2 ^ (m k - 4 * j - 1))
    (hmm : mm = ⌈cstar * (j : ℝ) ^ 2 * (2 : ℝ) ^ (k - j)⌉₊)
    (hcoarse : 8 * cstar * (j : ℝ) ^ 2 * (2 : ℝ) ^ (k - j) ≤ (ell : ℝ))
    (h I : ℤ) :
    ∃ (c : Fin (j ^ 2) → Lattice) (B : Fin (j ^ 2) → Finset Lattice),
      (∀ ν, (c ν).1 + (c ν).2 = I + (mm : ℤ)) ∧
      (∀ ν, |(1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ) -
        ((h : ℝ) * (2 : ℝ) ^ (k - j) +
          30 * ((ν.val + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (k - j))| ≤ 1 / 2) ∧
      (∀ ν z, z ∈ B ν ↔
        I + (mm : ℤ) ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ I + (ell : ℤ) - (mm : ℤ) ∧
        |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) -
          ((1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ))| ≤ 8 * (2 : ℝ) ^ (k - j)) ∧
      (∀ ν μ', ν ≠ μ' → Disjoint (B ν) (B μ')) ∧
      (∀ ν, MeasurableSet {ω : Environment | ∀ z ∈ B ν, ω z ≤ (2 : ℝ) ^ (k - j)} ∧
        (environmentLaw μ).real {ω : Environment | ¬ ∀ z ∈ B ν, ω z ≤ (2 : ℝ) ^ (k - j)} ≤
          17 * (∫ x : ℝ, (max x 0) ^ p ∂μ) * (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4)) ∧
      (17 * (∫ x : ℝ, (max x 0) ^ p ∂μ) * (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4) ≤ q0 / 2 →
        ∀ E : Lattice → Set Environment, (∀ ν, q0 < (environmentLaw μ).real (E (c ν))) →
          ∀ ν, q0 / 2 ≤ (environmentLaw μ).real
            (E (c ν) ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ (2 : ℝ) ^ (k - j)})) := by
  have hkk0 : k0 ≤ k := by omega
  obtain ⟨-, hidx⟩ := scale_index_bounds k0 k (m k) hk (hm k hkk0)
  obtain ⟨hjk, hk0j, hk4, -⟩ := hidx j hjstar
  have hrecj := hrec j (by have := hjk; omega)
  have hm3 : m (k - j) ≤ 3 * (k - j) := hm (k - j) hk0j
  have hwpos : (0 : ℝ) < (2 : ℝ) ^ (k - j) := pow_pos zero_lt_two _
  have hw1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k - j) := one_le_pow₀ (by norm_num)
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hj2 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := one_le_pow₀ hjR
  have hX : 1 ≤ cstar * (j : ℝ) ^ 2 * (2 : ℝ) ^ (k - j) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hcstar hj2) hw1
  have hellR : (ell : ℝ) = (2 : ℝ) ^ (m k - 4 * j - 1) := by simp [hell]
  have hell8 : (8 : ℝ) ≤ ell := by nlinarith only [hcoarse, hX]
  have hmesh : (1 : ℝ) < (2 : ℝ) ^ (m k - 4 * j - 1) := by
    rw [← hellR]
    linarith only [hell8]
  have hhalf : (ell : ℝ) ≤ ((2 : ℝ) ^ (k - j)) ^ 3 / 2 := by
    rw [hellR]
    exact mesh_le_half_cube m k j hrecj hmesh hm3
  have hmmR : (mm : ℝ) < cstar * (j : ℝ) ^ 2 * (2 : ℝ) ^ (k - j) + 1 := by
    rw [hmm]
    exact Nat.ceil_lt_add_one (by linarith only [hX])
  have hmmlt : 2 * mm < ell := by
    have h2 : (2 * mm : ℝ) < ell := by nlinarith only [hmmR, hcoarse, hX, hell8]
    exact_mod_cast h2
  obtain ⟨c, B, hc1, hc2, hB, -, -, hB17, hdisj⟩ := exists_coarse_crossing_blocks a (h : ℝ)
    ((2 : ℝ) ^ (k - j)) I ell mm (j ^ 2) hw1 hmmlt hhalf
  have hCp0 : 0 ≤ ∫ x : ℝ, (max x 0) ^ p ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (le_max_right x 0) p
  have hx0 : (0 : ℝ) < (2 : ℝ) ^ (((k : ℝ) - 3) / 4) := Real.rpow_pos_of_pos zero_lt_two _
  have hxw : (2 : ℝ) ^ (((k : ℝ) - 3) / 4) ≤ (2 : ℝ) ^ (k - j) := by
    have hk4R : (k : ℝ) ≤ 4 * ((k - j : ℕ) : ℝ) + 3 := by exact_mod_cast hk4
    rw [← Real.rpow_natCast (2 : ℝ) (k - j)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hk4R])
  have hfour : ((2 : ℝ) ^ (k - j)) ^ 4 = ((2 : ℝ) ^ (k - j)) ^ (4 : ℝ) :=
    (Real.rpow_natCast ((2 : ℝ) ^ (k - j)) 4).symm
  have hpowsub : ((2 : ℝ) ^ (k - j)) ^ (4 : ℝ) * ((2 : ℝ) ^ (k - j)) ^ (-p) =
      ((2 : ℝ) ^ (k - j)) ^ (4 - p) := by
    rw [← Real.rpow_add hwpos, sub_eq_add_neg]
  have hdecay : ((2 : ℝ) ^ (k - j)) ^ (4 - p) ≤
      (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4) := by
    calc ((2 : ℝ) ^ (k - j)) ^ (4 - p)
        ≤ ((2 : ℝ) ^ (((k : ℝ) - 3) / 4)) ^ (4 - p) :=
          Real.rpow_le_rpow_of_nonpos hx0 hxw (by linarith only [hp])
      _ = (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4) := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring
  have hbound : ∀ ν, MeasurableSet {ω : Environment | ∀ z ∈ B ν, ω z ≤ (2 : ℝ) ^ (k - j)} ∧
      (environmentLaw μ).real {ω : Environment | ¬ ∀ z ∈ B ν, ω z ≤ (2 : ℝ) ^ (k - j)} ≤
        17 * (∫ x : ℝ, (max x 0) ^ p ∂μ) * (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4) := by
    intro ν
    obtain ⟨hmeas, hb⟩ := not_safe_measureReal_le μ (by linarith only [hp]) hmoment
      ((2 : ℝ) ^ (k - j)) hwpos (B ν)
    refine ⟨hmeas, hb.trans ?_⟩
    calc ((B ν).card : ℝ) * (∫ x : ℝ, (max x 0) ^ p ∂μ) * ((2 : ℝ) ^ (k - j)) ^ (-p)
        ≤ (17 * ((2 : ℝ) ^ (k - j)) ^ 4) * (∫ x : ℝ, (max x 0) ^ p ∂μ) *
            ((2 : ℝ) ^ (k - j)) ^ (-p) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hB17 ν) hCp0)
            (Real.rpow_nonneg hwpos.le _)
      _ = 17 * (∫ x : ℝ, (max x 0) ^ p ∂μ) *
            (((2 : ℝ) ^ (k - j)) ^ (4 : ℝ) * ((2 : ℝ) ^ (k - j)) ^ (-p)) := by
          rw [hfour]
          ring
      _ ≤ 17 * (∫ x : ℝ, (max x 0) ^ p ∂μ) * (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4) := by
          rw [hpowsub]
          exact mul_le_mul_of_nonneg_left hdecay (mul_nonneg (by norm_num) hCp0)
  refine ⟨c, B, hc1, hc2, hB, hdisj, hbound, ?_⟩
  intro hsmall E hE ν
  have hsub : E (c ν) ⊆ (E (c ν) ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ (2 : ℝ) ^ (k - j)}) ∪
      {ω : Environment | ¬ ∀ z ∈ B ν, ω z ≤ (2 : ℝ) ^ (k - j)} := by
    intro ω hω
    by_cases hsafe : ∀ z ∈ B ν, ω z ≤ (2 : ℝ) ^ (k - j)
    · exact Or.inl ⟨hω, hsafe⟩
    · exact Or.inr hsafe
  have hmain : (environmentLaw μ).real (E (c ν)) ≤
      (environmentLaw μ).real
        (E (c ν) ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ (2 : ℝ) ^ (k - j)}) +
      (environmentLaw μ).real
        {ω : Environment | ¬ ∀ z ∈ B ν, ω z ≤ (2 : ℝ) ^ (k - j)} :=
    (measureReal_mono hsub).trans (measureReal_union_le _ _)
  linarith only [hmain, hE ν, (hbound ν).2, hsmall]

/-- The block bound of `heavy_coarse_block_events` tends to zero, and for all large `k` the
conclusion of `heavy_coarse_block_events` holds for every coarse scale index, grid level and bin,
with its smallness condition discharged: an event with probability above `q₀` at each block
centre meets the no-heavy-vertex event of its block in probability at least `q₀ / 2`. -/
theorem heavy_coarse_block_events_eventually
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : 4 < p)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (m : ℕ → ℕ) (k0 : ℕ) (hm : ∀ k : ℕ, k0 ≤ k → m k ≤ 3 * k)
    (cstar : ℝ) (hcstar : 1 ≤ cstar) (a q0 : ℝ) (hq0 : 0 < q0) :
    Tendsto (fun k : ℕ => 17 * (∫ x : ℝ, (max x 0) ^ p ∂μ) *
      (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4)) atTop (𝓝 0) ∧
    ∀ᶠ k : ℕ in atTop, 4 * k0 + 3 ≤ k →
      (∀ i : ℕ, i ≤ k - k0 → (2 : ℝ) ^ m k / 2 ^ (4 * i) ≤ 2 ^ m (k - i)) →
      ∀ j : ℕ, 1 ≤ j → j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
      ∀ ell mm : ℕ, ell = 2 ^ (m k - 4 * j - 1) →
      mm = ⌈cstar * (j : ℝ) ^ 2 * (2 : ℝ) ^ (k - j)⌉₊ →
      8 * cstar * (j : ℝ) ^ 2 * (2 : ℝ) ^ (k - j) ≤ (ell : ℝ) →
      ∀ h I : ℤ,
      ∃ (c : Fin (j ^ 2) → Lattice) (B : Fin (j ^ 2) → Finset Lattice),
        (∀ ν, (c ν).1 + (c ν).2 = I + (mm : ℤ)) ∧
        (∀ ν, |(1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ) -
          ((h : ℝ) * (2 : ℝ) ^ (k - j) +
            30 * ((ν.val + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (k - j))| ≤ 1 / 2) ∧
        (∀ ν z, z ∈ B ν ↔
          I + (mm : ℤ) ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ I + (ell : ℤ) - (mm : ℤ) ∧
          |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) -
            ((1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ))| ≤ 8 * (2 : ℝ) ^ (k - j)) ∧
        (∀ ν μ', ν ≠ μ' → Disjoint (B ν) (B μ')) ∧
        (∀ ν, (environmentLaw μ).real
          {ω : Environment | ¬ ∀ z ∈ B ν, ω z ≤ (2 : ℝ) ^ (k - j)} ≤
            17 * (∫ x : ℝ, (max x 0) ^ p ∂μ) *
              (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4)) ∧
        (∀ E : Lattice → Set Environment,
          (∀ ν, q0 < (environmentLaw μ).real (E (c ν))) →
          ∀ ν, q0 / 2 ≤ (environmentLaw μ).real
            (E (c ν) ∩ {ω : Environment | ∀ z ∈ B ν, ω z ≤ (2 : ℝ) ^ (k - j)})) := by
  have hCp0 : 0 ≤ ∫ x : ℝ, (max x 0) ^ p ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (le_max_right x 0) p
  obtain ⟨hlim, hev⟩ := heavy_vertex_block_tail_decay hp hCp0 hq0
  refine ⟨hlim, ?_⟩
  filter_upwards [hev] with k hsmall hk hrec j hj hjstar ell mm hell hmm hcoarse h I
  obtain ⟨c, B, hc1, hc2, hB, hdisj, hbound, htrial⟩ :=
    heavy_coarse_block_events μ hp hmoment m k0 hm cstar hcstar a q0 k j hk hrec hj hjstar
      ell mm hell hmm hcoarse h I
  exact ⟨c, B, hc1, hc2, hB, hdisj, fun ν => (hbound ν).2, htrial hsmall⟩

end LPPDifferentiability

end
