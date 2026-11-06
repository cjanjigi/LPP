/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Analysis.DyadicCharacteristicLength
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Record scales and scale-index arithmetic

The record lemma for the characteristic lengths `L k = 2 ^ m k`, the index
arithmetic for the finest grid scale `⌈(m k - 1) / 4⌉`, and the abstract
forms of the bounds that follow from them. Everything is for an
arbitrary family `P : ℕ → ℕ → ℝ`; functions of `k` appear only inside
existentials.
-/

public section

namespace LPPDifferentiability

open Filter Topology

/-- A positive sequence tending to zero has infinitely many strict record
minima: indices `k ≥ k0` with `θ k < θ k'` for all `k0 ≤ k' < k`. -/
theorem exists_infinite_strict_record_minima (θ : ℕ → ℝ) (k0 : ℕ)
    (hpos : ∀ k : ℕ, k0 ≤ k → 0 < θ k) (hlim : Tendsto θ atTop (𝓝 0)) :
    ∃ K : Set ℕ, K.Infinite ∧
      ∀ k ∈ K, k0 ≤ k ∧ ∀ k' : ℕ, k0 ≤ k' → k' < k → θ k < θ k' := by
  classical
  refine ⟨{k | k0 ≤ k ∧ ∀ k' : ℕ, k0 ≤ k' → k' < k → θ k < θ k'}, ?_, fun k hk => hk⟩
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨x, hxmem, hxmin⟩ := Finset.exists_min_image (Finset.Icc k0 (max a k0)) θ
    ⟨k0, Finset.mem_Icc.2 ⟨le_rfl, le_max_right _ _⟩⟩
  have hxpos : 0 < θ x := hpos x (Finset.mem_Icc.1 hxmem).1
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hxpos))
  have hex : ∃ i : ℕ, k0 ≤ i ∧ θ i < θ x :=
    ⟨max N k0, le_max_right _ _, hN _ (le_max_left _ _)⟩
  have hspec := Nat.find_spec hex
  refine ⟨Nat.find hex, ⟨hspec.1, fun k' hk0' hlt => ?_⟩, ?_⟩
  · have hnot : ¬ (k0 ≤ k' ∧ θ k' < θ x) := Nat.find_min hex hlt
    have : θ x ≤ θ k' := not_lt.1 fun h => hnot ⟨hk0', h⟩
    exact lt_of_lt_of_le hspec.2 this
  · by_contra hle
    have hmem : Nat.find hex ∈ Finset.Icc k0 (max a k0) :=
      Finset.mem_Icc.2 ⟨hspec.1, le_trans (not_lt.1 hle) (le_max_left _ _)⟩
    exact absurd (lt_of_le_of_lt (hxmin _ hmem) hspec.2) (lt_irrefl _)

/-- The record lemma for lengths `L k = 2 ^ m k` with `m k ≤ 3 * k` for `k ≥ k0`:
there is an infinite set of indices `k ≥ k0` such that
`L (k - j) ≥ 2 ^ (-4 j) * L k` for `0 ≤ j ≤ k - k0`. -/
theorem exists_infinite_record_scales (m : ℕ → ℕ) (k0 : ℕ)
    (hm : ∀ k : ℕ, k0 ≤ k → m k ≤ 3 * k) :
    ∃ K : Set ℕ, K.Infinite ∧ ∀ k ∈ K, k0 ≤ k ∧ ∀ j : ℕ, j ≤ k - k0 →
      (2 : ℝ) ^ m k / 2 ^ (4 * j) ≤ 2 ^ m (k - j) := by
  have hpos : ∀ k : ℕ, k0 ≤ k → 0 < (2 : ℝ) ^ m k / 2 ^ (4 * k) :=
    fun k _ => by positivity
  have hlim : Tendsto (fun k : ℕ => (2 : ℝ) ^ m k / 2 ^ (4 * k)) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun k => by positivity)
      ((eventually_ge_atTop k0).mono fun k hk => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
    have h1 : (2 : ℝ) ^ m k ≤ 2 ^ (3 * k) := pow_le_pow_right₀ (by norm_num) (hm k hk)
    have h2 : (2 : ℝ) ^ (4 * k) = 2 ^ (3 * k) * 2 ^ k := by
      rw [← pow_add]
      congr 1
      omega
    calc (2 : ℝ) ^ m k / 2 ^ (4 * k) ≤ 2 ^ (3 * k) / 2 ^ (4 * k) := by gcongr
      _ = (1 / 2) ^ k := by
        rw [h2, one_div, inv_pow, div_mul_eq_div_div, div_self (by positivity)]
        simp
  obtain ⟨K, hKinf, hK⟩ := exists_infinite_strict_record_minima _ k0 hpos hlim
  refine ⟨K, hKinf, fun k hk => ⟨(hK k hk).1, fun j hj => ?_⟩⟩
  have hjk : j ≤ k := by omega
  have hle : (2 : ℝ) ^ m k / 2 ^ (4 * k) ≤ 2 ^ m (k - j) / 2 ^ (4 * (k - j)) := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      simp
    · exact ((hK k hk).2 (k - j) (by omega) (by omega)).le
  have h4 : (2 : ℝ) ^ (4 * k) = 2 ^ (4 * j) * 2 ^ (4 * (k - j)) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h4, ← div_div] at hle
  exact (div_le_div_iff_of_pos_right (by positivity)).1 hle

private theorem jstar_bounds (m : ℕ) :
    m ≤ 4 * ⌈((m : ℝ) - 1) / 4⌉₊ + 1 ∧ 4 * ⌈((m : ℝ) - 1) / 4⌉₊ ≤ m + 3 := by
  constructor
  · have h := Nat.le_ceil (((m : ℝ) - 1) / 4)
    have h' : (m : ℝ) ≤ 4 * (⌈((m : ℝ) - 1) / 4⌉₊ : ℝ) + 1 := by linarith
    exact_mod_cast h'
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have : ⌈(((0 : ℕ) : ℝ) - 1) / 4⌉₊ = 0 := Nat.ceil_eq_zero.2 (by norm_num)
      rw [this]
      norm_num
    · have hx : (0 : ℝ) ≤ ((m : ℝ) - 1) / 4 := by
        have : (1 : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      have h := Nat.ceil_lt_add_one hx
      have h' : 4 * (⌈((m : ℝ) - 1) / 4⌉₊ : ℝ) < (m : ℝ) + 3 := by linarith
      have h'' : 4 * ⌈((m : ℝ) - 1) / 4⌉₊ < m + 3 := by exact_mod_cast h'
      omega

/-- Index arithmetic for the finest scale `j* = ⌈(m - 1) / 4⌉` with `m ≤ 3 * k`
and `k ≥ 4 * k0 + 3`: `j* ≤ k`, and every scale index `j ≤ j*` has
`j ≤ k`, `k0 ≤ k - j`, `k ≤ 4 * (k - j) + 3` (so `2 ^ (k - j) ≥ 2 ^ ((k - 3) / 4)`)
and `4 * j ≤ m + 3`. -/
theorem scale_index_bounds (k0 k m : ℕ) (hk : 4 * k0 + 3 ≤ k) (hm : m ≤ 3 * k) :
    ⌈((m : ℝ) - 1) / 4⌉₊ ≤ k ∧ ∀ j : ℕ, j ≤ ⌈((m : ℝ) - 1) / 4⌉₊ →
      j ≤ k ∧ k0 ≤ k - j ∧ k ≤ 4 * (k - j) + 3 ∧ 4 * j ≤ m + 3 := by
  have h := (jstar_bounds m).2
  refine ⟨by omega, fun j hj => ?_⟩
  omega

/-- The ratio of the characteristic length `2 ^ m` to the mesh `2 ^ (m - 4 * j - 1)`
(natural-number subtraction, so the mesh is `2 ^ max 0 (m - 4 * j - 1)`) is at most
`2 ^ (4 * j + 1)`. -/
theorem mesh_ratio_le (m j : ℕ) :
    2 ^ m ≤ 2 ^ (4 * j + 1) * 2 ^ (m - 4 * j - 1) := by
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The inequality `j ^ 2 * 2 ^ (k - j) ≤ 2 * 2 ^ k` for `j ≤ k`. -/
theorem sq_mul_two_pow_le (k j : ℕ) (hj : j ≤ k) :
    (j : ℝ) ^ 2 * 2 ^ (k - j) ≤ 2 * 2 ^ k := by
  have hsq : ∀ i : ℕ, i ^ 2 ≤ 2 ^ (i + 1) := by
    intro i
    by_cases hi : i < 3
    · interval_cases i <;> norm_num
    · have hi3 : 3 ≤ i := not_lt.1 hi
      induction i, hi3 using Nat.le_induction with
      | base => norm_num
      | succ n hn ih =>
        calc (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
          _ ≤ 2 * 2 ^ (n + 1) := Nat.mul_le_mul_left 2 (ih (not_lt.2 hn))
          _ = 2 ^ (n + 1 + 1) := by ring
  have h1 : (j : ℝ) ^ 2 ≤ 2 ^ (j + 1) := by exact_mod_cast hsq j
  have h2 : (2 : ℝ) ^ (j + 1) * 2 ^ (k - j) = 2 * 2 ^ k := by
    have hexp : j + 1 + (k - j) = k + 1 := by omega
    rw [← pow_add, hexp, pow_succ']
  calc (j : ℝ) ^ 2 * 2 ^ (k - j) ≤ 2 ^ (j + 1) * 2 ^ (k - j) := by gcongr
    _ = 2 * 2 ^ k := h2

/-- From the record inequality at `(k, j)`: a mesh `l_{j,k} = 2 ^ (m k - 4 j - 1)`
larger than `1` satisfies `2 * l_{j,k} ≤ L (k - j) = 2 ^ m (k - j)`. -/
theorem mesh_double_le_length (m : ℕ → ℕ) (k j : ℕ)
    (hrec : (2 : ℝ) ^ m k / 2 ^ (4 * j) ≤ 2 ^ m (k - j))
    (hmesh : 1 < (2 : ℝ) ^ (m k - 4 * j - 1)) :
    2 * (2 : ℝ) ^ (m k - 4 * j - 1) ≤ 2 ^ m (k - j) := by
  have he : m k - 4 * j - 1 ≠ 0 := by
    intro h0
    rw [h0] at hmesh
    norm_num at hmesh
  have hmk : (2 : ℝ) ^ m k = 2 ^ (4 * j) * (2 * 2 ^ (m k - 4 * j - 1)) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  rw [hmk, mul_div_cancel_left₀ _ (by positivity)] at hrec
  exact hrec

/-- The bound `l_{j,k} ≤ w ^ 3 / 2` for `w = 2 ^ (k - j)`, from the record
inequality and `m (k - j) ≤ 3 * (k - j)`. -/
theorem mesh_le_half_cube (m : ℕ → ℕ) (k j : ℕ)
    (hrec : (2 : ℝ) ^ m k / 2 ^ (4 * j) ≤ 2 ^ m (k - j))
    (hmesh : 1 < (2 : ℝ) ^ (m k - 4 * j - 1)) (hm3 : m (k - j) ≤ 3 * (k - j)) :
    (2 : ℝ) ^ (m k - 4 * j - 1) ≤ ((2 : ℝ) ^ (k - j)) ^ 3 / 2 := by
  have h1 := mesh_double_le_length m k j hrec hmesh
  have h2 : (2 : ℝ) ^ m (k - j) ≤ ((2 : ℝ) ^ (k - j)) ^ 3 := by
    rw [← pow_mul, mul_comm]
    exact pow_le_pow_right₀ (by norm_num) hm3
  linarith

/-- The abstract form of the trial-probability bound: if `P k n > q0` for
integers `1 ≤ n < L k / 2` at index `k - j`, and the record inequality holds at
`(k, j)`, then `P (k - j) l > q0` for every integer `1 ≤ l < l_{j,k}`. -/
theorem trial_probability_of_record (P : ℕ → ℕ → ℝ) (q0 : ℝ) (m : ℕ → ℕ) (k j : ℕ)
    (hcount : ∀ n : ℕ, 1 ≤ n → (n : ℝ) < 2 ^ m (k - j) / 2 → q0 < P (k - j) n)
    (hrec : (2 : ℝ) ^ m k / 2 ^ (4 * j) ≤ 2 ^ m (k - j)) (l : ℕ) (hl : 1 ≤ l)
    (hlt : (l : ℝ) < 2 ^ (m k - 4 * j - 1)) : q0 < P (k - j) l := by
  have hmesh : 1 < (2 : ℝ) ^ (m k - 4 * j - 1) :=
    lt_of_le_of_lt (by exact_mod_cast hl) hlt
  have h1 := mesh_double_le_length m k j hrec hmesh
  exact hcount l hl (by linarith)

/-- All of the above for the characteristic lengths of an arbitrary family `P`.
Under the two inputs of `exists_first_dyadic_characteristic_length`, there are a
positive `k0`, functions `m` (with `L k = 2 ^ m k`) and `nk`, and an infinite set
`K` of record indices such that: the first-dyadic properties hold for `k ≥ k0`;
the record inequality `L (k - j) ≥ 2 ^ (-4 j) * L k` holds for `k ∈ K` and
`j ≤ k - k0`; and for `k ∈ K`, `k ≥ 4 * k0 + 3` and every scale index
`j ≤ ⌈(m k - 1) / 4⌉` the trial-probability bound `P (k - j) l > q0` holds for
integers `1 ≤ l < l_{j,k}`, and a mesh `l_{j,k} > 1` has `l_{j,k} ≤ w ^ 3 / 2`
for `w = 2 ^ (k - j)`. -/
theorem scale_record_arithmetic (P : ℕ → ℕ → ℝ) (q0 : ℝ) (hq0 : q0 < 1)
    (htilt : ∀ᶠ k : ℕ in atTop, P k (2 ^ (3 * k)) ≤ q0)
    (hshort : ∀ C : ℝ, 0 < C → ∀ c : ℝ, c < 1 →
      ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ C * 2 ^ k → c < P k n) :
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
  obtain ⟨k0, hk0, m, nk, htend, h⟩ :=
    exists_first_dyadic_characteristic_length P q0 hq0 htilt hshort
  obtain ⟨K, hKinf, hK⟩ := exists_infinite_record_scales m k0 fun k hk => (h k hk).2.2.1
  refine ⟨k0, hk0, m, nk, K, htend, h, hKinf, hK, fun k hkK hk j hj => ?_⟩
  have hidx := scale_index_bounds k0 k (m k) hk ((h k (hK k hkK).1).2.2.1)
  obtain ⟨hjk, hk0j, -, -⟩ := hidx.2 j hj
  have hrec := (hK k hkK).2 j (by omega)
  have hm3 : m (k - j) ≤ 3 * (k - j) := (h (k - j) hk0j).2.2.1
  exact ⟨fun l hl hlt => trial_probability_of_record P q0 m k j
      (fun n hn hnlt => (h (k - j) hk0j).2.2.2.1 n hn hnlt) hrec l hl hlt,
    fun hmesh => mesh_le_half_cube m k j hrec hmesh hm3⟩

end LPPDifferentiability
