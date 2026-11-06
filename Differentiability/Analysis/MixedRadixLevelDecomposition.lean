/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Analysis.GridScaleCounts
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Coarse levels and the mixed-radix decomposition of a level interval

Level-only arithmetic of the entrance and exit paths in the proof of the arbitrary-endpoints
proposition (Proposition 5.9 of the differentiability preprint, with the displays (5.39) and
(5.40)). The mesh at scale `j` is `l j = 2 ^ (m - 4 j - 1)`, given by a hypothesis `hl`, and
`jstar = ⌈(m - 1) / 4⌉`. A grid interval at scale `j` is `[e, e + l j]` with `e` a multiple of
`l j` and `|e| ≤ (A + 4) 2 ^ m`.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function
  in the planar corner growth model*, preprint.
-/

public section

open Filter

namespace LPPDifferentiability

private theorem floor_ceil_facts (l : ℕ) (hl : 0 < l) (a : ℤ) :
    ⌊(a : ℝ) / l⌋ * (l : ℤ) ≤ a ∧ a < (⌊(a : ℝ) / l⌋ + 1) * (l : ℤ) ∧
      (⌈(a : ℝ) / l⌉ - 1) * (l : ℤ) < a ∧ a ≤ ⌈(a : ℝ) / l⌉ * (l : ℤ) := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have h1 := Int.floor_le ((a : ℝ) / l)
  have h2 := Int.lt_floor_add_one ((a : ℝ) / l)
  have h3 := Int.le_ceil ((a : ℝ) / l)
  have h4 := Int.ceil_lt_add_one ((a : ℝ) / l)
  rw [le_div_iff₀ hl'] at h1
  rw [div_le_iff₀ hl'] at h3
  rw [div_lt_iff₀ hl'] at h2
  have h4' : ((⌈(a : ℝ) / l⌉ : ℝ) - 1) * l < a := by
    have h5 := Int.ceil_lt_add_one ((a : ℝ) / l)
    have : (⌈(a : ℝ) / l⌉ : ℝ) - 1 < (a : ℝ) / l := by linarith
    rw [lt_div_iff₀ hl'] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h4'
  · exact_mod_cast h3

/-- The endpoints (5.39) and (5.40) of the differentiability preprint: `I⁻ = (⌊a / l⌋ - 1) l` and
`I⁺ = (⌈a / l⌉ + 1) l` for the level
`a = level u`, the scale-`J` mesh `l`, are multiples of `l`, both `a - I⁻` and `I⁺ - a` lie in
`[l, 2 l)`, and `|I^±| ≤ |a| + 2 l ≤ (A + 4) 2 ^ m` when `|a| ≤ A 2 ^ m` and `l ≤ 2 ^ m`. -/
theorem grid_level_endpoints {A : ℝ} {m l : ℕ} (hl : 0 < l) (hlm : l ≤ 2 ^ m) {a : ℤ}
    (ha : |(a : ℝ)| ≤ A * 2 ^ m) :
    (l : ℤ) ∣ (⌊(a : ℝ) / l⌋ - 1) * (l : ℤ) ∧ (l : ℤ) ∣ (⌈(a : ℝ) / l⌉ + 1) * (l : ℤ) ∧
      ((l : ℤ) ≤ a - (⌊(a : ℝ) / l⌋ - 1) * (l : ℤ) ∧
        a - (⌊(a : ℝ) / l⌋ - 1) * (l : ℤ) < 2 * (l : ℤ)) ∧
      ((l : ℤ) ≤ (⌈(a : ℝ) / l⌉ + 1) * (l : ℤ) - a ∧
        (⌈(a : ℝ) / l⌉ + 1) * (l : ℤ) - a < 2 * (l : ℤ)) ∧
      |(((⌊(a : ℝ) / l⌋ - 1) * (l : ℤ) : ℤ) : ℝ)| ≤ (A + 4) * 2 ^ m ∧
      |(((⌈(a : ℝ) / l⌉ + 1) * (l : ℤ) : ℤ) : ℝ)| ≤ (A + 4) * 2 ^ m := by
  obtain ⟨f1, f2, c1, c2⟩ := floor_ceil_facts l hl a
  have hlr : (l : ℝ) ≤ 2 ^ m := by exact_mod_cast hlm
  have hp : (0 : ℝ) ≤ 2 ^ m := by positivity
  have hab := abs_le.1 ha
  refine ⟨Dvd.intro_left _ rfl, Dvd.intro_left _ rfl, ⟨by linarith, by linarith⟩,
    ⟨by linarith, by linarith⟩, ?_, ?_⟩
  · have e1 : a - 2 * (l : ℤ) < (⌊(a : ℝ) / l⌋ - 1) * (l : ℤ) := by linarith
    have e2 : (⌊(a : ℝ) / l⌋ - 1) * (l : ℤ) ≤ a := by linarith
    have e1' : ((a : ℝ) - 2 * l) < (((⌊(a : ℝ) / l⌋ - 1) * (l : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast e1
    have e2' : (((⌊(a : ℝ) / l⌋ - 1) * (l : ℤ) : ℤ) : ℝ) ≤ a := by exact_mod_cast e2
    rw [abs_le]
    constructor <;> nlinarith
  · have e1 : (⌈(a : ℝ) / l⌉ + 1) * (l : ℤ) < a + 2 * (l : ℤ) := by linarith
    have e2 : a ≤ (⌈(a : ℝ) / l⌉ + 1) * (l : ℤ) := by linarith
    have e1' : (((⌈(a : ℝ) / l⌉ + 1) * (l : ℤ) : ℤ) : ℝ) < (a : ℝ) + 2 * l := by
      exact_mod_cast e1
    have e2' : (a : ℝ) ≤ (((⌈(a : ℝ) / l⌉ + 1) * (l : ℤ) : ℤ) : ℝ) := by exact_mod_cast e2
    rw [abs_le]
    constructor <;> nlinarith

/-- If `level u ≤ level u'` then `I⁺(u') - I⁻(u) ≥ 2 l`, as used for the coarse-level gap in the
proof of Proposition 5.9 of the differentiability preprint. -/
theorem grid_level_endpoints_gap {l : ℕ} (hl : 0 < l) {a a' : ℤ} (h : a ≤ a') :
    2 * (l : ℤ) ≤ (⌈(a' : ℝ) / l⌉ + 1) * (l : ℤ) - (⌊(a : ℝ) / l⌋ - 1) * (l : ℤ) := by
  obtain ⟨f1, -, -, -⟩ := floor_ceil_facts l hl a
  obtain ⟨-, -, -, c2⟩ := floor_ceil_facts l hl a'
  linarith

private theorem radix_step (L : ℕ) (hL : 0 < L) (q a : ℤ) (h0 : 0 ≤ a - q)
    (h16 : a - q < 16 * L) :
    ∃ nj : ℕ, (nj : ℤ) = (a - q) / L ∧ nj ≤ 15 ∧ 0 ≤ a - (q + nj * L) ∧
      a - (q + nj * L) < L := by
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  have hn0 : 0 ≤ (a - q) / L := Int.ediv_nonneg h0 hL'.le
  have hn : (((a - q) / L).toNat : ℤ) = (a - q) / L := Int.toNat_of_nonneg hn0
  have hlt : (a - q) / L < 16 := (Int.ediv_lt_iff_lt_mul hL').2 (by linarith)
  have e : a - (q + (a - q) / L * L) = (a - q) % L := by rw [Int.emod_def]; ring
  refine ⟨((a - q) / L).toNat, hn, by omega, ?_, ?_⟩
  · rw [hn, e]; exact Int.emod_nonneg _ hL'.ne'
  · rw [hn, e]; exact Int.emod_lt_of_pos _ hL'

private theorem radix_core (l : ℕ → ℕ) (jstar : ℕ) (a : ℤ) (hpos : ∀ j, 0 < l j)
    (hdvd : ∀ j, j < jstar → l (j + 1) ∣ l j) (hratio : ∀ j, j < jstar → l j ≤ 16 * l (j + 1))
    (hlast : l jstar = 1) :
    ∀ r j q, j + r = jstar → (l j : ℤ) ∣ q → 0 ≤ a - q → a - q < 16 * l j →
      ∃ (n : ℕ → ℕ) (q' : ℕ → ℤ), q' j = q ∧ q' (jstar + 1) = a ∧
        ∀ i, j ≤ i → i ≤ jstar → (n i : ℤ) = (a - q' i) / l i ∧
          q' (i + 1) = q' i + n i * l i ∧ 0 ≤ a - q' (i + 1) ∧ a - q' (i + 1) < l i ∧
          (l i : ℤ) ∣ q' i ∧ n i ≤ 15 := by
  intro r
  induction r with
  | zero =>
    intro j q hj hd h0 h16
    obtain rfl : j = jstar := by omega
    obtain ⟨nj, hnj, hle, hr0, hr1⟩ := radix_step (l j) (hpos j) q a h0 h16
    simp only [hlast, Nat.cast_one, mul_one, Int.ediv_one] at hr0 hr1 hnj
    have hq1 : a = q + nj := by omega
    refine ⟨fun _ => nj, fun i => if i = j then q else a, by simp, by simp, ?_⟩
    intro i hi hi'
    obtain rfl : j = i := (le_antisymm hi' hi).symm
    simp only [hlast, Nat.cast_one, mul_one, Int.ediv_one, ite_true, show ¬ (j + 1 = j) by omega,
      ite_false]
    exact ⟨hnj, hq1, by omega, by omega, one_dvd _, hle⟩
  | succ r ih =>
    intro j q hj hd h0 h16
    have hjlt : j < jstar := by omega
    obtain ⟨nj, hnj, hle, hr0, hr1⟩ := radix_step (l j) (hpos j) q a h0 h16
    have hd1 : (l (j + 1) : ℤ) ∣ q + nj * l j := by
      have h1 : (l (j + 1) : ℤ) ∣ l j := by exact_mod_cast hdvd j hjlt
      exact dvd_add (h1.trans hd) (Dvd.dvd.mul_left h1 _)
    have hr1' : a - (q + nj * l j) < 16 * l (j + 1) := by
      have := hratio j hjlt
      have h2 : (l j : ℤ) ≤ 16 * l (j + 1) := by exact_mod_cast this
      linarith
    obtain ⟨n', q'', hq1, hqend, hall⟩ := ih (j + 1) (q + nj * l j) (by omega) hd1 hr0 hr1'
    refine ⟨Function.update n' j nj, Function.update q'' j q, by simp, ?_, ?_⟩
    · rw [Function.update_of_ne (by omega)]; exact hqend
    · intro i hji hij
      rcases eq_or_lt_of_le hji with rfl | hlt
      · rw [Function.update_self, Function.update_self, Function.update_of_ne (by omega), hq1]
        exact ⟨hnj, rfl, hr0, hr1, hd, hle⟩
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
        exact hall i hlt hij

private theorem mesh_facts {m jstar : ℕ} (hjstar : jstar = ⌈((m : ℝ) - 1) / 4⌉₊) (l : ℕ → ℕ)
    (hl : ∀ j, l j = 2 ^ (m - 4 * j - 1)) :
    (∀ j, 0 < l j) ∧ (∀ j, j < jstar → l (j + 1) ∣ l j) ∧
      (∀ j, j < jstar → l j ≤ 16 * l (j + 1)) ∧ l jstar = 1 := by
  refine ⟨fun j => by rw [hl]; positivity, fun j _ => ?_, fun j hj => ?_, ?_⟩
  · rw [hl, hl]; exact grid_mesh_dvd m (Nat.le_succ j)
  · rw [hl, hl]
    rcases grid_mesh_ratio hjstar hj with h | h | h | h <;> rw [h] <;> omega
  · rw [hl]; exact grid_mesh_jstar hjstar

/-- Mixed-radix decomposition of `[I⁻, a]` for the level `a = level u`, as in the proof of
Proposition 5.9 of the differentiability preprint.
There are counts `n j` and breakpoints `q j` with `q J = I⁻`; scale `j` (`J ≤ j ≤ jstar`)
uses the `n j` consecutive intervals `[q j + t l j, q j + (t + 1) l j]`, `t < n j`, ending at
`q (j + 1)`; `n J = 1`, `n j ≤ 15` for `j > J`, the remainder `a - q (j + 1)` is in `[0, l j)`,
the last breakpoint `q (jstar + 1)` is exactly `a`, and every left endpoint lies in the grid
`𝒢_j` (a multiple of `l j` of absolute value at most `(A + 4) 2 ^ m`) with its interval
inside `[I⁻, a]`. -/
theorem grid_mixed_radix_lower {A : ℝ} {m J jstar : ℕ}
    (hjstar : jstar = ⌈((m : ℝ) - 1) / 4⌉₊) (l : ℕ → ℕ) (hl : ∀ j, l j = 2 ^ (m - 4 * j - 1))
    (hJ : J ≤ jstar) {a : ℤ} (ha : |(a : ℝ)| ≤ A * 2 ^ m) :
    ∃ (n : ℕ → ℕ) (q : ℕ → ℤ), q J = (⌊(a : ℝ) / l J⌋ - 1) * (l J : ℤ) ∧ n J = 1 ∧
      (∀ j, J < j → j ≤ jstar → n j ≤ 15) ∧
      (∀ j, J ≤ j → j ≤ jstar → q (j + 1) = q j + n j * l j ∧ 0 ≤ a - q (j + 1) ∧
        a - q (j + 1) < l j) ∧
      q (jstar + 1) = a ∧
      (∀ j, J ≤ j → j ≤ jstar → ∀ t, t < n j →
        (l j : ℤ) ∣ q j + t * l j ∧ |((q j + t * l j : ℤ) : ℝ)| ≤ (A + 4) * 2 ^ m ∧
          q j + (t + 1) * l j ≤ a) := by
  obtain ⟨hpos, hdvd, hratio, hlast⟩ := mesh_facts hjstar l hl
  have hlm : l J ≤ 2 ^ m := by rw [hl]; exact grid_mesh_le m J
  obtain ⟨-, -, hg1, hg2, hb1, -⟩ := grid_level_endpoints (A := A) (hpos J) hlm ha
  obtain ⟨f1, f2, -, -⟩ := floor_ceil_facts (l J) (hpos J) a
  obtain ⟨n, q, hqJ, hqend, hall⟩ := radix_core l jstar a hpos hdvd hratio hlast (jstar - J) J
    ((⌊(a : ℝ) / l J⌋ - 1) * (l J : ℤ)) (by omega) (Dvd.intro_left _ rfl) (by linarith)
    (by linarith)
  have hL : (0 : ℤ) < l J := by exact_mod_cast hpos J
  have hn1 : n J = 1 := by
    have h := (hall J le_rfl hJ).1
    rw [hqJ] at h
    have h1 : (1 : ℤ) ≤ (a - (⌊(a : ℝ) / l J⌋ - 1) * (l J : ℤ)) / l J :=
      (Int.le_ediv_iff_mul_le hL).2 (by linarith)
    have h2 : (a - (⌊(a : ℝ) / l J⌋ - 1) * (l J : ℤ)) / l J < 2 :=
      (Int.ediv_lt_iff_lt_mul hL).2 (by linarith)
    omega
  have hmono : ∀ j, J ≤ j → j ≤ jstar + 1 → q J ≤ q j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hj ih =>
      intro hj1
      have h := (hall j hj (by omega)).2.1
      have : (0 : ℤ) ≤ n j * l j := by positivity
      linarith [ih (by omega)]
  refine ⟨n, q, hqJ, hn1, fun j hj hj' => (hall j hj.le hj').2.2.2.2.2,
    fun j hj hj' => ?_, hqend, fun j hj hj' t ht => ?_⟩
  · obtain ⟨-, h2, h3, h4, -, -⟩ := hall j hj hj'
    exact ⟨h2, h3, h4⟩
  · obtain ⟨-, h2, h3, -, h5, -⟩ := hall j hj hj'
    have hr : q j + (t + 1) * l j ≤ q (j + 1) := by
      have : ((t : ℤ) + 1) * l j ≤ n j * l j := by
        have : (t : ℤ) + 1 ≤ n j := by exact_mod_cast ht
        exact mul_le_mul_of_nonneg_right this (by positivity)
      linarith
    have hr2 : q j + (t + 1) * l j ≤ a := by linarith
    refine ⟨dvd_add h5 (Dvd.intro_left _ rfl), ?_, hr2⟩
    have hge : a - 2 * (l J : ℤ) < q j + t * l j := by
      have := hmono j hj (by omega)
      have h0 : (0 : ℤ) ≤ t * l j := by positivity
      rw [hqJ] at this
      linarith
    have hle : q j + t * l j ≤ a := by
      have : (0 : ℤ) ≤ l j := by positivity
      linarith
    have hge' : (a : ℝ) - 2 * l J < ((q j + t * l j : ℤ) : ℝ) := by exact_mod_cast hge
    have hle' : ((q j + t * l j : ℤ) : ℝ) ≤ a := by exact_mod_cast hle
    have hlr : (l J : ℝ) ≤ 2 ^ m := by exact_mod_cast hlm
    have hab := abs_le.1 ha
    have hp : (0 : ℝ) ≤ 2 ^ m := by positivity
    rw [abs_le]
    constructor <;> nlinarith

/-- Mirror of the mixed-radix decomposition above: the decomposition of `[a, I⁺]` from the right.
The breakpoints satisfy `q J = I⁺ = (⌈a / l J⌉ + 1) l J`, scale `j` uses the intervals
`[q j - (t + 1) l j, q j - t l j]`, `t < n j`, going down to `q (j + 1) ≥ a`, with the
same counts and remainder bounds, `q (jstar + 1) = a`, and left endpoints in `𝒢_j`. -/
theorem grid_mixed_radix_upper {A : ℝ} {m J jstar : ℕ}
    (hjstar : jstar = ⌈((m : ℝ) - 1) / 4⌉₊) (l : ℕ → ℕ) (hl : ∀ j, l j = 2 ^ (m - 4 * j - 1))
    (hJ : J ≤ jstar) {a : ℤ} (ha : |(a : ℝ)| ≤ A * 2 ^ m) :
    ∃ (n : ℕ → ℕ) (q : ℕ → ℤ), q J = (⌈(a : ℝ) / l J⌉ + 1) * (l J : ℤ) ∧ n J = 1 ∧
      (∀ j, J < j → j ≤ jstar → n j ≤ 15) ∧
      (∀ j, J ≤ j → j ≤ jstar → q (j + 1) = q j - n j * l j ∧ 0 ≤ q (j + 1) - a ∧
        q (j + 1) - a < l j) ∧
      q (jstar + 1) = a ∧
      (∀ j, J ≤ j → j ≤ jstar → ∀ t, t < n j →
        (l j : ℤ) ∣ q j - (t + 1) * l j ∧ |((q j - (t + 1) * l j : ℤ) : ℝ)| ≤ (A + 4) * 2 ^ m ∧
          a ≤ q j - (t + 1) * l j) := by
  have ha' : |(((-a : ℤ)) : ℝ)| ≤ A * 2 ^ m := by push_cast; rwa [abs_neg]
  obtain ⟨n, q, hqJ, hn1, hn15, htile, hend, hmem⟩ := grid_mixed_radix_lower hjstar l hl hJ ha'
  have hfl : ⌊(((-a : ℤ)) : ℝ) / l J⌋ = -⌈(a : ℝ) / l J⌉ := by
    push_cast; rw [neg_div, Int.floor_neg]
  refine ⟨n, fun i => - q i, ?_, hn1, hn15, fun j hj hj' => ?_, by simp [hend], fun j hj hj' t ht => ?_⟩
  · simp only [hqJ, hfl]; ring
  · obtain ⟨h1, h2, h3⟩ := htile j hj hj'
    refine ⟨by linarith, by linarith, by linarith⟩
  · obtain ⟨h1, h2, h3⟩ := hmem j hj hj' t ht
    have hd : (l j : ℤ) ∣ q j + (t + 1) * l j := by
      have : q j + (t + 1) * l j = (q j + t * l j) + l j := by ring
      rw [this]; exact dvd_add h1 dvd_rfl
    have hlj : (0 : ℝ) ≤ l j := by positivity
    have h4 : (((q j + t * l j : ℤ) : ℝ)) ≤ ((q j + (t + 1) * l j : ℤ) : ℝ) := by
      push_cast; nlinarith
    have h5 : ((q j + (t + 1) * l j : ℤ) : ℝ) ≤ ((-a : ℤ) : ℝ) := by exact_mod_cast h3
    have hab := abs_le.1 ha'
    have hab2 := abs_le.1 h2
    have hp : (0 : ℝ) ≤ 2 ^ m := by positivity
    refine ⟨?_, ?_, by linarith⟩
    · have : -q j - (t + 1) * l j = -(q j + (t + 1) * l j) := by ring
      show (l j : ℤ) ∣ -q j - (t + 1) * l j
      rw [this]; exact (dvd_neg).2 hd
    · show |(((-q j - (t + 1) * l j : ℤ)) : ℝ)| ≤ (A + 4) * 2 ^ m
      rw [abs_le]; push_cast at h4 h5 hab hab2 ⊢
      constructor <;> nlinarith

/-- The coarse levels `l_J ℤ ∩ [-(A+4) clen, (A+4) clen]` give at most
`(2 (A + 4) 2 ^ (4 J + 1) + 1) ^ 2` pairs `(I⁻, I⁺)`. The finite set `S` is any set of pairs
both of whose coordinates are coarse levels (so it covers the pairs with `I⁻ < I⁺`).
This is the count in the proof of Proposition 5.9 of the differentiability preprint. -/
theorem grid_coarse_pair_count_le {A : ℝ} (hA : 0 < A) (m J : ℕ) (S : Finset (ℤ × ℤ))
    (hS : ∀ p ∈ S, (((2 ^ (m - 4 * J - 1) : ℕ) : ℤ) ∣ p.1 ∧ |(p.1 : ℝ)| ≤ (A + 4) * 2 ^ m) ∧
      (((2 ^ (m - 4 * J - 1) : ℕ) : ℤ) ∣ p.2 ∧ |(p.2 : ℝ)| ≤ (A + 4) * 2 ^ m)) :
    (S.card : ℝ) ≤ (2 * (A + 4) * 2 ^ (4 * J + 1) + 1) ^ 2 := by
  have hfin : {I : ℤ | ((2 ^ (m - 4 * J - 1) : ℕ) : ℤ) ∣ I ∧
      |(I : ℝ)| ≤ (A + 4) * 2 ^ m}.Finite := by
    refine (Set.finite_Icc (-⌈(A + 4) * 2 ^ m⌉) ⌈(A + 4) * 2 ^ m⌉).subset ?_
    intro I hI
    have h := abs_le.1 hI.2
    have hc := Int.le_ceil ((A + 4) * 2 ^ m)
    constructor
    · have : (((-⌈(A + 4) * 2 ^ m⌉ : ℤ)) : ℝ) ≤ (I : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : (I : ℝ) ≤ ((⌈(A + 4) * 2 ^ m⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  have hG := (grid_count_le hA m J hfin.toFinset (fun I => by simp)).1
  have hr : (2 : ℝ) ^ m / 2 ^ (m - 4 * J - 1) ≤ 2 ^ (4 * J + 1) := by
    rw [div_le_iff₀ (by positivity)]
    exact_mod_cast grid_level_ratio_le m J
  have h1 : 2 * (A + 4) * (2 : ℝ) ^ m / 2 ^ (m - 4 * J - 1) ≤ 2 * (A + 4) * 2 ^ (4 * J + 1) := by
    rw [mul_div_assoc]
    gcongr
  have hsub : S ⊆ hfin.toFinset ×ˢ hfin.toFinset := by
    intro p hp
    obtain ⟨h1, h2⟩ := hS p hp
    exact Finset.mem_product.2 ⟨by simpa using h1, by simpa using h2⟩
  calc (S.card : ℝ) ≤ ((hfin.toFinset ×ˢ hfin.toFinset).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = (hfin.toFinset.card : ℝ) ^ 2 := by rw [Finset.card_product]; push_cast; ring
    _ ≤ (2 * (A + 4) * 2 ^ (4 * J + 1) + 1) ^ 2 := by
        gcongr
        linarith

/-- `2 l_J / s_k = 2 ^ (m - k - 4 J)` when `4 J + 1 ≤ m`, as in the proof of Proposition 5.9 of
the differentiability preprint. -/
theorem grid_two_mesh_div_scale_eq {m k J : ℕ} (h : 4 * J + 1 ≤ m) :
    2 * (2 : ℝ) ^ (m - 4 * J - 1) / 2 ^ k = (2 : ℝ) ^ ((m : ℤ) - k - 4 * J) := by
  have h1 : 2 * (2 : ℝ) ^ (m - 4 * J - 1) = 2 ^ (m - 4 * J) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2 : ((m : ℤ) - k - 4 * J) = ((m - 4 * J : ℕ) : ℤ) - k := by omega
  rw [h1, h2, zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]

/-- `2 l_J / s_k` tends to infinity when `m_k - k` does, along any filter
(in the proof of Proposition 5.9 of the differentiability preprint, `k → ∞` in `𝒦`). -/
theorem grid_two_mesh_div_scale_tendsto {ι : Type*} {f : Filter ι} {m k : ι → ℕ} (J : ℕ)
    (h : Tendsto (fun i => (m i : ℤ) - k i) f atTop) :
    Tendsto (fun i => 2 * (2 : ℝ) ^ (m i - 4 * J - 1) / 2 ^ k i) f atTop := by
  have h2 : Tendsto (fun i => (m i : ℤ) - k i - 4 * J) f atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right f (-(4 * (J : ℤ))) h
  have hev : ∀ᶠ i in f, ((4 * J + 1 : ℕ) : ℤ) ≤ (m i : ℤ) - k i := h.eventually_ge_atTop _
  have hz := (tendsto_intCast_atTop_atTop (R := ℝ)).comp h2
  refine tendsto_atTop_mono' f ?_ hz
  filter_upwards [hev] with i hi
  push_cast at hi
  rw [grid_two_mesh_div_scale_eq (by omega)]
  have hz0 : 0 ≤ (m i : ℤ) - k i - 4 * J := by omega
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hz0
  simp only [Function.comp_apply, hn, zpow_natCast, Int.cast_natCast]
  have h3 : n < 2 ^ n := Nat.lt_two_pow_self
  exact_mod_cast h3.le

end LPPDifferentiability
