/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Grid scales: meshes, counts and level bounds

Level-only arithmetic of the grid scales in the section on simultaneous grid connections.
It uses Sections 5.1 and 5.2 of the differentiability preprint, and (5.17), (5.18) and
(5.25) there.

Throughout, `m = m_k`, `k` and `j` are natural numbers, `jstar` is the finest
scale index `⌈(m - 1) / 4⌉`, the mesh at scale `j` is `2 ^ (m - 4 * j - 1)`
(natural subtraction truncated at zero, which is `2 ^ max 0 (m - 4 j - 1)`), and the
width at scale `j` is `2 ^ (k - j)`. A set of the preprint (`𝒢_j`, `ℋ_j`) appears here as an
arbitrary `Finset` whose members are exactly that set.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint.
-/

public section

namespace LPPDifferentiability

/-- As in (5.1) of the differentiability preprint: `j < jstar` exactly when `4 j + 1 < m`. -/
theorem grid_lt_jstar_iff {m j jstar : ℕ} (hjstar : jstar = ⌈((m : ℝ) - 1) / 4⌉₊) :
    j < jstar ↔ 4 * j + 1 < m := by
  subst hjstar
  rw [Nat.lt_ceil]
  constructor
  · intro h
    have h1 : ((4 * j + 1 : ℕ) : ℝ) < (m : ℝ) := by push_cast; linarith
    exact_mod_cast h1
  · intro h
    have h1 : ((4 * j + 1 : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast h
    push_cast at h1
    linarith

/-- As in (5.1) of the differentiability preprint: `m ≤ 4 jstar + 1` and `4 jstar ≤ m + 2`, that is
`(m - 1) / 4 ≤ jstar ≤ (m - 1) / 4 + 1`. -/
theorem grid_jstar_bounds {m jstar : ℕ} (hjstar : jstar = ⌈((m : ℝ) - 1) / 4⌉₊) :
    m ≤ 4 * jstar + 1 ∧ 4 * jstar ≤ m + 2 := by
  constructor
  · have h := Nat.le_ceil (((m : ℝ) - 1) / 4)
    rw [← hjstar] at h
    have h1 : (m : ℝ) ≤ ((4 * jstar + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h1
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have : jstar = 0 := by
        rw [hjstar, Nat.ceil_eq_zero]
        norm_num
      omega
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ ((m : ℝ) - 1) / 4 by linarith)
      rw [← hjstar] at h
      have h1 : ((4 * jstar : ℕ) : ℝ) < ((m + 3 : ℕ) : ℝ) := by push_cast; linarith
      have h2 : 4 * jstar < m + 3 := by exact_mod_cast h1
      omega

/-- As in (5.2) of the differentiability preprint: for `j < jstar` the mesh `l_j = 2 ^ (m - 4 j -
1)` exceeds `1`. -/
theorem grid_mesh_gt_one {m j jstar : ℕ} (hjstar : jstar = ⌈((m : ℝ) - 1) / 4⌉₊)
    (hj : j < jstar) : 4 * j + 1 < m ∧ 1 < 2 ^ (m - 4 * j - 1) := by
  have h := (grid_lt_jstar_iff hjstar).1 hj
  exact ⟨h, Nat.one_lt_two_pow (by omega)⟩

/-- As in (5.2) of the differentiability preprint: for `j < jstar` the ratio `l_j / l_{j+1}` is `2`,
`4`, `8` or `16`. -/
theorem grid_mesh_ratio {m j jstar : ℕ} (hjstar : jstar = ⌈((m : ℝ) - 1) / 4⌉₊)
    (hj : j < jstar) :
    2 ^ (m - 4 * j - 1) = 2 * 2 ^ (m - 4 * (j + 1) - 1) ∨
      2 ^ (m - 4 * j - 1) = 4 * 2 ^ (m - 4 * (j + 1) - 1) ∨
      2 ^ (m - 4 * j - 1) = 8 * 2 ^ (m - 4 * (j + 1) - 1) ∨
      2 ^ (m - 4 * j - 1) = 16 * 2 ^ (m - 4 * (j + 1) - 1) := by
  have h := (grid_lt_jstar_iff hjstar).1 hj
  have hd : m - 4 * j - 1 = (m - 4 * (j + 1) - 1) + 1 ∨
      m - 4 * j - 1 = (m - 4 * (j + 1) - 1) + 2 ∨
      m - 4 * j - 1 = (m - 4 * (j + 1) - 1) + 3 ∨
      m - 4 * j - 1 = (m - 4 * (j + 1) - 1) + 4 := by omega
  rcases hd with hd | hd | hd | hd
  · left; rw [hd, pow_add]; ring
  · right; left; rw [hd, pow_add]; ring
  · right; right; left; rw [hd, pow_add]; ring
  · right; right; right; rw [hd, pow_add]; ring

/-- As in (5.2) of the differentiability preprint: the finest mesh `l_jstar` is `1`. -/
theorem grid_mesh_jstar {m jstar : ℕ} (hjstar : jstar = ⌈((m : ℝ) - 1) / 4⌉₊) :
    2 ^ (m - 4 * jstar - 1) = 1 := by
  have h := (grid_jstar_bounds hjstar).1
  rw [show m - 4 * jstar - 1 = 0 by omega]
  rfl

/-- As in (5.2) of the differentiability preprint: the meshes are nested powers of two, each a
multiple of the next. -/
theorem grid_mesh_dvd (m : ℕ) {i j : ℕ} (hij : i ≤ j) :
    2 ^ (m - 4 * j - 1) ∣ 2 ^ (m - 4 * i - 1) :=
  pow_dvd_pow 2 (by omega)

/-- By the mesh definition (5.2) of the differentiability preprint, the mesh `l_j` is at most
`clen = 2 ^ m`. -/
theorem grid_mesh_le (m j : ℕ) : 2 ^ (m - 4 * j - 1) ≤ 2 ^ m :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

/-- From the mesh definition (5.2) of the differentiability preprint and `clen = 2 ^ m`, for
`j < jstar` we have `clen / l_j = 2 ^ (4 j + 1)`. -/
theorem grid_level_ratio_eq {m j jstar : ℕ} (hjstar : jstar = ⌈((m : ℝ) - 1) / 4⌉₊)
    (hj : j < jstar) : 2 ^ m = 2 ^ (4 * j + 1) * 2 ^ (m - 4 * j - 1) := by
  have h := (grid_lt_jstar_iff hjstar).1 hj
  rw [← pow_add]
  congr 1
  omega

/-- The scale and mesh definitions (5.1)-(5.2) of the differentiability preprint give
`clen / l_j ≤ 2 ^ (4 j + 1)` at every scale, including `j = jstar`. -/
theorem grid_level_ratio_le (m j : ℕ) : 2 ^ m ≤ 2 ^ (4 * j + 1) * 2 ^ (m - 4 * j - 1) := by
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- As in (5.5) to (5.7) of the differentiability preprint: from `m ≤ 3 k` and `k ≥ 4 k0 + 3` every
scale index `j ≤ jstar`
has `jstar ≤ k`, `j ≤ k`, `k0 ≤ k - j`, and (for `k0 > 0`) the width `2 ^ (k - j)` is at least `2`.
-/
theorem grid_scale_index_bounds {m k k0 j jstar : ℕ}
    (hjstar : jstar = ⌈((m : ℝ) - 1) / 4⌉₊) (hm : m ≤ 3 * k) (hk : 4 * k0 + 3 ≤ k)
    (hk0 : 0 < k0) (hj : j ≤ jstar) :
    jstar ≤ k ∧ j ≤ k ∧ k0 ≤ k - j ∧ 2 ≤ 2 ^ (k - j) := by
  have h := (grid_jstar_bounds hjstar).2
  have h1 : k - j ≥ 1 := by omega
  refine ⟨by omega, by omega, by omega, ?_⟩
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (k - j) := Nat.pow_le_pow_right (by norm_num) h1

private theorem grid_count_aux (B : ℝ) (hB : 0 ≤ B) (l : ℕ) (hl : 0 < l) (S : Finset ℤ)
    (hS : ∀ I ∈ S, (l : ℤ) ∣ I ∧ |(I : ℝ)| ≤ B) : (S.card : ℝ) ≤ 2 * B / l + 1 := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  set n : ℤ := ⌊B / l⌋ with hn
  have hn0 : 0 ≤ n := Int.floor_nonneg.2 (by positivity)
  have hnle : (n : ℝ) ≤ B / l := Int.floor_le _
  have hmap : S.card ≤ (Finset.Icc (-n) n).card := by
    apply Finset.card_le_card_of_injOn (fun I : ℤ => I / (l : ℤ))
    · intro I hI
      obtain ⟨⟨t, rfl⟩, hb⟩ := hS I hI
      have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
      have ht : (l : ℤ) * t / (l : ℤ) = t := Int.mul_ediv_cancel_left t hl0
      simp only [ht, Finset.coe_Icc, Set.mem_Icc]
      have hb' : (l : ℝ) * |(t : ℝ)| ≤ B := by
        have : |((l * t : ℤ) : ℝ)| = (l : ℝ) * |(t : ℝ)| := by
          push_cast
          rw [abs_mul, abs_of_pos hl']
        linarith
      have hbt : |(t : ℝ)| ≤ B / l := by
        rw [le_div_iff₀ hl']
        linarith
      have h1 : t ≤ n := Int.le_floor.2 (le_trans (le_abs_self _) hbt)
      have h2 : -t ≤ n := Int.le_floor.2 (by
        have := neg_le_abs (t : ℝ)
        push_cast
        linarith)
      constructor <;> omega
    · intro I hI I' hI' h
      obtain ⟨⟨t, rfl⟩, _⟩ := hS I hI
      obtain ⟨⟨t', rfl⟩, _⟩ := hS I' hI'
      have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
      simp only [Int.mul_ediv_cancel_left _ hl0] at h
      rw [h]
  have hcard : ((Finset.Icc (-n) n).card : ℝ) = 2 * (n : ℝ) + 1 := by
    rw [Int.card_Icc]
    have : (n + 1 - -n).toNat = (2 * n + 1).toNat := by congr 1; ring
    rw [this]
    have h2 : ((2 * n + 1).toNat : ℤ) = 2 * n + 1 := Int.toNat_of_nonneg (by omega)
    rw [← Int.cast_natCast, h2]
    push_cast
    ring
  calc (S.card : ℝ) ≤ ((Finset.Icc (-n) n).card : ℝ) := by exact_mod_cast hmap
    _ = 2 * (n : ℝ) + 1 := hcard
    _ ≤ 2 * B / l + 1 := by
      have : 2 * (n : ℝ) ≤ 2 * (B / l) := by linarith
      rw [mul_div_assoc]
      linarith

/-- As in (5.3) and (5.4) of the differentiability preprint: the grid `𝒢_j = {I ∈ l_j ℤ : |I| ≤ (A +
4) clen}` has at most
`2 (A + 4) clen / l_j + 1 ≤ c_A 2 ^ (4 j)` elements, with `c_A = 4 (A + 4) + 1`. The finite
set `S` is any set with exactly the members of `𝒢_j`. -/
theorem grid_count_le {A : ℝ} (hA : 0 < A) (m j : ℕ) (S : Finset ℤ)
    (hS : ∀ I : ℤ, I ∈ S ↔
      (((2 ^ (m - 4 * j - 1) : ℕ) : ℤ) ∣ I ∧ |(I : ℝ)| ≤ (A + 4) * 2 ^ m)) :
    (S.card : ℝ) ≤ 2 * (A + 4) * 2 ^ m / 2 ^ (m - 4 * j - 1) + 1 ∧
      (S.card : ℝ) ≤ (4 * (A + 4) + 1) * 2 ^ (4 * j) := by
  have hl : 0 < 2 ^ (m - 4 * j - 1) := by positivity
  have h1 := grid_count_aux ((A + 4) * 2 ^ m) (by positivity) _ hl S (fun I hI => (hS I).1 hI)
  have hlr : (0 : ℝ) < 2 ^ (m - 4 * j - 1) := by positivity
  have e1 : 2 * ((A + 4) * (2 : ℝ) ^ m) / ((2 ^ (m - 4 * j - 1) : ℕ) : ℝ) =
      2 * (A + 4) * 2 ^ m / 2 ^ (m - 4 * j - 1) := by push_cast; ring
  rw [e1] at h1
  refine ⟨h1, ?_⟩
  have hr : (2 : ℝ) ^ m / 2 ^ (m - 4 * j - 1) ≤ 2 ^ (4 * j + 1) := by
    rw [div_le_iff₀ hlr]
    exact_mod_cast grid_level_ratio_le m j
  have h2 : 2 * (A + 4) * (2 : ℝ) ^ m / 2 ^ (m - 4 * j - 1) ≤ 2 * (A + 4) * 2 ^ (4 * j + 1) := by
    rw [mul_div_assoc]
    gcongr
  have h3 : (1 : ℝ) ≤ 2 ^ (4 * j) := one_le_pow₀ (by norm_num)
  calc (S.card : ℝ) ≤ 2 * (A + 4) * 2 ^ m / 2 ^ (m - 4 * j - 1) + 1 := h1
    _ ≤ 2 * (A + 4) * 2 ^ (4 * j + 1) + 1 := by linarith
    _ ≤ (4 * (A + 4) + 1) * 2 ^ (4 * j) := by
      rw [pow_succ]
      nlinarith

/-- As in (5.10) of the differentiability preprint: the bin set `ℋ_j` of indices `h` with `[h w, (h
+ 1) w)` meeting
`[-R s, R s]`, where `w = 2 ^ (k - j)` and `s = 2 ^ k`, has at most `2 R s / w + 2 ≤ c_R 2 ^ j`
elements, with `c_R = 2 R + 2`. -/
theorem grid_bin_count_le {R : ℝ} (hR : 0 < R) {k j : ℕ} (hjk : j ≤ k) (S : Finset ℤ)
    (hS : ∀ h : ℤ, h ∈ S ↔ ∃ x : ℝ, (h : ℝ) * 2 ^ (k - j) ≤ x ∧
      x < ((h : ℝ) + 1) * 2 ^ (k - j) ∧ |x| ≤ R * 2 ^ k) :
    (S.card : ℝ) ≤ 2 * R * 2 ^ k / 2 ^ (k - j) + 2 ∧ (S.card : ℝ) ≤ (2 * R + 2) * 2 ^ j := by
  have hw : (0 : ℝ) < 2 ^ (k - j) := by positivity
  have hsw : (2 : ℝ) ^ k / 2 ^ (k - j) = 2 ^ j := by
    rw [div_eq_iff hw.ne', ← pow_add]
    congr 1
    omega
  set y : ℝ := R * 2 ^ k / 2 ^ (k - j) with hy
  have hy0 : 0 < y := by positivity
  have hsub : S ⊆ Finset.Icc ⌊-y⌋ ⌊y⌋ := by
    intro h hh
    obtain ⟨x, hx1, hx2, hx3⟩ := (hS h).1 hh
    have hxabs := abs_le.1 hx3
    have h1 : (h : ℝ) ≤ y := by
      rw [hy, le_div_iff₀ hw]
      linarith
    have h2 : -y < (h : ℝ) + 1 := by
      have : -(R * 2 ^ k) < ((h : ℝ) + 1) * 2 ^ (k - j) := by linarith
      have h3 : -y * 2 ^ (k - j) < ((h : ℝ) + 1) * 2 ^ (k - j) := by
        rw [hy, neg_mul, div_mul_cancel₀ _ hw.ne']
        exact this
      exact lt_of_mul_lt_mul_right h3 hw.le
    have h3 : ⌊-y⌋ ≤ h := by
      have := Int.floor_le (-y)
      have h4 : ((⌊-y⌋ : ℤ) : ℝ) < (h : ℝ) + 1 := by linarith
      have h5 : ⌊-y⌋ < h + 1 := by exact_mod_cast h4
      omega
    exact Finset.mem_Icc.2 ⟨h3, Int.le_floor.2 h1⟩
  have hcard : (S.card : ℝ) ≤ ((Finset.Icc ⌊-y⌋ ⌊y⌋).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hfl : (⌊-y⌋ : ℝ) > -y - 1 := Int.sub_one_lt_floor _
  have hfl2 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le _
  have hpos : 0 ≤ ⌊y⌋ + 1 - ⌊-y⌋ := by
    have hfl3 : y - 1 < (⌊y⌋ : ℝ) := Int.sub_one_lt_floor _
    have hfl4 : (⌊-y⌋ : ℝ) ≤ -y := Int.floor_le _
    have : (0 : ℝ) < (⌊y⌋ : ℝ) + 1 - ⌊-y⌋ := by linarith
    have : (0 : ℝ) < ((⌊y⌋ + 1 - ⌊-y⌋ : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this.le
  have hcard2 : ((Finset.Icc ⌊-y⌋ ⌊y⌋).card : ℝ) = (⌊y⌋ : ℝ) + 1 - ⌊-y⌋ := by
    rw [Int.card_Icc]
    have h3 : (((⌊y⌋ + 1 - ⌊-y⌋).toNat : ℤ) : ℝ) = (⌊y⌋ : ℝ) + 1 - ⌊-y⌋ := by
      rw [Int.toNat_of_nonneg hpos]
      push_cast
      ring
    exact_mod_cast h3
  have h1 : (S.card : ℝ) ≤ 2 * R * 2 ^ k / 2 ^ (k - j) + 2 := by
    have : 2 * R * 2 ^ k / 2 ^ (k - j) = 2 * y := by rw [hy]; ring
    rw [this]
    linarith
  refine ⟨h1, ?_⟩
  have h2 : 2 * R * (2 : ℝ) ^ k / 2 ^ (k - j) = 2 * R * 2 ^ j := by
    rw [mul_div_assoc, hsw]
  have h3 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  calc (S.card : ℝ) ≤ 2 * R * 2 ^ k / 2 ^ (k - j) + 2 := h1
    _ = 2 * R * 2 ^ j + 2 := by rw [h2]
    _ ≤ (2 * R + 2) * 2 ^ j := by nlinarith

private theorem sq_le_two_pow_succ (i : ℕ) : i ^ 2 ≤ 2 ^ (i + 1) := by
  rcases Nat.lt_or_ge i 3 with h | h
  · interval_cases i <;> norm_num
  · induction i, h using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      calc (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
        _ ≤ 2 * 2 ^ (n + 1) := by omega
        _ = 2 ^ (n + 1 + 1) := by ring

/-- As in (5.9) of the differentiability preprint: `j ^ 2 w_j = j ^ 2 2 ^ (k - j) ≤ 2 s_k`. -/
theorem grid_sq_mul_width_le {j k : ℕ} (hjk : j ≤ k) : j ^ 2 * 2 ^ (k - j) ≤ 2 * 2 ^ k := by
  calc j ^ 2 * 2 ^ (k - j) ≤ 2 ^ (j + 1) * 2 ^ (k - j) :=
        Nat.mul_le_mul_right _ (sq_le_two_pow_succ j)
    _ = 2 * 2 ^ k := by
        rw [← pow_add, show j + 1 + (k - j) = k + 1 by omega, pow_succ]
        ring

/-- As in (5.17) and (5.18) of the differentiability preprint, with `c j ^ 2 w ≥ 1` and a coarse
scale `l ≥ 8 c j ^ 2 w`,
`m' = ⌈c j ^ 2 w⌉` satisfies `m' ≤ 2 c j ^ 2 w ≤ l / 4`, and `l' = l - 2 m'` satisfies
`l / 2 ≤ l' < l`; also `8 ≤ l` and `1 ≤ l'`. -/
theorem grid_coarse_trim_bounds {c w l : ℝ} {j : ℕ} (h1 : 1 ≤ c * (j : ℝ) ^ 2 * w)
    (hl : 8 * (c * (j : ℝ) ^ 2 * w) ≤ l) :
    (⌈c * (j : ℝ) ^ 2 * w⌉₊ : ℝ) ≤ 2 * (c * (j : ℝ) ^ 2 * w) ∧
      2 * (c * (j : ℝ) ^ 2 * w) ≤ l / 4 ∧
      l / 2 ≤ l - 2 * (⌈c * (j : ℝ) ^ 2 * w⌉₊ : ℝ) ∧
      l - 2 * (⌈c * (j : ℝ) ^ 2 * w⌉₊ : ℝ) < l ∧
      8 ≤ l ∧ 1 ≤ l - 2 * (⌈c * (j : ℝ) ^ 2 * w⌉₊ : ℝ) := by
  set u : ℝ := c * (j : ℝ) ^ 2 * w with hu
  have hu0 : 0 ≤ u := by linarith
  have hc1 : (⌈u⌉₊ : ℝ) < u + 1 := Nat.ceil_lt_add_one hu0
  have hc2 : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- As in (5.25) of the differentiability preprint: for `w ≥ 2`, `2 (w + 1) j ^ 2 (16 w + 2) ≤ 60 j
^ 2 w ^ 2`. -/
theorem grid_staircase_count_le (j : ℕ) {w : ℕ} (hw : 2 ≤ w) :
    2 * (w + 1) * j ^ 2 * (16 * w + 2) ≤ 60 * j ^ 2 * w ^ 2 := by
  have h : 2 * (w + 1) * (16 * w + 2) ≤ 60 * w ^ 2 := by nlinarith
  calc 2 * (w + 1) * j ^ 2 * (16 * w + 2) = j ^ 2 * (2 * (w + 1) * (16 * w + 2)) := by ring
    _ ≤ j ^ 2 * (60 * w ^ 2) := Nat.mul_le_mul_left _ h
    _ = 60 * j ^ 2 * w ^ 2 := by ring

end LPPDifferentiability
