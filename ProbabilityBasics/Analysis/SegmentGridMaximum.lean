/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! Continuous sampled maxima on closed coordinate segments. -/

public section

open Filter Set Topology
open scoped NNReal

namespace ProbabilityBasics

/-- A continuous profile sampled on the positive integer boundary converges to
its maximum on the entire closed limiting segment. This supplies the elementary
compact-grid step in GRS (1510.00859v2), Lemma 6.4, and JR (1810.03580v3),
Theorem 4.16, including directions on either coordinate axis. -/
theorem tendsto_segment_grid_maximum
    (g : (ℝ≥0 × ℝ≥0) → ℝ) (hg : Continuous g) (α : ℝ)
    (ξ : ℝ≥0 × ℝ≥0)
    (hξunit : (ξ.1 : ℝ) + (ξ.2 : ℝ) = 1)
    (d : ℕ → ℕ × ℕ)
    (hpositive : ∀ n : ℕ, 0 < (d n).1 ∧ 0 < (d n).2)
    (hsize : Tendsto (fun n => (d n).1 + (d n).2) atTop atTop)
    (hratio : Tendsto (fun n =>
      ((d n).1 : ℝ) / (((d n).1 + (d n).2 : ℕ) : ℝ))
      atTop (𝓝 (ξ.1 : ℝ))) :
    Tendsto (fun n =>
      (Finset.Icc 1 (d n).1).sup'
        (Finset.nonempty_Icc.mpr ((hpositive n).1))
        (fun ℓ =>
          g (Real.toNNReal ((((d n).1 - ℓ : ℕ) : ℝ) /
                (((d n).1 + (d n).2 : ℕ) : ℝ)),
             Real.toNNReal ((((d n).2 - 1 : ℕ) : ℝ) /
                (((d n).1 + (d n).2 : ℕ) : ℝ))) +
            α * (ℓ : ℝ) / (((d n).1 + (d n).2 : ℕ) : ℝ)))
      atTop (𝓝 (sSup ((fun τ : ℝ =>
        g (Real.toNNReal ((ξ.1 : ℝ) - τ), ξ.2) + α * τ) ''
          Set.Icc 0 (ξ.1 : ℝ)))) := by
  classical
  let m : ℕ → ℝ := fun n => ((d n).1 + (d n).2 : ℕ)
  let a : ℕ → ℝ := fun n => (d n).1 / m n
  let b : ℕ → ℝ := fun n => ((d n).2 - 1 : ℕ) / m n
  let F : (ℝ × ℝ) → ℝ → ℝ := fun p t =>
    g (Real.toNNReal (p.1 - min p.1 t), Real.toNNReal p.2) + α * min p.1 t
  let S : ℝ × ℝ → ℝ := fun p => sSup (F p '' Icc 0 1)
  let v : ℕ → ℕ → ℝ := fun n ℓ =>
    g (Real.toNNReal (((d n).1 - ℓ : ℕ) / m n), Real.toNNReal (b n)) +
      α * ℓ / m n
  let M : ℕ → ℝ := fun n => (Finset.Icc 1 (d n).1).sup'
    (Finset.nonempty_Icc.mpr (hpositive n).1) (v n)
  have ha : Tendsto a atTop (𝓝 (ξ.1 : ℝ)) := hratio
  have hm (n : ℕ) : 0 < m n := by
    have hp := (hpositive n).1
    dsimp [m]
    exact_mod_cast (show 0 < (d n).1 + (d n).2 by omega)
  have ha1 (n : ℕ) : a n ≤ 1 := by
    apply (div_le_one (hm n)).2
    dsimp [m]
    push_cast
    have hn2 : (0 : ℝ) ≤ (d n).2 := Nat.cast_nonneg _
    linarith only [hn2]
  have hmTop : Tendsto m atTop atTop := tendsto_natCast_atTop_atTop.comp hsize
  have hinv : Tendsto (fun n => 1 / m n) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hmTop
  have hbEq (n : ℕ) : b n = 1 - a n - 1 / m n := by
    dsimp [b, a]
    rw [Nat.cast_sub (by have := (hpositive n).2; omega), Nat.cast_one]
    have hsum : ((d n).1 : ℝ) + (d n).2 = m n := by simp only [m, Nat.cast_add]
    field_simp [(hm n).ne']
    linarith only [hsum]
  have hb : Tendsto b atTop (𝓝 (ξ.2 : ℝ)) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub ha).sub hinv
    have hlim : 1 - (ξ.1 : ℝ) - 0 = (ξ.2 : ℝ) := by linarith only [hξunit]
    simpa only [← hbEq, hlim] using h
  -- A single compact parameter interval controls all moving segments.
  have hF : Continuous (Function.uncurry F) := by
    dsimp [F, Function.uncurry]
    fun_prop
  have hS : Continuous S := isCompact_Icc.continuous_sSup hF
  have hUpper : Tendsto (fun n => S (a n, b n)) atTop
      (𝓝 (S ((ξ.1 : ℝ), (ξ.2 : ℝ)))) :=
    (hS.tendsto _).comp (ha.prodMk_nhds hb)
  have hImage : F ((ξ.1 : ℝ), (ξ.2 : ℝ)) '' Icc 0 1 =
      (fun τ : ℝ => g (Real.toNNReal ((ξ.1 : ℝ) - τ), ξ.2) + α * τ) ''
        Icc 0 (ξ.1 : ℝ) := by
    have hξ1 : (ξ.1 : ℝ) ≤ 1 := by linarith only [hξunit, ξ.2.coe_nonneg]
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨min (ξ.1 : ℝ) t, ⟨le_min ξ.1.coe_nonneg ht.1, min_le_left _ _⟩, ?_⟩
      simp only [F, Real.toNNReal_coe]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t, ⟨ht.1, ht.2.trans hξ1⟩, ?_⟩
      simp only [F, min_eq_right ht.2, Real.toNNReal_coe]
  have hValue (n ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 (d n).1) :
      v n ℓ = F (a n, b n) ((ℓ : ℝ) / m n) := by
    have hle := (Finset.mem_Icc.mp hℓ).2
    have hscaled : (ℓ : ℝ) / m n ≤ a n :=
      (div_le_div_iff_of_pos_right (hm n)).2 (Nat.cast_le.mpr hle)
    dsimp [v, F]
    rw [min_eq_right hscaled, Nat.cast_sub hle]
    dsimp [a]
    rw [sub_div]
    ring
  have hBound (n : ℕ) : M n ≤ S (a n, b n) := by
    apply Finset.sup'_le
    intro ℓ hℓ
    rw [hValue n ℓ hℓ]
    apply le_csSup (isCompact_Icc.bddAbove_image
      ((hF.comp (continuous_const.prodMk continuous_id)).continuousOn))
    apply mem_image_of_mem
    exact ⟨div_nonneg (Nat.cast_nonneg _) (hm n).le,
      ((div_le_div_iff_of_pos_right (hm n)).2
        (Nat.cast_le.mpr (Finset.mem_Icc.mp hℓ).2)).trans (ha1 n)⟩
  obtain ⟨t, ht, htMax⟩ := isCompact_Icc.exists_sSup_image_eq
    (f := F ((ξ.1 : ℝ), (ξ.2 : ℝ)))
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by constructor <;> norm_num⟩)
    ((hF.comp (continuous_const.prodMk continuous_id)).continuousOn :
      ContinuousOn (F ((ξ.1 : ℝ), (ξ.2 : ℝ))) (Icc 0 1))
  -- Clamp a rounded maximizing point into the positive finite grid.
  let k : ℕ → ℕ := fun n => min (d n).1 (max 1 ⌊m n * t⌋₊)
  have hk (n : ℕ) : k n ∈ Finset.Icc 1 (d n).1 := by
    have hp := (hpositive n).1
    simp only [k, Finset.mem_Icc]
    omega
  have hFloor : Tendsto (fun n => (⌊m n * t⌋₊ : ℝ) / m n) atTop (𝓝 t) := by
    have hlo (n : ℕ) : t - 1 / m n ≤ (⌊m n * t⌋₊ : ℝ) / m n := by
      have hf := (Nat.lt_floor_add_one (m n * t)).le
      apply (le_div_iff₀ (hm n)).2
      have heq : (t - 1 / m n) * m n = m n * t - 1 := by
        field_simp [(hm n).ne']
      rw [heq]
      linarith only [hf]
    have hhi (n : ℕ) : (⌊m n * t⌋₊ : ℝ) / m n ≤ t := by
      apply (div_le_iff₀ (hm n)).2
      simpa only [mul_comm] using Nat.floor_le (mul_nonneg (hm n).le ht.1)
    have hleft : Tendsto (fun n => t - 1 / m n) atTop (𝓝 t) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := t)).sub hinv
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hleft tendsto_const_nhds hlo hhi
  have hkEq (n : ℕ) : (k n : ℝ) / m n =
      min (a n) (max (1 / m n) ((⌊m n * t⌋₊ : ℝ) / m n)) := by
    dsimp [k, a]
    rw [Nat.cast_min, Nat.cast_max, Nat.cast_one,
      max_div_div_right (hm n).le, min_div_div_right (hm n).le]
  have hkLim : Tendsto (fun n => (k n : ℝ) / m n) atTop
      (𝓝 (min (ξ.1 : ℝ) t)) := by
    have h := ha.min (hinv.max hFloor)
    simpa only [max_eq_right ht.1, ← hkEq] using h
  have hSample : Tendsto (fun n => v n (k n)) atTop
      (𝓝 (S ((ξ.1 : ℝ), (ξ.2 : ℝ)))) := by
    have hfirst : Tendsto (fun n => (((d n).1 - k n : ℕ) : ℝ) / m n)
        atTop (𝓝 ((ξ.1 : ℝ) - min (ξ.1 : ℝ) t)) := by
      have heq (n : ℕ) : (((d n).1 - k n : ℕ) : ℝ) / m n = a n - (k n : ℝ) / m n := by
        rw [Nat.cast_sub (Finset.mem_Icc.mp (hk n)).2, sub_div]
      simpa only [← heq] using ha.sub hkLim
    have hG := hg.tendsto _ |>.comp
      ((tendsto_real_toNNReal hfirst).prodMk_nhds (tendsto_real_toNNReal hb))
    have h := hG.add ((tendsto_const_nhds (x := α)).mul hkLim)
    have heq : S ((ξ.1 : ℝ), (ξ.2 : ℝ)) =
        g (Real.toNNReal ((ξ.1 : ℝ) - min (ξ.1 : ℝ) t), ξ.2) +
          α * min (ξ.1 : ℝ) t := by
      simpa only [S, F, Real.toNNReal_coe] using htMax
    simpa only [v, mul_div_assoc, Real.toNNReal_coe, heq, Function.comp_def] using h
  have hResult : Tendsto M atTop (𝓝 (S ((ξ.1 : ℝ), (ξ.2 : ℝ)))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hSample hUpper
      (fun n => Finset.le_sup' (v n) (hk n)) hBound
  simpa only [M, v, b, m, S, hImage] using hResult

end ProbabilityBasics
