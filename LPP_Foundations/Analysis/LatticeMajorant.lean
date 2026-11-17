/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Quadrant
import Martin2004.Analysis.RationalPassageNormalization
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

/-!
# A deterministic lattice majorant

Uniform lattice comparisons with a homogeneous continuous function imply a
linear majorant on the whole quadrant. This helper is conditional: it does not
produce the lattice estimates in its hypotheses. The floor argument is the
deterministic approximation step behind Janjigian and Rassoul-Agha,
*Busemann functions and Gibbs measures in directed polymer models on* `ℤ²`,
arXiv:1810.03580v3, Theorem 4.4.
-/

@[expose] public section

open Filter
open scoped NNReal Topology
open LPPDifferentiability

namespace LPP

/-- Conditional deterministic bridge: the displayed uniform lattice bounds give
a linear majorant for a continuous homogeneous function on the closed quadrant.
This is the floor approximation step in JR1810.03580v3, Theorem 4.4 and Lemma 4.5;
the theorem does not produce its lattice hypotheses. -/
theorem quadrant_majorant_of_uniform_lattice_bounds
    (g : Quadrant → ℝ) (hcont : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (G C : ℕ × ℕ → ℝ) (u0 u1 : ℝ)
    (hdom : ∀ d, G d ≤ C d)
    (hshape : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ d : ℕ × ℕ,
      N ≤ d.1 + d.2 →
      |G d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
        ε * ((d.1 + d.2 : ℕ) : ℝ))
    (hcenter : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ d : ℕ × ℕ,
      N ≤ d.1 + d.2 →
      |C d - (u0 * (d.1 : ℝ) + u1 * (d.2 : ℝ))| ≤
        ε * ((d.1 + d.2 : ℕ) : ℝ)) :
    ∀ z : Quadrant, g z ≤ u0 * (z.1 : ℝ) + u1 * (z.2 : ℝ) := by
  intro z
  by_cases hz : z = 0
  · have hg0 : g (0 : Quadrant) = 0 := by
      simpa using hhom (0 : ℝ≥0) (0 : Quadrant)
    subst z
    simp [hg0]
  · let d : ℕ → ℕ × ℕ := fun n =>
      (⌊(n : ℝ) * (z.1 : ℝ)⌋₊, ⌊(n : ℝ) * (z.2 : ℝ)⌋₊)
    let m : ℕ → ℕ := fun n => (d n).1 + (d n).2
    let r : ℕ → Quadrant := fun n => ((d n).1, (d n).2)
    let c : ℕ → ℝ≥0 := fun n => 1 / (n : ℝ≥0)
    let q : ℕ → Quadrant := fun n => c n • r n
    let A : ℕ → ℝ := fun n => ((d n).1 : ℝ) / (n : ℝ)
    let B : ℕ → ℝ := fun n => ((d n).2 : ℝ) / (n : ℝ)
    let L : ℕ → ℝ := fun n => (m n : ℝ) / (n : ℝ)
    let S : ℝ := (z.1 : ℝ) + (z.2 : ℝ)
    let T : ℝ := u0 * (z.1 : ℝ) + u1 * (z.2 : ℝ)
    have hcoords : z.1 ≠ 0 ∨ z.2 ≠ 0 := by
      by_contra h
      have hz₁ : z.1 = 0 := by
        by_contra hn
        exact h (Or.inl hn)
      have hz₂ : z.2 = 0 := by
        by_contra hn
        exact h (Or.inr hn)
      exact hz (Prod.ext hz₁ hz₂)
    have hS : 0 < S := by
      rcases hcoords with h₁ | h₂
      · have hp : 0 < z.1 := lt_of_le_of_ne zero_le (Ne.symm h₁)
        have hpR : (0 : ℝ) < (z.1 : ℝ) := by exact_mod_cast hp
        have hnR : 0 ≤ (z.2 : ℝ) := by positivity
        dsimp [S]
        linarith
      · have hp : 0 < z.2 := lt_of_le_of_ne zero_le (Ne.symm h₂)
        have hpR : (0 : ℝ) < (z.2 : ℝ) := by exact_mod_cast hp
        have hnR : 0 ≤ (z.1 : ℝ) := by positivity
        dsimp [S]
        linarith
    have hA : Tendsto A atTop (𝓝 (z.1 : ℝ)) := by
      simpa [A, d] using
        (LPPDifferentiability.tendsto_nat_floor_mul_div_nat
          (z.1 : ℝ) (show 0 ≤ (z.1 : ℝ) by positivity))
    have hB : Tendsto B atTop (𝓝 (z.2 : ℝ)) := by
      simpa [B, d] using
        (LPPDifferentiability.tendsto_nat_floor_mul_div_nat
          (z.2 : ℝ) (show 0 ≤ (z.2 : ℝ) by positivity))
    have hL : Tendsto L atTop (𝓝 S) := by
      simpa [L, S, m, d] using
        (LPPDifferentiability.tendsto_floor_pair_length
          (z.1 : ℝ) (z.2 : ℝ) (by positivity) (by positivity))
    have hq₁real : Tendsto (fun n => ((q n).1 : ℝ)) atTop (𝓝 (z.1 : ℝ)) := by
      have heq (n : ℕ) : ((q n).1 : ℝ) = A n := by
        simp [q, c, r, A, d, div_eq_mul_inv, mul_comm]
      simpa only [heq] using hA
    have hq₂real : Tendsto (fun n => ((q n).2 : ℝ)) atTop (𝓝 (z.2 : ℝ)) := by
      have heq (n : ℕ) : ((q n).2 : ℝ) = B n := by
        simp [q, c, r, B, d, div_eq_mul_inv, mul_comm]
      simpa only [heq] using hB
    have hq₁ : Tendsto (fun n => (q n).1) atTop (𝓝 z.1) :=
      NNReal.tendsto_coe.mp hq₁real
    have hq₂ : Tendsto (fun n => (q n).2) atTop (𝓝 z.2) :=
      NNReal.tendsto_coe.mp hq₂real
    have hq : Tendsto q atTop (𝓝 z) := hq₁.prodMk_nhds hq₂
    have hleft : Tendsto (fun n => g (r n) / (n : ℝ)) atTop (𝓝 (g z)) := by
      have hcontq : Tendsto (fun n => g (q n)) atTop (𝓝 (g z)) :=
        (hcont.tendsto z).comp hq
      have hscale (n : ℕ) : g (q n) = g (r n) / (n : ℝ) := by
        have hc : ((c n : ℝ≥0) : ℝ) = 1 / (n : ℝ) := by
          simp [c]
        calc
          g (q n) = g (c n • r n) := rfl
          _ = (c n : ℝ) * g (r n) := hhom (c n) (r n)
          _ = g (r n) / (n : ℝ) := by rw [hc]; simp [div_eq_mul_inv, mul_comm]
      simpa only [hscale] using hcontq
    have hnCast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hprod : Tendsto (fun n : ℕ => (n : ℝ) * L n) atTop atTop :=
      hnCast.atTop_mul_pos hS hL
    have hprodEq (n : ℕ) : (n : ℝ) * L n = (m n : ℝ) := by
      by_cases hn : n = 0
      · subst n
        simp [L, m, d]
      · simp only [L]
        field_simp [Nat.cast_ne_zero.mpr hn]
    have hM : Tendsto (fun n => (m n : ℝ)) atTop atTop := by
      simpa only [hprodEq] using hprod
    have hcut (N : ℕ) : ∀ᶠ n : ℕ in atTop, N ≤ m n := by
      filter_upwards [hM.eventually_ge_atTop (N : ℝ)] with n hn
      exact_mod_cast hn
    have hbound : ∀ ε : ℝ, 0 < ε → g z ≤ T + 2 * ε * S := by
      intro ε hε
      obtain ⟨N₁, hshapeN⟩ := hshape ε hε
      obtain ⟨N₂, hcenterN⟩ := hcenter ε hε
      let N := max N₁ N₂
      have hseqEventually : ∀ᶠ n : ℕ in atTop,
          g (r n) / (n : ℝ) ≤ u0 * A n + u1 * B n + 2 * ε * L n := by
        filter_upwards [hcut N] with n hn
        have hn₁ : N₁ ≤ (d n).1 + (d n).2 := by
          exact Nat.le_trans (Nat.le_max_left _ _) (by simpa [N, m] using hn)
        have hn₂ : N₂ ≤ (d n).1 + (d n).2 := by
          exact Nat.le_trans (Nat.le_max_right _ _) (by simpa [N, m] using hn)
        have hs := hshapeN (d n) hn₁
        have hc := hcenterN (d n) hn₂
        have hs' : |G (d n) - g (r n)| ≤ ε * (m n : ℝ) := by
          simpa [r, m] using hs
        have hc' : |C (d n) -
            (u0 * ((d n).1 : ℝ) + u1 * ((d n).2 : ℝ))| ≤ ε * (m n : ℝ) := by
          simpa [m] using hc
        have hg₁ : g (r n) ≤ G (d n) + ε * (m n : ℝ) := by
          have hlo := (abs_le.mp hs').1
          linarith
        have hg₂ : C (d n) ≤
            u0 * ((d n).1 : ℝ) + u1 * ((d n).2 : ℝ) + ε * (m n : ℝ) := by
          have hhi := (abs_le.mp hc').2
          linarith
        have hraw : g (r n) ≤
            u0 * ((d n).1 : ℝ) + u1 * ((d n).2 : ℝ) + 2 * ε * (m n : ℝ) := by
          have hdomn := hdom (d n)
          linarith
        have hnorm := div_le_div_of_nonneg_right hraw (Nat.cast_nonneg n)
        have hnormEq :
            (u0 * ((d n).1 : ℝ) + u1 * ((d n).2 : ℝ) + 2 * ε * (m n : ℝ)) / (n : ℝ) =
              u0 * A n + u1 * B n + 2 * ε * L n := by
          simp [A, B, L, add_div, mul_div_assoc]
        simpa only [hnormEq] using hnorm
      have hlimA : Tendsto (fun n => u0 * A n) atTop
          (𝓝 (u0 * (z.1 : ℝ))) := by
        simpa using (tendsto_const_nhds.mul hA)
      have hlimB : Tendsto (fun n => u1 * B n) atTop
          (𝓝 (u1 * (z.2 : ℝ))) := by
        simpa using (tendsto_const_nhds.mul hB)
      have hlimL : Tendsto (fun n => 2 * ε * L n) atTop (𝓝 (2 * ε * S)) := by
        simpa using ((tendsto_const_nhds.mul hL))
      have hright : Tendsto (fun n => u0 * A n + u1 * B n + 2 * ε * L n)
          atTop (𝓝 (T + 2 * ε * S)) := by
        simpa [T, add_assoc] using (hlimA.add hlimB).add hlimL
      have hle := le_of_tendsto_of_tendsto hleft hright
        hseqEventually
      simpa [T] using hle
    by_contra hnot
    have hgap : T < g z := lt_of_not_ge hnot
    let ε : ℝ := (g z - T) / (4 * S)
    have hε : 0 < ε := by
      dsimp [ε]
      exact div_pos (sub_pos.mpr hgap) (mul_pos (by norm_num) hS)
    have hεcalc : 2 * ε * S = (g z - T) / 2 := by
      dsimp [ε]
      field_simp [ne_of_gt hS]
      ring
    have hfinal := hbound ε hε
    rw [hεcalc] at hfinal
    linarith

end LPP

end
