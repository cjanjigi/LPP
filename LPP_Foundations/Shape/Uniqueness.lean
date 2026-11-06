/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Probability.EnvironmentLaw
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.DenseEmbedding
import Mathlib.Tactic

/-!
# Uniqueness of continuous homogeneous shape functions

Two continuous homogeneous functions that both approximate the last-passage times uniformly,
almost surely, are equal. These comparisons do not construct a shape function. They use the
uniform passage approximation of the shape theorem, without needing concavity or tail
assumptions.
-/

public section

open scoped NNReal
open MeasureTheory

namespace LPPDifferentiability

/-- Nonnegative homogeneity forces the value at the origin to vanish. -/
theorem homogeneous_quadrant_zero (g : Quadrant → ℝ)
    (hg : ∀ (c : ℝ≥0) (x : Quadrant),
      g (c * x.1, c * x.2) = (c : ℝ) * g x) : g (0, 0) = 0 := by
  simpa only [zero_mul, NNReal.coe_zero] using hg 0 (0, 0)

/-- Two functions with the uniform approximation on one common
 environment agree. The probability version below supplies such an environment. -/
theorem shapeCandidates_eq_of_common_environment
    (g h : Quadrant → ℝ) (hgc : Continuous g) (hhc : Continuous h)
    (hgh : ∀ (c : ℝ≥0) (x : Quadrant),
      g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hhh : ∀ (c : ℝ≥0) (x : Quadrant),
      h (c * x.1, c * x.2) = (c : ℝ) * h x)
    (ω : Environment)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
      N ≤ z.1 + z.2 →
      |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
        ε * ((z.1 + z.2 : ℕ) : ℝ))
    (hh : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
      N ≤ z.1 + z.2 →
      |lastPassage ω (0, 0) z - h ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
        ε * ((z.1 + z.2 : ℕ) : ℝ)) : g = h := by
  have hnat : ∀ i j : ℕ, g ((i : ℝ≥0), (j : ℝ≥0)) =
      h ((i : ℝ≥0), (j : ℝ≥0)) := by
    intro i j
    by_cases hs : i + j = 0
    · have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      subst i j
      simpa only [Nat.cast_zero] using (homogeneous_quadrant_zero g hgh).trans
        (homogeneous_quadrant_zero h hhh).symm
    have hsNat : 0 < i + j := Nat.pos_of_ne_zero hs
    have hsReal : 0 < (i + j : ℝ) := by exact_mod_cast hsNat
    by_contra hne
    let d := |g ((i : ℝ≥0), (j : ℝ≥0)) - h ((i : ℝ≥0), (j : ℝ≥0))|
    have hd : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hne)
    let ε := d / (4 * (i + j : ℝ))
    have hε : 0 < ε := div_pos hd (by positivity)
    obtain ⟨N, hN⟩ := hg ε hε
    obtain ⟨M, hM⟩ := hh ε hε
    let k := max N M + 1
    have hkNat : 0 < k := by dsimp [k]; omega
    have hk : 0 < (k : ℝ) := by exact_mod_cast hkNat
    have hNk : N ≤ k := by dsimp [k]; omega
    have hMk : M ≤ k := by dsimp [k]; omega
    have hlen : k ≤ k * i + k * j := by
      rw [← Nat.mul_add]
      exact Nat.le_mul_of_pos_right k hsNat
    have hNg := hN (k * i, k * j) (hNk.trans hlen)
    have hMh := hM (k * i, k * j) (hMk.trans hlen)
    have htriangle :
        |g (((k * i : ℕ) : ℝ≥0), ((k * j : ℕ) : ℝ≥0)) -
          h (((k * i : ℕ) : ℝ≥0), ((k * j : ℕ) : ℝ≥0))| ≤
        2 * ε * ((k * i + k * j : ℕ) : ℝ) := by
      calc
        _ ≤ |lastPassage ω (0, 0) (k * i, k * j) -
              g (((k * i : ℕ) : ℝ≥0), ((k * j : ℕ) : ℝ≥0))| +
            |lastPassage ω (0, 0) (k * i, k * j) -
              h (((k * i : ℕ) : ℝ≥0), ((k * j : ℕ) : ℝ≥0))| := by
          simpa only [abs_sub_comm] using abs_sub_le
            (g (((k * i : ℕ) : ℝ≥0), ((k * j : ℕ) : ℝ≥0)))
            (lastPassage ω (0, 0) (k * i, k * j))
            (h (((k * i : ℕ) : ℝ≥0), ((k * j : ℕ) : ℝ≥0)))
        _ ≤ _ := by linarith only [hNg, hMh]
    have hscaleg := hgh (k : ℝ≥0) ((i : ℝ≥0), (j : ℝ≥0))
    have hscaleh := hhh (k : ℝ≥0) ((i : ℝ≥0), (j : ℝ≥0))
    simp only [← Nat.cast_mul, NNReal.coe_natCast] at hscaleg hscaleh
    rw [hscaleg, hscaleh, ← mul_sub, abs_mul, abs_of_pos hk] at htriangle
    change (k : ℝ) * d ≤ _ at htriangle
    have hcast : ((k * i + k * j : ℕ) : ℝ) = (k : ℝ) * (i + j) := by
      push_cast
      ring
    rw [hcast] at htriangle
    have hbound : 2 * ε * ((k : ℝ) * (i + j)) = (k : ℝ) * d / 2 := by
      dsimp [ε]
      (field_simp [ne_of_gt hsReal]; ring)
    rw [hbound] at htriangle
    have hkd : 0 < (k : ℝ) * d := mul_pos hk hd
    linarith only [htriangle, hkd]
  have hrat : ∀ p q : ℚ≥0, g ((p : ℝ≥0), (q : ℝ≥0)) =
      h ((p : ℝ≥0), (q : ℝ≥0)) := by
    intro p q
    let c : ℝ≥0 := p.den * q.den
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr p.den_ne_zero)
        (Nat.cast_ne_zero.mpr q.den_ne_zero)
    have hp : c * (p : ℝ≥0) = ((p.num * q.den : ℕ) : ℝ≥0) := by
      have hp' : (p.den : ℝ≥0) * (p : ℝ≥0) = p.num := by
        exact_mod_cast p.den_mul_eq_num
      dsimp [c]
      push_cast
      calc
        _ = ((p.den : ℝ≥0) * (p : ℝ≥0)) * q.den := by ring
        _ = _ := by rw [hp']
    have hq : c * (q : ℝ≥0) = ((p.den * q.num : ℕ) : ℝ≥0) := by
      have hq' : (q.den : ℝ≥0) * (q : ℝ≥0) = q.num := by
        exact_mod_cast q.den_mul_eq_num
      dsimp [c]
      push_cast
      rw [mul_assoc, hq']
    have hg' := hgh c ((p : ℝ≥0), (q : ℝ≥0))
    have hh' := hhh c ((p : ℝ≥0), (q : ℝ≥0))
    simp only [hp, hq] at hg' hh'
    have heq := hnat (p.num * q.den) (p.den * q.num)
    rw [hg', hh'] at heq
    exact mul_left_cancel₀ (NNReal.coe_ne_zero.mpr hc) heq
  have hdense : DenseRange ((↑) : ℚ≥0 → ℝ≥0) := by
    apply dense_of_exists_between
    intro a b hab
    obtain ⟨q, hq, haq, hqb⟩ := (NNReal.lt_iff_exists_rat_btwn a b).mp hab
    let r : ℚ≥0 := ⟨q, hq⟩
    have hcast : (r : ℝ≥0) = Real.toNNReal (q : ℝ) := by
      apply NNReal.eq
      change (r : ℝ) = _
      rw [Real.coe_toNNReal _ (Rat.cast_nonneg.mpr hq), ← Rat.cast_nnratCast]
      rfl
    refine ⟨(r : ℝ≥0), ⟨r, rfl⟩, ?_, ?_⟩
    · rwa [hcast]
    · rwa [hcast]
  apply (hdense.prodMap hdense).equalizer hgc hhc
  funext p
  exact hrat p.1 p.2

/-- Probability-one uniform approximation determines a continuous homogeneous
function uniquely. The two events are intersected before choosing an environment. -/
theorem shapeCandidates_eq
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g h : Quadrant → ℝ) (hgc : Continuous g) (hhc : Continuous h)
    (hgh : ∀ (c : ℝ≥0) (x : Quadrant),
      g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hhh : ∀ (c : ℝ≥0) (x : Quadrant),
      h (c * x.1, c * x.2) = (c : ℝ) * h x)
    (hg : ∀ᵐ ω ∂environmentLaw μ,
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
        N ≤ z.1 + z.2 →
        |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
          ε * ((z.1 + z.2 : ℕ) : ℝ))
    (hh : ∀ᵐ ω ∂environmentLaw μ,
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
        N ≤ z.1 + z.2 →
        |lastPassage ω (0, 0) z - h ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
          ε * ((z.1 + z.2 : ℕ) : ℝ)) : g = h := by
  obtain ⟨ω, hgω, hhω⟩ := (hg.and hh).exists
  exact shapeCandidates_eq_of_common_environment g h hgc hhc hgh hhh ω hgω hhω

end LPPDifferentiability
