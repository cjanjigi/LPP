/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.ExponentialShapeFormula
import all LPP_Foundations.Analysis.ExponentialShapeFormula
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# The variational lower bound for the exponential shape (pure real analysis)

This is the deterministic last step of the lower bound for the exponential
shape. If `g` lies below `γ(x, y) = (√x + √y)²`,
is continuous at `(x, y)`, and the exit-grid bound reaches `γ(x, y)` for every
grid size `K`, then `γ(x, y) ≤ g(x, y)`.

The proof is a direct computation. One identity
(`exit_identity`) shows that a grid term with exit point far from `x` falls
short of `γ(x, y)` by a fixed amount; terms with exit point close to `x` are
controlled by continuity of `g`. Nothing here is probabilistic.
-/

public section

open scoped NNReal

namespace LPPDifferentiability

/-- Key identity (with `p = √x`, `q = √y`, `s = √(x - t)`):
`t / (1 - ρ) + γ(x - t, y) = γ(x, y) - √(y/x) (√x - √(x - t))²`, written for
real numbers with `t = p² - s²`. The mirror identity is the same statement with
`p` and `q` exchanged. -/
private theorem exit_identity (p q s : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (p ^ 2 - s ^ 2) / (p / (p + q)) + (s + q) ^ 2 = (p + q) ^ 2 - q / p * (p - s) ^ 2 := by
  have hne : p + q ≠ 0 := by positivity
  field_simp
  ring

/-- One coordinate of the exit grid. Let `m = p²` be the base point, and `h` the
section of `g` through the other coordinate, with `h u ≤ (√u + q)²`, and `h`
continuous from the left at `m`. For every `ε > 0` there is a grid size
threshold after which any grid term that reaches `(p + q)²` forces
`(p + q)² ≤ h m + ε`. -/
private theorem exit_term_bound (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (m : ℝ≥0)
    (hm : (m : ℝ) = p ^ 2) (h : ℝ≥0 → ℝ)
    (hle : ∀ u : ℝ≥0, h u ≤ (Real.sqrt (u : ℝ) + q) ^ 2)
    (hcont : ∀ ε > 0, ∃ δ > 0, ∀ u : ℝ≥0, u ≤ m → (m : ℝ) - u < δ → h u < h m + ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ r : ℕ, r < K →
      (p + q) ^ 2 ≤ ((r : ℝ) + 1) / K * m / (p / (p + q)) +
          h (m * ((K - r : ℕ) : ℝ≥0) / K) →
        (p + q) ^ 2 ≤ h m + ε := by
  obtain ⟨δ, hδ, hδ'⟩ := hcont (ε / 2) (by positivity)
  set c : ℝ := (p + q) / p with hc
  have hcpos : 0 < c := by positivity
  set η : ℝ := min δ (ε / (4 * c)) with hη
  have hηpos : 0 < η := lt_min hδ (by positivity)
  set θ : ℝ := q * η ^ 2 / (4 * p ^ 3) with hθ
  have hθpos : 0 < θ := by positivity
  refine ⟨⌈max (4 * p ^ 2 * c / ε) (2 * p ^ 2 * c / θ)⌉₊, fun K hK r hr hterm => ?_⟩
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hKbig : max (4 * p ^ 2 * c / ε) (2 * p ^ 2 * c / θ) ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hK)
  have hK1 : 4 * p ^ 2 * c / ε ≤ K := (le_max_left _ _).trans hKbig
  have hK2 : 2 * p ^ 2 * c / θ ≤ K := (le_max_right _ _).trans hKbig
  have hK1' : p ^ 2 * c / K ≤ ε / 4 := by
    rw [div_le_iff₀ hKpos]
    rw [div_le_iff₀ hε] at hK1
    linarith
  have hK2' : p ^ 2 * c / K ≤ θ / 2 := by
    rw [div_le_iff₀ hKpos]
    rw [div_le_iff₀ hθpos] at hK2
    linarith
  set u : ℝ≥0 := m * ((K - r : ℕ) : ℝ≥0) / K with hu
  have hrK : (r : ℝ) ≤ K := by exact_mod_cast hr.le
  have hucoe : (u : ℝ) = p ^ 2 * ((K : ℝ) - r) / K := by
    rw [hu, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_natCast,
      Nat.cast_sub hr.le, hm]
  have hD : (m : ℝ) - u = p ^ 2 * r / K := by
    rw [hucoe, hm]
    field_simp
    ring
  have hDnn : 0 ≤ (m : ℝ) - u := by
    rw [hD]
    positivity
  have hum : u ≤ m := by
    have : (u : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have ht : ((r : ℝ) + 1) / K * m = ((m : ℝ) - u) + p ^ 2 / K := by
    rw [hD, hm]
    field_simp
  have hw : ∀ X : ℝ, X / (p / (p + q)) = X * c := fun X => by
    rw [hc]
    have hne : p + q ≠ 0 := by positivity
    field_simp
  have hcomm : p ^ 2 / K * c = p ^ 2 * c / K := by ring
  rw [ht, hw] at hterm
  by_cases hnear : (m : ℝ) - u < η
  · have h1 : h u < h m + ε / 2 :=
      hδ' u hum (lt_of_lt_of_le hnear (min_le_left _ _))
    have h2 : ((m : ℝ) - u) * c ≤ ε / 4 := by
      have hle2 : (m : ℝ) - u ≤ ε / (4 * c) := hnear.le.trans (min_le_right _ _)
      calc ((m : ℝ) - u) * c ≤ ε / (4 * c) * c := by gcongr
        _ = ε / 4 := by field_simp
    nlinarith
  · exfalso
    rw [not_lt] at hnear
    have hs0 : 0 ≤ Real.sqrt (u : ℝ) := Real.sqrt_nonneg _
    have hs2 : Real.sqrt (u : ℝ) ^ 2 = u := Real.sq_sqrt (NNReal.coe_nonneg u)
    have hDs : p ^ 2 - Real.sqrt (u : ℝ) ^ 2 = (m : ℝ) - u := by rw [hs2, hm]
    have hsp : Real.sqrt (u : ℝ) < p := by nlinarith
    have hid := exit_identity p q (Real.sqrt (u : ℝ)) hp hq
    rw [hw, hDs] at hid
    have hhu := hle u
    have h5 : η ≤ (p - Real.sqrt (u : ℝ)) * (2 * p) := by
      nlinarith [sq_nonneg (p - Real.sqrt (u : ℝ))]
    have h6 : η / (2 * p) ≤ p - Real.sqrt (u : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h7 : (η / (2 * p)) ^ 2 ≤ (p - Real.sqrt (u : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h6 2
    have h8 : θ ≤ q / p * (p - Real.sqrt (u : ℝ)) ^ 2 := by
      have hθeq : q / p * (η / (2 * p)) ^ 2 = θ := by
        rw [hθ]
        field_simp
        ring
      calc θ = q / p * (η / (2 * p)) ^ 2 := hθeq.symm
        _ ≤ q / p * (p - Real.sqrt (u : ℝ)) ^ 2 := by gcongr
    nlinarith

/-- The deterministic last step of the lower bound for the exponential shape. If `g` lies
below the exponential shape `γ`, is continuous at `(x, y)` with `x, y > 0`, and for every
grid size `K ≥ 1` the exit-grid bound at the characteristic parameter reaches `γ(x, y)`,
then `γ(x, y) ≤ g(x, y)`. With the upper bound `g ≤ γ` this gives equality at `(x, y)`. -/
theorem exponentialShape_le_of_exitGridBound (g : Quadrant → ℝ) {x y : ℝ≥0}
    (hx : 0 < x) (hy : 0 < y) (hle : ∀ z : Quadrant, g z ≤ exponentialShape z)
    (hcont : ContinuousAt g (x, y))
    (hgrid : ∀ K : ℕ, 0 < K →
      exponentialShape (x, y) ≤ exitGridBound g (characteristicParameter x y) x y K) :
    exponentialShape (x, y) ≤ g (x, y) := by
  have hx' : (0 : ℝ) < (x : ℝ) := NNReal.coe_pos.mpr hx
  have hy' : (0 : ℝ) < (y : ℝ) := NNReal.coe_pos.mpr hy
  have ha : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hx'
  have hb : 0 < Real.sqrt (y : ℝ) := Real.sqrt_pos.mpr hy'
  have hxa : (x : ℝ) = Real.sqrt (x : ℝ) ^ 2 := (Real.sq_sqrt hx'.le).symm
  have hyb : (y : ℝ) = Real.sqrt (y : ℝ) ^ 2 := (Real.sq_sqrt hy'.le).symm
  have hρ : characteristicParameter x y =
      Real.sqrt (y : ℝ) / (Real.sqrt (x : ℝ) + Real.sqrt (y : ℝ)) := rfl
  have hsum : Real.sqrt (x : ℝ) + Real.sqrt (y : ℝ) ≠ 0 := by positivity
  have h1ρ : 1 - characteristicParameter x y =
      Real.sqrt (x : ℝ) / (Real.sqrt (x : ℝ) + Real.sqrt (y : ℝ)) := by
    rw [hρ]
    field_simp
    ring
  have hγ : exponentialShape (x, y) = (Real.sqrt (x : ℝ) + Real.sqrt (y : ℝ)) ^ 2 := rfl
  -- continuity of g at (x, y), read along each coordinate from the left
  have hc1 : ∀ ε > 0, ∃ δ > 0, ∀ u : ℝ≥0, u ≤ x → (x : ℝ) - u < δ →
      g (u, y) < g (x, y) + ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hcont ε hε
    refine ⟨δ, hδ, fun u hu hlt => ?_⟩
    have hux : (u : ℝ) ≤ x := by exact_mod_cast hu
    have hd : dist (u, y) (x, y) < δ := by
      refine (Prod.dist_eq).trans_lt (max_lt ?_ ?_)
      · show dist u x < δ
        rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hux)]
        exact hlt
      · simpa using hδ
    have := (abs_lt.1 (by simpa [Real.dist_eq] using hδ' hd)).2
    linarith
  have hc2 : ∀ ε > 0, ∃ δ > 0, ∀ v : ℝ≥0, v ≤ y → (y : ℝ) - v < δ →
      g (x, v) < g (x, y) + ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hcont ε hε
    refine ⟨δ, hδ, fun v hv hlt => ?_⟩
    have hvy : (v : ℝ) ≤ y := by exact_mod_cast hv
    have hd : dist (x, v) (x, y) < δ := by
      refine (Prod.dist_eq).trans_lt (max_lt ?_ ?_)
      · simpa using hδ
      · show dist v y < δ
        rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hvy)]
        exact hlt
    have := (abs_lt.1 (by simpa [Real.dist_eq] using hδ' hd)).2
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨K₁, hK₁⟩ := exit_term_bound (Real.sqrt (x : ℝ)) (Real.sqrt (y : ℝ)) ha hb x hxa
    (fun u => g (u, y)) (fun u => hle (u, y)) hc1 hε
  obtain ⟨K₂, hK₂⟩ := exit_term_bound (Real.sqrt (y : ℝ)) (Real.sqrt (x : ℝ)) hb ha y hyb
    (fun v => g (x, v))
    (fun v => (hle (x, v)).trans (le_of_eq (by
      show (Real.sqrt (x : ℝ) + Real.sqrt (v : ℝ)) ^ 2 =
        (Real.sqrt (v : ℝ) + Real.sqrt (x : ℝ)) ^ 2
      ring)))
    hc2 hε
  set K : ℕ := max (max K₁ K₂) 1 with hK
  have hKpos : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKK₁ : K₁ ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hKK₂ : K₂ ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have : Nonempty (Fin K) := ⟨⟨0, hKpos⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun r : Fin K => max
    ((((r : ℕ) : ℝ) + 1) / K * x / (1 - characteristicParameter x y) +
      g (x * ((K - (r : ℕ) : ℕ) : ℝ≥0) / K, y))
    ((((r : ℕ) : ℝ) + 1) / K * y / characteristicParameter x y +
      g (x, y * ((K - (r : ℕ) : ℕ) : ℝ≥0) / K)))
  have hmax := (hgrid K hKpos).trans (le_of_eq hi.symm)
  rcases le_max_iff.1 hmax with hA | hB
  · rw [h1ρ, hγ] at hA
    have := hK₁ K hKK₁ (i : ℕ) i.2 hA
    rw [hγ]
    exact this
  · rw [hρ, hγ, add_comm (Real.sqrt (x : ℝ)) (Real.sqrt (y : ℝ))] at hB
    have := hK₂ K hKK₂ (i : ℕ) i.2 hB
    have hsq : (Real.sqrt (x : ℝ) + Real.sqrt (y : ℝ)) ^ 2 =
        (Real.sqrt (y : ℝ) + Real.sqrt (x : ℝ)) ^ 2 := by ring
    rw [hγ]
    linarith

end LPPDifferentiability
