/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.GridCoarseGoodProbability
public import Differentiability.Probability.StairGeometryEvent
public import Differentiability.Probability.StaircaseFamilyEvent
public import Differentiability.Probability.HeavyVertexEvents
public import Differentiability.Probability.GridGoodEvent
public import Martin2004.Probability.ShapeAboveMean
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Analysis.QuadrantExtension
import Differentiability.Analysis.GridScaleCounts
import Differentiability.Analysis.GridScaleSums
import Mathlib.Tactic

/-! # The simultaneous grid event `Gγ`, general weights

This file proves items (i) and (ii) of Lemma 5.7 of the differentiability preprint, for
general weights. It also uses the remark after that lemma (Section 5.3 of the preprint)
and items (C3) and (C7) of Appendix B.

`grid_connections_simultaneous_general` is the hypothesis `hgridγ` of
`arbitrary_endpoints_defect_le_general`: the good event `Gγ` (the geometry event `E_geo`, the
heavy-vertex event `E_hv` and the per-vertex connections of item (i) along `γ^u`) has
probability at least `1 - 2 β_J` for record indices `k ≥ k₁`, with `β_J → 0`.

Proof. Off the events `¬E_geo`, `¬E_hv`, and the failure of the staircase event of
Lemma B.6 of the preprint, each of these has probability tending to `0`. The failures of
the coarse good events (probability at most `exp (-(q₀/2) j²)` each, summed over scales,
grid levels and bins to at most `β_J`) are also small. Then `grid_det_general_named` gives
the per-vertex clause. The scalar conditions of that theorem hold for large `k`.
-/

public section

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

/-- **Items (i) and (ii) of Lemma 5.7 of the differentiability preprint, general weights**
(with items (C1) to (C7) of Appendix B): for all `A, R > 0` there is `β → 0` (depending on
`A, R, q₀` only) such that for all `ε₀ > 0` and `J ≥ 1` there is `k₁` with
`P((Gγ A R ε₀ k J)ᶜ) ≤ 2 β J` for record indices `k ≥ k₁`. The conclusion is the hypothesis
`hgridγ` of `arbitrary_endpoints_defect_le_general`. -/
theorem grid_connections_simultaneous_general
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p' : ℝ) (hp' : 1 < p')
    (hmom' : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p') ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0:ℝ), (μ (Ioi t)) ^ (1/2:ℝ)) < ∞)
    (p : ℝ) (hp : 4 < p)
    (hmomp : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (q0 : ℝ) (hq0 : 0 < q0)
    (k0 : ℕ) (hk0 : 0 < k0) (m : ℕ → ℕ) (Kset : Set ℕ)
    (hm3 : ∀ k : ℕ, k0 ≤ k → m k ≤ 3 * k)
    (hKset : ∀ k ∈ Kset, k0 ≤ k)
    (m1 K1 K2 : ℕ) (hm1 : 1 ≤ m1) (hK1 : 1 ≤ K1) (hK2 : 1 ≤ K2)
    (hm1p : 40 < (m1 : ℝ) * p') (hK1p : 4 < ((K1 : ℝ) + 1) * p')
    (hK2p : 24 < (K2 : ℝ) * (p' - 1))
    (htrial :
      let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
      let dl : ℝ := derivWithin H (Iio 0) 0
      let dr : ℝ := derivWithin H (Ioi 0) 0
      let K : ℝ := 100 * (1 + |dl| + |dr|)
      let P : ℕ → ℕ → ℝ := fun k n => (environmentLaw μ).real {ω : Environment |
        ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
          (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤
            8 * (2 : ℝ) ^ k) ∧
            g (toQuadrant (a, 1 - a)) * (n : ℝ) - K * (2 : ℝ) ^ k < pathWeight ω q}
      ∀ k ∈ Kset, 4 * k0 + 3 ≤ k → ∀ j : ℕ, j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
        (∀ l : ℕ, 1 ≤ l → (l : ℝ) < 2 ^ (m k - 4 * j - 1) → q0 < P (k - j) l) ∧
        (1 < (2 : ℝ) ^ (m k - 4 * j - 1) →
          (2 : ℝ) ^ (m k - 4 * j - 1) ≤ ((2 : ℝ) ^ (k - j)) ^ 3 / 2)) :
    let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
    let dl : ℝ := derivWithin H (Iio 0) 0
    let dr : ℝ := derivWithin H (Ioi 0) 0
    let K : ℝ := 100 * (1 + |dl| + |dr|)
    let G0 : ℝ := H 0
    let Cm : ℝ := ∫ x : ℝ, max (-x) 0 ∂μ
    let cstar : ℝ := 50 / min a (1 - a)
    let θ₁ : ℝ := min a (1 - a) / 5
    let reach : Environment → ℝ → Lattice → Set Lattice := fun ω T z =>
      {y | ∃ (d : ℕ × ℕ) (q : Path z d), z + ((d.1 : ℤ), (d.2 : ℤ)) = y ∧
        ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}
    let reachBack : Environment → ℝ → Lattice → Set Lattice := fun ω T z =>
      {y | ∃ (d : ℕ × ℕ) (q : Path y d), y + ((d.1 : ℤ), (d.2 : ℤ)) = z ∧
        ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}
    let Ntr : ℕ := K1 * (2 * m1 ^ 2 + 1) ^ 2
    let W0 : ℕ := Ntr + 1
    let L : ℕ := ⌈4 * ((W0 : ℝ) + 2) / θ₁⌉₊
    let r0 : ℕ := K1 * (2 * L + 1) + Ntr
    let D1 : ℕ := ⌊2 * (W0 : ℝ) / θ₁⌋₊ + 4 * W0 + 2 * r0 + 2 * L + 8
    let d0 : ℕ := D1 + 2 * m1 ^ 2
    let c0 : ℕ := W0 + 2 * L + 1
    let collar : Set Lattice → ℕ → Set Lattice := fun Q c =>
      {z | ∃ y ∈ Q, |z.1 - y.1| + |z.2 - y.2| ≤ (c : ℤ)}
    let Egeo : Environment → ℝ → Set Lattice → Prop := fun ω T Q =>
      (¬ ∃ f : Fin (K1 + 1) → Lattice, Function.Injective f ∧
          (∀ i, f i ∈ collar Q (c0 + m1 ^ 2) ∧ ω (f i) < -T) ∧
          ∀ i : Fin (K1 + 1), 0 < i.val → ∃ j : Fin (K1 + 1), j.val < i.val ∧
            |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ d0) ∧
      ∀ z ∈ collar Q c0,
        ((reach ω T z).Finite → (reach ω T z).ncard < m1 ^ 2) ∧
        ((reachBack ω T z).Finite → (reachBack ω T z).ncard < m1 ^ 2)
    let C₁ : ℝ := 8 * cstar * (G0 + 2 * Cm) + 2 * K + 2 * (r0 : ℝ) + 3 * cstar + 1
    let Gγ : ℝ → ℝ → ℝ → ℕ → ℕ → Set Environment := fun A R ε₀ k J =>
      {ω : Environment |
        let T : ℝ := ε₀ * 2 ^ k / (k : ℝ) / (4 * (K2 : ℝ))
        let Qk : Set Lattice := {z | |((z.1 + z.2 : ℤ) : ℝ)| ≤ (A + 5) * 2 ^ m k ∧
          |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ (R + 2 * C₁ + 10) * 2 ^ k}
        let gf : Lattice → ℕ → Lattice := fun u t =>
          GreedyAttachment.vertex u a {y | (reach ω T y).Finite} t
        let gb : Lattice → ℕ → Lattice := fun u t =>
          -GreedyAttachment.vertex (-u) a {y | ω (-y) < -T ∨ (reachBack ω T (-y)).Finite} t
        Egeo ω T Qk ∧ (∀ z ∈ Qk, ω z ≤ ε₀ * 2 ^ k / (k : ℝ)) ∧
        ∀ u : Lattice, |((u.1 + u.2 : ℤ) : ℝ)| ≤ A * 2 ^ m k →
          |(1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)| ≤ R * 2 ^ k →
          ∀ j : ℕ, J ≤ j → j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
          ∀ I : ℤ, ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * 2 ^ m k →
          ((-T ≤ ω u ∧ ¬ (reachBack ω T u).Finite) →
            (⌊((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (m k - 4 * J - 1) : ℕ) : ℝ)⌋ - 1) *
              ((2 ^ (m k - 4 * J - 1) : ℕ) : ℤ) ≤ I →
            I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ≤ u.1 + u.2 →
            ∀ z₀ z₁ : Lattice, z₀ = gb u (u.1 + u.2 - I).toNat →
              z₁ = gb u (u.1 + u.2 - (I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ))).toNat →
            ∃ (D : ℕ × ℕ) (y : Path z₀ D),
              z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
              G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
                  pathWeight ω y ≤
                C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε₀ * 2 ^ k / (k : ℝ)) ∧
              G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
                  pathWeight ω y ≤
                C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε₀ * 2 ^ k / (k : ℝ)) ∧
              ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) -
                  ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| ≤
                C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ))) ∧
          (¬ (reach ω T u).Finite →
            u.1 + u.2 ≤ I →
            I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ≤
              (⌈((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (m k - 4 * J - 1) : ℕ) : ℝ)⌉ + 1) *
                ((2 ^ (m k - 4 * J - 1) : ℕ) : ℤ) →
            ∀ z₀ z₁ : Lattice, z₀ = gf u (I - (u.1 + u.2)).toNat →
              z₁ = gf u (I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) - (u.1 + u.2)).toNat →
            ∃ (D : ℕ × ℕ) (y : Path z₀ D),
              z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
              G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
                  pathWeight ω y ≤
                C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε₀ * 2 ^ k / (k : ℝ)) ∧
              G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
                  pathWeight ω y ≤
                C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε₀ * 2 ^ k / (k : ℝ)) ∧
              ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) -
                  ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| ≤
                C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)))}
    ∀ A R : ℝ, 0 < A → 0 < R → ∃ β : ℕ → ℝ, Tendsto β atTop (𝓝 0) ∧
      ∀ ε₀ : ℝ, 0 < ε₀ → ∀ J : ℕ, 1 ≤ J → ∃ k1 : ℕ, ∀ k ∈ Kset, k1 ≤ k →
        (environmentLaw μ).real (Gγ A R ε₀ k J)ᶜ ≤ 2 * β J := by
  classical
  intro H dl dr K G0 Cm cstar _ reach reachBack _ W0 L r0 _ _ _ _ Egeo C₁ Gγ A R hA hR
  -- Step 0: constants
  have hθ : 0 < min a (1 - a) := lt_min ha₀ (by linarith)
  have hθ2 : min a (1 - a) ≤ 1 / 2 := by
    have h1 := min_le_left a (1 - a)
    have h2 := min_le_right a (1 - a)
    linarith
  have hcdef : cstar = 50 / min a (1 - a) := rfl
  have hKdef : K = 100 * (1 + |dl| + |dr|) := rfl
  have hC₁def : C₁ = 8 * cstar * (G0 + 2 * Cm) + 2 * K + 2 * (r0 : ℝ) + 3 * cstar + 1 := rfl
  have hc100 : 100 ≤ cstar := by
    rw [hcdef, le_div_iff₀ hθ]
    linarith
  have hneg : ∃ p : ℝ, 1 < p ∧ (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞ :=
    ⟨p', hp', hmom'⟩
  have hG0 : G0 = g (a.toNNReal, (1 - a).toNNReal) := by
    simp only [G0, H, quadrantExtension, toQuadrant, add_zero, sub_zero]
  have hG0q : G0 = g (toQuadrant (a, 1 - a)) := hG0
  have hEG : (∫ x : ℝ, x ∂μ) ≤ G0 := by
    have hab : a.toNNReal + (1 - a).toNNReal = 1 := by
      rw [← Real.toNNReal_add ha₀.le (by linarith)]
      norm_num
    have h := integral_le_shape_of_negative_moment_and_positive_tail μ hneg hpos g hgcont
      hghom hgconc hgshape a.toNNReal (1 - a).toNNReal hab
    rw [hG0]
    exact h
  have hCm0 : 0 ≤ Cm := integral_nonneg fun x => le_max_right _ _
  have hGC : 0 ≤ G0 + 2 * Cm := by linarith [neg_integral_neg_part_le_integral_grid μ]
  have hK1' : 1 ≤ K := by
    rw [hKdef]; linarith [abs_nonneg dl, abs_nonneg dr]
  have hdl : |dl| ≤ K := by
    rw [hKdef]; linarith [abs_nonneg dl, abs_nonneg dr]
  have hdr : |dr| ≤ K := by
    rw [hKdef]; linarith [abs_nonneg dl, abs_nonneg dr]
  have hC1 : 1 ≤ C₁ := by
    have h1 : 0 ≤ 8 * cstar * (G0 + 2 * Cm) := mul_nonneg (by linarith) hGC
    have h3 : (0 : ℝ) ≤ r0 := Nat.cast_nonneg _
    rw [hC₁def]
    linarith
  have hB : 0 < R + 2 * C₁ + 10 := by linarith
  have hCp0 : 0 ≤ ∫ x : ℝ, (max x 0) ^ p ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (le_max_right x 0) p
  -- Step 1: the function `β`
  have hq2 : 0 < q0 / 2 := by positivity
  have hCpos : 0 < (4 * (A + 4) + 1) * (2 * R + 2) := by positivity
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (4 * (A + 4) + 1) * (2 * R + 2) := ⟨_, rfl⟩
  have hCpos' : 0 < C := by rw [hC]; exact hCpos
  obtain ⟨β, hβdef⟩ : ∃ β : ℕ → ℝ, β = fun J : ℕ =>
      C * ∑' i : ℕ, (2 : ℝ) ^ (5 * (i + J)) * Real.exp (-(q0 / 2 * ((i + J : ℕ) : ℝ) ^ 2)) :=
    ⟨_, rfl⟩
  refine ⟨β, by rw [hβdef]; exact grid_beta_tendsto (q0 / 2) C, ?_⟩
  intro ε₀ hε₀ J hJ
  have hβJ : 0 < β J := by rw [hβdef]; exact grid_beta_pos hq2 hCpos' J
  have hβJeq : β J = C * ∑' i : ℕ, (2 : ℝ) ^ (5 * (i + J)) *
      Real.exp (-(q0 / 2 * ((i + J : ℕ) : ℝ) ^ 2)) := by rw [hβdef]
  have hβ3 : 0 < β J / 3 := by linarith
  -- Step 2: the four exceptional events
  let Qs : ℕ → Set Lattice := fun k => {z : Lattice |
    |((z.1 + z.2 : ℤ) : ℝ)| ≤ (A + 5) * 2 ^ m k ∧
      |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ (R + 2 * C₁ + 10) * 2 ^ k}
  let Ts : ℕ → ℝ := fun k => ε₀ * 2 ^ k / (k : ℝ) / (4 * (K2 : ℝ))
  let Estair : Environment → ℕ → Prop := fun ω k =>
    let T : ℝ := Ts k
    let t : ℝ := ε₀ * (2 : ℝ) ^ k / (k : ℝ)
    let Nl : ℝ := 8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k
    let Vb : Set Lattice := {y | (reach ω T y).Finite}
    let Wb : Set Lattice := {y | ω (-y) < -T ∨ (reachBack ω T (-y)).Finite}
    (∀ (u : Lattice) (i n : ℕ), (n : ℝ) ≤ Nl →
      (∀ s, s ≤ i + n → GreedyAttachment.vertex u a Vb s ∈ Qs k) →
      (∀ s, s < n → -T ≤ ω (GreedyAttachment.vertex u a Vb (i + s))) →
      -2 * Cm * (n : ℝ) - t / 2 ≤
        ∑ s ∈ Finset.range n, ω (GreedyAttachment.vertex u a Vb (i + s))) ∧
    (∀ (u : Lattice) (i n : ℕ), (n : ℝ) ≤ Nl →
      (∀ s, s ≤ i + n → -GreedyAttachment.vertex (-u) a Wb s ∈ Qs k) →
      (∀ s, s < n → -T ≤ ω (-GreedyAttachment.vertex (-u) a Wb (i + 1 + s))) →
      -2 * Cm * (n : ℝ) - t / 2 ≤
        ∑ s ∈ Finset.range n, ω (-GreedyAttachment.vertex (-u) a Wb (i + 1 + s))) ∧
    (∀ z v : Lattice, z.1 ≤ v.1 → z.2 ≤ v.2 →
      let n : ℕ := (v.1 - z.1 + (v.2 - z.2)).toNat
      let q : ℝ := ((v.1 - z.1 : ℤ) : ℝ) / (n : ℝ)
      let x : ℕ → Lattice := GreedyAttachment.vertex z q Vb
      let e : ℕ × ℕ := ((v.1 - (x (n - L)).1).toNat, (v.2 - (x (n - L)).2).toNat)
      L ≤ n → (n : ℝ) ≤ Nl → (x (n - L)).1 ≤ v.1 → (x (n - L)).2 ≤ v.2 →
      (∀ s, s ≤ n - L → x s ∈ Qs k) →
      (∀ i : Fin (e.1 + e.2 + 1), (horizontalFirst (x (n - L)) e).vertex i ∈ Qs k) →
      (∀ s, s < n - L → -T ≤ ω (x s)) →
      (∀ i : Fin (e.1 + e.2 + 1), i.val < e.1 + e.2 →
        -T ≤ ω ((horizontalFirst (x (n - L)) e).vertex i)) →
      -2 * Cm * (n : ℝ) - t / 2 ≤
        (∑ s ∈ Finset.range (n - L), ω (x s)) +
          pathWeight ω (horizontalFirst (x (n - L)) e)) ∧
    (∀ (z u : Lattice) (Λ : ℤ) (n : ℕ), z.1 + z.2 < Λ →
      ((Λ - (z.1 + z.2) : ℤ) : ℝ) ≤ Nl → (n : ℝ) ≤ Nl → u ∈ Qs k →
      let q : ℝ := ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) - 2 * (W0 : ℝ) - 3 +
        a * (Λ : ℝ) - (z.1 : ℝ)) / ((Λ - (z.1 + z.2) : ℤ) : ℝ)
      (∀ s, s ≤ n → GreedyAttachment.vertex z q Vb s ∈ Qs k) →
      (∀ s, s < n → -T ≤ ω (GreedyAttachment.vertex z q Vb s)) →
      -2 * Cm * (n : ℝ) - t / 2 ≤
        ∑ s ∈ Finset.range n, ω (GreedyAttachment.vertex z q Vb s))
  have hEg : Tendsto (fun k : ℕ => (environmentLaw μ).real
      {ω : Environment | ¬ Egeo ω (Ts k) (Qs k)}) atTop (𝓝 0) :=
    stair_geometry_event_tendsto μ p' hp' hmom' a ha₀ ha₁ A (R + 2 * C₁ + 10) ε₀ hA hB hε₀
      m1 K1 K2 hm1 hK1 hK2 hm1p hK1p k0 m hm3
  have hSt : Tendsto (fun k : ℕ => (environmentLaw μ).real
      {ω : Environment | ¬ Estair ω k}) atTop (𝓝 0) :=
    staircase_family_event_tendsto μ p' hp' hmom' a ha₀ ha₁ A (R + 2 * C₁ + 10) ε₀ hA hB hε₀
      m1 K1 K2 hm1 hK1 hK2 hK2p k0 m hm3
  obtain ⟨Qf, hQf, hQt⟩ := heavy_working_region_event_tendsto μ hp hmomp m k0 hm3 a A R C₁ ε₀
    hA hR (by linarith) hε₀
  obtain ⟨kA1, hkA1⟩ := eventually_atTop.1 (hEg.eventually (ge_mem_nhds hβ3))
  obtain ⟨kA2, hkA2⟩ := eventually_atTop.1 (hQt.eventually (ge_mem_nhds hβ3))
  obtain ⟨kA3, hkA3⟩ := eventually_atTop.1 (hSt.eventually (ge_mem_nhds hβ3))
  obtain ⟨kH, hkH⟩ := eventually_atTop.1 (heavy_vertex_block_tail_decay hp hCp0 hq0).2
  obtain ⟨kS1, hkS1⟩ := grid_pow_sub_jstar_ge (4 * ((W0 : ℝ) + (r0 : ℝ) + (L : ℝ))) k0 m hm3
  obtain ⟨kS2, hkS2⟩ := grid_pow_sub_jstar_ge (2 * (W0 : ℝ) * K + 4 * (r0 : ℝ) * Cm) k0 m hm3
  refine ⟨max kA1 (max kA2 (max kA3 (max kH (max kS1 (max kS2 (4 * k0 + 3)))))),
    fun k hkK hk => ?_⟩
  have hkA1' : kA1 ≤ k := by omega
  have hkA2' : kA2 ≤ k := by omega
  have hkA3' : kA3 ≤ k := by omega
  have hkH' : kH ≤ k := by omega
  have hkS1' : kS1 ≤ k := by omega
  have hkS2' : kS2 ≤ k := by omega
  have hk4 : 4 * k0 + 3 ≤ k := by omega
  have hk0' : k0 ≤ k := hKset k hkK
  have hmk : m k ≤ 3 * k := hm3 k hk0'
  have ht : 0 ≤ ε₀ * 2 ^ k / (k : ℝ) := by positivity
  set jstar : ℕ := ⌈((m k : ℝ) - 1) / 4⌉₊ with hjstar
  -- Step 4: grid levels, bins and the bad events
  obtain ⟨S, hS⟩ : ∃ S : ℕ → Finset ℤ, ∀ j I, I ∈ S j ↔
      (((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ∣ I ∧ |(I : ℝ)| ≤ (A + 4) * 2 ^ m k) := by
    choose S hS using fun j : ℕ => exists_finset_int_of_bounded
      (fun I => ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ∣ I ∧ |(I : ℝ)| ≤ (A + 4) * 2 ^ m k)
      ((A + 4) * 2 ^ m k) (fun I hI => hI.2)
    exact ⟨S, hS⟩
  obtain ⟨Hn, hHn⟩ : ∃ Hn : ℕ → Finset ℤ, ∀ j h, h ∈ Hn j ↔
      ∃ x : ℝ, (h : ℝ) * 2 ^ (k - j) ≤ x ∧ x < ((h : ℝ) + 1) * 2 ^ (k - j) ∧
        |x| ≤ R * 2 ^ k := by
    choose Hn hHn using fun j : ℕ => exists_finset_int_of_bounded
      (fun h : ℤ => ∃ x : ℝ, (h : ℝ) * 2 ^ (k - j) ≤ x ∧ x < ((h : ℝ) + 1) * 2 ^ (k - j) ∧
        |x| ≤ R * 2 ^ k) (R * 2 ^ k + 1) (fun h ⟨x, h1, h2, h3⟩ =>
        abs_bin_le (by positivity) (one_le_pow₀ (by norm_num)) h1 h2 h3)
    exact ⟨Hn, hHn⟩
  let Bad : ℕ → ℤ → ℤ → Set Environment := fun j I h => {ω : Environment |
    8 * cstar * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) ≤ ((2 ^ (m k - 4 * j - 1) : ℕ) : ℝ) ∧
      ¬ CoarseGoodAt ω a G0 K cstar (m k) k j I h}
  have hBadmem : ∀ (j : ℕ) (I h : ℤ) (ω : Environment), ω ∈ Bad j I h ↔
      (8 * cstar * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) ≤ ((2 ^ (m k - 4 * j - 1) : ℕ) : ℝ) ∧
        ¬ CoarseGoodAt ω a G0 K cstar (m k) k j I h) := fun _ _ _ _ => Iff.rfl
  have hBad : ∀ j ∈ Finset.Icc J jstar, ∀ I h : ℤ,
      (environmentLaw μ).real (Bad j I h) ≤ Real.exp (-(q0 / 2 * (j : ℝ) ^ 2)) := by
    intro j hj I h
    obtain ⟨hJj, hjj⟩ := Finset.mem_Icc.1 hj
    by_cases hc : 8 * cstar * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) ≤
        ((2 ^ (m k - 4 * j - 1) : ℕ) : ℝ)
    · obtain ⟨-, hjk, -, -⟩ := grid_scale_index_bounds hjstar hmk hk4 hk0 hjj
      have hjb := (grid_jstar_bounds (m := m k) hjstar).2
      have hk4j : k ≤ 4 * (k - j) + 3 := by omega
      have htr := htrial k hkK hk4 j hjj
      have hP : ∀ n : ℕ, 1 ≤ n → (n : ℝ) < (2 : ℝ) ^ (m k - 4 * j - 1) →
          q0 < (environmentLaw μ).real {ω : Environment |
            ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
              (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤
                8 * (2 : ℝ) ^ (k - j)) ∧
              G0 * (n : ℝ) - K * (2 : ℝ) ^ (k - j) < pathWeight ω q} := by
        intro n hn1 hn2
        have h1 := htr.1 n hn1 hn2
        rw [hG0q]
        exact h1
      calc (environmentLaw μ).real (Bad j I h)
          ≤ (environmentLaw μ).real {ω : Environment | ¬ CoarseGoodAt ω a G0 K cstar (m k) k j I h} :=
            measureReal_mono (fun ω hω => ((hBadmem j I h ω).1 hω).2)
        _ ≤ Real.exp (-(q0 / 2 * (j : ℝ) ^ 2)) :=
            coarse_good_event_prob_le μ hp hmomp a G0 K cstar q0 (by linarith) k j (m k)
              (hJ.trans hJj) hk4j hc htr.2 hP (hkH k hkH') I h
    · calc (environmentLaw μ).real (Bad j I h)
          ≤ (environmentLaw μ).real (∅ : Set Environment) :=
            measureReal_mono (fun ω hω => absurd ((hBadmem j I h ω).1 hω).1 hc)
        _ = 0 := measureReal_empty
        _ ≤ Real.exp (-(q0 / 2 * (j : ℝ) ^ 2)) := (Real.exp_pos _).le
  have hcard : ∀ j ∈ Finset.Icc J jstar,
      ((S j).card : ℝ) * ((Hn j).card : ℝ) ≤ C * 2 ^ (5 * j) := by
    intro j hj
    obtain ⟨-, hjjs⟩ := Finset.mem_Icc.1 hj
    obtain ⟨-, hjk, -, -⟩ := grid_scale_index_bounds hjstar hmk hk4 hk0 hjjs
    have h1 := (grid_count_le hA (m k) j (S j) (hS j)).2
    have h2 := (grid_bin_count_le hR hjk (Hn j) (hHn j)).2
    calc ((S j).card : ℝ) * ((Hn j).card : ℝ) ≤
          ((4 * (A + 4) + 1) * 2 ^ (4 * j)) * ((2 * R + 2) * 2 ^ j) :=
          mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
      _ = C * 2 ^ (5 * j) := by
          rw [hC, show 5 * j = 4 * j + j by ring, pow_add]
          ring
  have hsum : (environmentLaw μ).real (⋃ j ∈ Finset.Icc J jstar, ⋃ I ∈ S j, ⋃ h ∈ Hn j,
      Bad j I h) ≤ C * ∑' i : ℕ, (2 : ℝ) ^ (5 * (i + J)) *
        Real.exp (-(q0 / 2 * ((i + J : ℕ) : ℝ) ^ 2)) :=
    (grid_union_measure_le (environmentLaw μ) J jstar S Hn Bad
      (fun j => Real.exp (-(q0 / 2 * (j : ℝ) ^ 2)))
      (fun j hj I _ h _ => hBad j hj I h)).trans
      (grid_scale_tail_le hq0 hCpos'.le J jstar S Hn hcard)
  -- Step 5: off the four events the good event holds
  let E1 : Set Environment := {ω : Environment | ¬ Egeo ω (Ts k) (Qs k)}
  let E2 : Set Environment := {ω : Environment | ¬ ∀ z ∈ Qf k, ω z ≤ ε₀ * 2 ^ k / (k : ℝ)}
  let E3 : Set Environment := {ω : Environment | ¬ Estair ω k}
  let U : Set Environment := ⋃ j ∈ Finset.Icc J jstar, ⋃ I ∈ S j, ⋃ h ∈ Hn j, Bad j I h
  have hsub : (Gγ A R ε₀ k J)ᶜ ⊆ E1 ∪ E2 ∪ E3 ∪ U := by
    intro ω hω
    by_contra hcon
    apply hω
    have hEg' : Egeo ω (Ts k) (Qs k) := by
      by_contra hh
      have hmem : ω ∈ E1 := hh
      exact hcon (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ hmem)))
    have hHv : ∀ z ∈ Qf k, ω z ≤ ε₀ * 2 ^ k / (k : ℝ) := by
      by_contra hh
      have hmem : ω ∈ E2 := hh
      exact hcon (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ hmem)))
    have hEs : Estair ω k := by
      by_contra hh
      have hmem : ω ∈ E3 := hh
      exact hcon (Set.mem_union_left _ (Set.mem_union_right _ hmem))
    have hUb : ∀ j ∈ Finset.Icc J jstar, ∀ I ∈ S j, ∀ h ∈ Hn j, ω ∉ Bad j I h :=
      fun j hj I hI h hh hm => hcon (Set.mem_union_right _
        (Set.mem_biUnion hj (Set.mem_biUnion hI (Set.mem_biUnion hh hm))))
    obtain ⟨hE1, hE2, hE3, hE4⟩ := hEs
    have hcoarseG : ∀ j : ℕ, J ≤ j → j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
        8 * cstar * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) ≤
          ((2 ^ (m k - 4 * j - 1) : ℕ) : ℝ) →
        ∀ I : ℤ, ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * 2 ^ m k →
        ∀ h : ℤ, (h : ℝ) * ((2 ^ (k - j) : ℕ) : ℝ) ≤ R * 2 ^ k →
          -(R * 2 ^ k) < ((h : ℝ) + 1) * ((2 ^ (k - j) : ℕ) : ℝ) →
        CoarseGoodAt ω a G0 K cstar (m k) k j I h := by
      intro j hJj hjj hc I hdiv hI h hb1 hb2
      have hwc : (((2 ^ (k - j) : ℕ)) : ℝ) = (2 : ℝ) ^ (k - j) := by push_cast; ring
      rw [hwc] at hb1 hb2
      have hw0 : (0 : ℝ) < 2 ^ (k - j) := by positivity
      have hR2 : 0 ≤ R * 2 ^ k := by positivity
      have hIm : I ∈ S j := (hS j I).2 ⟨hdiv, hI⟩
      have hhm : h ∈ Hn j := (hHn j h).2 ⟨max ((h : ℝ) * 2 ^ (k - j)) (-(R * 2 ^ k)),
        le_max_left _ _, max_lt (by nlinarith [hw0]) hb2,
        abs_le.2 ⟨le_max_right _ _, max_le hb1 (by linarith)⟩⟩
      by_contra hh
      exact hUb j (Finset.mem_Icc.2 ⟨hJj, hjj⟩) I hIm h hhm ((hBadmem j I h ω).2 ⟨hc, hh⟩)
    have hmain := grid_det_general_named ω (Ts k) (ε₀ * 2 ^ k / (k : ℝ)) a G0 dl dr K Cm cstar C₁
      A R m1 K1 k J m ha₀ ha₁ hm1 hK1 hJ ht hcdef hK1' hdl hdr hCm0 hGC (le_of_eq hC₁def.symm)
      (grid_scale_index_bounds hjstar hmk hk4 hk0 le_rfl).1 (hkS1 k hkS1') (hkS2 k hkS2')
      hEg' hE1 hE2 hE3 hE4 hcoarseG
    have hmem : Egeo ω (Ts k) (Qs k) ∧ (∀ z ∈ Qs k, ω z ≤ ε₀ * 2 ^ k / (k : ℝ)) ∧
        GridVertexClause ω (Ts k) (ε₀ * 2 ^ k / (k : ℝ)) a G0 dl dr C₁ A R k J m reach reachBack :=
      ⟨hEg', fun z hz => hHv z ((hQf k hk0' z).2 hz), hmain⟩
    exact hmem
  -- Step 6: the bound
  have e1 : (environmentLaw μ).real E1 ≤ β J / 3 := hkA1 k hkA1'
  have e2 : (environmentLaw μ).real E2 ≤ β J / 3 := hkA2 k hkA2'
  have e3 : (environmentLaw μ).real E3 ≤ β J / 3 := hkA3 k hkA3'
  have h1 := measureReal_mono (μ := environmentLaw μ) hsub
  have h2 := measureReal_union_le (μ := environmentLaw μ) (E1 ∪ E2 ∪ E3) U
  have h3 := measureReal_union_le (μ := environmentLaw μ) (E1 ∪ E2) E3
  have h4 := measureReal_union_le (μ := environmentLaw μ) E1 E2
  have h5 : (environmentLaw μ).real U ≤ C * ∑' i : ℕ, (2 : ℝ) ^ (5 * (i + J)) *
      Real.exp (-(q0 / 2 * ((i + J : ℕ) : ℝ) ^ 2)) := hsum
  linarith [h1, h2, h3, h4, h5, e1, e2, e3, hβJeq]

end LPPDifferentiability
