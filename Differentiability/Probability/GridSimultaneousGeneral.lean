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
import Differentiability.FinalDraft.Grid.GeneralTheorem
import Mathlib.Tactic

/-! # The simultaneous grid event `Gγ`, general weights

This file proves items (i) and (ii) of Lemma 5.7 of the differentiability preprint, for
general weights. It also uses the remark after that lemma (Section 5.3 of the preprint)
and items (C3) and (C7) of Appendix B.

`grid_connections_simultaneous_general` is the hypothesis `hgridγ` of
`arbitrary_endpoints_defect_le_general`: the good event `Gγ` (the geometry event `E_geo`, the
heavy-vertex event `E_hv` and the per-vertex connections of item (i) along `γ^u`) has
probability at least `1 - 2 β_J` for record indices `k ≥ k₁`, with `β_J → 0`.

The source four-way event implies the legacy event by retaining its geometry and cap and
using the actual selected grid connections. Complement monotonicity transfers the probability
bound.
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
  -- The constants of the source grid theorem.
  have hcdef : cstar = 50 / min a (1 - a) := rfl
  have hKdef : K = 100 * (1 + |dl| + |dr|) := rfl
  have hC₁def : C₁ = 8 * cstar * (G0 + 2 * Cm) + 2 * K + 2 * (r0 : ℝ) + 3 * cstar + 1 := rfl
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
  have htrial' : gridRecordTrials μ a G0 K q0 k0 m Kset := by
    rw [hG0q]
    exact htrial
  refine ⟨generalGridBeta A R q0, general_grid_beta_tendsto A R q0, ?_⟩
  intro ε₀ hε₀ J hJ
  have hactual := general_grid_connections_on_records μ p' hp' hmom' p hp hmomp
    a G0 dl dr K cstar A R C₁ ε₀ q0 ha₀ ha₁ hA hR hε₀ hq0 K1 K2 m1 hK1 hK2 hm1
    ((by norm_num : (4 : ℝ) < 40).trans hm1p) hK1p hK2p hK1' hdl hdr hGC hcdef
    (le_of_eq hC₁def.symm) k0 J hk0 hJ m Kset hm3 hKset htrial'
  obtain ⟨k1, hk1⟩ := eventually_atTop.mp (eventually_inf_principal.mp hactual)
  refine ⟨k1, fun k hk hlarge => ?_⟩
  obtain ⟨hprob, hpath⟩ := hk1 k hlarge hk
  let E := generalGridGoodEvent a G0 K cstar A R C₁ ε₀ Cm m k J K1 K2 m1
  have hsub : E ⊆ Gγ A R ε₀ k J := by
    intro ω hω
    have h := (mem_generalGridGoodEvent_iff a G0 K cstar A R C₁ ε₀ Cm m k J K1 K2 m1 ω).mp hω
    exact ⟨h.1.1.2, h.2, hpath ω hω⟩
  exact (measureReal_mono (compl_subset_compl.mpr hsub)).trans hprob

end LPPDifferentiability
