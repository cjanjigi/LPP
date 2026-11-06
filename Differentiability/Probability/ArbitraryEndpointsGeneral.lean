/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.RareFastCrossings
public import Differentiability.Probability.RarefastTranslation
public import Differentiability.Model.Paths.EndpointReductionGeneral
import Differentiability.Probability.GridCoarseGoodProbability
import Martin2004.Probability.ShapeAboveMean
import Differentiability.Analysis.GridScaleCounts
import Differentiability.Analysis.GridScaleSums
import Differentiability.Analysis.MixedRadixLevelDecomposition
import Mathlib.Tactic

/-!
# Arbitrary endpoints with general weights

Proposition 5.9 of the differentiability preprint extends to general weights by
trimming the endpoints before applying the grid construction. The trimming and
endpoint changes are described in Section B.3, items (C2) and (C8). The proof
uses `endpoint_pair_of_mem_general` with `ε₀ = ε / 512` and `Q = Q_k`.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen,
  *Differentiability of the shape function in the planar corner growth model*, preprint.
-/

public section

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

private theorem measureReal_le_of_compl_bound {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsFiniteMeasure ν] {G U V : Set α} {b : ℝ} (hG : ν.real Gᶜ ≤ b)
    (h : ∀ ω ∈ V, ω ∈ G → ω ∈ U) : ν.real V ≤ b + ν.real U := by
  refine (measureReal_mono (s₂ := Gᶜ ∪ U) fun ω hω => ?_).trans
    ((measureReal_union_le _ _).trans (by linarith))
  by_cases hg : ω ∈ G
  · exact Or.inr (h ω hω hg)
  · exact Or.inl hg

/-- The trimming bound of Section B.3, item (C2), of the differentiability preprint
holds for large `k`: `2 r₀ (t_k + |G₀| + K) ≤ ε 2^k / 64`. -/
private theorem scalar_trim_eventually (r0 : ℕ) (ε G K : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      2 * (r0 : ℝ) * (ε / 512 * 2 ^ k / (k : ℝ) + |G| + K) ≤ ε * 2 ^ k / 64 := by
  have h2 : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  filter_upwards [eventually_ge_atTop (r0 + 1),
    h2.eventually_ge_atTop (256 * r0 * (|G| + K) / ε)] with k hk hX
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hrk : (r0 : ℝ) ≤ k := by exact_mod_cast (by omega : r0 ≤ k)
  have hX0 : (0 : ℝ) < 2 ^ k := by positivity
  rw [div_le_iff₀ hε] at hX
  have hεX : 0 ≤ ε * 2 ^ k := by positivity
  have h1 : 2 * (r0 : ℝ) * (ε / 512 * 2 ^ k / (k : ℝ)) ≤ ε * 2 ^ k / 256 := by
    rw [show 2 * (r0 : ℝ) * (ε / 512 * 2 ^ k / (k : ℝ)) = ε * 2 ^ k / 256 * ((r0 : ℝ) / k) by
      field_simp; ring]
    have h3 : (r0 : ℝ) / k ≤ 1 := (div_le_one hk0).2 hrk
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ ε * 2 ^ k / 256)]
  have h3 : 2 * (r0 : ℝ) * (|G| + K) ≤ ε * 2 ^ k / 128 := by linarith
  have h4 : 2 * (r0 : ℝ) * (ε / 512 * 2 ^ k / (k : ℝ) + |G| + K) =
      2 * (r0 : ℝ) * (ε / 512 * 2 ^ k / (k : ℝ)) + 2 * (r0 : ℝ) * (|G| + K) := by ring
  rw [h4]
  linarith

/-- Proposition 5.9 of the differentiability preprint, with the general-weight
changes of Section B.3. Under the grid good event `hgridγ` and the characteristic-length
hypotheses, a path in the region around `z0` has defect below `-ε s_k` with probability
at most `ε`. -/
theorem arbitrary_endpoints_defect_le_general
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0:ℝ), (μ (Ioi t)) ^ (1/2:ℝ)) < ∞)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (k0 : ℕ) (m : ℕ → ℕ) (Kset : Set ℕ)
    (hmtop : Tendsto (fun k : ℕ => (2 : ℝ) ^ m k / 2 ^ k) atTop atTop)
    (hm3 : ∀ k : ℕ, k0 ≤ k → m k ≤ 3 * k)
    (hKset : ∀ k ∈ Kset, k0 ≤ k)
    (m1 K1 K2 : ℕ) (hm1 : 1 ≤ m1) (hK1 : 1 ≤ K1) (_ : 1 ≤ K2)
    (hgridγ :
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
          (environmentLaw μ).real (Gγ A R ε₀ k J)ᶜ ≤ 2 * β J) :
  let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
  let dl : ℝ := derivWithin H (Iio 0) 0
  let dr : ℝ := derivWithin H (Ioi 0) 0
  let G0 : ℝ := H 0
  ∀ A R ε ε'' : ℝ, 0 < A → 0 < R → 0 < ε → 0 < ε'' →
    ∃ k1 : ℕ, ∀ k ∈ Kset, k1 ≤ k → ∀ z0 : Lattice,
      (environmentLaw μ).real {ω : Environment |
        ∃ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
          (∀ i, |((q.vertex i).1 : ℝ) + ((q.vertex i).2 : ℝ) - ((z0.1 : ℝ) + (z0.2 : ℝ))| ≤
              A * 2 ^ m k ∧
            |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ) -
              ((1 - a) * (z0.1 : ℝ) - a * (z0.2 : ℝ))| ≤ R * 2 ^ k) ∧
          min (G0 * ((e.1 : ℝ) + (e.2 : ℝ)) + dl * ((1 - a) * (e.1 : ℝ) - a * (e.2 : ℝ)) -
              pathWeight ω q)
            (G0 * ((e.1 : ℝ) + (e.2 : ℝ)) + dr * ((1 - a) * (e.1 : ℝ) - a * (e.2 : ℝ)) -
              pathWeight ω q) < -(ε * 2 ^ k)} ≤ ε'' := by
  intro H dl dr G0 A R ε ε'' hA hR hε hε''
  classical
  obtain ⟨β, hβ, hβk⟩ := hgridγ A R hA hR
  clear hgridγ
  have hθ : 0 < min a (1 - a) := lt_min ha₀ (by linarith)
  let Cm : ℝ := ∫ x : ℝ, max (-x) 0 ∂μ
  have hCm : Cm = ∫ x : ℝ, max (-x) 0 ∂μ := rfl
  let cstar : ℝ := 50 / min a (1 - a)
  let K : ℝ := 100 * (1 + |dl| + |dr|)
  have hK : K = 100 * (1 + |dl| + |dr|) := rfl
  let θ₁ : ℝ := min a (1 - a) / 5
  let Ntr : ℕ := K1 * (2 * m1 ^ 2 + 1) ^ 2
  let W0 : ℕ := Ntr + 1
  let L : ℕ := ⌈4 * ((W0 : ℝ) + 2) / θ₁⌉₊
  let r0 : ℕ := K1 * (2 * L + 1) + Ntr
  let C₁ : ℝ := 8 * cstar * (G0 + 2 * Cm) + 2 * K + 2 * (r0 : ℝ) + 3 * cstar + 1
  have hC₁ : C₁ = 8 * cstar * (G0 + 2 * Cm) + 2 * K + 2 * (r0 : ℝ) + 3 * cstar + 1 := rfl
  have hEG : (∫ x : ℝ, x ∂μ) ≤ G0 := by
    have hab : a.toNNReal + (1 - a).toNNReal = 1 := by
      rw [← Real.toNNReal_add ha₀.le (by linarith)]
      norm_num
    have h := integral_le_shape_of_negative_moment_and_positive_tail μ hneg hpos g hgcont
      hghom hgconc hgshape a.toNNReal (1 - a).toNNReal hab
    have hG0 : G0 = g (a.toNNReal, (1 - a).toNNReal) := by
      simp only [G0, H, quadrantExtension, toQuadrant, add_zero, sub_zero]
    rw [hG0]
    exact h
  have hCm0 : 0 ≤ Cm := integral_nonneg fun x => le_max_right _ _
  have hGC : 0 ≤ G0 + 2 * Cm := by linarith [neg_integral_neg_part_le_integral_grid μ]
  have hC1 : 1 ≤ C₁ := by
    have hcs0 : 0 ≤ cstar := div_nonneg (by norm_num) hθ.le
    have hK0 : 0 ≤ K := by rw [hK]; positivity
    have h1 : 0 ≤ 8 * cstar * (G0 + 2 * Cm) := mul_nonneg (by linarith) hGC
    have h3 : (0 : ℝ) ≤ r0 := Nat.cast_nonneg _
    linarith
  have hdlr : |dl| ≤ K ∧ |dr| ≤ K := by rw [hK]; constructor <;> linarith [abs_nonneg dl, abs_nonneg dr]
  obtain ⟨J0, -, hJ0⟩ := grid_exists_J (c1 := C₁) hε
  obtain ⟨Jb, hJb⟩ := eventually_atTop.1
    (hβ.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < ε'' / 4)))
  obtain ⟨J, hJdef⟩ : ∃ J : ℕ, J = max (max J0 Jb) 1 := ⟨_, rfl⟩
  have hJ1 : 1 ≤ J := hJdef ▸ le_max_right _ _
  have hJε := hJ0 J (hJdef ▸ le_trans (le_max_left _ _) (le_max_left _ _))
  have hβJ : β J ≤ ε'' / 4 := hJb J (hJdef ▸ le_trans (le_max_right _ _) (le_max_left _ _))
  obtain ⟨k1g, hk1g⟩ := hβk (ε / 512) (by positivity) J hJ1
  let CAJ : ℝ := (2 * (A + 4) * 2 ^ (4 * J + 1) + 1) ^ 2
  have hCAJ : CAJ = (2 * (A + 4) * 2 ^ (4 * J + 1) + 1) ^ 2 := rfl
  have hCAJ1 : 1 ≤ CAJ := by
    have hx : 0 ≤ 2 * (A + 4) * 2 ^ (4 * J + 1) := by positivity
    rw [hCAJ]; exact one_le_pow₀ (by linarith)
  have hCAJ0 : CAJ ≠ 0 := by linarith
  let ϵ : ℝ := ε'' / (4 * CAJ)
  have hϵ : ϵ = ε'' / (4 * CAJ) := rfl
  have hϵ0 : 0 < ϵ := by positivity
  let R' : ℝ := R + 2 * C₁ + 1
  have hR' : R' = R + 2 * C₁ + 1 := rfl
  obtain ⟨s1p, Np, hp⟩ := rarefast_eventually_le μ hneg hpos g hgcont hghom hgconc hgshape
    a ha₀ ha₁ R' (ε / 2) 1 (by linarith) (by positivity) (Or.inl rfl) ϵ hϵ0
  obtain ⟨s1m, Nm, hm⟩ := rarefast_eventually_le μ hneg hpos g hgcont hghom hgconc hgshape
    a ha₀ ha₁ R' (ε / 2) (-1) (by linarith) (by positivity) (Or.inr rfl) ϵ hϵ0
  let fl : ℝ → Lattice → ℝ := fun sl d =>
    G0 * ((d.1 : ℝ) + (d.2 : ℝ)) + sl * ((1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ))
  let Ev : ℝ → ℝ → ℕ → Set Environment := fun sl s n => {ω : Environment |
    ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
      (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ R' * s) ∧
      fl sl (q.vertex (Fin.last (e.1 + e.2)) - u) - pathWeight ω q < -(ε / 2 * s)}
  have hp' : ∀ (s : ℝ) (n : ℕ), s1p ≤ s → Np * s ≤ n →
      (environmentLaw μ).real (Ev dr s n) ≤ ϵ := by
    intro s n h1 h2
    have h := hp s n h1 h2
    rw [ite_eq_left_of_eq_true _ _ (eq_true (rfl : (1 : ℝ) = 1))] at h
    exact h
  have hm' : ∀ (s : ℝ) (n : ℕ), s1m ≤ s → Nm * s ≤ n →
      (environmentLaw μ).real (Ev dl s n) ≤ ϵ := by
    intro s n h1 h2
    have h := hm s n h1 h2
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by norm_num : (-1 : ℝ) ≠ 1))] at h
    exact h
  have hmk : Tendsto (fun k : ℕ => (m k : ℤ) - k) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hmtop.eventually_ge_atTop ((2 : ℝ) ^ b.toNat)] with k hk
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    rw [le_div_iff₀ h2k, ← pow_add] at hk
    have := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 hk
    omega
  have hlen := grid_two_mesh_div_scale_tendsto (f := atTop) (m := m) (k := fun k => k) J hmk
  have h2k : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have hev : ∀ᶠ k : ℕ in atTop, k1g ≤ k ∧ 3 ≤ k ∧ s1p ≤ 2 ^ k ∧ s1m ≤ 2 ^ k ∧
      max Np Nm ≤ 2 * (2 : ℝ) ^ (m k - 4 * J - 1) / 2 ^ k ∧ 4 * J + 1 ≤ m k ∧
      2 * (r0 : ℝ) * (ε / 512 * 2 ^ k / (k : ℝ) + |G0| + K) ≤ ε * 2 ^ k / 64 := by
    filter_upwards [eventually_ge_atTop k1g, eventually_ge_atTop 3,
      h2k.eventually_ge_atTop s1p, h2k.eventually_ge_atTop s1m,
      hlen.eventually_ge_atTop (max Np Nm),
      hmk.eventually_ge_atTop ((4 * J + 1 : ℕ) : ℤ),
      scalar_trim_eventually r0 ε G0 K hε] with k h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, by omega, h7⟩
  obtain ⟨k1, hk1⟩ := eventually_atTop.1 hev
  refine ⟨k1, fun k hk hkk z0 => ?_⟩
  obtain ⟨hkg, hk3, hs1p, hs1m, hN, hmJ, hscal⟩ := hk1 k hkk
  have hm3k := hm3 k (hKset k hk)
  have hJs : J ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ := by
    have h1 : ((4 * J + 1 : ℕ) : ℝ) ≤ (m k : ℝ) := by exact_mod_cast hmJ
    have h2 : (J : ℝ) ≤ ((m k : ℝ) - 1) / 4 := by
      rw [le_div_iff₀ (by norm_num)]; push_cast at h1; linarith
    exact_mod_cast h2.trans (Nat.le_ceil _)
  have hjk : ⌈((m k : ℝ) - 1) / 4⌉₊ ≤ k := by
    have := (grid_jstar_bounds (m := m k) rfl).2
    omega
  have h2k0 : (0 : ℝ) < 2 ^ k := by positivity
  have h2k1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  rw [measureReal_region_defect_translate μ a G0 dl dr _ _ _ z0]
  let S : Finset (ℤ × ℤ) := ((Finset.Icc (-⌈(A + 4) * (2 : ℝ) ^ m k⌉) ⌈(A + 4) * (2 : ℝ) ^ m k⌉) ×ˢ
    (Finset.Icc (-⌈(A + 4) * (2 : ℝ) ^ m k⌉) ⌈(A + 4) * (2 : ℝ) ^ m k⌉)).filter (fun p =>
      (((2 ^ (m k - 4 * J - 1) : ℕ) : ℤ) ∣ p.1 ∧ |(p.1 : ℝ)| ≤ (A + 4) * 2 ^ m k) ∧
      (((2 ^ (m k - 4 * J - 1) : ℕ) : ℤ) ∣ p.2 ∧ |(p.2 : ℝ)| ≤ (A + 4) * 2 ^ m k) ∧
      2 * ((2 ^ (m k - 4 * J - 1) : ℕ) : ℤ) ≤ p.2 - p.1)
  have hScard : (S.card : ℝ) ≤ CAJ := grid_coarse_pair_count_le hA (m k) J S
    (fun p hp => ⟨(Finset.mem_filter.1 hp).2.1, (Finset.mem_filter.1 hp).2.2.1⟩)
  let vp : ℤ × ℤ → Lattice := fun p => (⌊a * (p.1 : ℝ)⌋, p.1 - ⌊a * (p.1 : ℝ)⌋)
  let X : ℝ → ℤ × ℤ → Set Environment := fun sl p => {ω : Environment |
    ∃ u : Lattice, u.1 + u.2 = (vp p).1 + (vp p).2 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = (p.2 - p.1).toNat ∧
    ∃ q : Path u e,
      (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ) -
        ((1 - a) * ((vp p).1 : ℝ) - a * ((vp p).2 : ℝ))| ≤ R' * 2 ^ k) ∧
      fl sl (q.vertex (Fin.last (e.1 + e.2)) - u) - pathWeight ω q < -(ε / 2 * 2 ^ k)}
  have hX : ∀ sl p, (environmentLaw μ).real (X sl p) =
      (environmentLaw μ).real (Ev sl (2 ^ k) (p.2 - p.1).toNat) := fun sl p =>
    measureReal_strip_crossing_translate μ a (R' * 2 ^ k) _ (vp p)
      (fun d W => fl sl d - W < -(ε / 2 * 2 ^ k))
  have hXle : ∀ p ∈ S, (environmentLaw μ).real (X dr p) + (environmentLaw μ).real (X dl p) ≤
      2 * ϵ := by
    intro p hp
    have hgap := (Finset.mem_filter.1 hp).2.2.2
    have hnn : (0 : ℤ) ≤ p.2 - p.1 := by
      have : (0 : ℤ) ≤ 2 * ((2 ^ (m k - 4 * J - 1) : ℕ) : ℤ) := by positivity
      linarith
    have hn : 2 * (2 : ℝ) ^ (m k - 4 * J - 1) ≤ ((p.2 - p.1).toNat : ℝ) := by
      have h1 : ((2 * ((2 ^ (m k - 4 * J - 1) : ℕ) : ℤ) : ℤ) : ℝ) ≤ ((p.2 - p.1 : ℤ) : ℝ) := by
        exact_mod_cast hgap
      have h2 : (((p.2 - p.1).toNat : ℕ) : ℝ) = ((p.2 - p.1 : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hnn
      rw [h2]; push_cast at h1 ⊢; exact h1
    have hNp : Np * 2 ^ k ≤ ((p.2 - p.1).toNat : ℝ) := by
      have := (le_max_left Np Nm).trans hN
      rw [le_div_iff₀ h2k0] at this; linarith
    have hNm : Nm * 2 ^ k ≤ ((p.2 - p.1).toNat : ℝ) := by
      have := (le_max_right Np Nm).trans hN
      rw [le_div_iff₀ h2k0] at this; linarith
    rw [hX, hX]
    linarith [hp' _ _ hs1p hNp, hm' _ _ hs1m hNm]
  have hGk := hk1g k hk hkg
  refine le_trans (measureReal_le_of_compl_bound (environmentLaw μ) hGk
    (U := ⋃ p ∈ S, (X dr p ∪ X dl p)) ?_) ?_
  · intro ω hω hG
    obtain ⟨hE, hcap, hconn⟩ := hG
    obtain ⟨p, hp1, hp2, hgap, sl, hsl, u, hu, e, he, q, hr, hd⟩ :=
      endpoint_pair_of_mem_general ω a G0 dl dr K C₁ A R ε (ε / 512 * 2 ^ k / (k : ℝ) / (4 * (K2 : ℝ)))
        (m k) k J m1 K1
        {z | |((z.1 + z.2 : ℤ) : ℝ)| ≤ (A + 5) * 2 ^ m k ∧
          |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ (R + 2 * C₁ + 10) * 2 ^ k}
        ha₀ ha₁ hm1 hK1 hC1 hε hJ1 hJs hjk (by omega) hJε hdlr.1 hdlr.2 hscal
        (fun z h1 h2 => ⟨by linarith [(by positivity : (0 : ℝ) ≤ 2 ^ m k)],
          by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ C₁) h2k0.le]⟩) hE hcap hconn hω
    have hpS : p ∈ S := by
      have hc := Int.le_ceil ((A + 4) * (2 : ℝ) ^ m k)
      have key : ∀ x : ℤ, |(x : ℝ)| ≤ (A + 4) * 2 ^ m k →
          -⌈(A + 4) * (2 : ℝ) ^ m k⌉ ≤ x ∧ x ≤ ⌈(A + 4) * (2 : ℝ) ^ m k⌉ := fun x hx => by
        have b := abs_le.1 hx
        have h1 : ((-⌈(A + 4) * (2 : ℝ) ^ m k⌉ : ℤ) : ℝ) ≤ (x : ℝ) := by push_cast; linarith
        have h2 : (x : ℝ) ≤ ((⌈(A + 4) * (2 : ℝ) ^ m k⌉ : ℤ) : ℝ) := by linarith
        exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      exact ⟨⟨key _ hp1.2, key _ hp2.2⟩, hp1, hp2, hgap⟩
    have hvr : (1 - a) * ((vp p).1 : ℝ) - a * ((vp p).2 : ℝ) = ⌊a * (p.1 : ℝ)⌋ - a * p.1 := by
      simp only [vp]; push_cast; ring
    have hfl1 := Int.floor_le (a * (p.1 : ℝ))
    have hfl2 := Int.lt_floor_add_one (a * (p.1 : ℝ))
    have hmemX : ω ∈ X sl p := by
      refine ⟨u, ?_, e, he, q, fun i => ?_, ?_⟩
      · simp only [vp]; rw [hu]; ring
      · have h1 := abs_le.1 (hr i)
        have e : (R + 2 * C₁ + 1) * 2 ^ k = (R + 2 * C₁) * 2 ^ k + 2 ^ k := by ring
        rw [hvr, hR', e, abs_le]
        constructor <;> linarith
      · rw [q.finish, add_sub_cancel_left]
        simpa only [fl, Int.cast_natCast] using hd
    simp only [Set.mem_iUnion, Set.mem_union]
    rcases hsl with h | h
    · exact ⟨p, hpS, Or.inl (h ▸ hmemX)⟩
    · exact ⟨p, hpS, Or.inr (h ▸ hmemX)⟩
  · have hU : (environmentLaw μ).real (⋃ p ∈ S, (X dr p ∪ X dl p)) ≤ (S.card : ℝ) * (2 * ϵ) := by
      refine (measureReal_biUnion_finset_le S _).trans ?_
      refine (Finset.sum_le_sum fun p hp => (measureReal_union_le _ _).trans (hXle p hp)).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : (S.card : ℝ) * (2 * ϵ) ≤ CAJ * (2 * ϵ) :=
      mul_le_mul_of_nonneg_right hScard (by positivity)
    have h4 : CAJ * (2 * ϵ) = ε'' / 2 := by rw [hϵ]; field_simp; ring
    linarith

end LPPDifferentiability
