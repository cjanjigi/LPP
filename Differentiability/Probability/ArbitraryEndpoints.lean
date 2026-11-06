/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.RareFastCrossings
public import Differentiability.Probability.RarefastTranslation
public import Differentiability.Model.Paths.GridEntranceExit
import Martin2004.Probability.ShapeAboveMean
import Differentiability.Analysis.GridScaleCounts
import Mathlib.Tactic

/-!
# Paths with arbitrary endpoints (Proposition 5.9 of the differentiability preprint)

Proposition 5.9 of the differentiability preprint, for bounded weights, using Proposition 3.4 with a
real centre. The conclusion of Lemma 5.7 (i) and (ii) enters as the hypothesis `hgrid`, and the
record scales enter through the hypotheses `hmtop`, `hm3` and `hKset`. Every vertex `u` of the
region is joined to coarse levels by its entrance and exit paths (`grid_entrance_exit`); a path with
defect below `-ε s_k` then gives a crossing between two coarse levels with defect below `-ε s_k / 2`
in the block of half-width `(R + 2 C₁) s_k`, hence, after translating its lower level to `0`, a
witness of the rarefast event of half-width `(R + 2 C₁ + 1) s_k`. There are boundedly many
pairs of coarse levels, so the probability is at most `2 β_J + 2 C_{A,J} ϵ`.

## References

* C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in the
  planar corner growth model*, preprint, Proposition 3.4, Lemma 5.7 and Proposition 5.9.
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

/-- **The reduction to coarse levels** (the proof of Proposition 5.9 of the differentiability
preprint), in one environment on which the conclusion of Lemma 5.7 (i) holds: a path in the region
with `min (Hdef₋, Hdef₊) < -ε s_k` gives a pair of coarse levels `I⁻ < I⁺` (multiples of `l_J` with
`|I^±| ≤ (A + 4) L_k` and `I⁺ - I⁻ ≥ 2 l_J`), a slope, and a crossing from level `I⁻` to level `I⁺`
with all vertices in `|r| ≤ (R + 2 C₁) s_k` and defect below `-ε s_k / 2`. -/
private theorem endpoint_pair_of_mem (ω : Environment) (a G0 dl dr c1 A R ε : ℝ) (M k J : ℕ)
    (hc1 : 1 ≤ c1) (hε : 0 < ε) (hJ1 : 1 ≤ J) (hJ : J ≤ ⌈((M : ℝ) - 1) / 4⌉₊)
    (hjk : ⌈((M : ℝ) - 1) / 4⌉₊ ≤ k) (hk : 0 < k)
    (hJε : 16 * c1 * ∑' i : ℕ, ((i + J : ℕ) : ℝ) ^ 2 / 2 ^ (i + J) ≤ ε / 8)
    (hconn : ∀ j : ℕ, J ≤ j → j ≤ ⌈((M : ℝ) - 1) / 4⌉₊ →
      ∀ I : ℤ, ((2 ^ (M - 4 * j - 1) : ℕ) : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * 2 ^ M →
      ∀ ρ : ℝ, |ρ| ≤ R * 2 ^ k → ∀ z₀ z₁ : Lattice,
      (z₀.1 + z₀.2 = I ∧ ρ - 1 < (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ∧
        (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ≤ ρ) →
      (z₁.1 + z₁.2 = I + ((2 ^ (M - 4 * j - 1) : ℕ) : ℤ) ∧
        ρ - 1 < (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ∧
        (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ≤ ρ) →
      ∃ (D : ℕ × ℕ) (y : Path z₀ D),
        z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
        G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
            pathWeight ω y ≤
          c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε / 512 * 2 ^ k / (k : ℝ)) ∧
        G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
            pathWeight ω y ≤
          c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε / 512 * 2 ^ k / (k : ℝ)) ∧
        ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) - ρ| ≤
          c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)))
    (hev : ∃ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
      (∀ i, |((q.vertex i).1 : ℝ) + ((q.vertex i).2 : ℝ)| ≤ A * 2 ^ M ∧
        |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ R * 2 ^ k) ∧
      min (G0 * ((e.1 : ℝ) + (e.2 : ℝ)) + dl * ((1 - a) * (e.1 : ℝ) - a * (e.2 : ℝ)) -
          pathWeight ω q)
        (G0 * ((e.1 : ℝ) + (e.2 : ℝ)) + dr * ((1 - a) * (e.1 : ℝ) - a * (e.2 : ℝ)) -
          pathWeight ω q) < -(ε * 2 ^ k)) :
    ∃ p : ℤ × ℤ, (((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) ∣ p.1 ∧ |(p.1 : ℝ)| ≤ (A + 4) * 2 ^ M) ∧
      (((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) ∣ p.2 ∧ |(p.2 : ℝ)| ≤ (A + 4) * 2 ^ M) ∧
      2 * ((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) ≤ p.2 - p.1 ∧
      ∃ sl : ℝ, (sl = dr ∨ sl = dl) ∧
      ∃ u : Lattice, u.1 + u.2 = p.1 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = (p.2 - p.1).toNat ∧
      ∃ q : Path u e,
        (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤
          (R + 2 * c1) * 2 ^ k) ∧
        G0 * ((e.1 : ℝ) + (e.2 : ℝ)) + sl * ((1 - a) * (e.1 : ℝ) - a * (e.2 : ℝ)) -
          pathWeight ω q < -(ε / 2 * 2 ^ k) := by
  obtain ⟨u, e, x, hreg, hmin⟩ := hev
  have hs0 : (0 : ℝ) < 2 ^ k := by positivity
  have hεs : 0 < ε * 2 ^ k := by positivity
  have hcs : 0 ≤ 2 * c1 * 2 ^ k := by positivity
  have hx0 := hreg 0
  rw [x.start] at hx0
  have hxl := hreg (Fin.last (e.1 + e.2))
  rw [x.finish] at hxl
  have hul : |((u.1 + u.2 : ℤ) : ℝ)| ≤ A * 2 ^ M := by exact_mod_cast hx0.1
  have hul' : |(((u + ((e.1 : ℤ), (e.2 : ℤ))).1 + (u + ((e.1 : ℤ), (e.2 : ℤ))).2 : ℤ) : ℝ)| ≤
      A * 2 ^ M := by exact_mod_cast hxl.1
  obtain ⟨⟨z, D1, y1, hz, hD1, a1, b1, c1'⟩, -⟩ := grid_entrance_exit ω a G0 dl dr c1 A R ε M k J
    hc1 hε hJ1 hJ hjk hk hJε hconn u hul hx0.2
  obtain ⟨-, ⟨D2, y2, hlev2, a2, b2, c2⟩⟩ := grid_entrance_exit ω a G0 dl dr c1 A R ε M k J
    hc1 hε hJ1 hJ hjk hk hJε hconn _ hul' hxl.2
  obtain ⟨E1, x1, hE1, d1l, d1r, hv1⟩ := exists_concat_defect_eq ω a G0 dl dr y1 hD1 x
  obtain ⟨E2, x2, hE2, d2l, d2r, hv2⟩ := exists_concat_defect_eq ω a G0 dl dr x1 hE1 y2
  have hl0 : 0 < 2 ^ (M - 4 * J - 1) := by positivity
  have hlm := grid_mesh_le M J
  obtain ⟨hd1, -, -, -, hb1, -⟩ := grid_level_endpoints (A := A) hl0 hlm hul
  obtain ⟨-, hd2, -, -, -, hb2⟩ := grid_level_endpoints (A := A) hl0 hlm hul'
  have hle : u.1 + u.2 ≤ (u + ((e.1 : ℤ), (e.2 : ℤ))).1 + (u + ((e.1 : ℤ), (e.2 : ℤ))).2 := by
    simp only [Prod.fst_add, Prod.snd_add]; omega
  have hgap := grid_level_endpoints_gap hl0 hle
  generalize (⌊((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (M - 4 * J - 1) : ℕ) : ℝ)⌋ - 1) *
    ((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) = Im at hz hd1 hb1 hgap
  generalize (⌈(((u + ((e.1 : ℤ), (e.2 : ℤ))).1 + (u + ((e.1 : ℤ), (e.2 : ℤ))).2 : ℤ) : ℝ) /
    ((2 ^ (M - 4 * J - 1) : ℕ) : ℝ)⌉ + 1) * ((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) = Ip
    at hlev2 hd2 hb2 hgap
  have hE := congrArg Prod.fst hE2
  have hE' := congrArg Prod.snd hE2
  simp only [Prod.fst_add, Prod.snd_add] at hE hE' hlev2
  have hlen : E2.1 + E2.2 = (Ip - Im).toNat := by omega
  have hvert : ∀ i, |(1 - a) * ((x2.vertex i).1 : ℝ) - a * ((x2.vertex i).2 : ℝ)| ≤
      (R + 2 * c1) * 2 ^ k := by
    intro i
    have e : (R + 2 * c1) * 2 ^ k = R * 2 ^ k + 2 * c1 * 2 ^ k := by ring
    rw [e]
    rcases hv2 i with ⟨j, hj⟩ | ⟨j, hj⟩ <;> rw [hj]
    · rcases hv1 j with ⟨j', hj'⟩ | ⟨j', hj'⟩ <;> rw [hj']
      · have h1 := abs_le.1 (c1' j')
        have h2 := abs_le.1 hx0.2
        rw [abs_le]; constructor <;> linarith
      · have h1 := abs_le.1 (hreg j').2
        rw [abs_le]; constructor <;> linarith
    · have h1 := abs_le.1 (c2 j)
      have h2 := abs_le.1 hxl.2
      rw [abs_le]; constructor <;> linarith
  refine ⟨(Im, Ip), ⟨hd1, hb1⟩, ⟨hd2, hb2⟩, hgap, ?_⟩
  rcases min_lt_iff.1 hmin with h | h
  · exact ⟨dl, Or.inr rfl, z, hz, E2, hlen, x2, hvert, by linarith⟩
  · exact ⟨dr, Or.inl rfl, z, hz, E2, hlen, x2, hvert, by linarith⟩

/-- **Proposition 5.9 of the differentiability preprint**, for bounded weights: under `hgrid` (the
conclusion of Lemma 5.7) and the hypotheses on the record scales, for all `A, R, ε, ε'' > 0` there
is `k₁` such that for every record index `k ≥ k₁` and every lattice point `z0`, the probability that
some admissible path with all vertices within level distance `A L_k` and transverse distance
`R s_k` of `z0` has `Hdef₋ < -ε s_k` or `Hdef₊ < -ε s_k` is at most `ε''`. -/
theorem arbitrary_endpoints_defect_le
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
    (hgrid :
      let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
      let dl : ℝ := derivWithin H (Iio 0) 0
      let dr : ℝ := derivWithin H (Ioi 0) 0
      let K : ℝ := 100 * (1 + |dl| + |dr|)
      let G0 : ℝ := H 0
      let E : ℝ := ∫ x : ℝ, x ∂μ
      let cstar : ℝ := 50 / min a (1 - a)
      let C₁ : ℝ := 8 * cstar * (G0 - E) + 2 * K + 3 * cstar
      let Gconn : ℝ → ℝ → ℝ → ℕ → ℕ → Set Environment := fun A R ε₀ k J =>
        {ω : Environment | ∀ j : ℕ, J ≤ j → j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
          ∀ I : ℤ, ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * 2 ^ m k →
          ∀ ρ : ℝ, |ρ| ≤ R * 2 ^ k → ∀ z₀ z₁ : Lattice,
          (z₀.1 + z₀.2 = I ∧ ρ - 1 < (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ∧
            (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ≤ ρ) →
          (z₁.1 + z₁.2 = I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ∧
            ρ - 1 < (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ∧
            (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ≤ ρ) →
          ∃ (D : ℕ × ℕ) (y : Path z₀ D),
            z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
            G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
                pathWeight ω y ≤
              C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε₀ * 2 ^ k / (k : ℝ)) ∧
            G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
                pathWeight ω y ≤
              C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε₀ * 2 ^ k / (k : ℝ)) ∧
            ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) - ρ| ≤
              C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ))}
      ∀ A R : ℝ, 0 < A → 0 < R → ∃ β : ℕ → ℝ, Tendsto β atTop (𝓝 0) ∧
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ J : ℕ, 1 ≤ J → ∃ k1 : ℕ, ∀ k ∈ Kset, k1 ≤ k →
          (environmentLaw μ).real (Gconn A R ε₀ k J)ᶜ ≤ 2 * β J) :
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
  -- `0 ≤ G0 - E` (S3) of the preprint and `1 ≤ C₁`.
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
  have hθ : 0 < min a (1 - a) := lt_min ha₀ (by linarith)
  have hθ2 : min a (1 - a) ≤ 1 / 2 := by
    have := min_le_left a (1 - a)
    have := min_le_right a (1 - a)
    linarith
  have hc100 : 100 ≤ 50 / min a (1 - a) := by rw [le_div_iff₀ hθ]; linarith
  set C₁ : ℝ := 8 * (50 / min a (1 - a)) * (G0 - ∫ x : ℝ, x ∂μ) +
    2 * (100 * (1 + |dl| + |dr|)) + 3 * (50 / min a (1 - a)) with hC₁
  have hC1 : 1 ≤ C₁ := by
    have h1 : 0 ≤ 8 * (50 / min a (1 - a)) * (G0 - ∫ x : ℝ, x ∂μ) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ 2 * (100 * (1 + |dl| + |dr|)) := by positivity
    linarith
  -- The choice of `J` ((5.38), `2 β_J ≤ ε''/2`) and `k₁` of Lemma 5.7 (ii).
  obtain ⟨β, hβ, hβk⟩ := hgrid A R hA hR
  obtain ⟨J0, -, hJ0⟩ := grid_exists_J (c1 := C₁) hε
  obtain ⟨Jb, hJb⟩ := eventually_atTop.1
    (hβ.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < ε'' / 4)))
  obtain ⟨J, hJdef⟩ : ∃ J : ℕ, J = max (max J0 Jb) 1 := ⟨_, rfl⟩
  have hJ1 : 1 ≤ J := hJdef ▸ le_max_right _ _
  have hJε := hJ0 J (hJdef ▸ le_trans (le_max_left _ _) (le_max_left _ _))
  have hβJ : β J ≤ ε'' / 4 := hJb J (hJdef ▸ le_trans (le_max_right _ _) (le_max_left _ _))
  obtain ⟨k1g, hk1g⟩ := hβk (ε / 512) (by positivity) J hJ1
  -- Proposition 3.4 at half-width `R + 2 C₁ + 1` and `ε / 2`, both signs.
  set CAJ : ℝ := (2 * (A + 4) * 2 ^ (4 * J + 1) + 1) ^ 2 with hCAJ
  have hCAJ1 : 1 ≤ CAJ := by
    have hx : 0 ≤ 2 * (A + 4) * 2 ^ (4 * J + 1) := by positivity
    rw [hCAJ]; exact one_le_pow₀ (by linarith)
  have hCAJ0 : CAJ ≠ 0 := by linarith
  set ϵ : ℝ := ε'' / (4 * CAJ) with hϵ
  have hϵ0 : 0 < ϵ := by positivity
  set R' : ℝ := R + 2 * C₁ + 1 with hR'
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
  -- Conditions on `k` (`m_k - k → ∞`, so `2 l_J / s_k → ∞` and `J ≤ j_*(k)`).
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
      max Np Nm ≤ 2 * (2 : ℝ) ^ (m k - 4 * J - 1) / 2 ^ k ∧ 4 * J + 1 ≤ m k := by
    filter_upwards [eventually_ge_atTop k1g, eventually_ge_atTop 3,
      h2k.eventually_ge_atTop s1p, h2k.eventually_ge_atTop s1m,
      hlen.eventually_ge_atTop (max Np Nm),
      hmk.eventually_ge_atTop ((4 * J + 1 : ℕ) : ℤ)] with k h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, by omega⟩
  obtain ⟨k1, hk1⟩ := eventually_atTop.1 hev
  refine ⟨k1, fun k hk hkk z0 => ?_⟩
  obtain ⟨hkg, hk3, hs1p, hs1m, hN, hmJ⟩ := hk1 k hkk
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
  -- Translation to `z0 = 0`.
  rw [measureReal_region_defect_translate μ a G0 dl dr _ _ _ z0]
  -- The coarse level pairs and their crossing events.
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
    obtain ⟨p, hp1, hp2, hgap, sl, hsl, u, hu, e, he, q, hr, hd⟩ :=
      endpoint_pair_of_mem ω a G0 dl dr C₁ A R ε (m k) k J hC1 hε hJ1 hJs hjk (by omega) hJε
        hG hω
    have hpS : p ∈ S := by
      have b1 := abs_le.1 hp1.2
      have b2 := abs_le.1 hp2.2
      have hc := Int.le_ceil ((A + 4) * (2 : ℝ) ^ m k)
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, hp1, hp2, hgap⟩
      · have : ((-⌈(A + 4) * (2 : ℝ) ^ m k⌉ : ℤ) : ℝ) ≤ (p.1 : ℝ) := by push_cast; linarith
        exact_mod_cast this
      · have : (p.1 : ℝ) ≤ ((⌈(A + 4) * (2 : ℝ) ^ m k⌉ : ℤ) : ℝ) := by linarith
        exact_mod_cast this
      · have : ((-⌈(A + 4) * (2 : ℝ) ^ m k⌉ : ℤ) : ℝ) ≤ (p.2 : ℝ) := by push_cast; linarith
        exact_mod_cast this
      · have : (p.2 : ℝ) ≤ ((⌈(A + 4) * (2 : ℝ) ^ m k⌉ : ℤ) : ℝ) := by linarith
        exact_mod_cast this
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
