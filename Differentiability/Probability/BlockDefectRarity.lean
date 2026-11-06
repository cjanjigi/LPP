/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.ArbitraryEndpoints
import Mathlib.Tactic

/-!
# The rare block events at one scale

Equation (6.4) of the differentiability preprint. At the scale `s_* = 2^k`, `n_* = n_k` of a large
record index `k`, every block event `A_b = A^H_b ∪ A^E_b` ((6.2) and (6.3) of the preprint) has
probability at most `2 q₀`: the defect event `A^H_b` by Proposition 5.9 with `A = 2`, `R = 5`,
`ε = η` (the block lies in a translate of the region), and the crossing event `A^E_b` by translation
invariance and the choice of `n_k`. The conclusion has the form of the hypothesis `hrare` of
`long_path_disjoint_witnesses_ae`.

## References

* C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in the
  planar corner growth model*, preprint, Section 6.2, Proposition 5.9 and (6.2)-(6.4).
-/

public section

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

/-- **Equation (6.4) of the differentiability preprint**: for every `η > 0` and every large record
index `k`, every block event at the scale `s = 2^k`, `n = n_k` has probability at most
`2 q₀`, in the form of the hypothesis `hrare` of `long_path_disjoint_witnesses_ae`. -/
theorem block_rare_events_le
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
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (q0 : ℝ) (hq0 : 0 < q0)
    (k0 : ℕ) (m nk : ℕ → ℕ) (Kset : Set ℕ)
    (hmtop : Tendsto (fun k : ℕ => (2 : ℝ) ^ m k / 2 ^ k) atTop atTop)
    (hm3 : ∀ k : ℕ, k0 ≤ k → m k ≤ 3 * k)
    (hKset : ∀ k ∈ Kset, k0 ≤ k)
    (hnk :
      let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
      let dl : ℝ := derivWithin H (Iio 0) 0
      let dr : ℝ := derivWithin H (Ioi 0) 0
      let K : ℝ := 100 * (1 + |dl| + |dr|)
      let P : ℕ → ℕ → ℝ := fun k n => (environmentLaw μ).real {ω : Environment |
        ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
          (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤
            8 * (2 : ℝ) ^ k) ∧
            g (toQuadrant (a, 1 - a)) * (n : ℝ) - K * (2 : ℝ) ^ k < pathWeight ω q}
      ∀ k : ℕ, k0 ≤ k →
        (2 : ℝ) ^ m k / 2 < nk k ∧ (nk k : ℝ) ≤ 2 ^ m k ∧ P k (nk k) ≤ q0)
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
    let K : ℝ := 100 * (1 + |dl| + |dr|)
    let G0 : ℝ := H 0
    ∀ η : ℝ, 0 < η → ∃ k1 : ℕ, ∀ k ∈ Kset, k1 ≤ k →
      let s : ℝ := 2 ^ k
      let n : ℕ := nk k
      ∀ b : Lattice, (environmentLaw μ).real {ω : Environment |
        let v : Lattice → Lattice := fun b =>
          let j : ℤ := ⌊(b.2:ℝ)*s+a*((b.1*n:ℤ):ℝ)⌋
          (j,b.1*n-j)
        let block : Lattice → Lattice → Prop := fun b z =>
          (b.1 : ℝ)*(n : ℝ) ≤ (z.1 : ℝ)+(z.2 : ℝ) ∧ (z.1 : ℝ)+(z.2 : ℝ) ≤ (b.1 : ℝ)*(n : ℝ)+3*(n : ℝ) ∧
            |(1-a)*(z.1 : ℝ)-a*(z.2 : ℝ)-(b.2 : ℝ)*s| ≤ 4*s
        let defectWitness : Lattice → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop := fun b _ e q =>
          (∀ i, block b (q.vertex i)) ∧
            min (G0*((e.1 : ℝ)+(e.2 : ℝ))+dl*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q)
              (G0*((e.1 : ℝ)+(e.2 : ℝ))+dr*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q) < -(η*s)
        let crossingWitness : Lattice → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop :=
          fun b u e q =>
            u.1+u.2 = (b.1+1)*n ∧ e.1+e.2 = n ∧
              (∀ i, |((1-a)*((q.vertex i).1 : ℝ)-a*((q.vertex i).2 : ℝ))-
                ((1-a)*((v (b.1+1,b.2)).1 : ℝ)-a*((v (b.1+1,b.2)).2 : ℝ))| ≤ 8*s) ∧
              G0*(n : ℝ)-K*s < pathWeight ω q
        ∃ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
          defectWitness b u e q ∨ crossingWitness b u e q} ≤ 2*q0 := by
  intro H dl dr K G0 η hη
  obtain ⟨k1, hk1⟩ := arbitrary_endpoints_defect_le μ hneg hpos g hgcont hghom hgconc hgshape
    a ha₀ ha₁ k0 m Kset hmtop hm3 hKset hgrid 2 5 η q0 (by norm_num) (by norm_num) hη hq0
  refine ⟨k1, fun k hk hkk => ?_⟩
  intro s n b
  have hk0 := hKset k hk
  obtain ⟨-, hn2, hP⟩ := hnk k hk0
  have hs1 : (1 : ℝ) ≤ s := one_le_pow₀ (by norm_num)
  have hG0 : G0 = g (toQuadrant (a, 1 - a)) := by
    simp only [G0, H, quadrantExtension, add_zero, sub_zero]
  -- The centre of the block (with level `b.1 n + n`) and the crossing entrance.
  let L0 : ℤ := b.1 * n + n
  let z0 : Lattice := (⌊(b.2 : ℝ) * s + a * (L0 : ℝ)⌋, L0 - ⌊(b.2 : ℝ) * s + a * (L0 : ℝ)⌋)
  let vb : Lattice := (⌊(b.2 : ℝ) * s + a * (((b.1 + 1) * n : ℤ) : ℝ)⌋,
    (b.1 + 1) * n - ⌊(b.2 : ℝ) * s + a * (((b.1 + 1) * n : ℤ) : ℝ)⌋)
  have hz0l : (z0.1 : ℝ) + (z0.2 : ℝ) = (b.1 : ℝ) * n + n := by
    simp only [z0, L0]; push_cast; ring
  have hz0r : (1 - a) * (z0.1 : ℝ) - a * (z0.2 : ℝ) =
      ⌊(b.2 : ℝ) * s + a * (L0 : ℝ)⌋ - a * (L0 : ℝ) := by
    simp only [z0]; push_cast; ring
  have hf1 := Int.floor_le ((b.2 : ℝ) * s + a * (L0 : ℝ))
  have hf2 := Int.lt_floor_add_one ((b.2 : ℝ) * s + a * (L0 : ℝ))
  let AH : Set Environment := {ω : Environment | ∃ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
    (∀ i, |((q.vertex i).1 : ℝ) + ((q.vertex i).2 : ℝ) - ((z0.1 : ℝ) + (z0.2 : ℝ))| ≤
        2 * 2 ^ m k ∧
      |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ) -
        ((1 - a) * (z0.1 : ℝ) - a * (z0.2 : ℝ))| ≤ 5 * s) ∧
    min (G0 * ((e.1 : ℝ) + (e.2 : ℝ)) + dl * ((1 - a) * (e.1 : ℝ) - a * (e.2 : ℝ)) -
        pathWeight ω q)
      (G0 * ((e.1 : ℝ) + (e.2 : ℝ)) + dr * ((1 - a) * (e.1 : ℝ) - a * (e.2 : ℝ)) -
        pathWeight ω q) < -(η * s)}
  let AE : Set Environment := {ω : Environment |
    ∃ u : Lattice, u.1 + u.2 = vb.1 + vb.2 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
      (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ) -
        ((1 - a) * (vb.1 : ℝ) - a * (vb.2 : ℝ))| ≤ 8 * s) ∧
      g (toQuadrant (a, 1 - a)) * (n : ℝ) - K * s < pathWeight ω q}
  have hAH : (environmentLaw μ).real AH ≤ q0 := hk1 k hk hkk z0
  have hAE : (environmentLaw μ).real AE ≤ q0 :=
    (measureReal_strip_crossing_translate μ a (8 * s) n vb
      (fun _ W => g (toQuadrant (a, 1 - a)) * (n : ℝ) - K * s < W)).trans_le hP
  refine le_trans (measureReal_mono (s₂ := AH ∪ AE) ?_) ((measureReal_union_le _ _).trans ?_)
  · intro ω hω
    obtain ⟨u, e, q, hw | hw⟩ := hω
    · obtain ⟨hblock, hmin⟩ := hw
      refine Or.inl ⟨u, e, q, fun i => ?_, hmin⟩
      obtain ⟨l1, l2, l3⟩ := hblock i
      have hnm : (n : ℝ) ≤ 2 ^ m k := hn2
      refine ⟨?_, ?_⟩
      · rw [hz0l, abs_le]; constructor <;> linarith
      · rw [hz0r, abs_le]
        have h3 := abs_le.1 l3
        constructor <;> linarith
    · obtain ⟨hu, he, hr, hwt⟩ := hw
      refine Or.inr ⟨u, ?_, e, he, q, hr, ?_⟩
      · rw [hu]; simp only [vb]; ring
      · rw [← hG0]; exact hwt
  · linarith

end LPPDifferentiability
