/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.RarefastSiteEvents
public import Differentiability.Probability.RarefastGoodPathContradiction
public import Differentiability.Probability.HighDensityOrientedPaths

/-! # Rare fast crossings

This file proves Proposition 3.4 of the differentiability preprint.

Steps 1–5 build good coarse-site events from a crossing probability bounded
below. The high-density oriented-path lemma then gives an infinite oriented
path of good sites with positive probability. Step 6 shows that such a path
has probability zero. Hence the crossing probability is below every `p₀` for
all large `s`, uniformly in the length `n`.

## References

* C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LPPDifferentiability

/-- Proposition 3.4 of the differentiability preprint, in the uniform form proved by Steps 1–6: for
every `p₀ > 0` there is `s₂` such that, for every `s ≥ s₂` and every length `n`, the probability
that some admissible path from level `0` to level `n`, with transverse coordinate at most `R s` in
absolute value at every vertex, has `f_σ`-defect below `-ε s` is less than `p₀`. The start is free
on level `0`. -/
theorem rarefast_uniform
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
    (R ε σ : ℝ) (hR : 0 < R) (hε : 0 < ε) (hσ : σ = 1 ∨ σ = -1) :
    let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
    let slope : ℝ :=
      if σ = 1 then derivWithin H (Ioi 0) 0 else derivWithin H (Iio 0) 0
    let rho : Lattice → ℝ := fun z => (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)
    let f : Lattice → ℝ := fun z => H 0 * ((z.1 : ℝ) + (z.2 : ℝ)) + slope * rho z
    let E : ℝ → ℕ → Set Environment := fun s n => {ω | ∃ u : Lattice,
      u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
        (∀ i, |rho (q.vertex i)| ≤ R * s) ∧
        f (q.vertex (Fin.last (e.1 + e.2)) - u) - pathWeight ω q < -(ε * s)}
    ∀ p₀ : ℝ, 0 < p₀ → ∃ s₂ : ℝ, ∀ (s : ℝ) (n : ℕ), s₂ ≤ s →
      (environmentLaw μ).real (E s n) < p₀ := by
  intro H slope rho f E p₀ hp₀
  obtain ⟨ζ, hζ0, -, hperc⟩ := exists_high_density_oriented_path_cutoff 10
  obtain ⟨T, hT, D₀, hD₀, s₂, hs₂, hsites⟩ :=
    exists_rarefast_coarse_site_events μ hneg hpos g hgcont hghom hgconc hgshape
      a ha₀ ha₁ R ε σ hR hε hσ ζ hζ0 p₀ hp₀
  refine ⟨s₂, fun s n hs => ?_⟩
  by_contra hcon
  have hlarge : p₀ ≤ (environmentLaw μ).real (E s n) := not_lt.mp hcon
  obtain ⟨G, hGm, hGc, hGi, -, hGW⟩ := hsites s n hs hlarge
  have hposP := (hperc (environmentLaw μ) G hGm hGc hGi).2
  have hzero := measureReal_rarefast_good_oriented_path_eq_zero μ hneg hpos g hgcont
    hghom hgconc hgshape a ha₀ ha₁ R ε σ hR hε hσ T hT D₀ hD₀ s (hs₂.trans hs) n G hGW
  exact hposP.ne' hzero

/-- Proposition 3.4 of the differentiability preprint in its equivalent form: for every `ε' > 0`
there exist `s₁` and `N` such that the probability is at most `ε'` whenever
`s ≥ s₁` and `n ≥ N s`. Here `N` can be taken to be `0`. -/
theorem rarefast_eventually_le
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
    (R ε σ : ℝ) (hR : 0 < R) (hε : 0 < ε) (hσ : σ = 1 ∨ σ = -1) :
    let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
    let slope : ℝ :=
      if σ = 1 then derivWithin H (Ioi 0) 0 else derivWithin H (Iio 0) 0
    let rho : Lattice → ℝ := fun z => (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)
    let f : Lattice → ℝ := fun z => H 0 * ((z.1 : ℝ) + (z.2 : ℝ)) + slope * rho z
    let E : ℝ → ℕ → Set Environment := fun s n => {ω | ∃ u : Lattice,
      u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
        (∀ i, |rho (q.vertex i)| ≤ R * s) ∧
        f (q.vertex (Fin.last (e.1 + e.2)) - u) - pathWeight ω q < -(ε * s)}
    ∀ ε' : ℝ, 0 < ε' → ∃ s₁ : ℝ, ∃ N : ℝ, ∀ (s : ℝ) (n : ℕ), s₁ ≤ s →
      N * s ≤ (n : ℝ) → (environmentLaw μ).real (E s n) ≤ ε' := by
  intro H slope rho f E ε' hε'
  obtain ⟨s₂, hs₂⟩ := rarefast_uniform μ hneg hpos g hgcont hghom hgconc hgshape
    a ha₀ ha₁ R ε σ hR hε hσ ε' hε'
  exact ⟨s₂, 0, fun s n hs _ => (hs₂ s n hs).le⟩

end LPPDifferentiability
