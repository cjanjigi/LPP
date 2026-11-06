/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.TiltChangeOfMeasure
public import Differentiability.Probability.RareFastCrossings

/-!
# The final limit in the change-of-measure lemma

In the last step of the proof of Lemma 4.2 of the differentiability preprint, the
event `calE(s, n)` of the change of measure is the event of Proposition 3.4 with
`σ = +`, `R = 8`, `ε = 1`, so `P(calE(s, ⌈s³⌉)) → 0`,
and the corollary `P(E(s, ⌈s³⌉)) ≤ err(s) + C √P(calE(s, ⌈s³⌉))` of the change
of measure gives `P(E(s, ⌈s³⌉)) → 0` off the flat segment.
-/

public section

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

/-- The center of `f_+`: `H 0 = g(ξ)` for `H h = g(a + h, 1 - a - h)`. -/
private theorem quadrantExtension_add_zero (g : Quadrant → ℝ) (a : ℝ) :
    quadrantExtension g (a + 0, 1 - a - 0) = g (toQuadrant (a, 1 - a)) := by
  rw [add_zero, sub_zero]
  rfl

/-- Exact match of the events in the last display of the proof of Lemma 4.2: the
event of Proposition 3.4 at `R = 8`, `ε = 1`, with center `H0 = G0` and slope
`dr`, is the event `calE` of the change of measure. -/
private theorem rarefast_event_eq_tilt_event (G0 H0 slope dr a s : ℝ) (n : ℕ)
    (hH0 : H0 = G0) (hslope : slope = dr) :
    {ω : Environment | ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧
      ∃ q : Path u e,
        (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * s) ∧
        H0 * (((q.vertex (Fin.last (e.1 + e.2)) - u).1 : ℝ) +
            ((q.vertex (Fin.last (e.1 + e.2)) - u).2 : ℝ)) +
          slope * ((1 - a) * ((q.vertex (Fin.last (e.1 + e.2)) - u).1 : ℝ) -
            a * ((q.vertex (Fin.last (e.1 + e.2)) - u).2 : ℝ)) -
          pathWeight ω q < -(1 * s)} =
    {ω : Environment | ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧
      ∃ q : Path u e,
        (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * s) ∧
        G0 * (((q.vertex (Fin.last (e.1 + e.2)) - u).1 : ℝ) +
            ((q.vertex (Fin.last (e.1 + e.2)) - u).2 : ℝ)) +
          dr * ((1 - a) * ((q.vertex (Fin.last (e.1 + e.2)) - u).1 : ℝ) -
            a * ((q.vertex (Fin.last (e.1 + e.2)) - u).2 : ℝ)) -
          pathWeight ω q < -s} := by
  subst hH0 hslope
  rw [one_mul]

/-- Lemma 4.2 of the differentiability preprint, including its final limit:
off the flat segment, the probability of the crossing event `E(s, ⌈s³⌉)` tends
to zero. `E(s, n)`: some admissible path from a site `u` of level `0` to a site
of level `n`, with transverse coordinate at most `8 s` in absolute value at every
vertex and weight above `g(ξ) n - K s`, where `K = 100 (1 + |dl| + |dr|)` and
`dl`, `dr` are the one-sided slopes of `H h = g(a + h, 1 - a - h)` at `0`. The
off-flat condition is `Gtop < 1` for the top-indicator shape value `Gtop` at
`ξ = (a, 1 - a)`, identified by the limit of its normalized means. -/
theorem tilt_crossing_tendsto_zero
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
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (Gtop : ℝ)
    (htop : Tendsto (fun m : ℕ => (∫ ω : Environment, lastPassage (fun z =>
      if (ω z : EReal) = sSup ((fun t : ℝ => (t : EReal)) '' μ.support) then (1 : ℝ) else 0)
        0 (⌊(m : ℝ) * a⌋₊, ⌊(m : ℝ) * (1 - a)⌋₊) ∂environmentLaw μ) / (m : ℝ))
      atTop (𝓝 Gtop))
    (hgap : Gtop < 1) :
    let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
    let dl : ℝ := derivWithin H (Iio 0) 0
    let dr : ℝ := derivWithin H (Ioi 0) 0
    let K : ℝ := 100 * (1 + |dl| + |dr|)
    Tendsto (fun s : ℝ => (environmentLaw μ).real {ω : Environment | ∃ u : Lattice,
        u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = ⌈s ^ 3⌉₊ ∧ ∃ q : Path u e,
          (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * s) ∧
            g (toQuadrant (a, 1 - a)) * (⌈s ^ 3⌉₊ : ℝ) - K * s < pathWeight ω q})
      atTop (𝓝 0) := by
  intro H dl dr K
  obtain ⟨C, -, err, herr, hle⟩ := tilt_change_of_measure_eventually_le μ a ha₀ ha₁
    (g (toQuadrant (a, 1 - a))) dl dr Gtop htop hgap
  -- Proposition 3.4 with `σ = +`, `R = 8`, `ε = 1`.
  have hrare := rarefast_uniform μ hneg hpos g hgcont hghom hgconc hgshape a ha₀ ha₁
    8 1 1 (by norm_num) one_pos (Or.inl rfl)
  dsimp only at hrare
  have hH0 : H 0 = g (toQuadrant (a, 1 - a)) := quadrantExtension_add_zero g a
  have hslope : (if (1 : ℝ) = 1 then dr else dl) = dr := ite_eq_left rfl
  refine squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) hle ?_
  rw [show 𝓝 (0 : ℝ) = 𝓝 (0 + C * Real.sqrt 0) by rw [Real.sqrt_zero, mul_zero, add_zero]]
  refine herr.add (tendsto_const_nhds.mul ((Real.continuous_sqrt.tendsto 0).comp ?_))
  rw [tendsto_order]
  refine ⟨fun b hb => Eventually.of_forall fun _ => hb.trans_le measureReal_nonneg,
    fun b hb => ?_⟩
  obtain ⟨s₂, hs₂⟩ := hrare b hb
  refine eventually_atTop.2 ⟨s₂, fun s hs => ?_⟩
  exact (congrArg (environmentLaw μ).real (rarefast_event_eq_tilt_event
    (g (toQuadrant (a, 1 - a))) (H 0) (if (1 : ℝ) = 1 then dr else dl) dr a s
    ⌈s ^ 3⌉₊ hH0 hslope)).ge.trans_lt (hs₂ s ⌈s ^ 3⌉₊ hs)

end LPPDifferentiability
