/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.TopRestrictedConcentration
public import Differentiability.Analysis.TiltStripShapeContinuity
public import Differentiability.Analysis.CubicTopTailScaling
import Mathlib.Tactic

/-!
# Shape bound and tail bound for the top sites

This file turns the uniform continuity estimate for the shape into a bound on the
shape at the displacements of the cubic strip. It also turns a bound on the mean of
the whole passage into a tail bound for the restricted passage.
-/

public section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace LPPDifferentiability

/-- Express the uniform continuity estimate for the shape in the natural
displacement carrier used by the path concentration theorem. -/
theorem eventually_cubic_top_shape_bound
    (g : Quadrant → ℝ) (hg : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant),
      g (c*x.1, c*x.2) = (c : ℝ)*g x)
    (a φ : ℝ) (ha0 : 0<a) (ha1 : a<1) (hφ : 0<φ)
    (hgap : g (toQuadrant (a,1-a)) ≤ 1-4*φ) :
    ∀ᶠ s : ℝ in atTop, ∀ d : ℕ × ℕ,
      d.1+d.2 = Nat.ceil (s^3) →
      |(1-a)*(d.1 : ℝ)-a*(d.2 : ℝ)| ≤ 16*s →
      g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) ≤ (1-3*φ)*(Nat.ceil (s^3) : ℝ) := by
  have hhom' : ∀ (c : ℝ≥0) (x : Quadrant), g (c • x) = (c : ℝ)*g x :=
    fun c x => hhom c x
  filter_upwards [eventually_cubic_tilt_strip_shape_bound g hg hhom' a φ ha0 ha1 hφ hgap]
    with s hs
  intro d hd hrho
  have hq : toQuadrant ((d.1 : ℝ), (d.2 : ℝ)) =
      ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) :=
    toQuadrant_quadrantInclusion ((d.1 : ℝ≥0), (d.2 : ℝ≥0))
  rw [← hq]
  exact hs d hd hrho

open Classical in
/-- Domination by the whole top passage supplies the restricted mean bound needed
for the concentration inequality. Its mean hypothesis concerns the whole passage
and is supplied by the shape result in the final theorem. -/
theorem source_top_tail_of_whole_mean_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (R : Finset Lattice) (u : Lattice) (d : ℕ × ℕ) (b t : ℝ)
    (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hi : Integrable (fun ω : Environment => lastPassage
      (fun z => if (ω z : EReal) = sSup ((fun r : ℝ => (r : EReal)) '' μ.support)
        then 1 else 0) u d) (environmentLaw μ))
    (hm : (∫ ω : Environment, lastPassage
      (fun z => if (ω z : EReal) = sSup ((fun r : ℝ => (r : EReal)) '' μ.support)
        then 1 else 0) u d ∂environmentLaw μ) ≤ b) :
    let E : Set Environment := {ω | ∃ p : Path u d,
      (∀ j, p.vertex j ∈ R) ∧
      b+t < ((p.collectedSites.filter (fun z => (ω z : EReal) =
        sSup ((fun r : ℝ => (r : EReal)) '' μ.support))).card : ℝ)}
    MeasurableSet E ∧
      (0 < R.card → (environmentLaw μ).real E ≤
        Real.exp (-(2*t^2)/(R.card : ℝ))) ∧
      (R=∅ → (environmentLaw μ).real E=0) := by
  obtain ⟨_hc, _hX, _hlaw, _hF, _hifin, hiorig, _heq, hdom⟩ :=
    source_top_restricted_transport μ R u d
  exact source_top_restricted_tail μ R u d b t hb ht
    ((integral_mono hiorig hi hdom).trans hm)

end LPPDifferentiability
