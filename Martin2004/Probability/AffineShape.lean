/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Scaling
public import LPP_Foundations.Probability.EnvironmentMap
public import LPP_Foundations.Probability.PassageIntegrable
public import LPP_Foundations.Probability.PassageMeasurable
public import Martin2004.Analysis.RationalPassageNormalization
public import LPP_Foundations.Frozen.Model.Quadrant

/-!
# Shapes under an affine change of weights

Replace every site weight `X` by `a * X + b`, with `a ≥ 0`. A path to the
displacement `d` has `d.1 + d.2` sites, so its weight becomes `a` times its old
weight plus `(d.1 + d.2) * b`, and the same is true of the largest path weight.
This file turns that exact identity into the expected-rate form of the shape
used by the shape theorems: the expected passage rate of the new law
is `a * g x + b * (x.1 + x.2)`.

Martin (2004), Lemma 4.5, uses this step (with `a = σ √r` and `b = r μ`).
The printed line there omits the drift term `b * (x.1 + x.2)`, which is kept here.
-/

public section

open MeasureTheory Filter
open scoped Topology NNReal

namespace LPPDifferentiability

/-- Expected last passage to the displacement `d`, after every weight is replaced by
`a * X + b` with `a ≥ 0`, is `a` times the old expectation plus `(d.1 + d.2) * b`.
This is the exact finite-size identity behind Martin (2004), Lemma 4.5. -/
theorem integral_lastPassage_affine_image
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun t : ℝ => t) μ) (a b : ℝ) (ha : 0 ≤ a)
    (hν : ν = μ.map (fun t : ℝ => a * t + b)) (d : ℕ × ℕ) :
    (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw ν) =
      a * (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw μ) +
        ((d.1 + d.2 : ℕ) : ℝ) * b := by
  have hφ : Measurable (fun t : ℝ => a * t + b) := by fun_prop
  -- The canonical law of the new weights is the image of the old law, site by site.
  have hlaw : environmentLaw ν =
      (environmentLaw μ).map (fun ω : Environment => fun z : Lattice => a * ω z + b) := by
    subst hν
    exact (environmentLaw_map_coordinatewise μ (fun t : ℝ => a * t + b) hφ).symm
  -- Exact identity at every environment, from the scaling theorem.
  have hpoint (ω : Environment) :
      lastPassage (fun z : Lattice => a * ω z + b) 0 d =
        a * lastPassage ω 0 d + ((d.1 + d.2 : ℕ) : ℝ) * b :=
    lastPassage_smul_add_const_of_nonneg a ha ω 0 d b
  have hint : Integrable (fun ω : Environment => lastPassage ω 0 d) (environmentLaw μ) :=
    integrable_lastPassage μ hμ 0 d
  rw [hlaw, integral_map
    (measurable_coordinatewise_environment_map (fun t : ℝ => a * t + b) hφ).aemeasurable
    (measurable_lastPassage 0 d).aestronglyMeasurable]
  simp only [hpoint]
  rw [integral_add (hint.const_mul a) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, one_smul]

/-- If the normalized expected passage to `x` has the limit `G` for the law `μ`, then for
the affine image law it has the limit `a * G + b * (x.1 + x.2)`; the drift term
`b * (x.1 + x.2)` is the one dropped in the printed line of Martin (2004), Lemma 4.5. -/
theorem tendsto_expected_rate_affine_image
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun t : ℝ => t) μ) (a b : ℝ) (ha : 0 ≤ a)
    (hν : ν = μ.map (fun t : ℝ => a * t + b)) (x : Quadrant) (G : ℝ)
    (hG : Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 G)) :
    Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw ν) / (n : ℝ)) atTop
      (𝓝 (a * G + b * ((x.1 : ℝ) + (x.2 : ℝ)))) := by
  -- Normalized site count of the floored displacement tends to `x.1 + x.2`.
  have hlen := tendsto_floor_pair_length (x.1 : ℝ) (x.2 : ℝ) x.1.2 x.2.2
  have hlim := (hG.const_mul a).add (hlen.const_mul b)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [integral_lastPassage_affine_image μ ν hμ a b ha hν]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

/-- The expected-rate shape of the affine image law is `a * g x + b * (x.1 + x.2)`: if `g` and
`h` are the expected-rate shapes of `μ` and of its image under `t ↦ a * t + b` (`a ≥ 0`),
then `h x = a * g x + b * (x.1 + x.2)` at every point `x` of the quadrant. This is the
identity that the first step of Martin (2004), Lemma 4.5 needs, with the drift term kept. -/
theorem expected_rate_affine_image
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun t : ℝ => t) μ) (a b : ℝ) (ha : 0 ≤ a)
    (hν : ν = μ.map (fun t : ℝ => a * t + b)) (g h : Quadrant → ℝ)
    (hg : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x)))
    (hh : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw ν) / (n : ℝ)) atTop (𝓝 (h x))) :
    ∀ x : Quadrant, h x = a * g x + b * ((x.1 : ℝ) + (x.2 : ℝ)) := fun x =>
  tendsto_nhds_unique (hh x)
    (tendsto_expected_rate_affine_image μ ν hμ a b ha hν x (g x) (hg x))

end LPPDifferentiability
