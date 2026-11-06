/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.RealDirectionInfiniteLimit
public import Martin2004.Probability.ERealFloorRate
public import Martin2004.Probability.ERealFloorRateGeometry
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace LPPDifferentiability.Full

/-!
# Proposition 2.1 of Martin (2004) in full generality

The theorem here is the proof of the statement `martin_prop_2_1` in
`Frozen/Martin/Proposition21.lean` (Martin (2004), Proposition 2.1 for `d = 2`). The function `g`
is the extended-real limit of the expected floor rates. The finite and infinite cases give the
almost-sure and `L¹` clauses, the geometry of the expected rate gives homogeneity, symmetry and
superadditivity, and uniqueness holds because limits in `EReal` are unique.

## Main results

- `martin_prop_2_1`: existence and uniqueness of the extended-real shape function, with its
  limits and its homogeneity, symmetry and superadditivity.

## References

- J. B. Martin, *Limiting shape for directed percolation models*, Ann. Probab. 32 (2004),
  Proposition 2.1.
-/

/-- Martin (2004), Proposition 2.1 in its full generality, `d = 2`. If the weight has a finite
mean, there is exactly one extended-real function `g` on the closed quadrant such that, in every
real direction `x`, the normalized expected passage time `E T(⌊n x⌋)/n` and, almost surely, the
normalized passage time `T(⌊n x⌋)/n` converge to `g x`; the convergence also holds in `L¹`
whenever `g x` is finite; `g` is positively homogeneous, symmetric in the two coordinates and
superadditive. The value `+∞` is allowed. The paper calls these properties immediate from
Kingman's subadditive ergodic theorem; here directions that are not lattice points, and weights
of either sign, are treated explicitly. -/
theorem martin_prop_2_1
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) :
    ∃! g : Quadrant → EReal,
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (((∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ) : ℝ) : EReal)) atTop (𝓝 (g x))) ∧
      (∀ x : Quadrant, ∀ᵐ ω ∂environmentLaw μ, Tendsto (fun n : ℕ =>
        ((lastPassage ω 0 (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) /
          (n : ℝ) : ℝ) : EReal)) atTop (𝓝 (g x))) ∧
      (∀ x : Quadrant, g x ≠ ⊤ → Tendsto (fun n : ℕ => ∫ ω : Environment,
        |lastPassage ω 0 (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) /
          (n : ℝ) - (g x).toReal| ∂environmentLaw μ) atTop (𝓝 0)) ∧
      (∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = ((c : ℝ) : EReal) * g x) ∧
      (∀ x : Quadrant, g (x.2, x.1) = g x) ∧
      (∀ x y : Quadrant, g x + g y ≤ g (x.1 + y.1, x.2 + y.2)) := by
  -- the function `g`: the extended-real limit of the expected floor rates (clause (E) by
  -- construction)
  choose g hgE using expected_floor_rate_ereal_limit_exists μ hμ
  -- g never takes the value bottom
  have hbot : ∀ x : Quadrant, g x ≠ ⊥ := fun x =>
    (expected_floor_rate_ereal_bot_lt μ hμ x (g x) (hgE x)).ne'
  -- clause (AS): case split on g x = top
  have hAS : ∀ x : Quadrant, ∀ᵐ ω ∂environmentLaw μ, Tendsto (fun n : ℕ =>
      ((lastPassage ω 0 (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) /
        (n : ℝ) : ℝ) : EReal)) atTop (𝓝 (g x)) := by
    intro x
    by_cases htop : g x = ⊤
    · have hx := hgE x
      rw [htop] at hx ⊢
      exact tendsto_lastPassage_floor_ae_of_rate_top μ hμ x hx
    · obtain ⟨hae, -⟩ := tendsto_lastPassage_floor_ae_and_L1 μ hμ x (g x) (hgE x) htop
      filter_upwards [hae] with ω hω
      have hcast := EReal.tendsto_coe.mpr hω
      rwa [EReal.coe_toReal htop (hbot x)] at hcast
  -- clause (L1): the finite case
  have hL1 : ∀ x : Quadrant, g x ≠ ⊤ → Tendsto (fun n : ℕ => ∫ ω : Environment,
      |lastPassage ω 0 (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) /
        (n : ℝ) - (g x).toReal| ∂environmentLaw μ) atTop (𝓝 0) := fun x htop =>
    (tendsto_lastPassage_floor_ae_and_L1 μ hμ x (g x) (hgE x) htop).2
  -- clauses (H), (S), (SA): geometry of the expected rate
  have hsmul := ereal_expected_rate_smul μ hμ g hgE
  have hswap := ereal_expected_rate_swap μ hμ g hgE
  have hsuper := ereal_expected_rate_superadditive μ hμ g hgE
  -- existence with these clauses, and uniqueness: clause (E) determines g
  refine ⟨g, ⟨hgE, hAS, hL1, hsmul, hswap, hsuper⟩, fun g' hg' => ?_⟩
  funext x
  exact tendsto_nhds_unique (hg'.1 x) (hgE x)

end LPPDifferentiability.Full
