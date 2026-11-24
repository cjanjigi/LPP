/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.CoarseCrossingBlocks
public import Differentiability.Probability.GridFineStaircaseFamily
public import LPP_Foundations.Model.Paths.HorizontalFirst
import Differentiability.Model.Paths.TransverseStaircase
import Lean.Elab.Tactic.Omega

/-! # Grid events for the differentiability paper

The fine event tests the deterministic floor staircases in one bin. The coarse event tests
the horizontal-first attachments and the crossing trials at fixed rounded centres.
-/

@[expose] public section

namespace LPPDifferentiability

/-- The point `ẑ(I, ρ)` of `stairdef`, on level `I` just below transverse coordinate `ρ`. -/
noncomputable def gridStaircasePoint (a ρ : ℝ) (I : ℤ) : Lattice :=
  let x : ℤ := ⌊ρ + a * (I : ℝ)⌋
  (x, I - x)

/-- The endpoint formula in `stairdef` is the unique site just below `ρ` on its level. -/
theorem eq_gridStaircasePoint_iff (a ρ : ℝ) (I : ℤ) (z : Lattice) :
    z = gridStaircasePoint a ρ I ↔
      z.1 + z.2 = I ∧ ρ - 1 < (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) ∧
        (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) ≤ ρ := by
  constructor
  · rintro rfl
    refine ⟨?_, (transverse_interval_iff_floor a ρ _ I).2 rfl⟩
    change ⌊ρ + a * (I : ℝ)⌋ + (I - ⌊ρ + a * (I : ℝ)⌋) = I
    omega
  · rintro ⟨hlevel, hlow, hupp⟩
    have h₂ : z.2 = I - z.1 := by omega
    have h₁ := (transverse_interval_iff_floor a ρ z.1 I).1
      (by simpa only [h₂] using And.intro hlow hupp)
    exact Prod.ext h₁ (by change z.2 = I - ⌊ρ + a * (I : ℝ)⌋; omega)

/-- Failure of the fine good event `eq:goodfine`, tested on each staircase in the bin.
The sum uses its collected sites, excluding the terminal vertex. -/
def fineGridFailure (a E t : ℝ) (I h : ℤ) (l w : ℕ) : Set Environment :=
  {ω | ∃ ρ : ℝ, (h : ℝ) * w ≤ ρ ∧ ρ < ((h : ℝ) + 1) * w ∧
    (∑ i ∈ Finset.range l, ω (gridStaircasePoint a ρ (I + (i : ℤ)))) < (l : ℝ) * E - t}

/-- The translated crossing event of `eq:crossblock` and `success55`. -/
def gridCrossingTrial (a G K w : ℝ) (I : ℤ) (l m : ℕ) (c : Lattice) : Set Environment :=
  {ω | ∃ (u : Lattice) (d : ℕ × ℕ) (x : Path u d),
    u.1 + u.2 = I + (m : ℤ) ∧ d.1 + d.2 = l - 2 * m ∧
    (∀ i, |(1 - a) * ((x.vertex i).1 : ℝ) - a * ((x.vertex i).2 : ℝ) -
      ((1 - a) * (c.1 : ℝ) - a * (c.2 : ℝ))| ≤ 8 * w) ∧
    G * ((l - 2 * m : ℕ) : ℝ) - K * w < pathWeight ω x}

/-- Failure of `eq:goodcoarse`. Every crossing trial fails, or a staircase of the bin and
its crossing blocks has weight below its threshold. The centres are fixed before observing
the weights. -/
def coarseGridFailure (a G E K t : ℝ) (I h : ℤ) (l m j w : ℕ) : Set Environment :=
  let c : Fin (j ^ 2) → Lattice := fun ν => coarseCrossingCentre a h w I m (ν.val + 1)
  (⋂ ν, (gridCrossingTrial a G K w I l m (c ν))ᶜ) ∪
    {ω | ∃ p : Lattice × (ℕ × ℕ), IsCoarseAttachmentStaircase a I l m j w h c p ∧
      pathWeight ω (horizontalFirst p.1 p.2) < ((p.2.1 + p.2.2 : ℕ) : ℝ) * E - t}

/-- The bounded good event at one grid cell in `eq:goodfine` and `eq:goodcoarse`. -/
noncomputable def boundedGridCellGood (a G E K t cstar : ℝ) (I h : ℤ) (l j w : ℕ) :
    Set Environment :=
  if 8 * (cstar * (j : ℝ) ^ 2 * (w : ℝ)) ≤ (l : ℝ) then
    (coarseGridFailure a G E K t I h l ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊ j w)ᶜ
  else
    (fineGridFailure a E t I h l w)ᶜ

/-- The event `G_{k,J}` of `eq:Gdef` for bounded weights. This is the intersection over the
scale indices, grid intervals and bins meeting the prescribed transverse range. -/
def boundedGridGoodEvent (a G E K t cstar A R : ℝ) (k J mk : ℕ) : Set Environment :=
  {ω | ∀ j : ℕ, J ≤ j → j ≤ ⌈((mk : ℝ) - 1) / 4⌉₊ →
    ∀ I : ℤ, ((2 ^ (mk - 4 * j - 1) : ℕ) : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * 2 ^ mk →
    ∀ h : ℤ, (∃ ρ : ℝ, (h : ℝ) * 2 ^ (k - j) ≤ ρ ∧
      ρ < ((h : ℝ) + 1) * 2 ^ (k - j) ∧ |ρ| ≤ R * 2 ^ k) →
    ω ∈ boundedGridCellGood a G E K t cstar I h (2 ^ (mk - 4 * j - 1)) j (2 ^ (k - j))}

end LPPDifferentiability
