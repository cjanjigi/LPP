/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Model.LastPassage.Translate
public import LPP_Foundations.Probability.TranslationEquiv
public import LPP_Foundations.Model.LastPassage.UniformShapeAllStarts
public import Martin2004.Shape.ExpectedRateUniform
import Mathlib.Tactic

/-! Normalized expected-rate shape at every fixed lattice start. -/

public section

open MeasureTheory Filter Set LPPDifferentiability
open scoped ENNReal NNReal Topology

namespace LPP

/-- The uniform origin shape estimate gives normalized passage convergence
from every fixed lattice start; see Georgiou–Rassoul-Agha–Seppäläinen,
arXiv:1510.00860v2, Theorem 4.3. -/
theorem ae_normalized_passage_shape_all_starts
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ x : Lattice, ∀ d : ℕ → ℕ × ℕ,
      (∀ n, (d n).1 + (d n).2 = n) →
      Tendsto (fun n => lastPassage ω x (d n) / (n : ℝ) -
        g (Real.toNNReal (((d n).1 : ℝ) / (n : ℝ)),
          Real.toNNReal (1 - ((d n).1 : ℝ) / (n : ℝ)))) atTop (𝓝 0) := by
  classical
  -- Martin's actual uniform shape theorem supplies the shared origin event and homogeneity.
  obtain ⟨_, hhom, hshape⟩ := ae_uniform_of_isExpectedRateShape μ hneg hpos hg

  -- Transfer the actual origin event to all fixed starts.
  have hAllStarts : ∀ᵐ ω ∂environmentLaw μ, ∀ x : Lattice,
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
        N ≤ z.1 + z.2 →
        |lastPassage ω x z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
          ε * ((z.1 + z.2 : ℕ) : ℝ) := by
    exact ae_uniform_passage_shape_all_starts_of_origin μ g hshape

  filter_upwards [hAllStarts] with ω hω
  intro x d hlength
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := hω x (ε / 2) (by positivity)
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left 1 N).trans hn
  have hnN : N ≤ n := (le_max_right 1 N).trans hn
  have hnNat : 0 < n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnNat
  have hlengthN : (d n).1 + (d n).2 = n := hlength n
  have hlengthR : ((d n).1 : ℝ) + ((d n).2 : ℝ) = (n : ℝ) := by
    exact_mod_cast hlengthN
  have hthreshold : N ≤ (d n).1 + (d n).2 := by
    rw [hlengthN]
    exact hnN
  have hshapeBound := hN (d n) hthreshold

  -- Homogeneity identifies the normalized endpoint with the literal target coordinates.
  let c : ℝ≥0 := 1 / (n : ℝ≥0)
  let v : Quadrant := (((d n).1 : ℝ≥0), ((d n).2 : ℝ≥0))
  let q : Quadrant :=
    (Real.toNNReal (((d n).1 : ℝ) / (n : ℝ)),
      Real.toNNReal (1 - ((d n).1 : ℝ) / (n : ℝ)))
  have hc : (c : ℝ) = 1 / (n : ℝ) := by simp [c]
  have hfirstNonneg : 0 ≤ ((d n).1 : ℝ) / (n : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hnpos.le
  have hsecondRatio : ((d n).2 : ℝ) / (n : ℝ) =
      1 - ((d n).1 : ℝ) / (n : ℝ) := by
    field_simp [ne_of_gt hnpos]
    linarith [hlengthR]
  have hsecondNonneg : 0 ≤ 1 - ((d n).1 : ℝ) / (n : ℝ) := by
    rw [← hsecondRatio]
    exact div_nonneg (Nat.cast_nonneg _) hnpos.le
  have hscale : c • v = q := by
    apply Prod.ext
    · apply NNReal.coe_injective
      change (c : ℝ) * ((d n).1 : ℝ) =
        ((Real.toNNReal (((d n).1 : ℝ) / (n : ℝ)) : ℝ≥0) : ℝ)
      rw [hc, Real.coe_toNNReal _ hfirstNonneg]
      field_simp [ne_of_gt hnpos]
    · apply NNReal.coe_injective
      change (c : ℝ) * ((d n).2 : ℝ) =
        ((Real.toNNReal (1 - ((d n).1 : ℝ) / (n : ℝ)) : ℝ≥0) : ℝ)
      rw [hc, Real.coe_toNNReal _ hsecondNonneg, ← hsecondRatio]
      field_simp [ne_of_gt hnpos]
  have hshapeScale : g q =
      g (((d n).1 : ℝ≥0), ((d n).2 : ℝ≥0)) / (n : ℝ) := by
    calc
      g q = g (c • v) := by rw [hscale]
      _ = (c : ℝ) * g v := hhom c v
      _ = g (((d n).1 : ℝ≥0), ((d n).2 : ℝ≥0)) / (n : ℝ) := by
        rw [hc]
        dsimp [v]
        ring

  have hnormalized :
      lastPassage ω x (d n) / (n : ℝ) - g q =
        (lastPassage ω x (d n) -
          g (((d n).1 : ℝ≥0), ((d n).2 : ℝ≥0))) / (n : ℝ) := by
    rw [hshapeScale]
    ring
  have habsNormalized :
      |lastPassage ω x (d n) / (n : ℝ) - g q| =
        |lastPassage ω x (d n) -
          g (((d n).1 : ℝ≥0), ((d n).2 : ℝ≥0))| / (n : ℝ) := by
    rw [hnormalized, abs_div, abs_of_pos hnpos]
  have herror :
      |lastPassage ω x (d n) -
        g (((d n).1 : ℝ≥0), ((d n).2 : ℝ≥0))| ≤
        (ε / 2) * (n : ℝ) := by
    calc
      |lastPassage ω x (d n) -
        g (((d n).1 : ℝ≥0), ((d n).2 : ℝ≥0))| ≤
          (ε / 2) * ((d n).1 + (d n).2 : ℕ) := hshapeBound
      _ = (ε / 2) * (n : ℝ) := by rw [hlengthN]
  have hsmall : |lastPassage ω x (d n) / (n : ℝ) - g q| ≤ ε / 2 := by
    rw [habsNormalized]
    exact (div_le_iff₀ hnpos).2 herror
  have hlt : |lastPassage ω x (d n) / (n : ℝ) - g q| < ε := by
    exact lt_of_le_of_lt hsmall (by linarith)
  simpa [q, Real.dist_eq] using hlt

end LPP

end
