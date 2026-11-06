/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.UniformShapeProbability
public import Differentiability.Probability.TravelPieceEvents
public import LPP_Foundations.Model.Paths.FloorSegment
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Probability of the floor pieces in the travel proof

This file gives the probability estimate for each piece of a floor segment, which
the travel estimate combines over the pieces.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace LPPDifferentiability

private theorem floor_piece_probability_parameters
    (d : ℕ × ℕ) (B j : ℕ) (hB : 1 ≤ B)
    (D η s : ℝ) (hD : 1 ≤ D) (hη : 0 < η)
    (hs : 3 * (B : ℝ) ≤ s)
    (hd : s ≤ ((d.1 + d.2 : ℕ) : ℝ))
    (hdD : ((d.1 + d.2 : ℕ) : ℝ) ≤ D * s) :
    let Δ : ℕ × ℕ :=
      (((j + 1) * d.1 / B - j * d.1 / B),
       ((j + 1) * d.2 / B - j * d.2 / B))
    1 ≤ s / (B : ℝ) - 2 ∧
      s / (B : ℝ) - 2 ≤ ((Δ.1 + Δ.2 : ℕ) : ℝ) ∧
      η / (4 * D) * ((Δ.1 + Δ.2 : ℕ) : ℝ) ≤ η * s / (2 * (B : ℝ)) := by
  dsimp only
  have hBr : 0 < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hDr : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hs0 : 0 ≤ s := (by positivity : (0 : ℝ) ≤ 3 * (B : ℝ)).trans hs
  have hround := floorSegment_increment_bounds d B j hB
  dsimp only at hround
  simp only [Nat.cast_add] at hround ⊢
  have hdivlo : s / (B : ℝ) ≤ ((d.1 : ℝ) + (d.2 : ℝ)) / (B : ℝ) := by
    simpa only [Nat.cast_add] using div_le_div_of_nonneg_right hd hBr.le
  have hupp :
      (((j + 1) * d.1 / B - j * d.1 / B : ℕ) : ℝ) +
        (((j + 1) * d.2 / B - j * d.2 / B : ℕ) : ℝ) ≤ D * s / (B : ℝ) + 2 := by
    have hdivhi : ((d.1 : ℝ) + (d.2 : ℝ)) / (B : ℝ) ≤ D * s / (B : ℝ) := by
      simpa only [Nat.cast_add] using div_le_div_of_nonneg_right hdD hBr.le
    linarith only [hround.2.2, hdivhi]
  have hsmall : 2 * (B : ℝ) ≤ D * s := by nlinarith only [hs, hD, hs0]
  have herr : η / (4 * D) * (D * s / (B : ℝ) + 2) ≤
      η * s / (2 * (B : ℝ)) := by
    have hi : η / (4 * D) * (D * s / (B : ℝ) + 2) =
        η * s / (4 * (B : ℝ)) + η / (2 * D) := by field_simp [ne_of_gt hDr, ne_of_gt hBr]; ring
    have hsecond : η / (2 * D) ≤ η * s / (4 * (B : ℝ)) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * D)
        (by positivity : 0 < 4 * (B : ℝ))).2
      nlinarith only [mul_le_mul_of_nonneg_left hsmall hη.le]
    rw [hi]
    calc
      η * s / (4 * (B : ℝ)) + η / (2 * D) ≤
          η * s / (4 * (B : ℝ)) + η * s / (4 * (B : ℝ)) := by linarith only [hsecond]
      _ = η * s / (2 * (B : ℝ)) := by ring
  refine ⟨?_, ?_, (mul_le_mul_of_nonneg_left hupp (by positivity)).trans herr⟩
  · have hdiv : 3 ≤ s / (B : ℝ) := (le_div_iff₀ hBr).2 hs
    linarith only [hdiv]
  · linarith only [hdivlo, hround.2.1]

private theorem exists_piece_probability_of_uniform
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ)
    (huniform : ∀ ε : ℝ, 0 < ε → ∃ p : ℝ → ℝ,
      (∀ s, 0 ≤ p s ∧ p s ≤ 1) ∧ Tendsto p atTop (𝓝 1) ∧
      ∀ (s : ℝ) (u : Lattice) (d : ℕ × ℕ), 1 ≤ s →
        s ≤ ((d.1 + d.2 : ℕ) : ℝ) →
        p s ≤ (environmentLaw μ).real {ω : Environment |
          |lastPassage ω u d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
            ε * ((d.1 + d.2 : ℕ) : ℝ)})
    (D : ℝ) (hD : 1 ≤ D) (B : ℕ) (hB : 1 ≤ B) (η : ℝ) (hη : 0 < η) :
    ∃ p : ℝ → ℝ, (∀ s, 0 ≤ p s ∧ p s ≤ 1) ∧ Tendsto p atTop (𝓝 1) ∧
      ∀ (s : ℝ) (u : Lattice) (d : ℕ × ℕ), 3 * (B : ℝ) ≤ s →
        s ≤ ((d.1 + d.2 : ℕ) : ℝ) → ((d.1 + d.2 : ℕ) : ℝ) ≤ D * s →
        let k : ℕ → ℕ × ℕ := fun j => (j * d.1 / B, j * d.2 / B)
        let Δ : Fin B → ℕ × ℕ := fun j =>
          ((k (j.val + 1)).1 - (k j.val).1, (k (j.val + 1)).2 - (k j.val).2)
        let U : Fin B → Lattice := fun j => u + (((k j.val).1 : ℤ), ((k j.val).2 : ℤ))
        MeasurableSet {ω : Environment | ∀ j : Fin B,
          g (((Δ j).1 : ℝ≥0), ((Δ j).2 : ℝ≥0)) - η * s / (2 * (B : ℝ)) ≤
            lastPassage ω (U j) (Δ j)} ∧
        p s ≤ (environmentLaw μ).real {ω : Environment | ∀ j : Fin B,
          g (((Δ j).1 : ℝ≥0), ((Δ j).2 : ℝ≥0)) - η * s / (2 * (B : ℝ)) ≤
            lastPassage ω (U j) (Δ j)} := by
  have hBr : 0 < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  obtain ⟨p0, hp0, ht0, hbound⟩ := huniform (η / (4 * D)) (by positivity)
  let p : ℝ → ℝ := fun s => max 0 (1 - (B : ℝ) * (1 - p0 (s / (B : ℝ) - 2)))
  refine ⟨p, ?_, ?_, ?_⟩
  · intro s
    refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
    have h := (hp0 (s / (B : ℝ) - 2)).2
    nlinarith only [h, hBr]
  · have htR : Tendsto (fun s : ℝ => s / (B : ℝ) - 2) atTop atTop :=
      by
        simpa only [sub_eq_add_neg, id_eq] using
          tendsto_atTop_add_const_right atTop (-2 : ℝ) (tendsto_id.atTop_div_const hBr)
    have ht : Tendsto p atTop (𝓝 (max (0 : ℝ) (1 - (B : ℝ) * (1 - 1)))) := tendsto_const_nhds.max
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul
        (tendsto_const_nhds.sub (ht0.comp htR))))
    simpa only [sub_self, mul_zero, sub_zero, max_eq_right zero_le_one] using ht
  · intro s u d hs hd hdD
    dsimp only
    let k : ℕ → ℕ × ℕ := fun j => (j * d.1 / B, j * d.2 / B)
    let Δ : Fin B → ℕ × ℕ := fun j =>
      ((k (j.val + 1)).1 - (k j.val).1, (k (j.val + 1)).2 - (k j.val).2)
    let U : Fin B → Lattice := fun j => u + (((k j.val).1 : ℤ), ((k j.val).2 : ℤ))
    let E : Fin B → Set Environment := fun j => {ω |
      g (((Δ j).1 : ℝ≥0), ((Δ j).2 : ℝ≥0)) - η * s / (2 * (B : ℝ)) ≤
        lastPassage ω (U j) (Δ j)}
    have hm (j : Fin B) : MeasurableSet (E j) :=
      measurableSet_le measurable_const (measurable_lastPassage (U j) (Δ j))
    have hq (j : Fin B) : p0 (s / (B : ℝ) - 2) ≤ (environmentLaw μ).real (E j) := by
      have hpar := floor_piece_probability_parameters d B j.val hB D η s hD hη hs hd hdD
      change 1 ≤ s / (B : ℝ) - 2 ∧
        s / (B : ℝ) - 2 ≤ (((Δ j).1 + (Δ j).2 : ℕ) : ℝ) ∧
        η / (4 * D) * (((Δ j).1 + (Δ j).2 : ℕ) : ℝ) ≤
          η * s / (2 * (B : ℝ)) at hpar
      apply (hbound _ (U j) (Δ j) hpar.1 hpar.2.1).trans
      apply measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      have habs := (abs_le.mp (show |lastPassage ω (U j) (Δ j) - g (((Δ j).1 : ℝ≥0), ((Δ j).2 : ℝ≥0))| ≤ η / (4 * D) * (((Δ j).1 + (Δ j).2 : ℕ) : ℝ) from hω)).1
      change g _ - η * s / (2 * (B : ℝ)) ≤ lastPassage ω (U j) (Δ j)
      linarith only [habs, hpar.2.2]
    constructor
    · change MeasurableSet {ω | ∀ j, ω ∈ E j}
      simp only [ofPred_forall]
      exact MeasurableSet.iInter hm
    · have hfinite := finite_intersection_probability_lower_bound (environmentLaw μ) B E
        (p0 (s / (B : ℝ) - 2)) hm hq
      change p s ≤ (environmentLaw μ).real {ω | ∀ j, ω ∈ E j}
      simpa only [p, ofPred_forall, ofPred_mem_eq] using hfinite

/-- The same unique shape supplies a probability tending to one for all floor
pieces, uniformly over deterministic signed starts and endpoints. The event
includes the maximizing families of paths and keeps the terminal exclusion. -/
theorem exists_unique_shape_with_travel_piece_probability
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! g : Quadrant → ℝ,
      Continuous g ∧
      (∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        (a : ℝ) * g x + (b : ℝ) * g y ≤
          g (a * x.1 + b * y.1, a * x.2 + b * y.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
            ε * ((d.1 + d.2 : ℕ) : ℝ)) ∧
      (∀ (D : ℝ), 1 ≤ D → ∀ (B : ℕ), 1 ≤ B → ∀ (η : ℝ), 0 < η →
        ∃ p : ℝ → ℝ, (∀ s, 0 ≤ p s ∧ p s ≤ 1) ∧ Tendsto p atTop (𝓝 1) ∧
        ∀ (s : ℝ) (u : Lattice) (d : ℕ × ℕ), 3 * (B : ℝ) ≤ s →
          s ≤ ((d.1 + d.2 : ℕ) : ℝ) → ((d.1 + d.2 : ℕ) : ℝ) ≤ D * s →
          let k : ℕ → ℕ × ℕ := fun j => (j * d.1 / B, j * d.2 / B)
          let Δ : Fin B → ℕ × ℕ := fun j =>
            ((k (j.val + 1)).1 - (k j.val).1, (k (j.val + 1)).2 - (k j.val).2)
          let U : Fin B → Lattice := fun j => u + (((k j.val).1 : ℤ), ((k j.val).2 : ℤ))
          MeasurableSet {ω : Environment | ∀ j : Fin B,
            g (((Δ j).1 : ℝ≥0), ((Δ j).2 : ℝ≥0)) - η * s / (2 * (B : ℝ)) ≤
              lastPassage ω (U j) (Δ j)} ∧
          p s ≤ (environmentLaw μ).real {ω : Environment | ∀ j : Fin B,
            g (((Δ j).1 : ℝ≥0), ((Δ j).2 : ℝ≥0)) - η * s / (2 * (B : ℝ)) ≤
              lastPassage ω (U j) (Δ j)} ∧
          MeasurableSet {ω : Environment | ∃ paths : (j : Fin B) → Path (U j) (Δ j),
            ∀ j, pathWeight ω (paths j) = lastPassage ω (U j) (Δ j) ∧
              g (((Δ j).1 : ℝ≥0), ((Δ j).2 : ℝ≥0)) - η * s / (2 * (B : ℝ)) ≤
                pathWeight ω (paths j)} ∧
          p s ≤ (environmentLaw μ).real {ω : Environment |
            ∃ paths : (j : Fin B) → Path (U j) (Δ j),
              ∀ j, pathWeight ω (paths j) = lastPassage ω (U j) (Δ j) ∧
                g (((Δ j).1 : ℝ≥0), ((Δ j).2 : ℝ≥0)) - η * s / (2 * (B : ℝ)) ≤
                  pathWeight ω (paths j)}) := by
  obtain ⟨g, hg, _hu⟩ :=
    exists_unique_shape_with_uniform_probability_of_negative_moment_and_positive_tail μ hneg hpos
  obtain ⟨_g0, _hg0, huniq⟩ := exists_unique_shape_of_negative_moment_and_positive_tail μ hneg hpos
  refine ⟨g, ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, ?_⟩, ?_⟩
  · intro D hD B hB η hη
    obtain ⟨p, hp, ht, hpieces⟩ := exists_piece_probability_of_uniform μ g hg.2.2.2.2 D hD B hB η hη
    refine ⟨p, hp, ht, ?_⟩
    intro s u d hs hd hdD
    dsimp only
    obtain ⟨hm, hb⟩ := hpieces s u d hs hd hdD
    refine ⟨hm, hb, measurableSet_exists_maximizing_family B _ _ _, ?_⟩
    simpa only [exists_maximizing_family_iff] using hb
  · intro f hf
    exact (huniq f ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩).trans
      (huniq g ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1⟩).symm

end LPPDifferentiability
