/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.Probability.RareFastCrossings
public import LPP_Foundations.Statements.ShapeDefinitions
import Differentiability.Model.Paths.TransverseStaircase
import Differentiability.Probability.RarefastTranslation
import LPP_Foundations.Probability.PassageMeasurable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The literal strip crossing and the real-center extension in Remark `rk:translate`
of the final differentiability draft. -/

@[expose] public section

open LPPStatements MeasureTheory Set
open scoped NNReal ENNReal

namespace LPPDifferentiability.FinalDraft

/-- The transverse coordinate in the direction `(a, 1 - a)`. -/
def stripTransverse (a : ℝ) (z : Lattice) : ℝ :=
  (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)

/-- Some crossing from level `I` to level `I+n`, entirely in the strip of half-width
`B` about `ρ`, has path weight above the given threshold on its displacement. -/
def stripCrossingEvent (a : ℝ) (I : ℤ) (ρ B : ℝ) (n : ℕ)
    (threshold : ℕ × ℕ → ℝ) : Set Environment :=
  {ω | ∃ u : Lattice, u.1 + u.2 = I ∧ ∃ d : ℕ × ℕ, d.1 + d.2 = n ∧ ∃ p : Path u d,
    (∀ i, |stripTransverse a (p.vertex i) - ρ| ≤ B) ∧ threshold d < pathWeight ω p}

/-- The extreme support of the literal profile, with `false` denoting the left slope
and `true` the right slope. -/
noncomputable def crossingSupport (g : Quadrant → ℝ) (a : ℝ) (right : Bool)
    (d : ℕ × ℕ) : ℝ :=
  let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
  let slope := if right then derivWithin H (Ioi 0) 0 else derivWithin H (Iio 0) 0
  H 0 * ((d.1 : ℝ) + (d.2 : ℝ)) + slope * stripTransverse a ((d.1 : ℤ), (d.2 : ℤ))

/-- The event uses a countable family of deterministic paths and measurable path weights. -/
theorem measurableSet_stripCrossingEvent (a : ℝ) (I : ℤ) (ρ B : ℝ) (n : ℕ)
    (threshold : ℕ × ℕ → ℝ) : MeasurableSet (stripCrossingEvent a I ρ B n threshold) := by
  apply measurableSet_setOfPred.mpr
  refine Measurable.exists fun u => Measurable.and measurable_const ?_
  refine Measurable.exists fun d => Measurable.and measurable_const ?_
  refine Measurable.exists fun p => Measurable.and measurable_const ?_
  exact measurableSet_setOfPred.mp (measurableSet_lt measurable_const (measurable_pathWeight p))

private theorem path_end_sub_start {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    p.vertex (Fin.last (d.1 + d.2)) - u = ((d.1 : ℤ), (d.2 : ℤ)) := by
  rw [p.finish]
  simp

/-- A lattice-centered crossing event has the same probability as its translate to
level zero and transverse center zero, with the same displacement and weight test. -/
theorem measureReal_stripCrossingEvent_translate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a B : ℝ) (n : ℕ) (v : Lattice) (threshold : ℕ × ℕ → ℝ) :
    (environmentLaw μ).real
        (stripCrossingEvent a (v.1 + v.2) (stripTransverse a v) B n threshold) =
      (environmentLaw μ).real (stripCrossingEvent a 0 0 B n threshold) := by
  simpa only [stripCrossingEvent, stripTransverse, path_end_sub_start, Int.toNat_natCast, sub_zero]
    using measureReal_strip_crossing_translate μ a B n v
      (fun z w => threshold (z.1.toNat, z.2.toNat) < w)

/-- On every signed level, the lattice point immediately below the real center is
within one transverse unit. The wider strip contains the same crossing path without
changing its endpoints or its weight. -/
theorem exists_lattice_center_stripCrossing_subset (a ρ : ℝ) (I : ℤ) :
    ∃ v : Lattice, v.1 + v.2 = I ∧ |stripTransverse a v - ρ| ≤ 1 ∧
      ∀ (R s : ℝ) (n : ℕ) (threshold : ℕ × ℕ → ℝ), 1 ≤ s →
        stripCrossingEvent a I ρ (R * s) n threshold ⊆
          stripCrossingEvent a I (stripTransverse a v) ((R + 1) * s) n threshold := by
  let j : ℤ := ⌊ρ + a * (I : ℝ)⌋
  let v : Lattice := (j, I - j)
  have hfloor := (transverse_interval_iff_floor a ρ j I).mpr rfl
  have hcenter : |stripTransverse a v - ρ| ≤ 1 := by
    change |(1 - a) * (j : ℝ) - a * ((I - j : ℤ) : ℝ) - ρ| ≤ 1
    exact abs_le.mpr ⟨by linarith [hfloor.1], by linarith [hfloor.2]⟩
  refine ⟨v, by simp [v], hcenter, ?_⟩
  intro R s n threshold hs ω
  rintro ⟨u, hu, d, hd, p, hstrip, hweight⟩
  refine ⟨u, hu, d, hd, p, fun i => ?_, hweight⟩
  calc
    |stripTransverse a (p.vertex i) - stripTransverse a v|
      ≤ |stripTransverse a (p.vertex i) - ρ| + |ρ - stripTransverse a v| := abs_sub_le _ _ _
    _ ≤ R * s + 1 := add_le_add (hstrip i) (by rwa [abs_sub_comm])
    _ ≤ (R + 1) * s := by linarith

/-- Proposition `prop:rarefast` written on the literal strip crossing event. -/
theorem rarefast_strip_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : HasNegativePartMomentAbove μ 1) (hpos : HasSqrtUpperTail μ)
    (g : Quadrant → ℝ) (hg : IsShapeFunction μ g) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) (right : Bool) :
    ∀ b : ℝ, 0 < b → ∃ s₀ : ℝ, ∀ (s : ℝ) (n : ℕ), s₀ ≤ s →
      (environmentLaw μ).real
        (stripCrossingEvent a 0 0 (R * s) n (fun d => crossingSupport g a right d + ε * s)) < b := by
  intro b hb
  obtain ⟨hgcont, hghom, hgconc, hgshape⟩ := hg
  let σ : ℝ := if right then 1 else -1
  have hσ : σ = 1 ∨ σ = -1 := by cases right <;> simp [σ]
  obtain ⟨s₀, hs₀⟩ := rarefast_uniform μ hneg hpos g hgcont hghom hgconc
    ((approximatesLastPassage_iff_positive_threshold μ g).mp hgshape)
    a ha₀ ha₁ R ε σ hR hε hσ b hb
  refine ⟨s₀, fun s n hs => (measureReal_mono ?_).trans_lt (hs₀ s n hs)⟩
  intro ω
  rintro ⟨u, hu, d, hd, p, hstrip, hweight⟩
  refine ⟨u, hu, d, hd, p, ?_, ?_⟩
  · simpa only [stripTransverse, sub_zero] using hstrip
  · have hdefect : crossingSupport g a right d - pathWeight ω p < -(ε * s) := by
      change crossingSupport g a right d + ε * s < pathWeight ω p at hweight
      linarith
    rw [path_end_sub_start]
    cases right
    · simpa [crossingSupport, stripTransverse, σ, show (-1 : ℝ) ≠ 1 by norm_num] using hdefect
    · simpa [crossingSupport, stripTransverse, σ] using hdefect

/-- Remark `rk:translate`. One cutoff works for every length, signed start level,
and real transverse center. Lattice translation uses half-width `(R + 1) * s`. -/
theorem rarefast_real_center_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : HasNegativePartMomentAbove μ 1) (hpos : HasSqrtUpperTail μ)
    (g : Quadrant → ℝ) (hg : IsShapeFunction μ g) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) (right : Bool) :
    ∀ b : ℝ, 0 < b → ∃ s₀ : ℝ, 1 ≤ s₀ ∧
      ∀ (s : ℝ) (n : ℕ) (I : ℤ) (ρ : ℝ), s₀ ≤ s →
        (environmentLaw μ).real
          (stripCrossingEvent a I ρ (R * s) n (fun d => crossingSupport g a right d + ε * s)) < b := by
  intro b hb
  obtain ⟨s₀, hs₀⟩ := rarefast_strip_uniform μ hneg hpos g hg a ha₀ ha₁
    (R + 1) ε (by linarith) hε right b hb
  refine ⟨max s₀ 1, le_max_right _ _, fun s n I ρ hs => ?_⟩
  obtain ⟨v, hlevel, -, hsubset⟩ := exists_lattice_center_stripCrossing_subset a ρ I
  refine (measureReal_mono (hsubset R s n _ ((le_max_right _ _).trans hs))).trans_lt ?_
  rw [← hlevel, measureReal_stripCrossingEvent_translate]
  exact hs₀ s n ((le_max_left _ _).trans hs)

end LPPDifferentiability.FinalDraft
