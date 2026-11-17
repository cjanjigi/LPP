/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.LatticeFixedBoxCenteredDisplacements
import ProbabilityBasics.Analysis.FloorBoxCardinality
import Mathlib.Tactic

/-! Generic action mesh centered displacement averages. -/
@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped BigOperators Topology
namespace LPP.Busemann

/-- The canonical centered displacements for a lattice action have vanishing mesh-cell averages, as in JR arXiv:1810.03580v3, Appendix B, Lemma B.6. -/
theorem ae_tendsto_mesh_centered_cell_averages_of_action
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω)
    (hzero : ∀ s : Ω, T 0 s = s)
    (hadd : ∀ (z w : Lattice) (s : Ω), T (z + w) s = T z (T w s))
    (hShift : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (B : Lattice → Lattice → Ω → ℝ)
    (hB : is_shift_covariant_cocycle P T B)
    (hInt : ∀ x y, Integrable (B x y) P) :
    let mΩ0 : MeasurableSpace Ω := inferInstance
    let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
    letI : MeasurableSpace Ω := mΩ0
    let u : Fin 2 → Ω → ℝ :=
      fun i => P[B 0 (finiteEdgeStep i) | I]
    let coord : Fin 2 → Lattice → ℤ := fun i x => if i = 0 then x.1 else x.2
    let Fbar : Lattice → Ω → ℝ := fun x s =>
      B 0 x s - ∑ i : Fin 2, u i s * ((coord i x : ℤ) : ℝ)
    let δ : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
    let a : ℕ → ℕ → ℕ → ℤ := fun m k n =>
      ⌊(n : ℝ) * (k : ℝ) * δ m / 8⌋
    let R₁ : ℕ → ℕ → ℕ → Finset ℤ := fun m k n =>
      Finset.Ico (a m k n) (a m (k + 1) n)
    let R₂ : ℕ → (ℕ × ℕ) → ℕ → Finset Lattice := fun m k n =>
      (R₁ m k.1 n).product (R₁ m k.2 n)
    ∀ᵐ s ∂P,
      (∀ (m k : ℕ) (i : Fin 2), Tendsto (fun n : ℕ =>
        (∑ t ∈ R₁ m k n, Fbar (t • finiteEdgeStep i) s) /
          ((n : ℝ) * ((R₁ m k n).card : ℝ))) atTop (𝓝 0)) ∧
      (∀ (m : ℕ) (k : ℕ × ℕ), Tendsto (fun n : ℕ =>
        (∑ z ∈ R₂ m k n, Fbar z s) /
          ((n : ℝ) * ((R₂ m k n).card : ℝ))) atTop (𝓝 0)) := by
  classical
  let mΩ0 : MeasurableSpace Ω := inferInstance
  let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
  let : MeasurableSpace Ω := mΩ0
  let u : Fin 2 → Ω → ℝ := fun i => P[B 0 (finiteEdgeStep i) | I]
  let coord : Fin 2 → Lattice → ℤ := fun i x => if i = 0 then x.1 else x.2
  let Fbar : Lattice → Ω → ℝ := fun x s =>
    B 0 x s - ∑ i : Fin 2, u i s * ((coord i x : ℤ) : ℝ)
  let δ : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  let a : ℕ → ℕ → ℕ → ℤ := fun m k n => ⌊(n : ℝ) * (k : ℝ) * δ m / 8⌋
  let R₁ : ℕ → ℕ → ℕ → Finset ℤ := fun m k n => Finset.Ico (a m k n) (a m (k + 1) n)
  let R₂ : ℕ → (ℕ × ℕ) → ℕ → Finset Lattice := fun m k n =>
    (R₁ m k.1 n).product (R₁ m k.2 n)
  change ∀ᵐ s ∂P, (∀ (m k : ℕ) (i : Fin 2), Tendsto (fun n : ℕ =>
        (∑ t ∈ R₁ m k n, Fbar (t • finiteEdgeStep i) s) /
          ((n : ℝ) * ((R₁ m k n).card : ℝ))) atTop (𝓝 0)) ∧
      (∀ (m : ℕ) (k : ℕ × ℕ), Tendsto (fun n : ℕ =>
        (∑ z ∈ R₂ m k n, Fbar z s) /
          ((n : ℝ) * ((R₂ m k n).card : ℝ))) atTop (𝓝 0))
  let lo : ℕ → ℕ → ℝ := fun m k => (k : ℝ) * δ m / 8
  let hi : ℕ → ℕ → ℝ := fun m k => ((k + 1 : ℕ) : ℝ) * δ m / 8
  let low : ℕ → (ℕ × ℕ) → Fin 2 → ℝ := fun m k j =>
    if j = 0 then lo m k.1 else lo m k.2
  let high : ℕ → (ℕ × ℕ) → Fin 2 → ℝ := fun m k j =>
    if j = 0 then hi m k.1 else hi m k.2
  have hδ (m : ℕ) : 0 < δ m := by dsimp [δ]; positivity
  have hlo (m k : ℕ) : 0 ≤ lo m k := by dsimp [lo]; positivity
  have hhi (m k : ℕ) : lo m k < hi m k := by
    dsimp [lo, hi]
    push_cast
    have hh := hδ m
    linarith
  have hlow (m : ℕ) (k : ℕ × ℕ) (j : Fin 2) : 0 ≤ low m k j := by
    dsimp [low]
    split_ifs <;> exact hlo _ _
  have hhigh (m : ℕ) (k : ℕ × ℕ) (j : Fin 2) : low m k j < high m k j := by
    dsimp [low, high]
    split_ifs <;> exact hhi _ _
  have hfloor (m k n : ℕ) : a m k n = ((⌊(n : ℝ) * lo m k⌋₊ : ℕ) : ℤ) := by
    dsimp only [a, lo]
    have hnonneg : 0 ≤ (n : ℝ) * (k : ℝ) * δ m / 8 := by positivity
    rw [← Int.natCast_floor_eq_floor hnonneg]
    congr 1
    ring
  have hcell (m k n : ℕ) : R₁ m k n =
      Finset.Ico ((⌊(n : ℝ) * lo m k⌋₊ : ℕ) : ℤ)
        ((⌊(n : ℝ) * hi m k⌋₊ : ℕ) : ℤ) := by
    dsimp only [R₁, hi]
    rw [hfloor m k n, hfloor m (k + 1) n]
  have hwidth (m k : ℕ) : hi m k - lo m k = δ m / 8 := by
    dsimp [hi, lo]
    push_cast
    ring
  have hcard1 (m k : ℕ) : Tendsto (fun n : ℕ => ((R₁ m k n).card : ℝ) / (n : ℝ))
      atTop (𝓝 (δ m / 8)) := by
    simpa only [← hcell, hwidth] using
      ProbabilityBasics.tendsto_floor_interval_card_div (lo m k) (hi m k) (hlo m k) (hhi m k)
  have hcard2 (m : ℕ) (k : ℕ × ℕ) :
      Tendsto (fun n : ℕ => ((R₂ m k n).card : ℝ) / (n : ℝ)^2)
        atTop (𝓝 ((δ m / 8) * (δ m / 8))) := by
    have hh := ProbabilityBasics.tendsto_floor_rectangle_card_div_sq
      (low m k) (high m k) (hlow m k) (hhigh m k)
    simpa only [low, high, R₂, hcell, hwidth, zero_ne_one, one_ne_zero,
      ite_false, ite_true, ↓reduceIte] using hh
  have hX (z : Lattice) :
      z.1 • finiteEdgeStep ((Equiv.refl (Fin 2)) 0) +
        z.2 • finiteEdgeStep ((Equiv.refl (Fin 2)) 1) = z := by
    rcases z with ⟨x, y⟩
    simp [finiteEdgeStep]
  have hcommon : ∀ᵐ s ∂P, ∀ (m : ℕ) (k : ℕ × ℕ),
      (∀ i : Fin 2, Tendsto (fun n : ℕ =>
        (∑ t ∈ R₁ m k.1 n, Fbar (t • finiteEdgeStep i) s) / (n : ℝ)^2) atTop (𝓝 0)) ∧
      Tendsto (fun n : ℕ => (∑ z ∈ R₂ m k n, Fbar z s) / (n : ℝ)^3) atTop (𝓝 0) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro k
    have hh := ae_tendsto_fixed_box_centered_displacements_of_action P T hzero hadd hShift B hB hInt
      (low m k) (high m k) (hlow m k) (hhigh m k)
    filter_upwards [hh] with s hs
    constructor
    · intro i
      simpa only [low, high, ↓reduceIte, hcell] using hs.1 i
    · simpa only [low, high, zero_ne_one, one_ne_zero, ite_false, ite_true,
        ↓reduceIte, R₂, hcell, hX] using
        hs.2 (Equiv.refl (Fin 2))
  filter_upwards [hcommon] with s hs
  constructor
  · intro m k i
    have hnum := (hs m (k, k)).1 i
    have hden := hcard1 m k
    have hwidthpos : 0 < δ m / 8 := by positivity
    have hquot := hnum.div hden (ne_of_gt hwidthpos)
    have heq (n : ℕ) :
        ((∑ t ∈ R₁ m k n, Fbar (t • finiteEdgeStep i) s) / (n : ℝ)^2) /
          (((R₁ m k n).card : ℝ) / (n : ℝ)) =
        (∑ t ∈ R₁ m k n, Fbar (t • finiteEdgeStep i) s) /
          ((n : ℝ) * ((R₁ m k n).card : ℝ)) := by
      by_cases hn : (n : ℝ) = 0
      · simp [hn]
      by_cases hc : ((R₁ m k n).card : ℝ) = 0
      · simp [hc]
      field_simp [hn, hc]
    simpa only [zero_div] using hquot.congr' (Eventually.of_forall fun n => heq n)
  · intro m k
    have hnum := (hs m k).2
    have hden := hcard2 m k
    have hwidthpos : 0 < (δ m / 8) * (δ m / 8) := by positivity
    have hquot := hnum.div hden (ne_of_gt hwidthpos)
    have heq (n : ℕ) :
        ((∑ z ∈ R₂ m k n, Fbar z s) / (n : ℝ)^3) /
          (((R₂ m k n).card : ℝ) / (n : ℝ)^2) =
        (∑ z ∈ R₂ m k n, Fbar z s) /
          ((n : ℝ) * ((R₂ m k n).card : ℝ)) := by
      by_cases hn : (n : ℝ) = 0
      · simp [hn]
      by_cases hc : ((R₂ m k n).card : ℝ) = 0
      · simp [hc]
      field_simp [hn, hc]
    simpa only [zero_div] using hquot.congr' (Eventually.of_forall fun n => heq n)

end LPP.Busemann
