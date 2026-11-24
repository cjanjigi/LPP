/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.Grid.GeneralEvents
public import Differentiability.FinalDraft.StairGeometry.Event
import Differentiability.FinalDraft.StairGeometry.Measurable
import LPP_Foundations.Model.Paths.Fintype
import LPP_Foundations.Probability.PassageMeasurable

/-! # The four conditions of the general-weight grid event -/

@[expose] public section

open MeasureTheory Set

namespace LPPDifferentiability

local notation "GridPath" => Σ u : Lattice, Σ d : ℕ × ℕ, Path u d

/-- The global weight condition for the selected paths in Appendix B,
`lem:stair-general` of `differentiability_final_draft.tex`. The path selector
reads the entire very-bad mask and the weight excludes the terminal vertex. -/
noncomputable def gridStaircaseWeightEvent
    (paths : (Lattice → Bool) → Finset GridPath) (T t Cm : ℝ) : Set Environment :=
  {ω | ∀ q ∈ paths (fun z => if ω z < -T then true else false),
    -2 * Cm * ((q.2.1.1 + q.2.1.2 : ℕ) : ℝ) - t / 2 ≤ pathWeight ω q.2.2}

/-- The literal four-way intersection for the specified staircase family
(`differentiability_final_draft.tex`, `rk:gridprob-general` and Appendix B item `ch:prob`).
The cutoff `J` changes the tested grid cells and leaves the selected family
at scale `k` unchanged. -/
noncomputable def generalGridGoodEventForPaths
    (paths : ℕ → (Lattice → Bool) → Finset GridPath)
    (a G K cstar A R C₁ ε₀ Cm : ℝ) (m : ℕ → ℕ) (k J K₁ K₂ K₃ : ℕ) :
    Set Environment :=
  let Q := StairGeometry.workingRegion a A R C₁ m k
  let T := StairGeometry.threshold ε₀ K₂ k
  let t := ε₀ * (2 : ℝ) ^ k / (k : ℝ)
  ((generalGridCellsGood a G K cstar A R k J (m k) ∩
      StairGeometry.goodEvent (StairGeometry.slopeCutoff a) K₁ K₃ T Q) ∩
      gridStaircaseWeightEvent (paths k) T t Cm) ∩ gridUpperCap Q t

/-- The weight condition on a measurable finite path selection is measurable
(`differentiability_final_draft.tex`, `lem:stair-general` and Appendix B item U5). -/
theorem measurableSet_gridStaircaseWeightEvent
    (paths : (Lattice → Bool) → Finset GridPath)
    (hpaths : ∀ P, MeasurableSet {b | paths b = P}) (T t Cm : ℝ) :
    MeasurableSet (gridStaircaseWeightEvent paths T t Cm) := by
  let mask (ω : Environment) (z : Lattice) := if ω z < -T then true else false
  have hmask : Measurable mask := Measurable.of_eval fun z =>
    Measurable.ite (measurableSet_lt (measurable_pi_apply z) measurable_const)
      measurable_const measurable_const
  let _ : MeasurableSpace (Finset GridPath) := ⊤
  have hselect : Measurable paths := measurable_to_countable' hpaths
  have hmem (q : GridPath) : MeasurableSet {ω : Environment | q ∈ paths (mask ω)} :=
    (hselect.comp hmask) (t := {P | q ∈ P}) trivial
  have heq : gridStaircaseWeightEvent paths T t Cm =
      ⋂ q : GridPath, {ω : Environment | q ∈ paths (mask ω)}ᶜ ∪
        {ω : Environment | -2 * Cm * ((q.2.1.1 + q.2.1.2 : ℕ) : ℝ) - t / 2 ≤
          pathWeight ω q.2.2} := by
    ext ω
    simp only [gridStaircaseWeightEvent, mask, mem_iInter, mem_union, mem_compl_iff, mem_ofPred_eq]
    exact forall_congr' fun q => imp_iff_not_or
  rw [heq]
  exact MeasurableSet.iInter fun q => (hmem q).compl.union
    (measurableSet_le measurable_const (measurable_pathWeight q.2.2))

/-- Every component of the general grid event is measurable
(Appendix B item `ch:prob`). -/
theorem measurableSet_generalGridGoodEventForPaths
    (paths : ℕ → (Lattice → Bool) → Finset GridPath)
    (hpaths : ∀ k P, MeasurableSet {b | paths k b = P})
    (a G K cstar A R C₁ ε₀ Cm : ℝ) (m : ℕ → ℕ) (k J K₁ K₂ K₃ : ℕ) :
    MeasurableSet (generalGridGoodEventForPaths paths a G K cstar A R C₁ ε₀ Cm m k J K₁ K₂ K₃) := by
  let T := StairGeometry.threshold ε₀ K₂ k
  let Q := StairGeometry.workingRegion a A R C₁ m k
  have hsigma : StairGeometry.badSiteSigma T ≤ (inferInstance : MeasurableSpace Environment) := by
    apply MeasurableSpace.generateFrom_le
    rintro _ ⟨z, rfl⟩
    exact measurableSet_lt (measurable_pi_apply z) measurable_const
  have hgeo : MeasurableSet (StairGeometry.goodEvent (StairGeometry.slopeCutoff a) K₁ K₃ T Q) :=
    hsigma _ (StairGeometry.measurableSet_goodEvent (StairGeometry.slopeCutoff a) T K₁ K₃ Q)
  unfold generalGridGoodEventForPaths
  exact (((measurableSet_generalGridCellsGood a G K cstar A R k J (m k)).inter hgeo).inter
    (measurableSet_gridStaircaseWeightEvent (paths k) (hpaths k) _ _ _)).inter
    (measurableSet_gridUpperCap _ _)

end LPPDifferentiability
