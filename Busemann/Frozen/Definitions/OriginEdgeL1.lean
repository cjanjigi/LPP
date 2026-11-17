module

public import LPP_Foundations.Frozen.Model.Environment
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! The source L¹ condition on exactly the two origin edge increments. -/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- The L¹ clause after Definition 4.1: only the two origin edge increments are required. -/
def has_integrable_origin_edges {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Lattice → Lattice → Ω → ℝ) : Prop :=
  Integrable (fun ω => B 0 ((1 : ℤ), (0 : ℤ)) ω) P ∧
  Integrable (fun ω => B 0 ((0 : ℤ), (1 : ℤ)) ω) P

end LPP.Busemann
