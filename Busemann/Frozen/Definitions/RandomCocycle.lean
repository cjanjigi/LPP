module

public import Busemann.Frozen.Definitions.Additive
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! A literal measurable shift-covariant additive random cocycle predicate. -/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- Definition 4.1: measurability, shift covariance, and additivity on every ordered lattice pair. -/
def is_shift_covariant_cocycle {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : Lattice → Ω → Ω)
    (B : Lattice → Lattice → Ω → ℝ) : Prop :=
  Measurable (fun p : (Lattice × Lattice) × Ω => B p.1.1 p.1.2 p.2) ∧
  (∀ x y z : Lattice, ∀ᵐ ω ∂P, B (x + z) (y + z) ω = B x y (T z ω)) ∧
  (∀ᵐ ω ∂P, is_additive (fun x y => B x y ω))

end LPP.Busemann
