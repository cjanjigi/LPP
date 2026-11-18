/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.StrongExistence.Definitions.OneSidedLimits
public import Busemann.Frozen.StrongExistence.Definitions.SkorokhodRealization

/-! The clauses of Theorem `thm:stexist` for the tilt-indexed Busemann process.
The Lean predicate splits monotonicity into two components. The canonical
property adds Skorokhod realization and uniqueness. -/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- The five clauses of Theorem `thm:stexist` for the two tilt-indexed branches.

* No ± distinction at fixed h.
* Forward measurable Busemann function.
* Mean −h.
* Monotonicity, split into within-tilt order and strict cross-tilt order.
* Left and right continuity. -/
def IsTiltIndexedBusemannProcess (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Bm Bp : StrongField μ) : Prop :=
  BranchAgreement μ Bm Bp ∧ ForwardCoalescingClass μ Bm Bp ∧ MeanTilt μ Bm ∧
    WithinTiltOrder μ Bm Bp ∧ StrictCrossTiltOrder μ Bm Bp ∧ OneSidedLimits μ Bm Bp

/-- The process clauses at the same two branches, with monotonicity split into two components. -/
theorem is_tilt_indexed_busemann_process_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Bm Bp : StrongField μ) :
    IsTiltIndexedBusemannProcess μ Bm Bp ↔
      BranchAgreement μ Bm Bp ∧ ForwardCoalescingClass μ Bm Bp ∧ MeanTilt μ Bm ∧
        WithinTiltOrder μ Bm Bp ∧ StrictCrossTiltOrder μ Bm Bp ∧ OneSidedLimits μ Bm Bp :=
  Iff.rfl

/-- The canonical tilt-indexed Busemann process satisfies the clauses of Theorem `thm:stexist`,
has a Skorokhod realization, and agrees with every process satisfying those
clauses. For each comparison, one almost-sure event gives agreement of both
branches at every tilt and lattice pair. -/
def IsCanonicalBusemannProcess (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Bm Bp : StrongField μ) : Prop :=
  IsTiltIndexedBusemannProcess μ Bm Bp ∧
  SkorokhodRealization μ Bm Bp ∧
  ∀ Bm' Bp' : StrongField μ,
    IsTiltIndexedBusemannProcess μ Bm' Bp' →
    ∀ᵐ ω ∂environmentLaw μ, ∀ (h : CoalescingTilt μ) (x y : Lattice),
      Bm' h x y ω = Bm h x y ω ∧ Bp' h x y ω = Bp h x y ω

/-- The canonical characterization at the same two branches. -/
theorem is_canonical_busemann_process_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Bm Bp : StrongField μ) :
    IsCanonicalBusemannProcess μ Bm Bp ↔
      BranchAgreement μ Bm Bp ∧ ForwardCoalescingClass μ Bm Bp ∧ MeanTilt μ Bm ∧
      WithinTiltOrder μ Bm Bp ∧ StrictCrossTiltOrder μ Bm Bp ∧ OneSidedLimits μ Bm Bp ∧
      SkorokhodRealization μ Bm Bp ∧
      (∀ Bm' Bp' : StrongField μ,
        (BranchAgreement μ Bm' Bp' ∧ ForwardCoalescingClass μ Bm' Bp' ∧
         MeanTilt μ Bm' ∧ WithinTiltOrder μ Bm' Bp' ∧
         StrictCrossTiltOrder μ Bm' Bp' ∧ OneSidedLimits μ Bm' Bp') →
        ∀ᵐ ω ∂environmentLaw μ, ∀ (h : CoalescingTilt μ) (x y : Lattice),
          Bm' h x y ω = Bm h x y ω ∧ Bp' h x y ω = Bp h x y ω) := by
  simp only [IsCanonicalBusemannProcess, IsTiltIndexedBusemannProcess, and_assoc]

end LPP.Busemann
