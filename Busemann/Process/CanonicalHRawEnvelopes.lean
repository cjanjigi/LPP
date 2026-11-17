/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.CanonicalHFieldSelection
public import Busemann.Process.MonotoneCocycleLimitAux
public import Busemann.Frozen.StrongExistence.Definitions.ForwardCoalescingClass
public import Busemann.Geometry.CanonicalHSidedSequences

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology

namespace LPP.Busemann

/-- The two literal countable-sequence limits are forward measurable and agree
with the selected field on the common sample set. These are raw candidates for
*Strong Existence*, lines 1194–1221. -/
theorem exists_canonical_H_raw_sided_fields
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (C : StrongField μ)
    (hClass : ForwardCoalescingClass μ C C)
    (D : Set (CoalescingTilt μ))
    (left right : CoalescingTilt μ → ℕ → CoalescingTilt μ)
    (hConstant : ∀ h : CoalescingTilt μ, h ∈ D →
      left h = (fun _ => h) ∧ right h = (fun _ => h)) :
    ∃ Bm Bp : StrongField μ,
      (∀ h x y ω,
        Bm h x y ω = limUnder atTop (fun n => C (left h n) x y ω) ∧
        Bp h x y ω = limUnder atTop (fun n => C (right h n) x y ω)) ∧
      (∀ h : CoalescingTilt μ,
        IsForwardMeasurable (Bm h) ∧ IsForwardMeasurable (Bp h) ∧
        Measurable (fun q : (Lattice × Lattice) × Environment =>
          Bm h q.1.1 q.1.2 q.2) ∧
        Measurable (fun q : (Lattice × Lattice) × Environment =>
          Bp h q.1.1 q.1.2 q.2)) ∧
      (∀ h : CoalescingTilt μ, h ∈ D → ∀ x y ω,
        Bm h x y ω = C h x y ω ∧ Bp h x y ω = C h x y ω) := by
  classical
  let Bm : StrongField μ := fun h x y ω =>
    limUnder atTop (fun n => C (left h n) x y ω)
  let Bp : StrongField μ := fun h x y ω =>
    limUnder atTop (fun n => C (right h n) x y ω)

  refine ⟨Bm, Bp, ?_, ?_, ?_⟩
  · intro h x y ω
    exact ⟨rfl, rfl⟩
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · change IsForwardMeasurable
        (fun x y ω => limUnder atTop (fun n => C (left h n) x y ω))
      exact isForwardMeasurable_limUnder
        (fun n x y ω => C (left h n) x y ω)
        (fun n => (hClass (left h n)).2.2.2)
    · change IsForwardMeasurable
        (fun x y ω => limUnder atTop (fun n => C (right h n) x y ω))
      exact isForwardMeasurable_limUnder
        (fun n x y ω => C (right h n) x y ω)
        (fun n => (hClass (right h n)).2.2.2)
    · change Measurable (fun q : (Lattice × Lattice) × Environment =>
        limUnder atTop (fun n => C (left h n) q.1.1 q.1.2 q.2))
      exact (StronglyMeasurable.limUnder
        (fun n => (hClass (left h n)).1.stronglyMeasurable)).measurable
    · change Measurable (fun q : (Lattice × Lattice) × Environment =>
        limUnder atTop (fun n => C (right h n) q.1.1 q.1.2 q.2))
      exact (StronglyMeasurable.limUnder
        (fun n => (hClass (right h n)).1.stronglyMeasurable)).measurable
  · intro h hh x y ω
    constructor
    · change limUnder atTop (fun n => C (left h n) x y ω) = C h x y ω
      rw [(hConstant h hh).1]
      apply tendsto_nhds_unique
        (tendsto_nhds_limUnder
          ⟨C h x y ω, (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => C h x y ω) atTop (𝓝 (C h x y ω)))⟩)
      exact tendsto_const_nhds
    · change limUnder atTop (fun n => C (right h n) x y ω) = C h x y ω
      rw [(hConstant h hh).2]
      apply tendsto_nhds_unique
        (tendsto_nhds_limUnder
          ⟨C h x y ω, (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => C h x y ω) atTop (𝓝 (C h x y ω)))⟩)
      exact tendsto_const_nhds

end LPP.Busemann
