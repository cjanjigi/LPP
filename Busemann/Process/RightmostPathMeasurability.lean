/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.RightmostCocyclePath
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Order.Lattice

/-! Measurability of the rightmost cocycle successor and its finite path. -/

@[expose] public section
open LPPDifferentiability

namespace LPP.Busemann

/-- For a fixed starting site, the rightmost cocycle successor is measurable
whenever each cocycle coordinate is measurable. This is the finite-step form
of the measurable cocycle-geodesic construction in GRS, arXiv:1510.00860v1,
Section 4, reading lines 698–730. -/
theorem measurable_rightmostCocycleSuccessor
    {Ω : Type*} [MeasurableSpace Ω]
    (B : Lattice → Lattice → Ω → ℝ)
    (hB : ∀ x y, Measurable (B x y))
    (x : Lattice) :
    Measurable (fun ω : Ω =>
      rightmostCocycleSuccessor (fun y z => B y z ω) x) := by
  classical
  let east : Lattice := x + (1, 0)
  let north : Lattice := x + (0, 1)

  -- The comparison that fixes the selected edge is a measurable event.
  have hcompare :
      MeasurableSet {ω : Ω | B x east ω ≤ B x north ω} :=
    measurableSet_le (hB x east) (hB x north)

  -- The rule chooses between two fixed neighboring sites.
  have hrepresentation :
      (fun ω : Ω =>
        rightmostCocycleSuccessor (fun y z => B y z ω) x) =
        fun ω => if B x east ω ≤ B x north ω then east else north := by
    funext ω
    by_cases h : B x east ω ≤ B x north ω
    · simp [rightmostCocycleSuccessor, east, north, h]
    · simp [rightmostCocycleSuccessor, east, north, h]
  rw [hrepresentation]
  exact Measurable.ite hcompare measurable_const measurable_const

/-- For a fixed start and finite time, the rightmost path position is
measurable under coordinatewise measurable cocycle data. This is the
finite-time coordinate form of the measurable cocycle-geodesic construction
in GRS, arXiv:1510.00860v1, Section 4, reading lines 698–730. -/
theorem measurable_rightmostCocyclePath
    {Ω : Type*} [MeasurableSpace Ω]
    (B : Lattice → Lattice → Ω → ℝ)
    (hB : ∀ x y, Measurable (B x y))
    (x : Lattice) (n : ℕ) :
    Measurable (fun ω : Ω =>
      rightmostCocyclePath (fun y z => B y z ω) x n) := by
  classical
  let step : Ω × Lattice → Lattice := fun p =>
    rightmostCocycleSuccessor (fun y z => B y z p.1) p.2

  -- Measurable fixed-site sections and countability give a joint successor.
  have hstep : Measurable step := by
    apply measurable_from_prod_countable_left
    intro y
    change Measurable (fun ω : Ω =>
      rightmostCocycleSuccessor (fun z w => B z w ω) y)
    exact measurable_rightmostCocycleSuccessor B hB y

  -- Iterate the joint successor while carrying the same environment coordinate.
  have hiterate (k : ℕ) :
      Measurable (fun p : Ω × Lattice =>
        (fun y => rightmostCocycleSuccessor
          (fun z w => B z w p.1) y)^[k] p.2) := by
    induction k with
    | zero =>
        change Measurable (fun p : Ω × Lattice => p.2)
        exact measurable_snd
    | succ k ih =>
        change Measurable (fun p : Ω × Lattice =>
          (fun y => rightmostCocycleSuccessor
            (fun z w => B z w p.1) y)^[Nat.succ k] p.2)
        have hiterate_step :
            (fun p : Ω × Lattice =>
              (fun y => rightmostCocycleSuccessor
                (fun z w => B z w p.1) y)^[Nat.succ k] p.2) =
            (fun p => step (p.1, (fun y => rightmostCocycleSuccessor
              (fun z w => B z w p.1) y)^[k] p.2)) := by
          funext p
          exact Function.iterate_succ_apply'
            (fun y => rightmostCocycleSuccessor
              (fun z w => B z w p.1) y) k p.2
        rw [hiterate_step]
        exact hstep.comp (measurable_fst.prodMk ih)

  -- Fix the starting site by composing with the measurable map ω ↦ (ω, x).
  change Measurable (fun ω : Ω =>
    (fun y => rightmostCocycleSuccessor (fun z w => B z w ω) y)^[n] x)
  exact (hiterate n).comp (measurable_id.prodMk measurable_const)

end LPP.Busemann
