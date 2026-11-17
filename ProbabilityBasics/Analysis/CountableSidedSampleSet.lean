/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Topology.ClusterPt
public import Mathlib.Topology.Constructions

public section
open Filter Set TopologicalSpace
open scoped Topology
namespace ProbabilityBasics

/-- A countable set of actual times samples both available sides of every
omitted time. The statement includes empty and
disconnected time sets. -/
theorem exists_countable_sided_sample_set (S : Set ℝ) :
    ∃ D : Set {u : ℝ // u ∈ S},
      D.Countable ∧
      ∀ t : {u : ℝ // u ∈ S}, t ∉ D →
        t ∈ closure (D ∩ Set.Iio t) ∧
        t ∈ closure (D ∩ Set.Ioi t) := by
  classical
  -- Start with a countable dense subset of the actual subtype S.
  obtain ⟨D0, hD0Countable, hD0Dense⟩ :=
    TopologicalSpace.exists_countable_dense (α := {u : ℝ // u ∈ S})
  -- Record the ambient points where one of the two sides is unavailable.
  let leftBad : Set ℝ := {x | x ∈ S ∧ 𝓝[S ∩ Set.Iio x] x = ⊥}
  let rightBad : Set ℝ := {x | x ∈ S ∧ 𝓝[S ∩ Set.Ioi x] x = ⊥}
  have hleftBadCountable : leftBad.Countable := by
    simpa [leftBad] using
      (countable_setOfPred_isolated_left_within (α := ℝ) (s := S))
  have hrightBadCountable : rightBad.Countable := by
    simpa [rightBad] using
      (countable_setOfPred_isolated_right_within (α := ℝ) (s := S))
  -- Pull both ambient exceptional sets back to the subtype and adjoin them to D0.
  let valS : {u : ℝ // u ∈ S} → ℝ := fun u => u.val
  have hvalSInjective : Function.Injective valS := by
    intro x y hxy
    exact Subtype.ext (by simpa [valS] using hxy)
  have hleftBadSubtypeCountable : (valS ⁻¹' leftBad).Countable :=
    hleftBadCountable.preimage (f := valS) hvalSInjective
  have hrightBadSubtypeCountable : (valS ⁻¹' rightBad).Countable :=
    hrightBadCountable.preimage (f := valS) hvalSInjective
  let D : Set {u : ℝ // u ∈ S} :=
    D0 ∪ ((valS ⁻¹' leftBad) ∪ (valS ⁻¹' rightBad))
  have hDCountable : D.Countable := by
    exact hD0Countable.union (hleftBadSubtypeCountable.union hrightBadSubtypeCountable)
  refine ⟨D, hDCountable, ?_⟩
  intro t htNotD
  -- At a point outside D, neither ambient one-sided filter can be bottom.
  have hleftNeBot : NeBot (𝓝[S ∩ Set.Iio (t : ℝ)] (t : ℝ)) := by
    apply neBot_iff.mpr
    intro hbot
    apply htNotD
    simp only [D, mem_union, mem_preimage, valS, leftBad, Set.mem_ofPred_eq]
    right
    left
    exact ⟨t.property, hbot⟩
  have hrightNeBot : NeBot (𝓝[S ∩ Set.Ioi (t : ℝ)] (t : ℝ)) := by
    apply neBot_iff.mpr
    intro hbot
    apply htNotD
    simp only [D, mem_union, mem_preimage, valS, rightBad, Set.mem_ofPred_eq]
    right
    right
    exact ⟨t.property, hbot⟩
  -- Nontrivial within-side filters put the real value of t in both ambient closures.
  have hleftAmbient : (t : ℝ) ∈ closure (S ∩ Set.Iio (t : ℝ)) :=
    mem_closure_iff_nhdsWithin_neBot.mpr hleftNeBot
  have hrightAmbient : (t : ℝ) ∈ closure (S ∩ Set.Ioi (t : ℝ)) :=
    mem_closure_iff_nhdsWithin_neBot.mpr hrightNeBot
  -- The subtype rays are open in the induced topology, with the expected ambient images.
  have hleftOpen : IsOpen (Set.Iio t : Set {u : ℝ // u ∈ S}) := by
    rw [isOpen_induced_iff]
    exact ⟨Set.Iio (t : ℝ), isOpen_Iio, by ext x; rfl⟩
  have hrightOpen : IsOpen (Set.Ioi t : Set {u : ℝ // u ∈ S}) := by
    rw [isOpen_induced_iff]
    exact ⟨Set.Ioi (t : ℝ), isOpen_Ioi, by ext x; rfl⟩
  have hleftImage :
      Subtype.val '' (Set.Iio t : Set {u : ℝ // u ∈ S}) = S ∩ Set.Iio (t : ℝ) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.property, hu⟩
    · rintro ⟨hxS, hxt⟩
      exact ⟨⟨x, hxS⟩, hxt, rfl⟩
  have hrightImage :
      Subtype.val '' (Set.Ioi t : Set {u : ℝ // u ∈ S}) = S ∩ Set.Ioi (t : ℝ) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.property, hu⟩
    · rintro ⟨hxS, hxt⟩
      exact ⟨⟨x, hxS⟩, hxt, rfl⟩
  -- Transfer the ambient closure statements to the actual subtype.
  have hleftSubtype : t ∈ closure (Set.Iio t : Set {u : ℝ // u ∈ S}) := by
    rw [closure_subtype, hleftImage]
    exact hleftAmbient
  have hrightSubtype : t ∈ closure (Set.Ioi t : Set {u : ℝ // u ∈ S}) := by
    rw [closure_subtype, hrightImage]
    exact hrightAmbient
  -- Density of D0 samples every open side ray near its endpoint.
  have hleftDenseInClosure :
      (Set.Iio t : Set {u : ℝ // u ∈ S}) ⊆
        closure ((Set.Iio t : Set {u : ℝ // u ∈ S}) ∩ D0) :=
    hD0Dense.open_subset_closure_inter hleftOpen
  have hrightDenseInClosure :
      (Set.Ioi t : Set {u : ℝ // u ∈ S}) ⊆
        closure ((Set.Ioi t : Set {u : ℝ // u ∈ S}) ∩ D0) :=
    hD0Dense.open_subset_closure_inter hrightOpen
  have hleftFromD0 :
      t ∈ closure ((Set.Iio t : Set {u : ℝ // u ∈ S}) ∩ D0) :=
    closure_minimal hleftDenseInClosure isClosed_closure hleftSubtype
  have hrightFromD0 :
      t ∈ closure ((Set.Ioi t : Set {u : ℝ // u ∈ S}) ∩ D0) :=
    closure_minimal hrightDenseInClosure isClosed_closure hrightSubtype
  -- Enlarge D0 to D and put each side in the exact order used by the statement.
  have hleftSubset :
      (Set.Iio t : Set {u : ℝ // u ∈ S}) ∩ D0 ⊆ D ∩ Set.Iio t := by
    rintro x ⟨hxSide, hxD0⟩
    exact ⟨by simp [D, hxD0], hxSide⟩
  have hrightSubset :
      (Set.Ioi t : Set {u : ℝ // u ∈ S}) ∩ D0 ⊆ D ∩ Set.Ioi t := by
    rintro x ⟨hxSide, hxD0⟩
    exact ⟨by simp [D, hxD0], hxSide⟩
  exact ⟨closure_mono hleftSubset hleftFromD0,
    closure_mono hrightSubset hrightFromD0⟩

end ProbabilityBasics
