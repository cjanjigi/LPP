/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Topology.PairedSamplePairMeasurability

@[expose] public section
open MeasureTheory
namespace LPP.Busemann

/-- A sampled finite state paired with either constant time pole has a
measurable ordered-graph hit against every open pair test, in the parent's
sampled-evaluation sigma algebra. -/
theorem measurableSet_squeezedFinitePoleSampleGraphPair_hit_open
    (S : Set ℝ) (J : Type*) [Countable J] (hS : IsClosed S)
    (D : Set {v : ℝ // v ∈ S})
    (t : {v : ℝ // v ∈ S}) (ht : t ∈ D)
    (minus isTop poleFirst : Bool)
    (U : Set (SqueezedState J × SqueezedState J)) (hU : IsOpen U) :
    @MeasurableSet (PairedSkorokhodPath S J)
      (MeasurableSpace.generateFrom
        {A : Set (PairedSkorokhodPath S J) |
          ∃ s : {v : ℝ // v ∈ S}, s ∈ D ∧
            ∃ j : J, ∃ V : Set ℝ, IsOpen V ∧
              (A = {f | evalMinus f s j ∈ V} ∨
               A = {f | evalPlus f s j ∈ V})})
      {f : PairedSkorokhodPath S J |
        let sample : SqueezedState J :=
          .finite (if minus then evalMinus f t else evalPlus f t) t.val
        let pole : SqueezedState J := if isTop then .top else .bottom
        let z : SqueezedState J × SqueezedState J :=
          if poleFirst then (pole, sample) else (sample, pole)
        z ∈ pairedPathOrderGraph S J f ∧ z ∈ U} := by
  classical
  -- Keep the exact parent sampled-evaluation sigma algebra on the path type.
  let : MeasurableSpace (PairedSkorokhodPath S J) :=
    MeasurableSpace.generateFrom
      {A : Set (PairedSkorokhodPath S J) |
        ∃ s : {v : ℝ // v ∈ S}, s ∈ D ∧
          ∃ j : J, ∃ V : Set ℝ, IsOpen V ∧
            (A = {f | evalMinus f s j ∈ V} ∨
             A = {f | evalPlus f s j ∈ V})}

  let sample : PairedSkorokhodPath S J → SqueezedState J := fun f =>
    .finite (if minus then evalMinus f t else evalPlus f t) t.val
  let pole : SqueezedState J := if isTop then .top else .bottom

  -- The sampled finite state is one of the two traces in the graph.
  have hSampleGraph (f : PairedSkorokhodPath S J) :
      sample f ∈ pairedTraceGraph S f.1 := by
    cases minus
    · change SqueezedState.finite (evalPlus f t) t.val ∈ pairedTraceGraph S f.1
      simp only [pairedTraceGraph, Set.mem_ofPred_eq]
      exact Or.inr (Or.inr ⟨t, Or.inr rfl⟩)
    · change SqueezedState.finite (evalMinus f t) t.val ∈ pairedTraceGraph S f.1
      simp only [pairedTraceGraph, Set.mem_ofPred_eq]
      exact Or.inr (Or.inr ⟨t, Or.inl rfl⟩)

  have hPoleGraph (f : PairedSkorokhodPath S J) :
      pole ∈ pairedTraceGraph S f.1 := by
    cases isTop <;> simp [pole, pairedTraceGraph]

  -- Reduce finite-state open hits to the public diagonal pair result.
  have hSampleOpen (V : Set (SqueezedState J)) (hV : IsOpen V) :
      MeasurableSet {f : PairedSkorokhodPath S J | sample f ∈ V} := by
    let pairOpen : Set (SqueezedState J × SqueezedState J) :=
      V ×ˢ (Set.univ : Set (SqueezedState J))
    have hPairOpen : IsOpen pairOpen := hV.prod isOpen_univ
    have hPairMeasurable : MeasurableSet
        {f : PairedSkorokhodPath S J |
          let z : SqueezedState J × SqueezedState J :=
            (SqueezedState.finite
                (if minus then evalMinus f t else evalPlus f t) t.val,
              SqueezedState.finite
                (if minus then evalMinus f t else evalPlus f t) t.val)
          z ∈ pairedPathOrderGraph S J f ∧ z ∈ pairOpen} :=
      measurableSet_squeezedFiniteSampleGraphPair_hit_open
        S J hS D t t ht ht minus minus pairOpen hPairOpen
    have hDiagonalGraph (f : PairedSkorokhodPath S J) :
        (sample f, sample f) ∈ pairedPathOrderGraph S J f := by
      change sample f ∈ pairedTraceGraph S f.1 ∧
        sample f ∈ pairedTraceGraph S f.1 ∧
        pairedTraceLE S f.1 (sample f) (sample f)
      exact ⟨hSampleGraph f, hSampleGraph f, Or.inl rfl⟩
    have hEventEq :
        {f : PairedSkorokhodPath S J | sample f ∈ V} =
          {f : PairedSkorokhodPath S J |
            let z : SqueezedState J × SqueezedState J := (sample f, sample f)
            z ∈ pairedPathOrderGraph S J f ∧ z ∈ pairOpen} := by
      ext f
      constructor
      · intro hVf
        refine ⟨hDiagonalGraph f, ?_⟩
        change sample f ∈ V ∧ sample f ∈ Set.univ
        exact ⟨hVf, Set.mem_univ _⟩
      · intro hHit
        rcases hHit with ⟨_, hPairOpenHit⟩
        change sample f ∈ V ∧ sample f ∈ Set.univ at hPairOpenHit
        exact hPairOpenHit.1
    rw [hEventEq]
    exact hPairMeasurable

  -- A constant pole cuts the arbitrary open pair test by an open section.
  let poleSection : SqueezedState J → SqueezedState J × SqueezedState J :=
    fun x => if poleFirst then (pole, x) else (x, pole)
  let V : Set (SqueezedState J) := poleSection ⁻¹' U
  have hPoleSection : Continuous poleSection := by
    cases poleFirst
    · exact continuous_id.prodMk continuous_const
    · exact continuous_const.prodMk continuous_id
  have hV : IsOpen V := hU.preimage hPoleSection
  let z : PairedSkorokhodPath S J → SqueezedState J × SqueezedState J :=
    fun f => poleSection (sample f)
  let graphHit : Set (PairedSkorokhodPath S J) :=
    {f | z f ∈ pairedPathOrderGraph S J f}
  let openHit : Set (PairedSkorokhodPath S J) := {f | z f ∈ U}
  have hOpenHitEq : openHit = {f | sample f ∈ V} := by
    ext f
    rfl
  have hOpenHitMeasurable : MeasurableSet openHit := by
    rw [hOpenHitEq]
    exact hSampleOpen V hV

  have hFirstGraph (f : PairedSkorokhodPath S J) :
      (z f).1 ∈ pairedTraceGraph S f.1 := by
    cases poleFirst
    · change sample f ∈ pairedTraceGraph S f.1
      exact hSampleGraph f
    · change pole ∈ pairedTraceGraph S f.1
      exact hPoleGraph f
  have hSecondGraph (f : PairedSkorokhodPath S J) :
      (z f).2 ∈ pairedTraceGraph S f.1 := by
    cases poleFirst
    · change pole ∈ pairedTraceGraph S f.1
      exact hPoleGraph f
    · change sample f ∈ pairedTraceGraph S f.1
      exact hSampleGraph f

  have hGraphIff (f : PairedSkorokhodPath S J) :
      z f ∈ pairedPathOrderGraph S J f ↔
        pairedTraceLE S f.1 (z f).1 (z f).2 := by
    change (z f).1 ∈ pairedTraceGraph S f.1 ∧
      (z f).2 ∈ pairedTraceGraph S f.1 ∧
      pairedTraceLE S f.1 (z f).1 (z f).2 ↔ _
    constructor
    · exact fun h => h.2.2
    · intro hOrder
      exact ⟨hFirstGraph f, hSecondGraph f, hOrder⟩

  have hGraphSetOfOrder
      (hOrder : ∀ f : PairedSkorokhodPath S J,
        pairedTraceLE S f.1 (z f).1 (z f).2) :
      graphHit = Set.univ := by
    ext f
    change z f ∈ pairedPathOrderGraph S J f ↔ True
    constructor
    · intro _
      trivial
    · intro _
      exact (hGraphIff f).mpr (hOrder f)
  have hGraphSetOfNoOrder
      (hNoOrder : ∀ f : PairedSkorokhodPath S J,
        ¬ pairedTraceLE S f.1 (z f).1 (z f).2) :
      graphHit = ∅ := by
    ext f
    change z f ∈ pairedPathOrderGraph S J f ↔ False
    constructor
    · intro hGraph
      exact hNoOrder f ((hGraphIff f).mp hGraph)
    · exact False.elim

  -- The literal order clauses accept bottom-first and top-second, and reject
  -- top-first and bottom-second for a finite sample.
  have hTopFirstImpossible (f : PairedSkorokhodPath S J) :
      ¬ pairedTraceLE S f.1 .top (sample f) := by
    intro hOrder
    rcases hOrder with hEqual | hBottom | hTop | hStrict | hJump
    · cases hEqual
    · cases hBottom
    · cases hTop
    · rcases hStrict with ⟨x, y, s, u, hFirst, _, _⟩
      cases hFirst
    · rcases hJump with ⟨s, hFirst, _⟩
      cases hFirst
  have hFiniteBottomImpossible (f : PairedSkorokhodPath S J) :
      ¬ pairedTraceLE S f.1 (sample f) .bottom := by
    intro hOrder
    rcases hOrder with hEqual | hBottom | hTop | hStrict | hJump
    · cases hEqual
    · cases hBottom
    · cases hTop
    · rcases hStrict with ⟨x, y, s, u, _, hSecond, _⟩
      cases hSecond
    · rcases hJump with ⟨s, _, hSecond⟩
      cases hSecond

  have hGraphMeasurable : MeasurableSet graphHit := by
    cases isTop <;> cases poleFirst
    · -- Finite then bottom is forbidden by the order.
      have hNoOrder : ∀ f : PairedSkorokhodPath S J,
          ¬ pairedTraceLE S f.1 (z f).1 (z f).2 := by
        intro f hOrder
        change pairedTraceLE S f.1 (sample f) .bottom at hOrder
        exact hFiniteBottomImpossible f hOrder
      rw [hGraphSetOfNoOrder hNoOrder]
      exact MeasurableSet.empty
    · -- Bottom then finite is always ordered.
      have hOrder : ∀ f : PairedSkorokhodPath S J,
          pairedTraceLE S f.1 (z f).1 (z f).2 := by
        intro f
        change pairedTraceLE S f.1 .bottom (sample f)
        exact Or.inr (Or.inl rfl)
      rw [hGraphSetOfOrder hOrder]
      exact MeasurableSet.univ
    · -- Finite then top is always ordered.
      have hOrder : ∀ f : PairedSkorokhodPath S J,
          pairedTraceLE S f.1 (z f).1 (z f).2 := by
        intro f
        change pairedTraceLE S f.1 (sample f) .top
        exact Or.inr (Or.inr (Or.inl rfl))
      rw [hGraphSetOfOrder hOrder]
      exact MeasurableSet.univ
    · -- Top then finite is forbidden by the order.
      have hNoOrder : ∀ f : PairedSkorokhodPath S J,
          ¬ pairedTraceLE S f.1 (z f).1 (z f).2 := by
        intro f hOrder
        change pairedTraceLE S f.1 .top (sample f) at hOrder
        exact hTopFirstImpossible f hOrder
      rw [hGraphSetOfNoOrder hNoOrder]
      exact MeasurableSet.empty

  -- Intersect the universal-or-empty order event with the open section hit.
  change MeasurableSet (graphHit ∩ openHit)
  exact hGraphMeasurable.inter hOpenHitMeasurable

end LPP.Busemann
