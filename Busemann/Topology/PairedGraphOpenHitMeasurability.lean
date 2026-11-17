/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Topology.PairedGraphSidedSamples
public import Busemann.Topology.PairedSamplePairMeasurability
public import Busemann.Topology.PairedPoleSampleMeasurability

@[expose] public section
open MeasureTheory
namespace LPP.Busemann

/-- An open set hits the literal ordered graph measurably in the sampled
evaluation sigma. This is the open-hit reduction built on
`PairedGraphSidedSamples.lean:249`. -/
theorem measurableSet_pairedPathOrderGraph_hit_open_of_sidedSamples
    (S : Set ℝ) (J : Type*) [Countable J] (hS : IsClosed S)
    (D : Set {v : ℝ // v ∈ S}) (hD : D.Countable)
    (hside : ∀ t : {v : ℝ // v ∈ S}, t ∉ D →
      t ∈ closure (D ∩ Set.Iio t) ∧
      t ∈ closure (D ∩ Set.Ioi t))
    (U : Set (SqueezedState J × SqueezedState J)) (hU : IsOpen U) :
    @MeasurableSet (PairedSkorokhodPath S J)
      (MeasurableSpace.generateFrom
        {A : Set (PairedSkorokhodPath S J) |
          ∃ s : {v : ℝ // v ∈ S}, s ∈ D ∧
            ∃ j : J, ∃ V : Set ℝ, IsOpen V ∧
              (A = {f | evalMinus f s j ∈ V} ∨
               A = {f | evalPlus f s j ∈ V})})
      {f : PairedSkorokhodPath S J |
        (pairedPathOrderGraph S J f ∩ U).Nonempty} := by
  classical
  have _hS : IsClosed S := hS

  -- Keep the exact generated sigma algebra from the parent theorem.
  let : MeasurableSpace (PairedSkorokhodPath S J) :=
    MeasurableSpace.generateFrom
      {A : Set (PairedSkorokhodPath S J) |
        ∃ s : {v : ℝ // v ∈ S}, s ∈ D ∧
          ∃ j : J, ∃ V : Set ℝ, IsOpen V ∧
            (A = {f | evalMinus f s j ∈ V} ∨
             A = {f | evalPlus f s j ∈ V})}

  let SampleTime : Type := {t : {v : ℝ // v ∈ S} // t ∈ D}
  let : Countable SampleTime := hD.to_subtype

  -- These are exactly the coordinates used in the density theorem.
  let sampledState : PairedSkorokhodPath S J → Set (SqueezedState J) :=
    fun f => {p | p = .bottom ∨ p = .top ∨
      ∃ t : {v : ℝ // v ∈ S}, t ∈ D ∧
        (p = .finite (evalMinus f t) t.val ∨
         p = .finite (evalPlus f t) t.val)}
  let sampledPairs : PairedSkorokhodPath S J →
      Set (SqueezedState J × SqueezedState J) :=
    fun f => {z | z ∈ pairedPathOrderGraph S J f ∧
      z.1 ∈ sampledState f ∧ z.2 ∈ sampledState f}

  -- The finite-finite events use the graph-pair producer.
  let finiteFiniteHits : Set (PairedSkorokhodPath S J) :=
    ⋃ i : (SampleTime × SampleTime) × (Bool × Bool),
      {f : PairedSkorokhodPath S J |
        let z : SqueezedState J × SqueezedState J :=
          (SqueezedState.finite
              (if i.2.1 then evalMinus f i.1.1.1 else evalPlus f i.1.1.1)
              i.1.1.1.val,
           SqueezedState.finite
              (if i.2.2 then evalMinus f i.1.2.1 else evalPlus f i.1.2.1)
              i.1.2.1.val)
        z ∈ pairedPathOrderGraph S J f ∧ z ∈ U}

  have hFiniteFiniteMeasurable : MeasurableSet finiteFiniteHits := by
    apply MeasurableSet.iUnion
    intro i
    rcases i with ⟨⟨t, u⟩, ⟨minus₁, minus₂⟩⟩
    exact measurableSet_squeezedFiniteSampleGraphPair_hit_open
      S J hS D t.1 u.1 t.2 u.2 minus₁ minus₂ U hU

  -- The finite-pole events retain both pole identities and both orientations.
  let finitePoleHits : Set (PairedSkorokhodPath S J) :=
    ⋃ i : SampleTime × (Bool × (Bool × Bool)),
      {f : PairedSkorokhodPath S J |
        let sample : SqueezedState J :=
          .finite (if i.2.1 then evalMinus f i.1.1 else evalPlus f i.1.1)
            i.1.1.val
        let pole : SqueezedState J := if i.2.2.1 then .top else .bottom
        let z : SqueezedState J × SqueezedState J :=
          if i.2.2.2 then (pole, sample) else (sample, pole)
        z ∈ pairedPathOrderGraph S J f ∧ z ∈ U}

  have hFinitePoleMeasurable : MeasurableSet finitePoleHits := by
    apply MeasurableSet.iUnion
    intro i
    rcases i with ⟨t, ⟨minus, isTop, poleFirst⟩⟩
    exact measurableSet_squeezedFinitePoleSampleGraphPair_hit_open
      S J hS D t.1 t.2 minus isTop poleFirst U hU

  -- Pole-pole graph membership is constant, including for an empty S.
  let polePoleHits : Set (PairedSkorokhodPath S J) :=
    ⋃ i : Bool × Bool,
      {f : PairedSkorokhodPath S J |
        let z : SqueezedState J × SqueezedState J :=
          (if i.1 then .top else .bottom,
           if i.2 then .top else .bottom)
        z ∈ pairedPathOrderGraph S J f ∧ z ∈ U}

  have hBottomBottomGraph (f : PairedSkorokhodPath S J) :
      (.bottom, .bottom) ∈ pairedPathOrderGraph S J f := by
    change .bottom ∈ pairedTraceGraph S f.1 ∧
      .bottom ∈ pairedTraceGraph S f.1 ∧
      pairedTraceLE S f.1 .bottom .bottom
    exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

  have hBottomTopGraph (f : PairedSkorokhodPath S J) :
      (.bottom, .top) ∈ pairedPathOrderGraph S J f := by
    change .bottom ∈ pairedTraceGraph S f.1 ∧
      .top ∈ pairedTraceGraph S f.1 ∧
      pairedTraceLE S f.1 .bottom .top
    exact ⟨Or.inl rfl, Or.inr (Or.inl rfl),
      Or.inr (Or.inr (Or.inl rfl))⟩

  have hTopTopGraph (f : PairedSkorokhodPath S J) :
      (.top, .top) ∈ pairedPathOrderGraph S J f := by
    change .top ∈ pairedTraceGraph S f.1 ∧
      .top ∈ pairedTraceGraph S f.1 ∧
      pairedTraceLE S f.1 .top .top
    exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inl rfl), Or.inl rfl⟩

  have hTopBottomNoGraph (f : PairedSkorokhodPath S J) :
      (.top, .bottom) ∉ pairedPathOrderGraph S J f := by
    intro hGraph
    change .top ∈ pairedTraceGraph S f.1 ∧
      .bottom ∈ pairedTraceGraph S f.1 ∧
      pairedTraceLE S f.1 .top .bottom at hGraph
    rcases hGraph.2.2 with hEqual | hBottom | hTop | hStrict | hJump
    · cases hEqual
    · cases hBottom
    · cases hTop
    · rcases hStrict with ⟨_, _, _, _, hFirst, _, _⟩
      cases hFirst
    · rcases hJump with ⟨_, hFirst, _⟩
      cases hFirst

  have hConstantGraphHit
      (z : SqueezedState J × SqueezedState J)
      (hGraph : ∀ f : PairedSkorokhodPath S J,
        z ∈ pairedPathOrderGraph S J f) :
      MeasurableSet {f : PairedSkorokhodPath S J |
        z ∈ pairedPathOrderGraph S J f ∧ z ∈ U} := by
    by_cases hUmem : z ∈ U
    · have hEvent :
        {f : PairedSkorokhodPath S J |
          z ∈ pairedPathOrderGraph S J f ∧ z ∈ U} = Set.univ := by
        ext f
        change (z ∈ pairedPathOrderGraph S J f ∧ z ∈ U) ↔ True
        constructor
        · intro _
          trivial
        · intro _
          exact ⟨hGraph f, hUmem⟩
      rw [hEvent]
      exact MeasurableSet.univ
    · have hEvent :
        {f : PairedSkorokhodPath S J |
          z ∈ pairedPathOrderGraph S J f ∧ z ∈ U} = ∅ := by
        ext f
        change (z ∈ pairedPathOrderGraph S J f ∧ z ∈ U) ↔ False
        constructor
        · rintro ⟨_, hzU⟩
          exact hUmem hzU
        · intro hFalse
          exact False.elim hFalse
      rw [hEvent]
      exact MeasurableSet.empty

  have hConstantNoGraphHit
      (z : SqueezedState J × SqueezedState J)
      (hNoGraph : ∀ f : PairedSkorokhodPath S J,
        z ∉ pairedPathOrderGraph S J f) :
      MeasurableSet {f : PairedSkorokhodPath S J |
        z ∈ pairedPathOrderGraph S J f ∧ z ∈ U} := by
    have hEvent :
        {f : PairedSkorokhodPath S J |
          z ∈ pairedPathOrderGraph S J f ∧ z ∈ U} = ∅ := by
      ext f
      change (z ∈ pairedPathOrderGraph S J f ∧ z ∈ U) ↔ False
      constructor
      · rintro ⟨hGraph, _⟩
        exact hNoGraph f hGraph
      · intro hFalse
        exact False.elim hFalse
    rw [hEvent]
    exact MeasurableSet.empty

  have hPolePoleMeasurable : MeasurableSet polePoleHits := by
    apply MeasurableSet.iUnion
    intro i
    rcases i with ⟨firstTop, secondTop⟩
    cases firstTop <;> cases secondTop
    · exact hConstantGraphHit (.bottom, .bottom) hBottomBottomGraph
    · exact hConstantGraphHit (.bottom, .top) hBottomTopGraph
    · exact hConstantNoGraphHit (.top, .bottom) hTopBottomNoGraph
    · exact hConstantGraphHit (.top, .top) hTopTopGraph

  -- Every finite sample or pole is in the sampled state set.
  have hFiniteSampled (f : PairedSkorokhodPath S J)
      (t : {v : ℝ // v ∈ S}) (ht : t ∈ D) (minus : Bool) :
      SqueezedState.finite
        (if minus then evalMinus f t else evalPlus f t) t.val ∈ sampledState f := by
    simp only [sampledState, Set.mem_ofPred_eq]
    refine Or.inr (Or.inr ⟨t, ht, ?_⟩)
    cases minus
    · exact Or.inr rfl
    · exact Or.inl rfl

  have hPoleSampled (f : PairedSkorokhodPath S J) (isTop : Bool) :
      (if isTop then (SqueezedState.top : SqueezedState J) else .bottom) ∈
        sampledState f := by
    cases isTop <;> simp [sampledState]

  -- An open neighborhood of a closure point meets the ordered sampled pairs.
  let openGraphHit : Set (PairedSkorokhodPath S J) :=
    {f | (pairedPathOrderGraph S J f ∩ U).Nonempty}
  have hOpenHitReduction :
      openGraphHit = {f | ∃ z, z ∈ sampledPairs f ∧ z ∈ U} := by
    ext f
    constructor
    · rintro ⟨z, hz⟩
      rcases hz with ⟨hzGraph, hzU⟩
      have hzClosure : z ∈ closure (sampledPairs f) := by
        change z ∈ closure
          {w : SqueezedState J × SqueezedState J |
            w ∈ pairedPathOrderGraph S J f ∧
            (w.1 = .bottom ∨ w.1 = .top ∨
              ∃ t : {v : ℝ // v ∈ S}, t ∈ D ∧
                (w.1 = .finite (evalMinus f t) t.val ∨
                 w.1 = .finite (evalPlus f t) t.val)) ∧
            (w.2 = .bottom ∨ w.2 = .top ∨
              ∃ t : {v : ℝ // v ∈ S}, t ∈ D ∧
                (w.2 = .finite (evalMinus f t) t.val ∨
                 w.2 = .finite (evalPlus f t) t.val))}
        rw [← pairedPathOrderGraph_eq_closure_sidedSamples D hside f]
        exact hzGraph
      obtain ⟨w, hwU, hwSample⟩ :=
        mem_closure_iff_nhds.mp hzClosure U (hU.mem_nhds hzU)
      exact ⟨w, hwSample, hwU⟩
    · rintro ⟨z, hzSample, hzU⟩
      change z ∈ pairedPathOrderGraph S J f ∧ _ at hzSample
      exact ⟨z, hzSample.1, hzU⟩

  -- Split the ordered sampled pairs into finite, mixed, and pole-only cases.
  have hSamplePairSplit :
      {f : PairedSkorokhodPath S J | ∃ z, z ∈ sampledPairs f ∧ z ∈ U} =
        finiteFiniteHits ∪ (finitePoleHits ∪ polePoleHits) := by
    ext f
    constructor
    · rintro ⟨z, hzSample, hzU⟩
      change z ∈ pairedPathOrderGraph S J f ∧
        z.1 ∈ sampledState f ∧ z.2 ∈ sampledState f at hzSample
      rcases hzSample with ⟨hzGraph, hfirst, hsecond⟩
      have hPairU (a b : SqueezedState J)
          (hfirstEq : z.1 = a) (hsecondEq : z.2 = b) :
          (a, b) ∈ pairedPathOrderGraph S J f ∧ (a, b) ∈ U := by
        have hzEq : z = (a, b) := Prod.ext hfirstEq hsecondEq
        exact hzEq ▸ ⟨hzGraph, hzU⟩
      rcases hfirst with hfirstBottom | hfirstTop | ⟨t, ht, hfirstFinite⟩
      · rcases hsecond with hsecondBottom | hsecondTop |
          ⟨u, hu, hsecondFinite⟩
        · have hPoleHit : f ∈ polePoleHits := by
            refine Set.mem_iUnion.mpr ⟨(false, false), ?_⟩
            exact hPairU .bottom .bottom hfirstBottom hsecondBottom
          exact Or.inr (Or.inr hPoleHit)
        · have hPoleHit : f ∈ polePoleHits := by
            refine Set.mem_iUnion.mpr ⟨(false, true), ?_⟩
            exact hPairU .bottom .top hfirstBottom hsecondTop
          exact Or.inr (Or.inr hPoleHit)
        · rcases hsecondFinite with hsecondMinus | hsecondPlus
          · have hMixedHit : f ∈ finitePoleHits := by
              refine Set.mem_iUnion.mpr
                ⟨(⟨u, hu⟩, (true, (false, true))), ?_⟩
              exact hPairU .bottom (.finite (evalMinus f u) u.val)
                hfirstBottom hsecondMinus
            exact Or.inr (Or.inl hMixedHit)
          · have hMixedHit : f ∈ finitePoleHits := by
              refine Set.mem_iUnion.mpr
                ⟨(⟨u, hu⟩, (false, (false, true))), ?_⟩
              exact hPairU .bottom (.finite (evalPlus f u) u.val)
                hfirstBottom hsecondPlus
            exact Or.inr (Or.inl hMixedHit)
      · rcases hsecond with hsecondBottom | hsecondTop |
          ⟨u, hu, hsecondFinite⟩
        · have hTopBottom :
            (.top, .bottom) ∈ pairedPathOrderGraph S J f := by
            exact (hPairU .top .bottom hfirstTop hsecondBottom).1
          exact False.elim (hTopBottomNoGraph f hTopBottom)
        · have hPoleHit : f ∈ polePoleHits := by
            refine Set.mem_iUnion.mpr ⟨(true, true), ?_⟩
            exact hPairU .top .top hfirstTop hsecondTop
          exact Or.inr (Or.inr hPoleHit)
        · rcases hsecondFinite with hsecondMinus | hsecondPlus
          · have hMixedHit : f ∈ finitePoleHits := by
              refine Set.mem_iUnion.mpr
                ⟨(⟨u, hu⟩, (true, (true, true))), ?_⟩
              exact hPairU .top (.finite (evalMinus f u) u.val)
                hfirstTop hsecondMinus
            exact Or.inr (Or.inl hMixedHit)
          · have hMixedHit : f ∈ finitePoleHits := by
              refine Set.mem_iUnion.mpr
                ⟨(⟨u, hu⟩, (false, (true, true))), ?_⟩
              exact hPairU .top (.finite (evalPlus f u) u.val)
                hfirstTop hsecondPlus
            exact Or.inr (Or.inl hMixedHit)
      · rcases hfirstFinite with hfirstMinus | hfirstPlus
        · rcases hsecond with hsecondBottom | hsecondTop |
            ⟨u, hu, hsecondFinite⟩
          · have hMixedHit : f ∈ finitePoleHits := by
              refine Set.mem_iUnion.mpr
                ⟨(⟨t, ht⟩, (true, (false, false))), ?_⟩
              exact hPairU (.finite (evalMinus f t) t.val) .bottom
                hfirstMinus hsecondBottom
            exact Or.inr (Or.inl hMixedHit)
          · have hMixedHit : f ∈ finitePoleHits := by
              refine Set.mem_iUnion.mpr
                ⟨(⟨t, ht⟩, (true, (true, false))), ?_⟩
              exact hPairU (.finite (evalMinus f t) t.val) .top
                hfirstMinus hsecondTop
            exact Or.inr (Or.inl hMixedHit)
          · rcases hsecondFinite with hsecondMinus | hsecondPlus
            · have hFiniteHit : f ∈ finiteFiniteHits := by
                refine Set.mem_iUnion.mpr
                  ⟨((⟨t, ht⟩, ⟨u, hu⟩), (true, true)), ?_⟩
                exact hPairU (.finite (evalMinus f t) t.val)
                  (.finite (evalMinus f u) u.val) hfirstMinus hsecondMinus
              exact Or.inl hFiniteHit
            · have hFiniteHit : f ∈ finiteFiniteHits := by
                refine Set.mem_iUnion.mpr
                  ⟨((⟨t, ht⟩, ⟨u, hu⟩), (true, false)), ?_⟩
                exact hPairU (.finite (evalMinus f t) t.val)
                  (.finite (evalPlus f u) u.val) hfirstMinus hsecondPlus
              exact Or.inl hFiniteHit
        · rcases hsecond with hsecondBottom | hsecondTop |
            ⟨u, hu, hsecondFinite⟩
          · have hMixedHit : f ∈ finitePoleHits := by
              refine Set.mem_iUnion.mpr
                ⟨(⟨t, ht⟩, (false, (false, false))), ?_⟩
              exact hPairU (.finite (evalPlus f t) t.val) .bottom
                hfirstPlus hsecondBottom
            exact Or.inr (Or.inl hMixedHit)
          · have hMixedHit : f ∈ finitePoleHits := by
              refine Set.mem_iUnion.mpr
                ⟨(⟨t, ht⟩, (false, (true, false))), ?_⟩
              exact hPairU (.finite (evalPlus f t) t.val) .top
                hfirstPlus hsecondTop
            exact Or.inr (Or.inl hMixedHit)
          · rcases hsecondFinite with hsecondMinus | hsecondPlus
            · have hFiniteHit : f ∈ finiteFiniteHits := by
                refine Set.mem_iUnion.mpr
                  ⟨((⟨t, ht⟩, ⟨u, hu⟩), (false, true)), ?_⟩
                exact hPairU (.finite (evalPlus f t) t.val)
                  (.finite (evalMinus f u) u.val) hfirstPlus hsecondMinus
              exact Or.inl hFiniteHit
            · have hFiniteHit : f ∈ finiteFiniteHits := by
                refine Set.mem_iUnion.mpr
                  ⟨((⟨t, ht⟩, ⟨u, hu⟩), (false, false)), ?_⟩
                exact hPairU (.finite (evalPlus f t) t.val)
                  (.finite (evalPlus f u) u.val) hfirstPlus hsecondPlus
              exact Or.inl hFiniteHit
    · intro hHits
      rcases hHits with hFiniteHit | hRest
      · rcases Set.mem_iUnion.mp hFiniteHit with ⟨i, hi⟩
        rcases i with ⟨⟨t, u⟩, ⟨minus₁, minus₂⟩⟩
        let z : SqueezedState J × SqueezedState J :=
          (SqueezedState.finite
              (if minus₁ then evalMinus f t.1 else evalPlus f t.1) t.1.val,
           SqueezedState.finite
              (if minus₂ then evalMinus f u.1 else evalPlus f u.1) u.1.val)
        change z ∈ pairedPathOrderGraph S J f ∧ z ∈ U at hi
        have hSamplePair : z ∈ sampledPairs f := by
          change z ∈ pairedPathOrderGraph S J f ∧
            z.1 ∈ sampledState f ∧ z.2 ∈ sampledState f
          refine ⟨hi.1, ?_, ?_⟩
          · simpa [z] using hFiniteSampled f t.1 t.2 minus₁
          · simpa [z] using hFiniteSampled f u.1 u.2 minus₂
        exact ⟨z, hSamplePair, hi.2⟩
      · rcases hRest with hMixedHit | hPoleHit
        · rcases Set.mem_iUnion.mp hMixedHit with ⟨i, hi⟩
          rcases i with ⟨t, ⟨minus, isTop, poleFirst⟩⟩
          let sample : SqueezedState J :=
            .finite (if minus then evalMinus f t.1 else evalPlus f t.1) t.1.val
          let pole : SqueezedState J := if isTop then .top else .bottom
          let z : SqueezedState J × SqueezedState J :=
            if poleFirst then (pole, sample) else (sample, pole)
          change z ∈ pairedPathOrderGraph S J f ∧ z ∈ U at hi
          have hSamplePair : z ∈ sampledPairs f := by
            change z ∈ pairedPathOrderGraph S J f ∧
              z.1 ∈ sampledState f ∧ z.2 ∈ sampledState f
            refine ⟨hi.1, ?_, ?_⟩
            · cases poleFirst
              · exact hFiniteSampled f t.1 t.2 minus
              · exact hPoleSampled f isTop
            · cases poleFirst
              · exact hPoleSampled f isTop
              · exact hFiniteSampled f t.1 t.2 minus
          exact ⟨z, hSamplePair, hi.2⟩
        · rcases Set.mem_iUnion.mp hPoleHit with ⟨i, hi⟩
          rcases i with ⟨firstTop, secondTop⟩
          let z : SqueezedState J × SqueezedState J :=
            (if firstTop then .top else .bottom,
             if secondTop then .top else .bottom)
          change z ∈ pairedPathOrderGraph S J f ∧ z ∈ U at hi
          have hSamplePair : z ∈ sampledPairs f := by
            change z ∈ pairedPathOrderGraph S J f ∧
              z.1 ∈ sampledState f ∧ z.2 ∈ sampledState f
            exact ⟨hi.1, hPoleSampled f firstTop, hPoleSampled f secondTop⟩
          exact ⟨z, hSamplePair, hi.2⟩

  -- Countable time unions and the finite pole choices finish measurability.
  change MeasurableSet openGraphHit
  rw [hOpenHitReduction, hSamplePairSplit]
  exact hFiniteFiniteMeasurable.union
    (hFinitePoleMeasurable.union hPolePoleMeasurable)

end LPP.Busemann
