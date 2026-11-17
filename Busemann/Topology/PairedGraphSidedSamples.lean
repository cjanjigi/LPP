/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.StrongExistence.Definitions.EvalPlus
public import Busemann.Frozen.StrongExistence.Definitions.PairedPathOrderGraph
import Busemann.Topology.PairedTraceLimits
import Busemann.Topology.SqueezedStateEmbedding
import Mathlib.Topology.ContinuousOn

/-!
# Sided samples of a compact ordered graph

Every sampled pair remains in the original graph.
-/

@[expose] public section
open Filter
namespace LPP.Busemann

private def sampledState {S : Set ℝ} {J : Type*}
    (D : Set {u : ℝ // u ∈ S}) (f : PairedSkorokhodPath S J) :
    Set (SqueezedState J) :=
  {p | p = .bottom ∨ p = .top ∨
    ∃ t : {u : ℝ // u ∈ S}, t ∈ D ∧
      (p = .finite (evalMinus f t) t.val ∨
       p = .finite (evalPlus f t) t.val)}

private def sampledPairs {S : Set ℝ} {J : Type*}
    (D : Set {u : ℝ // u ∈ S}) (f : PairedSkorokhodPath S J) :
    Set (SqueezedState J × SqueezedState J) :=
  {z | z ∈ pairedPathOrderGraph S J f ∧
    z.1 ∈ sampledState D f ∧ z.2 ∈ sampledState D f}

private theorem sampledState_mem_traceGraph
    {S : Set ℝ} {J : Type*} (D : Set {u : ℝ // u ∈ S})
    (f : PairedSkorokhodPath S J) {p : SqueezedState J}
    (hp : p ∈ sampledState D f) : p ∈ pairedTraceGraph S f.1 := by
  change p = .bottom ∨ p = .top ∨
    ∃ t : {u : ℝ // u ∈ S},
      p = .finite (f.1.1 t) t.val ∨ p = .finite (f.1.2 t) t.val
  rcases hp with hbot | htop | ⟨t, _, hm | hp⟩
  · exact Or.inl hbot
  · exact Or.inr (Or.inl htop)
  · exact Or.inr (Or.inr ⟨t, Or.inl hm⟩)
  · exact Or.inr (Or.inr ⟨t, Or.inr hp⟩)

private theorem exists_trace_approach
    {S : Set ℝ} {J : Type*} (D : Set {u : ℝ // u ∈ S})
    (t : {u : ℝ // u ∈ S}) (g : {u : ℝ // u ∈ S} → J → ℝ)
    (side : Set {u : ℝ // u ∈ S})
    (hside : t ∉ D → t ∈ closure (D ∩ side))
    (hlim : Tendsto g (nhdsWithin t side) (nhds (g t))) :
    ∃ l : Filter {u : ℝ // u ∈ S},
      NeBot l ∧ (∀ᶠ s in l, s ∈ D) ∧
      Tendsto (fun s => s.val) l (nhds t.val) ∧
      Tendsto (fun s => (SqueezedState.finite (g s) s.val : SqueezedState J))
        l (nhds (.finite (g t) t.val)) := by
  classical
  by_cases ht : t ∈ D
  · refine ⟨pure t, inferInstance, ?_, ?_, ?_⟩
    · simpa only [eventually_pure] using ht
    · exact tendsto_pure_nhds (fun s : {u : ℝ // u ∈ S} => s.val) t
    · exact tendsto_pure_nhds
        (fun s : {u : ℝ // u ∈ S} =>
          (SqueezedState.finite (g s) s.val : SqueezedState J)) t
  · let l := nhdsWithin t (D ∩ side)
    have : NeBot l := mem_closure_iff_nhdsWithin_neBot.mp (hside ht)
    refine ⟨l, inferInstance, ?_, ?_, ?_⟩
    · have hmem : ∀ᶠ s in l, s ∈ D ∩ side := self_mem_nhdsWithin
      exact hmem.mono (fun s hs => hs.1)
    · exact (continuous_subtype_val.tendsto t).mono_left nhdsWithin_le_nhds
    · have hg : Tendsto g l (nhds (g t)) :=
        hlim.mono_left (nhdsWithin_mono t Set.inter_subset_right)
      have htime : Tendsto (fun s : {u : ℝ // u ∈ S} => s.val)
          l (nhds t.val) :=
        (continuous_subtype_val.tendsto t).mono_left nhdsWithin_le_nhds
      have hpair : Tendsto (fun s => (g s, s.val)) l
          (nhds (g t, t.val)) := hg.prodMk_nhds htime
      simpa only [Function.comp_def] using
        (continuous_squeezedState_finite J).tendsto (g t, t.val) |>.comp hpair

private theorem exists_finite_trace_approach
    {S : Set ℝ} {J : Type*} (D : Set {u : ℝ // u ∈ S})
    (hside : ∀ t : {u : ℝ // u ∈ S}, t ∉ D →
      t ∈ closure (D ∩ Set.Iio t) ∧
      t ∈ closure (D ∩ Set.Ioi t))
    (f : PairedSkorokhodPath S J) (t : {u : ℝ // u ∈ S})
    (p : SqueezedState J)
    (hp : p = .finite (evalMinus f t) t.val ∨
      p = .finite (evalPlus f t) t.val) :
    ∃ (g : {u : ℝ // u ∈ S} → J → ℝ)
      (l : Filter {u : ℝ // u ∈ S}),
      NeBot l ∧ (∀ s, g s = evalMinus f s ∨ g s = evalPlus f s) ∧
      (∀ᶠ s in l, s ∈ D) ∧
      Tendsto (fun s => s.val) l (nhds t.val) ∧
      Tendsto (fun s => (SqueezedState.finite (g s) s.val : SqueezedState J))
        l (nhds p) := by
  rcases hp with hm | hp
  · obtain ⟨l, hne, hD, ht, hfin⟩ :=
      exists_trace_approach D t (evalMinus f) (Set.Iio t)
        (fun h => (hside t h).1)
        (pairedPath_oneSidedLimits_of_compactGraph f t).1.1
    refine ⟨evalMinus f, l, hne, (fun s => Or.inl rfl), hD, ht, ?_⟩
    simpa only [hm] using hfin
  · obtain ⟨l, hne, hD, ht, hfin⟩ :=
      exists_trace_approach D t (evalPlus f) (Set.Ioi t)
        (fun h => (hside t h).2)
        (pairedPath_oneSidedLimits_of_compactGraph f t).2.2
    refine ⟨evalPlus f, l, hne, (fun s => Or.inr rfl), hD, ht, ?_⟩
    simpa only [hp] using hfin

private theorem sampledState_mem_of_trace
    {S : Set ℝ} {J : Type*} (D : Set {u : ℝ // u ∈ S})
    (f : PairedSkorokhodPath S J)
    (g : {u : ℝ // u ∈ S} → J → ℝ)
    (hg : ∀ s, g s = evalMinus f s ∨ g s = evalPlus f s)
    (s : {u : ℝ // u ∈ S}) (hs : s ∈ D) :
    (SqueezedState.finite (g s) s.val : SqueezedState J) ∈ sampledState D f := by
  rcases hg s with hm | hp
  · exact Or.inr (Or.inr ⟨s, hs, Or.inl (by rw [hm])⟩)
  · exact Or.inr (Or.inr ⟨s, hs, Or.inr (by rw [hp])⟩)

private theorem exists_sampled_state_filter
    {S : Set ℝ} {J : Type*} (D : Set {u : ℝ // u ∈ S})
    (hside : ∀ t : {u : ℝ // u ∈ S}, t ∉ D →
      t ∈ closure (D ∩ Set.Iio t) ∧
      t ∈ closure (D ∩ Set.Ioi t))
    (f : PairedSkorokhodPath S J) (p : SqueezedState J)
    (hp : p ∈ pairedTraceGraph S f.1) :
    ∃ l : Filter (SqueezedState J), NeBot l ∧
      l ≤ nhds p ∧ (∀ᶠ a in l, a ∈ sampledState D f) := by
  rcases hp with hbot | htop | ⟨t, hm | hp⟩
  · refine ⟨pure p, inferInstance, ?_, ?_⟩
    · exact pure_le_nhds p
    · simpa only [eventually_pure] using (show p ∈ sampledState D f from Or.inl hbot)
  · refine ⟨pure p, inferInstance, ?_, ?_⟩
    · exact pure_le_nhds p
    · simpa only [eventually_pure] using
        (show p ∈ sampledState D f from Or.inr (Or.inl htop))
  · obtain ⟨g, l, hne, hg, hD, _, hfin⟩ :=
      exists_finite_trace_approach D hside f t p (Or.inl hm)
    let e : {u : ℝ // u ∈ S} → SqueezedState J :=
      fun s => .finite (g s) s.val
    refine ⟨Filter.map e l, (Filter.map_neBot_iff e).2 hne, ?_, ?_⟩
    · exact hfin
    · change ∀ᶠ s in l, e s ∈ sampledState D f
      exact hD.mono (fun s hs => sampledState_mem_of_trace D f g hg s hs)
  · obtain ⟨g, l, hne, hg, hD, _, hfin⟩ :=
      exists_finite_trace_approach D hside f t p (Or.inr hp)
    let e : {u : ℝ // u ∈ S} → SqueezedState J :=
      fun s => .finite (g s) s.val
    refine ⟨Filter.map e l, (Filter.map_neBot_iff e).2 hne, ?_, ?_⟩
    · exact hfin
    · change ∀ᶠ s in l, e s ∈ sampledState D f
      exact hD.mono (fun s hs => sampledState_mem_of_trace D f g hg s hs)

private theorem sampledPairs_of_diagonal
    {S : Set ℝ} {J : Type*} (D : Set {u : ℝ // u ∈ S})
    (f : PairedSkorokhodPath S J) {p : SqueezedState J}
    (hp : p ∈ sampledState D f) : (p, p) ∈ sampledPairs D f := by
  have hgraph := sampledState_mem_traceGraph D f hp
  exact ⟨⟨hgraph, hgraph, Or.inl rfl⟩, hp, hp⟩

private theorem sampledPairs_of_bottom
    {S : Set ℝ} {J : Type*} (D : Set {u : ℝ // u ∈ S})
    (f : PairedSkorokhodPath S J) {p : SqueezedState J}
    (hp : p ∈ sampledState D f) :
    ((.bottom : SqueezedState J), p) ∈ sampledPairs D f := by
  have hgraph := sampledState_mem_traceGraph D f hp
  exact ⟨⟨Or.inl rfl, hgraph, Or.inr (Or.inl rfl)⟩,
    Or.inl rfl, hp⟩

private theorem sampledPairs_of_top
    {S : Set ℝ} {J : Type*} (D : Set {u : ℝ // u ∈ S})
    (f : PairedSkorokhodPath S J) {p : SqueezedState J}
    (hp : p ∈ sampledState D f) :
    (p, (.top : SqueezedState J)) ∈ sampledPairs D f := by
  have hgraph := sampledState_mem_traceGraph D f hp
  exact ⟨⟨hgraph, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl))⟩,
    hp, Or.inr (Or.inl rfl)⟩

private theorem sampledPairs_of_strict
    {S : Set ℝ} {J : Type*} (D : Set {u : ℝ // u ∈ S})
    (f : PairedSkorokhodPath S J)
    (g h : {u : ℝ // u ∈ S} → J → ℝ)
    (hg : ∀ s, g s = evalMinus f s ∨ g s = evalPlus f s)
    (hh : ∀ s, h s = evalMinus f s ∨ h s = evalPlus f s)
    (s u : {u : ℝ // u ∈ S}) (hs : s ∈ D) (hu : u ∈ D)
    (hsu : s.val < u.val) :
    ((.finite (g s) s.val : SqueezedState J),
      (.finite (h u) u.val : SqueezedState J)) ∈ sampledPairs D f := by
  have hgs := sampledState_mem_of_trace D f g hg s hs
  have hhu := sampledState_mem_of_trace D f h hh u hu
  refine ⟨?_, hgs, hhu⟩
  exact ⟨sampledState_mem_traceGraph D f hgs,
    sampledState_mem_traceGraph D f hhu,
    Or.inr (Or.inr (Or.inr (Or.inl
      ⟨g s, h u, s.val, u.val, rfl, rfl, hsu⟩)))⟩

private theorem pair_mem_closure_of_strict_approaches
    {S : Set ℝ} {J : Type*} (D : Set {u : ℝ // u ∈ S})
    (f : PairedSkorokhodPath S J)
    (g h : {u : ℝ // u ∈ S} → J → ℝ)
    (hg : ∀ s, g s = evalMinus f s ∨ g s = evalPlus f s)
    (hh : ∀ s, h s = evalMinus f s ∨ h s = evalPlus f s)
    (l m : Filter {u : ℝ // u ∈ S})
    (hl : NeBot l) (hm : NeBot m)
    (hlD : ∀ᶠ s in l, s ∈ D) (hmD : ∀ᶠ u in m, u ∈ D)
    (p q : SqueezedState J)
    (hp : Tendsto (fun s => (SqueezedState.finite (g s) s.val : SqueezedState J))
      l (nhds p))
    (hq : Tendsto (fun u => (SqueezedState.finite (h u) u.val : SqueezedState J))
      m (nhds q))
    (horder : ∀ᶠ su in l ×ˢ m, su.1.val < su.2.val) :
    (p, q) ∈ closure (sampledPairs D f) := by
  let : NeBot l := hl
  let : NeBot m := hm
  have hfirst : Tendsto
      (fun su : {u : ℝ // u ∈ S} × {u : ℝ // u ∈ S} =>
        (SqueezedState.finite (g su.1) su.1.val : SqueezedState J))
      (l ×ˢ m) (nhds p) := hp.comp Filter.tendsto_fst
  have hsecond : Tendsto
      (fun su : {u : ℝ // u ∈ S} × {u : ℝ // u ∈ S} =>
        (SqueezedState.finite (h su.2) su.2.val : SqueezedState J))
      (l ×ˢ m) (nhds q) := hq.comp Filter.tendsto_snd
  have hpair := hfirst.prodMk_nhds hsecond
  apply mem_closure_of_tendsto hpair
  filter_upwards [hlD.prod_mk hmD, horder] with su hD hlt
  exact sampledPairs_of_strict D f g h hg hh su.1 su.2 hD.1 hD.2 hlt

private theorem trace_witness_of_finite
    {S : Set ℝ} {J : Type*} (f : PairedSkorokhodPath S J)
    {p : SqueezedState J} {x : J → ℝ} {u : ℝ}
    (hp : p ∈ pairedTraceGraph S f.1)
    (hfinite : p = .finite x u) :
    ∃ t : {v : ℝ // v ∈ S},
      p = .finite (evalMinus f t) t.val ∨
      p = .finite (evalPlus f t) t.val := by
  rcases hp with hbot | htop | ⟨t, hm | hp⟩
  · rw [hbot] at hfinite
    cases hfinite
  · rw [htop] at hfinite
    cases hfinite
  · exact ⟨t, Or.inl hm⟩
  · exact ⟨t, Or.inr hp⟩

/-- Sided samples of both coordinates are dense in the literal compact
ordered-pair graph, including its poles and equal-time directed pair. -/
theorem pairedPathOrderGraph_eq_closure_sidedSamples
    {S : Set ℝ} {J : Type*}
    (D : Set {u : ℝ // u ∈ S})
    (hside : ∀ t : {u : ℝ // u ∈ S}, t ∉ D →
      t ∈ closure (D ∩ Set.Iio t) ∧
      t ∈ closure (D ∩ Set.Ioi t))
    (f : PairedSkorokhodPath S J) :
    pairedPathOrderGraph S J f =
      closure {z : SqueezedState J × SqueezedState J |
        z ∈ pairedPathOrderGraph S J f ∧
        (z.1 = .bottom ∨ z.1 = .top ∨
          ∃ t : {u : ℝ // u ∈ S}, t ∈ D ∧
            (z.1 = .finite (evalMinus f t) t.val ∨
             z.1 = .finite (evalPlus f t) t.val)) ∧
        (z.2 = .bottom ∨ z.2 = .top ∨
          ∃ t : {u : ℝ // u ∈ S}, t ∈ D ∧
            (z.2 = .finite (evalMinus f t) t.val ∨
             z.2 = .finite (evalPlus f t) t.val))} := by
  classical
  change pairedPathOrderGraph S J f = closure (sampledPairs D f)
  have hemb : Topology.IsEmbedding (squeezedStateEmbedding J) := by
    change @Topology.IsEmbedding (SqueezedState J) (ℝ × (J → ℝ))
      (squeezedStateTopology J) inferInstance (squeezedStateEmbedding J)
    exact Topology.IsEmbedding.induced (squeezedStateEmbedding_injective J)
  have : T2Space (SqueezedState J) := hemb.t2Space
  have hclosed : IsClosed (pairedPathOrderGraph S J f) := f.2.isClosed
  apply Set.Subset.antisymm
  · intro z hz
    change z ∈ pairedOrderGraph S f.1 at hz
    obtain ⟨hp, hq, hrel⟩ := hz
    rcases hrel with heq | hbot | htop |
      ⟨x, y, u, v, hpfinite, hqfinite, huv⟩ | ⟨t, hpminus, hqplus⟩
    · obtain ⟨l, hne, hl, hsamp⟩ :=
        exists_sampled_state_filter D hside f z.1 hp
      let : NeBot l := hne
      have hlimState : Tendsto (fun a : SqueezedState J => a) l
          (nhds z.1) := hl
      have hlim : Tendsto (fun a : SqueezedState J => (a, a)) l
          (nhds (z.1, z.1)) := hlimState.prodMk_nhds hlimState
      have hmem : ∀ᶠ a in l, (a, a) ∈ sampledPairs D f :=
        hsamp.mono (fun a ha => sampledPairs_of_diagonal D f ha)
      have hclosure := mem_closure_of_tendsto hlim hmem
      have hzeq : z = (z.1, z.1) := Prod.ext rfl heq.symm
      rw [hzeq]
      exact hclosure
    · obtain ⟨l, hne, hl, hsamp⟩ :=
        exists_sampled_state_filter D hside f z.2 hq
      let : NeBot l := hne
      have hlimState : Tendsto (fun a : SqueezedState J => a) l
          (nhds z.2) := hl
      have hlim : Tendsto (fun a : SqueezedState J =>
          ((.bottom : SqueezedState J), a)) l
          (nhds ((.bottom : SqueezedState J), z.2)) :=
        tendsto_const_nhds.prodMk_nhds hlimState
      have hmem : ∀ᶠ a in l,
          ((.bottom : SqueezedState J), a) ∈ sampledPairs D f :=
        hsamp.mono (fun a ha => sampledPairs_of_bottom D f ha)
      have hclosure := mem_closure_of_tendsto hlim hmem
      have hzeq : z = ((.bottom : SqueezedState J), z.2) :=
        Prod.ext hbot rfl
      rw [hzeq]
      exact hclosure
    · obtain ⟨l, hne, hl, hsamp⟩ :=
        exists_sampled_state_filter D hside f z.1 hp
      let : NeBot l := hne
      have hlimState : Tendsto (fun a : SqueezedState J => a) l
          (nhds z.1) := hl
      have hlim : Tendsto (fun a : SqueezedState J =>
          (a, (.top : SqueezedState J))) l
          (nhds (z.1, (.top : SqueezedState J))) :=
        hlimState.prodMk_nhds tendsto_const_nhds
      have hmem : ∀ᶠ a in l,
          (a, (.top : SqueezedState J)) ∈ sampledPairs D f :=
        hsamp.mono (fun a ha => sampledPairs_of_top D f ha)
      have hclosure := mem_closure_of_tendsto hlim hmem
      have hzeq : z = (z.1, (.top : SqueezedState J)) :=
        Prod.ext rfl htop
      rw [hzeq]
      exact hclosure
    · obtain ⟨tu, hpu⟩ := trace_witness_of_finite f hp hpfinite
      obtain ⟨tv, hqv⟩ := trace_witness_of_finite f hq hqfinite
      obtain ⟨g, l, hneL, hg, hD1, htime1, hfirst⟩ :=
        exists_finite_trace_approach D hside f tu z.1 hpu
      obtain ⟨h, m, hneM, hh, hD2, htime2, hsecond⟩ :=
        exists_finite_trace_approach D hside f tv z.2 hqv
      have htu : u = tu.val := by
        rcases hpu with hminus | hplus
        · exact (SqueezedState.finite.inj (hpfinite.symm.trans hminus)).2
        · exact (SqueezedState.finite.inj (hpfinite.symm.trans hplus)).2
      have htv : v = tv.val := by
        rcases hqv with hminus | hplus
        · exact (SqueezedState.finite.inj (hqfinite.symm.trans hminus)).2
        · exact (SqueezedState.finite.inj (hqfinite.symm.trans hplus)).2
      have hstrict : tu.val < tv.val := by simpa only [← htu, ← htv] using huv
      have horder : ∀ᶠ su in l ×ˢ m, su.1.val < su.2.val :=
        (htime1.comp Filter.tendsto_fst).eventually_lt
          (htime2.comp Filter.tendsto_snd) hstrict
      exact pair_mem_closure_of_strict_approaches D f g h hg hh l m
        hneL hneM hD1 hD2 z.1 z.2 hfirst hsecond horder
    · by_cases htD : t ∈ D
      · have hfirst : z.1 ∈ sampledState D f :=
          Or.inr (Or.inr ⟨t, htD, Or.inl hpminus⟩)
        have hsecond : z.2 ∈ sampledState D f :=
          Or.inr (Or.inr ⟨t, htD, Or.inr hqplus⟩)
        exact subset_closure ⟨⟨hp, hq,
          Or.inr (Or.inr (Or.inr (Or.inr ⟨t, hpminus, hqplus⟩)))⟩,
          hfirst, hsecond⟩
      · let l := nhdsWithin t (D ∩ Set.Iio t)
        let m := nhdsWithin t (D ∩ Set.Ioi t)
        have hneL : NeBot l :=
          mem_closure_iff_nhdsWithin_neBot.mp (hside t htD).1
        have hneM : NeBot m :=
          mem_closure_iff_nhdsWithin_neBot.mp (hside t htD).2
        have hmemL : ∀ᶠ s in l, s ∈ D ∧ s < t := self_mem_nhdsWithin
        have hmemM : ∀ᶠ s in m, s ∈ D ∧ t < s := self_mem_nhdsWithin
        have hD1 : ∀ᶠ s in l, s ∈ D := hmemL.mono (fun _ hs => hs.1)
        have hD2 : ∀ᶠ s in m, s ∈ D := hmemM.mono (fun _ hs => hs.1)
        have hlimL : Tendsto (evalMinus f) l (nhds (evalMinus f t)) :=
          (pairedPath_oneSidedLimits_of_compactGraph f t).1.1.mono_left
            (nhdsWithin_mono t Set.inter_subset_right)
        have hlimM : Tendsto (evalPlus f) m (nhds (evalPlus f t)) :=
          (pairedPath_oneSidedLimits_of_compactGraph f t).2.2.mono_left
            (nhdsWithin_mono t Set.inter_subset_right)
        have htimeL : Tendsto (fun s : {u : ℝ // u ∈ S} => s.val)
            l (nhds t.val) :=
          (continuous_subtype_val.tendsto t).mono_left nhdsWithin_le_nhds
        have htimeM : Tendsto (fun s : {u : ℝ // u ∈ S} => s.val)
            m (nhds t.val) :=
          (continuous_subtype_val.tendsto t).mono_left nhdsWithin_le_nhds
        have hfirst : Tendsto (fun s =>
            (SqueezedState.finite (evalMinus f s) s.val : SqueezedState J))
            l (nhds z.1) := by
          have hpair := hlimL.prodMk_nhds htimeL
          have hfin := (continuous_squeezedState_finite J).tendsto
            (evalMinus f t, t.val) |>.comp hpair
          rw [hpminus]
          simpa only [Function.comp_def, evalMinus] using hfin
        have hsecond : Tendsto (fun s =>
            (SqueezedState.finite (evalPlus f s) s.val : SqueezedState J))
            m (nhds z.2) := by
          have hpair := hlimM.prodMk_nhds htimeM
          have hfin := (continuous_squeezedState_finite J).tendsto
            (evalPlus f t, t.val) |>.comp hpair
          rw [hqplus]
          simpa only [Function.comp_def, evalPlus] using hfin
        have horder : ∀ᶠ su in l ×ˢ m, su.1.val < su.2.val :=
          (hmemL.prod_mk hmemM).mono (fun su hs => lt_trans hs.1.2 hs.2.2)
        exact pair_mem_closure_of_strict_approaches D f
          (evalMinus f) (evalPlus f)
          (fun _ => Or.inl rfl) (fun _ => Or.inr rfl)
          l m hneL hneM hD1 hD2 z.1 z.2 hfirst hsecond horder
  · exact closure_minimal (fun z hz => hz.1) hclosed

end LPP.Busemann
