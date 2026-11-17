/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.StrongExistence.Definitions.EvalPlus
public import Busemann.Topology.SqueezedStateLimits
import Busemann.Topology.SqueezedStateEmbedding
import Busemann.Topology.SqueezedFiniteChart
import Mathlib.Topology.Ultrafilter

/-!
# Relative limits of compact ordered-pair paths

Compactness and the literal equal-time order determine both traces from either
available side of a time. The argument uses compact filters, with no countability
assumption on the coordinate type.
-/

@[expose] public section
open Filter
namespace LPP.Busemann

private theorem compressReal_abs_lt_one (a : ℝ) : |compressReal a| < 1 := by
  have hden : 0 < 1 + |a| := by positivity
  rw [compressReal, abs_div, abs_of_pos hden]
  exact (div_lt_one hden).2 (by linarith [abs_nonneg a])

private theorem compressReal_recover (a : ℝ) :
    compressReal a / (1 - |compressReal a|) = a := by
  have hden : 1 + |a| ≠ 0 := ne_of_gt (by positivity)
  have habs : |compressReal a| = |a| / (1 + |a|) := by
    rw [compressReal, abs_div, abs_of_pos (by positivity : 0 < 1 + |a|)]
  have hrest : 1 - |compressReal a| = 1 / (1 + |a|) := by
    rw [habs]
    field_simp [hden]
    ring
  rw [hrest, compressReal]
  field_simp [hden]

private theorem compressReal_injective : Function.Injective compressReal := by
  intro a b hab
  have h := congrArg (fun u : ℝ => u / (1 - |u|)) hab
  simpa only [compressReal_recover] using h

private theorem continuous_compressReal : Continuous compressReal := by
  rw [continuous_iff_continuousAt]
  intro a
  change ContinuousAt (fun b : ℝ => b / (1 + |b|)) a
  exact continuousAt_id.div
    (continuousAt_const.add continuous_abs.continuousAt)
    (ne_of_gt (by positivity))

private theorem cluster_image_eq_of_tendsto
    {α X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {l : Filter α} {u : α → X} {x : X} {g : X → Y} {y : Y}
    (hcluster : MapClusterPt x l u) (hg : Continuous g)
    (ht : Tendsto (g ∘ u) l (nhds y)) : g x = y := by
  obtain ⟨U, hU, hu⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  have hfirst : Tendsto (g ∘ u) U (nhds (g x)) :=
    (hg.tendsto x).comp hu
  have hsecond : Tendsto (g ∘ u) U (nhds y) := ht.mono_left hU
  exact tendsto_nhds_unique hfirst hsecond

private theorem left_equal_time_order
    {S : Set ℝ} {J : Type*} (f : RawPairedTrace S J)
    (t : {u : ℝ // u ∈ S}) (a : J → ℝ)
    (h : pairedTraceLE S f (.finite a t.val) (.finite (f.1 t) t.val)) :
    a = f.1 t := by
  rcases h with h | h | h | ⟨x, y, u, v, hp, hq, huv⟩ | ⟨s, hp, _⟩
  · exact (SqueezedState.finite.inj h).1
  · cases h
  · cases h
  · have hu : t.val = u := (SqueezedState.finite.inj hp).2
    have hv : v = t.val := (SqueezedState.finite.inj hq).2.symm
    rw [← hu, hv] at huv
    exact (lt_irrefl _ huv).elim
  · have ha : a = f.1 s := (SqueezedState.finite.inj hp).1
    have hs : t = s := Subtype.ext (SqueezedState.finite.inj hp).2
    simpa [hs] using ha

private theorem right_equal_time_order
    {S : Set ℝ} {J : Type*} (f : RawPairedTrace S J)
    (t : {u : ℝ // u ∈ S}) (a : J → ℝ)
    (h : pairedTraceLE S f (.finite (f.2 t) t.val) (.finite a t.val)) :
    a = f.2 t := by
  rcases h with h | h | h | ⟨x, y, u, v, hp, hq, huv⟩ | ⟨s, _, hq⟩
  · exact (SqueezedState.finite.inj h).1.symm
  · cases h
  · cases h
  · have hu : t.val = u := (SqueezedState.finite.inj hp).2
    have hv : v = t.val := (SqueezedState.finite.inj hq).2.symm
    rw [← hu, hv] at huv
    exact (lt_irrefl _ huv).elim
  · have ha : a = f.2 s := (SqueezedState.finite.inj hq).1
    have hs : t = s := Subtype.ext (SqueezedState.finite.inj hq).2
    simpa [hs] using ha

private theorem left_trace_limit
    {S : Set ℝ} {J : Type*} (f : PairedSkorokhodPath S J)
    (t : {u : ℝ // u ∈ S}) (g : {u : ℝ // u ∈ S} → J → ℝ)
    (hg : ∀ s, g s = evalMinus f s ∨ g s = evalPlus f s) :
    Tendsto g (nhdsWithin t (Set.Iio t)) (nhds (evalMinus f t)) := by
  have hemb : Topology.IsEmbedding (squeezedStateEmbedding J) := by
    change @Topology.IsEmbedding (SqueezedState J) (ℝ × (J → ℝ))
      (squeezedStateTopology J) inferInstance (squeezedStateEmbedding J)
    exact Topology.IsEmbedding.induced (squeezedStateEmbedding_injective J)
  have : T2Space (SqueezedState J) := hemb.t2Space
  let pair : {u : ℝ // u ∈ S} → SqueezedState J × SqueezedState J :=
    fun s => (.finite (g s) s.val, .finite (evalMinus f t) t.val)
  have hmem : ∀ᶠ s in nhdsWithin t (Set.Iio t),
      pair s ∈ pairedOrderGraph S f.1 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    change (SqueezedState.finite (g s) s.val) ∈ pairedTraceGraph S f.1 ∧
      (SqueezedState.finite (evalMinus f t) t.val) ∈ pairedTraceGraph S f.1 ∧
      pairedTraceLE S f.1 (.finite (g s) s.val) (.finite (evalMinus f t) t.val)
    refine ⟨?_, ?_, ?_⟩
    · rcases hg s with hm | hp
      · exact Or.inr (Or.inr ⟨s, Or.inl (by rw [hm]; rfl)⟩)
      · exact Or.inr (Or.inr ⟨s, Or.inr (by rw [hp]; rfl)⟩)
    · exact Or.inr (Or.inr ⟨t, Or.inl rfl⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨g s, evalMinus f t, s.val, t.val, rfl, rfl, hs⟩)))
  have hclock : Continuous (fun z : SqueezedState J × SqueezedState J =>
      (squeezedStateEmbedding J z.1).1) :=
    hemb.continuous.fst.comp continuous_fst
  have htime : Tendsto (fun s : {u : ℝ // u ∈ S} => compressReal s.val)
      (nhdsWithin t (Set.Iio t)) (nhds (compressReal t.val)) :=
    ((continuous_compressReal.comp continuous_subtype_val).tendsto t).mono_left
      nhdsWithin_le_nhds
  have hunique : ∀ z ∈ pairedOrderGraph S f.1,
      MapClusterPt z (nhdsWithin t (Set.Iio t)) pair →
        z = (.finite (evalMinus f t) t.val,
          .finite (evalMinus f t) t.val) := by
    intro z hz hcluster
    have hzfixed : z.2 = .finite (evalMinus f t) t.val := by
      apply cluster_image_eq_of_tendsto hcluster continuous_snd
      exact tendsto_const_nhds
    have hzclock : (squeezedStateEmbedding J z.1).1 =
        compressReal t.val := by
      apply cluster_image_eq_of_tendsto hcluster hclock
      exact htime
    have horder : pairedTraceLE S f.1 z.1 z.2 := hz.2.2
    cases hzstate : z.1 with
    | bottom =>
        have hfalse : (-1 : ℝ) = compressReal t.val := by
          simpa [hzstate, squeezedStateEmbedding] using hzclock
        have hlower := (abs_lt.mp (compressReal_abs_lt_one t.val)).1
        linarith
    | top =>
        have hfalse : (1 : ℝ) = compressReal t.val := by
          simpa [hzstate, squeezedStateEmbedding] using hzclock
        have hupper := (abs_lt.mp (compressReal_abs_lt_one t.val)).2
        linarith
    | finite a u =>
        have hcompressed : compressReal u = compressReal t.val := by
          simpa [hzstate, squeezedStateEmbedding] using hzclock
        have hu : u = t.val := compressReal_injective hcompressed
        rw [hzstate, hzfixed, hu] at horder
        change pairedTraceLE S f.1 (.finite a t.val)
          (.finite (f.1.1 t) t.val) at horder
        have ha := left_equal_time_order f.1 t a horder
        apply Prod.ext
        · simp [hzstate, hu, ha, evalMinus]
        · exact hzfixed
  have hpair : Tendsto pair (nhdsWithin t (Set.Iio t))
      (nhds (.finite (evalMinus f t) t.val,
        .finite (evalMinus f t) t.val)) :=
    f.2.tendsto_nhds_of_unique_mapClusterPt hmem hunique
  have hfinite : Tendsto (fun s : {u : ℝ // u ∈ S} =>
      (SqueezedState.finite (g s) s.val : SqueezedState J))
      (nhdsWithin t (Set.Iio t))
      (nhds (.finite (evalMinus f t) t.val)) := by
    simpa only [pair, Function.comp_def] using (continuous_fst.tendsto _).comp hpair
  have htuple : Tendsto (fun s : {u : ℝ // u ∈ S} => (g s, s.val))
      (nhdsWithin t (Set.Iio t)) (nhds (evalMinus f t, t.val)) := by
    apply (squeezedState_finite_isEmbedding J).tendsto_nhds_iff.mpr
    simpa only [Function.comp_def] using hfinite
  exact (continuous_fst.tendsto _).comp htuple

private theorem right_trace_limit
    {S : Set ℝ} {J : Type*} (f : PairedSkorokhodPath S J)
    (t : {u : ℝ // u ∈ S}) (g : {u : ℝ // u ∈ S} → J → ℝ)
    (hg : ∀ s, g s = evalMinus f s ∨ g s = evalPlus f s) :
    Tendsto g (nhdsWithin t (Set.Ioi t)) (nhds (evalPlus f t)) := by
  have hemb : Topology.IsEmbedding (squeezedStateEmbedding J) := by
    change @Topology.IsEmbedding (SqueezedState J) (ℝ × (J → ℝ))
      (squeezedStateTopology J) inferInstance (squeezedStateEmbedding J)
    exact Topology.IsEmbedding.induced (squeezedStateEmbedding_injective J)
  have : T2Space (SqueezedState J) := hemb.t2Space
  let pair : {u : ℝ // u ∈ S} → SqueezedState J × SqueezedState J :=
    fun s => (.finite (evalPlus f t) t.val, .finite (g s) s.val)
  have hmem : ∀ᶠ s in nhdsWithin t (Set.Ioi t),
      pair s ∈ pairedOrderGraph S f.1 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    change (SqueezedState.finite (evalPlus f t) t.val) ∈ pairedTraceGraph S f.1 ∧
      (SqueezedState.finite (g s) s.val) ∈ pairedTraceGraph S f.1 ∧
      pairedTraceLE S f.1 (.finite (evalPlus f t) t.val) (.finite (g s) s.val)
    refine ⟨?_, ?_, ?_⟩
    · exact Or.inr (Or.inr ⟨t, Or.inr rfl⟩)
    · rcases hg s with hm | hp
      · exact Or.inr (Or.inr ⟨s, Or.inl (by rw [hm]; rfl)⟩)
      · exact Or.inr (Or.inr ⟨s, Or.inr (by rw [hp]; rfl)⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨evalPlus f t, g s, t.val, s.val, rfl, rfl, hs⟩)))
  have hclock : Continuous (fun z : SqueezedState J × SqueezedState J =>
      (squeezedStateEmbedding J z.2).1) :=
    hemb.continuous.fst.comp continuous_snd
  have htime : Tendsto (fun s : {u : ℝ // u ∈ S} => compressReal s.val)
      (nhdsWithin t (Set.Ioi t)) (nhds (compressReal t.val)) :=
    ((continuous_compressReal.comp continuous_subtype_val).tendsto t).mono_left
      nhdsWithin_le_nhds
  have hunique : ∀ z ∈ pairedOrderGraph S f.1,
      MapClusterPt z (nhdsWithin t (Set.Ioi t)) pair →
        z = (.finite (evalPlus f t) t.val,
          .finite (evalPlus f t) t.val) := by
    intro z hz hcluster
    have hzfixed : z.1 = .finite (evalPlus f t) t.val := by
      apply cluster_image_eq_of_tendsto hcluster continuous_fst
      exact tendsto_const_nhds
    have hzclock : (squeezedStateEmbedding J z.2).1 =
        compressReal t.val := by
      apply cluster_image_eq_of_tendsto hcluster hclock
      exact htime
    have horder : pairedTraceLE S f.1 z.1 z.2 := hz.2.2
    cases hzstate : z.2 with
    | bottom =>
        have hfalse : (-1 : ℝ) = compressReal t.val := by
          simpa [hzstate, squeezedStateEmbedding] using hzclock
        have hlower := (abs_lt.mp (compressReal_abs_lt_one t.val)).1
        linarith
    | top =>
        have hfalse : (1 : ℝ) = compressReal t.val := by
          simpa [hzstate, squeezedStateEmbedding] using hzclock
        have hupper := (abs_lt.mp (compressReal_abs_lt_one t.val)).2
        linarith
    | finite a u =>
        have hcompressed : compressReal u = compressReal t.val := by
          simpa [hzstate, squeezedStateEmbedding] using hzclock
        have hu : u = t.val := compressReal_injective hcompressed
        rw [hzfixed, hzstate, hu] at horder
        have ha := right_equal_time_order f.1 t a horder
        apply Prod.ext
        · exact hzfixed
        · simp [hzstate, hu, ha, evalPlus]
  have hpair : Tendsto pair (nhdsWithin t (Set.Ioi t))
      (nhds (.finite (evalPlus f t) t.val,
        .finite (evalPlus f t) t.val)) :=
    f.2.tendsto_nhds_of_unique_mapClusterPt hmem hunique
  have hfinite : Tendsto (fun s : {u : ℝ // u ∈ S} =>
      (SqueezedState.finite (g s) s.val : SqueezedState J))
      (nhdsWithin t (Set.Ioi t))
      (nhds (.finite (evalPlus f t) t.val)) := by
    simpa only [pair, Function.comp_def] using (continuous_snd.tendsto _).comp hpair
  have htuple : Tendsto (fun s : {u : ℝ // u ∈ S} => (g s, s.val))
      (nhdsWithin t (Set.Ioi t)) (nhds (evalPlus f t, t.val)) := by
    apply (squeezedState_finite_isEmbedding J).tendsto_nhds_iff.mpr
    simpa only [Function.comp_def] using hfinite
  exact (continuous_fst.tendsto _).comp htuple

/-- Compactness of the existing ordered-pair graph forces both traces to have
the prescribed relative one-sided limits. A missing side has a bottom
within-filter, so this also covers endpoints and gaps in the time set. -/
theorem pairedPath_oneSidedLimits_of_compactGraph
    {S : Set ℝ} {J : Type*} (f : PairedSkorokhodPath S J)
    (t : {u : ℝ // u ∈ S}) :
    (Tendsto (evalMinus f) (nhdsWithin t (Set.Iio t))
        (nhds (evalMinus f t)) ∧
      Tendsto (evalPlus f) (nhdsWithin t (Set.Iio t))
        (nhds (evalMinus f t))) ∧
    (Tendsto (evalMinus f) (nhdsWithin t (Set.Ioi t))
        (nhds (evalPlus f t)) ∧
      Tendsto (evalPlus f) (nhdsWithin t (Set.Ioi t))
        (nhds (evalPlus f t))) := by
  constructor
  · constructor
    · exact left_trace_limit f t (evalMinus f) (fun _ => Or.inl rfl)
    · exact left_trace_limit f t (evalPlus f) (fun _ => Or.inr rfl)
  · constructor
    · exact right_trace_limit f t (evalMinus f) (fun _ => Or.inl rfl)
    · exact right_trace_limit f t (evalPlus f) (fun _ => Or.inr rfl)

end LPP.Busemann
