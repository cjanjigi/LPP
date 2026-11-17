/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Topology.FiniteOrderedPairSubsequence
public import Busemann.Topology.SqueezedStateLimits
public import Busemann.Frozen.StrongExistence.Definitions.PairedOrderGraph
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Compactness of the paired ordered graph

The finite-pair subsequence theorem handles two finite endpoints at once.
This module adds the endpoint-category argument and converts sequential
compactness to compactness in the induced topology.
-/

@[expose] public section
open Filter
open scoped Topology
namespace LPP.Busemann

private def pairedGraphEndpointKind {J : Type*} : SqueezedState J →
    Ordering
  | .bottom => .lt
  | .top => .eq
  | .finite _ _ => .gt

private theorem state_eq_bottom_of_kind_eq_bottom {J : Type*}
    {x : SqueezedState J}
    (h : pairedGraphEndpointKind x = .lt) : x = .bottom := by
  cases x <;> simp_all [pairedGraphEndpointKind]

private theorem state_eq_top_of_kind_eq_top {J : Type*}
    {x : SqueezedState J}
    (h : pairedGraphEndpointKind x = .eq) : x = .top := by
  cases x <;> simp_all [pairedGraphEndpointKind]

private theorem finite_trace_witness_of_graph_kind {S : Set ℝ} {J : Type*}
    {f : RawPairedTrace S J} {x : SqueezedState J}
    (hx : x ∈ pairedTraceGraph S f)
    (hkind : pairedGraphEndpointKind x = .gt) :
    ∃ t : {u : ℝ // u ∈ S},
      x = .finite (f.1 t) t.val ∨ x = .finite (f.2 t) t.val := by
  change x = .bottom ∨ x = .top ∨
    ∃ t : {u : ℝ // u ∈ S},
      x = .finite (f.1 t) t.val ∨ x = .finite (f.2 t) t.val at hx
  rcases hx with hbottom | htop | ⟨t, htrace⟩
  · subst x
    simp [pairedGraphEndpointKind] at hkind
  · subst x
    simp [pairedGraphEndpointKind] at hkind
  · exact ⟨t, htrace⟩

private theorem stable_finite_color {C : Type*} [Finite C] (c : ℕ → C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ k : C, ∀ n, c (φ n) = k := by
  classical
  obtain ⟨k, hk⟩ := Finite.exists_infinite_fiber c
  obtain ⟨φ, hφ, hcolor⟩ := Nat.exists_strictMono_subsequence
    (P := fun n => c n = k) (by
      intro N
      obtain ⟨n, hn, hgt⟩ := (Set.infinite_coe_iff.1 hk).exists_gt N
      exact ⟨n, hgt, hn⟩)
  exact ⟨φ, hφ, k, hcolor⟩

/-- The four relative one-sided trace limits make the ordered graph compact.
The graph and carrier are `PairedOrderGraph.lean:11` and
`PairedSkorokhodPath.lean:11`. At a missing side the within-neighborhood
filter is bottom, so no endpoint equality is imposed. This includes empty
and disconnected closed time sets. -/
theorem pairedOrderGraph_isCompact_of_oneSidedLimits
    {S : Set ℝ} {J : Type*} [Countable J]
    (hS : IsClosed S) (f : RawPairedTrace S J)
    (hleft : ∀ t : {u : ℝ // u ∈ S},
      Tendsto f.1 (nhdsWithin t (Set.Iio t)) (nhds (f.1 t)) ∧
      Tendsto f.2 (nhdsWithin t (Set.Iio t)) (nhds (f.1 t)))
    (hright : ∀ t : {u : ℝ // u ∈ S},
      Tendsto f.1 (nhdsWithin t (Set.Ioi t)) (nhds (f.2 t)) ∧
      Tendsto f.2 (nhdsWithin t (Set.Ioi t)) (nhds (f.2 t))) :
    IsCompact (pairedOrderGraph S f) := by
  -- Compactness follows from sequential compactness once the actual topology is pseudometrizable.
  have hseqcompact : IsSeqCompact (pairedOrderGraph S f) := by
    intro z hz
    classical
    -- Stabilize the pair of endpoint kinds on one infinite subsequence.
    let color : ℕ → Ordering × Ordering := fun n =>
      (pairedGraphEndpointKind (z n).1, pairedGraphEndpointKind (z n).2)
    obtain ⟨φ, hφ, k, hk⟩ := stable_finite_color color
    have hkindX (n : ℕ) : pairedGraphEndpointKind (z (φ n)).1 = k.1 := by
      have h := congrArg Prod.fst (hk n)
      simpa [color] using h
    have hkindY (n : ℕ) : pairedGraphEndpointKind (z (φ n)).2 = k.2 := by
      have h := congrArg Prod.snd (hk n)
      simpa [color] using h
    have hmemX (n : ℕ) : (z (φ n)).1 ∈ pairedTraceGraph S f := by
      have h := hz (φ n)
      change (z (φ n)).1 ∈ pairedTraceGraph S f ∧
        (z (φ n)).2 ∈ pairedTraceGraph S f ∧
        pairedTraceLE S f (z (φ n)).1 (z (φ n)).2 at h
      exact h.1
    have hmemY (n : ℕ) : (z (φ n)).2 ∈ pairedTraceGraph S f := by
      have h := hz (φ n)
      change (z (φ n)).1 ∈ pairedTraceGraph S f ∧
        (z (φ n)).2 ∈ pairedTraceGraph S f ∧
        pairedTraceLE S f (z (φ n)).1 (z (φ n)).2 at h
      exact h.2.1
    have horder (n : ℕ) :
        pairedTraceLE S f (z (φ n)).1 (z (φ n)).2 := by
      have h := hz (φ n)
      change (z (φ n)).1 ∈ pairedTraceGraph S f ∧
        (z (φ n)).2 ∈ pairedTraceGraph S f ∧
        pairedTraceLE S f (z (φ n)).1 (z (φ n)).2 at h
      exact h.2.2
    -- The two pole pairs with bottom first and top second are constant.
    cases hkindFirst : k.1 with
    | lt =>
      have hbottomX (n : ℕ) : (z (φ n)).1 = .bottom :=
        state_eq_bottom_of_kind_eq_bottom ((hkindX n).trans hkindFirst)
      cases hkindSecond : k.2 with
      | lt =>
        have hbottomY (n : ℕ) : (z (φ n)).2 = .bottom :=
          state_eq_bottom_of_kind_eq_bottom ((hkindY n).trans hkindSecond)
        refine ⟨(.bottom, .bottom), ?_, φ, hφ, ?_⟩
        · exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
        · apply Tendsto.congr' ?_ tendsto_const_nhds
          exact Filter.Eventually.of_forall
            (fun n => Prod.ext (hbottomX n).symm (hbottomY n).symm)
      | eq =>
        have htopY (n : ℕ) : (z (φ n)).2 = .top :=
          state_eq_top_of_kind_eq_top ((hkindY n).trans hkindSecond)
        refine ⟨(.bottom, .top), ?_, φ, hφ, ?_⟩
        · exact ⟨Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inl rfl)⟩
        · apply Tendsto.congr' ?_ tendsto_const_nhds
          exact Filter.Eventually.of_forall
            (fun n => Prod.ext (hbottomX n).symm (htopY n).symm)
      | gt =>
        -- A diagonal finite pair supplies a convergent subsequence for the second endpoint.
        have hfiniteWitness (n : ℕ) :=
          finite_trace_witness_of_graph_kind (hmemY n) ((hkindY n).trans hkindSecond)
        let b : ℕ → {u : ℝ // u ∈ S} := fun n => Classical.choose (hfiniteWitness n)
        have hb (n : ℕ) :
            (z (φ n)).2 = .finite (f.1 (b n)) (b n).val ∨
              (z (φ n)).2 = .finite (f.2 (b n)) (b n).val :=
          Classical.choose_spec (hfiniteWitness n)
        obtain ⟨w, hw, θ, hθ, hconv⟩ := finite_ordered_pair_subsequence
          hS f hleft hright b b (fun n => (z (φ n)).2) (fun n => (z (φ n)).2)
          hb hb (fun _ => Or.inl rfl)
        have hfiniteConv : Tendsto (fun n => (z (φ (θ n))).2) atTop (𝓝 w.2) := by
          simpa using hconv.snd_nhds
        have hbottomConv :
            Tendsto (fun n => (z (φ (θ n))).1) atTop
              (𝓝 (SqueezedState.bottom : SqueezedState J)) := by
          apply Tendsto.congr' ?_ tendsto_const_nhds
          exact Filter.Eventually.of_forall (fun n => (hbottomX (θ n)).symm)
        change w.1 ∈ pairedTraceGraph S f ∧ w.2 ∈ pairedTraceGraph S f ∧
          pairedTraceLE S f w.1 w.2 at hw
        refine ⟨(.bottom, w.2), ?_, φ ∘ θ, hφ.comp hθ, ?_⟩
        · exact ⟨Or.inl rfl, hw.2.1, Or.inr (Or.inl rfl)⟩
        · simpa [Function.comp_def] using hbottomConv.prodMk_nhds hfiniteConv
    | eq =>
      have htopX (n : ℕ) : (z (φ n)).1 = .top :=
        state_eq_top_of_kind_eq_top ((hkindX n).trans hkindFirst)
      cases hkindSecond : k.2 with
      | lt =>
        -- The literal order excludes a top endpoint followed by bottom.
        have hbottomY (n : ℕ) : (z (φ n)).2 = .bottom :=
          state_eq_bottom_of_kind_eq_bottom ((hkindY n).trans hkindSecond)
        have himpossible : False := by
          simpa [pairedTraceLE, htopX 0, hbottomY 0] using horder 0
        exact himpossible.elim
      | eq =>
        have htopY (n : ℕ) : (z (φ n)).2 = .top :=
          state_eq_top_of_kind_eq_top ((hkindY n).trans hkindSecond)
        refine ⟨(.top, .top), ?_, φ, hφ, ?_⟩
        · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inl rfl),
            Or.inr (Or.inr (Or.inl rfl))⟩
        · apply Tendsto.congr' ?_ tendsto_const_nhds
          exact Filter.Eventually.of_forall
            (fun n => Prod.ext (htopX n).symm (htopY n).symm)
      | gt =>
        -- The literal order excludes a top endpoint followed by a finite endpoint.
        have hfiniteWitness :=
          finite_trace_witness_of_graph_kind (hmemY 0) ((hkindY 0).trans hkindSecond)
        have himpossible : False := by
          rcases hfiniteWitness with ⟨t, hminus | hplus⟩
          · simpa [pairedTraceLE, htopX 0, hminus] using horder 0
          · simpa [pairedTraceLE, htopX 0, hplus] using horder 0
        exact himpossible.elim
    | gt =>
      have hfiniteWitnessX (n : ℕ) :=
        finite_trace_witness_of_graph_kind (hmemX n) ((hkindX n).trans hkindFirst)
      let a : ℕ → {u : ℝ // u ∈ S} := fun n => Classical.choose (hfiniteWitnessX n)
      have ha (n : ℕ) :
          (z (φ n)).1 = .finite (f.1 (a n)) (a n).val ∨
            (z (φ n)).1 = .finite (f.2 (a n)) (a n).val :=
        Classical.choose_spec (hfiniteWitnessX n)
      cases hkindSecond : k.2 with
      | lt =>
        -- The literal order excludes a finite endpoint followed by bottom.
        have hbottomY (n : ℕ) : (z (φ n)).2 = .bottom :=
          state_eq_bottom_of_kind_eq_bottom ((hkindY n).trans hkindSecond)
        have himpossible : False := by
          rcases ha 0 with hminus | hplus
          · simpa [pairedTraceLE, hminus, hbottomY 0] using horder 0
          · simpa [pairedTraceLE, hplus, hbottomY 0] using horder 0
        exact himpossible.elim
      | eq =>
        -- A diagonal finite pair supplies a convergent subsequence for the first endpoint.
        have htopY (n : ℕ) : (z (φ n)).2 = .top :=
          state_eq_top_of_kind_eq_top ((hkindY n).trans hkindSecond)
        obtain ⟨w, hw, θ, hθ, hconv⟩ := finite_ordered_pair_subsequence
          hS f hleft hright a a (fun n => (z (φ n)).1) (fun n => (z (φ n)).1)
          ha ha (fun _ => Or.inl rfl)
        have hfiniteConv : Tendsto (fun n => (z (φ (θ n))).1) atTop (𝓝 w.1) := by
          simpa using hconv.fst_nhds
        have htopConv :
            Tendsto (fun n => (z (φ (θ n))).2) atTop
              (𝓝 (SqueezedState.top : SqueezedState J)) := by
          apply Tendsto.congr' ?_ tendsto_const_nhds
          exact Filter.Eventually.of_forall (fun n => (htopY (θ n)).symm)
        change w.1 ∈ pairedTraceGraph S f ∧ w.2 ∈ pairedTraceGraph S f ∧
          pairedTraceLE S f w.1 w.2 at hw
        refine ⟨(w.1, .top), ?_, φ ∘ θ, hφ.comp hθ, ?_⟩
        · exact ⟨hw.1, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl))⟩
        · simpa [Function.comp_def] using hfiniteConv.prodMk_nhds htopConv
      | gt =>
        -- One application preserves the common subsequence and the equal-time order case.
        have hfiniteWitnessY (n : ℕ) :=
          finite_trace_witness_of_graph_kind (hmemY n) ((hkindY n).trans hkindSecond)
        let b : ℕ → {u : ℝ // u ∈ S} := fun n => Classical.choose (hfiniteWitnessY n)
        have hb (n : ℕ) :
            (z (φ n)).2 = .finite (f.1 (b n)) (b n).val ∨
              (z (φ n)).2 = .finite (f.2 (b n)) (b n).val :=
          Classical.choose_spec (hfiniteWitnessY n)
        obtain ⟨w, hw, θ, hθ, hconv⟩ := finite_ordered_pair_subsequence
          hS f hleft hright a b (fun n => (z (φ n)).1) (fun n => (z (φ n)).2)
          ha hb horder
        refine ⟨w, hw, φ ∘ θ, hφ.comp hθ, ?_⟩
        simpa [Function.comp_def] using hconv
  -- Countability gives a compatible pseudometric on the state product and its induced carrier.
  have hPseudoJ : TopologicalSpace.PseudoMetrizableSpace (J → ℝ) := inferInstance
  have hPseudoReal : TopologicalSpace.PseudoMetrizableSpace ℝ := inferInstance
  have hPseudoAmbient : TopologicalSpace.PseudoMetrizableSpace (ℝ × (J → ℝ)) :=
    @TopologicalSpace.pseudoMetrizableSpace_prod ℝ (J → ℝ)
      inferInstance inferInstance hPseudoReal hPseudoJ
  have hInducing : Topology.IsInducing (squeezedStateEmbedding J) :=
    Topology.IsInducing.induced (squeezedStateEmbedding J)
  have hPseudoState : TopologicalSpace.PseudoMetrizableSpace (SqueezedState J) :=
    @Topology.IsInducing.pseudoMetrizableSpace
      (SqueezedState J) (ℝ × (J → ℝ)) inferInstance inferInstance hPseudoAmbient
      (squeezedStateEmbedding J) hInducing
  have hPseudoPair :
      TopologicalSpace.PseudoMetrizableSpace (SqueezedState J × SqueezedState J) :=
    @TopologicalSpace.pseudoMetrizableSpace_prod (SqueezedState J) (SqueezedState J)
      inferInstance inferInstance hPseudoState hPseudoState
  exact @IsSeqCompact.isCompact _ inferInstance hPseudoPair _ hseqcompact

end LPP.Busemann
