/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.CoordinatePathSum
public import Busemann.Frozen.Definitions.PastVariables
public import LPP_Foundations.Model.LatticeEdgeLocality
public import Mathlib.Probability.Independence.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory LPPDifferentiability
open scoped BigOperators

namespace LPP.Busemann

/-- A measurable process sample can be filled from the exact raw future
observation, using zero only at coordinates outside that observation. -/
theorem exists_measurable_raw_future_fill (I : Set Lattice) :
    let J : Set Lattice := {y | ∃ x ∈ I, x ≤ y}
    let RawIndex := Sum {x : Lattice // x ∈ I}
      (ℕ × {x : Lattice // x ∈ J} × Fin 2)
    let RawVector := RawIndex → ℝ
    ∃ fill : RawVector → ProcessSample,
      Measurable fill ∧
      (∀ u x (_hx : x ∈ I), (fill u).1 x = u (.inl ⟨x, _hx⟩)) ∧
      (∀ u x (_hx : x ∉ I), (fill u).1 x = 0) ∧
      (∀ u j x i (_hx : x ∈ J),
        (fill u).2 j x i = u (.inr (j, ⟨x, _hx⟩, i))) ∧
      (∀ u j x i (_hx : x ∉ J), (fill u).2 j x i = 0) := by
  classical
  let J : Set Lattice := {y | ∃ x ∈ I, x ≤ y}
  let RawIndex := Sum {x : Lattice // x ∈ I}
    (ℕ × {x : Lattice // x ∈ J} × Fin 2)
  let RawVector := RawIndex → ℝ
  change ∃ fill : RawVector → ProcessSample,
    Measurable fill ∧
    (∀ u x (_hx : x ∈ I), (fill u).1 x = u (.inl ⟨x, _hx⟩)) ∧
    (∀ u x (_hx : x ∉ I), (fill u).1 x = 0) ∧
    (∀ u j x i (_hx : x ∈ J),
      (fill u).2 j x i = u (.inr (j, ⟨x, _hx⟩, i))) ∧
    (∀ u j x i (_hx : x ∉ J), (fill u).2 j x i = 0)
  let fill : RawVector → ProcessSample := fun u =>
    (fun x => if hx : x ∈ I then u (.inl ⟨x, hx⟩) else 0,
      fun j x i => if hx : x ∈ J then u (.inr (j, ⟨x, hx⟩, i)) else 0)
  have hFillEnv : Measurable
      (fun u : RawVector => fun x : Lattice =>
        if hx : x ∈ I then u (.inl ⟨x, hx⟩) else 0) := by
    apply measurable_pi_iff.mpr
    intro x
    by_cases hx : x ∈ I
    · let a : RawIndex := Sum.inl ⟨x, hx⟩
      simpa only [dite_eq_left hx] using
        (measurable_pi_apply a : Measurable (fun u : RawVector => u a))
    · simpa only [dite_eq_right hx] using
        (measurable_const : Measurable (fun _ : RawVector => (0 : ℝ)))
  have hFillEdges : Measurable
      (fun u : RawVector => fun j x i =>
        if hx : x ∈ J then u (.inr (j, ⟨x, hx⟩, i)) else 0) := by
    apply measurable_pi_iff.mpr
    intro j
    apply measurable_pi_iff.mpr
    intro x
    apply measurable_pi_iff.mpr
    intro i
    by_cases hx : x ∈ J
    · let a : RawIndex := Sum.inr (j, ⟨x, hx⟩, i)
      simpa only [dite_eq_left hx] using
        (measurable_pi_apply a : Measurable (fun u : RawVector => u a))
    · simpa only [dite_eq_right hx] using
        (measurable_const : Measurable (fun _ : RawVector => (0 : ℝ)))
  have hFill : Measurable fill := hFillEnv.prodMk hFillEdges
  refine ⟨fill, hFill, ?_, ?_, ?_, ?_⟩
  · intro u x hx
    simp [fill, hx]
  · intro u x hx
    simp [fill, hx]
  · intro u j x i hx
    simp [fill, hx]
  · intro u j x i hx
    simp [fill, hx]

/-- Raw future independence passes to the literal signed coordinate path sums,
as in JR1810.03580v3, proof of Theorem 4.8(b) after (4.19). -/
theorem countable_coordinate_future_indep_past
    (P : Measure ProcessSample)
    (hInt : ∀ j x i, Integrable (fun s : ProcessSample => s.2 j x i) P)
    (hRaw : ∀ I : Set Lattice,
      let J : Set Lattice := {y | ∃ x ∈ I, x ≤ y}
      let U : ProcessSample →
          (Sum {x : Lattice // x ∈ I} (ℕ × {x : Lattice // x ∈ J} × Fin 2) → ℝ) :=
        fun s a => match a with
          | .inl x => s.1 x.1
          | .inr (j, x, i) => s.2 j x.1 i
      IndepFun U (pastVariables I) P) :
    ∀ I : Set Lattice,
      let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
        if a ≤ b then ∑ k ∈ Finset.Ico a b, f k else -(∑ k ∈ Finset.Ico b a, f k)
      let R : ℕ → Lattice → Lattice → ProcessSample → ℝ := fun j x y s =>
        S (fun k => s.2 j (k, x.2) 0) x.1 y.1 +
          S (fun k => s.2 j (y.1, k) 1) x.2 y.2
      let W : ProcessSample →
          (Sum {x : Lattice // x ∈ I}
            (ℕ × {p : Lattice × Lattice // p.1 ∈ I ∧ p.1 ≤ p.2}) → ℝ) :=
        fun s a => match a with
          | .inl x => s.1 x.1
          | .inr (j, p) => R j p.1.1 p.1.2 s
      IndepFun W (pastVariables I) P := by
  classical
  intro I
  let J : Set Lattice := {y | ∃ x ∈ I, x ≤ y}
  let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
    if a ≤ b then ∑ k ∈ Finset.Ico a b, f k else -(∑ k ∈ Finset.Ico b a, f k)
  let R : ℕ → Lattice → Lattice → ProcessSample → ℝ := fun j x y s =>
    S (fun k => s.2 j (k, x.2) 0) x.1 y.1 +
      S (fun k => s.2 j (y.1, k) 1) x.2 y.2
  let W : ProcessSample →
      (Sum {x : Lattice // x ∈ I}
        (ℕ × {p : Lattice × Lattice // p.1 ∈ I ∧ p.1 ≤ p.2}) → ℝ) :=
    fun s a => match a with
      | .inl x => s.1 x.1
      | .inr (j, p) => R j p.1.1 p.1.2 s
  let RawIndex := Sum {x : Lattice // x ∈ I}
    (ℕ × {x : Lattice // x ∈ J} × Fin 2)
  let RawVector := RawIndex → ℝ
  let CocycleIndex := Sum {x : Lattice // x ∈ I}
    (ℕ × {p : Lattice × Lattice // p.1 ∈ I ∧ p.1 ≤ p.2})
  let CocycleVector := CocycleIndex → ℝ
  let U : ProcessSample → RawVector := fun s a => match a with
    | .inl x => s.1 x.1
    | .inr (j, x, i) => s.2 j x.1 i

  -- The regularity result uses this same actual law and integrability input.
  have hRJoint : Measurable
      (fun q : ℕ × Lattice × Lattice × ProcessSample =>
        R q.1 q.2.1 q.2.2.1 q.2.2.2) := by
    exact (coordinate_path_sum_regularities P hInt).1

  -- Reuse the exact measurable completion of the same raw observation.
  obtain ⟨fill, hFill, _, _, hFillEdges, _⟩ :=
    exists_measurable_raw_future_fill I

  -- The measurable map reads the path-sum vector from a filled raw vector.
  let F : RawVector → CocycleVector := fun u a => match a with
    | .inl x => u (.inl x)
    | .inr (j, p) => R j p.1.1 p.1.2 (fill u)
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro a
    cases a with
    | inl x =>
      let rawIndex : RawIndex := Sum.inl x
      change Measurable (fun u : RawVector => u rawIndex)
      exact measurable_pi_apply rawIndex
    | inr q =>
      rcases q with ⟨j, p⟩
      change Measurable (fun u : RawVector => R j p.1.1 p.1.2 (fill u))
      have hTuple : Measurable
          (fun u : RawVector => (j, p.1.1, p.1.2, fill u)) :=
        measurable_const.prodMk
          (measurable_const.prodMk (measurable_const.prodMk hFill))
      change Measurable
        ((fun q : ℕ × Lattice × Lattice × ProcessSample =>
          R q.1 q.2.1 q.2.2.1 q.2.2.2) ∘
          fun u : RawVector => (j, p.1.1, p.1.2, fill u))
      exact hRJoint.comp hTuple

  -- Match the fill to the original sample on the entire cone used by each ordered path.
  have hFactor : W = F ∘ U := by
    funext s a
    cases a with
    | inl x => rfl
    | inr q =>
      rcases q with ⟨j, p⟩
      have hAgree : ∀ u ∈ Set.Ici p.1.1, ∀ i,
          (s.2 j u i) = (fill (U s)).2 j u i := by
        intro u hu i
        have huJ : u ∈ J := ⟨p.1.1, p.2.1, Set.mem_Ici.mp hu⟩
        simpa only [U] using (hFillEdges (U s) j u i huJ).symm
      have hLocal := lattice_edge_coordinate_path_sum_eq_of_agree_on_future_cone
        (fun u i => s.2 j u i) (fun u i => (fill (U s)).2 j u i)
        p.1.1 p.1.2 p.2.2 hAgree
      change R j p.1.1 p.1.2 s = R j p.1.1 p.1.2 (fill (U s))
      exact hLocal

  -- The raw independence premise is exactly the local observation U.
  have hRawI : IndepFun U (pastVariables I) P := by
    convert hRaw I using 1
    all_goals rfl
  have hComposed : IndepFun (F ∘ U) (pastVariables I) P := by
    convert hRawI.comp hF measurable_id using 1
    all_goals rfl
  change IndepFun W (pastVariables I) P
  rw [hFactor]
  exact hComposed

end LPP.Busemann
