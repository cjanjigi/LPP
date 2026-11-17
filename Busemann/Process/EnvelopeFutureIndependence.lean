/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.FutureVariables
public import Busemann.Process.CountableFutureIndependence
public import Busemann.Process.UnitEnvelopes
import Mathlib.Tactic

@[expose] public section

open MeasureTheory ProbabilityTheory Filter LPPDifferentiability
open scoped BigOperators Topology

namespace LPP.Busemann

-- Retain the original bound abbreviation in the statement.
set_option linter.unusedVariables false in
/-- The full future vector of envelope cocycles is independent of the same raw past,
as in JR1810.03580v3, proof of Theorem 4.8 after (4.19). -/
theorem envelope_cocycles_future_indep_past
    (g : Quadrant → ℝ) (D : ℕ → SupportTilt g)
    (happrox : ∀ h : SupportTilt g, ∃ a b : ℕ → ℕ,
      StrictMono (fun n => (D (a n)).1.1) ∧
      StrictAnti (fun n => (D (b n)).1.1) ∧
      (∀ n, (D (a n)).1.1 < h.1.1 ∧ h.1.1 < (D (b n)).1.1) ∧
      Tendsto (fun n => (D (a n)).1) atTop (𝓝 h.1) ∧
      Tendsto (fun n => (D (b n)).1) atTop (𝓝 h.1))
    (P : Measure ProcessSample)
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
        if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
        else -(∑ k ∈ Finset.Ico b a, f k)
      let X : ℕ → Lattice → Fin 2 → ProcessSample → ℝ :=
        fun j x i s => s.2 j x i
      let Q : Set ProcessSample := {s | ∀ j k x,
        (D j).1.1 ≤ (D k).1.1 →
          X k x 0 s ≤ X j x 0 s ∧ X j x 1 s ≤ X k x 1 s}
      let Eminus : SupportTilt g → Lattice → Fin 2 → ProcessSample → EReal :=
        fun h x i s => if i = 0 then
          ⨅ j, if (D j).1.1 < h.1.1 then (X j x i s : EReal) else ⊤
        else
          ⨆ j, if (D j).1.1 < h.1.1 then (X j x i s : EReal) else ⊥
      let Eplus : SupportTilt g → Lattice → Fin 2 → ProcessSample → EReal :=
        fun h x i s => if i = 0 then
          ⨆ j, if h.1.1 < (D j).1.1 then (X j x i s : EReal) else ⊥
        else
          ⨅ j, if h.1.1 < (D j).1.1 then (X j x i s : EReal) else ⊤
      let eMinus := fun h x i s => (Eminus h x i s).toReal
      let ePlus := fun h x i s => (Eplus h x i s).toReal
      let Rminus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ :=
        fun h x y s =>
          S (fun k => eMinus h (k, x.2) 0 s) x.1 y.1 +
            S (fun k => eMinus h (y.1, k) 1 s) x.2 y.2
      let Rplus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ :=
        fun h x y s =>
          S (fun k => ePlus h (k, x.2) 0 s) x.1 y.1 +
            S (fun k => ePlus h (y.1, k) 1 s) x.2 y.2
      IndepFun (futureVariables g I Rminus Rplus) (pastVariables I) P := by
  classical
  intro I
  let J : Set Lattice := {y | ∃ x ∈ I, x ≤ y}
  let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
    if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
    else -(∑ k ∈ Finset.Ico b a, f k)
  let X : ℕ → Lattice → Fin 2 → ProcessSample → ℝ :=
    fun j x i s => s.2 j x i
  let Q : Set ProcessSample := {s | ∀ j k x,
      (D j).1.1 ≤ (D k).1.1 →
        X k x 0 s ≤ X j x 0 s ∧ X j x 1 s ≤ X k x 1 s}
  let Eminus : SupportTilt g → Lattice → Fin 2 → ProcessSample → EReal :=
    fun h x i s => if i = 0 then
      ⨅ j, if (D j).1.1 < h.1.1 then (X j x i s : EReal) else ⊤
    else
      ⨆ j, if (D j).1.1 < h.1.1 then (X j x i s : EReal) else ⊥
  let Eplus : SupportTilt g → Lattice → Fin 2 → ProcessSample → EReal :=
    fun h x i s => if i = 0 then
      ⨆ j, if h.1.1 < (D j).1.1 then (X j x i s : EReal) else ⊥
    else
      ⨅ j, if h.1.1 < (D j).1.1 then (X j x i s : EReal) else ⊤
  let eMinus := fun h x i s => (Eminus h x i s).toReal
  let ePlus := fun h x i s => (Eplus h x i s).toReal
  let Rminus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ :=
    fun h x y s =>
      S (fun k => eMinus h (k, x.2) 0 s) x.1 y.1 +
        S (fun k => eMinus h (y.1, k) 1 s) x.2 y.2
  let Rplus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ :=
    fun h x y s =>
      S (fun k => ePlus h (k, x.2) 0 s) x.1 y.1 +
        S (fun k => ePlus h (y.1, k) 1 s) x.2 y.2
  let RawIndex := Sum {x : Lattice // x ∈ I}
    (ℕ × {x : Lattice // x ∈ J} × Fin 2)
  let RawVector := RawIndex → ℝ
  let U : ProcessSample → RawVector := fun s a => match a with
    | .inl x => s.1 x.1
    | .inr (j, x, i) => s.2 j x.1 i
  let FutureIndex := Sum {x : Lattice // x ∈ I} (FutureCocycleIndex g I)
  let FutureVector := FutureIndex → ℝ

  obtain ⟨_, _, _, _, hMeasMinus, hMeasPlus, _, _, _, _, _⟩ :=
    countable_unit_envelopes_measurable_finite_and_cofinal g D happrox
  obtain ⟨fill, hFill, _, _, hFillEdges, _⟩ :=
    exists_measurable_raw_future_fill I

  have hFillEdgeEq (s : ProcessSample) (j : ℕ) (x : Lattice) (i : Fin 2)
      (hx : x ∈ J) : (fill (U s)).2 j x i = s.2 j x i := by
    simpa only [U] using hFillEdges (U s) j x i hx

  have hRawAt (s : ProcessSample) (x : Lattice) (hx : x ∈ J)
      (i : Fin 2) :
      ∀ j, X j x i s = X j x i (fill (U s)) := by
    intro j
    exact (hFillEdgeEq s j x i hx).symm
  have hEminusEq (s : ProcessSample) (x : Lattice) (hx : x ∈ J)
      (h : SupportTilt g) (i : Fin 2) :
      Eminus h x i s = Eminus h x i (fill (U s)) := by
    fin_cases i
    · simp [Eminus, hRawAt s x hx (0 : Fin 2)]
    · simp [Eminus, hRawAt s x hx (1 : Fin 2)]
  have hEplusEq (s : ProcessSample) (x : Lattice) (hx : x ∈ J)
      (h : SupportTilt g) (i : Fin 2) :
      Eplus h x i s = Eplus h x i (fill (U s)) := by
    fin_cases i
    · simp [Eplus, hRawAt s x hx (0 : Fin 2)]
    · simp [Eplus, hRawAt s x hx (1 : Fin 2)]
  have heMinusEq (s : ProcessSample) (x : Lattice) (hx : x ∈ J)
      (h : SupportTilt g) (i : Fin 2) :
      eMinus h x i s = eMinus h x i (fill (U s)) := by
    exact congrArg EReal.toReal (hEminusEq s x hx h i)
  have hePlusEq (s : ProcessSample) (x : Lattice) (hx : x ∈ J)
      (h : SupportTilt g) (i : Fin 2) :
      ePlus h x i s = ePlus h x i (fill (U s)) := by
    exact congrArg EReal.toReal (hEplusEq s x hx h i)

  have hMeasRminus : Measurable
      (fun q : SupportTilt g × Lattice × Lattice × ProcessSample =>
        Rminus q.1 q.2.1 q.2.2.1 q.2.2.2) :=
    measurable_lattice_coordinate_path_sum eMinus hMeasMinus
  have hMeasRplus : Measurable
      (fun q : SupportTilt g × Lattice × Lattice × ProcessSample =>
        Rplus q.1 q.2.1 q.2.2.1 q.2.2.2) :=
    measurable_lattice_coordinate_path_sum ePlus hMeasPlus

  let F : RawVector → FutureVector := fun u a => match a with
    | .inl x => u (.inl x)
    | .inr q =>
        if q.right then Rplus q.tilt q.root q.target (fill u)
        else Rminus q.tilt q.root q.target (fill u)
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro a
    cases a with
    | inl x =>
      let rawIndex : RawIndex := Sum.inl x
      change Measurable (fun u : RawVector => u rawIndex)
      exact measurable_pi_apply rawIndex
    | inr q =>
      by_cases hright : q.right
      · simp only [F, ite_eq_left hright]
        have hTuple : Measurable
            (fun u : RawVector => (q.tilt, q.root, q.target, fill u)) :=
          measurable_const.prodMk
            (measurable_const.prodMk (measurable_const.prodMk hFill))
        exact hMeasRplus.comp hTuple
      · simp only [F, ite_eq_right hright]
        have hTuple : Measurable
            (fun u : RawVector => (q.tilt, q.root, q.target, fill u)) :=
          measurable_const.prodMk
            (measurable_const.prodMk (measurable_const.prodMk hFill))
        exact hMeasRminus.comp hTuple

  have hAgreeMinus (q : FutureCocycleIndex g I) (s : ProcessSample) :
      ∀ x ∈ Set.Ici q.root, ∀ i,
        eMinus q.tilt x i s = eMinus q.tilt x i (fill (U s)) := by
    intro x hx i
    have hxJ : x ∈ J := ⟨q.root, q.root_mem, Set.mem_Ici.mp hx⟩
    exact heMinusEq s x hxJ q.tilt i
  have hAgreePlus (q : FutureCocycleIndex g I) (s : ProcessSample) :
      ∀ x ∈ Set.Ici q.root, ∀ i,
        ePlus q.tilt x i s = ePlus q.tilt x i (fill (U s)) := by
    intro x hx i
    have hxJ : x ∈ J := ⟨q.root, q.root_mem, Set.mem_Ici.mp hx⟩
    exact hePlusEq s x hxJ q.tilt i
  have hLocalMinus (q : FutureCocycleIndex g I) (s : ProcessSample) :
      Rminus q.tilt q.root q.target s =
        Rminus q.tilt q.root q.target (fill (U s)) := by
    simpa only [Rminus, S] using
      lattice_edge_coordinate_path_sum_eq_of_agree_on_future_cone
      (fun x i => eMinus q.tilt x i s)
      (fun x i => eMinus q.tilt x i (fill (U s)))
      q.root q.target q.target_ge (hAgreeMinus q s)
  have hLocalPlus (q : FutureCocycleIndex g I) (s : ProcessSample) :
      Rplus q.tilt q.root q.target s =
        Rplus q.tilt q.root q.target (fill (U s)) := by
    simpa only [Rplus, S] using
      lattice_edge_coordinate_path_sum_eq_of_agree_on_future_cone
      (fun x i => ePlus q.tilt x i s)
      (fun x i => ePlus q.tilt x i (fill (U s)))
      q.root q.target q.target_ge (hAgreePlus q s)

  have hFactor : futureVariables g I Rminus Rplus = F ∘ U := by
    funext s a
    cases a with
    | inl x => rfl
    | inr q =>
      by_cases hright : q.right
      · simpa only [futureVariables, F, Function.comp_apply, ite_eq_left hright] using
          hLocalPlus q s
      · simpa only [futureVariables, F, Function.comp_apply, ite_eq_right hright] using
          hLocalMinus q s

  have hRawI : IndepFun U (pastVariables I) P := by
    convert hRaw I using 1
    all_goals rfl
  have hComposed : IndepFun (F ∘ U) (pastVariables I) P := by
    convert hRawI.comp hF measurable_id using 1
    all_goals rfl
  change IndepFun (futureVariables g I Rminus Rplus) (pastVariables I) P
  rw [hFactor]
  exact hComposed

end LPP.Busemann
