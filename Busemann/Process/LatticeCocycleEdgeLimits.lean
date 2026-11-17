/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.Additive
public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import LPP_Foundations.Model.LatticeEdgeIntegration
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped Topology BigOperators

namespace LPP.Busemann

-- The edge extension identifies an additive field with its finite
-- horizontal-then-vertical signed path sum.
private theorem additive_eq_signed_edge_sums
    (D : Lattice → Lattice → ℝ) (hD : is_additive D) (x y : Lattice) :
    D x y =
      (if x.1 ≤ y.1 then
        ∑ k ∈ Finset.Ico x.1 y.1, D (k, x.2) ((k, x.2) + finiteEdgeStep 0)
       else
        -(∑ k ∈ Finset.Ico y.1 x.1,
          D (k, x.2) ((k, x.2) + finiteEdgeStep 0))) +
      (if x.2 ≤ y.2 then
        ∑ k ∈ Finset.Ico x.2 y.2, D (y.1, k) ((y.1, k) + finiteEdgeStep 1)
       else
        -(∑ k ∈ Finset.Ico y.2 x.2,
          D (y.1, k) ((y.1, k) + finiteEdgeStep 1))) := by
  classical
  let E : Lattice → Fin 2 → ℝ := fun z i => D z (z + finiteEdgeStep i)
  have hcurl (z : Lattice) :
      E z 0 + E (z + (1, 0)) 1 = E z 1 + E (z + (0, 1)) 0 := by
    dsimp [E, finiteEdgeStep]
    have hz₀ : z + (1, 0) + (0, 1) = z + (1, 1) := by
      ext <;> simp [Prod.mk_add_mk, add_assoc]
    have hz₁ : z + (0, 1) + (1, 0) = z + (1, 1) := by
      ext <;> simp [Prod.mk_add_mk, add_assoc]
    rw [hz₀, hz₁]
    have h₁ := hD z (z + (1, 0)) (z + (1, 1))
    have h₂ := hD z (z + (0, 1)) (z + (1, 1))
    exact h₁.trans h₂.symm
  obtain ⟨F, hFadd, hFedge, hFformula, hUnique⟩ :=
    exists_unique_lattice_edge_extension E hcurl
  have hEdgeD (z : Lattice) :
      D z (z + (1, 0)) = E z 0 ∧ D z (z + (0, 1)) = E z 1 := by
    dsimp [E, finiteEdgeStep]
    exact ⟨rfl, rfl⟩
  have hDF : D = F := hUnique D hD hEdgeD
  have hformula := hFformula x y
  rw [← hDF] at hformula
  simpa [E, finiteEdgeStep] using hformula

/-- Almost-sure limits on every signed unit edge of additive real lattice
fields give one almost-sure event with limits on every lattice pair. This is
the finite-path step in the unpublished H closedness argument. -/
theorem ae_all_pair_limits_of_unit_edge_limits
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℕ → Lattice → Lattice → Ω → ℝ)
    (hAdd : ∀ n : ℕ, ∀ᵐ ω ∂P, is_additive (fun x y => B n x y ω))
    (hEdge : ∀ x : Lattice, ∀ i : Fin 2, ∀ᵐ ω ∂P,
      ∃ l : ℝ, Tendsto
        (fun n => B n x (x + finiteEdgeStep i) ω) atTop (𝓝 l)) :
    ∀ᵐ ω ∂P, ∀ x y : Lattice,
      ∃ l : ℝ, Tendsto (fun n => B n x y ω) atTop (𝓝 l) := by
  classical
  have hEvent : ∀ᵐ ω ∂P,
      (∀ n, is_additive (fun x y => B n x y ω)) ∧
      (∀ x i, ∃ l : ℝ,
        Tendsto (fun n => B n x (x + finiteEdgeStep i) ω) atTop (𝓝 l)) := by
    filter_upwards [ae_all_iff.mpr hAdd,
      ae_all_iff.mpr (fun x => ae_all_iff.mpr (hEdge x))] with ω ha he
    exact ⟨ha, he⟩
  filter_upwards [hEvent] with ω hω
  intro x y
  have hHorizontal (k : ℤ) :
      ∃ l : ℝ, Tendsto
        (fun n => B n (k, x.2) ((k, x.2) + finiteEdgeStep 0) ω)
        atTop (𝓝 l) := hω.2 (k, x.2) 0
  have hVertical (k : ℤ) :
      ∃ l : ℝ, Tendsto
        (fun n => B n (y.1, k) ((y.1, k) + finiteEdgeStep 1) ω)
        atTop (𝓝 l) := hω.2 (y.1, k) 1
  choose lh htlh using hHorizontal
  choose lv htlv using hVertical
  have hhor (a b : ℤ) : ∃ l : ℝ,
      Tendsto (fun n => if a ≤ b then
        ∑ k ∈ Finset.Ico a b, B n (k, x.2) ((k, x.2) + finiteEdgeStep 0) ω
        else -(∑ k ∈ Finset.Ico b a,
          B n (k, x.2) ((k, x.2) + finiteEdgeStep 0) ω)) atTop (𝓝 l) := by
    by_cases hab : a ≤ b
    · refine ⟨∑ k ∈ Finset.Ico a b, lh k, ?_⟩
      simpa [hab] using
        tendsto_finsetSum _ (fun k _ => htlh k)
    · refine ⟨-(∑ k ∈ Finset.Ico b a, lh k), ?_⟩
      simpa [hab] using
        (tendsto_finsetSum _ (fun k _ => htlh k)).neg
  have hver (a b : ℤ) : ∃ l : ℝ,
      Tendsto (fun n => if a ≤ b then
        ∑ k ∈ Finset.Ico a b, B n (y.1, k) ((y.1, k) + finiteEdgeStep 1) ω
        else -(∑ k ∈ Finset.Ico b a,
          B n (y.1, k) ((y.1, k) + finiteEdgeStep 1) ω)) atTop (𝓝 l) := by
    by_cases hab : a ≤ b
    · refine ⟨∑ k ∈ Finset.Ico a b, lv k, ?_⟩
      simpa [hab] using
        tendsto_finsetSum _ (fun k _ => htlv k)
    · refine ⟨-(∑ k ∈ Finset.Ico b a, lv k), ?_⟩
      simpa [hab] using
        (tendsto_finsetSum _ (fun k _ => htlv k)).neg
  obtain ⟨lh', hth⟩ := hhor x.1 y.1
  obtain ⟨lv', htv⟩ := hver x.2 y.2
  refine ⟨lh' + lv', ?_⟩
  have hsum := hth.add htv
  convert hsum using 1
  ext n
  exact additive_eq_signed_edge_sums (fun a b => B n a b ω) (hω.1 n) x y

-- For an additive field, first obtain pair integrability from the finite path.
-- Then integrate the pointwise triangle inequality along that path.
private theorem integral_abs_pair_le_edge_integrals
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Lattice → Lattice → Ω → ℝ)
    (hAdd : ∀ᵐ ω ∂P, is_additive (fun a b => D a b ω))
    (hInt : ∀ z : Lattice, ∀ i : Fin 2,
      Integrable (D z (z + finiteEdgeStep i)) P)
    (x y : Lattice) :
    ∫ ω, |D x y ω| ∂P ≤
      (if x.1 ≤ y.1 then
        ∑ k ∈ Finset.Ico x.1 y.1,
          ∫ ω, |D (k, x.2) ((k, x.2) + finiteEdgeStep 0) ω| ∂P
       else
        ∑ k ∈ Finset.Ico y.1 x.1,
          ∫ ω, |D (k, x.2) ((k, x.2) + finiteEdgeStep 0) ω| ∂P) +
      (if x.2 ≤ y.2 then
        ∑ k ∈ Finset.Ico x.2 y.2,
          ∫ ω, |D (y.1, k) ((y.1, k) + finiteEdgeStep 1) ω| ∂P
       else
        ∑ k ∈ Finset.Ico y.2 x.2,
          ∫ ω, |D (y.1, k) ((y.1, k) + finiteEdgeStep 1) ω| ∂P) := by
  classical
  let H : ℤ → Ω → ℝ := fun k ω => D (k, x.2) ((k, x.2) + finiteEdgeStep 0) ω
  let V : ℤ → Ω → ℝ := fun k ω => D (y.1, k) ((y.1, k) + finiteEdgeStep 1) ω
  let SH : Ω → ℝ := fun ω =>
    if x.1 ≤ y.1 then ∑ k ∈ Finset.Ico x.1 y.1, H k ω
    else -(∑ k ∈ Finset.Ico y.1 x.1, H k ω)
  let SV : Ω → ℝ := fun ω =>
    if x.2 ≤ y.2 then ∑ k ∈ Finset.Ico x.2 y.2, V k ω
    else -(∑ k ∈ Finset.Ico y.2 x.2, V k ω)
  let RH : Ω → ℝ := fun ω =>
    if x.1 ≤ y.1 then ∑ k ∈ Finset.Ico x.1 y.1, |H k ω|
    else ∑ k ∈ Finset.Ico y.1 x.1, |H k ω|
  let RV : Ω → ℝ := fun ω =>
    if x.2 ≤ y.2 then ∑ k ∈ Finset.Ico x.2 y.2, |V k ω|
    else ∑ k ∈ Finset.Ico y.2 x.2, |V k ω|
  have hIntH (k : ℤ) : Integrable (H k) P := hInt (k, x.2) 0
  have hIntV (k : ℤ) : Integrable (V k) P := hInt (y.1, k) 1
  have hIntSH : Integrable SH P := by
    by_cases h : x.1 ≤ y.1
    · simpa [SH, h] using
        integrable_finsetSum (Finset.Ico x.1 y.1) (fun k _ => hIntH k)
    · simpa [SH, h] using
        (integrable_finsetSum (Finset.Ico y.1 x.1) (fun k _ => hIntH k)).neg
  have hIntSV : Integrable SV P := by
    by_cases h : x.2 ≤ y.2
    · simpa [SV, h] using
        integrable_finsetSum (Finset.Ico x.2 y.2) (fun k _ => hIntV k)
    · simpa [SV, h] using
        (integrable_finsetSum (Finset.Ico y.2 x.2) (fun k _ => hIntV k)).neg
  have hIntRH : Integrable RH P := by
    by_cases h : x.1 ≤ y.1
    · simpa [RH, h] using
        integrable_finsetSum (Finset.Ico x.1 y.1) (fun k _ => (hIntH k).abs)
    · simpa [RH, h] using
        integrable_finsetSum (Finset.Ico y.1 x.1) (fun k _ => (hIntH k).abs)
  have hIntRV : Integrable RV P := by
    by_cases h : x.2 ≤ y.2
    · simpa [RV, h] using
        integrable_finsetSum (Finset.Ico x.2 y.2) (fun k _ => (hIntV k).abs)
    · simpa [RV, h] using
        integrable_finsetSum (Finset.Ico y.2 x.2) (fun k _ => (hIntV k).abs)
  have hFormula : D x y =ᵐ[P] (fun ω => SH ω + SV ω) := by
    filter_upwards [hAdd] with ω ha
    exact additive_eq_signed_edge_sums (fun a b => D a b ω) ha x y
  have hIntPair : Integrable (D x y) P :=
    (integrable_congr hFormula).2 (hIntSH.add hIntSV)
  have hBound : ∀ᵐ ω ∂P, |D x y ω| ≤ RH ω + RV ω := by
    filter_upwards [hFormula] with ω heq
    have hH : |SH ω| ≤ RH ω := by
      by_cases h : x.1 ≤ y.1
      · simpa [SH, RH, h] using
          (Finset.abs_sum_le_sum_abs (fun k => H k ω) (Finset.Ico x.1 y.1))
      · simpa [SH, RH, h] using
          (Finset.abs_sum_le_sum_abs (fun k => H k ω) (Finset.Ico y.1 x.1))
    have hV : |SV ω| ≤ RV ω := by
      by_cases h : x.2 ≤ y.2
      · simpa [SV, RV, h] using
          (Finset.abs_sum_le_sum_abs (fun k => V k ω) (Finset.Ico x.2 y.2))
      · simpa [SV, RV, h] using
          (Finset.abs_sum_le_sum_abs (fun k => V k ω) (Finset.Ico y.2 x.2))
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add hH hV)
  have hIntegralBound := integral_mono_ae hIntPair.abs (hIntRH.add hIntRV) hBound
  calc
    ∫ ω, |D x y ω| ∂P ≤ ∫ ω, RH ω + RV ω ∂P := hIntegralBound
    _ = (∫ ω, RH ω ∂P) + (∫ ω, RV ω ∂P) := integral_add hIntRH hIntRV
    _ = _ := by
      congr 1
      · by_cases h : x.1 ≤ y.1
        · simpa [RH, H, h] using
            (integral_finsetSum (Finset.Ico x.1 y.1) (fun k _ => (hIntH k).abs))
        · simpa [RH, H, h] using
            (integral_finsetSum (Finset.Ico y.1 x.1) (fun k _ => (hIntH k).abs))
      · by_cases h : x.2 ≤ y.2
        · simpa [RV, V, h] using
            (integral_finsetSum (Finset.Ico x.2 y.2) (fun k _ => (hIntV k).abs))
        · simpa [RV, V, h] using
            (integral_finsetSum (Finset.Ico y.2 x.2) (fun k _ => (hIntV k).abs))

/-- Convergence in integral absolute difference on all signed unit edges
extends to every lattice pair when both fields are additive. This is the
finite-path L1 step in the unpublished H closedness argument. -/
theorem all_pair_integral_abs_sub_tendsto_of_unit_edges
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℕ → Lattice → Lattice → Ω → ℝ)
    (C : Lattice → Lattice → Ω → ℝ)
    (hAddB : ∀ n : ℕ, ∀ᵐ ω ∂P, is_additive (fun x y => B n x y ω))
    (hAddC : ∀ᵐ ω ∂P, is_additive (fun x y => C x y ω))
    (hIntB : ∀ n : ℕ, ∀ x : Lattice, ∀ i : Fin 2,
      Integrable (B n x (x + finiteEdgeStep i)) P)
    (hIntC : ∀ x : Lattice, ∀ i : Fin 2,
      Integrable (C x (x + finiteEdgeStep i)) P)
    (hEdge : ∀ x : Lattice, ∀ i : Fin 2,
      Tendsto (fun n => ∫ ω,
        |B n x (x + finiteEdgeStep i) ω -
          C x (x + finiteEdgeStep i) ω| ∂P) atTop (𝓝 0)) :
    ∀ x y : Lattice,
      Tendsto (fun n => ∫ ω, |B n x y ω - C x y ω| ∂P)
        atTop (𝓝 0) := by
  classical
  intro x y
  let D : ℕ → Lattice → Lattice → Ω → ℝ := fun n a b ω => B n a b ω - C a b ω
  have hAddD (n : ℕ) : ∀ᵐ ω ∂P, is_additive (fun a b => D n a b ω) := by
    filter_upwards [hAddB n, hAddC] with ω hb hc
    intro a b c
    change (B n a b ω - C a b ω) + (B n b c ω - C b c ω) =
      B n a c ω - C a c ω
    have hb' := hb a b c
    have hc' := hc a b c
    linarith
  have hIntD (n : ℕ) (z : Lattice) (i : Fin 2) :
      Integrable (D n z (z + finiteEdgeStep i)) P :=
    (hIntB n z i).sub (hIntC z i)
  have hPairBound (n : ℕ) :=
    integral_abs_pair_le_edge_integrals P (D n) (hAddD n) (hIntD n) x y
  have hHorizontal : Tendsto (fun n =>
      if x.1 ≤ y.1 then
        ∑ k ∈ Finset.Ico x.1 y.1, ∫ ω, |D n (k, x.2) ((k, x.2) + finiteEdgeStep 0) ω| ∂P
      else
        ∑ k ∈ Finset.Ico y.1 x.1, ∫ ω, |D n (k, x.2) ((k, x.2) + finiteEdgeStep 0) ω| ∂P)
      atTop (𝓝 0) := by
    by_cases h : x.1 ≤ y.1
    · simpa [h, D] using
        (tendsto_finsetSum (Finset.Ico x.1 y.1)
          (fun k _ => hEdge (k, x.2) 0))
    · simpa [h, D] using
        (tendsto_finsetSum (Finset.Ico y.1 x.1)
          (fun k _ => hEdge (k, x.2) 0))
  have hVertical : Tendsto (fun n =>
      if x.2 ≤ y.2 then
        ∑ k ∈ Finset.Ico x.2 y.2, ∫ ω, |D n (y.1, k) ((y.1, k) + finiteEdgeStep 1) ω| ∂P
      else
        ∑ k ∈ Finset.Ico y.2 x.2, ∫ ω, |D n (y.1, k) ((y.1, k) + finiteEdgeStep 1) ω| ∂P)
      atTop (𝓝 0) := by
    by_cases h : x.2 ≤ y.2
    · simpa [h, D] using
        (tendsto_finsetSum (Finset.Ico x.2 y.2)
          (fun k _ => hEdge (y.1, k) 1))
    · simpa [h, D] using
        (tendsto_finsetSum (Finset.Ico y.2 x.2)
          (fun k _ => hEdge (y.1, k) 1))
  have hUpper := hHorizontal.add hVertical
  exact squeeze_zero
    (fun n => integral_nonneg (fun ω => abs_nonneg (D n x y ω)))
    hPairBound (by simpa only [zero_add] using hUpper)

end LPP.Busemann
