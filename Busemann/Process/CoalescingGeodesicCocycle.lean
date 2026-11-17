/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.RealGeodesicCocycles
public import Busemann.Geometry.LocallyRightmostGeodesic
public import LPP_Foundations.Statements.ShapeDefinitions
public import LPP_Foundations.Model.LastPassage.PassageDifferenceLimits
public import LPP_Foundations.Model.LastPassage.GeodesicSegments
public import LPP_Foundations.Model.Paths.Coalescence
import Busemann.Geometry.GeodesicCocycleOrder
import Busemann.Geometry.GeodesicSegments
import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology
namespace LPP.Busemann

/-- A coalescing family of locally rightmost geodesics determines one real
cocycle on all signed sites. The same field is recovered from every ray in
the family and calibrates every step of every ray.
Strong Existence, (B-gen4), lines 304–307; (B-def)/(B_u), lines 1007–1028;
Theorem g400, lines 1596–1693. -/
theorem exists_full_event_unique_real_cocycle_of_coalescing_geodesic_family
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) :
    ∃ A : Set Environment,
      MeasurableSet A ∧ environmentLaw μ A = 1 ∧
      ∀ ω ∈ A, ∀ π : Lattice → ℕ → Lattice,
        (∀ u : Lattice, IsLocallyRightmostGeodesic ω u (π u)) →
        (∀ u v : Lattice, paths_coalesce u v (π u) (π v)) →
        ∃! C : Lattice → Lattice → ℝ,
          (∀ u : Lattice, has_passage_difference_limits ω (π u) C) ∧
          is_additive C ∧ recovers_environment ω C ∧
          ∀ u : Lattice, ∀ n : ℕ,
            C (π u n) (π u (n + 1)) = ω (π u n) := by
  classical
  obtain ⟨A, hAmeasurable, hAfull, hGood⟩ :=
    exists_full_event_unique_real_geodesic_cocycle μ hμ hmoment
  refine ⟨A, hAmeasurable, hAfull, ?_⟩
  intro ω hω π hRays hCoalesce
  have hStart (u : Lattice) : π u 0 = u := (hRays u).1
  have hSteps (u : Lattice) : ∀ n : ℕ,
      π u (n + 1) = π u n + ((1 : ℤ), (0 : ℤ)) ∨
        π u (n + 1) = π u n + ((0 : ℤ), (1 : ℤ)) :=
    (hRays u).2.1
  have hSegments (u : Lattice) : has_maximizing_segments ω (π u) :=
    (hRays u).has_maximizing_segments
  have hMono (u : Lattice) : Monotone (π u) := by
    apply monotone_nat_of_le_succ
    intro n
    rcases hSteps u n with he | hn
    · rw [he]
      constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
    · rw [hn]
      constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
  have hEscape₁ (u : Lattice) :
      Tendsto (fun n : ℕ => (π u n).1) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro M
    obtain ⟨m, n, _hlevel, hTail⟩ := hCoalesce u (M, M)
    refine Filter.eventually_atTop.2 ⟨m, ?_⟩
    intro t ht
    let k := t - m
    have hIndex : m + k = t := by
      dsimp only [k]
      omega
    have hDiagonalBound : M ≤ (π (M, M) (n + k)).1 := by
      have hMonoBound := hMono (M, M) (Nat.zero_le (n + k))
      rw [hStart (M, M)] at hMonoBound
      exact hMonoBound.1
    calc
      M ≤ (π (M, M) (n + k)).1 := hDiagonalBound
      _ = (π u (m + k)).1 := by rw [hTail k]
      _ = (π u t).1 := by rw [hIndex]
  have hEscape₂ (u : Lattice) :
      Tendsto (fun n : ℕ => (π u n).2) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro M
    obtain ⟨m, n, _hlevel, hTail⟩ := hCoalesce u (M, M)
    refine Filter.eventually_atTop.2 ⟨m, ?_⟩
    intro t ht
    let k := t - m
    have hIndex : m + k = t := by
      dsimp only [k]
      omega
    have hDiagonalBound : M ≤ (π (M, M) (n + k)).2 := by
      have hMonoBound := hMono (M, M) (Nat.zero_le (n + k))
      rw [hStart (M, M)] at hMonoBound
      exact hMonoBound.2
    calc
      M ≤ (π (M, M) (n + k)).2 := hDiagonalBound
      _ = (π u (m + k)).2 := by rw [hTail k]
      _ = (π u t).2 := by rw [hIndex]
  have hRoot (u : Lattice) :
      ∃! C : Lattice → Lattice → ℝ,
        has_passage_difference_limits ω (π u) C ∧
        is_additive C ∧ recovers_environment ω C ∧
        ∀ n : ℕ, C (π u n) (π u (n + 1)) = ω (π u n) := by
    exact hGood ω hω u (π u) (hStart u) (hSteps u) (hSegments u)
      (hEscape₁ u) (hEscape₂ u)
  let Cfamily : Lattice → (Lattice → Lattice → ℝ) :=
    fun u => Classical.choose (hRoot u)
  have hFamilyProp (u : Lattice) :
      has_passage_difference_limits ω (π u) (Cfamily u) ∧
      is_additive (Cfamily u) ∧ recovers_environment ω (Cfamily u) ∧
      ∀ n : ℕ, Cfamily u (π u n) (π u (n + 1)) = ω (π u n) :=
    (Classical.choose_spec (hRoot u)).1
  have hFamilyUnique (u : Lattice) :
      ∀ D : Lattice → Lattice → ℝ,
        (has_passage_difference_limits ω (π u) D ∧
          is_additive D ∧ recovers_environment ω D ∧
          ∀ n : ℕ, D (π u n) (π u (n + 1)) = ω (π u n)) →
        D = Cfamily u :=
    (Classical.choose_spec (hRoot u)).2
  let rootZero : Lattice := (0, 0)
  have hFieldEq (u : Lattice) : Cfamily u = Cfamily rootZero := by
    apply (geodesic_limit_fields_order_and_eq_of_coalescing
      ω u rootZero (π u) (π rootZero) (Cfamily u) (Cfamily rootZero)
      (hStart u) (hStart rootZero) (hSteps u) (hSteps rootZero)
      (hSegments u) (hSegments rootZero)
      (hEscape₁ u) (hEscape₂ u) (hEscape₁ rootZero) (hEscape₂ rootZero)
      (hFamilyProp u).1 (hFamilyProp rootZero).1).2
    exact hCoalesce u rootZero
  refine ⟨Cfamily rootZero, ?_, ?_⟩
  · refine ⟨?_, (hFamilyProp rootZero).2.1,
      (hFamilyProp rootZero).2.2.1, ?_⟩
    · intro u x y N hx hy
      have hLimit := (hFamilyProp u).1 x y N hx hy
      simpa only [hFieldEq u] using hLimit
    · intro u n
      have hCalibration := (hFamilyProp u).2.2.2 n
      simpa only [hFieldEq u] using hCalibration
  · intro D hD
    apply hFamilyUnique rootZero D
    refine ⟨?_, hD.2.1, hD.2.2.1, ?_⟩
    · intro x y N hx hy
      exact hD.1 rootZero x y N hx hy
    · intro n
      exact hD.2.2.2 rootZero n

end LPP.Busemann
