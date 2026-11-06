/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.TopRestrictedMean
public import ProbabilityBasics.Probability.FiniteIndexConcentration
public import Differentiability.Probability.TopIndicatorShape
import Mathlib.Tactic.Linarith

/-!
# Concentration for restricted top-indicator paths

A top-indicator shape bounds restricted passage means. The resulting
fixed-endpoint concentration estimate holds for paths confined to a given
region, on the original environment space.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace LPPDifferentiability

open Classical in
/-- A proved upper bound for the actual restricted mean gives the sharp strict
path-exceedance tail. The final producer below supplies that bound from its same
shape witness. Empty regions have exactly zero path-exceedance probability. -/
theorem source_top_restricted_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (R : Finset Lattice) (u : Lattice) (d : ℕ × ℕ) :
    let M : EReal := sSup ((fun t : ℝ => (t : EReal)) '' μ.support)
    let c : ℝ → Bool := fun t => if (t : EReal) = M then true else false
    let I : Type := {z : Lattice // z ∈ R}
    let Eligible : Type :=
      {p : Path u d // ∀ j : Fin (d.1 + d.2 + 1), p.vertex j ∈ R}
    let P : Finset Eligible := Finset.univ
    let count : Eligible → (I → Bool) → ℕ := fun p x =>
      (p.val.collectedSites.filter
        (fun z => if hz : z ∈ R then x ⟨z, hz⟩ = true else False)).card
    let F : (I → Bool) → ℝ := fun x => (↑(P.sup (fun p => count p x) : ℕ) : ℝ)
    let X : Environment → I → Bool := fun ω i => c (ω i.val)
    ∀ (b t : ℝ), 0 ≤ b → 0 ≤ t →
      (∫ ω, F (X ω) ∂environmentLaw μ) ≤ b →
      let E : Set Environment := {ω | ∃ p : Path u d,
        (∀ j : Fin (d.1 + d.2 + 1), p.vertex j ∈ R) ∧
        b + t < ((p.collectedSites.filter (fun z => (ω z : EReal) = M)).card : ℝ)}
      MeasurableSet E ∧
        (0 < R.card → (environmentLaw μ).real E ≤
          Real.exp (-(2 * t ^ 2) / (R.card : ℝ))) ∧
        (R = ∅ → (environmentLaw μ).real E = 0) := by
  classical
  intro M c I Eligible P count F X b t hb ht hmean E
  let ν : Measure (I → Bool) := Measure.pi (fun _ : I => μ.map c)
  have : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  obtain ⟨_hc, hX, hlaw, hF, _hi, _hiorig, heq, _hdom⟩ :=
    source_top_restricted_transport μ R u d
  change Measurable X at hX
  change (environmentLaw μ).map X = ν at hlaw
  change Measurable F at hF
  change (∫ ω, F (X ω) ∂environmentLaw μ) = (∫ x, F x ∂ν) at heq
  have hE : E = {ω | F (X ω) > b + t} := by
    ext ω
    exact (source_top_restricted_gt_iff μ R u d ω (b + t) (add_nonneg hb ht)).symm
  have hmeas : MeasurableSet {x | F x > b + t} :=
    measurableSet_lt measurable_const hF
  have hprob : (environmentLaw μ).real E = ν.real {x | F x > b + t} := by
    rw [hE, ← hlaw, map_measureReal_apply hX hmeas]
    rfl
  refine ⟨hE.symm ▸ hmeas.preimage hX, ?_, ?_⟩
  · intro hR
    have hnonneg : ∀ x, 0 ≤ F x := restrictedPathCountMaximum_nonneg u d R
    have hbound : ∀ x, |F x| ≤ (d.1 + d.2 : ℕ) := by
      intro x
      rw [abs_of_nonneg (hnonneg x)]
      exact restrictedPathCountMaximum_le_length u d R x
    have hcard : Fintype.card I = R.card := Fintype.card_coe R
    have hscale : (0 : ℝ) < (Fintype.card I : ℝ) * (1 : ℝ) ^ 2 := by
      rw [hcard]
      simpa only [one_pow, mul_one] using (Nat.cast_pos.mpr hR : (0 : ℝ) < R.card)
    let δ₀ : DecidableEq I := inferInstance
    have hosc : ∀ x i y,
        |F (@Function.update I (fun _ => Bool) δ₀ x i y) - F x| ≤ 1 :=
      restrictedPathCountMaximum_update_abs_le u d R
    have hosc_all (δ : DecidableEq I) :
        ∀ x i y, |F (@Function.update I (fun _ => Bool) δ x i y) - F x| ≤ 1 := by
      intro x i y
      have hupdate : @Function.update I (fun _ => Bool) δ x i y =
          @Function.update I (fun _ => Bool) δ₀ x i y := by
        funext j
        by_cases hj : j = i
        · subst j
          simp only [Function.update]
        · simp only [Function.update, dite_eq_right hj]
      rw [hupdate]
      exact hosc x i y
    have htail := measure_ge_centered_pi_le_sharp_of_fintype
      (fun _ : I => μ.map c) (F := F) (M := ((d.1 + d.2 : ℕ) : ℝ)) (b := 1)
      (Nat.cast_nonneg _) (by norm_num) hF hbound
      (hosc_all _) ht hscale
    rw [hprob]
    calc
      ν.real {x | F x > b + t} ≤
          ν.real {x | t ≤ F x - ∫ z, F z ∂ν} := by
        refine measureReal_mono ?_ (measure_ne_top ν _)
        intro x hx
        have hm : (∫ z, F z ∂ν) ≤ b := by rw [← heq]; exact hmean
        change b + t < F x at hx
        change t ≤ F x - ∫ z, F z ∂ν
        linarith only [hx, hm]
      _ ≤ Real.exp (-(2 * t ^ 2) / (R.card : ℝ)) := by
        simpa only [hcard, one_pow, mul_one] using htail
  · intro hR
    have hEmpty : E = ∅ := by
      ext ω
      constructor
      · rintro ⟨p, hp, _h⟩
        have h := hp (0 : Fin (d.1 + d.2 + 1))
        rw [hR] at h
        exact (Finset.notMem_empty _ h).elim
      · exact False.elim
    rw [hEmpty]
    exact measureReal_empty

open Classical in
/-- One genuine top-indicator shape also controls all actual restricted means
and fixed-endpoint confined-path tails on the original environment space. -/
theorem exists_source_top_indicator_shape_with_restricted_concentration
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    let M : EReal := sSup ((fun t : ℝ => (t : EReal)) '' μ.support)
    let χ : ℝ → ℝ := fun t => if (t : EReal) = M then 1 else 0
    ∃ g : Quadrant → ℝ,
      Continuous g ∧
      (∀ (c : ℝ≥0) (x : Quadrant),
        g (c * x.1, c * x.2) = (c : ℝ) * g x) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        (a : ℝ) * g x + (b : ℝ) * g y ≤
          g (a * x.1 + b * y.1, a * x.2 + b * y.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          |lastPassage (fun z => χ (ω z)) 0 d -
            g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
              ε * ((d.1 + d.2 : ℕ) : ℝ)) ∧
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage (fun z => χ (ω z)) 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) ∧
      (∀ (u : Lattice) (d : ℕ × ℕ),
        Integrable (fun ω : Environment => lastPassage (fun z => χ (ω z)) u d)
          (environmentLaw μ)) ∧
      (∀ x : Quadrant, 0 ≤ g x ∧ g x ≤ (x.1 : ℝ) + x.2) ∧
      (∀ (u : Lattice) (d : ℕ × ℕ),
        (∫ ω : Environment, lastPassage (fun z => χ (ω z)) u d ∂environmentLaw μ) ≤
          g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))) ∧
      (∀ x : Quadrant, (∫ t : ℝ, t ∂μ.map χ) * ((x.1 : ℝ) + x.2) ≤ g x) ∧
      (M = ⊤ → g = fun _ => 0) ∧
      (∀ (R : Finset Lattice) (u : Lattice) (d : ℕ × ℕ),
        let I : Type := {z : Lattice // z ∈ R}
        let Eligible : Type :=
          {p : Path u d // ∀ j : Fin (d.1 + d.2 + 1), p.vertex j ∈ R}
        let P : Finset Eligible := Finset.univ
        let count : Eligible → (I → Bool) → ℕ := fun p x =>
          (p.val.collectedSites.filter
            (fun z => if hz : z ∈ R then x ⟨z, hz⟩ = true else False)).card
        let F : (I → Bool) → ℝ := fun x => (↑(P.sup (fun p => count p x) : ℕ) : ℝ)
        let X : Environment → I → Bool := fun ω i =>
          if (ω i.val : EReal) = M then true else false
        Measurable (fun ω => F (X ω)) ∧
          Integrable (fun ω => F (X ω)) (environmentLaw μ) ∧
          (∫ ω, F (X ω) ∂environmentLaw μ) ≤ g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) ∧
          (∀ t : ℝ, 0 ≤ t →
            let E : Set Environment := {ω | ∃ p : Path u d,
              (∀ j : Fin (d.1 + d.2 + 1), p.vertex j ∈ R) ∧
              g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) + t <
                ((p.collectedSites.filter (fun z => (ω z : EReal) = M)).card : ℝ)}
            MeasurableSet E ∧
              (0 < R.card → (environmentLaw μ).real E ≤
                Real.exp (-(2 * t ^ 2) / (R.card : ℝ))) ∧
              (R = ∅ → (environmentLaw μ).real E = 0))) := by
  classical
  intro M χ
  obtain ⟨g, hcont, hhom, hconc, hsample, hlim, hpass, hbound, hwhole, hlower, htop⟩ :=
    exists_source_top_indicator_shape μ
  refine ⟨g, hcont, hhom, hconc, hsample, hlim, hpass, hbound, hwhole, hlower, htop, ?_⟩
  intro R u d I Eligible P count F X
  obtain ⟨_hc, hX, _hlaw, hF, _hi, hiorig, _heq, hdom⟩ :=
    source_top_restricted_transport μ R u d
  have hmean : (∫ ω, F (X ω) ∂environmentLaw μ) ≤
      g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) :=
    (integral_mono hiorig (hpass u d) hdom).trans (hwhole u d)
  refine ⟨hF.comp hX, hiorig, hmean, ?_⟩
  intro t ht
  exact source_top_restricted_tail μ R u d
    (g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))) t
    (hbound ((d.1 : ℝ≥0), (d.2 : ℝ≥0))).1 ht hmean

end LPPDifferentiability
