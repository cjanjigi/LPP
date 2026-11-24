/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Model.Animals.PathSets
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Real
import Differentiability.Probability.StaircaseGeneral
import LPP_Foundations.Model.Paths.Fintype
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! # Uniform weight bound for selected staircase paths

At each scale the path family is a finite set selected using the whole very-bad
mask. Enumerating that set gives the finite slots for the lower-tail estimate.
The active slots and the original family define the same failure event.
-/

public section

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

namespace LPPDifferentiability.Paper

/-- Appendix B, `lem:stair-general`. Under the negative-part moment assumption,
the chance that any of the selected paths is too light tends to zero. The finite
family can inspect the entire very-bad mask. Each path stays in the working
region and avoids very bad vertices among its collected sites. -/
theorem staircase_path_family_weight_failure_tendsto_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p' : ℝ) (hp' : 1 < p')
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p') ∂μ) < ∞)
    (ε₀ cstar ρ : ℝ) (hε₀ : 0 < ε₀) (hcstar : 0 < cstar) (hρ : 1 ≤ ρ)
    (K2 : ℕ) (hK2 : 2 * ρ + 2 < (K2 : ℝ) * (p' - 1))
    (Q : ℕ → Set Lattice) (hQ : ∀ k, (Q k).Finite)
    (paths : ℕ → (Lattice → Bool) → Finset (Σ u : Lattice, Σ d : ℕ × ℕ, Path u d))
    (hmeas : ∀ k P, MeasurableSet {a | paths k a = P})
    (hcard : ∀ k a, ((paths k a).card : ℝ) ≤ ((2 : ℝ) ^ k) ^ ρ)
    (hlen : ∀ k a q, q ∈ paths k a →
      ((q.2.1.1 + q.2.1.2 : ℕ) : ℝ) ≤ 8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k)
    (hregion : ∀ k a q, q ∈ paths k a → ∀ i, q.2.2.vertex i ∈ Q k)
    (hgood : ∀ k a q, q ∈ paths k a → ∀ z ∈ q.2.2.collectedSites, a z = false) :
    let Cm : ℝ := ∫ y, max (-y) 0 ∂μ
    let Tk : ℕ → ℝ := fun k => ε₀ * (2 : ℝ) ^ k / (k : ℝ) / (4 * (K2 : ℝ))
    let tk : ℕ → ℝ := fun k => ε₀ * (2 : ℝ) ^ k / (k : ℝ)
    let mask : ℕ → Environment → Lattice → Bool :=
      fun k ω z => if ω z < -Tk k then true else false
    Tendsto (fun k : ℕ => (environmentLaw μ).real {ω : Environment |
      ∃ q ∈ paths k (mask k ω), pathWeight ω q.2.2 <
        -2 * Cm * ((q.2.1.1 + q.2.1.2 : ℕ) : ℝ) - tk k / 2}) atTop (𝓝 0) := by
  classical
  intro Cm Tk tk mask
  let PathFamily := Finset (Σ u : Lattice, Σ d : ℕ × ℕ, Path u d)
  let _ : Countable PathFamily := by
    dsimp only [PathFamily]
    infer_instance
  let _ : MeasurableSpace PathFamily := ⊤
  have hpaths (k : ℕ) : Measurable (paths k) := measurable_to_countable' (hmeas k)
  let N (k : ℕ) := ⌊((2 : ℝ) ^ k) ^ ρ⌋₊
  let active (k : ℕ) (F : PathFamily) (j : Fin (N k)) : Bool := decide (j.val < F.card)
  let sites (k : ℕ) (F : PathFamily) (j : Fin (N k)) : Finset Lattice :=
    if h : j.val < F.card then (F.equivFin.symm ⟨j.val, h⟩).val.2.2.collectedSites else ∅
  have hslot (k : ℕ) (F : PathFamily) (j : Fin (N k)) (h : j.val < F.card) :
      sites k F j = (F.equivFin.symm ⟨j.val, h⟩).val.2.2.collectedSites := dite_eq_left h
  have hselected (k : ℕ) (a : Lattice → Bool) (j : Fin (N k))
      (h : active k (paths k a) j = true) :
      ∃ q ∈ paths k a, sites k (paths k a) j = q.2.2.collectedSites := by
    have hindex : j.val < (paths k a).card := of_decide_eq_true h
    let q := (paths k a).equivFin.symm ⟨j.val, hindex⟩
    exact ⟨q.val, q.property, hslot k _ j hindex⟩
  have hN (k : ℕ) : (Fintype.card (Fin (N k)) : ℝ) ≤ ((2 : ℝ) ^ k) ^ ρ := by
    rw [Fintype.card_fin]
    exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  have hlimit := staircase_general_family_tendsto μ p' hp' hmoment ε₀ cstar ρ hε₀ hcstar hρ
    K2 hK2 0 Q hQ (fun k => Fin (N k)) (fun k _ => hN k)
    (fun k a j => active k (paths k a) j) (fun k a j => sites k (paths k a) j)
    (fun k a j h => by
      obtain ⟨q, hq, hsites⟩ := hselected k a j h
      rw [hsites, Path.collectedSites_card]
      exact hlen k a q hq)
    (fun k a j h z hz => by
      obtain ⟨q, hq, hsites⟩ := hselected k a j h
      rw [hsites] at hz
      obtain ⟨i, rfl⟩ := (q.2.2.mem_collectedSites_iff z).1 hz
      exact hregion k a q hq i.castSucc)
    (fun k a j h z hz => by
      obtain ⟨q, hq, hsites⟩ := hselected k a j h
      rw [hsites] at hz
      exact hgood k a q hq z hz)
    (fun k j S => (hpaths k) (t := {F | active k F j = true ∧ sites k F j = S}) trivial)
  have hevent (k : ℕ) :
      {ω : Environment | ∃ q ∈ paths k (mask k ω), pathWeight ω q.2.2 <
        -2 * Cm * ((q.2.1.1 + q.2.1.2 : ℕ) : ℝ) - tk k / 2} =
      {ω : Environment | ∃ j : Fin (N k), active k (paths k (mask k ω)) j = true ∧
        ∑ z ∈ sites k (paths k (mask k ω)) j, ω z <
          -2 * Cm * ((sites k (paths k (mask k ω)) j).card : ℝ) - tk k / 2} := by
    ext ω
    constructor
    · rintro ⟨q, hq, hw⟩
      let F := paths k (mask k ω)
      let i := F.equivFin ⟨q, hq⟩
      let j : Fin (N k) := ⟨i.val, i.isLt.trans_le (Nat.le_floor (hcard k (mask k ω)))⟩
      have hj : sites k F j = q.2.2.collectedSites := by
        rw [hslot k _ _ i.isLt]
        exact congrArg (fun r => r.val.2.2.collectedSites) (F.equivFin.symm_apply_apply ⟨q, hq⟩)
      refine ⟨j, decide_eq_true i.isLt, ?_⟩
      change ∑ z ∈ sites k F j, ω z < -2 * Cm * ((sites k F j).card : ℝ) - tk k / 2
      rw [hj, Path.collectedSites_card, ← Path.pathWeight_eq_sum_collectedSites]
      exact hw
    · rintro ⟨j, h, hw⟩
      obtain ⟨q, hq, hsites⟩ := hselected k (mask k ω) j h
      rw [hsites, Path.collectedSites_card, ← Path.pathWeight_eq_sum_collectedSites] at hw
      exact ⟨q, hq, hw⟩
  simp_rw [hevent]
  exact hlimit

end LPPDifferentiability.Paper
