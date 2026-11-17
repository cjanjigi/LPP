/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Finite.PathTransitionProduct
public import LPP_Foundations.Probability.PathArrowCylinder
import Busemann.Finite.TransitionBounds
import LPP_Foundations.Model.Paths.Level
import Mathlib.Tactic

/-! Actual finite Gibbs cylinder masses under one absolute-level uniform arrow field. -/

@[expose] public section

open MeasureTheory LPPDifferentiability
open scoped BigOperators unitInterval

namespace LPP.Busemann

/-- One sitewise uniform arrow field at an absolute terminal level gives the
actual normalized finite Gibbs mass to every admissible path reaching that
level. This is JR1810.03580v3, Appendix A.1, with the departure-site
weight correction. No trace pushforward or Markov property is asserted. -/
theorem exists_finite_gibbs_arrow_cylinder_field (ω : Environment) (h : ℝ × ℝ)
    (β : ℝ) (hβ : 0 < β) (L : ℤ) :
    let Z : ℕ → Lattice → ℝ := fun n y =>
      ∑ k : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
        Real.exp (β * (pathWeight ω p + h.1 * (k.val : ℝ) +
          h.2 * ((n - k.val : ℕ) : ℝ)))
    let r : Lattice → ℕ := fun y => (L - y.1 - y.2).toNat
    let q : Lattice → Fin 2 → ℝ := fun y i =>
      Real.exp (β * (ω y + finiteTiltCoordinate h i)) *
        Z (r y - 1) (y + finiteEdgeStep i) / Z (r y) y
    let Q : Measure (Lattice → unitInterval) :=
      Measure.infinitePi (fun _ : Lattice => (volume : Measure unitInterval))
    ∃ a : Lattice → unitInterval,
      (∀ y, y.1 + y.2 < L → (a y : ℝ) = q y 0) ∧
      let A : (Lattice → unitInterval) → Lattice → Lattice := fun θ y =>
        if θ y < a y then y + (1, 0) else y + (0, 1)
      ∀ (x : Lattice) (d : ℕ × ℕ),
        x.1 + x.2 + ((d.1 + d.2 : ℕ) : ℤ) = L →
        ∀ p : LPPDifferentiability.Path x d,
          let Gamma : Set (Lattice → unitInterval) :=
            {θ | ∀ j : Fin (d.1 + d.2 + 1), ((A θ)^[j.val]) x = p.vertex j}
          MeasurableSet Gamma ∧ Q Gamma = ENNReal.ofReal
            (Real.exp (β * (pathWeight ω p + h.1 * (d.1 : ℝ) +
              h.2 * (d.2 : ℝ))) / Z (d.1 + d.2) x) := by
  classical
  let Z : ℕ → Lattice → ℝ := fun n y =>
    ∑ k : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
      Real.exp (β * (pathWeight ω p + h.1 * (k.val : ℝ) +
        h.2 * ((n - k.val : ℕ) : ℝ)))
  let r : Lattice → ℕ := fun y => (L - y.1 - y.2).toNat
  let q : Lattice → Fin 2 → ℝ := fun y i =>
    Real.exp (β * (ω y + finiteTiltCoordinate h i)) *
      Z (r y - 1) (y + finiteEdgeStep i) / Z (r y) y
  let Q : Measure (Lattice → unitInterval) :=
    Measure.infinitePi (fun _ : Lattice => (volume : Measure unitInterval))
  change ∃ a : Lattice → unitInterval,
    (∀ y, y.1 + y.2 < L → (a y : ℝ) = q y 0) ∧ _

  -- Actual normalization at every active site gives genuine unit-interval thresholds.
  have hbounds (y : Lattice) (hy : y.1 + y.2 < L) :
      (∀ i, 0 < q y i ∧ q y i < 1) ∧ q y 0 + q y 1 = 1 := by
    have hpositive : 0 < r y := by
      dsimp only [r]
      omega
    have hsuc : r y - 1 + 1 = r y := by omega
    let t : Fin 2 → ℝ := fun i =>
      Real.exp (β * (ω y + finiteTiltCoordinate h i)) *
        Z (r y - 1) (y + finiteEdgeStep i) / Z (r y - 1 + 1) y
    have htBounds : (∀ i, 0 < t i ∧ t i < 1) ∧ t 0 + t 1 = 1 :=
      finite_tilted_partition_transition_bounds ω h β hβ (r y - 1) y
    have ht : t = q y := by
      funext i
      dsimp only [t, q]
      rw [hsuc]
    rw [ht] at htBounds
    exact htBounds
  let a : Lattice → unitInterval := fun y =>
    if hy : y.1 + y.2 < L then
      ⟨q y 0, ((hbounds y hy).1 0).1.le, ((hbounds y hy).1 0).2.le⟩
    else ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩
  have ha (y : Lattice) (hy : y.1 + y.2 < L) : (a y : ℝ) = q y 0 := by
    simp only [a, dite_eq_left hy]
  refine ⟨a, ha, ?_⟩
  let A : (Lattice → unitInterval) → Lattice → Lattice := fun θ y =>
    if θ y < a y then y + (1, 0) else y + (0, 1)
  change ∀ (x : Lattice) (d : ℕ × ℕ),
    x.1 + x.2 + ((d.1 + d.2 : ℕ) : ℤ) = L →
    ∀ p : LPPDifferentiability.Path x d,
      let Gamma : Set (Lattice → unitInterval) :=
        {θ | ∀ j : Fin (d.1 + d.2 + 1), ((A θ)^[j.val]) x = p.vertex j}
      MeasurableSet Gamma ∧ Q Gamma = _
  intro x d hLevel p
  let Gamma : Set (Lattice → unitInterval) :=
    {θ | ∀ j : Fin (d.1 + d.2 + 1), ((A θ)^[j.val]) x = p.vertex j}
  change MeasurableSet Gamma ∧ Q Gamma = _

  -- Every prescribed departure is active; the terminal vertex is never charged.
  have hactive (j : Fin (d.1 + d.2)) :
      (p.vertex j.castSucc).1 + (p.vertex j.castSucc).2 < L := by
    have hpath := p.level j.castSucc
    have hj := j.isLt
    simp only [Fin.val_castSucc] at hpath
    omega
  have hfactor (j : Fin (d.1 + d.2)) :
      (if stepCode p j then ((a (p.vertex j.castSucc)) : ℝ)
        else 1 - ((a (p.vertex j.castSucc)) : ℝ)) =
      q (p.vertex j.castSucc) (if stepCode p j = true then 0 else 1) := by
    have ha0 := ha (p.vertex j.castSucc) (hactive j)
    have hnorm := (hbounds (p.vertex j.castSucc) (hactive j)).2
    cases hc : stepCode p j
    · have hnorth : 1 - ((a (p.vertex j.castSucc)) : ℝ) = q (p.vertex j.castSucc) 1 := by
        rw [ha0]
        linarith only [hnorm]
      simpa [hc] using hnorth
    · simpa [hc] using ha0
  have hproduct :
      (∏ j : Fin (d.1 + d.2), if stepCode p j then
        ((a (p.vertex j.castSucc)) : ℝ) else 1 - ((a (p.vertex j.castSucc)) : ℝ)) =
      ∏ j : Fin (d.1 + d.2),
        q (p.vertex j.castSucc) (if stepCode p j = true then 0 else 1) :=
    Finset.prod_congr rfl (fun j _ => hfactor j)

  -- Consume both factors, transporting the path's terminal level to this same L.
  have htransition :
      (∏ j : Fin (d.1 + d.2),
        q (p.vertex j.castSucc) (if stepCode p j = true then 0 else 1)) =
      Real.exp (β * (pathWeight ω p + h.1 * (d.1 : ℝ) + h.2 * (d.2 : ℝ))) /
        Z (d.1 + d.2) x := by
    subst L
    exact finite_path_transition_product ω h β hβ x d p
  have hcylinder := uniform_arrow_path_cylinder a x d p
  have hmeas : MeasurableSet Gamma := hcylinder.1
  have hmass : Q Gamma = ENNReal.ofReal
      (∏ j : Fin (d.1 + d.2), if stepCode p j then
        ((a (p.vertex j.castSucc)) : ℝ) else 1 - ((a (p.vertex j.castSucc)) : ℝ)) :=
    hcylinder.2
  exact ⟨hmeas, hmass.trans (congrArg ENNReal.ofReal (hproduct.trans htransition))⟩

end LPP.Busemann
