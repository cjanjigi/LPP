/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.Additive
public import Busemann.Frozen.Definitions.Recovery
public import LPP_Foundations.Frozen.Model.LastPassage
import Busemann.Process.NortheastBoundaryPotential
import LPP_Foundations.Model.LastPassage.Basic
import LPP_Foundations.Model.LastPassage.Bounds
import LPP_Foundations.Model.Paths.Geometry
import Mathlib.Tactic

/-! The two one-sided terminal boundaries recover the finite cocycle maximum. -/
@[expose] public section
open LPPDifferentiability LPP.Busemann
open scoped BigOperators

namespace LPP.Busemann

/-- The cocycle potential is the larger of the two one-sided boundary passage
values. This finite consequence of recovery and the two-boundary NE identity
is related to GRS 1510.00859v2, (5.7)–(5.8) and Lemmas 6.3–6.4; it is not
a separate displayed statement in that source. -/
theorem cocycle_potential_eq_max_one_sided_boundary_passages
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hrec : recovers_environment ω C)
    (x : Lattice) (d : ℕ × ℕ) :
    let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
    let ωN : Environment := fun z =>
      if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0))
      else ω z
    let ωE : Environment := fun z =>
      if z.1 = v.1 ∧ z.2 < v.2 then C z (z + (0, 1))
      else ω z
    C x v = max (lastPassage ωN x d) (lastPassage ωE x d) := by
  classical
  intro v ωN ωE
  let ωNE : Environment := fun z =>
    if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0))
    else if z.1 = v.1 ∧ z.2 < v.2 then C z (z + (0, 1))
    else ω z
  have hNEmax := northeast_boundary_potential_eq_cocycle ω C hC hrec x d
  have hNE : lastPassage ωNE x d = C x v := by
    exact hNEmax.1
  have hNleNE : ∀ z, ωN z ≤ ωNE z := by
    intro z
    by_cases hn : z.2 = v.2 ∧ z.1 < v.1
    · simp [ωN, ωNE, hn]
    · by_cases he : z.1 = v.1 ∧ z.2 < v.2
      · calc
          ωN z = ω z := by simp [ωN, hn]
          _ = min (C z (z + (1, 0))) (C z (z + (0, 1))) := (hrec z).symm
          _ ≤ C z (z + (0, 1)) := min_le_right _ _
          _ = ωNE z := by simp [ωNE, he]
      · simp [ωN, ωNE, hn, he]
  have hEleNE : ∀ z, ωE z ≤ ωNE z := by
    intro z
    by_cases he : z.1 = v.1 ∧ z.2 < v.2
    · simp [ωE, ωNE, he]
    · by_cases hn : z.2 = v.2 ∧ z.1 < v.1
      · calc
          ωE z = ω z := by simp [ωE, he]
          _ = min (C z (z + (1, 0))) (C z (z + (0, 1))) := (hrec z).symm
          _ ≤ C z (z + (1, 0)) := min_le_left _ _
          _ = ωNE z := by simp [ωNE, hn]
      · simp [ωE, ωNE, hn, he]
  have hNbound : lastPassage ωN x d ≤ C x v := by
    calc
      lastPassage ωN x d ≤ lastPassage ωNE x d :=
        lastPassage_mono ωN ωNE x d hNleNE
      _ = C x v := hNE
  have hEbound : lastPassage ωE x d ≤ C x v := by
    calc
      lastPassage ωE x d ≤ lastPassage ωNE x d :=
        lastPassage_mono ωE ωNE x d hEleNE
      _ = C x v := hNE
  have hupper : max (lastPassage ωN x d) (lastPassage ωE x d) ≤ C x v :=
    max_le hNbound hEbound
  by_cases hzero : d.1 + d.2 = 0
  · have hd : d = (0, 0) := by
      ext <;> omega
    have hdiag : C x x = 0 := by
      have h := hC x x x
      linarith
    have hv : v = x := by simp [v, hd]
    rw [hv, hd]
    simp only [lastPassage_zero, max_self]
    exact hdiag
  · have hm : 0 < d.1 + d.2 := Nat.pos_of_ne_zero hzero
    let m : ℕ := d.1 + d.2
    let j : Fin m := ⟨m - 1, by dsimp [m]; omega⟩
    have hlast : j.succ = Fin.last m := by
      apply Fin.ext
      change j.val + 1 = m
      dsimp [j]
      omega
    obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ωNE x d
    have hpNE : pathWeight ωNE p = C x v := hp.trans hNE
    have hlastStep :
        p.vertex j.castSucc + (1, 0) = v ∨ p.vertex j.castSucc + (0, 1) = v := by
      have hs := p.step j
      rw [hlast, p.finish] at hs
      rcases hs with heast | hnorth
      · exact Or.inl (by simpa [v, m] using heast.symm)
      · exact Or.inr (by simpa [v, m] using hnorth.symm)
    rcases hlastStep with hEast | hNorth
    · have hpenFirst : (p.vertex j.castSucc).1 + 1 = v.1 := by
        have h := congrArg Prod.fst hEast
        simpa using h
      have hpenFirstLt : (p.vertex j.castSucc).1 < v.1 := by omega
      have hcollectedFirstLt (i : Fin m) : (p.vertex i.castSucc).1 < v.1 := by
        have hival : i.val ≤ j.val := by
          dsimp [j]
          omega
        have hij : i.castSucc ≤ j.castSucc := by
          rw [Fin.le_iff_val_le_val]
          simpa only [Fin.val_castSucc] using hival
        exact lt_of_le_of_lt (p.fst_monotone hij) hpenFirstLt
      have hweightN : pathWeight ωNE p = pathWeight ωN p := by
        unfold pathWeight
        apply Finset.sum_congr rfl
        intro i hi
        have hfirstNe : (p.vertex i.castSucc).1 ≠ v.1 :=
          ne_of_lt (hcollectedFirstLt i)
        have hnotEast :
            ¬ ((p.vertex i.castSucc).1 = v.1 ∧
              (p.vertex i.castSucc).2 < v.2) := by
          rintro ⟨heq, _⟩
          exact hfirstNe heq
        simp [ωNE, ωN, hnotEast]
      have hpN : pathWeight ωN p = C x v := hweightN.symm.trans hpNE
      have hlower : C x v ≤ max (lastPassage ωN x d) (lastPassage ωE x d) := by
        calc
          C x v = pathWeight ωN p := hpN.symm
          _ ≤ lastPassage ωN x d := pathWeight_le_lastPassage ωN p
          _ ≤ max (lastPassage ωN x d) (lastPassage ωE x d) := le_max_left _ _
      exact le_antisymm hlower hupper
    · have hpenSecond : (p.vertex j.castSucc).2 + 1 = v.2 := by
        have h := congrArg Prod.snd hNorth
        simpa using h
      have hpenSecondLt : (p.vertex j.castSucc).2 < v.2 := by omega
      have hcollectedSecondLt (i : Fin m) : (p.vertex i.castSucc).2 < v.2 := by
        have hival : i.val ≤ j.val := by
          dsimp [j]
          omega
        have hij : i.castSucc ≤ j.castSucc := by
          rw [Fin.le_iff_val_le_val]
          simpa only [Fin.val_castSucc] using hival
        exact lt_of_le_of_lt (p.snd_monotone hij) hpenSecondLt
      have hweightE : pathWeight ωNE p = pathWeight ωE p := by
        unfold pathWeight
        apply Finset.sum_congr rfl
        intro i hi
        have hsecondNe : (p.vertex i.castSucc).2 ≠ v.2 :=
          ne_of_lt (hcollectedSecondLt i)
        have hnotNorth :
            ¬ ((p.vertex i.castSucc).2 = v.2 ∧
              (p.vertex i.castSucc).1 < v.1) := by
          rintro ⟨heq, _⟩
          exact hsecondNe heq
        simp [ωNE, ωE, hnotNorth]
      have hpE : pathWeight ωE p = C x v := hweightE.symm.trans hpNE
      have hlower : C x v ≤ max (lastPassage ωN x d) (lastPassage ωE x d) := by
        calc
          C x v = pathWeight ωE p := hpE.symm
          _ ≤ lastPassage ωE x d := pathWeight_le_lastPassage ωE p
          _ ≤ max (lastPassage ωN x d) (lastPassage ωE x d) := le_max_right _ _
      exact le_antisymm hlower hupper

end LPP.Busemann
