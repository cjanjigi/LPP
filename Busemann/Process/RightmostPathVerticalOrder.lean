/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RightmostPaths
public import LPP_Foundations.Model.Paths.HeightOrder
import Mathlib.Order.Monotone.Basic
import Lean.Elab.Tactic.Omega

/-! Height and north-hit ordering of the three old vertical rays in Appendix A.4. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

private theorem vertical_path_step
    (C : Lattice → Lattice → ℝ) (x : Lattice) (n : ℕ) :
    rightmostCocyclePath C x (n + 1) = rightmostCocyclePath C x n + (1, 0) ∨
      rightmostCocyclePath C x (n + 1) = rightmostCocyclePath C x n + (0, 1) := by
  simpa only [rightmostCocyclePath, Function.iterate_succ_apply'] using
    rightmostCocycleSuccessor_step C (rightmostCocyclePath C x n)

private theorem vertical_path_level
    (C : Lattice → Lattice → ℝ) (x : Lattice) (n : ℕ) :
    (rightmostCocyclePath C x n).1 + (rightmostCocyclePath C x n).2 =
      x.1 + x.2 + (n : ℤ) := by
  induction n with
  | zero => simp only [rightmostCocyclePath, Function.iterate_zero_apply, Nat.cast_zero, add_zero]
  | succ n ih =>
      rcases vertical_path_step C x n with h | h <;>
        simp only [h, Prod.fst_add, Prod.snd_add, Nat.cast_succ] <;> omega

private theorem vertical_path_coordinates_monotone
    (C : Lattice → Lattice → ℝ) (x : Lattice) :
    Monotone (fun n => (rightmostCocyclePath C x n).1) ∧
      Monotone (fun n => (rightmostCocyclePath C x n).2) := by
  constructor
  · apply monotone_nat_of_le_succ
    intro n
    rcases vertical_path_step C x n with h | h <;>
      simp only [h, Prod.fst_add] <;> omega
  · apply monotone_nat_of_le_succ
    intro n
    rcases vertical_path_step C x n with h | h <;>
      simp only [h, Prod.snd_add] <;> omega

private theorem vertical_rays_height_lt_of_disjoint
    (C : Lattice → Lattice → ℝ) (a b : ℕ) (hab : a < b)
    (hAvoid : ∀ r s : ℕ,
      rightmostCocyclePath C (0, (a : ℤ)) r ≠
        rightmostCocyclePath C (0, (b : ℤ)) s)
    (n : ℕ) (hbn : b ≤ n) :
    (rightmostCocyclePath C (0, (a : ℤ)) (n - a)).2 <
      (rightmostCocyclePath C (0, (b : ℤ)) (n - b)).2 := by
  let p : ℕ → Lattice := fun k =>
    rightmostCocyclePath C (0, (a : ℤ)) (b - a + k)
  let q : ℕ → Lattice := rightmostCocyclePath C (0, (b : ℤ))
  have hpStep (k : ℕ) :
      p (k + 1) = p k + (1, 0) ∨ p (k + 1) = p k + (0, 1) := by
    dsimp only [p]
    simpa only [Nat.add_assoc] using vertical_path_step C (0, (a : ℤ)) (b - a + k)
  have hqStep (k : ℕ) :
      q (k + 1) = q k + (1, 0) ∨ q (k + 1) = q k + (0, 1) :=
    vertical_path_step C (0, (b : ℤ)) k
  have hqZero : q 0 = (0, (b : ℤ)) := by
    simp only [q, rightmostCocyclePath, Function.iterate_zero_apply]
  have hpLevel : (p 0).1 + (p 0).2 = (b : ℤ) := by
    have h := vertical_path_level C (0, (a : ℤ)) (b - a)
    simp only [zero_add] at h
    dsimp only [p]
    simp only [Nat.add_zero]
    omega
  have hInitialLevel : (p 0).1 + (p 0).2 = (q 0).1 + (q 0).2 := by
    rw [hqZero]
    simpa only [zero_add] using hpLevel
  have hpFirstNonneg : 0 ≤ (p 0).1 := by
    have h := (vertical_path_coordinates_monotone C (0, (a : ℤ))).1
      (Nat.zero_le (b - a))
    simpa only [p, Nat.add_zero, rightmostCocyclePath,
      Function.iterate_zero_apply] using h
  have hpqNe : p 0 ≠ q 0 := by
    simpa only [p, q, Nat.add_zero] using hAvoid (b - a) 0
  have hInitialHeightNe : (p 0).2 ≠ (b : ℤ) := by
    intro hHeight
    apply hpqNe
    rw [hqZero]
    apply Prod.ext
    · have hFirst : (p 0).1 = 0 := by omega
      exact hFirst
    · exact hHeight
  have hInitialHeight : (p 0).2 < (q 0).2 := by
    rw [hqZero]
    change (p 0).2 < (b : ℤ)
    omega
  have hAvoidShifted : ∀ k, k ≤ n - b → p k ≠ q k := by
    intro k _
    exact hAvoid (b - a + k) k
  have hFinalHeight : (p (n - b)).2 < (q (n - b)).2 :=
    (up_right_paths_strict_height_order_iff_of_disjoint p q (n - b)
      hpStep hqStep hInitialLevel hAvoidShifted).mp hInitialHeight
  have hIndex : b - a + (n - b) = n - a := by omega
  simpa only [p, q, hIndex] using hFinalHeight

/-- The three disjoint old rightmost rays retain their strict height order at
all common absolute levels, and their actual north-line hits satisfy
`0 ≤ a1 < a2 < M1`. This derives the old-ray geometry used in Georgiou,
Rassoul-Agha and Seppäläinen, arXiv:1510.00860v1, Appendix A.4,
lines 1570–1575 and 1616–1632, from the physical ray and hit data. -/
theorem rightmostCocyclePath_height_order_and_north_hit_order
    (C : Lattice → Lattice → ℝ)
    (m ell : ℕ) (hm : 0 < m) (hmell : m < ell)
    (M1 M2 a1 a2 : ℤ) (hTop : (ell : ℤ) < M2)
    (nL nM nU : ℕ)
    (hNorthL : rightmostCocyclePath C 0 nL = (M1, M2))
    (hNorthM : rightmostCocyclePath C (0, (m : ℤ)) nM = (a2, M2))
    (hNorthU : rightmostCocyclePath C (0, (ell : ℤ)) nU = (a1, M2))
    (hDisjointLM : ∀ r s : ℕ,
      rightmostCocyclePath C 0 r ≠
        rightmostCocyclePath C (0, (m : ℤ)) s)
    (hDisjointMU : ∀ r s : ℕ,
      rightmostCocyclePath C (0, (m : ℤ)) r ≠
        rightmostCocyclePath C (0, (ell : ℤ)) s) :
    (∀ n : ℕ, m ≤ n →
      (rightmostCocyclePath C 0 n).2 <
        (rightmostCocyclePath C (0, (m : ℤ)) (n - m)).2) ∧
    (∀ n : ℕ, ell ≤ n →
      (rightmostCocyclePath C (0, (m : ℤ)) (n - m)).2 <
        (rightmostCocyclePath C (0, (ell : ℤ)) (n - ell)).2) ∧
    0 ≤ a1 ∧ a1 < a2 ∧ a2 < M1 := by
  -- Disjointness makes the initial common-level comparison strict; finite order propagates it.
  have hZero : ((0, 0) : Lattice) = (0 : Lattice) := by
    apply Prod.ext <;> simp only [Prod.fst_zero, Prod.snd_zero]
  have hLM : ∀ n : ℕ, m ≤ n →
      (rightmostCocyclePath C 0 n).2 <
        (rightmostCocyclePath C (0, (m : ℤ)) (n - m)).2 := by
    intro n hn
    simpa only [Nat.sub_zero, Nat.cast_zero, hZero] using
      vertical_rays_height_lt_of_disjoint C 0 m hm hDisjointLM n hn
  have hMU : ∀ n : ℕ, ell ≤ n →
      (rightmostCocyclePath C (0, (m : ℤ)) (n - m)).2 <
        (rightmostCocyclePath C (0, (ell : ℤ)) (n - ell)).2 :=
    vertical_rays_height_lt_of_disjoint C m ell hmell hDisjointMU

  -- The first coordinate is nonnegative for every ray rooted on the vertical axis.
  have hFirstNonneg (a k : ℕ) :
      0 ≤ (rightmostCocyclePath C (0, (a : ℤ)) k).1 := by
    have h := (vertical_path_coordinates_monotone C (0, (a : ℤ))).1 (Nat.zero_le k)
    simpa only [rightmostCocyclePath, Function.iterate_zero_apply] using h
  have ha1 : 0 ≤ a1 := by simpa only [hNorthU] using hFirstNonneg ell nU
  have ha2 : 0 ≤ a2 := by simpa only [hNorthM] using hFirstNonneg m nM

  -- Actual hit equations determine all three absolute hit levels.
  have hLevelL : M1 + M2 = (nL : ℤ) := by
    simpa only [hNorthL, Prod.fst_zero, Prod.snd_zero, zero_add] using
      vertical_path_level C 0 nL
  have hLevelM : a2 + M2 = (m : ℤ) + (nM : ℤ) := by
    simpa only [hNorthM, zero_add] using vertical_path_level C (0, (m : ℤ)) nM
  have hLevelU : a1 + M2 = (ell : ℤ) + (nU : ℤ) := by
    simpa only [hNorthU, zero_add] using vertical_path_level C (0, (ell : ℤ)) nU
  have hAboveUpperStart : ell ≤ m + nM := by omega
  have hMiddleIndex : m + nM - m = nM := by omega
  have hLowerBelow : (rightmostCocyclePath C 0 (m + nM)).2 < M2 := by
    have h := hLM (m + nM) (by omega)
    simpa only [hMiddleIndex, hNorthM] using h
  have hUpperAbove : M2 <
      (rightmostCocyclePath C (0, (ell : ℤ)) (m + nM - ell)).2 := by
    have h := hMU (m + nM) hAboveUpperStart
    simpa only [hMiddleIndex, hNorthM] using h

  -- Monotonicity forces upper hit earlier and lower hit later than the middle hit level.
  have hUpperTime : nU < m + nM - ell := by
    by_contra hNot
    have hMono := (vertical_path_coordinates_monotone C (0, (ell : ℤ))).2
      (show m + nM - ell ≤ nU by omega)
    have hAtUpper :
        (rightmostCocyclePath C (0, (ell : ℤ)) (m + nM - ell)).2 ≤ M2 := by
      simpa only [hNorthU] using hMono
    omega
  have hLowerTime : m + nM < nL := by
    by_contra hNot
    have hMono := (vertical_path_coordinates_monotone C 0).2
      (show nL ≤ m + nM by omega)
    have hAtLower : M2 ≤ (rightmostCocyclePath C 0 (m + nM)).2 := by
      simpa only [hNorthL] using hMono
    omega
  have ha1a2 : a1 < a2 := by omega
  have ha2M1 : a2 < M1 := by omega
  exact ⟨hLM, hMU, ha1, ha1a2, ha2M1⟩

end LPP.Busemann
