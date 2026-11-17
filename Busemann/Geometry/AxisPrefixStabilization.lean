/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.RightmostCocyclePath
public import Mathlib.Topology.Instances.Real.Lemmas

/-! Finite axis prefixes of the existing rightmost cocycle path. -/

@[expose] public section
open Filter LPPDifferentiability
open scoped Topology

namespace LPP.Busemann

/-- Finite axis prefixes stabilize when longitudinal increments have finite
limits and transverse increments diverge. The existing successor takes east
at ties; north stabilization uses a strict reverse inequality.
JSP (2025), Lemma 5.1; GRS arXiv:1510.00860v1, Lemma 5.1. -/
theorem rightmostCocyclePath_axis_prefix_stabilizes
    (u : Lattice) (Be Bn : ℕ → Lattice → Lattice → ℝ)
    (hEastFinite : ∀ k : ℕ, ∃ a : ℝ,
      Tendsto (fun n => Be n (u + ((k : ℤ), (0 : ℤ)))
        (u + ((k : ℤ), (0 : ℤ)) + ((1 : ℤ), (0 : ℤ)))) atTop (𝓝 a))
    (hEastTransverse : ∀ k : ℕ,
      Tendsto (fun n => Be n (u + ((k : ℤ), (0 : ℤ)))
        (u + ((k : ℤ), (0 : ℤ)) + ((0 : ℤ), (1 : ℤ)))) atTop atTop)
    (hNorthFinite : ∀ k : ℕ, ∃ a : ℝ,
      Tendsto (fun n => Bn n (u + ((0 : ℤ), (k : ℤ)))
        (u + ((0 : ℤ), (k : ℤ)) + ((0 : ℤ), (1 : ℤ)))) atTop (𝓝 a))
    (hNorthTransverse : ∀ k : ℕ,
      Tendsto (fun n => Bn n (u + ((0 : ℤ), (k : ℤ)))
        (u + ((0 : ℤ), (k : ℤ)) + ((1 : ℤ), (0 : ℤ)))) atTop atTop) :
    (∀ M : ℕ, ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, k ≤ M →
      rightmostCocyclePath (Be n) u k = u + ((k : ℤ), (0 : ℤ))) ∧
    (∀ M : ℕ, ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, k ≤ M →
      rightmostCocyclePath (Bn n) u k = u + ((0 : ℤ), (k : ℤ))) := by
  classical
  let eastAxis (k : ℕ) : Lattice := u + ((k : ℤ), (0 : ℤ))
  let northAxis (k : ℕ) : Lattice := u + ((0 : ℤ), (k : ℤ))
  have finiteEventually {P : ℕ → ℕ → Prop}
      (hP : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, P k n) (M : ℕ) :
      ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, k ≤ M → P k n := by
    have hfin (s : Finset ℕ) :
        ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, k ∈ s → P k n := by
      induction s using Finset.induction_on with
      | empty =>
        exact Filter.Eventually.of_forall fun _n _k hk => by
          simp at hk
      | @insert j s hjs ih =>
        filter_upwards [hP j, ih] with n hnew hkeep
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact hnew
        · exact hkeep k hk
    have h := hfin (Finset.range (M + 1))
    exact h.mono fun n hn k hk =>
      hn k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hEastCompare (k : ℕ) :
      ∀ᶠ n : ℕ in atTop,
        Be n (eastAxis k) (eastAxis k + ((1 : ℤ), (0 : ℤ))) <
          Be n (eastAxis k) (eastAxis k + ((0 : ℤ), (1 : ℤ))) := by
    obtain ⟨a, ha⟩ := hEastFinite k
    have hchosen : ∀ᶠ n : ℕ in atTop,
        Be n (eastAxis k) (eastAxis k + ((1 : ℤ), (0 : ℤ))) < a + 1 :=
      Filter.Tendsto.eventually_lt_const (lt_add_of_pos_right a zero_lt_one) ha
    have htransverse : ∀ᶠ n : ℕ in atTop,
        a + 1 ≤ Be n (eastAxis k) (eastAxis k + ((0 : ℤ), (1 : ℤ))) :=
      (Filter.tendsto_atTop.1 (hEastTransverse k)) (a + 1)
    filter_upwards [hchosen, htransverse] with n heast hnorth
    exact lt_of_lt_of_le heast hnorth
  have hNorthCompare (k : ℕ) :
      ∀ᶠ n : ℕ in atTop,
        Bn n (northAxis k) (northAxis k + ((0 : ℤ), (1 : ℤ))) <
          Bn n (northAxis k) (northAxis k + ((1 : ℤ), (0 : ℤ))) := by
    obtain ⟨a, ha⟩ := hNorthFinite k
    have hchosen : ∀ᶠ n : ℕ in atTop,
        Bn n (northAxis k) (northAxis k + ((0 : ℤ), (1 : ℤ))) < a + 1 :=
      Filter.Tendsto.eventually_lt_const (lt_add_of_pos_right a zero_lt_one) ha
    have htransverse : ∀ᶠ n : ℕ in atTop,
        a + 1 ≤ Bn n (northAxis k) (northAxis k + ((1 : ℤ), (0 : ℤ))) :=
      (Filter.tendsto_atTop.1 (hNorthTransverse k)) (a + 1)
    filter_upwards [hchosen, htransverse] with n enorth heast
    exact lt_of_lt_of_le enorth heast
  have hEastSuccessor (n k : ℕ)
      (h : Be n (eastAxis k) (eastAxis k + ((1 : ℤ), (0 : ℤ))) <
        Be n (eastAxis k) (eastAxis k + ((0 : ℤ), (1 : ℤ)))) :
      rightmostCocycleSuccessor (Be n) (eastAxis k) = eastAxis (k + 1) := by
    dsimp [rightmostCocycleSuccessor]
    rw [ite_eq_left (le_of_lt h)]
    apply Prod.ext <;> simp [eastAxis, Nat.cast_succ, add_assoc]
  have hNorthSuccessor (n k : ℕ)
      (h : Bn n (northAxis k) (northAxis k + ((0 : ℤ), (1 : ℤ))) <
        Bn n (northAxis k) (northAxis k + ((1 : ℤ), (0 : ℤ)))) :
      rightmostCocycleSuccessor (Bn n) (northAxis k) = northAxis (k + 1) := by
    dsimp [rightmostCocycleSuccessor]
    rw [ite_eq_right (not_le_of_gt h)]
    apply Prod.ext <;> simp [northAxis, Nat.cast_succ, add_assoc]
  have hEastPath (M n : ℕ)
      (hcmp : ∀ k : ℕ, k ≤ M →
        Be n (eastAxis k) (eastAxis k + ((1 : ℤ), (0 : ℤ))) <
          Be n (eastAxis k) (eastAxis k + ((0 : ℤ), (1 : ℤ)))) :
      ∀ k : ℕ, k ≤ M → rightmostCocyclePath (Be n) u k = eastAxis k := by
    intro k
    induction k with
    | zero =>
      intro _hk
      simp [rightmostCocyclePath, eastAxis]
    | succ k ih =>
      intro hk
      have hk' : k ≤ M := Nat.le_of_succ_le hk
      calc
        rightmostCocyclePath (Be n) u (k + 1) =
            rightmostCocycleSuccessor (Be n) (rightmostCocyclePath (Be n) u k) := by
          simp only [rightmostCocyclePath, Function.iterate_succ_apply']
        _ = rightmostCocycleSuccessor (Be n) (eastAxis k) := by rw [ih hk']
        _ = eastAxis (k + 1) := hEastSuccessor n k (hcmp k hk')
  have hNorthPath (M n : ℕ)
      (hcmp : ∀ k : ℕ, k ≤ M →
        Bn n (northAxis k) (northAxis k + ((0 : ℤ), (1 : ℤ))) <
          Bn n (northAxis k) (northAxis k + ((1 : ℤ), (0 : ℤ)))) :
      ∀ k : ℕ, k ≤ M → rightmostCocyclePath (Bn n) u k = northAxis k := by
    intro k
    induction k with
    | zero =>
      intro _hk
      simp [rightmostCocyclePath, northAxis]
    | succ k ih =>
      intro hk
      have hk' : k ≤ M := Nat.le_of_succ_le hk
      calc
        rightmostCocyclePath (Bn n) u (k + 1) =
            rightmostCocycleSuccessor (Bn n) (rightmostCocyclePath (Bn n) u k) := by
          simp only [rightmostCocyclePath, Function.iterate_succ_apply']
        _ = rightmostCocycleSuccessor (Bn n) (northAxis k) := by rw [ih hk']
        _ = northAxis (k + 1) := hNorthSuccessor n k (hcmp k hk')
  constructor
  · intro M
    filter_upwards [finiteEventually hEastCompare M] with n hcmp
    intro k hk
    exact hEastPath M n (fun j hj => hcmp j hj) k hk
  · intro M
    filter_upwards [finiteEventually hNorthCompare M] with n hcmp
    intro k hk
    exact hNorthPath M n (fun j hj => hcmp j hj) k hk

end LPP.Busemann
