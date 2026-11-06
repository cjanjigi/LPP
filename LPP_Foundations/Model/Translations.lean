/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Environment
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Filter.Cofinite

import Mathlib.Algebra.Group.Prod

/-! Deterministic facts about integer translations of environments and finite sets. -/

public section

namespace LPPDifferentiability

/-- Iterating the existing environment translation adds its displacement each time. -/
theorem environment_translate_iterate (ω : Environment) (v : Lattice) (n : ℕ)
    (z : Lattice) :
    ((fun ω : Environment => fun z => ω (v + z))^[n] ω) z = ω (n • v + z) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change ((fun ω : Environment => fun z => ω (v + z))^[n] ω) (v + z) =
        ω (Nat.succ n • v + z)
      calc
        _ = ω (n • v + (v + z)) := ih (v + z)
        _ = ω ((n • v + v) + z) := by rw [add_assoc]
        _ = ω ((n + 1) • v + z) := by rw [← succ_nsmul]
        _ = ω (Nat.succ n • v + z) := by rw [Nat.succ_eq_add_one]

private theorem nat_smul_lattice_injective (v : Lattice) (hv : v ≠ 0) :
    Function.Injective (fun n : ℕ => n • v) := by
  intro n m hnm
  by_cases hv₁ : v.1 = 0
  · have hv₂ : v.2 ≠ 0 := by
      intro h₂
      apply hv
      exact Prod.ext hv₁ h₂
    have hcoord : n • v.2 = m • v.2 := by
      simpa using congrArg (AddMonoidHom.snd ℤ ℤ) hnm
    have hmul : (n : ℤ) * v.2 = (m : ℤ) * v.2 := by
      simpa only [Int.nsmul_eq_mul] using hcoord
    have hcast : (n : ℤ) = (m : ℤ) := mul_right_cancel₀ hv₂ hmul
    exact Int.natCast_inj.mp hcast
  · have hcoord : n • v.1 = m • v.1 := by
      simpa using congrArg (AddMonoidHom.fst ℤ ℤ) hnm
    have hmul : (n : ℤ) * v.1 = (m : ℤ) * v.1 := by
      simpa only [Int.nsmul_eq_mul] using hcoord
    have hcast : (n : ℤ) = (m : ℤ) := mul_right_cancel₀ hv₁ hmul
    exact Int.natCast_inj.mp hcast

/-- Any fixed finite set eventually misses a translate of another finite set
along repeated steps in a nonzero lattice direction. -/
theorem eventually_disjoint_finite_translates (v : Lattice) (hv : v ≠ 0)
    (S T : Finset Lattice) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Disjoint S (T.image fun z => n • v + z) := by
  let differences : Finset Lattice := (S ×ˢ T).image fun p => p.1 - p.2
  have havoids : ∀ᶠ n : ℕ in Filter.atTop,
      n • v ∉ (differences : Set Lattice) := by
    rw [← Nat.cofinite_eq_atTop]
    exact (nat_smul_lattice_injective v hv).tendsto_cofinite.eventually
      differences.finite_toSet.eventually_cofinite_notMem
  filter_upwards [havoids] with n hn
  rw [Finset.disjoint_left]
  intro x hxS hxImage
  obtain ⟨t, ht, hxt⟩ := Finset.mem_image.mp hxImage
  have hdiff : n • v ∈ differences := by
    apply Finset.mem_image.mpr
    refine ⟨(x, t), Finset.mem_product.mpr ⟨hxS, ht⟩, ?_⟩
    change x - t = n • v
    rw [← hxt]
    exact add_sub_cancel_right _ _
  exact hn hdiff

end LPPDifferentiability
