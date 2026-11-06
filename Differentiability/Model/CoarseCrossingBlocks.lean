/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.FiniteLevelStripCardinality
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! Actual finite coarse crossing blocks with the source count and separation. -/
public section

namespace LPPDifferentiability

/-- Rounded centers and their actual closed crossing blocks, with the source
counting bound and pairwise disjointness. -/
theorem exists_coarse_crossing_blocks
    (a h w : ℝ) (I : ℤ) (ell m N : ℕ)
    (hw : 1 ≤ w) (hm : 2 * m < ell) (hell : (ell : ℝ) ≤ w ^ 3 / 2) :
    ∃ c : Fin N → Lattice, ∃ B : Fin N → Finset Lattice,
      (∀ nu, (c nu).1 + (c nu).2 = I + (m : ℤ)) ∧
      (∀ nu, |(1-a)*((c nu).1 : ℝ)-a*((c nu).2 : ℝ) -
        (h*w + 30*((nu.val+1 : ℕ) : ℝ)*w)| ≤ 1/2) ∧
      (∀ nu z, z ∈ B nu ↔
        I + (m : ℤ) ≤ z.1+z.2 ∧
        z.1+z.2 ≤ I + (ell : ℤ) - (m : ℤ) ∧
        |(1-a)*(z.1 : ℝ)-a*(z.2 : ℝ) -
          ((1-a)*((c nu).1 : ℝ)-a*((c nu).2 : ℝ))| ≤ 8*w) ∧
      (∀ nu, ((B nu).card : ℝ) ≤ ((ell-2*m+1 : ℕ) : ℝ)*(16*w+1)) ∧
      (∀ nu, ((B nu).card : ℝ) ≤ 34*(ell : ℝ)*w) ∧
      (∀ nu, ((B nu).card : ℝ) ≤ 17*w^4) ∧
      (∀ nu mu, nu ≠ mu → Disjoint (B nu) (B mu)) := by
  classical
  let level0 : ℤ := I + (m : ℤ)
  let target : Fin N → ℝ := fun nu =>
    h*w + 30*((nu.val+1 : ℕ) : ℝ)*w
  let first : Fin N → ℤ := fun nu =>
    Int.floor (target nu + a*(level0 : ℝ) + (1/2 : ℝ))
  let center : Fin N → Lattice := fun nu => (first nu, level0-first nu)

  have hcenterLevel (nu : Fin N) :
      (center nu).1+(center nu).2 = I+(m:ℤ) := by
    simp only [center]
    omega
  have hcenterRho (nu : Fin N) :
      (1-a)*((center nu).1:ℝ)-a*((center nu).2:ℝ) =
        (first nu:ℝ)-a*(level0:ℝ) := by
    have hsum : ((center nu).1:ℝ)+((center nu).2:ℝ)=(level0:ℝ) := by
      exact_mod_cast hcenterLevel nu
    calc
      _ = (center nu).1 - a*(((center nu).1:ℝ)+((center nu).2:ℝ)) := by ring
      _ = (first nu:ℝ)-a*(level0:ℝ) := by rw [hsum]

  have hcenterRound (nu : Fin N) :
      |(1-a)*((center nu).1:ℝ)-a*((center nu).2:ℝ)-target nu| ≤ 1/2 := by
    let x0 : ℝ := target nu + a*(level0:ℝ)
    have hfloorLe : (first nu:ℝ) ≤ x0 + 1/2 := by
      dsimp only [first, x0]
      exact Int.floor_le _
    have hfloorLt : x0 + 1/2 < (first nu:ℝ)+1 := by
      dsimp only [first, x0]
      exact Int.lt_floor_add_one _
    have hup : (first nu:ℝ)-x0 ≤ 1/2 := by linarith
    have hlo : -(1/2:ℝ) ≤ (first nu:ℝ)-x0 := by linarith
    have hformula :
        (1-a)*((center nu).1:ℝ)-a*((center nu).2:ℝ)-target nu =
          (first nu:ℝ)-x0 := by
      rw [hcenterRho]
      dsimp only [x0]
      ring
    rw [hformula]
    exact abs_le.mpr ⟨hlo,hup⟩

  let tubeExists (nu : Fin N) :=
    exists_finset_signed_level_tube a (8*w)
      (fun _ => (1-a)*((center nu).1:ℝ)-a*((center nu).2:ℝ))
      level0 (ell-2*m) (by linarith [hw])
  let blocks : Fin N → Finset Lattice := fun nu => Classical.choose (tubeExists nu)
  have hblocksSpec (nu : Fin N) := Classical.choose_spec (tubeExists nu)

  have hupper : level0 + ((ell-2*m : ℕ) : ℤ) = I+(ell:ℤ)-(m:ℤ) := by
    dsimp only [level0]
    omega
  have hblocksMem (nu : Fin N) (z : Lattice) :
      z ∈ blocks nu ↔
        I+(m:ℤ) ≤ z.1+z.2 ∧
        z.1+z.2 ≤ I+(ell:ℤ)-(m:ℤ) ∧
        |(1-a)*(z.1:ℝ)-a*(z.2:ℝ) -
          ((1-a)*((center nu).1:ℝ)-a*((center nu).2:ℝ))| ≤ 8*w := by
    rw [(hblocksSpec nu).1 z]
    constructor
    · rintro ⟨hlo,hhi,htrans⟩
      refine ⟨?_,?_,htrans⟩
      · simpa only [level0] using hlo
      · rw [hupper] at hhi
        exact hhi
    · rintro ⟨hlo,hhi,htrans⟩
      refine ⟨?_,?_,htrans⟩
      · simpa only [level0] using hlo
      · rw [← hupper] at hhi
        exact hhi

  have hblockCard (nu : Fin N) :
      ((blocks nu).card : ℝ) ≤ ((ell-2*m+1 : ℕ) : ℝ)*(16*w+1) := by
    calc
      ((blocks nu).card : ℝ) ≤
          ((ell-2*m+1 : ℕ) : ℝ)*(2*(8*w)+1) := (hblocksSpec nu).2
      _ = ((ell-2*m+1 : ℕ) : ℝ)*(16*w+1) := by congr 1; ring

  have hlevelsBoundNat : ell-2*m+1 ≤ 2*ell := by omega
  have hlevelsBound :
      ((ell-2*m+1 : ℕ) : ℝ) ≤ 2*(ell:ℝ) := by exact_mod_cast hlevelsBoundNat
  have hsiteBound : 16*w+1 ≤ 17*w := by nlinarith [hw]
  have hcard34 (nu : Fin N) : ((blocks nu).card : ℝ) ≤ 34*(ell:ℝ)*w := by
    calc
      ((blocks nu).card : ℝ) ≤ ((ell-2*m+1 : ℕ) : ℝ)*(16*w+1) := hblockCard nu
      _ ≤ (2*(ell:ℝ))*(17*w) :=
        mul_le_mul hlevelsBound hsiteBound (by positivity) (by positivity)
      _ = 34*(ell:ℝ)*w := by ring
  have hcard17 (nu : Fin N) : ((blocks nu).card : ℝ) ≤ 17*w^4 := by
    calc
      ((blocks nu).card : ℝ) ≤ 34*(ell:ℝ)*w := hcard34 nu
      _ = (34*w)*(ell:ℝ) := by ring
      _ ≤ (34*w)*(w^3/2) :=
        mul_le_mul_of_nonneg_left hell (by positivity)
      _ = 17*w^4 := by ring

  have hindexGap (nu mu : Fin N) (hne : nu ≠ mu) :
      1 ≤ |(nu.val:ℝ)-(mu.val:ℝ)| := by
    have hval : nu.val ≠ mu.val := by
      intro hval
      exact hne (Fin.ext hval)
    by_cases hlt : nu.val < mu.val
    · have hnat : nu.val+1 ≤ mu.val := Nat.succ_le_of_lt hlt
      have hnatR : (nu.val:ℝ)+1 ≤ (mu.val:ℝ) := by exact_mod_cast hnat
      have hneg : (nu.val:ℝ)-(mu.val:ℝ) < 0 := by linarith
      rw [abs_of_neg hneg]
      linarith
    · have hgt : mu.val < nu.val := by omega
      have hnat : mu.val+1 ≤ nu.val := Nat.succ_le_of_lt hgt
      have hnatR : (mu.val:ℝ)+1 ≤ (nu.val:ℝ) := by exact_mod_cast hnat
      have hpos : 0 < (nu.val:ℝ)-(mu.val:ℝ) := by linarith
      rw [abs_of_pos hpos]
      linarith

  have htargetDiff (nu mu : Fin N) :
      target nu-target mu = 30*w*((nu.val:ℝ)-(mu.val:ℝ)) := by
    dsimp only [target]
    push_cast
    ring
  have htargetSeparated (nu mu : Fin N) (hne : nu ≠ mu) :
      30*w ≤ |target nu-target mu| := by
    have hmul := mul_le_mul_of_nonneg_left (hindexGap nu mu hne)
      (by positivity : 0 ≤ 30*w)
    rw [htargetDiff, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 30*w)]
    simpa only [mul_one] using hmul

  have hcenterSeparated (nu mu : Fin N) (hne : nu ≠ mu) :
      16*w < |((1-a)*((center nu).1:ℝ)-a*((center nu).2:ℝ))-
        ((1-a)*((center mu).1:ℝ)-a*((center mu).2:ℝ))| := by
    let rhoNu : ℝ := (1-a)*((center nu).1:ℝ)-a*((center nu).2:ℝ)
    let rhoMu : ℝ := (1-a)*((center mu).1:ℝ)-a*((center mu).2:ℝ)
    have htriangle : |target nu-target mu| ≤
        |target nu-rhoNu|+(|rhoNu-rhoMu|+|rhoMu-target mu|) := by
      calc
        |target nu-target mu| =
            |(target nu-rhoNu)+((rhoNu-rhoMu)+(rhoMu-target mu))| := by
          congr 1; ring
        _ ≤ |target nu-rhoNu|+|(rhoNu-rhoMu)+(rhoMu-target mu)| := abs_add_le _ _
        _ ≤ |target nu-rhoNu|+(|rhoNu-rhoMu|+|rhoMu-target mu|) :=
          add_le_add_right (abs_add_le _ _) _
    have hroundLeft : |target nu-rhoNu| ≤ 1/2 := by
      dsimp only [rhoNu]
      rw [abs_sub_comm]
      exact hcenterRound nu
    have hroundRight : |rhoMu-target mu| ≤ 1/2 := by
      dsimp only [rhoMu]
      exact hcenterRound mu
    have hstrict : 16*w < 30*w-1 := by nlinarith [hw]
    dsimp only [rhoNu, rhoMu] at *
    linarith [htargetSeparated nu mu hne, htriangle, hroundLeft, hroundRight, hstrict]

  have hdisjoint (nu mu : Fin N) (hne : nu ≠ mu) :
      Disjoint (blocks nu) (blocks mu) := by
    refine Finset.disjoint_left.mpr ?_
    intro z hzn hzm
    have hzn' := (hblocksMem nu z).mp hzn
    have hzm' := (hblocksMem mu z).mp hzm
    have hclose :
        |((1-a)*((center nu).1:ℝ)-a*((center nu).2:ℝ))-
          ((1-a)*((center mu).1:ℝ)-a*((center mu).2:ℝ))| ≤ 16*w := by
      have hleft :
          |((1-a)*((center nu).1:ℝ)-a*((center nu).2:ℝ))-
            ((1-a)*(z.1:ℝ)-a*(z.2:ℝ))| ≤ 8*w := by
        rw [abs_sub_comm]
        exact hzn'.2.2
      calc
        _ = |(((1-a)*((center nu).1:ℝ)-a*((center nu).2:ℝ))-
            ((1-a)*(z.1:ℝ)-a*(z.2:ℝ))) +
            (((1-a)*(z.1:ℝ)-a*(z.2:ℝ))-
              ((1-a)*((center mu).1:ℝ)-a*((center mu).2:ℝ)))| := by
          congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ 8*w+8*w := add_le_add hleft hzm'.2.2
        _ = 16*w := by ring
    exact (not_lt_of_ge hclose) (hcenterSeparated nu mu hne)

  refine ⟨center, blocks, ?_, ?_, hblocksMem, ?_, ?_, ?_, ?_⟩
  · intro nu
    simpa only [level0] using hcenterLevel nu
  · intro nu
    simpa only [target] using hcenterRound nu
  · intro nu
    exact hblockCard nu
  · intro nu
    exact hcard34 nu
  · intro nu
    exact hcard17 nu
  · intro nu mu hne
    exact hdisjoint nu mu hne

end LPPDifferentiability

end
