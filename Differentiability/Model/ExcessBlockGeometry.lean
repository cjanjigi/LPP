/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.FiniteLevelStripCardinality
import Mathlib.Tactic

/-! Literal closed excess boxes and the source's floor-rounded signed centers. -/
public section
namespace LPPDifferentiability

/-- The source center uses the half-open interval `(hs-1,hs]`. -/
theorem excess_block_center (a s : ℝ) (m : ℕ) (p h : ℤ) :
    let j : ℤ := ⌊(h : ℝ)*s+a*((p*m : ℤ) : ℝ)⌋
    let v : Lattice := (j,p*m-j)
    v.1+v.2=p*m ∧
      (h : ℝ)*s-1 < (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ∧
      (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ≤ (h : ℝ)*s := by
  dsimp only
  have hlo := Int.sub_one_lt_floor ((h:ℝ)*s+a*((p*m:ℤ):ℝ))
  have hhi := Int.floor_le ((h:ℝ)*s+a*((p*m:ℤ):ℝ))
  push_cast
  push_cast at hlo hhi
  refine ⟨by omega, ?_, ?_⟩ <;> nlinarith only [hlo,hhi]

/-- The exact closed source strip exists with its two original cardinal bounds. -/
theorem exists_excess_block_base (a s : ℝ) (m : ℕ)
    (hs : 3 ≤ s) (hm : (m:ℝ) ≤ s^3) :
    ∃ Q : Finset Lattice,
      (∀ z, z ∈ Q ↔ 0 ≤ z.1+z.2 ∧ z.1+z.2 ≤ 3*(m:ℤ) ∧
        |(1-a)*(z.1:ℝ)-a*(z.2:ℝ)| ≤ 4*s+1) ∧
      (Q.card:ℝ) ≤ (3*(m:ℝ)+1)*(8*s+3) ∧
      (3*(m:ℝ)+1)*(8*s+3) ≤ 44*s^4 := by
  obtain ⟨Q,hQ,hcard⟩ := exists_finset_signed_level_tube a (4*s+1)
    (fun _ => 0) 0 (3*m) (by linarith only [hs])
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro z
    simpa only [zero_add, Nat.cast_mul, Nat.cast_ofNat, sub_zero] using hQ z
  · convert hcard using 1; push_cast; ring
  · have hs0 : 0 ≤ s := by linarith only [hs]
    have hs3 : 1 ≤ s^3 := one_le_pow₀ (by linarith only [hs])
    have h1 : 3*(m:ℝ)+1 ≤ 4*s^3 := by linarith only [hm,hs3]
    have h2 : 8*s+3 ≤ 11*s := by linarith only [hs]
    calc
      (3*(m:ℝ)+1)*(8*s+3) ≤ (4*s^3)*(11*s) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 44*s^4 := by ring

/-- Exact membership after translation, using a literal injective `Finset.map`. -/
theorem mem_translated_excess_block (a s : ℝ) (m : ℕ) (Q : Finset Lattice)
    (hQ : ∀ z, z ∈ Q ↔ 0 ≤ z.1+z.2 ∧ z.1+z.2 ≤ 3*(m:ℤ) ∧
      |(1-a)*(z.1:ℝ)-a*(z.2:ℝ)| ≤ 4*s+1)
    (v z : Lattice) :
    z ∈ Q.map ⟨fun w => v+w, fun _ _ h => add_left_cancel h⟩ ↔
      v.1+v.2 ≤ z.1+z.2 ∧ z.1+z.2 ≤ v.1+v.2+3*(m:ℤ) ∧
      |((1-a)*(z.1:ℝ)-a*(z.2:ℝ))-
        ((1-a)*(v.1:ℝ)-a*(v.2:ℝ))| ≤ 4*s+1 := by
  classical
  have hmem : z ∈ Q.map ⟨fun w => v+w, fun _ _ h => add_left_cancel h⟩ ↔ z-v ∈ Q := by
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨w,hw,heq⟩
      change v+w=z at heq
      rw [← heq]
      simpa only [add_sub_cancel_left] using hw
    · intro hz
      exact ⟨z-v,hz,add_sub_cancel _ _⟩
  rw [hmem,hQ]
  simp only [Prod.fst_sub,Prod.snd_sub,Int.cast_sub]
  have he : (1-a)*((z.1:ℝ)-(v.1:ℝ))-a*((z.2:ℝ)-(v.2:ℝ)) =
      ((1-a)*(z.1:ℝ)-a*(z.2:ℝ))-((1-a)*(v.1:ℝ)-a*(v.2:ℝ)) := by ring
  rw [he]
  constructor
  · rintro ⟨hlo,hhi,hr⟩
    exact ⟨by omega, by omega, hr⟩
  · rintro ⟨hlo,hhi,hr⟩
    exact ⟨by omega, by omega, hr⟩

/-- The original closed block is inside the actual translated excess box. -/
theorem source_block_subset_excess_block (a s : ℝ) (m : ℕ) (Q : Finset Lattice)
    (hQ : ∀ z, z ∈ Q ↔ 0 ≤ z.1+z.2 ∧ z.1+z.2 ≤ 3*(m:ℤ) ∧
      |(1-a)*(z.1:ℝ)-a*(z.2:ℝ)| ≤ 4*s+1) (p h : ℤ) :
    let j : ℤ := ⌊(h:ℝ)*s+a*((p*m:ℤ):ℝ)⌋
    let v : Lattice := (j,p*m-j)
    ∀ z : Lattice, (p*m ≤ z.1+z.2 ∧ z.1+z.2 ≤ p*m+3*(m:ℤ) ∧
      |(1-a)*(z.1:ℝ)-a*(z.2:ℝ)-(h:ℝ)*s| ≤ 4*s) →
      z ∈ Q.map ⟨fun w => v+w, fun _ _ h => add_left_cancel h⟩ := by
  dsimp only
  intro z hz
  rw [mem_translated_excess_block a s m Q hQ]
  obtain ⟨hv,hlo,hhi⟩ := excess_block_center a s m p h
  refine ⟨by simpa only [hv] using hz.1, by simpa only [hv] using hz.2.1, ?_⟩
  rcases abs_le.mp hz.2.2 with ⟨hzlo,hzhi⟩
  apply abs_le.mpr
  constructor <;> linarith only [hzlo,hzhi,hlo,hhi]

end LPPDifferentiability
end
