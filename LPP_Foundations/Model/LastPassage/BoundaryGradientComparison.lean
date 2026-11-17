/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.LastPassage
import LPP_Foundations.Model.LastPassage.Locality
import LPP_Foundations.Model.LastPassage.GradientOrder

/-! Finite horizontal and vertical passage-difference comparisons at a boundary. -/

@[expose] public section

open LPPDifferentiability

namespace LPP

/-- The horizontal passage difference at the old endpoint lies between the
two boundary-modified differences. This is the finite comparison in
GRS1510.00859v2, Theorem 6.1, Step 1, using Lemma 6.3 and the proof of (6.6). -/
theorem horizontal_passage_difference_boundary_comparison
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (x : Lattice) (a b : ℕ) :
    let v : Lattice := x + (((a + 1 : ℕ) : ℤ), (b : ℤ))
    let N : Environment := fun z =>
      if z.2 = v.2 + 1 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
    let E : Environment := fun z =>
      if z.1 = v.1 + 1 ∧ z.2 < v.2 then C z (z + (0, 1)) else ω z
    (lastPassage E x (a + 2, b) -
        lastPassage E (x + (1, 0)) (a + 1, b) ≤
      lastPassage ω x (a + 1, b) - lastPassage ω (x + (1, 0)) (a, b)) ∧
    (lastPassage ω x (a + 1, b) - lastPassage ω (x + (1, 0)) (a, b) ≤
      lastPassage N x (a + 1, b + 1) -
        lastPassage N (x + (1, 0)) (a, b + 1)) := by
  let v : Lattice := x + (((a + 1 : ℕ) : ℤ), (b : ℤ))
  let N : Environment := fun z =>
    if z.2 = v.2 + 1 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
  let E : Environment := fun z =>
    if z.1 = v.1 + 1 ∧ z.2 < v.2 then C z (z + (0, 1)) else ω z
  change
    (lastPassage E x (a + 2, b) -
        lastPassage E (x + (1, 0)) (a + 1, b) ≤
      lastPassage ω x (a + 1, b) - lastPassage ω (x + (1, 0)) (a, b)) ∧
    (lastPassage ω x (a + 1, b) - lastPassage ω (x + (1, 0)) (a, b) ≤
      lastPassage N x (a + 1, b + 1) -
        lastPassage N (x + (1, 0)) (a, b + 1))
  -- Old rectangles stay below the changed row and column.
  have hNlocal (u : Lattice) (d : ℕ × ℕ)
      (hterminal : (u + ((d.1 : ℤ), (d.2 : ℤ))).2 ≤ v.2) :
      lastPassage N u d = lastPassage ω u d := by
    apply lastPassage_eq_of_eqOn
    intro z hz
    change
      (if z.2 = v.2 + 1 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z) = ω z
    split_ifs with hchange
    · have hzupper : z.2 ≤ (u + ((d.1 : ℤ), (d.2 : ℤ))).2 := hz.2.2
      have hend := hterminal
      simp only [Prod.snd_add] at hzupper hend
      omega
    · rfl
  have hElocal (u : Lattice) (d : ℕ × ℕ)
      (hterminal : (u + ((d.1 : ℤ), (d.2 : ℤ))).1 ≤ v.1) :
      lastPassage E u d = lastPassage ω u d := by
    apply lastPassage_eq_of_eqOn
    intro z hz
    change
      (if z.1 = v.1 + 1 ∧ z.2 < v.2 then C z (z + (0, 1)) else ω z) = ω z
    split_ifs with hchange
    · have hzupper : z.1 ≤ (u + ((d.1 : ℤ), (d.2 : ℤ))).1 := hz.2.1
      have hend := hterminal
      simp only [Prod.fst_add] at hzupper hend
      omega
    · rfl
  have hEndpoint : x + (((a + 1 : ℕ) : ℤ), (b : ℤ)) = v := rfl
  have hChildEndpoint : x + (1, 0) + ((a : ℤ), (b : ℤ)) = v := by
    apply Prod.ext
    · change x.1 + 1 + (a : ℤ) = x.1 + (((a + 1 : ℕ) : ℤ))
      omega
    · change x.2 + 0 + (b : ℤ) = x.2 + (b : ℤ)
      omega
  have hEfirst : lastPassage E x (a + 1, b) = lastPassage ω x (a + 1, b) := by
    apply hElocal
    change (x + (((a + 1 : ℕ) : ℤ), (b : ℤ))).1 ≤ v.1
    rw [hEndpoint]
  have hEchild : lastPassage E (x + (1, 0)) (a, b) =
      lastPassage ω (x + (1, 0)) (a, b) := by
    apply hElocal
    change (x + (1, 0) + ((a : ℤ), (b : ℤ))).1 ≤ v.1
    rw [hChildEndpoint]
  have hNfirst : lastPassage N x (a + 1, b) = lastPassage ω x (a + 1, b) := by
    apply hNlocal
    change (x + (((a + 1 : ℕ) : ℤ), (b : ℤ))).2 ≤ v.2
    rw [hEndpoint]
  have hNchild : lastPassage N (x + (1, 0)) (a, b) =
      lastPassage ω (x + (1, 0)) (a, b) := by
    apply hNlocal
    change (x + (1, 0) + ((a : ℤ), (b : ℤ))).2 ≤ v.2
    rw [hChildEndpoint]
  constructor
  · -- Use east decrease for E, then identify its old-endpoint gradient.
    have horder := (LPP.local_gradient_order E a b x).1.1
    change
      lastPassage E x (a + 2, b) -
          lastPassage E (x + (1, 0)) (a + 1, b) ≤
        lastPassage E x (a + 1, b) - lastPassage E (x + (1, 0)) (a, b)
      at horder
    rw [hEfirst, hEchild] at horder
    exact horder
  · -- Use north increase for N, with the same old-endpoint identification.
    have horder := (LPP.local_gradient_order N a b x).1.2
    change
      lastPassage N x (a + 1, b) - lastPassage N (x + (1, 0)) (a, b) ≤
        lastPassage N x (a + 1, b + 1) -
          lastPassage N (x + (1, 0)) (a, b + 1)
      at horder
    rw [hNfirst, hNchild] at horder
    exact horder

/-- The vertical passage difference at the old endpoint lies between the
two boundary-modified differences. This is the finite comparison in
GRS1510.00859v2, Theorem 6.1, Step 1, using Lemma 6.3 and the proof of (6.6). -/
theorem vertical_passage_difference_boundary_comparison
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (x : Lattice) (a b : ℕ) :
    let v : Lattice := x + ((a : ℤ), ((b + 1 : ℕ) : ℤ))
    let N : Environment := fun z =>
      if z.2 = v.2 + 1 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
    let E : Environment := fun z =>
      if z.1 = v.1 + 1 ∧ z.2 < v.2 then C z (z + (0, 1)) else ω z
    (lastPassage N x (a, b + 2) -
        lastPassage N (x + (0, 1)) (a, b + 1) ≤
      lastPassage ω x (a, b + 1) - lastPassage ω (x + (0, 1)) (a, b)) ∧
    (lastPassage ω x (a, b + 1) - lastPassage ω (x + (0, 1)) (a, b) ≤
      lastPassage E x (a + 1, b + 1) -
        lastPassage E (x + (0, 1)) (a + 1, b)) := by
  let v : Lattice := x + ((a : ℤ), ((b + 1 : ℕ) : ℤ))
  let N : Environment := fun z =>
    if z.2 = v.2 + 1 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
  let E : Environment := fun z =>
    if z.1 = v.1 + 1 ∧ z.2 < v.2 then C z (z + (0, 1)) else ω z
  change
    (lastPassage N x (a, b + 2) -
        lastPassage N (x + (0, 1)) (a, b + 1) ≤
      lastPassage ω x (a, b + 1) - lastPassage ω (x + (0, 1)) (a, b)) ∧
    (lastPassage ω x (a, b + 1) - lastPassage ω (x + (0, 1)) (a, b) ≤
      lastPassage E x (a + 1, b + 1) -
        lastPassage E (x + (0, 1)) (a + 1, b))
  -- Old rectangles stay below the changed row and column.
  have hNlocal (u : Lattice) (d : ℕ × ℕ)
      (hterminal : (u + ((d.1 : ℤ), (d.2 : ℤ))).2 ≤ v.2) :
      lastPassage N u d = lastPassage ω u d := by
    apply lastPassage_eq_of_eqOn
    intro z hz
    change
      (if z.2 = v.2 + 1 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z) = ω z
    split_ifs with hchange
    · have hzupper : z.2 ≤ (u + ((d.1 : ℤ), (d.2 : ℤ))).2 := hz.2.2
      have hend := hterminal
      simp only [Prod.snd_add] at hzupper hend
      omega
    · rfl
  have hElocal (u : Lattice) (d : ℕ × ℕ)
      (hterminal : (u + ((d.1 : ℤ), (d.2 : ℤ))).1 ≤ v.1) :
      lastPassage E u d = lastPassage ω u d := by
    apply lastPassage_eq_of_eqOn
    intro z hz
    change
      (if z.1 = v.1 + 1 ∧ z.2 < v.2 then C z (z + (0, 1)) else ω z) = ω z
    split_ifs with hchange
    · have hzupper : z.1 ≤ (u + ((d.1 : ℤ), (d.2 : ℤ))).1 := hz.2.1
      have hend := hterminal
      simp only [Prod.fst_add] at hzupper hend
      omega
    · rfl
  have hEndpoint : x + ((a : ℤ), ((b + 1 : ℕ) : ℤ)) = v := rfl
  have hChildEndpoint : x + (0, 1) + ((a : ℤ), (b : ℤ)) = v := by
    apply Prod.ext
    · change x.1 + 0 + (a : ℤ) = x.1 + (a : ℤ)
      omega
    · change x.2 + 1 + (b : ℤ) = x.2 + (((b + 1 : ℕ) : ℤ))
      omega
  have hNfirst : lastPassage N x (a, b + 1) = lastPassage ω x (a, b + 1) := by
    apply hNlocal
    change (x + ((a : ℤ), ((b + 1 : ℕ) : ℤ))).2 ≤ v.2
    rw [hEndpoint]
  have hNchild : lastPassage N (x + (0, 1)) (a, b) =
      lastPassage ω (x + (0, 1)) (a, b) := by
    apply hNlocal
    change (x + (0, 1) + ((a : ℤ), (b : ℤ))).2 ≤ v.2
    rw [hChildEndpoint]
  have hEfirst : lastPassage E x (a, b + 1) = lastPassage ω x (a, b + 1) := by
    apply hElocal
    change (x + ((a : ℤ), ((b + 1 : ℕ) : ℤ))).1 ≤ v.1
    rw [hEndpoint]
  have hEchild : lastPassage E (x + (0, 1)) (a, b) =
      lastPassage ω (x + (0, 1)) (a, b) := by
    apply hElocal
    change (x + (0, 1) + ((a : ℤ), (b : ℤ))).1 ≤ v.1
    rw [hChildEndpoint]
  constructor
  · -- Use vertical decrease for N, then identify its old-endpoint gradient.
    have horder := (LPP.local_gradient_order N a b x).2.1
    change
      lastPassage N x (a, b + 2) -
          lastPassage N (x + (0, 1)) (a, b + 1) ≤
        lastPassage N x (a, b + 1) - lastPassage N (x + (0, 1)) (a, b)
      at horder
    rw [hNfirst, hNchild] at horder
    exact horder
  · -- Use horizontal increase for E, with the same old-endpoint identification.
    have horder := (LPP.local_gradient_order E a b x).2.2
    change
      lastPassage E x (a, b + 1) - lastPassage E (x + (0, 1)) (a, b) ≤
        lastPassage E x (a + 1, b + 1) -
          lastPassage E (x + (0, 1)) (a + 1, b)
      at horder
    rw [hEfirst, hEchild] at horder
    exact horder

end LPP
