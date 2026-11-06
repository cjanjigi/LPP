/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.StageIndexSets
public import Differentiability.Model.Paths.StageGeometry
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Differentiability.Model.StageItinerarySteps
import Mathlib.Tactic

/-! The actual first-cut itinerary has a connected finite image. -/

public section

namespace LPPDifferentiability

/-- The actual path cuts produce the itinerary and its radius-two connected image,
while retaining every cut, remainder, geometry, and collected-slice fact. -/
theorem Path.exists_first_stage_index_image {d : ℕ × ℕ} (p : Path 0 d)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 1 ≤ m)
    (s : ℝ) (hs : 2 ≤ s) :
    let rho (t : Fin (d.1 + d.2 + 1)) : ℝ :=
      (1-a)*(p.vertex t).1-a*(p.vertex t).2
    let pi (t : Fin (d.1 + d.2 + 1)) : ℤ := ⌊(t.val : ℝ)/(m : ℝ)⌋
    let eta (t : Fin (d.1 + d.2 + 1)) : ℤ := ⌊rho t/s⌋
    ∃ N : ℕ, ∃ cuts : Fin (N + 2) → Fin (d.1 + d.2 + 1),
      (cuts 0 = 0 ∧ cuts (Fin.last (N + 1)) = Fin.last (d.1 + d.2) ∧
      Monotone cuts ∧ N ≤ d.1 + d.2 ∧
      (∀ i : Fin N,
        let k := cuts ⟨i.val, by omega⟩
        let l := cuts ⟨i.val + 1, by omega⟩
        k < l ∧ (2*m ≤ l.val-k.val ∨ s ≤ |rho l-rho k|) ∧
        ∀ t, k < t → t < l → t.val-k.val < 2*m ∧ |rho t-rho k| < s) ∧
      (∀ t, cuts ⟨N, by omega⟩ < t →
        t.val-(cuts ⟨N, by omega⟩).val < 2*m ∧
          |rho t-rho (cuts ⟨N, by omega⟩)| < s) ∧
      (∀ i : Fin (N + 1),
        (cuts i.succ).val-(cuts i.castSucc).val ≤ 2*m ∧
        ∀ t, cuts i.castSucc ≤ t → t ≤ cuts i.succ →
          |rho t-rho (cuts i.castSucc)| ≤ s+1) ∧
      (∀ i : Fin N,
        |rho (cuts ⟨i.val + 1, by omega⟩)-rho (cuts ⟨i.val, by omega⟩)| < s →
          (cuts ⟨i.val + 1, by omega⟩).val-(cuts ⟨i.val, by omega⟩).val = 2*m) ∧
      (⋃ i : Fin (N + 1),
        p.vertex '' {t | cuts i.castSucc ≤ t ∧ t < cuts i.succ}) =
          (↑p.collectedSites : Set Lattice) ∧
      (∀ i j : Fin (N + 1), i ≠ j → Disjoint
        (p.vertex '' {t | cuts i.castSucc ≤ t ∧ t < cuts i.succ})
        (p.vertex '' {t | cuts j.castSucc ≤ t ∧ t < cuts j.succ})) ∧
      (∀ i : Fin (N + 1), ∀ t, cuts i.castSucc ≤ t → t ≤ cuts i.succ →
        (pi (cuts i.castSucc) : ℝ)*(m : ℝ) ≤ (p.vertex t).1+(p.vertex t).2 ∧
        (p.vertex t).1+(p.vertex t).2 ≤ (pi (cuts i.castSucc) : ℝ)*(m : ℝ)+3*(m : ℝ) ∧
        |rho t-(eta (cuts i.castSucc) : ℝ)*s| ≤ 4*s) ∧
      (∀ i : Fin N,
        (pi (cuts ⟨i.val + 1, by omega⟩)-pi (cuts ⟨i.val, by omega⟩) = 0 ∨
          pi (cuts ⟨i.val + 1, by omega⟩)-pi (cuts ⟨i.val, by omega⟩) = 1 ∨
          pi (cuts ⟨i.val + 1, by omega⟩)-pi (cuts ⟨i.val, by omega⟩) = 2) ∧
        |eta (cuts ⟨i.val + 1, by omega⟩)-eta (cuts ⟨i.val, by omega⟩)| ≤ 2) ∧
      pi (cuts 0) = 0 ∧ eta (cuts 0) = 0) ∧
      (let c (i : Fin (N + 1)) : Lattice :=
        (pi (cuts i.castSucc), eta (cuts i.castSucc))
       let A := Finset.univ.image c
       A.card ≤ N + 1 ∧
       (0 : Lattice) ∈ A ∧
       ((SimpleGraph.fromRel (fun x y : Lattice =>
         |x.1-y.1| ≤ 2 ∧ |x.2-y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected) := by
  intro _ pi eta
  obtain ⟨N, cuts, hProducer⟩ :=
    p.exists_first_cuts_blocks_indices a ha ha1 m hm s hs
  have hProducerKeep := hProducer
  rcases hProducer with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hindices, hpi0, heta0⟩
  have hpi0' : pi (cuts 0) = 0 := hpi0
  have heta0' : eta (cuts 0) = 0 := heta0
  let c (i : Fin (N + 1)) : Lattice :=
    (pi (cuts i.castSucc), eta (cuts i.castSucc))
  have hc0 : c 0 = 0 := by
    have hcast : (0 : Fin (N + 1)).castSucc = (0 : Fin (N + 2)) := Fin.ext rfl
    refine Prod.ext ?_ ?_
    · change pi (cuts ((0 : Fin (N + 1)).castSucc)) = 0
      rw [hcast]
      exact hpi0'
    · change eta (cuts ((0 : Fin (N + 1)).castSucc)) = 0
      rw [hcast]
      exact heta0'
  have hstep : ∀ i : Fin N,
      |(c i.succ).1 - (c i.castSucc).1| ≤ 2 ∧
      |(c i.succ).2 - (c i.castSucc).2| ≤ 2 := by
    intro i
    obtain ⟨hpi, heta⟩ : (pi (cuts i.succ.castSucc) - pi (cuts i.castSucc.castSucc) = 0 ∨
          pi (cuts i.succ.castSucc) - pi (cuts i.castSucc.castSucc) = 1 ∨
          pi (cuts i.succ.castSucc) - pi (cuts i.castSucc.castSucc) = 2) ∧
        |eta (cuts i.succ.castSucc) - eta (cuts i.castSucc.castSucc)| ≤ 2 := hindices i
    constructor
    · change |pi (cuts i.succ.castSucc) - pi (cuts i.castSucc.castSucc)| ≤ 2
      exact abs_le.mpr ⟨by omega, by omega⟩
    · exact heta
  have himage := stage_index_image_connected c hc0 hstep
  exact ⟨N, cuts, hProducerKeep, himage⟩

end LPPDifferentiability
