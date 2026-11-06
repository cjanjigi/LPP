/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.LevelNetCoverage
public import Differentiability.Model.Paths.ReachableLevel
import LPP_Foundations.Model.Paths.HorizontalFirst
import Mathlib.Tactic

/-! # Central forward attachments from one level net -/

public section

namespace LPPDifferentiability

/-- One level net has a central reachable point and an actual path from
every signed endpoint in the original interval. The net is common to all
endpoints, while the point and path witnesses may depend on the endpoint. -/
theorem exists_forward_middle_net_attachments
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (m : ℕ)
    (hm : 1 ≤ min a (1 - a) * (m : ℝ) / 4)
    (I : ℤ) (lo hi : ℝ) (hlohi : lo ≤ hi) :
    ∃ (M : ℕ) (v : Fin (M + 1) → Lattice),
      1 ≤ M ∧ Function.Injective v ∧
      (∀ j, (v j).1 + (v j).2 = I + (m : ℤ) ∧
        ((1 - a) * ((v j).1 : ℝ) - a * ((v j).2 : ℝ)) ∈
          Set.Icc (lo - a * (m : ℝ)) (hi + (1 - a) * (m : ℝ))) ∧
      (∀ (j : ℕ) (hj : j < M),
        min a (1 - a) * (m : ℝ) / 4 ≤
          (((1 - a) * ((v ⟨j + 1, by omega⟩).1 : ℝ) -
              a * ((v ⟨j + 1, by omega⟩).2 : ℝ)) -
            ((1 - a) * ((v ⟨j, by omega⟩).1 : ℝ) -
              a * ((v ⟨j, by omega⟩).2 : ℝ))) ∧
        (((1 - a) * ((v ⟨j + 1, by omega⟩).1 : ℝ) -
            a * ((v ⟨j + 1, by omega⟩).2 : ℝ)) -
          ((1 - a) * ((v ⟨j, by omega⟩).1 : ℝ) -
            a * ((v ⟨j, by omega⟩).2 : ℝ))) ≤ min a (1 - a) * (m : ℝ) / 2) ∧
      (∀ j, ((1 - a) * ((v j).1 : ℝ) - a * ((v j).2 : ℝ) ≤
        lo - a * (m : ℝ) + min a (1 - a) * (m : ℝ) / 2) ↔ j.val = 0) ∧
      (∀ j, (hi + (1 - a) * (m : ℝ) - min a (1 - a) * (m : ℝ) / 2 ≤
        (1 - a) * ((v j).1 : ℝ) - a * ((v j).2 : ℝ)) ↔ j.val = M) ∧
      (1 - a) * ((v ⟨0, by omega⟩).1 : ℝ) -
        a * ((v ⟨0, by omega⟩).2 : ℝ) ≤
          lo - a * (m : ℝ) + min a (1 - a) * (m : ℝ) / 2 ∧
      hi + (1 - a) * (m : ℝ) - min a (1 - a) * (m : ℝ) / 2 ≤
        (1 - a) * ((v ⟨M, by omega⟩).1 : ℝ) -
          a * ((v ⟨M, by omega⟩).2 : ℝ) ∧
      (M + 1 : ℝ) <
        4 * (hi - lo + (m : ℝ)) / (min a (1 - a) * (m : ℝ)) ∧
      (∀ u : Lattice, u.1 + u.2 = I →
        ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)) ∈ Set.Icc lo hi →
        ∃ (j : Fin (M + 1)) (k : Fin (m + 1))
          (p : Path u (k.val, m - k.val)),
          k.val + (m - k.val) = m ∧
          p.vertex (Fin.last (k.val + (m - k.val))) = v j ∧
          ((k.val : ℝ) / (m : ℝ)) ∈ Set.Icc (1 / 4) (3 / 4) ∧
          |(1 - a) * (((v j - u).1 : ℤ) : ℝ) -
            a * (((v j - u).2 : ℤ) : ℝ)| ≤ (m : ℝ)) := by
  let A : ℝ := lo - a * (m : ℝ)
  let B : ℝ := hi + (1 - a) * (m : ℝ)
  have hBA : B - A = hi - lo + (m : ℝ) := by
    dsimp [A, B]
    ring
  have hwidth : (m : ℝ) ≤ B - A := by
    rw [hBA]
    linarith [sub_nonneg.mpr hlohi]
  obtain ⟨M, v, hM, hinj, hnet, hgap, hstart, hend, hfirst, hlast,
      hcard, _hcoverage⟩ :=
    exists_level_net a ha ha1 m hm (I + (m : ℤ)) A B hwidth
  let x : Fin (M + 1) → ℝ := fun j =>
    (1 - a) * ((v j).1 : ℝ) - a * ((v j).2 : ℝ)
  refine ⟨M, v, hM, hinj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨hlevel, hleft, hright⟩ := hnet j
    refine ⟨hlevel, ?_⟩
    simpa only [Set.mem_Icc, A, B] using And.intro hleft hright
  · intro j hj
    simpa only [x] using hgap j hj
  · simpa only [x, A] using hstart
  · simpa only [x, B] using hend
  · simpa only [x, A] using hfirst
  · simpa only [x, B] using hlast
  · rw [hBA] at hcard
    exact hcard
  · intro u hu hinterval
    let rhoU : ℝ := (1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)
    let L : ℝ := rhoU - a * (m : ℝ) + (m : ℝ) / 4
    let U : ℝ := rhoU - a * (m : ℝ) + 3 * (m : ℝ) / 4
    let g : ℝ := min a (1 - a) * (m : ℝ) / 2
    have htheta : min a (1 - a) ≤ (1 / 2 : ℝ) := by
      have h₁ := min_le_left a (1 - a)
      have h₂ := min_le_right a (1 - a)
      linarith
    have hthetaPos : 0 < min a (1 - a) := lt_min ha (by linarith [ha1])
    have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hgapBound : g ≤ (m : ℝ) / 4 := by
      dsimp [g]
      nlinarith
    have hgapBound' : min a (1 - a) * (m : ℝ) / 2 ≤ (m : ℝ) / 4 := by
      simpa only [g] using hgapBound
    have hg : 0 ≤ g := by
      dsimp [g]
      exact div_nonneg (mul_nonneg (le_of_lt hthetaPos) hmnonneg) (by norm_num)
    have hlen : L + g ≤ U := by
      dsimp [L, U]
      nlinarith [hgapBound]
    have hfirstMiddle : A + g ≤ L := by
      dsimp [A, L, g, rhoU]
      linarith [hinterval.1, hgapBound']
    have hlastMiddle : U ≤ B - g := by
      dsimp [B, U, g, rhoU]
      linarith [hinterval.2, hgapBound']
    have hfirstGrid : x ⟨0, by omega⟩ ≤ L := by
      have hsource : x ⟨0, by omega⟩ ≤ A + g := by
        simpa only [x, A, g] using hfirst
      exact hsource.trans hfirstMiddle
    have hlastGrid : U ≤ x ⟨M, by omega⟩ := by
      have hsource : B - g ≤ x ⟨M, by omega⟩ := by
        simpa only [x, B, g] using hlast
      exact hlastMiddle.trans hsource
    have hgapGrid : ∀ (j : ℕ) (hj : j < M),
        x ⟨j + 1, by omega⟩ - x ⟨j, by omega⟩ ≤ g := by
      intro j hj
      simpa only [x, g] using (hgap j hj).2
    obtain ⟨j, hjlo, hjhi⟩ :=
      finite_grid_interval_coverage M x L U g hg hlen hfirstGrid hlastGrid hgapGrid
    have hcoord :
        ((1 - a) * ((v j).1 : ℝ) - a * ((v j).2 : ℝ)) ∈
          Set.Icc (rhoU - a * (m : ℝ) + (m : ℝ) / 4)
            (rhoU - a * (m : ℝ) + 3 * (m : ℝ) / 4) := by
      rw [Set.mem_Icc]
      constructor
      · simpa only [L, x] using hjlo
      · simpa only [U, x] using hjhi
    have hlevel : (v j).1 + (v j).2 = u.1 + u.2 + (m : ℤ) := by
      calc
        (v j).1 + (v j).2 = I + (m : ℤ) := (hnet j).1
        _ = u.1 + u.2 + (m : ℤ) := by rw [← hu]
    have hfull :
        ((1 - a) * ((v j).1 : ℝ) - a * ((v j).2 : ℝ)) ∈
          Set.Icc (rhoU - a * (m : ℝ))
            (rhoU + (1 - a) * (m : ℝ)) := by
      rcases hcoord with ⟨hlo, hhi⟩
      constructor
      · dsimp [rhoU] at hlo
        dsimp [rhoU]
        linarith only [hlo, hmnonneg]
      · dsimp [rhoU] at hhi
        dsimp [rhoU]
        linarith only [hhi, hmnonneg]
    have hreachable :=
      (forwardLevelInterval_iff u (v j) m a).2 ⟨hlevel, hfull⟩
    have hmem := (forwardReachable_mem_iff u (v j) m).2 hreachable
    rcases Finset.mem_image.mp hmem with ⟨k, -, hpoint⟩
    have htrans :
        (1 - a) * ((v j).1 : ℝ) - a * ((v j).2 : ℝ) =
          rhoU - a * (m : ℝ) + (k.val : ℝ) := by
      rw [← hpoint]
      simpa only [rhoU] using forwardReachable_transverse u m k a
    rcases hcoord with ⟨hlo, hhi⟩
    rw [htrans] at hlo hhi
    have hklo : (m : ℝ) / 4 ≤ (k.val : ℝ) := by
      linarith only [hlo]
    have hkhi : (k.val : ℝ) ≤ 3 * (m : ℝ) / 4 := by
      linarith only [hhi]
    have hthetaPos : 0 < min a (1 - a) := lt_min ha (by linarith [ha1])
    have hmpos : 0 < (m : ℝ) := by
      nlinarith [hm, hthetaPos, hmnonneg]
    have hcentral : ((k.val : ℝ) / (m : ℝ)) ∈ Set.Icc (1 / 4) (3 / 4) := by
      rw [Set.mem_Icc]
      constructor
      · apply (le_div_iff₀ hmpos).2
        nlinarith [hklo]
      · apply (div_le_iff₀ hmpos).2
        nlinarith [hkhi]
    have hlength : k.val + (m - k.val) = m := by omega
    have hfinish :
        (horizontalFirst u (k.val, m - k.val)).vertex
            (Fin.last (k.val + (m - k.val))) = v j := by
      calc
        (horizontalFirst u (k.val, m - k.val)).vertex
            (Fin.last (k.val + (m - k.val))) =
              u + ((k.val : ℤ), ((m - k.val : ℕ) : ℤ)) :=
                (horizontalFirst u (k.val, m - k.val)).finish
        _ = v j := hpoint
    have hsub :
        (1 - a) * (((v j - u).1 : ℤ) : ℝ) -
            a * (((v j - u).2 : ℤ) : ℝ) =
          ((1 - a) * ((v j).1 : ℝ) - a * ((v j).2 : ℝ)) - rhoU := by
      simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
      dsimp [rhoU]
      ring
    have hdiff :
        ((1 - a) * ((v j).1 : ℝ) - a * ((v j).2 : ℝ)) - rhoU =
          (k.val : ℝ) - a * (m : ℝ) := by
      rw [htrans]
      dsimp [rhoU]
      ring
    have hbound : -(m : ℝ) ≤ (k.val : ℝ) - a * (m : ℝ) ∧
        (k.val : ℝ) - a * (m : ℝ) ≤ (m : ℝ) := by
      have ham : a * (m : ℝ) ≤ (m : ℝ) := by
        have h := mul_le_mul_of_nonneg_right (le_of_lt ha1) hmnonneg
        simpa only [one_mul] using h
      have hkm : (k.val : ℝ) ≤ (m : ℝ) := by
        nlinarith only [hkhi, hmnonneg]
      have hamnonneg : 0 ≤ a * (m : ℝ) :=
        mul_nonneg (le_of_lt ha) hmnonneg
      constructor
      · linarith only [hklo, hmnonneg, ham]
      · linarith only [hkm, hamnonneg]
    refine ⟨j, k, horizontalFirst u (k.val, m - k.val), hlength, hfinish,
      hcentral, ?_⟩
    calc
      |(1 - a) * (((v j - u).1 : ℤ) : ℝ) -
          a * (((v j - u).2 : ℤ) : ℝ)| =
        |((1 - a) * ((v j).1 : ℝ) - a * ((v j).2 : ℝ)) - rhoU| :=
          congrArg abs hsub
      _ = |(k.val : ℝ) - a * (m : ℝ)| := congrArg abs hdiff
      _ ≤ (m : ℝ) := abs_le.mpr hbound

end LPPDifferentiability
