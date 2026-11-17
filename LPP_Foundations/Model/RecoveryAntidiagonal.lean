/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Basic
import LPP_Foundations.Model.LocalDefectPath
import LPP_Foundations.Model.LastPassage.Outgoing
import Mathlib.Tactic

/-! Finite antidiagonal recovery for an additive edge potential. -/

public section

open LPPDifferentiability

namespace LPP

/-- Recovery makes an additive potential an upper bound attained on every finite
antidiagonal, including the zero-length case. This is the finite step in the proof of
JR arXiv:1810.03580v3, Lemma 4.5a, lines 814–829. -/
theorem lastPassage_antidiagonal_comparison_and_attainment
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : ∀ x y z, C x y + C y z = C x z)
    (hrec : ∀ x,
      min (C x (x + (1, 0))) (C x (x + (0, 1))) = ω x) :
    ∀ u : Lattice, ∀ n : ℕ,
      (∀ d : ℕ × ℕ, d.1 + d.2 = n →
        lastPassage ω u d ≤ C u (u + ((d.1 : ℤ), (d.2 : ℤ)))) ∧
      (∃ d : ℕ × ℕ, d.1 + d.2 = n ∧
        lastPassage ω u d = C u (u + ((d.1 : ℤ), (d.2 : ℤ)))) := by
  -- Additivity forces each zero-length potential increment to vanish.
  have hCdiag (x : Lattice) : C x x = 0 := by
    have h := hC x x x
    linarith
  -- Recovery makes both local edge errors nonpositive.
  have hright : ∀ x, ω x - C x (x + (1, 0)) ≤ 0 := by
    intro x
    have hle : ω x ≤ C x (x + (1, 0)) := by
      calc
        ω x = min (C x (x + (1, 0))) (C x (x + (0, 1))) := (hrec x).symm
        _ ≤ C x (x + (1, 0)) := min_le_left _ _
    linarith
  have hup : ∀ x, ω x - C x (x + (0, 1)) ≤ 0 := by
    intro x
    have hle : ω x ≤ C x (x + (0, 1)) := by
      calc
        ω x = min (C x (x + (1, 0))) (C x (x + (0, 1))) := (hrec x).symm
        _ ≤ C x (x + (0, 1)) := min_le_right _ _
    linarith
  -- The path estimate gives the upper bound for every displacement.
  have hupper (u : Lattice) (d : ℕ × ℕ) :
      lastPassage ω u d ≤ C u (u + ((d.1 : ℤ), (d.2 : ℤ))) := by
    have h := LPP.lastPassage_le_additivePotential_add_steps C hC ω 0 hright hup u d
    simpa using h
  -- Iterate the recovering edge and the outgoing recurrence to find equality.
  have hAttain : ∀ n : ℕ, ∀ u : Lattice,
      ∃ d : ℕ × ℕ, d.1 + d.2 = n ∧
        lastPassage ω u d = C u (u + ((d.1 : ℤ), (d.2 : ℤ))) := by
    intro n
    induction n with
    | zero =>
        intro u
        refine ⟨(0, 0), ?_, ?_⟩
        · simp
        · have hzeroEnd : u + ((0 : ℤ), (0 : ℤ)) = u := by
            apply Prod.ext <;> dsimp <;> ring
          rw [lastPassage_zero]
          change 0 = C u (u + ((0 : ℤ), (0 : ℤ)))
          rw [hzeroEnd]
          exact (hCdiag u).symm
    | succ n ih =>
        intro u
        rcases le_total (C u (u + (1, 0))) (C u (u + (0, 1))) with heast | hnorth
        · -- Choose an east edge whose weight equals its potential increment.
          have hrecover : ω u = C u (u + (1, 0)) := by
            calc
              ω u = min (C u (u + (1, 0))) (C u (u + (0, 1))) := (hrec u).symm
              _ = C u (u + (1, 0)) := min_eq_left heast
          obtain ⟨d, hd, hpath⟩ := ih (u + (1, 0))
          have hsum : (d.1 + 1) + d.2 = n + 1 := by omega
          have hend :
              (u + (1, 0)) + ((d.1 : ℤ), (d.2 : ℤ)) =
                u + (((d.1 + 1 : ℕ) : ℤ), (d.2 : ℤ)) := by
            apply Prod.ext <;> dsimp <;> omega
          -- The outgoing recurrence puts at least this recovered edge plus the tail value below the passage value.
          have hrecurrence :
              ω u + lastPassage ω (u + (1, 0)) d ≤
                lastPassage ω u (d.1 + 1, d.2) := by
            by_cases hzero : d.2 = 0
            · have hdpair : d = (d.1, 0) := by
                apply Prod.ext
                · rfl
                · exact hzero
              have hparentPair : (d.1 + 1, 0) = (d.1 + 1, d.2) := by
                exact Prod.ext rfl hzero.symm
              have hout := lastPassage_outgoing_horizontal_succ ω u d.1
              have htail := congrArg (lastPassage ω (u + (1, 0))) hdpair
              have hparent := congrArg (lastPassage ω u) hparentPair
              calc
                ω u + lastPassage ω (u + (1, 0)) d =
                    ω u + lastPassage ω (u + (1, 0)) (d.1, 0) :=
                  congrArg (fun z => ω u + z) htail
                _ = lastPassage ω u (d.1 + 1, 0) := hout.symm
                _ ≤ lastPassage ω u (d.1 + 1, d.2) := hparent.le
            · have hsub : d.2 - 1 + 1 = d.2 := by omega
              have hout := lastPassage_outgoing_succ_succ ω u d.1 (d.2 - 1)
              have hout' :
                  lastPassage ω u (d.1 + 1, d.2) =
                    ω u + max (lastPassage ω (u + (1, 0)) (d.1, d.2))
                      (lastPassage ω (u + (0, 1)) (d.1 + 1, d.2 - 1)) := by
                simpa only [hsub] using hout
              rw [hout']
              exact add_le_add_right (le_max_left _ _) _
          have hlower :
              C u (u + (((d.1 + 1 : ℕ) : ℤ), (d.2 : ℤ))) ≤
                lastPassage ω u (d.1 + 1, d.2) := by
            calc
              C u (u + (((d.1 + 1 : ℕ) : ℤ), (d.2 : ℤ))) =
                  C u (u + (1, 0)) +
                    C (u + (1, 0)) (u + (((d.1 + 1 : ℕ) : ℤ), (d.2 : ℤ))) :=
                  (hC u (u + (1, 0))
                    (u + (((d.1 + 1 : ℕ) : ℤ), (d.2 : ℤ)))).symm
              _ = ω u +
                    C (u + (1, 0)) (u + (((d.1 + 1 : ℕ) : ℤ), (d.2 : ℤ))) := by
                  rw [← hrecover]
              _ = ω u +
                    C (u + (1, 0)) ((u + (1, 0)) + ((d.1 : ℤ), (d.2 : ℤ))) := by
                  rw [← hend]
              _ = ω u + lastPassage ω (u + (1, 0)) d := by rw [← hpath]
              _ ≤ lastPassage ω u (d.1 + 1, d.2) := hrecurrence
          refine ⟨(d.1 + 1, d.2), hsum, ?_⟩
          exact le_antisymm (hupper u (d.1 + 1, d.2)) hlower
        · -- Choose a north edge whose weight equals its potential increment.
          have hrecover : ω u = C u (u + (0, 1)) := by
            calc
              ω u = min (C u (u + (1, 0))) (C u (u + (0, 1))) := (hrec u).symm
              _ = C u (u + (0, 1)) := min_eq_right hnorth
          obtain ⟨d, hd, hpath⟩ := ih (u + (0, 1))
          have hsum : d.1 + (d.2 + 1) = n + 1 := by omega
          have hend :
              (u + (0, 1)) + ((d.1 : ℤ), (d.2 : ℤ)) =
                u + ((d.1 : ℤ), ((d.2 + 1 : ℕ) : ℤ)) := by
            apply Prod.ext <;> dsimp <;> omega
          -- The outgoing recurrence puts at least this recovered edge plus the tail value below the passage value.
          have hrecurrence :
              ω u + lastPassage ω (u + (0, 1)) d ≤
                lastPassage ω u (d.1, d.2 + 1) := by
            by_cases hzero : d.1 = 0
            · have hdpair : d = (0, d.2) := by
                apply Prod.ext
                · exact hzero
                · rfl
              have hparentPair : (0, d.2 + 1) = (d.1, d.2 + 1) := by
                exact Prod.ext hzero.symm rfl
              have hout := lastPassage_outgoing_vertical_succ ω u d.2
              have htail := congrArg (lastPassage ω (u + (0, 1))) hdpair
              have hparent := congrArg (lastPassage ω u) hparentPair
              calc
                ω u + lastPassage ω (u + (0, 1)) d =
                    ω u + lastPassage ω (u + (0, 1)) (0, d.2) :=
                  congrArg (fun z => ω u + z) htail
                _ = lastPassage ω u (0, d.2 + 1) := hout.symm
                _ ≤ lastPassage ω u (d.1, d.2 + 1) := hparent.le
            · have hsub : d.1 - 1 + 1 = d.1 := by omega
              have hout := lastPassage_outgoing_succ_succ ω u (d.1 - 1) d.2
              have hout' :
                  lastPassage ω u (d.1, d.2 + 1) =
                    ω u + max (lastPassage ω (u + (1, 0)) (d.1 - 1, d.2 + 1))
                      (lastPassage ω (u + (0, 1)) (d.1, d.2)) := by
                simpa only [hsub] using hout
              rw [hout']
              exact add_le_add_right (le_max_right _ _) _
          have hlower :
              C u (u + ((d.1 : ℤ), ((d.2 + 1 : ℕ) : ℤ))) ≤
                lastPassage ω u (d.1, d.2 + 1) := by
            calc
              C u (u + ((d.1 : ℤ), ((d.2 + 1 : ℕ) : ℤ))) =
                  C u (u + (0, 1)) +
                    C (u + (0, 1)) (u + ((d.1 : ℤ), ((d.2 + 1 : ℕ) : ℤ))) :=
                  (hC u (u + (0, 1))
                    (u + ((d.1 : ℤ), ((d.2 + 1 : ℕ) : ℤ)))).symm
              _ = ω u +
                    C (u + (0, 1)) (u + ((d.1 : ℤ), ((d.2 + 1 : ℕ) : ℤ))) := by
                  rw [← hrecover]
              _ = ω u +
                    C (u + (0, 1)) ((u + (0, 1)) + ((d.1 : ℤ), (d.2 : ℤ))) := by
                  rw [← hend]
              _ = ω u + lastPassage ω (u + (0, 1)) d := by rw [← hpath]
              _ ≤ lastPassage ω u (d.1, d.2 + 1) := hrecurrence
          refine ⟨(d.1, d.2 + 1), hsum, ?_⟩
          exact le_antisymm (hupper u (d.1, d.2 + 1)) hlower
  intro u n
  constructor
  · intro d hd
    exact hupper u d
  · exact hAttain n u

end LPP
