/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.Additive
public import Busemann.Frozen.Definitions.Recovery
public import LPP_Foundations.Frozen.Model.LastPassage
import LPP_Foundations.Model.LastPassage.Basic
import LPP_Foundations.Model.LastPassage.Outgoing
import LPP_Foundations.Model.RecoveryAntidiagonal
import Mathlib.Tactic

/-! # The finite northeast boundary potential -/

@[expose] public section

open LPPDifferentiability LPP.Busemann
open scoped BigOperators

namespace LPP.Busemann

/-- The terminal-excluded finite last-passage maximum with cocycle weights on
its north and east boundary equals the cocycle potential. The original
environment's passage value is bounded by the same potential. This is the
finite boundary construction in GRS arXiv:1510.00859v2, Lemmas 6.3–6.4. -/
theorem northeast_boundary_potential_eq_cocycle
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hrec : recovers_environment ω C)
    (x : Lattice) (d : ℕ × ℕ) :
    letI : DecidableEq ℝ := Classical.decEq ℝ
    let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
    let ωNE : Environment := fun z =>
      if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0))
      else if z.1 = v.1 ∧ z.2 < v.2 then C z (z + (0, 1))
      else ω z
    let A : Finset (Path x d) := Finset.univ
    (A.image (fun p => pathWeight ωNE p)).max'
      (by dsimp [A]; exact Finset.Nonempty.image Finset.univ_nonempty _) = C x v ∧
      lastPassage ω x d ≤ C x v := by
  classical
  let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
  let boundaryEnv : Lattice → Environment := fun terminal z =>
    if z.2 = terminal.2 ∧ z.1 < terminal.1 then C z (z + (1, 0))
    else if z.1 = terminal.1 ∧ z.2 < terminal.2 then C z (z + (0, 1))
    else ω z
  let ωNE : Environment := boundaryEnv v
  change lastPassage ωNE x d = C x v ∧ lastPassage ω x d ≤ C x v
  have hdiag (u : Lattice) : C u u = 0 := by
    have h := hC u u u
    linarith
  have hpotential :
      ∀ (n : ℕ) (terminal start : Lattice) (e : ℕ × ℕ),
        e.1 + e.2 = n →
        start + ((e.1 : ℤ), (e.2 : ℤ)) = terminal →
        lastPassage (boundaryEnv terminal) start e = C start terminal := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro terminal start e hlen hend
      have hend₁ : start.1 + (e.1 : ℤ) = terminal.1 := by
        have h := congrArg Prod.fst hend
        simpa using h
      have hend₂ : start.2 + (e.2 : ℤ) = terminal.2 := by
        have h := congrArg Prod.snd hend
        simpa using h
      by_cases he₁ : e.1 = 0
      · by_cases he₂ : e.2 = 0
        · have he : e = (0, 0) := Prod.ext he₁ he₂
          subst e
          have hst : start = terminal := by
            apply Prod.ext
            · have h := congrArg Prod.fst hend
              simpa using h
            · have h := congrArg Prod.snd hend
              simpa using h
          rw [lastPassage_zero]
          rw [← hst]
          exact (hdiag start).symm
        · have hpos₂ : 1 ≤ e.2 := by omega
          have hend₁eq : start.1 = terminal.1 := by simpa [he₁] using hend₁
          have hend₂lt : start.2 < terminal.2 := by omega
          have hboundary :
              boundaryEnv terminal start = C start (start + (0, 1)) := by
            simp [boundaryEnv, hend₁eq, hend₂lt]
          have hsub : e.2 - 1 + 1 = e.2 := Nat.sub_add_cancel hpos₂
          have hsubZ : ((e.2 - 1 : ℕ) : ℤ) + 1 = (e.2 : ℤ) := by
            exact_mod_cast hsub
          have hendChild :
              (start + (0, 1)) + ((0 : ℤ), ((e.2 - 1 : ℕ) : ℤ)) = terminal := by
            apply Prod.ext
            · change start.1 + 0 + 0 = terminal.1
              simpa [he₁] using hend₁
            · change start.2 + 1 + ((e.2 - 1 : ℕ) : ℤ) = terminal.2
              calc
                _ = start.2 + (((e.2 - 1 : ℕ) : ℤ) + 1) := by ring
                _ = start.2 + (e.2 : ℤ) := by rw [hsubZ]
                _ = terminal.2 := hend₂
          have hchildLen : e.2 - 1 < n := by omega
          have hchild := ih (e.2 - 1) hchildLen terminal (start + (0, 1))
            (0, e.2 - 1) (by simp) hendChild
          have houtgoing := lastPassage_outgoing_vertical_succ
            (boundaryEnv terminal) start (e.2 - 1)
          have hePair : e = (0, e.2) := Prod.ext he₁ rfl
          have hparent : lastPassage (boundaryEnv terminal) start e =
              boundaryEnv terminal start +
                lastPassage (boundaryEnv terminal) (start + (0, 1)) (0, e.2 - 1) := by
            rw [hePair]
            simpa [hsub] using houtgoing
          rw [hparent, hboundary, hchild]
          exact hC start (start + (0, 1)) terminal
      · by_cases he₂ : e.2 = 0
        · have hpos₁ : 1 ≤ e.1 := by omega
          have hend₂eq : start.2 = terminal.2 := by simpa [he₂] using hend₂
          have hend₁lt : start.1 < terminal.1 := by omega
          have hboundary :
              boundaryEnv terminal start = C start (start + (1, 0)) := by
            simp [boundaryEnv, hend₂eq, hend₁lt]
          have hsub : e.1 - 1 + 1 = e.1 := Nat.sub_add_cancel hpos₁
          have hsubZ : ((e.1 - 1 : ℕ) : ℤ) + 1 = (e.1 : ℤ) := by
            exact_mod_cast hsub
          have hendChild :
              (start + (1, 0)) + (((e.1 - 1 : ℕ) : ℤ), (0 : ℤ)) = terminal := by
            apply Prod.ext
            · change start.1 + 1 + ((e.1 - 1 : ℕ) : ℤ) = terminal.1
              calc
                _ = start.1 + (((e.1 - 1 : ℕ) : ℤ) + 1) := by ring
                _ = start.1 + (e.1 : ℤ) := by rw [hsubZ]
                _ = terminal.1 := hend₁
            · change start.2 + 0 + 0 = terminal.2
              simpa [he₂] using hend₂
          have hchildLen : (e.1 - 1) + 0 < n := by omega
          have hchild := ih (e.1 - 1) hchildLen terminal (start + (1, 0))
            (e.1 - 1, 0) rfl hendChild
          have houtgoing := lastPassage_outgoing_horizontal_succ
            (boundaryEnv terminal) start (e.1 - 1)
          have hePair : e = (e.1, 0) := Prod.ext rfl he₂
          have hparent : lastPassage (boundaryEnv terminal) start e =
              boundaryEnv terminal start +
                lastPassage (boundaryEnv terminal) (start + (1, 0)) (e.1 - 1, 0) := by
            rw [hePair]
            simpa [hsub] using houtgoing
          rw [hparent, hboundary, hchild]
          exact hC start (start + (1, 0)) terminal
        · have hpos₁ : 1 ≤ e.1 := by omega
          have hpos₂ : 1 ≤ e.2 := by omega
          let a : ℕ := e.1 - 1
          let b : ℕ := e.2 - 1
          have ha : a + 1 = e.1 := by dsimp [a]; exact Nat.sub_add_cancel hpos₁
          have hb : b + 1 = e.2 := by dsimp [b]; exact Nat.sub_add_cancel hpos₂
          have hend₁lt : start.1 < terminal.1 := by omega
          have hend₂lt : start.2 < terminal.2 := by omega
          have hnotNorth : ¬ (start.2 = terminal.2 ∧ start.1 < terminal.1) := by
            rintro ⟨h, _⟩
            exact (ne_of_lt hend₂lt) h
          have hnotEast : ¬ (start.1 = terminal.1 ∧ start.2 < terminal.2) := by
            rintro ⟨h, _⟩
            exact (ne_of_lt hend₁lt) h
          have hbulk : boundaryEnv terminal start = ω start := by
            simp [boundaryEnv, hnotNorth, hnotEast]
          have hendRight :
              (start + (1, 0)) + ((a : ℤ), (e.2 : ℤ)) = terminal := by
            apply Prod.ext
            · change start.1 + 1 + (a : ℤ) = terminal.1
              calc
                _ = start.1 + ((1 : ℤ) + (a : ℤ)) := by ring
                _ = start.1 + (e.1 : ℤ) := by
                  congr 1
                  exact_mod_cast (show 1 + a = e.1 by omega)
                _ = terminal.1 := hend₁
            · change start.2 + 0 + (e.2 : ℤ) = terminal.2
              simpa using hend₂
          have hendUp :
              (start + (0, 1)) + ((e.1 : ℤ), (b : ℤ)) = terminal := by
            apply Prod.ext
            · change start.1 + 0 + (e.1 : ℤ) = terminal.1
              simpa using hend₁
            · change start.2 + 1 + (b : ℤ) = terminal.2
              calc
                _ = start.2 + ((1 : ℤ) + (b : ℤ)) := by ring
                _ = start.2 + (e.2 : ℤ) := by
                  congr 1
                  exact_mod_cast (show 1 + b = e.2 by omega)
                _ = terminal.2 := hend₂
          have hrightLen : a + e.2 < n := by omega
          have hupLen : e.1 + b < n := by omega
          have hright := ih (a + e.2) hrightLen terminal (start + (1, 0))
            (a, e.2) rfl hendRight
          have hup := ih (e.1 + b) hupLen terminal (start + (0, 1))
            (e.1, b) rfl hendUp
          have houtgoing := lastPassage_outgoing_succ_succ
            (boundaryEnv terminal) start a b
          have hparent : lastPassage (boundaryEnv terminal) start e =
              boundaryEnv terminal start + max
                (lastPassage (boundaryEnv terminal) (start + (1, 0)) (a, e.2))
                (lastPassage (boundaryEnv terminal) (start + (0, 1)) (e.1, b)) := by
            simpa only [ha, hb] using houtgoing
          have hrecC := hrec start
          have haddRight := hC start (start + (1, 0)) terminal
          have haddUp := hC start (start + (0, 1)) terminal
          have hCmax : C start terminal = ω start +
              max (C (start + (1, 0)) terminal) (C (start + (0, 1)) terminal) := by
            rcases le_total (C start (start + (1, 0)))
                (C start (start + (0, 1))) with hle | hle
            · have hmin := hrecC
              rw [min_eq_left hle] at hmin
              have hchildOrder : C (start + (0, 1)) terminal ≤
                  C (start + (1, 0)) terminal := by
                linarith
              calc
                C start terminal = C start (start + (1, 0)) +
                    C (start + (1, 0)) terminal := haddRight.symm
                _ = ω start + C (start + (1, 0)) terminal := by rw [hmin]
                _ = ω start + max (C (start + (1, 0)) terminal)
                    (C (start + (0, 1)) terminal) := by rw [max_eq_left hchildOrder]
            · have hmin := hrecC
              rw [min_eq_right hle] at hmin
              have hchildOrder : C (start + (1, 0)) terminal ≤
                  C (start + (0, 1)) terminal := by
                linarith
              calc
                C start terminal = C start (start + (0, 1)) +
                    C (start + (0, 1)) terminal := haddUp.symm
                _ = ω start + C (start + (0, 1)) terminal := by rw [hmin]
                _ = ω start + max (C (start + (1, 0)) terminal)
                    (C (start + (0, 1)) terminal) := by rw [max_eq_right hchildOrder]
          rw [hparent, hbulk, hright, hup, hCmax]
  constructor
  · change lastPassage (boundaryEnv v) x d = C x v
    exact hpotential (d.1 + d.2) v x d rfl rfl
  · have hcomparison := LPP.lastPassage_antidiagonal_comparison_and_attainment
      ω C (fun u y z => hC u y z) (fun u => hrec u) x (d.1 + d.2)
    simpa [v] using hcomparison.1 d rfl

end LPP.Busemann

end
