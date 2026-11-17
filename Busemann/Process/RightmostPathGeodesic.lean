/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.LocallyRightmostGeodesic
public import Busemann.Process.RightmostPaths
import Busemann.Process.PathTotalCalibration
import LPP_Foundations.Model.LastPassage.RightmostFinite
import LPP_Foundations.Model.Paths.Level
import LPP_Foundations.Model.Paths.Translate
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-! Membership of the east-tie cocycle ray in the literal local geodesic class. -/

@[expose] public section

open LPPDifferentiability LPP.Busemann

namespace LPP.Busemann

private theorem rightmostCocyclePath_iterate_add
    (C : Lattice → Lattice → ℝ) (u : Lattice) (m n : ℕ) :
    rightmostCocyclePath C (rightmostCocyclePath C u m) n =
      rightmostCocyclePath C u (m + n) := by
  change (rightmostCocycleSuccessor C)^[n]
      ((rightmostCocycleSuccessor C)^[m] u) =
    (rightmostCocycleSuccessor C)^[m + n] u
  rw [Nat.add_comm m n, Function.iterate_add_apply]

private theorem rightmostCocyclePath_step
    (C : Lattice → Lattice → ℝ) (u : Lattice) (n : ℕ) :
    rightmostCocyclePath C u (n + 1) =
      rightmostCocycleSuccessor C (rightmostCocyclePath C u n) := by
  simp [rightmostCocyclePath, Function.iterate_succ_apply']

private theorem rightmost_path_eq_of_calibrated
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    {x : Lattice} {d : ℕ × ℕ}
    (p g : Path x d)
    (htrace : ∀ j : ℕ, ∀ hj : j < d.1 + d.2 + 1,
      p.vertex ⟨j, hj⟩ = rightmostCocyclePath C x j)
    (hpLeG : ∀ i : Fin (d.1 + d.2 + 1), (p.vertex i).1 ≤ (g.vertex i).1)
    (hpcal : ∀ k : Fin (d.1 + d.2),
      C (p.vertex k.castSucc) (p.vertex k.succ) = ω (p.vertex k.castSucc))
    (hgcal : ∀ k : Fin (d.1 + d.2),
      C (g.vertex k.castSucc) (g.vertex k.succ) = ω (g.vertex k.castSucc)) :
    p = g := by
  apply LPPDifferentiability.Path.ext
  intro i
  induction i using Fin.induction with
  | zero =>
      rw [p.start, g.start]
  | succ j ih =>
      have hprev : p.vertex j.castSucc = g.vertex j.castSucc := ih
      rcases p.step j with hpEast | hpNorth
      · rcases g.step j with hgEast | hgNorth
        · rw [hpEast, hgEast, hprev]
        · have horder := hpLeG j.succ
          rw [hpEast, hgNorth, hprev] at horder
          simp only [Prod.fst_add] at horder
          omega
      · rcases g.step j with hgEast | hgNorth
        · have hbefore : p.vertex j.castSucc = rightmostCocyclePath C x j.val := by
            have h := htrace j.val j.castSucc.isLt
            have hindex :
                (⟨j.val, j.castSucc.isLt⟩ : Fin (d.1 + d.2 + 1)) =
                  j.castSucc := by
              apply Fin.ext
              rfl
            rw [hindex] at h
            exact h
          have hafter : p.vertex j.succ =
              rightmostCocyclePath C x (j.val + 1) := by
            have h := htrace j.succ.val j.succ.isLt
            have hindex :
                (⟨j.succ.val, j.succ.isLt⟩ : Fin (d.1 + d.2 + 1)) =
                  j.succ := by
              apply Fin.ext
              rfl
            rw [hindex] at h
            simpa only [Fin.val_succ] using h
          have hactualNorth :
              rightmostCocycleSuccessor C (p.vertex j.castSucc) =
                p.vertex j.castSucc + (0, 1) := by
            calc
              rightmostCocycleSuccessor C (p.vertex j.castSucc) =
                  rightmostCocycleSuccessor C (rightmostCocyclePath C x j.val) := by
                    rw [hbefore]
              _ = rightmostCocyclePath C x (j.val + 1) :=
                    (rightmostCocyclePath_step C x j.val).symm
              _ = p.vertex j.succ := hafter.symm
              _ = p.vertex j.castSucc + (0, 1) := hpNorth
          have hnotEast :
              ¬ C (p.vertex j.castSucc) (p.vertex j.castSucc + (1, 0)) ≤
                C (p.vertex j.castSucc) (p.vertex j.castSucc + (0, 1)) := by
            intro hEastLe
            have hEast : rightmostCocycleSuccessor C (p.vertex j.castSucc) =
                p.vertex j.castSucc + (1, 0) := by
              simp [rightmostCocycleSuccessor, hEastLe]
            have hEq := hEast.symm.trans hactualNorth
            have hFirst := congrArg Prod.fst hEq
            simp only [Prod.fst_add] at hFirst
            omega
          have hpEdge := hpcal j
          have hgEdge := hgcal j
          rw [hpNorth] at hpEdge
          rw [hgEast, ← hprev] at hgEdge
          have hcalEq :
              C (p.vertex j.castSucc) (p.vertex j.castSucc + (1, 0)) =
                C (p.vertex j.castSucc) (p.vertex j.castSucc + (0, 1)) :=
            hgEdge.trans hpEdge.symm
          exact False.elim (hnotEast (le_of_eq hcalEq))
        · rw [hpNorth, hgNorth, hprev]

/-- The actual east-tie cocycle ray has locally-rightmost finite segments.
Strong Existence manuscript, lines 430–438 and 1718–1720. -/
theorem isLocallyRightmostGeodesic_rightmostCocyclePath
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hrec : recovers_environment ω C)
    (u : Lattice) :
    IsLocallyRightmostGeodesic ω u (rightmostCocyclePath C u) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simp only [rightmostCocyclePath, Function.iterate_zero_apply]
  · intro n
    simpa only [rightmostCocyclePath, Function.iterate_succ_apply'] using
      rightmostCocycleSuccessor_step C (rightmostCocyclePath C u n)
  · intro m N hN
    let x : Lattice := rightmostCocyclePath C u m
    obtain ⟨rayPrefix, htrace, hpotential, hmaximum⟩ :=
      exists_rightmostCocyclePath_prefix ω C hC hrec x N
    let d : ℕ × ℕ := (rayPrefix.1.val, N - rayPrefix.1.val)
    let p : Path x d := rayPrefix.2
    have hlength : d.1 + d.2 = N := by
      dsimp [d]
      have hlt := rayPrefix.1.isLt
      omega
    have htraceEnd : p.vertex (Fin.last (d.1 + d.2)) =
        rightmostCocyclePath C x N := by
      have h := htrace N (by
        have hlt := rayPrefix.1.isLt
        omega)
      have hindex :
          (⟨N, by
            have hlt := rayPrefix.1.isLt
            omega⟩ :
            Fin (rayPrefix.1.val + (N - rayPrefix.1.val) + 1)) =
              Fin.last (rayPrefix.1.val + (N - rayPrefix.1.val)) := by
        apply Fin.ext
        simp only [Fin.val_last]
        have hlt := rayPrefix.1.isLt
        omega
      rw [hindex] at h
      simpa [p, d] using h
    have hendpoint : x + ((d.1 : ℤ), (d.2 : ℤ)) =
        rightmostCocyclePath C x N := p.finish.symm.trans htraceEnd
    have htraceP : ∀ j : ℕ, ∀ hj : j < d.1 + d.2 + 1,
        p.vertex ⟨j, hj⟩ = rightmostCocyclePath C x j := by
      intro j hj
      have h := htrace j (by simpa [d] using hj)
      have hindex :
          (⟨j, by simpa [d] using hj⟩ :
            Fin (rayPrefix.1.val + (N - rayPrefix.1.val) + 1)) =
          (⟨j, hj⟩ : Fin (d.1 + d.2 + 1)) := by
        apply Fin.ext
        rfl
      rw [hindex] at h
      simpa [p] using h
    have hpMaximum : pathWeight ω p = lastPassage ω x d := by
      simpa [p, d] using hmaximum
    have hpTotal : pathWeight ω p =
        C x (x + ((d.1 : ℤ), (d.2 : ℤ))) := by
      calc
        pathWeight ω p = C x (rightmostCocyclePath C x N) := by
          simpa [p] using hpotential
        _ = C x (x + ((d.1 : ℤ), (d.2 : ℤ))) := by rw [← hendpoint]
    have hpcal : ∀ k : Fin (d.1 + d.2),
        C (p.vertex k.castSucc) (p.vertex k.succ) =
          ω (p.vertex k.castSucc) :=
      (pathWeight_eq_cocycle_iff_calibrated ω C hC hrec x d p).mp hpTotal
    obtain ⟨g, hg, _⟩ :=
      LPPDifferentiability.exists_unique_rightmost_maximizing_path ω x d
    rcases hg with ⟨hgMaximum, hgGreatest⟩
    have hgTotal : pathWeight ω g = C x (x + ((d.1 : ℤ), (d.2 : ℤ))) := by
      calc
        pathWeight ω g = lastPassage ω x d := hgMaximum
        _ = pathWeight ω p := hpMaximum.symm
        _ = C x (x + ((d.1 : ℤ), (d.2 : ℤ))) := hpTotal
    have hgcal : ∀ k : Fin (d.1 + d.2),
        C (g.vertex k.castSucc) (g.vertex k.succ) =
          ω (g.vertex k.castSucc) :=
      (pathWeight_eq_cocycle_iff_calibrated ω C hC hrec x d g).mp hgTotal
    have hpLeG : ∀ i : Fin (d.1 + d.2 + 1),
        (p.vertex i).1 ≤ (g.vertex i).1 := by
      intro i
      exact hgGreatest p hpMaximum i
    have hpg : p = g :=
      rightmost_path_eq_of_calibrated ω C p g htraceP hpLeG hpcal hgcal
    refine ⟨d, p, hlength, ?_, hpMaximum, ?_⟩
    · intro i
      have h := htraceP i.val i.isLt
      have hindex : (⟨i.val, i.isLt⟩ : Fin (d.1 + d.2 + 1)) = i := by
        apply Fin.ext
        rfl
      rw [hindex] at h
      have hshift : rightmostCocyclePath C x i.val =
          rightmostCocyclePath C u (m + i.val) := by
        dsimp [x]
        exact rightmostCocyclePath_iterate_add C u m i.val
      rw [hshift] at h
      exact h
    · intro q hq i
      have hqFirst : (q.vertex i).1 ≤ (p.vertex i).1 := by
        have h := hgGreatest q hq i
        simpa [hpg] using h
      have hpLevel := p.level i
      have hqLevel := q.level i
      have hqLevelAtX :
          (q.vertex i).1 + (q.vertex i).2 = x.1 + x.2 + (i.val : ℤ) := by
        simpa [x] using hqLevel
      have hlevelEq :
          (p.vertex i).1 + (p.vertex i).2 =
            (q.vertex i).1 + (q.vertex i).2 :=
        hpLevel.trans hqLevelAtX.symm
      have hSecond : (p.vertex i).2 ≤ (q.vertex i).2 := by omega
      exact ⟨hqFirst, hSecond⟩

end LPP.Busemann
