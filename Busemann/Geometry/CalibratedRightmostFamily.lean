/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Geometry.LocallyRightmostGeodesic
public import Busemann.Process.RightmostPathGeodesic
public import Busemann.Frozen.Definitions.Additive
public import Busemann.Frozen.Definitions.Recovery
public import LPP_Foundations.Model.Paths.Coalescence
import Busemann.Process.CalibratedPaths
import LPP_Foundations.Model.Paths.HorizontalFirst
import LPP_Foundations.Model.Paths.WeightConcat
import Lean.Elab.Tactic.Omega

@[expose] public section
open LPPDifferentiability
namespace LPP.Busemann

/-- A coalescing all-root family of locally rightmost geodesics calibrated by
the same recovering additive cocycle is exactly that cocycle's east-tie
rightmost path family. This identifies the original quantile sampler's paths
after finite-field reconstruction; Strong Existence, lm:B-cK lines 1018–1038
and lm:orig_space lines 1079–1082. -/
theorem rightmostCocyclePath_eq_coalescing_calibrated_locallyRightmost_family
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hAdd : is_additive C) (hRec : recovers_environment ω C)
    (π : Lattice → ℕ → Lattice)
    (hGeo : ∀ u : Lattice, IsLocallyRightmostGeodesic ω u (π u))
    (hCoal : ∀ u v : Lattice, paths_coalesce u v (π u) (π v))
    (hCal : ∀ (u : Lattice) (n : ℕ),
      C (π u n) (π u (n + 1)) = ω (π u n)) :
    ∀ u : Lattice, rightmostCocyclePath C u = π u := by
  classical
  have hLevel (u : Lattice) (j : ℕ) :
      (π u j).1 + (π u j).2 = u.1 + u.2 + (j : ℤ) := by
    induction j with
    | zero => simp only [(hGeo u).1, Nat.cast_zero, add_zero]
    | succ j ih =>
        rcases (hGeo u).2.1 j with he | hn
        · rw [he]
          simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ]
          omega
        · rw [hn]
          simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ]
          omega
  have hSucc (u : Lattice) (t : ℕ) :
      rightmostCocycleSuccessor C (π u t) = π u (t + 1) := by
    let x : Lattice := π u t
    let e : Lattice := x + ((1 : ℤ), (0 : ℤ))
    let north : Lattice := x + ((0 : ℤ), (1 : ℤ))
    have hStep := (hGeo u).2.1 t
    have hRecovery : min (C x e) (C x north) = ω x := hRec x
    by_cases hEastLe : C x e ≤ C x north
    · have hEastCal : C x e = ω x := by
        simpa only [min_eq_left hEastLe] using hRecovery
      rcases hStep with he | hn
      · calc
          rightmostCocycleSuccessor C (π u t) = e := by
            simp [rightmostCocycleSuccessor, x, e, north, hEastLe]
          _ = π u (t + 1) := he.symm
      · have hNorth : π u (t + 1) = north := hn
        obtain ⟨m, n, hAlign, hTail⟩ := hCoal u e
        have heLevel : e.1 + e.2 = u.1 + u.2 + (t : ℤ) + 1 := by
          dsimp [e, x]
          have hl := hLevel u t
          omega
        have hm : m = t + 1 + n := by omega
        have hMeet : π u (t + (n + 2)) = π e (n + 1) := by
          simpa only [hm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hTail 1
        obtain ⟨d, g, hd, hgTrace, hgMaximum, hgGreatest⟩ :=
          (hGeo u).2.2 t (n + 2) (by omega)
        obtain ⟨dE, p, hdE, hpTrace, _hpMaximum, _hpGreatest⟩ :=
          (hGeo e).2.2 0 (n + 1) (by omega)
        have hStartE : π e 0 = e := (hGeo e).1
        have hgEnd : g.vertex (Fin.last (d.1 + d.2)) =
            π u (t + (n + 2)) := by
          simpa only [Fin.val_last, hd] using
            hgTrace (Fin.last (d.1 + d.2))
        have hpEnd : p.vertex (Fin.last (dE.1 + dE.2)) =
            π e (n + 1) := by
          simpa only [Fin.val_last, hdE, zero_add] using
            hpTrace (Fin.last (dE.1 + dE.2))
        have hCoordinate :
            x + ((d.1 : ℤ), (d.2 : ℤ)) =
              e + ((dE.1 : ℤ), (dE.2 : ℤ)) := by
          calc
            x + ((d.1 : ℤ), (d.2 : ℤ)) =
                g.vertex (Fin.last (d.1 + d.2)) := g.finish.symm
            _ = π u (t + (n + 2)) := hgEnd
            _ = π e (n + 1) := hMeet
            _ = p.vertex (Fin.last (dE.1 + dE.2)) := hpEnd.symm
            _ = π e 0 + ((dE.1 : ℤ), (dE.2 : ℤ)) := p.finish
            _ = e + ((dE.1 : ℤ), (dE.2 : ℤ)) := by rw [hStartE]
        have hDisp : d = ((1 : ℕ), (0 : ℕ)) + dE := by
          apply Prod.ext
          · have hf := congrArg Prod.fst hCoordinate
            simp only [e, Prod.fst_add] at hf
            simp only [Prod.fst_add]
            omega
          · have hs := congrArg Prod.snd hCoordinate
            simp only [e, Prod.snd_add] at hs
            simp only [Prod.snd_add]
            omega
        have hGCal (k : Fin (d.1 + d.2)) :
            C (g.vertex k.castSucc) (g.vertex k.succ) =
              ω (g.vertex k.castSucc) := by
          rw [hgTrace k.castSucc, hgTrace k.succ]
          simpa only [Fin.val_castSucc, Fin.val_succ, Nat.add_assoc] using
            hCal u (t + k.val)
        have hPCal (k : Fin (dE.1 + dE.2)) :
            C (p.vertex k.castSucc) (p.vertex k.succ) =
              ω (p.vertex k.castSucc) := by
          rw [hpTrace k.castSucc, hpTrace k.succ]
          simpa only [Fin.val_castSucc, Fin.val_succ, zero_add] using
            hCal e k.val
        let pE : LPPDifferentiability.Path e dE :=
          { vertex := p.vertex
            start := p.start.trans hStartE
            finish := by simpa only [hStartE] using p.finish
            step := p.step }
        have hpEVertex (i : Fin (dE.1 + dE.2 + 1)) :
            pE.vertex i = p.vertex i := rfl
        have hPCalE (k : Fin (dE.1 + dE.2)) :
            C (pE.vertex k.castSucc) (pE.vertex k.succ) =
              ω (pE.vertex k.castSucc) := by
          rw [hpEVertex k.castSucc, hpEVertex k.succ]
          exact hPCal k
        have hGPotential :=
          (calibrated_path_weight_eq_and_maximizing
            ω C hAdd hRec x d g hGCal).1
        have hPPotential :=
          (calibrated_path_weight_eq_and_maximizing
            ω C hAdd hRec e dE pE hPCalE).1
        subst d
        let first : LPPDifferentiability.Path x ((1 : ℕ), (0 : ℕ)) :=
          horizontalFirst x ((1 : ℕ), (0 : ℕ))
        let q : LPPDifferentiability.Path x (((1 : ℕ), (0 : ℕ)) + dE) :=
          first.concat pE
        have hFirstWeight : pathWeight ω first = ω x := by
          simp [first, pathWeight, horizontalFirst]
        have hQPotential :
            pathWeight ω q =
              C x (x + (((((1 : ℕ), (0 : ℕ)) + dE).1 : ℤ),
                ((((1 : ℕ), (0 : ℕ)) + dE).2 : ℤ))) := by
          calc
            pathWeight ω q = pathWeight ω first + pathWeight ω pE :=
              pathWeight_concat ω first pE
            _ = ω x + C e (e + ((dE.1 : ℤ), (dE.2 : ℤ))) := by
              rw [hFirstWeight, hPPotential]
            _ = C x e + C e (e + ((dE.1 : ℤ), (dE.2 : ℤ))) := by
              rw [hEastCal]
            _ = C x (e + ((dE.1 : ℤ), (dE.2 : ℤ))) :=
              hAdd x e _
            _ = C x (x + (((((1 : ℕ), (0 : ℕ)) + dE).1 : ℤ),
                  ((((1 : ℕ), (0 : ℕ)) + dE).2 : ℤ))) := by
              rw [← hCoordinate]
        have hQMaximum : pathWeight ω q =
            lastPassage ω x (((1 : ℕ), (0 : ℕ)) + dE) := by
          calc
            pathWeight ω q =
                C x (x + (((((1 : ℕ), (0 : ℕ)) + dE).1 : ℤ),
                  ((((1 : ℕ), (0 : ℕ)) + dE).2 : ℤ))) := hQPotential
            _ = pathWeight ω g := hGPotential.symm
            _ = lastPassage ω x (((1 : ℕ), (0 : ℕ)) + dE) := hgMaximum
        have hQFirst : q.vertex ⟨1, by
              simp only [Prod.fst_add, Prod.snd_add]
              omega⟩ = e := by
          have h := Path.concat_vertex_left first pE (Fin.last 1)
          have hCoord : q.vertex ⟨1, by
              simp only [Prod.fst_add, Prod.snd_add]
              omega⟩ = (x.1 + 1, x.2) := by
            simpa [q, first, horizontalFirst] using h
          rw [hCoord]
          apply Prod.ext
          · simp only [e, Prod.fst_add]
          · simp only [e, Prod.snd_add, add_zero]
        have hGFirst : g.vertex ⟨1, by
              simp only [Prod.fst_add, Prod.snd_add]
              omega⟩ = north := by
          have h := hgTrace ⟨1, by
            have hd' := hdE
            omega⟩
          simpa only [hNorth] using h
        have hOrder := (hgGreatest q hQMaximum ⟨1, by
          simp only [Prod.fst_add, Prod.snd_add]
          omega⟩).1
        rw [hQFirst, hGFirst] at hOrder
        dsimp [e, north] at hOrder
        omega
    · have hStrict : C x north < C x e := lt_of_not_ge hEastLe
      have hNorthCal : C x north = ω x := by
        simpa only [min_eq_right (le_of_lt hStrict)] using hRecovery
      rcases hStep with he | hn
      · have hECal : C x e = ω x := by
          simpa only [x, e, he] using hCal u t
        rw [hNorthCal, hECal] at hStrict
        exact False.elim ((lt_irrefl (ω x)) hStrict)
      · calc
          rightmostCocycleSuccessor C (π u t) = north := by
            simp [rightmostCocycleSuccessor, x, e, north, hEastLe]
          _ = π u (t + 1) := hn.symm
  intro u
  funext t
  induction t with
  | zero => simpa only [rightmostCocyclePath, Function.iterate_zero_apply] using
      (hGeo u).1.symm
  | succ t ih =>
      calc
        rightmostCocyclePath C u (t + 1) =
            rightmostCocycleSuccessor C (rightmostCocyclePath C u t) := by
          simp only [rightmostCocyclePath, Function.iterate_succ_apply']
        _ = rightmostCocycleSuccessor C (π u t) := by rw [ih]
        _ = π u (t + 1) := hSucc u t

end LPP.Busemann
