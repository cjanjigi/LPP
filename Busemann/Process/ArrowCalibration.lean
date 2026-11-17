/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.CalibratedPaths
import LPP_Foundations.Model.Path.ArrowOrder
import Lean.Elab.Tactic.Omega

/-! Finite path and weight data for a calibrated up-right arrow map. -/

@[expose] public section
open LPPDifferentiability LPP.Busemann

namespace LPP.Busemann

/-- A calibrated up-right arrow yields one endpoint-indexed path whose
vertices are its iterates and whose collected weight is both the endpoint
potential and the last-passage maximum. This packages the finite path steps in
GRS, arXiv:1510.00860v1, Appendix A.1–A.2 (lines 1481–1489). -/
theorem exists_calibrated_arrow_iterate_path
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hrec : recovers_environment ω C)
    (s : Lattice → Lattice)
    (hs : ∀ z, s z = z + (1, 0) ∨ s z = z + (0, 1))
    (hcalArrow : ∀ z, C z (s z) = ω z)
    (x : Lattice) (N : ℕ) :
    ∃ q : Sigma (fun k : Fin (N + 1) =>
      LPPDifferentiability.Path x (k.val, N - k.val)),
      (∀ j : ℕ, ∀ hj : j < q.1.val + (N - q.1.val) + 1,
        q.2.vertex ⟨j, hj⟩ = s^[j] x) ∧
        pathWeight ω q.2 = C x (s^[N] x) ∧
        pathWeight ω q.2 = lastPassage ω x (q.1.val, N - q.1.val) := by
  -- The finite-arrow result supplies the path and its full trace.
  obtain ⟨q, htrace⟩ :=
    LPPDifferentiability.exists_arrow_iterate_path_trace s hs x N
  have hqBound : q.1.val ≤ N := Nat.le_of_lt_succ q.1.isLt
  have hpathLength : q.1.val + (N - q.1.val) = N := by omega

  -- Adjacent entries of the trace turn arrow calibration into path calibration.
  have hpathCalibration :
      ∀ i : Fin (q.1.val + (N - q.1.val)),
        C (q.2.vertex i.castSucc) (q.2.vertex i.succ) =
          ω (q.2.vertex i.castSucc) := by
    intro i
    have hbefore := htrace i.val (by omega)
    have hbeforeIndex :
        (⟨i.val, by omega⟩ : Fin (q.1.val + (N - q.1.val) + 1)) =
          i.castSucc := by
      apply Fin.ext
      rfl
    rw [hbeforeIndex] at hbefore
    have hafter := htrace (i.val + 1) (by omega)
    have hafterIndex :
        (⟨i.val + 1, by omega⟩ : Fin (q.1.val + (N - q.1.val) + 1)) =
          i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
    rw [hafterIndex] at hafter
    calc
      C (q.2.vertex i.castSucc) (q.2.vertex i.succ) =
          C (s^[i.val] x) (s^[i.val + 1] x) := by rw [hbefore, hafter]
      _ = C (s^[i.val] x) (s (s^[i.val] x)) := by
        rw [Function.iterate_succ_apply']
      _ = ω (s^[i.val] x) := hcalArrow (s^[i.val] x)
      _ = ω (q.2.vertex i.castSucc) := by rw [hbefore]

  -- The last trace entry and the path endpoint have the same index and site.
  have hlastIndex :
      (⟨N, by omega⟩ : Fin (q.1.val + (N - q.1.val) + 1)) =
        Fin.last (q.1.val + (N - q.1.val)) := by
    apply Fin.ext
    simp only [Fin.val_last]
    exact hpathLength.symm
  have hlastTrace :
      q.2.vertex (Fin.last (q.1.val + (N - q.1.val))) = s^[N] x := by
    have h := htrace N (by omega)
    rw [← hlastIndex]
    exact h
  have hterminal :
      s^[N] x = x + ((q.1.val : ℤ), ((N - q.1.val : ℕ) : ℤ)) := by
    rw [← hlastTrace]
    exact q.2.finish

  -- One application of the calibration theorem supplies both weights.
  have hweights := calibrated_path_weight_eq_and_maximizing ω C hC hrec x
    (q.1.val, N - q.1.val) q.2 hpathCalibration
  refine ⟨q, htrace, ?_⟩
  constructor
  · calc
      pathWeight ω q.2 =
          C x (x + ((q.1.val : ℤ), ((N - q.1.val : ℕ) : ℤ))) :=
        hweights.1
      _ = C x (s^[N] x) := by rw [← hterminal]
  · exact hweights.2

end LPP.Busemann
