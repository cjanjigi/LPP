-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Environment
public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Data.EReal.Basic

@[expose] public section

open LPPDifferentiability
open scoped ENNReal

namespace LPP.Busemann

/-- The source finite tilted point-to-line value, including its stated -infinity case. -/
noncomputable def finiteTiltedPotential (ω : Environment) (h : ℝ × ℝ)
    (x : Lattice) (n : ℤ) : EReal := by
  classical
  if hx : x.1 + x.2 ≤ n then
    let m : ℕ := (n - (x.1 + x.2)).toNat
    let f : Fin (m + 1) → ℝ := fun k =>
      lastPassage ω x (k.val, m - k.val) +
        h.1 * (k.val : ℝ) + h.2 * ((m - k.val : ℕ) : ℝ)
    let values : Finset ℝ := Finset.univ.image f
    have hvalues : values.Nonempty :=
      Finset.Nonempty.image Finset.univ_nonempty f
    let maximum : ℝ := values.max' hvalues
    exact (maximum : EReal)
  else
    exact ⊥

end LPP.Busemann
