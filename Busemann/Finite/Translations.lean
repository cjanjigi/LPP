/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.FiniteBusemannEdge
public import LPP_Foundations.Probability.TranslationEquiv
import Busemann.Finite.PotentialOrder
import LPP_Foundations.Model.LastPassage.Translate
import Lean.Elab.Tactic.Omega

/-! Finite potential and edge covariance under the canonical translation. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- Translating the weights and start also shifts the integer horizon by the level of the
translation, as in the finite construction of JR arXiv:1810.03580v3. -/
theorem finiteTiltedPotential_translate (ω : Environment) (h : ℝ × ℝ)
    (x z : Lattice) (n : ℤ) :
    finiteTiltedPotential (environmentTranslationEquiv z ω) h x n =
      finiteTiltedPotential ω h (z + x) (n + z.1 + z.2) := by
  classical
  have hlevel : (z + x).1 + (z + x).2 = (z.1 + z.2) + (x.1 + x.2) := by
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hrem : n + z.1 + z.2 - ((z + x).1 + (z + x).2) = n - (x.1 + x.2) := by
    rw [hlevel]
    omega
  have henv : (environmentTranslationEquiv z ω : Environment) = fun y => ω (z + y) := by
    funext y
    exact environmentTranslationEquiv_apply z ω y
  by_cases hx : x.1 + x.2 ≤ n
  · have hx' : (z + x).1 + (z + x).2 ≤ n + z.1 + z.2 := by
      rw [hlevel]
      omega
    apply le_antisymm
    · rw [← EReal.coe_toReal (finiteTiltedPotential_ne_top ω h (z + x) _ hx')
        (finiteTiltedPotential_ne_bot ω h (z + x) _ hx')]
      apply (finiteTiltedPotential_le_coe_iff (environmentTranslationEquiv z ω)
        h x n hx _).2
      intro k
      let j : Fin ((n + z.1 + z.2 - ((z + x).1 + (z + x).2)).toNat + 1) :=
        ⟨k.val, by simpa only [hrem] using k.isLt⟩
      have hb := finiteTiltedPotential_candidate_le ω h (z + x) _ hx' j
      rw [← EReal.coe_toReal (finiteTiltedPotential_ne_top ω h (z + x) _ hx')
        (finiteTiltedPotential_ne_bot ω h (z + x) _ hx')] at hb
      have hr := EReal.coe_le_coe_iff.mp hb
      simpa only [j, hrem, henv, lastPassage_translate] using hr
    · rw [← EReal.coe_toReal
        (finiteTiltedPotential_ne_top (environmentTranslationEquiv z ω) h x n hx)
        (finiteTiltedPotential_ne_bot (environmentTranslationEquiv z ω) h x n hx)]
      apply (finiteTiltedPotential_le_coe_iff ω h (z + x) _ hx' _).2
      intro k
      let j : Fin ((n - (x.1 + x.2)).toNat + 1) :=
        ⟨k.val, by simpa only [hrem] using k.isLt⟩
      have hb := finiteTiltedPotential_candidate_le (environmentTranslationEquiv z ω)
        h x n hx j
      rw [← EReal.coe_toReal
        (finiteTiltedPotential_ne_top (environmentTranslationEquiv z ω) h x n hx)
        (finiteTiltedPotential_ne_bot (environmentTranslationEquiv z ω) h x n hx)] at hb
      have hr := EReal.coe_le_coe_iff.mp hb
      simpa only [j, hrem, henv, lastPassage_translate] using hr
  · have hx' : ¬ (z + x).1 + (z + x).2 ≤ n + z.1 + z.2 := by
      rw [hlevel]
      omega
    simp only [finiteTiltedPotential, dite_eq_right hx, dite_eq_right hx']

/-- The finite Busemann edge has the same covariance with the shifted integer horizon;
this includes the inactive zero branch of the JR finite construction. -/
theorem finiteBusemannEdge_translate (ω : Environment) (h : ℝ × ℝ)
    (x z : Lattice) (n : ℤ) (i : Fin 2) :
    finiteBusemannEdge (environmentTranslationEquiv z ω) h x n i =
      finiteBusemannEdge ω h (z + x) (n + z.1 + z.2) i := by
  classical
  have hlevel : (z + x).1 + (z + x).2 = (z.1 + z.2) + (x.1 + x.2) := by
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  by_cases hx : x.1 + x.2 < n
  · have hx' : (z + x).1 + (z + x).2 < n + z.1 + z.2 := by
      rw [hlevel]
      omega
    simp only [finiteBusemannEdge, dite_eq_left hx, dite_eq_left hx',
      finiteTiltedPotential_translate]
    rw [← add_assoc z x (finiteEdgeStep i)]
  · have hx' : ¬ (z + x).1 + (z + x).2 < n + z.1 + z.2 := by
      rw [hlevel]
      omega
    simp only [finiteBusemannEdge, dite_eq_right hx, dite_eq_right hx']

end LPP.Busemann
