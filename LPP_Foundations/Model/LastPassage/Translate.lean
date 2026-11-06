/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.Translate
public import LPP_Foundations.Model.LastPassage.Basic

/-! Deterministic covariance of passage times under lattice translations. -/

public section

namespace LPPDifferentiability

/-- Translating the environment translates the endpoints of its passage time. -/
theorem lastPassage_translate (ω : Environment) (v u : Lattice) (d : ℕ × ℕ) :
    lastPassage (fun z => ω (v + z)) u d = lastPassage ω (v + u) d := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage (fun z => ω (v + z)) u d
    calc
      lastPassage (fun z => ω (v + z)) u d =
          pathWeight (fun z => ω (v + z)) p := hp.symm
      _ = pathWeight ω (p.translate v) := (pathWeight_translate ω p v).symm
      _ ≤ lastPassage ω (v + u) d := pathWeight_le_lastPassage ω (p.translate v)
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω (v + u) d
    have hw := pathWeight_translate ω (Path.untranslate v p) v
    rw [Path.translate_untranslate] at hw
    calc
      lastPassage ω (v + u) d = pathWeight ω p := hp.symm
      _ = pathWeight (fun z => ω (v + z)) (Path.untranslate v p) := hw
      _ ≤ lastPassage (fun z => ω (v + z)) u d :=
        pathWeight_le_lastPassage (fun z => ω (v + z)) (Path.untranslate v p)

end LPPDifferentiability
