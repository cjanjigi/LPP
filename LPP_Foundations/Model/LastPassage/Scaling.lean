/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Bounds
public import LPP_Foundations.Model.Paths.Scaling

/-! Positive homogeneity and exact constant shifts for finite passage maxima. -/

@[expose] public section

namespace LPPDifferentiability

/-- Nonnegative scaling commutes with the finite passage maximum, including at zero. -/
theorem lastPassage_smul_of_nonneg (a : ℝ) (ha : 0 ≤ a) (ω : Environment)
    (u : Lattice) (d : ℕ × ℕ) :
    lastPassage (a • ω) u d = a * lastPassage ω u d := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage (a • ω) u d
    calc
      lastPassage (a • ω) u d = pathWeight (a • ω) p := hp.symm
      _ = a * pathWeight ω p := pathWeight_smul a ω p
      _ ≤ a * lastPassage ω u d :=
        mul_le_mul_of_nonneg_left (pathWeight_le_lastPassage ω p) ha
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω u d
    calc
      a * lastPassage ω u d = a * pathWeight ω p := by rw [hp]
      _ = pathWeight (a • ω) p := (pathWeight_smul a ω p).symm
      _ ≤ lastPassage (a • ω) u d := pathWeight_le_lastPassage (a • ω) p

/-- Adding a constant to every site adds the path length times that constant to passage. -/
theorem lastPassage_add_const (ω : Environment) (u : Lattice) (d : ℕ × ℕ) (c : ℝ) :
    lastPassage (ω + fun _ : Lattice => c) u d =
      lastPassage ω u d + ((d.1 + d.2 : ℕ) : ℝ) * c := by
  have hshift (p : Path u d) :
      pathWeight (ω + fun _ : Lattice => c) p =
        pathWeight ω p + ((d.1 + d.2 : ℕ) : ℝ) * c := by
    rw [pathWeight_add, pathWeight_const]
  apply le_antisymm
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage (ω + fun _ : Lattice => c) u d
    calc
      lastPassage (ω + fun _ : Lattice => c) u d =
          pathWeight (ω + fun _ : Lattice => c) p := hp.symm
      _ = pathWeight ω p + ((d.1 + d.2 : ℕ) : ℝ) * c := hshift p
      _ ≤ lastPassage ω u d + ((d.1 + d.2 : ℕ) : ℝ) * c :=
        add_le_add (pathWeight_le_lastPassage ω p) le_rfl
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω u d
    calc
      lastPassage ω u d + ((d.1 + d.2 : ℕ) : ℝ) * c =
          pathWeight ω p + ((d.1 + d.2 : ℕ) : ℝ) * c := by rw [← hp]
      _ = pathWeight (ω + fun _ : Lattice => c) p := (hshift p).symm
      _ ≤ lastPassage (ω + fun _ : Lattice => c) u d :=
        pathWeight_le_lastPassage (ω + fun _ : Lattice => c) p

/-- A nonnegative scaling and an arbitrary constant shift have the expected affine effect. -/
theorem lastPassage_smul_add_const_of_nonneg (a : ℝ) (ha : 0 ≤ a) (ω : Environment)
    (u : Lattice) (d : ℕ × ℕ) (c : ℝ) :
    lastPassage (a • ω + fun _ : Lattice => c) u d =
      a * lastPassage ω u d + ((d.1 + d.2 : ℕ) : ℝ) * c := by
  calc
    lastPassage (a • ω + fun _ : Lattice => c) u d =
        lastPassage (a • ω) u d + ((d.1 + d.2 : ℕ) : ℝ) * c :=
      lastPassage_add_const (a • ω) u d c
    _ = a * lastPassage ω u d + ((d.1 + d.2 : ℕ) : ℝ) * c := by
      rw [lastPassage_smul_of_nonneg a ha ω u d]

end LPPDifferentiability
