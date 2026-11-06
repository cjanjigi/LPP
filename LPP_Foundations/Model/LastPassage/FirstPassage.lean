/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.FirstPassage
public import LPP_Foundations.Model.LastPassage.Bounds
public import LPP_Foundations.Model.Paths.WeightConcat
import LPP_Foundations.Model.Paths.WeightZero
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! First-passage minima of path weights: attainment, the sign identity with
last-passage maxima, and elementary bounds mirroring the last-passage lemmas. The definition is
Martin (2004), equation (2.9). The sign identity is the remark after Theorem 2.4 of
Martin (2004). -/

@[expose] public section

namespace LPPDifferentiability

/-- Every path weight is at least the first-passage minimum over all admissible paths.
Meaning: S(z) is the smallest path weight. Martin (2004), equation (2.9). -/
theorem firstPassage_le_pathWeight (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) : firstPassage ω u d ≤ pathWeight ω p := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩)

/-- Some admissible path attains the first-passage minimum.
Meaning: the minimum in (2.9) is achieved by a path, since the path family is finite and
nonempty. Martin (2004), equation (2.9). -/
theorem exists_pathWeight_eq_firstPassage (ω : Environment) (u : Lattice) (d : ℕ × ℕ) :
    ∃ p : Path u d, pathWeight ω p = firstPassage ω u d := by
  classical
  have h := Finset.min'_mem (Finset.univ.image (pathWeight ω : Path u d → ℝ))
    (Finset.Nonempty.image Finset.univ_nonempty _)
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp h
  exact ⟨p, hp⟩

/-- Zero displacement collects no weight, so the first-passage time over it is zero.
Meaning: a path from z to z has no sites, so its weight is the empty sum. Martin (2004),
equation (2.9), with the path convention of Martin (2004), Section 2, for z1 = z2. -/
@[simp] theorem firstPassage_zero (ω : Environment) (u : Lattice) :
    firstPassage ω u (0, 0) = 0 := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_firstPassage ω u (0, 0)
  exact hp.symm.trans (pathWeight_zero ω u p)

/-- Sign identity: the first-passage time with weights omega equals minus the last-passage
time with the negated weights. Meaning: replacing max by min and X by -X changes only the
sign. Source: the remark after Theorem 2.4 and equation (2.9) of Martin (2004). -/
theorem firstPassage_eq_neg_lastPassage (ω : Environment) (u : Lattice) (d : ℕ × ℕ) :
    firstPassage ω u d = -lastPassage (-ω) u d := by
  apply le_antisymm
  · -- A maximizing path for the negated weights gives a path whose weight is the negated maximum.
    obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage (-ω) u d
    have h1 : pathWeight (-ω) p = -pathWeight ω p := pathWeight_neg ω p
    have h2 : firstPassage ω u d ≤ pathWeight ω p := firstPassage_le_pathWeight ω p
    linarith
  · -- An attaining path for the weights omega bounds the negated maximum from below.
    obtain ⟨p, hp⟩ := exists_pathWeight_eq_firstPassage ω u d
    have h1 : pathWeight (-ω) p = -pathWeight ω p := pathWeight_neg ω p
    have h2 : pathWeight (-ω) p ≤ lastPassage (-ω) u d := pathWeight_le_lastPassage (-ω) p
    linarith

/-- Raising every site weight cannot lower the first-passage time.
Meaning: first passage is monotone in the weights. Martin (2004), equation (2.9). -/
theorem firstPassage_mono (ω η : Environment) (u : Lattice) (d : ℕ × ℕ)
    (h : ∀ z, ω z ≤ η z) :
    firstPassage ω u d ≤ firstPassage η u d := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_firstPassage η u d
  calc
    firstPassage ω u d ≤ pathWeight ω p := firstPassage_le_pathWeight ω p
    _ ≤ pathWeight η p := pathWeight_mono ω η p h
    _ = firstPassage η u d := hp

/-- Constant site weights c give first-passage time equal to the number of steps times c.
Meaning: every admissible path has d1 + d2 sites in the weight sum.
Martin (2004), equation (2.9). -/
theorem firstPassage_const (u : Lattice) (d : ℕ × ℕ) (c : ℝ) :
    firstPassage (fun _ : Lattice => c) u d = ((d.1 + d.2 : ℕ) : ℝ) * c := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_firstPassage (fun _ : Lattice => c) u d
  calc
    firstPassage (fun _ : Lattice => c) u d = pathWeight (fun _ : Lattice => c) p := hp.symm
    _ = ((d.1 + d.2 : ℕ) : ℝ) * c := pathWeight_const c p

/-- A pointwise upper bound on the site weights bounds the first-passage time from above.
Meaning: the minimum is at most the weight of any one path, which is at most the bound.
Martin (2004), equation (2.9). -/
theorem firstPassage_le_const (ω : Environment) (u : Lattice) (d : ℕ × ℕ) (c : ℝ)
    (h : ∀ z, ω z ≤ c) :
    firstPassage ω u d ≤ ((d.1 + d.2 : ℕ) : ℝ) * c := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_firstPassage ω u d
  calc
    firstPassage ω u d = pathWeight ω p := hp.symm
    _ ≤ ((d.1 + d.2 : ℕ) : ℝ) * c := pathWeight_le_const ω p c h

/-- A pointwise lower bound on the site weights bounds the first-passage time from below.
Meaning: the minimum is attained by some path, whose weight is at least the bound.
Martin (2004), equation (2.9). -/
theorem const_le_firstPassage (ω : Environment) (u : Lattice) (d : ℕ × ℕ) (c : ℝ)
    (h : ∀ z, c ≤ ω z) :
    ((d.1 + d.2 : ℕ) : ℝ) * c ≤ firstPassage ω u d := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_firstPassage ω u d
  calc
    ((d.1 + d.2 : ℕ) : ℝ) * c ≤ pathWeight ω p := const_le_pathWeight ω p c h
    _ = firstPassage ω u d := hp

/-- Uniform absolute bounds on the site weights give an absolute bound on first-passage time.
Meaning: the attaining path has at most d1 + d2 sites, each bounded by B in absolute value.
Martin (2004), equation (2.9). -/
theorem firstPassage_abs_le (ω : Environment) (u : Lattice) (d : ℕ × ℕ) (B : ℝ)
    (h : ∀ z, |ω z| ≤ B) :
    |firstPassage ω u d| ≤ ((d.1 + d.2 : ℕ) : ℝ) * B := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_firstPassage ω u d
  rw [← hp]
  exact pathWeight_abs_le ω p B h

/-- Concatenating two minimizing paths gives a path to u + (d + e), so first passage is
subadditive. Meaning: the first-passage time over d + e is at most the sum of the two pieces.
This is the reverse of the superadditivity (2.2) of Martin (2004) for last-passage times,
which concerns the maximum. Martin (2004), equation (2.9). -/
theorem firstPassage_subadditive (ω : Environment) (u : Lattice) (d e : ℕ × ℕ) :
    firstPassage ω u (d + e) ≤
      firstPassage ω u d + firstPassage ω (u + ((d.1 : ℤ), (d.2 : ℤ))) e := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_firstPassage ω u d
  obtain ⟨q, hq⟩ := exists_pathWeight_eq_firstPassage ω (u + ((d.1 : ℤ), (d.2 : ℤ))) e
  calc
    firstPassage ω u (d + e) ≤ pathWeight ω (p.concat q) :=
      firstPassage_le_pathWeight ω (p.concat q)
    _ = pathWeight ω p + pathWeight ω q := pathWeight_concat ω p q
    _ = firstPassage ω u d + firstPassage ω (u + ((d.1 : ℤ), (d.2 : ℤ))) e := by
      rw [hp, hq]

/-- A pointwise perturbation bound on the site weights bounds the change in first-passage
time. Meaning: the difference of two first-passage times is at most the number of steps times
the perturbation bound. Derived from the sign identity and `lastPassage_sub_abs_le`.
Source: Martin (2004), equation (2.9), and the sign remark after Theorem 2.4. -/
theorem firstPassage_sub_abs_le (ω η : Environment) (u : Lattice) (d : ℕ × ℕ) (B : ℝ)
    (h : ∀ z, |ω z - η z| ≤ B) :
    |firstPassage ω u d - firstPassage η u d| ≤ ((d.1 + d.2 : ℕ) : ℝ) * B := by
  have hneg : ∀ z, |(-ω) z - (-η) z| ≤ B := by
    intro z
    have hz : (-ω) z - (-η) z = -(ω z - η z) := by
      simp only [Pi.neg_apply]
      ring
    rw [hz, abs_neg]
    exact h z
  have hlast := lastPassage_sub_abs_le (-ω) (-η) u d B hneg
  rw [firstPassage_eq_neg_lastPassage ω u d, firstPassage_eq_neg_lastPassage η u d]
  have hrw : -lastPassage (-ω) u d - -lastPassage (-η) u d =
      -(lastPassage (-ω) u d - lastPassage (-η) u d) := by
    ring
  rw [hrw, abs_neg]
  exact hlast

end LPPDifferentiability
