/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Basic
public import LPP_Foundations.Model.LastPassage.Bounds
public import LPP_Foundations.Model.LastPassage.Locality
public import LPP_Foundations.Probability.CoordinateLaw
public import ProbabilityBasics.Probability.IdentDistribSublinear
public import LPP_Foundations.Probability.PassageIntegrable
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Floor sandwich with a phase, and box maxima

Martin (2004), Proposition 2.1(i), states the almost-sure passage-time limit for
every direction in the nonnegative orthant. This file provides auxiliary floor/phase
comparisons for passage times and an almost-sure sublinear bound on maxima of absolute
single-site weights over finite sets of offsets.

Contents:
- floor inequalities for the lattice point `floor (n x)` shifted by a phase `theta`;
- the lower bound for a passage time over a box on which the weights are bounded below;
- the pathwise sandwich between passage times at floor points with a phase and at phase zero;
- almost-sure sublinearity of box maxima of single-site weights along any lattice sequence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace LPPDifferentiability

/-! ### Floor inequalities with a phase -/

/-- Lower floor comparison with a phase, one coordinate:
`floor (m x + theta) <= floor ((m + j) x)`, when `x = 0` or `j x` is at least one. -/
private theorem floor_phase_le_floor_coord (x θ : ℝ) (j m : ℕ) (hθ1 : θ < 1)
    (hj : x = 0 ∨ 1 ≤ (j : ℝ) * x) :
    ⌊(m : ℝ) * x + θ⌋₊ ≤ ⌊((m + j : ℕ) : ℝ) * x⌋₊ := by
  rcases hj with h0 | h1
  · subst h0
    have hfloor : ⌊θ⌋₊ = 0 := Nat.floor_eq_zero.mpr hθ1
    simp [hfloor]
  · apply Nat.floor_le_floor
    have e : ((m + j : ℕ) : ℝ) * x = (m : ℝ) * x + (j : ℝ) * x := by
      push_cast
      ring
    rw [e]
    linarith

/-- Adding a phase in `[0, 1)` never lowers a floor. -/
private theorem floor_le_floor_add_phase (a θ : ℝ) (hθ0 : 0 ≤ θ) :
    ⌊a⌋₊ ≤ ⌊a + θ⌋₊ :=
  Nat.floor_le_floor (le_add_of_nonneg_right hθ0)

/-- Adding a phase in `[0, 1)` to a nonnegative number raises its floor by at most one. -/
theorem floor_add_phase_le_floor_add_one (a θ : ℝ) (ha : 0 ≤ a) (hθ1 : θ < 1) :
    ⌊a + θ⌋₊ ≤ ⌊a⌋₊ + 1 := by
  have h : ⌊a + θ⌋₊ ≤ ⌊a + 1⌋₊ := Nat.floor_le_floor (by linarith)
  rwa [Nat.floor_add_one ha] at h

/-- A real number at most `b + D` has floor at most the floor of `b` plus `D`. -/
private theorem floor_le_floor_add_nat (a b : ℝ) (D : ℕ) (hb : 0 ≤ b) (h : a ≤ b + D) :
    ⌊a⌋₊ ≤ ⌊b⌋₊ + D := by
  have h1 : ⌊a⌋₊ ≤ ⌊b + D⌋₊ := Nat.floor_le_floor h
  rwa [Nat.floor_add_natCast hb] at h1

/-- Left floor inequality, both coordinates: the floor at `m x + theta` is at most the floor at
`(m + j) x`. Here `m` is the difference `n - j`, so that `n = m + j`. -/
theorem floor_phase_le_floor (x θ : ℝ × ℝ) (j m : ℕ)
    (hθ1 : 0 ≤ θ.1 ∧ θ.1 < 1) (hθ2 : 0 ≤ θ.2 ∧ θ.2 < 1)
    (hj1 : x.1 = 0 ∨ 1 ≤ (j : ℝ) * x.1) (hj2 : x.2 = 0 ∨ 1 ≤ (j : ℝ) * x.2) :
    (⌊(m : ℝ) * x.1 + θ.1⌋₊, ⌊(m : ℝ) * x.2 + θ.2⌋₊) ≤
      (⌊((m + j : ℕ) : ℝ) * x.1⌋₊, ⌊((m + j : ℕ) : ℝ) * x.2⌋₊) :=
  Prod.mk_le_mk.mpr
    ⟨floor_phase_le_floor_coord x.1 θ.1 j m hθ1.2 hj1,
      floor_phase_le_floor_coord x.2 θ.2 j m hθ2.2 hj2⟩

/-- Right floor inequality, both coordinates: `floor ((m + j) x)` is at most
`floor ((m + j) x + theta)`. -/
theorem floor_le_floor_phase (x θ : ℝ × ℝ) (j m : ℕ)
    (hθ1 : 0 ≤ θ.1) (hθ2 : 0 ≤ θ.2) :
    (⌊((m + j : ℕ) : ℝ) * x.1⌋₊, ⌊((m + j : ℕ) : ℝ) * x.2⌋₊) ≤
      (⌊((m + j : ℕ) : ℝ) * x.1 + θ.1⌋₊, ⌊((m + j : ℕ) : ℝ) * x.2 + θ.2⌋₊) :=
  Prod.mk_le_mk.mpr
    ⟨floor_le_floor_add_phase _ θ.1 hθ1, floor_le_floor_add_phase _ θ.2 hθ2⟩

/-- Upper gap with a phase: `floor ((m + j) x + theta)` exceeds `floor ((m + j) x)` by at
most one in each coordinate, so the right endpoint lies one step above the centre. -/
theorem floor_phase_le_floor_add_one (x θ : ℝ × ℝ) (j m : ℕ)
    (hx1 : 0 ≤ x.1) (hx2 : 0 ≤ x.2) (hθ1 : θ.1 < 1) (hθ2 : θ.2 < 1) :
    (⌊((m + j : ℕ) : ℝ) * x.1 + θ.1⌋₊, ⌊((m + j : ℕ) : ℝ) * x.2 + θ.2⌋₊) ≤
      (⌊((m + j : ℕ) : ℝ) * x.1⌋₊ + 1, ⌊((m + j : ℕ) : ℝ) * x.2⌋₊ + 1) :=
  Prod.mk_le_mk.mpr
    ⟨floor_add_phase_le_floor_add_one _ θ.1 (mul_nonneg (Nat.cast_nonneg _) hx1) hθ1,
      floor_add_phase_le_floor_add_one _ θ.2 (mul_nonneg (Nat.cast_nonneg _) hx2) hθ2⟩

/-- Gap bound for the left endpoint: if `j x_i <= D` in each coordinate, the floor at
`(m + j) x` exceeds the floor at `m x + theta` by at most `D` in each coordinate. -/
theorem floor_phase_gap_le (x θ : ℝ × ℝ) (j m D : ℕ)
    (hx1 : 0 ≤ x.1) (hx2 : 0 ≤ x.2) (hθ1 : 0 ≤ θ.1) (hθ2 : 0 ≤ θ.2)
    (hD1 : (j : ℝ) * x.1 ≤ D) (hD2 : (j : ℝ) * x.2 ≤ D) :
    ⌊((m + j : ℕ) : ℝ) * x.1⌋₊ ≤ ⌊(m : ℝ) * x.1 + θ.1⌋₊ + D ∧
      ⌊((m + j : ℕ) : ℝ) * x.2⌋₊ ≤ ⌊(m : ℝ) * x.2 + θ.2⌋₊ + D := by
  constructor
  · apply floor_le_floor_add_nat _ _ D (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hx1) hθ1)
    have e : ((m + j : ℕ) : ℝ) * x.1 = (m : ℝ) * x.1 + (j : ℝ) * x.1 := by
      push_cast
      ring
    rw [e]
    linarith
  · apply floor_le_floor_add_nat _ _ D (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hx2) hθ2)
    have e : ((m + j : ℕ) : ℝ) * x.2 = (m : ℝ) * x.2 + (j : ℝ) * x.2 := by
      push_cast
      ring
    rw [e]
    linarith

/-- A step in the floor argument: if `x_1 > 0` and `j x_1 >= 1`, then `b_n + e_1 <= b_(n + j)` in
the first coordinate, and the second coordinate is monotone. -/
theorem floor_add_unit_le_floor_fst (x : ℝ × ℝ) (j n : ℕ) (hx1 : 0 < x.1) (hx2 : 0 ≤ x.2)
    (hj : 1 ≤ (j : ℝ) * x.1) :
    (⌊(n : ℝ) * x.1⌋₊ + 1, ⌊(n : ℝ) * x.2⌋₊) ≤
      (⌊((n + j : ℕ) : ℝ) * x.1⌋₊, ⌊((n + j : ℕ) : ℝ) * x.2⌋₊) := by
  refine Prod.mk_le_mk.mpr ⟨?_, ?_⟩
  · have e : ((n + j : ℕ) : ℝ) * x.1 = (n : ℝ) * x.1 + (j : ℝ) * x.1 := by
      push_cast
      ring
    have h : ⌊(n : ℝ) * x.1 + 1⌋₊ ≤ ⌊((n + j : ℕ) : ℝ) * x.1⌋₊ :=
      Nat.floor_le_floor (by rw [e]; linarith)
    rwa [Nat.floor_add_one (mul_nonneg (Nat.cast_nonneg _) hx1.le)] at h
  · exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.le_add_right n j) hx2)

/-- A step in the floor argument, second coordinate: if `x_2 > 0` and `j x_2 >= 1`, then
`b_n + e_2 <= b_(n + j)` in the second coordinate, and the first coordinate is monotone. -/
theorem floor_add_unit_le_floor_snd (x : ℝ × ℝ) (j n : ℕ) (hx2 : 0 < x.2) (hx1 : 0 ≤ x.1)
    (hj : 1 ≤ (j : ℝ) * x.2) :
    (⌊(n : ℝ) * x.1⌋₊, ⌊(n : ℝ) * x.2⌋₊ + 1) ≤
      (⌊((n + j : ℕ) : ℝ) * x.1⌋₊, ⌊((n + j : ℕ) : ℝ) * x.2⌋₊) := by
  refine Prod.mk_le_mk.mpr ⟨?_, ?_⟩
  · exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.le_add_right n j) hx1)
  · have e : ((n + j : ℕ) : ℝ) * x.2 = (n : ℝ) * x.2 + (j : ℝ) * x.2 := by
      push_cast
      ring
    have h : ⌊(n : ℝ) * x.2 + 1⌋₊ ≤ ⌊((n + j : ℕ) : ℝ) * x.2⌋₊ :=
      Nat.floor_le_floor (by rw [e]; linarith)
    rwa [Nat.floor_add_one (mul_nonneg (Nat.cast_nonneg _) hx2.le)] at h

/-! ### Box lower bound -/

/-- Lower bound for a passage time over a box. If every weight `omega z` on the box
`[u, u + d]` is at least `-M`, then the passage time over the box is at least
`-(d_1 + d_2) M`. -/
theorem lastPassage_box_lower_bound (ω : Environment) (u1 u2 : ℤ) (d : ℕ × ℕ) (M : ℝ)
    (h : ∀ z : Lattice, u1 ≤ z.1 → z.1 ≤ u1 + (d.1 : ℤ) → u2 ≤ z.2 → z.2 ≤ u2 + (d.2 : ℤ) →
      -M ≤ ω z) :
    ((d.1 + d.2 : ℕ) : ℝ) * (-M) ≤ lastPassage ω (u1, u2) d := by
  rw [← lastPassage_const (u1, u2) d (-M)]
  apply lastPassage_le_of_leOn
  intro z hz
  have h1 : (u1, u2) ≤ z := hz.1
  have h2 : z ≤ (u1, u2) + ((d.1 : ℤ), (d.2 : ℤ)) := hz.2
  exact h z (Prod.le_def.mp h1).1 (Prod.le_def.mp h2).1 (Prod.le_def.mp h1).2
    (Prod.le_def.mp h2).2

/-- A passage time from the origin is bounded by its length times the sum of the absolute
weights over a box containing the rectangle. -/
theorem abs_lastPassage_le_box_sum (ω : Environment) (a N : ℕ × ℕ)
    (h1 : a.1 ≤ N.1) (h2 : a.2 ≤ N.2) :
    |lastPassage ω 0 a| ≤ ((N.1 + N.2 : ℕ) : ℝ) *
      ∑ z ∈ Finset.Icc ((0 : ℤ), (0 : ℤ)) ((N.1 : ℤ), (N.2 : ℤ)), |ω z| := by
  set B := ∑ z ∈ Finset.Icc ((0 : ℤ), (0 : ℤ)) ((N.1 : ℤ), (N.2 : ℤ)), |ω z| with hB
  have hbox : ∀ z : Lattice, 0 ≤ z → z ≤ ((a.1 : ℤ), (a.2 : ℤ)) → |ω z| ≤ B := by
    intro z hz0 hza
    refine Finset.single_le_sum (f := fun z => |ω z|) (fun _ _ => abs_nonneg _) ?_
    rw [Finset.mem_Icc]
    exact ⟨hz0, hza.trans (Prod.mk_le_mk.mpr ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩)⟩
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hup : lastPassage ω 0 a ≤ ((a.1 + a.2 : ℕ) : ℝ) * B := by
    rw [← lastPassage_const 0 a B]
    apply lastPassage_le_of_leOn
    intro z hz
    exact (abs_le.mp (hbox z hz.1 (by simpa using hz.2))).2
  have hlow : ((a.1 + a.2 : ℕ) : ℝ) * (-B) ≤ lastPassage ω 0 a :=
    lastPassage_box_lower_bound ω 0 0 a B fun z g1 g2 g3 g4 =>
      (abs_le.mp (hbox z ⟨g1, g3⟩ ⟨by simpa using g2, by simpa using g4⟩)).1
  have hN : ((a.1 + a.2 : ℕ) : ℝ) * B ≤ ((N.1 + N.2 : ℕ) : ℝ) * B :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add h1 h2) hB0
  refine abs_le.mpr ⟨?_, hup.trans hN⟩
  linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (a.1 + a.2)) hB0]

/-! ### Pathwise sandwich -/

/-- Deterministic core of the sandwich. Endpoints `A <= B <= C` are coordinatewise ordered,
`C` is at most one step above `B`, and `B` is at most `D` steps above `A`. If the weights are
bounded by `M` in absolute value on the box `b - (D, D) <= z <= b + (1, 1)` with `b = B`,
then passage times satisfy the two-sided bound. -/
private theorem lastPassage_sandwich_core (ω : Environment) (A B C : ℕ × ℕ) (D : ℕ) (M : ℝ)
    (b : Lattice) (hb : b = ((B.1 : ℤ), (B.2 : ℤ)))
    (hAB1 : A.1 ≤ B.1) (hAB2 : A.2 ≤ B.2) (hBC1 : B.1 ≤ C.1) (hBC2 : B.2 ≤ C.2)
    (hC1 : C.1 ≤ B.1 + 1) (hC2 : C.2 ≤ B.2 + 1)
    (hA1 : B.1 ≤ A.1 + D) (hA2 : B.2 ≤ A.2 + D)
    (hM : ∀ z : Lattice, b.1 - D ≤ z.1 → z.1 ≤ b.1 + 1 → b.2 - D ≤ z.2 → z.2 ≤ b.2 + 1 →
      |ω z| ≤ M) :
    lastPassage ω 0 A - 2 * D * M ≤ lastPassage ω 0 B ∧
      lastPassage ω 0 B ≤ lastPassage ω 0 C + 2 * M := by
  have hb1 : b.1 = (B.1 : ℤ) := by rw [hb]
  have hb2 : b.2 = (B.2 : ℤ) := by rw [hb]
  obtain ⟨E, hE1, hE2, hED1, hED2⟩ : ∃ E : ℕ × ℕ, B.1 = A.1 + E.1 ∧ B.2 = A.2 + E.2 ∧
      E.1 ≤ D ∧ E.2 ≤ D :=
    ⟨(B.1 - A.1, B.2 - A.2), by dsimp only; omega, by dsimp only; omega,
      by dsimp only; omega, by dsimp only; omega⟩
  obtain ⟨F, hF1, hF2, hFD1, hFD2⟩ : ∃ F : ℕ × ℕ, C.1 = B.1 + F.1 ∧ C.2 = B.2 + F.2 ∧
      F.1 ≤ 1 ∧ F.2 ≤ 1 :=
    ⟨(C.1 - B.1, C.2 - B.2), by dsimp only; omega, by dsimp only; omega,
      by dsimp only; omega, by dsimp only; omega⟩
  have hAE : A + E = B := Prod.ext (by show A.1 + E.1 = B.1; omega)
    (by show A.2 + E.2 = B.2; omega)
  have hBF : B + F = C := Prod.ext (by show B.1 + F.1 = C.1; omega)
    (by show B.2 + F.2 = C.2; omega)
  have hM0 : 0 ≤ M :=
    (abs_nonneg _).trans (hM b (by omega) (by omega) (by omega) (by omega))
  -- Lower side: superadditivity on `A <= B` with the box `[A, B]`.
  have hsup1 := lastPassage_superadditive ω 0 A E
  rw [zero_add, hAE] at hsup1
  have hbox1 := lastPassage_box_lower_bound ω (A.1 : ℤ) (A.2 : ℤ) E M (fun z g1 g2 g3 g4 =>
    (abs_le.mp (hM z (by omega) (by omega) (by omega) (by omega))).1)
  rw [mul_neg] at hbox1
  have hsE : ((E.1 + E.2 : ℕ) : ℝ) ≤ 2 * D := by
    have : E.1 + E.2 ≤ 2 * D := by omega
    exact_mod_cast this
  have hsE' : ((E.1 + E.2 : ℕ) : ℝ) * M ≤ 2 * D * M := mul_le_mul_of_nonneg_right hsE hM0
  -- Upper side: superadditivity on `B <= C` with the box `[B, C]`.
  have hsup2 := lastPassage_superadditive ω 0 B F
  rw [zero_add, hBF] at hsup2
  have hbox2 := lastPassage_box_lower_bound ω (B.1 : ℤ) (B.2 : ℤ) F M (fun z g1 g2 g3 g4 =>
    (abs_le.mp (hM z (by omega) (by omega) (by omega) (by omega))).1)
  rw [mul_neg] at hbox2
  have hsF : ((F.1 + F.2 : ℕ) : ℝ) ≤ 2 := by
    have : F.1 + F.2 ≤ 2 := by omega
    exact_mod_cast this
  have hsF' : ((F.1 + F.2 : ℕ) : ℝ) * M ≤ 2 * M := mul_le_mul_of_nonneg_right hsF hM0
  constructor
  · linarith
  · linarith

/-- Pathwise sandwich between passage times at floor points with a phase and at phase zero. Let
`b = floor ((m + j) x)` be the box centre, and let `M` bound `|omega z|` on the box
`b - (D, D) <= z <= b + (1, 1)`. Then the passage time at `floor (m x + theta)` minus `2 D M` is at
most the passage time at `b`, and the passage time at `b` is at most the passage time at
`floor ((m + j) x + theta)` plus `2 M`. Here `n = m + j`, and `m` is the difference `n - j`. -/
theorem lastPassage_phase_sandwich (ω : Environment) (x θ : ℝ × ℝ) (j m D : ℕ) (M : ℝ)
    (b : Lattice)
    (hb : b = ((⌊((m + j : ℕ) : ℝ) * x.1⌋₊ : ℤ), (⌊((m + j : ℕ) : ℝ) * x.2⌋₊ : ℤ)))
    (hx1 : 0 ≤ x.1) (hx2 : 0 ≤ x.2)
    (hθ1 : 0 ≤ θ.1 ∧ θ.1 < 1) (hθ2 : 0 ≤ θ.2 ∧ θ.2 < 1)
    (hj1 : x.1 = 0 ∨ 1 ≤ (j : ℝ) * x.1) (hj2 : x.2 = 0 ∨ 1 ≤ (j : ℝ) * x.2)
    (hD1 : (j : ℝ) * x.1 ≤ D) (hD2 : (j : ℝ) * x.2 ≤ D)
    (hM : ∀ z : Lattice, b.1 - D ≤ z.1 → z.1 ≤ b.1 + 1 → b.2 - D ≤ z.2 → z.2 ≤ b.2 + 1 →
      |ω z| ≤ M) :
    lastPassage ω 0 (⌊(m : ℝ) * x.1 + θ.1⌋₊, ⌊(m : ℝ) * x.2 + θ.2⌋₊) - 2 * D * M ≤
        lastPassage ω 0 (⌊((m + j : ℕ) : ℝ) * x.1⌋₊, ⌊((m + j : ℕ) : ℝ) * x.2⌋₊) ∧
      lastPassage ω 0 (⌊((m + j : ℕ) : ℝ) * x.1⌋₊, ⌊((m + j : ℕ) : ℝ) * x.2⌋₊) ≤
        lastPassage ω 0 (⌊((m + j : ℕ) : ℝ) * x.1 + θ.1⌋₊,
          ⌊((m + j : ℕ) : ℝ) * x.2 + θ.2⌋₊) + 2 * M := by
  have hAB := Prod.le_def.mp (floor_phase_le_floor x θ j m hθ1 hθ2 hj1 hj2)
  have hBC := Prod.le_def.mp (floor_le_floor_phase x θ j m hθ1.1 hθ2.1)
  have hCB := Prod.le_def.mp (floor_phase_le_floor_add_one x θ j m hx1 hx2 hθ1.2 hθ2.2)
  have hgap := floor_phase_gap_le x θ j m D hx1 hx2 hθ1.1 hθ2.1 hD1 hD2
  exact lastPassage_sandwich_core ω
    (⌊(m : ℝ) * x.1 + θ.1⌋₊, ⌊(m : ℝ) * x.2 + θ.2⌋₊)
    (⌊((m + j : ℕ) : ℝ) * x.1⌋₊, ⌊((m + j : ℕ) : ℝ) * x.2⌋₊)
    (⌊((m + j : ℕ) : ℝ) * x.1 + θ.1⌋₊, ⌊((m + j : ℕ) : ℝ) * x.2 + θ.2⌋₊)
    D M b hb hAB.1 hAB.2 hBC.1 hBC.2 hCB.1 hCB.2 hgap.1 hgap.2 hM

/-! ### Almost-sure box maxima -/

/-- Box maxima of single-site weights are sublinear almost surely. Let `b` be any sequence of
lattice points, `O` a finite nonempty set of offsets, and `mu` a law with integrable identity
(a first moment). Then almost surely `max_{o in O} |omega (b n + o)| / n` tends to zero. -/
theorem ae_box_max_div_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (b : ℕ → Lattice) (O : Finset Lattice)
    (hO : O.Nonempty) :
    ∀ᵐ ω ∂environmentLaw μ,
      Tendsto (fun n : ℕ => O.sup' hO (fun o => |ω (b n + o)|) / (n : ℝ)) atTop (𝓝 0) := by
  have hsite : ∀ o : Lattice, ∀ᵐ ω ∂environmentLaw μ,
      Tendsto (fun n : ℕ => |ω (b n + o)| / (n : ℝ)) atTop (𝓝 0) := by
    intro o
    have hid : ∀ n : ℕ, IdentDistrib (fun ω : Environment => |ω (b n + o)|)
        (fun ω : Environment => |ω 0|) (environmentLaw μ) (environmentLaw μ) := by
      intro n
      have h : IdentDistrib (fun ω : Environment => ω (b n + o)) (fun ω : Environment => ω 0)
          (environmentLaw μ) (environmentLaw μ) :=
        ⟨(measurable_environment_eval _).aemeasurable,
          (measurable_environment_eval _).aemeasurable,
          by rw [environmentLaw_map_eval, environmentLaw_map_eval]⟩
      exact h.comp continuous_abs.measurable
    exact ae_tendsto_identDistrib_div_nat (integrable_environment_eval μ hμ 0).abs hid
  have hall : ∀ᵐ ω ∂environmentLaw μ, ∀ o ∈ O,
      Tendsto (fun n : ℕ => |ω (b n + o)| / (n : ℝ)) atTop (𝓝 0) := by
    rw [Filter.eventually_all_finset]
    exact fun o _ => hsite o
  filter_upwards [hall] with ω hω
  have hsum : Tendsto (fun n : ℕ => ∑ o ∈ O, |ω (b n + o)| / (n : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_finsetSum O (fun o ho => hω o ho)
    simpa using h
  have hnonneg : ∀ n : ℕ, 0 ≤ O.sup' hO (fun o => |ω (b n + o)|) / (n : ℝ) := fun n =>
    div_nonneg (le_trans (abs_nonneg _) (Finset.le_sup' (fun o => |ω (b n + o)|) hO.choose_spec))
      (Nat.cast_nonneg n)
  refine squeeze_zero hnonneg (fun n => ?_) hsum
  rw [← Finset.sum_div]
  gcongr
  apply Finset.sup'_le
  intro o ho
  exact Finset.single_le_sum (f := fun o => |ω (b n + o)|) (fun o _ => abs_nonneg _) ho

end LPPDifferentiability
