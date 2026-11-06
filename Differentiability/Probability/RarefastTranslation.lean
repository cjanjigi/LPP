/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.TranslationEquiv
public import LPP_Foundations.Model.Paths.Translate
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # Translation invariance of path events

A path event "some path `q` from `u` with displacement `e` satisfies a condition on
`u`, `e`, its vertices and its weight" has the same probability after every vertex is
moved by a lattice vector `-v`, because the environment law is invariant under the
translation `ω ↦ ω (v + ·)` (`measurePreserving_environmentTranslationEquiv`). Two
instances are used in the proof of Proposition 5.9 of the differentiability preprint (the
arbitrary-endpoints proposition) and one in (6.4) of the preprint:

* crossings of a strip around a lattice point `v` starting on the level of `v`, moved to
  crossings of the strip around the origin starting on level `0`;
* paths in the translate `z0 + ℛ` of a region, moved to paths in `ℛ`.

## References

* C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint.
-/

public section

open MeasureTheory

namespace LPPDifferentiability

/-- **Translation invariance of a path event.** Moving the start point and every vertex of
the witnessing path by `-v` does not change the probability of the event. -/
theorem measureReal_path_event_translate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : Lattice)
    (Φ : (u : Lattice) → (e : ℕ × ℕ) → (Fin (e.1 + e.2 + 1) → Lattice) → ℝ → Prop) :
    (environmentLaw μ).real {ω : Environment | ∃ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
        Φ (-v + u) e (fun i => -v + q.vertex i) (pathWeight ω q)} =
      (environmentLaw μ).real {ω : Environment | ∃ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
        Φ u e q.vertex (pathWeight ω q)} := by
  set S : Set Environment := {ω : Environment | ∃ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
    Φ u e q.vertex (pathWeight ω q)} with hS
  have hset : {ω : Environment | ∃ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
        Φ (-v + u) e (fun i => -v + q.vertex i) (pathWeight ω q)} =
      environmentTranslationEquiv v ⁻¹' S := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hS]
    constructor
    · rintro ⟨u, e, q, h⟩
      refine ⟨-v + u, e, q.translate (-v), ?_⟩
      have hw : pathWeight (environmentTranslationEquiv v ω) (q.translate (-v)) =
          pathWeight ω q := by
        unfold pathWeight
        simp only [environmentTranslationEquiv_apply, Path.translate_vertex,
          add_neg_cancel_left]
      rw [hw]
      exact h
    · rintro ⟨u, e, q, h⟩
      refine ⟨v + u, e, q.translate v, ?_⟩
      have h1 : -v + (v + u) = u := neg_add_cancel_left v u
      have h2 : (fun i => -v + (q.translate v).vertex i) = q.vertex := by
        funext i
        simp only [Path.translate_vertex, neg_add_cancel_left]
      have h3 : pathWeight ω (q.translate v) =
          pathWeight (environmentTranslationEquiv v ω) q := rfl
      rw [h1, h2, h3]
      exact h
  rw [hset, measureReal_def, measureReal_def,
    (measurePreserving_environmentTranslationEquiv μ v).measure_preimage_equiv S]

private theorem transverse_neg_add (a : ℝ) (v z : Lattice) :
    (1 - a) * (((-v + z).1 : ℤ) : ℝ) - a * (((-v + z).2 : ℤ) : ℝ) =
      ((1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)) - ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ)) := by
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, Int.cast_add,
    Int.cast_neg]
  ring

private theorem level_neg_add (v z : Lattice) :
    (((-v + z).1 : ℤ) : ℝ) + (((-v + z).2 : ℤ) : ℝ) =
      ((z.1 : ℝ) + (z.2 : ℝ)) - ((v.1 : ℝ) + (v.2 : ℝ)) := by
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, Int.cast_add,
    Int.cast_neg]
  ring

/-- **Strip crossings around a lattice point.** Crossings that start on the level of `v`,
have length `n` and stay within transverse distance `B` of `v`, with a condition `Q` on
their displacement vector and weight, have the probability of the same crossings
around the origin starting on level `0`. -/
theorem measureReal_strip_crossing_translate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a B : ℝ) (n : ℕ) (v : Lattice) (Q : Lattice → ℝ → Prop) :
    (environmentLaw μ).real {ω : Environment |
      ∃ u : Lattice, u.1 + u.2 = v.1 + v.2 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
        (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ) -
          ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ))| ≤ B) ∧
        Q (q.vertex (Fin.last (e.1 + e.2)) - u) (pathWeight ω q)} =
    (environmentLaw μ).real {ω : Environment |
      ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
        (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ B) ∧
        Q (q.vertex (Fin.last (e.1 + e.2)) - u) (pathWeight ω q)} := by
  let Φ : (u : Lattice) → (e : ℕ × ℕ) → (Fin (e.1 + e.2 + 1) → Lattice) → ℝ → Prop :=
    fun u e x W => u.1 + u.2 = 0 ∧ e.1 + e.2 = n ∧
      (∀ i, |(1 - a) * ((x i).1 : ℝ) - a * ((x i).2 : ℝ)| ≤ B) ∧
      Q (x (Fin.last (e.1 + e.2)) - u) W
  have h := measureReal_path_event_translate μ v Φ
  have hL : {ω : Environment |
      ∃ u : Lattice, u.1 + u.2 = v.1 + v.2 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
        (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ) -
          ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ))| ≤ B) ∧
        Q (q.vertex (Fin.last (e.1 + e.2)) - u) (pathWeight ω q)} =
      {ω : Environment | ∃ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
        Φ (-v + u) e (fun i => -v + q.vertex i) (pathWeight ω q)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Φ, transverse_neg_add, add_sub_add_left_eq_sub]
    constructor
    · rintro ⟨u, hu, e, he, q, hr, hQ⟩
      refine ⟨u, e, q, ?_, he, hr, hQ⟩
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
      omega
    · rintro ⟨u, e, q, hu, he, hr, hQ⟩
      refine ⟨u, ?_, e, he, q, hr, hQ⟩
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] at hu
      omega
  have hR : {ω : Environment |
      ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
        (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ B) ∧
        Q (q.vertex (Fin.last (e.1 + e.2)) - u) (pathWeight ω q)} =
      {ω : Environment | ∃ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
        Φ u e q.vertex (pathWeight ω q)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Φ]
    constructor
    · rintro ⟨u, hu, e, he, q, hr, hQ⟩
      exact ⟨u, e, q, hu, he, hr, hQ⟩
    · rintro ⟨u, e, q, hu, he, hr, hQ⟩
      exact ⟨u, hu, e, he, q, hr, hQ⟩
  rw [hL, hR, h]

/-- **Translates of a region.** Paths all of whose vertices lie within level distance `X`
and transverse distance `Y` of `z0`, with `min (Hdef₋, Hdef₊) < Z`, have the probability
of the same paths around the origin. -/
theorem measureReal_region_defect_translate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a G0 dl dr X Y Z : ℝ) (z0 : Lattice) :
    (environmentLaw μ).real {ω : Environment |
      ∃ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
        (∀ i, |((q.vertex i).1 : ℝ) + ((q.vertex i).2 : ℝ) - ((z0.1 : ℝ) + (z0.2 : ℝ))| ≤ X ∧
          |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ) -
            ((1 - a) * (z0.1 : ℝ) - a * (z0.2 : ℝ))| ≤ Y) ∧
        min (G0 * ((e.1 : ℝ) + (e.2 : ℝ)) + dl * ((1 - a) * (e.1 : ℝ) - a * (e.2 : ℝ)) -
            pathWeight ω q)
          (G0 * ((e.1 : ℝ) + (e.2 : ℝ)) + dr * ((1 - a) * (e.1 : ℝ) - a * (e.2 : ℝ)) -
            pathWeight ω q) < Z} =
    (environmentLaw μ).real {ω : Environment |
      ∃ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
        (∀ i, |((q.vertex i).1 : ℝ) + ((q.vertex i).2 : ℝ)| ≤ X ∧
          |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ Y) ∧
        min (G0 * ((e.1 : ℝ) + (e.2 : ℝ)) + dl * ((1 - a) * (e.1 : ℝ) - a * (e.2 : ℝ)) -
            pathWeight ω q)
          (G0 * ((e.1 : ℝ) + (e.2 : ℝ)) + dr * ((1 - a) * (e.1 : ℝ) - a * (e.2 : ℝ)) -
            pathWeight ω q) < Z} := by
  let Φ : (u : Lattice) → (e : ℕ × ℕ) → (Fin (e.1 + e.2 + 1) → Lattice) → ℝ → Prop :=
    fun _ e x W =>
      (∀ i, |((x i).1 : ℝ) + ((x i).2 : ℝ)| ≤ X ∧
        |(1 - a) * ((x i).1 : ℝ) - a * ((x i).2 : ℝ)| ≤ Y) ∧
      min (G0 * ((e.1 : ℝ) + (e.2 : ℝ)) + dl * ((1 - a) * (e.1 : ℝ) - a * (e.2 : ℝ)) - W)
        (G0 * ((e.1 : ℝ) + (e.2 : ℝ)) + dr * ((1 - a) * (e.1 : ℝ) - a * (e.2 : ℝ)) - W) < Z
  have h := measureReal_path_event_translate μ z0 Φ
  simp only [Φ, transverse_neg_add, level_neg_add] at h
  exact h

end LPPDifferentiability
