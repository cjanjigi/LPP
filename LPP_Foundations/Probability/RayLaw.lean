/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.RayProcess

/-!
# Joint laws of signed passage columns and block sequences

The complete positive-length columns have translation-invariant laws. Every
fixed-block sequence has a stationary pushforward law, and its literal left
shift is ergodic for nonzero block displacement. Arbitrary starting points
cover both the initial block and the positive-index tail in Liggett (1985), (1.9).
-/

public section

open MeasureTheory

namespace LPPDifferentiability

/-- Measurability of the whole positive-length signed passage column. -/
theorem measurable_neg_lastPassage_column (u : Lattice) (a : ℕ × ℕ) :
    Measurable (fun ω : Environment => fun j : ℕ =>
      -lastPassage ω u ((j + 1) • a)) :=
  Measurable.of_eval (fun j => (measurable_lastPassage u ((j + 1) • a)).neg)

/-- Translating the start preserves the joint law of all positive lengths. -/
theorem environmentLaw_map_neg_lastPassage_column (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (a : ℕ × ℕ) (u v : Lattice) :
    (environmentLaw μ).map (fun ω : Environment => fun j : ℕ =>
      -lastPassage ω (v + u) ((j + 1) • a)) =
    (environmentLaw μ).map (fun ω : Environment => fun j : ℕ =>
      -lastPassage ω u ((j + 1) • a)) := by
  have htrans : Measurable (fun ω : Environment => fun z => ω (v + z)) :=
    Measurable.of_eval (fun z => measurable_pi_apply (v + z))
  calc
    _ = (environmentLaw μ).map ((fun ω : Environment => fun j : ℕ =>
        -lastPassage ω u ((j + 1) • a)) ∘
        (fun ω : Environment => fun z => ω (v + z))) := by
      congr 1
      funext ω j
      simp only [Function.comp_apply, lastPassage_translate]
    _ = ((environmentLaw μ).map (fun ω : Environment => fun z => ω (v + z))).map
        (fun ω : Environment => fun j : ℕ => -lastPassage ω u ((j + 1) • a)) :=
      (Measure.map_map (measurable_neg_lastPassage_column u a) htrans).symm
    _ = _ := by rw [environmentLaw_map_translation]

/-- The adjacent complete-column law in Liggett (1985), (1.8), indexed by j+1. -/
theorem environmentLaw_map_neg_lastPassage_ray_column (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (a : ℕ × ℕ) (m : ℕ) :
    (environmentLaw μ).map (fun ω : Environment => fun j : ℕ =>
      -lastPassage ω ((m + 1) • ((a.1 : ℤ), (a.2 : ℤ))) ((j + 1) • a)) =
    (environmentLaw μ).map (fun ω : Environment => fun j : ℕ =>
      -lastPassage ω (m • ((a.1 : ℤ), (a.2 : ℤ))) ((j + 1) • a)) := by
  simpa only [add_nsmul, one_nsmul, add_comm] using
    environmentLaw_map_neg_lastPassage_column μ a
      (m • ((a.1 : ℤ), (a.2 : ℤ))) ((a.1 : ℤ), (a.2 : ℤ))

/-- Measurability of the complete sequence of fixed-displacement signed blocks. -/
theorem measurable_neg_lastPassage_blocks (u : Lattice) (d : ℕ × ℕ) :
    Measurable (fun ω : Environment => fun n : ℕ =>
      -lastPassage ω (n • ((d.1 : ℤ), (d.2 : ℤ)) + u) d) :=
  Measurable.of_eval (fun n =>
    (measurable_lastPassage (n • ((d.1 : ℤ), (d.2 : ℤ)) + u) d).neg)

/-- Translating by one whole block intertwines its sequence map with left shift. -/
theorem neg_lastPassage_blocks_semiconj (u : Lattice) (d : ℕ × ℕ) :
    Function.Semiconj
      (fun ω : Environment => fun n : ℕ =>
        -lastPassage ω (n • ((d.1 : ℤ), (d.2 : ℤ)) + u) d)
      (fun ω : Environment => fun z => ω (((d.1 : ℤ), (d.2 : ℤ)) + z))
      (fun x : ℕ → ℝ => fun n => x (n + 1)) := by
  intro ω
  funext n
  change -lastPassage (fun z => ω (((d.1 : ℤ), (d.2 : ℤ)) + z))
    (n • ((d.1 : ℤ), (d.2 : ℤ)) + u) d =
    -lastPassage ω ((n + 1) • ((d.1 : ℤ), (d.2 : ℤ)) + u) d
  rw [lastPassage_translate]
  congr 2
  simp only [add_nsmul, one_nsmul]
  abel

/-- The literal left shift preserves the actual pushed-forward block law. -/
theorem measurePreserving_neg_lastPassage_blocks_shift (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (u : Lattice) (d : ℕ × ℕ) :
    MeasurePreserving (fun x : ℕ → ℝ => fun n => x (n + 1))
      ((environmentLaw μ).map (fun ω : Environment => fun n : ℕ =>
        -lastPassage ω (n • ((d.1 : ℤ), (d.2 : ℤ)) + u) d))
      ((environmentLaw μ).map (fun ω : Environment => fun n : ℕ =>
        -lastPassage ω (n • ((d.1 : ℤ), (d.2 : ℤ)) + u) d)) := by
  have hmap : MeasurePreserving
      (fun ω : Environment => fun n : ℕ =>
        -lastPassage ω (n • ((d.1 : ℤ), (d.2 : ℤ)) + u) d)
      (environmentLaw μ)
      ((environmentLaw μ).map (fun ω : Environment => fun n : ℕ =>
        -lastPassage ω (n • ((d.1 : ℤ), (d.2 : ℤ)) + u) d)) :=
    ⟨measurable_neg_lastPassage_blocks u d, rfl⟩
  exact hmap.of_semiconj
    (measurePreserving_environment_translation μ ((d.1 : ℤ), (d.2 : ℤ)))
    (neg_lastPassage_blocks_semiconj u d)
    (Measurable.of_eval (fun n => measurable_pi_apply (n + 1)))

/-- Every nonzero fixed-displacement signed block law is ergodic under left shift. -/
theorem ergodic_neg_lastPassage_blocks_shift (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (u : Lattice) (d : ℕ × ℕ) (hd : d ≠ 0) :
    Ergodic (fun x : ℕ → ℝ => fun n => x (n + 1))
      ((environmentLaw μ).map (fun ω : Environment => fun n : ℕ =>
        -lastPassage ω (n • ((d.1 : ℤ), (d.2 : ℤ)) + u) d)) := by
  have hmap : MeasurePreserving
      (fun ω : Environment => fun n : ℕ =>
        -lastPassage ω (n • ((d.1 : ℤ), (d.2 : ℤ)) + u) d)
      (environmentLaw μ)
      ((environmentLaw μ).map (fun ω : Environment => fun n : ℕ =>
        -lastPassage ω (n • ((d.1 : ℤ), (d.2 : ℤ)) + u) d)) :=
    ⟨measurable_neg_lastPassage_blocks u d, rfl⟩
  exact hmap.ergodic_of_ergodic_semiconj
    (ergodic_environment_natRay_translation μ d hd)
    (Measurable.of_eval (fun n => measurable_pi_apply (n + 1)))
    (neg_lastPassage_blocks_semiconj u d)

/-- Casting the natural multiple `k • a` of a ray direction to integers gives the integer
multiple of the cast direction. -/
theorem cast_natRay_smul (a : ℕ × ℕ) (k : ℕ) :
    ((((k • a).1 : ℕ) : ℤ), (((k • a).2 : ℕ) : ℤ)) =
      k • ((a.1 : ℤ), (a.2 : ℤ)) := by
  ext <;> simp

private theorem natRay_smul_ne_zero (a : ℕ × ℕ) (ha : a ≠ 0)
    (k : ℕ) (hk : 0 < k) : k • a ≠ 0 := by
  intro h
  apply ha
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  change k * a.1 = 0 at h₁
  change k * a.2 = 0 at h₂
  exact Prod.ext ((mul_eq_zero.mp h₁).resolve_left (Nat.ne_of_gt hk))
    ((mul_eq_zero.mp h₂).resolve_left (Nat.ne_of_gt hk))

/-- Every ray block sequence is stationary; q=1 is exactly the tail `n ≥ 1`. -/
theorem measurePreserving_neg_lastPassage_ray_blocks_shift (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (a : ℕ × ℕ) (k q : ℕ) :
    MeasurePreserving (fun x : ℕ → ℝ => fun n => x (n + 1))
      ((environmentLaw μ).map (fun ω : Environment => fun n : ℕ =>
        -lastPassage ω (((n + q) * k) • ((a.1 : ℤ), (a.2 : ℤ))) (k • a)))
      ((environmentLaw μ).map (fun ω : Environment => fun n : ℕ =>
        -lastPassage ω (((n + q) * k) • ((a.1 : ℤ), (a.2 : ℤ))) (k • a))) := by
  simpa only [cast_natRay_smul, ← mul_smul, ← add_nsmul, ← Nat.add_mul] using
    measurePreserving_neg_lastPassage_blocks_shift μ
      ((q * k) • ((a.1 : ℤ), (a.2 : ℤ))) (k • a)

/-- All positive ray block sizes are ergodic, including the tail `q = 1`. -/
theorem ergodic_neg_lastPassage_ray_blocks_shift (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (a : ℕ × ℕ) (ha : a ≠ 0)
    (k : ℕ) (hk : 0 < k) (q : ℕ) :
    Ergodic (fun x : ℕ → ℝ => fun n => x (n + 1))
      ((environmentLaw μ).map (fun ω : Environment => fun n : ℕ =>
        -lastPassage ω (((n + q) * k) • ((a.1 : ℤ), (a.2 : ℤ))) (k • a))) := by
  simpa only [cast_natRay_smul, ← mul_smul, ← add_nsmul, ← Nat.add_mul] using
    ergodic_neg_lastPassage_blocks_shift μ
      ((q * k) • ((a.1 : ℤ), (a.2 : ℤ))) (k • a) (natRay_smul_ne_zero a ha k hk)

end LPPDifferentiability
