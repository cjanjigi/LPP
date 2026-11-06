/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Foundations.BK.NBU
public import ProbabilityBasics.Foundations.BK.Theorem16
public import ProbabilityBasics.Frozen.Foundations.BK.BernoulliProduct
public import ProbabilityBasics.Frozen.Foundations.BK.VdBKDisjointOccurrence
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Theorem 3.3 of van den Berg and Kesten (1985)

* `theorem_3_3` is Theorem 3.3 (3.4): for increasing events `A` and `B` of `{0,1}ⁿ` with
  independent coordinates, `P[A ∘ B] ≤ P[A] P[B]`.

The proof is the paper's. Embed `{0,1}ⁿ` in `ℕⁿ` (`boolToNat`), replace each increasing event
by the smallest increasing subset of `ℕⁿ` containing it (`natLift`), note that `A ∘ B` is
contained in the preimage of the sum of the two lifted sets, that a law on `ℕ` carried by
`{0,1}` is new better than used, and apply Theorem 1.6 (iii).

## References

- J. van den Berg and H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985), Theorem 1.6 and Theorem 3.3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped Pointwise

namespace ProbabilityBasics.BK

variable {n : ℕ}

/-- The embedding of `{0,1}ⁿ` in `ℕⁿ` (p. 562, "we imbed the state space `Ω` in `ℕⁿ`"). -/
private def boolToNat (ω : Fin n → Bool) : Fin n → ℕ := fun i => (ω i).toNat

/-- The smallest increasing subset of `ℕⁿ` containing the image of `A`: the paper's `Ã`
(p. 562). -/
private def natLift (A : Set (Fin n → Bool)) : Set (Fin n → ℕ) :=
  (upperClosure (boolToNat '' A) : Set (Fin n → ℕ))

/-- On `Bool`, `toNat` preserves and reflects the order. -/
private theorem toNat_le_toNat_iff (a b : Bool) : a.toNat ≤ b.toNat ↔ a ≤ b := by
  cases a <;> cases b <;> decide

/-- The embedding preserves and reflects the coordinatewise order. -/
private theorem boolToNat_le_iff {a ω : Fin n → Bool} : boolToNat a ≤ boolToNat ω ↔ a ≤ ω := by
  simp only [Pi.le_def, boolToNat, toNat_le_toNat_iff]

/-- The lifted set `Ã` is increasing. -/
private theorem isUpperSet_natLift (A : Set (Fin n → Bool)) : IsUpperSet (natLift A) :=
  (upperClosure (boolToNat '' A)).upper

/-- Step 2 of the proof (p. 562): lifting an increasing event changes nothing seen from `Ω`.
The paper says only a set of probability `0` is added; for the image measure this is the exact
identity `boolToNat ⁻¹' Ã = A`. -/
private theorem preimage_natLift {A : Set (Fin n → Bool)} (hA : IsUpperSet A) :
    boolToNat ⁻¹' natLift A = A := by
  ext ω
  constructor
  · intro h
    obtain ⟨_, ⟨a, ha, rfl⟩, hle⟩ := mem_upperClosure.1 h
    exact hA (boolToNat_le_iff.1 hle) ha
  · intro h
    exact subset_upperClosure ⟨ω, h, rfl⟩

/-- Step 3 of the proof (p. 562), the half that the inequality needs: `A ∘ B` is contained in
the preimage of `Ã + B̃`. If `K' ⊆ K(ω)` witnesses `ω ∈ A ∘ B`, then `ω` is the sum of the two
configurations with ones `K'` and `K(ω) \ K'`, which have no common one
(the other inclusion is not needed). -/
private theorem vdBKDisjointOccurrence_subset_preimage_add {A B : Set (Fin n → Bool)} :
    vdBKDisjointOccurrence A B ⊆ boolToNat ⁻¹' (natLift A + natLift B) := by
  rintro ω ⟨K', hK', hA, hB⟩
  refine ⟨boolToNat (configOfOnes K'), subset_upperClosure ⟨_, hA, rfl⟩,
    boolToNat (configOfOnes (onesOf ω \ K')), subset_upperClosure ⟨_, hB, rfl⟩, ?_⟩
  funext i
  by_cases hω : ω i = true
  · by_cases hi : i ∈ K' <;> simp [boolToNat, configOfOnes, onesOf, hω, hi]
  · have hi : i ∉ K' := fun h => hω (by simpa [onesOf] using hK' h)
    simp [boolToNat, configOfOnes, onesOf, hω, hi]

/-- The law of `ω_i` seen as a `ℕ`-valued variable (step 1, p. 562). -/
private noncomputable abbrev natLaw (p : unitInterval) : Measure ℕ :=
  (bernoulliMeasure true false p).map Bool.toNat

/-- The image law of a coordinate is carried by `{0, 1}`. -/
private theorem natLaw_Ici_two (p : unitInterval) : natLaw p (Ici 2) = 0 := by
  rw [Measure.map_apply (measurable_of_finite _) measurableSet_Ici]
  have : Bool.toNat ⁻¹' Ici 2 = ∅ := by
    ext b
    cases b <;> simp
  rw [this, measure_empty]

/-- Step 4 of the proof (p. 562): the image law of a coordinate is new better than used. -/
private theorem isNBU_natLaw (p : unitInterval) : IsNBU (natLaw p) :=
  isNBU_of_measure_Ici_two _ (natLaw_Ici_two p)

/-- Step 1 of the proof (p. 562): the image of the product law under the embedding is the
product of the image laws. -/
private theorem map_boolToNat_bernoulliProduct (p : Fin n → unitInterval) :
    (bernoulliProduct p).map boolToNat = Measure.pi fun i => natLaw (p i) :=
  Measure.pi_map_pi (f := fun _ => Bool.toNat) fun _ => (measurable_of_finite _).aemeasurable

/-- For an increasing event `A`, its probability equals the product measure of its lift
(steps 1 and 2 of the proof, p. 562). -/
private theorem bernoulliProduct_eq_pi_natLift (p : Fin n → unitInterval)
    {A : Set (Fin n → Bool)} (hA : IsUpperSet A) :
    bernoulliProduct p A = Measure.pi (fun i => natLaw (p i)) (natLift A) := by
  rw [← map_boolToNat_bernoulliProduct, Measure.map_apply (measurable_of_finite _)
    (MeasurableSet.of_discrete), preimage_natLift hA]

/-- **van den Berg and Kesten (1985), Theorem 3.3** (3.4), p. 562: if `A` and `B` are
increasing events in `{0,1}ⁿ` and the coordinates are independent with `P[ω_i = 1] = p i`, then
`P[A ∘ B] ≤ P[A] P[B]`. The proof is the paper's: `P[A ∘ B] ≤ P[Ã + B̃] ≤ P[Ã] P[B̃] = P[A] P[B]`
by Theorem 1.6 (iii), which applies because laws on `ℕ` carried by `{0,1}` are NBU. -/
theorem theorem_3_3 (p : Fin n → unitInterval) {A B : Set (Fin n → Bool)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    bernoulliProduct p (vdBKDisjointOccurrence A B) ≤
      bernoulliProduct p A * bernoulliProduct p B := by
  have hmeas : MeasurableSet (natLift A + natLift B) := MeasurableSet.of_discrete
  calc bernoulliProduct p (vdBKDisjointOccurrence A B)
      ≤ bernoulliProduct p (boolToNat ⁻¹' (natLift A + natLift B)) :=
        measure_mono vdBKDisjointOccurrence_subset_preimage_add
    _ = Measure.pi (fun i => natLaw (p i)) (natLift A + natLift B) := by
        rw [← Measure.map_apply (measurable_of_finite _) hmeas, map_boolToNat_bernoulliProduct]
    _ ≤ Measure.pi (fun i => natLaw (p i)) (natLift A) *
          Measure.pi (fun i => natLaw (p i)) (natLift B) :=
        theorem_1_6_iii _ (fun i => isNBU_natLaw (p i)) (isUpperSet_natLift A)
          (isUpperSet_natLift B)
    _ = bernoulliProduct p A * bernoulliProduct p B := by
        rw [bernoulliProduct_eq_pi_natLift p hA, bernoulliProduct_eq_pi_natLift p hB]

end ProbabilityBasics.BK
