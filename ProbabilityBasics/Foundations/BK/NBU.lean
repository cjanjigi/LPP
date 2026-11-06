/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# New better than used laws on `ℕ`

A law `m` on `ℕ` is new better than used (NBU) if
`m [s + t, ∞) ≤ m [s, ∞) * m [t, ∞)` for all `s` and `t`. This file contains

* `IsNBU`, this definition in half-line form;
* `isNBU_iff_upperSets`, its equivalence with the paper's (1.1) for `n = 1`
  (an increasing set `A` and an increasing set `B` satisfy
  `m (A + B) ≤ m A * m B`);
* `isNBU_of_measure_Ici_two`, the remark on p. 562 that a law carried by
  `{0, 1}` is NBU;
* `nbu_sumUpper_le_prod`, the one-dimensional core of the proof of Lemma 1.3
  (pp. 557-558).

Only `R = ℕ` is treated.

## References

- J. van den Berg and H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985), (1.1), Lemma 1.3 and Theorem 3.3.
-/

@[expose] public section

open MeasureTheory Set
open scoped Pointwise

namespace ProbabilityBasics.BK

/-- A law `m` on `ℕ` is new better than used (NBU): the tail at `s + t` is at most the
product of the tails at `s` and at `t`. This is the paper's (1.1) for `n = 1` in half-line
form (van den Berg and Kesten (1985), pp. 556-557). -/
def IsNBU (m : Measure ℕ) : Prop :=
  ∀ s t : ℕ, m (Ici (s + t)) ≤ m (Ici s) * m (Ici t)

/-- A nonempty increasing subset of `ℕ` is the half-line starting at its least element. This
is the fact behind "an increasing set in one dimension is a half-line" (p. 558); in `ℕ` the
least element exists, so no supremum argument is needed. -/
private theorem eq_Ici_sInf_of_isUpperSet {A : Set ℕ} (hA : IsUpperSet A) (hne : A.Nonempty) :
    A = Ici (sInf A) := by
  ext x
  refine ⟨fun hx => Nat.sInf_le hx, fun hx => hA hx (Nat.sInf_mem hne)⟩

/-- The sum of two half-lines of `ℕ` is the half-line starting at the sum of the starting
points. -/
private theorem Ici_add_Ici_nat (s t : ℕ) : Ici s + Ici t = Ici (s + t) := by
  ext x
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact add_le_add (Set.mem_Ici.1 ha) (Set.mem_Ici.1 hb)
  · have hx' : s + t ≤ x := hx
    exact ⟨s, le_refl s, x - s, Set.mem_Ici.2 (by omega), show s + (x - s) = x by omega⟩

/-- The half-line form of NBU is the paper's (1.1) for `n = 1`: `m (A + B) ≤ m A * m B` for
all increasing sets `A` and `B` of `ℕ`. The paper (p. 557) states this equivalence without
proof. An increasing subset of `ℕ` is empty or a half-line `Ici s`, and
`Ici s + Ici t = Ici (s + t)`. -/
theorem isNBU_iff_upperSets (m : Measure ℕ) :
    IsNBU m ↔ ∀ A B : Set ℕ, IsUpperSet A → IsUpperSet B → m (A + B) ≤ m A * m B := by
  refine ⟨fun h A B hA hB => ?_, fun h s t => ?_⟩
  · rcases A.eq_empty_or_nonempty with rfl | hAne
    · simp
    rcases B.eq_empty_or_nonempty with rfl | hBne
    · simp
    rw [eq_Ici_sInf_of_isUpperSet hA hAne, eq_Ici_sInf_of_isUpperSet hB hBne,
      Ici_add_Ici_nat]
    exact h _ _
  · have key := h (Ici s) (Ici t) (isUpperSet_Ici s) (isUpperSet_Ici t)
    rwa [Ici_add_Ici_nat] at key

/-- A probability law on `ℕ` carried by `{0, 1}` (that is, with `m [2, ∞) = 0`) is NBU. This is
the remark "a probability measure on `ℕ` with all mass concentrated on `{0, 1}` is always NBU"
in the proof of Theorem 3.3 (p. 562). The paper gives no proof. If `s = 0` or `t = 0` one
factor is `m [0, ∞) = 1`; otherwise `s + t ≥ 2` and the left side vanishes. -/
theorem isNBU_of_measure_Ici_two (m : Measure ℕ) [IsProbabilityMeasure m]
    (h : m (Ici 2) = 0) : IsNBU m := by
  have hzero : (Ici (0 : ℕ)) = univ := by
    ext x
    simp
  intro s t
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · rw [zero_add, hzero, measure_univ, one_mul]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [add_zero, hzero, measure_univ, mul_one]
  have hle : m (Ici (s + t)) ≤ m (Ici 2) := measure_mono (Ici_subset_Ici.2 (by omega))
  rw [h] at hle
  exact hle.trans zero_le

/-- The one-dimensional core of Lemma 1.3 (pp. 557-558). Let `D`
be an increasing subset of `ℕ × ℕ`, a section of the increasing set `A` with the other
coordinates fixed, and let `m` be an NBU probability law. Then the probability that a single
coordinate lies in `{s + t : (s, t) ∈ D}` (made increasing) is at most the `m ⊗ m` measure of
`D`. -/
theorem nbu_sumUpper_le_prod (m : Measure ℕ) [IsProbabilityMeasure m] (hm : IsNBU m)
    {D : Set (ℕ × ℕ)} (hD : IsUpperSet D) :
    m {t | ∃ p ∈ D, p.1 + p.2 ≤ t} ≤ (m.prod m) D := by
  rcases ({t | ∃ p ∈ D, p.1 + p.2 ≤ t} : Set ℕ).eq_empty_or_nonempty with hSe | hSne
  · rw [hSe]
    simp
  -- The set of reachable sums is a half-line with a least element `t₀`, attained at some
  -- `p ∈ D` (step 5, "the supremum is attained").
  obtain ⟨p, hpD, hp⟩ := Nat.sInf_mem hSne
  have half_line : {t | ∃ p ∈ D, p.1 + p.2 ≤ t} ⊆ Ici (sInf {t | ∃ p ∈ D, p.1 + p.2 ≤ t}) :=
    fun _ hx => Nat.sInf_le hx
  -- Step 4: `A` increasing gives the box `[p.1, ∞) × [p.2, ∞)` inside `D`.
  have box_subset : Ici p.1 ×ˢ Ici p.2 ⊆ D :=
    fun q hq => hD (show p ≤ q from ⟨hq.1, hq.2⟩) hpD
  -- Step 6: NBU at `(p.1, p.2)` and the product measure of a box.
  calc m {t | ∃ p ∈ D, p.1 + p.2 ≤ t}
      ≤ m (Ici (sInf {t | ∃ p ∈ D, p.1 + p.2 ≤ t})) := measure_mono half_line
    _ ≤ m (Ici (p.1 + p.2)) := measure_mono (Ici_subset_Ici.2 hp)
    _ ≤ m (Ici p.1) * m (Ici p.2) := hm _ _
    _ = (m.prod m) (Ici p.1 ×ˢ Ici p.2) := (Measure.prod_prod _ _).symm
    _ ≤ (m.prod m) D := measure_mono box_subset

end ProbabilityBasics.BK
