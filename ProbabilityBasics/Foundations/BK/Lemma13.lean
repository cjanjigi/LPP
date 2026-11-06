/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Foundations.BK.Identification
public import ProbabilityBasics.Foundations.BK.NBU
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Marginal

/-!
# Lemma 1.3 of van den Berg and Kesten (1985) for `R = ℕ`

**Lemma 1.3.** Let `μ₁, ..., μₙ` be new better than used (NBU) probability measures on `ℕ`,
and let `i ≠ j` with `μᵢ = μⱼ`. For every increasing set `A` of `ℕ^n`, the product measure
satisfies `μ(A*) ≤ μ(A)`, where `A*` is the image of `A` under `(i, j)`-identification
(`pairImage`).

The paper conditions on the coordinates other than the two merged ones. For fixed values `x`
of those coordinates, the section of `A` is an increasing set `D_x` of `ℕ × ℕ`, and the section
of `A*` is `{(a, b) : a ∈ S_x}` with `S_x = {s + t : (s, t) ∈ D_x}` made increasing. The
one-dimensional inequality `nbu_sumUpper_le_prod` (module `NBU`) gives
`m S_x ≤ (m ⊗ m) D_x`. Integrating over `x` gives the lemma. The integration over all
coordinates but two is done with Mathlib's marginal integrals (`lmarginal`).

Every set of `ℕ^ι` is measurable for a finite index type, so there is no measurability
hypothesis, in contrast with the paper's appeal to Dellacherie and Meyer.

## References

- J. van den Berg and H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985), Lemma 1.3.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityBasics.BK

section Sections

variable {ι : Type*} [DecidableEq ι]

/-- The section of `A` at `x`: the pairs `(a, b)` such that `A` contains the point obtained from
`x` by setting coordinate `i` to `a` and coordinate `j` to `b`. This is the set of values of the
two merged coordinates, given the other coordinates (paper, p. 557 and p. 558, "given
`X₃ = x₃, ..., Xₙ = xₙ`"). -/
private def pairSection (i j : ι) (A : Set (ι → ℕ)) (x : ι → ℕ) : Set (ℕ × ℕ) :=
  {p | Function.update (Function.update x i p.1) j p.2 ∈ A}

/-- If `A` is increasing, so is each of its sections (the paper's use of "A increasing" to move
the other coordinates up to `x`). -/
private theorem isUpperSet_pairSection (i j : ι) {A : Set (ι → ℕ)} (hA : IsUpperSet A)
    (x : ι → ℕ) : IsUpperSet (pairSection i j A x) := by
  intro p q hpq hp
  have hp' : Function.update (Function.update x i p.1) j p.2 ∈ A := hp
  show Function.update (Function.update x i q.1) j q.2 ∈ A
  refine hA (fun k => ?_) hp'
  by_cases hkj : k = j
  · subst hkj
    simpa using (Prod.le_def.1 hpq).2
  · by_cases hki : k = i
    · subst hki
      simpa [hkj] using (Prod.le_def.1 hpq).1
    · simp [hkj, hki]

/-- **Membership in the image, for fixed other coordinates.** For `i ≠ j` and increasing `A`,
setting coordinates `i` and `j` of `x` to `a` and `b` gives a point of the `(i, j)`-image of `A`
exactly when `a` is at least `s + t` for some `(s, t)` in the section of `A` at `x`. The value `b`
plays no role: coordinate `j` is free in `A*`. -/
private theorem update_mem_pairImage_iff {i j : ι} (hij : i ≠ j) {A : Set (ι → ℕ)}
    (hA : IsUpperSet A) (x : ι → ℕ) (a b : ℕ) :
    Function.update (Function.update x i a) j b ∈ pairImage i j A ↔
      ∃ q ∈ pairSection i j A x, q.1 + q.2 ≤ a := by
  constructor
  · rintro ⟨c, hc, hsum, hk⟩
    have hyi : Function.update (Function.update x i a) j b i = a := by simp [hij]
    rw [hyi] at hsum
    refine ⟨(c i, c j), ?_, hsum⟩
    show Function.update (Function.update x i (c i)) j (c j) ∈ A
    refine hA (fun k => ?_) hc
    by_cases hkj : k = j
    · subst hkj
      simp
    · by_cases hki : k = i
      · subst hki
        simp [hkj]
      · simpa [hki, hkj] using hk k hki hkj
  · rintro ⟨q, hq, hqa⟩
    refine ⟨Function.update (Function.update x i q.1) j q.2, hq, ?_, ?_⟩
    · simpa [hij] using hqa
    · intro k hki hkj
      simp [hki, hkj]

end Sections

section Integrals

/-- Two indicator values agree when the points lie in their sets for the same reasons. -/
private theorem indicator_congr_of_iff {α β : Type*} {T : Set α} {S : Set β} {y : α} {a : β}
    (h : y ∈ T ↔ a ∈ S) :
    T.indicator (1 : α → ℝ≥0∞) y = S.indicator (1 : β → ℝ≥0∞) a := by
  by_cases hy : y ∈ T
  · have e1 : T.indicator (1 : α → ℝ≥0∞) y = 1 := Set.indicator_of_mem hy 1
    have e2 : S.indicator (1 : β → ℝ≥0∞) a = 1 := Set.indicator_of_mem (h.1 hy) 1
    rw [e1, e2]
  · have e1 : T.indicator (1 : α → ℝ≥0∞) y = 0 := Set.indicator_of_notMem hy 1
    have e2 : S.indicator (1 : β → ℝ≥0∞) a = 0 :=
      Set.indicator_of_notMem (fun ha => hy (h.2 ha)) 1
    rw [e1, e2]

variable {ι : Type*} [DecidableEq ι]

/-- Integrating the indicator of `T` over the two coordinates `i` and `j` gives `m S` when
`T` is described, in these two coordinates, by the set `S` of the first one alone. The second
integral is the total mass `1` of the probability measure `m`. -/
private theorem lintegral_indicator_eq_left {i j : ι} (m : Measure ℕ) [IsProbabilityMeasure m]
    {T : Set (ι → ℕ)} {S : Set ℕ} (x : ι → ℕ)
    (h : ∀ a b : ℕ, Function.update (Function.update x i a) j b ∈ T ↔ a ∈ S) :
    ∫⁻ a, ∫⁻ b, T.indicator (1 : (ι → ℕ) → ℝ≥0∞) (Function.update (Function.update x i a) j b)
        ∂m ∂m = m S := by
  have hS : MeasurableSet S := (Set.to_countable S).measurableSet
  calc ∫⁻ a, ∫⁻ b, T.indicator (1 : (ι → ℕ) → ℝ≥0∞)
          (Function.update (Function.update x i a) j b) ∂m ∂m
      = ∫⁻ a, S.indicator (1 : ℕ → ℝ≥0∞) a ∂m := by
        refine lintegral_congr fun a => ?_
        calc ∫⁻ b, T.indicator (1 : (ι → ℕ) → ℝ≥0∞)
              (Function.update (Function.update x i a) j b) ∂m
            = ∫⁻ _b, S.indicator (1 : ℕ → ℝ≥0∞) a ∂m :=
              lintegral_congr fun b => indicator_congr_of_iff (h a b)
          _ = S.indicator (1 : ℕ → ℝ≥0∞) a := by
              rw [lintegral_const, measure_univ, mul_one]
    _ = m S := lintegral_indicator_one hS

/-- Integrating the indicator of `T` over the two coordinates `i` and `j` gives the
`m ⊗ m` measure of `U` when `T` is described, in these two coordinates, by the set `U` of
pairs. -/
private theorem lintegral_indicator_eq_prod {i j : ι} (m : Measure ℕ) [IsProbabilityMeasure m]
    {T : Set (ι → ℕ)} {U : Set (ℕ × ℕ)} (x : ι → ℕ)
    (h : ∀ a b : ℕ, Function.update (Function.update x i a) j b ∈ T ↔ (a, b) ∈ U) :
    ∫⁻ a, ∫⁻ b, T.indicator (1 : (ι → ℕ) → ℝ≥0∞) (Function.update (Function.update x i a) j b)
        ∂m ∂m = (m.prod m) U := by
  have hU : MeasurableSet U := (Set.to_countable U).measurableSet
  rw [Measure.prod_apply hU]
  refine lintegral_congr fun a => ?_
  calc ∫⁻ b, T.indicator (1 : (ι → ℕ) → ℝ≥0∞) (Function.update (Function.update x i a) j b) ∂m
      = ∫⁻ b, (Prod.mk a ⁻¹' U).indicator (1 : ℕ → ℝ≥0∞) b ∂m :=
        lintegral_congr fun b => indicator_congr_of_iff (h a b)
    _ = m (Prod.mk a ⁻¹' U) := lintegral_indicator_one (Set.to_countable _).measurableSet

/-- **Marginal integral over two coordinates.** The marginal integral over the
coordinates `i` and `j` is the iterated integral over those two coordinates, with the others
fixed at `x` (Mathlib's `lmarginal_insert` and `lmarginal_singleton`). -/
private theorem lmarginal_pair (μ : ι → Measure ℕ) [∀ i, SigmaFinite (μ i)] {i j : ι}
    (hij : i ≠ j) {f : (ι → ℕ) → ℝ≥0∞} (hf : Measurable f) (x : ι → ℕ) :
    (∫⋯∫⁻_({i, j} : Finset ι), f ∂μ) x =
      ∫⁻ a, ∫⁻ b, f (Function.update (Function.update x i a) j b) ∂μ j ∂μ i := by
  rw [lmarginal_insert f hf (by simpa using hij) x, lmarginal_singleton]

/-- **The inequality for fixed other coordinates `x`.** With the other coordinates fixed, the
`(i, j)`-image has integral `m S_x` over the two merged coordinates, `A` has `(m ⊗ m) D_x`, and
`m S_x ≤ (m ⊗ m) D_x` by the NBU inequality `nbu_sumUpper_le_prod`. -/
private theorem section_integral_le (m : Measure ℕ) [IsProbabilityMeasure m] (hm : IsNBU m)
    {i j : ι} (hij : i ≠ j) {A : Set (ι → ℕ)} (hA : IsUpperSet A) (x : ι → ℕ) :
    ∫⁻ a, ∫⁻ b, (pairImage i j A).indicator (1 : (ι → ℕ) → ℝ≥0∞)
        (Function.update (Function.update x i a) j b) ∂m ∂m ≤
      ∫⁻ a, ∫⁻ b, A.indicator (1 : (ι → ℕ) → ℝ≥0∞)
        (Function.update (Function.update x i a) j b) ∂m ∂m := by
  have hL := lintegral_indicator_eq_left (i := i) (j := j) m
    (T := pairImage i j A) (S := {t | ∃ q ∈ pairSection i j A x, q.1 + q.2 ≤ t}) x
    (update_mem_pairImage_iff hij hA x)
  have hR := lintegral_indicator_eq_prod (i := i) (j := j) m
    (T := A) (U := pairSection i j A x) x (fun _ _ => Iff.rfl)
  rw [hL, hR]
  exact nbu_sumUpper_le_prod m hm (isUpperSet_pairSection i j hA x)

end Integrals

section Main

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Lemma 1.3** of van den Berg and Kesten (1985), pp. 557-558, for `R = ℕ`. Let `μ i` be
NBU probability measures on `ℕ`, indexed by a finite set `ι`, and let `i ≠ j` with `μ i = μ j`.
Then for every increasing set `A` of `ℕ^ι`, the product measure of the image of `A` under
`(i, j)`-identification (`pairImage i j A`) is at most the product measure of `A`.

The proof follows the paper: condition on all coordinates except `i` and `j` (marginal
integrals), compare the two sections by `nbu_sumUpper_le_prod`, and integrate. -/
theorem lemma_1_3 (μ : ι → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, IsNBU (μ i)) {i j : ι} (hij : i ≠ j) (hμij : μ i = μ j)
    {A : Set (ι → ℕ)} (hA : IsUpperSet A) :
    Measure.pi μ (pairImage i j A) ≤ Measure.pi μ A := by
  have meas_set : ∀ S : Set (ι → ℕ), MeasurableSet S :=
    fun S => (Set.to_countable S).measurableSet
  have meas_ind : ∀ S : Set (ι → ℕ), Measurable (S.indicator (1 : (ι → ℕ) → ℝ≥0∞)) :=
    fun S => measurable_one.indicator (meas_set S)
  calc Measure.pi μ (pairImage i j A)
      = ∫⁻ x, (pairImage i j A).indicator (1 : (ι → ℕ) → ℝ≥0∞) x ∂Measure.pi μ :=
        (lintegral_indicator_one (meas_set _)).symm
    _ ≤ ∫⁻ x, A.indicator (1 : (ι → ℕ) → ℝ≥0∞) x ∂Measure.pi μ := by
        refine lintegral_le_of_lmarginal_le ({i, j} : Finset ι) (meas_ind _) (meas_ind _)
          (fun x => ?_)
        rw [lmarginal_pair μ hij (meas_ind _) x, lmarginal_pair μ hij (meas_ind _) x, ← hμij]
        exact section_integral_le (μ i) (hμ i) hij hA x
    _ = Measure.pi μ A := lintegral_indicator_one (meas_set _)

end Main

end ProbabilityBasics.BK
