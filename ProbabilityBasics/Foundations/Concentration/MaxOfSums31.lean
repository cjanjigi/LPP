/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Foundations.Concentration.MaxOfSumsProduct

/-!
# Martin (2004), Lemma 3.1, on a general probability space

This is Lemma 3.1 of Martin (2004). It is general probability and does not depend on the LPP
model.

Let `Y i`, `i : ι`, be independent measurable real random variables on a probability space, each
bounded by `L` in absolute value almost surely, with `ι` finite. Let `C` be a nonempty family of
subsets of `ι`, each of size at most `R`, and let `Z` be the maximum over `c ∈ C` of the sums
`∑ i ∈ c, Y i`.

## Main results

* `two_mul_exp_neg_div_sixteen_le_exp_sixty_four_sub_div_sixty_four`: the scalar comparison
  `2 exp (-v / 16) ≤ exp (64 - v / 64)` for `v ≥ 0`.
* `measureReal_abs_sup_sum_sub_integral_ge_le_two_mul_exp`: for `L > 0`, `R > 0` and `u ≥ 0`,
  `P (u ≤ |Z - E Z|) ≤ 2 exp (-u² / (16 R L²))`. The index type is reindexed by `Fin n`, the joint
  law becomes `Measure.pi` of the marginals, and the product-space bound of `MaxOfSumsProduct`
  applies.
* `martin_lemma_3_1`: Martin's printed bound `P (u ≤ |Z - E Z|) ≤ exp (64 - u² / (64 R L²))` for
  every `u > 0`, with no sign condition on `L` and `R` a natural number.

## References

- J. B. Martin, *Limiting shape for directed percolation models*, Ann. Probab. 32 (2004),
  Lemma 3.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace ProbabilityBasics.Concentration

section MaxOfSums31

/-! ### The scalar comparison -/

/-- Scalar comparison with Martin's displayed constant: `2 exp (-v / 16) ≤ exp (64 - v / 64)` for
`v ≥ 0`. It holds because `2 ≤ e⁶⁴` (from `x + 1 ≤ eˣ`) and `-v / 16 ≤ -(v / 64)`. -/
theorem two_mul_exp_neg_div_sixteen_le_exp_sixty_four_sub_div_sixty_four
    (v : ℝ) (hv : 0 ≤ v) : 2 * Real.exp (-v / 16) ≤ Real.exp (64 - v / 64) := by
  have h2 : (2 : ℝ) ≤ Real.exp 64 := by
    have h1 : (64 : ℝ) + 1 ≤ Real.exp 64 := Real.add_one_le_exp 64
    linarith
  have h3 : Real.exp (-v / 16) ≤ Real.exp (-(v / 64)) :=
    Real.exp_le_exp.2 (by linarith)
  calc 2 * Real.exp (-v / 16) ≤ Real.exp 64 * Real.exp (-(v / 64)) :=
        mul_le_mul h2 h3 (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (64 - v / 64) := by rw [← Real.exp_add]; ring_nf

/-! ### Measurability of the clamped maximum -/

/-- The maximum over `C` of the sums of the clamped coordinates is measurable: it is a finite
supremum of finite sums of measurable functions of the coordinates. -/
private theorem measurable_clampedMax {n : ℕ} (C : Finset (Finset (Fin n))) (hC : C.Nonempty)
    (L : ℝ) :
    Measurable fun y : Fin n → ℝ => C.sup' hC (fun c => ∑ j ∈ c, max (-L) (min (y j) L)) := by
  have hj : ∀ j : Fin n, Measurable fun y : Fin n → ℝ => max (-L) (min (y j) L) := fun j => by
    fun_prop
  have e : (fun y : Fin n → ℝ => C.sup' hC (fun c => ∑ j ∈ c, max (-L) (min (y j) L))) =
      C.sup' hC (fun c (y : Fin n → ℝ) => ∑ j ∈ c, max (-L) (min (y j) L)) := by
    funext y
    simp only [Finset.sup'_apply]
  rw [e]
  exact Finset.measurable_sup' hC fun c _ => Finset.measurable_sum _ fun j _ => hj j

/-! ### The stronger bound on a general probability space -/

/-- The stronger form of Martin (2004), Lemma 3.1, on a general probability space. For independent
measurable `Y i`, `i : ι` finite, with `|Y i| ≤ L` almost surely and `L > 0`, a natural number
`R > 0`, a nonempty family `C` of sets of size at most `R`, and `u ≥ 0`, the maximum `Z` of the set
sums satisfies `P (u ≤ |Z - E Z|) ≤ 2 exp (-u² / (16 R L²))`. The proof reindexes `ι` by `Fin n`,
identifies the joint law with the product of the marginals, notes that `Z` equals the clamped
maximum almost surely, transfers the event and the mean to the product space and applies
`measureReal_abs_sup_sum_sub_integral_ge_le_pi`. -/
theorem measureReal_abs_sup_sum_sub_integral_ge_le_two_mul_exp {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ι : Type*} [Fintype ι]
    (Y : ι → Ω → ℝ) (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    {L : ℝ} (hL0 : 0 < L) (hL : ∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ L)
    (C : Finset (Finset ι)) (hC : C.Nonempty) {R : ℕ} (hR0 : 0 < R)
    (hR : ∀ c ∈ C, c.card ≤ R) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u ≤ |C.sup' hC (fun c => ∑ i ∈ c, Y i ω) -
        ∫ η, C.sup' hC (fun c => ∑ i ∈ c, Y i η) ∂P|} ≤
      2 * Real.exp (-u ^ 2 / (16 * R * L ^ 2)) := by
  -- Reindex the finite index type by `Fin n`.
  obtain ⟨n, ⟨e⟩⟩ : ∃ n : ℕ, Nonempty (ι ≃ Fin n) := ⟨_, ⟨Fintype.equivFin ι⟩⟩
  obtain ⟨W, hW⟩ : ∃ W : Ω → Fin n → ℝ, ∀ ω j, W ω j = Y (e.symm j) ω := ⟨_, fun _ _ => rfl⟩
  have hWm : Measurable W := by
    refine Measurable.of_eval fun j => ?_
    have h : (fun ω => W ω j) = Y (e.symm j) := funext fun ω => hW ω j
    rw [h]
    exact hY _
  -- The joint law of the reindexed variables is the product of the marginals.
  have hind' : iIndepFun (fun j => Y (e.symm j)) P := hind.precomp e.symm.injective
  have hlaw : P.map W = Measure.pi (fun j => P.map (Y (e.symm j))) := by
    have h := (iIndepFun_iff_map_fun_eq_pi_map (fun j => (hY (e.symm j)).aemeasurable)).1 hind'
    have hWeq : W = fun ω j => Y (e.symm j) ω := funext fun ω => funext (hW ω)
    rw [hWeq]
    exact h
  -- The family and the clamped maximum on `Fin n`.
  have hC' : (C.image (Finset.map e.toEmbedding)).Nonempty := hC.image _
  have hR' : ∀ c ∈ C.image (Finset.map e.toEmbedding), c.card ≤ R := by
    intro c hc
    obtain ⟨c0, hc0, rfl⟩ := Finset.mem_image.1 hc
    rw [Finset.card_map]
    exact hR c0 hc0
  obtain ⟨F, hFdef⟩ : ∃ F : (Fin n → ℝ) → ℝ, ∀ y, F y =
      (C.image (Finset.map e.toEmbedding)).sup' hC'
        (fun c => ∑ j ∈ c, max (-L) (min (y j) L)) := ⟨_, fun _ => rfl⟩
  have hFm : Measurable F := by
    have h : F = fun y => (C.image (Finset.map e.toEmbedding)).sup' hC'
        (fun c => ∑ j ∈ c, max (-L) (min (y j) L)) := funext hFdef
    rw [h]
    exact measurable_clampedMax _ hC' L
  -- Almost surely every `|Y i| ≤ L`, so the clamp changes nothing and `F (W ω) = Z ω`.
  have hae : ∀ᵐ ω ∂P, F (W ω) = C.sup' hC (fun c => ∑ i ∈ c, Y i ω) := by
    filter_upwards [ae_all_iff.2 hL] with ω hω
    rw [hFdef, Finset.sup'_image]
    refine Finset.sup'_congr hC rfl fun c _ => ?_
    simp only [Function.comp_apply, Finset.sum_map, Equiv.coe_toEmbedding, hW,
      Equiv.symm_apply_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := abs_le.1 (hω i)
    rw [min_eq_left h.2, max_eq_right h.1]
  -- Transfer the mean and the event to the product space.
  have hmean : ∫ η, C.sup' hC (fun c => ∑ i ∈ c, Y i η) ∂P = ∫ y, F y ∂(P.map W) := by
    rw [integral_map hWm.aemeasurable hFm.aestronglyMeasurable]
    exact (integral_congr_ae hae).symm
  have hmeas : MeasurableSet {y : Fin n → ℝ | u ≤ |F y - ∫ z, F z ∂(P.map W)|} :=
    measurableSet_le measurable_const
      (by simpa only [Real.norm_eq_abs] using (hFm.sub_const _).norm)
  have hevent : P.real {ω | u ≤ |C.sup' hC (fun c => ∑ i ∈ c, Y i ω) -
        ∫ η, C.sup' hC (fun c => ∑ i ∈ c, Y i η) ∂P|} =
      (P.map W).real {y | u ≤ |F y - ∫ z, F z ∂(P.map W)|} := by
    rw [map_measureReal_apply hWm hmeas, hmean]
    apply measureReal_congr
    filter_upwards [hae] with ω hω
    show (u ≤ |C.sup' hC (fun c => ∑ i ∈ c, Y i ω) - ∫ y, F y ∂(P.map W)|) =
      (u ≤ |F (W ω) - ∫ z, F z ∂(P.map W)|)
    rw [hω]
  -- Apply the product-space bound.
  have hprod := measureReal_abs_sup_sum_sub_integral_ge_le_pi
    (fun j => P.map (Y (e.symm j))) (C.image (Finset.map e.toEmbedding)) hC' hL0 hR0 hR' hu
  rw [hevent, hlaw]
  simpa only [hFdef] using hprod

/-! ### Martin's Lemma 3.1 -/

/-- Martin (2004), Lemma 3.1 in its printed generality. For independent measurable random variables
`Y i`, `i : ι` finite, with `|Y i| ≤ L` almost surely, a nonempty family `C` of subsets of `ι` of
size at most `R`, and `Z` the maximum over `C` of the set sums,
`P (u ≤ |Z - E Z|) ≤ exp (64 - u² / (64 R L²))` for every `u > 0`. Degenerate cases: for `R = 0` or
`L = 0` Lean's division by zero makes the right side `exp 64 ≥ 1`; for `L < 0` the hypothesis `hL`
is impossible when `ι` is nonempty, and when `ι` is empty `Z = 0` and the event is empty. Otherwise
this follows from the stronger bound `measureReal_abs_sup_sum_sub_integral_ge_le_two_mul_exp` and
the scalar comparison. -/
theorem martin_lemma_3_1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {ι : Type*} [Fintype ι]
    (Y : ι → Ω → ℝ) (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (L : ℝ) (hL : ∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ L)
    (C : Finset (Finset ι)) (hC : C.Nonempty) (R : ℕ) (hR : ∀ c ∈ C, c.card ≤ R)
    (u : ℝ) (hu : 0 < u) :
    P.real {ω | u ≤ |C.sup' hC (fun c => ∑ i ∈ c, Y i ω) -
        ∫ η, C.sup' hC (fun c => ∑ i ∈ c, Y i η) ∂P|} ≤
      Real.exp (64 - u ^ 2 / (64 * R * L ^ 2)) := by
  have hone : 1 ≤ Real.exp 64 := Real.one_le_exp (by norm_num)
  -- A zero denominator makes the right side `exp 64 ≥ 1`.
  have hzero : R = 0 ∨ L = 0 → Real.exp 64 ≤ Real.exp (64 - u ^ 2 / (64 * R * L ^ 2)) := by
    rintro (h | h) <;> simp [h]
  rcases lt_trichotomy L 0 with hLneg | hLzero | hLpos
  · by_cases hι : Nonempty ι
    · -- `hL` forces `|Y i ω| ≤ L < 0` at some point, which is absurd.
      exfalso
      obtain ⟨i⟩ := hι
      obtain ⟨ω, hω⟩ := (hL i).exists
      linarith [abs_nonneg (Y i ω)]
    · -- No indices: every set sum is `0`, so `Z = 0` and the event is empty.
      rw [not_nonempty_iff] at hι
      have hsum : ∀ (c : Finset ι) (ω : Ω), ∑ i ∈ c, Y i ω = 0 := fun c ω =>
        Finset.sum_eq_zero fun i _ => isEmptyElim i
      have hZ : ∀ ω, C.sup' hC (fun c => ∑ i ∈ c, Y i ω) = 0 := fun ω => by
        simp only [hsum]
        exact Finset.sup'_const hC 0
      have hempty : {ω | u ≤ |C.sup' hC (fun c => ∑ i ∈ c, Y i ω) -
          ∫ η, C.sup' hC (fun c => ∑ i ∈ c, Y i η) ∂P|} = ∅ := by
        ext ω
        simp only [hZ, integral_zero, sub_self, abs_zero, mem_ofPred_eq, mem_empty_iff_false,
          iff_false, not_le]
        exact hu
      rw [hempty, measureReal_empty]
      exact (Real.exp_pos _).le
  · exact measureReal_le_one.trans (hone.trans (hzero (Or.inr hLzero)))
  · rcases Nat.eq_zero_or_pos R with hR0 | hR0
    · exact measureReal_le_one.trans (hone.trans (hzero (Or.inl hR0)))
    · -- The stronger bound, then the scalar comparison with `v = u² / (R L²)`.
      have h := measureReal_abs_sup_sum_sub_integral_ge_le_two_mul_exp P Y hY hind hLpos hL C hC
        hR0 hR hu.le
      have hRpos : (0 : ℝ) < R := by exact_mod_cast hR0
      have hv : 0 ≤ u ^ 2 / (R * L ^ 2) := by positivity
      have hs := two_mul_exp_neg_div_sixteen_le_exp_sixty_four_sub_div_sixty_four _ hv
      refine h.trans (le_trans (le_of_eq ?_) (hs.trans (le_of_eq ?_)))
      · congr 2
        field_simp
      · congr 1
        field_simp

end MaxOfSums31

end ProbabilityBasics.Concentration
