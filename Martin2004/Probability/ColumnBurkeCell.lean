/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Model.StationaryColumns
public import Martin2004.Probability.ColumnLaws

@[expose] public section

/-!
# The one-cell Burke property of the stationary column model

The one-cell computation follows Martin (2004), Lemma 4.1, with the formula quoted from
Seppäläinen (1998), Section 6.

A cell of the stationary column model receives the vertical increment `J` of the column on its
left, the horizontal increment `I` coming from below and the site weight `w`, and returns
`(max (J + w - I) 0, max (I - J) w)` (`columnBurkeCell`). This module proves two facts.

* `measurable_columnBurkeCell`: the cell map is measurable.
* `map_columnBurkeCell`: if `J` is geometric with `P(J = k) = (1 - θ) θ ^ k`, `I` is Bernoulli with
  `P(I = 1) = ρ`, and `w` is Bernoulli with `P(w = 1) = p`, all independent, and if
  `ρ θ (1 - p) = p (1 - ρ)` with `θ < 1`, then the two outputs are independent with the same laws
  as `J` and `I`.

The proof moves everything to the discrete space `ℕ × Bool × Bool`. There the cell map is
`(J, I, w) ↦ (J + w - I, w ∨ (I ∧ J = 0))` with the Booleans read as `0` and `1` and truncated
subtraction. Each output value has exactly two input values mapping to it, and the masses are
compared one output value at a time (`Measure.ext_of_singleton`). The result is then carried to the
real line through the casts `ℕ → ℝ` and `Bool → ℝ`.
-/

open MeasureTheory ProbabilityTheory unitInterval

namespace LPPDifferentiability

/-- The cell map is measurable. -/
theorem measurable_columnBurkeCell : Measurable columnBurkeCell := by
  unfold columnBurkeCell
  fun_prop

/-! ## The discrete cell -/

/-- The cell map on the discrete space `ℕ × Bool × Bool`, with `true` read as `1` and `false` as
`0`: the new vertical increment is `J + w - I` (truncated subtraction) and the horizontal increment
is `1` exactly when `w = 1` or when `I = 1` and `J = 0`. -/
private def discreteCell (x : ℕ × Bool × Bool) : ℕ × Bool :=
  (x.1 + x.2.2.toNat - x.2.1.toNat, x.2.2 || (x.2.1 && decide (x.1 = 0)))

private theorem measurable_discreteCell : Measurable discreteCell := Measurable.of_discrete

/-- The cast of a discrete input to the real line. -/
private def castIn (x : ℕ × Bool × Bool) : ℝ × ℝ × ℝ :=
  ((x.1 : ℝ), ((x.2.1.toNat : ℕ) : ℝ), ((x.2.2.toNat : ℕ) : ℝ))

/-- The cast of a discrete output to the real line. -/
private def castOut (x : ℕ × Bool) : ℝ × ℝ :=
  ((x.1 : ℝ), ((x.2.toNat : ℕ) : ℝ))

private theorem measurable_castIn : Measurable castIn := Measurable.of_discrete

private theorem measurable_castOut : Measurable castOut := Measurable.of_discrete

/-- Truncated subtraction of naturals, seen in the reals, is a maximum with zero. -/
private theorem cast_sub_eq_max (a b : ℕ) : ((a - b : ℕ) : ℝ) = max ((a : ℝ) - b) 0 := by
  rcases le_total a b with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
    exact (max_eq_right (sub_nonpos.2 (Nat.cast_le.2 h))).symm
  · rw [Nat.cast_sub h]
    exact (max_eq_left (sub_nonneg.2 (Nat.cast_le.2 h))).symm

/-- The real cell map on integer inputs `(J, I, w)` with `I, w ∈ {0, 1}` is the cast of the discrete
cell. The first component is the truncated subtraction; the second is checked in the two cases
`J = 0` and `J = j + 1` and the four values of `(I, w)`. -/
private theorem columnBurkeCell_cast (a : ℕ) (u v : Bool) :
    columnBurkeCell ((a : ℝ), ((u.toNat : ℕ) : ℝ), ((v.toNat : ℕ) : ℝ)) =
      castOut (discreteCell (a, u, v)) := by
  have hfirst : max ((a : ℝ) + (v.toNat : ℝ) - (u.toNat : ℝ)) 0 =
      ((a + v.toNat - u.toNat : ℕ) : ℝ) := by
    rw [cast_sub_eq_max]
    push_cast
    rfl
  have hsecond : max ((u.toNat : ℝ) - (a : ℝ)) (v.toNat : ℝ) =
      ((((v || (u && decide (a = 0))).toNat : ℕ)) : ℝ) := by
    by_cases ha : a = 0
    · -- `J = 0`: all four values of `(I, w)` are numerals
      subst ha
      cases u <;> cases v <;> norm_num
    · -- `J ≥ 1`: `I - J ≤ 0 ≤ w`, so the maximum is `w`, and `I - J > 0` never happens
      have hone : (1 : ℝ) ≤ a := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha
      have hu : (u.toNat : ℝ) ≤ 1 := by cases u <;> norm_num
      have hv : (0 : ℝ) ≤ v.toNat := Nat.cast_nonneg _
      simp only [decide_eq_false ha, Bool.and_false, Bool.or_false]
      exact max_eq_right (by linarith)
  exact Prod.ext hfirst hsecond

/-- The real cell map composed with the casts is the casts composed with the discrete cell. -/
private theorem columnBurkeCell_comp_castIn :
    columnBurkeCell ∘ castIn = castOut ∘ discreteCell := by
  funext x
  obtain ⟨a, u, v⟩ := x
  exact columnBurkeCell_cast a u v

/-! ## The two-point preimages -/

/-- The inputs mapped to `(k, 0)`: `(k, 0, 0)` and `(k + 1, 1, 0)`. -/
private theorem preimage_false (k : ℕ) :
    discreteCell ⁻¹' {(k, false)} = {(k, false, false)} ∪ {(k + 1, true, false)} := by
  ext ⟨a, u, v⟩
  cases u <;> cases v <;> simp [discreteCell]
  omega

/-- The inputs mapped to `(0, 1)`: `(0, 1, 1)` and `(0, 1, 0)`. -/
private theorem preimage_zero_true :
    discreteCell ⁻¹' {(0, true)} = {(0, true, true)} ∪ {(0, true, false)} := by
  ext ⟨a, u, v⟩
  cases u <;> cases v <;> simp [discreteCell]
  omega

/-- The inputs mapped to `(k + 1, 1)`: `(k, 0, 1)` and `(k + 1, 1, 1)`. -/
private theorem preimage_succ_true (k : ℕ) :
    discreteCell ⁻¹' {(k + 1, true)} = {(k, false, true)} ∪ {(k + 1, true, true)} := by
  ext ⟨a, u, v⟩
  cases u <;> cases v <;> simp [discreteCell]
  omega

/-! ## Masses of singletons -/

/-- The probability of the outcome `b` for a Bernoulli law with mass `r` on `true`. -/
private noncomputable def bw (r : unitInterval) (b : Bool) : ℝ :=
  if b then (r : ℝ) else 1 - (r : ℝ)

private theorem bw_true (r : unitInterval) : bw r true = r := by simp [bw]

private theorem bw_false (r : unitInterval) : bw r false = 1 - r := by simp [bw]

private theorem bw_nonneg (r : unitInterval) (b : Bool) : 0 ≤ bw r b := by
  cases b
  · rw [bw_false]
    exact sub_nonneg.2 r.2.2
  · rw [bw_true]
    exact r.2.1

private theorem mass_ber (r : unitInterval) (b : Bool) :
    bernoulliMeasure true false r {b} = ENNReal.ofReal (bw r b) := by
  cases b
  · rw [bernoulliMeasure_apply_of_notMem_of_mem (x := true) (y := false) r
      (measurableSet_singleton false) (by simp) (Set.mem_singleton false), bw_false,
      ← unitInterval.coe_symm_eq]
    exact (ofReal_unitInterval _).symm
  · rw [bernoulliMeasure_apply_of_mem_of_notMem (x := true) (y := false) r
      (measurableSet_singleton true) (Set.mem_singleton true) (by simp), bw_true]
    exact (ofReal_unitInterval _).symm

private theorem geom_nonneg (θ : unitInterval) (k : ℕ) : 0 ≤ (θ : ℝ) ^ k * (1 - θ) :=
  mul_nonneg (pow_nonneg θ.2.1 k) (sub_nonneg.2 θ.2.2)

private theorem mass_geom {θ : unitInterval} (hθ : (θ : ℝ) < 1) (k : ℕ) :
    geometricMeasure (σ θ) {k} = ENNReal.ofReal ((θ : ℝ) ^ k * (1 - θ)) := by
  have hsucc : σ θ ≠ 0 := by
    intro h
    have h' : ((σ θ : unitInterval) : ℝ) = ((0 : unitInterval) : ℝ) := congrArg Subtype.val h
    have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
    rw [unitInterval.coe_symm_eq, h0] at h'
    linarith
  rw [geometricMeasure_singleton hsucc]
  congr 1
  rw [unitInterval.coe_symm_eq, sub_sub_cancel]

/-- The mass of one input `(k, b, c)` under the product of the three laws. -/
private theorem mass_triple {p ρ θ : unitInterval} (hθ : (θ : ℝ) < 1) (k : ℕ) (b c : Bool) :
    ((geometricMeasure (σ θ)).prod
        ((bernoulliMeasure true false ρ).prod (bernoulliMeasure true false p))) {(k, b, c)} =
      ENNReal.ofReal ((θ : ℝ) ^ k * (1 - θ) * (bw ρ b * bw p c)) := by
  rw [← Set.singleton_prod_singleton, ← Set.singleton_prod_singleton, Measure.prod_prod,
    Measure.prod_prod, mass_geom hθ, mass_ber, mass_ber,
    ← ENNReal.ofReal_mul (bw_nonneg ρ b), ← ENNReal.ofReal_mul (geom_nonneg θ k)]

/-- The mass of one output `(k, b)` under the target law. -/
private theorem mass_target {ρ θ : unitInterval} (hθ : (θ : ℝ) < 1) (k : ℕ) (b : Bool) :
    ((geometricMeasure (σ θ)).prod (bernoulliMeasure true false ρ)) {(k, b)} =
      ENNReal.ofReal ((θ : ℝ) ^ k * (1 - θ) * bw ρ b) := by
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, mass_geom hθ, mass_ber,
    ← ENNReal.ofReal_mul (geom_nonneg θ k)]

/-- The sum of two masses `ofReal a + ofReal b` is `ofReal c` when `a + b = c` and `a, b ≥ 0`. -/
private theorem ofReal_add_eq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = c) :
    ENNReal.ofReal a + ENNReal.ofReal b = ENNReal.ofReal c := by
  rw [← ENNReal.ofReal_add ha hb, h]

private theorem term_nonneg (θ ρ p : unitInterval) (k : ℕ) (b c : Bool) :
    0 ≤ (θ : ℝ) ^ k * (1 - θ) * (bw ρ b * bw p c) :=
  mul_nonneg (geom_nonneg θ k) (mul_nonneg (bw_nonneg ρ b) (bw_nonneg p c))

/-! ## The discrete Burke property -/

/-- The one-cell Burke property on the discrete space: the image of the product of the geometric,
Bernoulli and Bernoulli laws under the discrete cell is the product of the geometric and the first
Bernoulli law. The three kinds of output value `(k, 0)`, `(0, 1)` and `(k + 1, 1)` are compared
separately, each through its two preimages. -/
private theorem map_discreteCell {p ρ θ : unitInterval} (hθ : (θ : ℝ) < 1)
    (hrel : (ρ : ℝ) * θ * (1 - p) = p * (1 - ρ)) :
    ((geometricMeasure (σ θ)).prod
        ((bernoulliMeasure true false ρ).prod (bernoulliMeasure true false p))).map discreteCell =
      (geometricMeasure (σ θ)).prod (bernoulliMeasure true false ρ) := by
  refine Measure.ext_of_singleton ?_
  rintro ⟨k, b⟩
  rw [Measure.map_apply measurable_discreteCell (measurableSet_singleton _), mass_target hθ]
  cases b
  · -- output `(k, 0)`: inputs `(k, 0, 0)` and `(k + 1, 1, 0)`
    rw [preimage_false k, measure_union (Set.disjoint_singleton.2 (by simp))
      (measurableSet_singleton _), mass_triple hθ, mass_triple hθ]
    refine ofReal_add_eq (term_nonneg _ _ _ _ _ _) (term_nonneg _ _ _ _ _ _) ?_
    simp only [bw_true, bw_false]
    linear_combination ((θ : ℝ) ^ k * (1 - θ)) * hrel
  · rcases k with _ | k
    · -- output `(0, 1)`: inputs `(0, 1, 1)` and `(0, 1, 0)`
      rw [preimage_zero_true, measure_union (Set.disjoint_singleton.2 (by simp))
        (measurableSet_singleton _), mass_triple hθ, mass_triple hθ]
      refine ofReal_add_eq (term_nonneg _ _ _ _ _ _) (term_nonneg _ _ _ _ _ _) ?_
      simp only [bw_true, bw_false]
      ring
    · -- output `(k + 1, 1)`: inputs `(k, 0, 1)` and `(k + 1, 1, 1)`
      rw [preimage_succ_true k, measure_union (Set.disjoint_singleton.2 (by simp))
        (measurableSet_singleton _), mass_triple hθ, mass_triple hθ]
      refine ofReal_add_eq (term_nonneg _ _ _ _ _ _) (term_nonneg _ _ _ _ _ _) ?_
      simp only [bw_true, bw_false]
      linear_combination (-((θ : ℝ) ^ k * (1 - θ))) * hrel

/-! ## Transport to the real line -/

/-- The Bernoulli law on the real line with values `1` and `0` is the image of the Boolean one under
the cast `Bool → ℝ`. -/
private theorem bernoulliMeasure_real_eq_map (r : unitInterval) :
    bernoulliMeasure (1 : ℝ) 0 r =
      (bernoulliMeasure true false r).map (fun b : Bool => ((b.toNat : ℕ) : ℝ)) := by
  have hm : Measurable (fun b : Bool => ((b.toNat : ℕ) : ℝ)) := Measurable.of_discrete
  rw [map_bernoulliMeasure' true false hm r]
  simp

/-- **One-cell Burke property** of the stationary column model (Martin (2004), Lemma 4.1; the
computation is the discrete-time Burke theorem for a queue with Bernoulli arrivals, Seppäläinen
(1998), Section 6). If `J` has the law
`Geom(θ)` with `P(J = k) = (1 - θ) θ ^ k`, `I` has the law `Ber(ρ)` and `w` has the law `Ber(p)`,
all independent, and `ρ θ (1 - p) = p (1 - ρ)` with `θ < 1`, then the cell output
`(max (J + w - I) 0, max (I - J) w)` has the law `Geom(θ) ⊗ Ber(ρ)`: the outputs are independent
with the laws of `J` and `I`. -/
theorem map_columnBurkeCell {p ρ θ : unitInterval} (hθ : (θ : ℝ) < 1)
    (hrel : (ρ : ℝ) * θ * (1 - p) = p * (1 - ρ)) :
    ((geometricCountLaw θ).prod ((bernoulliMeasure (1 : ℝ) 0 ρ).prod
        (bernoulliMeasure (1 : ℝ) 0 p))).map columnBurkeCell =
      (geometricCountLaw θ).prod (bernoulliMeasure (1 : ℝ) 0 ρ) := by
  have hnat : Measurable (fun k : ℕ => (k : ℝ)) := Measurable.of_discrete
  have hbool : Measurable (fun b : Bool => ((b.toNat : ℕ) : ℝ)) := Measurable.of_discrete
  have hsource : (geometricCountLaw θ).prod
      ((bernoulliMeasure (1 : ℝ) 0 ρ).prod (bernoulliMeasure (1 : ℝ) 0 p)) =
      ((geometricMeasure (σ θ)).prod
        ((bernoulliMeasure true false ρ).prod (bernoulliMeasure true false p))).map castIn := by
    rw [geometricCountLaw_def, bernoulliMeasure_real_eq_map ρ, bernoulliMeasure_real_eq_map p,
      Measure.map_prod_map _ _ hbool hbool, Measure.map_prod_map _ _ hnat (hbool.prodMap hbool)]
    try rfl
  have htarget : (geometricCountLaw θ).prod (bernoulliMeasure (1 : ℝ) 0 ρ) =
      ((geometricMeasure (σ θ)).prod (bernoulliMeasure true false ρ)).map castOut := by
    rw [geometricCountLaw_def, bernoulliMeasure_real_eq_map ρ,
      Measure.map_prod_map _ _ hnat hbool]
    try rfl
  rw [hsource, htarget, Measure.map_map measurable_columnBurkeCell measurable_castIn,
    columnBurkeCell_comp_castIn, ← Measure.map_map measurable_castOut measurable_discreteCell,
    map_discreteCell hθ hrel]

end LPPDifferentiability
