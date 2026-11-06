/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Foundations.Concentration.Herbst
public import ProbabilityBasics.Foundations.Concentration.MaxOfSums
public import ProbabilityBasics.Foundations.Concentration.ModifiedLogSobolev

/-!
# Concentration of the maximum of clamped set sums on a finite product (Martin 2004, Lemma 3.1)

This is the core of the proof of Lemma 3.1 of Martin (2004), by the entropy method. It is general
probability and does not depend on the LPP model.

Let `ν i` be probability laws on `ℝ` for `i : Fin n`, let `L > 0`, let `R > 0` be a natural number,
and let `C` be a nonempty family of subsets of `Fin n`, each of size at most `R`. Write
`F y` for the maximum over `c ∈ C` of the sums `∑ j ∈ c, clamp_L (y j)`, where
`clamp_L t = max (-L) (min t L)`.

## Main result

* `measureReal_abs_sup_sum_sub_integral_ge_le_pi`: for the product law `P = Measure.pi ν` and every
  `u ≥ 0`, `P (u ≤ |F - E F|) ≤ 2 exp (-u² / (16 R L²))`.

## Proof outline

1. The modified logarithmic Sobolev inequality (`ModifiedLogSobolev`) for `G = σ F`, with base
   point `-L` in every coordinate, bounds the entropy of `exp (σ F)` by a sum over coordinates `i`
   of the averages of `exp (σ F) φ(σ F_i - σ F)`, where `φ z = e^z - z - 1` and `F_i` is the value
   of `F` after lowering coordinate `i` to `-L`.
2. Put `D_i = F - F_i`. For a maximizing set `c*` (`MaxOfSums`),
   `0 ≤ D_i ≤ 2 L · 1[i ∈ c*]`, and `|c*| ≤ R`. For `σ = ± s` and `0 < s ≤ 1 / (2 L)` the
   exponential sum bounds of `MaxOfSums` give `∑ i, φ(σ (F_i - F)) ≤ 4 s² L² R` at every point.
3. Hence `Ent(exp (σ F)) ≤ 4 L² R s² E exp (σ F)` for `σ = ± s`.
4. Herbst's argument and Chernoff's bound (`Herbst`) for `F` and for `-F`, with `c = 4 L² R` and
   `T = 1 / (2 L)`, followed by the union bound, give the tail bound for `u ≤ 4 L R`.
5. For `u > 4 L R` the event is empty: `|F| ≤ R L` and `|E F| ≤ R L`.

## References

- J. B. Martin, *Limiting shape for directed percolation models*, Ann. Probab. 32 (2004),
  Lemma 3.1.
- S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities: A Nonasymptotic Theory of
  Independence*, Oxford University Press, 2013, Chapters 4 and 6 (entropy method).
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityBasics.Concentration

section MaxOfSumsProduct

/-! ### The clamped maximum -/

/-- The clamp of a real number to `[-L, L]`. -/
private def clamp (L t : ℝ) : ℝ := max (-L) (min t L)

/-- The maximum over the family `C` of the sums of the clamped coordinates. -/
private noncomputable def Fmax {n : ℕ} (C : Finset (Finset (Fin n))) (hC : C.Nonempty) (L : ℝ)
    (y : Fin n → ℝ) : ℝ :=
  C.sup' hC (fun c => ∑ j ∈ c, clamp L (y j))

/-- The clamped maximum is measurable: it is a finite supremum of finite sums of measurable
functions of the coordinates. -/
private theorem measurable_Fmax {n : ℕ} (C : Finset (Finset (Fin n))) (hC : C.Nonempty) (L : ℝ) :
    Measurable (Fmax C hC L) := by
  have hj : ∀ j : Fin n, Measurable fun y : Fin n → ℝ => clamp L (y j) := fun j => by
    unfold clamp; fun_prop
  have e : Fmax C hC L =
      C.sup' hC (fun c (y : Fin n → ℝ) => ∑ j ∈ c, clamp L (y j)) := by
    funext y
    simp only [Fmax, Finset.sup'_apply]
  rw [e]
  exact Finset.measurable_sup' hC fun c _ => Finset.measurable_sum _ fun j _ => hj j

/-- The clamp of a real number lies in `[-L, L]` when `L ≥ 0`. -/
private theorem abs_clamp_le {L : ℝ} (hL : 0 ≤ L) (t : ℝ) : |clamp L t| ≤ L := by
  unfold clamp
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

/-- Every clamped set sum has absolute value at most `R L` when the sets have size at most `R`, so
the same holds for the maximum. -/
private theorem abs_Fmax_le {n : ℕ} (C : Finset (Finset (Fin n))) (hC : C.Nonempty) {L : ℝ}
    (hL : 0 ≤ L) {R : ℕ} (hR : ∀ c ∈ C, c.card ≤ R) (y : Fin n → ℝ) :
    |Fmax C hC L y| ≤ R * L := by
  have hsum : ∀ c ∈ C, |∑ j ∈ c, clamp L (y j)| ≤ R * L := by
    intro c hc
    calc |∑ j ∈ c, clamp L (y j)| ≤ ∑ j ∈ c, |clamp L (y j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ c, L := Finset.sum_le_sum fun j _ => abs_clamp_le hL _
      _ = c.card * L := by simp
      _ ≤ R * L := mul_le_mul_of_nonneg_right (by exact_mod_cast hR c hc) hL
  unfold Fmax
  rw [abs_le]
  constructor
  · obtain ⟨c, hc⟩ := hC
    exact le_trans (neg_le_of_abs_le (hsum c hc))
      (Finset.le_sup' (fun c => ∑ j ∈ c, clamp L (y j)) hc)
  · exact Finset.sup'_le hC _ fun c hc => (abs_le.1 (hsum c hc)).2

/-- Lowering coordinate `i` of `y` to `-L` and then clamping is the same as clamping and then
lowering, because `clamp L (-L) = -L`. -/
private theorem Fmax_update {n : ℕ} (C : Finset (Finset (Fin n))) (hC : C.Nonempty) {L : ℝ}
    (hL : 0 ≤ L) (y : Fin n → ℝ) (i : Fin n) :
    Fmax C hC L (Function.update y i (-L)) =
      C.sup' hC (fun c => ∑ j ∈ c, Function.update (fun j => clamp L (y j)) i (-L) j) := by
  unfold Fmax
  congr 1
  funext c
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j = i
  · subst h
    simp only [Function.update_self, clamp]
    rw [min_eq_left (by linarith), max_eq_right le_rfl]
  · simp [Function.update_of_ne h]

/-! ### The modified logarithmic Sobolev inequality for the clamped maximum -/

/-- The modified logarithmic Sobolev inequality for `G = σ F` with base point `-L` in every
coordinate and either sign of `σ`, on a product of laws on `ℝ`. The comparison values are
rewritten with `Fmax_update`. -/
private theorem mlsi_Fmax {n : ℕ} (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (C : Finset (Finset (Fin n))) (hC : C.Nonempty) {L : ℝ} (hL : 0 ≤ L) {R : ℕ}
    (hR : ∀ c ∈ C, c.card ≤ R) (s : ℝ) :
    entropy (Measure.pi ν) (fun y => Real.exp (s * Fmax C hC L y)) ≤
      ∑ i, ∫ y, Real.exp (s * Fmax C hC L y) *
        (Real.exp (s * C.sup' hC (fun c => ∑ j ∈ c,
            Function.update (fun j => clamp L (y j)) i (-L) j) - s * Fmax C hC L y) -
          (s * C.sup' hC (fun c => ∑ j ∈ c,
            Function.update (fun j => clamp L (y j)) i (-L) j) - s * Fmax C hC L y) - 1)
        ∂Measure.pi ν := by
  have hb : ∀ y : Fin n → ℝ, |s * Fmax C hC L y| ≤ |s| * (R * L) := fun y => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_Fmax_le C hC hL hR y) (abs_nonneg s)
  have h := entropy_exp_pi_le_sum ν (G := fun y => s * Fmax C hC L y) (M := |s| * (R * L))
    ((measurable_Fmax C hC L).const_mul s) hb (fun _ => -L)
  simpa only [Fmax_update C hC hL] using h

/-! ### The pointwise bound on the sum of brackets -/

/-- The bracket `φ(x) = e^x - x - 1` with `x = σ (F_i - F)` equals `e^{-σ D} - (-σ D) - 1` when
`D = F - F_i`. -/
private theorem bracket_eq (σ F Fi D : ℝ) (h : D = F - Fi) :
    Real.exp (σ * Fi - σ * F) - (σ * Fi - σ * F) - 1 =
      Real.exp (-(σ * D)) - (-(σ * D)) - 1 := by
  have hx : σ * Fi - σ * F = -(σ * D) := by
    rw [h]
    ring
  rw [hx]

/-- Pointwise bound. For `σ = s` or `σ = -s`, `0 ≤ s` and
`2 L s ≤ 1`, the brackets `φ(σ (F_i y - F y))` summed over the coordinates `i` are at most
`4 s² L² R`. Take a maximizing set `c*` of the clamped vector (`MaxOfSums`); the drops
`D_i = F y - F_i y` satisfy `0 ≤ D_i`, and `D_i ≤ 2 L` on `c*`, `D_i = 0` off it. -/
private theorem sum_bracket_le {n : ℕ} (C : Finset (Finset (Fin n))) (hC : C.Nonempty) {L : ℝ}
    (hL : 0 ≤ L) {R : ℕ} (hR : ∀ c ∈ C, c.card ≤ R) {s σ : ℝ} (hs : 0 ≤ s)
    (hsL : 2 * L * s ≤ 1) (hσ : σ = s ∨ σ = -s) (y : Fin n → ℝ) :
    ∑ i, (Real.exp (σ * C.sup' hC (fun c => ∑ j ∈ c,
            Function.update (fun j => clamp L (y j)) i (-L) j) - σ * Fmax C hC L y) -
          (σ * C.sup' hC (fun c => ∑ j ∈ c,
            Function.update (fun j => clamp L (y j)) i (-L) j) - σ * Fmax C hC L y) - 1) ≤
      4 * s ^ 2 * L ^ 2 * R := by
  have hy : ∀ j, |clamp L (y j)| ≤ L := fun j => abs_clamp_le hL _
  obtain ⟨c, hcC, hc⟩ :=
    exists_mem_sup_sum_sub_update_neg_le C hC (y := fun j => clamp L (y j)) hy
  obtain ⟨D, hD_def⟩ : ∃ D : Fin n → ℝ, ∀ i, D i = Fmax C hC L y - C.sup' hC (fun c =>
      ∑ j ∈ c, Function.update (fun j => clamp L (y j)) i (-L) j) := ⟨_, fun _ => rfl⟩
  have hD0 : ∀ i, 0 ≤ D i := fun i => by
    rw [hD_def i]
    exact sub_nonneg.2 (sup_sum_update_neg_le C hC hy i)
  have hDle : ∀ i, D i ≤ if i ∈ c then 2 * L else 0 := fun i => by
    rw [hD_def i]
    exact hc i
  have hcard : c.card ≤ R := hR c hcC
  rcases hσ with hσ | hσ
  · rw [hσ]
    have hmain := sum_exp_neg_mul_add_sub_one_le hcard hD0 hDle hs hsL
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) hmain
    rw [bracket_eq s _ _ (D i) (hD_def i)]
    ring
  · rw [hσ]
    have hmain := sum_exp_mul_sub_sub_one_le hcard hD0 hDle hs hsL
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) hmain
    rw [bracket_eq (-s) _ _ (D i) (hD_def i)]
    simp only [neg_mul, neg_neg]

/-! ### The entropy bound -/

/-- The brackets are nonnegative: `e^x - x - 1 ≥ 0`. -/
private theorem exp_sub_sub_one_nonneg (x : ℝ) : 0 ≤ Real.exp x - x - 1 := by
  linarith [Real.add_one_le_exp x]

/-- Entropy bound. For `σ = s` or `σ = -s` and `0 < s ≤ 1 / (2 L)`,
`Ent(exp (σ F)) ≤ 4 L² R s² E exp (σ F)` under the product law. From the modified logarithmic
Sobolev inequality (`mlsi_Fmax`), exchange the sum over `i` with the integral (every term is
measurable, nonnegative and bounded) and use the pointwise bound `sum_bracket_le`. -/
private theorem entropy_exp_mul_Fmax_le {n : ℕ} (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (C : Finset (Finset (Fin n))) (hC : C.Nonempty) {L : ℝ}
    (hL : 0 ≤ L) {R : ℕ} (hR : ∀ c ∈ C, c.card ≤ R) {s σ : ℝ} (hs : 0 ≤ s)
    (hsL : 2 * L * s ≤ 1) (hσ : σ = s ∨ σ = -s) :
    entropy (Measure.pi ν) (fun y => Real.exp (σ * Fmax C hC L y)) ≤
      (4 * L ^ 2 * R) * s ^ 2 * ∫ y, Real.exp (σ * Fmax C hC L y) ∂Measure.pi ν := by
  have hmlsi := mlsi_Fmax ν C hC hL hR σ
  -- Name the brackets.
  obtain ⟨b, hb_def⟩ : ∃ b : Fin n → (Fin n → ℝ) → ℝ, ∀ i y, b i y =
      Real.exp (σ * C.sup' hC (fun c => ∑ j ∈ c,
          Function.update (fun j => clamp L (y j)) i (-L) j) - σ * Fmax C hC L y) -
        (σ * C.sup' hC (fun c => ∑ j ∈ c,
          Function.update (fun j => clamp L (y j)) i (-L) j) - σ * Fmax C hC L y) - 1 :=
    ⟨_, fun _ _ => rfl⟩
  have hmlsi' : entropy (Measure.pi ν) (fun y => Real.exp (σ * Fmax C hC L y)) ≤
      ∑ i, ∫ y, Real.exp (σ * Fmax C hC L y) * b i y ∂Measure.pi ν := by
    simpa only [hb_def] using hmlsi
  -- Pointwise facts about the brackets.
  have hbnonneg : ∀ i y, 0 ≤ b i y := fun i y => by
    rw [hb_def]
    exact exp_sub_sub_one_nonneg _
  have hbsum : ∀ y, ∑ i, b i y ≤ 4 * s ^ 2 * L ^ 2 * R := fun y =>
    (Finset.sum_congr rfl fun i _ => hb_def i y).le.trans (sum_bracket_le C hC hL hR hs hsL hσ y)
  have hble : ∀ i y, b i y ≤ 4 * s ^ 2 * L ^ 2 * R := fun i y =>
    le_trans (Finset.single_le_sum (fun j _ => hbnonneg j y) (Finset.mem_univ i)) (hbsum y)
  -- Measurability.
  have hFm := measurable_Fmax C hC L
  have hexp_meas : Measurable fun y => Real.exp (σ * Fmax C hC L y) := (hFm.const_mul σ).exp
  have hb_meas : ∀ i, Measurable (b i) := fun i => by
    have hFi : Measurable fun y : Fin n → ℝ => C.sup' hC (fun c => ∑ j ∈ c,
        Function.update (fun j => clamp L (y j)) i (-L) j) := by
      have e : (fun y : Fin n → ℝ => C.sup' hC (fun c => ∑ j ∈ c,
          Function.update (fun j => clamp L (y j)) i (-L) j)) =
          fun y => Fmax C hC L (Function.update y i (-L)) :=
        funext fun y => (Fmax_update C hC hL y i).symm
      rw [e]
      exact hFm.comp measurable_update_left
    have hx := (hFi.const_mul σ).sub (hFm.const_mul σ)
    have e : b i = fun y => Real.exp (σ * C.sup' hC (fun c => ∑ j ∈ c,
          Function.update (fun j => clamp L (y j)) i (-L) j) - σ * Fmax C hC L y) -
        (σ * C.sup' hC (fun c => ∑ j ∈ c,
          Function.update (fun j => clamp L (y j)) i (-L) j) - σ * Fmax C hC L y) - 1 :=
      funext (hb_def i)
    rw [e]
    exact (hx.exp.sub hx).sub measurable_const
  -- Boundedness of `exp (σ F)` and integrability of every term.
  have hexp_le : ∀ y, Real.exp (σ * Fmax C hC L y) ≤ Real.exp (|σ| * (R * L)) := fun y => by
    refine Real.exp_le_exp.2 ?_
    calc σ * Fmax C hC L y ≤ |σ * Fmax C hC L y| := le_abs_self _
      _ = |σ| * |Fmax C hC L y| := abs_mul _ _
      _ ≤ |σ| * (R * L) := mul_le_mul_of_nonneg_left (abs_Fmax_le C hC hL hR y) (abs_nonneg σ)
  have hexp_int : Integrable (fun y => Real.exp (σ * Fmax C hC L y)) (Measure.pi ν) :=
    Integrable.of_bound hexp_meas.aestronglyMeasurable (Real.exp (|σ| * (R * L)))
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hexp_le y)
  have hterm_int : ∀ i, Integrable (fun y => Real.exp (σ * Fmax C hC L y) * b i y)
      (Measure.pi ν) := fun i =>
    Integrable.of_bound (hexp_meas.mul (hb_meas i)).aestronglyMeasurable
      (Real.exp (|σ| * (R * L)) * (4 * s ^ 2 * L ^ 2 * R))
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hbnonneg i y))]
        exact mul_le_mul (hexp_le y) (hble i y) (hbnonneg i y) (Real.exp_pos _).le)
  -- Exchange the sum and the integral, then use the pointwise bound.
  have hpoint : ∀ y, ∑ i, Real.exp (σ * Fmax C hC L y) * b i y ≤
      Real.exp (σ * Fmax C hC L y) * (4 * s ^ 2 * L ^ 2 * R) := fun y => by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbsum y) (Real.exp_pos _).le
  calc entropy (Measure.pi ν) (fun y => Real.exp (σ * Fmax C hC L y))
      ≤ ∑ i, ∫ y, Real.exp (σ * Fmax C hC L y) * b i y ∂Measure.pi ν := hmlsi'
    _ = ∫ y, ∑ i, Real.exp (σ * Fmax C hC L y) * b i y ∂Measure.pi ν :=
        (integral_finsetSum _ fun i _ => hterm_int i).symm
    _ ≤ ∫ y, Real.exp (σ * Fmax C hC L y) * (4 * s ^ 2 * L ^ 2 * R) ∂Measure.pi ν :=
        integral_mono (integrable_finsetSum _ fun i _ => hterm_int i)
          (hexp_int.mul_const _) hpoint
    _ = (4 * L ^ 2 * R) * s ^ 2 * ∫ y, Real.exp (σ * Fmax C hC L y) ∂Measure.pi ν := by
        rw [integral_mul_const]
        ring

/-! ### From the entropy bounds to the two-sided tail -/

/-- Herbst's argument for `F` and for `-F` with `c = 4 L² R` and `T = 1 / (2 L)`, followed by the
union bound: if both `exp (s F)` and `exp (-s F)` have entropy
at most `4 L² R s² E exp (± s F)` for `0 < s ≤ 1 / (2 L)`, and `|F| ≤ R L`, then
`P(t ≤ |F - E F|) ≤ 2 exp (-t² / (16 R L²))` for `0 ≤ t ≤ 4 L R`. -/
private theorem two_sided_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {F : Ω → ℝ} {L R : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hF : Measurable F) (hFM : ∀ ω, |F ω| ≤ R * L)
    (hentP : ∀ s ∈ Ioc 0 (1 / (2 * L)), entropy P (fun ω => Real.exp (s * F ω)) ≤
      (4 * L ^ 2 * R) * s ^ 2 * ∫ ω, Real.exp (s * F ω) ∂P)
    (hentN : ∀ s ∈ Ioc 0 (1 / (2 * L)), entropy P (fun ω => Real.exp (s * (-F ω))) ≤
      (4 * L ^ 2 * R) * s ^ 2 * ∫ ω, Real.exp (s * (-F ω)) ∂P)
    {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ 4 * L * R) :
    P.real {ω | t ≤ |F ω - ∫ η, F η ∂P|} ≤ 2 * Real.exp (-t ^ 2 / (16 * R * L ^ 2)) := by
  have hc : 0 < 4 * L ^ 2 * R := by positivity
  have hT : 2 * (4 * L ^ 2 * R) * (1 / (2 * L)) = 4 * L * R := by
    field_simp
  have htT' : t ≤ 2 * (4 * L ^ 2 * R) * (1 / (2 * L)) := by rw [hT]; exact htT
  have hexp : -t ^ 2 / (4 * (4 * L ^ 2 * R)) = -t ^ 2 / (16 * R * L ^ 2) := by
    congr 1; ring
  have hup := measureReal_le_sub_integral_le_of_entropy_le P (M := R * L) (c := 4 * L ^ 2 * R)
    (T := 1 / (2 * L)) hF hFM hc hentP ht htT'
  have hdown := measureReal_le_sub_integral_le_of_entropy_le P (X := fun ω => -F ω)
    (M := R * L) (c := 4 * L ^ 2 * R) (T := 1 / (2 * L)) hF.neg (by simpa using hFM) hc hentN
    ht htT'
  rw [hexp] at hup hdown
  have hneg_int : ∫ η, -F η ∂P = -∫ η, F η ∂P := integral_neg _
  have hsubset : {ω | t ≤ |F ω - ∫ η, F η ∂P|} ⊆
      {ω | t ≤ F ω - ∫ η, F η ∂P} ∪ {ω | t ≤ (-F ω) - ∫ η, -F η ∂P} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_union, hneg_int] at hω ⊢
    rcases le_abs'.1 hω with h | h
    · right; linarith
    · left; linarith
  calc P.real {ω | t ≤ |F ω - ∫ η, F η ∂P|}
      ≤ P.real ({ω | t ≤ F ω - ∫ η, F η ∂P} ∪ {ω | t ≤ (-F ω) - ∫ η, -F η ∂P}) :=
        measureReal_mono hsubset
    _ ≤ P.real {ω | t ≤ F ω - ∫ η, F η ∂P} + P.real {ω | t ≤ (-F ω) - ∫ η, -F η ∂P} :=
        measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-t ^ 2 / (16 * R * L ^ 2)) := by linarith

/-! ### The concentration bound -/

/-- Martin (2004), Lemma 3.1 on a finite product of laws on `ℝ`, in the stronger form
`2 exp (-u² / (16 R L²))`. For probability laws `ν i` on
`ℝ`, `L > 0`, a natural number `R > 0`, and a nonempty family `C` of sets of size at most `R`, the
maximum `F y` over `C` of the sums of `clamp_L (y j)` satisfies, under `Measure.pi ν`,
`P(u ≤ |F - E F|) ≤ 2 exp (-u² / (16 R L²))` for every `u ≥ 0`. The proof is the entropy method:
the modified logarithmic Sobolev inequality with base point `-L`, the exponential sum bounds for
the drops of a maximizing set, Herbst's argument for `F` and `-F`, and the union bound; for
`u > 4 L R` the event is empty because `|F| ≤ R L`. -/
theorem measureReal_abs_sup_sum_sub_integral_ge_le_pi {n : ℕ} (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (C : Finset (Finset (Fin n))) (hC : C.Nonempty)
    {L : ℝ} (hL : 0 < L) {R : ℕ} (hR0 : 0 < R) (hR : ∀ c ∈ C, c.card ≤ R)
    {u : ℝ} (hu : 0 ≤ u) :
    (Measure.pi ν).real {y | u ≤
      |C.sup' hC (fun c => ∑ j ∈ c, max (-L) (min (y j) L)) -
        ∫ z, C.sup' hC (fun c => ∑ j ∈ c, max (-L) (min (z j) L)) ∂Measure.pi ν|} ≤
      2 * Real.exp (-u ^ 2 / (16 * R * L ^ 2)) := by
  change (Measure.pi ν).real {y | u ≤ |Fmax C hC L y - ∫ z, Fmax C hC L z ∂Measure.pi ν|} ≤ _
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR0
  have hFm := measurable_Fmax C hC L
  have hFM := abs_Fmax_le C hC hL.le hR
  -- The entropy bounds for `F` and `-F`, for `0 < s ≤ 1 / (2 L)`.
  have hsL : ∀ s ∈ Ioc (0 : ℝ) (1 / (2 * L)), 2 * L * s ≤ 1 := fun s hs => by
    have h := hs.2
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hentP : ∀ s ∈ Ioc (0 : ℝ) (1 / (2 * L)),
      entropy (Measure.pi ν) (fun y => Real.exp (s * Fmax C hC L y)) ≤
        (4 * L ^ 2 * R) * s ^ 2 * ∫ y, Real.exp (s * Fmax C hC L y) ∂Measure.pi ν :=
    fun s hs => entropy_exp_mul_Fmax_le ν C hC hL.le hR hs.1.le (hsL s hs) (Or.inl rfl)
  have hentN : ∀ s ∈ Ioc (0 : ℝ) (1 / (2 * L)),
      entropy (Measure.pi ν) (fun y => Real.exp (s * (-Fmax C hC L y))) ≤
        (4 * L ^ 2 * R) * s ^ 2 * ∫ y, Real.exp (s * (-Fmax C hC L y)) ∂Measure.pi ν :=
    fun s hs => by
      have h := entropy_exp_mul_Fmax_le ν C hC hL.le hR (σ := -s) hs.1.le (hsL s hs) (Or.inr rfl)
      simpa only [neg_mul, mul_neg] using h
  rcases le_or_gt u (4 * L * R) with hu4 | hu4
  · exact two_sided_tail (Measure.pi ν) hL hRpos hFm hFM hentP hentN hu hu4
  · -- The event is empty: `|F - E F| ≤ 2 R L < u`.
    have hmean : |∫ z, Fmax C hC L z ∂Measure.pi ν| ≤ R * L := by
      simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const (μ := Measure.pi ν) (f := Fmax C hC L) (C := R * L)
          (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hFM y)
    have hRL : 0 < (R : ℝ) * L := mul_pos hRpos hL
    have hempty : {y : Fin n → ℝ | u ≤ |Fmax C hC L y - ∫ z, Fmax C hC L z ∂Measure.pi ν|} =
        ∅ := by
      ext y
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      calc |Fmax C hC L y - ∫ z, Fmax C hC L z ∂Measure.pi ν|
          ≤ |Fmax C hC L y| + |∫ z, Fmax C hC L z ∂Measure.pi ν| := abs_sub _ _
        _ ≤ R * L + R * L := add_le_add (hFM y) hmean
        _ < u := by linarith
    rw [hempty, measureReal_empty]
    positivity

end MaxOfSumsProduct

end ProbabilityBasics.Concentration
