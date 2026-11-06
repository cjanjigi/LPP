/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Foundations.Concentration.Entropy
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Tensorization of entropy on a finite product

Sub-additivity of entropy on a finite product of probability spaces. The mathematics follows
Boucheron, Lugosi and Massart (2013), Chapter 4, with every step written out. This is general
probability and does not depend on the LPP model.

## Main results

Let `μ i` be probability measures on the coordinate spaces `E i`, `i : Fin n`, and
`P = Measure.pi μ`.

* `integral_integral_update`: integrating out coordinate `i` and then integrating over `P` gives
  the integral over `P`.
* `entropy_pi_le_sum` (tensorization): for a measurable `g` with values in `[a, b]`, `0 < a`,
  `Ent_P(g) ≤ ∑ i, ∫ Ent_{μ i}(t ↦ g(x with coordinate i replaced by t)) dP(x)`.

## Proof outline

`measurePreserving_piFinSuccAbove` splits off one coordinate: the integral over `P` is an integral
over `(s, r)` of the function at `insertNth s r`. For `entropy_pi_le_sum` the induction on `n`
splits off coordinate `0`. The chain rule `entropy_prod_eq` writes the entropy as the coordinate-0
term plus the entropy of the average `G` over coordinate `0`; the induction hypothesis applies to
`G`, and convexity `entropy_integral_le` compares the entropies of `G` with those of `g`, one
coordinate at a time. Fubini and `Fin.sum_univ_succAbove` reassemble the sum.

## References

- S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities: A Nonasymptotic Theory of
  Independence*, Oxford University Press, 2013, Chapter 4.
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityBasics.Concentration

section Helpers

variable {α : Type*} [MeasurableSpace α]

/-! ### Boundedness of the entropy -/

/-- The entropy of a measurable function with values in `[a, b]`, `0 < a`, is bounded by
`2 b (|log a| + |log b|)`: both `E[g log g]` and `E g log E g` are. -/
private lemma abs_entropy_le (μ : Measure α) [IsProbabilityMeasure μ] {g : α → ℝ} {a b : ℝ}
    (ha : 0 < a) (hg : Measurable g) (hgab : ∀ x, g x ∈ Icc a b) :
    |entropy μ g| ≤ 2 * (b * (|Real.log a| + |Real.log b|)) := by
  have hm := integral_mem_Icc μ hg hgab
  have hterm : |(∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ)| ≤ b * (|Real.log a| + |Real.log b|) :=
    abs_mul_le_of_mem_Icc ha hm (abs_log_le_of_mem_Icc ha hm)
  have hint : |∫ x, g x * Real.log (g x) ∂μ| ≤ b * (|Real.log a| + |Real.log b|) := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => g x * Real.log (g x))
        (C := b * (|Real.log a| + |Real.log b|))
        (ae_of_all _ fun x => by
          simpa only [Real.norm_eq_abs] using
            abs_mul_le_of_mem_Icc ha (hgab x) (abs_log_le_of_mem_Icc ha (hgab x)))
  have hint' := abs_le.1 hint
  have hterm' := abs_le.1 hterm
  rw [entropy_eq]
  exact abs_le.2 ⟨by linarith [hint'.1, hint'.2, hterm'.1, hterm'.2],
    by linarith [hint'.1, hint'.2, hterm'.1, hterm'.2]⟩

end Helpers

section Pi

/-! ### Splitting off one coordinate -/

/-- The product integral after separating coordinate `i`: invariance of the integral under the
measure-preserving equivalence `piFinSuccAbove`. No integrability is needed. -/
private lemma integral_pi_succAbove {n : ℕ} {E : Fin (n + 1) → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : Fin (n + 1)) (F : (∀ j, E j) → ℝ) :
    ∫ x, F x ∂Measure.pi μ =
      ∫ p : E i × (∀ j : Fin n, E (i.succAbove j)), F (i.insertNth p.1 p.2)
        ∂(μ i).prod (Measure.pi fun j => μ (i.succAbove j)) :=
  (((measurePreserving_piFinSuccAbove μ i).symm).integral_comp' F).symm

/-- Change of variables for entropy: the entropy on the product is the entropy on the split product
of the function composed with `insertNth`. -/
private lemma entropy_pi_succ {n : ℕ} {E : Fin (n + 1) → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : Fin (n + 1)) (g : (∀ j, E j) → ℝ) :
    entropy (Measure.pi μ) g =
      entropy ((μ i).prod (Measure.pi fun j => μ (i.succAbove j)))
        (fun p => g (i.insertNth p.1 p.2)) := by
  rw [entropy_eq, entropy_eq, integral_pi_succAbove μ i (fun x => g x * Real.log (g x)),
    integral_pi_succAbove μ i g]

/-- Integrating out one coordinate and then integrating over the product gives the product
integral. -/
theorem integral_integral_update {n : ℕ} {E : Fin n → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n)
    {f : (∀ j, E j) → ℝ} {M : ℝ} (hf : Measurable f) (hfM : ∀ x, |f x| ≤ M) :
    ∫ x, (∫ t, f (Function.update x i t) ∂μ i) ∂Measure.pi μ = ∫ x, f x ∂Measure.pi μ := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    have hint : Integrable
        (fun p : E i × (∀ j : Fin m, E (i.succAbove j)) => f (i.insertNth p.1 p.2))
        ((μ i).prod (Measure.pi fun j => μ (i.succAbove j))) :=
      integrable_of_abs_le _ (hf.comp (MeasurableEquiv.piFinSuccAbove E i).symm.measurable)
        fun p => hfM _
    have hleft := integral_pi_succAbove μ i (fun x => ∫ t, f (Function.update x i t) ∂μ i)
    have hright := integral_pi_succAbove μ i f
    have hsnd := integral_fun_snd (μ := μ i) (ν := Measure.pi fun j => μ (i.succAbove j))
      (fun r => ∫ t, f (i.insertNth t r) ∂μ i)
    have hfubini := integral_prod_symm
      (fun p : E i × (∀ j : Fin m, E (i.succAbove j)) => f (i.insertNth p.1 p.2)) hint
    rw [probReal_univ, one_smul] at hsnd
    rw [hleft, hright, hfubini]
    simp only [Fin.update_insertNth]
    exact hsnd

/-! ### The coordinate entropies -/

/-- The entropy in coordinate `i`, as a function of the remaining coordinates, is measurable. -/
private lemma measurable_entropy_update {n : ℕ} {E : Fin n → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : Fin n) {g : (∀ j, E j) → ℝ} (hg : Measurable g) :
    Measurable fun x => entropy (μ i) (fun t => g (Function.update x i t)) := by
  have hint : ∀ h : (∀ j, E j) → ℝ, Measurable h →
      Measurable fun x => ∫ t, h (Function.update x i t) ∂μ i :=
    fun h hh => (hh.comp (measurable_update' (a := i))).stronglyMeasurable.integral_prod_right'.measurable
  simp only [entropy_eq]
  exact (hint _ (hg.mul hg.log)).sub ((hint _ hg).mul (hint _ hg).log)

/-- The entropy in coordinate `i` is bounded when `g` takes values in `[a, b]`, `0 < a`. -/
private lemma abs_entropy_update_le {n : ℕ} {E : Fin n → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : Fin n) {g : (∀ j, E j) → ℝ} {a b : ℝ} (ha : 0 < a) (hg : Measurable g)
    (hgab : ∀ x, g x ∈ Icc a b) (x : ∀ j, E j) :
    |entropy (μ i) (fun t => g (Function.update x i t))| ≤
      2 * (b * (|Real.log a| + |Real.log b|)) :=
  abs_entropy_le (μ i) ha (hg.comp (measurable_update x (a := i))) fun _ => hgab _

/-! ### Tensorization -/

/-- Sub-additivity (tensorization) of entropy on a finite product of probability spaces:
`Ent_P(g) ≤ ∑ i, ∫ Ent_{μ i}(t ↦ g(update x i t)) dP(x)`. The proof is an induction on the number
of coordinates: split off coordinate `0` (`insertNth`), apply the chain rule `entropy_prod_eq`, the
induction hypothesis to the average `G` of `g` over coordinate `0`, and convexity
`entropy_integral_le` to compare the entropies of `G` with those of `g`.
Source: Boucheron, Lugosi and Massart (2013), Chapter 4 (sub-additivity of entropy). -/
theorem entropy_pi_le_sum {n : ℕ} {E : Fin n → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    {g : (∀ j, E j) → ℝ} {a b : ℝ} (ha : 0 < a) (hg : Measurable g)
    (hgab : ∀ x, g x ∈ Icc a b) :
    entropy (Measure.pi μ) g ≤
      ∑ i, ∫ x, entropy (μ i) (fun t => g (Function.update x i t)) ∂Measure.pi μ := by
  induction n with
  | zero =>
    let x₀ : ∀ i : Fin 0, E i := fun i => Fin.elim0 i
    have hval : ∀ x : ∀ i : Fin 0, E i, g x = g x₀ := fun x =>
      congrArg g (Subsingleton.elim x x₀)
    have hlog : ∫ x, g x * Real.log (g x) ∂Measure.pi μ = g x₀ * Real.log (g x₀) :=
      integral_eq_const (ae_of_all _ fun x => by rw [hval x])
    have hmean : ∫ x, g x ∂Measure.pi μ = g x₀ := integral_eq_const (ae_of_all _ hval)
    rw [entropy_eq, hlog, hmean]
    simp
  | succ n ih =>
    let μr := fun j : Fin n => μ ((0 : Fin (n + 1)).succAbove j)
    let f : E 0 × (∀ j : Fin n, E ((0 : Fin (n + 1)).succAbove j)) → ℝ :=
      fun p => g ((0 : Fin (n + 1)).insertNth p.1 p.2)
    let G := fun r : ∀ j : Fin n, E ((0 : Fin (n + 1)).succAbove j) =>
      ∫ s, g ((0 : Fin (n + 1)).insertNth s r) ∂μ 0
    have hins : Measurable fun p : E 0 × (∀ j : Fin n, E ((0 : Fin (n + 1)).succAbove j)) =>
        (0 : Fin (n + 1)).insertNth p.1 p.2 :=
      (MeasurableEquiv.piFinSuccAbove E 0).symm.measurable
    have hf : Measurable f := hg.comp hins
    have hfab : ∀ p, f p ∈ Icc a b := fun p => hgab _
    have hG_meas : Measurable G := hf.stronglyMeasurable.integral_prod_left'.measurable
    have hG_mem : ∀ r, G r ∈ Icc a b := fun r =>
      integral_mem_Icc (μ 0) (hf.comp measurable_prodMk_right) fun s => hfab (s, r)
    -- Chain rule: coordinate `0`, then the average `G`.
    have hchange : entropy (Measure.pi μ) g = entropy ((μ 0).prod (Measure.pi μr)) f :=
      entropy_pi_succ μ 0 g
    have hchain : entropy ((μ 0).prod (Measure.pi μr)) f =
        (∫ r, entropy (μ 0) (fun s => f (s, r)) ∂Measure.pi μr) +
          entropy (Measure.pi μr) (fun r => ∫ s, f (s, r) ∂μ 0) :=
      entropy_prod_eq (μ 0) (Measure.pi μr) ha hf hfab
    -- Induction hypothesis for the average `G` over the remaining coordinates.
    have hih : entropy (Measure.pi μr) (fun r => ∫ s, f (s, r) ∂μ 0) ≤
        ∑ j : Fin n, ∫ r, entropy (μr j) (fun t => G (Function.update r j t)) ∂Measure.pi μr :=
      ih (μ := μr) (g := G) (hg := hG_meas) (hgab := hG_mem)
    -- The coordinate-`0` term.
    have hent0 : ∫ x, entropy (μ 0) (fun t => g (Function.update x 0 t)) ∂Measure.pi μ =
        ∫ r, entropy (μ 0) (fun s => f (s, r)) ∂Measure.pi μr := by
      have hsnd := integral_fun_snd (μ := μ 0) (ν := Measure.pi μr)
        (fun r => entropy (μ 0) (fun s => f (s, r)))
      rw [probReal_univ, one_smul] at hsnd
      rw [integral_pi_succAbove μ 0 (fun x => entropy (μ 0) fun t => g (Function.update x 0 t))]
      simp only [Fin.update_insertNth]
      exact hsnd
    -- The terms of the remaining coordinates, by convexity.
    have hterm : ∀ j : Fin n,
        ∫ r, entropy (μr j) (fun t => G (Function.update r j t)) ∂Measure.pi μr ≤
          ∫ x, entropy (μ ((0 : Fin (n + 1)).succAbove j))
            (fun t => g (Function.update x ((0 : Fin (n + 1)).succAbove j) t))
            ∂Measure.pi μ := by
      intro j
      have hΦ_meas := measurable_entropy_update μ ((0 : Fin (n + 1)).succAbove j) hg
      have hΨ_int : Integrable
          (fun p : E 0 × (∀ j : Fin n, E ((0 : Fin (n + 1)).succAbove j)) =>
            entropy (μ ((0 : Fin (n + 1)).succAbove j))
              (fun t => g (Function.update ((0 : Fin (n + 1)).insertNth p.1 p.2)
                ((0 : Fin (n + 1)).succAbove j) t)))
          ((μ 0).prod (Measure.pi μr)) :=
        integrable_of_abs_le _ (hΦ_meas.comp hins) fun p =>
          abs_entropy_update_le μ ((0 : Fin (n + 1)).succAbove j) ha hg hgab _
      have hpt : ∀ p : E 0 × (∀ j : Fin n, E ((0 : Fin (n + 1)).succAbove j)),
          entropy (μ ((0 : Fin (n + 1)).succAbove j))
              (fun t => g (Function.update ((0 : Fin (n + 1)).insertNth p.1 p.2)
                ((0 : Fin (n + 1)).succAbove j) t)) =
            entropy (μ ((0 : Fin (n + 1)).succAbove j))
              (fun t => f (p.1, Function.update p.2 j t)) :=
        fun p => by simp only [Fin.insertNth_update, f]
      have hΨ_int' : Integrable
          (fun p : E 0 × (∀ j : Fin n, E ((0 : Fin (n + 1)).succAbove j)) =>
            entropy (μ ((0 : Fin (n + 1)).succAbove j))
              (fun t => f (p.1, Function.update p.2 j t)))
          ((μ 0).prod (Measure.pi μr)) :=
        hΨ_int.congr (ae_of_all _ hpt)
      have hlhs_int : Integrable
          (fun r => entropy (μr j) (fun t => G (Function.update r j t))) (Measure.pi μr) :=
        integrable_of_abs_le _ (measurable_entropy_update μr j hG_meas) fun r =>
          abs_entropy_update_le μr j ha hG_meas hG_mem r
      have hrhs_int : Integrable
          (fun r => ∫ s, entropy (μ ((0 : Fin (n + 1)).succAbove j))
            (fun t => f (s, Function.update r j t)) ∂μ 0) (Measure.pi μr) :=
        hΨ_int'.integral_prod_right
      have hgm : ∀ r : ∀ j : Fin n, E ((0 : Fin (n + 1)).succAbove j),
          Measurable fun z : E 0 × E ((0 : Fin (n + 1)).succAbove j) =>
            f (z.1, Function.update r j z.2) := fun r =>
        hf.comp (measurable_fst.prodMk ((measurable_update r (a := j)).comp measurable_snd))
      calc ∫ r, entropy (μr j) (fun t => G (Function.update r j t)) ∂Measure.pi μr
          ≤ ∫ r, ∫ s, entropy (μ ((0 : Fin (n + 1)).succAbove j))
              (fun t => f (s, Function.update r j t)) ∂μ 0 ∂Measure.pi μr := by
            refine integral_mono hlhs_int hrhs_int fun r => ?_
            exact entropy_integral_le (μ 0) (μ ((0 : Fin (n + 1)).succAbove j)) ha (hgm r)
              fun z => hfab _
        _ = ∫ p, entropy (μ ((0 : Fin (n + 1)).succAbove j))
              (fun t => f (p.1, Function.update p.2 j t)) ∂(μ 0).prod (Measure.pi μr) :=
            (integral_prod_symm _ hΨ_int').symm
        _ = ∫ p, entropy (μ ((0 : Fin (n + 1)).succAbove j))
              (fun t => g (Function.update ((0 : Fin (n + 1)).insertNth p.1 p.2)
                ((0 : Fin (n + 1)).succAbove j) t)) ∂(μ 0).prod (Measure.pi μr) :=
            integral_congr_ae (ae_of_all _ fun p => (hpt p).symm)
        _ = ∫ x, entropy (μ ((0 : Fin (n + 1)).succAbove j))
              (fun t => g (Function.update x ((0 : Fin (n + 1)).succAbove j) t))
              ∂Measure.pi μ :=
            (integral_pi_succAbove μ 0 fun x => entropy (μ ((0 : Fin (n + 1)).succAbove j))
              fun t => g (Function.update x ((0 : Fin (n + 1)).succAbove j) t)).symm
    -- Reassemble.
    calc entropy (Measure.pi μ) g
        = entropy ((μ 0).prod (Measure.pi μr)) f := hchange
      _ = (∫ r, entropy (μ 0) (fun s => f (s, r)) ∂Measure.pi μr) +
            entropy (Measure.pi μr) (fun r => ∫ s, f (s, r) ∂μ 0) := hchain
      _ ≤ (∫ r, entropy (μ 0) (fun s => f (s, r)) ∂Measure.pi μr) +
            ∑ j : Fin n, ∫ r, entropy (μr j) (fun t => G (Function.update r j t))
              ∂Measure.pi μr := add_le_add le_rfl hih
      _ ≤ (∫ r, entropy (μ 0) (fun s => f (s, r)) ∂Measure.pi μr) +
            ∑ j : Fin n, ∫ x, entropy (μ ((0 : Fin (n + 1)).succAbove j))
              (fun t => g (Function.update x ((0 : Fin (n + 1)).succAbove j) t))
              ∂Measure.pi μ := add_le_add le_rfl (Finset.sum_le_sum fun j _ => hterm j)
      _ = ∑ i, ∫ x, entropy (μ i) (fun t => g (Function.update x i t)) ∂Measure.pi μ := by
        rw [Fin.sum_univ_succAbove _ 0, hent0]

end Pi

end ProbabilityBasics.Concentration
