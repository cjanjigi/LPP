/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# A universal fourth-moment bound for independent nonnegative variables

The fourth moment of a finite sum of independent nonnegative variables is at most
34 times the sum of their individual fourth moments plus the fourth power of the
sum of their means. The constant 34 does not depend on the laws or the number of
variables.
-/

public section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace LPPDifferentiability

private theorem integrable_power_four {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : MemLp X 4 P) {k : ℕ} (hk : k ≤ 4) :
    Integrable (fun ω => X ω ^ k) P := by
  have hn := (hX.mono_exponent (by exact_mod_cast hk : (k : ℝ≥0∞) ≤ 4)).integrable_norm_pow'
  apply (integrable_norm_iff (hX.aestronglyMeasurable.pow k)).mp
  simpa only [Pi.pow_apply, norm_pow] using hn

private theorem independent_power_add {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : MemLp X 4 P) (hY : MemLp Y 4 P) (hXY : IndepFun X Y P)
    {n : ℕ} (hn : n ≤ 4) :
    (∫ ω, (X ω + Y ω) ^ n ∂P) =
      ∑ k ∈ Finset.range (n + 1),
        (∫ ω, X ω ^ k ∂P) * (∫ ω, Y ω ^ (n-k) ∂P) * (n.choose k : ℝ) := by
  have hind (k : ℕ) : IndepFun (fun ω => X ω ^ k) (fun ω => Y ω ^ (n-k)) P :=
    hXY.comp (measurable_id.pow_const k) (measurable_id.pow_const (n-k))
  have hi (k : ℕ) (hk : k ∈ Finset.range (n+1)) :
      Integrable (fun ω => X ω ^ k * Y ω ^ (n-k) * (n.choose k : ℝ)) P := by
    exact ((hind k).integrable_mul
      (integrable_power_four hX (by have := Finset.mem_range.mp hk; omega))
      (integrable_power_four hY (by omega))).mul_const _
  simp_rw [add_pow]
  rw [integral_finsetSum _ hi]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_mul_const,
    (hind k).integral_fun_mul_eq_mul_integral
      (hX.aestronglyMeasurable.pow k) (hY.aestronglyMeasurable.pow (n-k))]

/-- The raw second, third and fourth moments satisfy the finite Bell bounds.
All moment factorization and integrability come from the individual L4 facts. -/
private theorem finite_bell_bounds {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 4 P) (h0 : ∀ i, 0 ≤ᵐ[P] X i)
    (hind : iIndepFun X P) (s : Finset ι) :
    let m := ∑ i ∈ s, ∫ ω, X i ω ∂P
    let b := ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂P
    let c := ∑ i ∈ s, ∫ ω, X i ω ^ 3 ∂P
    let a := ∑ i ∈ s, ∫ ω, X i ω ^ 4 ∂P
    (∫ ω, (∑ i ∈ s, X i ω)^2 ∂P) ≤ m^2+b ∧
    (∫ ω, (∑ i ∈ s, X i ω)^3 ∂P) ≤ m^3+3*m*b+c ∧
    (∫ ω, (∑ i ∈ s, X i ω)^4 ∂P) ≤ m^4+6*m^2*b+3*b^2+4*m*c+a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    let S : Ω → ℝ := fun ω => ∑ j ∈ s, X j ω
    let m := ∑ j ∈ s, ∫ ω, X j ω ∂P
    let b := ∑ j ∈ s, ∫ ω, X j ω ^ 2 ∂P
    let c := ∑ j ∈ s, ∫ ω, X j ω ^ 3 ∂P
    let a := ∑ j ∈ s, ∫ ω, X j ω ^ 4 ∂P
    let u := ∫ ω, X i ω ∂P
    let v := ∫ ω, X i ω ^ 2 ∂P
    let w := ∫ ω, X i ω ^ 3 ∂P
    let z := ∫ ω, X i ω ^ 4 ∂P
    have hS : MemLp S 4 P := memLp_finsetSum s fun j _ => hX j
    have hiS : IndepFun S (X i) P :=
      by
        simpa only [S, Finset.sum_fn] using
          hind.indepFun_finsetSum_of_notMem₀ (fun j => (hX j).aemeasurable) his
    have hmean : (∫ ω, S ω ∂P) = m :=
      integral_finsetSum s fun j _ => (hX j).integrable (by norm_num)
    have hm : 0 ≤ m := Finset.sum_nonneg fun j _ => integral_nonneg_of_ae (h0 j)
    have hu : 0 ≤ u := integral_nonneg_of_ae (h0 i)
    have hb : 0 ≤ b := Finset.sum_nonneg fun j _ => integral_nonneg fun ω => sq_nonneg _
    have hv : 0 ≤ v := integral_nonneg fun ω => sq_nonneg _
    have hw : 0 ≤ w := integral_nonneg_of_ae ((h0 i).mono fun ω h => pow_nonneg h _)
    have h2 := independent_power_add hS (hX i) hiS (n := 2) (by omega)
    have h3 := independent_power_add hS (hX i) hiS (n := 3) (by omega)
    have h4 := independent_power_add hS (hX i) hiS (n := 4) (by omega)
    norm_num [Finset.sum_range_succ, Nat.choose, hmean] at h2 h3 h4
    change (∫ ω, S ω ^ 2 ∂P) ≤ m^2+b ∧
      (∫ ω, S ω ^ 3 ∂P) ≤ m^3+3*m*b+c ∧
      (∫ ω, S ω ^ 4 ∂P) ≤ m^4+6*m^2*b+3*b^2+4*m*c+a at ih
    have hprod2 := mul_le_mul_of_nonneg_right ih.1 (by positivity : 0 ≤ 6*v)
    have hprod3 := mul_le_mul_of_nonneg_right ih.2.1 (by positivity : 0 ≤ 4*u)
    have hprod2' := mul_le_mul_of_nonneg_right ih.1 (by positivity : 0 ≤ 3*u)
    simp only [Finset.sum_insert his]
    change (∫ ω, (X i ω + S ω)^2 ∂P) ≤ (u+m)^2+(v+b) ∧
      (∫ ω, (X i ω + S ω)^3 ∂P) ≤ (u+m)^3+3*(u+m)*(v+b)+(w+c) ∧
      (∫ ω, (X i ω + S ω)^4 ∂P) ≤
        (u+m)^4+6*(u+m)^2*(v+b)+3*(v+b)^2+4*(u+m)*(w+c)+(z+a)
    simp_rw [add_comm (X i _) (S _)]
    refine ⟨?_, ?_, ?_⟩
    · nlinarith only [h2, ih.1, sq_nonneg u]
    · nlinarith only [h3, hprod2', mul_nonneg hm (sq_nonneg u),
        pow_nonneg hu 3, mul_nonneg hu hv, ih.2.1]
    · have he := mul_nonneg (sq_nonneg u) hb
      have he' := mul_nonneg (sq_nonneg u) hv
      have he'' := mul_nonneg (sq_nonneg m) hv
      have he''' := mul_nonneg (sq_nonneg m) (sq_nonneg u)
      nlinarith only [h4, hprod2, hprod3, ih.2.2, he, he', he'', he''',
        sq_nonneg v, pow_nonneg hu 4, mul_nonneg hm (pow_nonneg hu 3),
        mul_nonneg (mul_nonneg hm hu) hv, mul_nonneg hu hw]

private theorem lower_powers_le {x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t) :
    x^2 ≤ t*x+x^4/t^2 ∧ x^3 ≤ t^2*x+x^4/t := by
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  by_cases hxt : x ≤ t
  · have h2 := mul_le_mul_of_nonneg_right hxt hx
    have h3 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hxt 2) hx
    constructor
    · nlinarith only [h2, div_nonneg (pow_nonneg hx 4) ht2.le]
    · nlinarith only [h3, div_nonneg (pow_nonneg hx 4) ht.le]
  · have htx : t ≤ x := le_of_lt (lt_of_not_ge hxt)
    have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le htx 2) (sq_nonneg x)
    have h3 := mul_le_mul_of_nonneg_left htx (pow_nonneg hx 3)
    constructor
    · have : x^2 ≤ x^4/t^2 := (le_div_iff₀ ht2).2 (by nlinarith only [h2])
      nlinarith only [this, mul_nonneg ht.le hx]
    · have : x^3 ≤ x^4/t := (le_div_iff₀ ht).2 (by nlinarith only [h3])
      nlinarith only [this, mul_nonneg (sq_nonneg t) hx]

/-- A fixed numerical constant, independent of the finite index set and laws. -/
theorem nonnegative_fourth_moment_le {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 4 P) (h0 : ∀ i, 0 ≤ᵐ[P] X i)
    (hind : iIndepFun X P) (s : Finset ι) :
    (∫ ω, (∑ i ∈ s, X i ω)^4 ∂P) ≤
      34*((∑ i ∈ s, ∫ ω, X i ω^4 ∂P)+(∑ i ∈ s, ∫ ω, X i ω ∂P)^4) := by
  classical
  let S : Ω → ℝ := fun ω => ∑ i ∈ s, X i ω
  let m := ∑ i ∈ s, ∫ ω, X i ω ∂P
  let a := ∑ i ∈ s, ∫ ω, X i ω^4 ∂P
  let b := ∑ i ∈ s, ∫ ω, X i ω^2 ∂P
  let c := ∑ i ∈ s, ∫ ω, X i ω^3 ∂P
  have hm : 0 ≤ m := Finset.sum_nonneg fun i _ => integral_nonneg_of_ae (h0 i)
  have ha : 0 ≤ a := Finset.sum_nonneg fun i _ => integral_nonneg fun ω => by positivity
  have hb : 0 ≤ b := Finset.sum_nonneg fun i _ => integral_nonneg fun ω => sq_nonneg _
  have hc : 0 ≤ c := Finset.sum_nonneg fun i _ =>
    integral_nonneg_of_ae ((h0 i).mono fun ω h => pow_nonneg h _)
  have hS : MemLp S 4 P := memLp_finsetSum s fun i _ => hX i
  have hmean : (∫ ω, S ω ∂P) = m :=
    integral_finsetSum s fun i _ => (hX i).integrable (by norm_num)
  have hbell : (∫ ω, S ω^4 ∂P) ≤ m^4+6*m^2*b+3*b^2+4*m*c+a :=
    (finite_bell_bounds X hX h0 hind s).2.2
  change (∫ ω, S ω^4 ∂P) ≤ 34*(a+m^4)
  by_cases hz : a+m^4 = 0
  · have hm0 : m = 0 := by
      apply eq_zero_of_pow_eq_zero (n := 4)
      linarith only [ha, hz, pow_nonneg hm 4]
    have hS0 : 0 ≤ᵐ[P] S := by
      filter_upwards [(s.eventually_all).mpr (fun i _ => h0 i)] with ω hω
      exact Finset.sum_nonneg fun i hi => hω i hi
    have hzero := (integral_eq_zero_iff_of_nonneg_ae hS0
      (hS.integrable (by norm_num))).mp (hmean.trans hm0)
    have hi0 : (∫ ω, S ω^4 ∂P) = 0 := by
      calc
        _ = ∫ ω, (0:ℝ)^4 ∂P := integral_congr_ae (hzero.mono fun ω h => congrArg (·^4) h)
        _ = 0 := by simp
    rw [hi0, hz]
    norm_num
  · have hpos : 0 < a+m^4 := lt_of_le_of_ne (add_nonneg ha (pow_nonneg hm 4)) (Ne.symm hz)
    let t : ℝ := (a+m^4)^((4:ℝ)⁻¹)
    have ht : 0 < t := Real.rpow_pos_of_pos hpos _
    have ht4 : t^4 = a+m^4 := Real.rpow_inv_natCast_pow hpos.le (by norm_num)
    have hmt : m ≤ t := by
      by_contra h
      have hh := pow_lt_pow_left₀ (lt_of_not_ge h) (le_of_lt ht) (by norm_num : 4 ≠ 0)
      nlinarith only [hh, ht4, ha]
    have hat : a ≤ t^4 := by nlinarith only [ht4, pow_nonneg hm 4]
    have hlow (k : ℕ) (hk : k=2 ∨ k=3) :
        (∑ i ∈ s, ∫ ω, X i ω^k ∂P) ≤
          (if k=2 then t*m+a/t^2 else t^2*m+a/t) := by
      rcases hk with rfl | rfl
      · simp only [ite_true]
        calc
          _ ≤ ∑ i ∈ s, ∫ ω, t*X i ω+X i ω^4/t^2 ∂P := by
            apply Finset.sum_le_sum
            intro i _
            apply integral_mono_ae (integrable_power_four (hX i) (by omega))
              ((((hX i).integrable (by norm_num)).const_mul t).add
                ((integrable_power_four (hX i) (by omega)).div_const (t^2)))
            exact (h0 i).mono fun ω h => (lower_powers_le h ht).1
          _ = t*m+a/t^2 := by
            simp_rw [integral_add (((hX _).integrable (by norm_num)).const_mul t)
              ((integrable_power_four (hX _) (k := 4) (by omega)).div_const (t^2)),
              integral_const_mul, integral_div, Finset.sum_add_distrib,
              ← Finset.mul_sum, ← Finset.sum_div]
            rfl
      · norm_num
        calc
          _ ≤ ∑ i ∈ s, ∫ ω, t^2*X i ω+X i ω^4/t ∂P := by
            apply Finset.sum_le_sum
            intro i _
            apply integral_mono_ae (integrable_power_four (hX i) (by omega))
              ((((hX i).integrable (by norm_num)).const_mul (t^2)).add
                ((integrable_power_four (hX i) (by omega)).div_const t))
            exact (h0 i).mono fun ω h => (lower_powers_le h ht).2
          _ = t^2*m+a/t := by
            simp_rw [integral_add (((hX _).integrable (by norm_num)).const_mul (t^2))
              ((integrable_power_four (hX _) (k := 4) (by omega)).div_const t),
              integral_const_mul, integral_div, Finset.sum_add_distrib,
              ← Finset.mul_sum, ← Finset.sum_div]
            rfl
    have hb0 := hlow 2 (Or.inl rfl)
    have hc0 := hlow 3 (Or.inr rfl)
    norm_num at hb0 hc0
    have hb2 : b ≤ 2*t^2 := by
      have had : a/t^2 ≤ t^2 := (div_le_iff₀ (sq_pos_of_pos ht)).2 (by nlinarith only [hat])
      have htm := mul_le_mul_of_nonneg_left hmt ht.le
      nlinarith only [hb0, had, htm]
    have hc3 : c ≤ 2*t^3 := by
      have had : a/t ≤ t^3 := (div_le_iff₀ ht).2 (by nlinarith only [hat])
      have htm := mul_le_mul_of_nonneg_left hmt (sq_nonneg t)
      nlinarith only [hc0, had, htm]
    have hm2 := pow_le_pow_left₀ hm hmt 2
    have hm4 := pow_le_pow_left₀ hm hmt 4
    have hmb := mul_le_mul hm2 hb2 hb (sq_nonneg t)
    have hbb := pow_le_pow_left₀ hb hb2 2
    have hmc := mul_le_mul hmt hc3 hc ht.le
    nlinarith only [hbell, hm4, hmb, hbb, hmc, hat, ht4]

universe u v
/-- One positive constant works before all probability spaces, finite indices,
individual laws and independent nonnegative L4 variables. -/
theorem exists_nonnegative_fourth_moment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type u) (ι : Type v) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ),
      (∀ i, MemLp (X i) 4 P) → (∀ i, 0 ≤ᵐ[P] X i) → iIndepFun X P →
      ∀ s : Finset ι, (∫ ω, (∑ i ∈ s, X i ω)^4 ∂P) ≤
        C*((∑ i ∈ s, ∫ ω, X i ω^4 ∂P)+(∑ i ∈ s, ∫ ω, X i ω ∂P)^4) := by
  refine ⟨34, by norm_num, ?_⟩
  intro Ω ι _ P _ X hX h0 hind s
  exact nonnegative_fourth_moment_le X hX h0 hind s

end LPPDifferentiability
