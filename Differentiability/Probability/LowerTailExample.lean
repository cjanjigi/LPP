/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Probability.CoordinateLaw
public import LPP_Foundations.Probability.EnvironmentLaw
public import Differentiability.Probability.LowerTailExampleLaw
public import Mathlib.Data.EReal.Basic
public import Mathlib.Probability.BorelCantelli
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# The lower-tail example

This is the example of Appendix C (Lower tail integrability) of the differentiability preprint,
showing that a finite first moment of the negative part cannot be dropped.
The weights are independent with `P (w < -t) = (1 + t) ^ (-α)` for `t ≥ 0`, so
they are almost surely nonpositive. The last passage time `L_{0,x}` is at most
the larger of the two weights at the predecessors `x - e₁` and `x - e₂` (the
path weight used here leaves out the terminal vertex, so the predecessor is
collected). The events `{w_{x-e₁} < -A|x|₁ and w_{x-e₂} < -A|x|₁}`, for `x` in
`{(3i, 3j) : i, j ≥ 1, 1/2 ≤ i/j ≤ 2}`, are independent with divergent
probability sum, and the second Borel-Cantelli lemma, for every positive
integer `A`, gives `liminf L_{0,x} / |x|₁ = -∞` almost surely.
The proof uses only the points `(3i, 3j)` with `i ≤ j ≤ 2i`, which lie in the
set of the preprint. The last passage time inequality is a short argument that the
preprint states in one line.

## References

* C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in the
  planar corner growth model*, preprint, Appendix C.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace LPPDifferentiability

private def tailSite (q : (ℕ × ℕ) × Bool) : Lattice :=
  if q.2 then (3 * (q.1.1 : ℤ) - 1, 3 * (q.1.2 : ℤ))
  else (3 * (q.1.1 : ℤ), 3 * (q.1.2 : ℤ) - 1)

private def tailRegion (x : ℕ × ℕ) : Prop := 1 ≤ x.1 ∧ x.1 ≤ x.2 ∧ x.2 ≤ 2 * x.1

private def tailThreshold (A : ℕ) (x : ℕ × ℕ) : ℝ := (A : ℝ) * ((3 * x.1 + 3 * x.2 : ℕ) : ℝ)

private def tailCut (A : ℕ) (x : ℕ × ℕ) : Set ℝ := {y | tailRegion x ∧ y < -tailThreshold A x}

private def tailEvent (A : ℕ) (q : (ℕ × ℕ) × Bool) : Set Environment :=
  (fun ω : Environment => ω (tailSite q)) ⁻¹' tailCut A q.1

private def tailPair (A : ℕ) (x : ℕ × ℕ) : Set Environment :=
  tailEvent A (x, true) ∩ tailEvent A (x, false)

private theorem tailSite_injective : Function.Injective tailSite := by
  rintro ⟨⟨i, j⟩, b⟩ ⟨⟨i', j'⟩, b'⟩ h
  cases b <;> cases b' <;> simp [tailSite, Prod.ext_iff] at h ⊢ <;> omega

private theorem measurableSet_tailCut (A : ℕ) (x : ℕ × ℕ) : MeasurableSet (tailCut A x) := by
  unfold tailCut
  by_cases h : tailRegion x
  · simp only [h, true_and]
    exact measurableSet_Iio
  · simp [h]

private theorem measurableSet_tailEvent (A : ℕ) (q : (ℕ × ℕ) × Bool) :
    MeasurableSet (tailEvent A q) :=
  measurable_environment_eval (tailSite q) (measurableSet_tailCut A q.1)

private theorem measurableSet_tailPair (A : ℕ) (x : ℕ × ℕ) : MeasurableSet (tailPair A x) :=
  (measurableSet_tailEvent A _).inter (measurableSet_tailEvent A _)

/-- The comparison step: with nonpositive weights, a last passage time to `(a, b)` is at most
the larger weight at the two predecessors. -/
private theorem lastPassage_le_max (ω : Environment) (hω : ∀ z, ω z ≤ 0) (a b : ℕ)
    (hab : 1 ≤ a + b) :
    lastPassage ω 0 (a, b) ≤ max (ω ((a : ℤ) - 1, (b : ℤ))) (ω ((a : ℤ), (b : ℤ) - 1)) := by
  unfold lastPassage
  apply Finset.max'_le
  intro y hy
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hy
  unfold pathWeight
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin (a + b), i0.val = a + b - 1 := ⟨⟨a + b - 1, by omega⟩, rfl⟩
  have hs : i0.succ = Fin.last (a + b) := Fin.ext (by rw [Fin.val_succ, hi0, Fin.val_last]; omega)
  have hfin : p.vertex (Fin.last (a + b)) = ((a : ℤ), (b : ℤ)) := by simpa using p.finish
  have hstep : p.vertex i0.succ = p.vertex i0.castSucc + (1, 0) ∨
      p.vertex i0.succ = p.vertex i0.castSucc + (0, 1) := p.step i0
  have hV : p.vertex i0.castSucc = ((a : ℤ) - 1, (b : ℤ)) ∨
      p.vertex i0.castSucc = ((a : ℤ), (b : ℤ) - 1) := by
    rw [hs, hfin] at hstep
    rcases hstep with h | h
    · left
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at h ⊢
      omega
    · right
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at h ⊢
      omega
  have hsum : ∑ i : Fin (a + b), ω (p.vertex i.castSucc) ≤ ω (p.vertex i0.castSucc) := by
    have h : ω (p.vertex i0.castSucc) + ∑ i ∈ Finset.univ.erase i0, ω (p.vertex i.castSucc) =
      ∑ i : Fin (a + b), ω (p.vertex i.castSucc) :=
    Finset.add_sum_erase Finset.univ (fun i : Fin (a + b) => ω (p.vertex i.castSucc))
      (Finset.mem_univ i0)
    have h0 : ∑ i ∈ Finset.univ.erase i0, ω (p.vertex i.castSucc) ≤ 0 :=
      Finset.sum_nonpos (fun i _ => hω _)
    linarith
  refine hsum.trans ?_
  rcases hV with h | h
  · rw [h]
    exact le_max_left _ _
  · rw [h]
    exact le_max_right _ _

private theorem tailEvent_indep (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : ℕ)
    (T : Finset ((ℕ × ℕ) × Bool)) :
    environmentLaw μ (⋂ q ∈ T, tailEvent A q) = ∏ q ∈ T, environmentLaw μ (tailEvent A q) := by
  have hcoord : iIndepFun (fun q (ω : Environment) => ω (tailSite q)) (environmentLaw μ) :=
    (iIndepFun_environment_eval μ).precomp tailSite_injective
  exact hcoord.meas_biInter (fun q _ => MeasurableSpace.measurableSet_comap.2
    ⟨tailCut A q.1, measurableSet_tailCut A q.1, rfl⟩)

private theorem tailPair_prob (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : ℕ) (x : ℕ × ℕ) :
    environmentLaw μ (tailPair A x) =
      environmentLaw μ (tailEvent A (x, true)) * environmentLaw μ (tailEvent A (x, false)) := by
  have h := tailEvent_indep μ A {(x, true), (x, false)}
  have hnot : ((x, true) : (ℕ × ℕ) × Bool) ∉ ({(x, false)} : Finset ((ℕ × ℕ) × Bool)) := by simp
  rw [Finset.set_biInter_insert, Finset.set_biInter_singleton, Finset.prod_insert hnot,
    Finset.prod_singleton] at h
  exact h

private theorem tailEvent_prob (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : ℕ)
    (q : (ℕ × ℕ) × Bool) : environmentLaw μ (tailEvent A q) = μ (tailCut A q.1) := by
  have h := Measure.map_apply (μ := environmentLaw μ)
    (measurable_environment_eval (tailSite q)) (measurableSet_tailCut A q.1)
  rw [environmentLaw_map_eval] at h
  exact h.symm

private theorem tailPair_prob_cut (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : ℕ)
    (x : ℕ × ℕ) : environmentLaw μ (tailPair A x) = μ (tailCut A x) * μ (tailCut A x) := by
  rw [tailPair_prob, tailEvent_prob, tailEvent_prob]

private theorem tailPair_indep (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : ℕ) :
    iIndepSet (tailPair A) (environmentLaw μ) := by
  have hset : ∀ S : Finset (ℕ × ℕ), (⋂ x ∈ S, tailPair A x) =
      ⋂ q ∈ S ×ˢ (Finset.univ : Finset Bool), tailEvent A q := by
    intro S
    ext ω
    constructor
    · intro h
      rw [Set.mem_iInter₂] at h ⊢
      rintro ⟨x, b⟩ hq
      have hx : x ∈ S := (Finset.mem_product.1 hq).1
      have h' := h x hx
      cases b
      · exact h'.2
      · exact h'.1
    · intro h
      rw [Set.mem_iInter₂] at h ⊢
      intro x hx
      exact ⟨h (x, true) (Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩),
        h (x, false) (Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩)⟩
  rw [iIndepSet_iff_meas_biInter (measurableSet_tailPair A)]
  intro S
  rw [hset S, tailEvent_indep, Finset.prod_product]
  refine Finset.prod_congr rfl (fun x _ => ?_)
  rw [tailPair_prob, Fintype.prod_bool]

private theorem tailCut_measure (μ : Measure ℝ) {α : ℝ}
    (htail : ∀ t : ℝ, 0 ≤ t → μ (Iio (-t)) = ENNReal.ofReal ((1 + t) ^ (-α)))
    (A : ℕ) (x : ℕ × ℕ) (hx : tailRegion x) :
    μ (tailCut A x) = ENNReal.ofReal ((1 + tailThreshold A x) ^ (-α)) := by
  have h : tailCut A x = Iio (-tailThreshold A x) := by
    ext y
    simp [tailCut, hx]
  rw [h]
  exact htail _ (by unfold tailThreshold; positivity)

private theorem tail_inner_lower (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (htail : ∀ t : ℝ, 0 ≤ t → μ (Iio (-t)) = ENNReal.ofReal ((1 + t) ^ (-α)))
    (A : ℕ) (hA : 1 ≤ A) (i : ℕ) :
    ENNReal.ofReal (((10 * A : ℝ) ^ (-α)) ^ 2 * (i : ℝ)⁻¹) ≤
      ∑' j : ℕ, environmentLaw μ (tailPair A (i, j)) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hi0 : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hi.ne'
  have hterm : ∀ j ∈ Finset.Icc i (2 * i),
      ENNReal.ofReal ((10 * A * i : ℝ) ^ (-α) * (10 * A * i : ℝ) ^ (-α)) ≤
        environmentLaw μ (tailPair A (i, j)) := by
    intro j hj
    have hj' := Finset.mem_Icc.1 hj
    have hreg : tailRegion (i, j) := ⟨hi, hj'.1, hj'.2⟩
    have hpos : 0 < 1 + tailThreshold A (i, j) := by unfold tailThreshold; positivity
    rw [tailPair_prob_cut, tailCut_measure μ htail A (i, j) hreg,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hpos.le _)]
    apply ENNReal.ofReal_le_ofReal
    have hj2 : (j : ℝ) ≤ 2 * i := by exact_mod_cast hj'.2
    have h1 : (A : ℝ) * (3 * i + 3 * j) ≤ A * (9 * i) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : (1 : ℝ) ≤ A * i := one_le_mul_of_one_le_of_one_le hA' hi'
    have hthr : 1 + tailThreshold A (i, j) ≤ 10 * A * i := by
      unfold tailThreshold
      push_cast
      linarith
    have hc : (10 * A * i : ℝ) ^ (-α) ≤ (1 + tailThreshold A (i, j)) ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos hpos hthr (by linarith)
    exact mul_self_le_mul_self (Real.rpow_nonneg (by positivity) _) hc
  have hcard : (Finset.Icc i (2 * i)).card = i + 1 := by
    rw [Nat.card_Icc]
    omega
  have hr : (i : ℝ)⁻¹ ≤ (i : ℝ) ^ (-α) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hi' (by linarith)
  have h2 : (i : ℝ)⁻¹ * (i : ℝ)⁻¹ ≤ (i : ℝ) ^ (-α) * (i : ℝ) ^ (-α) :=
    mul_self_le_mul_self (inv_nonneg.2 (Nat.cast_nonneg _)) hr
  have h3 : (i : ℝ)⁻¹ = i * ((i : ℝ)⁻¹ * (i : ℝ)⁻¹) := by
    rw [← mul_assoc, mul_inv_cancel₀ hi0, one_mul]
  have h4 : (i : ℝ)⁻¹ ≤ ((i + 1 : ℕ) : ℝ) * ((i : ℝ) ^ (-α) * (i : ℝ) ^ (-α)) :=
    calc (i : ℝ)⁻¹ = i * ((i : ℝ)⁻¹ * (i : ℝ)⁻¹) := h3
      _ ≤ i * ((i : ℝ) ^ (-α) * (i : ℝ) ^ (-α)) := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
      _ ≤ ((i + 1 : ℕ) : ℝ) * ((i : ℝ) ^ (-α) * (i : ℝ) ^ (-α)) :=
        mul_le_mul_of_nonneg_right (by push_cast; linarith) (mul_self_nonneg _)
  have hc_eq : (10 * A * i : ℝ) ^ (-α) = (10 * A : ℝ) ^ (-α) * (i : ℝ) ^ (-α) :=
    Real.mul_rpow (by positivity) (by positivity)
  have hreal : ((10 * A : ℝ) ^ (-α)) ^ 2 * (i : ℝ)⁻¹ ≤
      ((i + 1 : ℕ) : ℝ) * ((10 * A * i : ℝ) ^ (-α) * (10 * A * i : ℝ) ^ (-α)) :=
    calc ((10 * A : ℝ) ^ (-α)) ^ 2 * (i : ℝ)⁻¹
        ≤ ((10 * A : ℝ) ^ (-α)) ^ 2 * (((i + 1 : ℕ) : ℝ) * ((i : ℝ) ^ (-α) * (i : ℝ) ^ (-α))) :=
          mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
      _ = _ := by rw [hc_eq]; ring
  calc ENNReal.ofReal (((10 * A : ℝ) ^ (-α)) ^ 2 * (i : ℝ)⁻¹)
      ≤ ENNReal.ofReal (((i + 1 : ℕ) : ℝ) *
          ((10 * A * i : ℝ) ^ (-α) * (10 * A * i : ℝ) ^ (-α))) := ENNReal.ofReal_le_ofReal hreal
    _ = ((i + 1 : ℕ) : ENNReal) *
          ENNReal.ofReal ((10 * A * i : ℝ) ^ (-α) * (10 * A * i : ℝ) ^ (-α)) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ = (Finset.Icc i (2 * i)).card •
          ENNReal.ofReal ((10 * A * i : ℝ) ^ (-α) * (10 * A * i : ℝ) ^ (-α)) := by
        rw [hcard, nsmul_eq_mul]
    _ ≤ ∑ j ∈ Finset.Icc i (2 * i), environmentLaw μ (tailPair A (i, j)) :=
        Finset.card_nsmul_le_sum _ _ _ hterm
    _ ≤ ∑' j : ℕ, environmentLaw μ (tailPair A (i, j)) := ENNReal.sum_le_tsum _

private theorem tail_sum_eq_top (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (htail : ∀ t : ℝ, 0 ≤ t → μ (Iio (-t)) = ENNReal.ofReal ((1 + t) ^ (-α)))
    (A : ℕ) (hA : 1 ≤ A) :
    ∑' x : ℕ × ℕ, environmentLaw μ (tailPair A x) = ⊤ := by
  rw [ENNReal.tsum_prod']
  by_contra hne
  have hle : ∑' i : ℕ, ENNReal.ofReal (((10 * A : ℝ) ^ (-α)) ^ 2 * (i : ℝ)⁻¹) ≤
      ∑' i : ℕ, ∑' j : ℕ, environmentLaw μ (tailPair A (i, j)) :=
    ENNReal.tsum_le_tsum (fun i => tail_inner_lower μ hα0 hα1 htail A hA i)
  have hne' := ne_top_of_le_ne_top hne hle
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hu : 0 < (10 * (A : ℝ)) ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
  have hK : 0 < ((10 * (A : ℝ)) ^ (-α)) ^ 2 := pow_pos hu 2
  have hs : Summable (fun i : ℕ => ((10 * (A : ℝ)) ^ (-α)) ^ 2 * (i : ℝ)⁻¹) :=
    (ENNReal.summable_toReal hne').congr
      (fun i => ENNReal.toReal_ofReal (by positivity))
  have hs2 : Summable (fun i : ℕ => (i : ℝ)⁻¹) :=
    (hs.mul_left (((10 * (A : ℝ)) ^ (-α)) ^ 2)⁻¹).congr
      (fun i => inv_mul_cancel_left₀ hK.ne' _)
  exact Real.not_summable_natCast_inv hs2

private theorem tail_ae_frequently (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (htail : ∀ t : ℝ, 0 ≤ t → μ (Iio (-t)) = ENNReal.ofReal ((1 + t) ^ (-α)))
    (A : ℕ) (hA : 1 ≤ A) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ N : ℕ, ∃ x : ℕ × ℕ, N ≤ x.1 + x.2 ∧ ω ∈ tailPair A x := by
  obtain ⟨e, he⟩ : ∃ e : ℕ × ℕ ≃ ℕ, ∀ n, e.symm n = Nat.unpair n :=
    ⟨Nat.pairEquiv, fun _ => rfl⟩
  have hind : iIndepSet (fun n => tailPair A (e.symm n)) (environmentLaw μ) :=
    (tailPair_indep μ A).precomp e.symm.injective
  have hmeas : ∀ n, MeasurableSet (tailPair A (e.symm n)) := fun n => measurableSet_tailPair A _
  have hsum : ∑' n, environmentLaw μ (tailPair A (e.symm n)) = ⊤ :=
    calc ∑' n, environmentLaw μ (tailPair A (e.symm n))
        = ∑' x, environmentLaw μ (tailPair A x) :=
          Equiv.tsum_eq e.symm (fun x => environmentLaw μ (tailPair A x))
      _ = ⊤ := tail_sum_eq_top μ hα0 hα1 htail A hA
  have h1 := measure_limsup_eq_one hmeas hind hsum
  have hS : MeasurableSet (Filter.limsup (fun n => tailPair A (e.symm n)) Filter.atTop) :=
    MeasurableSet.measurableSet_limsup hmeas
  have hae : ∀ᵐ ω ∂environmentLaw μ,
      ω ∈ Filter.limsup (fun n => tailPair A (e.symm n)) Filter.atTop :=
    ae_iff.2 ((prob_compl_eq_zero_iff hS).2 h1)
  filter_upwards [hae] with ω hω N
  rw [Filter.mem_limsup_iff_frequently_mem] at hω
  obtain ⟨n, hnN, hmem⟩ := Filter.frequently_atTop.1 hω (N ^ 2)
  refine ⟨e.symm n, ?_, hmem⟩
  by_contra hlt
  replace hlt := not_le.1 hlt
  rw [he] at hlt
  have hn : Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 = n := Nat.pair_unpair n
  have hmax : max (Nat.unpair n).1 (Nat.unpair n).2 + 1 ≤ N := by
    have : max (Nat.unpair n).1 (Nat.unpair n).2 ≤ (Nat.unpair n).1 + (Nat.unpair n).2 :=
      max_le (by omega) (by omega)
    omega
  have h2 := Nat.pair_lt_max_add_one_sq (Nat.unpair n).1 (Nat.unpair n).2
  have h3 : (max (Nat.unpair n).1 (Nat.unpair n).2 + 1) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hmax 2
  rw [hn] at h2
  exact absurd (h2.trans_le h3) (not_lt.2 hnN)

/-- The lower-tail example, last passage part: for every law `μ` with
`μ (-∞, -t) = (1 + t) ^ (-α)` for `t ≥ 0` and `0 < α < 1`, almost surely
`liminf L_{0,x} / |x|₁ = -∞` over `x` in `{(3i, 3j) : i, j ≥ 1, 1/2 ≤ i/j ≤ 2}` as `|x|₁ → ∞`. -/
theorem lowerTail_liminf_eq_bot (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (htail : ∀ t : ℝ, 0 ≤ t → μ (Iio (-t)) = ENNReal.ofReal ((1 + t) ^ (-α))) :
    ∀ᵐ ω ∂environmentLaw μ,
      Filter.liminf
        (fun x : ℕ × ℕ => ((lastPassage ω 0 x / ((x.1 + x.2 : ℕ) : ℝ) : ℝ) : EReal))
        (Filter.comap (fun x : ℕ × ℕ => x.1 + x.2) Filter.atTop ⊓
          Filter.principal {x : ℕ × ℕ | ∃ i j : ℕ, 1 ≤ i ∧ 1 ≤ j ∧ x = (3 * i, 3 * j) ∧
            (1 / 2 : ℝ) ≤ (i : ℝ) / j ∧ (i : ℝ) / j ≤ 2}) = ⊥ := by
  have hnp : ∀ᵐ ω ∂environmentLaw μ, ∀ z : Lattice, ω z ≤ 0 :=
    ae_all_iff.2 fun z => ae_of_ae_map (p := fun y : ℝ => y ≤ 0)
      (measurable_environment_eval z).aemeasurable
      (by rw [environmentLaw_map_eval μ z]; exact lowerTail_ae_nonpos μ htail)
  have hA : ∀ᵐ ω ∂environmentLaw μ, ∀ A : ℕ, 1 ≤ A →
      ∀ N : ℕ, ∃ x : ℕ × ℕ, N ≤ x.1 + x.2 ∧ ω ∈ tailPair A x :=
    ae_all_iff.2 fun A => by
      by_cases hA : 1 ≤ A
      · filter_upwards [tail_ae_frequently μ hα0 hα1.le htail A hA] with ω h _ using h
      · exact Filter.Eventually.of_forall fun ω h => absurd h hA
  filter_upwards [hnp, hA] with ω hω hAω
  refine (EReal.eq_bot_iff_forall_lt _).2 fun B => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt (1 - B)
  have hA1 : 1 ≤ n + 1 := by omega
  have hAB : -((n + 1 : ℕ) : ℝ) ≤ B - 1 := by push_cast; linarith
  refine lt_of_le_of_lt (Filter.liminf_le_of_frequently_le' (x := ((B - 1 : ℝ) : EReal)) ?_)
    (EReal.coe_lt_coe_iff.2 (by linarith : B - 1 < B))
  rw [Filter.frequently_inf_principal, Filter.frequently_comap, Filter.frequently_atTop]
  intro N
  obtain ⟨x, hxN, hxmem⟩ := hAω (n + 1) hA1 N
  have h1 : tailRegion x ∧ ω (tailSite (x, true)) < -tailThreshold (n + 1) x := hxmem.1
  have h2 : tailRegion x ∧ ω (tailSite (x, false)) < -tailThreshold (n + 1) x := hxmem.2
  obtain ⟨hr1, hr2, hr3⟩ := h1.1
  have e1 : tailSite (x, true) = (3 * (x.1 : ℤ) - 1, 3 * (x.2 : ℤ)) := by simp [tailSite]
  have e2 : tailSite (x, false) = (3 * (x.1 : ℤ), 3 * (x.2 : ℤ) - 1) := by simp [tailSite]
  rw [e1] at h1
  rw [e2] at h2
  have hL : lastPassage ω 0 (3 * x.1, 3 * x.2) ≤
      max (ω (3 * (x.1 : ℤ) - 1, 3 * (x.2 : ℤ))) (ω (3 * (x.1 : ℤ), 3 * (x.2 : ℤ) - 1)) := by
    have := lastPassage_le_max ω hω (3 * x.1) (3 * x.2) (by omega)
    push_cast at this
    exact this
  have hlt : lastPassage ω 0 (3 * x.1, 3 * x.2) < -tailThreshold (n + 1) x :=
    lt_of_le_of_lt hL (max_lt h1.2 h2.2)
  have hs0 : (0 : ℝ) < ((3 * x.1 + 3 * x.2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < 3 * x.1 + 3 * x.2)
  have hx2 : (0 : ℝ) < x.2 := by exact_mod_cast (by omega : 0 < x.2)
  refine ⟨3 * x.1 + 3 * x.2, by omega, (3 * x.1, 3 * x.2), rfl, ?_, ?_⟩
  · refine ⟨x.1, x.2, hr1, by omega, rfl, ?_, ?_⟩
    · rw [le_div_iff₀ hx2]
      have : (x.2 : ℝ) ≤ 2 * x.1 := by exact_mod_cast hr3
      linarith
    · rw [div_le_iff₀ hx2]
      have : (x.1 : ℝ) ≤ x.2 := by exact_mod_cast hr2
      linarith
  · show ((lastPassage ω 0 (3 * x.1, 3 * x.2) / ((3 * x.1 + 3 * x.2 : ℕ) : ℝ) : ℝ) : EReal) ≤
      ((B - 1 : ℝ) : EReal)
    rw [EReal.coe_le_coe_iff, div_le_iff₀ hs0]
    unfold tailThreshold at hlt
    calc lastPassage ω 0 (3 * x.1, 3 * x.2)
        ≤ -(((n + 1 : ℕ) : ℝ) * ((3 * x.1 + 3 * x.2 : ℕ) : ℝ)) := hlt.le
      _ = -((n + 1 : ℕ) : ℝ) * ((3 * x.1 + 3 * x.2 : ℕ) : ℝ) := by ring
      _ ≤ (B - 1) * ((3 * x.1 + 3 * x.2 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hAB hs0.le

/-- The lower-tail example with the hypotheses of the preprint, `0 < p < 1` and
`max p (1/2) < α < 1`, for any law `μ` with `μ (-∞, -t) = (1 + t) ^ (-α)` for `t ≥ 0`:
`E (w⁻) ^ p < ∞`, `E w⁻ = ∞` (extended-valued expectations of the negative part
`w⁻ = max (-w) 0`), and almost surely the liminf of `L_{0,x} / |x|₁` over `x` in
`{(3i, 3j) : i, j ≥ 1, 1/2 ≤ i/j ≤ 2}` as `|x|₁ → ∞` equals `-∞`. -/
theorem lowerTailExample {p α : ℝ} (hp0 : 0 < p) (_hp1 : p < 1) (hα : max p (1 / 2) < α)
    (hα1 : α < 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (htail : ∀ t : ℝ, 0 ≤ t → μ (Iio (-t)) = ENNReal.ofReal ((1 + t) ^ (-α))) :
    (∫⁻ w, ENNReal.ofReal ((max (-w) 0) ^ p) ∂μ < ⊤) ∧
      (∫⁻ w, ENNReal.ofReal (max (-w) 0) ∂μ = ⊤) ∧
      ∀ᵐ ω ∂environmentLaw μ,
        Filter.liminf
          (fun x : ℕ × ℕ => ((lastPassage ω 0 x / ((x.1 + x.2 : ℕ) : ℝ) : ℝ) : EReal))
          (Filter.comap (fun x : ℕ × ℕ => x.1 + x.2) Filter.atTop ⊓
            Filter.principal {x : ℕ × ℕ | ∃ i j : ℕ, 1 ≤ i ∧ 1 ≤ j ∧ x = (3 * i, 3 * j) ∧
              (1 / 2 : ℝ) ≤ (i : ℝ) / j ∧ (i : ℝ) / j ≤ 2}) = ⊥ := by
  have hpα : p < α := lt_of_le_of_lt (le_max_left _ _) hα
  have hα0 : 0 < α := hp0.trans hpα
  exact ⟨lowerTail_lintegral_negPart_rpow_lt_top μ hp0 hpα htail,
    lowerTail_lintegral_negPart_eq_top μ hα0 hα1.le htail,
    lowerTail_liminf_eq_bot μ hα0 hα1 htail⟩

end LPPDifferentiability
