/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RightmostShieldedGridCount
public import ProbabilityBasics.Probability.RectangleConditionalMean
import Busemann.Process.RightmostPathCovariance
import Mathlib.Tactic

/-! A stationary event of locally shielded rightmost paths has measure zero. -/

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped BigOperators Topology

namespace LPP.Busemann

-- Translate the two geometric guards and both independent path times together.
private theorem translated_rightmost_shield
    {Ω : Type*} (T : Lattice → Ω → Ω)
    (B : Lattice → Lattice → Ω → ℝ) (s : Ω) (c : Lattice)
    (hCov : ∀ x y z : Lattice, B (x + z) (y + z) s = B x y (T z s))
    (M1 M2 : ℕ) (a : ℤ)
    (hShield : ∀ v : Lattice,
      v ∉ Set.Icc (0 : Lattice) ((M1 : ℤ), (M2 : ℤ)) →
      (v.1 ≤ 0 ∨ v.2 ≤ 0) → ∀ r t : ℕ,
        rightmostCocyclePath (fun x y => B x y (T c s)) v r ≠
          rightmostCocyclePath (fun x y => B x y (T c s)) (a, (M2 : ℤ)) t) :
    ∀ v : Lattice,
      v ∉ Set.Icc c (c + ((M1 : ℤ), (M2 : ℤ))) →
      (v.1 ≤ c.1 ∨ v.2 ≤ c.2) → ∀ r t : ℕ,
        rightmostCocyclePath (fun x y => B x y s) v r ≠
          rightmostCocyclePath (fun x y => B x y s) (c + (a, (M2 : ℤ))) t := by
  intro v hOut hSide r t hMeet
  have hOutLocal : v - c ∉ Set.Icc (0 : Lattice) ((M1 : ℤ), (M2 : ℤ)) := by
    intro h
    apply hOut
    change (0 ≤ v.1 - c.1 ∧ 0 ≤ v.2 - c.2) ∧
      (v.1 - c.1 ≤ (M1 : ℤ) ∧ v.2 - c.2 ≤ (M2 : ℤ)) at h
    change (c.1 ≤ v.1 ∧ c.2 ≤ v.2) ∧
      (v.1 ≤ c.1 + (M1 : ℤ) ∧ v.2 ≤ c.2 + (M2 : ℤ))
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hSideLocal : (v - c).1 ≤ 0 ∨ (v - c).2 ≤ 0 := by
    change v.1 - c.1 ≤ 0 ∨ v.2 - c.2 ≤ 0
    rcases hSide with hx | hy
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  let C : Lattice → Lattice → ℝ := fun x y => B x y s
  let D : Lattice → Lattice → ℝ := fun x y => B x y (T c s)
  have hDC : ∀ x y, D x y = C (x + c) (y + c) := fun x y => (hCov x y c).symm
  have hLeft : rightmostCocyclePath D (v - c) r + c = rightmostCocyclePath C v r := by
    simpa only [sub_add_cancel] using rightmostCocyclePath_translate C D c hDC (v - c) r
  have hRight := rightmostCocyclePath_translate C D c hDC (a, (M2 : ℤ)) t
  rw [add_comm (a, (M2 : ℤ)) c] at hRight
  exact hShield (v - c) hOutLocal hSideLocal r t
    (add_right_cancel (hLeft.trans (hMeet.trans hRight.symm)))

/-- Conditional ergodic density contradicts the finite boundary count for a
stationary family of local shields. This is the counting closure in GRS,
arXiv:1510.00860v1, Appendix A, lines 1633–1639; the invariant conditional mean
is allowed to be random, and no ergodicity of the whole law is assumed. -/
theorem measure_shielded_rightmost_event_eq_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω)
    (hzero : ∀ s : Ω, T 0 s = s)
    (hadd : ∀ z w : Lattice, ∀ s : Ω, T (z + w) s = T z (T w s))
    (hShift : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (B : Lattice → Lattice → Ω → ℝ)
    (hCov : ∀ x y z : Lattice, ∀ᵐ s ∂P,
      B (x + z) (y + z) s = B x y (T z s))
    (M1 M2 : ℕ)
    (E : Set Ω) (hEMeas : MeasurableSet E)
    (hShield : ∀ s ∈ E, ∃ a : ℤ, 0 < a ∧ a < (M1 : ℤ) ∧
      ∀ v : Lattice,
        v ∉ Set.Icc (0 : Lattice) ((M1 : ℤ), (M2 : ℤ)) →
        (v.1 ≤ 0 ∨ v.2 ≤ 0) → ∀ r t : ℕ,
          rightmostCocyclePath (fun x y => B x y s) v r ≠
            rightmostCocyclePath (fun x y => B x y s) (a, (M2 : ℤ)) t) :
    P E = 0 := by
  classical
  by_contra hNonzero
  -- Space the cells by one lattice gap and retain the exact signed action.
  let c : Lattice → Lattice := fun z =>
    (((M1 : ℤ) + 1) * z.1, ((M2 : ℤ) + 1) * z.2)
  let T' : Lattice → Ω → Ω := fun z => T (c z)
  have hcZero : c 0 = 0 := by ext <;> simp only [c, Prod.fst_zero, Prod.snd_zero, mul_zero]
  have hcAdd (z w : Lattice) : c (z + w) = c z + c w := by
    ext <;> simp only [c, Prod.fst_add, Prod.snd_add, mul_add]
  have hzero' (s : Ω) : T' 0 s = s := by
    dsimp only [T']
    rw [hcZero, hzero]
  have hadd' (z w : Lattice) (s : Ω) : T' (z + w) s = T' z (T' w s) := by
    dsimp only [T']
    rw [hcAdd, hadd]
  have hShift' (z : Lattice) : MeasurePreserving (T' z) P P := hShift (c z)

  -- The invariant field belongs to this scaled action and the original ambient.
  let mΩ : MeasurableSpace Ω := inferInstance
  let I : MeasurableSpace Ω := ⨅ z : Lattice, @MeasurableSpace.invariants Ω mΩ (T' z)
  let : MeasurableSpace Ω := mΩ
  have hIle : I ≤ mΩ :=
    (iInf_le (fun z : Lattice => @MeasurableSpace.invariants Ω mΩ (T' z)) 0).trans
      (MeasurableSpace.invariants_le (T' 0))
  let f : Ω → ℝ := E.indicator 1
  have hf : Integrable f P := (integrable_const (1 : ℝ)).indicator hEMeas
  have hfNonneg : 0 ≤ᵐ[P] f := by
    filter_upwards [] with s
    simp only [f, Set.indicator_apply, Pi.one_apply]
    split_ifs <;> norm_num
  let g : Ω → ℝ := P[f | I]
  have hgInt : Integrable g P := integrable_condExp
  have hgNonneg : 0 ≤ᵐ[P] g := condExp_nonneg hfNonneg
  have hIntegral : (∫ s, g s ∂P) = (P E).toReal := by
    calc
      _ = ∫ s, f s ∂P := integral_condExp hIle
      _ = P.real E := integral_indicator_one hEMeas
      _ = (P E).toReal := rfl
  have hIntegralPos : 0 < ∫ s, g s ∂P := by
    rw [hIntegral]
    exact ENNReal.toReal_pos hNonzero (measure_ne_top P E)
  have hSupportPos : 0 < P (Function.support g) :=
    (integral_pos_iff_support_of_nonneg_ae hgNonneg hgInt).mp hIntegralPos
  have hSupportAE : Function.support g =ᵐ[P] {s : Ω | 0 < g s} := by
    filter_upwards [hgNonneg] with s hs
    apply propext
    change (g s ≠ 0) ↔ 0 < g s
    exact ⟨fun hn => lt_of_le_of_ne hs hn.symm, ne_of_gt⟩
  have hPositiveG : 0 < P {s : Ω | 0 < g s} := by
    rw [← measure_congr hSupportAE]
    exact hSupportPos

  -- The actual half-open rectangle export has denominator n², not (n+1)².
  let Q (n : ℕ) : Finset Lattice :=
    (Finset.Ico (0 : ℤ) (n : ℤ)).product (Finset.Ico (0 : ℤ) (n : ℤ))
  have hLimit : ∀ᵐ s ∂P, Tendsto
      (fun n : ℕ => (∑ p ∈ Q n, f (T' p s)) / (n : ℝ)^2) atTop (𝓝 (g s)) := by
    simpa only [Q, mul_one, Nat.floor_natCast, one_mul, g, I] using
      ProbabilityBasics.ae_tendsto_prefix_rectangle_condExp P T' hzero' hadd' hShift'
        f hf (fun _ => (1 : ℝ)) (fun _ => zero_lt_one)
  have hCovAll : ∀ᵐ s ∂P, ∀ x y z : Lattice,
      B (x + z) (y + z) s = B x y (T z s) :=
    ae_all_iff.mpr fun x => ae_all_iff.mpr fun y => ae_all_iff.mpr fun z => hCov x y z
  -- Select a positive-density sample only after ALL covariance coordinates.
  have hSample : ∃ s : Ω, 0 < g s ∧
      (∀ x y z : Lattice, B (x + z) (y + z) s = B x y (T z s)) ∧
      Tendsto (fun n : ℕ => (∑ p ∈ Q n, f (T' p s)) / (n : ℝ)^2)
        atTop (𝓝 (g s)) := by
    by_contra hNone
    have hz : P {s : Ω | 0 < g s} = 0 := measure_eq_zero_iff_ae_notMem.mpr (by
      filter_upwards [hCovAll, hLimit] with s hc hl
      intro hs
      exact hNone ⟨s, hs, hc, hl⟩)
    exact (ne_of_gt hPositiveG) hz
  obtain ⟨s, hsPos, hsCov, hsLimit⟩ := hSample

  -- These pointwise finite choices need no measurable selection of shields.
  let S (n : ℕ) : Finset Lattice := (Q n).filter fun p => T' p s ∈ E
  have hIndices (n : ℕ) (p : Lattice) (hp : p ∈ S n) :
      0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2 ∧ p.2 < (n : ℤ) := by
    have hq := (Finset.mem_filter.mp hp).1
    have h := Finset.mem_product.mp hq
    exact ⟨(Finset.mem_Ico.mp h.1).1, (Finset.mem_Ico.mp h.1).2,
      (Finset.mem_Ico.mp h.2).1, (Finset.mem_Ico.mp h.2).2⟩
  have hGridShield (n : ℕ) (p : Lattice) (hp : p ∈ S n) :
      ∃ a : ℤ, 0 < a ∧ a < (M1 : ℤ) ∧
        ∀ v : Lattice, v ∉ Set.Icc (c p) (c p + ((M1 : ℤ), (M2 : ℤ))) →
          (v.1 ≤ (c p).1 ∨ v.2 ≤ (c p).2) → ∀ r t : ℕ,
            rightmostCocyclePath (fun x y => B x y s) v r ≠
              rightmostCocyclePath (fun x y => B x y s) (c p + (a, (M2 : ℤ))) t := by
    obtain ⟨a, ha0, haM, ha⟩ := hShield (T' p s) (Finset.mem_filter.mp hp).2
    exact ⟨a, ha0, haM, translated_rightmost_shield T B s (c p) hsCov M1 M2 a ha⟩
  let d : ℕ := max (M1 + 1) (M2 + 1)
  have hCount (n : ℕ) : (S n).card ≤ 2 * (d * n) + 1 :=
    card_shielded_rightmost_grid_cells_le (fun x y => B x y s) M1 M2 n (S n)
      (hIndices n) (hGridShield n)
  have hSum (n : ℕ) : (∑ p ∈ Q n, f (T' p s)) = ((S n).card : ℝ) := by
    simp only [f, Set.indicator_apply, Pi.one_apply, Finset.sum_boole, S]

  -- The linear boundary bound makes the same actual quadratic averages vanish.
  have hUpperLimit : Tendsto
      (fun n : ℕ => (2 * (d : ℝ) * (n : ℝ) + 1) / (n : ℝ)^2) atTop (𝓝 0) := by
    have h1 := tendsto_const_div_atTop_nhds_zero_nat (2 * (d : ℝ))
    have h2 := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).mul
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hh := h1.add h2
    apply (show Tendsto (fun n : ℕ => (2 * (d : ℝ)) / (n : ℝ) +
      (1 / (n : ℝ)) * (1 / (n : ℝ))) atTop (𝓝 (0 : ℝ)) by simpa only [add_zero, mul_zero] using hh).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    field_simp [hn0]
  have hZeroLimit : Tendsto
      (fun n : ℕ => (∑ p ∈ Q n, f (T' p s)) / (n : ℝ)^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => ?_) (fun n => ?_) hUpperLimit
    · rw [hSum]
      positivity
    · rw [hSum]
      apply div_le_div_of_nonneg_right _ (sq_nonneg (n : ℝ))
      have hc : ((S n).card : ℝ) ≤ 2 * ((d : ℝ) * (n : ℝ)) + 1 := by
        exact_mod_cast hCount n
      simpa only [mul_assoc] using hc
  have hValue : g s = 0 := tendsto_nhds_unique hsLimit hZeroLimit
  exact (ne_of_gt hsPos) hValue

end LPP.Busemann
