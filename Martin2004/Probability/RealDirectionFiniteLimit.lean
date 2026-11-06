/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.RealDirectionFiniteLimitTransfer
public import LPP_Foundations.Probability.TranslationErgodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Tactic

/-!
# Real direction, finite case: the almost-sure and L1 limit

Martin (2004), Proposition 2.1 (i) says that `T(⌊n x⌋)/n` tends to `g(x)` almost surely, and in L1
when `g(x)` is finite. Martin gives no argument when the fractional parts of `n x` keep changing.
This file finishes the argument, using a random phase, for a direction whose expected rate is
finite.

* `exists_random_phase_limit` gives a limit `Y` on the product of the phase law and the
  environment law.
* Fubini picks one phase `θ₀` at which the convergence holds for almost every environment.
* `RealDirectionFiniteLimitTransfer` brings the limit back to phase 0.
* The phase-0 limit `L` satisfies `L ∘ τ ≤ L` for one lattice translation `τ` (translation,
  superadditivity (2.2) and the box lower bound), and `τ` preserves the law, so `L ∘ τ = L` almost
  surely. Ergodicity of `τ` makes `L` a constant `c`.
* The L1 transfer gives `E |T(⌊n x⌋)/n - c| → 0`, so `E T(⌊n x⌋)/n → c`, and the limit of the
  expected rate identifies `c = g(x)`.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace LPPDifferentiability

/-- If `L ∘ τ ≤ L` almost surely for a measure-preserving map `τ` of a probability space, then
`L ∘ τ = L` almost surely. Compare the integrals of the bounded function `arctan ∘ L`. -/
private theorem ae_eq_of_ae_le_of_measurePreserving {α : Type*} [MeasurableSpace α]
    {P : Measure α} [IsProbabilityMeasure P] {τ : α → α} (hτ : MeasurePreserving τ P P)
    {L : α → ℝ} (hL : Measurable L) (hle : ∀ᵐ a ∂P, L (τ a) ≤ L a) :
    (fun a => L (τ a)) =ᵐ[P] L := by
  have hbdd : ∀ f : α → ℝ, Measurable f → Integrable (fun a => Real.arctan (f a)) P := by
    intro f hf
    refine (integrable_const (Real.pi / 2)).mono'
      (Real.continuous_arctan.measurable.comp hf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  have hA := hbdd L hL
  have hAτ := hbdd (fun a => L (τ a)) (hL.comp hτ.measurable)
  have hmean : ∫ a, Real.arctan (L (τ a)) ∂P = ∫ a, Real.arctan (L a) ∂P := by
    have h := integral_map (μ := P) hτ.measurable.aemeasurable
      (f := fun a => Real.arctan (L a))
      (by rw [hτ.map_eq]; exact hA.aestronglyMeasurable)
    rw [hτ.map_eq] at h
    exact h.symm
  have hle' : (fun a => Real.arctan (L (τ a))) ≤ᵐ[P] fun a => Real.arctan (L a) :=
    hle.mono fun a h => Real.arctan_strictMono.monotone h
  have heq := (integral_eq_iff_of_ae_le hAτ hA hle').mp hmean
  exact heq.mono fun a h => Real.arctan_injective h

/-- Pathwise step of the constancy argument: translating the environment by `e`, then using
superadditivity (2.2) of Martin (2004) on `0 ≤ e ≤ a + e ≤ B` and the box lower bound on the last
piece. -/
private theorem lastPassage_translate_le (ω : Environment) (e a B : ℕ × ℕ) (D' : ℕ) (S : ℝ)
    (hS : S = ∑ o ∈ Finset.Icc ((-(D' : ℤ)), (-(D' : ℤ))) ((D' : ℤ), (D' : ℤ)),
      |ω (((a.1 : ℤ), (a.2 : ℤ)) + o)|)
    (h1 : a + e ≤ B) (h2 : B.1 ≤ a.1 + D') (h3 : B.2 ≤ a.2 + D') :
    lastPassage (fun z => ω (((e.1 : ℤ), (e.2 : ℤ)) + z)) 0 a ≤
      lastPassage ω 0 B + 2 * D' * S - lastPassage ω 0 e := by
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1' := Prod.le_def.mp h1
  obtain ⟨d, hd1, hd2⟩ : ∃ d : ℕ × ℕ, B.1 = (e + a).1 + d.1 ∧ B.2 = (e + a).2 + d.2 :=
    ⟨(B.1 - (e + a).1, B.2 - (e + a).2), by simp only [Prod.fst_add, Prod.snd_add] at h1' ⊢; omega,
      by simp only [Prod.fst_add, Prod.snd_add] at h1' ⊢; omega⟩
  have hB : e + a + d = B := Prod.ext (by show (e + a).1 + d.1 = B.1; omega)
    (by show (e + a).2 + d.2 = B.2; omega)
  have htr : lastPassage (fun z => ω (((e.1 : ℤ), (e.2 : ℤ)) + z)) 0 a =
      lastPassage ω (((e.1 : ℤ), (e.2 : ℤ))) a := by
    rw [lastPassage_translate, add_zero]
  have hsup1 := lastPassage_superadditive ω 0 e a
  rw [zero_add] at hsup1
  have hsup2 := lastPassage_superadditive ω 0 (e + a) d
  rw [zero_add, hB] at hsup2
  have hbox := lastPassage_box_lower_bound ω ((e + a).1 : ℤ) ((e + a).2 : ℤ) d S
    (fun z g1 g2 g3 g4 => by
      have hmem : z - ((a.1 : ℤ), (a.2 : ℤ)) ∈
          Finset.Icc ((-(D' : ℤ)), (-(D' : ℤ))) ((D' : ℤ), (D' : ℤ)) := by
        rw [Finset.mem_Icc, Prod.le_def, Prod.le_def]
        simp only [Prod.fst_sub, Prod.snd_sub]
        have k1 : (((e + a).1 : ℕ) : ℤ) = (e.1 : ℤ) + (a.1 : ℤ) := by simp
        have k2 : (((e + a).2 : ℕ) : ℤ) = (e.2 : ℤ) + (a.2 : ℤ) := by simp
        have q1 : (a + e).1 = a.1 + e.1 := rfl
        have q2 : (a + e).2 = a.2 + e.2 := rfl
        omega
      have h := Finset.single_le_sum (f := fun o => |ω (((a.1 : ℤ), (a.2 : ℤ)) + o)|)
        (fun _ _ => abs_nonneg _) hmem
      rw [add_sub_cancel] at h
      rw [hS]
      exact (abs_le.mp h).1)
  have hdsum : ((d.1 + d.2 : ℕ) : ℝ) ≤ 2 * D' := by
    have : d.1 + d.2 ≤ 2 * D' := by simp only [Prod.fst_add, Prod.snd_add] at hd1 hd2; omega
    exact_mod_cast this
  have hbd : ((d.1 + d.2 : ℕ) : ℝ) * S ≤ 2 * D' * S := mul_le_mul_of_nonneg_right hdsum hS0
  rw [htr]
  rw [mul_neg] at hbox
  have : lastPassage ω 0 (e + a) ≤ lastPassage ω 0 B + 2 * D' * S := by
    linarith
  linarith


/-- Constancy of the phase-0 limit. If `L` is the almost-sure limit of `T(⌊n x⌋)/n`, and `e` is a
unit step with `b_n + e ≤ b_{n+j}` and gaps at most `D`, then `L` is almost surely constant:
`L ∘ τ_e ≤ L`, equality by the law-preserving argument, and ergodicity of the translation `τ_e`. -/
private theorem ae_eq_const_of_step (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : ℝ × ℝ) (e : ℕ × ℕ) (he : e = (1, 0) ∨ e = (0, 1))
    (j' D' : ℕ)
    (hstep : ∀ n : ℕ, (⌊(n : ℝ) * x.1⌋₊, ⌊(n : ℝ) * x.2⌋₊) + e ≤
      (⌊((n + j' : ℕ) : ℝ) * x.1⌋₊, ⌊((n + j' : ℕ) : ℝ) * x.2⌋₊))
    (hgap : ∀ n : ℕ, ⌊((n + j' : ℕ) : ℝ) * x.1⌋₊ ≤ ⌊(n : ℝ) * x.1⌋₊ + D' ∧
      ⌊((n + j' : ℕ) : ℝ) * x.2⌋₊ ≤ ⌊(n : ℝ) * x.2⌋₊ + D')
    (L : Environment → ℝ) (hLm : Measurable L)
    (hL : ∀ᵐ ω ∂environmentLaw μ,
      Tendsto (fun n : ℕ => lastPassage ω 0 (⌊(n : ℝ) * x.1⌋₊, ⌊(n : ℝ) * x.2⌋₊) / (n : ℝ))
        atTop (𝓝 (L ω))) :
    ∃ c : ℝ, ∀ᵐ ω ∂environmentLaw μ, L ω = c := by
  set v : Lattice := ((e.1 : ℤ), (e.2 : ℤ)) with hv
  have hv0 : v ≠ 0 := by
    rcases he with rfl | rfl <;> simp [hv, Prod.ext_iff]
  have hτ := measurePreserving_environment_translation μ v
  have hLτ := hτ.quasiMeasurePreserving.ae hL
  have hbox := ae_box_sum_div_tendsto_zero μ hμ x D' D'
  have hle : ∀ᵐ ω ∂environmentLaw μ, L (fun z => ω (v + z)) ≤ L ω := by
    filter_upwards [hL, hLτ, hbox] with ω h1 h2 h3
    have hX : Tendsto (fun n : ℕ => lastPassage ω 0
        (⌊((n + j' : ℕ) : ℝ) * x.1⌋₊, ⌊((n + j' : ℕ) : ℝ) * x.2⌋₊) / ((n + j' : ℕ) : ℝ))
        atTop (𝓝 (L ω)) :=
      (tendsto_add_atTop_iff_nat (f := fun n : ℕ => lastPassage ω 0
        (⌊(n : ℝ) * x.1⌋₊, ⌊(n : ℝ) * x.2⌋₊) / (n : ℝ)) j').mpr h1
    have hratio : Tendsto (fun n : ℕ => 1 + (j' : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
        (tendsto_const_div_atTop_nhds_zero_nat (j' : ℝ))
    have hsum := tendsto_const_div_atTop_nhds_zero_nat
      (lastPassage ω 0 e)
    have hr := ((hX.mul hratio).add (h3.const_mul (2 * (D' : ℝ)))).sub hsum
    refine le_of_tendsto_of_tendsto h2 (by simpa using hr) ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hnj : ((n + j' : ℕ) : ℝ) ≠ 0 := by positivity
    have hpath := lastPassage_translate_le ω e (⌊(n : ℝ) * x.1⌋₊, ⌊(n : ℝ) * x.2⌋₊)
      (⌊((n + j' : ℕ) : ℝ) * x.1⌋₊, ⌊((n + j' : ℕ) : ℝ) * x.2⌋₊) D' _ rfl (hstep n)
      (hgap n).1 (hgap n).2
    have hdiv := div_le_div_of_nonneg_right hpath (Nat.cast_nonneg n)
    refine hdiv.trans (le_of_eq ?_)
    push_cast at hnj ⊢
    field_simp
  have heq := ae_eq_of_ae_le_of_measurePreserving hτ hLm hle
  obtain ⟨c, hc⟩ := (ergodic_environment_translation μ v hv0).ae_eq_const_of_ae_eq_comp_ae
    hLm.aestronglyMeasurable heq
  exact ⟨c, hc⟩


/-- Martin (2004), Proposition 2.1 (i), finite case, in every real direction (Martin gives no proof
for non-lattice directions; the random phase supplies one). Let `μ` have a finite mean and let `x`
be a direction in the closed quadrant whose expected rate `E T(⌊n x⌋)/n` tends in `EReal` to
`g ≠ +∞`. Then `T(⌊n x⌋)/n → g` almost surely, and in L1. -/
theorem tendsto_lastPassage_floor_ae_and_L1 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : Quadrant) (g : EReal)
    (hg : Tendsto (fun n : ℕ => ((((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) /
        (n : ℝ)) : ℝ) : EReal)) atTop (𝓝 g))
    (hgtop : g ≠ ⊤) :
    (∀ᵐ ω ∂environmentLaw μ,
      Tendsto (fun n : ℕ => lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) / (n : ℝ)) atTop (𝓝 g.toReal)) ∧
    Tendsto (fun n : ℕ => ∫ ω, |lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) / (n : ℝ) - g.toReal|
        ∂environmentLaw μ) atTop (𝓝 0) := by
  set x' : ℝ × ℝ := ((x.1 : ℝ), (x.2 : ℝ)) with hx'
  have hx1 : 0 ≤ x'.1 := NNReal.coe_nonneg _
  have hx2 : 0 ≤ x'.2 := NNReal.coe_nonneg _
  by_cases hzero : x'.1 = 0 ∧ x'.2 = 0
  · -- the zero direction: every passage time is `T(0, 0) = 0`
    have hT0 : ∀ (n : ℕ) (ω : Environment), lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) = 0 := by
      intro n ω
      have h1 : (x.1 : ℝ) = 0 := hzero.1
      have h2 : (x.2 : ℝ) = 0 := hzero.2
      simp [h1, h2]
    have hg0 : g = ((0 : ℝ) : EReal) := by
      refine tendsto_nhds_unique hg ?_
      simp only [hT0, integral_zero, zero_div, EReal.coe_zero]
      exact tendsto_const_nhds
    simp only [hT0, hg0, EReal.toReal_coe, zero_div, sub_zero, abs_zero, integral_zero]
    exact ⟨Filter.Eventually.of_forall fun _ => tendsto_const_nhds, tendsto_const_nhds⟩
  -- Step 1: the limit on the product space and the choice of a phase
  obtain ⟨Y, hYm, hYi, hYae, hYL1⟩ := exists_random_phase_limit μ hμ x g hg hgtop
  have hgood := Measure.ae_ae_of_ae_prod hYae
  obtain ⟨θ0, hθ0, hθ0sq⟩ := (hgood.and ae_phase_in_unit_square).exists
  have hLm : Measurable (fun ω : Environment => Y (θ0, ω)) :=
    hYm.comp (measurable_const.prodMk measurable_id)
  -- Step 2: transfer to phase 0
  have hLconv : ∀ᵐ ω ∂environmentLaw μ,
      Tendsto (fun n : ℕ => lastPassage ω 0 (⌊(n : ℝ) * x'.1⌋₊, ⌊(n : ℝ) * x'.2⌋₊) / (n : ℝ))
        atTop (𝓝 (Y (θ0, ω))) :=
    ae_tendsto_floor_of_phase_tendsto μ hμ x' hx1 hx2 θ0 hθ0sq.1 hθ0sq.2
      (fun ω => Y (θ0, ω)) hθ0
  have hYL : ∀ᵐ θ ∂((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ico (0 : ℝ) 1))),
      ∀ᵐ ω ∂environmentLaw μ, Y (θ, ω) = Y (θ0, ω) := by
    filter_upwards [hgood, ae_phase_in_unit_square] with θ hθ hsq
    have h := ae_tendsto_floor_of_phase_tendsto μ hμ x' hx1 hx2 θ hsq.1 hsq.2
      (fun ω => Y (θ, ω)) hθ
    filter_upwards [h, hLconv] with ω h1 h2
    exact tendsto_nhds_unique h1 h2
  -- Step 3: the limit is a constant
  obtain ⟨j, D, hj, hj1, hj2, hD1, hD2⟩ := exists_floor_step_count x' hx1 hx2
  have hgap : ∀ n : ℕ, ⌊((n + j : ℕ) : ℝ) * x'.1⌋₊ ≤ ⌊(n : ℝ) * x'.1⌋₊ + D ∧
      ⌊((n + j : ℕ) : ℝ) * x'.2⌋₊ ≤ ⌊(n : ℝ) * x'.2⌋₊ + D := fun n => by
    have h := floor_phase_gap_le x' (0, 0) j n D hx1 hx2 le_rfl le_rfl hD1 hD2
    simpa only [add_zero] using h
  obtain ⟨e, he, hstep⟩ : ∃ e : ℕ × ℕ, (e = (1, 0) ∨ e = (0, 1)) ∧ ∀ n : ℕ,
      (⌊(n : ℝ) * x'.1⌋₊, ⌊(n : ℝ) * x'.2⌋₊) + e ≤
        (⌊((n + j : ℕ) : ℝ) * x'.1⌋₊, ⌊((n + j : ℕ) : ℝ) * x'.2⌋₊) := by
    rcases hx1.eq_or_lt with h0 | hpos
    · have hpos2 : 0 < x'.2 := lt_of_le_of_ne hx2 fun h => hzero ⟨h0.symm, h.symm⟩
      exact ⟨(0, 1), Or.inr rfl, fun n =>
        floor_add_unit_le_floor_snd x' j n hpos2 hx1 (hj2.resolve_left hpos2.ne')⟩
    · exact ⟨(1, 0), Or.inl rfl, fun n =>
        floor_add_unit_le_floor_fst x' j n hpos hx2 (hj1.resolve_left hpos.ne')⟩
  obtain ⟨c, hc⟩ := ae_eq_const_of_step μ hμ x' e he j D hstep hgap
    (fun ω => Y (θ0, ω)) hLm hLconv
  have hYc : ∀ᵐ p ∂(((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ico (0 : ℝ) 1))).prod
      (environmentLaw μ)), Y p = c := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem (s := {p | Y p = c})
      (hYm (measurableSet_singleton c))).mpr ?_
    filter_upwards [hYL] with θ h
    filter_upwards [h, hc] with ω h1 h2
    exact h1.trans h2
  -- Step 4: L1 convergence to `c` and identification of `c`
  have hL1c := hYL1.congr fun n => integral_congr_ae (by
    filter_upwards [hYc] with p hp
    rw [hp])
  have hL1T := tendsto_integral_abs_floor_of_phase μ hμ x' hx1 hx2 c hL1c
  have hmean : Tendsto (fun n : ℕ => (∫ ω : Environment, lastPassage ω 0
      (⌊(n : ℝ) * x'.1⌋₊, ⌊(n : ℝ) * x'.2⌋₊) ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 c) := by
    refine tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hL1T)
    have hint : Integrable (fun ω : Environment => lastPassage ω 0
        (⌊(n : ℝ) * x'.1⌋₊, ⌊(n : ℝ) * x'.2⌋₊) / (n : ℝ) - c) (environmentLaw μ) :=
      ((integrable_lastPassage μ hμ 0 _).div_const _).sub (integrable_const c)
    rw [Real.dist_eq, ← integral_div]
    have : (∫ ω : Environment, lastPassage ω 0 (⌊(n : ℝ) * x'.1⌋₊, ⌊(n : ℝ) * x'.2⌋₊) / (n : ℝ)
        ∂environmentLaw μ) - c = ∫ ω : Environment, (lastPassage ω 0
          (⌊(n : ℝ) * x'.1⌋₊, ⌊(n : ℝ) * x'.2⌋₊) / (n : ℝ) - c) ∂environmentLaw μ := by
      rw [integral_sub ((integrable_lastPassage μ hμ 0 _).div_const _) (integrable_const c)]
      simp
    rw [this]
    exact (abs_integral_le_integral_abs).trans_eq rfl
  have hgbot : g ≠ ⊥ := (expected_floor_rate_ereal_bot_lt μ hμ x g hg).ne'
  have hgeq : ((g.toReal : ℝ) : EReal) = g := EReal.coe_toReal hgtop hgbot
  have hg' : Tendsto (fun n : ℕ => (∫ ω : Environment, lastPassage ω 0
      (⌊(n : ℝ) * x'.1⌋₊, ⌊(n : ℝ) * x'.2⌋₊) ∂environmentLaw μ) / (n : ℝ)) atTop
      (𝓝 g.toReal) := by
    rw [← hgeq] at hg
    exact EReal.tendsto_coe.mp hg
  have hcg : c = g.toReal := tendsto_nhds_unique hmean hg'
  subst hcg
  exact ⟨by filter_upwards [hLconv, hc] with ω h1 h2; rwa [h2] at h1, hL1T⟩

end LPPDifferentiability
