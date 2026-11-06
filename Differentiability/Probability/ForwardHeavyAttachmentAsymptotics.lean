/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.HeavyAttachmentScaleParameters
public import Differentiability.Probability.ForwardHeavyAttachmentProbability

/-!
# Forward heavy-attachment net with asymptotic success probability

This file combines the parameter choices and the probability estimates of the forward heavy
attachment construction. It gives one net of sites and, for each large scale `s`, a set of
environments whose probability tends to one, on which every path of the family has weight at
least `-eta * s / 4`.
-/

public section
open MeasureTheory Set Filter
open scoped Classical ENNReal Topology
namespace LPPDifferentiability

/-- The common net and the family of paths from its points work at every sufficiently large
scale, uniformly in the level `I` and the interval `[lo, hi]`. -/
theorem exists_forward_heavy_attachment_asymptotics
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p a D eta kappa : ℝ)
    (hp : 1 < p) (ha : a ∈ Ioo (0 : ℝ) 1) (hD : 1 ≤ D)
    (heta : 0 < eta) (hkappa : 0 < kappa) (hkappa16 : kappa ≤ 1/16)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0)^p) ∂μ) < ∞)
    (hkappaBudget : kappa ≤ eta/(16*(∫ x, max (-x) 0 ∂μ)+16)) :
    ∃ K : ℕ, 2 ≤ K ∧ 4 ≤ (K:ℝ)*(p-1) ∧
    ∃ p_att : ℝ → ℝ, Tendsto p_att atTop (𝓝 1) ∧
      ∀ᶠ s : ℝ in atTop,
        0 ≤ p_att s ∧ p_att s ≤ 1 ∧
        ∀ (I : ℤ) (lo hi : ℝ), lo ≤ hi → hi-lo ≤ D*s →
        let m := Nat.ceil (kappa*s)
        let rho := fun z : Lattice => (1-a)*(z.1:ℝ)-a*(z.2:ℝ)
        ∃ (J : Finset Lattice) (M : ℕ) (v : Fin (M+1) → Lattice)
          (j : J → Fin (M+1)) (d : J → ℕ × ℕ),
          (∀ u, u ∈ J ↔ u.1+u.2=I ∧ rho u ∈ Icc lo hi) ∧
          (J.card:ℝ) ≤ D*s+1 ∧
          1 ≤ M ∧ Function.Injective v ∧
          (∀ k, (v k).1+(v k).2=I+(m:ℤ) ∧
            rho (v k) ∈ Icc (lo-a*(m:ℝ)) (hi+(1-a)*(m:ℝ))) ∧
          (∀ (k : ℕ) (hk : k < M),
            min a (1-a)*(m:ℝ)/4 ≤ rho (v ⟨k+1, by omega⟩)-rho (v ⟨k, by omega⟩) ∧
            rho (v ⟨k+1, by omega⟩)-rho (v ⟨k, by omega⟩) ≤ min a (1-a)*(m:ℝ)/2) ∧
          (∀ k, (rho (v k) ≤ lo-a*(m:ℝ)+min a (1-a)*(m:ℝ)/2) ↔ k.val=0) ∧
          (∀ k, (hi+(1-a)*(m:ℝ)-min a (1-a)*(m:ℝ)/2 ≤ rho (v k)) ↔ k.val=M) ∧
          rho (v ⟨0, by omega⟩) ≤ lo-a*(m:ℝ)+min a (1-a)*(m:ℝ)/2 ∧
          hi+(1-a)*(m:ℝ)-min a (1-a)*(m:ℝ)/2 ≤ rho (v ⟨M, by omega⟩) ∧
          (M+1:ℝ) < 4*(hi-lo+(m:ℝ))/(min a (1-a)*(m:ℝ)) ∧
          (M+1:ℝ) ≤ 8*D/(min a (1-a)*kappa)+2 ∧
          (∀ u, (d u).1+(d u).2=m ∧
            u.val+(((d u).1:ℤ),((d u).2:ℤ))=v (j u) ∧
            ((d u).1:ℝ)/(m:ℝ) ∈ Icc (1/4) (3/4) ∧
            |rho (v (j u)-u.val)| ≤ (m:ℝ)) ∧
          ∃ (q : Environment → (u : J) → Path u.val (d u)) (A : Set Environment),
            MeasurableSet A ∧ (environmentLaw μ).real A ≥ p_att s ∧
            (∀ ω u, (q ω u).vertex (Fin.last ((d u).1+(d u).2))=v (j u)) ∧
            (∀ ω, ω ∈ A → ∀ u, pathWeight ω (q ω u) ≥ -eta*s/4) := by
  classical
  obtain ⟨K, hK, hKp, hF, hFnonneg, hcuts⟩ :=
    exists_heavy_attachment_scale_parameters μ p a D eta kappa hp ha hD heta
      hkappa hkappa16 hmoment hkappaBudget
  let C₁ : ℝ := ∫ x, max (-x) 0 ∂μ
  let Cₚ : ℝ := ∫ x, (max (-x) 0)^p ∂μ
  let theta0 := min a (1-a)
  let L := 4*K+4
  let B := 8*D/(theta0*kappa)+2
  let C := Cₚ*(64*(K:ℝ)/eta)^p
  let epsilon := (p-1)/(2*p)
  let m := fun s : ℝ => Nat.ceil (kappa*s)
  let F := fun s : ℝ =>
    (48*D*s^2*(C*s^(-p))^2 + (D*s+1+B*((L+1:ℕ):ℝ)^2)*(C*s^(-p)) +
      (D*s+1)*(((((2*K+5)*(m s+1):ℕ):ℝ)*(C*s^(-p)))^K)) +
    (D*s+1)*((2*(m s:ℝ)*Cₚ*(s^(1-epsilon))^(-p))^K+
      Real.exp (-((eta*s/16)^2)/(2*s^(1-epsilon)*(2*C₁*(m s:ℝ)+(eta*s/16)/3))))
  change Tendsto F atTop (𝓝 0) at hF
  change ∀ s, 0 < s → 0 ≤ F s at hFnonneg
  let p_att := fun s => max 0 (1-F s)
  have hp_att : Tendsto p_att atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (0:ℝ))).max
      ((tendsto_const_nhds (x := (1:ℝ))).sub hF)
    simpa only [sub_zero, max_eq_right (by norm_num : (0:ℝ) ≤ 1)] using h
  refine ⟨K, hK, hKp, p_att, hp_att, ?_⟩
  filter_upwards [hcuts] with s hcut
  rcases hcut with ⟨hs, hmpos, hspacing, hcutTube, hcutBox, hmTwo, hmS,
    hmass, htail, hbudget⟩
  have hspos : 0 < s := by linarith only [hs]
  have hKpos : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hT : 0 < eta*s/(64*(K:ℝ)) := by positivity
  have hb : 0 < s^(1-epsilon) := Real.rpow_pos_of_pos hspos _
  have ht : 0 < eta*s/16 := by positivity
  have hB : 0 ≤ B := by
    have htheta : 0 < theta0 := lt_min ha.1 (sub_pos.mpr ha.2)
    dsimp only [B]
    positivity
  have hpT : 0 ≤ μ.real (Iio (-(eta*s/(64*(K:ℝ))))) := measureReal_nonneg
  have hbound : μ.real (Iio (-(eta*s/(64*(K:ℝ))))) ≤ C*s^(-p) := htail
  have htailNonneg : 0 ≤ C*s^(-p) := hpT.trans hbound
  refine ⟨le_max_left _ _, max_le (by norm_num) (by linarith only [hFnonneg s hspos]), ?_⟩
  intro I lo hi hlohi hwidth
  obtain ⟨J, M, v, Q, R, j, d, hJ, hJcard, hM, hinj, hnet, hgap,
    hfirstOnly, hlastOnly, hfirst, hlast, hcard, huniform, hQ, hQcard, hR,
    hd, hSigma, hrect, hbox, q, hinactive, hmem, hend, hgood, hsource,
    hGmeas, hequiv, hEmeas, hAmeas, hAbound, hweights⟩ :=
    exists_forward_heavy_attachment_probability μ (eta*s/(64*(K:ℝ))) p
      (s^(1-epsilon)) (eta*s/16) hp hT hmass hb ht hmoment a D s kappa lo hi I K
      ha.1 ha.2 hD hs hkappa hkappa16 hlohi hwidth hspacing hK hcutTube hcutBox
  refine ⟨J, M, v, j, d, hJ, hJcard, hM, hinj, hnet, hgap,
    hfirstOnly, hlastOnly, hfirst, hlast, hcard, huniform, hd, ?_⟩
  let mask := fun ω : Environment => fun z : R =>
    if ω z.val < -(eta*s/(64*(K:ℝ))) then true else false
  refine ⟨fun ω u => q (mask ω) u, _, hAmeas, ?_, fun ω u => hend (mask ω) u, ?_⟩
  · apply le_trans _ hAbound
    apply max_le_max_left
    apply sub_le_sub_left
    change 48*D*s^2*μ.real (Iio (-(eta*s/(64*(K:ℝ)))))^2 +
        (D*s+1+B*((L+1:ℕ):ℝ)^2)*μ.real (Iio (-(eta*s/(64*(K:ℝ))))) +
        (D*s+1)*(((((2*K+5)*(m s+1):ℕ):ℝ)*
          μ.real (Iio (-(eta*s/(64*(K:ℝ))))))^K) +
        (D*s+1)*((2*(m s:ℝ)*Cₚ*(s^(1-epsilon))^(-p))^K+
          Real.exp (-((eta*s/16)^2)/(2*s^(1-epsilon)*(2*C₁*(m s:ℝ)+(eta*s/16)/3)))) ≤ F s
    dsimp only [F]
    have hDs : 0 ≤ D*s+1 := by positivity
    have hpair : 0 ≤ 48*D*s^2 := by positivity
    have hboxCoeff : 0 ≤ D*s+1+B*((L+1:ℕ):ℝ)^2 := by positivity
    have hcountCoeff : (0:ℝ) ≤ (((2*K+5)*(m s+1):ℕ):ℝ) := Nat.cast_nonneg _
    exact add_le_add
      (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpT hbound 2) hpair)
        (mul_le_mul_of_nonneg_left hbound hboxCoeff))
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (mul_nonneg hcountCoeff hpT)
            (mul_le_mul_of_nonneg_left hbound hcountCoeff) K) hDs)) (le_refl _)
  · intro ω hω u
    have hw := (hweights ω hω u).2.2
    change -eta*s/4 ≤ pathWeight ω (q (mask ω) u)
    linarith only [hw, hbudget]

end LPPDifferentiability
end
