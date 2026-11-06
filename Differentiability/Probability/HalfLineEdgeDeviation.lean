/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.OrientedPercolation
public import Differentiability.Probability.LevelSigma
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
import Differentiability.Model.OrientedPercolationLaws
import Differentiability.Probability.AugmentedMeasurability
import LPP_Foundations.Probability.EnvironmentLaw
import Differentiability.Probability.HalfLineEdge
import Differentiability.Probability.LevelIndependence
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Integration

/-!
# Exponential upper deviation of the half-line edge

Let `a_n` be the right edge after `n` steps of the growth from the antidiagonal half-line
through the top sites (`halfLineEdge`). If `E a_L < c L` for one block length `L`, then
`P(a_n ≥ c n) ≤ A e^{-B n}` for all `n`. The proof is a Chernoff bound over blocks:

* Almost surely, `a_{n+m}` is at most `a_n` plus the edge of the next `m` steps read
  from the lowest point at time `n`. Almost surely, because the edge has a junk value when
  the reached set is empty.
* The next block, read from that lowest point, is independent of the weights at lower
  levels and has the law of `a_L`. So `E exp (λ a_{kL}) ≤ φ(λ)^k`.
* Dominated convergence gives a small `λ > 0` with `φ(λ) < exp (λ c L)`; Markov's
  inequality and `a_{kL+r} ≤ a_{kL} + r` finish.

Section 2.3 of the differentiability preprint uses the edge speed of the top-site
cluster. This file proves an exponential upper-deviation bound for that edge.
-/

@[expose] public section

namespace LPPDifferentiability

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- Pathwise subadditivity at a point `t` of level `n` whose first coordinate is the edge. -/
private theorem halfLineEdge_add_le_of (ω : Environment) (n m : ℕ) (t : Lattice)
    (ht1 : t.1 = halfLineEdge ω n) (ht2 : t.1 + t.2 = n)
    (hne : (openReachSet (topSites ω) antidiagHalfLine (n + m)).Nonempty) :
    halfLineEdge ω (n + m) ≤ halfLineEdge ω n + halfLineEdge (fun z => ω (t + z)) m := by
  have hbddn : BddAbove (Prod.fst '' openReachSet (topSites ω) antidiagHalfLine n) := by
    refine ⟨0 + n, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact bddAbove_fst_openReachSet _ _ n 0
      (fun u hu => (show u.1 + u.2 = 0 ∧ u.1 ≤ 0 from hu).2) x hx
  have hsub : openReachSet (topSites ω) antidiagHalfLine n ⊆
      (fun z => t + z) '' antidiagHalfLine := by
    intro v hv
    have hl : v.1 + v.2 = 0 + (n : ℤ) :=
      openReachSet_subset_levelSet (topSites ω) antidiagHalfLine 0 n
        antidiagHalfLine_subset_levelSet hv
    have hle : v.1 ≤ halfLineEdge ω n :=
      le_maxFirst (openReachSet (topSites ω) antidiagHalfLine n) hbddn hv
    refine ⟨(v.1 - t.1, v.2 - t.2), ?_, ?_⟩
    · show v.1 - t.1 + (v.2 - t.2) = 0 ∧ v.1 - t.1 ≤ 0
      exact ⟨by omega, by omega⟩
    · exact Prod.ext (by show t.1 + (v.1 - t.1) = v.1; omega)
        (by show t.2 + (v.2 - t.2) = v.2; omega)
  have hmono : openReachSet (topSites ω) antidiagHalfLine (n + m) ⊆
      openReachSet (topSites ω) ((fun z => t + z) '' antidiagHalfLine) m := by
    rw [← openReachSet_add (topSites ω) antidiagHalfLine n m]
    exact openReachSet_mono subset_rfl hsub m
  have hne' := hne.mono hmono
  have hbddT : BddAbove (Prod.fst '' openReachSet (topSites ω)
      ((fun z => t + z) '' antidiagHalfLine) m) := by
    refine ⟨t.1 + m, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    refine bddAbove_fst_openReachSet _ _ m t.1 ?_ x hx
    rintro _ ⟨s, hs, rfl⟩
    have : s.1 ≤ 0 := (show s.1 + s.2 = 0 ∧ s.1 ≤ 0 from hs).2
    show t.1 + s.1 ≤ t.1
    omega
  have hE := openEdge_translate ω antidiagHalfLine t m hne' bddAbove_fst_antidiagHalfLine
  have hle : halfLineEdge ω (n + m) ≤
      openEdge (topSites ω) ((fun z => t + z) '' antidiagHalfLine) m := by
    unfold halfLineEdge openEdge maxFirst
    exact csSup_le_csSup hbddT (hne.image Prod.fst) (Set.image_mono hmono)
  have hE' : openEdge (topSites ω) ((fun z => t + z) '' antidiagHalfLine) m =
      t.1 + halfLineEdge (fun z => ω (t + z)) m := hE
  omega

private theorem ae_halfLineEdge_add_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (n m : ℕ) :
    ∀ᵐ ω ∂environmentLaw ν, halfLineEdge ω (n + m) ≤ halfLineEdge ω n +
      halfLineEdge (fun z => ω ((halfLineEdge ω n, (n : ℤ) - halfLineEdge ω n) + z)) m := by
  filter_upwards [ae_openReachSet_nonempty_of_infinite ν hp₀ antidiagHalfLine subset_rfl
    antidiagHalfLine_infinite] with ω hω
  exact halfLineEdge_add_le_of ω n m (halfLineEdge ω n, (n : ℤ) - halfLineEdge ω n) rfl
    (by show halfLineEdge ω n + ((n : ℤ) - halfLineEdge ω n) = n; omega) (hω (n + m))

private theorem ae_halfLineEdge_add_nat_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (n r : ℕ) :
    ∀ᵐ ω ∂environmentLaw ν, halfLineEdge ω (n + r) ≤ halfLineEdge ω n + r := by
  filter_upwards [ae_halfLineEdge_add_le ν hp₀ n r] with ω hω
  have := halfLineEdge_le
    (fun z => ω ((halfLineEdge ω n, (n : ℤ) - halfLineEdge ω n) + z)) r
  omega

private theorem measurable_halfLineEdge_levels (n : ℕ) :
    Measurable[levelsAtMost (n : ℤ)] (fun ω : Environment => halfLineEdge ω n) := by
  have h := measurable_openEdge_levelsAtMost antidiagHalfLine 0 antidiagHalfLine_subset_levelSet n
  rw [zero_add] at h
  exact h

private theorem measurable_halfLineEdge (n : ℕ) :
    Measurable (fun ω : Environment => halfLineEdge ω n) :=
  (measurable_halfLineEdge_levels n).mono (levelsAtMost_le n) le_rfl

private theorem measurable_exp_edge (lam : ℝ) (n : ℕ) :
    Measurable (fun ω : Environment => Real.exp (lam * (halfLineEdge ω n : ℝ))) :=
  (Measurable.of_discrete (f := fun a : ℤ => Real.exp (lam * (a : ℝ)))).comp
    (measurable_halfLineEdge n)

private theorem exp_edge_le {lam : ℝ} (hlam : 0 < lam) (ω : Environment) (n : ℕ) :
    Real.exp (lam * (halfLineEdge ω n : ℝ)) ≤ Real.exp (lam * n) :=
  Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by exact_mod_cast halfLineEdge_le ω n) hlam.le)

private theorem integrable_of_nonneg_le {P : Measure Environment} [IsFiniteMeasure P]
    {f : Environment → ℝ} (hf : AEMeasurable f P) (C : ℝ) (h0 : ∀ ω, 0 ≤ f ω)
    (hC : ∀ ω, f ω ≤ C) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun ω => by
    rw [Real.norm_of_nonneg (h0 ω)]
    exact hC ω)

private theorem integrable_exp_edge (ν : Measure ℝ) [IsProbabilityMeasure ν] {lam : ℝ}
    (hlam : 0 < lam) (n : ℕ) :
    Integrable (fun ω : Environment => Real.exp (lam * (halfLineEdge ω n : ℝ)))
      (environmentLaw ν) :=
  integrable_of_nonneg_le (measurable_exp_edge lam n).aemeasurable (Real.exp (lam * n))
    (fun _ => (Real.exp_pos _).le) (fun ω => exp_edge_le hlam ω n)

/-- The next `L` steps from the lowest point at time `n`: independent of lower levels. -/
private theorem edge_shift_exists (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (n L : ℕ) :
    ∃ Y : Environment → ℤ, (∀ ω, Y ω ≤ L) ∧
      (∀ᵐ ω ∂environmentLaw ν, halfLineEdge ω (n + L) ≤ halfLineEdge ω n + Y ω) ∧
      IndepFun (fun ω => halfLineEdge ω n) Y (environmentLaw ν) ∧
      IdentDistrib Y (fun ω => halfLineEdge ω L) (environmentLaw ν) (environmentLaw ν) := by
  have hT : Measurable[levelsAtMost (n : ℤ)]
      (fun ω : Environment => ((halfLineEdge ω n, (n : ℤ) - halfLineEdge ω n) : Lattice)) :=
    (Measurable.of_discrete (f := fun a : ℤ => ((a, (n : ℤ) - a) : Lattice))).comp
      (measurable_halfLineEdge_levels n)
  have hloc : ∀ ω ω' : Environment, (∀ z : Lattice, 0 < z.1 + z.2 → ω z = ω' z) →
      halfLineEdge ω L = halfLineEdge ω' L := by
    intro ω ω' h
    unfold halfLineEdge openEdge
    rw [openReachSet_congr (topSites ω) (topSites ω') antidiagHalfLine 0 L
      antidiagHalfLine_subset_levelSet (fun z h1 _ => by
        show ω z = 1 ↔ ω' z = 1
        rw [h z h1])]
  obtain ⟨hind, hid⟩ := indepFun_identDistrib_shift_of_levelsAtMost ν (n : ℤ) _ hT
    (fun ω => by show halfLineEdge ω n + ((n : ℤ) - halfLineEdge ω n) = n; omega)
    (fun ω => halfLineEdge ω L) (measurable_halfLineEdge L) hloc
    (fun ω => halfLineEdge ω n) (measurable_halfLineEdge_levels n)
  exact ⟨fun ω => halfLineEdge
      (fun z => ω ((halfLineEdge ω n, (n : ℤ) - halfLineEdge ω n) + z)) L,
    fun ω => halfLineEdge_le _ L, ae_halfLineEdge_add_le ν hp₀ n L, hind, hid⟩

private theorem integral_exp_edge_step (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) {lam : ℝ} (hlam : 0 < lam) (L n : ℕ) :
    ∫ ω, Real.exp (lam * (halfLineEdge ω (n + L) : ℝ)) ∂environmentLaw ν ≤
      (∫ ω, Real.exp (lam * (halfLineEdge ω n : ℝ)) ∂environmentLaw ν) *
        ∫ ω, Real.exp (lam * (halfLineEdge ω L : ℝ)) ∂environmentLaw ν := by
  obtain ⟨Y, hYle, hdom, hind, hid⟩ := edge_shift_exists ν hp₀ n L
  have hφ : Measurable (fun a : ℤ => Real.exp (lam * (a : ℝ))) := Measurable.of_discrete
  have hindφ := hind.comp hφ hφ
  have hidφ := hid.comp hφ
  have hYm : AEMeasurable (fun ω => Real.exp (lam * (Y ω : ℝ))) (environmentLaw ν) :=
    hidφ.aemeasurable_fst
  have hYb : ∀ ω, Real.exp (lam * (Y ω : ℝ)) ≤ Real.exp (lam * L) := fun ω =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by exact_mod_cast hYle ω) hlam.le)
  have hYint : Integrable (fun ω => Real.exp (lam * (Y ω : ℝ))) (environmentLaw ν) :=
    integrable_of_nonneg_le hYm (Real.exp (lam * L)) (fun _ => (Real.exp_pos _).le) hYb
  have hAint := integrable_exp_edge ν hlam n
  have hprod : ∫ ω, Real.exp (lam * (halfLineEdge ω n : ℝ)) * Real.exp (lam * (Y ω : ℝ))
        ∂environmentLaw ν =
      (∫ ω, Real.exp (lam * (halfLineEdge ω n : ℝ)) ∂environmentLaw ν) *
        ∫ ω, Real.exp (lam * (Y ω : ℝ)) ∂environmentLaw ν :=
    hindφ.integral_fun_mul_eq_mul_integral hAint.aestronglyMeasurable hYint.aestronglyMeasurable
  have hprodint : Integrable (fun ω => Real.exp (lam * (halfLineEdge ω n : ℝ)) *
      Real.exp (lam * (Y ω : ℝ))) (environmentLaw ν) :=
    integrable_of_nonneg_le ((measurable_exp_edge lam n).aemeasurable.mul hYm)
      (Real.exp (lam * n) * Real.exp (lam * L))
      (fun _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (fun ω => mul_le_mul (exp_edge_le hlam ω n) (hYb ω) (Real.exp_pos _).le
        (Real.exp_pos _).le)
  have hidint : ∫ ω, Real.exp (lam * (Y ω : ℝ)) ∂environmentLaw ν =
      ∫ ω, Real.exp (lam * (halfLineEdge ω L : ℝ)) ∂environmentLaw ν := hidφ.integral_eq
  calc ∫ ω, Real.exp (lam * (halfLineEdge ω (n + L) : ℝ)) ∂environmentLaw ν
      ≤ ∫ ω, Real.exp (lam * (halfLineEdge ω n : ℝ)) * Real.exp (lam * (Y ω : ℝ))
          ∂environmentLaw ν := by
        refine integral_mono_ae (integrable_exp_edge ν hlam (n + L)) hprodint ?_
        filter_upwards [hdom] with ω hω
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        have h1 : (halfLineEdge ω (n + L) : ℝ) ≤ halfLineEdge ω n + Y ω := by
          exact_mod_cast hω
        exact (mul_le_mul_of_nonneg_left h1 hlam.le).trans_eq (mul_add _ _ _)
    _ = (∫ ω, Real.exp (lam * (halfLineEdge ω n : ℝ)) ∂environmentLaw ν) *
        ∫ ω, Real.exp (lam * (halfLineEdge ω L : ℝ)) ∂environmentLaw ν := by
        rw [hprod, hidint]

private theorem integral_exp_edge_le_pow (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) {lam : ℝ} (hlam : 0 < lam) (L k : ℕ) :
    ∫ ω, Real.exp (lam * (halfLineEdge ω (k * L) : ℝ)) ∂environmentLaw ν ≤
      (∫ ω, Real.exp (lam * (halfLineEdge ω L : ℝ)) ∂environmentLaw ν) ^ k := by
  induction k with
  | zero =>
    refine (integral_mono (integrable_exp_edge ν hlam (0 * L)) (integrable_const (1 : ℝ))
      (fun ω => (exp_edge_le hlam ω (0 * L)).trans_eq (by simp))).trans ?_
    simp
  | succ k ih =>
    have hφ0 : 0 ≤ ∫ ω, Real.exp (lam * (halfLineEdge ω L : ℝ)) ∂environmentLaw ν :=
      integral_nonneg fun _ => (Real.exp_pos _).le
    have hstep := integral_exp_edge_step ν hp₀ hlam L (k * L)
    rw [show (k + 1) * L = k * L + L by ring, pow_succ]
    exact hstep.trans (mul_le_mul_of_nonneg_right ih hφ0)

private theorem norm_slope_exp_le {lam x L : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hL : 0 ≤ L) (hx : x ≤ L) :
    ‖lam⁻¹ * (Real.exp (lam * x) - 1)‖ ≤ |x| * Real.exp L := by
  have hE : 1 ≤ Real.exp L := Real.one_le_exp hL
  rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hlam]
  rcases le_or_gt 0 x with hx0 | hx0
  · have hy : 0 ≤ lam * x := mul_nonneg hlam.le hx0
    have h1 : 1 ≤ Real.exp (lam * x) := Real.one_le_exp hy
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.exp (lam * x) - 1), abs_of_nonneg hx0,
      inv_mul_le_iff₀ hlam]
    have h2 : Real.exp (lam * x) - 1 ≤ lam * x * Real.exp (lam * x) := by
      have h := Real.add_one_le_exp (-(lam * x))
      have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos (lam * x)).le
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h'
      linarith
    have hlx : lam * x ≤ L :=
      (mul_le_mul_of_nonneg_right hlam1 hx0).trans (by linarith)
    have h3 : Real.exp (lam * x) ≤ Real.exp L := Real.exp_le_exp.2 hlx
    have h4 := mul_le_mul_of_nonneg_left h3 hy
    linarith
  · have hy : lam * x < 0 := mul_neg_of_pos_of_neg hlam hx0
    have h1 : Real.exp (lam * x) ≤ 1 := Real.exp_le_one_iff.2 hy.le
    rw [abs_of_nonpos (by linarith : Real.exp (lam * x) - 1 ≤ 0), abs_of_neg hx0,
      inv_mul_le_iff₀ hlam]
    have h2 := Real.add_one_le_exp (lam * x)
    have h3 : -x ≤ -x * Real.exp L := le_mul_of_one_le_right (by linarith) hE
    have h4 := mul_le_mul_of_nonneg_left h3 hlam.le
    linarith

private theorem exists_small_lambda (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (c : ℝ) (L : ℕ)
    (hc : ∫ ω, (halfLineEdge ω L : ℝ) ∂environmentLaw ν < c * L) :
    ∃ lam : ℝ, 0 < lam ∧
      ∫ ω, Real.exp (lam * (halfLineEdge ω L : ℝ)) ∂environmentLaw ν <
        Real.exp (lam * (c * L)) := by
  have hdc : Tendsto (fun lam : ℝ => ∫ ω, lam⁻¹ * (Real.exp (lam * (halfLineEdge ω L : ℝ)) - 1)
      ∂environmentLaw ν) (𝓝[>] 0) (𝓝 (∫ ω, (halfLineEdge ω L : ℝ) ∂environmentLaw ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ω => |(halfLineEdge ω L : ℝ)| * Real.exp L) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun lam =>
        ((Measurable.of_discrete
          (f := fun a : ℤ => lam⁻¹ * (Real.exp (lam * (a : ℝ)) - 1))).comp
          (measurable_halfLineEdge L)).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with lam hlam
      exact ae_of_all _ fun ω => norm_slope_exp_le hlam.1 hlam.2.le (Nat.cast_nonneg L)
        (by exact_mod_cast halfLineEdge_le ω L)
    · exact (integrable_halfLineEdge ν hp₀ L).abs.mul_const _
    · refine ae_of_all _ fun ω => ?_
      have h1 : HasDerivAt (fun s : ℝ => s * (halfLineEdge ω L : ℝ)) (halfLineEdge ω L : ℝ) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).mul_const (halfLineEdge ω L : ℝ)
      have hd : HasDerivAt (fun s : ℝ => Real.exp (s * (halfLineEdge ω L : ℝ)))
          (halfLineEdge ω L : ℝ) 0 := by
        simpa using h1.exp
      refine hd.tendsto_slope_zero_right.congr fun lam => ?_
      simp [smul_eq_mul]
  obtain ⟨lam, hlam, hlt⟩ : ∃ lam : ℝ, 0 < lam ∧
      (∫ ω, lam⁻¹ * (Real.exp (lam * (halfLineEdge ω L : ℝ)) - 1) ∂environmentLaw ν) < c * L := by
    refine Filter.Eventually.exists (f := 𝓝[>] (0 : ℝ)) ?_
    filter_upwards [hdc.eventually (gt_mem_nhds hc),
      Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with lam h1 h2
    exact ⟨h2.1, h1⟩
  refine ⟨lam, hlam, ?_⟩
  have hint := integrable_exp_edge ν hlam L
  have e1 : ∫ ω, lam⁻¹ * (Real.exp (lam * (halfLineEdge ω L : ℝ)) - 1) ∂environmentLaw ν =
      lam⁻¹ * ((∫ ω, Real.exp (lam * (halfLineEdge ω L : ℝ)) ∂environmentLaw ν) - 1) := by
    rw [integral_const_mul, integral_sub hint (integrable_const 1)]
    simp
  rw [e1] at hlt
  have h2 := (inv_mul_lt_iff₀ hlam).1 hlt
  have h3 := Real.add_one_le_exp (lam * (c * L))
  linarith

/-- The tail at time `kL + r`, by Markov's inequality at time `kL`. Here
`ε = exp (λ (c (kL + r) - r))`. -/
private theorem edge_tail_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) {lam : ℝ} (hlam : 0 < lam) (L : ℕ) (c : ℝ) (k r : ℕ) {ε : ℝ}
    (hε : ε = Real.exp (lam * (c * ((k * L + r : ℕ) : ℝ) - r))) :
    (environmentLaw ν).real {ω | c * ((k * L + r : ℕ) : ℝ) ≤ halfLineEdge ω (k * L + r)} ≤
      ε⁻¹ * (∫ ω, Real.exp (lam * (halfLineEdge ω L : ℝ)) ∂environmentLaw ν) ^ k := by
  have hεpos : 0 < ε := by rw [hε]; exact Real.exp_pos _
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := environmentLaw ν)
    (f := fun ω => Real.exp (lam * (halfLineEdge ω (k * L) : ℝ)))
    (ae_of_all _ fun _ => (Real.exp_pos _).le) (integrable_exp_edge ν hlam (k * L)) ε
  have hsub : {ω | c * ((k * L + r : ℕ) : ℝ) ≤ halfLineEdge ω (k * L + r)} ≤ᵐ[environmentLaw ν]
      {ω | ε ≤ Real.exp (lam * (halfLineEdge ω (k * L) : ℝ))} := by
    filter_upwards [ae_halfLineEdge_add_nat_le ν hp₀ (k * L) r] with ω hω
    refine fun hmem => ?_
    have h1 : c * ((k * L + r : ℕ) : ℝ) ≤ (halfLineEdge ω (k * L + r) : ℝ) := hmem
    have h2 : (halfLineEdge ω (k * L + r) : ℝ) ≤ halfLineEdge ω (k * L) + r := by
      exact_mod_cast hω
    have h3 : c * ((k * L + r : ℕ) : ℝ) - r ≤ halfLineEdge ω (k * L) := by linarith
    show ε ≤ Real.exp (lam * (halfLineEdge ω (k * L) : ℝ))
    rw [hε]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h3 hlam.le)
  have hmeas : (environmentLaw ν).real {ω | c * ((k * L + r : ℕ) : ℝ) ≤
        halfLineEdge ω (k * L + r)} ≤
      (environmentLaw ν).real {ω | ε ≤ Real.exp (lam * (halfLineEdge ω (k * L) : ℝ))} := by
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have h4 := hmk.trans (integral_exp_edge_le_pow ν hp₀ hlam L k)
  refine hmeas.trans ?_
  rw [inv_mul_eq_div, le_div_iff₀ hεpos]
  exact (mul_comm _ _).trans_le h4

/-- The real inequality behind `A e^{-B n}`, with `ℓ = log φ - λ c L` and `B L = -ℓ`. -/
private theorem tail_arith (L k r : ℕ) (c lam φ ℓ B : ℝ) (hr : r < L)
    (hlam : 0 < lam) (hφ0 : 0 < φ) (hℓ : ℓ = Real.log φ - lam * (c * L)) (hBpos : 0 < B)
    (hB : B * L = -ℓ) :
    Real.exp (-(lam * (c * ((k * L + r : ℕ) : ℝ) - r))) * φ ^ k ≤
      Real.exp (lam * (|1 - c| * L) - ℓ) * Real.exp (-(B * ((k * L + r : ℕ) : ℝ))) := by
  have hrL : (r : ℝ) ≤ L := by exact_mod_cast hr.le
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hφk : φ ^ k = Real.exp (k * Real.log φ) := by
    rw [Real.exp_nat_mul, Real.exp_log hφ0]
  rw [hφk, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hlog : Real.log φ = ℓ + lam * (c * L) := by linarith
  have hℓB : ℓ = -(B * L) := by linarith
  rw [hlog, hℓB]
  push_cast
  have hP1 : 0 ≤ |1 - c| * L - (1 - c) * r := by
    nlinarith [mul_nonneg (abs_nonneg (1 - c)) (sub_nonneg.2 hrL),
      mul_nonneg (sub_nonneg.2 (le_abs_self (1 - c))) hr0]
  have hP2 : 0 ≤ B * (L - r) := mul_nonneg hBpos.le (sub_nonneg.2 hrL)
  nlinarith [mul_nonneg hlam.le hP1, hP2]

/-- **Exponential upper deviation of the half-line edge.** If the mean edge at one
block length `L` is below `c L`, then `P(c n ≤ a_n) ≤ A e^{-B n}` for all `n`. -/
theorem halfLineEdge_upper_deviation (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (c : ℝ) (L : ℕ) (hL : 0 < L)
    (hc : ∫ ω, (halfLineEdge ω L : ℝ) ∂environmentLaw ν < c * L) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ n : ℕ,
      (environmentLaw ν).real {ω | c * n ≤ halfLineEdge ω n} ≤ A * Real.exp (-(B * n)) := by
  obtain ⟨lam, hlam, hlt⟩ := exists_small_lambda ν hp₀ c L hc
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hφ0 : 0 < ∫ ω, Real.exp (lam * (halfLineEdge ω L : ℝ)) ∂environmentLaw ν :=
    integral_exp_pos (integrable_exp_edge ν hlam L)
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ,
      (∫ ω, Real.exp (lam * (halfLineEdge ω L : ℝ)) ∂environmentLaw ν) = φ := ⟨_, rfl⟩
  rw [hφ] at hlt hφ0
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log φ - lam * (c * L) := ⟨_, rfl⟩
  have hℓneg : ℓ < 0 := by linarith [(Real.log_lt_iff_lt_exp hφ0).2 hlt]
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = -ℓ / L := ⟨_, rfl⟩
  have hBpos : 0 < B := by rw [hBdef]; exact div_pos (neg_pos.2 hℓneg) hLpos
  have hBL : B * L = -ℓ := by
    rw [hBdef, div_mul_eq_mul_div, mul_div_assoc, div_self hLpos.ne', mul_one]
  refine ⟨Real.exp (lam * (|1 - c| * L) - ℓ), B, Real.exp_pos _, hBpos, fun n => ?_⟩
  have hn : n / L * L + n % L = n := Nat.div_add_mod' n L
  have h1 := edge_tail_bound ν hp₀ hlam L c (n / L) (n % L) rfl
  rw [← Real.exp_neg, hφ, hn] at h1
  have h2 := tail_arith L (n / L) (n % L) c lam φ ℓ B (Nat.mod_lt n hL) hlam hφ0 hℓ hBpos hBL
  rw [hn] at h2
  exact h1.trans h2

end LPPDifferentiability
