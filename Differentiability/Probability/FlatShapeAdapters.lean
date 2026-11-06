/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.WeakNegativeShape
public import Differentiability.Probability.TopIndicatorShape
public import ProbabilityBasics.Probability.PositiveMomentTail
public import LPP_Foundations.Probability.EnvironmentMap
public import LPP_Foundations.Probability.PassageSymmetry
public import LPP_Foundations.Probability.PassageMeanBounds
public import Differentiability.Model.OrientedPercolation
public import LPP_Foundations.Model.LastPassage.Axes
public import LPP_Foundations.Model.LastPassage.Bounds
public import Martin2004.Analysis.RationalPassageNormalization
public import LPP_Foundations.Shape.Uniqueness

/-!
# Shape adapters for flat segments

Three statements about a given shape block (a continuous, homogeneous, concave
function that is the almost sure uniform limit of passage times):

* for a weight law that is at most `1` almost surely with a negative moment above one,
  the block also gives the limit of the expected passage times at floors, finite mean
  integrability, and the bound by the level;
* the same for the 0/1 field of sites equal to `1`, together with nonnegativity and the
  value at `(1, 0)`, which is the mass of the atom at `1`;
* a block for a coordinatewise image of the environment is symmetric in its two
  arguments.

The shape in each statement is identified with the shape already constructed for the same
law, by the uniqueness of the almost sure limit. No new shape is constructed.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

private theorem ae_environment_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hle : ∀ᵐ t ∂ν, t ≤ 1) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ z : Lattice, ω z ≤ 1 := by
  rw [ae_all_iff]
  intro z
  have hmap : ∀ᵐ x ∂(environmentLaw ν).map (fun ω : Environment => ω z), x ≤ 1 := by
    rw [environmentLaw_map_eval]
    exact hle
  exact ae_of_ae_map (measurable_environment_eval z).aemeasurable hmap

private theorem positive_tail_of_ae_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hle : ∀ᵐ t ∂ν, t ≤ 1) :
    (∫⁻ t in Ioi (0 : ℝ), (ν (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
  refine positive_integrated_sqrt_tail_lt_top_of_moment ν (p := 3) (by norm_num) ?_
  calc
    (∫⁻ x, ENNReal.ofReal ((max x 0) ^ (3 : ℝ)) ∂ν) ≤ ∫⁻ _x, (1 : ℝ≥0∞) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hle] with x hx
      exact ENNReal.ofReal_le_one.mpr
        (Real.rpow_le_one (le_max_right x 0) (max_le hx zero_le_one) (by norm_num))
    _ = 1 := by simp
    _ < ∞ := ENNReal.one_lt_top

private theorem integral_lastPassage_le_length_of_ae_le_one
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hle : ∀ᵐ t ∂ν, t ≤ 1)
    (hμ : Integrable (fun t : ℝ => t) ν) (d : ℕ × ℕ) :
    ∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw ν ≤ ((d.1 + d.2 : ℕ) : ℝ) := by
  calc
    ∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw ν ≤
        ∫ _ω : Environment, ((d.1 + d.2 : ℕ) : ℝ) ∂environmentLaw ν := by
      refine integral_mono_ae (integrable_lastPassage ν hμ 0 d) (integrable_const _) ?_
      filter_upwards [ae_environment_le_one ν hle] with ω hω
      simpa only [mul_one] using lastPassage_le_const ω 0 d 1 hω
    _ = ((d.1 + d.2 : ℕ) : ℝ) := by simp

/-- Expected-floor limits for a shape block of a law at most `1`. -/
theorem expected_floor_limit_of_shape_block (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hle : ∀ᵐ t ∂ν, t ≤ 1)
    (hneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂ν) < ∞)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ)) :
    (∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw ν) / (n : ℝ))
      atTop (𝓝 (g x))) ∧
    (∀ (u : Lattice) (d : ℕ × ℕ),
      Integrable (fun ω : Environment => lastPassage ω u d) (environmentLaw ν)) ∧
    (∀ x : Quadrant, g x ≤ (x.1 : ℝ) + x.2) := by
  have hpos := positive_tail_of_ae_le_one ν hle
  have hμ := integrable_id_of_negative_moment_and_positive_tail ν hneg hpos
  obtain ⟨g', hg', _⟩ :=
    exists_unique_shape_with_expected_rate_of_negative_moment_and_positive_tail ν hneg hpos
  have hgg : g = g' :=
    (exists_unique_shape_of_negative_moment_and_positive_tail ν hneg hpos).unique
      ⟨hgcont, hghom, hgconc, hgshape⟩ ⟨hg'.1, hg'.2.1, hg'.2.2.1, hg'.2.2.2.1⟩
  subst hgg
  refine ⟨hg'.2.2.2.2.1, fun u d => integrable_lastPassage ν hμ u d, ?_⟩
  intro x
  refine le_of_tendsto_of_tendsto' (hg'.2.2.2.2.1 x)
    (tendsto_floor_pair_length (x.1 : ℝ) (x.2 : ℝ) x.1.property x.2.property) ?_
  intro n
  exact div_le_div_of_nonneg_right
    (integral_lastPassage_le_length_of_ae_le_one ν hle hμ _) (Nat.cast_nonneg n)

/-- The coordinate indicator of the value `1`. -/
private theorem measurable_indicator_one :
    Measurable (fun t : ℝ => if t = 1 then (1 : ℝ) else 0) :=
  Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const

private theorem integral_indicator_one_environment_eval
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (z : Lattice) :
    ∫ ω : Environment, (if ω z = 1 then (1 : ℝ) else 0) ∂environmentLaw ν =
      ν.real {1} := by
  have hχ := measurable_indicator_one
  have h1 := integral_map (measurable_environment_eval z).aemeasurable
    hχ.aestronglyMeasurable (μ := environmentLaw ν)
  rw [environmentLaw_map_eval] at h1
  have h2 : (fun t : ℝ => if t = 1 then (1 : ℝ) else 0) =
      Set.indicator ({1} : Set ℝ) (1 : ℝ → ℝ) := by
    funext t
    by_cases ht : t = 1 <;> simp [Set.indicator, ht]
  rw [← h1, h2]
  exact integral_indicator_one (measurableSet_singleton 1)

private theorem integrable_indicator_one_environment_eval
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (z : Lattice) :
    Integrable (fun ω : Environment => if ω z = 1 then (1 : ℝ) else 0)
      (environmentLaw ν) := by
  refine (integrable_const (1 : ℝ)).mono'
    ((measurable_indicator_one.comp (measurable_environment_eval z)).aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  by_cases h : ω z = 1 <;> simp [h]

/-- Expected-floor limits for a shape block of the 0/1 top field. -/
theorem expected_floor_limit_of_top_shape_block (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (gtop : Quadrant → ℝ) (htcont : Continuous gtop)
    (hthom : ∀ (c : ℝ≥0) (x : Quadrant), gtop (c * x.1, c * x.2) = (c : ℝ) * gtop x)
    (htconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * gtop x + (t : ℝ) * gtop y ≤ gtop (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (htshape : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage (topField ω) 0 d - gtop ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ)) :
    (∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage (topField ω) 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw ν) / (n : ℝ))
      atTop (𝓝 (gtop x))) ∧
    (∀ (u : Lattice) (d : ℕ × ℕ),
      Integrable (fun ω : Environment => lastPassage (topField ω) u d) (environmentLaw ν)) ∧
    (∀ x : Quadrant, 0 ≤ gtop x ∧ gtop x ≤ (x.1 : ℝ) + x.2) ∧
    gtop ((1 : ℝ≥0), (0 : ℝ≥0)) = ν.real {1} := by
  classical
  have _htconc := htconc
  let χ : ℝ → ℝ := fun t => if t = 1 then (1 : ℝ) else 0
  have hχ : Measurable χ := measurable_indicator_one
  have hfield : Measurable (fun ω : Environment => fun z : Lattice => χ (ω z)) :=
    measurable_coordinatewise_environment_map χ hχ
  have hlaw := environmentLaw_map_coordinatewise ν χ hχ
  have hν : ∀ᵐ t ∂ν.map χ, 0 ≤ t ∧ t ≤ 1 := by
    refine (ae_map_iff (p := fun y : ℝ => 0 ≤ y ∧ y ≤ 1) hχ.aemeasurable
      (by exact measurableSet_Icc)).2 (Eventually.of_forall fun t => ?_)
    by_cases ht : t = 1 <;> simp [χ, ht]
  obtain ⟨g', hg'⟩ := exists_shape_with_expected_bounds_of_ae_mem_unit_interval (ν.map χ) hν
  have hsample : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage (fun z => χ (ω z)) 0 d - g' ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ) := by
    have h := hg'.2.2.2.1
    rw [← hlaw] at h
    exact ae_of_ae_map hfield.aemeasurable h
  have hgg : gtop = g' := by
    obtain ⟨ω, h1, h2⟩ := (htshape.and hsample).exists
    refine shapeCandidates_eq_of_common_environment gtop g' htcont hg'.1 hthom hg'.2.1
      (topField ω) ?_ ?_
    · intro ε hε
      obtain ⟨N, _, hN⟩ := h1 ε hε
      exact ⟨N, hN⟩
    · intro ε hε
      obtain ⟨N, _, hN⟩ := h2 ε hε
      exact ⟨N, hN⟩
  subst hgg
  have hpass (u : Lattice) (d : ℕ × ℕ) :
      Integrable (fun ω : Environment => lastPassage (topField ω) u d)
        (environmentLaw ν) ∧
      (∫ ω : Environment, lastPassage (topField ω) u d ∂environmentLaw ν) =
        ∫ η : Environment, lastPassage η u d ∂environmentLaw (ν.map χ) := by
    have hi : Integrable (fun η : Environment => lastPassage η u d)
        ((environmentLaw ν).map (fun ω : Environment => fun z : Lattice => χ (ω z))) := by
      rw [hlaw]
      exact hg'.2.2.2.2.2.1 u d
    refine ⟨hi.comp_measurable hfield, ?_⟩
    have heq := integral_map hfield.aemeasurable hi.aestronglyMeasurable
    rw [hlaw] at heq
    exact heq.symm
  have hlim (x : Quadrant) : Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage (topField ω) 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw ν) / (n : ℝ))
      atTop (𝓝 (gtop x)) := by
    simpa only [(hpass _ _).2] using hg'.2.2.2.2.1 x
  refine ⟨hlim, fun u d => (hpass u d).1, hg'.2.2.2.2.2.2.1, ?_⟩
  have haxis (n : ℕ) : ∫ ω : Environment, lastPassage (topField ω) 0 (n, 0)
      ∂environmentLaw ν = (n : ℝ) * ν.real {1} := by
    have hsum : ∀ ω : Environment, lastPassage (topField ω) 0 (n, 0) =
        ∑ i : Fin n, (if ω ((0 : Lattice).1 + (i.val : ℤ), (0 : Lattice).2) = 1
          then (1 : ℝ) else 0) := fun ω => lastPassage_horizontal (topField ω) 0 n
    simp_rw [hsum]
    rw [integral_finsetSum _ fun i _ => integrable_indicator_one_environment_eval ν _]
    simp [integral_indicator_one_environment_eval]
  have hev : (fun _ : ℕ => ν.real {1}) =ᶠ[atTop] (fun n : ℕ =>
      (∫ ω : Environment, lastPassage (topField ω) 0
        (⌊(n : ℝ) * (((1 : ℝ≥0), (0 : ℝ≥0)).1 : ℝ)⌋₊,
          ⌊(n : ℝ) * (((1 : ℝ≥0), (0 : ℝ≥0)).2 : ℝ)⌋₊) ∂environmentLaw ν) / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [NNReal.coe_one, mul_one, NNReal.coe_zero, mul_zero, Nat.floor_natCast,
      Nat.floor_zero]
    rw [haxis n]
    field_simp
  exact tendsto_nhds_unique (hlim ((1 : ℝ≥0), (0 : ℝ≥0)))
    ((tendsto_const_nhds (x := ν.real {1}) (f := (atTop : Filter ℕ))).congr' hev)

/-- A shape block for a coordinatewise image of the environment is symmetric. -/
theorem shape_swap_of_coordinatewise_field (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (ψ : ℝ → ℝ) (hψ : Measurable ψ)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgshape : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage (fun z => ψ (ω z)) 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ)) :
    ∀ x : Quadrant, g (x.2, x.1) = g x := by
  have _hψ := hψ
  have hswap := (measurePreserving_environmentSwap ν).quasiMeasurePreserving.ae hgshape
  obtain ⟨ω, h1, h2⟩ := (hgshape.and hswap).exists
  have hcomm : g = fun x : Quadrant => g (x.2, x.1) := by
    refine shapeCandidates_eq_of_common_environment g (fun x : Quadrant => g (x.2, x.1))
      hgcont (hgcont.comp (continuous_snd.prodMk continuous_fst))
      hghom (fun c x => hghom c (x.2, x.1)) (fun z => ψ (ω z)) ?_ ?_
    · intro ε hε
      obtain ⟨N, _, hN⟩ := h1 ε hε
      exact ⟨N, hN⟩
    · intro ε hε
      obtain ⟨N, _, hN⟩ := h2 ε hε
      refine ⟨N, fun z hz => ?_⟩
      have h := hN z.swap (by simpa only [Prod.fst_swap, Prod.snd_swap, add_comm] using hz)
      have e : lastPassage (fun w => ψ (environmentSwap ω w)) 0 z.swap =
          lastPassage (fun w => ψ (ω w)) 0 z := by
        have e := lastPassage_swap (fun w => ψ (ω w)) 0 z.swap
        rw [Prod.swap_swap] at e
        exact e.symm
      have h' : |lastPassage (fun w => ψ (ω w)) 0 z - g ((z.2 : ℝ≥0), (z.1 : ℝ≥0))| ≤
          ε * ((z.2 + z.1 : ℕ) : ℝ) := by
        rw [← e]
        exact h
      rw [Nat.add_comm z.2 z.1] at h'
      exact h'
  intro x
  exact (congrFun hcomm x).symm

end LPPDifferentiability
