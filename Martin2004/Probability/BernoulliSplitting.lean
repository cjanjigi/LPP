/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Bounds
public import LPP_Foundations.Model.LastPassage.Scaling
public import Martin2004.Probability.LayerCakePassage
public import Martin2004.Probability.QuantileFieldCoupling
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Splitting into two Bernoulli models

Martin (2004), proof of Lemma 4.2, up to its first Bernoulli display.

For a fixed level `x`, the local indicator `I(X1 > x, X2 <= x)` uses the cdf
`F_i(x) = μ_i(Iic x)` and its threshold interval is `[X2, X1)`. Martin (2004),
proof of Lemma 4.2, uses `X1 >= x` and `X2 < x`, giving `(X2, X1]`; the fixed-level
probabilities can differ at atoms. For each pair of values, the two threshold intervals
have the same Lebesgue length, which is what the threshold integral uses. The local
indicator field is an independent Bernoulli field with parameter
`[F2(x) - F1(x)]_+`; `1 - I(X1 <= x, X2 > x)` is one with parameter
`1 - [F1(x) - F2(x)]_+`. The last
passage of the layer environment is at most the sum of the two last passages, minus the
common number of sites of all paths. Taking means and integrating over `x` gives the
finite-box form of the first Bernoulli display of the proof; the limit in the box size is
not taken in this file.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace LPPDifferentiability

/-! ### Laws of the level-`x` indicator fields -/

/-- The uniform field on the lattice. -/
private noncomputable abbrev uniformField : Measure Environment :=
  Measure.infinitePi (fun _ : Lattice => volume.restrict (Ioo (0 : ℝ) 1))

/-- The measurable stand-in for the literal quantile of a law. -/
private noncomputable abbrev qm (μ : Measure ℝ) : ℝ → ℝ :=
  (Ioo (0 : ℝ) 1).indicator (fun y : ℝ => sInf {r : ℝ | y ≤ μ.real (Iic r)})

private theorem uniform_prob : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
  ⟨by simp⟩

private theorem measurable_qm (μ : Measure ℝ) [IsProbabilityMeasure μ] : Measurable (qm μ) :=
  measurable_indicator_source_quantile μ

/-- A zero-one field cut out by a measurable set of levels has the Bernoulli environment law. -/
private theorem map_indicator_field (S : Set ℝ) (hS : MeasurableSet S) (p : unitInterval)
    (hp : (p : ℝ) = (volume.restrict (Ioo (0 : ℝ) 1)).real S) :
    uniformField.map (fun u : Environment => fun z : Lattice =>
      S.indicator (fun _ => (1 : ℝ)) (u z)) =
        environmentLaw (bernoulliMeasure (1 : ℝ) 0 p) := by
  have hν := uniform_prob
  have hp' : p = ⟨(volume.restrict (Ioo (0 : ℝ) 1)).real S,
      ⟨measureReal_nonneg, measureReal_le_one⟩⟩ := Subtype.ext hp
  have hlaw : (volume.restrict (Ioo (0 : ℝ) 1)).map (S.indicator (fun _ => (1 : ℝ))) =
      bernoulliMeasure (1 : ℝ) 0 p := by
    rw [hp']
    exact (hasLaw_indicator_one_bernoulliMeasure (P := volume.restrict (Ioo (0 : ℝ) 1))
      (M := ℝ) hS.nullMeasurableSet).map_eq
  have hpi := Measure.infinitePi_map_pi
    (μ := fun _ : Lattice => volume.restrict (Ioo (0 : ℝ) 1))
    (f := fun _ : Lattice => S.indicator (fun _ => (1 : ℝ)))
    (fun _ => measurable_const.indicator hS)
  refine hpi.trans ?_
  unfold environmentLaw
  simp only [hlaw]

/-- Mean last passage of the zero-one field equals that of the Bernoulli environment. -/
private theorem integral_indicator_field (S : Set ℝ) (hS : MeasurableSet S) (p : unitInterval)
    (hp : (p : ℝ) = (volume.restrict (Ioo (0 : ℝ) 1)).real S) (d : ℕ × ℕ) :
    ∫ u, lastPassage (fun z => S.indicator (fun _ => (1 : ℝ)) (u z)) 0 d ∂uniformField =
      ∫ ω, lastPassage ω 0 d ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0 p) := by
  have hmeasF : Measurable (fun u : Environment => fun z : Lattice =>
      S.indicator (fun _ => (1 : ℝ)) (u z)) :=
    measurable_pi_iff.2 fun z => (measurable_const.indicator hS).comp (measurable_pi_apply z)
  rw [← map_indicator_field S hS p hp]
  exact (integral_map hmeasF.aemeasurable (measurable_lastPassage 0 d).aestronglyMeasurable).symm

/-- Last passage of the zero-one field is integrable. -/
private theorem integrable_indicator_field (S : Set ℝ) (hS : MeasurableSet S) (p : unitInterval)
    (hp : (p : ℝ) = (volume.restrict (Ioo (0 : ℝ) 1)).real S) (d : ℕ × ℕ) :
    Integrable (fun u : Environment =>
      lastPassage (fun z => S.indicator (fun _ => (1 : ℝ)) (u z)) 0 d) uniformField := by
  have hmeasF : Measurable (fun u : Environment => fun z : Lattice =>
      S.indicator (fun _ => (1 : ℝ)) (u z)) :=
    measurable_pi_iff.2 fun z => (measurable_const.indicator hS).comp (measurable_pi_apply z)
  have hint : Integrable (fun ω : Environment => lastPassage ω 0 d)
      (environmentLaw (bernoulliMeasure (1 : ℝ) 0 p)) :=
    integrable_lastPassage _ (integrable_bernoulliMeasure (1 : ℝ) 0 p _) 0 d
  rw [← map_indicator_field S hS p hp] at hint
  exact (integrable_map_measure (measurable_lastPassage 0 d).aestronglyMeasurable
    hmeasF.aemeasurable).1 hint

/-- In the coupling of the proof of Martin (2004), Lemma 4.2, the probability that the level lies
in `[X2, X1)` is `[F2(x) - F1(x)]_+`. -/
private theorem real_setA (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (x : ℝ) :
    (volume.restrict (Ioo (0 : ℝ) 1)).real {t : ℝ | x ∈ Ico (qm μ₂ t) (qm μ₁ t)} =
      max (μ₂.real (Iic x) - μ₁.real (Iic x)) 0 := by
  have h := volume_real_gt_and_le_of_eq_source_quantile μ₁ μ₂ (qm μ₁) (qm μ₂)
    (fun t ht => indicator_of_mem ht
      (fun y : ℝ => sInf {r : ℝ | y ≤ μ₁.real (Iic r)}))
    (fun t ht => indicator_of_mem ht
      (fun y : ℝ => sInf {r : ℝ | y ≤ μ₂.real (Iic r)})) x
  have hset : {t : ℝ | x ∈ Ico (qm μ₂ t) (qm μ₁ t)} =
      {t : ℝ | x < qm μ₁ t ∧ qm μ₂ t ≤ x} :=
    Set.ext fun t => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [hset]
  exact h

private theorem measurable_setA (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (x : ℝ) :
    MeasurableSet {t : ℝ | x ∈ Ico (qm μ₂ t) (qm μ₁ t)} := by
  have h1 : MeasurableSet {t : ℝ | qm μ₂ t ≤ x} :=
    measurableSet_le (measurable_qm μ₂) measurable_const
  have h2 : MeasurableSet {t : ℝ | x < qm μ₁ t} :=
    measurableSet_lt measurable_const (measurable_qm μ₁)
  exact h1.inter h2

/-- The first Bernoulli model in Martin (2004), Lemma 4.2: mean last passage of the field
`I(X1 > x, X2 <= x)`. -/
private theorem integral_FA (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (x : ℝ) (d : ℕ × ℕ) :
    ∫ u, lastPassage (fun z => (Ico (qm μ₂ (u z)) (qm μ₁ (u z))).indicator
        (fun _ => (1 : ℝ)) x) 0 d ∂uniformField =
      ∫ ω, lastPassage ω 0 d ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0
        (Set.projIcc (0 : ℝ) 1 zero_le_one (μ₂.real (Iic x) - μ₁.real (Iic x)))) := by
  have hν := uniform_prob
  have h1 : 0 ≤ μ₁.real (Iic x) := measureReal_nonneg
  have h2 : μ₂.real (Iic x) ≤ 1 := measureReal_le_one
  have h3 : μ₂.real (Iic x) - μ₁.real (Iic x) ≤ 1 := by linarith
  have hp : ((Set.projIcc (0 : ℝ) 1 zero_le_one (μ₂.real (Iic x) - μ₁.real (Iic x)) :
        Set.Icc (0 : ℝ) 1) : ℝ) =
      (volume.restrict (Ioo (0 : ℝ) 1)).real {t : ℝ | x ∈ Ico (qm μ₂ t) (qm μ₁ t)} := by
    rw [real_setA μ₁ μ₂ x, Set.coe_projIcc, min_eq_right h3, max_comm]
  exact integral_indicator_field {t : ℝ | x ∈ Ico (qm μ₂ t) (qm μ₁ t)}
    (measurable_setA μ₁ μ₂ x)
    (Set.projIcc (0 : ℝ) 1 zero_le_one (μ₂.real (Iic x) - μ₁.real (Iic x))) hp d

/-- The second Bernoulli model in Martin (2004), Lemma 4.2: mean last passage of the field
`-I(X1 <= x, X2 > x)` is that of the Bernoulli model `1 - I(X1 <= x, X2 > x)` minus the
number of sites. -/
private theorem integral_FB (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (x : ℝ) (d : ℕ × ℕ) :
    ∫ u, lastPassage (fun z => -((Ico (qm μ₁ (u z)) (qm μ₂ (u z))).indicator
        (fun _ => (1 : ℝ)) x)) 0 d ∂uniformField =
      ∫ ω, lastPassage ω 0 d ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0
        (unitInterval.symm
          (Set.projIcc (0 : ℝ) 1 zero_le_one (μ₁.real (Iic x) - μ₂.real (Iic x))))) -
        ((d.1 + d.2 : ℕ) : ℝ) := by
  have hν := uniform_prob
  have h1 : 0 ≤ μ₂.real (Iic x) := measureReal_nonneg
  have h2 : μ₁.real (Iic x) ≤ 1 := measureReal_le_one
  have h3 : μ₁.real (Iic x) - μ₂.real (Iic x) ≤ 1 := by linarith
  have hS : MeasurableSet {t : ℝ | x ∈ Ico (qm μ₁ t) (qm μ₂ t)} :=
    measurable_setA μ₂ μ₁ x
  have hp : ((unitInterval.symm
        (Set.projIcc (0 : ℝ) 1 zero_le_one (μ₁.real (Iic x) - μ₂.real (Iic x))) :
        unitInterval) : ℝ) =
      (volume.restrict (Ioo (0 : ℝ) 1)).real {t : ℝ | x ∈ Ico (qm μ₁ t) (qm μ₂ t)}ᶜ := by
    rw [unitInterval.coe_symm_eq, Set.coe_projIcc, measureReal_compl hS, real_setA μ₂ μ₁ x,
      probReal_univ, min_eq_right h3, max_comm]
  have hpt : ∀ u : Environment,
      lastPassage (fun z => -((Ico (qm μ₁ (u z)) (qm μ₂ (u z))).indicator
        (fun _ => (1 : ℝ)) x)) 0 d =
        lastPassage (fun z => ({t : ℝ | x ∈ Ico (qm μ₁ t) (qm μ₂ t)}ᶜ).indicator
          (fun _ => (1 : ℝ)) (u z)) 0 d + ((d.1 + d.2 : ℕ) : ℝ) * (-1) := by
    intro u
    rw [← lastPassage_add_const (fun z : Lattice =>
      ({t : ℝ | x ∈ Ico (qm μ₁ t) (qm μ₂ t)}ᶜ).indicator (fun _ => (1 : ℝ)) (u z)) 0 d (-1)]
    congr 1
    funext z
    show -((Ico (qm μ₁ (u z)) (qm μ₂ (u z))).indicator (fun _ => (1 : ℝ)) x) =
      ({t : ℝ | x ∈ Ico (qm μ₁ t) (qm μ₂ t)}ᶜ).indicator (fun _ => (1 : ℝ)) (u z) + -1
    by_cases h : x ∈ Ico (qm μ₁ (u z)) (qm μ₂ (u z))
    · rw [indicator_of_mem h, indicator_of_notMem
        (show u z ∉ {t : ℝ | x ∈ Ico (qm μ₁ t) (qm μ₂ t)}ᶜ from fun hc => hc h)]
      ring
    · rw [indicator_of_notMem h, indicator_of_mem
        (show u z ∈ {t : ℝ | x ∈ Ico (qm μ₁ t) (qm μ₂ t)}ᶜ from h)]
      ring
  have hint := integrable_indicator_field _ hS.compl
    (unitInterval.symm
      (Set.projIcc (0 : ℝ) 1 zero_le_one (μ₁.real (Iic x) - μ₂.real (Iic x)))) hp d
  calc ∫ u, lastPassage (fun z => -((Ico (qm μ₁ (u z)) (qm μ₂ (u z))).indicator
        (fun _ => (1 : ℝ)) x)) 0 d ∂uniformField
      = ∫ u, (lastPassage (fun z => ({t : ℝ | x ∈ Ico (qm μ₁ t) (qm μ₂ t)}ᶜ).indicator
          (fun _ => (1 : ℝ)) (u z)) 0 d + ((d.1 + d.2 : ℕ) : ℝ) * (-1)) ∂uniformField :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ u, lastPassage (fun z => ({t : ℝ | x ∈ Ico (qm μ₁ t) (qm μ₂ t)}ᶜ).indicator
          (fun _ => (1 : ℝ)) (u z)) 0 d ∂uniformField + ((d.1 + d.2 : ℕ) : ℝ) * (-1) := by
        rw [integral_add hint (integrable_const _), integral_const]
        simp
    _ = ∫ ω, lastPassage ω 0 d ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0
        (unitInterval.symm
          (Set.projIcc (0 : ℝ) 1 zero_le_one (μ₁.real (Iic x) - μ₂.real (Iic x))))) -
        ((d.1 + d.2 : ℕ) : ℝ) := by
        rw [integral_indicator_field _ hS.compl
          (unitInterval.symm
            (Set.projIcc (0 : ℝ) 1 zero_le_one (μ₁.real (Iic x) - μ₂.real (Iic x)))) hp d]
        ring

/-! ### The finite-box inequality -/

/-- The integrand of the first Bernoulli display in the proof of Martin (2004), Lemma 4.2, for a
box of displacement `d`: the mean last passage of the first Bernoulli model plus that of the
second, minus the number of sites. -/
private noncomputable def splitIntegrand (μ₁ μ₂ : Measure ℝ) (d : ℕ × ℕ) (x : ℝ) : ℝ :=
  ∫ ω, lastPassage ω 0 d ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0
      (Set.projIcc (0 : ℝ) 1 zero_le_one (μ₂.real (Iic x) - μ₁.real (Iic x)))) +
    ∫ ω, lastPassage ω 0 d ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0
      (unitInterval.symm
        (Set.projIcc (0 : ℝ) 1 zero_le_one (μ₁.real (Iic x) - μ₂.real (Iic x))))) -
    ((d.1 + d.2 : ℕ) : ℝ)

private theorem splitting_core (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂]
    (h₁ : Integrable (fun t : ℝ => t) μ₁) (h₂ : Integrable (fun t : ℝ => t) μ₂)
    (d : ℕ × ℕ) :
    Integrable (splitIntegrand μ₁ μ₂ d) ∧
      ∫ ω, lastPassage ω 0 d ∂environmentLaw μ₁ - ∫ ω, lastPassage ω 0 d ∂environmentLaw μ₂ ≤
        ∫ x : ℝ, splitIntegrand μ₁ μ₂ d x := by
  have hν := uniform_prob
  -- The coupled environments of the proof of Martin (2004), Lemma 4.2.
  let X₁ : Environment → Environment := fun u z => qm μ₁ (u z)
  let X₂ : Environment → Environment := fun u z => qm μ₂ (u z)
  have hm₁ : ∀ z : Lattice, Measurable fun u : Environment => X₁ u z := fun z =>
    (measurable_qm μ₁).comp (measurable_pi_apply z)
  have hm₂ : ∀ z : Lattice, Measurable fun u : Environment => X₂ u z := fun z =>
    (measurable_qm μ₂).comp (measurable_pi_apply z)
  have hX₁ : Measurable X₁ := measurable_pi_iff.2 hm₁
  have hX₂ : Measurable X₂ := measurable_pi_iff.2 hm₂
  have hlaw₁ : uniformField.map X₁ = environmentLaw μ₁ :=
    map_indicator_source_quantile_field μ₁
  have hlaw₂ : uniformField.map X₂ = environmentLaw μ₂ :=
    map_indicator_source_quantile_field μ₂
  have hi₁ : ∀ z : Lattice, Integrable (fun u : Environment => X₁ u z) uniformField := fun z => by
    have h := integrable_environment_eval μ₁ h₁ z
    rw [← hlaw₁] at h
    exact (integrable_map_measure (measurable_pi_apply z).aestronglyMeasurable
      hX₁.aemeasurable).1 h
  have hi₂ : ∀ z : Lattice, Integrable (fun u : Environment => X₂ u z) uniformField := fun z => by
    have h := integrable_environment_eval μ₂ h₂ z
    rw [← hlaw₂] at h
    exact (integrable_map_measure (measurable_pi_apply z).aestronglyMeasurable
      hX₂.aemeasurable).1 h
  have hmean₁ : ∫ ω, lastPassage ω 0 d ∂environmentLaw μ₁ =
      ∫ u, lastPassage (X₁ u) 0 d ∂uniformField := by
    rw [← hlaw₁]
    exact integral_map hX₁.aemeasurable (measurable_lastPassage 0 d).aestronglyMeasurable
  have hmean₂ : ∫ ω, lastPassage ω 0 d ∂environmentLaw μ₂ =
      ∫ u, lastPassage (X₂ u) 0 d ∂uniformField := by
    rw [← hlaw₂]
    exact integral_map hX₂.aemeasurable (measurable_lastPassage 0 d).aestronglyMeasurable
  -- The three last-passage functions of the product space, and their integrability.
  let FL : Environment × ℝ → ℝ := fun q => lastPassage (fun z =>
    (Ico (X₂ q.1 z) (X₁ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2 -
      (Ico (X₁ q.1 z) (X₂ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2) 0 d
  let FA : Environment × ℝ → ℝ := fun q => lastPassage (fun z =>
    (Ico (X₂ q.1 z) (X₁ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2) 0 d
  let FB : Environment × ℝ → ℝ := fun q => lastPassage (fun z =>
    -((Ico (X₁ q.1 z) (X₂ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2)) 0 d
  have hFL : Integrable FL (uniformField.prod volume) :=
    integrable_lastPassage_layer_prod uniformField X₁ X₂ hm₁ hm₂ hi₁ hi₂ d
  have hFA : Integrable FA (uniformField.prod volume) :=
    integrable_lastPassage_of_coord
      (Y := fun (q : Environment × ℝ) (z : Lattice) =>
        (Ico (X₂ q.1 z) (X₁ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2) (fun z =>
        integrable_indicator_Ico_prod uniformField (fun u => X₁ u z) (fun u => X₂ u z)
          (hm₁ z) (hm₂ z) (hi₁ z) (hi₂ z)) 0 d
  have hFB : Integrable FB (uniformField.prod volume) :=
    integrable_lastPassage_of_coord
      (Y := fun (q : Environment × ℝ) (z : Lattice) =>
        -((Ico (X₁ q.1 z) (X₂ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2)) (fun z =>
        (integrable_indicator_Ico_prod uniformField (fun u => X₂ u z) (fun u => X₁ u z)
          (hm₂ z) (hm₁ z) (hi₂ z) (hi₁ z)).neg) 0 d
  -- Splitting: the maximum of a sum is at most the sum of the maxima.
  have hpt : ∀ q : Environment × ℝ, FL q ≤ FA q + FB q := by
    intro q
    have h := lastPassage_add_le
      (fun z => (Ico (X₂ q.1 z) (X₁ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2)
      (fun z => -((Ico (X₁ q.1 z) (X₂ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2)) 0 d
    have e : (fun z : Lattice =>
        (Ico (X₂ q.1 z) (X₁ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2 -
          (Ico (X₁ q.1 z) (X₂ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2) =
        (fun z => (Ico (X₂ q.1 z) (X₁ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2) +
          (fun z => -((Ico (X₁ q.1 z) (X₂ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2)) :=
      funext fun z => sub_eq_add_neg _ _
    show lastPassage (fun z : Lattice =>
        (Ico (X₂ q.1 z) (X₁ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2 -
          (Ico (X₁ q.1 z) (X₂ q.1 z)).indicator (fun _ => (1 : ℝ)) q.2) 0 d ≤ FA q + FB q
    rw [e]
    exact h
  -- Integrating over the probability space for each level, then over the levels.
  have hmono : ∫ x : ℝ, ∫ u, FL (u, x) ∂uniformField ≤
      ∫ x : ℝ, (∫ u, FA (u, x) ∂uniformField + ∫ u, FB (u, x) ∂uniformField) := by
    refine integral_mono_ae hFL.integral_prod_right
      (hFA.integral_prod_right.add hFB.integral_prod_right) ?_
    filter_upwards [hFL.prod_left_ae, hFA.prod_left_ae, hFB.prod_left_ae] with x hL hA hB
    exact le_of_le_of_eq (integral_mono hL (hA.add hB) fun u => hpt (u, x))
      (integral_add hA hB)
  -- The two Bernoulli models (the first Bernoulli display of the proof).
  have hEA : ∀ x : ℝ, ∫ u, FA (u, x) ∂uniformField =
      ∫ ω, lastPassage ω 0 d ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0
        (Set.projIcc (0 : ℝ) 1 zero_le_one (μ₂.real (Iic x) - μ₁.real (Iic x)))) :=
    fun x => integral_FA μ₁ μ₂ x d
  have hEB : ∀ x : ℝ, ∫ u, FB (u, x) ∂uniformField =
      ∫ ω, lastPassage ω 0 d ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0
        (unitInterval.symm
          (Set.projIcc (0 : ℝ) 1 zero_le_one (μ₁.real (Iic x) - μ₂.real (Iic x))))) -
        ((d.1 + d.2 : ℕ) : ℝ) :=
    fun x => integral_FB μ₁ μ₂ x d
  have hsum : ∀ x : ℝ, ∫ u, FA (u, x) ∂uniformField + ∫ u, FB (u, x) ∂uniformField =
      splitIntegrand μ₁ μ₂ d x := by
    intro x
    rw [hEA x, hEB x]
    unfold splitIntegrand
    ring
  have hfun : splitIntegrand μ₁ μ₂ d =
      fun x => ∫ u, FA (u, x) ∂uniformField + ∫ u, FB (u, x) ∂uniformField :=
    funext fun x => (hsum x).symm
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hFA.integral_prod_right.add hFB.integral_prod_right
  · calc ∫ ω, lastPassage ω 0 d ∂environmentLaw μ₁ - ∫ ω, lastPassage ω 0 d ∂environmentLaw μ₂
        = ∫ u, lastPassage (X₁ u) 0 d ∂uniformField -
            ∫ u, lastPassage (X₂ u) 0 d ∂uniformField := by rw [hmean₁, hmean₂]
      _ ≤ ∫ x : ℝ, ∫ u, FL (u, x) ∂uniformField :=
          integral_lastPassage_sub_le_integral_layer uniformField X₁ X₂ hm₁ hm₂ hi₁ hi₂ d
      _ ≤ ∫ x : ℝ, (∫ u, FA (u, x) ∂uniformField + ∫ u, FB (u, x) ∂uniformField) := hmono
      _ = ∫ x : ℝ, splitIntegrand μ₁ μ₂ d x := integral_congr_ae (Filter.Eventually.of_forall hsum)

/-- The integrand of the first Bernoulli display in the proof of Martin (2004), Lemma 4.2
is integrable over the level `x`. -/
theorem integrable_bernoulli_splitting_integrand (μ₁ μ₂ : Measure ℝ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : Integrable (fun t : ℝ => t) μ₁) (h₂ : Integrable (fun t : ℝ => t) μ₂)
    (d : ℕ × ℕ) :
    Integrable (fun x : ℝ =>
      ∫ ω, lastPassage ω 0 d ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0
          (Set.projIcc (0 : ℝ) 1 zero_le_one (μ₂.real (Iic x) - μ₁.real (Iic x)))) +
        ∫ ω, lastPassage ω 0 d ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0
          (unitInterval.symm
            (Set.projIcc (0 : ℝ) 1 zero_le_one (μ₁.real (Iic x) - μ₂.real (Iic x))))) -
        ((d.1 + d.2 : ℕ) : ℝ)) :=
  (splitting_core μ₁ μ₂ h₁ h₂ d).1

/-- Martin (2004), proof of Lemma 4.2, up to its first Bernoulli display, for a finite box.
The mean
last passage to `d` for weights of law `μ₁`, minus that for law `μ₂`, is at most the integral over
the level `x` of: the mean last passage of the Bernoulli model with parameter
`[F2(x) - F1(x)]_+`, plus that of the Bernoulli model with parameter `1 - [F1(x) - F2(x)]_+`,
minus the number of sites `d.1 + d.2` of a path. The limit in the box size is not taken here. -/
theorem lastPassage_mean_sub_le_integral_bernoulli (μ₁ μ₂ : Measure ℝ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : Integrable (fun t : ℝ => t) μ₁) (h₂ : Integrable (fun t : ℝ => t) μ₂)
    (d : ℕ × ℕ) :
    ∫ ω, lastPassage ω 0 d ∂environmentLaw μ₁ - ∫ ω, lastPassage ω 0 d ∂environmentLaw μ₂ ≤
      ∫ x : ℝ,
        (∫ ω, lastPassage ω 0 d ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0
            (Set.projIcc (0 : ℝ) 1 zero_le_one (μ₂.real (Iic x) - μ₁.real (Iic x)))) +
          ∫ ω, lastPassage ω 0 d ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0
            (unitInterval.symm
              (Set.projIcc (0 : ℝ) 1 zero_le_one (μ₁.real (Iic x) - μ₂.real (Iic x))))) -
          ((d.1 + d.2 : ℕ) : ℝ)) :=
  (splitting_core μ₁ μ₂ h₁ h₂ d).2

end LPPDifferentiability
