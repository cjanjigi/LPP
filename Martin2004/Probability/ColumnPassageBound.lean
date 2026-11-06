/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Analysis.ColumnBoundOptimization
public import Martin2004.Model.ColumnPassage
public import Martin2004.Model.StationaryColumns
public import Martin2004.Probability.ColumnLaws
public import LPP_Foundations.Probability.FiniteEnvironmentLaw
public import Martin2004.Probability.StationaryColumns
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# The mean of the one-site-per-column passage time

Martin (2004), Lemma 4.1, quotes Seppäläinen (1998) for the limit of `E T̃(m, n) / n`. Here the
upper bound is proved at every finite size, in two steps.

* `integral_columnPassage_le_stationary`: if `θ < 1` and `ρ θ (1 - p) = p (1 - ρ)`, the
  mean of `columnPassage` under the environment law with `Ber(p)` weights is at most
  `m ρ + (n + 1) θ / (1 - θ)`. The environment is placed next to independent boundary inputs
  (`Ber(ρ)` bottom increments and `Geom(θ)` left column). The boundary column is nonnegative
  almost surely, so the deterministic comparison of `Model/StationaryColumns.lean` bounds
  `columnPassage` by the stationary passage time. The box of weights together with the inputs
  has the law `stationaryColumnLaw`, whose mean is known.
* `integral_columnPassage_le`: for a law carried by `{0, 1}` with `P(1) = p`, the mean is
  at most `m p + 2 √(m (n + 1) p (1 - p))`. It combines the trivial bound (parameters
  `ρ = 1`, `θ = 0`),
  the stationary bound for every `ρ` in `(p, 1)` with `θ = p (1 - ρ) / (ρ (1 - p))`, and the
  optimization lemma `le_mul_add_two_sqrt_of_stationary_bounds` with `N = n + 1`.
-/

open MeasureTheory ProbabilityTheory unitInterval

namespace LPPDifferentiability

/-! ## The coupling of the environment with the boundary inputs -/

/-- The box of weights `(omega (i, j))` with `i < m`, `j ≤ n` has the law of an array of
independent copies of `μ`: the sites of the box are distinct sites of the lattice. -/
private theorem environmentLaw_map_box (μ : Measure ℝ) [IsProbabilityMeasure μ] (m n : ℕ) :
    (environmentLaw μ).map
        (fun ω : Environment => fun (i : Fin m) (j : Fin (n + 1)) =>
          ω (((i : ℕ) : ℤ), ((j : ℕ) : ℤ))) =
      Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (n + 1) => μ := by
  have hinj : Function.Injective (fun s : (Σ _ : Fin m, Fin (n + 1)) =>
      ((((s.1 : ℕ) : ℤ), ((s.2 : ℕ) : ℤ)) : Lattice)) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only [Prod.mk.injEq, Nat.cast_inj, Fin.val_inj] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  exact @environmentLaw_map_finite_blocks (Fin m) _ (fun _ => Fin (n + 1)) _ μ _ _ hinj

/-- **The coupling**. Put the environment with `Ber(p)` weights next to independent
boundary inputs: `Ber(ρ)` bottom increments and `Geom(θ)` left column. Sending
`(omega, (I, J))` to `(I, J, box omega)`, with `box omega` the weights of the sites `(i, j)`,
`i < m`, `j ≤ n`, gives exactly the input law `stationaryColumnLaw p ρ θ m n` of the stationary
column model. -/
private theorem measurePreserving_coupling (p ρ θ : unitInterval) (m n : ℕ) :
    MeasurePreserving
      (fun z : Environment × ((Fin m → ℝ) × (Fin (n + 1) → ℝ)) =>
        (z.2.1, z.2.2, fun (i : Fin m) (j : Fin (n + 1)) =>
          z.1 (((i : ℕ) : ℤ), ((j : ℕ) : ℤ))))
      ((environmentLaw (bernoulliMeasure (1 : ℝ) 0 p)).prod
        ((Measure.pi fun _ : Fin m => bernoulliMeasure (1 : ℝ) 0 ρ).prod
          (Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ)))
      (stationaryColumnLaw p ρ θ m n) := by
  unfold stationaryColumnLaw
  -- stage 1: replace the environment by its box of weights
  have hbox : MeasurePreserving
      (fun ω : Environment => fun (i : Fin m) (j : Fin (n + 1)) =>
        ω (((i : ℕ) : ℤ), ((j : ℕ) : ℤ)))
      (environmentLaw (bernoulliMeasure (1 : ℝ) 0 p))
      (Measure.pi fun _ : Fin m =>
        Measure.pi fun _ : Fin (n + 1) => bernoulliMeasure (1 : ℝ) 0 p) :=
    ⟨measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
      measurable_environment_eval _, environmentLaw_map_box _ m n⟩
  have h1 := hbox.prod (MeasurePreserving.id
    ((Measure.pi fun _ : Fin m => bernoulliMeasure (1 : ℝ) 0 ρ).prod
      (Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ)))
  -- stage 2: put the boundary inputs in front of the weights
  have h2 := Measure.measurePreserving_swap
    (μ := Measure.pi fun _ : Fin m =>
        Measure.pi fun _ : Fin (n + 1) => bernoulliMeasure (1 : ℝ) 0 p)
    (ν := (Measure.pi fun _ : Fin m => bernoulliMeasure (1 : ℝ) 0 ρ).prod
      (Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ))
  -- stage 3: regroup `((I, J), W)` as `(I, (J, W))`
  have h3 := measurePreserving_prodAssoc
    (Measure.pi fun _ : Fin m => bernoulliMeasure (1 : ℝ) 0 ρ)
    (Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ)
    (Measure.pi fun _ : Fin m =>
      Measure.pi fun _ : Fin (n + 1) => bernoulliMeasure (1 : ℝ) 0 p)
  exact h3.comp (h2.comp h1)

/-- The coordinates of a `Geom(θ)` sample are nonnegative almost surely: the count law is carried by
the natural numbers. -/
private theorem ae_geometric_pi_nonneg (θ : unitInterval) (n : ℕ) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ), ∀ j, 0 ≤ x j := by
  rw [ae_all_iff]
  intro j
  have hgeo : ∀ᵐ t ∂geometricCountLaw θ, 0 ≤ t := by
    rw [geometricCountLaw_def]
    exact (ae_map_iff (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).aemeasurable
      measurableSet_Ici).2 (ae_of_all _ fun k => Nat.cast_nonneg k)
  exact (measurePreserving_eval (fun _ : Fin (n + 1) => geometricCountLaw θ) j
    ).quasiMeasurePreserving.ae hgeo

/-! ## The stationary bound -/

/-- **The stationary bound** (Martin (2004), Lemma 4.1, through the stationary comparison of
Seppäläinen (1998), Section 6). Let the weights be independent `Ber(p)`.
If `θ < 1` and `ρ θ (1 - p) = p (1 - ρ)`, the mean of the one-site-per-column passage time satisfies
`E T̃(m, n) ≤ m ρ + (n + 1) θ / (1 - θ)`. -/
theorem integral_columnPassage_le_stationary {p ρ θ : unitInterval} (hθ : (θ : ℝ) < 1)
    (hrel : (ρ : ℝ) * θ * (1 - p) = p * (1 - ρ)) (m n : ℕ) :
    ∫ ω, columnPassage ω m n ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0 p) ≤
      (m : ℝ) * ρ + ((n : ℝ) + 1) * ((θ : ℝ) / (1 - θ)) := by
  -- the environment law and the law of the boundary inputs
  set P := environmentLaw (bernoulliMeasure (1 : ℝ) 0 p) with hP
  set Q := (Measure.pi fun _ : Fin m => bernoulliMeasure (1 : ℝ) 0 ρ).prod
    (Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ) with hQ
  have hmp := measurePreserving_coupling p ρ θ m n
  obtain ⟨hSint, hSmean⟩ := integrable_and_integral_stationaryColumnPassage hθ hrel m n
  -- `columnPassage` does not see the boundary inputs
  have hcp : Integrable (fun ω : Environment => columnPassage ω m n) P :=
    integrable_columnPassage _ (integrable_bernoulliMeasure (1 : ℝ) 0 p (fun t : ℝ => t)) m n
  have hint1 : Integrable (fun z : Environment × ((Fin m → ℝ) × (Fin (n + 1) → ℝ)) =>
      columnPassage z.1 m n) (P.prod Q) := hcp.comp_fst Q
  have hlhs : ∫ ω, columnPassage ω m n ∂P =
      ∫ z, columnPassage z.1 m n ∂P.prod Q := by
    rw [integral_fun_fst (μ := P) (ν := Q) (fun ω : Environment => columnPassage ω m n)]
    simp
  -- the stationary passage time on the coupled inputs
  have hint2 : Integrable
      (fun z : Environment × ((Fin m → ℝ) × (Fin (n + 1) → ℝ)) =>
        stationaryColumnPassage m n z.2.1 z.2.2 (fun (i : Fin m) (j : Fin (n + 1)) =>
          z.1 (((i : ℕ) : ℤ), ((j : ℕ) : ℤ)))) (P.prod Q) :=
    hmp.integrable_comp_of_integrable hSint
  have hcomp : ∫ z : Environment × ((Fin m → ℝ) × (Fin (n + 1) → ℝ)),
      stationaryColumnPassage m n z.2.1 z.2.2 (fun (i : Fin m) (j : Fin (n + 1)) =>
        z.1 (((i : ℕ) : ℤ), ((j : ℕ) : ℤ))) ∂P.prod Q =
      ∫ x, stationaryColumnPassage m n x.1 x.2.1 x.2.2 ∂stationaryColumnLaw p ρ θ m n := by
    conv_rhs => rw [← hmp.map_eq]
    exact (integral_map hmp.measurable.aemeasurable (by
      rw [hmp.map_eq]
      exact hSint.aestronglyMeasurable)).symm
  -- the left column is nonnegative almost surely
  have hJ : ∀ᵐ z ∂(P.prod Q), ∀ j, 0 ≤ z.2.2 j := by
    have hgeo := ae_geometric_pi_nonneg θ n
    have hQ' : ∀ᵐ x ∂Q, ∀ j, 0 ≤ x.2 j :=
      (measurePreserving_snd (μ := Measure.pi fun _ : Fin m => bernoulliMeasure (1 : ℝ) 0 ρ)
        (ν := Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ)).quasiMeasurePreserving.ae
        hgeo
    exact (measurePreserving_snd (μ := P) (ν := Q)).quasiMeasurePreserving.ae hQ'
  -- the comparison of the deterministic part
  have hae : ∀ᵐ z ∂(P.prod Q), columnPassage z.1 m n ≤
      stationaryColumnPassage m n z.2.1 z.2.2 (fun (i : Fin m) (j : Fin (n + 1)) =>
        z.1 (((i : ℕ) : ℤ), ((j : ℕ) : ℤ))) := by
    filter_upwards [hJ] with z hz
    exact columnPassage_le_stationaryColumnPassage z.1 m n z.2.1 hz
  calc ∫ ω, columnPassage ω m n ∂P = ∫ z, columnPassage z.1 m n ∂P.prod Q := hlhs
    _ ≤ _ := integral_mono_ae hint1 hint2 hae
    _ = _ := hcomp
    _ = _ := hSmean

/-! ## The bound for a zero-one law -/

/-- **The column passage bound** (Martin (2004), Lemma 4.1, applied to the finite-size stationary
bounds). If the weight law `μ` is carried by `{0, 1}` and gives `1` the probability `p`, then
`E T̃(m, n) ≤ m p + 2 √(m (n + 1) p (1 - p))`. -/
theorem integral_columnPassage_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h01 : ∀ᵐ t ∂μ, t = 0 ∨ t = 1) (p : ℝ) (hp : μ.real {1} = p) (m n : ℕ) :
    ∫ ω, columnPassage ω m n ∂environmentLaw μ ≤
      (m : ℝ) * p + 2 * Real.sqrt ((m : ℝ) * ((n : ℝ) + 1) * (p * (1 - p))) := by
  obtain ⟨hp01, hμ⟩ := exists_eq_bernoulliMeasure_of_ae_zero_or_one μ h01 p hp
  subst hμ
  -- the trivial bound, from the parameters `ρ = 1`, `θ = 0`
  have htriv : ∫ ω, columnPassage ω m n ∂environmentLaw
      (bernoulliMeasure (1 : ℝ) 0 ⟨p, hp01⟩) ≤ (m : ℝ) := by
    have h := integral_columnPassage_le_stationary (p := ⟨p, hp01⟩) (ρ := 1) (θ := 0)
      (by simp) (by simp) m n
    simpa using h
  -- the stationary bound for every `ρ` in `(p, 1)`, from `θ = p (1 - ρ) / (ρ (1 - p))`
  have hstat : ∀ ρ : ℝ, p < ρ → ρ < 1 →
      ∫ ω, columnPassage ω m n ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0 ⟨p, hp01⟩) ≤
        (m : ℝ) * ρ + ((n : ℝ) + 1) * (p * (1 - ρ) / (ρ - p)) := by
    intro ρ hρ1 hρ2
    have hp1 : p < 1 := hρ1.trans hρ2
    have hρ0 : 0 < ρ := lt_of_le_of_lt hp01.1 hρ1
    have hq : 0 < 1 - p := sub_pos.mpr hp1
    have hρp : 0 < ρ - p := sub_pos.mpr hρ1
    have hden : 0 < ρ * (1 - p) := mul_pos hρ0 hq
    set θ : ℝ := p * (1 - ρ) / (ρ * (1 - p)) with hθdef
    have hθ0 : 0 ≤ θ := div_nonneg (mul_nonneg hp01.1 (by linarith)) hden.le
    have hθ1 : θ < 1 := by
      rw [hθdef, div_lt_one hden]
      nlinarith
    have hrel : ρ * θ * (1 - p) = p * (1 - ρ) := by
      rw [hθdef]
      field_simp
    have h := integral_columnPassage_le_stationary (p := ⟨p, hp01⟩)
      (ρ := ⟨ρ, ⟨hρ0.le, hρ2.le⟩⟩) (θ := ⟨θ, ⟨hθ0, hθ1.le⟩⟩) hθ1 hrel m n
    have hratio : θ / (1 - θ) = p * (1 - ρ) / (ρ - p) := by
      rw [div_eq_div_iff (sub_pos.mpr hθ1).ne' hρp.ne']
      linear_combination hrel
    rw [hratio] at h
    exact h
  exact le_mul_add_two_sqrt_of_stationary_bounds (N := (n : ℝ) + 1) (Nat.cast_nonneg m)
    (by positivity) hp01.1 hp01.2 htriv hstat

end LPPDifferentiability
