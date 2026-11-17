/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.ResamplingVersion
public import ProbabilityBasics.Probability.DisjointFamilies
public import LPP_Foundations.Probability.CoordinateLaw
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# A retained-coordinate version of an environment observable

The canonical iid environment splits into independent arrays on a set of sites
and its complement. An observable unchanged by fresh outside resampling therefore
has a measurable version on the retained array.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- A measurable observable of an iid environment that is unchanged almost
surely by independently resampling outside `S` has a measurable version on the
retained coordinate array. This is the version step in the public Strong
Existence source, lines 998–999. -/
theorem exists_measurable_restriction_version_of_ae_resampling_invariant
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (S : Set Lattice) [DecidablePred (fun z : Lattice => z ∈ S)]
    {Z : Type*} [MeasurableSpace Z]
    (f : Environment → Z) (hf : Measurable f)
    (hinv : ∀ᵐ p : Environment × Environment ∂
      (environmentLaw μ).prod (environmentLaw μ),
      f p.1 = f (Set.piecewise S p.1 p.2)) :
    ∃ g : (S → ℝ) → Z, Measurable g ∧
      ∀ᵐ ω ∂environmentLaw μ,
        f ω = g (fun z : S => ω z) := by
  let P₀ : Measure Environment := environmentLaw μ
  let P : Measure (S → ℝ) := Measure.infinitePi (fun _ : S => μ)
  let Q : Measure (↥(Sᶜ) → ℝ) := Measure.infinitePi (fun _ : ↥(Sᶜ) => μ)
  let e : Environment ≃ᵐ (S → ℝ) × (↥(Sᶜ) → ℝ) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Lattice => ℝ)
      (fun z : Lattice => z ∈ S)
  -- The two restricted arrays have their prescribed marginal laws.
  have hP : P₀.map (fun ω : Environment => fun z : S => ω z) = P := by
    change (Measure.infinitePi (fun _ : Lattice => μ)).map S.domRestrict =
      Measure.infinitePi (fun _ : S => μ)
    exact Measure.infinitePi_map_restrict' (fun _ : Lattice => μ) (I := S)
  have hQ : P₀.map (fun ω : Environment => fun z : ↥(Sᶜ) => ω z) = Q := by
    change (Measure.infinitePi (fun _ : Lattice => μ)).map (Sᶜ).domRestrict =
      Measure.infinitePi (fun _ : ↥(Sᶜ) => μ)
    exact Measure.infinitePi_map_restrict' (fun _ : Lattice => μ) (I := Sᶜ)

  -- Disjoint coordinate families give the full joint law of the split array.
  have hdisjoint : Disjoint S Sᶜ := disjoint_compl_right
  have hindep : IndepFun
      (fun ω : Environment => fun z : S => ω z)
      (fun ω : Environment => fun z : ↥(Sᶜ) => ω z) P₀ :=
    ProbabilityBasics.indepFun_restrict_of_iIndepFun P₀
      (fun z (ω : Environment) => ω z)
      (iIndepFun_environment_eval μ)
      measurable_environment_eval S Sᶜ hdisjoint
  have hsplit : P₀.map e = P.prod Q := by
    change P₀.map (fun ω : Environment =>
      ((fun z : S => ω z), (fun z : ↥(Sᶜ) => ω z))) = P.prod Q
    rw [hindep.map_prod_eq_prod_map_map
      (measurable_pi_iff.mpr (fun z : S => measurable_environment_eval z)).aemeasurable
      (measurable_pi_iff.mpr (fun z : ↥(Sᶜ) =>
        measurable_environment_eval z)).aemeasurable,
      hP, hQ]

  -- The inverse split reassembles retained and outside coordinates pointwise.
  have hpiecewise (ω η : Environment) :
      e.symm ((e ω).1, (e η).2) = Set.piecewise S ω η := by
    apply e.injective
    rw [e.apply_symm_apply]
    change
      ((fun z : S => ω z), (fun z : ↥(Sᶜ) => η z)) =
      ((fun z : S => Set.piecewise S ω η z),
        (fun z : ↥(Sᶜ) => Set.piecewise S ω η z))
    apply Prod.ext
    · funext z
      exact (S.piecewise_eq_of_mem (f := ω) (g := η) z.property).symm
    · funext z
      exact (S.piecewise_eq_of_notMem (f := ω) (g := η) z.property).symm

  -- Split both independent environments, then put the unused fresh retained
  -- array first. Its remaining coordinates have the generic theorem's order.
  let E : (Environment × Environment) ≃ᵐ
      (S → ℝ) × ((↥(Sᶜ) → ℝ) × ((S → ℝ) × (↥(Sᶜ) → ℝ))) :=
    ((MeasurableEquiv.prodCongr e e).trans MeasurableEquiv.prodComm).trans
      MeasurableEquiv.prodAssoc
  have hEpoint (p : Environment × Environment) :
      E p = ((e p.2).1, ((e p.2).2, e p.1)) := rfl
  have hpair : (P₀.prod P₀).map (MeasurableEquiv.prodCongr e e) =
      (P.prod Q).prod (P.prod Q) := by
    change (P₀.prod P₀).map (Prod.map e e) = (P.prod Q).prod (P.prod Q)
    rw [← Measure.map_prod_map P₀ P₀ e.measurable e.measurable, hsplit]
  have hE : (P₀.prod P₀).map E = P.prod (Q.prod (P.prod Q)) := by
    calc
      (P₀.prod P₀).map E =
          (((P₀.prod P₀).map (MeasurableEquiv.prodCongr e e)).map
            MeasurableEquiv.prodComm).map MeasurableEquiv.prodAssoc := by
              rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable
                MeasurableEquiv.prodComm.measurable,
                Measure.map_map (MeasurableEquiv.prodAssoc.measurable.comp
                  MeasurableEquiv.prodComm.measurable)
                  (MeasurableEquiv.prodCongr e e).measurable]
              rfl
      _ = P.prod (Q.prod (P.prod Q)) := by
        rw [hpair]
        change (((P.prod Q).prod (P.prod Q)).map Prod.swap).map
          MeasurableEquiv.prodAssoc = P.prod (Q.prod (P.prod Q))
        rw [Measure.prod_swap, Measure.prodAssoc_prod]

  -- Transport the original almost-sure resampling identity through the
  -- equivalence; no measurable equality predicate on `Z` is needed.
  have htrans : ∀ᵐ t ∂P.prod (Q.prod (P.prod Q)),
      f (e.symm t.2.2) = f (e.symm (t.2.2.1, t.2.1)) := by
    rw [← hE, ← MeasurableEquiv.map_ae E (P₀.prod P₀)]
    simp only [Filter.eventually_map]
    filter_upwards [hinv] with p hp
    rw [hEpoint]
    simpa only [e.symm_apply_apply, hpiecewise] using hp

  -- Fubini removes the fresh retained array, which the equality does not use.
  have hsections : ∀ᵐ x ∂P, ∀ᵐ t ∂Q.prod (P.prod Q),
      f (e.symm t.2) = f (e.symm (t.2.1, t.1)) :=
    Measure.ae_ae_of_ae_prod htrans
  obtain ⟨_, htriple⟩ := hsections.exists

  -- Apply the generic version theorem to the split observable.
  have hmeas : Measurable (fun p : (S → ℝ) × (↥(Sᶜ) → ℝ) => f (e.symm p)) :=
    hf.comp e.symm.measurable
  obtain ⟨g, hgmeas, hga⟩ :=
    ProbabilityBasics.exists_measurable_retained_version_of_ae_resampling_invariant
      P Q (fun p => f (e.symm p)) hmeas htriple
  refine ⟨g, hgmeas, ?_⟩

  -- Pull the version back through the split map to the original law.
  have hback : ∀ᵐ ω ∂P₀,
      f (e.symm (e ω)) = g (e ω).1 := by
    rw [← hsplit] at hga
    exact ae_of_ae_map e.measurable.aemeasurable hga
  filter_upwards [hback] with ω hω
  change f ω = g (e ω).1
  simpa only [e.symm_apply_apply] using hω

end LPPDifferentiability
