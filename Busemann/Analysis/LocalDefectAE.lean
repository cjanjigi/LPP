/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.RandomCocycle
public import LPP_Foundations.Model.LocalDefectPath
public import LPP_Foundations.Probability.TranslationEquiv

/-! Almost-everywhere local cocycle defects give finite-passage bounds. -/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- An almost-sure bound on the two origin defects controls passage from the origin.

This is the conditional finite-passage step in GRS, Theorem 4.4(4.8), used in
the projection argument of Janjigian--Rassoul-Agha (2018), equation (4.21).
The sitewise bounds are obtained from the canonical shifts and cocycle
covariance, then the deterministic path estimate is applied. -/
theorem ae_lastPassage_le_cocycle_add_steps
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (C : Lattice → Lattice → Environment → ℝ)
    (hC : is_shift_covariant_cocycle (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) C)
    (c : ℝ)
    (hdefect : ∀ᵐ ω ∂environmentLaw μ,
      max (ω 0 - C 0 ((1 : ℤ), (0 : ℤ)) ω)
        (ω 0 - C 0 ((0 : ℤ), (1 : ℤ)) ω) ≤ c) :
    ∀ d : ℕ × ℕ, ∀ᵐ ω ∂environmentLaw μ,
      lastPassage ω (0, 0) d ≤
        C 0 ((d.1 : ℤ), (d.2 : ℤ)) ω + ((d.1 + d.2 : ℕ) : ℝ) * c := by
  intro d
  let e₁ : Lattice := ((1 : ℤ), (0 : ℤ))
  let e₂ : Lattice := ((0 : ℤ), (1 : ℤ))
  let P : Measure Environment := environmentLaw μ
  let edgeBound (x : Lattice) (ω : Environment) : Prop :=
    ω x - C x (x + e₁) ω ≤ c ∧ ω x - C x (x + e₂) ω ≤ c

  -- Translate the origin defect event and use cocycle covariance at each site.
  have hright (x : Lattice) : ∀ᵐ ω ∂P, ω x - C x (x + e₁) ω ≤ c := by
    have htranslated :=
      (measurePreserving_environmentTranslationEquiv μ x).quasiMeasurePreserving.ae hdefect
    have hcov := hC.2.1 0 e₁ x
    filter_upwards [htranslated, hcov] with ω hω hcovω
    have htranslated' :
        max (ω x - C 0 e₁ (environmentTranslationEquiv x ω))
          (ω x - C 0 e₂ (environmentTranslationEquiv x ω)) ≤ c := by
      simpa [P, environmentTranslationEquiv_apply] using hω
    have hcov' : C x (x + e₁) ω = C 0 e₁ (environmentTranslationEquiv x ω) := by
      calc
        C x (x + e₁) ω = C (0 + x) (e₁ + x) ω := by
          exact congrArg₂ (fun u v : Lattice => C u v ω)
            (zero_add x).symm (add_comm x e₁)
        _ = C 0 e₁ (environmentTranslationEquiv x ω) := hcovω
    rw [← hcov'] at htranslated'
    exact le_trans (le_max_left _ _) htranslated'

  have hup (x : Lattice) : ∀ᵐ ω ∂P, ω x - C x (x + e₂) ω ≤ c := by
    have htranslated :=
      (measurePreserving_environmentTranslationEquiv μ x).quasiMeasurePreserving.ae hdefect
    have hcov := hC.2.1 0 e₂ x
    filter_upwards [htranslated, hcov] with ω hω hcovω
    have htranslated' :
        max (ω x - C 0 e₁ (environmentTranslationEquiv x ω))
          (ω x - C 0 e₂ (environmentTranslationEquiv x ω)) ≤ c := by
      simpa [P, environmentTranslationEquiv_apply] using hω
    have hcov' : C x (x + e₂) ω = C 0 e₂ (environmentTranslationEquiv x ω) := by
      calc
        C x (x + e₂) ω = C (0 + x) (e₂ + x) ω := by
          exact congrArg₂ (fun u v : Lattice => C u v ω)
            (zero_add x).symm (add_comm x e₂)
        _ = C 0 e₂ (environmentTranslationEquiv x ω) := hcovω
    rw [← hcov'] at htranslated'
    exact le_trans (le_max_right _ _) htranslated'

  -- Countability gives one event on which the two edge bounds hold everywhere.
  have hedges : ∀ᵐ ω ∂P, ∀ x : Lattice, edgeBound x ω := by
    rw [ae_all_iff]
    intro x
    exact (hright x).and (hup x)

  -- The cocycle supplies additivity on one almost-sure event.
  filter_upwards [hedges, hC.2.2] with ω hedgesω hadd
  have hpass := LPP.lastPassage_le_additivePotential_add_steps
    (fun x y => C x y ω)
    (by
      intro x y z
      exact hadd x y z)
    ω c
    (fun x => (hedgesω x).1)
    (fun x => (hedgesω x).2)
    (0, 0) d
  have hzero : ((0, 0) : Lattice) = 0 := by
    ext <;> simp
  simpa [P, edgeBound, e₁, e₂, hzero] using hpass

end LPP.Busemann
