/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section
open MeasureTheory

namespace ProbabilityBasics

/-- If a measurable output is unchanged almost surely when the outside coordinate is resampled, it has a measurable version depending only on the retained coordinate. This is the version step in the public Strong Existence source, lines 998–1003. -/
theorem exists_measurable_retained_version_of_ae_resampling_invariant
    {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (P : Measure X) [SFinite P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (f : X × Y → Z) (hf : Measurable f)
    (hinv : ∀ᵐ p : Y × (X × Y) ∂Q.prod (P.prod Q),
      f p.2 = f (p.2.1, p.1)) :
    ∃ g : X → Z, Measurable g ∧
      ∀ᵐ p : X × Y ∂P.prod Q, f p = g p.1 := by
  -- Fubini turns the triple almost-everywhere identity into good outside sections.
  have hsections :
      ∀ᵐ y ∂Q, ∀ᵐ p : X × Y ∂P.prod Q, f p = f (p.1, y) :=
    Measure.ae_ae_of_ae_prod hinv
  -- A probability has a nonempty almost-everywhere filter, so one good outside value exists.
  have hgood : ∃ y, ∀ᵐ p : X × Y ∂P.prod Q, f p = f (p.1, y) :=
    hsections.exists
  obtain ⟨y₀, hy₀⟩ := hgood
  -- The fixed outside section supplies the retained-coordinate version.
  refine ⟨fun x => f (x, y₀), ?_, ?_⟩
  · -- Restricting a measurable map to a fixed section preserves measurability.
    exact hf.comp (measurable_id.prodMk measurable_const)
  · -- The selected section equality is exactly the required almost-everywhere result.
    filter_upwards [hy₀] with p hp
    exact hp

end ProbabilityBasics
