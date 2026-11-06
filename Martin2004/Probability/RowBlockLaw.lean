/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# The block environment is i.i.d. with the `r`-fold sum law

Martin (2004), proof of Lemma 4.4: if the weights `X(z)` are i.i.d. with law `F`, the block weights
`X~^(r)(z) = sum of X(v) over the sites v of the block B^(r)(z)` are i.i.d. with law `F^(r)`, the
law of `X_1 + ... + X_r`. Martin states this without proof.

The block `B^(r)(z)` of the site `z = (x, y)` is `{(r x + j, y) : 0 <= j < r}`, and the law `F^(r)`
is the hypothesis `hν` below (the image of the product law of `r` coordinates under the sum), so
no definition is introduced. The proof regroups the sites of the lattice through the bijection
`((x, y), j) <-> (r x + j, y)` (division with remainder in the first coordinate), then uses the
product-measure facts for currying and for coordinatewise maps.
-/

@[expose] public section

open MeasureTheory

namespace LPPDifferentiability

/-- Division with remainder in the first coordinate: the site `(x * r + j, y)` corresponds to the
block `(x, y)` and the position `j` inside it. -/
private def blockSiteEquiv (r : ℕ) [NeZero r] : Lattice × Fin r ≃ Lattice where
  toFun p := (p.1.1 * (r : ℤ) + ((p.2 : ℕ) : ℤ), p.1.2)
  invFun z := (((Int.divModEquiv r z.1).1, z.2), (Int.divModEquiv r z.1).2)
  left_inv p := by
    obtain ⟨⟨a, y⟩, j⟩ := p
    have h := (Int.divModEquiv r).apply_symm_apply (a, j)
    simp only [Int.divModEquiv_symm_apply] at h
    show (((Int.divModEquiv r (a * (r : ℤ) + ((j : ℕ) : ℤ))).1, y),
      (Int.divModEquiv r (a * (r : ℤ) + ((j : ℕ) : ℤ))).2) = ((a, y), j)
    rw [h]
  right_inv z := by
    have h := (Int.divModEquiv r).symm_apply_apply z.1
    simp only [Int.divModEquiv_symm_apply] at h
    exact Prod.ext h rfl

/-- Martin (2004), proof of Lemma 4.4: the block environment of an i.i.d. environment with law `μ`
is an i.i.d. environment whose marginal is the law `ν` of the sum of `r` independent copies of `μ`.
The block at the site `z` has weight `sum over j < r of ω (r x + j, y)`. -/
theorem map_environmentLaw_blockField (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℕ)
    (hr : 1 ≤ r) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = (Measure.pi (fun _ : Fin r => μ)).map (fun y => ∑ i, y i)) :
    (environmentLaw μ).map
        (fun (ω : Environment) (z : Lattice) =>
          ∑ j ∈ Finset.range r, ω ((r : ℤ) * z.1 + (j : ℤ), z.2)) =
      environmentLaw ν := by
  subst hν
  have : NeZero r := ⟨by omega⟩
  have hΦ : Measurable
      (fun (ω : Environment) (p : Lattice × Fin r) => ω (blockSiteEquiv r p)) :=
    measurable_pi_iff.2 fun p => measurable_pi_apply _
  have hsum : Measurable (fun y : Fin r → ℝ => ∑ i, y i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hF : Measurable (fun (x : Lattice → Fin r → ℝ) (z : Lattice) => ∑ i, x z i) :=
    measurable_pi_iff.2 fun z => Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply i).comp (measurable_pi_apply z)
  -- Step 1: regroup the sites of the lattice into blocks and positions inside a block.
  have h1 : (Measure.infinitePi fun _ : Lattice => μ).map
      (fun (ω : Environment) (p : Lattice × Fin r) => ω (blockSiteEquiv r p)) =
        Measure.infinitePi fun _ : Lattice × Fin r => μ := by
    have h := Measure.infinitePi_map_piCongrLeft (X := fun _ : Lattice => ℝ) (fun _ => μ)
      (blockSiteEquiv r)
    calc (Measure.infinitePi fun _ : Lattice => μ).map
          (fun (ω : Environment) (p : Lattice × Fin r) => ω (blockSiteEquiv r p))
        = ((Measure.infinitePi fun _ : Lattice × Fin r => μ).map
            (MeasurableEquiv.piCongrLeft (fun _ : Lattice => ℝ) (blockSiteEquiv r))).map
            (fun (ω : Environment) (p : Lattice × Fin r) => ω (blockSiteEquiv r p)) := by
          rw [h]
      _ = (Measure.infinitePi fun _ : Lattice × Fin r => μ).map
            ((fun (ω : Environment) (p : Lattice × Fin r) => ω (blockSiteEquiv r p)) ∘
              (MeasurableEquiv.piCongrLeft (fun _ : Lattice => ℝ) (blockSiteEquiv r))) :=
          Measure.map_map hΦ (MeasurableEquiv.measurable _)
      _ = (Measure.infinitePi fun _ : Lattice × Fin r => μ).map id := by
          congr 1
          funext x
          funext p
          exact MeasurableEquiv.piCongrLeft_apply_apply (blockSiteEquiv r) (β := fun _ => ℝ) x p
      _ = Measure.infinitePi fun _ : Lattice × Fin r => μ := Measure.map_id
  -- Step 2: currying turns the product over pairs into a product over blocks of a product over
  -- the positions inside the block.
  have h2 : (Measure.infinitePi fun _ : Lattice × Fin r => μ).map
      (MeasurableEquiv.curry Lattice (Fin r) ℝ) =
        Measure.infinitePi fun _ : Lattice => Measure.infinitePi fun _ : Fin r => μ :=
    Measure.infinitePi_map_curry (X := ℝ) (fun _ _ => μ)
  -- Step 3: summing the positions inside each block turns the product of products into the
  -- product of the sum law.
  have h3 : (Measure.infinitePi fun _ : Lattice => Measure.infinitePi fun _ : Fin r => μ).map
      (fun (x : Lattice → Fin r → ℝ) (z : Lattice) => ∑ i, x z i) =
        Measure.infinitePi fun _ : Lattice =>
          (Measure.pi (fun _ : Fin r => μ)).map (fun y => ∑ i, y i) := by
    have h := Measure.infinitePi_map_pi
      (fun _ : Lattice => (Measure.infinitePi fun _ : Fin r => μ)) (Y := fun _ => ℝ)
      (f := fun _ (y : Fin r → ℝ) => ∑ i, y i) (fun _ => hsum)
    rw [h, Measure.infinitePi_eq_pi (fun _ : Fin r => μ)]
  -- The block map is the composite of the three maps.
  have hcomp : (fun (ω : Environment) (z : Lattice) =>
        ∑ j ∈ Finset.range r, ω ((r : ℤ) * z.1 + (j : ℤ), z.2)) =
      (fun (x : Lattice → Fin r → ℝ) (z : Lattice) => ∑ i, x z i) ∘
        ((MeasurableEquiv.curry Lattice (Fin r) ℝ) ∘
          (fun (ω : Environment) (p : Lattice × Fin r) => ω (blockSiteEquiv r p))) := by
    funext ω z
    show _ = ∑ i : Fin r, ω (blockSiteEquiv r (z, i))
    rw [← Fin.sum_univ_eq_sum_range (fun j => ω ((r : ℤ) * z.1 + (j : ℤ), z.2)) r]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine congrArg ω (Prod.ext ?_ rfl)
    show (r : ℤ) * z.1 + ((i : ℕ) : ℤ) = z.1 * (r : ℤ) + ((i : ℕ) : ℤ)
    ring
  have hc : Measurable (MeasurableEquiv.curry Lattice (Fin r) ℝ) := MeasurableEquiv.measurable _
  unfold environmentLaw
  rw [hcomp, ← Measure.map_map hF (hc.comp hΦ), ← Measure.map_map hc hΦ, h1, h2, h3]

end LPPDifferentiability
