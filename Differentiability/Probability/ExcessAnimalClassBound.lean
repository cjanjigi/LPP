/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.RootedAnimalTransfer
public import Differentiability.Probability.ExcessResidueFieldLaw
public import Differentiability.Model.Animals.ExcessSumCover
import Mathlib.Tactic

/-!
# Uniform animal bounds for residue classes

Pull the rooted animal bound back to each signed residue field on the
original probability space. A single event controls every radius-two
connected finite set in the residue class.
-/

public section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal
namespace LPPDifferentiability

/-- The universal rooted bound pulls back through the actual whole residue
field law. The same event controls every radius-two connected finite set. -/
theorem exists_excess_class_eventually_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      ∀ (a s M : ℝ) (m : ℕ) (Q : Finset Lattice),
      (∀ z, z ∈ Q ↔ 0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ 3 * (m : ℤ) ∧
        |(1-a)*(z.1:ℝ)-a*(z.2:ℝ)| ≤ 4*s+1) →
      3 ≤ s → 1 ≤ m →
      (∫⁻ t in Ioi (0 : ℝ), (environmentLaw μ)
        {ω : Environment | t < ∑ z ∈ Q, max (ω z-M) 0}^(1/2 : ℝ)) < ∞ →
      ∀ (α : Fin 4) (β : Fin 10), ∀ᵐ ω ∂environmentLaw μ,
        ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
          ∀ A : Finset Lattice, (0 : Lattice) ∈ A → A.card ≤ N+1 →
          ((SimpleGraph.fromRel (fun x y : Lattice =>
            |x.1-y.1| ≤ 2 ∧ |x.2-y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected →
          let v : Lattice → Lattice := fun b =>
            let j : ℤ := ⌊(b.2:ℝ)*s+a*((b.1*m:ℤ):ℝ)⌋
            (j,b.1*m-j)
          let Z : Lattice → ℝ := fun b =>
            ∑ z ∈ Q.map ⟨fun w => v b+w, fun _ _ h => add_left_cancel h⟩,
              max (ω z-M) 0
          (∑ b ∈ A.filter (fun b => b.1 % 4 = (α.val:ℤ) ∧
            b.2 % 10 = (β.val:ℤ)), Z b) / (N:ℝ) <
              2*C*(∫⁻ t in Ioi (0 : ℝ), (environmentLaw μ)
                {ω : Environment | t < ∑ z ∈ Q, max (ω z-M) 0}^(1/2 : ℝ)).toReal + ε := by
  obtain ⟨C,hC,hroot⟩ := exists_rooted_animal_eventually_bound
  refine ⟨C,hC,?_⟩
  intro μ _ a s M m Q hQ hs hm htail α β
  classical
  let ν : Measure ℝ := (environmentLaw μ).map
    (fun ω : Environment => ∑ z ∈ Q, max (ω z-M) 0)
  let v : Lattice → Lattice := fun b =>
    let j : ℤ := ⌊(b.2:ℝ)*s+a*((b.1*m:ℤ):ℝ)⌋
    (j,b.1*m-j)
  let Z : Environment → Lattice → ℝ := fun ω b =>
    ∑ z ∈ Q.map ⟨fun w => v b+w, fun _ _ h => add_left_cancel h⟩,
      max (ω z-M) 0
  let X : Environment → Environment := fun ω u =>
    Z ω (4*u.1+(α.val:ℤ),10*u.2+(β.val:ℤ))
  obtain ⟨hν,hXmeas,hXlaw⟩ := excess_residue_field_map μ a s M m Q hQ hs hm α β
  let : IsProbabilityMeasure ν := hν
  have hνnonneg : ∀ᵐ x ∂ν, 0 ≤ x := by
    apply (ae_map_iff (measurable_excess_box_sum Q M).aemeasurable (by measurability)).2
    exact Eventually.of_forall fun ω => Finset.sum_nonneg fun z _ => le_max_right _ _
  have htailEq (t : ℝ) : ν (Ioi t) = (environmentLaw μ)
      {ω : Environment | t < ∑ z ∈ Q, max (ω z-M) 0} := by
    rw [show ν = (environmentLaw μ).map
      (fun ω : Environment => ∑ z ∈ Q, max (ω z-M) 0) from rfl,
      Measure.map_apply (measurable_excess_box_sum Q M) measurableSet_Ioi]
    rfl
  have hνtail : (∫⁻ t in Ioi (0 : ℝ), (ν (Ioi t))^(1/2 : ℝ)) < ∞ := by
    simpa only [htailEq] using htail
  have hpres : MeasurePreserving X (environmentLaw μ) (environmentLaw ν) :=
    ⟨hXmeas,hXlaw⟩
  have hback := hpres.quasiMeasurePreserving.ae
    (hroot ν hνnonneg hνtail
      ((0-(α.val:ℤ))/4,(0-(β.val:ℤ))/10))
  filter_upwards [hback] with ω hω
  intro ε hε
  filter_upwards [hω ε hε] with N hN
  intro A hzero hcard hA
  obtain ⟨B,_hsub,ho,hB,hsize,_hsharp,hcover⟩ :=
    exists_excess_sum_animal_cover A N hzero hcard hA α β
  have hfinite := hcover ω Q a s M m
  have hbound := hN B hB ho hsize
  have hNreal : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hresult := (div_le_div_of_nonneg_right hfinite hNreal).trans_lt hbound
  simpa only [htailEq] using hresult

end LPPDifferentiability
