/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.ExcessBlockLaw

/-!
# Laws of the residue-class fields

This file shows that the family of excess sums, indexed by the boxes of one residue class, is
a product of copies of the law of a single box sum. The law of the whole field is therefore
determined by the law of one box.
-/

public section
open MeasureTheory ProbabilityTheory
namespace LPPDifferentiability

/-- For one residue class, the field of excess sums indexed by the translates of `Q` has the
law of the infinite product of copies of the law of the sum over `Q`. -/
theorem excess_residue_field_map (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a s M : ℝ) (m : ℕ) (Q : Finset Lattice)
    (hQ : ∀ z, z ∈ Q ↔ 0 ≤ z.1+z.2 ∧ z.1+z.2 ≤ 3*(m:ℤ) ∧
      |(1-a)*(z.1:ℝ)-a*(z.2:ℝ)| ≤ 4*s+1)
    (hs : 3 ≤ s) (hm : 1 ≤ m) (α : Fin 4) (β : Fin 10) :
    let ν := (environmentLaw μ).map
      (fun ω : Environment => ∑ z ∈ Q, max (ω z-M) 0)
    let v : Lattice → Lattice := fun d =>
      let p := 4*d.1+(α.val:ℤ)
      let h := 10*d.2+(β.val:ℤ)
      let j : ℤ := ⌊(h:ℝ)*s+a*((p*m:ℤ):ℝ)⌋
      (j,p*m-j)
    let X : Environment → Environment := fun ω d =>
      ∑ z ∈ Q.map ⟨fun w => v d+w, fun _ _ h => add_left_cancel h⟩,
        max (ω z-M) 0
    IsProbabilityMeasure ν ∧ Measurable X ∧
      (environmentLaw μ).map X = environmentLaw ν := by
  classical
  dsimp only
  let v : Lattice → Lattice := fun d =>
    let p := 4*d.1+(α.val:ℤ)
    let h := 10*d.2+(β.val:ℤ)
    let j : ℤ := ⌊(h:ℝ)*s+a*((p*m:ℤ):ℝ)⌋
    (j,p*m-j)
  let Z : Lattice → Environment → ℝ := fun d ω =>
    ∑ z ∈ Q.map ⟨fun w => v d+w, fun _ _ h => add_left_cancel h⟩,
      max (ω z-M) 0
  have hmeas (d : Lattice) : Measurable (Z d) :=
    measurable_excess_box_sum _ M
  have hmargin (d : Lattice) : (environmentLaw μ).map (Z d) =
      (environmentLaw μ).map (fun ω : Environment => ∑ z ∈ Q, max (ω z-M) 0) :=
    excess_box_sum_map_translation μ Q M (v d)
  have hind : iIndepFun Z (environmentLaw μ) :=
    iIndepFun_excess_residue_sums μ a s M m Q hQ hs hm α β
  refine ⟨inferInstance, measurable_pi_iff.mpr hmeas, ?_⟩
  change (environmentLaw μ).map (fun ω d => Z d ω) = _
  rw [hind.map_fun_eq_infinitePi_map hmeas]
  simp_rw [hmargin]
  rfl

/-- There is a finite box `Q` with the two cardinality bounds, such that for each of the forty
residue classes the field of translated box sums has the product law. -/
theorem exists_excess_residue_field_laws (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a s M : ℝ) (m : ℕ) (hs : 3 ≤ s) (hm : 1 ≤ m) (hms : (m:ℝ) ≤ s^3) :
    ∃ Q : Finset Lattice,
      (∀ z, z ∈ Q ↔ 0 ≤ z.1+z.2 ∧ z.1+z.2 ≤ 3*(m:ℤ) ∧
        |(1-a)*(z.1:ℝ)-a*(z.2:ℝ)| ≤ 4*s+1) ∧
      (Q.card:ℝ) ≤ (3*(m:ℝ)+1)*(8*s+3) ∧
      (3*(m:ℝ)+1)*(8*s+3) ≤ 44*s^4 ∧
      (∀ (α : Fin 4) (β : Fin 10),
        let ν := (environmentLaw μ).map
          (fun ω : Environment => ∑ z ∈ Q, max (ω z-M) 0)
        let v : Lattice → Lattice := fun d =>
          let p := 4*d.1+(α.val:ℤ)
          let h := 10*d.2+(β.val:ℤ)
          let j : ℤ := ⌊(h:ℝ)*s+a*((p*m:ℤ):ℝ)⌋
          (j,p*m-j)
        let X : Environment → Environment := fun ω d =>
          ∑ z ∈ Q.map ⟨fun w => v d+w, fun _ _ h => add_left_cancel h⟩,
            max (ω z-M) 0
        IsProbabilityMeasure ν ∧ Measurable X ∧
          (environmentLaw μ).map X = environmentLaw ν) := by
  obtain ⟨Q,hQ,hcard,hbound⟩ := exists_excess_block_base a s m hs hms
  refine ⟨Q,hQ,hcard,hbound,?_⟩
  intro α β
  exact excess_residue_field_map μ a s M m Q hQ hs hm α β

end LPPDifferentiability
end
