/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.RootedCoordinateBarrier
public import Busemann.Geometry.GeodesicMeasurability
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Lean.Elab.Tactic.Omega

/-! Lower geodesic cuts generate the Borel sets on a rooted geodesic fibre. -/

@[expose] public section
open MeasureTheory LPPDifferentiability
namespace LPP.Busemann

/-- On the existing rooted geodesic fibre, lower cuts by genuine geodesics
generate every path Borel set. Strong Existence, public source Lemma gen,
lines 1509–1519. -/
theorem geodesic_lower_cuts_generate_borel (ω : Environment) (u : Lattice) :
    (inferInstance : MeasurableSpace
      {γ : ℕ → Lattice // IsLocallyRightmostGeodesic ω u γ}) =
    MeasurableSpace.generateFrom
      {S : Set {γ : ℕ → Lattice // IsLocallyRightmostGeodesic ω u γ} |
        ∃ ρ : ℕ → Lattice,
          IsLocallyRightmostGeodesic ω u ρ ∧
          S = {γ | pathSoutheastLE γ.val ρ}} := by
  classical
  let G : Set (ℕ → Lattice) := {γ | IsLocallyRightmostGeodesic ω u γ}
  let C : Set (Set G) :=
    {S | ∃ ρ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u ρ ∧
      S = {γ | pathSoutheastLE γ.val ρ}}
  have hCoeOriginal : Measurable (fun γ : G => γ.val) := measurable_subtype_coe
  let m : MeasurableSpace G := MeasurableSpace.generateFrom C
  suffices h : (Subtype.instMeasurableSpace : MeasurableSpace G) = m by
    exact h
  have hCut (ρ : ℕ → Lattice) (hρ : IsLocallyRightmostGeodesic ω u ρ) :
      MeasurableSet[m] {γ : G | pathSoutheastLE γ.val ρ} := by
    apply MeasurableSpace.measurableSet_generateFrom
    exact ⟨ρ, hρ, rfl⟩
  have hBounds (γ : ℕ → Lattice) (hγ : IsLocallyRightmostGeodesic ω u γ) :
      ∀ n : ℕ, u.1 ≤ (γ n).1 ∧ (γ n).1 ≤ u.1 + (n : ℤ) := by
    intro n
    induction n with
    | zero => simp [hγ.1]
    | succ n ih =>
        rcases hγ.2.1 n with heast | hnorth
        · rw [heast]
          simp only [Prod.fst_add, Nat.cast_succ]
          omega
        · rw [hnorth]
          simp only [Prod.fst_add, Nat.cast_succ]
          omega
  have hFirst (n : ℕ) : Measurable[m] (fun γ : G => (γ.val n).1) := by
    apply measurable_of_Iic
    intro z
    by_cases hlo : z < u.1
    · have hEmpty : (fun γ : G => (γ.val n).1) ⁻¹' Set.Iic z = ∅ := by
        ext γ
        have hb := (hBounds γ.val γ.property n).1
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
        omega
      rw [hEmpty]
      exact MeasurableSet.empty
    by_cases hhi : u.1 + (n : ℤ) ≤ z
    · have hUniv : (fun γ : G => (γ.val n).1) ⁻¹' Set.Iic z = Set.univ := by
        ext γ
        have hb := (hBounds γ.val γ.property n).2
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
        omega
      rw [hUniv]
      exact MeasurableSet.univ
    let k : ℕ := (z - u.1).toNat
    have hk : k ≤ n := by dsimp [k]; omega
    have hkEq : u.1 + (k : ℤ) = z := by dsimp [k]; omega
    obtain ⟨β, _hβroot, _hβstep, hgreat⟩ :=
      exists_rooted_coordinate_barrier_greatest_cut u n k hk
    obtain ⟨ρ, hρ, _hρβ, hρcut⟩ := hgreat ω
    have hSet : (fun γ : G => (γ.val n).1) ⁻¹' Set.Iic z =
        {γ : G | pathSoutheastLE γ.val ρ} := by
      ext γ
      change (γ.val n).1 ≤ z ↔ pathSoutheastLE γ.val ρ
      rw [← hkEq]
      exact hρcut γ.val γ.property
    rw [hSet]
    exact hCut ρ hρ
  have hSecond (n : ℕ) : Measurable[m] (fun γ : G => (γ.val n).2) := by
    have hSubtract : Measurable[m]
        (fun γ : G => u.1 + u.2 + (n : ℤ) - (γ.val n).1) :=
      measurable_const.sub (hFirst n)
    convert hSubtract using 1
    funext γ
    have hLevel : ∀ t : ℕ,
        (γ.val t).1 + (γ.val t).2 = u.1 + u.2 + (t : ℤ) := by
      intro t
      induction t with
      | zero => simp [γ.property.1]
      | succ t ih =>
          rcases γ.property.2.1 t with heast | hnorth
          · rw [heast]
            simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ]
            omega
          · rw [hnorth]
            simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ]
            omega
    have hLevel := hLevel n
    omega
  have hVal : Measurable[m] (fun γ : G => γ.val) := by
    apply measurable_pi_iff.mpr
    intro n
    exact (hFirst n).prodMk (hSecond n)
  have hOriginalLE : (Subtype.instMeasurableSpace : MeasurableSpace G) ≤ m := by
    exact hVal.comap_le
  have hGenerateLE : m ≤ (Subtype.instMeasurableSpace : MeasurableSpace G) := by
    apply MeasurableSpace.generateFrom_le
    intro S hS
    obtain ⟨ρ, _hρ, rfl⟩ := hS
    have hPath : MeasurableSet {γ : ℕ → Lattice | pathSoutheastLE γ ρ} := by
      have hRelation := measurableSet_pathSoutheastLE
      exact hRelation.preimage (measurable_id.prodMk measurable_const)
    exact hPath.preimage hCoeOriginal
  exact le_antisymm hOriginalLE hGenerateLE

end LPP.Busemann
