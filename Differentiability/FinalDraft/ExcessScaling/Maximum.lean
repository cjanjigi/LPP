/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.Probability.ExcessAnimalBound
public import LPP_Foundations.Model.Animals.BoxCardinality
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic

/-! The finite, attained maximum in the final draft's excess-animal estimate. -/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace LPPDifferentiability

private abbrev radiusTwoGraph : SimpleGraph Lattice :=
  SimpleGraph.fromRel (fun x y : Lattice => |x.1 - y.1| ≤ 2 ∧ |x.2 - y.2| ≤ 2)

/-- The rooted animals in Lemma `lem:excess` of `differentiability_final_draft.tex`. The
parameter is the cardinality cap, so at source stage count `N` it is `N + 1`. -/
def rootedRadiusTwoAnimals (cap : ℕ) : Set (Finset Lattice) :=
  {A | (0 : Lattice) ∈ A ∧ A.card ≤ cap ∧
    ((SimpleGraph.fromRel (fun x y : Lattice =>
      |x.1 - y.1| ≤ 2 ∧ |x.2 - y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected}

private theorem radiusTwoGraph_adj_bounds {x y : Lattice} (h : radiusTwoGraph.Adj x y) :
    |y.1 - x.1| ≤ 2 ∧ |y.2 - x.2| ≤ 2 := by
  change x ≠ y ∧
    ((|x.1 - y.1| ≤ 2 ∧ |x.2 - y.2| ≤ 2) ∨ (|y.1 - x.1| ≤ 2 ∧ |y.2 - x.2| ≤ 2)) at h
  rcases h.2 with hxy | hyx
  · simpa only [abs_sub_comm y.1 x.1, abs_sub_comm y.2 x.2] using hxy
  · exact hyx

private theorem radiusTwoGraph_walk_bounds {x y : Lattice} (p : radiusTwoGraph.Walk x y) :
    |y.1 - x.1| ≤ 2 * (p.length : ℤ) ∧ |y.2 - x.2| ≤ 2 * (p.length : ℤ) := by
  induction p with
  | nil => simp
  | @cons x z y hxz p ih =>
    obtain ⟨h₁, h₂⟩ := radiusTwoGraph_adj_bounds hxz
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    exact ⟨(abs_sub_le y.1 z.1 x.1).trans (by omega), (abs_sub_le y.2 z.2 x.2).trans (by omega)⟩

/-- Each animal in Lemma `lem:excess` lies in the closed box about its root of
radius twice the cardinality cap minus two. -/
theorem radiusTwoAnimal_subset_integerBox {cap : ℕ} {A : Finset Lattice}
    (hA : A ∈ rootedRadiusTwoAnimals cap) : A ⊆ integerBox 0 (2 * (cap - 1)) := by
  classical
  obtain ⟨hzero, hcard, hconn⟩ := hA
  intro z hz
  -- A simple path in the induced graph visits at most the available vertices.
  obtain ⟨p, hp⟩ := hconn.exists_isPath (⟨0, hzero⟩ : A) (⟨z, hz⟩ : A)
  have hlen := hp.length_lt
  change p.length < Fintype.card A at hlen
  rw [Fintype.card_coe] at hlen
  have hcap : p.length ≤ cap - 1 := by omega
  -- Each edge changes either coordinate by at most two.
  let f : radiusTwoGraph.induce (↑A : Set Lattice) →g radiusTwoGraph :=
    ⟨Subtype.val, fun h => h⟩
  have hcoords := radiusTwoGraph_walk_bounds (p.map f)
  simp only [SimpleGraph.Walk.length_map] at hcoords
  have hradius : 2 * (p.length : ℤ) ≤ ((2 * (cap - 1) : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_le_mul_left 2 hcap
  exact (mem_integerBox_iff 0 z _).mpr ⟨hcoords.1.trans hradius, hcoords.2.trans hradius⟩

/-- The family of rooted animals in Lemma `lem:excess` is finite for every cardinality cap. -/
theorem rootedRadiusTwoAnimals_finite (cap : ℕ) : (rootedRadiusTwoAnimals cap).Finite := by
  classical
  apply (Finset.finite_toSet (integerBox 0 (2 * (cap - 1))).powerset).subset
  intro A hA
  exact Finset.mem_powerset.mpr (radiusTwoAnimal_subset_integerBox hA)

/-- The origin requirement in Lemma `lem:excess` leaves no animal when the cap is zero. -/
theorem rootedRadiusTwoAnimals_zero : rootedRadiusTwoAnimals 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro A hA
  obtain ⟨hzero, hcard, -⟩ := hA
  have hAempty := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
  exact Finset.notMem_empty _ (hAempty ▸ hzero)

/-- The singleton root is an admissible animal in Lemma `lem:excess` at every positive cap. -/
theorem singleton_mem_rootedRadiusTwoAnimals {cap : ℕ} (hcap : 1 ≤ cap) :
    ({(0 : Lattice)} : Finset Lattice) ∈ rootedRadiusTwoAnimals cap := by
  have hzero : (0 : Lattice) ∈ ({0} : Finset Lattice) := Finset.mem_singleton_self _
  refine ⟨hzero, by simpa only [Finset.card_singleton] using hcap, ?_⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  refine ⟨⟨0, hzero⟩, fun y => ?_⟩
  have hy : y = ⟨0, hzero⟩ := Subtype.ext (Finset.mem_singleton.mp y.property)
  subst y
  exact .rfl

/-- The rooted-animal family in Appendix B, Lemma `lem:excess`, is nonempty for every positive cardinality cap. -/
theorem rootedRadiusTwoAnimals_nonempty {cap : ℕ} (hcap : 1 ≤ cap) :
    (rootedRadiusTwoAnimals cap).Nonempty :=
  ⟨{0}, singleton_mem_rootedRadiusTwoAnimals hcap⟩

/-- The actual maximum of the weight sum in Lemma `lem:excess`, with
cardinality cap `N + 1` at stage count `N`. -/
noncomputable def rootedRadiusTwoAnimalMaximum (Z : Lattice → ℝ) (N : ℕ) : ℝ :=
  sSup ((fun A : Finset Lattice => ∑ b ∈ A, Z b) '' rootedRadiusTwoAnimals (N + 1))

/-- An admissible animal actually attains the real maximum in Lemma `lem:excess`.
The same value bounds every admissible animal with that cap. -/
theorem rootedRadiusTwoAnimalMaximum_attained (Z : Lattice → ℝ) (N : ℕ) :
    ∃ A ∈ rootedRadiusTwoAnimals (N + 1),
      (∑ b ∈ A, Z b) = rootedRadiusTwoAnimalMaximum Z N ∧
      ∀ A' ∈ rootedRadiusTwoAnimals (N + 1), (∑ b ∈ A', Z b) ≤ rootedRadiusTwoAnimalMaximum Z N := by
  let weight := fun A : Finset Lattice => ∑ b ∈ A, Z b
  have hfinite := (rootedRadiusTwoAnimals_finite (N + 1)).image weight
  have hnonempty := (rootedRadiusTwoAnimals_nonempty (Nat.succ_pos N)).image weight
  have hmax := hnonempty.isGreatest_csSup hfinite
  obtain ⟨A, hA, hAmax⟩ := hmax.1
  exact ⟨A, hA, hAmax, fun A' hA' => hmax.2 ⟨A', hA', rfl⟩⟩

/-- The extended-real supremum used for the excess bound is the normalized,
attained real maximum on the same family from Lemma `lem:excess`. -/
theorem iSup_radiusTwoAnimal_eq_maximum (Z : Lattice → ℝ) (N : ℕ) :
    (⨆ A : {A : Finset Lattice // (0 : Lattice) ∈ A ∧ A.card ≤ N + 1 ∧
      ((SimpleGraph.fromRel (fun x y : Lattice =>
        |x.1 - y.1| ≤ 2 ∧ |x.2 - y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected},
      (((∑ b ∈ A.val, Z b) / (N : ℝ) : ℝ) : EReal)) =
    ((rootedRadiusTwoAnimalMaximum Z N / (N : ℝ) : ℝ) : EReal) := by
  obtain ⟨A, hA, hval, hupper⟩ := rootedRadiusTwoAnimalMaximum_attained Z N
  apply le_antisymm
  · apply iSup_le
    intro A'
    exact EReal.coe_le_coe_iff.mpr
      (div_le_div_of_nonneg_right (hupper A'.val A'.property) (Nat.cast_nonneg N))
  · rw [← hval]
    exact le_iSup (fun B : {B : Finset Lattice // B ∈ rootedRadiusTwoAnimals (N + 1)} =>
      (((∑ b ∈ B.val, Z b) / (N : ℝ) : ℝ) : EReal)) ⟨A, hA⟩

/-- The normalized maximum in Lemma `lem:excess` has the same extended-real limsup
bound as the uniform estimates over every admissible animal. -/
theorem limsup_radiusTwoAnimalMaximum_le_iff (Z : Lattice → ℝ) (C : ℝ) :
    (limsup (fun N : ℕ => ((rootedRadiusTwoAnimalMaximum Z N / (N : ℝ) : ℝ) : EReal))
      atTop ≤ (C : EReal)) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ A ∈ rootedRadiusTwoAnimals (N + 1), (∑ b ∈ A, Z b) / (N : ℝ) < C + ε := by
  rw [show (fun N : ℕ => ((rootedRadiusTwoAnimalMaximum Z N / (N : ℝ) : ℝ) : EReal)) =
      (fun N : ℕ => ⨆ A : {A : Finset Lattice // A ∈ rootedRadiusTwoAnimals (N + 1)},
        (((∑ b ∈ A.val, Z b) / (N : ℝ) : ℝ) : EReal))
      from funext fun N => (iSup_radiusTwoAnimal_eq_maximum Z N).symm]
  constructor
  · intro h ε hε
    have huniform := (limsup_iSup_radiusTwoAnimal_le_iff Z C).mp h
    filter_upwards [huniform ε hε] with N hN A hA
    exact hN A hA.1 hA.2.1 hA.2.2
  · intro h
    refine (limsup_iSup_radiusTwoAnimal_le_iff Z C).mpr ?_
    intro ε hε
    filter_upwards [h ε hε] with N hN A hzero hcard hconn
    exact hN A ⟨hzero, hcard, hconn⟩

private theorem limsup_radiusTwoAnimalMaximum_le {Z : Lattice → ℝ} {C : ℝ}
    (hZ : ∀ b, 0 ≤ Z b)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ A ∈ rootedRadiusTwoAnimals (N + 1), (∑ b ∈ A, Z b) / (N : ℝ) < C + ε) :
    limsup (fun N : ℕ => rootedRadiusTwoAnimalMaximum Z N / (N : ℝ)) atTop ≤ C := by
  have hnonneg (N : ℕ) : 0 ≤ rootedRadiusTwoAnimalMaximum Z N / (N : ℝ) := by
    obtain ⟨A, _, hval, -⟩ := rootedRadiusTwoAnimalMaximum_attained Z N
    rw [← hval]
    exact div_nonneg (Finset.sum_nonneg fun b _ => hZ b) (Nat.cast_nonneg N)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  apply limsup_le_of_le (isCoboundedUnder_le_of_le atTop hnonneg)
  filter_upwards [h ε hε] with N hN
  obtain ⟨A, hA, hval, -⟩ := rootedRadiusTwoAnimalMaximum_attained Z N
  rw [← hval]
  exact (hN A hA).le

/-- The excess bound of Lemma `lem:excess` with the attained real maximum and
a real limsup. The proof keeps the same constant, block, weights and
environment as the uniform bound. -/
theorem exists_excess_animal_maximum_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p η : ℝ}
    (hp : 4 < p) (hη : 0 < η)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (a s : ℝ), 3 ≤ s → ∀ m : ℕ,
      1 ≤ m → (m : ℝ) ≤ s ^ 3 → ∃ Q : Finset Lattice,
      (∀ z, z ∈ Q ↔ 0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ 3 * (m : ℤ) ∧
        |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ 4 * s + 1) ∧
      (Q.card : ℝ) ≤ (3 * (m : ℝ) + 1) * (8 * s + 3) ∧
      (3 * (m : ℝ) + 1) * (8 * s + 3) ≤ 44 * s ^ 4 ∧
      ∀ᵐ ω ∂environmentLaw μ,
        let v : Lattice → Lattice := fun b =>
          let j : ℤ := ⌊(b.2 : ℝ) * s + a * ((b.1 * m : ℤ) : ℝ)⌋
          (j, b.1 * m - j)
        let Z : Lattice → ℝ := fun b =>
          ∑ z ∈ Q.map ⟨fun w => v b + w, fun _ _ h => add_left_cancel h⟩,
            max (ω z - η * s / 4) 0
        limsup (fun N : ℕ => rootedRadiusTwoAnimalMaximum Z N / (N : ℝ)) atTop ≤
          C₀ * s ^ (2 - p / 4) := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_excess_animal_bound μ hp hη hmoment
  refine ⟨C₀, hC₀, fun a s hs m hm hms => ?_⟩
  obtain ⟨Q, hQ, hcard, hcardBound, hprob⟩ := hbound a s hs m hm hms
  refine ⟨Q, hQ, hcard, hcardBound, ?_⟩
  filter_upwards [hprob] with ω hω
  dsimp only at hω ⊢
  apply limsup_radiusTwoAnimalMaximum_le
  · intro b
    exact Finset.sum_nonneg fun z _ => le_max_right _ _
  · intro ε hε
    filter_upwards [hω.2 ε hε] with N hN A hA
    exact hN A hA.1 hA.2.1 hA.2.2

end LPPDifferentiability
