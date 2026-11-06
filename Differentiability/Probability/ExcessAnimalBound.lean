/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.ExcessAnimalClassBound
public import Differentiability.Probability.ExcessTailScaling
public import Differentiability.Model.Animals.RadiusTwoFamily
import Mathlib.Tactic

/-!
# Uniform excess bound over radius-two animals

This file proves one constant that bounds the excess sum over every admissible finite
radius-two animal, on the environment probability space. The bound is built from
the residue-class estimates and the integrated square-root tail bound of the excess
sum.
-/

public section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal
namespace LPPDifferentiability

/-- The forty residue classes partition every finite weighted sum,
including signed indices and signed weights. -/
theorem sum_excess_residue_classes (A : Finset Lattice) (Z : Lattice → ℝ) :
    (∑ r : Fin 4 × Fin 10, ∑ b ∈ A.filter (fun b =>
      b.1 % 4 = (r.1.val:ℤ) ∧ b.2 % 10 = (r.2.val:ℤ)), Z b) = ∑ b ∈ A, Z b := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  obtain ⟨r,hr,huniq⟩ := excess_residue_partition b
  rw [Finset.sum_eq_single r]
  · simp only [hr, and_self, ite_true]
  · intro t _ htr
    have hfalse : ¬(b.1 % 4 = (t.1.val:ℤ) ∧ b.2 % 10 = (t.2.val:ℤ)) := by
      intro ht
      exact htr (huniq t ht)
    simp only [hfalse, ite_false]
  · intro hrnot
    exact False.elim (hrnot (Finset.mem_univ r))

/-- One constant, depending only on the marginal of the environment and on the parameters
`p` and `eta`, bounds the supremum over all admissible finite animals. The same finite box
`Q` also satisfies its two cardinality bounds. -/
theorem exists_excess_animal_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p eta : ℝ}
    (hp : 4 < p) (heta : 0 < eta)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max x 0)^p) ∂μ) < ∞) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ (a s : ℝ), 3 ≤ s → ∀ m : ℕ,
      1 ≤ m → (m:ℝ) ≤ s^3 → ∃ Q : Finset Lattice,
      (∀ z, z ∈ Q ↔ 0 ≤ z.1+z.2 ∧ z.1+z.2 ≤ 3*(m:ℤ) ∧
        |(1-a)*(z.1:ℝ)-a*(z.2:ℝ)| ≤ 4*s+1) ∧
      (Q.card:ℝ) ≤ (3*(m:ℝ)+1)*(8*s+3) ∧
      (3*(m:ℝ)+1)*(8*s+3) ≤ 44*s^4 ∧
      ∀ᵐ ω ∂environmentLaw μ,
        let v : Lattice → Lattice := fun b =>
          let j : ℤ := ⌊(b.2:ℝ)*s+a*((b.1*m:ℤ):ℝ)⌋
          (j,b.1*m-j)
        let Z : Lattice → ℝ := fun b =>
          ∑ z ∈ Q.map ⟨fun w => v b+w, fun _ _ h => add_left_cancel h⟩,
            max (ω z-eta*s/4) 0
        (limsup (fun N : ℕ =>
          ⨆ A : {A : Finset Lattice // (0 : Lattice) ∈ A ∧ A.card ≤ N+1 ∧
            ((SimpleGraph.fromRel (fun x y : Lattice =>
              |x.1-y.1| ≤ 2 ∧ |x.2-y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected},
            (((∑ b ∈ A.val, Z b) / (N:ℝ) : ℝ) : EReal)) atTop ≤
              ((C0*s^(2-p/4) : ℝ) : EReal)) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
          ∀ A : Finset Lattice, (0 : Lattice) ∈ A → A.card ≤ N+1 →
            ((SimpleGraph.fromRel (fun x y : Lattice =>
              |x.1-y.1| ≤ 2 ∧ |x.2-y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected →
            (∑ b ∈ A, Z b) / (N:ℝ) < C0*s^(2-p/4)+ε := by
  classical
  obtain ⟨C,hC,hclass⟩ := exists_excess_class_eventually_bound
  obtain ⟨K,hK,htail⟩ := exists_excess_sum_integrated_sqrt_tail_bound μ hp heta hmoment
  refine ⟨80*C*K, by positivity, ?_⟩
  intro a s hs m hm hms
  obtain ⟨Q,hQ,hcard,hcardbound⟩ := exists_excess_block_base a s m hs hms
  refine ⟨Q,hQ,hcard,hcardbound,?_⟩
  let M : ℝ := eta*s/4
  let T : ℝ≥0∞ := ∫⁻ t in Ioi (0 : ℝ), (environmentLaw μ)
    {ω : Environment | t < ∑ z ∈ Q, max (ω z-M) 0}^(1/2 : ℝ)
  have htailbound : T ≤ ENNReal.ofReal (K*s^(2-p/4)) :=
    htail s hs Q (hcard.trans hcardbound)
  have hfinite : T < ∞ := htailbound.trans_lt ENNReal.ofReal_lt_top
  have hscale : 0 ≤ K*s^(2-p/4) := by positivity
  have htailreal : T.toReal ≤ K*s^(2-p/4) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top htailbound
    simpa only [ENNReal.toReal_ofReal hscale] using h
  have hall : ∀ r : Fin 4 × Fin 10, ∀ᵐ ω ∂environmentLaw μ,
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
          (∑ b ∈ A.filter (fun b => b.1 % 4 = (r.1.val:ℤ) ∧
            b.2 % 10 = (r.2.val:ℤ)), Z b) / (N:ℝ) < 2*C*T.toReal+ε :=
    fun r => hclass μ a s M m Q hQ hs hm hfinite r.1 r.2
  filter_upwards [ae_all_iff.mpr hall] with ω hω
  dsimp only
  let v : Lattice → Lattice := fun b =>
    let j : ℤ := ⌊(b.2:ℝ)*s+a*((b.1*m:ℤ):ℝ)⌋
    (j,b.1*m-j)
  let Z : Lattice → ℝ := fun b =>
    ∑ z ∈ Q.map ⟨fun w => v b+w, fun _ _ h => add_left_cancel h⟩,
      max (ω z-M) 0
  have huniform : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ A : Finset Lattice, (0 : Lattice) ∈ A → A.card ≤ N+1 →
        ((SimpleGraph.fromRel (fun x y : Lattice =>
          |x.1-y.1| ≤ 2 ∧ |x.2-y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected →
        (∑ b ∈ A, Z b) / (N:ℝ) < (80*C*K)*s^(2-p/4)+ε := by
    intro ε hε
    have hεsmall : (0 : ℝ) < ε/80 := by positivity
    have hfiniteClasses : ∀ᶠ N : ℕ in atTop, ∀ r : Fin 4 × Fin 10,
        ∀ A : Finset Lattice, (0 : Lattice) ∈ A → A.card ≤ N+1 →
          ((SimpleGraph.fromRel (fun x y : Lattice =>
            |x.1-y.1| ≤ 2 ∧ |x.2-y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected →
          (∑ b ∈ A.filter (fun b => b.1 % 4 = (r.1.val:ℤ) ∧
            b.2 % 10 = (r.2.val:ℤ)), Z b) / (N:ℝ) < 2*C*T.toReal+ε/80 := by
      apply eventually_all.mpr
      intro r
      exact hω r (ε/80) hεsmall
    filter_upwards [hfiniteClasses] with N hN
    intro A hzero hsize hconn
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4 × Fin 10)))
      (fun r _ => (hN r A hzero hsize hconn).le)
    have hpartition : (∑ r : Fin 4 × Fin 10,
        (∑ b ∈ A.filter (fun b => b.1 % 4 = (r.1.val:ℤ) ∧
          b.2 % 10 = (r.2.val:ℤ)), Z b) / (N:ℝ)) = (∑ b ∈ A, Z b) / (N:ℝ) := by
      rw [← Finset.sum_div, sum_excess_residue_classes]
    rw [hpartition] at hsum
    have hcount : (∑ _r : Fin 4 × Fin 10, (2*C*T.toReal+ε/80)) =
        80*C*T.toReal+ε/2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Nat.reduceMul, nsmul_eq_mul]
      ring
    rw [hcount] at hsum
    have hscaled : 80*C*T.toReal ≤ (80*C*K)*s^(2-p/4) := by
      calc
        _ ≤ 80*C*(K*s^(2-p/4)) :=
          mul_le_mul_of_nonneg_left htailreal (by positivity)
        _ = _ := by ring
    linarith only [hsum,hscaled,hε]
  exact ⟨(limsup_iSup_radiusTwoAnimal_le_iff Z _).mpr huniform,huniform⟩

end LPPDifferentiability
