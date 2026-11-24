/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Model.LastPassage.Basic
public import LPP_Foundations.Probability.DisjointSupportEvents
public import Mathlib.Data.Nat.Dist
import all Differentiability.Probability.BlackBlockIndependence
import LPP_Foundations.Probability.PassageMeasurable
import LPP_Foundations.Model.Paths.Geometry
import Mathlib.Tactic

/-! # Blocks defined by passage times of the original weights -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LPPDifferentiability.FinalDraft

/-- The southwest corner of a block at scale `N`. -/
def passageBlockCorner (N : ℕ) (z : Lattice) : Lattice :=
  ((N : ℤ) * z.1, (N : ℤ) * z.2)

/-- The displacement at level `N` with first coordinate `i`. -/
def passageBlockDisplacement (N : ℕ) (i : Fin (N + 1)) : ℕ × ℕ :=
  (i, N - i.val)

/-- The starting sites are the `N + 1` sites at level `N` from the corner. -/
def passageBlockStart (N : ℕ) (z : Lattice) (i : Fin (N + 1)) : Lattice :=
  passageBlockCorner N z + ((i.val : ℤ), (N : ℤ) - (i.val : ℤ))

/-- Every sufficiently eastward passage through the second half of a black block loses
at least `δ` from its largest possible weight. -/
def IsBlackPassageBlock (ω : Environment) (N : ℕ) (c δ : ℝ) (z : Lattice) : Prop :=
  ∀ i j : Fin (N + 1), c * N ≤ (j.val : ℝ) →
    lastPassage ω (passageBlockStart N z i) (passageBlockDisplacement N j) ≤ (N : ℝ) - δ

/-- The displacements used in a block crossing have the stated total length. -/
theorem passageBlockDisplacement_level (N : ℕ) (j : Fin (N + 1)) :
    (passageBlockDisplacement N j).1 + (passageBlockDisplacement N j).2 = N := by
  have hj := j.isLt
  unfold passageBlockDisplacement
  omega

/-- Agreement on every collected vertex gives equality of passage times. -/
theorem lastPassage_eq_of_agree_on_collected (ω η : Environment) (u : Lattice) (d : ℕ × ℕ)
    (h : ∀ p : Path u d, ∀ i : Fin (d.1 + d.2),
      ω (p.vertex i.castSucc) = η (p.vertex i.castSucc)) :
    lastPassage ω u d = lastPassage η u d := by
  have hpath (p : Path u d) : pathWeight ω p = pathWeight η p := by
    unfold pathWeight
    exact Finset.sum_congr rfl fun i _ => h p i
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω u d
  obtain ⟨q, hq⟩ := exists_pathWeight_eq_lastPassage η u d
  apply le_antisymm
  · rw [← hp, hpath p]
    exact pathWeight_le_lastPassage η p
  · rw [← hq, ← hpath q]
    exact pathWeight_le_lastPassage ω q

/-- A passage block depends only on weights within this finite square. -/
private def passageBlockSites (N : ℕ) (z : Lattice) : Finset Lattice :=
  Finset.Icc (passageBlockCorner N z) (passageBlockCorner N z + ((2 * (N : ℤ)), 2 * (N : ℤ)))

private theorem isBlackPassageBlock_iff_of_agree (N : ℕ) (c δ : ℝ) (z : Lattice)
    (ω η : Environment) (h : ∀ v ∈ passageBlockSites N z, ω v = η v) :
    IsBlackPassageBlock ω N c δ z ↔ IsBlackPassageBlock η N c δ z := by
  have heq (i j : Fin (N + 1)) :
      lastPassage ω (passageBlockStart N z i) (passageBlockDisplacement N j) =
        lastPassage η (passageBlockStart N z i) (passageBlockDisplacement N j) := by
    apply lastPassage_eq_of_agree_on_collected
    intro p k
    apply h
    apply Finset.mem_Icc.mpr
    obtain ⟨hl, hr⟩ := p.vertex_mem_Icc k.castSucc
    have hNi := i.isLt
    have hNj := j.isLt
    have hcast : (((N - j.val : ℕ) : ℤ)) = (N : ℤ) - j.val := by omega
    simp only [passageBlockCorner, passageBlockStart,
      passageBlockDisplacement, Prod.le_def, Prod.fst_add, Prod.snd_add] at hl hr ⊢
    omega
  unfold IsBlackPassageBlock
  simp only [heq]

/-- The event that one block is black is measurable for the original product weights. -/
theorem measurableSet_isBlackPassageBlock (N : ℕ) (c δ : ℝ) (z : Lattice) :
    MeasurableSet {ω : Environment | IsBlackPassageBlock ω N c δ z} := by
  have heq : {ω : Environment | IsBlackPassageBlock ω N c δ z} =
      ⋂ (i : Fin (N + 1)) (j : Fin (N + 1)) (_ : c * N ≤ (j.val : ℝ)),
        {ω : Environment | lastPassage ω (passageBlockStart N z i)
          (passageBlockDisplacement N j) ≤ (N : ℝ) - δ} := by
    ext ω
    simp only [mem_ofPred_eq, IsBlackPassageBlock, mem_iInter]
  rw [heq]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => measurableSet_le (measurable_lastPassage _ _) measurable_const

/-- Blocks separated by more than two coarse lattice units in some coordinate have
independent black events under the original law. -/
theorem iIndepSet_isBlackPassageBlock (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (N : ℕ) (hN : 0 < N) (c δ : ℝ) (T : Finset (ℕ × ℕ))
    (hT : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → 2 < Nat.dist u.1 v.1 ∨ 2 < Nat.dist u.2 v.2) :
    iIndepSet (fun v : {u : ℕ × ℕ // u ∈ T} =>
      {ω : Environment | IsBlackPassageBlock ω N c δ ((v.1.1 : ℤ), (v.1.2 : ℤ))})
      (environmentLaw ν) := by
  refine iIndepSet_environment_of_disjoint_supports ν _
    (fun v : {u : ℕ × ℕ // u ∈ T} => passageBlockSites N ((v.1.1 : ℤ), (v.1.2 : ℤ)))
    (fun v => measurableSet_isBlackPassageBlock N c δ _)
    (fun v ω η h => isBlackPassageBlock_iff_of_agree N c δ _ ω η h) ?_
  intro v w hvw
  have hd := hT v.1 v.2 w.1 w.2 (fun h => hvw (Subtype.ext h))
  rw [Finset.disjoint_left]
  intro x hx hw
  simp only [passageBlockSites, Finset.mem_Icc, passageBlockCorner, Prod.le_def,
    Prod.fst_add, Prod.snd_add] at hx hw
  have hd' : ((v.1.1 : ℤ) + 3 ≤ (w.1.1 : ℤ) ∨ (w.1.1 : ℤ) + 3 ≤ (v.1.1 : ℤ)) ∨
      ((v.1.2 : ℤ) + 3 ≤ (w.1.2 : ℤ) ∨ (w.1.2 : ℤ) + 3 ≤ (v.1.2 : ℤ)) := by
    unfold Nat.dist at hd
    omega
  rcases hd' with (hd | hd) | (hd | hd)
  · exact coord_disjoint N hN hd (x := x.1) (by omega) (by omega)
  · exact coord_disjoint N hN hd (x := x.1) (by omega) (by omega)
  · exact coord_disjoint N hN hd (x := x.2) (by omega) (by omega)
  · exact coord_disjoint N hN hd (x := x.2) (by omega) (by omega)

end LPPDifferentiability.FinalDraft
