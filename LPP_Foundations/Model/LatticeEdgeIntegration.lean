/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-! Integrating a curl-free real edge field on the signed integer lattice.
This supplies the deterministic path-independence step of JR1810.03580v3,
proof of Theorem 4.8 immediately after (4.19). -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

private noncomputable def orientedSum (f : ℤ → ℝ) (a b : ℤ) : ℝ :=
  if a ≤ b then ∑ k ∈ Finset.Ico a b, f k else -(∑ k ∈ Finset.Ico b a, f k)

private theorem orientedSum_self (f : ℤ → ℝ) (a : ℤ) : orientedSum f a a = 0 := by
  simp [orientedSum]

private theorem orientedSum_succ (f : ℤ → ℝ) (a b : ℤ) :
    orientedSum f a (b + 1) = orientedSum f a b + f b := by
  classical
  by_cases hab : a ≤ b
  · have hab' : a ≤ b + 1 := by omega
    simp only [orientedSum, ite_eq_left hab, ite_eq_left hab']
    exact (Finset.sum_Ico_add_eq_sum_Ico_add_one hab f).symm
  · have hba : b < a := by omega
    have hsplit : (∑ k ∈ Finset.Ico b a, f k) =
        f b + ∑ k ∈ Finset.Ico (b + 1) a, f k := by
      rw [← Finset.insert_Ico_add_one_left_eq_Ico hba, Finset.sum_insert (by simp)]
    have hform : orientedSum f a (b + 1) = -(∑ k ∈ Finset.Ico (b + 1) a, f k) := by
      by_cases ha : a ≤ b + 1
      · have heq : a = b + 1 := by omega
        subst a
        simp [orientedSum]
      · simp only [orientedSum, ite_eq_right ha]
    rw [hform]
    simp only [orientedSum, ite_eq_right hab]
    rw [hsplit]
    ring

private theorem orientedSum_telescope_anchor (f F : ℤ → ℝ)
    (hF : ∀ k, F (k + 1) = F k + f k) (a b : ℤ) :
    orientedSum f a b = F b - F a := by
  refine Int.inductionOn' b a ?_ ?_ ?_
  · rw [orientedSum_self, sub_self]
  · intro k _ ih
    rw [orientedSum_succ, ih, hF]
    ring
  · intro k _ ih
    have hsum := orientedSum_succ f a (k - 1)
    have hstep := hF (k - 1)
    have hk : k - 1 + 1 = k := by omega
    rw [hk] at hsum hstep
    linarith

private theorem orientedSum_glue (f : ℤ → ℝ) (a b c : ℤ) :
    orientedSum f a b + orientedSum f b c = orientedSum f a c := by
  have h := orientedSum_telescope_anchor f (fun k => orientedSum f a k)
    (orientedSum_succ f a) b c
  linarith

private theorem orientedSum_telescope (f F : ℤ → ℝ)
    (hF : ∀ k, F (k + 1) = F k + f k) (a b : ℤ) :
    orientedSum f a b = F b - F a := by
  have ha := orientedSum_telescope_anchor f F hF 0 a
  have hb := orientedSum_telescope_anchor f F hF 0 b
  have hg := orientedSum_glue f 0 a b
  linarith

private theorem orientedSum_sub (f g : ℤ → ℝ) (a b : ℤ) :
    orientedSum (fun k => f k - g k) a b = orientedSum f a b - orientedSum g a b := by
  classical
  unfold orientedSum
  split_ifs
  · rw [Finset.sum_sub_distrib]
  · rw [Finset.sum_sub_distrib]
    ring

private theorem primitive_coordinate_formula (E : Lattice → Fin 2 → ℝ)
    (F : Lattice → ℝ)
    (hF0 : ∀ x, F (x + (1, 0)) = F x + E x 0)
    (hF1 : ∀ x, F (x + (0, 1)) = F x + E x 1)
    (x y : Lattice) :
    F y - F x = orientedSum (fun k => E (k, x.2) 0) x.1 y.1 +
      orientedSum (fun k => E (y.1, k) 1) x.2 y.2 := by
  have hhor := orientedSum_telescope (fun k => E (k, x.2) 0)
    (fun k => F (k, x.2)) (fun k => by
      simpa only [Prod.mk_add_mk, add_zero] using hF0 (k, x.2)) x.1 y.1
  have hver := orientedSum_telescope (fun k => E (y.1, k) 1)
    (fun k => F (y.1, k)) (fun k => by
      simpa only [Prod.mk_add_mk, add_zero] using hF1 (y.1, k)) x.2 y.2
  rw [hhor, hver]
  change F y - F x = (F (y.1, x.2) - F x) + (F y - F (y.1, x.2))
  ring

/-- A real curl-free field on all signed lattice edges has a unique additive
extension. Its values are the literal signed horizontal-then-vertical sums.
This is the deterministic path-sum extension in JR1810.03580v3, proof of
Theorem 4.8 after (4.19); no probabilistic hypothesis is needed. -/
theorem exists_unique_lattice_edge_extension (E : Lattice → Fin 2 → ℝ)
    (hcurl : ∀ x, E x 0 + E (x + (1, 0)) 1 = E x 1 + E (x + (0, 1)) 0) :
    let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
      if a ≤ b then ∑ k ∈ Finset.Ico a b, f k else -(∑ k ∈ Finset.Ico b a, f k)
    let R : Lattice → Lattice → ℝ := fun x y =>
      S (fun k => E (k, x.2) 0) x.1 y.1 + S (fun k => E (y.1, k) 1) x.2 y.2
    ∃ B : Lattice → Lattice → ℝ,
      (∀ x y z, B x y + B y z = B x z) ∧
      (∀ x, B x (x + (1, 0)) = E x 0 ∧ B x (x + (0, 1)) = E x 1) ∧
      (∀ x y, B x y = R x y) ∧
      (∀ C : Lattice → Lattice → ℝ,
        (∀ x y z, C x y + C y z = C x z) →
        (∀ x, C x (x + (1, 0)) = E x 0 ∧ C x (x + (0, 1)) = E x 1) → C = B) := by
  classical
  dsimp only
  let Φ : Lattice → ℝ := fun x =>
    orientedSum (fun k => E (k, 0) 0) 0 x.1 + orientedSum (fun k => E (x.1, k) 1) 0 x.2
  have hΦ0 (x : Lattice) : Φ (x + (1, 0)) = Φ x + E x 0 := by
    have hdiff : (fun t => E (x.1 + 1, t) 1 - E (x.1, t) 1) =
        (fun t => E (x.1, t + 1) 0 - E (x.1, t) 0) := by
      funext t
      have hc := hcurl (x.1, t)
      simp only [Prod.mk_add_mk, add_zero] at hc
      linarith
    have htel := orientedSum_telescope
      (fun t => E (x.1, t + 1) 0 - E (x.1, t) 0)
      (fun t => E (x.1, t) 0) (fun _ => by ring) 0 x.2
    rw [← hdiff, orientedSum_sub] at htel
    dsimp only [Φ, Prod.fst_add, Prod.snd_add]
    simp only [add_zero]
    rw [orientedSum_succ]
    linarith
  have hΦ1 (x : Lattice) : Φ (x + (0, 1)) = Φ x + E x 1 := by
    dsimp only [Φ, Prod.fst_add, Prod.snd_add]
    simp only [add_zero]
    rw [orientedSum_succ]
    ring
  refine ⟨fun x y => Φ y - Φ x, ?_, ?_, ?_, ?_⟩
  · intro x y z
    ring
  · intro x
    constructor
    · have h := hΦ0 x
      linarith
    · have h := hΦ1 x
      linarith
  · intro x y
    exact primitive_coordinate_formula E Φ hΦ0 hΦ1 x y
  · intro C hC hEdge
    have hC0 (x : Lattice) : C 0 (x + (1, 0)) = C 0 x + E x 0 := by
      rw [← hC 0 x (x + (1, 0)), (hEdge x).1]
    have hC1 (x : Lattice) : C 0 (x + (0, 1)) = C 0 x + E x 1 := by
      rw [← hC 0 x (x + (0, 1)), (hEdge x).2]
    funext x y
    have hcf := primitive_coordinate_formula E (fun t => C 0 t) hC0 hC1 x y
    have hpf := primitive_coordinate_formula E Φ hΦ0 hΦ1 x y
    have hadd := hC 0 x y
    linarith

end LPPDifferentiability
