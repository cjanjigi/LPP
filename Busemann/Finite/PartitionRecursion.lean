/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.PathWeight
public import LPP_Foundations.Model.Paths.Fintype
public import LPP_Foundations.Model.Paths.Nonempty
public import Mathlib.Analysis.SpecialFunctions.Exp
import LPP_Foundations.Model.Paths.FirstStep
import LPP_Foundations.Model.Paths.Translate
import LPP_Foundations.Model.Paths.Geometry
import LPP_Foundations.Model.Paths.WeightZero
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! The actual finite exponential path partition and its first-step recursion,
with the terminal-excluded convention of JR1810.03580v3, Section 2.2. -/

@[expose] public section

open LPPDifferentiability
open scoped BigOperators

namespace LPP.Busemann

private abbrev Line (x : Lattice) (n : ℕ) :=
  Σ k : Fin (n + 1), LPPDifferentiability.Path x (k.val, n - k.val)

private def vertex {x : Lattice} {n : ℕ} (p : Line x n) (i : Fin (n + 1)) : Lattice :=
  p.2.vertex ⟨i.val, by have hk := p.1.isLt; have hi := i.isLt; omega⟩

private theorem vertex_zero {x : Lattice} {n : ℕ} (p : Line x n) : vertex p 0 = x :=
  p.2.start

private theorem vertex_last {x : Lattice} {n : ℕ} (p : Line x n) :
    vertex p (Fin.last n) = x + ((p.1.val : ℤ), ((n - p.1.val : ℕ) : ℤ)) := by
  unfold vertex
  convert p.2.finish using 1
  congr 1
  apply Fin.ext
  change n = p.1.val + (n - p.1.val)
  have hk := p.1.isLt
  omega

private theorem line_ext {x : Lattice} {n : ℕ} {p q : Line x n}
    (hv : ∀ i, vertex p i = vertex q i) : p = q := by
  rcases p with ⟨a, p⟩
  rcases q with ⟨b, q⟩
  have hend := congrArg Prod.fst (hv (Fin.last n))
  rw [vertex_last, vertex_last] at hend
  simp only [Prod.fst_add] at hend
  have hab : a = b := Fin.ext (by omega)
  subst b
  have hpq : p = q := by
    apply LPPDifferentiability.Path.ext
    intro i
    exact hv ⟨i.val, by have hi := i.isLt; have ha := a.isLt; omega⟩
  cases hpq
  rfl

private def reindex {x : Lattice} {d e : ℕ × ℕ} (hd : d = e) (p : LPPDifferentiability.Path x d) :
    LPPDifferentiability.Path x e := hd ▸ p

private theorem reindex_vertex {x : Lattice} {d e : ℕ × ℕ}
    (hd : d = e) (p : LPPDifferentiability.Path x d) (i : Fin (e.1 + e.2 + 1)) :
    (reindex hd p).vertex i = p.vertex ⟨i.val, by subst e; exact i.isLt⟩ := by
  subst e
  rfl

private theorem reindex_weight (ω : Environment) {x : Lattice} {d e : ℕ × ℕ}
    (hd : d = e) (p : LPPDifferentiability.Path x d) : pathWeight ω (reindex hd p) = pathWeight ω p := by
  subst e
  rfl

private noncomputable def headEquiv (x : Lattice) (s d : ℕ × ℕ)
    (hs : s.1 + s.2 = 1) := (LPPDifferentiability.Path.exists_first_step_equiv x s d hs).choose

private theorem head_vertex (x : Lattice) (s d : ℕ × ℕ) (hs : s.1 + s.2 = 1) :
    ∀ p (i : Fin (d.1 + d.2 + 1)), (headEquiv x s d hs p).vertex i =
      p.val.vertex ⟨i.val + 1, by
        have hi := i.isLt
        simp only [Prod.fst_add, Prod.snd_add]
        omega⟩ :=
  (LPPDifferentiability.Path.exists_first_step_equiv x s d hs).choose_spec.1

private theorem head_weight (ω : Environment) (x : Lattice) (s d : ℕ × ℕ)
    (hs : s.1 + s.2 = 1)
    (p : {p : LPPDifferentiability.Path x (s + d) //
      p.vertex ⟨1, by simp only [Prod.fst_add, Prod.snd_add]; omega⟩ =
        x + ((s.1 : ℤ), (s.2 : ℤ))}) :
    pathWeight ω p.val = ω x + pathWeight ω (headEquiv x s d hs p) :=
  (LPPDifferentiability.Path.exists_first_step_equiv x s d hs).choose_spec.2 ω p

private noncomputable def addHead (x : Lattice) (n : ℕ) (s : ℕ × ℕ)
    (hs : s.1 + s.2 = 1) (q : Line (x + ((s.1 : ℤ), (s.2 : ℤ))) n) :
    Line x (n + 1) := by
  let k : Fin (n + 1 + 1) := ⟨q.1.val + s.1, by have hq := q.1.isLt; omega⟩
  have hd : s + (q.1.val, n - q.1.val) = (k.val, n + 1 - k.val) := by
    apply Prod.ext <;> dsimp [k] <;> have hq := q.1.isLt <;> omega
  exact ⟨k, reindex hd ((headEquiv x s (q.1.val, n - q.1.val) hs).symm q.2).val⟩

private theorem addHead_index (x : Lattice) (n : ℕ) (s : ℕ × ℕ)
    (hs : s.1 + s.2 = 1) (q : Line (x + ((s.1 : ℤ), (s.2 : ℤ))) n) :
    (addHead x n s hs q).1.val = q.1.val + s.1 := rfl

private theorem addHead_vertex (x : Lattice) (n : ℕ) (s : ℕ × ℕ)
    (hs : s.1 + s.2 = 1) (q : Line (x + ((s.1 : ℤ), (s.2 : ℤ))) n)
    (i : Fin (n + 1)) :
    vertex (addHead x n s hs q) ⟨i.val + 1, by omega⟩ = vertex q i := by
  unfold vertex addHead
  rw [reindex_vertex]
  have hv := head_vertex x s (q.1.val, n - q.1.val) hs
    ((headEquiv x s (q.1.val, n - q.1.val) hs).symm q.2)
    ⟨i.val, by have hq := q.1.isLt; have hi := i.isLt; omega⟩
  simpa only [Equiv.apply_symm_apply] using hv.symm

private theorem addHead_first (x : Lattice) (n : ℕ) (s : ℕ × ℕ)
    (hs : s.1 + s.2 = 1) (q : Line (x + ((s.1 : ℤ), (s.2 : ℤ))) n) :
    vertex (addHead x n s hs q) ⟨1, by omega⟩ = x + ((s.1 : ℤ), (s.2 : ℤ)) := by
  exact (addHead_vertex x n s hs q 0).trans (vertex_zero q)

private theorem addHead_weight (ω : Environment) (x : Lattice) (n : ℕ) (s : ℕ × ℕ)
    (hs : s.1 + s.2 = 1) (q : Line (x + ((s.1 : ℤ), (s.2 : ℤ))) n) :
    pathWeight ω (addHead x n s hs q).2 = ω x + pathWeight ω q.2 := by
  unfold addHead
  rw [reindex_weight]
  have hw := head_weight ω x s (q.1.val, n - q.1.val) hs
    ((headEquiv x s (q.1.val, n - q.1.val) hs).symm q.2)
  simpa only [Equiv.apply_symm_apply] using hw

private theorem addHead_injective (x : Lattice) (n : ℕ) (s : ℕ × ℕ)
    (hs : s.1 + s.2 = 1) : Function.Injective (addHead x n s hs) := by
  intro p q hpq
  apply line_ext
  intro i
  have hv := congrArg (fun r : Line x (n + 1) => vertex r ⟨i.val + 1, by omega⟩) hpq
  simpa only [addHead_vertex] using hv

private theorem exists_addHead (x : Lattice) (n : ℕ) (s : ℕ × ℕ)
    (hs : s.1 + s.2 = 1) (p : Line x (n + 1))
    (hp : vertex p ⟨1, by omega⟩ = x + ((s.1 : ℤ), (s.2 : ℤ))) :
    ∃ q, addHead x n s hs q = p := by
  have hb := p.2.vertex_mem_Icc ⟨1, by have hk := p.1.isLt; omega⟩
  have h1 := hb.2.1
  have h2 := hb.2.2
  change (vertex p ⟨1, by omega⟩).1 ≤ _ at h1
  change (vertex p ⟨1, by omega⟩).2 ≤ _ at h2
  rw [hp] at h1 h2
  simp only [Prod.fst_add, Prod.snd_add] at h1 h2
  have hle1 : s.1 ≤ p.1.val := by omega
  have hle2 : s.2 ≤ n + 1 - p.1.val := by omega
  let j : Fin (n + 1) := ⟨p.1.val - s.1, by have hk := p.1.isLt; omega⟩
  have hd : (p.1.val, n + 1 - p.1.val) = s + (j.val, n - j.val) := by
    apply Prod.ext <;> dsimp [j] <;> have hk := p.1.isLt <;> omega
  let pp := reindex hd p.2
  have hpp : pp.vertex ⟨1, by simp only [Prod.fst_add, Prod.snd_add]; omega⟩ =
      x + ((s.1 : ℤ), (s.2 : ℤ)) := by
    unfold pp
    rw [reindex_vertex]
    exact hp
  let q : Line (x + ((s.1 : ℤ), (s.2 : ℤ))) n :=
    ⟨j, headEquiv x s (j.val, n - j.val) hs ⟨pp, hpp⟩⟩
  refine ⟨q, ?_⟩
  apply line_ext
  intro i
  by_cases hi : i.val = 0
  · have hi0 : i = 0 := Fin.ext hi
    rw [hi0, vertex_zero, vertex_zero]
  · let t : Fin (n + 1) := ⟨i.val - 1, by have hi' := i.isLt; omega⟩
    have hit : i = ⟨t.val + 1, by omega⟩ := Fin.ext (by dsimp [t]; omega)
    rw [hit, addHead_vertex]
    change (headEquiv x s (j.val, n - j.val) hs ⟨pp, hpp⟩).vertex _ = _
    rw [head_vertex]
    unfold pp
    rw [reindex_vertex]
    rfl

private theorem first_cases {x : Lattice} {n : ℕ} (p : Line x (n + 1)) :
    vertex p ⟨1, by omega⟩ = x + (1, 0) ∨
      vertex p ⟨1, by omega⟩ = x + (0, 1) := by
  let t : Fin (p.1.val + (n + 1 - p.1.val)) :=
    ⟨0, by have hk := p.1.isLt; omega⟩
  have hzero : t.castSucc = 0 := Fin.ext rfl
  have hp := p.2.step t
  rw [hzero, p.2.start] at hp
  exact hp

private noncomputable def prependSum (x : Lattice) (n : ℕ) :
    Line (x + (1, 0)) n ⊕ Line (x + (0, 1)) n → Line x (n + 1)
  | Sum.inl q => addHead x n (1, 0) (by decide) q
  | Sum.inr q => addHead x n (0, 1) (by decide) q

private theorem prependSum_bijective (x : Lattice) (n : ℕ) :
    Function.Bijective (prependSum x n) := by
  constructor
  · intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (addHead_injective x n (1, 0) (by decide) hab)
      | inr b =>
        have hv := congrArg (fun p : Line x (n + 1) => vertex p ⟨1, by omega⟩) hab
        change vertex (addHead x n (1, 0) (by decide) a) _ = vertex (addHead x n (0, 1) (by decide) b) _ at hv
        rw [addHead_first, addHead_first] at hv
        have hc := congrArg Prod.fst hv
        simp only [Prod.fst_add] at hc
        omega
    | inr a =>
      cases b with
      | inl b =>
        have hv := congrArg (fun p : Line x (n + 1) => vertex p ⟨1, by omega⟩) hab
        change vertex (addHead x n (0, 1) (by decide) a) _ = vertex (addHead x n (1, 0) (by decide) b) _ at hv
        rw [addHead_first, addHead_first] at hv
        have hc := congrArg Prod.fst hv
        simp only [Prod.fst_add] at hc
        omega
      | inr b => exact congrArg Sum.inr (addHead_injective x n (0, 1) (by decide) hab)
  · intro p
    rcases first_cases p with hp | hp
    · obtain ⟨q, hq⟩ := exists_addHead x n (1, 0) (by decide) p hp
      exact ⟨Sum.inl q, hq⟩
    · obtain ⟨q, hq⟩ := exists_addHead x n (0, 1) (by decide) p hp
      exact ⟨Sum.inr q, hq⟩

private noncomputable def energy (ω : Environment) (h : ℝ × ℝ) {x : Lattice} {n : ℕ}
    (p : Line x n) : ℝ :=
  pathWeight ω p.2 + h.1 * (p.1.val : ℝ) + h.2 * ((n - p.1.val : ℕ) : ℝ)

private theorem energy_addHead (ω : Environment) (h : ℝ × ℝ)
    (x : Lattice) (n : ℕ) (s : ℕ × ℕ) (hs : s.1 + s.2 = 1)
    (q : Line (x + ((s.1 : ℤ), (s.2 : ℤ))) n) :
    energy ω h (addHead x n s hs q) =
      ω x + h.1 * (s.1 : ℝ) + h.2 * (s.2 : ℝ) + energy ω h q := by
  unfold energy
  rw [addHead_weight, addHead_index]
  have hsub : n + 1 - (q.1.val + s.1) = s.2 + (n - q.1.val) := by
    have hq := q.1.isLt
    omega
  rw [hsub]
  push_cast
  ring

private theorem sum_exp_succ (ω : Environment) (h : ℝ × ℝ) (β : ℝ)
    (n : ℕ) (x : Lattice) :
    (∑ p : Line x (n + 1), Real.exp (β * energy ω h p)) =
      Real.exp (β * ω x) *
        (Real.exp (β * h.1) * (∑ q : Line (x + (1, 0)) n, Real.exp (β * energy ω h q)) +
         Real.exp (β * h.2) * (∑ q : Line (x + (0, 1)) n, Real.exp (β * energy ω h q))) := by
  classical
  have heq := Fintype.sum_bijective (prependSum x n) (prependSum_bijective x n)
    (fun q => Real.exp (β * energy ω h (prependSum x n q)))
    (fun p => Real.exp (β * energy ω h p)) (fun _ => rfl)
  rw [← heq, Fintype.sum_sum_type]
  simp only [prependSum, energy_addHead, Nat.cast_one, Nat.cast_zero, mul_one, mul_zero,
    add_zero]
  simp_rw [mul_add, Real.exp_add]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

-- The named parameter `hβ` is part of the shared theorem interface.
set_option linter.unusedVariables false in
/-- The actual tilted finite path sum is positive, starts at one, and splits
at its first departure step. This is the terminal-excluded partition convention
of JR1810.03580v3, Section 2.2, with the departure-weight correction. -/
theorem finite_tilted_partition_zero_pos_succ (ω : Environment) (h : ℝ × ℝ)
    (β : ℝ) (hβ : 0 < β) (N : ℕ) (x : Lattice) :
    let Z : ℕ → Lattice → ℝ := fun n y =>
      ∑ k : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
        Real.exp (β * (pathWeight ω p + h.1 * (k.val : ℝ) +
          h.2 * ((n - k.val : ℕ) : ℝ)))
    Z 0 x = 1 ∧ 0 < Z N x ∧
      Z (N + 1) x = Real.exp (β * ω x) *
        (Real.exp (β * h.1) * Z N (x + (1, 0)) +
         Real.exp (β * h.2) * Z N (x + (0, 1))) := by
  classical
  clear hβ
  dsimp only
  constructor
  · have : Subsingleton (LPPDifferentiability.Path x (0, 0)) := ⟨fun p q => by
      apply LPPDifferentiability.Path.ext
      intro i
      have hi : i = 0 := Fin.ext (by omega)
      rw [hi, p.start, q.start]⟩
    let : Unique (LPPDifferentiability.Path x (0, 0)) :=
      { default := Classical.choice (inferInstance : Nonempty (LPPDifferentiability.Path x (0, 0)))
        uniq := fun p => @Subsingleton.elim _ this p _ }
    simp [pathWeight_zero]
  constructor
  · apply Finset.sum_pos
    · intro k _
      exact Finset.sum_pos (fun p _ => Real.exp_pos _) Finset.univ_nonempty
    · exact Finset.univ_nonempty
  · simpa only [Line, Fintype.sum_sigma, energy] using sum_exp_succ ω h β N x

end LPP.Busemann
