/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.PathSets
public import LPP_Foundations.Model.Paths.Fintype
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import LPP_Foundations.Model.Paths.Level
import Mathlib.Tactic

/-! # The rare event of a block as a finite path event

The block event `A_{p,h}` in equation (6.3) of the differentiability preprint is the union of
the defect event and the crossing event at `b = (p,h)`. Its witnesses are the paths
satisfying the predicates `defectWitness b` or `crossingWitness b`.
This file lists those witnesses as a finite indexed family of paths with
weight thresholds, the form used by the BK inequality `real_weight_path_bk`:
each defect path is listed twice (slopes `dl` and `dr`, threshold
`f_σ(e) + η s`) and each crossing path once (threshold `G0 m - K s`).
It proves that the listed path event is exactly the literal event.

## References

* C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint.
-/

public section

open scoped BigOperators

namespace LPPDifferentiability

private theorem coord_abs_le (a L r : ℝ) (z : Lattice)
    (hL : |(z.1 : ℝ)+(z.2 : ℝ)| ≤ L) (hr : |(1-a)*(z.1 : ℝ)-a*(z.2 : ℝ)| ≤ r) :
    |(z.1 : ℝ)| ≤ (|a|+|1-a|)*L+r ∧ |(z.2 : ℝ)| ≤ (|a|+|1-a|)*L+r := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans hL
  have h1 : |a*((z.1 : ℝ)+(z.2 : ℝ))| ≤ |a| * L := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hL (abs_nonneg a)
  have h2 : |(1-a)*((z.1 : ℝ)+(z.2 : ℝ))| ≤ |1-a| * L := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hL (abs_nonneg _)
  have h3 : 0 ≤ |a| * L := mul_nonneg (abs_nonneg a) hL0
  have h4 : 0 ≤ |1-a| * L := mul_nonneg (abs_nonneg _) hL0
  obtain ⟨e1, e1'⟩ := abs_le.mp h1
  obtain ⟨e2, e2'⟩ := abs_le.mp h2
  obtain ⟨er, er'⟩ := abs_le.mp hr
  constructor
  · apply abs_le.mpr; constructor <;> linarith
  · apply abs_le.mpr; constructor <;> linarith

private theorem mem_box_of_vertex_bound {u : Lattice} {e : ℕ × ℕ} (q : Path u e) (R : ℕ)
    (h : ∀ i, |((q.vertex i).1 : ℝ)| ≤ R ∧ |((q.vertex i).2 : ℝ)| ≤ R) :
    (u, e) ∈ (Finset.Icc (-(R : ℤ)) R ×ˢ Finset.Icc (-(R : ℤ)) R) ×ˢ
      (Finset.range (2*R+1) ×ˢ Finset.range (2*R+1)) := by
  have hcast : ∀ x : ℤ, |(x : ℝ)| ≤ (R : ℝ) → -(R : ℤ) ≤ x ∧ x ≤ R := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := abs_le.mp hx
    exact ⟨by exact_mod_cast hx1, by exact_mod_cast hx2⟩
  have h0 := h 0
  have hl := h (Fin.last _)
  rw [q.start] at h0
  rw [q.finish] at hl
  simp only [Prod.fst_add, Prod.snd_add] at hl
  have a1 := hcast _ h0.1
  have a2 := hcast _ h0.2
  have b1 := hcast _ hl.1
  have b2 := hcast _ hl.2
  simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
  omega

/-- The rare event of the block at `b`, with the witness predicates `defectWitness b` and
`crossingWitness b`, is a finite path event: there is a finite indexed family of
paths with weight thresholds such that a listed path exceeding its threshold
is a witness, every witness is listed (with the same collected sites) above its
threshold, and the listed event equals the literal event. -/
theorem exists_stage_witness_path_event (a s : ℝ) (m : ℕ) (η G0 dl dr K : ℝ)
    (b : Lattice) :
    ∃ (I : Type) (_ : Fintype I) (start : I → Lattice) (displacement : I → ℕ × ℕ)
      (paths : (i : I) → Path (start i) (displacement i)) (threshold : I → ℝ),
      (∀ ω : Environment,
        let v : Lattice → Lattice := fun b =>
          let j : ℤ := ⌊(b.2:ℝ)*s+a*((b.1*m:ℤ):ℝ)⌋
          (j,b.1*m-j)
        let block : Lattice → Lattice → Prop := fun b z =>
          (b.1 : ℝ)*(m : ℝ) ≤ (z.1 : ℝ)+(z.2 : ℝ) ∧ (z.1 : ℝ)+(z.2 : ℝ) ≤ (b.1 : ℝ)*(m : ℝ)+3*(m : ℝ) ∧
            |(1-a)*(z.1 : ℝ)-a*(z.2 : ℝ)-(b.2 : ℝ)*s| ≤ 4*s
        let defectWitness : Lattice → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop := fun b _ e q =>
          (∀ i, block b (q.vertex i)) ∧
            min (G0*((e.1 : ℝ)+(e.2 : ℝ))+dl*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q)
              (G0*((e.1 : ℝ)+(e.2 : ℝ))+dr*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q) < -(η*s)
        let crossingWitness : Lattice → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop :=
          fun b u e q =>
            u.1+u.2 = (b.1+1)*m ∧ e.1+e.2 = m ∧
              (∀ i, |((1-a)*((q.vertex i).1 : ℝ)-a*((q.vertex i).2 : ℝ))-
                ((1-a)*((v (b.1+1,b.2)).1 : ℝ)-a*((v (b.1+1,b.2)).2 : ℝ))| ≤ 8*s) ∧
              G0*(m : ℝ)-K*s < pathWeight ω q
        (∀ i, threshold i < pathWeight ω (paths i) →
          defectWitness b (start i) (displacement i) (paths i) ∨
            crossingWitness b (start i) (displacement i) (paths i)) ∧
        ∀ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
          defectWitness b u e q ∨ crossingWitness b u e q →
          ∃ i, (paths i).collectedSites = q.collectedSites ∧
            threshold i < pathWeight ω (paths i)) ∧
      {ω : Environment | ∃ i, threshold i < pathWeight ω (paths i)} =
        {ω : Environment |
          let v : Lattice → Lattice := fun b =>
            let j : ℤ := ⌊(b.2:ℝ)*s+a*((b.1*m:ℤ):ℝ)⌋
            (j,b.1*m-j)
          let block : Lattice → Lattice → Prop := fun b z =>
            (b.1 : ℝ)*(m : ℝ) ≤ (z.1 : ℝ)+(z.2 : ℝ) ∧ (z.1 : ℝ)+(z.2 : ℝ) ≤ (b.1 : ℝ)*(m : ℝ)+3*(m : ℝ) ∧
              |(1-a)*(z.1 : ℝ)-a*(z.2 : ℝ)-(b.2 : ℝ)*s| ≤ 4*s
          let defectWitness : Lattice → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop := fun b _ e q =>
            (∀ i, block b (q.vertex i)) ∧
              min (G0*((e.1 : ℝ)+(e.2 : ℝ))+dl*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q)
                (G0*((e.1 : ℝ)+(e.2 : ℝ))+dr*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q) < -(η*s)
          let crossingWitness : Lattice → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop :=
            fun b u e q =>
              u.1+u.2 = (b.1+1)*m ∧ e.1+e.2 = m ∧
                (∀ i, |((1-a)*((q.vertex i).1 : ℝ)-a*((q.vertex i).2 : ℝ))-
                  ((1-a)*((v (b.1+1,b.2)).1 : ℝ)-a*((v (b.1+1,b.2)).2 : ℝ))| ≤ 8*s) ∧
                G0*(m : ℝ)-K*s < pathWeight ω q
          ∃ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
            defectWitness b u e q ∨ crossingWitness b u e q} := by
  classical
  let v : Lattice → Lattice := fun b =>
    let j : ℤ := ⌊(b.2:ℝ)*s+a*((b.1*m:ℤ):ℝ)⌋
    (j,b.1*m-j)
  let block : Lattice → Lattice → Prop := fun b z =>
    (b.1 : ℝ)*(m : ℝ) ≤ (z.1 : ℝ)+(z.2 : ℝ) ∧ (z.1 : ℝ)+(z.2 : ℝ) ≤ (b.1 : ℝ)*(m : ℝ)+3*(m : ℝ) ∧
      |(1-a)*(z.1 : ℝ)-a*(z.2 : ℝ)-(b.2 : ℝ)*s| ≤ 4*s
  let rv : ℝ := (1-a)*((v (b.1+1,b.2)).1 : ℝ)-a*((v (b.1+1,b.2)).2 : ℝ)
  -- The geometric part of a crossing witness (no weights).
  let cross : (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop := fun u e q =>
    u.1+u.2 = (b.1+1)*m ∧ e.1+e.2 = m ∧
      ∀ i, |((1-a)*((q.vertex i).1 : ℝ)-a*((q.vertex i).2 : ℝ))-rv| ≤ 8*s
  -- The two witness predicates, unfolded, with the weights.
  let defW : Environment → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop := fun ω _ e q =>
    (∀ i, block b (q.vertex i)) ∧
      min (G0*((e.1 : ℝ)+(e.2 : ℝ))+dl*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q)
        (G0*((e.1 : ℝ)+(e.2 : ℝ))+dr*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q) < -(η*s)
  let crossW : Environment → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop := fun ω u e q =>
    u.1+u.2 = (b.1+1)*m ∧ e.1+e.2 = m ∧
      (∀ i, |((1-a)*((q.vertex i).1 : ℝ)-a*((q.vertex i).2 : ℝ))-rv| ≤ 8*s) ∧
      G0*(m : ℝ)-K*s < pathWeight ω q
  -- A box containing the start and displacement of every listed path.
  let R : ℕ := ⌈(|a|+|1-a|)*(|(b.1 : ℝ)*(m : ℝ)|+3*(m : ℝ))+(|(b.2 : ℝ)*s|+8*|s|+|rv|)⌉₊
  let box : Finset (Lattice × (ℕ × ℕ)) :=
    (Finset.Icc (-(R : ℤ)) R ×ˢ Finset.Icc (-(R : ℤ)) R) ×ˢ
      (Finset.range (2*R+1) ×ˢ Finset.range (2*R+1))
  have hbox : ∀ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
      ((∀ i, block b (q.vertex i)) ∨ cross u e q) → (u, e) ∈ box := by
    intro u e q hq
    apply mem_box_of_vertex_bound q R
    intro i
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hs0 := le_abs_self s
    have hs1 := abs_nonneg s
    have hrv1 := neg_abs_le rv
    have hrv2 := le_abs_self rv
    have hb1 := neg_abs_le ((b.1 : ℝ)*(m : ℝ))
    have hb1' := le_abs_self ((b.1 : ℝ)*(m : ℝ))
    have hb2 := neg_abs_le ((b.2 : ℝ)*s)
    have hb2' := le_abs_self ((b.2 : ℝ)*s)
    have hgeom : |((q.vertex i).1 : ℝ)+((q.vertex i).2 : ℝ)| ≤ |(b.1 : ℝ)*(m : ℝ)|+3*(m : ℝ) ∧
        |(1-a)*((q.vertex i).1 : ℝ)-a*((q.vertex i).2 : ℝ)| ≤ |(b.2 : ℝ)*s|+8*|s|+|rv| := by
      rcases hq with hq | ⟨hu, he, hband⟩
      · obtain ⟨h1, h2, h3⟩ := hq i
        obtain ⟨h3a, h3b⟩ := abs_le.mp h3
        exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
      · have hl := q.level i
        have hi : (i.val : ℤ) ≤ m := by have := i.isLt; omega
        have hlZ : (q.vertex i).1+(q.vertex i).2 = (b.1+1)*(m : ℤ)+(i.val : ℤ) := by
          rw [hl, hu]
        have hlR : ((q.vertex i).1 : ℝ)+((q.vertex i).2 : ℝ) =
            ((b.1 : ℝ)+1)*(m : ℝ)+(i.val : ℝ) := by exact_mod_cast hlZ
        have hiR : (i.val : ℝ) ≤ m := by exact_mod_cast hi
        have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
        obtain ⟨h3a, h3b⟩ := abs_le.mp (hband i)
        exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    have hc := coord_abs_le a _ _ (q.vertex i) hgeom.1 hgeom.2
    have hR := Nat.le_ceil
      ((|a|+|1-a|)*(|(b.1 : ℝ)*(m : ℝ)|+3*(m : ℝ))+(|(b.2 : ℝ)*s|+8*|s|+|rv|))
    exact ⟨hc.1.trans hR, hc.2.trans hR⟩
  -- The index set: paths in the box, with a label `0`, `1` (defect, slopes
  -- `dl`, `dr`) or `2` (crossing), and the geometric condition of that label.
  let I := {x : (Σ ue : box, Path ue.1.1 ue.1.2) × Fin 3 //
    (x.2 ≠ 2 → ∀ i, block b (x.1.2.vertex i)) ∧ (x.2 = 2 → cross x.1.1.1.1 x.1.1.1.2 x.1.2)}
  let st : I → Lattice := fun x => x.1.1.1.1.1
  let dp : I → ℕ × ℕ := fun x => x.1.1.1.1.2
  let pa : (x : I) → Path (st x) (dp x) := fun x => x.1.1.2
  let threshold : I → ℝ := fun x =>
    if x.1.2 = 0 then
      G0*(((dp x).1 : ℝ)+((dp x).2 : ℝ))+dl*((1-a)*((dp x).1 : ℝ)-a*((dp x).2 : ℝ))+η*s
    else if x.1.2 = 1 then
      G0*(((dp x).1 : ℝ)+((dp x).2 : ℝ))+dr*((1-a)*((dp x).1 : ℝ)-a*((dp x).2 : ℝ))+η*s
    else G0*(m : ℝ)-K*s
  have hk3 : ∀ k : Fin 3, k ≠ 0 → k ≠ 1 → k = 2 := by decide
  have ht0 : ∀ x : I, x.1.2 = 0 → threshold x =
      G0*(((dp x).1 : ℝ)+((dp x).2 : ℝ))+dl*((1-a)*((dp x).1 : ℝ)-a*((dp x).2 : ℝ))+η*s :=
    fun x hx => ite_eq_left hx
  have ht1 : ∀ x : I, x.1.2 = 1 → threshold x =
      G0*(((dp x).1 : ℝ)+((dp x).2 : ℝ))+dr*((1-a)*((dp x).1 : ℝ)-a*((dp x).2 : ℝ))+η*s := by
    intro x hx
    have h0 : x.1.2 ≠ 0 := by rw [hx]; decide
    exact (ite_eq_right h0).trans (ite_eq_left hx)
  have ht2 : ∀ x : I, x.1.2 = 2 → threshold x = G0*(m : ℝ)-K*s := by
    intro x hx
    have h0 : x.1.2 ≠ 0 := by rw [hx]; decide
    have h1 : x.1.2 ≠ 1 := by rw [hx]; decide
    exact (ite_eq_right h0).trans (ite_eq_right h1)
  have hfwd : ∀ (ω : Environment) (x : I), threshold x < pathWeight ω (pa x) →
      defW ω (st x) (dp x) (pa x) ∨ crossW ω (st x) (dp x) (pa x) := by
    intro ω x hthr
    by_cases h2 : x.1.2 = 2
    · rw [ht2 x h2] at hthr
      obtain ⟨hu, he, hband⟩ := x.2.2 h2
      exact Or.inr ⟨hu, he, hband, hthr⟩
    · refine Or.inl ⟨x.2.1 h2, ?_⟩
      by_cases h0 : x.1.2 = 0
      · rw [ht0 x h0] at hthr
        exact min_lt_iff.mpr (Or.inl (by linarith))
      · have h1 : x.1.2 = 1 := by
          by_contra h1
          exact h2 (hk3 _ h0 h1)
        rw [ht1 x h1] at hthr
        exact min_lt_iff.mpr (Or.inr (by linarith))
  have hbwd : ∀ (ω : Environment) (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
      defW ω u e q ∨ crossW ω u e q →
      ∃ x : I, (pa x).collectedSites = q.collectedSites ∧ threshold x < pathWeight ω (pa x) := by
    rintro ω u e q (⟨hblock, hmin⟩ | ⟨hu, he, hband, hw⟩)
    · have hm := hbox u e q (Or.inl hblock)
      rcases min_lt_iff.mp hmin with h | h
      · let x : I := ⟨(⟨⟨(u, e), hm⟩, q⟩, 0), fun _ => hblock,
          fun h0 => ((by decide : (0 : Fin 3) ≠ 2) h0).elim⟩
        refine ⟨x, rfl, ?_⟩
        rw [ht0 x rfl]
        show G0*((e.1 : ℝ)+(e.2 : ℝ))+dl*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))+η*s < pathWeight ω q
        linarith
      · let x : I := ⟨(⟨⟨(u, e), hm⟩, q⟩, 1), fun _ => hblock,
          fun h0 => ((by decide : (1 : Fin 3) ≠ 2) h0).elim⟩
        refine ⟨x, rfl, ?_⟩
        rw [ht1 x rfl]
        show G0*((e.1 : ℝ)+(e.2 : ℝ))+dr*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))+η*s < pathWeight ω q
        linarith
    · let x : I := ⟨(⟨⟨(u, e), hbox u e q (Or.inr ⟨hu, he, hband⟩)⟩, q⟩, 2),
        fun h2 => absurd rfl h2, fun _ => ⟨hu, he, hband⟩⟩
      refine ⟨x, rfl, ?_⟩
      rw [ht2 x rfl]
      exact hw
  refine ⟨I, Subtype.fintype _, st, dp, pa, threshold, fun ω => ?_, ?_⟩
  · intro _ _ _ _
    exact ⟨fun x hx => hfwd ω x hx, fun u e q hq => hbwd ω u e q hq⟩
  · ext ω
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨st x, dp x, pa x, hfwd ω x hx⟩
    · rintro ⟨u, e, q, hq⟩
      obtain ⟨x, -, hx⟩ := hbwd ω u e q hq
      exact ⟨x, hx⟩

end LPPDifferentiability
