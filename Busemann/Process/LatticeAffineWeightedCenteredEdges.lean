/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.LatticeCenteredIncrementMeans
public import Busemann.Process.LatticeUnitActionRectangles
public import ProbabilityBasics.Probability.RectangleAffineWeights
import ProbabilityBasics.Combinatorics.ColumnRectangle
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-! One- and two-coordinate affine averages for centered edges of a generic action. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped BigOperators Topology

namespace LPP.Busemann

private theorem permutation_two_cases (σ : Equiv.Perm (Fin 2)) :
    (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0) := by
  have hne : σ 1 ≠ σ 0 := fun h => (by norm_num : (1 : Fin 2) ≠ 0) (σ.injective h)
  by_cases h0 : σ 0 = 0
  · exact Or.inl ⟨h0, Fin.eq_one_of_ne_zero (σ 1) (by simpa only [h0] using hne)⟩
  · have h0one : σ 0 = 1 := Fin.eq_one_of_ne_zero (σ 0) h0
    refine Or.inr ⟨h0one, ?_⟩
    by_contra h1
    exact hne ((Fin.eq_one_of_ne_zero (σ 1) h1).trans h0one.symm)

private theorem sum_rectangle_swap (a b : ℤ) (g : Lattice → ℝ) :
    (∑ z ∈ (Finset.Ico (0 : ℤ) a).product (Finset.Ico (0 : ℤ) b), g (z.2, z.1)) =
      ∑ z ∈ (Finset.Ico (0 : ℤ) b).product (Finset.Ico (0 : ℤ) a), g z := by
  calc
    _ = ∑ y ∈ Finset.Ico (0 : ℤ) b, ∑ x ∈ Finset.Ico (0 : ℤ) a, g (y, x) :=
      Finset.sum_product_right _ _ _
    _ = _ := (Finset.sum_product _ _ _).symm

/-- Centered unit edges of a generic action have vanishing affine averages along
single-coordinate prefixes and every ordering of the two-coordinate prefixes.
This is the affine specialization of JR arXiv:1810.03580v3, Appendix B, Lemma B.5. -/
theorem ae_tendsto_affine_weighted_centered_edges_of_action
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω)
    (hzero : ∀ s : Ω, T 0 s = s)
    (hadd : ∀ (z w : Lattice) (s : Ω), T (z + w) s = T z (T w s))
    (hShift : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (B : Lattice → Lattice → Ω → ℝ)
    (hB : is_shift_covariant_cocycle P T B)
    (hInt : ∀ x y, Integrable (B x y) P)
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) :
    let mΩ0 : MeasurableSpace Ω := inferInstance
    let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
    letI : MeasurableSpace Ω := mΩ0
    let u : Fin 2 → Ω → ℝ :=
      fun i => P[B 0 (finiteEdgeStep i) | I]
    let F : Fin 2 → Ω → ℝ :=
      fun i s => B 0 (finiteEdgeStep i) s - u i s
    let R₁ : ℕ → Finset ℤ := fun n =>
      Finset.Ico 0 ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)
    let R₂ : ℕ → Finset (ℤ × ℤ) := fun n =>
      (R₁ n).product (Finset.Ico 0 ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
    let κ : Fin 2 → (ℤ × ℤ) → ℤ := fun j k => if j = 0 then k.1 else k.2
    let X : Equiv.Perm (Fin 2) → (ℤ × ℤ) → Lattice :=
      fun σ k => k.1 • finiteEdgeStep (σ 0) + k.2 • finiteEdgeStep (σ 1)
    ∀ᵐ s ∂P,
      (∀ (i : Fin 2) (c d : ℝ), Tendsto (fun n : ℕ =>
        (∑ k ∈ R₁ n, (c + d * (((k + 1 : ℤ) : ℝ) / (n : ℝ))) *
          F i (T (k • finiteEdgeStep i) s)) / (n : ℝ))
        atTop (𝓝 0)) ∧
      (∀ (σ : Equiv.Perm (Fin 2)) (j : Fin 2) (c d : ℝ),
        Tendsto (fun n : ℕ =>
          (∑ k ∈ R₂ n, (c + d * (((κ j k + 1 : ℤ) : ℝ) / (n : ℝ))) *
            F (σ j) (T (X σ k) s)) / (n : ℝ)^2)
          atTop (𝓝 0)) := by
  classical
  let mΩ0 : MeasurableSpace Ω := inferInstance
  let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
  let : MeasurableSpace Ω := mΩ0
  let u : Fin 2 → Ω → ℝ :=
    fun i => P[B 0 (finiteEdgeStep i) | I]
  let F : Fin 2 → Ω → ℝ :=
    fun i s => B 0 (finiteEdgeStep i) s - u i s
  let R₁ : ℕ → Finset ℤ := fun n =>
    Finset.Ico 0 ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)
  let R₂ : ℕ → Finset (ℤ × ℤ) := fun n =>
    (R₁ n).product (Finset.Ico 0 ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
  let κ : Fin 2 → (ℤ × ℤ) → ℤ := fun j k => if j = 0 then k.1 else k.2
  let X : Equiv.Perm (Fin 2) → (ℤ × ℤ) → Lattice :=
    fun σ k => k.1 • finiteEdgeStep (σ 0) + k.2 • finiteEdgeStep (σ 1)
  change ∀ᵐ s ∂P,
    (∀ (i : Fin 2) (c d : ℝ), Tendsto (fun n : ℕ =>
      (∑ k ∈ R₁ n, (c + d * (((k + 1 : ℤ) : ℝ) / (n : ℝ))) *
        F i (T (k • finiteEdgeStep i) s)) / (n : ℝ))
      atTop (𝓝 0)) ∧
    (∀ (σ : Equiv.Perm (Fin 2)) (j : Fin 2) (c d : ℝ),
      Tendsto (fun n : ℕ =>
        (∑ k ∈ R₂ n, (c + d * (((κ j k + 1 : ℤ) : ℝ) / (n : ℝ))) *
          F (σ j) (T (X σ k) s)) / (n : ℝ)^2)
        atTop (𝓝 0))
  -- The actual centering producer supplies both full- and unit-invariant zero means.
  have hF (i : Fin 2) : Integrable (F i) P ∧
      P[F i | I] =ᵐ[P] (0 : Ω → ℝ) ∧
      P[F i | @MeasurableSpace.invariants Ω mΩ0 (T (finiteEdgeStep i))] =ᵐ[P]
        (0 : Ω → ℝ) := by
    have h := centered_increment_condExp_zero_of_action
      P T hzero hadd hShift B hB hInt i
    exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  have hRect (β : Fin 2 → ℝ) (hβ : ∀ j, 0 < β j) (i : Fin 2) :=
    ProbabilityBasics.ae_tendsto_affine_weighted_prefix_rectangles_of_condExp_zero
      P T hzero hadd hShift (F i) (hF i).1 β hβ (hF i).2.1
  -- A one-coordinate average is the same generic theorem on a column action.
  have hColumn (i : Fin 2) : ∀ᵐ s ∂P, ∀ c d : ℝ,
      Tendsto (fun n : ℕ =>
        (∑ k ∈ R₁ n, (c + d * (((k + 1 : ℤ) : ℝ) / (n : ℝ))) *
          F i (T (k • finiteEdgeStep i) s)) / (n : ℝ)) atTop (𝓝 0) := by
    let Tcol : Lattice → Ω → Ω := fun z s => T (z.1 • finiteEdgeStep i) s
    have hc0 (s : Ω) : Tcol 0 s = s := by
      change T ((0 : ℤ) • finiteEdgeStep i) s = s
      simpa only [zero_zsmul] using hzero s
    have hcadd (z w : Lattice) (s : Ω) : Tcol (z + w) s = Tcol z (Tcol w s) := by
      change T ((z.1 + w.1) • finiteEdgeStep i) s =
        T (z.1 • finiteEdgeStep i) (T (w.1 • finiteEdgeStep i) s)
      rw [add_zsmul]
      exact hadd (z.1 • finiteEdgeStep i) (w.1 • finiteEdgeStep i) s
    have hcMP (z : Lattice) : MeasurePreserving (Tcol z) P P := hShift (z.1 • finiteEdgeStep i)
    have hCE : P[F i | ⨅ z : Lattice,
        @MeasurableSpace.invariants Ω mΩ0 (Tcol z)] =ᵐ[P]
          (0 : Ω → ℝ) := by
      rw [show (⨅ z : Lattice, @MeasurableSpace.invariants Ω mΩ0 (Tcol z)) =
          @MeasurableSpace.invariants Ω mΩ0 (T (finiteEdgeStep i)) from
        unit_column_invariants_of_action T hzero hadd i]
      exact (hF i).2.2
    let β : Fin 2 → ℝ := fun j => if j = 0 then b 0 else 1
    have hβ : ∀ j, 0 < β j := by
      intro j
      dsimp only [β]
      split_ifs
      · exact hb 0
      · norm_num
    have h := ProbabilityBasics.ae_tendsto_affine_weighted_prefix_rectangles_of_condExp_zero
      P Tcol hc0 hcadd hcMP (F i) (hF i).1 β hβ hCE
    filter_upwards [h] with s hs
    intro c d
    have hlim : Tendsto (fun n : ℕ =>
        (∑ z ∈ (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
          (Finset.Ico (0 : ℤ) (n : ℤ)),
          (c + d * (((z.1 + 1 : ℤ) : ℝ) / (n : ℝ))) *
            F i (T (z.1 • finiteEdgeStep i) s)) / (n : ℝ)^2) atTop (𝓝 0) := by
      simpa [β, Tcol] using hs 0 c d
    exact hlim.congr' (Eventually.of_forall (fun n =>
      ProbabilityBasics.sum_column_rectangle_div_sq
        (fun k : ℤ => (c + d * (((k + 1 : ℤ) : ℝ) / (n : ℝ))) *
          F i (T (k • finiteEdgeStep i) s)) ⌊(n : ℝ) * b 0⌋₊ n))
  let bs : Fin 2 → ℝ := fun j => if j = 0 then b 1 else b 0
  have hbs : ∀ j, 0 < bs j := by
    intro j
    dsimp only [bs]
    split_ifs
    · exact hb 1
    · exact hb 0
  have hColumns := ae_all_iff.mpr hColumn
  have hOriginal := ae_all_iff.mpr (fun i : Fin 2 => hRect b hb i)
  have hSwapped := ae_all_iff.mpr (fun i : Fin 2 => hRect bs hbs i)
  filter_upwards [hColumns, hOriginal, hSwapped] with s hsCol hsOrig hsSwap
  refine ⟨hsCol, ?_⟩
  intro σ j c d
  rcases permutation_two_cases σ with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hσ (i : Fin 2) : σ i = i := by
      fin_cases i
      · exact h0
      · exact h1
    have hX (k : Lattice) : X σ k = k := by
      dsimp only [X]
      rw [h0, h1]
      apply Prod.ext <;> simp [finiteEdgeStep]
    have h := hsOrig j j c d
    simpa only [hσ j, hX, κ, Int.cast_add, Int.cast_one] using h
  · have hX (k : Lattice) : X σ k = (k.2, k.1) := by
      dsimp only [X]
      rw [h0, h1]
      apply Prod.ext <;> simp [finiteEdgeStep]
    by_cases hj : j = 0
    · subst j
      have h := hsSwap 1 1 c d
      convert h using 1
      funext n
      simp only [h0, hX, κ]
      change (∑ k ∈ (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
          (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ)),
          (c + d * (((k.1 + 1 : ℤ) : ℝ) / (n : ℝ))) * F 1 (T (k.2, k.1) s)) /
            (n : ℝ)^2 =
        (∑ z ∈ (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ)).product
          (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)),
          (c + d * (((z.2 : ℝ) + 1) / (n : ℝ))) * F 1 (T z s)) / (n : ℝ)^2
      congr 1
      simpa only [Int.cast_add, Int.cast_one] using
        sum_rectangle_swap ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ)
          (fun z : Lattice => (c + d * (((z.2 + 1 : ℤ) : ℝ) / (n : ℝ))) * F 1 (T z s))
    · have hj1 : j = 1 := Fin.eq_one_of_ne_zero j hj
      subst j
      have h := hsSwap 0 0 c d
      convert h using 1
      funext n
      simp only [h1, hX, κ]
      change (∑ k ∈ (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
          (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ)),
          (c + d * (((k.2 + 1 : ℤ) : ℝ) / (n : ℝ))) * F 0 (T (k.2, k.1) s)) /
            (n : ℝ)^2 =
        (∑ z ∈ (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ)).product
          (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)),
          (c + d * (((z.1 : ℝ) + 1) / (n : ℝ))) * F 0 (T z s)) / (n : ℝ)^2
      congr 1
      simpa only [Int.cast_add, Int.cast_one] using
        sum_rectangle_swap ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ)
          (fun z : Lattice => (c + d * (((z.1 + 1 : ℤ) : ℝ) / (n : ℝ))) * F 0 (T z s))

end LPP.Busemann
