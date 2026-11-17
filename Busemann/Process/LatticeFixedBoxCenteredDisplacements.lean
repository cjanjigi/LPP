/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.LatticeAffineWeightedCenteredEdges
public import Busemann.Process.LatticeInvariantConditionalDrifts
public import Busemann.Process.CenteredDisplacementSums
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Generic action box centered displacement averages. -/
@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped BigOperators Topology
namespace LPP.Busemann

private theorem sum_int_prefix (N : ℕ) (g : ℤ → ℝ) :
    (∑ k ∈ Finset.Ico (0 : ℤ) (N : ℤ), g k) = ∑ k ∈ Finset.range N, g (k : ℤ) := by
  rw [Int.Ico_eq_finset_map]
  simp

private theorem sum_int_rectangle (N M : ℕ) (g : Lattice → ℝ) :
    (∑ z ∈ (Finset.Ico (0 : ℤ) (N : ℤ)).product (Finset.Ico 0 (M : ℤ)), g z) =
      ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range M, g ((k : ℤ), (l : ℤ)) := by
  calc
    _ = ∑ k ∈ Finset.Ico (0 : ℤ) (N : ℤ),
      ∑ l ∈ Finset.Ico (0 : ℤ) (M : ℤ), g (k, l) := Finset.sum_product _ _ _
    _ = ∑ k ∈ Finset.range N, ∑ l ∈ Finset.Ico (0 : ℤ) (M : ℤ), g ((k : ℤ), l) := by
      rw [sum_int_prefix]
    _ = _ := by apply Finset.sum_congr rfl; intro k _; exact sum_int_prefix M _

private theorem weighted_div_succ {α : Type*} (S : Finset α) (v w : α → ℝ)
    (m : ℝ) (n r : ℕ) :
    (∑ k ∈ S, (m - w k) * v k) / (n : ℝ)^(r + 1) =
      (m / (n : ℝ)) * ((∑ k ∈ S, v k) / (n : ℝ)^r) -
        (∑ k ∈ S, (w k / (n : ℝ)) * v k) / (n : ℝ)^r := by
  have hs : (∑ k ∈ S, (m - w k) * v k) =
      m * (∑ k ∈ S, v k) - ∑ k ∈ S, w k * v k := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  have hw : (∑ k ∈ S, (w k / (n : ℝ)) * v k) =
      (∑ k ∈ S, w k * v k) / (n : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hs, hw, pow_succ]
  ring

private theorem interval_difference (l u : ℕ) (h : l ≤ u) (g : ℤ → ℝ) :
    (∑ k ∈ Finset.Ico (l : ℤ) (u : ℤ), g k) =
      (∑ k ∈ Finset.Ico (0 : ℤ) (u : ℤ), g k) -
      ∑ k ∈ Finset.Ico (0 : ℤ) (l : ℤ), g k := by
  have hh : (l : ℤ) ≤ (u : ℤ) := by exact_mod_cast h
  have hu := Finset.Ico_union_Ico_eq_Ico (show (0 : ℤ) ≤ l by omega) hh
  have hs := Finset.sum_union (f := g) (Finset.Ico_disjoint_Ico_consecutive (0 : ℤ) l u)
  rw [hu] at hs
  linarith only [hs]

private theorem rectangle_difference (l₀ u₀ l₁ u₁ : ℕ) (h₀ : l₀ ≤ u₀) (h₁ : l₁ ≤ u₁)
    (g : Lattice → ℝ) :
    (∑ k ∈ (Finset.Ico (l₀ : ℤ) (u₀ : ℤ)).product
      (Finset.Ico (l₁ : ℤ) (u₁ : ℤ)), g k) =
    (∑ k ∈ (Finset.Ico (0 : ℤ) (u₀ : ℤ)).product (Finset.Ico 0 (u₁ : ℤ)), g k) -
    (∑ k ∈ (Finset.Ico (0 : ℤ) (l₀ : ℤ)).product (Finset.Ico 0 (u₁ : ℤ)), g k) -
    (∑ k ∈ (Finset.Ico (0 : ℤ) (u₀ : ℤ)).product (Finset.Ico 0 (l₁ : ℤ)), g k) +
    (∑ k ∈ (Finset.Ico (0 : ℤ) (l₀ : ℤ)).product (Finset.Ico 0 (l₁ : ℤ)), g k) := by
  have hs (A D : Finset ℤ) : (∑ k ∈ A.product D, g k) =
      ∑ k ∈ A, ∑ l ∈ D, g (k, l) := Finset.sum_product _ _ _
  simp only [hs]
  simp_rw [interval_difference l₁ u₁ h₁]
  rw [Finset.sum_sub_distrib, interval_difference l₀ u₀ h₀,
    interval_difference l₀ u₀ h₀]
  ring

/-- The canonical centered displacements for a lattice action have vanishing fixed-box averages, as in JR arXiv:1810.03580v3, Appendix B, Lemma B.6. -/
theorem ae_tendsto_fixed_box_centered_displacements_of_action
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω)
    (hzero : ∀ s : Ω, T 0 s = s)
    (hadd : ∀ (z w : Lattice) (s : Ω), T (z + w) s = T z (T w s))
    (hShift : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (B : Lattice → Lattice → Ω → ℝ)
    (hB : is_shift_covariant_cocycle P T B)
    (hInt : ∀ x y, Integrable (B x y) P)
    (a b : Fin 2 → ℝ) (ha : ∀ j, 0 ≤ a j) (hab : ∀ j, a j < b j) :
    let mΩ0 : MeasurableSpace Ω := inferInstance
    let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
    letI : MeasurableSpace Ω := mΩ0
    let u : Fin 2 → Ω → ℝ :=
      fun i => P[B 0 (finiteEdgeStep i) | I]
    let coord : Fin 2 → Lattice → ℤ := fun i x => if i = 0 then x.1 else x.2
    let Fbar : Lattice → Ω → ℝ := fun x s =>
      B 0 x s - ∑ i : Fin 2, u i s * ((coord i x : ℤ) : ℝ)
    let Q : Fin 2 → ℕ → Finset ℤ := fun j n =>
      Finset.Ico ((⌊(n : ℝ) * a j⌋₊ : ℕ) : ℤ)
        ((⌊(n : ℝ) * b j⌋₊ : ℕ) : ℤ)
    let X : Equiv.Perm (Fin 2) → (ℤ × ℤ) → Lattice :=
      fun σ k => k.1 • finiteEdgeStep (σ 0) + k.2 • finiteEdgeStep (σ 1)
    ∀ᵐ s ∂P,
      (∀ i : Fin 2, Tendsto (fun n : ℕ =>
        (∑ k ∈ Q 0 n, Fbar (k • finiteEdgeStep i) s) / (n : ℝ)^2)
        atTop (𝓝 0)) ∧
      (∀ σ : Equiv.Perm (Fin 2), Tendsto (fun n : ℕ =>
        (∑ k ∈ (Q 0 n).product (Q 1 n), Fbar (X σ k) s) / (n : ℝ)^3)
        atTop (𝓝 0)) := by
  classical
  let mΩ0 : MeasurableSpace Ω := inferInstance
  let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
  let : MeasurableSpace Ω := mΩ0
  let u : Fin 2 → Ω → ℝ := fun i => P[B 0 (finiteEdgeStep i) | I]
  let coord : Fin 2 → Lattice → ℤ := fun i x => if i = 0 then x.1 else x.2
  let Fbar : Lattice → Ω → ℝ := fun x s =>
    B 0 x s - ∑ i : Fin 2, u i s * ((coord i x : ℤ) : ℝ)
  let Q : Fin 2 → ℕ → Finset ℤ := fun j n =>
    Finset.Ico ((⌊(n : ℝ) * a j⌋₊ : ℕ) : ℤ) ((⌊(n : ℝ) * b j⌋₊ : ℕ) : ℤ)
  let X : Equiv.Perm (Fin 2) → Lattice → Lattice :=
    fun σ k => k.1 • finiteEdgeStep (σ 0) + k.2 • finiteEdgeStep (σ 1)
  let F : Fin 2 → Ω → ℝ := fun i s => B 0 (finiteEdgeStep i) s - u i s
  let Z : ℝ → ℕ → Finset ℤ := fun β n => Finset.Ico 0 ((⌊(n : ℝ) * β⌋₊ : ℕ) : ℤ)
  let R : (Fin 2 → ℝ) → ℕ → Finset Lattice := fun β n => (Z (β 0) n).product (Z (β 1) n)
  change ∀ᵐ s ∂P, (∀ i : Fin 2, Tendsto (fun n : ℕ =>
    (∑ k ∈ Q 0 n, Fbar (k • finiteEdgeStep i) s) / (n : ℝ)^2) atTop (𝓝 0)) ∧
    (∀ σ : Equiv.Perm (Fin 2), Tendsto (fun n : ℕ =>
      (∑ k ∈ (Q 0 n).product (Q 1 n), Fbar (X σ k) s) / (n : ℝ)^3) atTop (𝓝 0))
  -- Keep one full-action representative and transfer its equality under every signed shift.
  obtain ⟨U, hU, hUEq⟩ := exists_full_action_directional_drifts_condExp_of_action P T hzero hadd hShift B hB hInt
  have hMeans : ∀ᵐ s ∂P, ∀ (i : Fin 2) (z : Lattice), u i (T z s) = U i s := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro z
    have he : U i =ᵐ[P] u i := hUEq i
    have hp := (hShift z).quasiMeasurePreserving.ae he.symm
    filter_upwards [hp] with s hs
    exact hs.trans (hU.2 i z s)
  have hCov : ∀ᵐ s ∂P, ∀ x y z : Lattice,
      B (x + z) (y + z) s = B x y (T z s) := by
    apply ae_all_iff.mpr; intro x
    apply ae_all_iff.mpr; intro y
    exact ae_all_iff.mpr (fun z => hB.2.1 x y z)
  have hFloor (β : ℝ) (hβ : 0 ≤ β) : Tendsto
      (fun n : ℕ => (⌊(n : ℝ) * β⌋₊ : ℝ) / (n : ℝ)) atTop (𝓝 β) := by
    simpa only [Function.comp_def, mul_comm] using
      (tendsto_nat_floor_mul_div_atTop hβ).comp tendsto_natCast_atTop_atTop
  have hPositive (β : Fin 2 → ℝ) (hβ : ∀ j, 0 < β j) : ∀ᵐ s ∂P,
      (∀ i : Fin 2, Tendsto (fun n : ℕ =>
        (∑ k ∈ Z (β 0) n, Fbar (k • finiteEdgeStep i) s) / (n : ℝ)^2) atTop (𝓝 0)) ∧
      (∀ σ : Equiv.Perm (Fin 2), Tendsto (fun n : ℕ =>
        (∑ k ∈ R β n, Fbar (X σ k) s) / (n : ℝ)^3) atTop (𝓝 0)) := by
    have hAffine := ae_tendsto_affine_weighted_centered_edges_of_action P T hzero hadd hShift B hB hInt β hβ
    filter_upwards [hAffine, hMeans, hCov, hB.2.2] with s hs hm hc hadd
    have hu (i : Fin 2) : u i s = U i s := by simpa only [hzero] using hm i 0
    have hzero : Fbar 0 s = 0 := by
      have hz := hadd 0 0 0
      simp [Fbar, coord]
      linarith only [hz]
    let C : Lattice → Lattice → ℝ := fun x y => Fbar y s - Fbar x s
    have hC : is_additive C := by intro x y z; dsimp only [C]; ring
    let v : Fin 2 → Lattice → ℝ := fun i z => F i (T z s)
    have hedge (x : Lattice) (i : Fin 2) : C x (x + finiteEdgeStep i) = v i x := by
      have hc' : B x (x + finiteEdgeStep i) s = B 0 (finiteEdgeStep i) (T x s) := by
        simpa only [zero_add, add_comm (finiteEdgeStep i) x] using hc 0 (finiteEdgeStep i) x
      have hadd' := hadd 0 x (x + finiteEdgeStep i)
      have hm' : u i (T x s) = u i s := (hm i x).trans (hu i).symm
      fin_cases i <;>
        simp [C, Fbar, coord, Fin.sum_univ_two, finiteEdgeStep, v, F, hm'] at * <;>
        linarith only [hadd', hc']
    have hray (i : Fin 2) (n : ℕ) :
        (∑ k ∈ Z (β 0) n, Fbar (k • finiteEdgeStep i) s) =
        ∑ k ∈ Z (β 0) n, ((⌊(n : ℝ) * β 0⌋₊ : ℝ) - ((k + 1 : ℤ) : ℝ)) *
          v i (k • finiteEdgeStep i) := by
      dsimp only [Z]
      rw [sum_int_prefix, sum_int_prefix]
      have h := sum_additive_ray_prefix_eq_weighted_edges C hC v hedge 0 i ⌊(n : ℝ) * β 0⌋₊
      simpa [C, hzero, Int.cast_add, sub_add_eq_sub_sub] using h
    have hRayLimit (i : Fin 2) : Tendsto (fun n : ℕ =>
        (∑ k ∈ Z (β 0) n, Fbar (k • finiteEdgeStep i) s) / (n : ℝ)^2) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ =>
          (∑ k ∈ Z (β 0) n, v i (k • finiteEdgeStep i)) / (n : ℝ)) atTop (𝓝 0) := by
        simpa only [one_mul, zero_mul, add_zero, v] using hs.1 i 1 0
      have h1 : Tendsto (fun n : ℕ =>
          (∑ k ∈ Z (β 0) n, (((k + 1 : ℤ) : ℝ) / (n : ℝ)) *
            v i (k • finiteEdgeStep i)) / (n : ℝ)) atTop (𝓝 0) := by
        simpa only [one_mul, zero_add, v] using hs.1 i 0 1
      have hh := ((hFloor (β 0) (hβ 0).le).mul h0).sub h1
      simp only [mul_zero, sub_zero] at hh
      apply hh.congr'
      filter_upwards [] with n
      rw [hray]
      simpa only [pow_one] using (weighted_div_succ (Z (β 0) n) (fun k => v i (k • finiteEdgeStep i))
        (fun k => ((k + 1 : ℤ) : ℝ)) (⌊(n : ℝ) * β 0⌋₊ : ℝ) n 1).symm
    refine ⟨hRayLimit, ?_⟩
    intro σ
    have hbox (n : ℕ) :
        (∑ k ∈ R β n, Fbar (X σ k) s) =
        (⌊(n : ℝ) * β 1⌋₊ : ℝ) *
          (∑ k ∈ Z (β 0) n, Fbar (k • finiteEdgeStep (σ 0)) s) +
        ∑ k ∈ R β n, ((⌊(n : ℝ) * β 1⌋₊ : ℝ) - ((k.2 + 1 : ℤ) : ℝ)) * v (σ 1) (X σ k) := by
      dsimp only [R, Z]
      rw [sum_int_rectangle, sum_int_prefix, sum_int_rectangle]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      let z : Lattice := (k : ℤ) • finiteEdgeStep (σ 0)
      have ht := sum_additive_ray_prefix_eq_weighted_edges C hC v hedge z (σ 1) ⌊(n : ℝ) * β 1⌋₊
      have hx (l : ℕ) : Fbar (X σ ((k : ℤ), (l : ℤ))) s =
          Fbar z s + C z (z + (l : ℤ) • finiteEdgeStep (σ 1)) := by
        dsimp only [X, z, C]
        ring
      simp_rw [hx]
      rw [Finset.sum_add_distrib, ht]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro l _
      simp only [X, z, Int.cast_add, Int.cast_natCast, Int.cast_one]
      ring
    have h0 : Tendsto (fun n : ℕ => (∑ k ∈ R β n, v (σ 1) (X σ k)) / (n : ℝ)^2)
        atTop (𝓝 0) := by
      simpa only [one_mul, zero_mul, add_zero, v] using hs.2 σ 1 1 0
    have h1 : Tendsto (fun n : ℕ =>
        (∑ k ∈ R β n, (((k.2 + 1 : ℤ) : ℝ) / (n : ℝ)) * v (σ 1) (X σ k)) /
          (n : ℝ)^2) atTop (𝓝 0) := by
      simpa only [one_mul, zero_add, v, show (1 : Fin 2) ≠ 0 by decide, ite_false] using hs.2 σ 1 0 1
    have hh := ((hFloor (β 1) (hβ 1).le).mul (hRayLimit (σ 0))).add
      (((hFloor (β 1) (hβ 1).le).mul h0).sub h1)
    simp only [mul_zero, sub_zero, add_zero] at hh
    apply hh.congr'
    filter_upwards [] with n
    rw [hbox, add_div, weighted_div_succ (R β n) (fun k => v (σ 1) (X σ k))
      (fun k => ((k.2 + 1 : ℤ) : ℝ)) (⌊(n : ℝ) * β 1⌋₊ : ℝ) n 2]
    congr 1
    ring
  -- Zero endpoints are empty; the affine parent is called only at positive aspects.
  have hRay (β : ℝ) (hβ : 0 ≤ β) : ∀ᵐ s ∂P, ∀ i : Fin 2,
      Tendsto (fun n : ℕ => (∑ k ∈ Z β n, Fbar (k • finiteEdgeStep i) s) /
        (n : ℝ)^2) atTop (𝓝 0) := by
    by_cases hz : β = 0
    · subst β
      filter_upwards [] with s i
      simp [Z]
    · let β' : Fin 2 → ℝ := fun j => if j = 0 then β else 1
      have hp : ∀ j, 0 < β' j := by intro j; dsimp [β']; split_ifs <;> positivity
      filter_upwards [hPositive β' hp] with s hs
      simpa only [β', ite_true] using hs.1
  have hBox (β : Fin 2 → ℝ) (hβ : ∀ j, 0 ≤ β j) : ∀ᵐ s ∂P, ∀ σ : Equiv.Perm (Fin 2),
      Tendsto (fun n : ℕ => (∑ k ∈ R β n, Fbar (X σ k) s) / (n : ℝ)^3) atTop (𝓝 0) := by
    by_cases h0 : β 0 = 0
    · filter_upwards [] with s σ
      simp [R, Z, h0]
    by_cases h1 : β 1 = 0
    · filter_upwards [] with s σ
      simp [R, Z, h1]
    have hp : ∀ j, 0 < β j := by
      intro j; fin_cases j
      · exact lt_of_le_of_ne (hβ 0) (Ne.symm h0)
      · exact lt_of_le_of_ne (hβ 1) (Ne.symm h1)
    filter_upwards [hPositive β hp] with s hs
    exact hs.2
  let corner : Fin 2 × Fin 2 → Fin 2 → ℝ := fun p j =>
    if (if j = 0 then p.1 else p.2) = 0 then a j else b j
  have hcorner (p : Fin 2 × Fin 2) : ∀ j, 0 ≤ corner p j := by
    intro j
    change 0 ≤ if (if j = 0 then p.1 else p.2) = 0 then a j else b j
    have ha' := ha j
    have hb' := (ha j).trans (hab j).le
    split_ifs <;> assumption
  have hCorners := ae_all_iff.mpr (fun p : Fin 2 × Fin 2 => hBox (corner p) (hcorner p))
  filter_upwards [hRay (a 0) (ha 0), hRay (b 0) ((ha 0).trans (hab 0).le), hCorners]
    with s hA hB' hCorners'
  have hOrder (j : Fin 2) (n : ℕ) : ⌊(n : ℝ) * a j⌋₊ ≤ ⌊(n : ℝ) * b j⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left (hab j).le (Nat.cast_nonneg n))
  refine ⟨?_, ?_⟩
  · intro i
    have hh := (hB' i).sub (hA i)
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [] with n
    rw [← sub_div]
    exact congrArg (fun t : ℝ => t / (n : ℝ)^2)
      (interval_difference _ _ (hOrder 0 n) (fun k => Fbar (k • finiteEdgeStep i) s)).symm
  · intro σ
    have hh := (((hCorners' (1, 1) σ).sub (hCorners' (0, 1) σ)).sub
      (hCorners' (1, 0) σ)).add (hCorners' (0, 0) σ)
    simp only [sub_zero, add_zero] at hh
    apply hh.congr'
    filter_upwards [] with n
    simp only [corner, R, Z, ite_true]
    rw [← sub_div, ← sub_div, ← add_div]
    exact congrArg (fun t : ℝ => t / (n : ℝ)^3)
      (rectangle_difference _ _ _ _ (hOrder 0 n) (hOrder 1 n) (fun k => Fbar (X σ k) s)).symm

end LPP.Busemann
