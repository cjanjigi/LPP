/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Frozen.Model.Quadrant
public import Busemann.Finite.RestrictedNortheastPassage
public import ProbabilityBasics.Analysis.SegmentGridMaximum
import LPP_Foundations.Model.LastPassage.Swap
import Mathlib.Tactic

/-! Deterministic error estimates for the restricted maxima in GRS Lemma 6.4. -/

@[expose] public section

open LPPDifferentiability Filter
open scoped NNReal Topology

namespace LPP.Busemann

/-- A uniform shape estimate outside a finite triangle controls every prefix
inside a growing triangle. This includes bounded and zero prefixes in the
finite exit formula of GRS arXiv:1510.00859v2, Lemma 6.4. -/
theorem uniform_passage_error_on_triangles
    (ω : Environment) (g : Quadrant → ℝ) (x : Lattice)
    (hshape : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ e : ℕ × ℕ,
      N ≤ e.1 + e.2 →
      |lastPassage ω x e - g ((e.1 : ℝ≥0), (e.2 : ℝ≥0))| ≤
        ε * ((e.1 + e.2 : ℕ) : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ e : ℕ × ℕ,
      e.1 + e.2 ≤ m →
      |lastPassage ω x e - g ((e.1 : ℝ≥0), (e.2 : ℝ≥0))| ≤ ε * (m : ℝ) := by
  classical
  intro ε hε
  obtain ⟨N, hN⟩ := hshape (ε / 2) (by positivity)
  let S := (Finset.range (N + 1)).product (Finset.range (N + 1))
  have hS : S.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    simp [S]
  let A := S.sup' hS (fun e => |lastPassage ω x e - g ((e.1 : ℝ≥0), (e.2 : ℝ≥0))|)
  obtain ⟨K, hK⟩ := exists_nat_gt (A / (ε / 2))
  have hA : A < (K : ℝ) * (ε / 2) := (div_lt_iff₀ (by positivity)).mp hK
  refine ⟨K, ?_⟩
  intro m hm e he
  have hKm : (K : ℝ) ≤ m := by exact_mod_cast hm
  have hem : ((e.1 + e.2 : ℕ) : ℝ) ≤ m := by exact_mod_cast he
  by_cases hlarge : N ≤ e.1 + e.2
  · have hbound := hN e hlarge
    nlinarith only [hbound, hem, hε]
  · have heS : e ∈ S := by
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩
    have hbound : |lastPassage ω x e - g ((e.1 : ℝ≥0), (e.2 : ℝ≥0))| ≤ A :=
      Finset.le_sup' (fun e => |lastPassage ω x e - g ((e.1 : ℝ≥0), (e.2 : ℝ≥0))|) heS
    have hmnonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith only [hbound, hA, hKm, hε, hmnonneg]

private theorem shape_normalization (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c * z.1, c * z.2) = (c : ℝ) * g z)
    (m : ℕ) (hm : 0 < m) (e : ℕ × ℕ) :
    g ((e.1 : ℝ≥0), (e.2 : ℝ≥0)) / (m : ℝ) =
      g (Real.toNNReal ((e.1 : ℝ) / m), Real.toNNReal ((e.2 : ℝ) / m)) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  let z : Quadrant :=
    (Real.toNNReal ((e.1 : ℝ) / m), Real.toNNReal ((e.2 : ℝ) / m))
  have hscale : ((m : ℝ≥0) * z.1, (m : ℝ≥0) * z.2) =
      ((e.1 : ℝ≥0), (e.2 : ℝ≥0)) := by
    apply Prod.ext <;> apply NNReal.eq
    · change (m : ℝ) * (Real.toNNReal ((e.1 : ℝ) / m) : ℝ) = e.1
      rw [Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) hmR.le)]
      field_simp [hmR.ne']
    · change (m : ℝ) * (Real.toNNReal ((e.2 : ℝ) / m) : ℝ) = e.2
      rw [Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) hmR.le)]
      field_simp [hmR.ne']
  have hh := hhom (m : ℝ≥0) z
  rw [hscale] at hh
  change g ((e.1 : ℝ≥0), (e.2 : ℝ≥0)) = (m : ℝ) * g z at hh
  rw [hh]
  exact mul_div_cancel_left₀ _ hmR.ne'

private theorem finite_sup_div_error {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f F : ι → ℝ) (m δ : ℝ) (hm : 0 < m)
    (herror : ∀ i ∈ S, |f i / m - F i| ≤ δ) :
    |S.sup' hS f / m - S.sup' hS F| ≤ δ := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' (s := S) (H := hS) f
  obtain ⟨j, hj, hMax⟩ := Finset.exists_mem_eq_sup' (s := S) (H := hS) F
  have hup := (abs_le.mp (herror i hi)).2
  have hlo := (abs_le.mp (herror j hj)).1
  have hiBound := Finset.le_sup' F hi
  have hjBound := div_le_div_of_nonneg_right (Finset.le_sup' f hj) hm.le
  rw [← hmax] at hup
  rw [← hMax] at hlo
  exact abs_le.mpr ⟨by linarith only [hlo, hjBound], by linarith only [hup, hiBound]⟩

private theorem abs_three (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| :=
  (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))

private theorem exit_summand_error
    (ω : Environment) (C : Lattice → Lattice → ℝ) (hC : is_additive C)
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c * z.1, c * z.2) = (c : ℝ) * g z)
    (x : Lattice) (m : ℕ) (hm : 0 < m) (a b ε : ℝ)
    (hpass : ∀ e : ℕ × ℕ, e.1 + e.2 ≤ m →
      |lastPassage ω x e - g ((e.1 : ℝ≥0), (e.2 : ℝ≥0))| ≤ ε * (m : ℝ))
    (hcoc : ∀ e : ℕ × ℕ, e.1 + e.2 ≤ m →
      |C x (x + ((e.1 : ℤ), (e.2 : ℤ))) -
        (a * (e.1 : ℝ) + b * (e.2 : ℝ))| ≤ ε * (m : ℝ))
    (hweight : ∀ e : ℕ × ℕ, e.1 + e.2 ≤ m →
      |ω (x + ((e.1 : ℤ), (e.2 : ℤ)))| ≤ ε * (m : ℝ))
    (e f d : ℕ × ℕ) (he : e.1 + e.2 ≤ m) (hf : f.1 + f.2 ≤ m)
    (hd : d.1 + d.2 ≤ m) :
    |(lastPassage ω x e + ω (x + ((e.1 : ℤ), (e.2 : ℤ))) +
        C (x + ((f.1 : ℤ), (f.2 : ℤ))) (x + ((d.1 : ℤ), (d.2 : ℤ)))) / (m : ℝ) -
      (g (Real.toNNReal ((e.1 : ℝ) / m), Real.toNNReal ((e.2 : ℝ) / m)) +
        ((a * (d.1 : ℝ) + b * (d.2 : ℝ)) -
          (a * (f.1 : ℝ) + b * (f.2 : ℝ))) / (m : ℝ))| ≤ 4 * ε := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hterminal := hcoc d hd
  have hentry := hcoc f hf
  have hadd := hC x (x + ((f.1 : ℤ), (f.2 : ℤ))) (x + ((d.1 : ℤ), (d.2 : ℤ)))
  have htail : |C (x + ((f.1 : ℤ), (f.2 : ℤ))) (x + ((d.1 : ℤ), (d.2 : ℤ))) -
      ((a * (d.1 : ℝ) + b * (d.2 : ℝ)) -
        (a * (f.1 : ℝ) + b * (f.2 : ℝ)))| ≤ 2 * ε * (m : ℝ) := by
    calc
      _ = |(C x (x + ((d.1 : ℤ), (d.2 : ℤ))) -
          (a * (d.1 : ℝ) + b * (d.2 : ℝ))) -
        (C x (x + ((f.1 : ℤ), (f.2 : ℤ))) -
          (a * (f.1 : ℝ) + b * (f.2 : ℝ)))| := by congr 1; linarith only [hadd]
      _ ≤ _ := abs_sub _ _
      _ ≤ _ := by linarith only [hterminal, hentry]
  have hp := hpass e he
  have hw := hweight e he
  rw [← shape_normalization g hhom m hm e, ← add_div, ← sub_div,
    abs_div, abs_of_pos hmR]
  apply (div_le_iff₀ hmR).mpr
  have htriangle := abs_three
    (lastPassage ω x e - g ((e.1 : ℝ≥0), (e.2 : ℝ≥0)))
    (ω (x + ((e.1 : ℤ), (e.2 : ℤ))))
    (C (x + ((f.1 : ℤ), (f.2 : ℤ))) (x + ((d.1 : ℤ), (d.2 : ℤ))) -
      ((a * (d.1 : ℝ) + b * (d.2 : ℝ)) - (a * (f.1 : ℝ) + b * (f.2 : ℝ))))
  have hscalar : lastPassage ω x e + ω (x + ((e.1 : ℤ), (e.2 : ℤ))) +
      C (x + ((f.1 : ℤ), (f.2 : ℤ))) (x + ((d.1 : ℤ), (d.2 : ℤ))) -
      (g ((e.1 : ℝ≥0), (e.2 : ℝ≥0)) +
        ((a * (d.1 : ℝ) + b * (d.2 : ℝ)) - (a * (f.1 : ℝ) + b * (f.2 : ℝ)))) =
      (lastPassage ω x e - g ((e.1 : ℝ≥0), (e.2 : ℝ≥0))) +
        ω (x + ((e.1 : ℤ), (e.2 : ℤ))) +
        (C (x + ((f.1 : ℤ), (f.2 : ℤ))) (x + ((d.1 : ℤ), (d.2 : ℤ))) -
          ((a * (d.1 : ℝ) + b * (d.2 : ℝ)) - (a * (f.1 : ℝ) + b * (f.2 : ℝ)))) := by ring
  rw [hscalar]
  linarith only [htriangle, hp, hw, htail]

/-- Uniform ordinary, cocycle and single-site errors control both literal
restricted maxima by their deterministic exit grids (GRS Lemma 6.4). The
native theorem supplies these finite error bounds from its actual events. -/
theorem restrictedNE_grid_error
    (ω : Environment) (C : Lattice → Lattice → ℝ) (hC : is_additive C)
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c * z.1, c * z.2) = (c : ℝ) * g z)
    (x : Lattice) (d : ℕ × ℕ) (hd1 : 0 < d.1) (hd2 : 0 < d.2) (a b ε : ℝ)
    (hpass : ∀ e : ℕ × ℕ, e.1 + e.2 ≤ d.1 + d.2 →
      |lastPassage ω x e - g ((e.1 : ℝ≥0), (e.2 : ℝ≥0))| ≤ ε * ((d.1 + d.2 : ℕ) : ℝ))
    (hcoc : ∀ e : ℕ × ℕ, e.1 + e.2 ≤ d.1 + d.2 →
      |C x (x + ((e.1 : ℤ), (e.2 : ℤ))) -
        (a * (e.1 : ℝ) + b * (e.2 : ℝ))| ≤ ε * ((d.1 + d.2 : ℕ) : ℝ))
    (hweight : ∀ e : ℕ × ℕ, e.1 + e.2 ≤ d.1 + d.2 →
      |ω (x + ((e.1 : ℤ), (e.2 : ℤ)))| ≤ ε * ((d.1 + d.2 : ℕ) : ℝ)) :
    let m : ℝ := (d.1 + d.2 : ℕ)
    |restrictedNE ω C x d 0 (by simpa using hd1) / m -
      (Finset.Icc 1 d.1).sup' (Finset.nonempty_Icc.mpr hd1)
        (fun ℓ => g (Real.toNNReal (((d.1 - ℓ : ℕ) : ℝ) / m),
          Real.toNNReal (((d.2 - 1 : ℕ) : ℝ) / m)) + a * (ℓ : ℝ) / m)| ≤ 4 * ε ∧
    |restrictedNE ω C x d 1 (by simpa using hd2) / m -
      (Finset.Icc 1 d.2).sup' (Finset.nonempty_Icc.mpr hd2)
        (fun ℓ => g (Real.toNNReal (((d.1 - 1 : ℕ) : ℝ) / m),
          Real.toNNReal (((d.2 - ℓ : ℕ) : ℝ) / m)) + b * (ℓ : ℝ) / m)| ≤ 4 * ε := by
  let m : ℕ := d.1 + d.2
  have hm : 0 < m := by dsimp [m]; omega
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨hNorth, hEast⟩ := restrictedNE_eq_exitMax ω C hC x d hd1 hd2
  constructor
  · rw [hNorth]
    apply finite_sup_div_error _ _ _ _ _ _ hmR
    intro ℓ hℓ
    have hℓle := (Finset.mem_Icc.mp hℓ).2
    have hℓpos := (Finset.mem_Icc.mp hℓ).1
    have hp : x + (((d.1 - ℓ : ℕ) : ℤ), ((d.2 - 1 : ℕ) : ℤ)) =
        x + ((d.1 : ℤ), (d.2 : ℤ)) - ((ℓ : ℤ), 1) := by
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> omega
    have he : x + (((d.1 - ℓ : ℕ) : ℤ), (d.2 : ℤ)) =
        x + ((d.1 : ℤ), (d.2 : ℤ)) - ((ℓ : ℤ), 0) := by
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> omega
    have hs := exit_summand_error ω C hC g hhom x m hm a b ε hpass hcoc hweight
      (d.1 - ℓ, d.2 - 1) (d.1 - ℓ, d.2) d (by dsimp [m]; omega)
      (by dsimp [m]; omega) (le_refl _)
    have hlinear : (a * (d.1 : ℝ) + b * (d.2 : ℝ)) -
        (a * ((d.1 - ℓ : ℕ) : ℝ) + b * (d.2 : ℝ)) = a * (ℓ : ℝ) := by
      rw [Nat.cast_sub hℓle]
      ring
    simpa only [hp, he, hlinear] using hs
  · rw [hEast]
    apply finite_sup_div_error _ _ _ _ _ _ hmR
    intro ℓ hℓ
    have hℓle := (Finset.mem_Icc.mp hℓ).2
    have hℓpos := (Finset.mem_Icc.mp hℓ).1
    have hp : x + (((d.1 - 1 : ℕ) : ℤ), ((d.2 - ℓ : ℕ) : ℤ)) =
        x + ((d.1 : ℤ), (d.2 : ℤ)) - (1, (ℓ : ℤ)) := by
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> omega
    have he : x + ((d.1 : ℤ), ((d.2 - ℓ : ℕ) : ℤ)) =
        x + ((d.1 : ℤ), (d.2 : ℤ)) - (0, (ℓ : ℤ)) := by
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> omega
    have hs := exit_summand_error ω C hC g hhom x m hm a b ε hpass hcoc hweight
      (d.1 - 1, d.2 - ℓ) (d.1, d.2 - ℓ) d (by dsimp [m]; omega)
      (by dsimp [m]; omega) (le_refl _)
    have hlinear : (a * (d.1 : ℝ) + b * (d.2 : ℝ)) -
        (a * (d.1 : ℝ) + b * ((d.2 - ℓ : ℕ) : ℝ)) = b * (ℓ : ℝ) := by
      rw [Nat.cast_sub hℓle]
      ring
    simpa only [hp, he, hlinear] using hs

end LPP.Busemann
