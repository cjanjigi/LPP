/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.SelectedGridPaths.Family

/-! The exact fine and coarse labels that supply the selected path weights. -/

public section

namespace LPPDifferentiability.SelectedGridPaths
open StairGeometry
open scoped Classical

/-- An actual fine piece belongs to the family at its source grid cell. -/
theorem fineChoice_mem {a cstar A R C₁ : ℝ} {m : ℕ → ℕ} {k K₁ K₃ j : ℕ}
    {b : Lattice → Bool} {u : Lattice} {I : ℤ} {q : PackedPath}
    (hu : u ∈ workingRegion a A R C₁ m k) (hj : j ∈ scales (m k))
    (hI : I ∈ gridLevels A (m k) j)
    (hfine : (mesh (m k) j : ℝ) < 8 * (cstar * ((j : ℝ) ^ 2 * (width k j : ℝ))))
    (hq : fineChoice (workingRegion a A R C₁ m k) b a u I (mesh (m k) j) = some q) :
    q ∈ pathFamily a cstar A R C₁ m k K₁ K₃ b := by
  unfold pathFamily
  refine Finset.mem_biUnion.mpr ⟨u, mem_regionSites.mpr hu,
    Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_biUnion.mpr ⟨I, hI, ?_⟩⟩⟩
  rw [ite_eq_left hfine]
  exact Option.mem_toFinset.mpr hq

/-- The selected path from the actual arrival target, or either selected
piece at the actual merge start, belongs to the family at the fixed block. -/
theorem coarseChoice_mem {a cstar A R C₁ : ℝ} {m : ℕ → ℕ} {k K₁ K₃ j : ℕ}
    {b : Lattice → Bool} {u v : Lattice} {I h : ℤ} {q : PackedPath}
    (ν : Fin (j ^ 2))
    (hu : u ∈ workingRegion a A R C₁ m k) (hj : j ∈ scales (m k))
    (hI : I ∈ gridLevels A (m k) j) (hh : h ∈ gridBins R k j)
    (hr : (h : ℝ) * width k j ≤ transverse a u ∧
      transverse a u < ((h : ℝ) + 1) * width k j)
    (hcoarse : 8 * (cstar * ((j : ℝ) ^ 2 * (width k j : ℝ))) ≤ (mesh (m k) j : ℝ)) :
    let Q := workingRegion a A R C₁ m k
    let w := width k j
    let l := mesh (m k) j
    let m' := ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊
    let r := trimLength (slopeCutoff a) K₁ K₃
    let c := coarseCrossingCentre a h w I m' (ν.val + 1)
    let left := I + (m' : ℤ)
    let right := I + (l : ℤ) - (m' : ℤ)
    left ≤ lev v → lev v ≤ right → |transverse a v - transverse a c| ≤ 8 * (w : ℝ) →
    ((lev v ≤ left + (r : ℤ) ∧
      arrivalChoice Q b a (arrivalBoxSize (slopeCutoff a) K₁ K₃) u v I = some q) ∨
      (right - (r : ℤ) ≤ lev v ∧
        q ∈ mergeChoices Q b a (deviationBound K₁ K₃) u v I (I + (l : ℤ)))) →
    q ∈ pathFamily a cstar A R C₁ m k K₁ K₃ b := by
  classical
  intro Q w l m' r c left right hleft hright hband hcase
  unfold pathFamily
  refine Finset.mem_biUnion.mpr ⟨u, mem_regionSites.mpr hu,
    Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_biUnion.mpr ⟨I, hI, ?_⟩⟩⟩
  rw [ite_eq_right (not_lt.mpr hcoarse)]
  refine Finset.mem_biUnion.mpr ⟨h, Finset.mem_filter.mpr ⟨hh, hr⟩,
    Finset.mem_biUnion.mpr ⟨ν, Finset.mem_univ _, Finset.mem_union.mpr ?_⟩⟩
  rcases hcase with ⟨hα, hpath⟩ | ⟨hβ, hpath⟩
  · exact Or.inl (Finset.mem_biUnion.mpr ⟨v, Finset.mem_filter.mpr
      ⟨(trimWindow_spec a w left r c).1 v |>.mpr ⟨hleft, hα, hband⟩, hright⟩,
          Option.mem_toFinset.mpr hpath⟩)
  · have he : right - (r : ℤ) + (r : ℤ) = right := sub_add_cancel _ _
    exact Or.inr (Finset.mem_biUnion.mpr ⟨v, Finset.mem_filter.mpr
      ⟨(trimWindow_spec a w (right - (r : ℤ)) r c).1 v |>.mpr
        ⟨hβ, he.symm ▸ hright, hband⟩, hleft⟩, hpath⟩)

end LPPDifferentiability.SelectedGridPaths
