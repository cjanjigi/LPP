/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.SelectedGridPaths.Membership
public import Differentiability.FinalDraft.Grid.GeneralEvents
public import Differentiability.Model.Paths.GridCoarseGeneralArrival
import LPP_Foundations.Model.Paths.Level
import Mathlib.Tactic

/-! A coarse grid cell with the fixed rounded trial and its trimming windows. -/

@[expose] public section

namespace LPPDifferentiability.SelectedGridPaths
open StairGeometry Set
open scoped Classical

/-- The source grid labels at a coarse trial for the staircase through `u`. -/
structure CoarseBlock (a cstar A R C₁ : ℝ) (m : ℕ → ℕ) (k : ℕ) (u : Lattice) where
  j : ℕ
  I : ℤ
  h : ℤ
  ν : Fin (j ^ 2)
  site_mem : u ∈ workingRegion a A R C₁ m k
  scale_mem : j ∈ scales (m k)
  level_mem : I ∈ gridLevels A (m k) j
  bin_mem : h ∈ gridBins R k j
  transverse_mem : (h : ℝ) * width k j ≤ transverse a u ∧
    transverse a u < ((h : ℝ) + 1) * width k j
  coarse : 8 * (cstar * ((j : ℝ) ^ 2 * (width k j : ℝ))) ≤ (mesh (m k) j : ℝ)

namespace CoarseBlock

variable {a cstar A R C₁ : ℝ} {m : ℕ → ℕ} {k : ℕ} {u : Lattice}

abbrev ell (C : CoarseBlock a cstar A R C₁ m k u) := mesh (m k) C.j
abbrev w (C : CoarseBlock a cstar A R C₁ m k u) := width k C.j
abbrev scaleFactor (C : CoarseBlock a cstar A R C₁ m k u) : ℝ := (C.j : ℝ) ^ 2 * (C.w : ℝ)
noncomputable abbrev inset (C : CoarseBlock a cstar A R C₁ m k u) : ℕ := ⌈cstar * C.scaleFactor⌉₊
noncomputable abbrev centre (C : CoarseBlock a cstar A R C₁ m k u) : Lattice :=
  coarseCrossingCentre a C.h C.w C.I C.inset (C.ν.val + 1)
abbrev upperLevel (C : CoarseBlock a cstar A R C₁ m k u) : ℤ := C.I + (C.ell : ℤ)
abbrev sites (C : CoarseBlock a cstar A R C₁ m k u) : Set Lattice :=
  gridCrossingBlock a C.w C.I C.ell C.inset C.centre
abbrev cappedTrial (C : CoarseBlock a cstar A R C₁ m k u) (G K : ℝ) : Set Environment :=
  gridCappedTrial a G K C.I C.h C.ell C.inset C.j C.w C.ν

/-- A selected arrival at a vertex of the initial trimming window is in `P_k`. -/
theorem arrival_mem (C : CoarseBlock a cstar A R C₁ m k u) {K₁ K₃ : ℕ}
    {b : Lattice → Bool} {v : Lattice} {q : PackedPath}
    (hv : v ∈ C.sites)
    (hwin : lev v ≤ C.I + (C.inset : ℤ) + (trimLength (slopeCutoff a) K₁ K₃ : ℤ))
    (hq : arrivalChoice (workingRegion a A R C₁ m k) b a
      (arrivalBoxSize (slopeCutoff a) K₁ K₃) u v C.I = some q) :
    q ∈ pathFamily a cstar A R C₁ m k K₁ K₃ b :=
  coarseChoice_mem C.ν C.site_mem C.scale_mem C.level_mem C.bin_mem C.transverse_mem C.coarse
    hv.1 hv.2.1 hv.2.2 (Or.inl ⟨hwin, hq⟩)

/-- The selected pieces from the terminal trimming window are in `P_k`. -/
theorem merge_mem (C : CoarseBlock a cstar A R C₁ m k u) {K₁ K₃ : ℕ}
    {b : Lattice → Bool} {v : Lattice} {q : PackedPath}
    (hv : v ∈ C.sites)
    (hwin : C.upperLevel - (C.inset : ℤ) - (trimLength (slopeCutoff a) K₁ K₃ : ℤ) ≤ lev v)
    (hq : q ∈ mergeChoices (workingRegion a A R C₁ m k) b a
      (deviationBound K₁ K₃) u v C.I C.upperLevel) :
    q ∈ pathFamily a cstar A R C₁ m k K₁ K₃ b :=
  coarseChoice_mem C.ν C.site_mem C.scale_mem C.level_mem C.bin_mem C.transverse_mem C.coarse
    hv.1 hv.2.1 hv.2.2 (Or.inr ⟨hwin, hq⟩)

/-- The cap and crossing share the exact fixed rounded block. Each crossing
vertex lies in that block, and the path has the source length and weight. -/
theorem exists_capped_crossing (C : CoarseBlock a cstar A R C₁ m k u)
    {ω : Environment} {G K : ℝ} (h : ω ∈ C.cappedTrial G K)
    (hlen : 2 * C.inset ≤ C.ell) :
    ∃ (z : Lattice) (d : ℕ × ℕ) (p : Path z d),
      lev z = C.I + (C.inset : ℤ) ∧ d.1 + d.2 = C.ell - 2 * C.inset ∧
      (∀ i, p.vertex i ∈ C.sites) ∧ (∀ i, ω (p.vertex i) ≤ (C.w : ℝ)) ∧
      G * ((C.ell - 2 * C.inset : ℕ) : ℝ) - K * (C.w : ℝ) < pathWeight ω p := by
  obtain ⟨⟨z, d, p, hz, hd, hb, hw⟩, hcap⟩ := h
  have hv (i : Fin (d.1 + d.2 + 1)) : p.vertex i ∈ C.sites := by
    have hl := p.level i
    have hi := i.isLt
    change C.I + (C.inset : ℤ) ≤ (p.vertex i).1 + (p.vertex i).2 ∧
      (p.vertex i).1 + (p.vertex i).2 ≤ C.I + (C.ell : ℤ) - (C.inset : ℤ) ∧ _
    exact ⟨by omega, by omega, hb i⟩
  exact ⟨z, d, p, hz, hd, hv, fun i => hcap _ (hv i), hw⟩

end CoarseBlock
end LPPDifferentiability.SelectedGridPaths
