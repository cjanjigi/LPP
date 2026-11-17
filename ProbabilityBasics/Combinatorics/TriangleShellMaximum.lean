/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# Finite maxima over integer triangles and shells

The maximum of a real function on the closed nonnegative triangle through
level `n` is the maximum of its values on the shells from level zero through
`n`. This elementary identity extends the shell estimate of
Janjigian--Rassoul-Agha, Appendix B, Theorem B.3 to filled triangles.
-/

@[expose] public section

namespace ProbabilityBasics

/-- The maximum on the nonnegative integer triangle through `n` equals the
maximum of the shell maxima through level `n`. This elementary extension is
used after Janjigian--Rassoul-Agha, Appendix B, Theorem B.3. -/
theorem sup_triangle_eq_sup_shell_prefix (f : (ℤ × ℤ) → ℝ) (n : ℕ) :
    let Δ : ℕ → Finset (ℤ × ℤ) := fun r => insert 0
      (((Finset.Icc (0 : ℤ) (r : ℤ)).product
        (Finset.Icc (0 : ℤ) (r : ℤ))).filter
          (fun x => x.1 + x.2 ≤ (r : ℤ)))
    let S : ℕ → Finset (ℤ × ℤ) := fun r => insert ((r : ℤ), 0)
      (((Finset.Icc (0 : ℤ) (r : ℤ)).product
        (Finset.Icc (0 : ℤ) (r : ℤ))).filter
          (fun x => x.1 + x.2 = (r : ℤ)))
    (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _) f =
      (Finset.range (n + 1)).sup'
        ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
        (fun r => (S r).sup' (by dsimp [S]; exact Finset.insert_nonempty _ _) f) := by
  classical
  let Δ : ℕ → Finset (ℤ × ℤ) := fun r => insert 0
    (((Finset.Icc (0 : ℤ) (r : ℤ)).product
      (Finset.Icc (0 : ℤ) (r : ℤ))).filter
        (fun x => x.1 + x.2 ≤ (r : ℤ)))
  let S : ℕ → Finset (ℤ × ℤ) := fun r => insert ((r : ℤ), 0)
    (((Finset.Icc (0 : ℤ) (r : ℤ)).product
      (Finset.Icc (0 : ℤ) (r : ℤ))).filter
        (fun x => x.1 + x.2 = (r : ℤ)))
  change
    (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _) f =
      (Finset.range (n + 1)).sup'
        ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
        (fun r => (S r).sup' (by dsimp [S]; exact Finset.insert_nonempty _ _) f)

  -- The inserted point is already in the filtered triangle.
  have hZeroInTriangleFilter (r : ℕ) :
      (0 : ℤ × ℤ) ∈
        (((Finset.Icc (0 : ℤ) (r : ℤ)).product
          (Finset.Icc (0 : ℤ) (r : ℤ))).filter
            (fun x => x.1 + x.2 ≤ (r : ℤ))) := by
    simp

  -- The inserted shell endpoint is already in the equal-sum filter.
  have hShellWitnessInFilter (r : ℕ) :
      ((r : ℤ), 0) ∈
        (((Finset.Icc (0 : ℤ) (r : ℤ)).product
          (Finset.Icc (0 : ℤ) (r : ℤ))).filter
            (fun x => x.1 + x.2 = (r : ℤ))) := by
    simp

  have hTriangleMemFilter {r : ℕ} {x : ℤ × ℤ} (hx : x ∈ Δ r) :
      x ∈ (((Finset.Icc (0 : ℤ) (r : ℤ)).product
        (Finset.Icc (0 : ℤ) (r : ℤ))).filter
          (fun y => y.1 + y.2 ≤ (r : ℤ))) := by
    rcases Finset.mem_insert.mp hx with hxZero | hx
    · subst x
      exact hZeroInTriangleFilter r
    · exact hx

  have hShellMemFilter {r : ℕ} {x : ℤ × ℤ} (hx : x ∈ S r) :
      x ∈ (((Finset.Icc (0 : ℤ) (r : ℤ)).product
        (Finset.Icc (0 : ℤ) (r : ℤ))).filter
          (fun y => y.1 + y.2 = (r : ℤ))) := by
    rcases Finset.mem_insert.mp hx with hxWitness | hx
    · subst x
      exact hShellWitnessInFilter r
    · exact hx

  -- The coordinate sum places a triangle point on one of its prefix shells.
  have hTrianglePointOnPrefixShell {x : ℤ × ℤ} (hx : x ∈ Δ n) :
      ∃ r ∈ Finset.range (n + 1), x ∈ S r := by
    have hxFilter := hTriangleMemFilter hx
    rcases Finset.mem_filter.mp hxFilter with ⟨hxProduct, hsum⟩
    rcases Finset.mem_product.mp hxProduct with ⟨hx1, hx2⟩
    rcases Finset.mem_Icc.mp hx1 with ⟨h01, _⟩
    rcases Finset.mem_Icc.mp hx2 with ⟨h02, _⟩
    let r : ℕ := (x.1 + x.2).toNat
    have hsumNonneg : 0 ≤ x.1 + x.2 := add_nonneg h01 h02
    have hrCast : (r : ℤ) = x.1 + x.2 := by
      dsimp [r]
      exact Int.toNat_of_nonneg hsumNonneg
    have hrLeZ : (r : ℤ) ≤ (n : ℤ) := by
      rw [hrCast]
      exact hsum
    have hrLe : r ≤ n := by
      exact_mod_cast hrLeZ
    have hrMem : r ∈ Finset.range (n + 1) := by
      apply Finset.mem_range.mpr
      omega
    have h1r : x.1 ≤ (r : ℤ) := by
      rw [hrCast]
      omega
    have h2r : x.2 ≤ (r : ℤ) := by
      rw [hrCast]
      omega
    have hxShellFilter :
        x ∈ (((Finset.Icc (0 : ℤ) (r : ℤ)).product
          (Finset.Icc (0 : ℤ) (r : ℤ))).filter
            (fun y => y.1 + y.2 = (r : ℤ))) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨h01, h1r⟩
      · exact Finset.mem_Icc.mpr ⟨h02, h2r⟩
      · exact hrCast.symm
    exact ⟨r, hrMem, Finset.mem_insert.mpr (Or.inr hxShellFilter)⟩

  -- Every shell through level n lies inside the closed triangle at level n.
  have hPrefixShellPointInTriangle {r : ℕ}
      (hr : r ∈ Finset.range (n + 1)) {x : ℤ × ℤ} (hx : x ∈ S r) :
      x ∈ Δ n := by
    have hrLt : r < n + 1 := Finset.mem_range.mp hr
    have hrLe : r ≤ n := by omega
    have hrLeZ : (r : ℤ) ≤ (n : ℤ) := by exact_mod_cast hrLe
    have hxFilter := hShellMemFilter hx
    rcases Finset.mem_filter.mp hxFilter with ⟨hxProduct, hsum⟩
    rcases Finset.mem_product.mp hxProduct with ⟨hx1, hx2⟩
    rcases Finset.mem_Icc.mp hx1 with ⟨h01, h1r⟩
    rcases Finset.mem_Icc.mp hx2 with ⟨h02, h2r⟩
    have h1n : x.1 ≤ (n : ℤ) := h1r.trans hrLeZ
    have h2n : x.2 ≤ (n : ℤ) := h2r.trans hrLeZ
    have hsumN : x.1 + x.2 ≤ (n : ℤ) := by rw [hsum]; exact hrLeZ
    have hxTriangleFilter :
        x ∈ (((Finset.Icc (0 : ℤ) (n : ℤ)).product
          (Finset.Icc (0 : ℤ) (n : ℤ))).filter
            (fun y => y.1 + y.2 ≤ (n : ℤ))) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨h01, h1n⟩, Finset.mem_Icc.mpr ⟨h02, h2n⟩⟩, hsumN⟩
    exact Finset.mem_insert.mpr (Or.inr hxTriangleFilter)

  -- Compare the two finite suprema using those membership bounds.
  apply le_antisymm
  · apply Finset.sup'_le
    intro x hx
    obtain ⟨r, hr, hxShell⟩ := hTrianglePointOnPrefixShell hx
    calc
      f x ≤ (S r).sup' (by dsimp [S]; exact Finset.insert_nonempty _ _) f :=
        Finset.le_sup' _ hxShell
      _ ≤ (Finset.range (n + 1)).sup'
          ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
          (fun k => (S k).sup' (by dsimp [S]; exact Finset.insert_nonempty _ _) f) :=
        Finset.le_sup'
          (fun k => (S k).sup' (by dsimp [S]; exact Finset.insert_nonempty _ _) f) hr
  · apply Finset.sup'_le
    intro r hr
    apply Finset.sup'_le
    intro x hx
    exact Finset.le_sup' _ (hPrefixShellPointInTriangle hr hx)

end ProbabilityBasics
