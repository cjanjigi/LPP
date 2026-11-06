/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.DefectAlgebra
public import LPP_Foundations.Model.Paths.HorizontalFirst
public import LPP_Foundations.Model.Paths.WeightConcat
public import Differentiability.Model.CoarseCrossingBlocks
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # Coarse scale of one grid interval: attaching a crossing by two staircases

At a coarse scale (`8 c_* j² w ≤ l`, with `c_* = 50 / min a (1 - a)`) a crossing of
one of the `j²` blocks from level `I + m'` to level `I + l - m'`, where
`m' = ⌈c_* j² w⌉`, is attached to the two points `ẑ(I, ρ)` and `ẑ(I + l, ρ)` by
horizontal-first staircases of length `m'`. Both staircases exist, the concatenation
has small defect, and it stays within transverse distance `3 c_* j² w` of `ρ`.
Here `ẑ(I, ρ)` is a site on level `I` with transverse coordinate in `(ρ - 1, ρ]`.
-/

public section

namespace LPPDifferentiability

/-- A step of an admissible path changes the transverse coordinate by at most `1`, so
after `i` steps it has moved by at most `i`. -/
private theorem transverse_drift (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    {u : Lattice} {d : ℕ × ℕ} (p : Path u d) (i : Fin (d.1 + d.2 + 1)) :
    |(1 - a) * ((p.vertex i).1 : ℝ) - a * ((p.vertex i).2 : ℝ) -
      ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| ≤ (i.val : ℝ) := by
  induction i using Fin.induction with
  | zero => simp [p.start]
  | succ j ih =>
    simp only [Fin.val_castSucc] at ih
    obtain ⟨h₁, h₂⟩ := abs_le.mp ih
    have hs : (((j.succ : Fin (d.1 + d.2 + 1)).val : ℕ) : ℝ) = (j.val : ℝ) + 1 := by
      simp
    rw [hs]
    rcases p.step j with h | h <;> rw [h] <;>
      simp only [Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_one, Int.cast_zero] <;>
      rw [abs_le] <;> constructor <;> nlinarith

/-- Every vertex of a concatenation is a vertex of one of the two pieces. -/
private theorem concat_vertex_cases {u : Lattice} {d e : ℕ × ℕ} (p : Path u d)
    (q : Path (u + ((d.1 : ℤ), (d.2 : ℤ))) e) (k : Fin ((d + e).1 + (d + e).2 + 1)) :
    (∃ i, (p.concat q).vertex k = p.vertex i) ∨ ∃ i, (p.concat q).vertex k = q.vertex i := by
  have hk := k.isLt
  simp only [Prod.fst_add, Prod.snd_add] at hk
  by_cases h : k.val < d.1 + d.2
  · exact Or.inl ⟨⟨k.val, by omega⟩, by simp [Path.concat, Path.concatVertex, h]⟩
  · exact Or.inr ⟨⟨k.val - (d.1 + d.2), by omega⟩, by simp [Path.concat, Path.concatVertex, h]⟩

/-- A lattice vector of level `m` whose transverse coordinate is at most
`min a (1 - a) * m` in absolute value lies in the closed first quadrant, so it is the
displacement of a path. -/
theorem exists_nat_displacement_of_transverse_le (a : ℝ)
    (z v : Lattice) (m : ℕ) (hlev : v.1 + v.2 = z.1 + z.2 + (m : ℤ))
    (hr : |((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ)) - ((1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ))| ≤
      min a (1 - a) * (m : ℝ)) :
    ∃ d : ℕ × ℕ, z + ((d.1 : ℤ), (d.2 : ℤ)) = v := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hθ₁ : min a (1 - a) ≤ a := min_le_left _ _
  have hθ₂ : min a (1 - a) ≤ 1 - a := min_le_right _ _
  have hlevR : (v.1 : ℝ) + v.2 = z.1 + z.2 + m := by exact_mod_cast hlev
  obtain ⟨h₁, h₂⟩ := abs_le.mp hr
  have hx : (v.1 : ℝ) - z.1 = ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ)) -
      ((1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)) + a * m := by
    have : (v.2 : ℝ) = z.1 + z.2 + m - v.1 := by linarith
    rw [this]
    ring
  have hxa : 0 ≤ (v.1 : ℝ) - z.1 := by linarith [mul_le_mul_of_nonneg_right hθ₁ hm0]
  have hxb : (v.1 : ℝ) - z.1 ≤ m := by linarith [mul_le_mul_of_nonneg_right hθ₂ hm0]
  have hxa' : 0 ≤ v.1 - z.1 := by
    have : ((0 : ℤ) : ℝ) ≤ ((v.1 - z.1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hxb' : v.1 - z.1 ≤ (m : ℤ) := by
    have : ((v.1 - z.1 : ℤ) : ℝ) ≤ (((m : ℤ) : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  refine ⟨((v.1 - z.1).toNat, (v.2 - z.2).toNat), ?_⟩
  apply Prod.ext <;> simp <;> omega

/-- The sums of reals behind the defect bound of the coarse concatenation. -/
private theorem coarse_defect_core (a G E s K t cstar P w mR lR x1 y1 x y x2 y2 W1 Wx W2 : ℝ)
    (hK : |s| ≤ K) (hEG : E ≤ G) (hP : 1 ≤ P) (hwP : w ≤ P) (hmP : mR ≤ 2 * cstar * P)
    (hd₁ : x1 + y1 = mR) (hd : x + y = lR - 2 * mR) (hd₂ : x2 + y2 = mR)
    (hr : |(1 - a) * (x1 + x + x2) - a * (y1 + y + y2)| ≤ 1)
    (hW1 : mR * E - t ≤ W1) (hWx : G * (lR - 2 * mR) - K * w < Wx) (hW2 : mR * E - t ≤ W2) :
    (G * (x1 + y1) + s * ((1 - a) * x1 - a * y1) - W1) +
      ((G * (x + y) + s * ((1 - a) * x - a * y) - Wx) +
        (G * (x2 + y2) + s * ((1 - a) * x2 - a * y2) - W2)) ≤
      4 * cstar * (G - E) * P + 2 * K * P + 2 * t := by
  have hK0 : 0 ≤ K := (abs_nonneg s).trans hK
  have hs : s * ((1 - a) * (x1 + x + x2) - a * (y1 + y + y2)) ≤ K := by
    calc s * ((1 - a) * (x1 + x + x2) - a * (y1 + y + y2)) ≤
        |s * ((1 - a) * (x1 + x + x2) - a * (y1 + y + y2))| := le_abs_self _
      _ = |s| * |(1 - a) * (x1 + x + x2) - a * (y1 + y + y2)| := abs_mul _ _
      _ ≤ K * 1 := mul_le_mul hK hr (abs_nonneg _) hK0
      _ = K := mul_one K
  have h2 : (G - E) * (2 * mR) ≤ (G - E) * (4 * cstar * P) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 : K * w ≤ K * P := mul_le_mul_of_nonneg_left hwP hK0
  have h4 : K * 1 ≤ K * P := mul_le_mul_of_nonneg_left hP hK0
  have g1 : G * (x1 + y1) = G * mR := by rw [hd₁]
  have g2 : G * (x2 + y2) = G * mR := by rw [hd₂]
  have g3 : G * (x + y) = G * (lR - 2 * mR) := by rw [hd]
  linarith

/-- The start of the crossing is a nonnegative multiple of `θ₀ m'` from `ẑ₀` transversally. -/
private theorem coarse_reach_bound (θ P w N h ρ ru rc rz m : ℝ)
    (hcr : |rc - (h * w + 30 * N * w)| ≤ 1 / 2) (hu : |ru - rc| ≤ 8 * w)
    (hz₁ : ρ - 1 < rz) (hz₂ : rz ≤ ρ) (hρ₁ : h * w ≤ ρ) (hρ₂ : ρ < (h + 1) * w)
    (hN : w ≤ N * w) (hNP : N * w ≤ P) (hP : 2 ≤ P)
    (hθm : 50 * P ≤ θ * m) : |ru - rz| ≤ θ * m := by
  obtain ⟨c₁, c₂⟩ := abs_le.mp hcr
  obtain ⟨u₁, u₂⟩ := abs_le.mp hu
  rw [abs_le]
  constructor <;> linarith

/-- The end of the crossing is a nonpositive multiple of `θ₀ m'` from `ẑ₁` transversally. -/
private theorem coarse_return_bound (θ P w N h ρ ru rc rz m : ℝ)
    (hcr : |rc - (h * w + 30 * N * w)| ≤ 1 / 2) (hu : |ru - rc| ≤ 8 * w)
    (hz₁ : ρ - 1 < rz) (hz₂ : rz ≤ ρ) (hρ₁ : h * w ≤ ρ) (hρ₂ : ρ < (h + 1) * w)
    (hN : w ≤ N * w) (hNP : N * w ≤ P) (hP : 2 ≤ P)
    (hθm : 50 * P ≤ θ * m) : |rz - ru| ≤ θ * m := by
  obtain ⟨c₁, c₂⟩ := abs_le.mp hcr
  obtain ⟨u₁, u₂⟩ := abs_le.mp hu
  rw [abs_le]
  constructor <;> linarith

/-- A point within `8 w` of a block centre is within `39 j² w` of `ρ`. -/
private theorem coarse_location_bound (P w N h ρ rx rc : ℝ)
    (hcr : |rc - (h * w + 30 * N * w)| ≤ 1 / 2) (hx : |rx - rc| ≤ 8 * w)
    (hρ₁ : h * w ≤ ρ) (hρ₂ : ρ < (h + 1) * w)
    (hN : w ≤ N * w) (hNP : N * w ≤ P) (hP : 2 ≤ P) :
    |rx - ρ| ≤ 39 * P := by
  obtain ⟨c₁, c₂⟩ := abs_le.mp hcr
  obtain ⟨u₁, u₂⟩ := abs_le.mp hx
  rw [abs_le]
  constructor <;> linarith

/-- Vertices of the first staircase, within `m'` steps of `ẑ₀`. -/
private theorem coarse_first_location (rv rz ρ i m P c : ℝ) (hd : |rv - rz| ≤ i) (hi : i ≤ m)
    (hz₁ : ρ - 1 < rz) (hz₂ : rz ≤ ρ) (hm : m ≤ 2 * c * P) (hcP : 1 ≤ c * P) :
    |rv - ρ| ≤ 3 * c * P := by
  obtain ⟨d₁, d₂⟩ := abs_le.mp hd
  rw [abs_le]
  constructor <;> linarith

/-- Vertices of the second staircase, within `m'` steps of a point near the block. -/
private theorem coarse_second_location (rv ru ρ i m P c : ℝ) (hd : |rv - ru| ≤ i) (hi : i ≤ m)
    (hu : |ru - ρ| ≤ 39 * P) (hm : m ≤ 2 * c * P) (hcP : 100 * P ≤ c * P) :
    |rv - ρ| ≤ 3 * c * P := by
  obtain ⟨d₁, d₂⟩ := abs_le.mp hd
  obtain ⟨u₁, u₂⟩ := abs_le.mp hu
  rw [abs_le]
  constructor <;> linarith

/-- **Coarse scale of Lemma 5.7(i), one fixed environment.**
Let `ẑ₀, ẑ₁` be sites on levels `I` and `I + l` with transverse coordinates in
`(ρ - 1, ρ]`, let `ρ` lie in the bin `[h w, (h + 1) w)`, let `c_* = 50 / min a (1 - a)`,
`m' = ⌈c_* j² w⌉` and `l ≥ 8 c_* j² w`. The statement holds for every family of centres
`c ν` of the `j²` blocks that has the level and rounding properties below;
`exists_coarse_crossing_blocks` supplies one such family. For every such family and every
crossing `x` of block `ν` from level
`I + m'` to level `I + l - m'` with weight above `G0 (l - 2 m') - K w`, the two
displacements from `ẑ₀` to the start of `x` and from the end of `x` to `ẑ₁` have natural
coordinates, and if the two horizontal-first staircases have weight at least `m' E - t`,
the concatenation is an admissible path from `ẑ₀` to `ẑ₁` whose two defects are at most
`4 c_* (G0 - E) j² w + 2 K j² w + 2 t` and all of whose vertices are within
`3 c_* j² w` of `ρ` in transverse coordinate. -/
theorem coarse_scale_connection
    (a G0 E dl dr K t cstar : ℝ) (ω : Environment) (ha₀ : 0 < a) (ha₁ : a < 1)
    (hcstar : cstar = 50 / min a (1 - a)) (hEG : E ≤ G0)
    (hdl : |dl| ≤ K) (hdr : |dr| ≤ K)
    (w j l m : ℕ) (hw : 2 ≤ w) (hj : 1 ≤ j)
    (hm : m = ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊)
    (hl : 8 * cstar * ((j : ℝ) ^ 2 * (w : ℝ)) ≤ (l : ℝ))
    (_hell : (l : ℝ) ≤ (w : ℝ) ^ 3 / 2)
    (I h : ℤ) (ρ : ℝ) (hρ₁ : (h : ℝ) * (w : ℝ) ≤ ρ) (hρ₂ : ρ < ((h : ℝ) + 1) * (w : ℝ))
    (z₀ z₁ : Lattice)
    (hz₀ : z₀.1 + z₀.2 = I ∧ ρ - 1 < (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ∧
      (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ≤ ρ)
    (hz₁ : z₁.1 + z₁.2 = I + (l : ℤ) ∧ ρ - 1 < (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ∧
      (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ≤ ρ) :
    ∀ c : Fin (j ^ 2) → Lattice,
      (∀ ν, (c ν).1 + (c ν).2 = I + (m : ℤ)) →
      (∀ ν, |(1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ) -
        ((h : ℝ) * (w : ℝ) + 30 * ((ν.val + 1 : ℕ) : ℝ) * (w : ℝ))| ≤ 1 / 2) →
      ∀ (ν : Fin (j ^ 2)) (u : Lattice) (d : ℕ × ℕ) (x : Path u d),
        u.1 + u.2 = I + (m : ℤ) → d.1 + d.2 = l - 2 * m →
        (∀ k, |(1 - a) * ((x.vertex k).1 : ℝ) - a * ((x.vertex k).2 : ℝ) -
          ((1 - a) * ((c ν).1 : ℝ) - a * ((c ν).2 : ℝ))| ≤ 8 * (w : ℝ)) →
        G0 * ((l - 2 * m : ℕ) : ℝ) - K * (w : ℝ) < pathWeight ω x →
        ∃ d₁ d₂ : ℕ × ℕ,
          z₀ + ((d₁.1 : ℤ), (d₁.2 : ℤ)) = u ∧
          u + ((d.1 : ℤ), (d.2 : ℤ)) + ((d₂.1 : ℤ), (d₂.2 : ℤ)) = z₁ ∧
          ((m : ℝ) * E - t ≤ pathWeight ω (horizontalFirst z₀ d₁) →
            (m : ℝ) * E - t ≤
              pathWeight ω (horizontalFirst (u + ((d.1 : ℤ), (d.2 : ℤ))) d₂) →
            ∃ (D : ℕ × ℕ) (y : Path z₀ D),
              z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
              G0 * ((D.1 : ℝ) + (D.2 : ℝ)) +
                dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) - pathWeight ω y ≤
                  4 * cstar * (G0 - E) * ((j : ℝ) ^ 2 * (w : ℝ)) +
                    2 * K * ((j : ℝ) ^ 2 * (w : ℝ)) + 2 * t ∧
              G0 * ((D.1 : ℝ) + (D.2 : ℝ)) +
                dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) - pathWeight ω y ≤
                  4 * cstar * (G0 - E) * ((j : ℝ) ^ 2 * (w : ℝ)) +
                    2 * K * ((j : ℝ) ^ 2 * (w : ℝ)) + 2 * t ∧
              ∀ k, |(1 - a) * ((y.vertex k).1 : ℝ) - a * ((y.vertex k).2 : ℝ) - ρ| ≤
                3 * cstar * ((j : ℝ) ^ 2 * (w : ℝ))) := by
  set P : ℝ := (j : ℝ) ^ 2 * (w : ℝ) with hP
  have hθ : 0 < min a (1 - a) := lt_min ha₀ (by linarith)
  have hθ2 : min a (1 - a) ≤ 1 / 2 := by
    have h1 := min_le_left a (1 - a)
    have h2 := min_le_right a (1 - a)
    linarith
  have hcpos : 0 < cstar := by rw [hcstar]; positivity
  have hcθ : min a (1 - a) * cstar = 50 := by rw [hcstar]; field_simp
  have hc100 : 100 ≤ cstar := by
    have := mul_le_mul_of_nonneg_right hθ2 hcpos.le
    linarith
  have hw2 : (2 : ℝ) ≤ w := by exact_mod_cast hw
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj2 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by
    rw [sq]
    exact one_le_mul_of_one_le_of_one_le hj1 hj1
  have hP2 : 2 ≤ P := by
    calc (2 : ℝ) = 1 * 2 := by norm_num
      _ ≤ (j : ℝ) ^ 2 * (w : ℝ) := mul_le_mul hj2 hw2 (by norm_num) (by positivity)
  have hwP : (w : ℝ) ≤ P := le_mul_of_one_le_left (by positivity) hj2
  have hcP : 100 * P ≤ cstar * P := mul_le_mul_of_nonneg_right hc100 (by linarith)
  have hcP1 : 1 ≤ cstar * P := by linarith
  have hmge : cstar * P ≤ (m : ℝ) := by
    rw [hm]
    exact Nat.le_ceil _
  have hmlt : (m : ℝ) < cstar * P + 1 := by
    rw [hm]
    exact Nat.ceil_lt_add_one (by positivity)
  have hmP : (m : ℝ) ≤ 2 * cstar * P := by linarith
  have hθm : 50 * P ≤ min a (1 - a) * (m : ℝ) := by
    calc 50 * P = (min a (1 - a) * cstar) * P := by rw [hcθ]
      _ = min a (1 - a) * (cstar * P) := by ring
      _ ≤ min a (1 - a) * (m : ℝ) := mul_le_mul_of_nonneg_left hmge hθ.le
  have hml : 2 * m < l := by
    have : ((2 * m : ℕ) : ℝ) < l := by push_cast; linarith
    exact_mod_cast this
  intro c _hlevel hround ν u d x hu hd hx hW
  have hd' : (d.1 : ℤ) + d.2 = (l : ℤ) - 2 * m := by omega
  have hν : ((ν.val + 1 : ℕ) : ℝ) ≤ (j : ℝ) ^ 2 := by
    have h1 : ν.val + 1 ≤ j ^ 2 := ν.isLt
    exact_mod_cast h1
  have hN1 : (1 : ℝ) ≤ ((ν.val + 1 : ℕ) : ℝ) := by
    have : 1 ≤ ν.val + 1 := by omega
    exact_mod_cast this
  have hNw : ((ν.val + 1 : ℕ) : ℝ) * (w : ℝ) ≤ P :=
    mul_le_mul_of_nonneg_right hν (by positivity)
  have hNw1 : (w : ℝ) ≤ ((ν.val + 1 : ℕ) : ℝ) * (w : ℝ) :=
    le_mul_of_one_le_left (by positivity) hN1
  have hcr := hround ν
  have hxs := hx ⟨0, by omega⟩
  have hxe := hx (Fin.last (d.1 + d.2))
  rw [show (⟨0, by omega⟩ : Fin (d.1 + d.2 + 1)) = 0 from rfl, x.start] at hxs
  rw [x.finish] at hxe
  obtain ⟨hz₀l, hz₀a, hz₀b⟩ := hz₀
  obtain ⟨hz₁l, hz₁a, hz₁b⟩ := hz₁
  have hdisp₁ : ∃ d₁ : ℕ × ℕ, z₀ + ((d₁.1 : ℤ), (d₁.2 : ℤ)) = u :=
    exists_nat_displacement_of_transverse_le a z₀ u m (by omega)
      (coarse_reach_bound _ P w _ h ρ _ _ _ m hcr hxs hz₀a hz₀b hρ₁ hρ₂ hNw1 hNw hP2 hθm)
  have hdisp₂ : ∃ d₂ : ℕ × ℕ,
      u + ((d.1 : ℤ), (d.2 : ℤ)) + ((d₂.1 : ℤ), (d₂.2 : ℤ)) = z₁ :=
    exists_nat_displacement_of_transverse_le a (u + ((d.1 : ℤ), (d.2 : ℤ))) z₁ m
      (by simp only [Prod.fst_add, Prod.snd_add]; omega)
      (coarse_return_bound _ P w _ h ρ _ _ _ m hcr hxe hz₁a hz₁b hρ₁ hρ₂ hNw1 hNw hP2 hθm)
  obtain ⟨d₁, h1⟩ := hdisp₁
  obtain ⟨d₂, h2⟩ := hdisp₂
  refine ⟨d₁, d₂, h1, h2, fun hw1' hw2' => ?_⟩
  subst h1
  have e1 := congrArg Prod.fst h2
  have e2 := congrArg Prod.snd h2
  simp only [Prod.fst_add, Prod.snd_add] at e1 e2
  have hd₁ : d₁.1 + d₁.2 = m := by
    have := hu
    simp only [Prod.fst_add, Prod.snd_add] at this
    omega
  have hd₂ : d₂.1 + d₂.2 = m := by omega
  have hD : z₀ + (((d₁ + (d + d₂)).1 : ℤ), ((d₁ + (d + d₂)).2 : ℤ)) = z₁ := by
    rw [← h2]
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add] <;> omega
  have r1 : (z₀.1 : ℝ) + d₁.1 + d.1 + d₂.1 = z₁.1 := by exact_mod_cast e1
  have r2 : (z₀.2 : ℝ) + d₁.2 + d.2 + d₂.2 = z₁.2 := by exact_mod_cast e2
  have hrD : |(1 - a) * ((d₁.1 : ℝ) + d.1 + d₂.1) - a * ((d₁.2 : ℝ) + d.2 + d₂.2)| ≤ 1 := by
    have q1 : (d₁.1 : ℝ) + d.1 + d₂.1 = z₁.1 - z₀.1 := by linarith
    have q2 : (d₁.2 : ℝ) + d.2 + d₂.2 = z₁.2 - z₀.2 := by linarith
    rw [q1, q2, abs_le]
    constructor <;> linarith
  have hd₁R : (d₁.1 : ℝ) + d₁.2 = m := by exact_mod_cast hd₁
  have hd₂R : (d₂.1 : ℝ) + d₂.2 = m := by exact_mod_cast hd₂
  have hdR : (d.1 : ℝ) + d.2 = (l : ℝ) - 2 * m := by exact_mod_cast hd'
  have hcast : ((l - 2 * m : ℕ) : ℝ) = (l : ℝ) - 2 * m := by
    rw [Nat.cast_sub hml.le]
    push_cast
    ring
  rw [hcast] at hW
  have hloc : ∀ i : Fin (d.1 + d.2 + 1), |(1 - a) * ((x.vertex i).1 : ℝ) -
      a * ((x.vertex i).2 : ℝ) - ρ| ≤ 39 * P := fun i =>
    coarse_location_bound P w _ h ρ _ _ hcr (hx i) hρ₁ hρ₂ hNw1 hNw hP2
  have hlocu : |(1 - a) * (((z₀ + ((d₁.1 : ℤ), (d₁.2 : ℤ)) + ((d.1 : ℤ), (d.2 : ℤ))).1 : ℤ) : ℝ) -
      a * (((z₀ + ((d₁.1 : ℤ), (d₁.2 : ℤ)) + ((d.1 : ℤ), (d.2 : ℤ))).2 : ℤ) : ℝ) - ρ| ≤
        39 * P :=
    coarse_location_bound P w _ h ρ _ _ hcr hxe hρ₁ hρ₂ hNw1 hNw hP2
  have key : ∀ (s₁ : Path z₀ d₁)
      (s₂ : Path (z₀ + ((d₁.1 : ℤ), (d₁.2 : ℤ)) + ((d.1 : ℤ), (d.2 : ℤ))) d₂),
      (m : ℝ) * E - t ≤ pathWeight ω s₁ → (m : ℝ) * E - t ≤ pathWeight ω s₂ →
      ∃ (D : ℕ × ℕ) (y : Path z₀ D),
        z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
        G0 * ((D.1 : ℝ) + (D.2 : ℝ)) +
          dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) - pathWeight ω y ≤
            4 * cstar * (G0 - E) * P + 2 * K * P + 2 * t ∧
        G0 * ((D.1 : ℝ) + (D.2 : ℝ)) +
          dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) - pathWeight ω y ≤
            4 * cstar * (G0 - E) * P + 2 * K * P + 2 * t ∧
        ∀ k, |(1 - a) * ((y.vertex k).1 : ℝ) - a * ((y.vertex k).2 : ℝ) - ρ| ≤
          3 * cstar * P := by
    intro s₁ s₂ hs₁ hs₂
    refine ⟨d₁ + (d + d₂), s₁.concat (x.concat s₂), hD, ?_, ?_, ?_⟩
    · have f1 := Path.path_support_defect_concat a G0 dl ω s₁ (x.concat s₂)
      have f2 := Path.path_support_defect_concat a G0 dl ω x s₂
      rw [f1, f2]
      exact coarse_defect_core a G0 E dl K t cstar P (w : ℝ) m l d₁.1 d₁.2 d.1 d.2 d₂.1 d₂.2
        _ _ _ hdl hEG (by linarith) hwP hmP hd₁R hdR hd₂R hrD hs₁ hW hs₂
    · have f1 := Path.path_support_defect_concat a G0 dr ω s₁ (x.concat s₂)
      have f2 := Path.path_support_defect_concat a G0 dr ω x s₂
      rw [f1, f2]
      exact coarse_defect_core a G0 E dr K t cstar P (w : ℝ) m l d₁.1 d₁.2 d.1 d.2 d₂.1 d₂.2
        _ _ _ hdr hEG (by linarith) hwP hmP hd₁R hdR hd₂R hrD hs₁ hW hs₂
    · intro k
      rcases concat_vertex_cases s₁ (x.concat s₂) k with ⟨i, hi⟩ | ⟨i₂, hi₂⟩
      · rw [hi]
        have hile : (i.val : ℝ) ≤ m := by
          have := i.isLt
          have : i.val ≤ m := by omega
          exact_mod_cast this
        exact coarse_first_location _ _ ρ _ m P cstar (transverse_drift a ha₀ ha₁ s₁ i) hile
          hz₀a hz₀b hmP hcP1
      · rcases concat_vertex_cases x s₂ i₂ with ⟨i, hi⟩ | ⟨i, hi⟩
        · rw [hi₂, hi]
          exact (hloc i).trans (by linarith)
        · rw [hi₂, hi]
          have hile : (i.val : ℝ) ≤ m := by
            have := i.isLt
            have : i.val ≤ m := by omega
            exact_mod_cast this
          exact coarse_second_location _ _ ρ _ m P cstar (transverse_drift a ha₀ ha₁ s₂ i) hile
            hlocu hmP hcP
  exact key _ _ hw1' hw2'

end LPPDifferentiability
